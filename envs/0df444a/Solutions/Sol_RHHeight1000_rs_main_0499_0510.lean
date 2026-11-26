-- Prove2me | solution 1 for RHHeight1000.rs_main_0499_0510
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T10:41:03.610729+00:00
-- url     : https://prove2.me/submissions/38cfb6da-8ad4-46d5-bab7-5d1c00b0ca7a

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

noncomputable def hp619308 := nat_lit 154742504910672534362390528

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

noncomputable def hp631348 := nat_lit 253092741970790968397859029543733109897246971520789871559966720

noncomputable def hp631351 := nat_lit 11389173388685593577903656329467989945376113718435544220198502400

noncomputable def hp632130 := nat_lit 3861888762982039923063034508418779142719222587902677483520

noncomputable def hp632133 := nat_lit 173784994334191796537836552878845061422365016455620486758400

noncomputable def hp633087 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600

noncomputable def hp633090 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600

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

noncomputable def hp684401 := nat_lit 64791741944522487909851911563195676133695224709322207119351480320

noncomputable def hp684404 := nat_lit 2915628387503511955943336020343805426016285111919499320370816614400

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

noncomputable def hp740132 := nat_lit 1982464000000000000000000

noncomputable def hp740271 := @Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (Enclosure.sfrac Bool.true 1 1) Bool.true 1

noncomputable def hp740893 := nat_lit 2973696000000000000000000

noncomputable def hp742826 := nat_lit 3868562622766813359059763200000000000000

noncomputable def hp743845 := nat_lit 2857031722136135354286080000

noncomputable def hp745658 := nat_lit 3996645342911614855169325114413848961633120431781532997847909552396155328908156533147964360867027353600

noncomputable def hp745661 := nat_lit 363694726204956951820408585411660255508613959292119502804159769268050134930642244516464756838899489177600

noncomputable def hp749778 := nat_lit 42817430781178796431748579083484854091482398720

noncomputable def hp749779 := nat_lit 299722015468251575022240053584393978640376791040

noncomputable def hp752398 := nat_lit 6428321374806304547143680000

noncomputable def hp754729 := nat_lit 2571328549922521818857472000

noncomputable def hp756249 := nat_lit 1714219033281681212571648000

noncomputable def hp758057 := nat_lit 1428515861068067677143040000

noncomputable def hp762191 := nat_lit 714257930534033838571520000

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

noncomputable def hp763950 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 877478 1000)) Bool.false 3258179606373724984551 4722366482869645213696 515163359319180494358809

noncomputable def hp763951 := nat_lit 642832137480630454714368000

noncomputable def hp763952 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 877478 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 877478 1000)) Bool.false 3258179606373724984551 4722366482869645213696

noncomputable def hp763953 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 877478 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp763954 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp763953 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp763955 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 877478 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp763956 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000)) (Enclosure.sfrac Bool.false 877478 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp763954 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp763957 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 877478 1000)) hp763956 Bool.false 3258179606373724984551 4722366482869645213696

noncomputable def hp763958 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 877478 1000) 877478 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 877478 1000)) rfl

noncomputable def hp763959 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000)) (Enclosure.sfrac Bool.false 877478 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp763954 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp763960 := nat_lit 54663183022926960790408790016

noncomputable def hp763961 := @hp763959 8747961 16777216 26615 33554432 795847487632998012135 4722366482869645213696 5276100937128920598809 hp763951 hp763960 3258179606373724984551 4722366482869645213696

noncomputable def hp763962 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000)) (Enclosure.sfrac Bool.false 877478 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000)) (Enclosure.sfrac Bool.false 877478 1000) 11)

noncomputable def hp763963 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000)) (Enclosure.sfrac Bool.false 877478 1000) 11) hp763962

noncomputable def hp763964 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000)) (Enclosure.sfrac Bool.false 877478 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000)) (Enclosure.sfrac Bool.false 877478 1000) 11)

noncomputable def hp763965 := @hp763964 139967376 536870912 212920 536870912 139967376 536870912 212920 536870912 150288825606733824 8747961 16777216

noncomputable def hp763966 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000)) (Enclosure.sfrac Bool.false 877478 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp763967 := hp763966 BSN.quadSignPos 9 10 11 877478 1000 186 239 536870912 268435456 9007199254740992

noncomputable def hp763968 := hp763967 Bool.false 927646871830 3998 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp763969 := hp763968 Bool.false 178331775 182786 Bool.true 226932543 Bool.true 431148583 28296951008113761 1 Bool.false 489619181

noncomputable def hp763970 := hp763969 Bool.true Bool.false 386276651 Bool.false Bool.false 139967376 212920 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 186 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 489619181 536870912) BSN.abs_quadSignPos

noncomputable def hp763971 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000)) (Enclosure.sfrac Bool.false 877478 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp763972 := hp763971 BSN.quadSignPos 7 8 9 877478 1000 61 127 536870912 268435456 9007199254740992

noncomputable def hp763973 := hp763972 Bool.false 927646871830 3998 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp763974 := hp763973 Bool.false 226728939 149281 Bool.true 520056994 Bool.true 347958989 28296951008113761 1 Bool.false 442456646

noncomputable def hp763975 := hp763974 Bool.true Bool.false 324104667 Bool.false Bool.false 178331775 182786 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 442456646 536870912) BSN.abs_quadSignPos

noncomputable def hp763976 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000)) (Enclosure.sfrac Bool.false 877478 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp763977 := hp763976 BSN.quadSignPos 5 6 7 877478 1000 99 12 536870912 268435456 9007199254740992

noncomputable def hp763978 := hp763977 Bool.false 927646871830 3998 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp763979 := hp763978 Bool.false 188996033 110934 Bool.false 74413583 Bool.false 823597280 28296951008113761 1 Bool.false 74175543

noncomputable def hp763980 := hp763979 Bool.false Bool.false 19713144 Bool.false Bool.false 226728939 149281 BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 74175543 536870912) BSN.abs_quadSignPos

noncomputable def hp763981 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000)) (Enclosure.sfrac Bool.false 877478 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp763982 := hp763981 BSN.quadSignPos 3 4 5 877478 1000 325 200 536870912 268435456 9007199254740992

noncomputable def hp763983 := hp763982 Bool.false 927646871830 3998 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp763984 := hp763983 Bool.false 379593900 65569 Bool.false 496798441 Bool.false 789922891 28296951008113761 1 Bool.false 428872292

noncomputable def hp763985 := hp763984 Bool.true Bool.false 53303998 Bool.false Bool.false 188996033 110934 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 325 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 428872292 536870912) BSN.abs_quadSignPos

noncomputable def hp763986 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000)) (Enclosure.sfrac Bool.false 877478 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp763987 := hp763986 BSN.quadSignNeg 1 2 3 877478 1000 712 486 536870912 268435456 9007199254740992

noncomputable def hp763988 := hp763987 Bool.false 927646871830 3998 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp763989 := hp763988 Bool.false 536870648 4058 Bool.false 670328490 Bool.false 247941000 28296951008113761 1 Bool.false 170008605

noncomputable def hp763990 := hp763989 Bool.false Bool.false 480628481 Bool.true Bool.false 379593900 65569 BSN.abs_quadSignPos (BSN.cos_quad_nat0 712 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 170008605 536870912) BSN.abs_quadSignNeg

noncomputable def hp763991 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000)) (Enclosure.sfrac Bool.false 877478 1000) 1) Bool.false

noncomputable def hp763992 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000)) (Enclosure.sfrac Bool.false 877478 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000)))

noncomputable def hp763993 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000))) Bool.false 67108831 67108864

noncomputable def hp763994 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 57977929489) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 57977929489 33554432

noncomputable def hp763995 := nat_lit 999040188683558682733458282368232744457124412862762476337

noncomputable def hp763996 := nat_lit 578189431248611284053210165142027879156739481796608000

noncomputable def hp763997 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000)) Bool.false hp763995 hp763996 548850871104260557

noncomputable def hp763998 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 877478 4000) (Real.log (Enclosure.sfrac Bool.false 3079871561936 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1754956))))))

noncomputable def hp763999 := nat_lit 249702435399355046294183670256640000

noncomputable def hp764000 := nat_lit 1314650560854286786828220477086751723520

noncomputable def hp764001 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp763998 (Enclosure.sfrac Bool.false 877478 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 877478 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp763999 hp764000)) Bool.false

noncomputable def hp764002 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 877478 1000) 877478 1000 3079871561936 16000000 1754956

noncomputable def hp764003 := hp764002 4000 2000 hp763999 hp764000 (@Eq.refl Real (Enclosure.sfrac Bool.false 877478 1000)) rfl rfl rfl rfl

noncomputable def hp764004 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp763998 (Enclosure.sfrac Bool.false 877478 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 877478 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp763999 hp764000) 15563333651235292183813 9007199254740992000

noncomputable def hp764005 := nat_lit 20460343064239281822381225622901406606481907975429375515381760

noncomputable def hp764006 := @hp764004 548850871104260557 73728000000000000000000 hp763999 hp764000 0 1 hp764005 hp763995 hp763996 548850871104260557 73728000000000000000000

noncomputable def hp764007 := @Enclosure.Real.IsNear.subLit_ff_p (hp763998 (Enclosure.sfrac Bool.false 877478 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 877478 2000) (Real.log Real.pi)) 20087088183153763941637 9007199254740992000 45737567129317 18000000000000000000

noncomputable def hp764008 := nat_lit 522218820693686327581884809216000

noncomputable def hp764009 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 877478 4000) (Real.log (Enclosure.sfrac Bool.false 3079871561936 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1754956))))))

noncomputable def hp764010 := @hp764009 (Enclosure.sfrac Bool.false 877478 2000) 961555911079182881229 360287970189639680 45737567129317 18000000000000000000 877478 2000 0

noncomputable def hp764011 := nat_lit 1606967054652301115330960

noncomputable def hp764012 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 877478 4000) (Real.log (Enclosure.sfrac Bool.false 3079871561936 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1754956))))) 961697344512048617389

noncomputable def hp764013 := nat_lit 2165231421416052905099451321173409792

noncomputable def hp764014 := @hp764012 360287970189639680 5484245622375107 2178000000000000000000 883958955410851 2251799813685248 200000001089 8712000000000000000 hp764013 961555911079182881229 360287970189639680 45737567129317

noncomputable def hp764015 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 877478 4000) (Real.log (Enclosure.sfrac Bool.false 3079871561936 16000000)) 877478 4000 0 1 54798943364508775 4503599627370496

noncomputable def hp764016 := nat_lit 117679834802960697865011200

noncomputable def hp764017 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3079871561936) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp764016 hp617687

noncomputable def hp764018 := BSN.log_rat_reduce_isNear 3079871561936 16000000 17 6159743123872 4194304000000 103161802 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp764019 := nat_lit 143755976600059662861749976781810745132013262105727305607180561586468787927826658935906267707856951933161712916238195447962292715520

noncomputable def hp764020 := nat_lit 1764965198158866047159168554026119900033082504544130764118915861603813981418426137356597056739322503019971580389788493699721723904

noncomputable def hp764021 := nat_lit 793830571555960092009830879160684319980487115786592064914859292006801349674437233663491214284314977480353496257159044792320

noncomputable def hp764022 := BSN.log_dyadic_bound 982719561936 5177023561936 6 5 hp764019 268435456 87120000 hp764020 hp764021 103161802 6159743123872

noncomputable def hp764023 := hp764022 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp764024 := @BSN.binarySplit_of_base5 (BSN.artanhP 982719561936) (BSN.artanhQ 5177023561936) 0 5 hp764020 hp764019 hp764021 rfl rfl rfl

noncomputable def hp764025 := hp764018 rfl rfl rfl rfl (hp764023 (hp764024 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp764026 := @hp764015 12500018513 1089000000000000000 961697344512048617389 360287970189639680 5484245622375107 2178000000000000000000 (Enclosure.Real.IsNear.const Bool.false 877478 4000) (BSN.isNear_log_sfrac 3079871561936 16000000 54798943364508775 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp764017 1000001481040000 87120000000000000000000 54798943364508775 4503599627370496 12500018513 1089000000000000000 (hp764025 rfl rfl rfl) rfl)) rfl

noncomputable def hp764027 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1754956)))) 1 4

noncomputable def hp764028 := @hp764027 0 1 883958955410851 562949953421312 200000001089 2178000000000000000 883958955410851 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp764029 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1754956))) 884279719003555 562949953421312 1

noncomputable def hp764030 := @hp764029 2000000000000000 19119 33554432 1 10890000 29660740660124431941632 883958955410851 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp764031 := BSN.arctan_dyadic_bound_f 1000 1754956 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp764032 := hp764031 1 19119 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1754956) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1754956) 0 0 rfl)

noncomputable def hp764033 := hp764028 (hp764030 (hp764032 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp764034 := @hp764007 16852298870379 33554432000 1316217 268435456000 hp764008 15563333651235292183813 9007199254740992000 548850871104260557 73728000000000000000000 (@hp764010 1 hp764011 20087088183153763941637 9007199254740992000 45737567129317 18000000000000000000 (@hp764014 18000000000000000000 hp764026 hp764033 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 877478 2000) rfl rfl)

noncomputable def hp764035 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 877478 2000) (Real.log Real.pi) 877478 2000 0 1 38410761 33554432

noncomputable def hp764036 := hp764034 (@hp764035 3 268435456 16852298870379 33554432000 1316217 268435456000 (Enclosure.Real.IsNear.const Bool.false 877478 2000) hd4909 rfl) rfl

noncomputable def hp764037 := @hp763997 73728000000000000000000 57977929489 33554432 501 67108864 (@hp764001 hp763995 hp763996 548850871104260557 73728000000000000000000 (hp764003 rfl rfl rfl rfl rfl) (hp764006 (hp764036 rfl) (Enclosure.Real.IsNear.const Bool.true hp763999 hp764000) rfl rfl)) rfl

noncomputable def hp764038 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 57977929489) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 4770556000778120593408) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp764039 := BSN.sin_reduce_arg_pos_rat_q0 57977929489 33554432 226375608064910080 72057594037927936 275 4770556000778120593408 hp619237 rfl rfl rfl rfl

noncomputable def hp764040 := BSN.cos_dyadic_bound_f 135587356 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp764041 := hp764040 1 67108831 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 135587356) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp764042 := hp764041 (@BSN.binarySplit_of_le (BSN.cosOddP 135587356) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp764043 := @BSN.cos_arg_round Bool.false 67108831 67108864 4770556000778120593408 hp619237 135587356 137438953472 21801270 21780000 hp764042 rfl

noncomputable def hp764044 := hp764038 67108831 67108864 275 1000000000000000 21780000 10890000 hp764039 BSN.pi_near_15 hp764043 rfl rfl

noncomputable def hp764045 := @hp763994 501 67108864 Bool.false 67108831 67108864 1 10890000 hp764037 (Enclosure.sfrac_false_div 57977929489 33554432) (hp764044 rfl rfl) rfl

noncomputable def hp764046 := @hp763991 67108831 67108864 345187429 45675970560000 536870648 536870912 4058 536870912 (@hp763992 Bool.false 67108831 67108864 345187429 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000)) (Enclosure.sfrac Bool.false 877478 1000)) (@hp763993 5522998864 730815528960000 67108831 67108864 345187429 45675970560000 (hp764045 rfl) rfl))

noncomputable def hp764047 := @hp763997 73728000000000000000000 927646871830 536870912 3998 536870912 (@hp764001 hp763995 hp763996 548850871104260557 73728000000000000000000 (hp764003 rfl rfl rfl rfl rfl) (hp764006 (hp764036 rfl) (Enclosure.Real.IsNear.const Bool.true hp763999 hp764000) rfl rfl)) rfl

noncomputable def hp764048 := hp763990 (BSN.cos_quad_nat2 486 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 480628481 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 877478 1000)) rfl rfl (hp764046 rfl) hp764047

noncomputable def hp764049 := nat_lit 27852448029297099528802881019925744974730595519034415361803792095050242507395589123660607246414653574771264000000

noncomputable def hp764050 := nat_lit 8230991168261055612457747634570283959506572759405913264724399048414137097167139422498103940801000000000000

noncomputable def hp764051 := nat_lit 168808750608024210519093471278497666816479046386922823824753626087646474630464755827082011729163142993546201600000

noncomputable def hp764052 := BSN.cos_dyadic_bound_f 670328490 536870912 4 3 536870912 268435456 hp764049 hp716712 hp764050 hp764051 hp716714

noncomputable def hp764053 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 670328490) (BSN.cosEvenQ 536870912) 0 3 hp764049 hp716712 hp764050 rfl rfl rfl

noncomputable def hp764054 := hp764052 hp764050 170008605 rfl rfl rfl rfl rfl rfl rfl rfl (hp764053 rfl)

noncomputable def hp764055 := @BSN.binarySplit_of_base3 (BSN.cosOddP 670328490) (BSN.cosOddQ 536870912) 0 3 hp764051 hp716714 hp764050 rfl rfl rfl

noncomputable def hp764056 := nat_lit 527465345811932629666473368762219190209874618017790952673280000000000000

noncomputable def hp764057 := nat_lit 14281926306012357280601449275985806348708321000000000000000000000000

noncomputable def hp764058 := nat_lit 1582367473583185864284858903388105599016926437411372858019840000000000000

noncomputable def hp764059 := BSN.cos_dyadic_bound_f 247941000 536870912 3 2 536870912 268435456 hp764056 hp708868 hp764057 hp764058 hp708870

noncomputable def hp764060 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 247941000) (BSN.cosEvenQ 536870912) 0 2 hp764056 hp708868 hp764057 rfl rfl rfl

noncomputable def hp764061 := hp764059 hp764057 480628481 rfl rfl rfl rfl rfl rfl rfl rfl (hp764060 rfl)

noncomputable def hp764062 := @BSN.binarySplit_of_base2 (BSN.cosOddP 247941000) (BSN.cosOddQ 536870912) 0 2 hp764058 hp708870 hp764057 rfl rfl rfl

noncomputable def hp764063 := hp764048 hd4911 hd4913 hd4915 hd4917 hd4918 (hp764054 (hp764055 rfl) rfl rfl rfl rfl) (hp764061 (hp764062 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764064 := hp763985 (BSN.cos_quad_nat0 200 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 53303998 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 877478 1000)) rfl rfl (hp764063 rfl rfl rfl rfl rfl) hp764047

noncomputable def hp764065 := nat_lit 15306908006036964839412097414205178983219509940910026011892076927093532225

noncomputable def hp764066 := nat_lit 3710579958210290249168011294154584169891519325671046455728509804832321

noncomputable def hp764067 := nat_lit 40083513362545424585675887876061123248347463575856124527360450555084760641

noncomputable def hp764068 := BSN.sin_dyadic_bound_f 496798441 536870912 3 2 536870912 268435456 hp764065 hp708845 hp764066 hp764067 hp708848

noncomputable def hp764069 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 496798441) (BSN.sinEvenQ 536870912) 0 2 hp764065 hp708845 hp764066 rfl rfl rfl

noncomputable def hp764070 := hp764068 hp764066 428872292 rfl rfl rfl rfl rfl rfl rfl rfl (hp764069 rfl)

noncomputable def hp764071 := @BSN.binarySplit_of_base2 (BSN.sinOddP 496798441) (BSN.sinOddQ 536870912) 0 2 hp764067 hp708848 hp764066 rfl rfl rfl

noncomputable def hp764072 := nat_lit 53781614332379112697478671662298331660464745011710166114512276033046601714493870773023808419553660516927400066961

noncomputable def hp764073 := nat_lit 59022335709565762429814563884065326811769270414834276994032109405404773145015503062445879208652626134843281

noncomputable def hp764074 := nat_lit 325669720583416926558171858594077583078047231422216095809747343276888092701050088752027032868749822606622477008785

noncomputable def hp764075 := BSN.cos_dyadic_bound_f 789922891 536870912 4 3 536870912 268435456 hp764072 hp716712 hp764073 hp764074 hp716714

noncomputable def hp764076 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 789922891) (BSN.cosEvenQ 536870912) 0 3 hp764072 hp716712 hp764073 rfl rfl rfl

noncomputable def hp764077 := hp764075 hp764073 53303998 rfl rfl rfl rfl rfl rfl rfl rfl (hp764076 rfl)

noncomputable def hp764078 := @BSN.binarySplit_of_base3 (BSN.cosOddP 789922891) (BSN.cosOddQ 536870912) 0 3 hp764074 hp716714 hp764073 rfl rfl rfl

noncomputable def hp764079 := hp764064 hd4920 hd4922 hd4924 hd4926 hd4918 (hp764070 (hp764071 rfl) rfl rfl rfl rfl) (hp764077 (hp764078 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764080 := hp763980 (BSN.cos_quad_nat0 12 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 19713144 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 877478 1000)) rfl rfl (hp764079 rfl rfl rfl rfl rfl) hp764047

noncomputable def hp764081 := nat_lit 30662592048075527134014056656321

noncomputable def hp764082 := BSN.sin_dyadic_bound_f 74413583 536870912 2 1 536870912 268435456 hp764081 hp708890 hp764081 hp764081 hp708891

noncomputable def hp764083 := @BSN.binarySplit_of_base (BSN.sinEvenP 74413583) (BSN.sinEvenQ 536870912) 0 1 hp764081 hp708890 hp764081 rfl rfl rfl

noncomputable def hp764084 := hp764082 hp764081 74175543 rfl rfl rfl rfl rfl rfl rfl rfl (hp764083 rfl)

noncomputable def hp764085 := @BSN.binarySplit_of_base (BSN.sinOddP 74413583) (BSN.sinOddQ 536870912) 0 1 hp764081 hp708891 hp764081 rfl rfl rfl

noncomputable def hp764086 := nat_lit 63587880857624044323514014086977802915010621005932987107683941965191492186615824983537484292985230599389184000000

noncomputable def hp764087 := nat_lit 97404460188120465866999094823022600510217848933431472223779038334307456545205993858763080073216000000000000

noncomputable def hp764088 := nat_lit 384920949963404190389846098165062166051384261740434671680910793701621643918713610857255317636774950264740249600000

noncomputable def hp764089 := BSN.cos_dyadic_bound_f 823597280 536870912 4 3 536870912 268435456 hp764086 hp716712 hp764087 hp764088 hp716714

noncomputable def hp764090 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 823597280) (BSN.cosEvenQ 536870912) 0 3 hp764086 hp716712 hp764087 rfl rfl rfl

noncomputable def hp764091 := hp764089 hp764087 19713144 rfl rfl rfl rfl rfl rfl rfl rfl (hp764090 rfl)

noncomputable def hp764092 := @BSN.binarySplit_of_base3 (BSN.cosOddP 823597280) (BSN.cosOddQ 536870912) 0 3 hp764088 hp716714 hp764087 rfl rfl rfl

noncomputable def hp764093 := hp764080 hd4928 hd4930 hd4932 hd4934 hd4918 (hp764084 (hp764085 rfl) rfl rfl rfl rfl) (hp764091 (hp764092 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764094 := hp763975 (BSN.cos_quad_nat3 127 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 324104667 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 877478 1000)) rfl rfl (hp764093 rfl rfl rfl rfl rfl) hp764047

noncomputable def hp764095 := nat_lit 18381945885409481022263290787508059488214676809086499061595946971098415360

noncomputable def hp764096 := nat_lit 5350662165222217839706589768989910961234281174579993438451760222863616

noncomputable def hp764097 := nat_lit 48134528627804947657996712821942743565672631378086748981469986836325499136

noncomputable def hp764098 := BSN.sin_dyadic_bound_f 520056994 536870912 3 2 536870912 268435456 hp764095 hp708845 hp764096 hp764097 hp708848

noncomputable def hp764099 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 520056994) (BSN.sinEvenQ 536870912) 0 2 hp764095 hp708845 hp764096 rfl rfl rfl

noncomputable def hp764100 := hp764098 hp764096 442456646 rfl rfl rfl rfl rfl rfl rfl rfl (hp764099 rfl)

noncomputable def hp764101 := @BSN.binarySplit_of_base2 (BSN.sinOddP 520056994) (BSN.sinOddQ 536870912) 0 2 hp764097 hp708848 hp764096 rfl rfl rfl

noncomputable def hp764102 := nat_lit 3682975807355365607109825077819051830401560072084998724406607501172956705

noncomputable def hp764103 := nat_lit 214894095378825011447635507524996468407630589431075502818829090446881

noncomputable def hp764104 := nat_lit 9645541095490582301935769508228190513912378310696870155965122494068448801

noncomputable def hp764105 := BSN.sin_dyadic_bound_f 347958989 536870912 3 2 536870912 268435456 hp764102 hp708845 hp764103 hp764104 hp708848

noncomputable def hp764106 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 347958989) (BSN.sinEvenQ 536870912) 0 2 hp764102 hp708845 hp764103 rfl rfl rfl

noncomputable def hp764107 := hp764105 hp764103 324104667 rfl rfl rfl rfl rfl rfl rfl rfl (hp764106 rfl)

noncomputable def hp764108 := @BSN.binarySplit_of_base2 (BSN.sinOddP 347958989) (BSN.sinOddQ 536870912) 0 2 hp764104 hp708848 hp764103 rfl rfl rfl

noncomputable def hp764109 := hp764094 hd4936 hd4938 hd4940 hd4942 hd4918 (hp764100 (hp764101 rfl) rfl rfl rfl rfl) (hp764107 (hp764108 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764110 := hp763970 (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 386276651 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 877478 1000)) rfl rfl (hp764109 rfl rfl rfl rfl rfl) hp764047

noncomputable def hp764111 := nat_lit 370155452044961628596051811316321411636811467943510866219591642523502081

noncomputable def hp764112 := nat_lit 7033544488659164161064696505916738497546123570617735492944689497601

noncomputable def hp764113 := nat_lit 1110452289045907567459833304555952401433439311583391363187789038191511041

noncomputable def hp764114 := BSN.cos_dyadic_bound_f 226932543 536870912 3 2 536870912 268435456 hp764111 hp708868 hp764112 hp764113 hp708870

noncomputable def hp764115 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 226932543) (BSN.cosEvenQ 536870912) 0 2 hp764111 hp708868 hp764112 rfl rfl rfl

noncomputable def hp764116 := hp764114 hp764112 489619181 rfl rfl rfl rfl rfl rfl rfl rfl (hp764115 rfl)

noncomputable def hp764117 := @BSN.binarySplit_of_base2 (BSN.cosOddP 226932543) (BSN.cosOddQ 536870912) 0 2 hp764113 hp708870 hp764112 rfl rfl rfl

noncomputable def hp764118 := nat_lit 8682181638851833811036017363476269831536078639689388188217382637109800385

noncomputable def hp764119 := nat_lit 1194031281806194470061782153663716051394134848037426683227916652015041

noncomputable def hp764120 := nat_lit 22737113955869973761666612114189060685177948790384908468796490279755738561

noncomputable def hp764121 := BSN.sin_dyadic_bound_f 431148583 536870912 3 2 536870912 268435456 hp764118 hp708845 hp764119 hp764120 hp708848

noncomputable def hp764122 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 431148583) (BSN.sinEvenQ 536870912) 0 2 hp764118 hp708845 hp764119 rfl rfl rfl

noncomputable def hp764123 := hp764121 hp764119 386276651 rfl rfl rfl rfl rfl rfl rfl rfl (hp764122 rfl)

noncomputable def hp764124 := @BSN.binarySplit_of_base2 (BSN.sinOddP 431148583) (BSN.sinOddQ 536870912) 0 2 hp764120 hp708848 hp764119 rfl rfl rfl

noncomputable def hp764125 := hp764110 hd4944 hd4946 hd4961 hd4963 hd4918 (hp764116 (hp764117 rfl) rfl rfl rfl rfl) (hp764123 (hp764124 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764126 := @hp763965 26615 33554432 (hp764125 rfl rfl rfl rfl rfl) (hp764125 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp764127 := @hp763963 Bool.false 8747961 16777216 26615 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 877478 1000)) (Enclosure.sfrac Bool.false 877478 1000) 11) hp764126

noncomputable def hp764128 := @Enclosure.Real.IsNear.mulLit_tf hp763954 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1))) 9760809 33554432 1

noncomputable def hp764129 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp763953 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp764130 := @hp764129 1 1 0 1 9760809 33554432 1 33554432 9760809 33554432 1

noncomputable def hp764131 := @Enclosure.Real.IsNear.of_eq (hp763953 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp764132 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 877478 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp764133 := @hp764131 (@Inv.inv Real Real.instInv (Real.sqrt hp763955)) Bool.false 9760809 33554432 1 33554432 (hp764132 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 877478 1000) 877478 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 877478 1000))))

noncomputable def hp764134 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp763955)) Bool.false 19521618 67108864 2 67108864 9760809 33554432

noncomputable def hp764135 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp763955) Bool.false 230698077 67108864 7 67108864 230698077 67108864 7 67108864

noncomputable def hp764136 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 877478 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp764137 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 877478 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp764138 := @hp764137 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 877478 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 4686042708473

noncomputable def hp764139 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 877478 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 877478 1000 0

noncomputable def hp764140 := @hp764139 1 10680707 67108864 1 67108864 4686042708473 33554432000 438739 33554432000 (Enclosure.Real.IsNear.const Bool.false 877478 1000) hd4949

noncomputable def hp764141 := @hp764138 33554432000 438739 33554432000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 877478 1000) 877478 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 877478 1000))) (hp764140 rfl)

noncomputable def hp764142 := @hp764136 4686042708473 33554432000 438739 33554432000 396531823 396531861 33554432 hp764141 rfl rfl rfl

noncomputable def hp764143 := @Enclosure.Real.IsNear.recentre' hp763955 Bool.false 793063684 67108864 38 67108864 198265921 16777216 19 33554432 (hp764142 rfl rfl rfl)

noncomputable def hp764144 := @Enclosure.Real.IsNear.sqrt_image hp763955 198265921 16777216 19 33554432 115349035 115349042 33554432 (hp764143 rfl) rfl rfl

noncomputable def hp764145 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp763955) 230698077 67108864 7 67108864 9760808 9760810 33554432 (hp764135 (hp764144 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp764146 := @hp764130 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp764133 (@hp764134 1 33554432 (hp764145 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp764147 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp764148 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp764149 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1))) (hp764147 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764148 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp764150 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 877478 1000) 877478 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 877478 1000)) rfl

noncomputable def hp764151 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp764152 := @hp764151 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764148 (Enclosure.sfrac Bool.false 1 16)))) 81459805

noncomputable def hp764153 := @hp764152 33554432 723 33554432 1000923 4194304 216494027 22837985280000 81534992400015 140737488355328 2697010794333907 95789453011845120000

noncomputable def hp764154 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp764155 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1)))) 27643079

noncomputable def hp764156 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp764157 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 43091797) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false

noncomputable def hp764158 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1))) Bool.false 12129262558299617317475

noncomputable def hp764159 := nat_lit 512735433007485312404659653

noncomputable def hp764160 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp764161 := @Enclosure.Real.IsNear.subLit_ff_p hp763955 (Enclosure.sfrac Bool.false 11 1) 198265921 16777216 19 33554432 11 1 0

noncomputable def hp764162 := @hp764160 500000000000000 13716545 16777216 19 33554432 12129262558299617317475 2361183241434822606848 hp764159 hp682805 hd4948 (@hp764161 1 13716545 13716545 16777216 19 33554432 (hp764143 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp764163 := @hp764157 43091797 8388608 239 67108864 Bool.false 27643079 67108864 1 10890000 (@hp764158 2361183241434822606848 hp764159 hp682805 43091797 8388608 239 67108864 (hp764162 rfl) rfl) (Enclosure.sfrac_false_div 43091797 8388608)

noncomputable def hp764164 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 43091797) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 513253718727094188376064) (@Nat.cast Real Real.instNatCast hp630689)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp764165 := BSN.sin_reduce_arg_pos_rat_q3 43091797 8388608 226375608064910080 72057594037927936 0 513253718727094188376064 hp630689 rfl rfl rfl rfl

noncomputable def hp764166 := nat_lit 11592288060681888355570460553000740654410000

noncomputable def hp764167 := BSN.sin_dyadic_bound_f 58350192230 137438953472 2 1 67108864 21801270 hp764166 hp749778 hp764166 hp764166 hp749779

noncomputable def hp764168 := @BSN.binarySplit_of_base (BSN.sinEvenP 58350192230) (BSN.sinEvenQ 137438953472) 0 1 hp764166 hp749778 hp764166 rfl rfl rfl

noncomputable def hp764169 := hp764167 hp764166 27643079 rfl rfl rfl rfl rfl rfl rfl rfl (hp764168 rfl)

noncomputable def hp764170 := @BSN.binarySplit_of_base (BSN.sinOddP 58350192230) (BSN.sinOddQ 137438953472) 0 1 hp764166 hp749779 hp764166 rfl rfl rfl

noncomputable def hp764171 := @BSN.sin_arg_round Bool.false 27643079 67108864 513253718727094188376064 hp630689 58350192230 137438953472 21801270 21780000 (hp764169 (hp764170 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764172 := hp764164 27643079 67108864 0 1000000000000000 21780000 10890000 hp764165 BSN.pi_near_15 hp764171 rfl rfl

noncomputable def hp764173 := @hp764155 67108864 166863679 45675970560000 81459082 81460528 33554432 (@hp764156 27643079 67108864 2669818864 730815528960000 27643079 67108864 166863679 45675970560000 (hp764163 (hp764172 rfl rfl) rfl rfl) rfl)

noncomputable def hp764174 := @hp764154 Bool.false 162919610 67108864 1446 67108864 81459805 33554432 723 33554432 (hp764173 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp764175 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764148 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp764176 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764148 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 89243553)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp764177 := nat_lit 52680095495587890255185424605

noncomputable def hp764178 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764148 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp764177

noncomputable def hp764179 := nat_lit 45336390503790842169250738537292211

noncomputable def hp764180 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764148 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp764181 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp764182 := @hp764181 (Enclosure.sfrac Bool.false 1 16) 41981831501695 281474976710656 1679991989 1125899906842624 1 16 0

noncomputable def hp764183 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1)) 188143606737025

noncomputable def hp764184 := @hp764183 281474976710656 1042457781 1125899906842624 13716545 16777216 19 33554432 704338255179541381120 41981831501695 281474976710656 1679991989

noncomputable def hp764185 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1)) 13716545 16777216 19

noncomputable def hp764186 := @hp764185 33554432 13716545 16777216 19 33554432 188143606737025 281474976710656 1042457781 1125899906842624 (@hp764161 1 13716545 13716545 16777216 19 33554432 (hp764143 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp764187 := hp764186 (@hp764161 1 13716545 13716545 16777216 19 33554432 (hp764143 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp764188 := @hp764184 1125899906842624 (hp764187 rfl) (@hp764161 1 13716545 13716545 16777216 19 33554432 (hp764143 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp764189 := @hp764180 500000000000000 59574017546111 281474976710656 1679991989 1125899906842624 hp764177 hp631146 hp764179 hp682143 hd4948 (@hp764182 1 953184280737776 59574017546111 281474976710656 1679991989 1125899906842624 (hp764188 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp764190 := @hp764176 89243553 67108864 315 33554432 Bool.false 8007384 33554432 1 10890000 (@hp764178 hp631146 hp764179 hp682143 89243553 67108864 315 33554432 (hp764189 rfl) rfl) (Enclosure.sfrac_true_div 89243553 67108864)

noncomputable def hp764191 := nat_lit 521771265648699030403673738937479610894294509864690627119260052169897965851561398556871858347490689921

noncomputable def hp764192 := nat_lit 255224420933006582546929419566565826348339622313849018794869876901648385821118524127599805088641

noncomputable def hp764193 := nat_lit 3161489935874244105960842600464028169038251896404456983617046631122248904314678163108902534496937853825

noncomputable def hp764194 := BSN.cos_dyadic_bound_f 89243553 67108864 4 3 33554432 10890000 hp764191 hp745658 hp764192 hp764193 hp745661

noncomputable def hp764195 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 89243553) (BSN.cosEvenQ 67108864) 0 3 hp764191 hp745658 hp764192 rfl rfl rfl

noncomputable def hp764196 := hp764194 hp764192 8007384 rfl rfl rfl rfl rfl rfl rfl rfl (hp764195 rfl)

noncomputable def hp764197 := @BSN.binarySplit_of_base3 (BSN.cosOddP 89243553) (BSN.cosOddQ 67108864) 0 3 hp764193 hp745661 hp764192 rfl rfl rfl

noncomputable def hp764198 := hp764190 (BSN.cos_neg_of_bound 89243553 67108864 Bool.false 8007384 33554432 1 10890000 (hp764196 (hp764197 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp764199 := hp764153 hp764174 (@hp764175 8007384 33554432 3463904432 365407764480000 1000923 4194304 216494027 22837985280000 (hp764198 rfl) rfl)

noncomputable def hp764200 := @hp764128 33554432 81534992400015 140737488355328 2697010794333907 95789453011845120000 795847487632998012135 4722366482869645213696 5276100937128920598809 hp763951 (hp764146 rfl) (@hp764149 Bool.false 81534992400015 140737488355328 2697010794333907 95789453011845120000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763955 (Enclosure.sfrac Bool.false 11 1)) (hp764150 rfl (hp763958 rfl rfl))) (hp764199 rfl))

noncomputable def hp764201 := @hp763952 515163359319180494358809 hp763951 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 877478 1000))) (@hp763957 515163359319180494358809 hp763951 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 877478 1000) 11 (hp763958 rfl rfl)) (@hp763961 515163359319180494358809 hp763951 hp764127 (hp764200 rfl) rfl rfl))

theorem hd5065 : hp763950 hp763951 := hp764201

noncomputable def hp764202 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 878750 1000)) Bool.true 306950420731442336620847 75557863725914323419136 49977158152574219333851

noncomputable def hp764203 := nat_lit 62335237573879316820787200

noncomputable def hp764204 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 878750 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 878750 1000)) Bool.true 306950420731442336620847 75557863725914323419136

noncomputable def hp764205 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 878750 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp764206 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp764205 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp764207 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 878750 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp764208 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 878750 1000)) (Enclosure.sfrac Bool.false 878750 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp764206 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp764209 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 878750 1000)) hp764208 Bool.true 306950420731442336620847 75557863725914323419136

noncomputable def hp764210 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 878750 1000) 878750 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 878750 1000)) rfl

noncomputable def hp764211 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 878750 1000)) (Enclosure.sfrac Bool.false 878750 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp764206 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp764212 := nat_lit 20599094039609144292130640887808

noncomputable def hp764213 := @hp764211 284162861 67108864 213227 268435456 12988517996591175966417 75557863725914323419136 462254643830705631451 hp764203 hp764212 306950420731442336620847 75557863725914323419136

noncomputable def hp764214 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 878750 1000)) (Enclosure.sfrac Bool.false 878750 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 878750 1000)) (Enclosure.sfrac Bool.false 878750 1000) 11)

noncomputable def hp764215 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 878750 1000)) (Enclosure.sfrac Bool.false 878750 1000) 11) hp764214

noncomputable def hp764216 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 878750 1000)) (Enclosure.sfrac Bool.false 878750 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 878750 1000)) (Enclosure.sfrac Bool.false 878750 1000) 11)

noncomputable def hp764217 := @hp764216 1136651444 536870912 213227 536870912 1136651444 536870912 213227 536870912 1220470194732793856 284162861 67108864

noncomputable def hp764218 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 878750 1000)) (Enclosure.sfrac Bool.false 878750 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp764219 := hp764218 BSN.quadSignPos 9 10 11 878750 1000 186 239 536870912 268435456 9007199254740992

noncomputable def hp764220 := hp764219 Bool.false 929333599878 4003 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp764221 := hp764220 Bool.true 1076289639 183050 Bool.true 112639391 Bool.true 381942735 28296951008113761 1 Bool.false 525097915

noncomputable def hp764222 := hp764221 Bool.true Bool.false 350529918 Bool.false Bool.true 1136651444 213227 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 186 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 525097915 536870912) BSN.abs_quadSignPos

noncomputable def hp764223 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 878750 1000)) (Enclosure.sfrac Bool.false 878750 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp764224 := hp764223 BSN.quadSignPos 7 8 9 878750 1000 61 127 536870912 268435456 9007199254740992

noncomputable def hp764225 := hp764224 Bool.false 929333599878 4003 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp764226 := hp764225 Bool.true 1043088969 149497 Bool.true 253379158 Bool.true 161715147 28296951008113761 1 Bool.false 244077002

noncomputable def hp764227 := hp764226 Bool.true Bool.false 159280754 Bool.false Bool.true 1076289639 183050 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 244077002 536870912) BSN.abs_quadSignPos

noncomputable def hp764228 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 878750 1000)) (Enclosure.sfrac Bool.false 878750 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp764229 := hp764228 BSN.quadSignNeg 5 6 7 878750 1000 99 13 536870912 268435456 9007199254740992

noncomputable def hp764230 := hp764229 Bool.false 929333599878 4003 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp764231 := hp764230 Bool.true 1108145497 111095 Bool.false 537549457 Bool.false 338148839 28296951008113761 1 Bool.false 452127553

noncomputable def hp764232 := hp764231 Bool.false Bool.false 316230170 Bool.true Bool.true 1043088969 149497 BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 452127553 536870912) BSN.abs_quadSignNeg

noncomputable def hp764233 := hp764218 BSN.quadSignNeg 3 4 5 878750 1000 326 201 536870912 268435456 9007199254740992

noncomputable def hp764234 := hp764233 Bool.false 929333599878 4003 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp764235 := hp764234 Bool.true 707248821 65665 Bool.false 393511508 Bool.false 534251274 28296951008113761 1 Bool.false 398996543

noncomputable def hp764236 := hp764235 Bool.true Bool.false 450340526 Bool.true Bool.true 1108145497 111095 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 326 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 398996543 536870912) BSN.abs_quadSignNeg

noncomputable def hp764237 := hp764218 BSN.quadSignPos 1 2 3 878750 1000 714 487 536870912 268435456 9007199254740992

noncomputable def hp764238 := hp764237 Bool.false 929333599878 4003 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp764239 := hp764238 Bool.true 536870544 4066 Bool.false 197076773 Bool.false 341112086 28296951008113761 1 Bool.false 501103399

noncomputable def hp764240 := hp764239 Bool.true Bool.false 318619986 Bool.false Bool.true 707248821 65665 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 714 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 501103399 536870912) BSN.abs_quadSignPos

noncomputable def hp764241 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 878750 1000)) (Enclosure.sfrac Bool.false 878750 1000) 1) Bool.true

noncomputable def hp764242 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 878750 1000)) (Enclosure.sfrac Bool.false 878750 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 878750 1000)))

noncomputable def hp764243 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 878750 1000))) Bool.true 67108818 67108864

noncomputable def hp764244 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 878750 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 7260418749) (@Nat.cast Real Real.instNatCast 4194304)) Bool.false 7260418749 4194304

noncomputable def hp764245 := nat_lit 2117270904928852886268382881220550313570713

noncomputable def hp764246 := nat_lit 1223135762904738501681563293847792910336

noncomputable def hp764247 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 878750 1000)) Bool.false hp764245 hp764246 532055427535055933

noncomputable def hp764248 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 878750 4000) (Real.log (Enclosure.sfrac Bool.false 3088807250000 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1757500))))))

noncomputable def hp764249 := nat_lit 251517544055064373906250000000000000

noncomputable def hp764250 := nat_lit 1326126451386032348898515625000000000000

noncomputable def hp764251 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 878750 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp764248 (Enclosure.sfrac Bool.false 878750 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 878750 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp764249 hp764250)) Bool.false

noncomputable def hp764252 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 878750 1000) 878750 1000 3088807250000 16000000 1757500

noncomputable def hp764253 := hp764252 4000 2000 hp764249 hp764250 (@Eq.refl Real (Enclosure.sfrac Bool.false 878750 1000)) rfl rfl rfl rfl

noncomputable def hp764254 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp764248 (Enclosure.sfrac Bool.false 878750 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 878750 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp764249 hp764250) 124733057996416300509 72057594037927936

noncomputable def hp764255 := nat_lit 165411789447566631739717412595355493247711953125000000000000

noncomputable def hp764256 := @hp764254 532055427535055933 71368704000000000000000 hp764249 hp764250 0 1 hp764255 hp764245 hp764246 532055427535055933 71368704000000000000000

noncomputable def hp764257 := @Enclosure.Real.IsNear.subLit_ff_p (hp764248 (Enclosure.sfrac Bool.false 878750 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 878750 2000) (Real.log Real.pi)) 160975555653778486749 72057594037927936 44337565075373 17424000000000000000

noncomputable def hp764258 := nat_lit 33482775301542455992966447104

noncomputable def hp764259 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 878750 4000) (Real.log (Enclosure.sfrac Bool.false 3088807250000 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1757500))))))

noncomputable def hp764260 := @hp764259 (Enclosure.sfrac Bool.false 878750 2000) 192635861034193073629 72057594037927936 44337565075373 17424000000000000000 878750 2000 0

noncomputable def hp764261 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 878750 4000) (Real.log (Enclosure.sfrac Bool.false 3088807250000 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1757500))))) 192664147735261735485

noncomputable def hp764262 := nat_lit 433777395985893288305636166695124992

noncomputable def hp764263 := @hp764261 72057594037927936 8787513014639 3484800000000000000 883959408395683 2251799813685248 200000001089 8712000000000000000 hp764262 192635861034193073629 72057594037927936 44337565075373

noncomputable def hp764264 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 878750 4000) (Real.log (Enclosure.sfrac Bool.false 3088807250000 16000000)) 878750 4000 0 1 54811990820842599 4503599627370496

noncomputable def hp764265 := nat_lit 117707854002085578934321152

noncomputable def hp764266 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3088807250000) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp764265 hp617687

noncomputable def hp764267 := BSN.log_rat_reduce_isNear 3088807250000 16000000 17 6177614500000 4194304000000 103939491 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp764268 := nat_lit 146256606430164710833656980107465359256812384073454912891420618389836989698748588562011718750000000000000000000000000000000000000000

noncomputable def hp764269 := nat_lit 1822774555016695168112337213231321926511968484422766734681011496319515744095802307128906250000000000000000000000000000000000000000

noncomputable def hp764270 := nat_lit 869038392233996631677047955194410734288905236094883686922938911790795326232910156250000000000000000000000000000000000000000

noncomputable def hp764271 := BSN.log_dyadic_bound 991655250000 5185959250000 6 5 hp764268 268435456 87120000 hp764269 hp764270 103939491 6177614500000

noncomputable def hp764272 := hp764271 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp764273 := @BSN.binarySplit_of_base5 (BSN.artanhP 991655250000) (BSN.artanhQ 5185959250000) 0 5 hp764269 hp764268 hp764270 rfl rfl rfl

noncomputable def hp764274 := hp764267 rfl rfl rfl rfl (hp764272 (hp764273 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp764275 := @hp764264 12500018513 1089000000000000000 192664147735261735485 72057594037927936 8787513014639 3484800000000000000 (Enclosure.Real.IsNear.const Bool.false 878750 4000) (BSN.isNear_log_sfrac 3088807250000 16000000 54811990820842599 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp764266 1000001481040000 87120000000000000000000 54811990820842599 4503599627370496 12500018513 1089000000000000000 (hp764274 rfl rfl rfl) rfl)) rfl

noncomputable def hp764276 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1757500)))) 1 4

noncomputable def hp764277 := @hp764276 0 1 883959408395683 562949953421312 200000001089 2178000000000000000 883959408395683 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp764278 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1757500))) 884279719003555 562949953421312 1

noncomputable def hp764279 := @hp764278 2000000000000000 19092 33554432 1 10890000 29660755859773174317056 883959408395683 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp764280 := BSN.arctan_dyadic_bound_f 1000 1757500 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp764281 := hp764280 1 19092 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1757500) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1757500) 0 0 rfl)

noncomputable def hp764282 := hp764277 (hp764279 (hp764281 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp764283 := @hp764257 135013824915 268435456 10545 2147483648 hp764258 124733057996416300509 72057594037927936 532055427535055933 71368704000000000000000 (@hp764260 1 321951111307556973498000 160975555653778486749 72057594037927936 44337565075373 17424000000000000000 (@hp764263 17424000000000000000 hp764275 hp764282 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 878750 2000) rfl rfl)

noncomputable def hp764284 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 878750 2000) (Real.log Real.pi) 878750 2000 0 1 38410761 33554432

noncomputable def hp764285 := hp764283 (@hp764284 3 268435456 135013824915 268435456 10545 2147483648 (Enclosure.Real.IsNear.const Bool.false 878750 2000) hd4909 rfl) rfl

noncomputable def hp764286 := @hp764247 71368704000000000000000 7260418749 4194304 251 33554432 (@hp764251 hp764245 hp764246 532055427535055933 71368704000000000000000 (hp764253 rfl rfl rfl rfl rfl) (hp764256 (hp764285 rfl) (Enclosure.Real.IsNear.const Bool.true hp764249 hp764250) rfl rfl)) rfl

noncomputable def hp764287 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 7260418749) (@Nat.cast Real Real.instNatCast 4194304)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 707034793969071423488) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp764288 := BSN.sin_reduce_arg_pos_rat_q2 7260418749 4194304 226375608064910080 72057594037927936 275 707034793969071423488 604462909807314587353088 rfl rfl rfl rfl

noncomputable def hp764289 := BSN.cos_dyadic_bound_f 160761099 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp764290 := hp764289 1 67108818 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 160761099) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp764291 := hp764290 (@BSN.binarySplit_of_le (BSN.cosOddP 160761099) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp764292 := @BSN.cos_arg_round Bool.false 67108818 67108864 707034793969071423488 604462909807314587353088 160761099 137438953472 21801270 21780000 hp764291 rfl

noncomputable def hp764293 := hp764287 67108818 67108864 275 1000000000000000 21780000 10890000 hp764288 BSN.pi_near_15 hp764292 rfl rfl

noncomputable def hp764294 := @hp764244 251 33554432 Bool.true 67108818 67108864 1 10890000 hp764286 (Enclosure.sfrac_false_div 7260418749 4194304) (hp764293 rfl rfl) rfl

noncomputable def hp764295 := @hp764241 33554409 33554432 172934027 22837985280000 536870544 536870912 4066 536870912 (@hp764242 Bool.true 33554409 33554432 172934027 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 878750 1000)) (Enclosure.sfrac Bool.false 878750 1000)) (@hp764243 2766944432 365407764480000 33554409 33554432 172934027 22837985280000 (hp764294 rfl) rfl))

noncomputable def hp764296 := @hp764247 71368704000000000000000 929333599878 536870912 4003 536870912 (@hp764251 hp764245 hp764246 532055427535055933 71368704000000000000000 (hp764253 rfl rfl rfl rfl rfl) (hp764256 (hp764285 rfl) (Enclosure.Real.IsNear.const Bool.true hp764249 hp764250) rfl rfl)) rfl

noncomputable def hp764297 := hp764240 (BSN.cos_quad_nat3 487 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 318619986 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 878750 1000)) rfl rfl (hp764295 rfl) hp764296

noncomputable def hp764298 := nat_lit 210540302303962889756972104994153003442689267934557637606862368942516961

noncomputable def hp764299 := nat_lit 2275535100941148454722850965439893893983074282718864519850051693281

noncomputable def hp764300 := nat_lit 631616355841686786974006869280528130540279837655107475091547406724164321

noncomputable def hp764301 := BSN.cos_dyadic_bound_f 197076773 536870912 3 2 536870912 268435456 hp764298 hp708868 hp764299 hp764300 hp708870

noncomputable def hp764302 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 197076773) (BSN.cosEvenQ 536870912) 0 2 hp764298 hp708868 hp764299 rfl rfl rfl

noncomputable def hp764303 := hp764301 hp764299 501103399 rfl rfl rfl rfl rfl rfl rfl rfl (hp764302 rfl)

noncomputable def hp764304 := @BSN.binarySplit_of_base2 (BSN.cosOddP 197076773) (BSN.cosOddQ 536870912) 0 2 hp764300 hp708870 hp764299 rfl rfl rfl

noncomputable def hp764305 := nat_lit 3401520693163930034606631590575837940503798487895049674071737378245402880

noncomputable def hp764306 := nat_lit 183306074851953498708572165054116366824953310265921286917764150681856

noncomputable def hp764307 := nat_lit 8908447891308151689733745048955202227201755639127556702390016753446379776

noncomputable def hp764308 := BSN.sin_dyadic_bound_f 341112086 536870912 3 2 536870912 268435456 hp764305 hp708845 hp764306 hp764307 hp708848

noncomputable def hp764309 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 341112086) (BSN.sinEvenQ 536870912) 0 2 hp764305 hp708845 hp764306 rfl rfl rfl

noncomputable def hp764310 := hp764308 hp764306 318619986 rfl rfl rfl rfl rfl rfl rfl rfl (hp764309 rfl)

noncomputable def hp764311 := @BSN.binarySplit_of_base2 (BSN.sinOddP 341112086) (BSN.sinOddQ 536870912) 0 2 hp764307 hp708848 hp764306 rfl rfl rfl

noncomputable def hp764312 := hp764297 hd4911 hd4913 hd4915 hd4917 hd4918 (hp764303 (hp764304 rfl) rfl rfl rfl rfl) (hp764310 (hp764311 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764313 := hp764236 (BSN.cos_quad_nat1 201 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 450340526 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 878750 1000)) rfl rfl (hp764312 rfl rfl rfl rfl rfl) hp764296

noncomputable def hp764314 := nat_lit 3347288437998311217373648610595197065794996940290294327763165410502967296

noncomputable def hp764315 := nat_lit 574988952417795222118004873098975580973740981842813197366154682761216

noncomputable def hp764316 := nat_lit 10040715336090098061676709822039393246223043338907197356894763922143379456

noncomputable def hp764317 := BSN.cos_dyadic_bound_f 393511508 536870912 3 2 536870912 268435456 hp764314 hp708868 hp764315 hp764316 hp708870

noncomputable def hp764318 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 393511508) (BSN.cosEvenQ 536870912) 0 2 hp764314 hp708868 hp764315 rfl rfl rfl

noncomputable def hp764319 := hp764317 hp764315 398996543 rfl rfl rfl rfl rfl rfl rfl rfl (hp764318 rfl)

noncomputable def hp764320 := @BSN.binarySplit_of_base2 (BSN.cosOddP 393511508) (BSN.cosOddQ 536870912) 0 2 hp764316 hp708870 hp764315 rfl rfl rfl

noncomputable def hp764321 := nat_lit 20473135472389676886064796385279944176167419828088371572744457930884112640

noncomputable def hp764322 := nat_lit 6636888656920275896633465011790471976285395221287250561083618665554176

noncomputable def hp764323 := nat_lit 53609371274623663778718012541904573982953066052730317618184206817333207296

noncomputable def hp764324 := BSN.sin_dyadic_bound_f 534251274 536870912 3 2 536870912 268435456 hp764321 hp708845 hp764322 hp764323 hp708848

noncomputable def hp764325 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 534251274) (BSN.sinEvenQ 536870912) 0 2 hp764321 hp708845 hp764322 rfl rfl rfl

noncomputable def hp764326 := hp764324 hp764322 450340526 rfl rfl rfl rfl rfl rfl rfl rfl (hp764325 rfl)

noncomputable def hp764327 := @BSN.binarySplit_of_base2 (BSN.sinOddP 534251274) (BSN.sinOddQ 536870912) 0 2 hp764323 hp708848 hp764322 rfl rfl rfl

noncomputable def hp764328 := hp764313 hd4920 hd4922 hd4924 hd4926 hd4918 (hp764319 (hp764320 rfl) rfl rfl rfl rfl) (hp764326 (hp764327 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764329 := hp764232 (BSN.cos_quad_nat1 13 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 316230170 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 878750 1000)) rfl rfl (hp764328 rfl rfl rfl rfl rfl) hp764296

noncomputable def hp764330 := nat_lit 20983566868179234505642739955521657832949050803722185975164441819733569665

noncomputable def hp764331 := nat_lit 6971840132508810796742022639229344878878981010747848749219186844905601

noncomputable def hp764332 := nat_lit 54945673104064409440155308037331303956491233754778800084598611796791406721

noncomputable def hp764333 := BSN.sin_dyadic_bound_f 537549457 536870912 3 2 536870912 268435456 hp764330 hp708845 hp764331 hp764332 hp708848

noncomputable def hp764334 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 537549457) (BSN.sinEvenQ 536870912) 0 2 hp764330 hp708845 hp764331 rfl rfl rfl

noncomputable def hp764335 := hp764333 hp764331 452127553 rfl rfl rfl rfl rfl rfl rfl rfl (hp764334 rfl)

noncomputable def hp764336 := @BSN.binarySplit_of_base2 (BSN.sinOddP 537549457) (BSN.sinOddQ 536870912) 0 2 hp764332 hp708848 hp764331 rfl rfl rfl

noncomputable def hp764337 := nat_lit 3284849588931342119028045470695473952828682338200172033557587521055162305

noncomputable def hp764338 := nat_lit 170947677667188452846447664624384879183454875761171638581235507462081

noncomputable def hp764339 := nat_lit 8602900722389672959006939127031135158080251958820646762378835792894296001

noncomputable def hp764340 := BSN.sin_dyadic_bound_f 338148839 536870912 3 2 536870912 268435456 hp764337 hp708845 hp764338 hp764339 hp708848

noncomputable def hp764341 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 338148839) (BSN.sinEvenQ 536870912) 0 2 hp764337 hp708845 hp764338 rfl rfl rfl

noncomputable def hp764342 := hp764340 hp764338 316230170 rfl rfl rfl rfl rfl rfl rfl rfl (hp764341 rfl)

noncomputable def hp764343 := @BSN.binarySplit_of_base2 (BSN.sinOddP 338148839) (BSN.sinOddQ 536870912) 0 2 hp764339 hp708848 hp764338 rfl rfl rfl

noncomputable def hp764344 := hp764329 hd4928 hd4930 hd4932 hd4934 hd4918 (hp764335 (hp764336 rfl) rfl rfl rfl rfl) (hp764342 (hp764343 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764345 := hp764227 (BSN.cos_quad_nat3 127 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 159280754 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 878750 1000)) rfl rfl (hp764344 rfl rfl rfl rfl rfl) hp764296

noncomputable def hp764346 := nat_lit 1035504435755091276495491178454420809881855238623807887407982096587055360

noncomputable def hp764347 := nat_lit 16988972326266018723376004436877344411335819008782578777206259343616

noncomputable def hp764348 := nat_lit 2712007921022425102981686668135347176847240605069673104750504299974779136

noncomputable def hp764349 := BSN.sin_dyadic_bound_f 253379158 536870912 3 2 536870912 268435456 hp764346 hp708845 hp764347 hp764348 hp708848

noncomputable def hp764350 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 253379158) (BSN.sinEvenQ 536870912) 0 2 hp764346 hp708845 hp764347 rfl rfl rfl

noncomputable def hp764351 := hp764349 hp764347 244077002 rfl rfl rfl rfl rfl rfl rfl rfl (hp764350 rfl)

noncomputable def hp764352 := @BSN.binarySplit_of_base2 (BSN.sinOddP 253379158) (BSN.sinOddQ 536870912) 0 2 hp764348 hp708848 hp764347 rfl rfl rfl

noncomputable def hp764353 := nat_lit 683916055830508514651052284728881

noncomputable def hp764354 := BSN.sin_dyadic_bound_f 161715147 536870912 2 1 536870912 268435456 hp764353 hp708890 hp764353 hp764353 hp708891

noncomputable def hp764355 := @BSN.binarySplit_of_base (BSN.sinEvenP 161715147) (BSN.sinEvenQ 536870912) 0 1 hp764353 hp708890 hp764353 rfl rfl rfl

noncomputable def hp764356 := hp764354 hp764353 159280754 rfl rfl rfl rfl rfl rfl rfl rfl (hp764355 rfl)

noncomputable def hp764357 := @BSN.binarySplit_of_base (BSN.sinOddP 161715147) (BSN.sinOddQ 536870912) 0 1 hp764353 hp708891 hp764353 rfl rfl rfl

noncomputable def hp764358 := hp764345 hd4936 hd4938 hd4940 hd4942 hd4918 (hp764351 (hp764352 rfl) rfl rfl rfl rfl) (hp764356 (hp764357 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764359 := hp764222 (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 350529918 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 878750 1000)) rfl rfl (hp764358 rfl rfl rfl rfl rfl) hp764296

noncomputable def hp764360 := nat_lit 160976016040622149911819846476161

noncomputable def hp764361 := BSN.cos_dyadic_bound_f 112639391 536870912 2 1 536870912 268435456 hp764360 hp708767 hp764360 hp764360 hp708768

noncomputable def hp764362 := @BSN.binarySplit_of_base (BSN.cosEvenP 112639391) (BSN.cosEvenQ 536870912) 0 1 hp764360 hp708767 hp764360 rfl rfl rfl

noncomputable def hp764363 := hp764361 hp764360 525097915 rfl rfl rfl rfl rfl rfl rfl rfl (hp764362 rfl)

noncomputable def hp764364 := @BSN.binarySplit_of_base (BSN.cosOddP 112639391) (BSN.cosOddQ 536870912) 0 1 hp764360 hp708768 hp764360 rfl rfl rfl

noncomputable def hp764365 := nat_lit 5346764867519086776601549529025041332032687651801745054936057577173130625

noncomputable def hp764366 := nat_lit 452883010899629330345875051828535412198293386694587445342447562890625

noncomputable def hp764367 := nat_lit 14002698556722818348373974492600719193227765660664207716587691596542090625

noncomputable def hp764368 := BSN.sin_dyadic_bound_f 381942735 536870912 3 2 536870912 268435456 hp764365 hp708845 hp764366 hp764367 hp708848

noncomputable def hp764369 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 381942735) (BSN.sinEvenQ 536870912) 0 2 hp764365 hp708845 hp764366 rfl rfl rfl

noncomputable def hp764370 := hp764368 hp764366 350529918 rfl rfl rfl rfl rfl rfl rfl rfl (hp764369 rfl)

noncomputable def hp764371 := @BSN.binarySplit_of_base2 (BSN.sinOddP 381942735) (BSN.sinOddQ 536870912) 0 2 hp764367 hp708848 hp764366 rfl rfl rfl

noncomputable def hp764372 := hp764359 hd4944 hd4946 hd4961 hd4963 hd4918 (hp764363 (hp764364 rfl) rfl rfl rfl rfl) (hp764370 (hp764371 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764373 := @hp764217 213227 268435456 (hp764372 rfl rfl rfl rfl rfl) (hp764372 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp764374 := @hp764215 Bool.true 284162861 67108864 213227 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 878750 1000)) (Enclosure.sfrac Bool.false 878750 1000) 11) hp764373

noncomputable def hp764375 := @Enclosure.Real.IsNear.mulLit_tf hp764206 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1))) 19514549 67108864 1

noncomputable def hp764376 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp764205 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp764377 := @hp764376 1 1 0 1 19514549 67108864 1 67108864 19514549 67108864 1

noncomputable def hp764378 := @Enclosure.Real.IsNear.of_eq (hp764205 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp764379 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 878750 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp764380 := @hp764378 (@Inv.inv Real Real.instInv (Real.sqrt hp764207)) Bool.false 19514549 67108864 1 67108864 (hp764379 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 878750 1000) 878750 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 878750 1000))))

noncomputable def hp764381 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp764207)) Bool.false 19514549 67108864 1 67108864 19514549 67108864

noncomputable def hp764382 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp764207) Bool.false 230781637 67108864 7 67108864 230781637 67108864 7 67108864

noncomputable def hp764383 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 878750 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp764384 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 878750 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp764385 := @hp764384 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 878750 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 37542685105

noncomputable def hp764386 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 878750 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 878750 1000 0

noncomputable def hp764387 := @hp764386 1 10680707 67108864 1 67108864 37542685105 268435456 3515 268435456 (Enclosure.Real.IsNear.const Bool.false 878750 1000) hd4949

noncomputable def hp764388 := @hp764385 268435456 3515 268435456 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 878750 1000) 878750 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 878750 1000))) (hp764387 rfl)

noncomputable def hp764389 := @hp764383 37542685105 268435456 3515 268435456 396819127 396819165 33554432 hp764388 rfl rfl rfl

noncomputable def hp764390 := @Enclosure.Real.IsNear.recentre' hp764207 Bool.false 793638292 67108864 38 67108864 198409573 16777216 19 33554432 (hp764389 rfl rfl rfl)

noncomputable def hp764391 := @Enclosure.Real.IsNear.sqrt_image hp764207 198409573 16777216 19 33554432 115390815 115390822 33554432 (hp764390 rfl) rfl rfl

noncomputable def hp764392 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp764207) 230781637 67108864 7 67108864 9757274 9757275 33554432 (hp764382 (hp764391 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp764393 := @hp764377 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp764380 (@hp764381 1 67108864 (hp764392 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp764394 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp764395 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp764396 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1))) (hp764394 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764395 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp764397 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 878750 1000) 878750 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 878750 1000)) rfl

noncomputable def hp764398 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp764399 := @hp764398 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764395 (Enclosure.sfrac Bool.false 1 16)))) 145788381

noncomputable def hp764400 := @hp764399 67108864 1163 67108864 4565393 16777216 436391179 45675970560000 665581254098733 1125899906842624 19519131618164969 766315624094760960000

noncomputable def hp764401 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp764402 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1)))) 7722837

noncomputable def hp764403 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp764404 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 43543093) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false

noncomputable def hp764405 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1))) Bool.false 12256291108493916000335

noncomputable def hp764406 := nat_lit 512735433009953234972679621

noncomputable def hp764407 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp764408 := @Enclosure.Real.IsNear.subLit_ff_p hp764207 (Enclosure.sfrac Bool.false 11 1) 198409573 16777216 19 33554432 11 1 0

noncomputable def hp764409 := @hp764407 500000000000000 13860197 16777216 19 33554432 12256291108493916000335 2361183241434822606848 hp764406 hp682805 hd4948 (@hp764408 1 13860197 13860197 16777216 19 33554432 (hp764390 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp764410 := @hp764404 43543093 8388608 15 4194304 Bool.false 30891348 67108864 1 10890000 (@hp764405 2361183241434822606848 hp764406 hp682805 43543093 8388608 15 4194304 (hp764409 rfl) rfl) (Enclosure.sfrac_false_div 43543093 8388608)

noncomputable def hp764411 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 43543093) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 578292326644975639986176) (@Nat.cast Real Real.instNatCast hp630689)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp764412 := BSN.sin_reduce_arg_pos_rat_q3 43543093 8388608 226375608064910080 72057594037927936 0 578292326644975639986176 hp630689 rfl rfl rfl rfl

noncomputable def hp764413 := nat_lit 18682305284694366080836010021982823447783696

noncomputable def hp764414 := BSN.sin_dyadic_bound_f 65744225894 137438953472 2 1 67108864 21801270 hp764413 hp749778 hp764413 hp764413 hp749779

noncomputable def hp764415 := @BSN.binarySplit_of_base (BSN.sinEvenP 65744225894) (BSN.sinEvenQ 137438953472) 0 1 hp764413 hp749778 hp764413 rfl rfl rfl

noncomputable def hp764416 := hp764414 hp764413 30891348 rfl rfl rfl rfl rfl rfl rfl rfl (hp764415 rfl)

noncomputable def hp764417 := @BSN.binarySplit_of_base (BSN.sinOddP 65744225894) (BSN.sinOddQ 137438953472) 0 1 hp764413 hp749779 hp764413 rfl rfl rfl

noncomputable def hp764418 := @BSN.sin_arg_round Bool.false 30891348 67108864 578292326644975639986176 hp630689 65744225894 137438953472 21801270 21780000 (hp764416 (hp764417 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764419 := hp764411 30891348 67108864 0 1000000000000000 21780000 10890000 hp764412 BSN.pi_near_15 hp764418 rfl rfl

noncomputable def hp764420 := @hp764402 16777216 10471519 2854748160000 72893609 72894772 33554432 (@hp764403 30891348 67108864 167544304 45675970560000 7722837 16777216 10471519 2854748160000 (hp764410 (hp764419 rfl rfl) rfl rfl) rfl)

noncomputable def hp764421 := @hp764401 Bool.false 145788381 67108864 1163 67108864 145788381 67108864 1163 67108864 (hp764420 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp764422 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764395 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp764423 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764395 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 86919551)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp764424 := nat_lit 51308247365022256577873100245

noncomputable def hp764425 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764395 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp764424

noncomputable def hp764426 := nat_lit 45631012385291697017919272577430659

noncomputable def hp764427 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764395 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp764428 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp764429 := @hp764428 (Enclosure.sfrac Bool.false 1 16) 40430457992743 281474976710656 1690909541 1125899906842624 1 16 0

noncomputable def hp764430 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1)) 192105060878809

noncomputable def hp764431 := @hp764430 281474976710656 1053375333 1125899906842624 13860197 16777216 19 33554432 678310526723175743488 40430457992743 281474976710656 1690909541

noncomputable def hp764432 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1)) 13860197 16777216 19

noncomputable def hp764433 := @hp764432 33554432 13860197 16777216 19 33554432 192105060878809 281474976710656 1053375333 1125899906842624 (@hp764408 1 13860197 13860197 16777216 19 33554432 (hp764390 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp764434 := hp764433 (@hp764408 1 13860197 13860197 16777216 19 33554432 (hp764390 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp764435 := @hp764431 1125899906842624 (hp764434 rfl) (@hp764408 1 13860197 13860197 16777216 19 33554432 (hp764390 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp764436 := @hp764427 500000000000000 58022644037159 281474976710656 1690909541 1125899906842624 hp764424 hp631146 hp764426 hp682143 hd4948 (@hp764429 1 928362304594544 58022644037159 281474976710656 1690909541 1125899906842624 (hp764435 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp764437 := @hp764423 86919551 67108864 635 67108864 Bool.false 9130786 33554432 1 10890000 (@hp764425 hp631146 hp764426 hp682143 86919551 67108864 635 67108864 (hp764436 rfl) rfl) (Enclosure.sfrac_true_div 86919551 67108864)

noncomputable def hp764438 := nat_lit 469420193373902084515817774480716018200371113113515230712564319417477482250984820241483297400446062081

noncomputable def hp764439 := nat_lit 185955783733263846736740501665390834468068023430159372987847445057446521669784202530573954649601

noncomputable def hp764440 := nat_lit 2844639963947397079230654470154125073936920326495116297488960931131569840359593345104273710681278713345

noncomputable def hp764441 := BSN.cos_dyadic_bound_f 86919551 67108864 4 3 33554432 10890000 hp764438 hp745658 hp764439 hp764440 hp745661

noncomputable def hp764442 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 86919551) (BSN.cosEvenQ 67108864) 0 3 hp764438 hp745658 hp764439 rfl rfl rfl

noncomputable def hp764443 := hp764441 hp764439 9130786 rfl rfl rfl rfl rfl rfl rfl rfl (hp764442 rfl)

noncomputable def hp764444 := @BSN.binarySplit_of_base3 (BSN.cosOddP 86919551) (BSN.cosOddQ 67108864) 0 3 hp764440 hp745661 hp764439 rfl rfl rfl

noncomputable def hp764445 := hp764437 (BSN.cos_neg_of_bound 86919551 67108864 Bool.false 9130786 33554432 1 10890000 (hp764443 (hp764444 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp764446 := hp764400 hp764421 (@hp764422 9130786 33554432 6982258864 730815528960000 4565393 16777216 436391179 45675970560000 (hp764445 rfl) rfl)

noncomputable def hp764447 := @hp764375 67108864 665581254098733 1125899906842624 19519131618164969 766315624094760960000 12988517996591175966417 75557863725914323419136 462254643830705631451 hp764203 (hp764393 rfl) (@hp764396 Bool.false 665581254098733 1125899906842624 19519131618164969 766315624094760960000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764207 (Enclosure.sfrac Bool.false 11 1)) (hp764397 rfl (hp764210 rfl rfl))) (hp764446 rfl))

noncomputable def hp764448 := @hp764204 49977158152574219333851 hp764203 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 878750 1000))) (@hp764209 49977158152574219333851 hp764203 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 878750 1000) 11 (hp764210 rfl rfl)) (@hp764213 49977158152574219333851 hp764203 hp764374 (hp764447 rfl) rfl rfl))

theorem hd5066 : hp764202 hp764203 := hp764448

noncomputable def hp764449 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 880021 1000)) Bool.false 34941177192362437896801 9444732965739290427392 1833655035804068967707

noncomputable def hp764450 := nat_lit 2285625377708908283428864

noncomputable def hp764451 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 880021 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 880021 1000)) Bool.false 34941177192362437896801 9444732965739290427392

noncomputable def hp764452 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 880021 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp764453 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp764452 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp764454 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 880021 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp764455 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 880021 1000)) (Enclosure.sfrac Bool.false 880021 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp764453 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp764456 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 880021 1000)) hp764455 Bool.false 34941177192362437896801 9444732965739290427392

noncomputable def hp764457 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 880021 1000) 880021 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 880021 1000)) rfl

noncomputable def hp764458 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 880021 1000)) (Enclosure.sfrac Bool.false 880021 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp764453 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp764459 := nat_lit 9379450832808610734099457376256

noncomputable def hp764460 := @hp764458 946007447 268435456 106767 134217728 1656499178308420364897 9444732965739290427392 15494586076839114011 hp764450 hp764459 34941177192362437896801 9444732965739290427392

noncomputable def hp764461 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 880021 1000)) (Enclosure.sfrac Bool.false 880021 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 880021 1000)) (Enclosure.sfrac Bool.false 880021 1000) 11)

noncomputable def hp764462 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 880021 1000)) (Enclosure.sfrac Bool.false 880021 1000) 11) hp764461

noncomputable def hp764463 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 880021 1000)) (Enclosure.sfrac Bool.false 880021 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 880021 1000)) (Enclosure.sfrac Bool.false 880021 1000) 11)

noncomputable def hp764464 := @hp764463 946007447 536870912 213534 536870912 946007447 536870912 213534 536870912 1015767761659363328 946007447 268435456

noncomputable def hp764465 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 880021 1000)) (Enclosure.sfrac Bool.false 880021 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp764466 := hp764465 BSN.quadSignPos 9 10 11 880021 1000 185 239 536870912 268435456 9007199254740992

noncomputable def hp764467 := hp764466 Bool.false 931019495531 4010 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp764468 := hp764467 Bool.false 1021867890 183313 Bool.true 841257300 Bool.true 332281922 28296951008113761 1 Bool.false 536866969

noncomputable def hp764469 := hp764468 Bool.true Bool.false 311470238 Bool.false Bool.false 946007447 213534 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 185 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536866969 536870912) BSN.abs_quadSignPos

noncomputable def hp764470 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 880021 1000)) (Enclosure.sfrac Bool.false 880021 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp764471 := hp764470 BSN.quadSignNeg 7 8 9 880021 1000 60 126 536870912 268435456 9007199254740992

noncomputable def hp764472 := hp764471 Bool.false 931019495531 4010 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp764473 := hp764472 Bool.false 1025355211 149711 Bool.true 829732182 Bool.true 818438930 28296951008113761 1 Bool.false 13581225

noncomputable def hp764474 := hp764473 Bool.false Bool.false 24867026 Bool.true Bool.false 1021867890 183313 BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 13581225 536870912) BSN.abs_quadSignNeg

noncomputable def hp764475 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 880021 1000)) (Enclosure.sfrac Bool.false 880021 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp764476 := hp764475 BSN.quadSignNeg 5 6 7 880021 1000 100 13 536870912 268435456 9007199254740992

noncomputable def hp764477 := hp764476 Bool.false 931019495531 4010 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp764478 := hp764477 Bool.false 1010892837 111252 Bool.false 157500023 Bool.false 696227562 28296951008113761 1 Bool.false 513933502

noncomputable def hp764479 := hp764478 Bool.false Bool.false 516847770 Bool.true Bool.false 1025355211 149711 BSN.abs_quadSignPos (BSN.cos_quad_nat0 100 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 513933502 536870912) BSN.abs_quadSignNeg

noncomputable def hp764480 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 880021 1000)) (Enclosure.sfrac Bool.false 880021 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp764481 := hp764480 BSN.quadSignNeg 3 4 5 880021 1000 327 202 536870912 268435456 9007199254740992

noncomputable def hp764482 := hp764481 Bool.false 931019495531 4010 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp764483 := hp764482 Bool.false 1081268102 65755 Bool.false 290136441 Bool.false 278611323 28296951008113761 1 Bool.false 276218603

noncomputable def hp764484 := hp764483 Bool.false Bool.false 466185643 Bool.true Bool.false 1010892837 111252 BSN.abs_quadSignPos (BSN.cos_quad_nat3 327 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 276218603 536870912) BSN.abs_quadSignNeg

noncomputable def hp764485 := hp764480 BSN.quadSignPos 1 2 3 880021 1000 715 488 536870912 268435456 9007199254740992

noncomputable def hp764486 := hp764485 Bool.false 931019495531 4010 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp764487 := hp764486 Bool.false 536870896 4066 Bool.false 566679648 Bool.false 434040590 28296951008113761 1 Bool.false 467162580

noncomputable def hp764488 := hp764487 Bool.false Bool.false 370768642 Bool.false Bool.false 1081268102 65755 BSN.abs_quadSignPos (BSN.cos_quad_nat3 715 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 467162580 536870912) BSN.abs_quadSignPos

noncomputable def hp764489 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 880021 1000)) (Enclosure.sfrac Bool.false 880021 1000) 1) Bool.false

noncomputable def hp764490 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 880021 1000)) (Enclosure.sfrac Bool.false 880021 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 880021 1000)))

noncomputable def hp764491 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 880021 1000))) Bool.false 67108862 67108864

noncomputable def hp764492 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 880021 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 116377436941) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 116377436941 67108864

noncomputable def hp764493 := nat_lit 26117993395563937746550529437477052132458886102524648062839

noncomputable def hp764494 := nat_lit 15060899370183448328652579592372632660487588780651315200

noncomputable def hp764495 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 880021 1000)) Bool.false hp764493 hp764494 14800628006588149787

noncomputable def hp764496 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 880021 4000) (Real.log (Enclosure.sfrac Bool.false 3097748841764 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1760042))))))

noncomputable def hp764497 := nat_lit 253341753335022176612841176368480000

noncomputable def hp764498 := nat_lit 1337676580187214654729340032479412828480

noncomputable def hp764499 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 880021 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp764496 (Enclosure.sfrac Bool.false 880021 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 880021 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp764497 hp764498)) Bool.false

noncomputable def hp764500 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 880021 1000) 880021 1000 3097748841764 16000000 1760042

noncomputable def hp764501 := hp764500 4000 2000 hp764497 hp764498 (@Eq.refl Real (Enclosure.sfrac Bool.false 880021 1000)) rfl rfl rfl rfl

noncomputable def hp764502 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp764496 (Enclosure.sfrac Bool.false 880021 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 880021 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp764497 hp764498) 6247966753047743329751 3602879701896396800

noncomputable def hp764503 := nat_lit 8357757886580460078896169419992656682386843552807887380108480

noncomputable def hp764504 := @hp764502 14800628006588149787 hp740132 hp764497 hp764498 0 1 hp764503 hp764493 hp764494 14800628006588149787 hp740132

noncomputable def hp764505 := @Enclosure.Real.IsNear.subLit_ff_p (hp764496 (Enclosure.sfrac Bool.false 880021 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 880021 2000) (Real.log Real.pi)) 40313563219272721911091 18014398509481984000 1233364310263697 484000000000000000000

noncomputable def hp764506 := nat_lit 2096469755534012963115835064320000

noncomputable def hp764507 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 880021 4000) (Real.log (Enclosure.sfrac Bool.false 3097748841764 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1760042))))))

noncomputable def hp764508 := @hp764507 (Enclosure.sfrac Bool.false 880021 2000) 48240087714629144431923 18014398509481984000 1233364310263697 484000000000000000000 880021 2000 0

noncomputable def hp764509 := nat_lit 80627126438545443822182000

noncomputable def hp764510 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 880021 4000) (Real.log (Enclosure.sfrac Bool.false 3097748841764 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1760042))))) 48247159393654406279923

noncomputable def hp764511 := nat_lit 108627020527961928422428394594085371904

noncomputable def hp764512 := @hp764510 18014398509481984000 11000278791828773 4356000000000000000000 883959878157731 2251799813685248 200000001089 8712000000000000000 hp764511 48240087714629144431923 18014398509481984000 1233364310263697

noncomputable def hp764513 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 880021 4000) (Real.log (Enclosure.sfrac Bool.false 3097748841764 16000000)) 880021 4000 0 1 54825009168706663 4503599627370496

noncomputable def hp764514 := nat_lit 117735810691247632101146624

noncomputable def hp764515 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3097748841764) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp764514 hp617687

noncomputable def hp764516 := BSN.log_rat_reduce_isNear 3097748841764 16000000 17 6195497683528 4194304000000 104715445 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp764517 := nat_lit 148798007907265956837334050691427939649501420147074709468853724202055864495940455106506316252417336739624670193907030300912144875520

noncomputable def hp764518 := nat_lit 1882169401015544696564630462498572465008362024904713570346976126072909874809701385416199071365358759274224795459468798034946555904

noncomputable def hp764519 := nat_lit 950655327064017448605681695911673724056616651552021118204096473094113139765051391386626862800633964288564122883298631352320

noncomputable def hp764520 := BSN.log_dyadic_bound 1000596841764 5194900841764 6 5 hp764517 268435456 87120000 hp764518 hp764519 104715445 6195497683528

noncomputable def hp764521 := hp764520 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp764522 := @BSN.binarySplit_of_base5 (BSN.artanhP 1000596841764) (BSN.artanhQ 5194900841764) 0 5 hp764518 hp764517 hp764519 rfl rfl rfl

noncomputable def hp764523 := hp764516 rfl rfl rfl rfl (hp764521 (hp764522 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp764524 := @hp764513 12500018513 1089000000000000000 48247159393654406279923 18014398509481984000 11000278791828773 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 880021 4000) (BSN.isNear_log_sfrac 3097748841764 16000000 54825009168706663 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp764515 1000001481040000 87120000000000000000000 54825009168706663 4503599627370496 12500018513 1089000000000000000 (hp764523 rfl rfl rfl) rfl)) rfl

noncomputable def hp764525 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1760042)))) 1 4

noncomputable def hp764526 := @hp764525 0 1 883959878157731 562949953421312 200000001089 2178000000000000000 883959878157731 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp764527 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1760042))) 884279719003555 562949953421312 1

noncomputable def hp764528 := @hp764527 2000000000000000 19064 33554432 1 10890000 29660771622371870113792 883959878157731 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp764529 := BSN.arctan_dyadic_bound_f 1000 1760042 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp764530 := hp764529 1 19064 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1760042) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1760042) 0 0 rfl)

noncomputable def hp764531 := hp764526 (hp764528 (hp764530 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp764532 := @hp764505 33802276305981 67108864000 2640063 536870912000 hp764506 6247966753047743329751 3602879701896396800 14800628006588149787 hp740132 (@hp764508 1 hp764509 40313563219272721911091 18014398509481984000 1233364310263697 484000000000000000000 (@hp764512 484000000000000000000 hp764524 hp764531 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 880021 2000) rfl rfl)

noncomputable def hp764533 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 880021 2000) (Real.log Real.pi) 880021 2000 0 1 38410761 33554432

noncomputable def hp764534 := hp764532 (@hp764533 3 268435456 33802276305981 67108864000 2640063 536870912000 (Enclosure.Real.IsNear.const Bool.false 880021 2000) hd4909 rfl) rfl

noncomputable def hp764535 := @hp764495 hp740132 116377436941 67108864 251 33554432 (@hp764499 hp764493 hp764494 14800628006588149787 hp740132 (hp764501 rfl rfl rfl rfl rfl) (hp764504 (hp764534 rfl) (Enclosure.Real.IsNear.const Bool.true hp764497 hp764498) rfl rfl)) rfl

noncomputable def hp764536 := nat_lit 15189898854746703047688192

noncomputable def hp764537 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 116377436941) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp764536) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp764538 := BSN.sin_reduce_arg_pos_rat_q3 116377436941 67108864 226375608064910080 72057594037927936 275 hp764536 hp617687 rfl rfl rfl rfl

noncomputable def hp764539 := nat_lit 14373133107595712804622514319089456756465730188429531630955584869929633557853792333811648131030705340269275081405135450292890776573914631671281

noncomputable def hp764540 := nat_lit 10235309457902865431605418108756066155488344144809488143718250055661187177461275628560209546967164741889406142395913895481034851418410481

noncomputable def hp764541 := nat_lit 71776408436960859843712355332249053680765661373623090711098674706834137854603958496927658362676682699536164740079294349954418475593029803347441

noncomputable def hp764542 := BSN.sin_dyadic_bound_f 215861445763 137438953472 4 3 67108864 21801270 hp764539 hp737934 hp764540 hp764541 hp737937

noncomputable def hp764543 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215861445763) (BSN.sinEvenQ 137438953472) 0 3 hp764539 hp737934 hp764540 rfl rfl rfl

noncomputable def hp764544 := hp764542 hp764540 67108862 rfl rfl rfl rfl rfl rfl rfl rfl (hp764543 rfl)

noncomputable def hp764545 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215861445763) (BSN.sinOddQ 137438953472) 0 3 hp764541 hp737937 hp764540 rfl rfl rfl

noncomputable def hp764546 := @BSN.sin_arg_round Bool.false 67108862 67108864 hp764536 hp617687 215861445763 137438953472 21801270 21780000 (hp764544 (hp764545 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764547 := hp764537 67108862 67108864 275 1000000000000000 21780000 10890000 hp764538 BSN.pi_near_15 hp764546 rfl rfl

noncomputable def hp764548 := @hp764492 251 33554432 Bool.false 67108862 67108864 1 10890000 hp764535 (Enclosure.sfrac_false_div 116377436941 67108864) (hp764547 rfl rfl) rfl

noncomputable def hp764549 := @hp764489 33554431 33554432 172934027 22837985280000 536870896 536870912 4066 536870912 (@hp764490 Bool.false 33554431 33554432 172934027 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 880021 1000)) (Enclosure.sfrac Bool.false 880021 1000)) (@hp764491 2766944432 365407764480000 33554431 33554432 172934027 22837985280000 (hp764548 rfl) rfl))

noncomputable def hp764550 := @hp764495 hp740132 931019495531 536870912 4010 536870912 (@hp764499 hp764493 hp764494 14800628006588149787 hp740132 (hp764501 rfl rfl rfl rfl rfl) (hp764504 (hp764534 rfl) (Enclosure.Real.IsNear.const Bool.true hp764497 hp764498) rfl rfl)) rfl

noncomputable def hp764551 := hp764488 (BSN.cos_quad_nat0 488 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 370768642 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 880021 1000)) rfl rfl (hp764549 rfl) hp764550

noncomputable def hp764552 := nat_lit 25917313208808265649837127157028894162100414894992305665051780634147553280

noncomputable def hp764553 := nat_lit 10634104499084407953701104930005098222405266681319702560557952879558656

noncomputable def hp764554 := nat_lit 67861460330070749565267436003284238360760049531305330556704236403819544576

noncomputable def hp764555 := BSN.sin_dyadic_bound_f 566679648 536870912 3 2 536870912 268435456 hp764552 hp708845 hp764553 hp764554 hp708848

noncomputable def hp764556 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 566679648) (BSN.sinEvenQ 536870912) 0 2 hp764552 hp708845 hp764553 rfl rfl rfl

noncomputable def hp764557 := hp764555 hp764553 467162580 rfl rfl rfl rfl rfl rfl rfl rfl (hp764556 rfl)

noncomputable def hp764558 := @BSN.binarySplit_of_base2 (BSN.sinOddP 566679648) (BSN.sinOddQ 536870912) 0 2 hp764554 hp708848 hp764553 rfl rfl rfl

noncomputable def hp764559 := nat_lit 4954736726851655100414231126789274273781236550799581347490980832432800000

noncomputable def hp764560 := nat_lit 1259629320633326255400830592863903936121823693126591987661232100000000

noncomputable def hp764561 := nat_lit 14861690921913698648731891719182095013471466005012490858497620033098400000

noncomputable def hp764562 := BSN.cos_dyadic_bound_f 434040590 536870912 3 2 536870912 268435456 hp764559 hp708868 hp764560 hp764561 hp708870

noncomputable def hp764563 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 434040590) (BSN.cosEvenQ 536870912) 0 2 hp764559 hp708868 hp764560 rfl rfl rfl

noncomputable def hp764564 := hp764562 hp764560 370768642 rfl rfl rfl rfl rfl rfl rfl rfl (hp764563 rfl)

noncomputable def hp764565 := @BSN.binarySplit_of_base2 (BSN.cosOddP 434040590) (BSN.cosOddQ 536870912) 0 2 hp764561 hp708870 hp764560 rfl rfl rfl

noncomputable def hp764566 := hp764551 hd4911 hd4913 hd4915 hd4917 hd4918 (hp764557 (hp764558 rfl) rfl rfl rfl rfl) (hp764564 (hp764565 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764567 := hp764484 (BSN.cos_quad_nat2 202 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 466185643 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 880021 1000)) rfl rfl (hp764566 rfl rfl rfl rfl rfl) hp764550

noncomputable def hp764568 := nat_lit 1780256791392885725227632425391597995978588976689503282278902393982444225

noncomputable def hp764569 := nat_lit 50213238870807052135454780226558282042365598052408937377493558256321

noncomputable def hp764570 := nat_lit 4662496013166052735607008473048104133201569204170899934355656994669224641

noncomputable def hp764571 := BSN.sin_dyadic_bound_f 290136441 536870912 3 2 536870912 268435456 hp764568 hp708845 hp764569 hp764570 hp708848

noncomputable def hp764572 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 290136441) (BSN.sinEvenQ 536870912) 0 2 hp764568 hp708845 hp764569 rfl rfl rfl

noncomputable def hp764573 := hp764571 hp764569 276218603 rfl rfl rfl rfl rfl rfl rfl rfl (hp764572 rfl)

noncomputable def hp764574 := @BSN.binarySplit_of_base2 (BSN.sinOddP 290136441) (BSN.sinOddQ 536870912) 0 2 hp764570 hp708848 hp764569 rfl rfl rfl

noncomputable def hp764575 := nat_lit 841012746455776777726749944288300458785361703953700526873791000522209761

noncomputable def hp764576 := nat_lit 36306977856577141513721427334072633463922164597998047982319160474081

noncomputable def hp764577 := nat_lit 2522965625411617178897222390010233231089157267531905584525408363245681121

noncomputable def hp764578 := BSN.cos_dyadic_bound_f 278611323 536870912 3 2 536870912 268435456 hp764575 hp708868 hp764576 hp764577 hp708870

noncomputable def hp764579 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 278611323) (BSN.cosEvenQ 536870912) 0 2 hp764575 hp708868 hp764576 rfl rfl rfl

noncomputable def hp764580 := hp764578 hp764576 466185643 rfl rfl rfl rfl rfl rfl rfl rfl (hp764579 rfl)

noncomputable def hp764581 := @BSN.binarySplit_of_base2 (BSN.cosOddP 278611323) (BSN.cosOddQ 536870912) 0 2 hp764577 hp708870 hp764576 rfl rfl rfl

noncomputable def hp764582 := hp764567 hd4920 hd4922 hd4924 hd4926 hd4918 (hp764573 (hp764574 rfl) rfl rfl rfl rfl) (hp764580 (hp764581 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764583 := hp764479 (BSN.cos_quad_nat1 13 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 516847770 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 880021 1000)) rfl rfl (hp764582 rfl rfl rfl rfl rfl) hp764550

noncomputable def hp764584 := nat_lit 85884181231708948940828418489420182611896862003366462478602992512688961

noncomputable def hp764585 := nat_lit 378656112940436124317675587585862546655063052906892255141530985281

noncomputable def hp764586 := nat_lit 257651786382900965950236620117085376110597275883993573651298694476096321

noncomputable def hp764587 := BSN.cos_dyadic_bound_f 157500023 536870912 3 2 536870912 268435456 hp764584 hp708868 hp764585 hp764586 hp708870

noncomputable def hp764588 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 157500023) (BSN.cosEvenQ 536870912) 0 2 hp764584 hp708868 hp764585 rfl rfl rfl

noncomputable def hp764589 := hp764587 hp764585 513933502 rfl rfl rfl rfl rfl rfl rfl rfl (hp764588 rfl)

noncomputable def hp764590 := @BSN.binarySplit_of_base2 (BSN.cosOddP 157500023) (BSN.cosOddQ 536870912) 0 2 hp764586 hp708870 hp764585 rfl rfl rfl

noncomputable def hp764591 := nat_lit 84230422299861200391736930574817216806348415599292640780298912139549030358287231629006366088564507190213147693056

noncomputable def hp764592 := nat_lit 12972227119110710701068768398863522315385767386477680641371473354087059541539504037972515655072351190061056

noncomputable def hp764593 := nat_lit 420908787284023663034860006413472401485927593884908143315624115196367039698589626077471083814754753183262385442816

noncomputable def hp764594 := BSN.sin_dyadic_bound_f 696227562 536870912 4 3 536870912 268435456 hp764591 hp642702 hp764592 hp764593 hp642705

noncomputable def hp764595 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 696227562) (BSN.sinEvenQ 536870912) 0 3 hp764591 hp642702 hp764592 rfl rfl rfl

noncomputable def hp764596 := hp764594 hp764592 516847770 rfl rfl rfl rfl rfl rfl rfl rfl (hp764595 rfl)

noncomputable def hp764597 := @BSN.binarySplit_of_base3 (BSN.sinOddP 696227562) (BSN.sinOddQ 536870912) 0 3 hp764593 hp642705 hp764592 rfl rfl rfl

noncomputable def hp764598 := hp764583 hd4928 hd4930 hd4932 hd4934 hd4918 (hp764589 (hp764590 rfl) rfl rfl rfl rfl) (hp764596 (hp764597 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764599 := hp764474 (BSN.cos_quad_nat2 126 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 24867026 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 880021 1000)) rfl rfl (hp764598 rfl rfl rfl rfl rfl) hp764550

noncomputable def hp764600 := nat_lit 65510288434344948195764066741293548259259250588792955528503230029865930874437557169504556597338166923475706515456

noncomputable def hp764601 := nat_lit 106476856148665469012572193001823247399182451420248647233357404233675920860841306849174631060358844979941376

noncomputable def hp764602 := nat_lit 396531820721711470094842240777452019052408938615101236623403997011911173447777383468776313157914585291131498598400

noncomputable def hp764603 := BSN.cos_dyadic_bound_f 829732182 536870912 4 3 536870912 268435456 hp764600 hp716712 hp764601 hp764602 hp716714

noncomputable def hp764604 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 829732182) (BSN.cosEvenQ 536870912) 0 3 hp764600 hp716712 hp764601 rfl rfl rfl

noncomputable def hp764605 := hp764603 hp764601 13581225 rfl rfl rfl rfl rfl rfl rfl rfl (hp764604 rfl)

noncomputable def hp764606 := @BSN.binarySplit_of_base3 (BSN.cosOddP 829732182) (BSN.cosOddQ 536870912) 0 3 hp764602 hp716714 hp764601 rfl rfl rfl

noncomputable def hp764607 := nat_lit 62004670349521810516656371028474507344426479408173434871139450268318587299354185930382875570369391024883264000000

noncomputable def hp764608 := nat_lit 90330694028110344535083587391914679335634272551379543861928021959302243443660493605380053414801000000000000

noncomputable def hp764609 := nat_lit 375357599646684709195379081080263791770477334556340874246912756420304485250920800649216120407921648332759001600000

noncomputable def hp764610 := BSN.cos_dyadic_bound_f 818438930 536870912 4 3 536870912 268435456 hp764607 hp716712 hp764608 hp764609 hp716714

noncomputable def hp764611 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 818438930) (BSN.cosEvenQ 536870912) 0 3 hp764607 hp716712 hp764608 rfl rfl rfl

noncomputable def hp764612 := hp764610 hp764608 24867026 rfl rfl rfl rfl rfl rfl rfl rfl (hp764611 rfl)

noncomputable def hp764613 := @BSN.binarySplit_of_base3 (BSN.cosOddP 818438930) (BSN.cosOddQ 536870912) 0 3 hp764609 hp716714 hp764608 rfl rfl rfl

noncomputable def hp764614 := hp764599 hd4936 hd4938 hd4940 hd4942 hd4918 (hp764605 (hp764606 rfl) rfl rfl rfl rfl) (hp764612 (hp764613 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764615 := hp764469 (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 311470238 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 880021 1000)) rfl rfl (hp764614 rfl rfl rfl rfl rfl) hp764550

noncomputable def hp764616 := nat_lit 179737514138106488913400211663780588273694370197672976209712501623052541382814509209256957508834849357824000000000

noncomputable def hp764617 := nat_lit 125645271756345980309970703152986910043679122761047508219259294213438827611229361521000000000000000000000000

noncomputable def hp764618 := nat_lit 897581682569478448100441751445143639571602191884087173951121925681703234848847827436449264472327846789120000000000

noncomputable def hp764619 := BSN.sin_dyadic_bound_f 841257300 536870912 4 3 536870912 268435456 hp764616 hp642702 hp764617 hp764618 hp642705

noncomputable def hp764620 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 841257300) (BSN.sinEvenQ 536870912) 0 3 hp764616 hp642702 hp764617 rfl rfl rfl

noncomputable def hp764621 := hp764619 hp764617 536866969 rfl rfl rfl rfl rfl rfl rfl rfl (hp764620 rfl)

noncomputable def hp764622 := @BSN.binarySplit_of_base3 (BSN.sinOddP 841257300) (BSN.sinOddQ 536870912) 0 3 hp764618 hp642705 hp764617 rfl rfl rfl

noncomputable def hp764623 := nat_lit 3062733528888317946008500707637915398843584464604919068861776107146379520

noncomputable def hp764624 := nat_lit 148611942523191176916235111424024406839156271196085383456540505211136

noncomputable def hp764625 := nat_lit 8021204346800557072878685091728425243169743535240470565921912548374937856

noncomputable def hp764626 := BSN.sin_dyadic_bound_f 332281922 536870912 3 2 536870912 268435456 hp764623 hp708845 hp764624 hp764625 hp708848

noncomputable def hp764627 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 332281922) (BSN.sinEvenQ 536870912) 0 2 hp764623 hp708845 hp764624 rfl rfl rfl

noncomputable def hp764628 := hp764626 hp764624 311470238 rfl rfl rfl rfl rfl rfl rfl rfl (hp764627 rfl)

noncomputable def hp764629 := @BSN.binarySplit_of_base2 (BSN.sinOddP 332281922) (BSN.sinOddQ 536870912) 0 2 hp764625 hp708848 hp764624 rfl rfl rfl

noncomputable def hp764630 := hp764615 hd4944 hd4946 hd4961 hd4963 hd4918 (hp764621 (hp764622 rfl) rfl rfl rfl rfl) (hp764628 (hp764629 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764631 := @hp764464 106767 134217728 (hp764630 rfl rfl rfl rfl rfl) (hp764630 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp764632 := @hp764462 Bool.false 946007447 268435456 106767 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 880021 1000)) (Enclosure.sfrac Bool.false 880021 1000) 11) hp764631

noncomputable def hp764633 := @Enclosure.Real.IsNear.mulLit_tf hp764453 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1))) 19507499 67108864 1

noncomputable def hp764634 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp764452 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp764635 := @hp764634 1 1 0 1 19507499 67108864 1 67108864 19507499 67108864 1

noncomputable def hp764636 := @Enclosure.Real.IsNear.of_eq (hp764452 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp764637 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 880021 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp764638 := @hp764636 (@Inv.inv Real Real.instInv (Real.sqrt hp764454)) Bool.false 19507499 67108864 1 67108864 (hp764637 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 880021 1000) 880021 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 880021 1000))))

noncomputable def hp764639 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp764454)) Bool.false 19507499 67108864 1 67108864 19507499 67108864

noncomputable def hp764640 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp764454) Bool.false 230865041 67108864 7 67108864 230865041 67108864 7 67108864

noncomputable def hp764641 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 880021 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp764642 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 880021 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp764643 := @hp764642 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 880021 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9399246454847

noncomputable def hp764644 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 880021 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 880021 1000 0

noncomputable def hp764645 := @hp764644 1 10680707 67108864 1 67108864 9399246454847 67108864000 880021 67108864000 (Enclosure.Real.IsNear.const Bool.false 880021 1000) hd4949

noncomputable def hp764646 := @hp764643 67108864000 880021 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 880021 1000) 880021 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 880021 1000))) (hp764645 rfl)

noncomputable def hp764647 := @hp764641 9399246454847 67108864000 880021 67108864000 397105997 397106035 33554432 hp764646 rfl rfl rfl

noncomputable def hp764648 := @Enclosure.Real.IsNear.recentre' hp764454 Bool.false 794212032 67108864 38 67108864 12409563 1048576 19 33554432 (hp764647 rfl rfl rfl)

noncomputable def hp764649 := @Enclosure.Real.IsNear.sqrt_image hp764454 12409563 1048576 19 33554432 115432517 115432524 33554432 (hp764648 rfl) rfl rfl

noncomputable def hp764650 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp764454) 230865041 67108864 7 67108864 9753749 9753750 33554432 (hp764640 (hp764649 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp764651 := @hp764635 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp764638 (@hp764639 1 67108864 (hp764650 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp764652 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp764653 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp764654 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1))) (hp764652 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764653 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp764655 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 880021 1000) 880021 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 880021 1000)) rfl

noncomputable def hp764656 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp764657 := @hp764656 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764653 (Enclosure.sfrac Bool.false 1 16)))) 16535209

noncomputable def hp764658 := @hp764657 8388608 479 33554432 5135467 16777216 219216527 22837985280000 84916020157603 140737488355328 396617618863539 17029236090994688000

noncomputable def hp764659 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp764660 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1)))) 17022765

noncomputable def hp764661 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp764662 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 351949659) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp764663 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1))) Bool.false 773945485624324431985

noncomputable def hp764664 := nat_lit 512735433012417429509086661

noncomputable def hp764665 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp764666 := @Enclosure.Real.IsNear.subLit_ff_p hp764454 (Enclosure.sfrac Bool.false 11 1) 12409563 1048576 19 33554432 11 1 0

noncomputable def hp764667 := @hp764665 500000000000000 875227 1048576 19 33554432 773945485624324431985 147573952589676412928 hp764664 hp682805 hd4948 (@hp764666 1 875227 875227 1048576 19 33554432 (hp764648 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp764668 := @hp764662 351949659 67108864 15 4194304 Bool.false 34045530 67108864 1 10890000 (@hp764663 147573952589676412928 hp764664 hp682805 351949659 67108864 15 4194304 (hp764667 rfl) rfl) (Enclosure.sfrac_false_div 351949659 67108864)

noncomputable def hp764669 := nat_lit 5145861616382279090700288

noncomputable def hp764670 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 351949659) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp764669) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp764671 := BSN.sin_reduce_arg_pos_rat_q3 351949659 67108864 226375608064910080 72057594037927936 0 hp764669 hp617687 rfl rfl rfl rfl

noncomputable def hp764672 := nat_lit 28596521559087651278668310960935793585875216

noncomputable def hp764673 := BSN.sin_dyadic_bound_f 73127091814 137438953472 2 1 67108864 21801270 hp764672 hp749778 hp764672 hp764672 hp749779

noncomputable def hp764674 := @BSN.binarySplit_of_base (BSN.sinEvenP 73127091814) (BSN.sinEvenQ 137438953472) 0 1 hp764672 hp749778 hp764672 rfl rfl rfl

noncomputable def hp764675 := hp764673 hp764672 34045530 rfl rfl rfl rfl rfl rfl rfl rfl (hp764674 rfl)

noncomputable def hp764676 := @BSN.binarySplit_of_base (BSN.sinOddP 73127091814) (BSN.sinOddQ 137438953472) 0 1 hp764672 hp749779 hp764672 rfl rfl rfl

noncomputable def hp764677 := @BSN.sin_arg_round Bool.false 34045530 67108864 hp764669 hp617687 73127091814 137438953472 21801270 21780000 (hp764675 (hp764676 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764678 := hp764670 34045530 67108864 0 1000000000000000 21780000 10890000 hp764671 BSN.pi_near_15 hp764677 rfl rfl

noncomputable def hp764679 := @hp764660 33554432 10471519 2854748160000 66140357 66141315 33554432 (@hp764661 34045530 67108864 167544304 45675970560000 17022765 33554432 10471519 2854748160000 (hp764668 (hp764678 rfl rfl) rfl rfl) rfl)

noncomputable def hp764680 := @hp764659 Bool.false 132281672 67108864 958 67108864 16535209 8388608 479 33554432 (hp764679 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp764681 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764653 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp764682 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764653 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 84537375)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp764683 := nat_lit 194929915565672430883964245

noncomputable def hp764684 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764653 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp764683

noncomputable def hp764685 := nat_lit 45925189212435571557705078270924639

noncomputable def hp764686 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764653 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp764687 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp764688 := @hp764687 (Enclosure.sfrac Bool.false 1 16) 151719725223 1099511627776 1701810601 1125899906842624 1 16 0

noncomputable def hp764689 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1)) 766022301529

noncomputable def hp764690 := @hp764689 1099511627776 1064276393 1125899906842624 875227 1048576 19 33554432 159089662595432448 151719725223 1099511627776 1701810601

noncomputable def hp764691 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1)) 875227 1048576 19

noncomputable def hp764692 := @hp764691 33554432 875227 1048576 19 33554432 766022301529 1099511627776 1064276393 1125899906842624 (@hp764666 1 875227 875227 1048576 19 33554432 (hp764648 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp764693 := hp764692 (@hp764666 1 875227 875227 1048576 19 33554432 (hp764648 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp764694 := @hp764690 1125899906842624 (hp764693 rfl) (@hp764666 1 875227 875227 1048576 19 33554432 (hp764648 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp764695 := @hp764686 500000000000000 220439201959 1099511627776 1701810601 1125899906842624 hp764683 hp619308 hp764685 hp682143 hd4948 (@hp764688 1 3527027231344 220439201959 1099511627776 1701810601 1125899906842624 (hp764694 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp764696 := @hp764682 84537375 67108864 319 33554432 Bool.false 10270934 33554432 1 10890000 (@hp764684 hp619308 hp764685 hp682143 84537375 67108864 319 33554432 (hp764695 rfl) rfl) (Enclosure.sfrac_true_div 84537375 67108864)

noncomputable def hp764697 := nat_lit 419962447700081262896389169208083823050127985303904179135272215900493600511822208001052663824462890625

noncomputable def hp764698 := nat_lit 133224806842124200476463160681460770349892720519930952215585688004276031279005110263824462890625

noncomputable def hp764699 := nat_lit 2545229452782236709671358923838430079930442645261480912879354838563589743861248248247160823824462890625

noncomputable def hp764700 := BSN.cos_dyadic_bound_f 84537375 67108864 4 3 33554432 10890000 hp764697 hp745658 hp764698 hp764699 hp745661

noncomputable def hp764701 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 84537375) (BSN.cosEvenQ 67108864) 0 3 hp764697 hp745658 hp764698 rfl rfl rfl

noncomputable def hp764702 := hp764700 hp764698 10270934 rfl rfl rfl rfl rfl rfl rfl rfl (hp764701 rfl)

noncomputable def hp764703 := @BSN.binarySplit_of_base3 (BSN.cosOddP 84537375) (BSN.cosOddQ 67108864) 0 3 hp764699 hp745661 hp764698 rfl rfl rfl

noncomputable def hp764704 := hp764696 (BSN.cos_neg_of_bound 84537375 67108864 Bool.false 10270934 33554432 1 10890000 (hp764702 (hp764703 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp764705 := hp764658 hp764680 (@hp764681 10270934 33554432 3507464432 365407764480000 5135467 16777216 219216527 22837985280000 (hp764704 rfl) rfl)

noncomputable def hp764706 := @hp764633 67108864 84916020157603 140737488355328 396617618863539 17029236090994688000 1656499178308420364897 9444732965739290427392 15494586076839114011 hp764450 (hp764651 rfl) (@hp764654 Bool.false 84916020157603 140737488355328 396617618863539 17029236090994688000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764454 (Enclosure.sfrac Bool.false 11 1)) (hp764655 rfl (hp764457 rfl rfl))) (hp764705 rfl))

noncomputable def hp764707 := @hp764451 1833655035804068967707 hp764450 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 880021 1000))) (@hp764456 1833655035804068967707 hp764450 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 880021 1000) 11 (hp764457 rfl rfl)) (@hp764460 1833655035804068967707 hp764450 hp764632 (hp764706 rfl) rfl rfl))

theorem hd5067 : hp764449 hp764450 := hp764707

noncomputable def hp764708 := nat_lit 5162390203525924997467897

noncomputable def hp764709 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 881292 1000)) Bool.true 12445287495392789598849 4722366482869645213696 hp764708

noncomputable def hp764710 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 881292 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 881292 1000)) Bool.true 12445287495392789598849 4722366482869645213696

noncomputable def hp764711 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 881292 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp764712 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp764711 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp764713 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 881292 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp764714 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 881292 1000)) (Enclosure.sfrac Bool.false 881292 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp764712 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp764715 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 881292 1000)) hp764714 Bool.true 12445287495392789598849 4722366482869645213696

noncomputable def hp764716 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 881292 1000) 881292 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 881292 1000)) rfl

noncomputable def hp764717 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 881292 1000)) (Enclosure.sfrac Bool.false 881292 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp764712 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp764718 := nat_lit 3340756423876861375079088390144

noncomputable def hp764719 := @hp764717 755480535 268435456 106921 134217728 845266629262143843711 4722366482869645213696 41438150786178959707897 hp752398 hp764718 12445287495392789598849 4722366482869645213696

noncomputable def hp764720 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 881292 1000)) (Enclosure.sfrac Bool.false 881292 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 881292 1000)) (Enclosure.sfrac Bool.false 881292 1000) 11)

noncomputable def hp764721 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 881292 1000)) (Enclosure.sfrac Bool.false 881292 1000) 11) hp764720

noncomputable def hp764722 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 881292 1000)) (Enclosure.sfrac Bool.false 881292 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 881292 1000)) (Enclosure.sfrac Bool.false 881292 1000) 11)

noncomputable def hp764723 := @hp764722 755480535 536870912 213842 536870912 755480535 536870912 213842 536870912 811191047647395840 755480535 268435456

noncomputable def hp764724 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 881292 1000)) (Enclosure.sfrac Bool.false 881292 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp764725 := hp764724 BSN.quadSignPos 9 10 11 881292 1000 185 239 536870912 268435456 9007199254740992

noncomputable def hp764726 := hp764725 Bool.false 932705883903 4015 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp764727 := hp764726 Bool.true 670942998 183578 Bool.true 726067633 Bool.true 282128389 28296951008113761 1 Bool.false 524118907

noncomputable def hp764728 := hp764727 Bool.true Bool.false 269321290 Bool.false Bool.true 755480535 213842 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 185 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 524118907 536870912) BSN.abs_quadSignPos

noncomputable def hp764729 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 881292 1000)) (Enclosure.sfrac Bool.false 881292 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp764730 := hp764729 BSN.quadSignNeg 7 8 9 881292 1000 60 126 536870912 268435456 9007199254740992

noncomputable def hp764731 := hp764730 Bool.false 932705883903 4015 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp764732 := hp764731 Bool.true 696996510 149928 Bool.true 562277630 Bool.true 631355138 28296951008113761 1 Bool.false 268376801

noncomputable def hp764733 := hp764732 Bool.false Bool.false 206496058 Bool.true Bool.true 670942998 183578 BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268376801 536870912) BSN.abs_quadSignNeg

noncomputable def hp764734 := hp764729 BSN.quadSignNeg 5 6 7 881292 1000 100 14 536870912 268435456 9007199254740992

noncomputable def hp764735 := hp764734 Bool.false 932705883903 4015 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp764736 := hp764735 Bool.true 597711035 111414 Bool.false 621258165 Bool.false 211484148 28296951008113761 1 Bool.false 215779216

noncomputable def hp764737 := hp764736 Bool.false Bool.false 495752853 Bool.true Bool.true 696996510 149928 BSN.abs_quadSignPos (BSN.cos_quad_nat0 100 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 215779216 536870912) BSN.abs_quadSignNeg

noncomputable def hp764738 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 881292 1000)) (Enclosure.sfrac Bool.false 881292 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp764739 := hp764738 BSN.quadSignPos 3 4 5 881292 1000 328 203 536870912 268435456 9007199254740992

noncomputable def hp764740 := hp764739 Bool.false 932705883903 4015 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp764741 := hp764740 Bool.true 860473470 65852 Bool.false 187254093 Bool.false 23464090 28296951008113761 1 Bool.false 504544647

noncomputable def hp764742 := hp764741 Bool.false Bool.false 23456620 Bool.false Bool.true 597711035 111414 BSN.abs_quadSignPos (BSN.cos_quad_nat0 328 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 504544647 536870912) BSN.abs_quadSignPos

noncomputable def hp764743 := hp764724 BSN.quadSignNeg 1 2 3 881292 1000 717 489 536870912 268435456 9007199254740992

noncomputable def hp764744 := hp764743 Bool.false 932705883903 4015 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp764745 := hp764744 Bool.true 536870792 4074 Bool.false 93460386 Bool.false 527461813 28296951008113761 1 Bool.false 92989046

noncomputable def hp764746 := hp764745 Bool.true Bool.false 446608418 Bool.true Bool.true 860473470 65852 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 717 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 92989046 536870912) BSN.abs_quadSignNeg

noncomputable def hp764747 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 881292 1000)) (Enclosure.sfrac Bool.false 881292 1000) 1) Bool.true

noncomputable def hp764748 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 881292 1000)) (Enclosure.sfrac Bool.false 881292 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 881292 1000)))

noncomputable def hp764749 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 881292 1000))) Bool.true 67108849 67108864

noncomputable def hp764750 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 881292 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 116588235487) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 116588235487 67108864

noncomputable def hp764751 := nat_lit 111867534856153594795650915819144438916142828904934141

noncomputable def hp764752 := nat_lit 64391601358918861068354138472824622441633415168000

noncomputable def hp764753 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 881292 1000)) Bool.false hp764751 hp764752 33349361808705678229

noncomputable def hp764754 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 881292 4000) (Real.log (Enclosure.sfrac Bool.false 3106703357056 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1762584))))))

noncomputable def hp764755 := nat_lit 255176531812185649861122523791360000

noncomputable def hp764756 := nat_lit 1349310419127041822334721792152667422720

noncomputable def hp764757 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 881292 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp764754 (Enclosure.sfrac Bool.false 881292 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 881292 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp764755 hp764756)) Bool.false

noncomputable def hp764758 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 881292 1000) 881292 1000 3106703357056 16000000 1762584

noncomputable def hp764759 := hp764758 4000 2000 hp764755 hp764756 (@Eq.refl Real (Enclosure.sfrac Bool.false 881292 1000)) rfl rfl rfl rfl

noncomputable def hp764760 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp764754 (Enclosure.sfrac Bool.false 881292 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 881292 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp764755 hp764756) 7824104891061613527077 4503599627370496000

noncomputable def hp764761 := nat_lit 10557145100639350063480000923537767926284004466563819964989440

noncomputable def hp764762 := @hp764760 33349361808705678229 hp739140 hp764755 hp764756 0 1 hp764761 hp764751 hp764752 33349361808705678229 hp739140

noncomputable def hp764763 := @Enclosure.Real.IsNear.subLit_ff_p (hp764754 (Enclosure.sfrac Bool.false 881292 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 881292 2000) (Real.log Real.pi)) 2019162702898695903649 900719925474099200 173690098685989 68062500000000000000

noncomputable def hp764764 := nat_lit 26253339552799431890458535526400

noncomputable def hp764765 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 881292 4000) (Real.log (Enclosure.sfrac Bool.false 3106703357056 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1762584))))))

noncomputable def hp764766 := @hp764765 (Enclosure.sfrac Bool.false 881292 2000) 12080306675895779098661 4503599627370496000 173690098685989 68062500000000000000 881292 2000 0

noncomputable def hp764767 := nat_lit 20191627028986959036490000

noncomputable def hp764768 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 881292 4000) (Real.log (Enclosure.sfrac Bool.false 3106703357056 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1762584))))) 12082074596558064224661

noncomputable def hp764769 := nat_lit 27202432322042772970898379186192252928

noncomputable def hp764770 := @hp764768 4503599627370496000 918013859613233 363000000000000000000 883960331142563 2251799813685248 200000001089 8712000000000000000 hp764769 12080306675895779098661 4503599627370496000 173690098685989

noncomputable def hp764771 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 881292 4000) (Real.log (Enclosure.sfrac Bool.false 3106703357056 16000000)) 881292 4000 0 1 54838008726088807 4503599627370496

noncomputable def hp764772 := nat_lit 117763727028157024028327936

noncomputable def hp764773 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3106703357056) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp764772 hp617687

noncomputable def hp764774 := BSN.log_rat_reduce_isNear 3106703357056 16000000 17 6213406714112 4194304000000 105490279 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp764775 := nat_lit 151382844214892962986215158805979938677335197868096691581623485054447177217160423021040262530177830581933910358264561326228001259520

noncomputable def hp764776 := nat_lit 1943235191890351867571022404452918360416498225266897082955385000584781018237785159344140189026739834052003763732308390215317192704

noncomputable def hp764777 := nat_lit 1039240295197849033033540780071488985900703333759524934512744292523590381931147509484093957905400704283637640760501018296320

noncomputable def hp764778 := BSN.log_dyadic_bound 1009551357056 5203855357056 6 5 hp764775 268435456 87120000 hp764776 hp764777 105490279 6213406714112

noncomputable def hp764779 := hp764778 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp764780 := @BSN.binarySplit_of_base5 (BSN.artanhP 1009551357056) (BSN.artanhQ 5203855357056) 0 5 hp764776 hp764775 hp764777 rfl rfl rfl

noncomputable def hp764781 := hp764774 rfl rfl rfl rfl (hp764779 (hp764780 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp764782 := @hp764771 12500018513 1089000000000000000 12082074596558064224661 4503599627370496000 918013859613233 363000000000000000000 (Enclosure.Real.IsNear.const Bool.false 881292 4000) (BSN.isNear_log_sfrac 3106703357056 16000000 54838008726088807 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp764773 1000001481040000 87120000000000000000000 54838008726088807 4503599627370496 12500018513 1089000000000000000 (hp764781 rfl rfl rfl) rfl)) rfl

noncomputable def hp764783 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1762584)))) 1 4

noncomputable def hp764784 := @hp764783 0 1 883960331142563 562949953421312 200000001089 2178000000000000000 883960331142563 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp764785 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1762584))) 884279719003555 562949953421312 1

noncomputable def hp764786 := @hp764785 2000000000000000 19037 33554432 1 10890000 29660786822020612489216 883960331142563 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp764787 := BSN.arctan_dyadic_bound_f 1000 1762584 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp764788 := hp764787 1 19037 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1762584) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1762584) 0 0 rfl)

noncomputable def hp764789 := hp764784 (hp764786 (hp764788 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp764790 := @hp764763 8462774095803 16777216000 660969 134217728000 hp764764 7824104891061613527077 4503599627370496000 33349361808705678229 hp739140 (@hp764766 1 hp764767 2019162702898695903649 900719925474099200 173690098685989 68062500000000000000 (@hp764770 68062500000000000000 hp764782 hp764789 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 881292 2000) rfl rfl)

noncomputable def hp764791 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 881292 2000) (Real.log Real.pi) 881292 2000 0 1 38410761 33554432

noncomputable def hp764792 := hp764790 (@hp764791 3 268435456 8462774095803 16777216000 660969 134217728000 (Enclosure.Real.IsNear.const Bool.false 881292 2000) hd4909 rfl) rfl

noncomputable def hp764793 := @hp764753 hp739140 116588235487 67108864 503 67108864 (@hp764757 hp764751 hp764752 33349361808705678229 hp739140 (hp764759 rfl rfl rfl rfl rfl) (hp764762 (hp764792 rfl) (Enclosure.Real.IsNear.const Bool.true hp764755 hp764756) rfl rfl)) rfl

noncomputable def hp764794 := nat_lit 15185551168562951108952064

noncomputable def hp764795 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 116588235487) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp764794) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp764796 := BSN.sin_reduce_arg_pos_rat_q1 116588235487 67108864 226375608064910080 72057594037927936 276 hp764794 hp617687 rfl rfl rfl rfl

noncomputable def hp764797 := nat_lit 14356651514797069130575733724417758346892707626841165336476629969456134921559468358337734405774542055543189320027579603705635182164406994866176

noncomputable def hp764798 := nat_lit 10200209873738314774862019177617593862499469863249392921670627938509492380688632629831718596847657076545483847205410033693885006697598976

noncomputable def hp764799 := nat_lit 71694204693996011365203876768431950159420540508067846871535903117899090490186927392157961748277294811583385098097882290843376207279357525364736

noncomputable def hp764800 := BSN.sin_dyadic_bound_f 215799661426 137438953472 4 3 67108864 21801270 hp764797 hp737934 hp764798 hp764799 hp737937

noncomputable def hp764801 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215799661426) (BSN.sinEvenQ 137438953472) 0 3 hp764797 hp737934 hp764798 rfl rfl rfl

noncomputable def hp764802 := hp764800 hp764798 67108849 rfl rfl rfl rfl rfl rfl rfl rfl (hp764801 rfl)

noncomputable def hp764803 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215799661426) (BSN.sinOddQ 137438953472) 0 3 hp764799 hp737937 hp764798 rfl rfl rfl

noncomputable def hp764804 := @BSN.sin_arg_round Bool.false 67108849 67108864 hp764794 hp617687 215799661426 137438953472 21801270 21780000 (hp764802 (hp764803 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764805 := hp764795 67108849 67108864 276 1000000000000000 21780000 10890000 hp764796 BSN.pi_near_15 hp764804 rfl rfl

noncomputable def hp764806 := @hp764750 503 67108864 Bool.true 67108849 67108864 1 10890000 hp764793 (Enclosure.sfrac_false_div 116588235487 67108864) (hp764805 rfl rfl) rfl

noncomputable def hp764807 := @hp764747 67108849 67108864 346548679 45675970560000 536870792 536870912 4074 536870912 (@hp764748 Bool.true 67108849 67108864 346548679 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 881292 1000)) (Enclosure.sfrac Bool.false 881292 1000)) (@hp764749 5544778864 730815528960000 67108849 67108864 346548679 45675970560000 (hp764806 rfl) rfl))

noncomputable def hp764808 := @hp764753 hp739140 932705883903 536870912 4015 536870912 (@hp764757 hp764751 hp764752 33349361808705678229 hp739140 (hp764759 rfl rfl rfl rfl rfl) (hp764762 (hp764792 rfl) (Enclosure.Real.IsNear.const Bool.true hp764755 hp764756) rfl rfl)) rfl

noncomputable def hp764809 := hp764746 (BSN.cos_quad_nat1 489 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 446608418 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 881292 1000)) rfl rfl (hp764807 rfl) hp764808

noncomputable def hp764810 := nat_lit 76297495359083026060360350848016

noncomputable def hp764811 := BSN.sin_dyadic_bound_f 93460386 536870912 2 1 536870912 268435456 hp764810 hp708890 hp764810 hp764810 hp708891

noncomputable def hp764812 := @BSN.binarySplit_of_base (BSN.sinEvenP 93460386) (BSN.sinEvenQ 536870912) 0 1 hp764810 hp708890 hp764810 rfl rfl rfl

noncomputable def hp764813 := hp764811 hp764810 92989046 rfl rfl rfl rfl rfl rfl rfl rfl (hp764812 rfl)

noncomputable def hp764814 := @BSN.binarySplit_of_base (BSN.sinOddP 93460386) (BSN.sinOddQ 536870912) 0 1 hp764810 hp708891 hp764810 rfl rfl rfl

noncomputable def hp764815 := nat_lit 19451771784152090576412310587529938050199028783634468677256160886139113825

noncomputable def hp764816 := nat_lit 5991398214184320670893757189375254264996206135954989704334277089415521

noncomputable def hp764817 := nat_lit 50935416218527748323803175931890849243616033909108252742816261110314815841

noncomputable def hp764818 := BSN.sin_dyadic_bound_f 527461813 536870912 3 2 536870912 268435456 hp764815 hp708845 hp764816 hp764817 hp708848

noncomputable def hp764819 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 527461813) (BSN.sinEvenQ 536870912) 0 2 hp764815 hp708845 hp764816 rfl rfl rfl

noncomputable def hp764820 := hp764818 hp764816 446608418 rfl rfl rfl rfl rfl rfl rfl rfl (hp764819 rfl)

noncomputable def hp764821 := @BSN.binarySplit_of_base2 (BSN.sinOddP 527461813) (BSN.sinOddQ 536870912) 0 2 hp764817 hp708848 hp764816 rfl rfl rfl

noncomputable def hp764822 := hp764809 hd4911 hd4913 hd4915 hd4917 hd4918 (hp764813 (hp764814 rfl) rfl rfl rfl rfl) (hp764820 (hp764821 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764823 := hp764742 (BSN.cos_quad_nat3 203 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 23456620 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 881292 1000)) rfl rfl (hp764822 rfl rfl rfl rfl rfl) hp764808

noncomputable def hp764824 := nat_lit 171600236340113664040137530597767903673361801585448502394762010839310881

noncomputable def hp764825 := nat_lit 1511647583959766008359615363625771780898870607707616808121178874401

noncomputable def hp764826 := nat_lit 514797685725173072588395872562576459476523607015130091950669790160183841

noncomputable def hp764827 := BSN.cos_dyadic_bound_f 187254093 536870912 3 2 536870912 268435456 hp764824 hp708868 hp764825 hp764826 hp708870

noncomputable def hp764828 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 187254093) (BSN.cosEvenQ 536870912) 0 2 hp764824 hp708868 hp764825 rfl rfl rfl

noncomputable def hp764829 := hp764827 hp764825 504544647 rfl rfl rfl rfl rfl rfl rfl rfl (hp764828 rfl)

noncomputable def hp764830 := @BSN.binarySplit_of_base2 (BSN.cosOddP 187254093) (BSN.cosOddQ 536870912) 0 2 hp764826 hp708870 hp764825 rfl rfl rfl

noncomputable def hp764831 := nat_lit 303120189035168550046689610000

noncomputable def hp764832 := BSN.sin_dyadic_bound_f 23464090 536870912 2 1 536870912 268435456 hp764831 hp708890 hp764831 hp764831 hp708891

noncomputable def hp764833 := @BSN.binarySplit_of_base (BSN.sinEvenP 23464090) (BSN.sinEvenQ 536870912) 0 1 hp764831 hp708890 hp764831 rfl rfl rfl

noncomputable def hp764834 := hp764832 hp764831 23456620 rfl rfl rfl rfl rfl rfl rfl rfl (hp764833 rfl)

noncomputable def hp764835 := @BSN.binarySplit_of_base (BSN.sinOddP 23464090) (BSN.sinOddQ 536870912) 0 1 hp764831 hp708891 hp764831 rfl rfl rfl

noncomputable def hp764836 := hp764823 hd4920 hd4922 hd4924 hd4926 hd4918 (hp764829 (hp764830 rfl) rfl rfl rfl rfl) (hp764834 (hp764835 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764837 := hp764737 (BSN.cos_quad_nat2 14 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 495752853 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 881292 1000)) rfl rfl (hp764836 rfl rfl rfl rfl rfl) hp764808

noncomputable def hp764838 := nat_lit 20541706226285263428540609311080258437155159582133529929925905715168716566069151180540504126663278739311553140625

noncomputable def hp764839 := nat_lit 3305714287914741723168656459006736372423718231432464635522641270052127137104673369234957694802578369140625

noncomputable def hp764840 := nat_lit 124531088503805793912389681386668297794233601972994084745668805880948304646793944890459772481154132382672218740625

noncomputable def hp764841 := BSN.cos_dyadic_bound_f 621258165 536870912 4 3 536870912 268435456 hp764838 hp716712 hp764839 hp764840 hp716714

noncomputable def hp764842 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 621258165) (BSN.cosEvenQ 536870912) 0 3 hp764838 hp716712 hp764839 rfl rfl rfl

noncomputable def hp764843 := hp764841 hp764839 215779216 rfl rfl rfl rfl rfl rfl rfl rfl (hp764842 rfl)

noncomputable def hp764844 := @BSN.binarySplit_of_base3 (BSN.cosOddP 621258165) (BSN.cosOddQ 536870912) 0 3 hp764840 hp716714 hp764839 rfl rfl rfl

noncomputable def hp764845 := nat_lit 279194130003820697327724294580042988709160707154208043115329749044494336

noncomputable def hp764846 := nat_lit 4001497590556123501023065446513677587284308851916079392502442950656

noncomputable def hp764847 := nat_lit 837574387016280979736170837609235938772307552844920297187204242247581696

noncomputable def hp764848 := BSN.cos_dyadic_bound_f 211484148 536870912 3 2 536870912 268435456 hp764845 hp708868 hp764846 hp764847 hp708870

noncomputable def hp764849 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 211484148) (BSN.cosEvenQ 536870912) 0 2 hp764845 hp708868 hp764846 rfl rfl rfl

noncomputable def hp764850 := hp764848 hp764846 495752853 rfl rfl rfl rfl rfl rfl rfl rfl (hp764849 rfl)

noncomputable def hp764851 := @BSN.binarySplit_of_base2 (BSN.cosOddP 211484148) (BSN.cosOddQ 536870912) 0 2 hp764847 hp708870 hp764846 rfl rfl rfl

noncomputable def hp764852 := hp764837 hd4928 hd4930 hd4932 hd4934 hd4918 (hp764843 (hp764844 rfl) rfl rfl rfl rfl) (hp764850 (hp764851 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764853 := hp764733 (BSN.cos_quad_nat2 126 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 206496058 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 881292 1000)) rfl rfl (hp764852 rfl rfl rfl rfl rfl) hp764808

noncomputable def hp764854 := nat_lit 13778403106651590851272656587482377910838731683129935918000559012045210562298407664973589483621695597104704000000

noncomputable def hp764855 := nat_lit 998641632288104774629428489560863602854977708950644467172148882797258921526099916508715618481000000000000

noncomputable def hp764856 := nat_lit 83549093226429985832726786278114744695069102602177881519232403680779089687738582792126689461782872213579737600000

noncomputable def hp764857 := BSN.cos_dyadic_bound_f 562277630 536870912 4 3 536870912 268435456 hp764854 hp716712 hp764855 hp764856 hp716714

noncomputable def hp764858 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 562277630) (BSN.cosEvenQ 536870912) 0 3 hp764854 hp716712 hp764855 rfl rfl rfl

noncomputable def hp764859 := hp764857 hp764855 268376801 rfl rfl rfl rfl rfl rfl rfl rfl (hp764858 rfl)

noncomputable def hp764860 := @BSN.binarySplit_of_base3 (BSN.cosOddP 562277630) (BSN.cosOddQ 536870912) 0 3 hp764856 hp716714 hp764855 rfl rfl rfl

noncomputable def hp764861 := nat_lit 21911585551286000403347542594235421556876333527452546667447894419165605503330008576784585528902710643320883777536

noncomputable def hp764862 := nat_lit 4011295252667800552280460388765343171863999359114392453471611348362990394844212488393891404970438174969856

noncomputable def hp764863 := nat_lit 132829492266367649999885176800942422216269342936362840009733353562910577202558322847758976729643978400410279874560

noncomputable def hp764864 := BSN.cos_dyadic_bound_f 631355138 536870912 4 3 536870912 268435456 hp764861 hp716712 hp764862 hp764863 hp716714

noncomputable def hp764865 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 631355138) (BSN.cosEvenQ 536870912) 0 3 hp764861 hp716712 hp764862 rfl rfl rfl

noncomputable def hp764866 := hp764864 hp764862 206496058 rfl rfl rfl rfl rfl rfl rfl rfl (hp764865 rfl)

noncomputable def hp764867 := @BSN.binarySplit_of_base3 (BSN.cosOddP 631355138) (BSN.cosOddQ 536870912) 0 3 hp764863 hp716714 hp764862 rfl rfl rfl

noncomputable def hp764868 := hp764853 hd4936 hd4938 hd4940 hd4942 hd4918 (hp764859 (hp764860 rfl) rfl rfl rfl rfl) (hp764866 (hp764867 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764869 := hp764728 (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 269321290 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 881292 1000)) rfl rfl (hp764868 rfl rfl rfl rfl rfl) hp764808

noncomputable def hp764870 := nat_lit 99642962637226596955075934058075914591085735867359311618260854345692008524815954579161324433616947010676536976961

noncomputable def hp764871 := nat_lit 21464704990851005428149289776996025752524145947118047202970038958139592703826733100114406159782343318775361

noncomputable def hp764872 := nat_lit 497874397801683170185681510491091156344587478672338060525089317050601644480575187665749069013764060453386254624321

noncomputable def hp764873 := BSN.sin_dyadic_bound_f 726067633 536870912 4 3 536870912 268435456 hp764870 hp642702 hp764871 hp764872 hp642705

noncomputable def hp764874 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 726067633) (BSN.sinEvenQ 536870912) 0 3 hp764870 hp642702 hp764871 rfl rfl rfl

noncomputable def hp764875 := hp764873 hp764871 524118907 rfl rfl rfl rfl rfl rfl rfl rfl (hp764874 rfl)

noncomputable def hp764876 := @BSN.binarySplit_of_base3 (BSN.sinOddP 726067633) (BSN.sinOddQ 536870912) 0 3 hp764872 hp642705 hp764871 rfl rfl rfl

noncomputable def hp764877 := nat_lit 1591693314137546481728400223184504007359350106847844699677859652935579105

noncomputable def hp764878 := nat_lit 40139717516152797215564537223261252995422632532807089788449956787681

noncomputable def hp764879 := nat_lit 4168655596531881299997937289565815691531543405101206811487117791091717601

noncomputable def hp764880 := BSN.sin_dyadic_bound_f 282128389 536870912 3 2 536870912 268435456 hp764877 hp708845 hp764878 hp764879 hp708848

noncomputable def hp764881 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 282128389) (BSN.sinEvenQ 536870912) 0 2 hp764877 hp708845 hp764878 rfl rfl rfl

noncomputable def hp764882 := hp764880 hp764878 269321290 rfl rfl rfl rfl rfl rfl rfl rfl (hp764881 rfl)

noncomputable def hp764883 := @BSN.binarySplit_of_base2 (BSN.sinOddP 282128389) (BSN.sinOddQ 536870912) 0 2 hp764879 hp708848 hp764878 rfl rfl rfl

noncomputable def hp764884 := hp764869 hd4944 hd4946 hd4961 hd4963 hd4918 (hp764875 (hp764876 rfl) rfl rfl rfl rfl) (hp764882 (hp764883 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764885 := @hp764723 106921 134217728 (hp764884 rfl rfl rfl rfl rfl) (hp764884 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp764886 := @hp764721 Bool.true 755480535 268435456 106921 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 881292 1000)) (Enclosure.sfrac Bool.false 881292 1000) 11) hp764885

noncomputable def hp764887 := @Enclosure.Real.IsNear.mulLit_tf hp764712 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1))) 9750231 33554432 1

noncomputable def hp764888 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp764711 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp764889 := @hp764888 1 1 0 1 9750231 33554432 1 33554432 9750231 33554432 1

noncomputable def hp764890 := @Enclosure.Real.IsNear.of_eq (hp764711 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp764891 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 881292 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp764892 := @hp764890 (@Inv.inv Real Real.instInv (Real.sqrt hp764713)) Bool.false 9750231 33554432 1 33554432 (hp764891 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 881292 1000) 881292 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 881292 1000))))

noncomputable def hp764893 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp764713)) Bool.false 19500462 67108864 2 67108864 9750231 33554432

noncomputable def hp764894 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp764713) Bool.false 230948355 67108864 7 67108864 230948355 67108864 7 67108864

noncomputable def hp764895 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 881292 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp764896 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 881292 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp764897 := @hp764896 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 881292 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 2353205408361

noncomputable def hp764898 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 881292 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 881292 1000 0

noncomputable def hp764899 := @hp764898 1 10680707 67108864 1 67108864 2353205408361 16777216000 220323 16777216000 (Enclosure.Real.IsNear.const Bool.false 881292 1000) hd4949

noncomputable def hp764900 := @hp764897 16777216000 220323 16777216000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 881292 1000) 881292 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 881292 1000))) (hp764899 rfl)

noncomputable def hp764901 := @hp764895 2353205408361 16777216000 220323 16777216000 397392660 397392699 33554432 hp764900 rfl rfl rfl

noncomputable def hp764902 := @Enclosure.Real.IsNear.recentre' hp764713 Bool.false 794785359 67108864 39 67108864 794785359 67108864 39 67108864 (hp764901 rfl rfl rfl)

noncomputable def hp764903 := @Enclosure.Real.IsNear.sqrt_image hp764713 794785359 67108864 39 67108864 115474174 115474181 33554432 (hp764902 rfl) rfl rfl

noncomputable def hp764904 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp764713) 230948355 67108864 7 67108864 9750230 9750232 33554432 (hp764894 (hp764903 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp764905 := @hp764889 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp764892 (@hp764893 1 33554432 (hp764904 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp764906 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp764907 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp764908 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1))) (hp764906 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764907 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp764909 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 881292 1000) 881292 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 881292 1000)) rfl

noncomputable def hp764910 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp764911 := @hp764910 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764907 (Enclosure.sfrac Bool.false 1 16)))) 7587063

noncomputable def hp764912 := @hp764911 4194304 413 33554432 11426287 33554432 452726179 45675970560000 86691959325081 140737488355328 33902899013313893 1532631248189521920000

noncomputable def hp764913 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp764914 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1)))) 37099333

noncomputable def hp764915 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp764916 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 355551979) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp764917 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1))) Bool.false 50039492518413914824525

noncomputable def hp764918 := nat_lit 1052456941438803745903169873

noncomputable def hp764919 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp764920 := @Enclosure.Real.IsNear.subLit_ff_p hp764713 (Enclosure.sfrac Bool.false 11 1) 794785359 67108864 39 67108864 11 1 0

noncomputable def hp764921 := @hp764919 500000000000000 56587855 67108864 39 67108864 50039492518413914824525 9444732965739290427392 hp764918 hp738031 hd4948 (@hp764920 1 56587855 56587855 67108864 39 67108864 (hp764902 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp764922 := @hp764916 355551979 67108864 123 33554432 Bool.false 37099333 67108864 1 10890000 (@hp764917 9444732965739290427392 hp764918 hp738031 355551979 67108864 123 33554432 (hp764921 rfl) rfl) (Enclosure.sfrac_false_div 355551979 67108864)

noncomputable def hp764923 := nat_lit 5665010640691696215523328

noncomputable def hp764924 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 355551979) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp764923) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp764925 := BSN.sin_reduce_arg_pos_rat_q3 355551979 67108864 226375608064910080 72057594037927936 0 hp764923 hp617687 rfl rfl rfl rfl

noncomputable def hp764926 := nat_lit 45323325585031598534209690272138199116651461025635929619326233689782949433530243017729777920

noncomputable def hp764927 := nat_lit 1764279692084436458232657438991371587506547549326976797028717114724186417656347728158976

noncomputable def hp764928 := nat_lit 118701091507962240406759669267365487846755006371109476754849708407436266500283954769160970496

noncomputable def hp764929 := BSN.sin_dyadic_bound_f 80504643174 137438953472 3 2 67108864 21801270 hp764926 hp738039 hp764927 hp764928 hp738042

noncomputable def hp764930 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 80504643174) (BSN.sinEvenQ 137438953472) 0 2 hp764926 hp738039 hp764927 rfl rfl rfl

noncomputable def hp764931 := hp764929 hp764927 37099333 rfl rfl rfl rfl rfl rfl rfl rfl (hp764930 rfl)

noncomputable def hp764932 := @BSN.binarySplit_of_base2 (BSN.sinOddP 80504643174) (BSN.sinOddQ 137438953472) 0 2 hp764928 hp738042 hp764927 rfl rfl rfl

noncomputable def hp764933 := @BSN.sin_arg_round Bool.false 37099333 67108864 hp764923 hp617687 80504643174 137438953472 21801270 21780000 (hp764931 (hp764932 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp764934 := hp764924 37099333 67108864 0 1000000000000000 21780000 10890000 hp764925 BSN.pi_near_15 hp764933 rfl rfl

noncomputable def hp764935 := @hp764914 67108864 85814027 22837985280000 60696091 60696917 33554432 (@hp764915 37099333 67108864 1373024432 365407764480000 37099333 67108864 85814027 22837985280000 (hp764922 (hp764934 rfl rfl) rfl rfl) rfl)

noncomputable def hp764936 := @hp764913 Bool.false 121393008 67108864 826 67108864 7587063 4194304 413 33554432 (hp764935 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp764937 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764907 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp764938 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764907 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 20523835)) (@Nat.cast Real Real.instNatCast 16777216)) Bool.true

noncomputable def hp764939 := nat_lit 775368564453896539121931327805

noncomputable def hp764940 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764907 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp764939

noncomputable def hp764941 := nat_lit 189741792306356541496273088119979861

noncomputable def hp764942 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp764907 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp764943 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp764944 := @hp764943 (Enclosure.sfrac Bool.false 1 16) 595361331745695 4503599627370496 7031099907 4503599627370496 1 16 0

noncomputable def hp764945 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1)) 3202185333501025

noncomputable def hp764946 := @hp764945 4503599627370496 4413854211 4503599627370496 56587855 67108864 39 67108864 39954022642980728340480 595361331745695 4503599627370496 7031099907

noncomputable def hp764947 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1)) 56587855 67108864 39

noncomputable def hp764948 := @hp764947 67108864 56587855 67108864 39 67108864 3202185333501025 4503599627370496 4413854211 4503599627370496 (@hp764920 1 56587855 56587855 67108864 39 67108864 (hp764902 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp764949 := hp764948 (@hp764920 1 56587855 56587855 67108864 39 67108864 (hp764902 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp764950 := @hp764946 4503599627370496 (hp764949 rfl) (@hp764920 1 56587855 56587855 67108864 39 67108864 (hp764902 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp764951 := @hp764942 500000000000000 876836308456351 4503599627370496 7031099907 4503599627370496 hp764939 hp627574 hp764941 hp738055 hd4948 (@hp764944 1 14029380935301616 876836308456351 4503599627370496 7031099907 4503599627370496 (hp764950 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp764952 := @hp764938 20523835 16777216 659 67108864 Bool.false 11426287 33554432 1 10890000 (@hp764940 hp627574 hp764941 hp738055 20523835 16777216 659 67108864 (hp764951 rfl) rfl) (Enclosure.sfrac_true_div 20523835 16777216)

noncomputable def hp764953 := nat_lit 22258587748387055931395639176779268113904718494097990679153839534170379967717571742191528140625

noncomputable def hp764954 := nat_lit 5586015985549622022892339801027500289311513228059689360838017014060044955880312744140625

noncomputable def hp764955 := nat_lit 134915558183659708528497488730165792537416710630941549155760812440079506421216413336103233740625

noncomputable def hp764956 := BSN.cos_dyadic_bound_f 20523835 16777216 4 3 33554432 10890000 hp764953 hp633087 hp764954 hp764955 hp633090

noncomputable def hp764957 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 20523835) (BSN.cosEvenQ 16777216) 0 3 hp764953 hp633087 hp764954 rfl rfl rfl

noncomputable def hp764958 := hp764956 hp764954 11426287 rfl rfl rfl rfl rfl rfl rfl rfl (hp764957 rfl)

noncomputable def hp764959 := @BSN.binarySplit_of_base3 (BSN.cosOddP 20523835) (BSN.cosOddQ 16777216) 0 3 hp764955 hp633090 hp764954 rfl rfl rfl

noncomputable def hp764960 := hp764952 (BSN.cos_neg_of_bound 20523835 16777216 Bool.false 11426287 33554432 1 10890000 (hp764958 (hp764959 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp764961 := hp764912 hp764936 (@hp764937 11426287 33554432 7243618864 730815528960000 11426287 33554432 452726179 45675970560000 (hp764960 rfl) rfl)

noncomputable def hp764962 := @hp764887 33554432 86691959325081 140737488355328 33902899013313893 1532631248189521920000 845266629262143843711 4722366482869645213696 41438150786178959707897 hp752398 (hp764905 rfl) (@hp764908 Bool.false 86691959325081 140737488355328 33902899013313893 1532631248189521920000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764713 (Enclosure.sfrac Bool.false 11 1)) (hp764909 rfl (hp764716 rfl rfl))) (hp764961 rfl))

noncomputable def hp764963 := @hp764710 hp764708 hp752398 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 881292 1000))) (@hp764715 hp764708 hp752398 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 881292 1000) 11 (hp764716 rfl rfl)) (@hp764719 hp764708 hp752398 hp764886 (hp764962 rfl) rfl rfl))

theorem hd5068 : hp764709 hp752398 := hp764963

noncomputable def hp764964 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 882563 1000)) Bool.false 5312939341412785396993 9444732965739290427392 1033231544292757913771011

noncomputable def hp764965 := nat_lit 1285664274961260909428736000

noncomputable def hp764966 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 882563 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 882563 1000)) Bool.false 5312939341412785396993 9444732965739290427392

noncomputable def hp764967 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 882563 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp764968 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp764967 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp764969 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 882563 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp764970 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 882563 1000)) (Enclosure.sfrac Bool.false 882563 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp764968 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp764971 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 882563 1000)) hp764970 Bool.false 5312939341412785396993 9444732965739290427392

noncomputable def hp764972 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 882563 1000) 882563 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 882563 1000)) rfl

noncomputable def hp764973 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 882563 1000)) (Enclosure.sfrac Bool.false 882563 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp764968 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp764974 := nat_lit 1426181294812480732271956983808

noncomputable def hp764975 := @hp764973 101956161 268435456 214153 268435456 1725675836039923703041 9444732965739290427392 7551607750474514603011 hp764965 hp764974 5312939341412785396993 9444732965739290427392

noncomputable def hp764976 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 882563 1000)) (Enclosure.sfrac Bool.false 882563 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 882563 1000)) (Enclosure.sfrac Bool.false 882563 1000) 11)

noncomputable def hp764977 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 882563 1000)) (Enclosure.sfrac Bool.false 882563 1000) 11) hp764976

noncomputable def hp764978 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 882563 1000)) (Enclosure.sfrac Bool.false 882563 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 882563 1000)) (Enclosure.sfrac Bool.false 882563 1000) 11)

noncomputable def hp764979 := @hp764978 101956161 536870912 214153 536870912 101956161 536870912 214153 536870912 109474594280177664 101956161 268435456

noncomputable def hp764980 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 882563 1000)) (Enclosure.sfrac Bool.false 882563 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp764981 := hp764980 BSN.quadSignPos 9 10 11 882563 1000 185 239 536870912 268435456 9007199254740992

noncomputable def hp764982 := hp764981 Bool.false 934392764613 4021 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp764983 := hp764982 Bool.false 188347738 183845 Bool.true 610385628 Bool.true 231482519 28296951008113761 1 Bool.false 487128731

noncomputable def hp764984 := hp764983 Bool.true Bool.false 224376509 Bool.false Bool.false 101956161 214153 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 185 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 487128731 536870912) BSN.abs_quadSignPos

noncomputable def hp764985 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 882563 1000)) (Enclosure.sfrac Bool.false 882563 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp764986 := hp764985 BSN.quadSignNeg 7 8 9 882563 1000 60 126 536870912 268435456 9007199254740992

noncomputable def hp764987 := hp764986 Bool.false 934392764613 4021 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp764988 := hp764987 Bool.false 147574560 150146 Bool.true 294330740 Bool.true 443779008 28296951008113761 1 Bool.false 458190547

noncomputable def hp764989 := hp764988 Bool.false Bool.false 363664946 Bool.true Bool.false 188347738 183845 BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 458190547 536870912) BSN.abs_quadSignNeg

noncomputable def hp764990 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 882563 1000)) (Enclosure.sfrac Bool.false 882563 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp764991 := hp764990 BSN.quadSignNeg 5 6 7 882563 1000 101 14 536870912 268435456 9007199254740992

noncomputable def hp764992 := hp764991 Bool.false 934392764613 4021 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp764993 := hp764992 Bool.false 341847718 111577 Bool.false 242193788 Bool.false 570547928 28296951008113761 1 Bool.false 234062155

noncomputable def hp764994 := hp764993 Bool.true Bool.false 261182432 Bool.true Bool.false 147574560 150146 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 101 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 234062155 536870912) BSN.abs_quadSignNeg

noncomputable def hp764995 := hp764980 BSN.quadSignPos 3 4 5 882563 1000 329 203 536870912 268435456 9007199254740992

noncomputable def hp764996 := hp764995 Bool.false 934392764613 4021 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp764997 := hp764996 Bool.false 165926997 65949 Bool.false 84864084 Bool.false 612124052 28296951008113761 1 Bool.false 84511113

noncomputable def hp764998 := hp764997 Bool.true Bool.false 487856975 Bool.false Bool.false 341847718 111577 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 329 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 84511113 536870912) BSN.abs_quadSignPos

noncomputable def hp764999 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 882563 1000)) (Enclosure.sfrac Bool.false 882563 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp765000 := hp764999 BSN.quadSignNeg 1 2 3 882563 1000 718 490 536870912 268435456 9007199254740992

noncomputable def hp765001 := hp765000 Bool.false 934392764613 4021 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp765002 := hp765001 Bool.false 536870896 4082 Bool.false 464048318 Bool.false 621375374 28296951008113761 1 Bool.false 348498532

noncomputable def hp765003 := hp765002 Bool.true Bool.false 215671886 Bool.true Bool.false 165926997 65949 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 718 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 348498532 536870912) BSN.abs_quadSignNeg

noncomputable def hp765004 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 882563 1000)) (Enclosure.sfrac Bool.false 882563 1000) 1) Bool.false

noncomputable def hp765005 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 882563 1000)) (Enclosure.sfrac Bool.false 882563 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 882563 1000)))

noncomputable def hp765006 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 882563 1000))) Bool.false 67108862 67108864

noncomputable def hp765007 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 882563 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 14599886947) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false 14599886947 8388608

noncomputable def hp765008 := nat_lit 133351094488611901512213428767131019158377181271670691526661

noncomputable def hp765009 := nat_lit 76619090414170362062374483554897011616114128562683904000

noncomputable def hp765010 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 882563 1000)) Bool.false hp765008 hp765009 133589242410352077749

noncomputable def hp765011 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 882563 4000) (Real.log (Enclosure.sfrac Bool.false 3115670795876 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1765126))))))

noncomputable def hp765012 := nat_lit 257021925347446086540912055540640000

noncomputable def hp765013 := nat_lit 1361028452858376917020679349599579161920

noncomputable def hp765014 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 882563 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp765011 (Enclosure.sfrac Bool.false 882563 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 882563 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp765012 hp765013)) Bool.false

noncomputable def hp765015 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 882563 1000) 882563 1000 3115670795876 16000000 1765126

noncomputable def hp765016 := hp765015 4000 2000 hp765012 hp765013 (@Eq.refl Real (Enclosure.sfrac Bool.false 882563 1000)) rfl rfl rfl rfl

noncomputable def hp765017 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp765011 (Enclosure.sfrac Bool.false 882563 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 882563 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp765012 hp765013) 31353021883438544827381 18014398509481984000

noncomputable def hp765018 := nat_lit 42672350236355808483908297205481926130680698006934621288531520

noncomputable def hp765019 := @hp765017 133589242410352077749 hp738659 hp765012 hp765013 0 1 hp765018 hp765008 hp765009 133589242410352077749 hp738659

noncomputable def hp765020 := @Enclosure.Real.IsNear.subLit_ff_p (hp765011 (Enclosure.sfrac Bool.false 882563 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 882563 2000) (Real.log Real.pi)) 40452961416859467494389 18014398509481984000 11132053839433319 4356000000000000000000

noncomputable def hp765021 := nat_lit 2104065681564701157178615005184000

noncomputable def hp765022 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 882563 4000) (Real.log (Enclosure.sfrac Bool.false 3115670795876 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1765126))))))

noncomputable def hp765023 := @hp765022 (Enclosure.sfrac Bool.false 882563 2000) 9680476442544288323377 3602879701896396800 11132053839433319 4356000000000000000000 882563 2000 0

noncomputable def hp765024 := nat_lit 16181184566743786997755600

noncomputable def hp765025 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 882563 4000) (Real.log (Enclosure.sfrac Bool.false 3115670795876 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1765126))))) 9681890779825735700977

noncomputable def hp765026 := nat_lit 21798495049705660812099000613518442496

noncomputable def hp765027 := @hp765025 3602879701896396800 1002913985353529 396000000000000000000 883960800904611 2251799813685248 200000001089 8712000000000000000 hp765026 9680476442544288323377 3602879701896396800 11132053839433319

noncomputable def hp765028 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 882563 4000) (Real.log (Enclosure.sfrac Bool.false 3115670795876 16000000)) 882563 4000 0 1 54850989560097895 4503599627370496

noncomputable def hp765029 := nat_lit 117791603156928942791720960

noncomputable def hp765030 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3115670795876) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp765029 hp617687

noncomputable def hp765031 := BSN.log_rat_reduce_isNear 3115670795876 16000000 17 6231341591752 4194304000000 106263997 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp765032 := nat_lit 154011840848511685263382206741710120364954040077273255146501670760346986543119462208524463996938997132298670146696046052246966763520

noncomputable def hp765033 := nat_lit 2006013486083266755593813103827975894394041551154646732757420111257626264588426454794290105212556246423819223964778245728322453504

noncomputable def hp765034 := nat_lit 1135330455002443893130943341998846441828309751448100030112840806534585759421836197513507559787342487264265499414686015160320

noncomputable def hp765035 := BSN.log_dyadic_bound 1018518795876 5212822795876 6 5 hp765032 268435456 87120000 hp765033 hp765034 106263997 6231341591752

noncomputable def hp765036 := hp765035 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp765037 := @BSN.binarySplit_of_base5 (BSN.artanhP 1018518795876) (BSN.artanhQ 5212822795876) 0 5 hp765033 hp765032 hp765034 rfl rfl rfl

noncomputable def hp765038 := hp765031 rfl rfl rfl rfl (hp765036 (hp765037 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp765039 := @hp765028 12500018513 1089000000000000000 9681890779825735700977 3602879701896396800 1002913985353529 396000000000000000000 (Enclosure.Real.IsNear.const Bool.false 882563 4000) (BSN.isNear_log_sfrac 3115670795876 16000000 54850989560097895 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp765030 1000001481040000 87120000000000000000000 54850989560097895 4503599627370496 12500018513 1089000000000000000 (hp765038 rfl rfl rfl) rfl)) rfl

noncomputable def hp765040 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1765126)))) 1 4

noncomputable def hp765041 := @hp765040 0 1 883960800904611 562949953421312 200000001089 2178000000000000000 883960800904611 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp765042 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1765126))) 884279719003555 562949953421312 1

noncomputable def hp765043 := @hp765042 2000000000000000 19009 33554432 1 10890000 29660802584619308285952 883960800904611 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp765044 := BSN.arctan_dyadic_bound_f 1000 1765126 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp765045 := hp765044 1 19009 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1765126) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1765126) 0 0 rfl)

noncomputable def hp765046 := hp765041 (hp765043 (hp765045 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp765047 := @hp765020 33899916460443 67108864000 2647689 536870912000 hp765021 31353021883438544827381 18014398509481984000 133589242410352077749 hp738659 (@hp765023 1 hp765024 40452961416859467494389 18014398509481984000 11132053839433319 4356000000000000000000 (@hp765027 4356000000000000000000 hp765039 hp765046 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 882563 2000) rfl rfl)

noncomputable def hp765048 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 882563 2000) (Real.log Real.pi) 882563 2000 0 1 38410761 33554432

noncomputable def hp765049 := hp765047 (@hp765048 3 268435456 33899916460443 67108864000 2647689 536870912000 (Enclosure.Real.IsNear.const Bool.false 882563 2000) hd4909 rfl) rfl

noncomputable def hp765050 := @hp765010 hp738659 14599886947 8388608 63 8388608 (@hp765014 hp765008 hp765009 133589242410352077749 hp738659 (hp765016 rfl rfl rfl rfl rfl) (hp765019 (hp765049 rfl) (Enclosure.Real.IsNear.const Bool.true hp765012 hp765013) rfl rfl)) rfl

noncomputable def hp765051 := nat_lit 1898759095424868946018304

noncomputable def hp765052 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 14599886947) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp765051) (@Nat.cast Real Real.instNatCast hp630689)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp765053 := BSN.sin_reduce_arg_pos_rat_q3 14599886947 8388608 226375608064910080 72057594037927936 276 hp765051 hp630689 rfl rfl rfl rfl

noncomputable def hp765054 := nat_lit 14373792671996510266487483193911963250916658774323111806469590496364758522052593456392776754605911796274389989974677602512940927173744631484416

noncomputable def hp765055 := nat_lit 10236715751341815375786606332081333590462782574928485958353907065112717150107824220178810321889959788852461596296661663371572779392700416

noncomputable def hp765056 := nat_lit 71779698081547845764209755740155829143775211406857332110724369987474877411773305705028829387170338858590335595530101698855257614380463120715776

noncomputable def hp765057 := BSN.sin_dyadic_bound_f 215863917154 137438953472 4 3 67108864 21801270 hp765054 hp737934 hp765055 hp765056 hp737937

noncomputable def hp765058 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215863917154) (BSN.sinEvenQ 137438953472) 0 3 hp765054 hp737934 hp765055 rfl rfl rfl

noncomputable def hp765059 := hp765057 hp765055 67108862 rfl rfl rfl rfl rfl rfl rfl rfl (hp765058 rfl)

noncomputable def hp765060 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215863917154) (BSN.sinOddQ 137438953472) 0 3 hp765056 hp737937 hp765055 rfl rfl rfl

noncomputable def hp765061 := @BSN.sin_arg_round Bool.false 67108862 67108864 hp765051 hp630689 215863917154 137438953472 21801270 21780000 (hp765059 (hp765060 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765062 := hp765052 67108862 67108864 276 1000000000000000 21780000 10890000 hp765053 BSN.pi_near_15 hp765061 rfl rfl

noncomputable def hp765063 := @hp765007 63 8388608 Bool.false 67108862 67108864 1 10890000 hp765050 (Enclosure.sfrac_false_div 14599886947 8388608) (hp765062 rfl rfl) rfl

noncomputable def hp765064 := @hp765004 33554431 33554432 43403663 5709496320000 536870896 536870912 4082 536870912 (@hp765005 Bool.false 33554431 33554432 43403663 5709496320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 882563 1000)) (Enclosure.sfrac Bool.false 882563 1000)) (@hp765006 694458608 91351941120000 33554431 33554432 43403663 5709496320000 (hp765063 rfl) rfl))

noncomputable def hp765065 := @hp765010 hp738659 934392764613 536870912 4021 536870912 (@hp765014 hp765008 hp765009 133589242410352077749 hp738659 (hp765016 rfl rfl rfl rfl rfl) (hp765019 (hp765049 rfl) (Enclosure.Real.IsNear.const Bool.true hp765012 hp765013) rfl rfl)) rfl

noncomputable def hp765066 := hp765003 (BSN.cos_quad_nat2 490 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 215671886 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 882563 1000)) rfl rfl (hp765064 rfl) hp765065

noncomputable def hp765067 := nat_lit 6474196255290930863278425990594116188060993078649646940484026745993625856

noncomputable def hp765068 := nat_lit 2150332519747069631197227873282877704852352078591785156672362646405376

noncomputable def hp765069 := nat_lit 19418288100833298450572883516035782808773274531791757251138735512688066816

noncomputable def hp765070 := BSN.cos_dyadic_bound_f 464048318 536870912 3 2 536870912 268435456 hp765067 hp708868 hp765068 hp765069 hp708870

noncomputable def hp765071 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 464048318) (BSN.cosEvenQ 536870912) 0 2 hp765067 hp708868 hp765068 rfl rfl rfl

noncomputable def hp765072 := hp765070 hp765068 348498532 rfl rfl rfl rfl rfl rfl rfl rfl (hp765071 rfl)

noncomputable def hp765073 := @BSN.binarySplit_of_base2 (BSN.cosOddP 464048318) (BSN.cosOddQ 536870912) 0 2 hp765069 hp708870 hp765068 rfl rfl rfl

noncomputable def hp765074 := nat_lit 20557229079203630107504758328147284133118840478510691753622461405208872098908457492153502634052226847949259411456

noncomputable def hp765075 := nat_lit 3313206086758195605208443358663595848669310207628451364853115246614738881788803933860063770426810546917376

noncomputable def hp765076 := nat_lit 124625126658332506590512674524490734342752196237015284788142535123034846299038327659321643804540408648268730470400

noncomputable def hp765077 := BSN.cos_dyadic_bound_f 621375374 536870912 4 3 536870912 268435456 hp765074 hp716712 hp765075 hp765076 hp716714

noncomputable def hp765078 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 621375374) (BSN.cosEvenQ 536870912) 0 3 hp765074 hp716712 hp765075 rfl rfl rfl

noncomputable def hp765079 := hp765077 hp765075 215671886 rfl rfl rfl rfl rfl rfl rfl rfl (hp765078 rfl)

noncomputable def hp765080 := @BSN.binarySplit_of_base3 (BSN.cosOddP 621375374) (BSN.cosOddQ 536870912) 0 3 hp765076 hp716714 hp765075 rfl rfl rfl

noncomputable def hp765081 := hp765066 hd4911 hd4913 hd4915 hd4917 hd4918 (hp765072 (hp765073 rfl) rfl rfl rfl rfl) (hp765079 (hp765080 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765082 := hp764998 (BSN.cos_quad_nat3 203 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 487856975 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 882563 1000)) rfl rfl (hp765081 rfl rfl rfl rfl rfl) hp765065

noncomputable def hp765083 := nat_lit 51867547304115053878707634811136

noncomputable def hp765084 := BSN.sin_dyadic_bound_f 84864084 536870912 2 1 536870912 268435456 hp765083 hp708890 hp765083 hp765083 hp708891

noncomputable def hp765085 := @BSN.binarySplit_of_base (BSN.sinEvenP 84864084) (BSN.sinEvenQ 536870912) 0 1 hp765083 hp708890 hp765083 rfl rfl rfl

noncomputable def hp765086 := hp765084 hp765083 84511113 rfl rfl rfl rfl rfl rfl rfl rfl (hp765085 rfl)

noncomputable def hp765087 := @BSN.binarySplit_of_base (BSN.sinOddP 84864084) (BSN.sinOddQ 536870912) 0 1 hp765083 hp708891 hp765083 rfl rfl rfl

noncomputable def hp765088 := nat_lit 35290815971337275691104470183454732037290409785848849315535337499492679680

noncomputable def hp765089 := nat_lit 19711313055036168328454689813357704654390259987464791072691188316307456

noncomputable def hp765090 := nat_lit 92396413989508520632741828601731242861558250922957757593236764860444901376

noncomputable def hp765091 := BSN.sin_dyadic_bound_f 612124052 536870912 3 2 536870912 268435456 hp765088 hp708845 hp765089 hp765090 hp708848

noncomputable def hp765092 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 612124052) (BSN.sinEvenQ 536870912) 0 2 hp765088 hp708845 hp765089 rfl rfl rfl

noncomputable def hp765093 := hp765091 hp765089 487856975 rfl rfl rfl rfl rfl rfl rfl rfl (hp765092 rfl)

noncomputable def hp765094 := @BSN.binarySplit_of_base2 (BSN.sinOddP 612124052) (BSN.sinOddQ 536870912) 0 2 hp765090 hp708848 hp765089 rfl rfl rfl

noncomputable def hp765095 := hp765082 hd4920 hd4922 hd4924 hd4926 hd4918 (hp765086 (hp765087 rfl) rfl rfl rfl rfl) (hp765093 (hp765094 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765096 := hp764994 (BSN.cos_quad_nat2 14 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 261182432 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 882563 1000)) rfl rfl (hp765095 rfl rfl rfl rfl rfl) hp765065

noncomputable def hp765097 := nat_lit 864408902467503764825628777529593763862954439605360524981051500175360000

noncomputable def hp765098 := nat_lit 11838699532377066551854139736011666923522646986917515732756421738496

noncomputable def hp765099 := nat_lit 2263908910472790773578419986827458695989861638490346365639186609109794816

noncomputable def hp765100 := BSN.sin_dyadic_bound_f 242193788 536870912 3 2 536870912 268435456 hp765097 hp708845 hp765098 hp765099 hp708848

noncomputable def hp765101 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 242193788) (BSN.sinEvenQ 536870912) 0 2 hp765097 hp708845 hp765098 rfl rfl rfl

noncomputable def hp765102 := hp765100 hp765098 234062155 rfl rfl rfl rfl rfl rfl rfl rfl (hp765101 rfl)

noncomputable def hp765103 := @BSN.binarySplit_of_base2 (BSN.sinOddP 242193788) (BSN.sinOddQ 536870912) 0 2 hp765099 hp708848 hp765098 rfl rfl rfl

noncomputable def hp765104 := nat_lit 14607735314199120753895383342451012514332861731404179411601071847384484634811261080493811882506468802141299408896

noncomputable def hp765105 := nat_lit 1189886645474957555670004148265372624832668494550725505425251478077280426042566170976934296971159342678016

noncomputable def hp765106 := nat_lit 88575432811245406184772500495121072847522337110193095185651029721884559076912501232267809474029991801287218298880

noncomputable def hp765107 := BSN.cos_dyadic_bound_f 570547928 536870912 4 3 536870912 268435456 hp765104 hp716712 hp765105 hp765106 hp716714

noncomputable def hp765108 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 570547928) (BSN.cosEvenQ 536870912) 0 3 hp765104 hp716712 hp765105 rfl rfl rfl

noncomputable def hp765109 := hp765107 hp765105 261182432 rfl rfl rfl rfl rfl rfl rfl rfl (hp765108 rfl)

noncomputable def hp765110 := @BSN.binarySplit_of_base3 (BSN.cosOddP 570547928) (BSN.cosOddQ 536870912) 0 3 hp765106 hp716714 hp765105 rfl rfl rfl

noncomputable def hp765111 := hp765096 hd4928 hd4930 hd4932 hd4934 hd4918 (hp765102 (hp765103 rfl) rfl rfl rfl rfl) (hp765109 (hp765110 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765112 := hp764989 (BSN.cos_quad_nat2 126 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 363664946 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 882563 1000)) rfl rfl (hp765111 rfl rfl rfl rfl rfl) hp765065

noncomputable def hp765113 := nat_lit 1047501419541547707019014600902738463002466380263783251460984156364800000

noncomputable def hp765114 := nat_lit 56322896187267376331878232572061704543744224257794785533977600000000

noncomputable def hp765115 := nat_lit 3142391612832268586304380046243071265598311652342834164811884513894400000

noncomputable def hp765116 := BSN.cos_dyadic_bound_f 294330740 536870912 3 2 536870912 268435456 hp765113 hp708868 hp765114 hp765115 hp708870

noncomputable def hp765117 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 294330740) (BSN.cosEvenQ 536870912) 0 2 hp765113 hp708868 hp765114 rfl rfl rfl

noncomputable def hp765118 := hp765116 hp765114 458190547 rfl rfl rfl rfl rfl rfl rfl rfl (hp765117 rfl)

noncomputable def hp765119 := @BSN.binarySplit_of_base2 (BSN.cosOddP 294330740) (BSN.cosOddQ 536870912) 0 2 hp765115 hp708870 hp765114 rfl rfl rfl

noncomputable def hp765120 := nat_lit 5414725808454086962875946540377975173629565617028038602051541253851447296

noncomputable def hp765121 := nat_lit 1504298561521166099635639632505697654031754756789269488422055068041216

noncomputable def hp765122 := nat_lit 16241168828239218556428568341868914125580633341570537267177779651418259456

noncomputable def hp765123 := BSN.cos_dyadic_bound_f 443779008 536870912 3 2 536870912 268435456 hp765120 hp708868 hp765121 hp765122 hp708870

noncomputable def hp765124 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 443779008) (BSN.cosEvenQ 536870912) 0 2 hp765120 hp708868 hp765121 rfl rfl rfl

noncomputable def hp765125 := hp765123 hp765121 363664946 rfl rfl rfl rfl rfl rfl rfl rfl (hp765124 rfl)

noncomputable def hp765126 := @BSN.binarySplit_of_base2 (BSN.cosOddP 443779008) (BSN.cosOddQ 536870912) 0 2 hp765122 hp708870 hp765121 rfl rfl rfl

noncomputable def hp765127 := hp765112 hd4936 hd4938 hd4940 hd4942 hd4918 (hp765118 (hp765119 rfl) rfl rfl rfl rfl) (hp765125 (hp765126 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765128 := hp764984 (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 224376509 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 882563 1000)) rfl rfl (hp765127 rfl rfl rfl rfl rfl) hp765065

noncomputable def hp765129 := nat_lit 34891398374646081692844789446087393274122093062354118752925786040260689920

noncomputable def hp765130 := nat_lit 19267900465073312094148319511169513264109666582102225373381213972135936

noncomputable def hp765131 := nat_lit 91351038189986761928345827460544136505987399512651669321343965282823110656

noncomputable def hp765132 := BSN.sin_dyadic_bound_f 610385628 536870912 3 2 536870912 268435456 hp765129 hp708845 hp765130 hp765131 hp708848

noncomputable def hp765133 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 610385628) (BSN.sinEvenQ 536870912) 0 2 hp765129 hp708845 hp765130 rfl rfl rfl

noncomputable def hp765134 := hp765132 hp765130 487128731 rfl rfl rfl rfl rfl rfl rfl rfl (hp765133 rfl)

noncomputable def hp765135 := @BSN.binarySplit_of_base2 (BSN.sinOddP 610385628) (BSN.sinOddQ 536870912) 0 2 hp765131 hp708848 hp765130 rfl rfl rfl

noncomputable def hp765136 := nat_lit 721338390206544855875157734655592878818986703353145908580514477224184385

noncomputable def hp765137 := nat_lit 8244144547008835428966351086644840151617979253105356191295143103041

noncomputable def hp765138 := nat_lit 1889206245735493751082337645243841067165672079672781875705609152974506561

noncomputable def hp765139 := BSN.sin_dyadic_bound_f 231482519 536870912 3 2 536870912 268435456 hp765136 hp708845 hp765137 hp765138 hp708848

noncomputable def hp765140 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 231482519) (BSN.sinEvenQ 536870912) 0 2 hp765136 hp708845 hp765137 rfl rfl rfl

noncomputable def hp765141 := hp765139 hp765137 224376509 rfl rfl rfl rfl rfl rfl rfl rfl (hp765140 rfl)

noncomputable def hp765142 := @BSN.binarySplit_of_base2 (BSN.sinOddP 231482519) (BSN.sinOddQ 536870912) 0 2 hp765138 hp708848 hp765137 rfl rfl rfl

noncomputable def hp765143 := hp765128 hd4944 hd4946 hd4961 hd4963 hd4918 (hp765134 (hp765135 rfl) rfl rfl rfl rfl) (hp765141 (hp765142 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765144 := @hp764979 214153 268435456 (hp765143 rfl rfl rfl rfl rfl) (hp765143 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp765145 := @hp764977 Bool.false 101956161 268435456 214153 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 882563 1000)) (Enclosure.sfrac Bool.false 882563 1000) 11) hp765144

noncomputable def hp765146 := @Enclosure.Real.IsNear.mulLit_tf hp764968 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1))) 9746719 33554432 1

noncomputable def hp765147 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp764967 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp765148 := @hp765147 1 1 0 1 9746719 33554432 1 33554432 9746719 33554432 1

noncomputable def hp765149 := @Enclosure.Real.IsNear.of_eq (hp764967 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp765150 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 882563 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp765151 := @hp765149 (@Inv.inv Real Real.instInv (Real.sqrt hp764969)) Bool.false 9746719 33554432 1 33554432 (hp765150 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 882563 1000) 882563 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 882563 1000))))

noncomputable def hp765152 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp764969)) Bool.false 19493438 67108864 2 67108864 9746719 33554432

noncomputable def hp765153 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp764969) Bool.false 231031578 67108864 6 67108864 115515789 33554432 3 33554432

noncomputable def hp765154 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 882563 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp765155 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 882563 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp765156 := @hp765155 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 882563 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9426396812041

noncomputable def hp765157 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 882563 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 882563 1000 0

noncomputable def hp765158 := @hp765157 1 10680707 67108864 1 67108864 9426396812041 67108864000 882563 67108864000 (Enclosure.Real.IsNear.const Bool.false 882563 1000) hd4949

noncomputable def hp765159 := @hp765156 67108864000 882563 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 882563 1000) 882563 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 882563 1000))) (hp765158 rfl)

noncomputable def hp765160 := @hp765154 9426396812041 67108864000 882563 67108864000 397679117 397679155 33554432 hp765159 rfl rfl rfl

noncomputable def hp765161 := @Enclosure.Real.IsNear.recentre' hp764969 Bool.false 795358272 67108864 38 67108864 12427473 1048576 19 33554432 (hp765160 rfl rfl rfl)

noncomputable def hp765162 := @Enclosure.Real.IsNear.sqrt_image hp764969 12427473 1048576 19 33554432 115515786 115515792 33554432 (hp765161 rfl) rfl rfl

noncomputable def hp765163 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp764969) 115515789 33554432 3 33554432 9746718 9746720 33554432 (hp765153 (hp765162 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp765164 := @hp765148 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp765151 (@hp765152 1 33554432 (hp765163 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp765165 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp765166 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp765167 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1))) (hp765165 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765166 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp765168 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 882563 1000) 882563 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 882563 1000)) rfl

noncomputable def hp765169 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp765170 := @hp765169 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765166 (Enclosure.sfrac Bool.false 1 16)))) 14058223

noncomputable def hp765171 := @hp765170 8388608 173 16777216 12594193 33554432 221939027 22837985280000 177051973699039 281474976710656 3861558837513919 191578906023690240000

noncomputable def hp765172 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp765173 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1)))) 2502761

noncomputable def hp765174 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp765175 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 359151697) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp765176 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1))) Bool.false 789782935391678102035

noncomputable def hp765177 := nat_lit 512735433017340492822453701

noncomputable def hp765178 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp765179 := @Enclosure.Real.IsNear.subLit_ff_p hp764969 (Enclosure.sfrac Bool.false 11 1) 12427473 1048576 19 33554432 11 1 0

noncomputable def hp765180 := @hp765178 500000000000000 893137 1048576 19 33554432 789782935391678102035 147573952589676412928 hp765177 hp682805 hd4948 (@hp765179 1 893137 893137 1048576 19 33554432 (hp765161 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp765181 := @hp765175 359151697 67108864 15 4194304 Bool.false 40044176 67108864 1 10890000 (@hp765176 147573952589676412928 hp765177 hp682805 359151697 67108864 15 4194304 (hp765180 rfl) rfl) (Enclosure.sfrac_false_div 359151697 67108864)

noncomputable def hp765182 := nat_lit 6183784677281739963367424

noncomputable def hp765183 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 359151697) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp765182) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp765184 := BSN.sin_reduce_arg_pos_rat_q3 359151697 67108864 226375608064910080 72057594037927936 0 hp765182 hp617687 rfl rfl rfl rfl

noncomputable def hp765185 := nat_lit 64349233810081601028935264064781584119746410520552277697513710492057679841818043190271156480

noncomputable def hp765186 := nat_lit 3556284247392078688908621985870900082438596057505239727157282081458192591146029515940096

noncomputable def hp765187 := nat_lit 168527949804289367900762696686450834094440460303067623581549082355828705369137781450541506816

noncomputable def hp765188 := BSN.sin_dyadic_bound_f 87876865638 137438953472 3 2 67108864 21801270 hp765185 hp738039 hp765186 hp765187 hp738042

noncomputable def hp765189 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 87876865638) (BSN.sinEvenQ 137438953472) 0 2 hp765185 hp738039 hp765186 rfl rfl rfl

noncomputable def hp765190 := hp765188 hp765186 40044176 rfl rfl rfl rfl rfl rfl rfl rfl (hp765189 rfl)

noncomputable def hp765191 := @BSN.binarySplit_of_base2 (BSN.sinOddP 87876865638) (BSN.sinOddQ 137438953472) 0 2 hp765187 hp738042 hp765186 rfl rfl rfl

noncomputable def hp765192 := @BSN.sin_arg_round Bool.false 40044176 67108864 hp765182 hp617687 87876865638 137438953472 21801270 21780000 (hp765190 (hp765191 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765193 := hp765183 40044176 67108864 0 1000000000000000 21780000 10890000 hp765184 BSN.pi_near_15 hp765192 rfl rfl

noncomputable def hp765194 := @hp765173 4194304 10471519 2854748160000 56232546 56233238 33554432 (@hp765174 40044176 67108864 167544304 45675970560000 2502761 4194304 10471519 2854748160000 (hp765181 (hp765193 rfl rfl) rfl rfl) rfl)

noncomputable def hp765195 := @hp765172 Bool.false 112465784 67108864 692 67108864 14058223 8388608 173 16777216 (hp765194 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp765196 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765166 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp765197 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765166 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 4974599)) (@Nat.cast Real Real.instNatCast 4194304)) Bool.true

noncomputable def hp765198 := nat_lit 183530309272528467426014845

noncomputable def hp765199 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765166 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp765198

noncomputable def hp765200 := nat_lit 46512907074782567863614744209271519

noncomputable def hp765201 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765166 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp765202 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp765203 := @hp765202 (Enclosure.sfrac Bool.false 1 16) 138828322143 1099511627776 1723589161 1125899906842624 1 16 0

noncomputable def hp765204 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1)) 797693700769

noncomputable def hp765205 := @hp765204 1099511627776 1086054953 1125899906842624 893137 1048576 19 33554432 145572046719418368 138828322143 1099511627776 1723589161

noncomputable def hp765206 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1)) 893137 1048576 19

noncomputable def hp765207 := @hp765206 33554432 893137 1048576 19 33554432 797693700769 1099511627776 1086054953 1125899906842624 (@hp765179 1 893137 893137 1048576 19 33554432 (hp765161 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp765208 := hp765207 (@hp765179 1 893137 893137 1048576 19 33554432 (hp765161 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp765209 := @hp765205 1125899906842624 (hp765208 rfl) (@hp765179 1 893137 893137 1048576 19 33554432 (hp765161 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp765210 := @hp765201 500000000000000 207547798879 1099511627776 1723589161 1125899906842624 hp765198 hp619308 hp765200 hp682143 hd4948 (@hp765203 1 3320764782064 207547798879 1099511627776 1723589161 1125899906842624 (hp765209 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp765211 := @hp765197 4974599 4194304 323 33554432 Bool.false 12594193 33554432 1 10890000 (@hp765199 hp619308 hp765200 hp682143 4974599 4194304 323 33554432 (hp765210 rfl) rfl) (Enclosure.sfrac_true_div 4974599 4194304)

noncomputable def hp765212 := nat_lit 318781006906376533721786553761134986060324680327724185281

noncomputable def hp765213 := nat_lit 375028804789675170445410456262942489515937413608683201

noncomputable def hp765214 := nat_lit 955592963109550250824468840370879073201942166155955189441

noncomputable def hp765215 := BSN.cos_dyadic_bound_f 4974599 4194304 3 2 33554432 10890000 hp765212 hp632130 hp765213 hp765214 hp632133

noncomputable def hp765216 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 4974599) (BSN.cosEvenQ 4194304) 0 2 hp765212 hp632130 hp765213 rfl rfl rfl

noncomputable def hp765217 := hp765215 hp765213 12594193 rfl rfl rfl rfl rfl rfl rfl rfl (hp765216 rfl)

noncomputable def hp765218 := @BSN.binarySplit_of_base2 (BSN.cosOddP 4974599) (BSN.cosOddQ 4194304) 0 2 hp765214 hp632133 hp765213 rfl rfl rfl

noncomputable def hp765219 := hp765211 (BSN.cos_neg_of_bound 4974599 4194304 Bool.false 12594193 33554432 1 10890000 (hp765217 (hp765218 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp765220 := hp765171 hp765195 (@hp765196 12594193 33554432 3551024432 365407764480000 12594193 33554432 221939027 22837985280000 (hp765219 rfl) rfl)

noncomputable def hp765221 := @hp765146 33554432 177051973699039 281474976710656 3861558837513919 191578906023690240000 1725675836039923703041 9444732965739290427392 7551607750474514603011 hp764965 (hp765164 rfl) (@hp765167 Bool.false 177051973699039 281474976710656 3861558837513919 191578906023690240000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp764969 (Enclosure.sfrac Bool.false 11 1)) (hp765168 rfl (hp764972 rfl rfl))) (hp765220 rfl))

noncomputable def hp765222 := @hp764966 1033231544292757913771011 hp764965 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 882563 1000))) (@hp764971 1033231544292757913771011 hp764965 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 882563 1000) 11 (hp764972 rfl rfl)) (@hp764975 1033231544292757913771011 hp764965 hp765145 (hp765221 rfl) rfl rfl))

theorem hd5069 : hp764964 hp764965 := hp765222

noncomputable def hp765223 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 883834 1000)) Bool.true 1022786759340051033225 2361183241434822606848 1149153454825974457326897

noncomputable def hp765224 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 883834 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 883834 1000)) Bool.true 1022786759340051033225 2361183241434822606848

noncomputable def hp765225 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 883834 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp765226 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp765225 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp765227 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 883834 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp765228 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 883834 1000)) (Enclosure.sfrac Bool.false 883834 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp765226 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp765229 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 883834 1000)) hp765228 Bool.true 1022786759340051033225 2361183241434822606848

noncomputable def hp765230 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 883834 1000) 883834 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 883834 1000)) rfl

noncomputable def hp765231 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 883834 1000)) (Enclosure.sfrac Bool.false 883834 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp765226 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp765232 := nat_lit 34319028766776107270878003200

noncomputable def hp765233 := @hp765231 20794325 33554432 53613 67108864 440483776932151923575 2361183241434822606848 7917911642851697646897 hp758057 hp765232 1022786759340051033225 2361183241434822606848

noncomputable def hp765234 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 883834 1000)) (Enclosure.sfrac Bool.false 883834 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 883834 1000)) (Enclosure.sfrac Bool.false 883834 1000) 11)

noncomputable def hp765235 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 883834 1000)) (Enclosure.sfrac Bool.false 883834 1000) 11) hp765234

noncomputable def hp765236 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 883834 1000)) (Enclosure.sfrac Bool.false 883834 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 883834 1000)) (Enclosure.sfrac Bool.false 883834 1000) 11)

noncomputable def hp765237 := @hp765236 166354600 536870912 214452 536870912 166354600 536870912 214452 536870912 178621891634790400 20794325 33554432

noncomputable def hp765238 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 883834 1000)) (Enclosure.sfrac Bool.false 883834 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp765239 := hp765238 BSN.quadSignPos 9 10 11 883834 1000 185 239 536870912 268435456 9007199254740992

noncomputable def hp765240 := hp765239 Bool.false 936080136428 4026 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp765241 := hp765240 Bool.true 84586074 184101 Bool.true 494212518 Bool.true 180345544 28296951008113761 1 Bool.false 427311767

noncomputable def hp765242 := hp765241 Bool.true Bool.false 176972868 Bool.false Bool.true 166354600 214452 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 185 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 427311767 536870912) BSN.abs_quadSignPos

noncomputable def hp765243 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 883834 1000)) (Enclosure.sfrac Bool.false 883834 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp765244 := hp765243 BSN.quadSignNeg 7 8 9 883834 1000 60 126 536870912 268435456 9007199254740992

noncomputable def hp765245 := hp765244 Bool.false 936080136428 4026 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp765246 := hp765245 Bool.true 115139323 150354 Bool.true 25892745 Bool.true 255711773 28296951008113761 1 Bool.false 536246642

noncomputable def hp765247 := hp765246 Bool.false Bool.false 477115727 Bool.true Bool.true 84586074 184101 BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536246642 536870912) BSN.abs_quadSignNeg

noncomputable def hp765248 := hp765238 BSN.quadSignPos 5 6 7 883834 1000 101 15 536870912 268435456 9007199254740992

noncomputable def hp765249 := hp765248 Bool.false 936080136428 4026 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp765250 := hp765249 Bool.false 64343493 111730 Bool.false 706935372 Bool.false 86787957 28296951008113761 1 Bool.false 519641852

noncomputable def hp765251 := hp765250 Bool.true Bool.false 86410454 Bool.false Bool.true 115139323 150354 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 101 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 519641852 536870912) BSN.abs_quadSignPos

noncomputable def hp765252 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 883834 1000)) (Enclosure.sfrac Bool.false 883834 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp765253 := hp765252 BSN.quadSignPos 3 4 5 883834 1000 329 204 536870912 268435456 9007199254740992

noncomputable def hp765254 := hp765253 Bool.false 936080136428 4026 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp765255 := hp765254 Bool.false 143968267 66037 Bool.false 826280036 Bool.false 357960263 28296951008113761 1 Bool.false 536600678

noncomputable def hp765256 := hp765255 Bool.true Bool.false 421891364 Bool.false Bool.false 64343493 111730 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 329 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536600678 536870912) BSN.abs_quadSignPos

noncomputable def hp765257 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 883834 1000)) (Enclosure.sfrac Bool.false 883834 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp765258 := hp765257 BSN.quadSignPos 1 2 3 883834 1000 719 491 536870912 268435456 9007199254740992

noncomputable def hp765259 := hp765258 Bool.false 936080136428 4026 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp765260 := hp765259 Bool.true 536870520 4082 Bool.false 835127355 Bool.false 715780040 28296951008113761 1 Bool.false 536808481

noncomputable def hp765261 := hp765260 Bool.false Bool.false 521793931 Bool.false Bool.false 143968267 66037 BSN.abs_quadSignPos (BSN.cos_quad_nat3 719 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536808481 536870912) BSN.abs_quadSignPos

noncomputable def hp765262 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 883834 1000)) (Enclosure.sfrac Bool.false 883834 1000) 1) Bool.true

noncomputable def hp765263 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 883834 1000)) (Enclosure.sfrac Bool.false 883834 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 883834 1000)))

noncomputable def hp765264 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 883834 1000))) Bool.true 67108815 67108864

noncomputable def hp765265 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 883834 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 117010017053) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 117010017053 67108864

noncomputable def hp765266 := nat_lit 1052737525482436738699886311943539561600831749341075027807

noncomputable def hp765267 := nat_lit 603777532935326961217311347787592719556900061970432000

noncomputable def hp765268 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 883834 1000)) Bool.false hp765266 hp765267 22296839597646907097

noncomputable def hp765269 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 883834 4000) (Real.log (Enclosure.sfrac Bool.false 3124651158224 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1767668))))))

noncomputable def hp765270 := nat_lit 258877979934166907745054889323520000

noncomputable def hp765271 := nat_lit 1372831168135523878884922277819879854080

noncomputable def hp765272 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 883834 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp765269 (Enclosure.sfrac Bool.false 883834 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 883834 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp765270 hp765271)) Bool.false

noncomputable def hp765273 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 883834 1000) 883834 1000 3124651158224 16000000 1767668

noncomputable def hp765274 := hp765273 4000 2000 hp765270 hp765271 (@Eq.refl Real (Enclosure.sfrac Bool.false 883834 1000)) rfl rfl rfl rfl

noncomputable def hp765275 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp765269 (Enclosure.sfrac Bool.false 883834 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 883834 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp765270 hp765271) 15704820340673875325867 9007199254740992000

noncomputable def hp765276 := nat_lit 21560064521880304408573671668603690221585034226505216569487360

noncomputable def hp765277 := @hp765275 22296839597646907097 hp740893 hp765270 hp765271 0 1 hp765276 hp765266 hp765267 22296839597646907097 hp740893

noncomputable def hp765278 := @Enclosure.Real.IsNear.subLit_ff_p (hp765269 (Enclosure.sfrac Bool.false 883834 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 883834 2000) (Real.log Real.pi)) 20261342627231066010539 9007199254740992000 1857990227160557 726000000000000000000

noncomputable def hp765279 := nat_lit 526966326193358383798282092544000

noncomputable def hp765280 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 883834 4000) (Real.log (Enclosure.sfrac Bool.false 3124651158224 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1767668))))))

noncomputable def hp765281 := @hp765280 (Enclosure.sfrac Bool.false 883834 2000) 24241777100288440972203 9007199254740992000 1857990227160557 726000000000000000000 883834 2000 0

noncomputable def hp765282 := nat_lit 40522685254462132021078000

noncomputable def hp765283 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 883834 4000) (Real.log (Enclosure.sfrac Bool.false 3124651158224 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1767668))))) 24245312945303998744203

noncomputable def hp765284 := nat_lit 54587629157828822901686707197359161344

noncomputable def hp765285 := @hp765283 9007199254740992000 5523970681209421 2178000000000000000000 883961253889443 2251799813685248 200000001089 8712000000000000000 hp765284 24241777100288440972203 9007199254740992000 1857990227160557

noncomputable def hp765286 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 883834 4000) (Real.log (Enclosure.sfrac Bool.false 3124651158224 16000000)) 883834 4000 0 1 54863951704288359 4503599627370496

noncomputable def hp765287 := nat_lit 117819439149620982429253632

noncomputable def hp765288 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3124651158224) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp765287 hp617687

noncomputable def hp765289 := BSN.log_rat_reduce_isNear 3124651158224 16000000 17 6249302316448 4194304000000 107036601 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp765290 := nat_lit 156685735080561039718101066847270188527079250277874926376605007962770380392287625855798764188354234092363980478950452971710206443520

noncomputable def hp765291 := nat_lit 2070546780671976474855514048058567957494714336587910203821252267501392656348956397913676796853331038254016313218591428174365589504

noncomputable def hp765292 := nat_lit 1239500071185124946903324959465438533958935849411035373503486420419932989619259767506558651849470428012840900815535546040320

noncomputable def hp765293 := BSN.log_dyadic_bound 1027499158224 5221803158224 6 5 hp765290 268435456 87120000 hp765291 hp765292 107036601 6249302316448

noncomputable def hp765294 := hp765293 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp765295 := @BSN.binarySplit_of_base5 (BSN.artanhP 1027499158224) (BSN.artanhQ 5221803158224) 0 5 hp765291 hp765290 hp765292 rfl rfl rfl

noncomputable def hp765296 := hp765289 rfl rfl rfl rfl (hp765294 (hp765295 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp765297 := @hp765286 12500018513 1089000000000000000 24245312945303998744203 9007199254740992000 5523970681209421 2178000000000000000000 (Enclosure.Real.IsNear.const Bool.false 883834 4000) (BSN.isNear_log_sfrac 3124651158224 16000000 54863951704288359 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp765288 1000001481040000 87120000000000000000000 54863951704288359 4503599627370496 12500018513 1089000000000000000 (hp765296 rfl rfl rfl) rfl)) rfl

noncomputable def hp765298 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1767668)))) 1 4

noncomputable def hp765299 := @hp765298 0 1 883961253889443 562949953421312 200000001089 2178000000000000000 883961253889443 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp765300 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1767668))) 884279719003555 562949953421312 1

noncomputable def hp765301 := @hp765300 2000000000000000 18982 33554432 1 10890000 29660817784268050661376 883961253889443 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp765302 := BSN.arctan_dyadic_bound_f 1000 1767668 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp765303 := hp765302 1 18982 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1767668) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1767668) 0 0 rfl)

noncomputable def hp765304 := hp765299 (hp765301 (hp765303 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp765305 := @hp765278 16974368268837 33554432000 1325751 268435456000 hp765279 15704820340673875325867 9007199254740992000 22296839597646907097 hp740893 (@hp765281 1 hp765282 20261342627231066010539 9007199254740992000 1857990227160557 726000000000000000000 (@hp765285 726000000000000000000 hp765297 hp765304 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 883834 2000) rfl rfl)

noncomputable def hp765306 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 883834 2000) (Real.log Real.pi) 883834 2000 0 1 38410761 33554432

noncomputable def hp765307 := hp765305 (@hp765306 3 268435456 16974368268837 33554432000 1325751 268435456000 (Enclosure.Real.IsNear.const Bool.false 883834 2000) hd4909 rfl) rfl

noncomputable def hp765308 := @hp765268 hp740893 117010017053 67108864 63 8388608 (@hp765272 hp765266 hp765267 22296839597646907097 hp740893 (hp765274 rfl rfl rfl rfl rfl) (hp765277 (hp765307 rfl) (Enclosure.Real.IsNear.const Bool.true hp765270 hp765271) rfl rfl)) rfl

noncomputable def hp765309 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 117010017053) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 11631406855198936662016) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp765310 := BSN.sin_reduce_arg_pos_rat_q2 117010017053 67108864 226375608064910080 72057594037927936 277 11631406855198936662016 hp617687 rfl rfl rfl rfl

noncomputable def hp765311 := BSN.cos_dyadic_bound_f 165292232 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp765312 := hp765311 1 67108815 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 165292232) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp765313 := hp765312 (@BSN.binarySplit_of_le (BSN.cosOddP 165292232) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp765314 := @BSN.cos_arg_round Bool.false 67108815 67108864 11631406855198936662016 hp617687 165292232 137438953472 21801270 21780000 hp765313 rfl

noncomputable def hp765315 := hp765309 67108815 67108864 277 1000000000000000 21780000 10890000 hp765310 BSN.pi_near_15 hp765314 rfl rfl

noncomputable def hp765316 := @hp765265 63 8388608 Bool.true 67108815 67108864 1 10890000 hp765308 (Enclosure.sfrac_false_div 117010017053 67108864) (hp765315 rfl rfl) rfl

noncomputable def hp765317 := @hp765262 67108815 67108864 43403663 5709496320000 536870520 536870912 4082 536870912 (@hp765263 Bool.true 67108815 67108864 43403663 5709496320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 883834 1000)) (Enclosure.sfrac Bool.false 883834 1000)) (@hp765264 694458608 91351941120000 67108815 67108864 43403663 5709496320000 (hp765316 rfl) rfl))

noncomputable def hp765318 := @hp765268 hp740893 936080136428 536870912 4026 536870912 (@hp765272 hp765266 hp765267 22296839597646907097 hp740893 (hp765274 rfl rfl rfl rfl rfl) (hp765277 (hp765307 rfl) (Enclosure.Real.IsNear.const Bool.true hp765270 hp765271) rfl rfl)) rfl

noncomputable def hp765319 := hp765261 (BSN.cos_quad_nat3 491 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 521793931 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 883834 1000)) rfl rfl (hp765317 rfl) hp765318

noncomputable def hp765320 := nat_lit 174545740565541264647103825318351836722923205387488400228633476033415962570772431454696617071013485889953246540625

noncomputable def hp765321 := nat_lit 115088654647391307702954590333919604071730963612894735334149980679114009477638121411300478301341562744140625

noncomputable def hp765322 := nat_lit 871685673759723260842664269976499007703926163952201892260801617129135146278124056342210887383554390446651256140625

noncomputable def hp765323 := BSN.sin_dyadic_bound_f 835127355 536870912 4 3 536870912 268435456 hp765320 hp642702 hp765321 hp765322 hp642705

noncomputable def hp765324 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 835127355) (BSN.sinEvenQ 536870912) 0 3 hp765320 hp642702 hp765321 rfl rfl rfl

noncomputable def hp765325 := hp765323 hp765321 536808481 rfl rfl rfl rfl rfl rfl rfl rfl (hp765324 rfl)

noncomputable def hp765326 := @BSN.binarySplit_of_base3 (BSN.sinOddP 835127355) (BSN.sinOddQ 536870912) 0 3 hp765322 hp642705 hp765321 rfl rfl rfl

noncomputable def hp765327 := nat_lit 94108753549830698709002902511182506866587044494113951698272734068649260564110070384105729537283178310821478400000

noncomputable def hp765328 := nat_lit 18086519610779467827878128014397453746879655617692438166283922479247068936305827097864061321216000000000000

noncomputable def hp765329 := nat_lit 470240082879583353025198453458840638381017797935680662921438134338334588311962620257836425990693440184123392000000

noncomputable def hp765330 := BSN.sin_dyadic_bound_f 715780040 536870912 4 3 536870912 268435456 hp765327 hp642702 hp765328 hp765329 hp642705

noncomputable def hp765331 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 715780040) (BSN.sinEvenQ 536870912) 0 3 hp765327 hp642702 hp765328 rfl rfl rfl

noncomputable def hp765332 := hp765330 hp765328 521793931 rfl rfl rfl rfl rfl rfl rfl rfl (hp765331 rfl)

noncomputable def hp765333 := @BSN.binarySplit_of_base3 (BSN.sinOddP 715780040) (BSN.sinOddQ 536870912) 0 3 hp765329 hp642705 hp765328 rfl rfl rfl

noncomputable def hp765334 := hp765319 hd4911 hd4913 hd4915 hd4917 hd4918 (hp765325 (hp765326 rfl) rfl rfl rfl rfl) (hp765332 (hp765333 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765335 := hp765256 (BSN.cos_quad_nat0 204 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 421891364 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 883834 1000)) rfl rfl (hp765334 rfl rfl rfl rfl rfl) hp765318

noncomputable def hp765336 := nat_lit 167252427064455932926545094907245439592448482013243798068547379718280874866382637480952743848090957743915528093696

noncomputable def hp765337 := nat_lit 101280798614830342329120854103394925842653056449546128591237754830287685182259324637628995555347182330576896

noncomputable def hp765338 := nat_lit 835304313296227809412691898401328450169824899474427662973730002666065971825687382148791627282170850832360203616256

noncomputable def hp765339 := BSN.sin_dyadic_bound_f 826280036 536870912 4 3 536870912 268435456 hp765336 hp642702 hp765337 hp765338 hp642705

noncomputable def hp765340 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 826280036) (BSN.sinEvenQ 536870912) 0 3 hp765336 hp642702 hp765337 rfl rfl rfl

noncomputable def hp765341 := hp765339 hp765337 536600678 rfl rfl rfl rfl rfl rfl rfl rfl (hp765340 rfl)

noncomputable def hp765342 := @BSN.binarySplit_of_base3 (BSN.sinOddP 826280036) (BSN.sinOddQ 536870912) 0 3 hp765338 hp642705 hp765337 rfl rfl rfl

noncomputable def hp765343 := nat_lit 2291812794276305955026899937036003849426508492426568312004848040239224001

noncomputable def hp765344 := nat_lit 269574338357507946492832578894874025395610312051110903367961863574721

noncomputable def hp765345 := nat_lit 6874899234152202849187714145950221800228734256655602714207808196990522561

noncomputable def hp765346 := BSN.cos_dyadic_bound_f 357960263 536870912 3 2 536870912 268435456 hp765343 hp708868 hp765344 hp765345 hp708870

noncomputable def hp765347 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 357960263) (BSN.cosEvenQ 536870912) 0 2 hp765343 hp708868 hp765344 rfl rfl rfl

noncomputable def hp765348 := hp765346 hp765344 421891364 rfl rfl rfl rfl rfl rfl rfl rfl (hp765347 rfl)

noncomputable def hp765349 := @BSN.binarySplit_of_base2 (BSN.cosOddP 357960263) (BSN.cosOddQ 536870912) 0 2 hp765345 hp708870 hp765344 rfl rfl rfl

noncomputable def hp765350 := hp765335 hd4920 hd4922 hd4924 hd4926 hd4918 (hp765341 (hp765342 rfl) rfl rfl rfl rfl) (hp765348 (hp765349 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765351 := hp765251 (BSN.cos_quad_nat3 15 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 86410454 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 883834 1000)) rfl rfl (hp765350 rfl rfl rfl rfl rfl) hp765318

noncomputable def hp765352 := nat_lit 89538236125215666185443491202048021530101195010784591910219739531557220329954917569970622969632915940640099926016

noncomputable def hp765353 := nat_lit 15579608825286978935378473954263023904856199167808936758252633797061570821904098464820504741804747905826816

noncomputable def hp765354 := nat_lit 447416252504186690661149229481390503150115087730940947486097061056609944644506898657975629991123110586008496766976

noncomputable def hp765355 := BSN.sin_dyadic_bound_f 706935372 536870912 4 3 536870912 268435456 hp765352 hp642702 hp765353 hp765354 hp642705

noncomputable def hp765356 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 706935372) (BSN.sinEvenQ 536870912) 0 3 hp765352 hp642702 hp765353 rfl rfl rfl

noncomputable def hp765357 := hp765355 hp765353 519641852 rfl rfl rfl rfl rfl rfl rfl rfl (hp765356 rfl)

noncomputable def hp765358 := @BSN.binarySplit_of_base3 (BSN.sinOddP 706935372) (BSN.sinOddQ 536870912) 0 3 hp765354 hp642705 hp765353 rfl rfl rfl

noncomputable def hp765359 := nat_lit 56733275792587041647551725354801

noncomputable def hp765360 := BSN.sin_dyadic_bound_f 86787957 536870912 2 1 536870912 268435456 hp765359 hp708890 hp765359 hp765359 hp708891

noncomputable def hp765361 := @BSN.binarySplit_of_base (BSN.sinEvenP 86787957) (BSN.sinEvenQ 536870912) 0 1 hp765359 hp708890 hp765359 rfl rfl rfl

noncomputable def hp765362 := hp765360 hp765359 86410454 rfl rfl rfl rfl rfl rfl rfl rfl (hp765361 rfl)

noncomputable def hp765363 := @BSN.binarySplit_of_base (BSN.sinOddP 86787957) (BSN.sinOddQ 536870912) 0 1 hp765359 hp708891 hp765359 rfl rfl rfl

noncomputable def hp765364 := hp765351 hd4928 hd4930 hd4932 hd4934 hd4918 (hp765357 (hp765358 rfl) rfl rfl rfl rfl) (hp765362 (hp765363 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765365 := hp765247 (BSN.cos_quad_nat2 126 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 477115727 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 883834 1000)) rfl rfl (hp765364 rfl rfl rfl rfl rfl) hp765318

noncomputable def hp765366 := nat_lit 449482075038468059725406750625

noncomputable def hp765367 := BSN.cos_dyadic_bound_f 25892745 536870912 2 1 536870912 268435456 hp765366 hp708767 hp765366 hp765366 hp708768

noncomputable def hp765368 := @BSN.binarySplit_of_base (BSN.cosEvenP 25892745) (BSN.cosEvenQ 536870912) 0 1 hp765366 hp708767 hp765366 rfl rfl rfl

noncomputable def hp765369 := hp765367 hp765366 536246642 rfl rfl rfl rfl rfl rfl rfl rfl (hp765368 rfl)

noncomputable def hp765370 := @BSN.binarySplit_of_base (BSN.cosOddP 25892745) (BSN.cosOddQ 536870912) 0 1 hp765366 hp708768 hp765366 rfl rfl rfl

noncomputable def hp765371 := nat_lit 596767243675594709044951092595466699498007631760454241205816994017676961

noncomputable def hp765372 := nat_lit 18281245785603027531173406766125510984727797803320319461456400453281

noncomputable def hp765373 := nat_lit 1790265168535212921079790930972867847472053439685756082978528069252124321

noncomputable def hp765374 := BSN.cos_dyadic_bound_f 255711773 536870912 3 2 536870912 268435456 hp765371 hp708868 hp765372 hp765373 hp708870

noncomputable def hp765375 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 255711773) (BSN.cosEvenQ 536870912) 0 2 hp765371 hp708868 hp765372 rfl rfl rfl

noncomputable def hp765376 := hp765374 hp765372 477115727 rfl rfl rfl rfl rfl rfl rfl rfl (hp765375 rfl)

noncomputable def hp765377 := @BSN.binarySplit_of_base2 (BSN.cosOddP 255711773) (BSN.cosOddQ 536870912) 0 2 hp765373 hp708870 hp765372 rfl rfl rfl

noncomputable def hp765378 := hp765365 hd4936 hd4938 hd4940 hd4942 hd4918 (hp765369 (hp765370 rfl) rfl rfl rfl rfl) (hp765376 (hp765377 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765379 := hp765242 (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 176972868 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 883834 1000)) rfl rfl (hp765378 rfl rfl rfl rfl rfl) hp765318

noncomputable def hp765380 := nat_lit 14990612087677174864582095574571354585037046368450700941446079545474883840

noncomputable def hp765381 := nat_lit 3558852037916124795006193373023015633203373497731785707788471538360576

noncomputable def hp765382 := nat_lit 39255364945378831871856430763178177125976601693612651003117598427086397696

noncomputable def hp765383 := BSN.sin_dyadic_bound_f 494212518 536870912 3 2 536870912 268435456 hp765380 hp708845 hp765381 hp765382 hp708848

noncomputable def hp765384 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 494212518) (BSN.sinEvenQ 536870912) 0 2 hp765380 hp708845 hp765381 rfl rfl rfl

noncomputable def hp765385 := hp765383 hp765381 427311767 rfl rfl rfl rfl rfl rfl rfl rfl (hp765384 rfl)

noncomputable def hp765386 := @BSN.binarySplit_of_base2 (BSN.sinOddP 494212518) (BSN.sinOddQ 536870912) 0 2 hp765382 hp708848 hp765381 rfl rfl rfl

noncomputable def hp765387 := nat_lit 1057844091639660258457359532036096

noncomputable def hp765388 := BSN.sin_dyadic_bound_f 180345544 536870912 2 1 536870912 268435456 hp765387 hp708890 hp765387 hp765387 hp708891

noncomputable def hp765389 := @BSN.binarySplit_of_base (BSN.sinEvenP 180345544) (BSN.sinEvenQ 536870912) 0 1 hp765387 hp708890 hp765387 rfl rfl rfl

noncomputable def hp765390 := hp765388 hp765387 176972868 rfl rfl rfl rfl rfl rfl rfl rfl (hp765389 rfl)

noncomputable def hp765391 := @BSN.binarySplit_of_base (BSN.sinOddP 180345544) (BSN.sinOddQ 536870912) 0 1 hp765387 hp708891 hp765387 rfl rfl rfl

noncomputable def hp765392 := hp765379 hd4944 hd4946 hd4961 hd4963 hd4918 (hp765385 (hp765386 rfl) rfl rfl rfl rfl) (hp765390 (hp765391 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765393 := @hp765237 53613 67108864 (hp765392 rfl rfl rfl rfl rfl) (hp765392 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp765394 := @hp765235 Bool.true 20794325 33554432 53613 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 883834 1000)) (Enclosure.sfrac Bool.false 883834 1000) 11) hp765393

noncomputable def hp765395 := @Enclosure.Real.IsNear.mulLit_tf hp765226 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1))) 9743213 33554432 1

noncomputable def hp765396 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp765225 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp765397 := @hp765396 1 1 0 1 9743213 33554432 1 33554432 9743213 33554432 1

noncomputable def hp765398 := @Enclosure.Real.IsNear.of_eq (hp765225 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp765399 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 883834 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp765400 := @hp765398 (@Inv.inv Real Real.instInv (Real.sqrt hp765227)) Bool.false 9743213 33554432 1 33554432 (hp765399 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 883834 1000) 883834 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 883834 1000))))

noncomputable def hp765401 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp765227)) Bool.false 19486426 67108864 2 67108864 9743213 33554432

noncomputable def hp765402 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp765227) Bool.false 231114712 67108864 6 67108864 28889339 8388608 3 33554432

noncomputable def hp765403 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 883834 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp765404 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 883834 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp765405 := @hp765404 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 883834 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 4719985995319

noncomputable def hp765406 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 883834 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 883834 1000 0

noncomputable def hp765407 := @hp765406 1 10680707 67108864 1 67108864 4719985995319 33554432000 441917 33554432000 (Enclosure.Real.IsNear.const Bool.false 883834 1000) hd4949

noncomputable def hp765408 := @hp765405 33554432000 441917 33554432000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 883834 1000) 883834 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 883834 1000))) (hp765407 rfl)

noncomputable def hp765409 := @hp765403 4719985995319 33554432000 441917 33554432000 397965368 397965406 33554432 hp765408 rfl rfl rfl

noncomputable def hp765410 := @Enclosure.Real.IsNear.recentre' hp765227 Bool.false 795930774 67108864 38 67108864 397965387 33554432 19 33554432 (hp765409 rfl rfl rfl)

noncomputable def hp765411 := @Enclosure.Real.IsNear.sqrt_image hp765227 397965387 33554432 19 33554432 115557353 115557359 33554432 (hp765410 rfl) rfl rfl

noncomputable def hp765412 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp765227) 28889339 8388608 3 33554432 9743212 9743214 33554432 (hp765402 (hp765411 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp765413 := @hp765397 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp765400 (@hp765401 1 33554432 (hp765412 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp765414 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp765415 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp765416 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1))) (hp765414 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765415 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp765417 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 883834 1000) 883834 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 883834 1000)) rfl

noncomputable def hp765418 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp765419 := @hp765418 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765415 (Enclosure.sfrac Bool.false 1 16)))) 13130995

noncomputable def hp765420 := @hp765419 8388608 151 16777216 3442945 8388608 447281179 45675970560000 45209293580275 70368744177664 4859111184606413 255438541364920320000

noncomputable def hp765421 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp765422 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1)))) 42871843

noncomputable def hp765423 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp765424 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 362748833) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp765425 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1))) Bool.false 25526179886378185887425

noncomputable def hp765426 := nat_lit 512735433019799370189348293

noncomputable def hp765427 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp765428 := @Enclosure.Real.IsNear.subLit_ff_p hp765227 (Enclosure.sfrac Bool.false 11 1) 397965387 33554432 19 33554432 11 1 0

noncomputable def hp765429 := @hp765427 500000000000000 28866635 33554432 19 33554432 25526179886378185887425 4722366482869645213696 hp765426 hp682805 hd4948 (@hp765428 1 28866635 28866635 33554432 19 33554432 (hp765410 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp765430 := @hp765424 362748833 67108864 15 4194304 Bool.false 42871843 67108864 1 10890000 (@hp765425 4722366482869645213696 hp765426 hp682805 362748833 67108864 15 4194304 (hp765429 rfl) rfl) (Enclosure.sfrac_false_div 362748833 67108864)

noncomputable def hp765431 := nat_lit 6702186608456171851350016

noncomputable def hp765432 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 362748833) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp765431) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp765433 := BSN.sin_reduce_arg_pos_rat_q3 362748833 67108864 226375608064910080 72057594037927936 0 hp765431 hp617687 rfl rfl rfl rfl

noncomputable def hp765434 := nat_lit 88797579143833007991323916554007343842569161039125709525928854125659099735925742438846439680

noncomputable def hp765435 := nat_lit 6771637808991034534669726328134255230485727985414659963216265626026841488936059529994496

noncomputable def hp765436 := nat_lit 232554124629776654492792220941678445079212730590495710737492267803807884422156762291073065216

noncomputable def hp765437 := BSN.sin_dyadic_bound_f 95243800166 137438953472 3 2 67108864 21801270 hp765434 hp738039 hp765435 hp765436 hp738042

noncomputable def hp765438 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 95243800166) (BSN.sinEvenQ 137438953472) 0 2 hp765434 hp738039 hp765435 rfl rfl rfl

noncomputable def hp765439 := hp765437 hp765435 42871843 rfl rfl rfl rfl rfl rfl rfl rfl (hp765438 rfl)

noncomputable def hp765440 := @BSN.binarySplit_of_base2 (BSN.sinOddP 95243800166) (BSN.sinOddQ 137438953472) 0 2 hp765436 hp738042 hp765435 rfl rfl rfl

noncomputable def hp765441 := @BSN.sin_arg_round Bool.false 42871843 67108864 hp765431 hp617687 95243800166 137438953472 21801270 21780000 (hp765439 (hp765440 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765442 := hp765432 42871843 67108864 0 1000000000000000 21780000 10890000 hp765433 BSN.pi_near_15 hp765441 rfl rfl

noncomputable def hp765443 := @hp765422 67108864 10471519 2854748160000 52523678 52524282 33554432 (@hp765423 42871843 67108864 167544304 45675970560000 42871843 67108864 10471519 2854748160000 (hp765430 (hp765442 rfl rfl) rfl rfl) rfl)

noncomputable def hp765444 := @hp765421 Bool.false 105047960 67108864 604 67108864 13130995 8388608 151 16777216 (hp765443 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp765445 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765415 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp765446 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765415 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 38516113)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp765447 := nat_lit 181887202820881769550480848245

noncomputable def hp765448 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765415 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp765447

noncomputable def hp765449 := nat_lit 46806449135456561070316211985045261

noncomputable def hp765450 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765415 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp765451 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp765452 := @hp765451 (Enclosure.sfrac Bool.false 1 16) 135320924953095 1125899906842624 1734466699 1125899906842624 1 16 0

noncomputable def hp765453 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1)) 833282616223225

noncomputable def hp765454 := @hp765453 1125899906842624 1096932491 1125899906842624 28866635 33554432 19 33554432 4540616774515729367040 135320924953095 1125899906842624 1734466699

noncomputable def hp765455 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1)) 28866635 33554432 19

noncomputable def hp765456 := @hp765455 33554432 28866635 33554432 19 33554432 833282616223225 1125899906842624 1096932491 1125899906842624 (@hp765428 1 28866635 28866635 33554432 19 33554432 (hp765410 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp765457 := hp765456 (@hp765428 1 28866635 28866635 33554432 19 33554432 (hp765410 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp765458 := @hp765454 1125899906842624 (hp765457 rfl) (@hp765428 1 28866635 28866635 33554432 19 33554432 (hp765410 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp765459 := @hp765450 500000000000000 205689669130759 1125899906842624 1734466699 1125899906842624 hp765447 hp682141 hp765449 hp682143 hd4948 (@hp765452 1 3291034706092144 205689669130759 1125899906842624 1734466699 1125899906842624 (hp765458 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp765460 := @hp765446 38516113 33554432 651 67108864 Bool.false 13771780 33554432 1 10890000 (@hp765448 hp682141 hp765449 hp682143 38516113 33554432 651 67108864 (hp765459 rfl) rfl) (Enclosure.sfrac_true_div 38516113 33554432)

noncomputable def hp765461 := nat_lit 4691667406703605178627028738480462586562473536758136052424476801

noncomputable def hp765462 := nat_lit 4843280448842261922134166853991992896779434019557328613640321

noncomputable def hp765463 := nat_lit 14065315659213131012036817881733403773893861742235293500046149761

noncomputable def hp765464 := BSN.cos_dyadic_bound_f 38516113 33554432 3 2 33554432 10890000 hp765461 hp684401 hp765462 hp765463 hp684404

noncomputable def hp765465 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 38516113) (BSN.cosEvenQ 33554432) 0 2 hp765461 hp684401 hp765462 rfl rfl rfl

noncomputable def hp765466 := hp765464 hp765462 13771780 rfl rfl rfl rfl rfl rfl rfl rfl (hp765465 rfl)

noncomputable def hp765467 := @BSN.binarySplit_of_base2 (BSN.cosOddP 38516113) (BSN.cosOddQ 33554432) 0 2 hp765463 hp684404 hp765462 rfl rfl rfl

noncomputable def hp765468 := hp765460 (BSN.cos_neg_of_bound 38516113 33554432 Bool.false 13771780 33554432 1 10890000 (hp765466 (hp765467 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp765469 := hp765420 hp765444 (@hp765445 13771780 33554432 7156498864 730815528960000 3442945 8388608 447281179 45675970560000 (hp765468 rfl) rfl)

noncomputable def hp765470 := @hp765395 33554432 45209293580275 70368744177664 4859111184606413 255438541364920320000 440483776932151923575 2361183241434822606848 7917911642851697646897 hp758057 (hp765413 rfl) (@hp765416 Bool.false 45209293580275 70368744177664 4859111184606413 255438541364920320000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765227 (Enclosure.sfrac Bool.false 11 1)) (hp765417 rfl (hp765230 rfl rfl))) (hp765469 rfl))

noncomputable def hp765471 := @hp765224 1149153454825974457326897 hp758057 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 883834 1000))) (@hp765229 1149153454825974457326897 hp758057 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 883834 1000) 11 (hp765230 rfl rfl)) (@hp765233 1149153454825974457326897 hp758057 hp765394 (hp765470 rfl) rfl rfl))

theorem hd5070 : hp765223 hp758057 := hp765471

noncomputable def hp765472 := nat_lit 41415531353128672575026459

noncomputable def hp765473 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 885104 1000)) Bool.false 691498028078457515615 1180591620717411303424 hp765472

noncomputable def hp765474 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 885104 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 885104 1000)) Bool.false 691498028078457515615 1180591620717411303424

noncomputable def hp765475 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 885104 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp765476 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp765475 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp765477 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 885104 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp765478 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 885104 1000)) (Enclosure.sfrac Bool.false 885104 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp765476 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp765479 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 885104 1000)) hp765478 Bool.false 691498028078457515615 1180591620717411303424

noncomputable def hp765480 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 885104 1000) 885104 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 885104 1000)) rfl

noncomputable def hp765481 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 885104 1000)) (Enclosure.sfrac Bool.false 885104 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp765476 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp765482 := nat_lit 46405647122585386745184911360

noncomputable def hp765483 := @hp765481 26522405 67108864 13423 16777216 224910944973108375135 1180591620717411303424 270512864232767110706459 hp738860 hp765482 691498028078457515615 1180591620717411303424

noncomputable def hp765484 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 885104 1000)) (Enclosure.sfrac Bool.false 885104 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 885104 1000)) (Enclosure.sfrac Bool.false 885104 1000) 11)

noncomputable def hp765485 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 885104 1000)) (Enclosure.sfrac Bool.false 885104 1000) 11) hp765484

noncomputable def hp765486 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 885104 1000)) (Enclosure.sfrac Bool.false 885104 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 885104 1000)) (Enclosure.sfrac Bool.false 885104 1000) 11)

noncomputable def hp765487 := @hp765486 106089620 536870912 214768 536870912 106089620 536870912 214768 536870912 113912862086266880 26522405 67108864

noncomputable def hp765488 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 885104 1000)) (Enclosure.sfrac Bool.false 885104 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp765489 := hp765488 BSN.quadSignPos 9 10 11 885104 1000 185 239 536870912 268435456 9007199254740992

noncomputable def hp765490 := hp765489 Bool.false 937766670621 4033 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp765491 := hp765490 Bool.false 177451831 184372 Bool.true 377640839 Bool.true 128758830 28296951008113761 1 Bool.false 347260302

noncomputable def hp765492 := hp765491 Bool.true Bool.false 127528020 Bool.false Bool.false 106089620 214768 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 185 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 347260302 536870912) BSN.abs_quadSignPos

noncomputable def hp765493 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 885104 1000)) (Enclosure.sfrac Bool.false 885104 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp765494 := hp765493 BSN.quadSignNeg 7 8 9 885104 1000 59 126 536870912 268435456 9007199254740992

noncomputable def hp765495 := hp765494 Bool.false 937766670621 4033 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp765496 := hp765495 Bool.false 184278238 150576 Bool.true 600490837 Bool.true 67302534 28296951008113761 1 Bool.false 482886659

noncomputable def hp765497 := hp765496 Bool.false Bool.false 532657886 Bool.true Bool.false 177451831 184372 BSN.abs_quadSignPos (BSN.cos_quad_nat3 59 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 482886659 536870912) BSN.abs_quadSignNeg

noncomputable def hp765498 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 885104 1000)) (Enclosure.sfrac Bool.false 885104 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp765499 := hp765498 BSN.quadSignPos 5 6 7 885104 1000 102 15 536870912 268435456 9007199254740992

noncomputable def hp765500 := hp765499 Bool.false 937766670621 4033 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp765501 := hp765500 Bool.false 213711879 111895 Bool.false 328486422 Bool.false 446549923 28296951008113761 1 Bool.false 439474325

noncomputable def hp765502 := hp765501 Bool.true Bool.false 396812423 Bool.false Bool.false 184278238 150576 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 102 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 439474325 536870912) BSN.abs_quadSignPos

noncomputable def hp765503 := hp765498 BSN.quadSignNeg 3 4 5 885104 1000 330 205 536870912 268435456 9007199254740992

noncomputable def hp765504 := hp765503 Bool.false 937766670621 4033 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp765505 := hp765504 Bool.false 318881226 66135 Bool.false 724287770 Bool.false 103822911 28296951008113761 1 Bool.false 118054386

noncomputable def hp765506 := hp765505 Bool.true Bool.false 103176994 Bool.true Bool.false 213711879 111895 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 330 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 118054386 536870912) BSN.abs_quadSignNeg

noncomputable def hp765507 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 885104 1000)) (Enclosure.sfrac Bool.false 885104 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp765508 := hp765507 BSN.quadSignPos 1 2 3 885104 1000 721 492 536870912 268435456 9007199254740992

noncomputable def hp765509 := hp765508 Bool.false 937766670621 4033 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp765510 := hp765509 Bool.false 536870624 4090 Bool.false 362426044 Bool.false 809936897 28296951008113761 1 Bool.false 335518997

noncomputable def hp765511 := hp765510 Bool.true Bool.false 33356461 Bool.false Bool.false 318881226 66135 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 721 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 335518997 536870912) BSN.abs_quadSignPos

noncomputable def hp765512 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 885104 1000)) (Enclosure.sfrac Bool.false 885104 1000) 1) Bool.false

noncomputable def hp765513 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 885104 1000)) (Enclosure.sfrac Bool.false 885104 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 885104 1000)))

noncomputable def hp765514 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 885104 1000))) Bool.false 67108828 67108864

noncomputable def hp765515 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 885104 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 117220833827) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 117220833827 67108864

noncomputable def hp765516 := nat_lit 2077655318777488228754791861711504475754870501793224053

noncomputable def hp765517 := nat_lit 1189456546876396681162520102348753014126087766016000

noncomputable def hp765518 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 885104 1000)) Bool.false hp765516 hp765517 8373292616275452737

noncomputable def hp765519 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 885104 4000) (Real.log (Enclosure.sfrac Bool.false 3133637363264 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1770208))))))

noncomputable def hp765520 := nat_lit 260743268742803352074396733931520000

noncomputable def hp765521 := nat_lit 1384709667037702958521572992145960468480

noncomputable def hp765522 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 885104 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp765519 (Enclosure.sfrac Bool.false 885104 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 885104 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp765520 hp765521)) Bool.false

noncomputable def hp765523 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 885104 1000) 885104 1000 3133637363264 16000000 1770208

noncomputable def hp765524 := hp765523 4000 2000 hp765520 hp765521 (@Eq.refl Real (Enclosure.sfrac Bool.false 885104 1000)) rfl rfl rfl rfl

noncomputable def hp765525 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp765519 (Enclosure.sfrac Bool.false 885104 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 885104 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp765520 hp765521) 1966639460837029913317 1125899906842624000

noncomputable def hp765526 := nat_lit 2723224379428029371193480788982503146461423864110414630748160

noncomputable def hp765527 := @hp765525 8373292616275452737 1115136000000000000000000 hp765520 hp765521 0 1 hp765526 hp765516 hp765517 8373292616275452737 1115136000000000000000000

noncomputable def hp765528 := @Enclosure.Real.IsNear.subLit_ff_p (hp765519 (Enclosure.sfrac Bool.false 885104 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 885104 2000) (Real.log Real.pi)) 2537023167211885896421 1125899906842624000 2790954096618713 1089000000000000000000

noncomputable def hp765529 := nat_lit 8248683757146597913545146368000

noncomputable def hp765530 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 885104 4000) (Real.log (Enclosure.sfrac Bool.false 3133637363264 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1770208))))))

noncomputable def hp765531 := @hp765530 (Enclosure.sfrac Bool.false 885104 2000) 3035292422784902832869 1125899906842624000 2790954096618713 1089000000000000000000 885104 2000 0

noncomputable def hp765532 := nat_lit 5074046334423771792842000

noncomputable def hp765533 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 885104 4000) (Real.log (Enclosure.sfrac Bool.false 3133637363264 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1770208))))) 3035734403638339970369

noncomputable def hp765534 := nat_lit 6834870912107289200406093549914816512

noncomputable def hp765535 := @hp765533 1125899906842624000 62862593101877 24750000000000000000 883961706874275 2251799813685248 200000001089 8712000000000000000 hp765534 3035292422784902832869 1125899906842624000 2790954096618713

noncomputable def hp765536 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 885104 4000) (Real.log (Enclosure.sfrac Bool.false 3133637363264 16000000)) 885104 4000 0 1 54876885041998951 4503599627370496

noncomputable def hp765537 := nat_lit 117847213280868540505653248

noncomputable def hp765538 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3133637363264) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp765537 hp617687

noncomputable def hp765539 := BSN.log_rat_reduce_isNear 3133637363264 16000000 17 6267274726528 4194304000000 107807488 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp765540 := nat_lit 159403118317574270286831138579219162013716985720689911517582204394091867683402872795566984188515951140732747718582965927140676075520

noncomputable def hp765541 := nat_lit 2136825623780802158249025558754162314371031158958526908069801258918186093205753540673579627880344121384976905918519649311500795904

noncomputable def hp765542 := nat_lit 1352270407769583312603349688133081505529951994539308561226237038829579635431577658569487275705120232461790696352155770552320

noncomputable def hp765543 := BSN.log_dyadic_bound 1036485363264 5230789363264 6 5 hp765540 268435456 87120000 hp765541 hp765542 107807488 6267274726528

noncomputable def hp765544 := hp765543 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp765545 := @BSN.binarySplit_of_base5 (BSN.artanhP 1036485363264) (BSN.artanhQ 5230789363264) 0 5 hp765541 hp765540 hp765542 rfl rfl rfl

noncomputable def hp765546 := hp765539 rfl rfl rfl rfl (hp765544 (hp765545 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp765547 := @hp765536 12500018513 1089000000000000000 3035734403638339970369 1125899906842624000 62862593101877 24750000000000000000 (Enclosure.Real.IsNear.const Bool.false 885104 4000) (BSN.isNear_log_sfrac 3133637363264 16000000 54876885041998951 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp765538 1000001481040000 87120000000000000000000 54876885041998951 4503599627370496 12500018513 1089000000000000000 (hp765546 rfl rfl rfl) rfl)) rfl

noncomputable def hp765548 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1770208)))) 1 4

noncomputable def hp765549 := @hp765548 0 1 883961706874275 562949953421312 200000001089 2178000000000000000 883961706874275 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp765550 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1770208))) 884279719003555 562949953421312 1

noncomputable def hp765551 := @hp765550 2000000000000000 18955 33554432 1 10890000 29660832983916793036800 883961706874275 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp765552 := BSN.arctan_dyadic_bound_f 1000 1770208 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp765553 := hp765552 1 18955 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1770208) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1770208) 0 0 rfl)

noncomputable def hp765554 := hp765549 (hp765551 (hp765553 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp765555 := @hp765528 2124844887759 4194304000 165957 33554432000 hp765529 1966639460837029913317 1125899906842624000 8373292616275452737 1115136000000000000000000 (@hp765531 1 hp765532 2537023167211885896421 1125899906842624000 2790954096618713 1089000000000000000000 (@hp765535 1089000000000000000000 hp765547 hp765554 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 885104 2000) rfl rfl)

noncomputable def hp765556 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 885104 2000) (Real.log Real.pi) 885104 2000 0 1 38410761 33554432

noncomputable def hp765557 := hp765555 (@hp765556 3 268435456 2124844887759 4194304000 165957 33554432000 (Enclosure.Real.IsNear.const Bool.false 885104 2000) hd4909 rfl) rfl

noncomputable def hp765558 := @hp765518 1115136000000000000000000 117220833827 67108864 505 67108864 (@hp765522 hp765516 hp765517 8373292616275452737 1115136000000000000000000 (hp765524 rfl rfl rfl rfl rfl) (hp765527 (hp765557 rfl) (Enclosure.Real.IsNear.const Bool.true hp765520 hp765521) rfl rfl)) rfl

noncomputable def hp765559 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 117220833827) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 9910652319693698760704) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp765560 := BSN.sin_reduce_arg_pos_rat_q0 117220833827 67108864 226375608064910080 72057594037927936 278 9910652319693698760704 hp617687 rfl rfl rfl rfl

noncomputable def hp765561 := BSN.cos_dyadic_bound_f 140838840 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp765562 := hp765561 1 67108828 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 140838840) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp765563 := hp765562 (@BSN.binarySplit_of_le (BSN.cosOddP 140838840) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp765564 := @BSN.cos_arg_round Bool.false 67108828 67108864 9910652319693698760704 hp617687 140838840 137438953472 21801270 21780000 hp765563 rfl

noncomputable def hp765565 := hp765559 67108828 67108864 278 1000000000000000 21780000 10890000 hp765560 BSN.pi_near_15 hp765564 rfl rfl

noncomputable def hp765566 := @hp765515 505 67108864 Bool.false 67108828 67108864 1 10890000 hp765558 (Enclosure.sfrac_false_div 117220833827 67108864) (hp765565 rfl rfl) rfl

noncomputable def hp765567 := @hp765512 16777207 16777216 347909929 45675970560000 536870624 536870912 4090 536870912 (@hp765513 Bool.false 16777207 16777216 347909929 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 885104 1000)) (Enclosure.sfrac Bool.false 885104 1000)) (@hp765514 5566558864 730815528960000 16777207 16777216 347909929 45675970560000 (hp765566 rfl) rfl))

noncomputable def hp765568 := @hp765518 1115136000000000000000000 937766670621 536870912 4033 536870912 (@hp765522 hp765516 hp765517 8373292616275452737 1115136000000000000000000 (hp765524 rfl rfl rfl rfl rfl) (hp765527 (hp765557 rfl) (Enclosure.Real.IsNear.const Bool.true hp765520 hp765521) rfl rfl)) rfl

noncomputable def hp765569 := hp765511 (BSN.cos_quad_nat0 492 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 33356461 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 885104 1000)) rfl rfl (hp765567 rfl) hp765568

noncomputable def hp765570 := nat_lit 4334796396131245990906380515414167657484848974521467761604820948823900160

noncomputable def hp765571 := nat_lit 297683791722907859442042382148205415488500223103832145143467270537216

noncomputable def hp765572 := nat_lit 11352556216109521458696661852704103913216194504337866504539536871338868736

noncomputable def hp765573 := BSN.sin_dyadic_bound_f 362426044 536870912 3 2 536870912 268435456 hp765570 hp708845 hp765571 hp765572 hp708848

noncomputable def hp765574 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 362426044) (BSN.sinEvenQ 536870912) 0 2 hp765570 hp708845 hp765571 rfl rfl rfl

noncomputable def hp765575 := hp765573 hp765571 335518997 rfl rfl rfl rfl rfl rfl rfl rfl (hp765574 rfl)

noncomputable def hp765576 := @BSN.binarySplit_of_base2 (BSN.sinOddP 362426044) (BSN.sinOddQ 536870912) 0 2 hp765572 hp708848 hp765571 rfl rfl rfl

noncomputable def hp765577 := nat_lit 59460291581101248689218691092078102510677692330907284959032926979076974842758577455820752358684072806722449694721

noncomputable def hp765578 := nat_lit 79691904622400396789085887107981633390226126159183568407035605952242361563110697609990598536520156322979841

noncomputable def hp765579 := nat_lit 359986161196264271153636826969551703958498713113426797717068167891220958579075303109025450167187099216304428539905

noncomputable def hp765580 := BSN.cos_dyadic_bound_f 809936897 536870912 4 3 536870912 268435456 hp765577 hp716712 hp765578 hp765579 hp716714

noncomputable def hp765581 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 809936897) (BSN.cosEvenQ 536870912) 0 3 hp765577 hp716712 hp765578 rfl rfl rfl

noncomputable def hp765582 := hp765580 hp765578 33356461 rfl rfl rfl rfl rfl rfl rfl rfl (hp765581 rfl)

noncomputable def hp765583 := @BSN.binarySplit_of_base3 (BSN.cosOddP 809936897) (BSN.cosOddQ 536870912) 0 3 hp765579 hp716714 hp765578 rfl rfl rfl

noncomputable def hp765584 := hp765569 hd4911 hd4913 hd4915 hd4917 hd4918 (hp765575 (hp765576 rfl) rfl rfl rfl rfl) (hp765582 (hp765583 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765585 := hp765506 (BSN.cos_quad_nat1 205 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 103176994 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 885104 1000)) rfl rfl (hp765584 rfl rfl rfl rfl rfl) hp765568

noncomputable def hp765586 := nat_lit 37982631266480847823962712473749244708704175354856266864747474114969419621385740252295006073852962334825024000000

noncomputable def hp765587 := nat_lit 20841732788692438858597100752932687536872500191535857280267037142772813118094819232235594209121000000000000

noncomputable def hp765588 := nat_lit 230125553325346774358976442895262092797060997201106443182773864930073324169263865875788300352288253446288345600000

noncomputable def hp765589 := BSN.cos_dyadic_bound_f 724287770 536870912 4 3 536870912 268435456 hp765586 hp716712 hp765587 hp765588 hp716714

noncomputable def hp765590 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 724287770) (BSN.cosEvenQ 536870912) 0 3 hp765586 hp716712 hp765587 rfl rfl rfl

noncomputable def hp765591 := hp765589 hp765587 118054386 rfl rfl rfl rfl rfl rfl rfl rfl (hp765590 rfl)

noncomputable def hp765592 := @BSN.binarySplit_of_base3 (BSN.cosOddP 724287770) (BSN.cosOddQ 536870912) 0 3 hp765588 hp716714 hp765587 rfl rfl rfl

noncomputable def hp765593 := nat_lit 116191084699012446350906130794241

noncomputable def hp765594 := BSN.sin_dyadic_bound_f 103822911 536870912 2 1 536870912 268435456 hp765593 hp708890 hp765593 hp765593 hp708891

noncomputable def hp765595 := @BSN.binarySplit_of_base (BSN.sinEvenP 103822911) (BSN.sinEvenQ 536870912) 0 1 hp765593 hp708890 hp765593 rfl rfl rfl

noncomputable def hp765596 := hp765594 hp765593 103176994 rfl rfl rfl rfl rfl rfl rfl rfl (hp765595 rfl)

noncomputable def hp765597 := @BSN.binarySplit_of_base (BSN.sinOddP 103822911) (BSN.sinOddQ 536870912) 0 1 hp765593 hp708891 hp765593 rfl rfl rfl

noncomputable def hp765598 := hp765585 hd4920 hd4922 hd4924 hd4926 hd4918 (hp765591 (hp765592 rfl) rfl rfl rfl rfl) (hp765596 (hp765597 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765599 := hp765502 (BSN.cos_quad_nat3 15 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 396812423 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 885104 1000)) rfl rfl (hp765598 rfl rfl rfl rfl rfl) hp765568

noncomputable def hp765600 := nat_lit 1625154660859131051767722008686884670933957640200829887168917893678326016

noncomputable def hp765601 := nat_lit 135562441357949028904788258707729981103954384821449287383058477179136

noncomputable def hp765602 := nat_lit 4875192857694677257245356449543238552839665011832846762931987564080619776

noncomputable def hp765603 := BSN.cos_dyadic_bound_f 328486422 536870912 3 2 536870912 268435456 hp765600 hp708868 hp765601 hp765602 hp708870

noncomputable def hp765604 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 328486422) (BSN.cosEvenQ 536870912) 0 2 hp765600 hp708868 hp765601 rfl rfl rfl

noncomputable def hp765605 := hp765603 hp765601 439474325 rfl rfl rfl rfl rfl rfl rfl rfl (hp765604 rfl)

noncomputable def hp765606 := @BSN.binarySplit_of_base2 (BSN.cosOddP 328486422) (BSN.cosOddQ 536870912) 0 2 hp765602 hp708870 hp765601 rfl rfl rfl

noncomputable def hp765607 := nat_lit 9991026080623005244422140359318241321137028695888833430795738589634259105

noncomputable def hp765608 := nat_lit 1581102955656292762957458353059338317654887097147682452318260634347681

noncomputable def hp765609 := nat_lit 26164413187322522594727484103738059769511252957742038928113657217538877601

noncomputable def hp765610 := BSN.sin_dyadic_bound_f 446549923 536870912 3 2 536870912 268435456 hp765607 hp708845 hp765608 hp765609 hp708848

noncomputable def hp765611 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 446549923) (BSN.sinEvenQ 536870912) 0 2 hp765607 hp708845 hp765608 rfl rfl rfl

noncomputable def hp765612 := hp765610 hp765608 396812423 rfl rfl rfl rfl rfl rfl rfl rfl (hp765611 rfl)

noncomputable def hp765613 := @BSN.binarySplit_of_base2 (BSN.sinOddP 446549923) (BSN.sinOddQ 536870912) 0 2 hp765609 hp708848 hp765608 rfl rfl rfl

noncomputable def hp765614 := hp765599 hd4928 hd4930 hd4932 hd4934 hd4918 (hp765605 (hp765606 rfl) rfl rfl rfl rfl) (hp765612 (hp765613 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765615 := hp765497 (BSN.cos_quad_nat2 126 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 532657886 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 885104 1000)) rfl rfl (hp765614 rfl rfl rfl rfl rfl) hp765568

noncomputable def hp765616 := nat_lit 32682219331669907197026818872698909430842923620023897675503840211849558625

noncomputable def hp765617 := nat_lit 16906397604045368573662810238544246081685822249584797416077166775745121

noncomputable def hp765618 := nat_lit 85568916463014635871665262021444262587123022911658499478122123237207161441

noncomputable def hp765619 := BSN.sin_dyadic_bound_f 600490837 536870912 3 2 536870912 268435456 hp765616 hp708845 hp765617 hp765618 hp708848

noncomputable def hp765620 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 600490837) (BSN.sinEvenQ 536870912) 0 2 hp765616 hp708845 hp765617 rfl rfl rfl

noncomputable def hp765621 := hp765619 hp765617 482886659 rfl rfl rfl rfl rfl rfl rfl rfl (hp765620 rfl)

noncomputable def hp765622 := @BSN.binarySplit_of_base2 (BSN.sinOddP 600490837) (BSN.sinOddQ 536870912) 0 2 hp765618 hp708848 hp765617 rfl rfl rfl

noncomputable def hp765623 := nat_lit 20517557746459558206215881176336

noncomputable def hp765624 := BSN.cos_dyadic_bound_f 67302534 536870912 2 1 536870912 268435456 hp765623 hp708767 hp765623 hp765623 hp708768

noncomputable def hp765625 := @BSN.binarySplit_of_base (BSN.cosEvenP 67302534) (BSN.cosEvenQ 536870912) 0 1 hp765623 hp708767 hp765623 rfl rfl rfl

noncomputable def hp765626 := hp765624 hp765623 532657886 rfl rfl rfl rfl rfl rfl rfl rfl (hp765625 rfl)

noncomputable def hp765627 := @BSN.binarySplit_of_base (BSN.cosOddP 67302534) (BSN.cosOddQ 536870912) 0 1 hp765623 hp708768 hp765623 rfl rfl rfl

noncomputable def hp765628 := hp765615 hd4936 hd4938 hd4940 hd4942 hd4918 (hp765621 (hp765622 rfl) rfl rfl rfl rfl) (hp765626 (hp765627 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765629 := hp765492 (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 127528020 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 885104 1000)) rfl rfl (hp765628 rfl rfl rfl rfl rfl) hp765568

noncomputable def hp765630 := nat_lit 5109898303261755803217430279738893186458150161908133753388185802506394305

noncomputable def hp765631 := nat_lit 413648668424202615545992696421364289058748160168166564718127429606081

noncomputable def hp765632 := nat_lit 13382397267841435537525242934950514231874774355595316132054752514535480001

noncomputable def hp765633 := BSN.sin_dyadic_bound_f 377640839 536870912 3 2 536870912 268435456 hp765630 hp708845 hp765631 hp765632 hp708848

noncomputable def hp765634 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 377640839) (BSN.sinEvenQ 536870912) 0 2 hp765630 hp708845 hp765631 rfl rfl rfl

noncomputable def hp765635 := hp765633 hp765631 347260302 rfl rfl rfl rfl rfl rfl rfl rfl (hp765634 rfl)

noncomputable def hp765636 := @BSN.binarySplit_of_base2 (BSN.sinOddP 377640839) (BSN.sinOddQ 536870912) 0 2 hp765632 hp708848 hp765631 rfl rfl rfl

noncomputable def hp765637 := nat_lit 274857813160639504190954367210000

noncomputable def hp765638 := BSN.sin_dyadic_bound_f 128758830 536870912 2 1 536870912 268435456 hp765637 hp708890 hp765637 hp765637 hp708891

noncomputable def hp765639 := @BSN.binarySplit_of_base (BSN.sinEvenP 128758830) (BSN.sinEvenQ 536870912) 0 1 hp765637 hp708890 hp765637 rfl rfl rfl

noncomputable def hp765640 := hp765638 hp765637 127528020 rfl rfl rfl rfl rfl rfl rfl rfl (hp765639 rfl)

noncomputable def hp765641 := @BSN.binarySplit_of_base (BSN.sinOddP 128758830) (BSN.sinOddQ 536870912) 0 1 hp765637 hp708891 hp765637 rfl rfl rfl

noncomputable def hp765642 := hp765629 hd4944 hd4946 hd4961 hd4963 hd4918 (hp765635 (hp765636 rfl) rfl rfl rfl rfl) (hp765640 (hp765641 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765643 := @hp765487 13423 16777216 (hp765642 rfl rfl rfl rfl rfl) (hp765642 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp765644 := @hp765485 Bool.false 26522405 67108864 13423 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 885104 1000)) (Enclosure.sfrac Bool.false 885104 1000) 11) hp765643

noncomputable def hp765645 := @Enclosure.Real.IsNear.mulLit_tf hp765476 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1))) 2434929 8388608 1

noncomputable def hp765646 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp765475 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp765647 := @hp765646 1 1 0 1 2434929 8388608 1 33554432 2434929 8388608 1

noncomputable def hp765648 := @Enclosure.Real.IsNear.of_eq (hp765475 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp765649 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 885104 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp765650 := @hp765648 (@Inv.inv Real Real.instInv (Real.sqrt hp765477)) Bool.false 2434929 8388608 1 33554432 (hp765649 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 885104 1000) 885104 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 885104 1000))))

noncomputable def hp765651 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp765477)) Bool.false 19479432 67108864 2 67108864 2434929 8388608

noncomputable def hp765652 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp765477) Bool.false 231197691 67108864 7 67108864 231197691 67108864 7 67108864

noncomputable def hp765653 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 885104 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp765654 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 885104 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp765655 := @hp765654 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 885104 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 590846030533

noncomputable def hp765656 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 885104 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 885104 1000 0

noncomputable def hp765657 := @hp765656 1 10680707 67108864 1 67108864 590846030533 4194304000 55319 4194304000 (Enclosure.Real.IsNear.const Bool.false 885104 1000) hd4949

noncomputable def hp765658 := @hp765655 4194304000 55319 4194304000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 885104 1000) 885104 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 885104 1000))) (hp765657 rfl)

noncomputable def hp765659 := @hp765653 590846030533 4194304000 55319 4194304000 398251188 398251226 33554432 hp765658 rfl rfl rfl

noncomputable def hp765660 := @Enclosure.Real.IsNear.recentre' hp765477 Bool.false 796502414 67108864 38 67108864 398251207 33554432 19 33554432 (hp765659 rfl rfl rfl)

noncomputable def hp765661 := @Enclosure.Real.IsNear.sqrt_image hp765477 398251207 33554432 19 33554432 115598842 115598849 33554432 (hp765660 rfl) rfl rfl

noncomputable def hp765662 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp765477) 231197691 67108864 7 67108864 9739715 9739717 33554432 (hp765652 (hp765661 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp765663 := @hp765647 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp765650 (@hp765651 1 33554432 (hp765662 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp765664 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp765665 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp765666 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1))) (hp765664 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765665 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp765667 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 885104 1000) 885104 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 885104 1000)) rfl

noncomputable def hp765668 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp765669 := @hp765668 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765665 (Enclosure.sfrac Bool.false 1 16)))) 6176437

noncomputable def hp765670 := @hp765669 4194304 267 33554432 14954995 33554432 450003679 45675970560000 92368584452815 140737488355328 27670924149857327 1532631248189521920000

noncomputable def hp765671 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp765672 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1)))) 45572387

noncomputable def hp765673 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp765674 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 366340553) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp765675 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1))) Bool.false 25778924715663781977525

noncomputable def hp765676 := nat_lit 512735433022254545294433733

noncomputable def hp765677 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp765678 := @Enclosure.Real.IsNear.subLit_ff_p hp765477 (Enclosure.sfrac Bool.false 11 1) 398251207 33554432 19 33554432 11 1 0

noncomputable def hp765679 := @hp765677 500000000000000 29152455 33554432 19 33554432 25778924715663781977525 4722366482869645213696 hp765676 hp682805 hd4948 (@hp765678 1 29152455 29152455 33554432 19 33554432 (hp765660 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp765680 := @hp765674 366340553 67108864 15 4194304 Bool.false 45572387 67108864 1 10890000 (@hp765675 4722366482869645213696 hp765676 hp682805 366340553 67108864 15 4194304 (hp765679 rfl) rfl) (Enclosure.sfrac_false_div 366340553 67108864)

noncomputable def hp765681 := nat_lit 7219808011771984903929856

noncomputable def hp765682 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 366340553) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp765681) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp765683 := BSN.sin_reduce_arg_pos_rat_q3 366340553 67108864 226375608064910080 72057594037927936 0 hp765681 hp617687 rfl rfl rfl rfl

noncomputable def hp765684 := nat_lit 119577408722382584303570561414785622627040480461727036615928265175126702034395858511560843520

noncomputable def hp765685 := nat_lit 12279107111829032254318674285929819774732471701152142813487295558206343804676607233106176

noncomputable def hp765686 := nat_lit 313159047147106664266654002042261315743565977207483230524780762694428076009638724451900989696

noncomputable def hp765687 := BSN.sin_dyadic_bound_f 102599642726 137438953472 3 2 67108864 21801270 hp765684 hp738039 hp765685 hp765686 hp738042

noncomputable def hp765688 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 102599642726) (BSN.sinEvenQ 137438953472) 0 2 hp765684 hp738039 hp765685 rfl rfl rfl

noncomputable def hp765689 := hp765687 hp765685 45572387 rfl rfl rfl rfl rfl rfl rfl rfl (hp765688 rfl)

noncomputable def hp765690 := @BSN.binarySplit_of_base2 (BSN.sinOddP 102599642726) (BSN.sinOddQ 137438953472) 0 2 hp765686 hp738042 hp765685 rfl rfl rfl

noncomputable def hp765691 := @BSN.sin_arg_round Bool.false 45572387 67108864 hp765681 hp617687 102599642726 137438953472 21801270 21780000 (hp765689 (hp765690 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765692 := hp765682 45572387 67108864 0 1000000000000000 21780000 10890000 hp765683 BSN.pi_near_15 hp765691 rfl rfl

noncomputable def hp765693 := @hp765672 67108864 10471519 2854748160000 49411229 49411763 33554432 (@hp765673 45572387 67108864 167544304 45675970560000 45572387 67108864 10471519 2854748160000 (hp765680 (hp765692 rfl rfl) rfl rfl) rfl)

noncomputable def hp765694 := @hp765671 Bool.false 98822992 67108864 534 67108864 6176437 4194304 267 33554432 (hp765693 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp765695 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765665 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp765696 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765665 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 37206745)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp765697 := nat_lit 175703887011141276880047162445

noncomputable def hp765698 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765665 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp765697

noncomputable def hp765699 := nat_lit 47099549218186188875776045612287461

noncomputable def hp765700 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765665 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp765701 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp765702 := @hp765701 (Enclosure.sfrac Bool.false 1 16) 128328436403535 1125899906842624 1745327859 1125899906842624 1 16 0

noncomputable def hp765703 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1)) 849865632527025

noncomputable def hp765704 := @hp765703 1125899906842624 1107793651 1125899906842624 29152455 33554432 19 33554432 4305987792968739717120 128328436403535 1125899906842624 1745327859

noncomputable def hp765705 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1)) 29152455 33554432 19

noncomputable def hp765706 := @hp765705 33554432 29152455 33554432 19 33554432 849865632527025 1125899906842624 1107793651 1125899906842624 (@hp765678 1 29152455 29152455 33554432 19 33554432 (hp765660 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp765707 := hp765706 (@hp765678 1 29152455 29152455 33554432 19 33554432 (hp765660 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp765708 := @hp765704 1125899906842624 (hp765707 rfl) (@hp765678 1 29152455 29152455 33554432 19 33554432 (hp765660 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp765709 := @hp765700 500000000000000 198697180581199 1125899906842624 1745327859 1125899906842624 hp765697 hp682141 hp765699 hp682143 hd4948 (@hp765702 1 3179154889299184 198697180581199 1125899906842624 1745327859 1125899906842624 (hp765708 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp765710 := @hp765696 37206745 33554432 655 67108864 Bool.false 14954995 33554432 1 10890000 (@hp765698 hp682141 hp765699 hp682143 37206745 33554432 655 67108864 (hp765709 rfl) rfl) (Enclosure.sfrac_true_div 37206745 33554432)

noncomputable def hp765711 := nat_lit 4084944783047065760436785780751706841457957304705386660912690625

noncomputable def hp765712 := nat_lit 3672598245775333852630901933573174487822260136410937187890625

noncomputable def hp765713 := nat_lit 12247489152649646613605095538387974175398227393843338108362290625

noncomputable def hp765714 := BSN.cos_dyadic_bound_f 37206745 33554432 3 2 33554432 10890000 hp765711 hp684401 hp765712 hp765713 hp684404

noncomputable def hp765715 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 37206745) (BSN.cosEvenQ 33554432) 0 2 hp765711 hp684401 hp765712 rfl rfl rfl

noncomputable def hp765716 := hp765714 hp765712 14954995 rfl rfl rfl rfl rfl rfl rfl rfl (hp765715 rfl)

noncomputable def hp765717 := @BSN.binarySplit_of_base2 (BSN.cosOddP 37206745) (BSN.cosOddQ 33554432) 0 2 hp765713 hp684404 hp765712 rfl rfl rfl

noncomputable def hp765718 := hp765710 (BSN.cos_neg_of_bound 37206745 33554432 Bool.false 14954995 33554432 1 10890000 (hp765716 (hp765717 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp765719 := hp765670 hp765694 (@hp765695 14954995 33554432 7200058864 730815528960000 14954995 33554432 450003679 45675970560000 (hp765718 rfl) rfl)

noncomputable def hp765720 := @hp765645 33554432 92368584452815 140737488355328 27670924149857327 1532631248189521920000 224910944973108375135 1180591620717411303424 270512864232767110706459 hp738860 (hp765663 rfl) (@hp765666 Bool.false 92368584452815 140737488355328 27670924149857327 1532631248189521920000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765477 (Enclosure.sfrac Bool.false 11 1)) (hp765667 rfl (hp765480 rfl rfl))) (hp765719 rfl))

noncomputable def hp765721 := @hp765474 hp765472 hp738860 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 885104 1000))) (@hp765479 hp765472 hp738860 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 885104 1000) 11 (hp765480 rfl rfl)) (@hp765483 hp765472 hp738860 hp765644 (hp765720 rfl) rfl rfl))

theorem hd5071 : hp765473 hp738860 := hp765721

noncomputable def hp765722 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 886373 1000)) Bool.true 13962957787815189248459 4722366482869645213696 94227644885428757859029

noncomputable def hp765723 := nat_lit 116878570451023719038976000

noncomputable def hp765724 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 886373 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 886373 1000)) Bool.true 13962957787815189248459 4722366482869645213696

noncomputable def hp765725 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 886373 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp765726 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp765725 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp765727 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 886373 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp765728 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 886373 1000)) (Enclosure.sfrac Bool.false 886373 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp765726 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp765729 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 886373 1000)) hp765728 Bool.true 13962957787815189248459 4722366482869645213696

noncomputable def hp765730 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 886373 1000) 886373 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 886373 1000)) rfl

noncomputable def hp765731 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 886373 1000)) (Enclosure.sfrac Bool.false 886373 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp765726 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp765732 := nat_lit 937038235220230392409097240576

noncomputable def hp765733 := @hp765731 211483461 67108864 215065 268435456 918867777100792366645 4722366482869645213696 586923467281163619029 hp765723 hp765732 13962957787815189248459 4722366482869645213696

noncomputable def hp765734 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 886373 1000)) (Enclosure.sfrac Bool.false 886373 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 886373 1000)) (Enclosure.sfrac Bool.false 886373 1000) 11)

noncomputable def hp765735 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 886373 1000)) (Enclosure.sfrac Bool.false 886373 1000) 11) hp765734

noncomputable def hp765736 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 886373 1000)) (Enclosure.sfrac Bool.false 886373 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 886373 1000)) (Enclosure.sfrac Bool.false 886373 1000) 11)

noncomputable def hp765737 := @hp765736 845933844 536870912 215065 536870912 845933844 536870912 215065 536870912 908314548639891456 211483461 67108864

noncomputable def hp765738 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 886373 1000)) (Enclosure.sfrac Bool.false 886373 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp765739 := hp765738 BSN.quadSignPos 9 10 11 886373 1000 185 239 536870912 268435456 9007199254740992

noncomputable def hp765740 := hp765739 Bool.false 939452365866 4038 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp765741 := hp765740 Bool.true 789757440 184626 Bool.true 260671918 Bool.true 76723704 28296951008113761 1 Bool.false 250549806

noncomputable def hp765742 := hp765741 Bool.true Bool.false 76462815 Bool.false Bool.true 845933844 215065 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 185 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 250549806 536870912) BSN.abs_quadSignPos

noncomputable def hp765743 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 886373 1000)) (Enclosure.sfrac Bool.false 886373 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp765744 := hp765743 BSN.quadSignNeg 7 8 9 886373 1000 59 125 536870912 268435456 9007199254740992

noncomputable def hp765745 := hp765744 Bool.false 939452365866 4038 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp765746 := hp765745 Bool.true 725254919 150782 Bool.true 331496629 Bool.true 721867474 28296951008113761 1 Bool.false 310830281

noncomputable def hp765747 := hp765746 Bool.false Bool.false 523192878 Bool.true Bool.true 789757440 184626 BSN.abs_quadSignPos (BSN.cos_quad_nat3 59 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 310830281 536870912) BSN.abs_quadSignNeg

noncomputable def hp765748 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 886373 1000)) (Enclosure.sfrac Bool.false 886373 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp765749 := hp765748 BSN.quadSignPos 5 6 7 886373 1000 102 15 536870912 268435456 9007199254740992

noncomputable def hp765750 := hp765749 Bool.false 939452365866 4038 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp765751 := hp765750 Bool.true 907378920 112047 Bool.false 793475323 Bool.false 806517644 28296951008113761 1 Bool.false 49767977

noncomputable def hp765752 := hp765751 Bool.true Bool.false 535610362 Bool.false Bool.true 725254919 150782 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 102 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 49767977 536870912) BSN.abs_quadSignPos

noncomputable def hp765753 := hp765743 BSN.quadSignNeg 3 4 5 886373 1000 331 205 536870912 268435456 9007199254740992

noncomputable def hp765754 := hp765753 Bool.false 939452365866 4038 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp765755 := hp765754 Bool.true 922617724 66223 Bool.false 622200817 Bool.false 693025529 28296951008113761 1 Bool.false 491977244

noncomputable def hp765756 := hp765755 Bool.false Bool.false 515972250 Bool.true Bool.true 907378920 112047 BSN.abs_quadSignPos (BSN.cos_quad_nat3 331 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 491977244 536870912) BSN.abs_quadSignNeg

noncomputable def hp765757 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 886373 1000)) (Enclosure.sfrac Bool.false 886373 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp765758 := hp765757 BSN.quadSignNeg 1 2 3 886373 1000 722 494 536870912 268435456 9007199254740992

noncomputable def hp765759 := hp765758 Bool.false 939452365866 4038 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp765760 := hp765759 Bool.true 536870768 4090 Bool.false 732572772 Bool.false 60529762 28296951008113761 1 Bool.false 109958432

noncomputable def hp765761 := hp765760 Bool.true Bool.false 533462296 Bool.true Bool.true 922617724 66223 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 722 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 109958432 536870912) BSN.abs_quadSignNeg

noncomputable def hp765762 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 886373 1000)) (Enclosure.sfrac Bool.false 886373 1000) 1) Bool.true

noncomputable def hp765763 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 886373 1000)) (Enclosure.sfrac Bool.false 886373 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 886373 1000)))

noncomputable def hp765764 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 886373 1000))) Bool.true 67108846 67108864

noncomputable def hp765765 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 886373 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 117431545733) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 117431545733 67108864

noncomputable def hp765766 := nat_lit 5503344276220439221317941224348929220374902413792250862491

noncomputable def hp765767 := nat_lit 3145008270749679698939377312399434003391623032324751360

noncomputable def hp765768 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 886373 1000)) Bool.false hp765766 hp765767 134164175233929481379

noncomputable def hp765769 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 886373 4000) (Real.log (Enclosure.sfrac Bool.false 3142629380516 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1772746))))))

noncomputable def hp765770 := nat_lit 262617812615804717399594942284640000

noncomputable def hp765771 := nat_lit 1396664237929137053013385255617355264320

noncomputable def hp765772 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 886373 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp765769 (Enclosure.sfrac Bool.false 886373 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 886373 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp765770 hp765771)) Bool.false

noncomputable def hp765773 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 886373 1000) 886373 1000 3142629380516 16000000 1772746

noncomputable def hp765774 := hp765773 4000 2000 hp765770 hp765771 (@Eq.refl Real (Enclosure.sfrac Bool.false 886373 1000)) rfl rfl rfl rfl

noncomputable def hp765775 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp765769 (Enclosure.sfrac Bool.false 886373 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 886373 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp765770 hp765771) 1260911756599276339291 720575940379279360

noncomputable def hp765776 := nat_lit 1761070168390540550821741191791657350519968772413520275997120

noncomputable def hp765777 := @hp765775 134164175233929481379 hp738659 hp765770 hp765771 0 1 hp765776 hp765766 hp765767 134164175233929481379 hp738659

noncomputable def hp765778 := @Enclosure.Real.IsNear.subLit_ff_p (hp765769 (Enclosure.sfrac Bool.false 886373 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 886373 2000) (Real.log Real.pi)) 40662017635052774230243 18014398509481984000 11179678909967849 4356000000000000000000

noncomputable def hp765779 := nat_lit 2115458889740548458797439385600000

noncomputable def hp765780 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 886373 4000) (Real.log (Enclosure.sfrac Bool.false 3142629380516 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1772746))))))

noncomputable def hp765781 := @hp765780 (Enclosure.sfrac Bool.false 886373 2000) 48645755860075311532259 18014398509481984000 11179678909967849 4356000000000000000000 886373 2000 0

noncomputable def hp765782 := nat_lit 81324035270105548460486000

noncomputable def hp765783 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 886373 4000) (Real.log (Enclosure.sfrac Bool.false 3142629380516 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1772746))))) 48652827557488402116259

noncomputable def hp765784 := nat_lit 109540503982295647585862446744424415232

noncomputable def hp765785 := @hp765783 18014398509481984000 11079678909423349 4356000000000000000000 883962176636323 2251799813685248 200000001089 8712000000000000000 hp765784 48645755860075311532259 18014398509481984000 11179678909967849

noncomputable def hp765786 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 886373 4000) (Real.log (Enclosure.sfrac Bool.false 3142629380516 16000000)) 886373 4000 0 1 54889789690670183 4503599627370496

noncomputable def hp765787 := nat_lit 117874925802873196153667584

noncomputable def hp765788 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3142629380516) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp765787 hp617687

noncomputable def hp765789 := BSN.log_rat_reduce_isNear 3142629380516 16000000 17 6285258761032 4194304000000 108576665 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp765790 := nat_lit 162164641583811620277335455119643432649967813543062601739032375117472262699617411822923146821705960492013675020127024511812260331520

noncomputable def hp765791 := nat_lit 2204890049278769761784632023244281200165564145189589299417247720690911944224584384187091588603731850906789924955594063752387887104

noncomputable def hp765792 := nat_lit 1474274042652837891691846047951135541043627444401850201079702870102683476633777912454949203172920802581577661559493041848320

noncomputable def hp765793 := BSN.log_dyadic_bound 1045477380516 5239781380516 6 5 hp765790 268435456 87120000 hp765791 hp765792 108576665 6285258761032

noncomputable def hp765794 := hp765793 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp765795 := @BSN.binarySplit_of_base5 (BSN.artanhP 1045477380516) (BSN.artanhQ 5239781380516) 0 5 hp765791 hp765790 hp765792 rfl rfl rfl

noncomputable def hp765796 := hp765789 rfl rfl rfl rfl (hp765794 (hp765795 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp765797 := @hp765786 12500018513 1089000000000000000 48652827557488402116259 18014398509481984000 11079678909423349 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 886373 4000) (BSN.isNear_log_sfrac 3142629380516 16000000 54889789690670183 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp765788 1000001481040000 87120000000000000000000 54889789690670183 4503599627370496 12500018513 1089000000000000000 (hp765796 rfl rfl rfl) rfl)) rfl

noncomputable def hp765798 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1772746)))) 1 4

noncomputable def hp765799 := @hp765798 0 1 883962176636323 562949953421312 200000001089 2178000000000000000 883962176636323 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp765800 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1772746))) 884279719003555 562949953421312 1

noncomputable def hp765801 := @hp765800 2000000000000000 18927 33554432 1 10890000 29660848746515488833536 883962176636323 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp765802 := BSN.arctan_dyadic_bound_f 1000 1772746 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp765803 := hp765802 1 18927 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1772746) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1772746) 0 0 rfl)

noncomputable def hp765804 := hp765799 (hp765801 (hp765803 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp765805 := @hp765778 34046261459853 67108864000 2659119 536870912000 hp765779 1260911756599276339291 720575940379279360 134164175233929481379 hp738659 (@hp765781 1 hp765782 40662017635052774230243 18014398509481984000 11179678909967849 4356000000000000000000 (@hp765785 4356000000000000000000 hp765797 hp765804 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 886373 2000) rfl rfl)

noncomputable def hp765806 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 886373 2000) (Real.log Real.pi) 886373 2000 0 1 38410761 33554432

noncomputable def hp765807 := hp765805 (@hp765806 3 268435456 34046261459853 67108864000 2659119 536870912000 (Enclosure.Real.IsNear.const Bool.false 886373 2000) hd4909 rfl) rfl

noncomputable def hp765808 := @hp765768 hp738659 117431545733 67108864 505 67108864 (@hp765772 hp765766 hp765767 134164175233929481379 hp738659 (hp765774 rfl rfl rfl rfl rfl) (hp765777 (hp765807 rfl) (Enclosure.Real.IsNear.const Bool.true hp765770 hp765771) rfl rfl)) rfl

noncomputable def hp765809 := nat_lit 15184886720786403338223616

noncomputable def hp765810 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 117431545733) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp765809) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp765811 := BSN.sin_reduce_arg_pos_rat_q1 117431545733 67108864 226375608064910080 72057594037927936 278 hp765809 hp617687 rfl rfl rfl rfl

noncomputable def hp765812 := nat_lit 14354133920824817988880423054728539517494902679239770036513023729414152496095161933681714292449455457432927380542783012636361927413305250290625

noncomputable def hp765813 := nat_lit 10194855408012165308395045785992281314622695433397560158012480977793299976559379907523598439412460767673585722057958010497694902587890625

noncomputable def hp765814 := nat_lit 71681647898757058802939916399236598037027370809912139186413550534842276570796108003129394271361168558077459120931123370364699612877891899890625

noncomputable def hp765815 := BSN.sin_dyadic_bound_f 215790219055 137438953472 4 3 67108864 21801270 hp765812 hp737934 hp765813 hp765814 hp737937

noncomputable def hp765816 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215790219055) (BSN.sinEvenQ 137438953472) 0 3 hp765812 hp737934 hp765813 rfl rfl rfl

noncomputable def hp765817 := hp765815 hp765813 67108846 rfl rfl rfl rfl rfl rfl rfl rfl (hp765816 rfl)

noncomputable def hp765818 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215790219055) (BSN.sinOddQ 137438953472) 0 3 hp765814 hp737937 hp765813 rfl rfl rfl

noncomputable def hp765819 := @BSN.sin_arg_round Bool.false 67108846 67108864 hp765809 hp617687 215790219055 137438953472 21801270 21780000 (hp765817 (hp765818 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765820 := hp765810 67108846 67108864 278 1000000000000000 21780000 10890000 hp765811 BSN.pi_near_15 hp765819 rfl rfl

noncomputable def hp765821 := @hp765765 505 67108864 Bool.true 67108846 67108864 1 10890000 hp765808 (Enclosure.sfrac_false_div 117431545733 67108864) (hp765820 rfl rfl) rfl

noncomputable def hp765822 := @hp765762 33554423 33554432 347909929 45675970560000 536870768 536870912 4090 536870912 (@hp765763 Bool.true 33554423 33554432 347909929 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 886373 1000)) (Enclosure.sfrac Bool.false 886373 1000)) (@hp765764 5566558864 730815528960000 33554423 33554432 347909929 45675970560000 (hp765821 rfl) rfl))

noncomputable def hp765823 := @hp765768 hp738659 939452365866 536870912 4038 536870912 (@hp765772 hp765766 hp765767 134164175233929481379 hp738659 (hp765774 rfl rfl rfl rfl rfl) (hp765777 (hp765807 rfl) (Enclosure.Real.IsNear.const Bool.true hp765770 hp765771) rfl rfl)) rfl

noncomputable def hp765824 := hp765761 (BSN.cos_quad_nat2 494 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 533462296 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 886373 1000)) rfl rfl (hp765822 rfl) hp765823

noncomputable def hp765825 := nat_lit 39754228779212398746494792548814359480085821383851298561362633231764336323364997288077399355610238495820240388096

noncomputable def hp765826 := nat_lit 23889621839132492205275269663725554476565082247382284596939743394475891694022372783003550149048182784393216

noncomputable def hp765827 := nat_lit 240844432169747642587529413538167153972588137178352642374964389344665750599331211028941103363838083557796117217280

noncomputable def hp765828 := BSN.cos_dyadic_bound_f 732572772 536870912 4 3 536870912 268435456 hp765825 hp716712 hp765826 hp765827 hp716714

noncomputable def hp765829 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 732572772) (BSN.cosEvenQ 536870912) 0 3 hp765825 hp716712 hp765826 rfl rfl rfl

noncomputable def hp765830 := hp765828 hp765826 109958432 rfl rfl rfl rfl rfl rfl rfl rfl (hp765829 rfl)

noncomputable def hp765831 := @BSN.binarySplit_of_base3 (BSN.cosOddP 732572772) (BSN.cosOddQ 536870912) 0 3 hp765827 hp716714 hp765826 rfl rfl rfl

noncomputable def hp765832 := nat_lit 13423812121105273050115231902736

noncomputable def hp765833 := BSN.cos_dyadic_bound_f 60529762 536870912 2 1 536870912 268435456 hp765832 hp708767 hp765832 hp765832 hp708768

noncomputable def hp765834 := @BSN.binarySplit_of_base (BSN.cosEvenP 60529762) (BSN.cosEvenQ 536870912) 0 1 hp765832 hp708767 hp765832 rfl rfl rfl

noncomputable def hp765835 := hp765833 hp765832 533462296 rfl rfl rfl rfl rfl rfl rfl rfl (hp765834 rfl)

noncomputable def hp765836 := @BSN.binarySplit_of_base (BSN.cosOddP 60529762) (BSN.cosOddQ 536870912) 0 1 hp765832 hp708768 hp765832 rfl rfl rfl

noncomputable def hp765837 := hp765824 hd4911 hd4913 hd4915 hd4917 hd4918 (hp765830 (hp765831 rfl) rfl rfl rfl rfl) (hp765835 (hp765836 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765838 := hp765756 (BSN.cos_quad_nat1 205 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 515972250 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 886373 1000)) rfl rfl (hp765837 rfl rfl rfl rfl rfl) hp765823

noncomputable def hp765839 := nat_lit 53708053064095743651552513303815576227340007345679461725787560190131860040756364718813717189847176735986490532161

noncomputable def hp765840 := nat_lit 3366409350588608856859729818862649477864857461276453061329594497094764252539975161374167661869586547466561

noncomputable def hp765841 := nat_lit 268441276372085543651102561989707547450417809825826392642468154177405053409926081117490088915862957592546172723521

noncomputable def hp765842 := BSN.sin_dyadic_bound_f 622200817 536870912 4 3 536870912 268435456 hp765839 hp642702 hp765840 hp765841 hp642705

noncomputable def hp765843 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 622200817) (BSN.sinEvenQ 536870912) 0 3 hp765839 hp642702 hp765840 rfl rfl rfl

noncomputable def hp765844 := hp765842 hp765840 491977244 rfl rfl rfl rfl rfl rfl rfl rfl (hp765843 rfl)

noncomputable def hp765845 := @BSN.binarySplit_of_base3 (BSN.sinOddP 622200817) (BSN.sinOddQ 536870912) 0 3 hp765841 hp642705 hp765840 rfl rfl rfl

noncomputable def hp765846 := nat_lit 82690124473063956146244804533345537049348576988102683716584677709866168887178350811161818813127734578455838174241

noncomputable def hp765847 := nat_lit 12274132191351702614349482337311164700742750710255782859380860904460665185126734796183105652710787369643041

noncomputable def hp765848 := nat_lit 413216108887234564239314056061535252765035739772060693149956826861310257409471994573222013648410660476826442247201

noncomputable def hp765849 := BSN.sin_dyadic_bound_f 693025529 536870912 4 3 536870912 268435456 hp765846 hp642702 hp765847 hp765848 hp642705

noncomputable def hp765850 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 693025529) (BSN.sinEvenQ 536870912) 0 3 hp765846 hp642702 hp765847 rfl rfl rfl

noncomputable def hp765851 := hp765849 hp765847 515972250 rfl rfl rfl rfl rfl rfl rfl rfl (hp765850 rfl)

noncomputable def hp765852 := @BSN.binarySplit_of_base3 (BSN.sinOddP 693025529) (BSN.sinOddQ 536870912) 0 3 hp765848 hp642705 hp765847 rfl rfl rfl

noncomputable def hp765853 := hp765838 hd4920 hd4922 hd4924 hd4926 hd4918 (hp765844 (hp765845 rfl) rfl rfl rfl rfl) (hp765851 (hp765852 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765854 := hp765752 (BSN.cos_quad_nat3 15 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 535610362 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 886373 1000)) rfl rfl (hp765853 rfl rfl rfl rfl rfl) hp765823

noncomputable def hp765855 := nat_lit 54758385270994385866442261561237728653580624742590427933045174666919870447956178535666922273707004187155514642001

noncomputable def hp765856 := nat_lit 62287528293355629061405666595026181721263246231921636007421538282171774316869228907996652261615001573117521

noncomputable def hp765857 := nat_lit 331573331714759404211171846981156523099861232555977010644151551364190090004125363633941096237818837110934109802065

noncomputable def hp765858 := BSN.cos_dyadic_bound_f 793475323 536870912 4 3 536870912 268435456 hp765855 hp716712 hp765856 hp765857 hp716714

noncomputable def hp765859 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 793475323) (BSN.cosEvenQ 536870912) 0 3 hp765855 hp716712 hp765856 rfl rfl rfl

noncomputable def hp765860 := hp765858 hp765856 49767977 rfl rfl rfl rfl rfl rfl rfl rfl (hp765859 rfl)

noncomputable def hp765861 := @BSN.binarySplit_of_base3 (BSN.cosOddP 793475323) (BSN.cosOddQ 536870912) 0 3 hp765857 hp716714 hp765856 rfl rfl rfl

noncomputable def hp765862 := nat_lit 151790501800154747452167847984673688364974549850837599421269975870178190635414945919089430838686852817499388379136

noncomputable def hp765863 := nat_lit 75747180765247838318448903261528147277224569037202915898456767836605319195002872787707649544870544367681536

noncomputable def hp765864 := nat_lit 758163356802435541852408181064731608865049972020585587698715801492829010656270319519082478432851492556022004842496

noncomputable def hp765865 := BSN.sin_dyadic_bound_f 806517644 536870912 4 3 536870912 268435456 hp765862 hp642702 hp765863 hp765864 hp642705

noncomputable def hp765866 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 806517644) (BSN.sinEvenQ 536870912) 0 3 hp765862 hp642702 hp765863 rfl rfl rfl

noncomputable def hp765867 := hp765865 hp765863 535610362 rfl rfl rfl rfl rfl rfl rfl rfl (hp765866 rfl)

noncomputable def hp765868 := @BSN.binarySplit_of_base3 (BSN.sinOddP 806517644) (BSN.sinOddQ 536870912) 0 3 hp765864 hp642705 hp765863 rfl rfl rfl

noncomputable def hp765869 := hp765854 hd4928 hd4930 hd4932 hd4934 hd4918 (hp765860 (hp765861 rfl) rfl rfl rfl rfl) (hp765867 (hp765868 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765870 := hp765747 (BSN.cos_quad_nat1 125 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 523192878 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 886373 1000)) rfl rfl (hp765869 rfl rfl rfl rfl rfl) hp765823

noncomputable def hp765871 := nat_lit 3033881576011334979663674326503376861825573715703950985195230723033557345

noncomputable def hp765872 := nat_lit 145825317698818189133222419750495925897347637040849310951153444088161

noncomputable def hp765873 := nat_lit 7945644219991507812527217066448295739948859264002757871865016692845078881

noncomputable def hp765874 := BSN.sin_dyadic_bound_f 331496629 536870912 3 2 536870912 268435456 hp765871 hp708845 hp765872 hp765873 hp708848

noncomputable def hp765875 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 331496629) (BSN.sinEvenQ 536870912) 0 2 hp765871 hp708845 hp765872 rfl rfl rfl

noncomputable def hp765876 := hp765874 hp765872 310830281 rfl rfl rfl rfl rfl rfl rfl rfl (hp765875 rfl)

noncomputable def hp765877 := @BSN.binarySplit_of_base2 (BSN.sinOddP 331496629) (BSN.sinOddQ 536870912) 0 2 hp765873 hp708848 hp765872 rfl rfl rfl

noncomputable def hp765878 := nat_lit 97354763445346040548288338154363851430966858258360135377008702265615631896627717968755858112417283295498825240576

noncomputable def hp765879 := nat_lit 20021180687220984899610110578452306824934573956846849525958557921656758859122956158099676812482334361522176

noncomputable def hp765880 := nat_lit 486448842310566368639915938316440804459839696089873210147398000043891399083139076095077474320560937189902122356736

noncomputable def hp765881 := BSN.sin_dyadic_bound_f 721867474 536870912 4 3 536870912 268435456 hp765878 hp642702 hp765879 hp765880 hp642705

noncomputable def hp765882 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 721867474) (BSN.sinEvenQ 536870912) 0 3 hp765878 hp642702 hp765879 rfl rfl rfl

noncomputable def hp765883 := hp765881 hp765879 523192878 rfl rfl rfl rfl rfl rfl rfl rfl (hp765882 rfl)

noncomputable def hp765884 := @BSN.binarySplit_of_base3 (BSN.sinOddP 721867474) (BSN.sinOddQ 536870912) 0 3 hp765880 hp642705 hp765879 rfl rfl rfl

noncomputable def hp765885 := hp765870 hd4936 hd4938 hd4940 hd4942 hd4918 (hp765876 (hp765877 rfl) rfl rfl rfl rfl) (hp765883 (hp765884 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765886 := hp765742 (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 76462815 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 886373 1000)) rfl rfl (hp765885 rfl rfl rfl rfl rfl) hp765823

noncomputable def hp765887 := nat_lit 1159968659320502239317138327499373019290271027801271059660529500776055040

noncomputable def hp765888 := nat_lit 21318369219762508224798232271949579423257743544924515732147481886976

noncomputable def hp765889 := nat_lit 3037978639908292916055379279646108084536405512656637183228296644204708096

noncomputable def hp765890 := BSN.sin_dyadic_bound_f 260671918 536870912 3 2 536870912 268435456 hp765887 hp708845 hp765888 hp765889 hp708848

noncomputable def hp765891 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 260671918) (BSN.sinEvenQ 536870912) 0 2 hp765887 hp708845 hp765888 rfl rfl rfl

noncomputable def hp765892 := hp765890 hp765888 250549806 rfl rfl rfl rfl rfl rfl rfl rfl (hp765891 rfl)

noncomputable def hp765893 := @BSN.binarySplit_of_base2 (BSN.sinOddP 260671918) (BSN.sinOddQ 536870912) 0 2 hp765889 hp708848 hp765888 rfl rfl rfl

noncomputable def hp765894 := nat_lit 34651197242977374857482191507456

noncomputable def hp765895 := BSN.sin_dyadic_bound_f 76723704 536870912 2 1 536870912 268435456 hp765894 hp708890 hp765894 hp765894 hp708891

noncomputable def hp765896 := @BSN.binarySplit_of_base (BSN.sinEvenP 76723704) (BSN.sinEvenQ 536870912) 0 1 hp765894 hp708890 hp765894 rfl rfl rfl

noncomputable def hp765897 := hp765895 hp765894 76462815 rfl rfl rfl rfl rfl rfl rfl rfl (hp765896 rfl)

noncomputable def hp765898 := @BSN.binarySplit_of_base (BSN.sinOddP 76723704) (BSN.sinOddQ 536870912) 0 1 hp765894 hp708891 hp765894 rfl rfl rfl

noncomputable def hp765899 := hp765886 hd4944 hd4946 hd4961 hd4963 hd4918 (hp765892 (hp765893 rfl) rfl rfl rfl rfl) (hp765897 (hp765898 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765900 := @hp765737 215065 268435456 (hp765899 rfl rfl rfl rfl rfl) (hp765899 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp765901 := @hp765735 Bool.true 211483461 67108864 215065 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 886373 1000)) (Enclosure.sfrac Bool.false 886373 1000) 11) hp765900

noncomputable def hp765902 := @Enclosure.Real.IsNear.mulLit_tf hp765726 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1))) 2434057 8388608 1

noncomputable def hp765903 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp765725 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp765904 := @hp765903 1 1 0 1 2434057 8388608 1 33554432 2434057 8388608 1

noncomputable def hp765905 := @Enclosure.Real.IsNear.of_eq (hp765725 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp765906 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 886373 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp765907 := @hp765905 (@Inv.inv Real Real.instInv (Real.sqrt hp765727)) Bool.false 2434057 8388608 1 33554432 (hp765906 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 886373 1000) 886373 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 886373 1000))))

noncomputable def hp765908 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp765727)) Bool.false 19472456 67108864 2 67108864 2434057 8388608

noncomputable def hp765909 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp765727) Bool.false 231280515 67108864 7 67108864 231280515 67108864 7 67108864

noncomputable def hp765910 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 886373 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp765911 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 886373 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp765912 := @hp765911 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 886373 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9467090305711

noncomputable def hp765913 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 886373 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 886373 1000 0

noncomputable def hp765914 := @hp765913 1 10680707 67108864 1 67108864 9467090305711 67108864000 886373 67108864000 (Enclosure.Real.IsNear.const Bool.false 886373 1000) hd4949

noncomputable def hp765915 := @hp765912 67108864000 886373 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 886373 1000) 886373 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 886373 1000))) (hp765914 rfl)

noncomputable def hp765916 := @hp765910 9467090305711 67108864000 886373 67108864000 398536578 398536616 33554432 hp765915 rfl rfl rfl

noncomputable def hp765917 := @Enclosure.Real.IsNear.recentre' hp765727 Bool.false 797073194 67108864 38 67108864 398536597 33554432 19 33554432 (hp765916 rfl rfl rfl)

noncomputable def hp765918 := @Enclosure.Real.IsNear.sqrt_image hp765727 398536597 33554432 19 33554432 115640254 115640261 33554432 (hp765917 rfl) rfl rfl

noncomputable def hp765919 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp765727) 231280515 67108864 7 67108864 9736227 9736229 33554432 (hp765909 (hp765918 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp765920 := @hp765904 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp765907 (@hp765908 1 33554432 (hp765919 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp765921 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp765922 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp765923 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1))) (hp765921 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765922 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp765924 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 886373 1000) 886373 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 886373 1000)) rfl

noncomputable def hp765925 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp765926 := @hp765925 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765922 (Enclosure.sfrac Bool.false 1 16)))) 23388685

noncomputable def hp765927 := @hp765926 16777216 15 2097152 16140481 33554432 226022777 22837985280000 377504625857485 562949953421312 120085026227027 6966505673588736000

noncomputable def hp765928 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp765929 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1)))) 24069329

noncomputable def hp765930 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp765931 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 184963435) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp765932 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1))) Bool.false 26031289304670206538975

noncomputable def hp765933 := nat_lit 512735433024706026727644613

noncomputable def hp765934 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp765935 := @Enclosure.Real.IsNear.subLit_ff_p hp765727 (Enclosure.sfrac Bool.false 11 1) 398536597 33554432 19 33554432 11 1 0

noncomputable def hp765936 := @hp765934 500000000000000 29437845 33554432 19 33554432 26031289304670206538975 4722366482869645213696 hp765933 hp682805 hd4948 (@hp765935 1 29437845 29437845 33554432 19 33554432 (hp765917 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp765937 := @hp765931 184963435 33554432 15 4194304 Bool.false 48138658 67108864 1 10890000 (@hp765932 4722366482869645213696 hp765933 hp682805 184963435 33554432 15 4194304 (hp765936 rfl) rfl) (Enclosure.sfrac_false_div 184963435 33554432)

noncomputable def hp765938 := nat_lit 3868325380363312053616640

noncomputable def hp765939 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 184963435) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp765938) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp765940 := BSN.sin_reduce_arg_pos_rat_q3 184963435 33554432 226375608064910080 72057594037927936 0 hp765938 hp619237 rfl rfl rfl rfl

noncomputable def hp765941 := nat_lit 157678587567227186494892740442273608264769660353802740944782735639706624605713760701633143040

noncomputable def hp765942 := nat_lit 21349393330633642940786016998522629837231300495597962262210008539682192210670608202998016

noncomputable def hp765943 := nat_lit 412933163658297795874243523797480889768945974059157162916482634280643578989480668471948615936

noncomputable def hp765944 := BSN.sin_dyadic_bound_f 109944419942 137438953472 3 2 67108864 21801270 hp765941 hp738039 hp765942 hp765943 hp738042

noncomputable def hp765945 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 109944419942) (BSN.sinEvenQ 137438953472) 0 2 hp765941 hp738039 hp765942 rfl rfl rfl

noncomputable def hp765946 := hp765944 hp765942 48138658 rfl rfl rfl rfl rfl rfl rfl rfl (hp765945 rfl)

noncomputable def hp765947 := @BSN.binarySplit_of_base2 (BSN.sinOddP 109944419942) (BSN.sinOddQ 137438953472) 0 2 hp765943 hp738042 hp765942 rfl rfl rfl

noncomputable def hp765948 := @BSN.sin_arg_round Bool.false 48138658 67108864 hp765938 hp619237 109944419942 137438953472 21801270 21780000 (hp765946 (hp765947 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp765949 := hp765939 48138658 67108864 0 1000000000000000 21780000 10890000 hp765940 BSN.pi_near_15 hp765948 rfl rfl

noncomputable def hp765950 := @hp765929 33554432 10471519 2854748160000 46777130 46777610 33554432 (@hp765930 48138658 67108864 167544304 45675970560000 24069329 33554432 10471519 2854748160000 (hp765937 (hp765949 rfl rfl) rfl rfl) rfl)

noncomputable def hp765951 := @hp765928 Bool.false 93554740 67108864 480 67108864 23388685 16777216 15 2097152 (hp765950 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp765952 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765922 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp765953 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765922 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 71737643)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp765954 := nat_lit 169385720472902180407627073845

noncomputable def hp765955 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765922 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp765954

noncomputable def hp765956 := nat_lit 47392208348442322955242852721144561

noncomputable def hp765957 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp765922 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp765958 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp765959 := @hp765958 (Enclosure.sfrac Bool.false 1 16) 121183450035015 1125899906842624 1756172679 1125899906842624 1 16 0

noncomputable def hp765960 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1)) 866586718244025

noncomputable def hp765961 := @hp765960 1125899906842624 1118638471 1125899906842624 29437845 33554432 19 33554432 4066241833725308436480 121183450035015 1125899906842624 1756172679

noncomputable def hp765962 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1)) 29437845 33554432 19

noncomputable def hp765963 := @hp765962 33554432 29437845 33554432 19 33554432 866586718244025 1125899906842624 1118638471 1125899906842624 (@hp765935 1 29437845 29437845 33554432 19 33554432 (hp765917 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp765964 := hp765963 (@hp765935 1 29437845 29437845 33554432 19 33554432 (hp765917 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp765965 := @hp765961 1125899906842624 (hp765964 rfl) (@hp765935 1 29437845 29437845 33554432 19 33554432 (hp765917 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp765966 := @hp765957 500000000000000 191552194212679 1125899906842624 1756172679 1125899906842624 hp765954 hp682141 hp765956 hp682143 hd4948 (@hp765959 1 3064835107402864 191552194212679 1125899906842624 1756172679 1125899906842624 (hp765965 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp765967 := @hp765953 71737643 67108864 329 33554432 Bool.false 16140481 33554432 1 10890000 (@hp765955 hp682141 hp765956 hp682143 71737643 67108864 329 33554432 (hp765966 rfl) rfl) (Enclosure.sfrac_true_div 71737643 67108864)

noncomputable def hp765968 := nat_lit 903139148334240893076124964899583808852058932342856926337627498081

noncomputable def hp765969 := nat_lit 701417872498997145904151114791314447733411210511605570003183201

noncomputable def hp765970 := nat_lit 2708014609257724684936566592469168797660709974607547567872876127841

noncomputable def hp765971 := BSN.cos_dyadic_bound_f 71737643 67108864 3 2 33554432 10890000 hp765968 hp738066 hp765969 hp765970 hp738069

noncomputable def hp765972 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 71737643) (BSN.cosEvenQ 67108864) 0 2 hp765968 hp738066 hp765969 rfl rfl rfl

noncomputable def hp765973 := hp765971 hp765969 16140481 rfl rfl rfl rfl rfl rfl rfl rfl (hp765972 rfl)

noncomputable def hp765974 := @BSN.binarySplit_of_base2 (BSN.cosOddP 71737643) (BSN.cosOddQ 67108864) 0 2 hp765970 hp738069 hp765969 rfl rfl rfl

noncomputable def hp765975 := hp765967 (BSN.cos_neg_of_bound 71737643 67108864 Bool.false 16140481 33554432 1 10890000 (hp765973 (hp765974 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp765976 := hp765927 hp765951 (@hp765952 16140481 33554432 3616364432 365407764480000 16140481 33554432 226022777 22837985280000 (hp765975 rfl) rfl)

noncomputable def hp765977 := @hp765902 33554432 377504625857485 562949953421312 120085026227027 6966505673588736000 918867777100792366645 4722366482869645213696 586923467281163619029 hp765723 (hp765920 rfl) (@hp765923 Bool.false 377504625857485 562949953421312 120085026227027 6966505673588736000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765727 (Enclosure.sfrac Bool.false 11 1)) (hp765924 rfl (hp765730 rfl rfl))) (hp765976 rfl))

noncomputable def hp765978 := @hp765724 94227644885428757859029 hp765723 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 886373 1000))) (@hp765729 94227644885428757859029 hp765723 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 886373 1000) 11 (hp765730 rfl rfl)) (@hp765733 94227644885428757859029 hp765723 hp765901 (hp765977 rfl) rfl rfl))

theorem hd5072 : hp765722 hp765723 := hp765978

noncomputable def hp765979 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 887643 1000)) Bool.false 40714850364486614389619 9444732965739290427392 576512469283444201165847

noncomputable def hp765980 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 887643 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 887643 1000)) Bool.false 40714850364486614389619 9444732965739290427392

noncomputable def hp765981 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 887643 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp765982 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp765981 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp765983 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 887643 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp765984 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000)) (Enclosure.sfrac Bool.false 887643 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp765982 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp765985 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 887643 1000)) hp765984 Bool.false 40714850364486614389619 9444732965739290427392

noncomputable def hp765986 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 887643 1000) 887643 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 887643 1000)) rfl

noncomputable def hp765987 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000)) (Enclosure.sfrac Bool.false 887643 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp765982 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp765988 := nat_lit 10929309423562730539573537931264

noncomputable def hp765989 := @hp765987 1103828347 268435456 215377 268435456 1877343081438250668915 9444732965739290427392 3433440913106245325847 hp762191 hp765988 40714850364486614389619 9444732965739290427392

noncomputable def hp765990 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000)) (Enclosure.sfrac Bool.false 887643 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000)) (Enclosure.sfrac Bool.false 887643 1000) 11)

noncomputable def hp765991 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000)) (Enclosure.sfrac Bool.false 887643 1000) 11) hp765990

noncomputable def hp765992 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000)) (Enclosure.sfrac Bool.false 887643 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000)) (Enclosure.sfrac Bool.false 887643 1000) 11)

noncomputable def hp765993 := @hp765992 1103828347 536870912 215377 536870912 1103828347 536870912 215377 536870912 1185226662690684928 1103828347 268435456

noncomputable def hp765994 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000)) (Enclosure.sfrac Bool.false 887643 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp765995 := hp765994 BSN.quadSignPos 9 10 11 887643 1000 185 239 536870912 268435456 9007199254740992

noncomputable def hp765996 := hp765995 Bool.false 941139877570 4044 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp765997 := hp765996 Bool.false 1141271646 184895 Bool.true 143122728 Bool.true 24159480 28296951008113761 1 Bool.false 141433487

noncomputable def hp765998 := hp765997 Bool.true Bool.false 24151326 Bool.false Bool.false 1103828347 215377 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 185 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 141433487 536870912) BSN.abs_quadSignPos

noncomputable def hp765999 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000)) (Enclosure.sfrac Bool.false 887643 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp766000 := hp765999 BSN.quadSignNeg 7 8 9 887643 1000 59 125 536870912 268435456 9007199254740992

noncomputable def hp766001 := hp766000 Bool.false 941139877570 4044 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp766002 := hp766001 Bool.false 1269260835 151002 Bool.true 61802354 Bool.true 532480723 28296951008113761 1 Bool.false 61665947

noncomputable def hp766003 := hp766002 Bool.false Bool.false 449374187 Bool.true Bool.false 1141271646 184895 BSN.abs_quadSignPos (BSN.cos_quad_nat3 59 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 61665947 536870912) BSN.abs_quadSignNeg

noncomputable def hp766004 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000)) (Enclosure.sfrac Bool.false 887643 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp766005 := hp766004 BSN.quadSignPos 5 6 7 887643 1000 103 16 536870912 268435456 9007199254740992

noncomputable def hp766006 := hp766005 Bool.false 941139877570 4044 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp766007 := hp766006 Bool.false 948833905 112211 Bool.false 416003884 Bool.false 323942264 28296951008113761 1 Bool.false 375606428

noncomputable def hp766008 := hp766007 Bool.false Bool.false 442068651 Bool.false Bool.false 1269260835 151002 BSN.abs_quadSignPos (BSN.cos_quad_nat3 103 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 375606428 536870912) BSN.abs_quadSignPos

noncomputable def hp766009 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000)) (Enclosure.sfrac Bool.false 887643 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp766010 := hp766009 BSN.quadSignNeg 3 4 5 887643 1000 332 206 536870912 268435456 9007199254740992

noncomputable def hp766011 := hp766010 Bool.false 941139877570 4044 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp766012 := hp766011 Bool.false 961180279 66321 Bool.false 521186063 Bool.false 439865689 28296951008113761 1 Bool.false 303145274

noncomputable def hp766013 := hp766012 Bool.false Bool.false 366534032 Bool.true Bool.false 948833905 112211 BSN.abs_quadSignPos (BSN.cos_quad_nat0 332 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 303145274 536870912) BSN.abs_quadSignNeg

noncomputable def hp766014 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000)) (Enclosure.sfrac Bool.false 887643 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp766015 := hp766014 BSN.quadSignPos 1 2 3 887643 1000 724 495 536870912 268435456 9007199254740992

noncomputable def hp766016 := hp766015 Bool.false 941139877570 4044 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp766017 := hp766016 Bool.false 536870680 4098 Bool.false 260848972 Bool.false 155664130 28296951008113761 1 Bool.false 474738544

noncomputable def hp766018 := hp766017 Bool.false Bool.false 153492184 Bool.false Bool.false 961180279 66321 BSN.abs_quadSignPos (BSN.cos_quad_nat0 724 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 474738544 536870912) BSN.abs_quadSignPos

noncomputable def hp766019 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000)) (Enclosure.sfrac Bool.false 887643 1000) 1) Bool.false

noncomputable def hp766020 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000)) (Enclosure.sfrac Bool.false 887643 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000)))

noncomputable def hp766021 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000))) Bool.false 67108835 67108864

noncomputable def hp766022 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 14705310587) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false 14705310587 8388608

noncomputable def hp766023 := nat_lit 15446656036592191214648058759191867923290427682446917575797

noncomputable def hp766024 := nat_lit 8811506675418920662965180120022572227452667655356416000

noncomputable def hp766025 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000)) Bool.false hp766023 hp766024 134355819508455282589

noncomputable def hp766026 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 887643 4000) (Real.log (Enclosure.sfrac Bool.false 3151641381796 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1775286))))))

noncomputable def hp766027 := nat_lit 264504612168975035438721670292640000

noncomputable def hp766028 := nat_lit 1408714213347122629590419881399355085120

noncomputable def hp766029 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp766026 (Enclosure.sfrac Bool.false 887643 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 887643 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp766027 hp766028)) Bool.false

noncomputable def hp766030 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 887643 1000) 887643 1000 3151641381796 16000000 1775286

noncomputable def hp766031 := hp766030 4000 2000 hp766027 hp766028 (@Eq.refl Real (Enclosure.sfrac Bool.false 887643 1000)) rfl rfl rfl rfl

noncomputable def hp766032 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp766026 (Enclosure.sfrac Bool.false 887643 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 887643 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp766027 hp766028) 31579417406868366348253 18014398509481984000

noncomputable def hp766033 := nat_lit 44486369385385510698186409226472579619076431725447122618295360

noncomputable def hp766034 := @hp766032 134355819508455282589 hp738659 hp766027 hp766028 0 1 hp766033 hp766023 hp766024 134355819508455282589 hp738659

noncomputable def hp766035 := @Enclosure.Real.IsNear.subLit_ff_p (hp766026 (Enclosure.sfrac Bool.false 887643 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 887643 2000) (Real.log Real.pi)) 40731735855822546456541 18014398509481984000 11195553933479359 4356000000000000000000

noncomputable def hp766036 := nat_lit 2119258827956761863167087214592000

noncomputable def hp766037 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 887643 4000) (Real.log (Enclosure.sfrac Bool.false 3151641381796 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1775286))))))

noncomputable def hp766038 := @hp766037 (Enclosure.sfrac Bool.false 887643 2000) 48726913223898604818397 18014398509481984000 11195553933479359 4356000000000000000000 887643 2000 0

noncomputable def hp766039 := nat_lit 81463471711645092913082000

noncomputable def hp766040 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 887643 4000) (Real.log (Enclosure.sfrac Bool.false 3151641381796 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1775286))))) 48733984924935574058397

noncomputable def hp766041 := nat_lit 109723254119032125293877334714357907456

noncomputable def hp766042 := @hp766040 18014398509481984000 1232839325881651 484000000000000000000 883962629621155 2251799813685248 200000001089 8712000000000000000 hp766041 48726913223898604818397 18014398509481984000 11195553933479359

noncomputable def hp766043 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 887643 4000) (Real.log (Enclosure.sfrac Bool.false 3151641381796 16000000)) 887643 4000 0 1 54902686017842279 4503599627370496

noncomputable def hp766044 := nat_lit 117902620454594530395553792

noncomputable def hp766045 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3151641381796) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp766044 hp617687

noncomputable def hp766046 := BSN.log_rat_reduce_isNear 3151641381796 16000000 17 6303282763592 4194304000000 109345346 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp766047 := nat_lit 164975428534446898130689238814117733495391553786930110138677138607245977908394885323897076828615987336830289116460007387216368107520

noncomputable def hp766048 := nat_lit 2274892623075226608470885788735333142682300313710676519536000521152738056026681068669004793365309905946618394809742134231568482304

noncomputable def hp766049 := nat_lit 1606400823521975492500170356545986199074577189350321130262141791995903917663281242062203645154295759590186521798179233464320

noncomputable def hp766050 := BSN.log_dyadic_bound 1054489381796 5248793381796 6 5 hp766047 268435456 87120000 hp766048 hp766049 109345346 6303282763592

noncomputable def hp766051 := hp766050 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp766052 := @BSN.binarySplit_of_base5 (BSN.artanhP 1054489381796) (BSN.artanhQ 5248793381796) 0 5 hp766048 hp766047 hp766049 rfl rfl rfl

noncomputable def hp766053 := hp766046 rfl rfl rfl rfl (hp766051 (hp766052 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp766054 := @hp766043 12500018513 1089000000000000000 48733984924935574058397 18014398509481984000 1232839325881651 484000000000000000000 (Enclosure.Real.IsNear.const Bool.false 887643 4000) (BSN.isNear_log_sfrac 3151641381796 16000000 54902686017842279 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp766045 1000001481040000 87120000000000000000000 54902686017842279 4503599627370496 12500018513 1089000000000000000 (hp766053 rfl rfl rfl) rfl)) rfl

noncomputable def hp766055 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1775286)))) 1 4

noncomputable def hp766056 := @hp766055 0 1 883962629621155 562949953421312 200000001089 2178000000000000000 883962629621155 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp766057 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1775286))) 884279719003555 562949953421312 1

noncomputable def hp766058 := @hp766057 2000000000000000 18900 33554432 1 10890000 29660863946164231208960 883962629621155 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp766059 := BSN.arctan_dyadic_bound_f 1000 1775286 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp766060 := hp766059 1 18900 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1775286) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1775286) 0 0 rfl)

noncomputable def hp766061 := hp766056 (hp766058 (hp766060 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp766062 := @hp766035 34095043126323 67108864000 2662929 536870912000 hp766036 31579417406868366348253 18014398509481984000 134355819508455282589 hp738659 (@hp766038 1 hp766039 40731735855822546456541 18014398509481984000 11195553933479359 4356000000000000000000 (@hp766042 4356000000000000000000 hp766054 hp766061 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 887643 2000) rfl rfl)

noncomputable def hp766063 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 887643 2000) (Real.log Real.pi) 887643 2000 0 1 38410761 33554432

noncomputable def hp766064 := hp766062 (@hp766063 3 268435456 34095043126323 67108864000 2662929 536870912000 (Enclosure.Real.IsNear.const Bool.false 887643 2000) hd4909 rfl) rfl

noncomputable def hp766065 := @hp766025 hp738659 14705310587 8388608 253 33554432 (@hp766029 hp766023 hp766024 134355819508455282589 hp738659 (hp766031 rfl rfl rfl rfl rfl) (hp766034 (hp766064 rfl) (Enclosure.Real.IsNear.const Bool.true hp766027 hp766028) rfl rfl)) rfl

noncomputable def hp766066 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 14705310587) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1120670302668140314624) (@Nat.cast Real Real.instNatCast hp630689)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp766067 := BSN.sin_reduce_arg_pos_rat_q0 14705310587 8388608 226375608064910080 72057594037927936 279 1120670302668140314624 hp630689 rfl rfl rfl rfl

noncomputable def hp766068 := BSN.cos_dyadic_bound_f 127405462 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp766069 := hp766068 1 67108835 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 127405462) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp766070 := hp766069 (@BSN.binarySplit_of_le (BSN.cosOddP 127405462) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp766071 := @BSN.cos_arg_round Bool.false 67108835 67108864 1120670302668140314624 hp630689 127405462 137438953472 21801270 21780000 hp766070 rfl

noncomputable def hp766072 := hp766066 67108835 67108864 279 1000000000000000 21780000 10890000 hp766067 BSN.pi_near_15 hp766071 rfl rfl

noncomputable def hp766073 := @hp766022 253 33554432 Bool.false 67108835 67108864 1 10890000 hp766065 (Enclosure.sfrac_false_div 14705310587 8388608) (hp766072 rfl rfl) rfl

noncomputable def hp766074 := @hp766019 67108835 67108864 174295277 22837985280000 536870680 536870912 4098 536870912 (@hp766020 Bool.false 67108835 67108864 174295277 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000)) (Enclosure.sfrac Bool.false 887643 1000)) (@hp766021 2788724432 365407764480000 67108835 67108864 174295277 22837985280000 (hp766073 rfl) rfl))

noncomputable def hp766075 := @hp766025 hp738659 941139877570 536870912 4044 536870912 (@hp766029 hp766023 hp766024 134355819508455282589 hp738659 (hp766031 rfl rfl rfl rfl rfl) (hp766034 (hp766064 rfl) (Enclosure.Real.IsNear.const Bool.true hp766027 hp766028) rfl rfl)) rfl

noncomputable def hp766076 := hp766018 (BSN.cos_quad_nat3 495 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 153492184 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 887643 1000)) rfl rfl (hp766074 rfl) hp766075

noncomputable def hp766077 := nat_lit 646189211375708837946071428824544073389800779127878108719012494893449216

noncomputable def hp766078 := nat_lit 21434484152449253843667969152392291334504790617782896857448500494336

noncomputable def hp766079 := nat_lit 1938524765158821615330526950535327435586733327802398760363322587679358976

noncomputable def hp766080 := BSN.cos_dyadic_bound_f 260848972 536870912 3 2 536870912 268435456 hp766077 hp708868 hp766078 hp766079 hp708870

noncomputable def hp766081 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 260848972) (BSN.cosEvenQ 536870912) 0 2 hp766077 hp708868 hp766078 rfl rfl rfl

noncomputable def hp766082 := hp766080 hp766078 474738544 rfl rfl rfl rfl rfl rfl rfl rfl (hp766081 rfl)

noncomputable def hp766083 := @BSN.binarySplit_of_base2 (BSN.cosOddP 260848972) (BSN.cosOddQ 536870912) 0 2 hp766079 hp708870 hp766078 rfl rfl rfl

noncomputable def hp766084 := nat_lit 587156935271128501437709917610000

noncomputable def hp766085 := BSN.sin_dyadic_bound_f 155664130 536870912 2 1 536870912 268435456 hp766084 hp708890 hp766084 hp766084 hp708891

noncomputable def hp766086 := @BSN.binarySplit_of_base (BSN.sinEvenP 155664130) (BSN.sinEvenQ 536870912) 0 1 hp766084 hp708890 hp766084 rfl rfl rfl

noncomputable def hp766087 := hp766085 hp766084 153492184 rfl rfl rfl rfl rfl rfl rfl rfl (hp766086 rfl)

noncomputable def hp766088 := @BSN.binarySplit_of_base (BSN.sinOddP 155664130) (BSN.sinOddQ 536870912) 0 1 hp766084 hp708891 hp766084 rfl rfl rfl

noncomputable def hp766089 := hp766076 hd4911 hd4913 hd4915 hd4917 hd4918 (hp766082 (hp766083 rfl) rfl rfl rfl rfl) (hp766087 (hp766088 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766090 := hp766013 (BSN.cos_quad_nat2 206 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 366534032 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 887643 1000)) rfl rfl (hp766089 rfl rfl rfl rfl rfl) hp766075

noncomputable def hp766091 := nat_lit 10169168539222762812435529907881233044425254777557875317388711076847097848479329312704232279814979110855647575361

noncomputable def hp766092 := nat_lit 401710815899106895028890270505283487962993797569844454033050231580188195935785198088888206543781838863681

noncomputable def hp766093 := nat_lit 61671221896104987439578305094306295896441695181044373543980883590219666145966871877994862943233764679275571723585

noncomputable def hp766094 := BSN.cos_dyadic_bound_f 521186063 536870912 4 3 536870912 268435456 hp766091 hp716712 hp766092 hp766093 hp716714

noncomputable def hp766095 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 521186063) (BSN.cosEvenQ 536870912) 0 3 hp766091 hp716712 hp766092 rfl rfl rfl

noncomputable def hp766096 := hp766094 hp766092 303145274 rfl rfl rfl rfl rfl rfl rfl rfl (hp766095 rfl)

noncomputable def hp766097 := @BSN.binarySplit_of_base3 (BSN.cosOddP 521186063) (BSN.cosOddQ 536870912) 0 3 hp766093 hp716714 hp766092 rfl rfl rfl

noncomputable def hp766098 := nat_lit 5226194844536724252870555437397864479111725662940778879587755163383744961

noncomputable def hp766099 := nat_lit 1401395423729767124539011445826282923870188308440940095590419207801281

noncomputable def hp766100 := nat_lit 15675781742762713224362588289301940871487436612205454758572084651735632321

noncomputable def hp766101 := BSN.cos_dyadic_bound_f 439865689 536870912 3 2 536870912 268435456 hp766098 hp708868 hp766099 hp766100 hp708870

noncomputable def hp766102 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 439865689) (BSN.cosEvenQ 536870912) 0 2 hp766098 hp708868 hp766099 rfl rfl rfl

noncomputable def hp766103 := hp766101 hp766099 366534032 rfl rfl rfl rfl rfl rfl rfl rfl (hp766102 rfl)

noncomputable def hp766104 := @BSN.binarySplit_of_base2 (BSN.cosOddP 439865689) (BSN.cosOddQ 536870912) 0 2 hp766100 hp708870 hp766099 rfl rfl rfl

noncomputable def hp766105 := hp766090 hd4920 hd4922 hd4924 hd4926 hd4918 (hp766096 (hp766097 rfl) rfl rfl rfl rfl) (hp766103 (hp766104 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766106 := hp766008 (BSN.cos_quad_nat0 16 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 442068651 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 887643 1000)) rfl rfl (hp766105 rfl rfl rfl rfl rfl) hp766075

noncomputable def hp766107 := nat_lit 7524932291083843756215289785570674562398242589974864696465031545711820800

noncomputable def hp766108 := nat_lit 896972406997864960789928262892207089558872987757678927880909026820096

noncomputable def hp766109 := nat_lit 19706703759417784723008289554545179328136111465096847486763275433678012416

noncomputable def hp766110 := BSN.sin_dyadic_bound_f 416003884 536870912 3 2 536870912 268435456 hp766107 hp708845 hp766108 hp766109 hp708848

noncomputable def hp766111 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 416003884) (BSN.sinEvenQ 536870912) 0 2 hp766107 hp708845 hp766108 rfl rfl rfl

noncomputable def hp766112 := hp766110 hp766108 375606428 rfl rfl rfl rfl rfl rfl rfl rfl (hp766111 rfl)

noncomputable def hp766113 := @BSN.binarySplit_of_base2 (BSN.sinOddP 416003884) (BSN.sinOddQ 536870912) 0 2 hp766109 hp708848 hp766108 rfl rfl rfl

noncomputable def hp766114 := nat_lit 1537069468353498152154884747881963788546649030986972254679330276807540736

noncomputable def hp766115 := nat_lit 121266517235963970524493980605791943325033228055694844085126672941056

noncomputable def hp766116 := nat_lit 4610965872026022528523605255684679781753297026504805374349820577076740096

noncomputable def hp766117 := BSN.cos_dyadic_bound_f 323942264 536870912 3 2 536870912 268435456 hp766114 hp708868 hp766115 hp766116 hp708870

noncomputable def hp766118 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 323942264) (BSN.cosEvenQ 536870912) 0 2 hp766114 hp708868 hp766115 rfl rfl rfl

noncomputable def hp766119 := hp766117 hp766115 442068651 rfl rfl rfl rfl rfl rfl rfl rfl (hp766118 rfl)

noncomputable def hp766120 := @BSN.binarySplit_of_base2 (BSN.cosOddP 323942264) (BSN.cosOddQ 536870912) 0 2 hp766116 hp708870 hp766115 rfl rfl rfl

noncomputable def hp766121 := hp766106 hd4928 hd4930 hd4932 hd4934 hd4918 (hp766112 (hp766113 rfl) rfl rfl rfl rfl) (hp766119 (hp766120 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766122 := hp766003 (BSN.cos_quad_nat1 125 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 449374187 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 887643 1000)) rfl rfl (hp766121 rfl rfl rfl rfl rfl) hp766075

noncomputable def hp766123 := nat_lit 14588816753950230890290163811856

noncomputable def hp766124 := BSN.sin_dyadic_bound_f 61802354 536870912 2 1 536870912 268435456 hp766123 hp708890 hp766123 hp766123 hp708891

noncomputable def hp766125 := @BSN.binarySplit_of_base (BSN.sinEvenP 61802354) (BSN.sinEvenQ 536870912) 0 1 hp766123 hp708890 hp766123 rfl rfl rfl

noncomputable def hp766126 := hp766124 hp766123 61665947 rfl rfl rfl rfl rfl rfl rfl rfl (hp766125 rfl)

noncomputable def hp766127 := @BSN.binarySplit_of_base (BSN.sinOddP 61802354) (BSN.sinOddQ 536870912) 0 1 hp766123 hp708891 hp766123 rfl rfl rfl

noncomputable def hp766128 := nat_lit 20202996893615466692342514196154707797621094983735829102598389382368521505

noncomputable def hp766129 := nat_lit 6462954815767545871579821998462739346995342424269186091786643847048481

noncomputable def hp766130 := nat_lit 52902147080243551024724026992407675987207732498240259443609079530450906401

noncomputable def hp766131 := BSN.sin_dyadic_bound_f 532480723 536870912 3 2 536870912 268435456 hp766128 hp708845 hp766129 hp766130 hp708848

noncomputable def hp766132 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 532480723) (BSN.sinEvenQ 536870912) 0 2 hp766128 hp708845 hp766129 rfl rfl rfl

noncomputable def hp766133 := hp766131 hp766129 449374187 rfl rfl rfl rfl rfl rfl rfl rfl (hp766132 rfl)

noncomputable def hp766134 := @BSN.binarySplit_of_base2 (BSN.sinOddP 532480723) (BSN.sinOddQ 536870912) 0 2 hp766130 hp708848 hp766129 rfl rfl rfl

noncomputable def hp766135 := hp766122 hd4936 hd4938 hd4940 hd4942 hd4918 (hp766126 (hp766127 rfl) rfl rfl rfl rfl) (hp766133 (hp766134 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766136 := hp765998 (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 24151326 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 887643 1000)) rfl rfl (hp766135 rfl rfl rfl rfl rfl) hp766075

noncomputable def hp766137 := nat_lit 419598978401283370755817598816256

noncomputable def hp766138 := BSN.sin_dyadic_bound_f 143122728 536870912 2 1 536870912 268435456 hp766137 hp708890 hp766137 hp766137 hp708891

noncomputable def hp766139 := @BSN.binarySplit_of_base (BSN.sinEvenP 143122728) (BSN.sinEvenQ 536870912) 0 1 hp766137 hp708890 hp766137 rfl rfl rfl

noncomputable def hp766140 := hp766138 hp766137 141433487 rfl rfl rfl rfl rfl rfl rfl rfl (hp766139 rfl)

noncomputable def hp766141 := @BSN.binarySplit_of_base (BSN.sinOddP 143122728) (BSN.sinOddQ 536870912) 0 1 hp766137 hp708891 hp766137 rfl rfl rfl

noncomputable def hp766142 := nat_lit 340682895577574697155996160000

noncomputable def hp766143 := BSN.sin_dyadic_bound_f 24159480 536870912 2 1 536870912 268435456 hp766142 hp708890 hp766142 hp766142 hp708891

noncomputable def hp766144 := @BSN.binarySplit_of_base (BSN.sinEvenP 24159480) (BSN.sinEvenQ 536870912) 0 1 hp766142 hp708890 hp766142 rfl rfl rfl

noncomputable def hp766145 := hp766143 hp766142 24151326 rfl rfl rfl rfl rfl rfl rfl rfl (hp766144 rfl)

noncomputable def hp766146 := @BSN.binarySplit_of_base (BSN.sinOddP 24159480) (BSN.sinOddQ 536870912) 0 1 hp766142 hp708891 hp766142 rfl rfl rfl

noncomputable def hp766147 := hp766136 hd4944 hd4946 hd4961 hd4963 hd4918 (hp766140 (hp766141 rfl) rfl rfl rfl rfl) (hp766145 (hp766146 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766148 := @hp765993 215377 268435456 (hp766147 rfl rfl rfl rfl rfl) (hp766147 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp766149 := @hp765991 Bool.false 1103828347 268435456 215377 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 887643 1000)) (Enclosure.sfrac Bool.false 887643 1000) 11) hp766148

noncomputable def hp766150 := @Enclosure.Real.IsNear.mulLit_tf hp765982 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1))) 19465487 67108864 1

noncomputable def hp766151 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp765981 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp766152 := @hp766151 1 1 0 1 19465487 67108864 1 67108864 19465487 67108864 1

noncomputable def hp766153 := @Enclosure.Real.IsNear.of_eq (hp765981 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp766154 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 887643 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp766155 := @hp766153 (@Inv.inv Real Real.instInv (Real.sqrt hp765983)) Bool.false 19465487 67108864 1 67108864 (hp766154 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 887643 1000) 887643 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 887643 1000))))

noncomputable def hp766156 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp765983)) Bool.false 19465487 67108864 1 67108864 19465487 67108864

noncomputable def hp766157 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp765983) Bool.false 231363315 67108864 7 67108864 231363315 67108864 7 67108864

noncomputable def hp766158 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 887643 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp766159 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 887643 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp766160 := @hp766159 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 887643 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9480654803601

noncomputable def hp766161 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 887643 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 887643 1000 0

noncomputable def hp766162 := @hp766161 1 10680707 67108864 1 67108864 9480654803601 67108864000 887643 67108864000 (Enclosure.Real.IsNear.const Bool.false 887643 1000) hd4949

noncomputable def hp766163 := @hp766160 67108864000 887643 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 887643 1000) 887643 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 887643 1000))) (hp766162 rfl)

noncomputable def hp766164 := @hp766158 9480654803601 67108864000 887643 67108864000 398821988 398822026 33554432 hp766163 rfl rfl rfl

noncomputable def hp766165 := @Enclosure.Real.IsNear.recentre' hp765983 Bool.false 797644014 67108864 38 67108864 398822007 33554432 19 33554432 (hp766164 rfl rfl rfl)

noncomputable def hp766166 := @Enclosure.Real.IsNear.sqrt_image hp765983 398822007 33554432 19 33554432 115681654 115681661 33554432 (hp766165 rfl) rfl rfl

noncomputable def hp766167 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp765983) 231363315 67108864 7 67108864 9732743 9732744 33554432 (hp766157 (hp766166 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp766168 := @hp766152 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp766155 (@hp766156 1 67108864 (hp766167 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp766169 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp766170 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp766171 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1))) (hp766169 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766170 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp766172 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 887643 1000) 887643 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 887643 1000)) rfl

noncomputable def hp766173 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp766174 := @hp766173 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766170 (Enclosure.sfrac Bool.false 1 16)))) 44530443

noncomputable def hp766175 := @hp766174 33554432 27 4194304 2165815 4194304 227384027 22837985280000 96444701406045 140737488355328 1408090989575977 85146180454973440000

noncomputable def hp766176 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp766177 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1)))) 50567649

noncomputable def hp766178 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp766179 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 186756719) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp766180 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1))) Bool.false 26283671579271011171525

noncomputable def hp766181 := nat_lit 512735433027157679959547333

noncomputable def hp766182 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp766183 := @Enclosure.Real.IsNear.subLit_ff_p hp765983 (Enclosure.sfrac Bool.false 11 1) 398822007 33554432 19 33554432 11 1 0

noncomputable def hp766184 := @hp766182 500000000000000 29723255 33554432 19 33554432 26283671579271011171525 4722366482869645213696 hp766181 hp682805 hd4948 (@hp766183 1 29723255 29723255 33554432 19 33554432 (hp766165 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp766185 := @hp766179 186756719 33554432 239 67108864 Bool.false 50567649 67108864 1 10890000 (@hp766180 4722366482869645213696 hp766181 hp682805 186756719 33554432 239 67108864 (hp766184 rfl) rfl) (Enclosure.sfrac_false_div 186756719 33554432)

noncomputable def hp766186 := nat_lit 4126764841296735175180288

noncomputable def hp766187 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 186756719) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp766186) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp766188 := BSN.sin_reduce_arg_pos_rat_q3 186756719 33554432 226375608064910080 72057594037927936 0 hp766186 hp619237 rfl rfl rfl rfl

noncomputable def hp766189 := nat_lit 204238202480326640971245493353104437121748580445400255280142629121255629978086666354125840640

noncomputable def hp766190 := nat_lit 35816185907691277655020316488407892114094608435796321708730989618675359980542689767465216

noncomputable def hp766191 := nat_lit 534851589814147797618011021126673246350680605133818903117607035620096413645496580858325115136

noncomputable def hp766192 := BSN.sin_dyadic_bound_f 117289711206 137438953472 3 2 67108864 21801270 hp766189 hp738039 hp766190 hp766191 hp738042

noncomputable def hp766193 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 117289711206) (BSN.sinEvenQ 137438953472) 0 2 hp766189 hp738039 hp766190 rfl rfl rfl

noncomputable def hp766194 := hp766192 hp766190 50567649 rfl rfl rfl rfl rfl rfl rfl rfl (hp766193 rfl)

noncomputable def hp766195 := @BSN.binarySplit_of_base2 (BSN.sinOddP 117289711206) (BSN.sinOddQ 137438953472) 0 2 hp766191 hp738042 hp766190 rfl rfl rfl

noncomputable def hp766196 := @BSN.sin_arg_round Bool.false 50567649 67108864 hp766186 hp619237 117289711206 137438953472 21801270 21780000 (hp766194 (hp766195 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766197 := hp766187 50567649 67108864 0 1000000000000000 21780000 10890000 hp766188 BSN.pi_near_15 hp766196 rfl rfl

noncomputable def hp766198 := @hp766177 67108864 166863679 45675970560000 44530227 44530659 33554432 (@hp766178 50567649 67108864 2669818864 730815528960000 50567649 67108864 166863679 45675970560000 (hp766185 (hp766197 rfl rfl) rfl rfl) rfl)

noncomputable def hp766199 := @hp766176 Bool.false 89060886 67108864 432 67108864 44530443 33554432 27 4194304 (hp766198 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp766200 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766170 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp766201 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766170 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 17250149)) (@Nat.cast Real Real.instNatCast 16777216)) Bool.true

noncomputable def hp766202 := nat_lit 162923051358114543649057230445

noncomputable def hp766203 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766170 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp766202

noncomputable def hp766204 := nat_lit 47684887988114364203390064206923461

noncomputable def hp766205 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766170 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp766206 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp766207 := @hp766206 (Enclosure.sfrac Bool.false 1 16) 113875050921135 1125899906842624 1767018259 1125899906842624 1 16 0

noncomputable def hp766208 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1)) 883471887795025

noncomputable def hp766209 := @hp766208 1125899906842624 1129484051 1125899906842624 29723255 33554432 19 33554432 3821012652629761720320 113875050921135 1125899906842624 1767018259

noncomputable def hp766210 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1)) 29723255 33554432 19

noncomputable def hp766211 := @hp766210 33554432 29723255 33554432 19 33554432 883471887795025 1125899906842624 1129484051 1125899906842624 (@hp766183 1 29723255 29723255 33554432 19 33554432 (hp766165 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp766212 := hp766211 (@hp766183 1 29723255 29723255 33554432 19 33554432 (hp766165 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp766213 := @hp766209 1125899906842624 (hp766212 rfl) (@hp766183 1 29723255 29723255 33554432 19 33554432 (hp766165 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp766214 := @hp766205 500000000000000 184243795098799 1125899906842624 1767018259 1125899906842624 hp766202 hp682141 hp766204 hp682143 hd4948 (@hp766207 1 2947900721580784 184243795098799 1125899906842624 1767018259 1125899906842624 (hp766213 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp766215 := @hp766201 17250149 16777216 331 33554432 Bool.false 17326520 33554432 1 10890000 (@hp766203 hp682141 hp766204 hp682143 17250149 16777216 331 33554432 (hp766214 rfl) rfl) (Enclosure.sfrac_true_div 17250149 16777216)

noncomputable def hp766216 := nat_lit 11793673080762359047807331735047850222288466053388963013805281

noncomputable def hp766217 := nat_lit 7840482783726915241962588218482107231536762490472511128801

noncomputable def hp766218 := nat_lit 35365338276719623312938070028706586452402324635185944019158241

noncomputable def hp766219 := BSN.cos_dyadic_bound_f 17250149 16777216 3 2 33554432 10890000 hp766216 hp631348 hp766217 hp766218 hp631351

noncomputable def hp766220 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 17250149) (BSN.cosEvenQ 16777216) 0 2 hp766216 hp631348 hp766217 rfl rfl rfl

noncomputable def hp766221 := hp766219 hp766217 17326520 rfl rfl rfl rfl rfl rfl rfl rfl (hp766220 rfl)

noncomputable def hp766222 := @BSN.binarySplit_of_base2 (BSN.cosOddP 17250149) (BSN.cosOddQ 16777216) 0 2 hp766218 hp631351 hp766217 rfl rfl rfl

noncomputable def hp766223 := hp766215 (BSN.cos_neg_of_bound 17250149 16777216 Bool.false 17326520 33554432 1 10890000 (hp766221 (hp766222 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp766224 := hp766175 hp766199 (@hp766200 17326520 33554432 3638144432 365407764480000 2165815 4194304 227384027 22837985280000 (hp766223 rfl) rfl)

noncomputable def hp766225 := @hp766150 67108864 96444701406045 140737488355328 1408090989575977 85146180454973440000 1877343081438250668915 9444732965739290427392 3433440913106245325847 hp762191 (hp766168 rfl) (@hp766171 Bool.false 96444701406045 140737488355328 1408090989575977 85146180454973440000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp765983 (Enclosure.sfrac Bool.false 11 1)) (hp766172 rfl (hp765986 rfl rfl))) (hp766224 rfl))

noncomputable def hp766226 := @hp765980 576512469283444201165847 hp762191 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 887643 1000))) (@hp765985 576512469283444201165847 hp762191 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 887643 1000) 11 (hp765986 rfl rfl)) (@hp765989 576512469283444201165847 hp762191 hp766149 (hp766225 rfl) rfl rfl))

theorem hd5073 : hp765979 hp762191 := hp766226

noncomputable def hp766227 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 888912 1000)) Bool.true 20441737308150466552939 9444732965739290427392 157432979705853290550803

noncomputable def hp766228 := nat_lit 194797617418372865064960000

noncomputable def hp766229 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 888912 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 888912 1000)) Bool.true 20441737308150466552939 9444732965739290427392

noncomputable def hp766230 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 888912 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp766231 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp766230 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp766232 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 888912 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp766233 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 888912 1000)) (Enclosure.sfrac Bool.false 888912 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp766231 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp766234 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 888912 1000)) hp766233 Bool.true 20441737308150466552939 9444732965739290427392

noncomputable def hp766235 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 888912 1000) 888912 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 888912 1000)) rfl

noncomputable def hp766236 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 888912 1000)) (Enclosure.sfrac Bool.false 888912 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp766231 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp766237 := nat_lit 685910884468197875718866075648

noncomputable def hp766238 := @hp766236 79437921 33554432 13481 16777216 1918049655267464633237 9444732965739290427392 907208063103707190803 hp766228 hp766237 20441737308150466552939 9444732965739290427392

noncomputable def hp766239 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 888912 1000)) (Enclosure.sfrac Bool.false 888912 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 888912 1000)) (Enclosure.sfrac Bool.false 888912 1000) 11)

noncomputable def hp766240 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 888912 1000)) (Enclosure.sfrac Bool.false 888912 1000) 11) hp766239

noncomputable def hp766241 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 888912 1000)) (Enclosure.sfrac Bool.false 888912 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 888912 1000)) (Enclosure.sfrac Bool.false 888912 1000) 11)

noncomputable def hp766242 := @hp766241 635503368 536870912 215696 536870912 635503368 536870912 215696 536870912 682366545514463232 79437921 33554432

noncomputable def hp766243 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 888912 1000)) (Enclosure.sfrac Bool.false 888912 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp766244 := hp766243 BSN.quadSignNeg 9 10 11 888912 1000 185 238 536870912 268435456 9007199254740992

noncomputable def hp766245 := hp766244 Bool.false 942826547255 4050 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp766246 := hp766245 Bool.true 618849429 185170 Bool.true 25179366 Bool.true 814464770 28296951008113761 1 Bool.false 25170136

noncomputable def hp766247 := hp766246 Bool.true Bool.false 28836203 Bool.true Bool.true 635503368 215696 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 185 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 25170136 536870912) BSN.abs_quadSignNeg

noncomputable def hp766248 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 888912 1000)) (Enclosure.sfrac Bool.false 888912 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp766249 := hp766248 BSN.quadSignNeg 7 8 9 888912 1000 58 125 536870912 268435456 9007199254740992

noncomputable def hp766250 := hp766249 Bool.false 942826547255 4050 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp766251 := hp766250 Bool.true 440434565 151229 Bool.true 635148562 Bool.true 342756366 28296951008113761 1 Bool.false 202989332

noncomputable def hp766252 := hp766251 Bool.true Bool.false 319941891 Bool.true Bool.true 618849429 185170 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 58 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 202989332 536870912) BSN.abs_quadSignNeg

noncomputable def hp766253 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 888912 1000)) (Enclosure.sfrac Bool.false 888912 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp766254 := hp766253 BSN.quadSignPos 5 6 7 888912 1000 104 16 536870912 268435456 9007199254740992

noncomputable def hp766255 := hp766254 Bool.false 942826547255 4050 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp766256 := hp766255 Bool.true 718059144 112382 Bool.false 38652369 Bool.false 684884425 28296951008113761 1 Bool.false 535480111

noncomputable def hp766257 := hp766256 Bool.false Bool.false 156140968 Bool.false Bool.true 440434565 151229 BSN.abs_quadSignPos (BSN.cos_quad_nat0 104 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 535480111 536870912) BSN.abs_quadSignPos

noncomputable def hp766258 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 888912 1000)) (Enclosure.sfrac Bool.false 888912 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp766259 := hp766258 BSN.quadSignPos 3 4 5 888912 1000 333 207 536870912 268435456 9007199254740992

noncomputable def hp766260 := hp766259 Bool.false 942826547255 4050 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp766261 := hp766260 Bool.true 610641187 66426 Bool.false 420073550 Bool.false 186727890 28296951008113761 1 Bool.false 378503440

noncomputable def hp766262 := hp766261 Bool.true Bool.false 182985841 Bool.false Bool.true 718059144 112382 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 333 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 378503440 536870912) BSN.abs_quadSignPos

noncomputable def hp766263 := hp766243 BSN.quadSignPos 1 2 3 888912 1000 725 496 536870912 268435456 9007199254740992

noncomputable def hp766264 := hp766263 Bool.false 942826547255 4050 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp766265 := hp766264 Bool.true 536870640 4114 Bool.false 631970140 Bool.false 250546292 28296951008113761 1 Bool.false 495806352

noncomputable def hp766266 := hp766265 Bool.true Bool.false 479461951 Bool.false Bool.true 610641187 66426 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 725 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 495806352 536870912) BSN.abs_quadSignPos

noncomputable def hp766267 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 888912 1000)) (Enclosure.sfrac Bool.false 888912 1000) 1) Bool.true

noncomputable def hp766268 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 888912 1000)) (Enclosure.sfrac Bool.false 888912 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 888912 1000)))

noncomputable def hp766269 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 888912 1000))) Bool.true 67108830 67108864

noncomputable def hp766270 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 888912 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 58926659203) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 58926659203 33554432

noncomputable def hp766271 := nat_lit 238152305437953229256817531405527913177826823238251359

noncomputable def hp766272 := nat_lit 135610357798592662264799205298187026591274500096000

noncomputable def hp766273 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 888912 1000)) Bool.false hp766271 hp766272 8409207055123595011

noncomputable def hp766274 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 888912 4000) (Real.log (Enclosure.sfrac Bool.false 3160659174976 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1777824))))))

noncomputable def hp766275 := nat_lit 266400742400359628873435808399360000

noncomputable def hp766276 := nat_lit 1420841110157004977091207224507447377920

noncomputable def hp766277 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 888912 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp766274 (Enclosure.sfrac Bool.false 888912 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 888912 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp766275 hp766276)) Bool.false

noncomputable def hp766278 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 888912 1000) 888912 1000 3160659174976 16000000 1777824

noncomputable def hp766279 := hp766278 4000 2000 hp766275 hp766276 (@Eq.refl Real (Enclosure.sfrac Bool.false 888912 1000)) rfl rfl rfl rfl

noncomputable def hp766280 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp766274 (Enclosure.sfrac Bool.false 888912 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 888912 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp766275 hp766276) 1977250790331396975271 1125899906842624000

noncomputable def hp766281 := nat_lit 2809358908052706509863462872874681917243970563793567391416320

noncomputable def hp766282 := @hp766280 8409207055123595011 1115136000000000000000000 hp766275 hp766276 0 1 hp766281 hp766271 hp766272 8409207055123595011 1115136000000000000000000

noncomputable def hp766283 := @Enclosure.Real.IsNear.subLit_ff_p (hp766274 (Enclosure.sfrac Bool.false 888912 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 888912 2000) (Real.log Real.pi)) 2550088469520606358183 1125899906842624000 2802854114243089 1089000000000000000000

noncomputable def hp766284 := nat_lit 8293190898890139658967056384000

noncomputable def hp766285 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 888912 4000) (Real.log (Enclosure.sfrac Bool.false 3160659174976 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1777824))))))

noncomputable def hp766286 := @hp766285 (Enclosure.sfrac Bool.false 888912 2000) 3050501438516251650727 1125899906842624000 2802854114243089 1089000000000000000000 888912 2000 0

noncomputable def hp766287 := nat_lit 5100176939041212716366000

noncomputable def hp766288 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 888912 4000) (Real.log (Enclosure.sfrac Bool.false 3160659174976 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1777824))))) 3050943420057554644227

noncomputable def hp766289 := nat_lit 6869118570897476474308384325208375296

noncomputable def hp766290 := @hp766288 1125899906842624000 77162614280749 30250000000000000000 883963082605987 2251799813685248 200000001089 8712000000000000000 hp766289 3050501438516251650727 1125899906842624000 2802854114243089

noncomputable def hp766291 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 888912 4000) (Real.log (Enclosure.sfrac Bool.false 3160659174976 16000000)) 888912 4000 0 1 54915553756638311 4503599627370496

noncomputable def hp766292 := nat_lit 117930253713245744322838528

noncomputable def hp766293 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3160659174976) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp766292 hp617687

noncomputable def hp766294 := BSN.log_rat_reduce_isNear 3160659174976 16000000 17 6321318349952 4194304000000 110112323 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp766295 := nat_lit 167831835763332797589674219549363606151655728271379881111565676330982251588069898556731173260118947428012338280655847587472495083520

noncomputable def hp766296 := nat_lit 2346769364503205027238157768120510743919217450285968998622873190609013114049591688971319634418017477332686617679851142481920917504

noncomputable def hp766297 := nat_lit 1749186233846162652152134273653252898214662124233424679650041015949015664339211203121526714393403399982776699689931972280320

noncomputable def hp766298 := BSN.log_dyadic_bound 1063507174976 5257811174976 6 5 hp766295 268435456 87120000 hp766296 hp766297 110112323 6321318349952

noncomputable def hp766299 := hp766298 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp766300 := @BSN.binarySplit_of_base5 (BSN.artanhP 1063507174976) (BSN.artanhQ 5257811174976) 0 5 hp766296 hp766295 hp766297 rfl rfl rfl

noncomputable def hp766301 := hp766294 rfl rfl rfl rfl (hp766299 (hp766300 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp766302 := @hp766291 12500018513 1089000000000000000 3050943420057554644227 1125899906842624000 77162614280749 30250000000000000000 (Enclosure.Real.IsNear.const Bool.false 888912 4000) (BSN.isNear_log_sfrac 3160659174976 16000000 54915553756638311 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp766293 1000001481040000 87120000000000000000000 54915553756638311 4503599627370496 12500018513 1089000000000000000 (hp766301 rfl rfl rfl) rfl)) rfl

noncomputable def hp766303 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1777824)))) 1 4

noncomputable def hp766304 := @hp766303 0 1 883963082605987 562949953421312 200000001089 2178000000000000000 883963082605987 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp766305 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1777824))) 884279719003555 562949953421312 1

noncomputable def hp766306 := @hp766305 2000000000000000 18873 33554432 1 10890000 29660879145812973584384 883963082605987 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp766307 := BSN.arctan_dyadic_bound_f 1000 1777824 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp766308 := hp766307 1 18873 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1777824) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1777824) 0 0 rfl)

noncomputable def hp766309 := hp766304 (hp766306 (hp766308 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp766310 := @hp766283 2133986648877 4194304000 166671 33554432000 hp766284 1977250790331396975271 1125899906842624000 8409207055123595011 1115136000000000000000000 (@hp766286 1 hp766287 2550088469520606358183 1125899906842624000 2802854114243089 1089000000000000000000 (@hp766290 1089000000000000000000 hp766302 hp766309 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 888912 2000) rfl rfl)

noncomputable def hp766311 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 888912 2000) (Real.log Real.pi) 888912 2000 0 1 38410761 33554432

noncomputable def hp766312 := hp766310 (@hp766311 3 268435456 2133986648877 4194304000 166671 33554432000 (Enclosure.Real.IsNear.const Bool.false 888912 2000) hd4909 rfl) rfl

noncomputable def hp766313 := @hp766273 1115136000000000000000000 58926659203 33554432 127 16777216 (@hp766277 hp766271 hp766272 8409207055123595011 1115136000000000000000000 (hp766279 rfl rfl rfl rfl rfl) (hp766282 (hp766312 rfl) (Enclosure.Real.IsNear.const Bool.true hp766275 hp766276) rfl rfl)) rfl

noncomputable def hp766314 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 58926659203) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 4842671355546289831936) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp766315 := BSN.sin_reduce_arg_pos_rat_q2 58926659203 33554432 226375608064910080 72057594037927936 279 4842671355546289831936 hp619237 rfl rfl rfl rfl

noncomputable def hp766316 := BSN.cos_dyadic_bound_f 137636998 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp766317 := hp766316 1 67108830 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 137636998) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp766318 := hp766317 (@BSN.binarySplit_of_le (BSN.cosOddP 137636998) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp766319 := @BSN.cos_arg_round Bool.false 67108830 67108864 4842671355546289831936 hp619237 137636998 137438953472 21801270 21780000 hp766318 rfl

noncomputable def hp766320 := hp766314 67108830 67108864 279 1000000000000000 21780000 10890000 hp766315 BSN.pi_near_15 hp766319 rfl rfl

noncomputable def hp766321 := @hp766270 127 16777216 Bool.true 67108830 67108864 1 10890000 hp766313 (Enclosure.sfrac_false_div 58926659203 33554432) (hp766320 rfl rfl) rfl

noncomputable def hp766322 := @hp766267 33554415 33554432 87487951 11418992640000 536870640 536870912 4114 536870912 (@hp766268 Bool.true 33554415 33554432 87487951 11418992640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 888912 1000)) (Enclosure.sfrac Bool.false 888912 1000)) (@hp766269 1399807216 182703882240000 33554415 33554432 87487951 11418992640000 (hp766321 rfl) rfl))

noncomputable def hp766323 := @hp766273 1115136000000000000000000 942826547255 536870912 4050 536870912 (@hp766277 hp766271 hp766272 8409207055123595011 1115136000000000000000000 (hp766279 rfl rfl rfl rfl rfl) (hp766282 (hp766312 rfl) (Enclosure.Real.IsNear.const Bool.true hp766275 hp766276) rfl rfl)) rfl

noncomputable def hp766324 := hp766266 (BSN.cos_quad_nat0 496 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 479461951 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 888912 1000)) rfl rfl (hp766322 rfl) hp766323

noncomputable def hp766325 := nat_lit 57163654909539736925733087548545807096643088674557832178639160458816534930094347880372972750015666615641702400000

noncomputable def hp766326 := nat_lit 4058436031727342884261564375329871037287446255854207296138969750560457085458006565609526071296000000000000

noncomputable def hp766327 := nat_lit 285706145440811190339977096596692123002238623739688450926767004651918553304025545915287750187520801393344512000000

noncomputable def hp766328 := BSN.sin_dyadic_bound_f 631970140 536870912 4 3 536870912 268435456 hp766325 hp642702 hp766326 hp766327 hp642705

noncomputable def hp766329 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 631970140) (BSN.sinEvenQ 536870912) 0 3 hp766325 hp642702 hp766326 rfl rfl rfl

noncomputable def hp766330 := hp766328 hp766326 495806352 rfl rfl rfl rfl rfl rfl rfl rfl (hp766329 rfl)

noncomputable def hp766331 := @BSN.binarySplit_of_base3 (BSN.sinOddP 631970140) (BSN.sinOddQ 536870912) 0 3 hp766327 hp642705 hp766326 rfl rfl rfl

noncomputable def hp766332 := nat_lit 549987677284171160804910461068668198144155059081597540454484000595050496

noncomputable def hp766333 := nat_lit 15527582226028578615335217965829077754141109142443323137249645756416

noncomputable def hp766334 := nat_lit 1649931976688061425257500712770072936276956895026507734717177502493638656

noncomputable def hp766335 := BSN.cos_dyadic_bound_f 250546292 536870912 3 2 536870912 268435456 hp766332 hp708868 hp766333 hp766334 hp708870

noncomputable def hp766336 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 250546292) (BSN.cosEvenQ 536870912) 0 2 hp766332 hp708868 hp766333 rfl rfl rfl

noncomputable def hp766337 := hp766335 hp766333 479461951 rfl rfl rfl rfl rfl rfl rfl rfl (hp766336 rfl)

noncomputable def hp766338 := @BSN.binarySplit_of_base2 (BSN.cosOddP 250546292) (BSN.cosOddQ 536870912) 0 2 hp766334 hp708870 hp766333 rfl rfl rfl

noncomputable def hp766339 := hp766324 hd4911 hd4913 hd4915 hd4917 hd4918 (hp766330 (hp766331 rfl) rfl rfl rfl rfl) (hp766337 (hp766338 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766340 := hp766262 (BSN.cos_quad_nat3 207 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 182985841 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 888912 1000)) rfl rfl (hp766339 rfl rfl rfl rfl rfl) hp766323

noncomputable def hp766341 := nat_lit 7823776911629072219033465439490858949429090276641278068940343804900000000

noncomputable def hp766342 := nat_lit 969622524787124699785408187455863428263687760726129100039062500000000

noncomputable def hp766343 := nat_lit 20489274427321724276526090252077321088668523801495505019157980054500000000

noncomputable def hp766344 := BSN.sin_dyadic_bound_f 420073550 536870912 3 2 536870912 268435456 hp766341 hp708845 hp766342 hp766343 hp708848

noncomputable def hp766345 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 420073550) (BSN.sinEvenQ 536870912) 0 2 hp766341 hp708845 hp766342 rfl rfl rfl

noncomputable def hp766346 := hp766344 hp766342 378503440 rfl rfl rfl rfl rfl rfl rfl rfl (hp766345 rfl)

noncomputable def hp766347 := @BSN.binarySplit_of_base2 (BSN.sinOddP 420073550) (BSN.sinOddQ 536870912) 0 2 hp766343 hp708848 hp766342 rfl rfl rfl

noncomputable def hp766348 := nat_lit 1215728951258188700425418674410000

noncomputable def hp766349 := BSN.sin_dyadic_bound_f 186727890 536870912 2 1 536870912 268435456 hp766348 hp708890 hp766348 hp766348 hp708891

noncomputable def hp766350 := @BSN.binarySplit_of_base (BSN.sinEvenP 186727890) (BSN.sinEvenQ 536870912) 0 1 hp766348 hp708890 hp766348 rfl rfl rfl

noncomputable def hp766351 := hp766349 hp766348 182985841 rfl rfl rfl rfl rfl rfl rfl rfl (hp766350 rfl)

noncomputable def hp766352 := @BSN.binarySplit_of_base (BSN.sinOddP 186727890) (BSN.sinOddQ 536870912) 0 1 hp766348 hp708891 hp766348 rfl rfl rfl

noncomputable def hp766353 := hp766340 hd4920 hd4922 hd4924 hd4926 hd4918 (hp766346 (hp766347 rfl) rfl rfl rfl rfl) (hp766351 (hp766352 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766354 := hp766257 (BSN.cos_quad_nat0 16 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 156140968 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 888912 1000)) rfl rfl (hp766353 rfl rfl rfl rfl rfl) hp766323

noncomputable def hp766355 := nat_lit 2232052820416426223405982489921

noncomputable def hp766356 := BSN.cos_dyadic_bound_f 38652369 536870912 2 1 536870912 268435456 hp766355 hp708767 hp766355 hp766355 hp708768

noncomputable def hp766357 := @BSN.binarySplit_of_base (BSN.cosEvenP 38652369) (BSN.cosEvenQ 536870912) 0 1 hp766355 hp708767 hp766355 rfl rfl rfl

noncomputable def hp766358 := hp766356 hp766355 535480111 rfl rfl rfl rfl rfl rfl rfl rfl (hp766357 rfl)

noncomputable def hp766359 := @BSN.binarySplit_of_base (BSN.cosOddP 38652369) (BSN.cosOddQ 536870912) 0 1 hp766355 hp708768 hp766355 rfl rfl rfl

noncomputable def hp766360 := nat_lit 30355551919731898703301533972698124493041660717150056736920181271376715428559046155724523976839822989950400390625

noncomputable def hp766361 := nat_lit 10651419269168980382979900655774588930080420201270058212133524039007956476289082644619388639926910400390625

noncomputable def hp766362 := nat_lit 183963722746442587486538069367816542983123281130300658600457175799415055162326630298672499000389603842686400390625

noncomputable def hp766363 := BSN.cos_dyadic_bound_f 684884425 536870912 4 3 536870912 268435456 hp766360 hp716712 hp766361 hp766362 hp716714

noncomputable def hp766364 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 684884425) (BSN.cosEvenQ 536870912) 0 3 hp766360 hp716712 hp766361 rfl rfl rfl

noncomputable def hp766365 := hp766363 hp766361 156140968 rfl rfl rfl rfl rfl rfl rfl rfl (hp766364 rfl)

noncomputable def hp766366 := @BSN.binarySplit_of_base3 (BSN.cosOddP 684884425) (BSN.cosOddQ 536870912) 0 3 hp766362 hp716714 hp766361 rfl rfl rfl

noncomputable def hp766367 := hp766354 hd4928 hd4930 hd4932 hd4934 hd4918 (hp766358 (hp766359 rfl) rfl rfl rfl rfl) (hp766365 (hp766366 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766368 := hp766252 (BSN.cos_quad_nat1 125 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 319941891 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 888912 1000)) rfl rfl (hp766367 rfl rfl rfl rfl rfl) hp766323

noncomputable def hp766369 := nat_lit 22443582697917458186965234754299122534669764972625822035884352519967835755799808494839093230306815296389447028736

noncomputable def hp766370 := nat_lit 4310263591705723677238185355156213894912440533318234121963340795263452791762407080633156179621156232237056

noncomputable def hp766371 := nat_lit 136051993144060297941911065214417672354296882522924883721926117037497988949062405100705078004141713582337410600960

noncomputable def hp766372 := BSN.cos_dyadic_bound_f 635148562 536870912 4 3 536870912 268435456 hp766369 hp716712 hp766370 hp766371 hp716714

noncomputable def hp766373 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 635148562) (BSN.cosEvenQ 536870912) 0 3 hp766369 hp716712 hp766370 rfl rfl rfl

noncomputable def hp766374 := hp766372 hp766370 202989332 rfl rfl rfl rfl rfl rfl rfl rfl (hp766373 rfl)

noncomputable def hp766375 := @BSN.binarySplit_of_base3 (BSN.cosOddP 635148562) (BSN.cosOddQ 536870912) 0 3 hp766371 hp716714 hp766370 rfl rfl rfl

noncomputable def hp766376 := nat_lit 3467586165429041911310655975654237683905355970626449189888615700209516800

noncomputable def hp766377 := nat_lit 190495287875657733444750031247258079510334197663986776253094504612096

noncomputable def hp766378 := nat_lit 9081464869467120607578521769520031706671010810558768090165774204684124416

noncomputable def hp766379 := BSN.sin_dyadic_bound_f 342756366 536870912 3 2 536870912 268435456 hp766376 hp708845 hp766377 hp766378 hp708848

noncomputable def hp766380 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 342756366) (BSN.sinEvenQ 536870912) 0 2 hp766376 hp708845 hp766377 rfl rfl rfl

noncomputable def hp766381 := hp766379 hp766377 319941891 rfl rfl rfl rfl rfl rfl rfl rfl (hp766380 rfl)

noncomputable def hp766382 := @BSN.binarySplit_of_base2 (BSN.sinOddP 342756366) (BSN.sinOddQ 536870912) 0 2 hp766378 hp708848 hp766377 rfl rfl rfl

noncomputable def hp766383 := hp766368 hd4936 hd4938 hd4940 hd4942 hd4918 (hp766374 (hp766375 rfl) rfl rfl rfl rfl) (hp766381 (hp766382 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766384 := hp766247 (BSN.cos_quad_nat2 238 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 28836203 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 888912 1000)) rfl rfl (hp766383 rfl rfl rfl rfl rfl) hp766323

noncomputable def hp766385 := nat_lit 401956598701583144912693745936

noncomputable def hp766386 := BSN.sin_dyadic_bound_f 25179366 536870912 2 1 536870912 268435456 hp766385 hp708890 hp766385 hp766385 hp708891

noncomputable def hp766387 := @BSN.binarySplit_of_base (BSN.sinEvenP 25179366) (BSN.sinEvenQ 536870912) 0 1 hp766385 hp708890 hp766385 rfl rfl rfl

noncomputable def hp766388 := hp766386 hp766385 25170136 rfl rfl rfl rfl rfl rfl rfl rfl (hp766387 rfl)

noncomputable def hp766389 := @BSN.binarySplit_of_base (BSN.sinOddP 25179366) (BSN.sinOddQ 536870912) 0 1 hp766385 hp708891 hp766385 rfl rfl rfl

noncomputable def hp766390 := nat_lit 60805328791119437349727625273090178403801599698037668646981856088130529752961705926758305815221383832194624000000

noncomputable def hp766391 := nat_lit 85205502417835946101434837205142484979958485483302753265352627340507435359898594272534683654321000000000000

noncomputable def hp766392 := nat_lit 368112311948459281913990422632306855216676082767452243420505403114779401192917639109581967001930823204890585600000

noncomputable def hp766393 := BSN.cos_dyadic_bound_f 814464770 536870912 4 3 536870912 268435456 hp766390 hp716712 hp766391 hp766392 hp716714

noncomputable def hp766394 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 814464770) (BSN.cosEvenQ 536870912) 0 3 hp766390 hp716712 hp766391 rfl rfl rfl

noncomputable def hp766395 := hp766393 hp766391 28836203 rfl rfl rfl rfl rfl rfl rfl rfl (hp766394 rfl)

noncomputable def hp766396 := @BSN.binarySplit_of_base3 (BSN.cosOddP 814464770) (BSN.cosOddQ 536870912) 0 3 hp766392 hp716714 hp766391 rfl rfl rfl

noncomputable def hp766397 := hp766384 hd4944 hd4946 hd4961 hd4963 hd4918 (hp766388 (hp766389 rfl) rfl rfl rfl rfl) (hp766395 (hp766396 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766398 := @hp766242 13481 16777216 (hp766397 rfl rfl rfl rfl rfl) (hp766397 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp766399 := @hp766240 Bool.true 79437921 33554432 13481 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 888912 1000)) (Enclosure.sfrac Bool.false 888912 1000) 11) hp766398

noncomputable def hp766400 := @Enclosure.Real.IsNear.mulLit_tf hp766231 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1))) 2432317 8388608 1

noncomputable def hp766401 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp766230 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp766402 := @hp766401 1 1 0 1 2432317 8388608 1 33554432 2432317 8388608 1

noncomputable def hp766403 := @Enclosure.Real.IsNear.of_eq (hp766230 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp766404 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 888912 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp766405 := @hp766403 (@Inv.inv Real Real.instInv (Real.sqrt hp766232)) Bool.false 2432317 8388608 1 33554432 (hp766404 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 888912 1000) 888912 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 888912 1000))))

noncomputable def hp766406 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp766232)) Bool.false 19458536 67108864 2 67108864 2432317 8388608

noncomputable def hp766407 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp766232) Bool.false 231445962 67108864 6 67108864 115722981 33554432 3 33554432

noncomputable def hp766408 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 888912 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp766409 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 888912 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp766410 := @hp766409 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 888912 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 593388038799

noncomputable def hp766411 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 888912 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 888912 1000 0

noncomputable def hp766412 := @hp766411 1 10680707 67108864 1 67108864 593388038799 4194304000 55557 4194304000 (Enclosure.Real.IsNear.const Bool.false 888912 1000) hd4949

noncomputable def hp766413 := @hp766410 4194304000 55557 4194304000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 888912 1000) 888912 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 888912 1000))) (hp766412 rfl)

noncomputable def hp766414 := @hp766408 593388038799 4194304000 55557 4194304000 399106970 399107008 33554432 hp766413 rfl rfl rfl

noncomputable def hp766415 := @Enclosure.Real.IsNear.recentre' hp766232 Bool.false 798213978 67108864 38 67108864 399106989 33554432 19 33554432 (hp766414 rfl rfl rfl)

noncomputable def hp766416 := @Enclosure.Real.IsNear.sqrt_image hp766232 399106989 33554432 19 33554432 115722978 115722984 33554432 (hp766415 rfl) rfl rfl

noncomputable def hp766417 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp766232) 115722981 33554432 3 33554432 9729267 9729269 33554432 (hp766407 (hp766416 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp766418 := @hp766402 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp766405 (@hp766406 1 33554432 (hp766417 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp766419 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp766420 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp766421 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1))) (hp766419 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766420 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp766422 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 888912 1000) 888912 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 888912 1000)) rfl

noncomputable def hp766423 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp766424 := @hp766423 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766420 (Enclosure.sfrac Bool.false 1 16)))) 42608243

noncomputable def hp766425 := @hp766424 33554432 199 33554432 18507427 33554432 228745277 22837985280000 788568946920761 1125899906842624 4084402250233853 255438541364920320000

noncomputable def hp766426 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp766427 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1)))) 13212231

noncomputable def hp766428 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp766429 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 377094627) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp766430 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1))) Bool.false 26535675382152082282535

noncomputable def hp766431 := nat_lit 512735433029605656699444677

noncomputable def hp766432 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp766433 := @Enclosure.Real.IsNear.subLit_ff_p hp766232 (Enclosure.sfrac Bool.false 11 1) 399106989 33554432 19 33554432 11 1 0

noncomputable def hp766434 := @hp766432 500000000000000 30008237 33554432 19 33554432 26535675382152082282535 4722366482869645213696 hp766431 hp682805 hd4948 (@hp766433 1 30008237 30008237 33554432 19 33554432 (hp766415 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp766435 := @hp766429 377094627 67108864 15 4194304 Bool.false 52848924 67108864 1 10890000 (@hp766430 4722366482869645213696 hp766431 hp682805 377094627 67108864 15 4194304 (hp766434 rfl) rfl) (Enclosure.sfrac_false_div 377094627 67108864)

noncomputable def hp766436 := nat_lit 8769633408863656564752384

noncomputable def hp766437 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 377094627) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp766436) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp766438 := BSN.sin_reduce_arg_pos_rat_q3 377094627 67108864 226375608064910080 72057594037927936 0 hp766436 hp617687 rfl rfl rfl rfl

noncomputable def hp766439 := nat_lit 260330335389429906674136635846130257170616209798142264920460274270456308989745185384666374400

noncomputable def hp766440 := nat_lit 58185277432114681130173337530013840184595365980867277620898952161871773211717130869678336

noncomputable def hp766441 := nat_lit 681723340332664427043766146574340174943695966497832146818390691452456826387942229224146739456

noncomputable def hp766442 := BSN.sin_dyadic_bound_f 124623986278 137438953472 3 2 67108864 21801270 hp766439 hp738039 hp766440 hp766441 hp738042

noncomputable def hp766443 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 124623986278) (BSN.sinEvenQ 137438953472) 0 2 hp766439 hp738039 hp766440 rfl rfl rfl

noncomputable def hp766444 := hp766442 hp766440 52848924 rfl rfl rfl rfl rfl rfl rfl rfl (hp766443 rfl)

noncomputable def hp766445 := @BSN.binarySplit_of_base2 (BSN.sinOddP 124623986278) (BSN.sinOddQ 137438953472) 0 2 hp766441 hp738042 hp766440 rfl rfl rfl

noncomputable def hp766446 := @BSN.sin_arg_round Bool.false 52848924 67108864 hp766436 hp617687 124623986278 137438953472 21801270 21780000 (hp766444 (hp766445 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766447 := hp766437 52848924 67108864 0 1000000000000000 21780000 10890000 hp766438 BSN.pi_near_15 hp766446 rfl rfl

noncomputable def hp766448 := @hp766427 16777216 10471519 2854748160000 42608044 42608442 33554432 (@hp766428 52848924 67108864 167544304 45675970560000 13212231 16777216 10471519 2854748160000 (hp766435 (hp766447 rfl rfl) rfl rfl) rfl)

noncomputable def hp766449 := @hp766426 Bool.false 85216486 67108864 398 67108864 42608243 33554432 199 33554432 (hp766448 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp766450 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766420 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp766451 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766420 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 66206777)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp766452 := nat_lit 156326332689868572311881799845

noncomputable def hp766453 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766420 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp766452

noncomputable def hp766454 := nat_lit 47977128726254650595543555616231393

noncomputable def hp766455 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766420 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp766456 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp766457 := @hp766456 (Enclosure.sfrac Bool.false 1 16) 106415060008215 1125899906842624 1777847575 1125899906842624 1 16 0

noncomputable def hp766458 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1)) 900494287848169

noncomputable def hp766459 := @hp766458 1125899906842624 1140313367 1125899906842624 30008237 33554432 19 33554432 3570696894821569658880 106415060008215 1125899906842624 1777847575

noncomputable def hp766460 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1)) 30008237 33554432 19

noncomputable def hp766461 := @hp766460 33554432 30008237 33554432 19 33554432 900494287848169 1125899906842624 1140313367 1125899906842624 (@hp766433 1 30008237 30008237 33554432 19 33554432 (hp766415 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp766462 := hp766461 (@hp766433 1 30008237 30008237 33554432 19 33554432 (hp766415 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp766463 := @hp766459 1125899906842624 (hp766462 rfl) (@hp766433 1 30008237 30008237 33554432 19 33554432 (hp766415 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp766464 := @hp766455 500000000000000 176783804185879 1125899906842624 1777847575 1125899906842624 hp766452 hp682141 hp766454 hp682143 hd4948 (@hp766457 1 2828540866974064 176783804185879 1125899906842624 1777847575 1125899906842624 (hp766463 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp766465 := @hp766451 66206777 67108864 333 33554432 Bool.false 18507427 33554432 1 10890000 (@hp766453 hp682141 hp766454 hp682143 66206777 67108864 333 33554432 (hp766464 rfl) rfl) (Enclosure.sfrac_true_div 66206777 67108864)

noncomputable def hp766466 := nat_lit 655063550582509328709492519404038496739540746237610312278688442561

noncomputable def hp766467 := nat_lit 369164195198878891903845167830196453804845695751424088865548481

noncomputable def hp766468 := nat_lit 1964452323357130228344669867876455097311012547321328088658334230721

noncomputable def hp766469 := BSN.cos_dyadic_bound_f 66206777 67108864 3 2 33554432 10890000 hp766466 hp738066 hp766467 hp766468 hp738069

noncomputable def hp766470 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 66206777) (BSN.cosEvenQ 67108864) 0 2 hp766466 hp738066 hp766467 rfl rfl rfl

noncomputable def hp766471 := hp766469 hp766467 18507427 rfl rfl rfl rfl rfl rfl rfl rfl (hp766470 rfl)

noncomputable def hp766472 := @BSN.binarySplit_of_base2 (BSN.cosOddP 66206777) (BSN.cosOddQ 67108864) 0 2 hp766468 hp738069 hp766467 rfl rfl rfl

noncomputable def hp766473 := hp766465 (BSN.cos_neg_of_bound 66206777 67108864 Bool.false 18507427 33554432 1 10890000 (hp766471 (hp766472 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp766474 := hp766425 hp766449 (@hp766450 18507427 33554432 3659924432 365407764480000 18507427 33554432 228745277 22837985280000 (hp766473 rfl) rfl)

noncomputable def hp766475 := @hp766400 33554432 788568946920761 1125899906842624 4084402250233853 255438541364920320000 1918049655267464633237 9444732965739290427392 907208063103707190803 hp766228 (hp766418 rfl) (@hp766421 Bool.false 788568946920761 1125899906842624 4084402250233853 255438541364920320000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766232 (Enclosure.sfrac Bool.false 11 1)) (hp766422 rfl (hp766235 rfl rfl))) (hp766474 rfl))

noncomputable def hp766476 := @hp766229 157432979705853290550803 hp766228 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 888912 1000))) (@hp766234 157432979705853290550803 hp766228 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 888912 1000) 11 (hp766235 rfl rfl)) (@hp766238 157432979705853290550803 hp766228 hp766399 (hp766475 rfl) rfl rfl))

theorem hd5074 : hp766227 hp766228 := hp766476

noncomputable def hp766477 := nat_lit 2312081263389472845244747

noncomputable def hp766478 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 890180 1000)) Bool.false 13887692940129180196765 9444732965739290427392 hp766477

noncomputable def hp766479 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 890180 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 890180 1000)) Bool.false 13887692940129180196765 9444732965739290427392

noncomputable def hp766480 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 890180 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp766481 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp766480 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp766482 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 890180 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp766483 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 890180 1000)) (Enclosure.sfrac Bool.false 890180 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp766481 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp766484 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 890180 1000)) hp766483 Bool.false 13887692940129180196765 9444732965739290427392

noncomputable def hp766485 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 890180 1000) 890180 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 890180 1000)) rfl

noncomputable def hp766486 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 890180 1000)) (Enclosure.sfrac Bool.false 890180 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp766481 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp766487 := nat_lit 1863974593585778592512391249920

noncomputable def hp766488 := @hp766486 169504817 134217728 215991 268435456 1959851835774428389277 9444732965739290427392 13230180558201810364747 hp743845 hp766487 13887692940129180196765 9444732965739290427392

noncomputable def hp766489 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 890180 1000)) (Enclosure.sfrac Bool.false 890180 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 890180 1000)) (Enclosure.sfrac Bool.false 890180 1000) 11)

noncomputable def hp766490 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 890180 1000)) (Enclosure.sfrac Bool.false 890180 1000) 11) hp766489

noncomputable def hp766491 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 890180 1000)) (Enclosure.sfrac Bool.false 890180 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 890180 1000)) (Enclosure.sfrac Bool.false 890180 1000) 11)

noncomputable def hp766492 := @hp766491 339009634 536870912 215991 536870912 339009634 536870912 215991 536870912 364008822764732416 169504817 134217728

noncomputable def hp766493 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 890180 1000)) (Enclosure.sfrac Bool.false 890180 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp766494 := hp766493 BSN.quadSignNeg 9 10 11 890180 1000 184 238 536870912 268435456 9007199254740992

noncomputable def hp766495 := hp766494 Bool.false 944512374088 4056 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp766496 := hp766495 Bool.false 334416853 185421 Bool.true 750157522 Bool.true 761010696 28296951008113761 1 Bool.false 92690560

noncomputable def hp766497 := hp766496 Bool.false Bool.false 81982154 Bool.true Bool.false 339009634 215991 BSN.abs_quadSignPos (BSN.cos_quad_nat0 184 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 92690560 536870912) BSN.abs_quadSignNeg

noncomputable def hp766498 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 890180 1000)) (Enclosure.sfrac Bool.false 890180 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp766499 := hp766498 BSN.quadSignNeg 7 8 9 890180 1000 58 125 536870912 268435456 9007199254740992

noncomputable def hp766500 := hp766499 Bool.false 944512374088 4056 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp766501 := hp766500 Bool.false 532261725 151431 Bool.true 364906374 Bool.true 152695236 28296951008113761 1 Bool.false 417560437

noncomputable def hp766502 := hp766501 Bool.true Bool.false 150644882 Bool.true Bool.false 334416853 185421 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 58 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 417560437 536870912) BSN.abs_quadSignNeg

noncomputable def hp766503 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 890180 1000)) (Enclosure.sfrac Bool.false 890180 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp766504 := hp766503 BSN.quadSignNeg 5 6 7 890180 1000 104 17 536870912 268435456 9007199254740992

noncomputable def hp766505 := hp766504 Bool.false 944512374088 4056 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp766506 := hp766505 Bool.false 477829969 112529 Bool.false 504734802 Bool.false 202713579 28296951008113761 1 Bool.false 316578540

noncomputable def hp766507 := hp766506 Bool.false Bool.false 197931010 Bool.true Bool.false 532261725 151431 BSN.abs_quadSignPos (BSN.cos_quad_nat0 104 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 316578540 536870912) BSN.abs_quadSignNeg

noncomputable def hp766508 := hp766498 BSN.quadSignPos 3 4 5 890180 1000 334 207 536870912 268435456 9007199254740992

noncomputable def hp766509 := hp766508 Bool.false 944512374088 4056 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp766510 := hp766509 Bool.false 462033003 66507 Bool.false 318862447 Bool.false 776926156 28296951008113761 1 Bool.false 444931294

noncomputable def hp766511 := hp766510 Bool.true Bool.false 532771373 Bool.false Bool.false 477829969 112529 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 334 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 444931294 536870912) BSN.abs_quadSignPos

noncomputable def hp766512 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 890180 1000)) (Enclosure.sfrac Bool.false 890180 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp766513 := hp766512 BSN.quadSignNeg 1 2 3 890180 1000 727 497 536870912 268435456 9007199254740992

noncomputable def hp766514 := hp766513 Bool.false 944512374088 4056 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp766515 := hp766514 Bool.false 536870840 4106 Bool.false 159305730 Bool.false 345175415 28296951008113761 1 Bool.false 156978222

noncomputable def hp766516 := hp766515 Bool.false Bool.false 321881206 Bool.true Bool.false 462033003 66507 BSN.abs_quadSignPos (BSN.cos_quad_nat3 727 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 156978222 536870912) BSN.abs_quadSignNeg

noncomputable def hp766517 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 890180 1000)) (Enclosure.sfrac Bool.false 890180 1000) 1) Bool.false

noncomputable def hp766518 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 890180 1000)) (Enclosure.sfrac Bool.false 890180 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 890180 1000)))

noncomputable def hp766519 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 890180 1000))) Bool.false 67108855 67108864

noncomputable def hp766520 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 890180 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 118064046761) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 118064046761 67108864

noncomputable def hp766521 := nat_lit 13860136361713370400876032893704213556123158332063

noncomputable def hp766522 := nat_lit 7878249404763804204723243068108235442067865600

noncomputable def hp766523 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 890180 1000)) Bool.false hp766521 hp766522 6736932767724809707

noncomputable def hp766524 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 890180 4000) (Real.log (Enclosure.sfrac Bool.false 3169682729600 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1780360))))))

noncomputable def hp766525 := nat_lit 268306224132692265902987264000000000

noncomputable def hp766526 := nat_lit 1433045218575681102215320255365120000000

noncomputable def hp766527 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 890180 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp766524 (Enclosure.sfrac Bool.false 890180 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 890180 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp766525 hp766526)) Bool.false

noncomputable def hp766528 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 890180 1000) 890180 1000 3169682729600 16000000 1780360

noncomputable def hp766529 := hp766528 4000 2000 hp766525 hp766526 (@Eq.refl Real (Enclosure.sfrac Bool.false 890180 1000)) rfl rfl rfl rfl

noncomputable def hp766530 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp766524 (Enclosure.sfrac Bool.false 890180 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 890180 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp766525 hp766526) 1584628980116131864891 900719925474099200

noncomputable def hp766531 := nat_lit 2270844741503118606479529229304498349035218261125201920000000

noncomputable def hp766532 := @hp766530 6736932767724809707 892108800000000000000000 hp766525 hp766526 0 1 hp766531 hp766521 hp766522 6736932767724809707 892108800000000000000000

noncomputable def hp766533 := @Enclosure.Real.IsNear.subLit_ff_p (hp766524 (Enclosure.sfrac Bool.false 890180 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 890180 2000) (Real.log Real.pi)) 408710565766130131007 180143985094819840 280681662011171 108900000000000000000

noncomputable def hp766534 := nat_lit 1063426507170721975270364938240

noncomputable def hp766535 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 890180 4000) (Real.log (Enclosure.sfrac Bool.false 3169682729600 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1780360))))))

noncomputable def hp766536 := @hp766535 (Enclosure.sfrac Bool.false 890180 2000) 2444454260459917467963 900719925474099200 280681662011171 108900000000000000000 890180 2000 0

noncomputable def hp766537 := nat_lit 4087105657661301310070000

noncomputable def hp766538 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 890180 4000) (Real.log (Enclosure.sfrac Bool.false 3169682729600 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1780360))))) 2444807845874153795563

noncomputable def hp766539 := nat_lit 5504421648265752841426154416005709824

noncomputable def hp766540 := @hp766538 900719925474099200 556363323995117 217800000000000000000 883963535590819 2251799813685248 200000001089 8712000000000000000 hp766539 2444454260459917467963 900719925474099200 280681662011171

noncomputable def hp766541 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 890180 4000) (Real.log (Enclosure.sfrac Bool.false 3169682729600 16000000)) 890180 4000 0 1 54928393041276007 4503599627370496

noncomputable def hp766542 := nat_lit 117957825867057214087233536

noncomputable def hp766543 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3169682729600) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp766542 hp617687

noncomputable def hp766544 := BSN.log_rat_reduce_isNear 3169682729600 16000000 17 6339365459200 4194304000000 110877604 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp766545 := nat_lit 170734544458533049761798602314648985952236962410676335633360802349471889485355639152718755473377341915636170752000000000000000000000

noncomputable def hp766546 := nat_lit 2420562921454740588656918766750685314105714508578730467829643352758145468322783761140274281155801467375216230400000000000000000000

noncomputable def hp766547 := nat_lit 1903396431181788198587898020374237714161683001716552383199179430529660318226765232487990887817708306432000000000000000000000

noncomputable def hp766548 := BSN.log_dyadic_bound 1072530729600 5266834729600 6 5 hp766545 268435456 87120000 hp766546 hp766547 110877604 6339365459200

noncomputable def hp766549 := hp766548 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp766550 := @BSN.binarySplit_of_base5 (BSN.artanhP 1072530729600) (BSN.artanhQ 5266834729600) 0 5 hp766546 hp766545 hp766547 rfl rfl rfl

noncomputable def hp766551 := hp766544 rfl rfl rfl rfl (hp766549 (hp766550 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp766552 := @hp766541 12500018513 1089000000000000000 2444807845874153795563 900719925474099200 556363323995117 217800000000000000000 (Enclosure.Real.IsNear.const Bool.false 890180 4000) (BSN.isNear_log_sfrac 3169682729600 16000000 54928393041276007 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp766543 1000001481040000 87120000000000000000000 54928393041276007 4503599627370496 12500018513 1089000000000000000 (hp766551 rfl rfl rfl) rfl)) rfl

noncomputable def hp766553 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1780360)))) 1 4

noncomputable def hp766554 := @hp766553 0 1 883963535590819 562949953421312 200000001089 2178000000000000000 883963535590819 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp766555 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1780360))) 884279719003555 562949953421312 1

noncomputable def hp766556 := @hp766555 2000000000000000 18846 33554432 1 10890000 29660894345461715959808 883963535590819 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp766557 := BSN.arctan_dyadic_bound_f 1000 1780360 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp766558 := hp766557 1 18846 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1780360) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1780360) 0 0 rfl)

noncomputable def hp766559 := hp766554 (hp766556 (hp766558 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp766560 := @hp766533 1709624561349 3355443200 133527 26843545600 hp766534 1584628980116131864891 900719925474099200 6736932767724809707 892108800000000000000000 (@hp766536 1 hp766537 408710565766130131007 180143985094819840 280681662011171 108900000000000000000 (@hp766540 108900000000000000000 hp766552 hp766559 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 890180 2000) rfl rfl)

noncomputable def hp766561 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 890180 2000) (Real.log Real.pi) 890180 2000 0 1 38410761 33554432

noncomputable def hp766562 := hp766560 (@hp766561 3 268435456 1709624561349 3355443200 133527 26843545600 (Enclosure.Real.IsNear.const Bool.false 890180 2000) hd4909 rfl) rfl

noncomputable def hp766563 := @hp766523 892108800000000000000000 118064046761 67108864 507 67108864 (@hp766527 hp766521 hp766522 6736932767724809707 892108800000000000000000 (hp766529 rfl rfl rfl rfl rfl) (hp766532 (hp766562 rfl) (Enclosure.Real.IsNear.const Bool.true hp766525 hp766526) rfl rfl)) rfl

noncomputable def hp766564 := nat_lit 15187031961906461972365312

noncomputable def hp766565 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 118064046761) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp766564) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp766566 := BSN.sin_reduce_arg_pos_rat_q3 118064046761 67108864 226375608064910080 72057594037927936 279 hp766564 hp617687 rfl rfl rfl rfl

noncomputable def hp766567 := nat_lit 14362263439057002423069524511910959337041552774269584431139625467812810363502925644176813064781304846604226814810172664703300255282442445040625

noncomputable def hp766568 := nat_lit 10212152151875499522762797951269685377270798431755865521672235068718057593985339781423964946576409607635584531210729825923315976806640625

noncomputable def hp766569 := nat_lit 71722194804923873243601512998503408840880856010410977078422714663139262582693388733310731582747549696270480840000526615737169126745360998640625

noncomputable def hp766570 := BSN.sin_dyadic_bound_f 215820704765 137438953472 4 3 67108864 21801270 hp766567 hp737934 hp766568 hp766569 hp737937

noncomputable def hp766571 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215820704765) (BSN.sinEvenQ 137438953472) 0 3 hp766567 hp737934 hp766568 rfl rfl rfl

noncomputable def hp766572 := hp766570 hp766568 67108855 rfl rfl rfl rfl rfl rfl rfl rfl (hp766571 rfl)

noncomputable def hp766573 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215820704765) (BSN.sinOddQ 137438953472) 0 3 hp766569 hp737937 hp766568 rfl rfl rfl

noncomputable def hp766574 := @BSN.sin_arg_round Bool.false 67108855 67108864 hp766564 hp617687 215820704765 137438953472 21801270 21780000 (hp766572 (hp766573 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766575 := hp766565 67108855 67108864 279 1000000000000000 21780000 10890000 hp766566 BSN.pi_near_15 hp766574 rfl rfl

noncomputable def hp766576 := @hp766520 507 67108864 Bool.false 67108855 67108864 1 10890000 hp766563 (Enclosure.sfrac_false_div 118064046761 67108864) (hp766575 rfl rfl) rfl

noncomputable def hp766577 := @hp766517 67108855 67108864 349271179 45675970560000 536870840 536870912 4106 536870912 (@hp766518 Bool.false 67108855 67108864 349271179 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 890180 1000)) (Enclosure.sfrac Bool.false 890180 1000)) (@hp766519 5588338864 730815528960000 67108855 67108864 349271179 45675970560000 (hp766576 rfl) rfl))

noncomputable def hp766578 := @hp766523 892108800000000000000000 944512374088 536870912 4056 536870912 (@hp766527 hp766521 hp766522 6736932767724809707 892108800000000000000000 (hp766529 rfl rfl rfl rfl rfl) (hp766532 (hp766562 rfl) (Enclosure.Real.IsNear.const Bool.true hp766525 hp766526) rfl rfl)) rfl

noncomputable def hp766579 := hp766516 (BSN.cos_quad_nat1 497 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 321881206 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 890180 1000)) rfl rfl (hp766577 rfl) hp766578

noncomputable def hp766580 := nat_lit 644058903243044870243831722410000

noncomputable def hp766581 := BSN.sin_dyadic_bound_f 159305730 536870912 2 1 536870912 268435456 hp766580 hp708890 hp766580 hp766580 hp708891

noncomputable def hp766582 := @BSN.binarySplit_of_base (BSN.sinEvenP 159305730) (BSN.sinEvenQ 536870912) 0 1 hp766580 hp708890 hp766580 rfl rfl rfl

noncomputable def hp766583 := hp766581 hp766580 156978222 rfl rfl rfl rfl rfl rfl rfl rfl (hp766582 rfl)

noncomputable def hp766584 := @BSN.binarySplit_of_base (BSN.sinOddP 159305730) (BSN.sinOddQ 536870912) 0 1 hp766580 hp708891 hp766580 rfl rfl rfl

noncomputable def hp766585 := nat_lit 3566524783809541339105121111084229091277267773359154950308412985133730625

noncomputable def hp766586 := nat_lit 201520320575111656350127869754711704219576626179909359426444937890625

noncomputable def hp766587 := nat_lit 9340571972315486659736464607717187610586012472831590730892486431165090625

noncomputable def hp766588 := BSN.sin_dyadic_bound_f 345175415 536870912 3 2 536870912 268435456 hp766585 hp708845 hp766586 hp766587 hp708848

noncomputable def hp766589 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 345175415) (BSN.sinEvenQ 536870912) 0 2 hp766585 hp708845 hp766586 rfl rfl rfl

noncomputable def hp766590 := hp766588 hp766586 321881206 rfl rfl rfl rfl rfl rfl rfl rfl (hp766589 rfl)

noncomputable def hp766591 := @BSN.binarySplit_of_base2 (BSN.sinOddP 345175415) (BSN.sinOddQ 536870912) 0 2 hp766587 hp708848 hp766586 rfl rfl rfl

noncomputable def hp766592 := hp766579 hd4911 hd4913 hd4915 hd4917 hd4918 (hp766583 (hp766584 rfl) rfl rfl rfl rfl) (hp766590 (hp766591 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766593 := hp766511 (BSN.cos_quad_nat3 207 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 532771373 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 890180 1000)) rfl rfl (hp766592 rfl rfl rfl rfl rfl) hp766578

noncomputable def hp766594 := nat_lit 1442894051258197355980353640790368614288661703708891846376427518220122241

noncomputable def hp766595 := nat_lit 106862910146341201949674850372558933294350869069206931532613862111361

noncomputable def hp766596 := nat_lit 4328468427954299385537161572670360724999396409388537125266217326936144001

noncomputable def hp766597 := BSN.cos_dyadic_bound_f 318862447 536870912 3 2 536870912 268435456 hp766594 hp708868 hp766595 hp766596 hp708870

noncomputable def hp766598 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 318862447) (BSN.cosEvenQ 536870912) 0 2 hp766594 hp708868 hp766595 rfl rfl rfl

noncomputable def hp766599 := hp766597 hp766595 444931294 rfl rfl rfl rfl rfl rfl rfl rfl (hp766598 rfl)

noncomputable def hp766600 := @BSN.binarySplit_of_base2 (BSN.cosOddP 318862447) (BSN.cosOddQ 536870912) 0 2 hp766596 hp708870 hp766595 rfl rfl rfl

noncomputable def hp766601 := nat_lit 130679238931058085419085321304870715962712096328631299018646759497983380053913647175680721649159187728059372404736

noncomputable def hp766602 := nat_lit 48367864352072359211127993634279842590493650865133153098613554473942987499696515702582860686902662461915136

noncomputable def hp766603 := nat_lit 652811048209411289214184145989581645964660442796739836707729309353402101071500498034810693239550332890227037700096

noncomputable def hp766604 := BSN.sin_dyadic_bound_f 776926156 536870912 4 3 536870912 268435456 hp766601 hp642702 hp766602 hp766603 hp642705

noncomputable def hp766605 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 776926156) (BSN.sinEvenQ 536870912) 0 3 hp766601 hp642702 hp766602 rfl rfl rfl

noncomputable def hp766606 := hp766604 hp766602 532771373 rfl rfl rfl rfl rfl rfl rfl rfl (hp766605 rfl)

noncomputable def hp766607 := @BSN.binarySplit_of_base3 (BSN.sinOddP 776926156) (BSN.sinOddQ 536870912) 0 3 hp766603 hp642705 hp766602 rfl rfl rfl

noncomputable def hp766608 := hp766593 hd4920 hd4922 hd4924 hd4926 hd4918 (hp766599 (hp766600 rfl) rfl rfl rfl rfl) (hp766606 (hp766607 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766609 := hp766507 (BSN.cos_quad_nat1 17 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 197931010 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 890180 1000)) rfl rfl (hp766608 rfl rfl rfl rfl rfl) hp766578

noncomputable def hp766610 := nat_lit 8944161619649248720659356311173342073151633733992172907316308497277553458371769234135557066352246372587027173376

noncomputable def hp766611 := nat_lit 273375134662429308779544023580650680264973941565709670678460008816982056547880003695946680822868249808896

noncomputable def hp766612 := nat_lit 54244432169950511680343970395626474596212695558974482960892406105193064458911719201767109767244341572544001085440

noncomputable def hp766613 := BSN.cos_dyadic_bound_f 504734802 536870912 4 3 536870912 268435456 hp766610 hp716712 hp766611 hp766612 hp716714

noncomputable def hp766614 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 504734802) (BSN.cosEvenQ 536870912) 0 3 hp766610 hp716712 hp766611 rfl rfl rfl

noncomputable def hp766615 := hp766613 hp766611 316578540 rfl rfl rfl rfl rfl rfl rfl rfl (hp766614 rfl)

noncomputable def hp766616 := @BSN.binarySplit_of_base3 (BSN.cosOddP 504734802) (BSN.cosOddQ 536870912) 0 3 hp766612 hp716714 hp766611 rfl rfl rfl

noncomputable def hp766617 := nat_lit 1688617810033741267555801617756081

noncomputable def hp766618 := BSN.sin_dyadic_bound_f 202713579 536870912 2 1 536870912 268435456 hp766617 hp708890 hp766617 hp766617 hp708891

noncomputable def hp766619 := @BSN.binarySplit_of_base (BSN.sinEvenP 202713579) (BSN.sinEvenQ 536870912) 0 1 hp766617 hp708890 hp766617 rfl rfl rfl

noncomputable def hp766620 := hp766618 hp766617 197931010 rfl rfl rfl rfl rfl rfl rfl rfl (hp766619 rfl)

noncomputable def hp766621 := @BSN.binarySplit_of_base (BSN.sinOddP 202713579) (BSN.sinOddQ 536870912) 0 1 hp766617 hp708891 hp766617 rfl rfl rfl

noncomputable def hp766622 := hp766609 hd4928 hd4930 hd4932 hd4934 hd4918 (hp766615 (hp766616 rfl) rfl rfl rfl rfl) (hp766620 (hp766621 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766623 := hp766502 (BSN.cos_quad_nat1 125 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 150644882 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 890180 1000)) rfl rfl (hp766622 rfl rfl rfl rfl rfl) hp766578

noncomputable def hp766624 := nat_lit 2474968896599279910867164034932419592272606198701285349922562315787673856

noncomputable def hp766625 := nat_lit 314377601139163079534281491472861042571098980911989796386235641733376

noncomputable def hp766626 := nat_lit 7424277934595561406442423541814313054732676398142032070174914476079554816

noncomputable def hp766627 := BSN.cos_dyadic_bound_f 364906374 536870912 3 2 536870912 268435456 hp766624 hp708868 hp766625 hp766626 hp708870

noncomputable def hp766628 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 364906374) (BSN.cosEvenQ 536870912) 0 2 hp766624 hp708868 hp766625 rfl rfl rfl

noncomputable def hp766629 := hp766627 hp766625 417560437 rfl rfl rfl rfl rfl rfl rfl rfl (hp766628 rfl)

noncomputable def hp766630 := @BSN.binarySplit_of_base2 (BSN.cosOddP 364906374) (BSN.cosOddQ 536870912) 0 2 hp766626 hp708870 hp766625 rfl rfl rfl

noncomputable def hp766631 := nat_lit 543628166274959463719894181724416

noncomputable def hp766632 := BSN.sin_dyadic_bound_f 152695236 536870912 2 1 536870912 268435456 hp766631 hp708890 hp766631 hp766631 hp708891

noncomputable def hp766633 := @BSN.binarySplit_of_base (BSN.sinEvenP 152695236) (BSN.sinEvenQ 536870912) 0 1 hp766631 hp708890 hp766631 rfl rfl rfl

noncomputable def hp766634 := hp766632 hp766631 150644882 rfl rfl rfl rfl rfl rfl rfl rfl (hp766633 rfl)

noncomputable def hp766635 := @BSN.binarySplit_of_base (BSN.sinOddP 152695236) (BSN.sinOddQ 536870912) 0 1 hp766631 hp708891 hp766631 rfl rfl rfl

noncomputable def hp766636 := hp766623 hd4936 hd4938 hd4940 hd4942 hd4918 (hp766629 (hp766630 rfl) rfl rfl rfl rfl) (hp766634 (hp766635 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766637 := hp766497 (BSN.cos_quad_nat2 238 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 81982154 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 890180 1000)) rfl rfl (hp766636 rfl rfl rfl rfl rfl) hp766578

noncomputable def hp766638 := nat_lit 43719901318950246598670597225119537494055588852632558140368974268731548702097687761509058065635322817483489284096

noncomputable def hp766639 := nat_lit 31756279868799237571523076226442204295279497401803874321200248645390837118961488017475629908540887640969216

noncomputable def hp766640 := nat_lit 264833617270629520600722767385761709937400213559531578112948980573206884143174021013445370258913133893349008609280

noncomputable def hp766641 := BSN.cos_dyadic_bound_f 750157522 536870912 4 3 536870912 268435456 hp766638 hp716712 hp766639 hp766640 hp716714

noncomputable def hp766642 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 750157522) (BSN.cosEvenQ 536870912) 0 3 hp766638 hp716712 hp766639 rfl rfl rfl

noncomputable def hp766643 := hp766641 hp766639 92690560 rfl rfl rfl rfl rfl rfl rfl rfl (hp766642 rfl)

noncomputable def hp766644 := @BSN.binarySplit_of_base3 (BSN.cosOddP 750157522) (BSN.cosOddQ 536870912) 0 3 hp766640 hp716714 hp766639 rfl rfl rfl

noncomputable def hp766645 := nat_lit 46311678365007622729484569542423006923893334809116003713783551041374805646404031046977228889394673878358604906496

noncomputable def hp766646 := nat_lit 37730201956466041746305942752149827610597581977108836817134843927418481155737414816513389398950230271983616

noncomputable def hp766647 := nat_lit 280508288519034211280834913412337102680755865245623195458566977816429598385316489140437389552791123781692245934080

noncomputable def hp766648 := BSN.cos_dyadic_bound_f 761010696 536870912 4 3 536870912 268435456 hp766645 hp716712 hp766646 hp766647 hp716714

noncomputable def hp766649 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 761010696) (BSN.cosEvenQ 536870912) 0 3 hp766645 hp716712 hp766646 rfl rfl rfl

noncomputable def hp766650 := hp766648 hp766646 81982154 rfl rfl rfl rfl rfl rfl rfl rfl (hp766649 rfl)

noncomputable def hp766651 := @BSN.binarySplit_of_base3 (BSN.cosOddP 761010696) (BSN.cosOddQ 536870912) 0 3 hp766647 hp716714 hp766646 rfl rfl rfl

noncomputable def hp766652 := hp766637 hd4944 hd4946 hd4961 hd4963 hd4918 (hp766643 (hp766644 rfl) rfl rfl rfl rfl) (hp766650 (hp766651 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766653 := @hp766492 215991 268435456 (hp766652 rfl rfl rfl rfl rfl) (hp766652 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp766654 := @hp766490 Bool.false 169504817 134217728 215991 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 890180 1000)) (Enclosure.sfrac Bool.false 890180 1000) 11) hp766653

noncomputable def hp766655 := @Enclosure.Real.IsNear.mulLit_tf hp766481 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1))) 19451603 67108864 1

noncomputable def hp766656 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp766480 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp766657 := @hp766656 1 1 0 1 19451603 67108864 1 67108864 19451603 67108864 1

noncomputable def hp766658 := @Enclosure.Real.IsNear.of_eq (hp766480 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp766659 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 890180 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp766660 := @hp766658 (@Inv.inv Real Real.instInv (Real.sqrt hp766482)) Bool.false 19451603 67108864 1 67108864 (hp766659 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 890180 1000) 890180 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 890180 1000))))

noncomputable def hp766661 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp766482)) Bool.false 19451603 67108864 1 67108864 19451603 67108864

noncomputable def hp766662 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp766482) Bool.false 231528455 67108864 7 67108864 231528455 67108864 7 67108864

noncomputable def hp766663 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 890180 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp766664 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 890180 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp766665 := @hp766664 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 890180 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 475387587863

noncomputable def hp766666 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 890180 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 890180 1000 0

noncomputable def hp766667 := @hp766666 1 10680707 67108864 1 67108864 475387587863 3355443200 44509 3355443200 (Enclosure.Real.IsNear.const Bool.false 890180 1000) hd4949

noncomputable def hp766668 := @hp766665 3355443200 44509 3355443200 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 890180 1000) 890180 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 890180 1000))) (hp766667 rfl)

noncomputable def hp766669 := @hp766663 475387587863 3355443200 44509 3355443200 399391524 399391563 33554432 hp766668 rfl rfl rfl

noncomputable def hp766670 := @Enclosure.Real.IsNear.recentre' hp766482 Bool.false 798783087 67108864 39 67108864 798783087 67108864 39 67108864 (hp766669 rfl rfl rfl)

noncomputable def hp766671 := @Enclosure.Real.IsNear.sqrt_image hp766482 798783087 67108864 39 67108864 115764224 115764231 33554432 (hp766670 rfl) rfl rfl

noncomputable def hp766672 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp766482) 231528455 67108864 7 67108864 9725801 9725802 33554432 (hp766662 (hp766671 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp766673 := @hp766657 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp766660 (@hp766661 1 67108864 (hp766672 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp766674 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp766675 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp766676 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1))) (hp766674 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766675 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp766677 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 890180 1000) 890180 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 890180 1000)) rfl

noncomputable def hp766678 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp766679 := @hp766678 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766675 (Enclosure.sfrac Bool.false 1 16)))) 81918397

noncomputable def hp766680 := @hp766679 67108864 377 67108864 1229947 2097152 473144929 45675970560000 100755286634959 140737488355328 2714367840100947 170292360909946880000

noncomputable def hp766681 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp766682 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1)))) 54976657

noncomputable def hp766683 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp766684 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 95167611) (@Nat.cast Real Real.instNatCast 16777216)) Bool.false

noncomputable def hp766685 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1))) Bool.false 53574602310906558747565

noncomputable def hp766686 := nat_lit 1052456941473143967939776849

noncomputable def hp766687 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp766688 := @Enclosure.Real.IsNear.subLit_ff_p hp766482 (Enclosure.sfrac Bool.false 11 1) 798783087 67108864 39 67108864 11 1 0

noncomputable def hp766689 := @hp766687 500000000000000 60585583 67108864 39 67108864 53574602310906558747565 9444732965739290427392 hp766686 hp738031 hd4948 (@hp766688 1 60585583 60585583 67108864 39 67108864 (hp766670 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp766690 := @hp766684 95167611 16777216 123 33554432 Bool.false 54976657 67108864 1 10890000 (@hp766685 9444732965739290427392 hp766686 hp738031 95167611 16777216 123 33554432 (hp766689 rfl) rfl) (Enclosure.sfrac_false_div 95167611 16777216)

noncomputable def hp766691 := nat_lit 2321240737085874820349952

noncomputable def hp766692 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 95167611) (@Nat.cast Real Real.instNatCast 16777216)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp766691) (@Nat.cast Real Real.instNatCast hp619230)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp766693 := BSN.sin_reduce_arg_pos_rat_q3 95167611 16777216 226375608064910080 72057594037927936 0 hp766691 hp619230 rfl rfl rfl rfl

noncomputable def hp766694 := nat_lit 327148269402119444633361767070758496091750439271406925156009331530089441857830515116384067840

noncomputable def hp766695 := nat_lit 91876193943188743445283887522878732175460997098590844626651026286886263963397179430543616

noncomputable def hp766696 := nat_lit 856668144120119097026559882700759019435824213620287085469676528536245960438377277490499297536

noncomputable def hp766697 := BSN.sin_dyadic_bound_f 131947259494 137438953472 3 2 67108864 21801270 hp766694 hp738039 hp766695 hp766696 hp738042

noncomputable def hp766698 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 131947259494) (BSN.sinEvenQ 137438953472) 0 2 hp766694 hp738039 hp766695 rfl rfl rfl

noncomputable def hp766699 := hp766697 hp766695 54976657 rfl rfl rfl rfl rfl rfl rfl rfl (hp766698 rfl)

noncomputable def hp766700 := @BSN.binarySplit_of_base2 (BSN.sinOddP 131947259494) (BSN.sinOddQ 137438953472) 0 2 hp766696 hp738042 hp766695 rfl rfl rfl

noncomputable def hp766701 := @BSN.sin_arg_round Bool.false 54976657 67108864 hp766691 hp619230 131947259494 137438953472 21801270 21780000 (hp766699 (hp766700 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766702 := hp766692 54976657 67108864 0 1000000000000000 21780000 10890000 hp766693 BSN.pi_near_15 hp766701 rfl rfl

noncomputable def hp766703 := @hp766682 67108864 85814027 22837985280000 40959010 40959387 33554432 (@hp766683 54976657 67108864 1373024432 365407764480000 54976657 67108864 85814027 22837985280000 (hp766690 (hp766702 rfl rfl) rfl rfl) rfl)

noncomputable def hp766704 := @hp766681 Bool.false 81918397 67108864 377 67108864 81918397 67108864 377 67108864 (hp766703 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp766705 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766675 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp766706 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766675 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 31678227)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp766707 := nat_lit 598384798649523922981244942845

noncomputable def hp766708 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766675 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp766707

noncomputable def hp766709 := nat_lit 39631333093583873188279656388291153

noncomputable def hp766710 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766675 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp766711 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp766712 := @hp766711 (Enclosure.sfrac Bool.false 1 16) 395216782457823 4503599627370496 7342922691 4503599627370496 1 16 0

noncomputable def hp766713 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1)) 3670612867449889

noncomputable def hp766714 := @hp766713 4503599627370496 4725676995 4503599627370496 60585583 67108864 39 67108864 26522549304479629443072 395216782457823 4503599627370496 7342922691

noncomputable def hp766715 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1)) 60585583 67108864 39

noncomputable def hp766716 := @hp766715 67108864 60585583 67108864 39 67108864 3670612867449889 4503599627370496 4725676995 4503599627370496 (@hp766688 1 60585583 60585583 67108864 39 67108864 (hp766670 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp766717 := hp766716 (@hp766688 1 60585583 60585583 67108864 39 67108864 (hp766670 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp766718 := @hp766714 4503599627370496 (hp766717 rfl) (@hp766688 1 60585583 60585583 67108864 39 67108864 (hp766670 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp766719 := @hp766710 500000000000000 676691759168479 4503599627370496 7342922691 4503599627370496 hp766707 hp627574 hp766709 hp742826 hd4948 (@hp766712 1 10827068146695664 676691759168479 4503599627370496 7342922691 4503599627370496 (hp766718 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp766720 := @hp766706 31678227 33554432 689 67108864 Bool.false 19679152 33554432 1 10890000 (@hp766708 hp627574 hp766709 hp742826 31678227 33554432 689 67108864 (hp766719 rfl) rfl) (Enclosure.sfrac_true_div 31678227 33554432)

noncomputable def hp766721 := nat_lit 2145643805917874838714506560186005868149816944026952871434896161

noncomputable def hp766722 := nat_lit 1014114359964051652410372509786183765674131347634191713813281

noncomputable def hp766723 := nat_lit 6434903189033696412838698935538445236918102569385590230877061921

noncomputable def hp766724 := BSN.cos_dyadic_bound_f 31678227 33554432 3 2 33554432 10890000 hp766721 hp684401 hp766722 hp766723 hp684404

noncomputable def hp766725 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 31678227) (BSN.cosEvenQ 33554432) 0 2 hp766721 hp684401 hp766722 rfl rfl rfl

noncomputable def hp766726 := hp766724 hp766722 19679152 rfl rfl rfl rfl rfl rfl rfl rfl (hp766725 rfl)

noncomputable def hp766727 := @BSN.binarySplit_of_base2 (BSN.cosOddP 31678227) (BSN.cosOddQ 33554432) 0 2 hp766723 hp684404 hp766722 rfl rfl rfl

noncomputable def hp766728 := hp766720 (BSN.cos_neg_of_bound 31678227 33554432 Bool.false 19679152 33554432 1 10890000 (hp766726 (hp766727 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp766729 := hp766680 hp766704 (@hp766705 19679152 33554432 7570318864 730815528960000 1229947 2097152 473144929 45675970560000 (hp766728 rfl) rfl)

noncomputable def hp766730 := @hp766655 67108864 100755286634959 140737488355328 2714367840100947 170292360909946880000 1959851835774428389277 9444732965739290427392 13230180558201810364747 hp743845 (hp766673 rfl) (@hp766676 Bool.false 100755286634959 140737488355328 2714367840100947 170292360909946880000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766482 (Enclosure.sfrac Bool.false 11 1)) (hp766677 rfl (hp766485 rfl rfl))) (hp766729 rfl))

noncomputable def hp766731 := @hp766479 hp766477 hp743845 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 890180 1000))) (@hp766484 hp766477 hp743845 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 890180 1000) 11 (hp766485 rfl rfl)) (@hp766488 hp766477 hp743845 hp766654 (hp766730 rfl) rfl rfl))

theorem hd5075 : hp766478 hp743845 := hp766731

noncomputable def hp766732 := nat_lit 1388872726159339578429023

noncomputable def hp766733 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 891448 1000)) Bool.true 43591284853012421774541 18889465931478580854784 hp766732

noncomputable def hp766734 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 891448 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 891448 1000)) Bool.true 43591284853012421774541 18889465931478580854784

noncomputable def hp766735 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 891448 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp766736 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp766735 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp766737 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 891448 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp766738 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 891448 1000)) (Enclosure.sfrac Bool.false 891448 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp766736 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp766739 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 891448 1000)) hp766738 Bool.true 43591284853012421774541 18889465931478580854784

noncomputable def hp766740 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 891448 1000) 891448 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 891448 1000)) rfl

noncomputable def hp766741 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 891448 1000)) (Enclosure.sfrac Bool.false 891448 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp766736 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp766742 := nat_lit 11701446427144282412713242525696

noncomputable def hp766743 := @hp766741 676391799 268435456 108153 134217728 4005556614688506802995 18889465931478580854784 7550497947328209981023 hp756249 hp766742 43591284853012421774541 18889465931478580854784

noncomputable def hp766744 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 891448 1000)) (Enclosure.sfrac Bool.false 891448 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 891448 1000)) (Enclosure.sfrac Bool.false 891448 1000) 11)

noncomputable def hp766745 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 891448 1000)) (Enclosure.sfrac Bool.false 891448 1000) 11) hp766744

noncomputable def hp766746 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 891448 1000)) (Enclosure.sfrac Bool.false 891448 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 891448 1000)) (Enclosure.sfrac Bool.false 891448 1000) 11)

noncomputable def hp766747 := @hp766746 676391799 536870912 216306 536870912 676391799 536870912 216306 536870912 726270163996901376 676391799 268435456

noncomputable def hp766748 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 891448 1000)) (Enclosure.sfrac Bool.false 891448 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp766749 := hp766748 BSN.quadSignNeg 9 10 11 891448 1000 184 238 536870912 268435456 9007199254740992

noncomputable def hp766750 := hp766749 Bool.false 946198685462 4061 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp766751 := hp766750 Bool.true 701057848 185693 Bool.true 631336280 Bool.true 707072081 28296951008113761 1 Bool.false 206513465

noncomputable def hp766752 := hp766751 Bool.false Bool.false 134785133 Bool.true Bool.true 676391799 216306 BSN.abs_quadSignPos (BSN.cos_quad_nat0 184 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 206513465 536870912) BSN.abs_quadSignNeg

noncomputable def hp766753 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 891448 1000)) (Enclosure.sfrac Bool.false 891448 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp766754 := hp766753 BSN.quadSignPos 7 8 9 891448 1000 58 124 536870912 268435456 9007199254740992

noncomputable def hp766755 := hp766754 Bool.false 946198685462 4061 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp766756 := hp766755 Bool.true 526764773 151655 Bool.true 94179645 Bool.true 805464420 28296951008113761 1 Bool.false 528631424

noncomputable def hp766757 := hp766756 Bool.true Bool.false 37819088 Bool.false Bool.true 701057848 185693 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 58 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 528631424 536870912) BSN.abs_quadSignPos

noncomputable def hp766758 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 891448 1000)) (Enclosure.sfrac Bool.false 891448 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp766759 := hp766758 BSN.quadSignNeg 5 6 7 891448 1000 105 17 536870912 268435456 9007199254740992

noncomputable def hp766760 := hp766759 Bool.false 946198685462 4061 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp766761 := hp766760 Bool.true 298874015 112698 Bool.false 127986920 Bool.false 564342131 28296951008113761 1 Bool.false 126778072

noncomputable def hp766762 := hp766761 Bool.true Bool.false 466006291 Bool.true Bool.true 526764773 151655 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 105 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 126778072 536870912) BSN.abs_quadSignNeg

noncomputable def hp766763 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 891448 1000)) (Enclosure.sfrac Bool.false 891448 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp766764 := hp766763 BSN.quadSignPos 3 4 5 891448 1000 335 208 536870912 268435456 9007199254740992

noncomputable def hp766765 := hp766764 Bool.false 946198685462 4061 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp766766 := hp766765 Bool.true 539386918 66611 Bool.false 218135884 Bool.false 524294107 28296951008113761 1 Bool.false 212183309

noncomputable def hp766767 := hp766766 Bool.false Bool.false 300575050 Bool.false Bool.true 298874015 112698 BSN.abs_quadSignPos (BSN.cos_quad_nat3 335 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 212183309 536870912) BSN.abs_quadSignPos

noncomputable def hp766768 := hp766748 BSN.quadSignNeg 1 2 3 891448 1000 728 498 536870912 268435456 9007199254740992

noncomputable def hp766769 := hp766768 Bool.false 946198685462 4061 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp766770 := hp766769 Bool.true 536870592 4122 Bool.false 530440718 Bool.false 440289079 28296951008113761 1 Bool.false 295462478

noncomputable def hp766771 := hp766770 Bool.false Bool.false 366224557 Bool.true Bool.true 539386918 66611 BSN.abs_quadSignPos (BSN.cos_quad_nat0 728 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 295462478 536870912) BSN.abs_quadSignNeg

noncomputable def hp766772 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 891448 1000)) (Enclosure.sfrac Bool.false 891448 1000) 1) Bool.true

noncomputable def hp766773 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 891448 1000)) (Enclosure.sfrac Bool.false 891448 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 891448 1000)))

noncomputable def hp766774 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 891448 1000))) Bool.true 67108824 67108864

noncomputable def hp766775 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 891448 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 59137417841) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 59137417841 33554432

noncomputable def hp766776 := nat_lit 875248352026936261453626694973989150509451227362810161

noncomputable def hp766777 := nat_lit 496613859434268657361054137774708021991485053337600

noncomputable def hp766778 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 891448 1000)) Bool.false hp766776 hp766777 511098476617480561

noncomputable def hp766779 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 891448 4000) (Real.log (Enclosure.sfrac Bool.false 3178719146816 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1782896))))))

noncomputable def hp766780 := nat_lit 270222593756481720208263863664640000

noncomputable def hp766781 := nat_lit 1445336556743913846326334570111671992320

noncomputable def hp766782 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 891448 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp766779 (Enclosure.sfrac Bool.false 891448 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 891448 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp766780 hp766781)) Bool.false

noncomputable def hp766783 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 891448 1000) 891448 1000 3178719146816 16000000 1782896

noncomputable def hp766784 := hp766783 4000 2000 hp766780 hp766781 (@Eq.refl Real (Enclosure.sfrac Bool.false 891448 1000)) rfl rfl rfl rfl

noncomputable def hp766785 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp766779 (Enclosure.sfrac Bool.false 891448 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 891448 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp766780 hp766781) 793729070446148118981 450359962737049600

noncomputable def hp766786 := nat_lit 1147205519968745896612497581636307059355747912728982534225920

noncomputable def hp766787 := @hp766785 511098476617480561 67584000000000000000000 hp766780 hp766781 0 1 hp766786 hp766776 hp766777 511098476617480561 67584000000000000000000

noncomputable def hp766788 := @Enclosure.Real.IsNear.subLit_ff_p (hp766779 (Enclosure.sfrac Bool.false 891448 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 891448 2000) (Real.log Real.pi)) 5117589237424915779801 2251799813685248000 85175125029707 33000000000000000000

noncomputable def hp766789 := nat_lit 33291410150885608400344842240000

noncomputable def hp766790 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 891448 4000) (Real.log (Enclosure.sfrac Bool.false 3178719146816 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1782896))))))

noncomputable def hp766791 := @hp766790 (Enclosure.sfrac Bool.false 891448 2000) 6121270457579959259353 2251799813685248000 85175125029707 33000000000000000000 891448 2000 0

noncomputable def hp766792 := nat_lit 10235178474849831559602000

noncomputable def hp766793 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 891448 4000) (Real.log (Enclosure.sfrac Bool.false 3178719146816 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1782896))))) 6122154421551757694353

noncomputable def hp766794 := nat_lit 13783875675895565031274455823542124544

noncomputable def hp766795 := @hp766793 2251799813685248000 1392889562922103 544500000000000000000 883963971798435 2251799813685248 200000001089 8712000000000000000 hp766794 6121270457579959259353 2251799813685248000 85175125029707

noncomputable def hp766796 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 891448 4000) (Real.log (Enclosure.sfrac Bool.false 3178719146816 16000000)) 891448 4000 0 1 54941214038748263 4503599627370496

noncomputable def hp766797 := nat_lit 117985358749479933180903424

noncomputable def hp766798 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3178719146816) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp766797 hp617687

noncomputable def hp766799 := BSN.log_rat_reduce_isNear 3178719146816 16000000 17 6357438293632 4194304000000 111641795 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp766800 := nat_lit 173686592705949296330473115027066189722892176627021820678763772502776206394242128022071551604630072009430068890349720956732723691520

noncomputable def hp766801 := nat_lit 2496377372771471531426257617265407132894938302042826494176048465048938154239091355141720737355224251365396548187092272852294959104

noncomputable def hp766802 := nat_lit 2069982515887000666136717998350455181667695922888289998554801984402775380955095934693900489424989108347308355289889447608320

noncomputable def hp766803 := BSN.log_dyadic_bound 1081567146816 5275871146816 6 5 hp766800 268435456 87120000 hp766801 hp766802 111641795 6357438293632

noncomputable def hp766804 := hp766803 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp766805 := @BSN.binarySplit_of_base5 (BSN.artanhP 1081567146816) (BSN.artanhQ 5275871146816) 0 5 hp766801 hp766800 hp766802 rfl rfl rfl

noncomputable def hp766806 := hp766799 rfl rfl rfl rfl (hp766804 (hp766805 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp766807 := @hp766796 12500018513 1089000000000000000 6122154421551757694353 2251799813685248000 1392889562922103 544500000000000000000 (Enclosure.Real.IsNear.const Bool.false 891448 4000) (BSN.isNear_log_sfrac 3178719146816 16000000 54941214038748263 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp766798 1000001481040000 87120000000000000000000 54941214038748263 4503599627370496 12500018513 1089000000000000000 (hp766806 rfl rfl rfl) rfl)) rfl

noncomputable def hp766808 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1782896)))) 1 4

noncomputable def hp766809 := @hp766808 0 1 883963971798435 562949953421312 200000001089 2178000000000000000 883963971798435 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp766810 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1782896))) 884279719003555 562949953421312 1

noncomputable def hp766811 := @hp766810 2000000000000000 18820 33554432 1 10890000 29660908982160504913920 883963971798435 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp766812 := BSN.arctan_dyadic_bound_f 1000 1782896 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp766813 := hp766812 1 18820 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1782896) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1782896) 0 0 rfl)

noncomputable def hp766814 := hp766809 (hp766811 (hp766813 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp766815 := @hp766788 4280149508991 8388608000 334293 67108864000 hp766789 793729070446148118981 450359962737049600 511098476617480561 67584000000000000000000 (@hp766791 1 hp766792 5117589237424915779801 2251799813685248000 85175125029707 33000000000000000000 (@hp766795 33000000000000000000 hp766807 hp766814 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 891448 2000) rfl rfl)

noncomputable def hp766816 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 891448 2000) (Real.log Real.pi) 891448 2000 0 1 38410761 33554432

noncomputable def hp766817 := hp766815 (@hp766816 3 268435456 4280149508991 8388608000 334293 67108864000 (Enclosure.Real.IsNear.const Bool.false 891448 2000) hd4909 rfl) rfl

noncomputable def hp766818 := @hp766778 67584000000000000000000 59137417841 33554432 509 67108864 (@hp766782 hp766776 hp766777 511098476617480561 67584000000000000000000 (hp766784 rfl rfl rfl rfl rfl) (hp766787 (hp766817 rfl) (Enclosure.Real.IsNear.const Bool.true hp766780 hp766781) rfl rfl)) rfl

noncomputable def hp766819 := nat_lit 7590648583518739960430592

noncomputable def hp766820 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 59137417841) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp766819) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp766821 := BSN.sin_reduce_arg_pos_rat_q1 59137417841 33554432 226375608064910080 72057594037927936 280 hp766819 hp619237 rfl rfl rfl rfl

noncomputable def hp766822 := nat_lit 14340538839627768802783159005601299306501424717219746571801997386787376022891867232759580843686770544454354172170716153638906865080719792840241

noncomputable def hp766823 := nat_lit 10165973449064916217530263157946850059961276984823377565729786901649952555796612359359182775564461069286154804030157409551711435643592241

noncomputable def hp766824 := nat_lit 71613840742671778141140865137876732676681605835604224270245920154912960026745376670882037896277391248903251394544563853083487225095346199895601

noncomputable def hp766825 := BSN.sin_dyadic_bound_f 215739208429 137438953472 4 3 67108864 21801270 hp766822 hp737934 hp766823 hp766824 hp737937

noncomputable def hp766826 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215739208429) (BSN.sinEvenQ 137438953472) 0 3 hp766822 hp737934 hp766823 rfl rfl rfl

noncomputable def hp766827 := hp766825 hp766823 67108824 rfl rfl rfl rfl rfl rfl rfl rfl (hp766826 rfl)

noncomputable def hp766828 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215739208429) (BSN.sinOddQ 137438953472) 0 3 hp766824 hp737937 hp766823 rfl rfl rfl

noncomputable def hp766829 := @BSN.sin_arg_round Bool.false 67108824 67108864 hp766819 hp619237 215739208429 137438953472 21801270 21780000 (hp766827 (hp766828 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766830 := hp766820 67108824 67108864 280 1000000000000000 21780000 10890000 hp766821 BSN.pi_near_15 hp766829 rfl rfl

noncomputable def hp766831 := @hp766775 509 67108864 Bool.true 67108824 67108864 1 10890000 hp766818 (Enclosure.sfrac_false_div 59137417841 33554432) (hp766830 rfl rfl) rfl

noncomputable def hp766832 := @hp766772 8388603 8388608 350632429 45675970560000 536870592 536870912 4122 536870912 (@hp766773 Bool.true 8388603 8388608 350632429 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 891448 1000)) (Enclosure.sfrac Bool.false 891448 1000)) (@hp766774 5610118864 730815528960000 8388603 8388608 350632429 45675970560000 (hp766831 rfl) rfl))

noncomputable def hp766833 := @hp766778 67584000000000000000000 946198685462 536870912 4061 536870912 (@hp766782 hp766776 hp766777 511098476617480561 67584000000000000000000 (hp766784 rfl rfl rfl rfl rfl) (hp766787 (hp766817 rfl) (Enclosure.Real.IsNear.const Bool.true hp766780 hp766781) rfl rfl)) rfl

noncomputable def hp766834 := hp766771 (BSN.cos_quad_nat2 498 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 366224557 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 891448 1000)) rfl rfl (hp766832 rfl) hp766833

noncomputable def hp766835 := nat_lit 10911348520475840606292796667930240652005971232313309027126122515913000089298013725987687727859399683414465581056

noncomputable def hp766836 := nat_lit 496183423099103261419553960533423969773457056736184481140512257042348257909597288681759856553983956094976

noncomputable def hp766837 := nat_lit 66170494013054917257660360542768301663114911117894257578627639894977183132777495712485804237390111079562511257600

noncomputable def hp766838 := BSN.cos_dyadic_bound_f 530440718 536870912 4 3 536870912 268435456 hp766835 hp716712 hp766836 hp766837 hp716714

noncomputable def hp766839 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 530440718) (BSN.cosEvenQ 536870912) 0 3 hp766835 hp716712 hp766836 rfl rfl rfl

noncomputable def hp766840 := hp766838 hp766836 295462478 rfl rfl rfl rfl rfl rfl rfl rfl (hp766839 rfl)

noncomputable def hp766841 := @BSN.binarySplit_of_base3 (BSN.cosOddP 530440718) (BSN.cosOddQ 536870912) 0 3 hp766837 hp716714 hp766836 rfl rfl rfl

noncomputable def hp766842 := nat_lit 5246351105725222489360037629144431707649875375825202598740767558344453441

noncomputable def hp766843 := nat_lit 1412223084452430399300539384991432483183116548045957727013804837514561

noncomputable def hp766844 := nat_lit 15736228871006762607281511808663312257983259894379515880768275065358331201

noncomputable def hp766845 := BSN.cos_dyadic_bound_f 440289079 536870912 3 2 536870912 268435456 hp766842 hp708868 hp766843 hp766844 hp708870

noncomputable def hp766846 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 440289079) (BSN.cosEvenQ 536870912) 0 2 hp766842 hp708868 hp766843 rfl rfl rfl

noncomputable def hp766847 := hp766845 hp766843 366224557 rfl rfl rfl rfl rfl rfl rfl rfl (hp766846 rfl)

noncomputable def hp766848 := @BSN.binarySplit_of_base2 (BSN.cosOddP 440289079) (BSN.cosOddQ 536870912) 0 2 hp766844 hp708870 hp766843 rfl rfl rfl

noncomputable def hp766849 := hp766834 hd4911 hd4913 hd4915 hd4917 hd4918 (hp766840 (hp766841 rfl) rfl rfl rfl rfl) (hp766847 (hp766848 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766850 := hp766767 (BSN.cos_quad_nat0 208 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 300575050 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 891448 1000)) rfl rfl (hp766849 rfl rfl rfl rfl rfl) hp766833

noncomputable def hp766851 := nat_lit 2264167002278960041785614797639936

noncomputable def hp766852 := BSN.sin_dyadic_bound_f 218135884 536870912 2 1 536870912 268435456 hp766851 hp708890 hp766851 hp766851 hp708891

noncomputable def hp766853 := @BSN.binarySplit_of_base (BSN.sinEvenP 218135884) (BSN.sinEvenQ 536870912) 0 1 hp766851 hp708890 hp766851 rfl rfl rfl

noncomputable def hp766854 := hp766852 hp766851 212183309 rfl rfl rfl rfl rfl rfl rfl rfl (hp766853 rfl)

noncomputable def hp766855 := @BSN.binarySplit_of_base (BSN.sinOddP 218135884) (BSN.sinOddQ 536870912) 0 1 hp766851 hp708891 hp766851 rfl rfl rfl

noncomputable def hp766856 := nat_lit 10414050977824686513727946267426640112686024794761138803172981209091439612775841317500141286650655160768143932881

noncomputable def hp766857 := nat_lit 431419445115320491147654355280177286643709722774541056956866942311817604070743945793760771718853614222801

noncomputable def hp766858 := nat_lit 63155783205911188624942568090589472863251540499085072702885197209687181800654385309374687749822975350961028316625

noncomputable def hp766859 := BSN.cos_dyadic_bound_f 524294107 536870912 4 3 536870912 268435456 hp766856 hp716712 hp766857 hp766858 hp716714

noncomputable def hp766860 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 524294107) (BSN.cosEvenQ 536870912) 0 3 hp766856 hp716712 hp766857 rfl rfl rfl

noncomputable def hp766861 := hp766859 hp766857 300575050 rfl rfl rfl rfl rfl rfl rfl rfl (hp766860 rfl)

noncomputable def hp766862 := @BSN.binarySplit_of_base3 (BSN.cosOddP 524294107) (BSN.cosOddQ 536870912) 0 3 hp766858 hp716714 hp766857 rfl rfl rfl

noncomputable def hp766863 := hp766850 hd4920 hd4922 hd4924 hd4926 hd4918 (hp766854 (hp766855 rfl) rfl rfl rfl rfl) (hp766861 (hp766862 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766864 := hp766762 (BSN.cos_quad_nat1 17 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 466006291 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 891448 1000)) rfl rfl (hp766863 rfl rfl rfl rfl rfl) hp766833

noncomputable def hp766865 := nat_lit 268325749824691736093212264960000

noncomputable def hp766866 := BSN.sin_dyadic_bound_f 127986920 536870912 2 1 536870912 268435456 hp766865 hp708890 hp766865 hp766865 hp708891

noncomputable def hp766867 := @BSN.binarySplit_of_base (BSN.sinEvenP 127986920) (BSN.sinEvenQ 536870912) 0 1 hp766865 hp708890 hp766865 rfl rfl rfl

noncomputable def hp766868 := hp766866 hp766865 126778072 rfl rfl rfl rfl rfl rfl rfl rfl (hp766867 rfl)

noncomputable def hp766869 := @BSN.binarySplit_of_base (BSN.sinOddP 127986920) (BSN.sinOddQ 536870912) 0 1 hp766865 hp708891 hp766865 rfl rfl rfl

noncomputable def hp766870 := nat_lit 25492151353428072651988107838646119908454935706861853162944949248140669985

noncomputable def hp766871 := nat_lit 10288209283369669227264952404184670569944546584444298322718600071902241

noncomputable def hp766872 := nat_lit 66748501205852829862172329654466396007887778537787181800904751249775817761

noncomputable def hp766873 := BSN.sin_dyadic_bound_f 564342131 536870912 3 2 536870912 268435456 hp766870 hp708845 hp766871 hp766872 hp708848

noncomputable def hp766874 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 564342131) (BSN.sinEvenQ 536870912) 0 2 hp766870 hp708845 hp766871 rfl rfl rfl

noncomputable def hp766875 := hp766873 hp766871 466006291 rfl rfl rfl rfl rfl rfl rfl rfl (hp766874 rfl)

noncomputable def hp766876 := @BSN.binarySplit_of_base2 (BSN.sinOddP 564342131) (BSN.sinOddQ 536870912) 0 2 hp766872 hp708848 hp766871 rfl rfl rfl

noncomputable def hp766877 := hp766864 hd4928 hd4930 hd4932 hd4934 hd4918 (hp766868 (hp766869 rfl) rfl rfl rfl rfl) (hp766875 (hp766876 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766878 := hp766757 (BSN.cos_quad_nat0 124 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 37819088 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 891448 1000)) rfl rfl (hp766877 rfl rfl rfl rfl rfl) hp766833

noncomputable def hp766879 := nat_lit 78673450181281359721246892300625

noncomputable def hp766880 := BSN.cos_dyadic_bound_f 94179645 536870912 2 1 536870912 268435456 hp766879 hp708767 hp766879 hp766879 hp708768

noncomputable def hp766881 := @BSN.binarySplit_of_base (BSN.cosEvenP 94179645) (BSN.cosEvenQ 536870912) 0 1 hp766879 hp708767 hp766879 rfl rfl rfl

noncomputable def hp766882 := hp766880 hp766879 528631424 rfl rfl rfl rfl rfl rfl rfl rfl (hp766881 rfl)

noncomputable def hp766883 := @BSN.binarySplit_of_base (BSN.cosOddP 94179645) (BSN.cosOddQ 536870912) 0 1 hp766879 hp708768 hp766879 rfl rfl rfl

noncomputable def hp766884 := nat_lit 58153850254312278111210734170428983731153883471219126451897488109892705764561131606532251270604784822124544000000

noncomputable def hp766885 := nat_lit 74568658756686909532065827579848051763250116348135097417955318480565322474432423032342745255936000000000000

noncomputable def hp766886 := nat_lit 352092474014789682674415995928344645261233311502006138586096113210382217622810930567379639101599819465857433600000

noncomputable def hp766887 := BSN.cos_dyadic_bound_f 805464420 536870912 4 3 536870912 268435456 hp766884 hp716712 hp766885 hp766886 hp716714

noncomputable def hp766888 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 805464420) (BSN.cosEvenQ 536870912) 0 3 hp766884 hp716712 hp766885 rfl rfl rfl

noncomputable def hp766889 := hp766887 hp766885 37819088 rfl rfl rfl rfl rfl rfl rfl rfl (hp766888 rfl)

noncomputable def hp766890 := @BSN.binarySplit_of_base3 (BSN.cosOddP 805464420) (BSN.cosOddQ 536870912) 0 3 hp766886 hp716714 hp766885 rfl rfl rfl

noncomputable def hp766891 := hp766878 hd4936 hd4938 hd4940 hd4942 hd4918 (hp766882 (hp766883 rfl) rfl rfl rfl rfl) (hp766889 (hp766890 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766892 := hp766752 (BSN.cos_quad_nat2 238 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 134785133 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 891448 1000)) rfl rfl (hp766891 rfl rfl rfl rfl rfl) hp766833

noncomputable def hp766893 := nat_lit 21908964775177463699629328552046393547827165774291989541713981526424949873209939912615751132084828303785984000000

noncomputable def hp766894 := nat_lit 4009857724235368691221849668489140062559972309646734195870201066062537211542836869852683042816000000000000

noncomputable def hp766895 := nat_lit 132813616976074434311155053746954879546015175727112612369455915519126882438447213820515328882778885167094169600000

noncomputable def hp766896 := BSN.cos_dyadic_bound_f 631336280 536870912 4 3 536870912 268435456 hp766893 hp716712 hp766894 hp766895 hp716714

noncomputable def hp766897 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 631336280) (BSN.cosEvenQ 536870912) 0 3 hp766893 hp716712 hp766894 rfl rfl rfl

noncomputable def hp766898 := hp766896 hp766894 206513465 rfl rfl rfl rfl rfl rfl rfl rfl (hp766897 rfl)

noncomputable def hp766899 := @BSN.binarySplit_of_base3 (BSN.cosOddP 631336280) (BSN.cosOddQ 536870912) 0 3 hp766895 hp716714 hp766894 rfl rfl rfl

noncomputable def hp766900 := nat_lit 34491870195737920032976822016799314864304522379444138865702315843076988144896774414643575037525317313063128200641

noncomputable def hp766901 := nat_lit 15615801206600059184309774752956753513656299192931275683792972687676999720392045011688783053565917467047361

noncomputable def hp766902 := nat_lit 209001218513736548025176379020175043643967565807004985463356445107694309315116436088193914670206158434454209361345

noncomputable def hp766903 := BSN.cos_dyadic_bound_f 707072081 536870912 4 3 536870912 268435456 hp766900 hp716712 hp766901 hp766902 hp716714

noncomputable def hp766904 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 707072081) (BSN.cosEvenQ 536870912) 0 3 hp766900 hp716712 hp766901 rfl rfl rfl

noncomputable def hp766905 := hp766903 hp766901 134785133 rfl rfl rfl rfl rfl rfl rfl rfl (hp766904 rfl)

noncomputable def hp766906 := @BSN.binarySplit_of_base3 (BSN.cosOddP 707072081) (BSN.cosOddQ 536870912) 0 3 hp766902 hp716714 hp766901 rfl rfl rfl

noncomputable def hp766907 := hp766892 hd4944 hd4946 hd4961 hd4963 hd4918 (hp766898 (hp766899 rfl) rfl rfl rfl rfl) (hp766905 (hp766906 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766908 := @hp766747 108153 134217728 (hp766907 rfl rfl rfl rfl rfl) (hp766907 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp766909 := @hp766745 Bool.true 676391799 268435456 108153 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 891448 1000)) (Enclosure.sfrac Bool.false 891448 1000) 11) hp766908

noncomputable def hp766910 := @Enclosure.Real.IsNear.mulLit_tf hp766736 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1))) 9722341 33554432 1

noncomputable def hp766911 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp766735 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp766912 := @hp766911 1 1 0 1 9722341 33554432 1 33554432 9722341 33554432 1

noncomputable def hp766913 := @Enclosure.Real.IsNear.of_eq (hp766735 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp766914 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 891448 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp766915 := @hp766913 (@Inv.inv Real Real.instInv (Real.sqrt hp766737)) Bool.false 9722341 33554432 1 33554432 (hp766914 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 891448 1000) 891448 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 891448 1000))))

noncomputable def hp766916 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp766737)) Bool.false 19444682 67108864 2 67108864 9722341 33554432

noncomputable def hp766917 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp766737) Bool.false 231610860 67108864 6 67108864 57902715 16777216 3 33554432

noncomputable def hp766918 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 891448 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp766919 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 891448 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp766920 := @hp766919 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 891448 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 1190161861717

noncomputable def hp766921 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 891448 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 891448 1000 0

noncomputable def hp766922 := @hp766921 1 10680707 67108864 1 67108864 1190161861717 8388608000 111431 8388608000 (Enclosure.Real.IsNear.const Bool.false 891448 1000) hd4949

noncomputable def hp766923 := @hp766920 8388608000 111431 8388608000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 891448 1000) 891448 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 891448 1000))) (hp766922 rfl)

noncomputable def hp766924 := @hp766918 1190161861717 8388608000 111431 8388608000 399675876 399675914 33554432 hp766923 rfl rfl rfl

noncomputable def hp766925 := @Enclosure.Real.IsNear.recentre' hp766737 Bool.false 799351790 67108864 38 67108864 399675895 33554432 19 33554432 (hp766924 rfl rfl rfl)

noncomputable def hp766926 := @Enclosure.Real.IsNear.sqrt_image hp766737 399675895 33554432 19 33554432 115805427 115805433 33554432 (hp766925 rfl) rfl rfl

noncomputable def hp766927 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp766737) 57902715 16777216 3 33554432 9722340 9722342 33554432 (hp766917 (hp766926 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp766928 := @hp766912 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp766915 (@hp766916 1 33554432 (hp766927 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp766929 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp766930 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp766931 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1))) (hp766929 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766930 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp766932 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 891448 1000) 891448 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 891448 1000)) rfl

noncomputable def hp766933 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp766934 := @hp766933 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766930 (Enclosure.sfrac Bool.false 1 16)))) 19771017

noncomputable def hp766935 := @hp766934 16777216 171 33554432 20838335 33554432 463616179 45675970560000 411995075536695 562949953421312 1545534891536063 102175416545968128000

noncomputable def hp766936 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp766937 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1)))) 28473495

noncomputable def hp766938 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp766939 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 384243711) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp766940 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1))) Bool.false 27038747419971518743365

noncomputable def hp766941 := nat_lit 512735433034492522028441029

noncomputable def hp766942 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp766943 := @Enclosure.Real.IsNear.subLit_ff_p hp766737 (Enclosure.sfrac Bool.false 11 1) 399675895 33554432 19 33554432 11 1 0

noncomputable def hp766944 := @hp766942 500000000000000 30577143 33554432 19 33554432 27038747419971518743365 4722366482869645213696 hp766941 hp682805 hd4948 (@hp766943 1 30577143 30577143 33554432 19 33554432 (hp766925 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp766945 := @hp766939 384243711 67108864 15 4194304 Bool.false 56946990 67108864 1 10890000 (@hp766940 4722366482869645213696 hp766941 hp682805 384243711 67108864 15 4194304 (hp766944 rfl) rfl) (Enclosure.sfrac_false_div 384243711 67108864)

noncomputable def hp766946 := nat_lit 9799924994093748565573632

noncomputable def hp766947 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 384243711) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp766946) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp766948 := BSN.sin_reduce_arg_pos_rat_q3 384243711 67108864 226375608064910080 72057594037927936 0 hp766946 hp617687 rfl rfl rfl rfl

noncomputable def hp766949 := nat_lit 406017101624706454529557161216727562172458598248526567077123359680921916116566151458926240000

noncomputable def hp766950 := nat_lit 141495819733492391746103175098356469432723088700321927895371182950392118427056544100000000

noncomputable def hp766951 := nat_lit 1063149034832757917038394112331746276167833824697769059223492483915732954970696114654359200000

noncomputable def hp766952 := BSN.sin_dyadic_bound_f 139265310310 137438953472 3 2 67108864 21801270 hp766949 hp738039 hp766950 hp766951 hp738042

noncomputable def hp766953 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 139265310310) (BSN.sinEvenQ 137438953472) 0 2 hp766949 hp738039 hp766950 rfl rfl rfl

noncomputable def hp766954 := hp766952 hp766950 56946990 rfl rfl rfl rfl rfl rfl rfl rfl (hp766953 rfl)

noncomputable def hp766955 := @BSN.binarySplit_of_base2 (BSN.sinOddP 139265310310) (BSN.sinOddQ 137438953472) 0 2 hp766951 hp738042 hp766950 rfl rfl rfl

noncomputable def hp766956 := @BSN.sin_arg_round Bool.false 56946990 67108864 hp766946 hp617687 139265310310 137438953472 21801270 21780000 (hp766954 (hp766955 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp766957 := hp766947 56946990 67108864 0 1000000000000000 21780000 10890000 hp766948 BSN.pi_near_15 hp766956 rfl rfl

noncomputable def hp766958 := @hp766937 33554432 10471519 2854748160000 39541863 39542205 33554432 (@hp766938 56946990 67108864 167544304 45675970560000 28473495 33554432 10471519 2854748160000 (hp766945 (hp766957 rfl rfl) rfl rfl) rfl)

noncomputable def hp766959 := @hp766936 Bool.false 79084068 67108864 342 67108864 19771017 16777216 171 33554432 (hp766958 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp766960 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766930 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp766961 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766930 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 30223791)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp766962 := nat_lit 142727818595317351949882033005

noncomputable def hp766963 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766930 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp766962

noncomputable def hp766964 := nat_lit 48560525254355543238453749874053573

noncomputable def hp766965 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp766930 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp766966 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp766967 := @hp766966 (Enclosure.sfrac Bool.false 1 16) 91036991505327 1125899906842624 1799466003 1125899906842624 1 16 0

noncomputable def hp766968 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1)) 934961674042449

noncomputable def hp766969 := @hp766968 1125899906842624 1161931795 1125899906842624 30577143 33554432 19 33554432 3054694540950072459264 91036991505327 1125899906842624 1799466003

noncomputable def hp766970 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1)) 30577143 33554432 19

noncomputable def hp766971 := @hp766970 33554432 30577143 33554432 19 33554432 934961674042449 1125899906842624 1161931795 1125899906842624 (@hp766943 1 30577143 30577143 33554432 19 33554432 (hp766925 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp766972 := hp766971 (@hp766943 1 30577143 30577143 33554432 19 33554432 (hp766925 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp766973 := @hp766969 1125899906842624 (hp766972 rfl) (@hp766943 1 30577143 30577143 33554432 19 33554432 (hp766925 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp766974 := @hp766965 500000000000000 161405735682991 1125899906842624 1799466003 1125899906842624 hp766962 hp682141 hp766964 hp682143 hd4948 (@hp766967 1 2582491770927856 161405735682991 1125899906842624 1799466003 1125899906842624 (hp766973 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp766975 := @hp766961 30223791 33554432 675 67108864 Bool.false 20838335 33554432 1 10890000 (@hp766963 hp682141 hp766964 hp682143 30223791 33554432 675 67108864 (hp766974 rfl) rfl) (Enclosure.sfrac_true_div 30223791 33554432)

noncomputable def hp766976 := nat_lit 1777766547687151069309825078580515441494230152557709110539177601

noncomputable def hp766977 := nat_lit 696292150453649302803833656422782878245272119291562968469121

noncomputable def hp766978 := nat_lit 5331907058760545909323867568428700758726199913434544205680594561

noncomputable def hp766979 := BSN.cos_dyadic_bound_f 30223791 33554432 3 2 33554432 10890000 hp766976 hp684401 hp766977 hp766978 hp684404

noncomputable def hp766980 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 30223791) (BSN.cosEvenQ 33554432) 0 2 hp766976 hp684401 hp766977 rfl rfl rfl

noncomputable def hp766981 := hp766979 hp766977 20838335 rfl rfl rfl rfl rfl rfl rfl rfl (hp766980 rfl)

noncomputable def hp766982 := @BSN.binarySplit_of_base2 (BSN.cosOddP 30223791) (BSN.cosOddQ 33554432) 0 2 hp766978 hp684404 hp766977 rfl rfl rfl

noncomputable def hp766983 := hp766975 (BSN.cos_neg_of_bound 30223791 33554432 Bool.false 20838335 33554432 1 10890000 (hp766981 (hp766982 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp766984 := hp766935 hp766959 (@hp766960 20838335 33554432 7417858864 730815528960000 20838335 33554432 463616179 45675970560000 (hp766983 rfl) rfl)

noncomputable def hp766985 := @hp766910 33554432 411995075536695 562949953421312 1545534891536063 102175416545968128000 4005556614688506802995 18889465931478580854784 7550497947328209981023 hp756249 (hp766928 rfl) (@hp766931 Bool.false 411995075536695 562949953421312 1545534891536063 102175416545968128000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766737 (Enclosure.sfrac Bool.false 11 1)) (hp766932 rfl (hp766740 rfl rfl))) (hp766984 rfl))

noncomputable def hp766986 := @hp766734 hp766732 hp756249 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 891448 1000))) (@hp766739 hp766732 hp756249 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 891448 1000) 11 (hp766740 rfl rfl)) (@hp766743 hp766732 hp756249 hp766909 (hp766985 rfl) rfl rfl))

theorem hd5076 : hp766733 hp756249 := hp766986

noncomputable def hp790762 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000)) Bool.false 556919581 10737418240 1213 10737418240

noncomputable def hp793197 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 876205 1000) (Enclosure.sfrac Bool.false 877478 1000) 876205 1000 877478 1000

noncomputable def hp793198 := hp793197 (@Eq.refl Real (Enclosure.sfrac Bool.false 876205 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 877478 1000)) rfl rfl rfl

noncomputable def hp793199 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 876205 1000) (Enclosure.sfrac Bool.false 877478 1000) hp793198)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 876205 1000) (Enclosure.sfrac Bool.false 877478 1000) hp793198))

noncomputable def hp793200 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 876205 1000) 876205 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 876205 1000)) rfl rfl

noncomputable def hp793201 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 876205 1000) (Enclosure.sfrac Bool.false 877478 1000) hp793198)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 876205 1000) (Enclosure.sfrac Bool.false 877478 1000) hp793198))

noncomputable def hp793202 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 876205 1000) (Enclosure.sfrac Bool.false 877478 1000) hp793198)) 55945259405031329085

noncomputable def hp793203 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 876205 1000) (Enclosure.sfrac Bool.false 877478 1000) hp793198)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 876205 1000))

noncomputable def hp793204 := @hp793202 147573952589676412928 hp763692 hp754729 (@hp793203 Bool.true 55945259405031329085 147573952589676412928 hp763692 hp754729 (hd4340 (Enclosure.sfrac Bool.false 876205 1000) (Enclosure.sfrac Bool.false 877478 1000) hp793198) hd5064)

noncomputable def hp793205 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 876205 1000) (Enclosure.sfrac Bool.false 877478 1000) hp793198)) 3258179606373724984551

noncomputable def hp793206 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 876205 1000) (Enclosure.sfrac Bool.false 877478 1000) hp793198)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 877478 1000))

noncomputable def hp793207 := @hp793205 4722366482869645213696 515163359319180494358809 hp763951 (@hp793206 Bool.false 3258179606373724984551 4722366482869645213696 515163359319180494358809 hp763951 (hd4359 (Enclosure.sfrac Bool.false 876205 1000) (Enclosure.sfrac Bool.false 877478 1000) hp793198) hd5065)

noncomputable def hp793208 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 876205 1000) (Enclosure.sfrac Bool.false 877478 1000) hp793198) hp793200 (hp793201 (hp793204 rfl rfl rfl) (hp793207 rfl rfl rfl))

noncomputable def hp793209 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 876205 1000) (Enclosure.sfrac Bool.false 877478 1000) hp793198)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793210 := hp793209 (Enclosure.sfrac Bool.false 876205 1000) 749551 1000 876205 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793211 := hp793210 (@Eq.refl Real (Enclosure.sfrac Bool.false 876205 1000)) rfl rfl rfl rfl

noncomputable def hp793212 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 876205 1000) (Enclosure.sfrac Bool.false 877478 1000) hp793198)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793213 := @hp793212 Bool.true Bool.false 55945259405031329085 147573952589676412928 hp763692 hp754729 556919581 10737418240 1213 10737418240 (@hp793203 Bool.true 55945259405031329085 147573952589676412928 hp763692 hp754729 (hd4340 (Enclosure.sfrac Bool.false 876205 1000) (Enclosure.sfrac Bool.false 877478 1000) hp793198) hd5064)

noncomputable def hp793214 := hp793213 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793215 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 876205 1000) (Enclosure.sfrac Bool.false 877478 1000) hp793198)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793216 := hp793215 (Enclosure.sfrac Bool.false 877478 1000) 749551 1000 877478 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793217 := hp793216 (@Eq.refl Real (Enclosure.sfrac Bool.false 877478 1000)) rfl rfl rfl rfl

noncomputable def hp793218 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 876205 1000) (Enclosure.sfrac Bool.false 877478 1000) hp793198)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793219 := @hp793218 Bool.false Bool.false 3258179606373724984551 4722366482869645213696 515163359319180494358809 hp763951 556919581 10737418240 1213 10737418240 (@hp793206 Bool.false 3258179606373724984551 4722366482869645213696 515163359319180494358809 hp763951 (hd4359 (Enclosure.sfrac Bool.false 876205 1000) (Enclosure.sfrac Bool.false 877478 1000) hp793198) hd5065)

noncomputable def hp793220 := hp793219 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793222 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 877478 1000) (Enclosure.sfrac Bool.false 878750 1000) 877478 1000 878750 1000

noncomputable def hp793223 := hp793222 (@Eq.refl Real (Enclosure.sfrac Bool.false 877478 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 878750 1000)) rfl rfl rfl

noncomputable def hp793224 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 877478 1000) (Enclosure.sfrac Bool.false 878750 1000) hp793223)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 877478 1000) (Enclosure.sfrac Bool.false 878750 1000) hp793223))

noncomputable def hp793225 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 877478 1000) 877478 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 877478 1000)) rfl rfl

noncomputable def hp793226 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 877478 1000) (Enclosure.sfrac Bool.false 878750 1000) hp793223)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 877478 1000) (Enclosure.sfrac Bool.false 878750 1000) hp793223))

noncomputable def hp793227 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 877478 1000) (Enclosure.sfrac Bool.false 878750 1000) hp793223)) 3258179606373724984551

noncomputable def hp793228 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 877478 1000) (Enclosure.sfrac Bool.false 878750 1000) hp793223)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 877478 1000))

noncomputable def hp793229 := @hp793227 4722366482869645213696 515163359319180494358809 hp763951 (@hp793228 Bool.false 3258179606373724984551 4722366482869645213696 515163359319180494358809 hp763951 (hd4340 (Enclosure.sfrac Bool.false 877478 1000) (Enclosure.sfrac Bool.false 878750 1000) hp793223) hd5065)

noncomputable def hp793230 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 877478 1000) (Enclosure.sfrac Bool.false 878750 1000) hp793223)) 306950420731442336620847

noncomputable def hp793231 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 877478 1000) (Enclosure.sfrac Bool.false 878750 1000) hp793223)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 878750 1000))

noncomputable def hp793232 := @hp793230 75557863725914323419136 49977158152574219333851 hp764203 (@hp793231 Bool.true 306950420731442336620847 75557863725914323419136 49977158152574219333851 hp764203 (hd4359 (Enclosure.sfrac Bool.false 877478 1000) (Enclosure.sfrac Bool.false 878750 1000) hp793223) hd5066)

noncomputable def hp793233 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 877478 1000) (Enclosure.sfrac Bool.false 878750 1000) hp793223) hp793225 (hp793226 (hp793229 rfl rfl rfl) (hp793232 rfl rfl rfl))

noncomputable def hp793234 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 877478 1000) (Enclosure.sfrac Bool.false 878750 1000) hp793223)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793235 := hp793234 (Enclosure.sfrac Bool.false 877478 1000) 749551 1000 877478 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793236 := hp793235 (@Eq.refl Real (Enclosure.sfrac Bool.false 877478 1000)) rfl rfl rfl rfl

noncomputable def hp793237 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 877478 1000) (Enclosure.sfrac Bool.false 878750 1000) hp793223)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793238 := @hp793237 Bool.false Bool.false 3258179606373724984551 4722366482869645213696 515163359319180494358809 hp763951 556919581 10737418240 1213 10737418240 (@hp793228 Bool.false 3258179606373724984551 4722366482869645213696 515163359319180494358809 hp763951 (hd4340 (Enclosure.sfrac Bool.false 877478 1000) (Enclosure.sfrac Bool.false 878750 1000) hp793223) hd5065)

noncomputable def hp793239 := hp793238 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793240 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 877478 1000) (Enclosure.sfrac Bool.false 878750 1000) hp793223)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793241 := hp793240 (Enclosure.sfrac Bool.false 878750 1000) 749551 1000 878750 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793242 := hp793241 (@Eq.refl Real (Enclosure.sfrac Bool.false 878750 1000)) rfl rfl rfl rfl

noncomputable def hp793243 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 877478 1000) (Enclosure.sfrac Bool.false 878750 1000) hp793223)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793244 := @hp793243 Bool.true Bool.false 306950420731442336620847 75557863725914323419136 49977158152574219333851 hp764203 556919581 10737418240 1213 10737418240 (@hp793231 Bool.true 306950420731442336620847 75557863725914323419136 49977158152574219333851 hp764203 (hd4359 (Enclosure.sfrac Bool.false 877478 1000) (Enclosure.sfrac Bool.false 878750 1000) hp793223) hd5066)

noncomputable def hp793245 := hp793244 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793247 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 878750 1000) (Enclosure.sfrac Bool.false 880021 1000) 878750 1000 880021 1000

noncomputable def hp793248 := hp793247 (@Eq.refl Real (Enclosure.sfrac Bool.false 878750 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 880021 1000)) rfl rfl rfl

noncomputable def hp793249 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 878750 1000) (Enclosure.sfrac Bool.false 880021 1000) hp793248)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 878750 1000) (Enclosure.sfrac Bool.false 880021 1000) hp793248))

noncomputable def hp793250 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 878750 1000) 878750 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 878750 1000)) rfl rfl

noncomputable def hp793251 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 878750 1000) (Enclosure.sfrac Bool.false 880021 1000) hp793248)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 878750 1000) (Enclosure.sfrac Bool.false 880021 1000) hp793248))

noncomputable def hp793252 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 878750 1000) (Enclosure.sfrac Bool.false 880021 1000) hp793248)) 306950420731442336620847

noncomputable def hp793253 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 878750 1000) (Enclosure.sfrac Bool.false 880021 1000) hp793248)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 878750 1000))

noncomputable def hp793254 := @hp793252 75557863725914323419136 49977158152574219333851 hp764203 (@hp793253 Bool.true 306950420731442336620847 75557863725914323419136 49977158152574219333851 hp764203 (hd4340 (Enclosure.sfrac Bool.false 878750 1000) (Enclosure.sfrac Bool.false 880021 1000) hp793248) hd5066)

noncomputable def hp793255 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 878750 1000) (Enclosure.sfrac Bool.false 880021 1000) hp793248)) 34941177192362437896801

noncomputable def hp793256 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 878750 1000) (Enclosure.sfrac Bool.false 880021 1000) hp793248)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 880021 1000))

noncomputable def hp793257 := @hp793255 9444732965739290427392 1833655035804068967707 hp764450 (@hp793256 Bool.false 34941177192362437896801 9444732965739290427392 1833655035804068967707 hp764450 (hd4359 (Enclosure.sfrac Bool.false 878750 1000) (Enclosure.sfrac Bool.false 880021 1000) hp793248) hd5067)

noncomputable def hp793258 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 878750 1000) (Enclosure.sfrac Bool.false 880021 1000) hp793248) hp793250 (hp793251 (hp793254 rfl rfl rfl) (hp793257 rfl rfl rfl))

noncomputable def hp793259 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 878750 1000) (Enclosure.sfrac Bool.false 880021 1000) hp793248)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793260 := hp793259 (Enclosure.sfrac Bool.false 878750 1000) 749551 1000 878750 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793261 := hp793260 (@Eq.refl Real (Enclosure.sfrac Bool.false 878750 1000)) rfl rfl rfl rfl

noncomputable def hp793262 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 878750 1000) (Enclosure.sfrac Bool.false 880021 1000) hp793248)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793263 := @hp793262 Bool.true Bool.false 306950420731442336620847 75557863725914323419136 49977158152574219333851 hp764203 556919581 10737418240 1213 10737418240 (@hp793253 Bool.true 306950420731442336620847 75557863725914323419136 49977158152574219333851 hp764203 (hd4340 (Enclosure.sfrac Bool.false 878750 1000) (Enclosure.sfrac Bool.false 880021 1000) hp793248) hd5066)

noncomputable def hp793264 := hp793263 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793265 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 878750 1000) (Enclosure.sfrac Bool.false 880021 1000) hp793248)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793266 := hp793265 (Enclosure.sfrac Bool.false 880021 1000) 749551 1000 880021 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793267 := hp793266 (@Eq.refl Real (Enclosure.sfrac Bool.false 880021 1000)) rfl rfl rfl rfl

noncomputable def hp793268 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 878750 1000) (Enclosure.sfrac Bool.false 880021 1000) hp793248)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793269 := @hp793268 Bool.false Bool.false 34941177192362437896801 9444732965739290427392 1833655035804068967707 hp764450 556919581 10737418240 1213 10737418240 (@hp793256 Bool.false 34941177192362437896801 9444732965739290427392 1833655035804068967707 hp764450 (hd4359 (Enclosure.sfrac Bool.false 878750 1000) (Enclosure.sfrac Bool.false 880021 1000) hp793248) hd5067)

noncomputable def hp793270 := hp793269 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793272 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 880021 1000) (Enclosure.sfrac Bool.false 881292 1000) 880021 1000 881292 1000

noncomputable def hp793273 := hp793272 (@Eq.refl Real (Enclosure.sfrac Bool.false 880021 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 881292 1000)) rfl rfl rfl

noncomputable def hp793274 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 880021 1000) (Enclosure.sfrac Bool.false 881292 1000) hp793273)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 880021 1000) (Enclosure.sfrac Bool.false 881292 1000) hp793273))

noncomputable def hp793275 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 880021 1000) 880021 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 880021 1000)) rfl rfl

noncomputable def hp793276 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 880021 1000) (Enclosure.sfrac Bool.false 881292 1000) hp793273)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 880021 1000) (Enclosure.sfrac Bool.false 881292 1000) hp793273))

noncomputable def hp793277 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 880021 1000) (Enclosure.sfrac Bool.false 881292 1000) hp793273)) 34941177192362437896801

noncomputable def hp793278 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 880021 1000) (Enclosure.sfrac Bool.false 881292 1000) hp793273)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 880021 1000))

noncomputable def hp793279 := @hp793277 9444732965739290427392 1833655035804068967707 hp764450 (@hp793278 Bool.false 34941177192362437896801 9444732965739290427392 1833655035804068967707 hp764450 (hd4340 (Enclosure.sfrac Bool.false 880021 1000) (Enclosure.sfrac Bool.false 881292 1000) hp793273) hd5067)

noncomputable def hp793280 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 880021 1000) (Enclosure.sfrac Bool.false 881292 1000) hp793273)) 12445287495392789598849

noncomputable def hp793281 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 880021 1000) (Enclosure.sfrac Bool.false 881292 1000) hp793273)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 881292 1000))

noncomputable def hp793282 := @hp793280 4722366482869645213696 hp764708 hp752398 (@hp793281 Bool.true 12445287495392789598849 4722366482869645213696 hp764708 hp752398 (hd4359 (Enclosure.sfrac Bool.false 880021 1000) (Enclosure.sfrac Bool.false 881292 1000) hp793273) hd5068)

noncomputable def hp793283 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 880021 1000) (Enclosure.sfrac Bool.false 881292 1000) hp793273) hp793275 (hp793276 (hp793279 rfl rfl rfl) (hp793282 rfl rfl rfl))

noncomputable def hp793284 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 880021 1000) (Enclosure.sfrac Bool.false 881292 1000) hp793273)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793285 := hp793284 (Enclosure.sfrac Bool.false 880021 1000) 749551 1000 880021 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793286 := hp793285 (@Eq.refl Real (Enclosure.sfrac Bool.false 880021 1000)) rfl rfl rfl rfl

noncomputable def hp793287 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 880021 1000) (Enclosure.sfrac Bool.false 881292 1000) hp793273)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793288 := @hp793287 Bool.false Bool.false 34941177192362437896801 9444732965739290427392 1833655035804068967707 hp764450 556919581 10737418240 1213 10737418240 (@hp793278 Bool.false 34941177192362437896801 9444732965739290427392 1833655035804068967707 hp764450 (hd4340 (Enclosure.sfrac Bool.false 880021 1000) (Enclosure.sfrac Bool.false 881292 1000) hp793273) hd5067)

noncomputable def hp793289 := hp793288 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793290 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 880021 1000) (Enclosure.sfrac Bool.false 881292 1000) hp793273)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793291 := hp793290 (Enclosure.sfrac Bool.false 881292 1000) 749551 1000 881292 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793292 := hp793291 (@Eq.refl Real (Enclosure.sfrac Bool.false 881292 1000)) rfl rfl rfl rfl

noncomputable def hp793293 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 880021 1000) (Enclosure.sfrac Bool.false 881292 1000) hp793273)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793294 := @hp793293 Bool.true Bool.false 12445287495392789598849 4722366482869645213696 hp764708 hp752398 556919581 10737418240 1213 10737418240 (@hp793281 Bool.true 12445287495392789598849 4722366482869645213696 hp764708 hp752398 (hd4359 (Enclosure.sfrac Bool.false 880021 1000) (Enclosure.sfrac Bool.false 881292 1000) hp793273) hd5068)

noncomputable def hp793295 := hp793294 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793297 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 881292 1000) (Enclosure.sfrac Bool.false 882563 1000) 881292 1000 882563 1000

noncomputable def hp793298 := hp793297 (@Eq.refl Real (Enclosure.sfrac Bool.false 881292 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 882563 1000)) rfl rfl rfl

noncomputable def hp793299 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 881292 1000) (Enclosure.sfrac Bool.false 882563 1000) hp793298)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 881292 1000) (Enclosure.sfrac Bool.false 882563 1000) hp793298))

noncomputable def hp793300 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 881292 1000) 881292 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 881292 1000)) rfl rfl

noncomputable def hp793301 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 881292 1000) (Enclosure.sfrac Bool.false 882563 1000) hp793298)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 881292 1000) (Enclosure.sfrac Bool.false 882563 1000) hp793298))

noncomputable def hp793302 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 881292 1000) (Enclosure.sfrac Bool.false 882563 1000) hp793298)) 12445287495392789598849

noncomputable def hp793303 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 881292 1000) (Enclosure.sfrac Bool.false 882563 1000) hp793298)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 881292 1000))

noncomputable def hp793304 := @hp793302 4722366482869645213696 hp764708 hp752398 (@hp793303 Bool.true 12445287495392789598849 4722366482869645213696 hp764708 hp752398 (hd4340 (Enclosure.sfrac Bool.false 881292 1000) (Enclosure.sfrac Bool.false 882563 1000) hp793298) hd5068)

noncomputable def hp793305 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 881292 1000) (Enclosure.sfrac Bool.false 882563 1000) hp793298)) 5312939341412785396993

noncomputable def hp793306 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 881292 1000) (Enclosure.sfrac Bool.false 882563 1000) hp793298)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 882563 1000))

noncomputable def hp793307 := @hp793305 9444732965739290427392 1033231544292757913771011 hp764965 (@hp793306 Bool.false 5312939341412785396993 9444732965739290427392 1033231544292757913771011 hp764965 (hd4359 (Enclosure.sfrac Bool.false 881292 1000) (Enclosure.sfrac Bool.false 882563 1000) hp793298) hd5069)

noncomputable def hp793308 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 881292 1000) (Enclosure.sfrac Bool.false 882563 1000) hp793298) hp793300 (hp793301 (hp793304 rfl rfl rfl) (hp793307 rfl rfl rfl))

noncomputable def hp793309 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 881292 1000) (Enclosure.sfrac Bool.false 882563 1000) hp793298)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793310 := hp793309 (Enclosure.sfrac Bool.false 881292 1000) 749551 1000 881292 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793311 := hp793310 (@Eq.refl Real (Enclosure.sfrac Bool.false 881292 1000)) rfl rfl rfl rfl

noncomputable def hp793312 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 881292 1000) (Enclosure.sfrac Bool.false 882563 1000) hp793298)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793313 := @hp793312 Bool.true Bool.false 12445287495392789598849 4722366482869645213696 hp764708 hp752398 556919581 10737418240 1213 10737418240 (@hp793303 Bool.true 12445287495392789598849 4722366482869645213696 hp764708 hp752398 (hd4340 (Enclosure.sfrac Bool.false 881292 1000) (Enclosure.sfrac Bool.false 882563 1000) hp793298) hd5068)

noncomputable def hp793314 := hp793313 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793315 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 881292 1000) (Enclosure.sfrac Bool.false 882563 1000) hp793298)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793316 := hp793315 (Enclosure.sfrac Bool.false 882563 1000) 749551 1000 882563 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793317 := hp793316 (@Eq.refl Real (Enclosure.sfrac Bool.false 882563 1000)) rfl rfl rfl rfl

noncomputable def hp793318 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 881292 1000) (Enclosure.sfrac Bool.false 882563 1000) hp793298)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793319 := @hp793318 Bool.false Bool.false 5312939341412785396993 9444732965739290427392 1033231544292757913771011 hp764965 556919581 10737418240 1213 10737418240 (@hp793306 Bool.false 5312939341412785396993 9444732965739290427392 1033231544292757913771011 hp764965 (hd4359 (Enclosure.sfrac Bool.false 881292 1000) (Enclosure.sfrac Bool.false 882563 1000) hp793298) hd5069)

noncomputable def hp793320 := hp793319 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793322 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 882563 1000) (Enclosure.sfrac Bool.false 883834 1000) 882563 1000 883834 1000

noncomputable def hp793323 := hp793322 (@Eq.refl Real (Enclosure.sfrac Bool.false 882563 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 883834 1000)) rfl rfl rfl

noncomputable def hp793324 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 882563 1000) (Enclosure.sfrac Bool.false 883834 1000) hp793323)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 882563 1000) (Enclosure.sfrac Bool.false 883834 1000) hp793323))

noncomputable def hp793325 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 882563 1000) 882563 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 882563 1000)) rfl rfl

noncomputable def hp793326 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 882563 1000) (Enclosure.sfrac Bool.false 883834 1000) hp793323)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 882563 1000) (Enclosure.sfrac Bool.false 883834 1000) hp793323))

noncomputable def hp793327 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 882563 1000) (Enclosure.sfrac Bool.false 883834 1000) hp793323)) 5312939341412785396993

noncomputable def hp793328 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 882563 1000) (Enclosure.sfrac Bool.false 883834 1000) hp793323)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 882563 1000))

noncomputable def hp793329 := @hp793327 9444732965739290427392 1033231544292757913771011 hp764965 (@hp793328 Bool.false 5312939341412785396993 9444732965739290427392 1033231544292757913771011 hp764965 (hd4340 (Enclosure.sfrac Bool.false 882563 1000) (Enclosure.sfrac Bool.false 883834 1000) hp793323) hd5069)

noncomputable def hp793330 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 882563 1000) (Enclosure.sfrac Bool.false 883834 1000) hp793323)) 1022786759340051033225

noncomputable def hp793331 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 882563 1000) (Enclosure.sfrac Bool.false 883834 1000) hp793323)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 883834 1000))

noncomputable def hp793332 := @hp793330 2361183241434822606848 1149153454825974457326897 hp758057 (@hp793331 Bool.true 1022786759340051033225 2361183241434822606848 1149153454825974457326897 hp758057 (hd4359 (Enclosure.sfrac Bool.false 882563 1000) (Enclosure.sfrac Bool.false 883834 1000) hp793323) hd5070)

noncomputable def hp793333 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 882563 1000) (Enclosure.sfrac Bool.false 883834 1000) hp793323) hp793325 (hp793326 (hp793329 rfl rfl rfl) (hp793332 rfl rfl rfl))

noncomputable def hp793334 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 882563 1000) (Enclosure.sfrac Bool.false 883834 1000) hp793323)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793335 := hp793334 (Enclosure.sfrac Bool.false 882563 1000) 749551 1000 882563 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793336 := hp793335 (@Eq.refl Real (Enclosure.sfrac Bool.false 882563 1000)) rfl rfl rfl rfl

noncomputable def hp793337 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 882563 1000) (Enclosure.sfrac Bool.false 883834 1000) hp793323)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793338 := @hp793337 Bool.false Bool.false 5312939341412785396993 9444732965739290427392 1033231544292757913771011 hp764965 556919581 10737418240 1213 10737418240 (@hp793328 Bool.false 5312939341412785396993 9444732965739290427392 1033231544292757913771011 hp764965 (hd4340 (Enclosure.sfrac Bool.false 882563 1000) (Enclosure.sfrac Bool.false 883834 1000) hp793323) hd5069)

noncomputable def hp793339 := hp793338 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793340 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 882563 1000) (Enclosure.sfrac Bool.false 883834 1000) hp793323)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793341 := hp793340 (Enclosure.sfrac Bool.false 883834 1000) 749551 1000 883834 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793342 := hp793341 (@Eq.refl Real (Enclosure.sfrac Bool.false 883834 1000)) rfl rfl rfl rfl

noncomputable def hp793343 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 882563 1000) (Enclosure.sfrac Bool.false 883834 1000) hp793323)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793344 := @hp793343 Bool.true Bool.false 1022786759340051033225 2361183241434822606848 1149153454825974457326897 hp758057 556919581 10737418240 1213 10737418240 (@hp793331 Bool.true 1022786759340051033225 2361183241434822606848 1149153454825974457326897 hp758057 (hd4359 (Enclosure.sfrac Bool.false 882563 1000) (Enclosure.sfrac Bool.false 883834 1000) hp793323) hd5070)

noncomputable def hp793345 := hp793344 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793347 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 883834 1000) (Enclosure.sfrac Bool.false 885104 1000) 883834 1000 885104 1000

noncomputable def hp793348 := hp793347 (@Eq.refl Real (Enclosure.sfrac Bool.false 883834 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 885104 1000)) rfl rfl rfl

noncomputable def hp793349 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 883834 1000) (Enclosure.sfrac Bool.false 885104 1000) hp793348)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 883834 1000) (Enclosure.sfrac Bool.false 885104 1000) hp793348))

noncomputable def hp793350 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 883834 1000) 883834 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 883834 1000)) rfl rfl

noncomputable def hp793351 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 883834 1000) (Enclosure.sfrac Bool.false 885104 1000) hp793348)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 883834 1000) (Enclosure.sfrac Bool.false 885104 1000) hp793348))

noncomputable def hp793352 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 883834 1000) (Enclosure.sfrac Bool.false 885104 1000) hp793348)) 1022786759340051033225

noncomputable def hp793353 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 883834 1000) (Enclosure.sfrac Bool.false 885104 1000) hp793348)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 883834 1000))

noncomputable def hp793354 := @hp793352 2361183241434822606848 1149153454825974457326897 hp758057 (@hp793353 Bool.true 1022786759340051033225 2361183241434822606848 1149153454825974457326897 hp758057 (hd4340 (Enclosure.sfrac Bool.false 883834 1000) (Enclosure.sfrac Bool.false 885104 1000) hp793348) hd5070)

noncomputable def hp793355 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 883834 1000) (Enclosure.sfrac Bool.false 885104 1000) hp793348)) 691498028078457515615

noncomputable def hp793356 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 883834 1000) (Enclosure.sfrac Bool.false 885104 1000) hp793348)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 885104 1000))

noncomputable def hp793357 := @hp793355 1180591620717411303424 hp765472 hp738860 (@hp793356 Bool.false 691498028078457515615 1180591620717411303424 hp765472 hp738860 (hd4359 (Enclosure.sfrac Bool.false 883834 1000) (Enclosure.sfrac Bool.false 885104 1000) hp793348) hd5071)

noncomputable def hp793358 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 883834 1000) (Enclosure.sfrac Bool.false 885104 1000) hp793348) hp793350 (hp793351 (hp793354 rfl rfl rfl) (hp793357 rfl rfl rfl))

noncomputable def hp793359 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 883834 1000) (Enclosure.sfrac Bool.false 885104 1000) hp793348)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793360 := hp793359 (Enclosure.sfrac Bool.false 883834 1000) 749551 1000 883834 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793361 := hp793360 (@Eq.refl Real (Enclosure.sfrac Bool.false 883834 1000)) rfl rfl rfl rfl

noncomputable def hp793362 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 883834 1000) (Enclosure.sfrac Bool.false 885104 1000) hp793348)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793363 := @hp793362 Bool.true Bool.false 1022786759340051033225 2361183241434822606848 1149153454825974457326897 hp758057 556919581 10737418240 1213 10737418240 (@hp793353 Bool.true 1022786759340051033225 2361183241434822606848 1149153454825974457326897 hp758057 (hd4340 (Enclosure.sfrac Bool.false 883834 1000) (Enclosure.sfrac Bool.false 885104 1000) hp793348) hd5070)

noncomputable def hp793364 := hp793363 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793365 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 883834 1000) (Enclosure.sfrac Bool.false 885104 1000) hp793348)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793366 := hp793365 (Enclosure.sfrac Bool.false 885104 1000) 749551 1000 885104 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793367 := hp793366 (@Eq.refl Real (Enclosure.sfrac Bool.false 885104 1000)) rfl rfl rfl rfl

noncomputable def hp793368 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 883834 1000) (Enclosure.sfrac Bool.false 885104 1000) hp793348)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793369 := @hp793368 Bool.false Bool.false 691498028078457515615 1180591620717411303424 hp765472 hp738860 556919581 10737418240 1213 10737418240 (@hp793356 Bool.false 691498028078457515615 1180591620717411303424 hp765472 hp738860 (hd4359 (Enclosure.sfrac Bool.false 883834 1000) (Enclosure.sfrac Bool.false 885104 1000) hp793348) hd5071)

noncomputable def hp793370 := hp793369 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793372 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 885104 1000) (Enclosure.sfrac Bool.false 886373 1000) 885104 1000 886373 1000

noncomputable def hp793373 := hp793372 (@Eq.refl Real (Enclosure.sfrac Bool.false 885104 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 886373 1000)) rfl rfl rfl

noncomputable def hp793374 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 885104 1000) (Enclosure.sfrac Bool.false 886373 1000) hp793373)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 885104 1000) (Enclosure.sfrac Bool.false 886373 1000) hp793373))

noncomputable def hp793375 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 885104 1000) 885104 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 885104 1000)) rfl rfl

noncomputable def hp793376 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 885104 1000) (Enclosure.sfrac Bool.false 886373 1000) hp793373)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 885104 1000) (Enclosure.sfrac Bool.false 886373 1000) hp793373))

noncomputable def hp793377 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 885104 1000) (Enclosure.sfrac Bool.false 886373 1000) hp793373)) 691498028078457515615

noncomputable def hp793378 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 885104 1000) (Enclosure.sfrac Bool.false 886373 1000) hp793373)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 885104 1000))

noncomputable def hp793379 := @hp793377 1180591620717411303424 hp765472 hp738860 (@hp793378 Bool.false 691498028078457515615 1180591620717411303424 hp765472 hp738860 (hd4340 (Enclosure.sfrac Bool.false 885104 1000) (Enclosure.sfrac Bool.false 886373 1000) hp793373) hd5071)

noncomputable def hp793380 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 885104 1000) (Enclosure.sfrac Bool.false 886373 1000) hp793373)) 13962957787815189248459

noncomputable def hp793381 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 885104 1000) (Enclosure.sfrac Bool.false 886373 1000) hp793373)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 886373 1000))

noncomputable def hp793382 := @hp793380 4722366482869645213696 94227644885428757859029 hp765723 (@hp793381 Bool.true 13962957787815189248459 4722366482869645213696 94227644885428757859029 hp765723 (hd4359 (Enclosure.sfrac Bool.false 885104 1000) (Enclosure.sfrac Bool.false 886373 1000) hp793373) hd5072)

noncomputable def hp793383 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 885104 1000) (Enclosure.sfrac Bool.false 886373 1000) hp793373) hp793375 (hp793376 (hp793379 rfl rfl rfl) (hp793382 rfl rfl rfl))

noncomputable def hp793384 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 885104 1000) (Enclosure.sfrac Bool.false 886373 1000) hp793373)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793385 := hp793384 (Enclosure.sfrac Bool.false 885104 1000) 749551 1000 885104 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793386 := hp793385 (@Eq.refl Real (Enclosure.sfrac Bool.false 885104 1000)) rfl rfl rfl rfl

noncomputable def hp793387 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 885104 1000) (Enclosure.sfrac Bool.false 886373 1000) hp793373)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793388 := @hp793387 Bool.false Bool.false 691498028078457515615 1180591620717411303424 hp765472 hp738860 556919581 10737418240 1213 10737418240 (@hp793378 Bool.false 691498028078457515615 1180591620717411303424 hp765472 hp738860 (hd4340 (Enclosure.sfrac Bool.false 885104 1000) (Enclosure.sfrac Bool.false 886373 1000) hp793373) hd5071)

noncomputable def hp793389 := hp793388 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793390 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 885104 1000) (Enclosure.sfrac Bool.false 886373 1000) hp793373)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793391 := hp793390 (Enclosure.sfrac Bool.false 886373 1000) 749551 1000 886373 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793392 := hp793391 (@Eq.refl Real (Enclosure.sfrac Bool.false 886373 1000)) rfl rfl rfl rfl

noncomputable def hp793393 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 885104 1000) (Enclosure.sfrac Bool.false 886373 1000) hp793373)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793394 := @hp793393 Bool.true Bool.false 13962957787815189248459 4722366482869645213696 94227644885428757859029 hp765723 556919581 10737418240 1213 10737418240 (@hp793381 Bool.true 13962957787815189248459 4722366482869645213696 94227644885428757859029 hp765723 (hd4359 (Enclosure.sfrac Bool.false 885104 1000) (Enclosure.sfrac Bool.false 886373 1000) hp793373) hd5072)

noncomputable def hp793395 := hp793394 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793397 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 886373 1000) (Enclosure.sfrac Bool.false 887643 1000) 886373 1000 887643 1000

noncomputable def hp793398 := hp793397 (@Eq.refl Real (Enclosure.sfrac Bool.false 886373 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 887643 1000)) rfl rfl rfl

noncomputable def hp793399 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 886373 1000) (Enclosure.sfrac Bool.false 887643 1000) hp793398)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 886373 1000) (Enclosure.sfrac Bool.false 887643 1000) hp793398))

noncomputable def hp793400 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 886373 1000) 886373 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 886373 1000)) rfl rfl

noncomputable def hp793401 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 886373 1000) (Enclosure.sfrac Bool.false 887643 1000) hp793398)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 886373 1000) (Enclosure.sfrac Bool.false 887643 1000) hp793398))

noncomputable def hp793402 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 886373 1000) (Enclosure.sfrac Bool.false 887643 1000) hp793398)) 13962957787815189248459

noncomputable def hp793403 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 886373 1000) (Enclosure.sfrac Bool.false 887643 1000) hp793398)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 886373 1000))

noncomputable def hp793404 := @hp793402 4722366482869645213696 94227644885428757859029 hp765723 (@hp793403 Bool.true 13962957787815189248459 4722366482869645213696 94227644885428757859029 hp765723 (hd4340 (Enclosure.sfrac Bool.false 886373 1000) (Enclosure.sfrac Bool.false 887643 1000) hp793398) hd5072)

noncomputable def hp793405 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 886373 1000) (Enclosure.sfrac Bool.false 887643 1000) hp793398)) 40714850364486614389619

noncomputable def hp793406 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 886373 1000) (Enclosure.sfrac Bool.false 887643 1000) hp793398)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 887643 1000))

noncomputable def hp793407 := @hp793405 9444732965739290427392 576512469283444201165847 hp762191 (@hp793406 Bool.false 40714850364486614389619 9444732965739290427392 576512469283444201165847 hp762191 (hd4359 (Enclosure.sfrac Bool.false 886373 1000) (Enclosure.sfrac Bool.false 887643 1000) hp793398) hd5073)

noncomputable def hp793408 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 886373 1000) (Enclosure.sfrac Bool.false 887643 1000) hp793398) hp793400 (hp793401 (hp793404 rfl rfl rfl) (hp793407 rfl rfl rfl))

noncomputable def hp793409 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 886373 1000) (Enclosure.sfrac Bool.false 887643 1000) hp793398)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793410 := hp793409 (Enclosure.sfrac Bool.false 886373 1000) 749551 1000 886373 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793411 := hp793410 (@Eq.refl Real (Enclosure.sfrac Bool.false 886373 1000)) rfl rfl rfl rfl

noncomputable def hp793412 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 886373 1000) (Enclosure.sfrac Bool.false 887643 1000) hp793398)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793413 := @hp793412 Bool.true Bool.false 13962957787815189248459 4722366482869645213696 94227644885428757859029 hp765723 556919581 10737418240 1213 10737418240 (@hp793403 Bool.true 13962957787815189248459 4722366482869645213696 94227644885428757859029 hp765723 (hd4340 (Enclosure.sfrac Bool.false 886373 1000) (Enclosure.sfrac Bool.false 887643 1000) hp793398) hd5072)

noncomputable def hp793414 := hp793413 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793415 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 886373 1000) (Enclosure.sfrac Bool.false 887643 1000) hp793398)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793416 := hp793415 (Enclosure.sfrac Bool.false 887643 1000) 749551 1000 887643 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793417 := hp793416 (@Eq.refl Real (Enclosure.sfrac Bool.false 887643 1000)) rfl rfl rfl rfl

noncomputable def hp793418 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 886373 1000) (Enclosure.sfrac Bool.false 887643 1000) hp793398)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793419 := @hp793418 Bool.false Bool.false 40714850364486614389619 9444732965739290427392 576512469283444201165847 hp762191 556919581 10737418240 1213 10737418240 (@hp793406 Bool.false 40714850364486614389619 9444732965739290427392 576512469283444201165847 hp762191 (hd4359 (Enclosure.sfrac Bool.false 886373 1000) (Enclosure.sfrac Bool.false 887643 1000) hp793398) hd5073)

noncomputable def hp793420 := hp793419 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793422 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 887643 1000) (Enclosure.sfrac Bool.false 888912 1000) 887643 1000 888912 1000

noncomputable def hp793423 := hp793422 (@Eq.refl Real (Enclosure.sfrac Bool.false 887643 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 888912 1000)) rfl rfl rfl

noncomputable def hp793424 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 887643 1000) (Enclosure.sfrac Bool.false 888912 1000) hp793423)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 887643 1000) (Enclosure.sfrac Bool.false 888912 1000) hp793423))

noncomputable def hp793425 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 887643 1000) 887643 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 887643 1000)) rfl rfl

noncomputable def hp793426 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 887643 1000) (Enclosure.sfrac Bool.false 888912 1000) hp793423)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 887643 1000) (Enclosure.sfrac Bool.false 888912 1000) hp793423))

noncomputable def hp793427 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 887643 1000) (Enclosure.sfrac Bool.false 888912 1000) hp793423)) 40714850364486614389619

noncomputable def hp793428 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 887643 1000) (Enclosure.sfrac Bool.false 888912 1000) hp793423)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 887643 1000))

noncomputable def hp793429 := @hp793427 9444732965739290427392 576512469283444201165847 hp762191 (@hp793428 Bool.false 40714850364486614389619 9444732965739290427392 576512469283444201165847 hp762191 (hd4340 (Enclosure.sfrac Bool.false 887643 1000) (Enclosure.sfrac Bool.false 888912 1000) hp793423) hd5073)

noncomputable def hp793430 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 887643 1000) (Enclosure.sfrac Bool.false 888912 1000) hp793423)) 20441737308150466552939

noncomputable def hp793431 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 887643 1000) (Enclosure.sfrac Bool.false 888912 1000) hp793423)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 888912 1000))

noncomputable def hp793432 := @hp793430 9444732965739290427392 157432979705853290550803 hp766228 (@hp793431 Bool.true 20441737308150466552939 9444732965739290427392 157432979705853290550803 hp766228 (hd4359 (Enclosure.sfrac Bool.false 887643 1000) (Enclosure.sfrac Bool.false 888912 1000) hp793423) hd5074)

noncomputable def hp793433 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 887643 1000) (Enclosure.sfrac Bool.false 888912 1000) hp793423) hp793425 (hp793426 (hp793429 rfl rfl rfl) (hp793432 rfl rfl rfl))

noncomputable def hp793434 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 887643 1000) (Enclosure.sfrac Bool.false 888912 1000) hp793423)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793435 := hp793434 (Enclosure.sfrac Bool.false 887643 1000) 749551 1000 887643 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793436 := hp793435 (@Eq.refl Real (Enclosure.sfrac Bool.false 887643 1000)) rfl rfl rfl rfl

noncomputable def hp793437 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 887643 1000) (Enclosure.sfrac Bool.false 888912 1000) hp793423)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793438 := @hp793437 Bool.false Bool.false 40714850364486614389619 9444732965739290427392 576512469283444201165847 hp762191 556919581 10737418240 1213 10737418240 (@hp793428 Bool.false 40714850364486614389619 9444732965739290427392 576512469283444201165847 hp762191 (hd4340 (Enclosure.sfrac Bool.false 887643 1000) (Enclosure.sfrac Bool.false 888912 1000) hp793423) hd5073)

noncomputable def hp793439 := hp793438 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793440 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 887643 1000) (Enclosure.sfrac Bool.false 888912 1000) hp793423)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793441 := hp793440 (Enclosure.sfrac Bool.false 888912 1000) 749551 1000 888912 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793442 := hp793441 (@Eq.refl Real (Enclosure.sfrac Bool.false 888912 1000)) rfl rfl rfl rfl

noncomputable def hp793443 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 887643 1000) (Enclosure.sfrac Bool.false 888912 1000) hp793423)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793444 := @hp793443 Bool.true Bool.false 20441737308150466552939 9444732965739290427392 157432979705853290550803 hp766228 556919581 10737418240 1213 10737418240 (@hp793431 Bool.true 20441737308150466552939 9444732965739290427392 157432979705853290550803 hp766228 (hd4359 (Enclosure.sfrac Bool.false 887643 1000) (Enclosure.sfrac Bool.false 888912 1000) hp793423) hd5074)

noncomputable def hp793445 := hp793444 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793447 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 888912 1000) (Enclosure.sfrac Bool.false 890180 1000) 888912 1000 890180 1000

noncomputable def hp793448 := hp793447 (@Eq.refl Real (Enclosure.sfrac Bool.false 888912 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 890180 1000)) rfl rfl rfl

noncomputable def hp793449 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 888912 1000) (Enclosure.sfrac Bool.false 890180 1000) hp793448)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 888912 1000) (Enclosure.sfrac Bool.false 890180 1000) hp793448))

noncomputable def hp793450 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 888912 1000) 888912 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 888912 1000)) rfl rfl

noncomputable def hp793451 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 888912 1000) (Enclosure.sfrac Bool.false 890180 1000) hp793448)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 888912 1000) (Enclosure.sfrac Bool.false 890180 1000) hp793448))

noncomputable def hp793452 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 888912 1000) (Enclosure.sfrac Bool.false 890180 1000) hp793448)) 20441737308150466552939

noncomputable def hp793453 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 888912 1000) (Enclosure.sfrac Bool.false 890180 1000) hp793448)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 888912 1000))

noncomputable def hp793454 := @hp793452 9444732965739290427392 157432979705853290550803 hp766228 (@hp793453 Bool.true 20441737308150466552939 9444732965739290427392 157432979705853290550803 hp766228 (hd4340 (Enclosure.sfrac Bool.false 888912 1000) (Enclosure.sfrac Bool.false 890180 1000) hp793448) hd5074)

noncomputable def hp793455 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 888912 1000) (Enclosure.sfrac Bool.false 890180 1000) hp793448)) 13887692940129180196765

noncomputable def hp793456 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 888912 1000) (Enclosure.sfrac Bool.false 890180 1000) hp793448)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 890180 1000))

noncomputable def hp793457 := @hp793455 9444732965739290427392 hp766477 hp743845 (@hp793456 Bool.false 13887692940129180196765 9444732965739290427392 hp766477 hp743845 (hd4359 (Enclosure.sfrac Bool.false 888912 1000) (Enclosure.sfrac Bool.false 890180 1000) hp793448) hd5075)

noncomputable def hp793458 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 888912 1000) (Enclosure.sfrac Bool.false 890180 1000) hp793448) hp793450 (hp793451 (hp793454 rfl rfl rfl) (hp793457 rfl rfl rfl))

noncomputable def hp793459 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 888912 1000) (Enclosure.sfrac Bool.false 890180 1000) hp793448)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793460 := hp793459 (Enclosure.sfrac Bool.false 888912 1000) 749551 1000 888912 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793461 := hp793460 (@Eq.refl Real (Enclosure.sfrac Bool.false 888912 1000)) rfl rfl rfl rfl

noncomputable def hp793462 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 888912 1000) (Enclosure.sfrac Bool.false 890180 1000) hp793448)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793463 := @hp793462 Bool.true Bool.false 20441737308150466552939 9444732965739290427392 157432979705853290550803 hp766228 556919581 10737418240 1213 10737418240 (@hp793453 Bool.true 20441737308150466552939 9444732965739290427392 157432979705853290550803 hp766228 (hd4340 (Enclosure.sfrac Bool.false 888912 1000) (Enclosure.sfrac Bool.false 890180 1000) hp793448) hd5074)

noncomputable def hp793464 := hp793463 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793465 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 888912 1000) (Enclosure.sfrac Bool.false 890180 1000) hp793448)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793466 := hp793465 (Enclosure.sfrac Bool.false 890180 1000) 749551 1000 890180 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793467 := hp793466 (@Eq.refl Real (Enclosure.sfrac Bool.false 890180 1000)) rfl rfl rfl rfl

noncomputable def hp793468 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 888912 1000) (Enclosure.sfrac Bool.false 890180 1000) hp793448)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793469 := @hp793468 Bool.false Bool.false 13887692940129180196765 9444732965739290427392 hp766477 hp743845 556919581 10737418240 1213 10737418240 (@hp793456 Bool.false 13887692940129180196765 9444732965739290427392 hp766477 hp743845 (hd4359 (Enclosure.sfrac Bool.false 888912 1000) (Enclosure.sfrac Bool.false 890180 1000) hp793448) hd5075)

noncomputable def hp793470 := hp793469 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793472 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 890180 1000) (Enclosure.sfrac Bool.false 891448 1000) 890180 1000 891448 1000

noncomputable def hp793473 := hp793472 (@Eq.refl Real (Enclosure.sfrac Bool.false 890180 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 891448 1000)) rfl rfl rfl

noncomputable def hp793474 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 890180 1000) (Enclosure.sfrac Bool.false 891448 1000) hp793473)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 890180 1000) (Enclosure.sfrac Bool.false 891448 1000) hp793473))

noncomputable def hp793475 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 890180 1000) 890180 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 890180 1000)) rfl rfl

noncomputable def hp793476 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 890180 1000) (Enclosure.sfrac Bool.false 891448 1000) hp793473)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 890180 1000) (Enclosure.sfrac Bool.false 891448 1000) hp793473))

noncomputable def hp793477 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 890180 1000) (Enclosure.sfrac Bool.false 891448 1000) hp793473)) 13887692940129180196765

noncomputable def hp793478 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 890180 1000) (Enclosure.sfrac Bool.false 891448 1000) hp793473)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 890180 1000))

noncomputable def hp793479 := @hp793477 9444732965739290427392 hp766477 hp743845 (@hp793478 Bool.false 13887692940129180196765 9444732965739290427392 hp766477 hp743845 (hd4340 (Enclosure.sfrac Bool.false 890180 1000) (Enclosure.sfrac Bool.false 891448 1000) hp793473) hd5075)

noncomputable def hp793480 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 890180 1000) (Enclosure.sfrac Bool.false 891448 1000) hp793473)) 43591284853012421774541

noncomputable def hp793481 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 890180 1000) (Enclosure.sfrac Bool.false 891448 1000) hp793473)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 891448 1000))

noncomputable def hp793482 := @hp793480 18889465931478580854784 hp766732 hp756249 (@hp793481 Bool.true 43591284853012421774541 18889465931478580854784 hp766732 hp756249 (hd4359 (Enclosure.sfrac Bool.false 890180 1000) (Enclosure.sfrac Bool.false 891448 1000) hp793473) hd5076)

noncomputable def hp793483 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 890180 1000) (Enclosure.sfrac Bool.false 891448 1000) hp793473) hp793475 (hp793476 (hp793479 rfl rfl rfl) (hp793482 rfl rfl rfl))

noncomputable def hp793484 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 890180 1000) (Enclosure.sfrac Bool.false 891448 1000) hp793473)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793485 := hp793484 (Enclosure.sfrac Bool.false 890180 1000) 749551 1000 890180 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793486 := hp793485 (@Eq.refl Real (Enclosure.sfrac Bool.false 890180 1000)) rfl rfl rfl rfl

noncomputable def hp793487 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 890180 1000) (Enclosure.sfrac Bool.false 891448 1000) hp793473)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793488 := @hp793487 Bool.false Bool.false 13887692940129180196765 9444732965739290427392 hp766477 hp743845 556919581 10737418240 1213 10737418240 (@hp793478 Bool.false 13887692940129180196765 9444732965739290427392 hp766477 hp743845 (hd4340 (Enclosure.sfrac Bool.false 890180 1000) (Enclosure.sfrac Bool.false 891448 1000) hp793473) hd5075)

noncomputable def hp793489 := hp793488 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793490 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 890180 1000) (Enclosure.sfrac Bool.false 891448 1000) hp793473)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793491 := hp793490 (Enclosure.sfrac Bool.false 891448 1000) 749551 1000 891448 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793492 := hp793491 (@Eq.refl Real (Enclosure.sfrac Bool.false 891448 1000)) rfl rfl rfl rfl

noncomputable def hp793493 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 890180 1000) (Enclosure.sfrac Bool.false 891448 1000) hp793473)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793494 := @hp793493 Bool.true Bool.false 43591284853012421774541 18889465931478580854784 hp766732 hp756249 556919581 10737418240 1213 10737418240 (@hp793481 Bool.true 43591284853012421774541 18889465931478580854784 hp766732 hp756249 (hd4359 (Enclosure.sfrac Bool.false 890180 1000) (Enclosure.sfrac Bool.false 891448 1000) hp793473) hd5076)

noncomputable def hp793495 := hp793494 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl
open Zeta.Certificates
noncomputable def certificatePairs : List (Σ' I : ZIntervalRS, I.Certified) := [(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 876205 1000) (Enclosure.sfrac Bool.false 877478 1000) hp793198) (hp793199 (hp793208 (hp793211 (hp793214 rfl rfl)) (hp793217 (hp793220 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 877478 1000) (Enclosure.sfrac Bool.false 878750 1000) hp793223) (hp793224 (hp793233 (hp793236 (hp793239 rfl rfl)) (hp793242 (hp793245 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 878750 1000) (Enclosure.sfrac Bool.false 880021 1000) hp793248) (hp793249 (hp793258 (hp793261 (hp793264 rfl rfl)) (hp793267 (hp793270 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 880021 1000) (Enclosure.sfrac Bool.false 881292 1000) hp793273) (hp793274 (hp793283 (hp793286 (hp793289 rfl rfl)) (hp793292 (hp793295 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 881292 1000) (Enclosure.sfrac Bool.false 882563 1000) hp793298) (hp793299 (hp793308 (hp793311 (hp793314 rfl rfl)) (hp793317 (hp793320 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 882563 1000) (Enclosure.sfrac Bool.false 883834 1000) hp793323) (hp793324 (hp793333 (hp793336 (hp793339 rfl rfl)) (hp793342 (hp793345 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 883834 1000) (Enclosure.sfrac Bool.false 885104 1000) hp793348) (hp793349 (hp793358 (hp793361 (hp793364 rfl rfl)) (hp793367 (hp793370 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 885104 1000) (Enclosure.sfrac Bool.false 886373 1000) hp793373) (hp793374 (hp793383 (hp793386 (hp793389 rfl rfl)) (hp793392 (hp793395 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 886373 1000) (Enclosure.sfrac Bool.false 887643 1000) hp793398) (hp793399 (hp793408 (hp793411 (hp793414 rfl rfl)) (hp793417 (hp793420 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 887643 1000) (Enclosure.sfrac Bool.false 888912 1000) hp793423) (hp793424 (hp793433 (hp793436 (hp793439 rfl rfl)) (hp793442 (hp793445 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 888912 1000) (Enclosure.sfrac Bool.false 890180 1000) hp793448) (hp793449 (hp793458 (hp793461 (hp793464 rfl rfl)) (hp793467 (hp793470 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 890180 1000) (Enclosure.sfrac Bool.false 891448 1000) hp793473) (hp793474 (hp793483 (hp793486 (hp793489 rfl rfl)) (hp793492 (hp793495 rfl rfl)))))]

theorem solution : Zeta.Certificates.BatchSpec 12 876205 1000 891448 1000 :=
  ⟨CertifiedZeroIntervals.ofCertifiedRS certificatePairs (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.singleton _)))))))))))), rfl, rfl, rfl⟩
#print axioms solution
