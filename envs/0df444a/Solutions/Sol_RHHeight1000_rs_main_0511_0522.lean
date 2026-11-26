-- Prove2me | solution 1 for RHHeight1000.rs_main_0511_0522
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T10:41:27.35729+00:00
-- url     : https://prove2.me/submissions/5b710bce-0067-42f4-9848-3eef4b7726a1

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

noncomputable def hp630709 := nat_lit 2475880078570760549798248448

noncomputable def hp630724 := nat_lit 988643523323402220304136834155207460536120982503085435781120

noncomputable def hp630727 := nat_lit 44488958549553099913686157536984335724125444212638844610150400

theorem hd4359 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 a b h))

noncomputable def hp631348 := nat_lit 253092741970790968397859029543733109897246971520789871559966720

noncomputable def hp631351 := nat_lit 11389173388685593577903656329467989945376113718435544220198502400

noncomputable def hp631536 := nat_lit 118842243771396506390315925504

noncomputable def hp631537 := nat_lit 1782633656570947595854738882560

noncomputable def hp632130 := nat_lit 3861888762982039923063034508418779142719222587902677483520

noncomputable def hp632133 := nat_lit 173784994334191796537836552878845061422365016455620486758400

noncomputable def hp642702 := nat_lit 3570415896635346974072005805030179415937144689025665314440334861177556999349704385084003346650664335197480996044800

noncomputable def hp642705 := nat_lit 124964556382237144092520203176056279557800064115898286005411720141214494977239653477940117132773251731911834861568000

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

noncomputable def hp740177 := nat_lit 21759806992472160846509436431027924547665573599712653161483140986990306751823661669370177199848368120331884066839754328502985489716814125465600

noncomputable def hp740180 := nat_lit 1980142436314966637032358715223541133837567197573851437694965829816117914415953211912686125186201498950201450082417643893771679564230085417369600

noncomputable def hp740271 := @Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (Enclosure.sfrac Bool.true 1 1) Bool.true 1

noncomputable def hp741590 := nat_lit 17142190332816812125716480000

noncomputable def hp742094 := nat_lit 12856642749612609094287360000

noncomputable def hp742826 := nat_lit 3868562622766813359059763200000000000000

noncomputable def hp743344 := nat_lit 5142657099845043637714944000

noncomputable def hp743845 := nat_lit 2857031722136135354286080000

noncomputable def hp746784 := nat_lit 77919046967349146025984000

noncomputable def hp749778 := nat_lit 42817430781178796431748579083484854091482398720

noncomputable def hp749779 := nat_lit 299722015468251575022240053584393978640376791040

noncomputable def hp751876 := nat_lit 428554758320420303142912000

noncomputable def hp755229 := nat_lit 102853141996900872754298880000

noncomputable def hp756249 := nat_lit 1714219033281681212571648000

noncomputable def hp763445 := nat_lit 68568761331267248502865920

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

noncomputable def hp766987 := nat_lit 2318029733919198565254227

noncomputable def hp766988 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 892716 1000)) Bool.false 22990705254852030015421 37778931862957161709568 hp766987

noncomputable def hp766989 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 892716 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 892716 1000)) Bool.false 22990705254852030015421 37778931862957161709568

noncomputable def hp766990 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 892716 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp766991 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp766990 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp766992 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 892716 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp766993 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 892716 1000)) (Enclosure.sfrac Bool.false 892716 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp766991 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp766994 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 892716 1000)) hp766993 Bool.false 22990705254852030015421 37778931862957161709568

noncomputable def hp766995 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 892716 1000) 892716 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 892716 1000)) rfl

noncomputable def hp766996 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 892716 1000)) (Enclosure.sfrac Bool.false 892716 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp766991 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp766997 := nat_lit 6171520448847800889715223166976

noncomputable def hp766998 := @hp766996 105184547 268435456 108303 134217728 8187296296279079299005 37778931862957161709568 12633038465451447174227 hp743845 hp766997 22990705254852030015421 37778931862957161709568

noncomputable def hp766999 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 892716 1000)) (Enclosure.sfrac Bool.false 892716 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 892716 1000)) (Enclosure.sfrac Bool.false 892716 1000) 11)

noncomputable def hp767000 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 892716 1000)) (Enclosure.sfrac Bool.false 892716 1000) 11) hp766999

noncomputable def hp767001 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 892716 1000)) (Enclosure.sfrac Bool.false 892716 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 892716 1000)) (Enclosure.sfrac Bool.false 892716 1000) 11)

noncomputable def hp767002 := @hp767001 105184547 536870912 216606 536870912 105184547 536870912 216606 536870912 112941047352393728 105184547 268435456

noncomputable def hp767003 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 892716 1000)) (Enclosure.sfrac Bool.false 892716 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp767004 := hp767003 BSN.quadSignNeg 9 10 11 892716 1000 184 238 536870912 268435456 9007199254740992

noncomputable def hp767005 := hp767004 Bool.false 947885481081 4067 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp767006 := hp767005 Bool.false 63233187 185950 Bool.true 512030793 Bool.true 652649221 28296951008113761 1 Bool.false 310656941

noncomputable def hp767007 := hp767006 Bool.false Bool.false 186682848 Bool.true Bool.false 105184547 216606 BSN.abs_quadSignPos (BSN.cos_quad_nat0 184 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 310656941 536870912) BSN.abs_quadSignNeg

noncomputable def hp767008 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 892716 1000)) (Enclosure.sfrac Bool.false 892716 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp767009 := hp767008 BSN.quadSignPos 7 8 9 892716 1000 57 124 536870912 268435456 9007199254740992

noncomputable def hp767010 := hp767009 Bool.false 947885481081 4067 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp767011 := hp767010 Bool.false 168816177 151864 Bool.true 666283528 Bool.true 614434503 28296951008113761 1 Bool.false 507946692

noncomputable def hp767012 := hp767011 Bool.true Bool.false 222009874 Bool.false Bool.false 63233187 185950 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 507946692 536870912) BSN.abs_quadSignPos

noncomputable def hp767013 := hp767008 BSN.quadSignNeg 5 6 7 892716 1000 105 18 536870912 268435456 9007199254740992

noncomputable def hp767014 := hp767013 Bool.false 947885481081 4067 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp767015 := hp767014 Bool.false 565460653 112852 Bool.false 595038139 Bool.false 83140072 28296951008113761 1 Bool.false 480478797

noncomputable def hp767016 := hp767015 Bool.true Bool.false 530446212 Bool.true Bool.false 168816177 151864 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 105 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 480478797 536870912) BSN.abs_quadSignNeg

noncomputable def hp767017 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 892716 1000)) (Enclosure.sfrac Bool.false 892716 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp767018 := hp767017 BSN.quadSignNeg 3 4 5 892716 1000 336 209 536870912 268435456 9007199254740992

noncomputable def hp767019 := hp767018 Bool.false 947885481081 4067 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp767020 := hp767019 Bool.false 420033181 66700 Bool.false 117893567 Bool.false 272146302 28296951008113761 1 Bool.false 523978491

noncomputable def hp767021 := hp767020 Bool.false Bool.false 260640025 Bool.true Bool.false 565460653 112852 BSN.abs_quadSignPos (BSN.cos_quad_nat0 336 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 523978491 536870912) BSN.abs_quadSignNeg

noncomputable def hp767022 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 892716 1000)) (Enclosure.sfrac Bool.false 892716 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp767023 := hp767022 BSN.quadSignPos 1 2 3 892716 1000 730 499 536870912 268435456 9007199254740992

noncomputable def hp767024 := hp767023 Bool.false 947885481081 4067 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp767025 := hp767024 Bool.false 536870744 4122 Bool.false 58745094 Bool.false 535886988 28296951008113761 1 Bool.false 533660136

noncomputable def hp767026 := hp767025 Bool.true Bool.false 451228920 Bool.false Bool.false 420033181 66700 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 730 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 533660136 536870912) BSN.abs_quadSignPos

noncomputable def hp767027 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 892716 1000)) (Enclosure.sfrac Bool.false 892716 1000) 1) Bool.false

noncomputable def hp767028 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 892716 1000)) (Enclosure.sfrac Bool.false 892716 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 892716 1000)))

noncomputable def hp767029 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 892716 1000))) Bool.false 67108843 67108864

noncomputable def hp767030 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 892716 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 118485685135) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 118485685135 67108864

noncomputable def hp767031 := nat_lit 24564399543750653773096031154171744567252371110525401

noncomputable def hp767032 := nat_lit 13912979836701087940455181446597960360410900070400

noncomputable def hp767033 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 892716 1000)) Bool.false hp767031 hp767032 33780335074883385517

noncomputable def hp767034 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 892716 4000) (Real.log (Enclosure.sfrac Bool.false 3187768426624 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1785432))))))

noncomputable def hp767035 := nat_lit 272149897865145990911952088596480000

noncomputable def hp767036 := nat_lit 1457715622735090920050822117125867438080

noncomputable def hp767037 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 892716 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp767034 (Enclosure.sfrac Bool.false 892716 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 892716 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp767035 hp767036)) Bool.false

noncomputable def hp767038 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 892716 1000) 892716 1000 3187768426624 16000000 1785432

noncomputable def hp767039 := hp767038 4000 2000 hp767035 hp767036 (@Eq.refl Real (Enclosure.sfrac Bool.false 892716 1000)) rfl rfl rfl rfl

noncomputable def hp767040 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp767034 (Enclosure.sfrac Bool.false 892716 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 892716 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp767035 hp767036) 1590288114097427891673 900719925474099200

noncomputable def hp767041 := nat_lit 2318187583438909697770014956716511210821610006063125459107840

noncomputable def hp767042 := @hp767040 33780335074883385517 hp739140 hp767035 hp767036 0 1 hp767041 hp767031 hp767032 33780335074883385517 hp739140

noncomputable def hp767043 := @Enclosure.Real.IsNear.subLit_ff_p (hp767034 (Enclosure.sfrac Bool.false 892716 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 892716 2000) (Real.log Real.pi)) 10252596867691246247229 4503599627370496000 351842703981119 136125000000000000000

noncomputable def hp767044 := nat_lit 133403035962225963915112611840000

noncomputable def hp767045 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 892716 4000) (Real.log (Enclosure.sfrac Bool.false 3187768426624 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1785432))))))

noncomputable def hp767046 := @hp767045 (Enclosure.sfrac Bool.false 892716 2000) 12262814590165086100797 4503599627370496000 351842703981119 136125000000000000000 892716 2000 0

noncomputable def hp767047 := nat_lit 20505193735382492494458000

noncomputable def hp767048 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 892716 4000) (Real.log (Enclosure.sfrac Bool.false 3187768426624 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1785432))))) 12264582519014652634797

noncomputable def hp767049 := nat_lit 27613403609390481693185028671359942656

noncomputable def hp767050 := @hp767048 4503599627370496000 84537625203419 33000000000000000000 883964424783267 2251799813685248 200000001089 8712000000000000000 hp767049 12262814590165086100797 4503599627370496000 351842703981119

noncomputable def hp767051 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 892716 4000) (Real.log (Enclosure.sfrac Bool.false 3187768426624 16000000)) 892716 4000 0 1 54954016816163943 4503599627370496

noncomputable def hp767052 := nat_lit 118012852504629089679704064

noncomputable def hp767053 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3187768426624) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp767052 hp617687

noncomputable def hp767054 := BSN.log_rat_reduce_isNear 3187768426624 16000000 17 6375536853248 4194304000000 112404900 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp767055 := nat_lit 176688799613603414740787384838343946691226374801029957109840174476309329948782867693033213179828378118897920790035747768452534763520

noncomputable def hp767056 := nat_lit 2574261995624747129456175527164096639171445943624326952694332530008639867283033333811369294621791598858626431854934014722524053504

noncomputable def hp767057 := nat_lit 2249842699722295920258377844372893631812638638158741379456568497265328161549576244062098588705248316552844758100650303160320

noncomputable def hp767058 := BSN.log_dyadic_bound 1090616426624 5284920426624 6 5 hp767055 268435456 87120000 hp767056 hp767057 112404900 6375536853248

noncomputable def hp767059 := hp767058 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp767060 := @BSN.binarySplit_of_base5 (BSN.artanhP 1090616426624) (BSN.artanhQ 5284920426624) 0 5 hp767056 hp767055 hp767057 rfl rfl rfl

noncomputable def hp767061 := hp767054 rfl rfl rfl rfl (hp767059 (hp767060 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp767062 := @hp767051 12500018513 1089000000000000000 12264582519014652634797 4503599627370496000 84537625203419 33000000000000000000 (Enclosure.Real.IsNear.const Bool.false 892716 4000) (BSN.isNear_log_sfrac 3187768426624 16000000 54954016816163943 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp767053 1000001481040000 87120000000000000000000 54954016816163943 4503599627370496 12500018513 1089000000000000000 (hp767061 rfl rfl rfl) rfl)) rfl

noncomputable def hp767063 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1785432)))) 1 4

noncomputable def hp767064 := @hp767063 0 1 883964424783267 562949953421312 200000001089 2178000000000000000 883964424783267 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp767065 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1785432))) 884279719003555 562949953421312 1

noncomputable def hp767066 := @hp767065 2000000000000000 18793 33554432 1 10890000 29660924181809247289344 883964424783267 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp767067 := BSN.arctan_dyadic_bound_f 1000 1785432 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp767068 := hp767067 1 18793 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1785432) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1785432) 0 0 rfl)

noncomputable def hp767069 := hp767064 (hp767066 (hp767068 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp767070 := @hp767043 8572475229219 16777216000 669537 134217728000 hp767044 1590288114097427891673 900719925474099200 33780335074883385517 hp739140 (@hp767046 1 hp767047 10252596867691246247229 4503599627370496000 351842703981119 136125000000000000000 (@hp767050 136125000000000000000 hp767062 hp767069 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 892716 2000) rfl rfl)

noncomputable def hp767071 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 892716 2000) (Real.log Real.pi) 892716 2000 0 1 38410761 33554432

noncomputable def hp767072 := hp767070 (@hp767071 3 268435456 8572475229219 16777216000 669537 134217728000 (Enclosure.Real.IsNear.const Bool.false 892716 2000) hd4909 rfl) rfl

noncomputable def hp767073 := @hp767033 hp739140 118485685135 67108864 509 67108864 (@hp767037 hp767031 hp767032 33780335074883385517 hp739140 (hp767039 rfl rfl rfl rfl rfl) (hp767042 (hp767072 rfl) (Enclosure.Real.IsNear.const Bool.true hp767035 hp767036) rfl rfl)) rfl

noncomputable def hp767074 := nat_lit 15184285952733105577000960

noncomputable def hp767075 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 118485685135) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp767074) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp767076 := BSN.sin_reduce_arg_pos_rat_q3 118485685135 67108864 226375608064910080 72057594037927936 280 hp767074 hp617687 rfl rfl rfl rfl

noncomputable def hp767077 := nat_lit 14351857895634154602715177772768264928389775823753295941889279197694864215807913156392007461739498565784666769912235890275609471762793356066816

noncomputable def hp767078 := nat_lit 10190016325093079261068471181065081736874224403285594942061721855719796094082997141720849773839630632204863512531333929427738314791714816

noncomputable def hp767079 := nat_lit 71670295951470656206434360456448780425697828739878847886170626404634563141900225321867717320733377104109138178845798519576582214128109591986176

noncomputable def hp767080 := BSN.sin_dyadic_bound_f 215781681628 137438953472 4 3 67108864 21801270 hp767077 hp737934 hp767078 hp767079 hp737937

noncomputable def hp767081 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215781681628) (BSN.sinEvenQ 137438953472) 0 3 hp767077 hp737934 hp767078 rfl rfl rfl

noncomputable def hp767082 := hp767080 hp767078 67108843 rfl rfl rfl rfl rfl rfl rfl rfl (hp767081 rfl)

noncomputable def hp767083 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215781681628) (BSN.sinOddQ 137438953472) 0 3 hp767079 hp737937 hp767078 rfl rfl rfl

noncomputable def hp767084 := @BSN.sin_arg_round Bool.false 67108843 67108864 hp767074 hp617687 215781681628 137438953472 21801270 21780000 (hp767082 (hp767083 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767085 := hp767075 67108843 67108864 280 1000000000000000 21780000 10890000 hp767076 BSN.pi_near_15 hp767084 rfl rfl

noncomputable def hp767086 := @hp767030 509 67108864 Bool.false 67108843 67108864 1 10890000 hp767073 (Enclosure.sfrac_false_div 118485685135 67108864) (hp767085 rfl rfl) rfl

noncomputable def hp767087 := @hp767027 67108843 67108864 350632429 45675970560000 536870744 536870912 4122 536870912 (@hp767028 Bool.false 67108843 67108864 350632429 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 892716 1000)) (Enclosure.sfrac Bool.false 892716 1000)) (@hp767029 5610118864 730815528960000 67108843 67108864 350632429 45675970560000 (hp767086 rfl) rfl))

noncomputable def hp767088 := @hp767033 hp739140 947885481081 536870912 4067 536870912 (@hp767037 hp767031 hp767032 33780335074883385517 hp739140 (hp767039 rfl rfl rfl rfl rfl) (hp767042 (hp767072 rfl) (Enclosure.Real.IsNear.const Bool.true hp767035 hp767036) rfl rfl)) rfl

noncomputable def hp767089 := hp767026 (BSN.cos_quad_nat3 499 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 451228920 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 892716 1000)) rfl rfl (hp767087 rfl) hp767088

noncomputable def hp767090 := nat_lit 11909304848907176915096106394896

noncomputable def hp767091 := BSN.cos_dyadic_bound_f 58745094 536870912 2 1 536870912 268435456 hp767090 hp708767 hp767090 hp767090 hp708768

noncomputable def hp767092 := @BSN.binarySplit_of_base (BSN.cosEvenP 58745094) (BSN.cosEvenQ 536870912) 0 1 hp767090 hp708767 hp767090 rfl rfl rfl

noncomputable def hp767093 := hp767091 hp767090 533660136 rfl rfl rfl rfl rfl rfl rfl rfl (hp767092 rfl)

noncomputable def hp767094 := @BSN.binarySplit_of_base (BSN.cosOddP 58745094) (BSN.cosOddQ 536870912) 0 1 hp767090 hp708768 hp767090 rfl rfl rfl

noncomputable def hp767095 := nat_lit 20725101887542673491303171579650864857255028146254309680806535385069977600

noncomputable def hp767096 := nat_lit 6801202342177572296422123137031909495562365609777926381872383168413696

noncomputable def hp767097 := nat_lit 54269017282629190693504575461625642010770353695869265854636942150053462016

noncomputable def hp767098 := BSN.sin_dyadic_bound_f 535886988 536870912 3 2 536870912 268435456 hp767095 hp708845 hp767096 hp767097 hp708848

noncomputable def hp767099 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 535886988) (BSN.sinEvenQ 536870912) 0 2 hp767095 hp708845 hp767096 rfl rfl rfl

noncomputable def hp767100 := hp767098 hp767096 451228920 rfl rfl rfl rfl rfl rfl rfl rfl (hp767099 rfl)

noncomputable def hp767101 := @BSN.binarySplit_of_base2 (BSN.sinOddP 535886988) (BSN.sinOddQ 536870912) 0 2 hp767097 hp708848 hp767096 rfl rfl rfl

noncomputable def hp767102 := hp767089 hd4911 hd4913 hd4915 hd4917 hd4918 (hp767093 (hp767094 rfl) rfl rfl rfl rfl) (hp767100 (hp767101 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767103 := hp767021 (BSN.cos_quad_nat1 209 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 260640025 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 892716 1000)) rfl rfl (hp767102 rfl rfl rfl rfl rfl) hp767088

noncomputable def hp767104 := nat_lit 193179230516680090350731192613121

noncomputable def hp767105 := BSN.cos_dyadic_bound_f 117893567 536870912 2 1 536870912 268435456 hp767104 hp708767 hp767104 hp767104 hp708768

noncomputable def hp767106 := @BSN.binarySplit_of_base (BSN.cosEvenP 117893567) (BSN.cosEvenQ 536870912) 0 1 hp767104 hp708767 hp767104 rfl rfl rfl

noncomputable def hp767107 := hp767105 hp767104 523978491 rfl rfl rfl rfl rfl rfl rfl rfl (hp767106 rfl)

noncomputable def hp767108 := @BSN.binarySplit_of_base (BSN.cosOddP 117893567) (BSN.cosOddQ 536870912) 0 1 hp767104 hp708768 hp767104 rfl rfl rfl

noncomputable def hp767109 := nat_lit 1378099312240167689946417873918311298109660409629715295944767223315431680

noncomputable def hp767110 := nat_lit 30089813713685708371486946618572209163764827083466844258094314291456

noncomputable def hp767111 := nat_lit 3609259005692521792046112024253432854329512120262547781155115336936325376

noncomputable def hp767112 := BSN.sin_dyadic_bound_f 272146302 536870912 3 2 536870912 268435456 hp767109 hp708845 hp767110 hp767111 hp708848

noncomputable def hp767113 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 272146302) (BSN.sinEvenQ 536870912) 0 2 hp767109 hp708845 hp767110 rfl rfl rfl

noncomputable def hp767114 := hp767112 hp767110 260640025 rfl rfl rfl rfl rfl rfl rfl rfl (hp767113 rfl)

noncomputable def hp767115 := @BSN.binarySplit_of_base2 (BSN.sinOddP 272146302) (BSN.sinOddQ 536870912) 0 2 hp767111 hp708848 hp767110 rfl rfl rfl

noncomputable def hp767116 := hp767103 hd4920 hd4922 hd4924 hd4926 hd4918 (hp767107 (hp767108 rfl) rfl rfl rfl rfl) (hp767114 (hp767115 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767117 := hp767016 (BSN.cos_quad_nat2 18 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 530446212 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 892716 1000)) rfl rfl (hp767116 rfl rfl rfl rfl rfl) hp767088

noncomputable def hp767118 := nat_lit 31510635527702796169885439839515649100869269764949073252551687158961115105

noncomputable def hp767119 := nat_lit 15716593551676339107892098593841947178894046897735011149267767334899681

noncomputable def hp767120 := nat_lit 82502409040137942562572898086722384492558449498936954214822270935879749601

noncomputable def hp767121 := BSN.sin_dyadic_bound_f 595038139 536870912 3 2 536870912 268435456 hp767118 hp708845 hp767119 hp767120 hp708848

noncomputable def hp767122 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 595038139) (BSN.sinEvenQ 536870912) 0 2 hp767118 hp708845 hp767119 rfl rfl rfl

noncomputable def hp767123 := hp767121 hp767119 480478797 rfl rfl rfl rfl rfl rfl rfl rfl (hp767122 rfl)

noncomputable def hp767124 := @BSN.binarySplit_of_base2 (BSN.sinOddP 595038139) (BSN.sinOddQ 536870912) 0 2 hp767120 hp708848 hp767119 rfl rfl rfl

noncomputable def hp767125 := nat_lit 47779498287362944518725781753856

noncomputable def hp767126 := BSN.cos_dyadic_bound_f 83140072 536870912 2 1 536870912 268435456 hp767125 hp708767 hp767125 hp767125 hp708768

noncomputable def hp767127 := @BSN.binarySplit_of_base (BSN.cosEvenP 83140072) (BSN.cosEvenQ 536870912) 0 1 hp767125 hp708767 hp767125 rfl rfl rfl

noncomputable def hp767128 := hp767126 hp767125 530446212 rfl rfl rfl rfl rfl rfl rfl rfl (hp767127 rfl)

noncomputable def hp767129 := @BSN.binarySplit_of_base (BSN.cosOddP 83140072) (BSN.cosOddQ 536870912) 0 1 hp767125 hp708768 hp767125 rfl rfl rfl

noncomputable def hp767130 := hp767117 hd4928 hd4930 hd4932 hd4934 hd4918 (hp767123 (hp767124 rfl) rfl rfl rfl rfl) (hp767128 (hp767129 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767131 := hp767012 (BSN.cos_quad_nat0 124 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 222009874 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 892716 1000)) rfl rfl (hp767130 rfl rfl rfl rfl rfl) hp767088

noncomputable def hp767132 := nat_lit 70637443767166597203854770847905785916529164394932658372189224556501267177342206406354067112040227706199517167616

noncomputable def hp767133 := nat_lit 7654360635778381241917553537612812479775018560363171593878623902847540464787401754275114454578457965756416

noncomputable def hp767134 := nat_lit 353016046603418675231947777037260744254020080907788964762446845616939819241454441541045426960652406833840260120576

noncomputable def hp767135 := BSN.sin_dyadic_bound_f 666283528 536870912 4 3 536870912 268435456 hp767132 hp642702 hp767133 hp767134 hp642705

noncomputable def hp767136 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 666283528) (BSN.sinEvenQ 536870912) 0 3 hp767132 hp642702 hp767133 rfl rfl rfl

noncomputable def hp767137 := hp767135 hp767133 507946692 rfl rfl rfl rfl rfl rfl rfl rfl (hp767136 rfl)

noncomputable def hp767138 := @BSN.binarySplit_of_base3 (BSN.sinOddP 666283528) (BSN.sinOddQ 536870912) 0 3 hp767134 hp642705 hp767133 rfl rfl rfl

noncomputable def hp767139 := nat_lit 19653071715429408508205849684847674153215484646609017358169910620892620693294327292973726645027962184073536876321

noncomputable def hp767140 := nat_lit 2895390474896359457681309942061726087563647876229880724885330737929262761625446400096222025103097909489441

noncomputable def hp767141 := nat_lit 119147531846493315963791199930611478796052784075153676123600597971352307288058033201513366807107493646163551203105

noncomputable def hp767142 := BSN.cos_dyadic_bound_f 614434503 536870912 4 3 536870912 268435456 hp767139 hp716712 hp767140 hp767141 hp716714

noncomputable def hp767143 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 614434503) (BSN.cosEvenQ 536870912) 0 3 hp767139 hp716712 hp767140 rfl rfl rfl

noncomputable def hp767144 := hp767142 hp767140 222009874 rfl rfl rfl rfl rfl rfl rfl rfl (hp767143 rfl)

noncomputable def hp767145 := @BSN.binarySplit_of_base3 (BSN.cosOddP 614434503) (BSN.cosOddQ 536870912) 0 3 hp767141 hp716714 hp767140 rfl rfl rfl

noncomputable def hp767146 := hp767131 hd4936 hd4938 hd4940 hd4942 hd4918 (hp767137 (hp767138 rfl) rfl rfl rfl rfl) (hp767144 (hp767145 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767147 := hp767007 (BSN.cos_quad_nat2 238 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 186682848 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 892716 1000)) rfl rfl (hp767146 rfl rfl rfl rfl rfl) hp767088

noncomputable def hp767148 := nat_lit 9472898468975441617454050147465591028979057081957617261415827367348604264608469731285380186969645309071543616481

noncomputable def hp767149 := nat_lit 324752839736053300350760553448198734841262808435763473464901262255261674751018599975156514200907154834401

noncomputable def hp767150 := nat_lit 57450056525049431325637648786894903338470035953096862992433865910125033099730160094341387513287698750686757241825

noncomputable def hp767151 := BSN.cos_dyadic_bound_f 512030793 536870912 4 3 536870912 268435456 hp767148 hp716712 hp767149 hp767150 hp716714

noncomputable def hp767152 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 512030793) (BSN.cosEvenQ 536870912) 0 3 hp767148 hp716712 hp767149 rfl rfl rfl

noncomputable def hp767153 := hp767151 hp767149 310656941 rfl rfl rfl rfl rfl rfl rfl rfl (hp767152 rfl)

noncomputable def hp767154 := @BSN.binarySplit_of_base3 (BSN.cosOddP 512030793) (BSN.cosOddQ 536870912) 0 3 hp767150 hp716714 hp767149 rfl rfl rfl

noncomputable def hp767155 := nat_lit 25024667483029570691106990455815091346371770412900429375911105482434652951201435998305119628245891445395875683921

noncomputable def hp767156 := nat_lit 5972523781608234722634579226224960507380447534207213201506891043482889553793815985014942302304773264105041

noncomputable def hp767157 := nat_lit 151684886396406326300602118160388185878767589367013222468997747871184198107151806050413881630451523128755109748305

noncomputable def hp767158 := BSN.cos_dyadic_bound_f 652649221 536870912 4 3 536870912 268435456 hp767155 hp716712 hp767156 hp767157 hp716714

noncomputable def hp767159 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 652649221) (BSN.cosEvenQ 536870912) 0 3 hp767155 hp716712 hp767156 rfl rfl rfl

noncomputable def hp767160 := hp767158 hp767156 186682848 rfl rfl rfl rfl rfl rfl rfl rfl (hp767159 rfl)

noncomputable def hp767161 := @BSN.binarySplit_of_base3 (BSN.cosOddP 652649221) (BSN.cosOddQ 536870912) 0 3 hp767157 hp716714 hp767156 rfl rfl rfl

noncomputable def hp767162 := hp767147 hd4944 hd4946 hd4961 hd4963 hd4918 (hp767153 (hp767154 rfl) rfl rfl rfl rfl) (hp767160 (hp767161 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767163 := @hp767002 108303 134217728 (hp767162 rfl rfl rfl rfl rfl) (hp767162 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp767164 := @hp767000 Bool.false 105184547 268435456 108303 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 892716 1000)) (Enclosure.sfrac Bool.false 892716 1000) 11) hp767163

noncomputable def hp767165 := @Enclosure.Real.IsNear.mulLit_tf hp766991 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1))) 9718887 33554432 1

noncomputable def hp767166 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp766990 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp767167 := @hp767166 1 1 0 1 9718887 33554432 1 33554432 9718887 33554432 1

noncomputable def hp767168 := @Enclosure.Real.IsNear.of_eq (hp766990 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp767169 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 892716 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp767170 := @hp767168 (@Inv.inv Real Real.instInv (Real.sqrt hp766992)) Bool.false 9718887 33554432 1 33554432 (hp767169 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 892716 1000) 892716 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 892716 1000))))

noncomputable def hp767171 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp766992)) Bool.false 19437774 67108864 2 67108864 9718887 33554432

noncomputable def hp767172 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp766992) Bool.false 231693177 67108864 7 67108864 231693177 67108864 7 67108864

noncomputable def hp767173 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 892716 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp767174 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 892716 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp767175 := @hp767174 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 892716 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 2383709507553

noncomputable def hp767176 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 892716 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 892716 1000 0

noncomputable def hp767177 := @hp767176 1 10680707 67108864 1 67108864 2383709507553 16777216000 223179 16777216000 (Enclosure.Real.IsNear.const Bool.false 892716 1000) hd4949

noncomputable def hp767178 := @hp767175 16777216000 223179 16777216000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 892716 1000) 892716 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 892716 1000))) (hp767177 rfl)

noncomputable def hp767179 := @hp767173 2383709507553 16777216000 223179 16777216000 399960025 399960064 33554432 hp767178 rfl rfl rfl

noncomputable def hp767180 := @Enclosure.Real.IsNear.recentre' hp766992 Bool.false 799920089 67108864 39 67108864 799920089 67108864 39 67108864 (hp767179 rfl rfl rfl)

noncomputable def hp767181 := @Enclosure.Real.IsNear.sqrt_image hp766992 799920089 67108864 39 67108864 115846585 115846592 33554432 (hp767180 rfl) rfl rfl

noncomputable def hp767182 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp766992) 231693177 67108864 7 67108864 9718886 9718888 33554432 (hp767172 (hp767181 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp767183 := @hp767167 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp767170 (@hp767171 1 33554432 (hp767182 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp767184 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp767185 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp767186 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1))) (hp767184 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767185 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp767187 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 892716 1000) 892716 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 892716 1000)) rfl

noncomputable def hp767188 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp767189 := @hp767188 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767185 (Enclosure.sfrac Bool.false 1 16)))) 38325453

noncomputable def hp767190 := @hp767189 33554432 165 33554432 21980455 33554432 478589929 45675970560000 842410895021115 1125899906842624 323322255115901 21286545113743360000

noncomputable def hp767191 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp767192 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1)))) 58754683

noncomputable def hp767193 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp767194 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 387814439) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp767195 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1))) Bool.false 54580030119973038789675

noncomputable def hp767196 := nat_lit 1052456941482910740750750033

noncomputable def hp767197 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp767198 := @Enclosure.Real.IsNear.subLit_ff_p hp766992 (Enclosure.sfrac Bool.false 11 1) 799920089 67108864 39 67108864 11 1 0

noncomputable def hp767199 := @hp767197 500000000000000 61722585 67108864 39 67108864 54580030119973038789675 9444732965739290427392 hp767196 hp738031 hd4948 (@hp767198 1 61722585 61722585 67108864 39 67108864 (hp767180 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp767200 := @hp767194 387814439 67108864 123 33554432 Bool.false 58754683 67108864 1 10890000 (@hp767195 9444732965739290427392 hp767196 hp738031 387814439 67108864 123 33554432 (hp767199 rfl) rfl) (Enclosure.sfrac_false_div 387814439 67108864)

noncomputable def hp767201 := nat_lit 10314521131381473251688448

noncomputable def hp767202 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 387814439) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp767201) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp767203 := BSN.sin_reduce_arg_pos_rat_q3 387814439 67108864 226375608064910080 72057594037927936 0 hp767201 hp617687 rfl rfl rfl rfl

noncomputable def hp767204 := nat_lit 498292075624230253208597032979565929878421671281753481568691087905693162832852539630366368000

noncomputable def hp767205 := nat_lit 213085626207898582459222968438507050272944786939875212975942970592139038564240062451425536

noncomputable def hp767206 := nat_lit 1304705678478171208317582058711867471600186276082880272811277513038713868023605024645085798656

noncomputable def hp767207 := BSN.sin_dyadic_bound_f 146578161254 137438953472 3 2 67108864 21801270 hp767204 hp738039 hp767205 hp767206 hp738042

noncomputable def hp767208 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 146578161254) (BSN.sinEvenQ 137438953472) 0 2 hp767204 hp738039 hp767205 rfl rfl rfl

noncomputable def hp767209 := hp767207 hp767205 58754683 rfl rfl rfl rfl rfl rfl rfl rfl (hp767208 rfl)

noncomputable def hp767210 := @BSN.binarySplit_of_base2 (BSN.sinOddP 146578161254) (BSN.sinOddQ 137438953472) 0 2 hp767206 hp738042 hp767205 rfl rfl rfl

noncomputable def hp767211 := @BSN.sin_arg_round Bool.false 58754683 67108864 hp767201 hp617687 146578161254 137438953472 21801270 21780000 (hp767209 (hp767210 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767212 := hp767202 58754683 67108864 0 1000000000000000 21780000 10890000 hp767203 BSN.pi_near_15 hp767211 rfl rfl

noncomputable def hp767213 := @hp767192 67108864 85814027 22837985280000 38325288 38325618 33554432 (@hp767193 58754683 67108864 1373024432 365407764480000 58754683 67108864 85814027 22837985280000 (hp767200 (hp767212 rfl rfl) rfl rfl) rfl)

noncomputable def hp767214 := @hp767191 Bool.false 76650906 67108864 330 67108864 38325453 33554432 165 33554432 (hp767213 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp767215 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767185 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp767216 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767185 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 28740139)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp767217 := nat_lit 542885883366809334926882251405

noncomputable def hp767218 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767185 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp767217

noncomputable def hp767219 := nat_lit 200549956760934490906014644635712681

noncomputable def hp767220 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767185 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp767221 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp767222 := @hp767221 (Enclosure.sfrac Bool.false 1 16) 332455063411215 4503599627370496 7431608847 4503599627370496 1 16 0

noncomputable def hp767223 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1)) 3809677499082225

noncomputable def hp767224 := @hp767223 4503599627370496 4814363151 4503599627370496 61722585 67108864 39 67108864 22310681636574603509760 332455063411215 4503599627370496 7431608847

noncomputable def hp767225 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1)) 61722585 67108864 39

noncomputable def hp767226 := @hp767225 67108864 61722585 67108864 39 67108864 3809677499082225 4503599627370496 4814363151 4503599627370496 (@hp767198 1 61722585 61722585 67108864 39 67108864 (hp767180 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp767227 := hp767226 (@hp767198 1 61722585 61722585 67108864 39 67108864 (hp767180 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp767228 := @hp767224 4503599627370496 (hp767227 rfl) (@hp767198 1 61722585 61722585 67108864 39 67108864 (hp767180 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp767229 := @hp767220 500000000000000 613930040121871 4503599627370496 7431608847 4503599627370496 hp767217 hp627574 hp767219 hp738055 hd4948 (@hp767222 1 9822880641949936 613930040121871 4503599627370496 7431608847 4503599627370496 (hp767228 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp767230 := @hp767216 28740139 33554432 697 67108864 Bool.false 21980455 33554432 1 10890000 (@hp767218 hp627574 hp767219 hp738055 28740139 33554432 697 67108864 (hp767229 rfl) rfl) (Enclosure.sfrac_true_div 28740139 33554432)

noncomputable def hp767231 := nat_lit 1453461110466930114161101955380977945404492946678677971196542561

noncomputable def hp767232 := nat_lit 465490598470013316263767386268576477819964085757450831363681

noncomputable def hp767233 := nat_lit 4359452350203850315850778331370396683257838911864519011926900321

noncomputable def hp767234 := BSN.cos_dyadic_bound_f 28740139 33554432 3 2 33554432 10890000 hp767231 hp684401 hp767232 hp767233 hp684404

noncomputable def hp767235 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 28740139) (BSN.cosEvenQ 33554432) 0 2 hp767231 hp684401 hp767232 rfl rfl rfl

noncomputable def hp767236 := hp767234 hp767232 21980455 rfl rfl rfl rfl rfl rfl rfl rfl (hp767235 rfl)

noncomputable def hp767237 := @BSN.binarySplit_of_base2 (BSN.cosOddP 28740139) (BSN.cosOddQ 33554432) 0 2 hp767233 hp684404 hp767232 rfl rfl rfl

noncomputable def hp767238 := hp767230 (BSN.cos_neg_of_bound 28740139 33554432 Bool.false 21980455 33554432 1 10890000 (hp767236 (hp767237 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp767239 := hp767190 hp767214 (@hp767215 21980455 33554432 7657438864 730815528960000 21980455 33554432 478589929 45675970560000 (hp767238 rfl) rfl)

noncomputable def hp767240 := @hp767165 33554432 842410895021115 1125899906842624 323322255115901 21286545113743360000 8187296296279079299005 37778931862957161709568 12633038465451447174227 hp743845 (hp767183 rfl) (@hp767186 Bool.false 842410895021115 1125899906842624 323322255115901 21286545113743360000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp766992 (Enclosure.sfrac Bool.false 11 1)) (hp767187 rfl (hp766995 rfl rfl))) (hp767239 rfl))

noncomputable def hp767241 := @hp766989 hp766987 hp743845 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 892716 1000))) (@hp766994 hp766987 hp743845 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 892716 1000) 11 (hp766995 rfl rfl)) (@hp766998 hp766987 hp743845 hp767164 (hp767240 rfl) rfl rfl))

theorem hd5077 : hp766988 hp743845 := hp767241

noncomputable def hp767242 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 893984 1000)) Bool.true 21767116352174073775419 9444732965739290427392 348100808003564408268299

noncomputable def hp767243 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 893984 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 893984 1000)) Bool.true 21767116352174073775419 9444732965739290427392

noncomputable def hp767244 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 893984 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp767245 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp767244 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp767246 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 893984 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp767247 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 893984 1000)) (Enclosure.sfrac Bool.false 893984 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp767245 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp767248 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 893984 1000)) hp767247 Bool.true 21767116352174073775419 9444732965739290427392

noncomputable def hp767249 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 893984 1000) 893984 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 893984 1000)) rfl

noncomputable def hp767250 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 893984 1000)) (Enclosure.sfrac Bool.false 893984 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp767245 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp767251 := nat_lit 1460766450950226021320560214016

noncomputable def hp767252 := @hp767250 169529083 67108864 216905 268435456 2091980992427860228805 9444732965739290427392 1813952911326645708299 hp751876 hp767251 21767116352174073775419 9444732965739290427392

noncomputable def hp767253 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 893984 1000)) (Enclosure.sfrac Bool.false 893984 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 893984 1000)) (Enclosure.sfrac Bool.false 893984 1000) 11)

noncomputable def hp767254 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 893984 1000)) (Enclosure.sfrac Bool.false 893984 1000) 11) hp767253

noncomputable def hp767255 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 893984 1000)) (Enclosure.sfrac Bool.false 893984 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 893984 1000)) (Enclosure.sfrac Bool.false 893984 1000) 11)

noncomputable def hp767256 := @hp767255 678116332 536870912 216905 536870912 678116332 536870912 216905 536870912 728121867205869568 169529083 67108864

noncomputable def hp767257 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 893984 1000)) (Enclosure.sfrac Bool.false 893984 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp767258 := hp767257 BSN.quadSignNeg 9 10 11 893984 1000 184 238 536870912 268435456 9007199254740992

noncomputable def hp767259 := hp767258 Bool.false 949572760224 4072 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp767260 := hp767259 Bool.true 733070756 186206 Bool.true 392241782 Bool.true 597742837 28296951008113761 1 Bool.false 399844976

noncomputable def hp767261 := hp767260 Bool.false Bool.false 237097770 Bool.true Bool.true 678116332 216905 BSN.abs_quadSignPos (BSN.cos_quad_nat0 184 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 399844976 536870912) BSN.abs_quadSignNeg

noncomputable def hp767262 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 893984 1000)) (Enclosure.sfrac Bool.false 893984 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp767263 := hp767262 BSN.quadSignPos 7 8 9 893984 1000 57 124 536870912 268435456 9007199254740992

noncomputable def hp767264 := hp767263 Bool.false 949572760224 4072 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp767265 := hp767264 Bool.true 732031310 152072 Bool.true 394589030 Bool.true 422921062 28296951008113761 1 Bool.false 360010510

noncomputable def hp767266 := hp767265 Bool.true Bool.false 378730487 Bool.false Bool.true 733070756 186206 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 360010510 536870912) BSN.abs_quadSignPos

noncomputable def hp767267 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 893984 1000)) (Enclosure.sfrac Bool.false 893984 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp767268 := hp767267 BSN.quadSignNeg 5 6 7 893984 1000 106 18 536870912 268435456 9007199254740992

noncomputable def hp767269 := hp767268 Bool.false 949572760224 4072 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp767270 := hp767269 Bool.true 393973038 113005 Bool.false 219258026 Bool.false 445736393 28296951008113761 1 Bool.false 492717286

noncomputable def hp767271 := hp767270 Bool.true Bool.false 362222613 Bool.true Bool.true 732031310 152072 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 106 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 492717286 536870912) BSN.abs_quadSignNeg

noncomputable def hp767272 := hp767262 BSN.quadSignNeg 3 4 5 893984 1000 337 210 536870912 268435456 9007199254740992

noncomputable def hp767273 := hp767272 Bool.false 949572760224 4072 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp767274 := hp767273 Bool.true 144986106 66788 Bool.false 18134774 Bool.false 20482022 28296951008113761 1 Bool.false 18131325

noncomputable def hp767275 := hp767274 Bool.true Bool.false 536480257 Bool.true Bool.true 393973038 113005 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 337 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 18131325 536870912) BSN.abs_quadSignNeg

noncomputable def hp767276 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 893984 1000)) (Enclosure.sfrac Bool.false 893984 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp767277 := hp767276 BSN.quadSignPos 1 2 3 893984 1000 731 500 536870912 268435456 9007199254740992

noncomputable def hp767278 := hp767277 Bool.false 949572760224 4072 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp767279 := hp767278 Bool.true 536870856 4122 Bool.false 430847851 Bool.false 631968421 28296951008113761 1 Bool.false 386067733

noncomputable def hp767280 := hp767279 Bool.false Bool.false 205929819 Bool.false Bool.true 144986106 66788 BSN.abs_quadSignPos (BSN.cos_quad_nat3 731 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 386067733 536870912) BSN.abs_quadSignPos

noncomputable def hp767281 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 893984 1000)) (Enclosure.sfrac Bool.false 893984 1000) 1) Bool.true

noncomputable def hp767282 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 893984 1000)) (Enclosure.sfrac Bool.false 893984 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 893984 1000)))

noncomputable def hp767283 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 893984 1000))) Bool.true 67108857 67108864

noncomputable def hp767284 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 893984 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 29674148757) (@Nat.cast Real Real.instNatCast 16777216)) Bool.false 29674148757 16777216

noncomputable def hp767285 := nat_lit 1116836520236392216244421153731822027843319750247038841

noncomputable def hp767286 := nat_lit 631438754658998642557118483680531066155662573568000

noncomputable def hp767287 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 893984 1000)) Bool.false hp767285 hp767286 4228521336626631751

noncomputable def hp767288 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 893984 4000) (Real.log (Enclosure.sfrac Bool.false 3196830569024 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1787968))))))

noncomputable def hp767289 := nat_lit 274088183184841151359387554283520000

noncomputable def hp767290 := nat_lit 1470182916752525238686051414535686062080

noncomputable def hp767291 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 893984 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp767288 (Enclosure.sfrac Bool.false 893984 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 893984 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp767289 hp767290)) Bool.false

noncomputable def hp767292 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 893984 1000) 893984 1000 3196830569024 16000000 1787968

noncomputable def hp767293 := hp767292 4000 2000 hp767289 hp767290 (@Eq.refl Real (Enclosure.sfrac Bool.false 893984 1000)) rfl rfl rfl rfl

noncomputable def hp767294 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp767288 (Enclosure.sfrac Bool.false 893984 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 893984 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp767289 hp767290) 995699311576604594969 562949953421312000

noncomputable def hp767295 := nat_lit 1463859963804244005675887694619373768334796063043798749675520

noncomputable def hp767296 := @hp767294 4228521336626631751 557568000000000000000000 hp767289 hp767290 0 1 hp767295 hp767285 hp767286 4228521336626631751 557568000000000000000000

noncomputable def hp767297 := @Enclosure.Real.IsNear.subLit_ff_p (hp767288 (Enclosure.sfrac Bool.false 893984 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 893984 2000) (Real.log Real.pi)) 1283752414579087495961 562949953421312000 2818704137717573 1089000000000000000000

noncomputable def hp767298 := nat_lit 2088132802671499479548428288000

noncomputable def hp767299 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 893984 4000) (Real.log (Enclosure.sfrac Bool.false 3196830569024 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1787968))))))

noncomputable def hp767300 := @hp767299 (Enclosure.sfrac Bool.false 893984 2000) 307077308031757317893 112589990684262400 2818704137717573 1089000000000000000000 893984 2000 0

noncomputable def hp767301 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 893984 4000) (Real.log (Enclosure.sfrac Bool.false 3196830569024 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1787968))))) 307121506275645722843

noncomputable def hp767302 := nat_lit 691476625012878637666984592580542464

noncomputable def hp767303 := @hp767301 112589990684262400 349213017197681 136125000000000000000 883964877768099 2251799813685248 200000001089 8712000000000000000 hp767302 307077308031757317893 112589990684262400 2818704137717573

noncomputable def hp767304 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 893984 4000) (Real.log (Enclosure.sfrac Bool.false 3196830569024 16000000)) 893984 4000 0 1 54966801423854695 4503599627370496

noncomputable def hp767305 := nat_lit 118040307240591074640527360

noncomputable def hp767306 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3196830569024) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp767305 hp617687

noncomputable def hp767307 := BSN.log_rat_reduce_isNear 3196830569024 16000000 17 6393661138048 4194304000000 113166922 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp767308 := nat_lit 179741997497988724754987066604424368711660389652979738370218086625949950470327059779576230599343875582236746921242024012257186283520

noncomputable def hp767309 := nat_lit 2654267162658673044899431567899342209435453592639113523354293695082180380314972578418323848822841950085618723368196510801675157504

noncomputable def hp767310 := nat_lit 2443933715823685953089918700346858753293373397866399882770533174219803381771873664106553410098135900950193750419425271480320

noncomputable def hp767311 := BSN.log_dyadic_bound 1099678569024 5293982569024 6 5 hp767308 268435456 87120000 hp767309 hp767310 113166922 6393661138048

noncomputable def hp767312 := hp767311 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp767313 := @BSN.binarySplit_of_base5 (BSN.artanhP 1099678569024) (BSN.artanhQ 5293982569024) 0 5 hp767309 hp767308 hp767310 rfl rfl rfl

noncomputable def hp767314 := hp767307 rfl rfl rfl rfl (hp767312 (hp767313 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp767315 := @hp767304 12500018513 1089000000000000000 307121506275645722843 112589990684262400 349213017197681 136125000000000000000 (Enclosure.Real.IsNear.const Bool.false 893984 4000) (BSN.isNear_log_sfrac 3196830569024 16000000 54966801423854695 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp767306 1000001481040000 87120000000000000000000 54966801423854695 4503599627370496 12500018513 1089000000000000000 (hp767314 rfl rfl rfl) rfl)) rfl

noncomputable def hp767316 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1787968)))) 1 4

noncomputable def hp767317 := @hp767316 0 1 883964877768099 562949953421312 200000001089 2178000000000000000 883964877768099 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp767318 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1787968))) 884279719003555 562949953421312 1

noncomputable def hp767319 := @hp767318 2000000000000000 18766 33554432 1 10890000 29660939381457989664768 883964877768099 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp767320 := BSN.arctan_dyadic_bound_f 1000 1787968 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp767321 := hp767320 1 18766 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1787968) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1787968) 0 0 rfl)

noncomputable def hp767322 := hp767317 (hp767319 (hp767321 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp767323 := @hp767297 1073081430057 2097152000 83811 16777216000 hp767298 995699311576604594969 562949953421312000 4228521336626631751 557568000000000000000000 (@hp767300 1 513500965831634998384400 1283752414579087495961 562949953421312000 2818704137717573 1089000000000000000000 (@hp767303 1089000000000000000000 hp767315 hp767322 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 893984 2000) rfl rfl)

noncomputable def hp767324 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 893984 2000) (Real.log Real.pi) 893984 2000 0 1 38410761 33554432

noncomputable def hp767325 := hp767323 (@hp767324 3 268435456 1073081430057 2097152000 83811 16777216000 (Enclosure.Real.IsNear.const Bool.false 893984 2000) hd4909 rfl) rfl

noncomputable def hp767326 := @hp767287 557568000000000000000000 29674148757 16777216 509 67108864 (@hp767291 hp767285 hp767286 4228521336626631751 557568000000000000000000 (hp767293 rfl rfl rfl rfl rfl) (hp767296 (hp767325 rfl) (Enclosure.Real.IsNear.const Bool.true hp767289 hp767290) rfl rfl)) rfl

noncomputable def hp767327 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 29674148757) (@Nat.cast Real Real.instNatCast 16777216)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1043791462670557773824) (@Nat.cast Real Real.instNatCast hp619230)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp767328 := BSN.sin_reduce_arg_pos_rat_q2 29674148757 16777216 226375608064910080 72057594037927936 281 1043791462670557773824 hp619230 rfl rfl rfl rfl

noncomputable def hp767329 := BSN.cos_dyadic_bound_f 59332675 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp767330 := hp767329 1 67108857 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 59332675) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp767331 := hp767330 (@BSN.binarySplit_of_le (BSN.cosOddP 59332675) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp767332 := @BSN.cos_arg_round Bool.false 67108857 67108864 1043791462670557773824 hp619230 59332675 137438953472 21801270 21780000 hp767331 rfl

noncomputable def hp767333 := hp767327 67108857 67108864 281 1000000000000000 21780000 10890000 hp767328 BSN.pi_near_15 hp767332 rfl rfl

noncomputable def hp767334 := @hp767284 509 67108864 Bool.true 67108857 67108864 1 10890000 hp767326 (Enclosure.sfrac_false_div 29674148757 16777216) (hp767333 rfl rfl) rfl

noncomputable def hp767335 := @hp767281 67108857 67108864 350632429 45675970560000 536870856 536870912 4122 536870912 (@hp767282 Bool.true 67108857 67108864 350632429 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 893984 1000)) (Enclosure.sfrac Bool.false 893984 1000)) (@hp767283 5610118864 730815528960000 67108857 67108864 350632429 45675970560000 (hp767334 rfl) rfl))

noncomputable def hp767336 := @hp767287 557568000000000000000000 949572760224 536870912 4072 536870912 (@hp767291 hp767285 hp767286 4228521336626631751 557568000000000000000000 (hp767293 rfl rfl rfl rfl rfl) (hp767296 (hp767325 rfl) (Enclosure.Real.IsNear.const Bool.true hp767289 hp767290) rfl rfl)) rfl

noncomputable def hp767337 := hp767280 (BSN.cos_quad_nat0 500 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 205929819 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 893984 1000)) rfl rfl (hp767335 rfl) hp767336

noncomputable def hp767338 := nat_lit 8657979893955704919902964643344162484633263640721697230841070512112647265

noncomputable def hp767339 := nat_lit 1187384700614635270054111552872353754096451433867747415414768624712801

noncomputable def hp767340 := nat_lit 22673739194654422523594343599577679839390010518616278299244513144426445921

noncomputable def hp767341 := BSN.sin_dyadic_bound_f 430847851 536870912 3 2 536870912 268435456 hp767338 hp708845 hp767339 hp767340 hp708848

noncomputable def hp767342 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 430847851) (BSN.sinEvenQ 536870912) 0 2 hp767338 hp708845 hp767339 rfl rfl rfl

noncomputable def hp767343 := hp767341 hp767339 386067733 rfl rfl rfl rfl rfl rfl rfl rfl (hp767342 rfl)

noncomputable def hp767344 := @BSN.binarySplit_of_base2 (BSN.sinOddP 430847851) (BSN.sinOddQ 536870912) 0 2 hp767340 hp708848 hp767339 rfl rfl rfl

noncomputable def hp767345 := nat_lit 21996944566632878584937617148304756836911712834115640616512237610505494158438435669472516825748457183873354810321

noncomputable def hp767346 := nat_lit 4058303563180599180038028865174188711859262609105399080779583521795876581794068806556283172449078622143441

noncomputable def hp767347 := nat_lit 133346550945517542845352609016800915390568046694441661278675201965652041987836030738365796571846465067820255921105

noncomputable def hp767348 := BSN.cos_dyadic_bound_f 631968421 536870912 4 3 536870912 268435456 hp767345 hp716712 hp767346 hp767347 hp716714

noncomputable def hp767349 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 631968421) (BSN.cosEvenQ 536870912) 0 3 hp767345 hp716712 hp767346 rfl rfl rfl

noncomputable def hp767350 := hp767348 hp767346 205929819 rfl rfl rfl rfl rfl rfl rfl rfl (hp767349 rfl)

noncomputable def hp767351 := @BSN.binarySplit_of_base3 (BSN.cosOddP 631968421) (BSN.cosOddQ 536870912) 0 3 hp767347 hp716714 hp767346 rfl rfl rfl

noncomputable def hp767352 := hp767337 hd4911 hd4913 hd4915 hd4917 hd4918 (hp767343 (hp767344 rfl) rfl rfl rfl rfl) (hp767350 (hp767351 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767353 := hp767275 (BSN.cos_quad_nat2 210 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536480257 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 893984 1000)) rfl rfl (hp767352 rfl rfl rfl rfl rfl) hp767336

noncomputable def hp767354 := BSN.sin_dyadic_bound_f 18134774 536870912 1 0 536870912 268435456 0 1 1 0 1

noncomputable def hp767355 := hp767354 1 18131325 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 18134774) (BSN.sinEvenQ 536870912) 0 0 rfl)

noncomputable def hp767356 := hp767355 (@BSN.binarySplit_of_le (BSN.sinOddP 18134774) (BSN.sinOddQ 536870912) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp767357 := nat_lit 175991346124824215445265578256

noncomputable def hp767358 := BSN.cos_dyadic_bound_f 20482022 536870912 2 1 536870912 268435456 hp767357 hp708767 hp767357 hp767357 hp708768

noncomputable def hp767359 := @BSN.binarySplit_of_base (BSN.cosEvenP 20482022) (BSN.cosEvenQ 536870912) 0 1 hp767357 hp708767 hp767357 rfl rfl rfl

noncomputable def hp767360 := hp767358 hp767357 536480257 rfl rfl rfl rfl rfl rfl rfl rfl (hp767359 rfl)

noncomputable def hp767361 := @BSN.binarySplit_of_base (BSN.cosOddP 20482022) (BSN.cosOddQ 536870912) 0 1 hp767357 hp708768 hp767357 rfl rfl rfl

noncomputable def hp767362 := hp767353 hd4920 hd4922 hd4924 hd4926 hd4918 hp767356 (hp767360 (hp767361 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp767363 := hp767271 (BSN.cos_quad_nat2 18 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 362222613 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 893984 1000)) rfl rfl (hp767362 rfl rfl rfl rfl) hp767336

noncomputable def hp767364 := nat_lit 322565539947208134543093581956698695258722785428850806002925100992717056

noncomputable def hp767365 := nat_lit 5341263436983573967530943426451407097275610193846948408859974328576

noncomputable def hp767366 := nat_lit 967685937314750436481345683983243182961973805066164724111957583029494016

noncomputable def hp767367 := BSN.cos_dyadic_bound_f 219258026 536870912 3 2 536870912 268435456 hp767364 hp708868 hp767365 hp767366 hp708870

noncomputable def hp767368 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 219258026) (BSN.cosEvenQ 536870912) 0 2 hp767364 hp708868 hp767365 rfl rfl rfl

noncomputable def hp767369 := hp767367 hp767365 492717286 rfl rfl rfl rfl rfl rfl rfl rfl (hp767368 rfl)

noncomputable def hp767370 := @BSN.binarySplit_of_base2 (BSN.cosOddP 219258026) (BSN.cosOddQ 536870912) 0 2 hp767366 hp708870 hp767365 rfl rfl rfl

noncomputable def hp767371 := nat_lit 5510918263200258896247496804597362318197860000005352244333968929431311681

noncomputable def hp767372 := nat_lit 1558205578041641345567821899217454073312429234565626567553514074363201

noncomputable def hp767373 := nat_lit 16529638378444693406051354769993652046446955141546925479866799760145208641

noncomputable def hp767374 := BSN.cos_dyadic_bound_f 445736393 536870912 3 2 536870912 268435456 hp767371 hp708868 hp767372 hp767373 hp708870

noncomputable def hp767375 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 445736393) (BSN.cosEvenQ 536870912) 0 2 hp767371 hp708868 hp767372 rfl rfl rfl

noncomputable def hp767376 := hp767374 hp767372 362222613 rfl rfl rfl rfl rfl rfl rfl rfl (hp767375 rfl)

noncomputable def hp767377 := @BSN.binarySplit_of_base2 (BSN.cosOddP 445736393) (BSN.cosOddQ 536870912) 0 2 hp767373 hp708870 hp767372 rfl rfl rfl

noncomputable def hp767378 := hp767363 hd4928 hd4930 hd4932 hd4934 hd4918 (hp767369 (hp767370 rfl) rfl rfl rfl rfl) (hp767376 (hp767377 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767379 := hp767266 (BSN.cos_quad_nat0 124 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 378730487 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 893984 1000)) rfl rfl (hp767378 rfl rfl rfl rfl rfl) hp767336

noncomputable def hp767380 := nat_lit 6090924543435304709448556098061087274409699985444721008889203161607840000

noncomputable def hp767381 := nat_lit 587705909748361745443651027168760964124282118611882087944096100000000

noncomputable def hp767382 := nat_lit 15951469899429062605729785774211241058083489219401278642757908315287200000

noncomputable def hp767383 := BSN.sin_dyadic_bound_f 394589030 536870912 3 2 536870912 268435456 hp767380 hp708845 hp767381 hp767382 hp708848

noncomputable def hp767384 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 394589030) (BSN.sinEvenQ 536870912) 0 2 hp767380 hp708845 hp767381 rfl rfl rfl

noncomputable def hp767385 := hp767383 hp767381 360010510 rfl rfl rfl rfl rfl rfl rfl rfl (hp767384 rfl)

noncomputable def hp767386 := @BSN.binarySplit_of_base2 (BSN.sinOddP 394589030) (BSN.sinOddQ 536870912) 0 2 hp767382 hp708848 hp767381 rfl rfl rfl

noncomputable def hp767387 := nat_lit 4466070472797283445563517080469993106413495149022498023510753204784210176

noncomputable def hp767388 := nat_lit 1023468575758156613164609782294388094842328255374516250298493686128896

noncomputable def hp767389 := nat_lit 13396164481240334023464222021845390543050800790556745038031662626980372736

noncomputable def hp767390 := BSN.cos_dyadic_bound_f 422921062 536870912 3 2 536870912 268435456 hp767387 hp708868 hp767388 hp767389 hp708870

noncomputable def hp767391 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 422921062) (BSN.cosEvenQ 536870912) 0 2 hp767387 hp708868 hp767388 rfl rfl rfl

noncomputable def hp767392 := hp767390 hp767388 378730487 rfl rfl rfl rfl rfl rfl rfl rfl (hp767391 rfl)

noncomputable def hp767393 := @BSN.binarySplit_of_base2 (BSN.cosOddP 422921062) (BSN.cosOddQ 536870912) 0 2 hp767389 hp708870 hp767388 rfl rfl rfl

noncomputable def hp767394 := hp767379 hd4936 hd4938 hd4940 hd4942 hd4918 (hp767385 (hp767386 rfl) rfl rfl rfl rfl) (hp767392 (hp767393 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767395 := hp767261 (BSN.cos_quad_nat2 238 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 237097770 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 893984 1000)) rfl rfl (hp767394 rfl rfl rfl rfl rfl) hp767336

noncomputable def hp767396 := nat_lit 3304287611783639228731447666196958057605688706611748974108208723209216256

noncomputable def hp767397 := nat_lit 560313164566782701600740555372870408601317566981497680146595151339776

noncomputable def hp767398 := nat_lit 9911742209021784120791141517480128431999863484701283926964332979324969216

noncomputable def hp767399 := BSN.cos_dyadic_bound_f 392241782 536870912 3 2 536870912 268435456 hp767396 hp708868 hp767397 hp767398 hp708870

noncomputable def hp767400 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 392241782) (BSN.cosEvenQ 536870912) 0 2 hp767396 hp708868 hp767397 rfl rfl rfl

noncomputable def hp767401 := hp767399 hp767397 399844976 rfl rfl rfl rfl rfl rfl rfl rfl (hp767400 rfl)

noncomputable def hp767402 := @BSN.binarySplit_of_base2 (BSN.cosOddP 392241782) (BSN.cosOddQ 536870912) 0 2 hp767398 hp708870 hp767397 rfl rfl rfl

noncomputable def hp767403 := nat_lit 17601081269732516749456095431961617276458954479737435517981952087960494824453431214645823604290927150877165871761

noncomputable def hp767404 := nat_lit 2080523213741137996283536724587076249761141139102445972831107639517973158532074958860893120728565671912081

noncomputable def hp767405 := nat_lit 106714829116629849911154760810176550536977567618230459033932516765430055658797776681335887364422477536290273354385

noncomputable def hp767406 := BSN.cos_dyadic_bound_f 597742837 536870912 4 3 536870912 268435456 hp767403 hp716712 hp767404 hp767405 hp716714

noncomputable def hp767407 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 597742837) (BSN.cosEvenQ 536870912) 0 3 hp767403 hp716712 hp767404 rfl rfl rfl

noncomputable def hp767408 := hp767406 hp767404 237097770 rfl rfl rfl rfl rfl rfl rfl rfl (hp767407 rfl)

noncomputable def hp767409 := @BSN.binarySplit_of_base3 (BSN.cosOddP 597742837) (BSN.cosOddQ 536870912) 0 3 hp767405 hp716714 hp767404 rfl rfl rfl

noncomputable def hp767410 := hp767395 hd4944 hd4946 hd4961 hd4963 hd4918 (hp767401 (hp767402 rfl) rfl rfl rfl rfl) (hp767408 (hp767409 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767411 := @hp767256 216905 268435456 (hp767410 rfl rfl rfl rfl rfl) (hp767410 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp767412 := @hp767254 Bool.true 169529083 67108864 216905 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 893984 1000)) (Enclosure.sfrac Bool.false 893984 1000) 11) hp767411

noncomputable def hp767413 := @Enclosure.Real.IsNear.mulLit_tf hp767245 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1))) 9715439 33554432 1

noncomputable def hp767414 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp767244 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp767415 := @hp767414 1 1 0 1 9715439 33554432 1 33554432 9715439 33554432 1

noncomputable def hp767416 := @Enclosure.Real.IsNear.of_eq (hp767244 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp767417 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 893984 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp767418 := @hp767416 (@Inv.inv Real Real.instInv (Real.sqrt hp767246)) Bool.false 9715439 33554432 1 33554432 (hp767417 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 893984 1000) 893984 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 893984 1000))))

noncomputable def hp767419 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp767246)) Bool.false 19430878 67108864 2 67108864 9715439 33554432

noncomputable def hp767420 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp767246) Bool.false 231775407 67108864 7 67108864 231775407 67108864 7 67108864

noncomputable def hp767421 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 893984 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp767422 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 893984 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp767423 := @hp767422 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 893984 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 298386911459

noncomputable def hp767424 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 893984 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 893984 1000 0

noncomputable def hp767425 := @hp767424 1 10680707 67108864 1 67108864 298386911459 2097152000 27937 2097152000 (Enclosure.Real.IsNear.const Bool.false 893984 1000) hd4949

noncomputable def hp767426 := @hp767423 2097152000 27937 2097152000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 893984 1000) 893984 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 893984 1000))) (hp767425 rfl)

noncomputable def hp767427 := @hp767421 298386911459 2097152000 27937 2097152000 400243973 400244011 33554432 hp767426 rfl rfl rfl

noncomputable def hp767428 := @Enclosure.Real.IsNear.recentre' hp767246 Bool.false 800487984 67108864 38 67108864 50030499 4194304 19 33554432 (hp767427 rfl rfl rfl)

noncomputable def hp767429 := @Enclosure.Real.IsNear.sqrt_image hp767246 50030499 4194304 19 33554432 115887700 115887707 33554432 (hp767428 rfl) rfl rfl

noncomputable def hp767430 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp767246) 231775407 67108864 7 67108864 9715438 9715440 33554432 (hp767420 (hp767429 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp767431 := @hp767415 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp767418 (@hp767419 1 33554432 (hp767430 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp767432 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp767433 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp767434 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1))) (hp767432 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767433 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp767435 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 893984 1000) 893984 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 893984 1000)) rfl

noncomputable def hp767436 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp767437 := @hp767436 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767433 (Enclosure.sfrac Bool.false 1 16)))) 74569121

noncomputable def hp767438 := @hp767437 67108864 305 67108864 2887595 4194304 469061179 45675970560000 215325420953995 281474976710656 22284312644831627 1532631248189521920000

noncomputable def hp767439 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp767440 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1)))) 7549371

noncomputable def hp767441 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp767442 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 97845657) (@Nat.cast Real Real.instNatCast 16777216)) Bool.false

noncomputable def hp767443 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1))) Bool.false 3442638009437285166025

noncomputable def hp767444 := nat_lit 512735433039372438100352453

noncomputable def hp767445 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp767446 := @Enclosure.Real.IsNear.subLit_ff_p hp767246 (Enclosure.sfrac Bool.false 11 1) 50030499 4194304 19 33554432 11 1 0

noncomputable def hp767447 := @hp767445 500000000000000 3893155 4194304 19 33554432 3442638009437285166025 590295810358705651712 hp767444 hp682805 hd4948 (@hp767446 1 3893155 3893155 4194304 19 33554432 (hp767428 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp767448 := @hp767442 97845657 16777216 15 4194304 Bool.false 60394968 67108864 1 10890000 (@hp767443 590295810358705651712 hp767444 hp682805 97845657 16777216 15 4194304 (hp767447 rfl) rfl) (Enclosure.sfrac_false_div 97845657 16777216)

noncomputable def hp767449 := nat_lit 2707187840051668334936064

noncomputable def hp767450 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 97845657) (@Nat.cast Real Real.instNatCast 16777216)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp767449) (@Nat.cast Real Real.instNatCast hp619230)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp767451 := BSN.sin_reduce_arg_pos_rat_q3 97845657 16777216 226375608064910080 72057594037927936 0 hp767449 hp619230 rfl rfl rfl rfl

noncomputable def hp767452 := nat_lit 605398200332310532757900537990220371092909479030127756912474722327440991024004789948507889920

noncomputable def hp767453 := nat_lit 314476828741612414528342461764771700970069697883550131431622096772749282846118401775902976

noncomputable def hp767454 := nat_lit 1585057562195231641885265045036291341537001856044237425034163551272332430033499781976550154496

noncomputable def hp767455 := BSN.sin_dyadic_bound_f 153885812326 137438953472 3 2 67108864 21801270 hp767452 hp738039 hp767453 hp767454 hp738042

noncomputable def hp767456 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 153885812326) (BSN.sinEvenQ 137438953472) 0 2 hp767452 hp738039 hp767453 rfl rfl rfl

noncomputable def hp767457 := hp767455 hp767453 60394968 rfl rfl rfl rfl rfl rfl rfl rfl (hp767456 rfl)

noncomputable def hp767458 := @BSN.binarySplit_of_base2 (BSN.sinOddP 153885812326) (BSN.sinOddQ 137438953472) 0 2 hp767454 hp738042 hp767453 rfl rfl rfl

noncomputable def hp767459 := @BSN.sin_arg_round Bool.false 60394968 67108864 hp767449 hp619230 153885812326 137438953472 21801270 21780000 (hp767457 (hp767458 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767460 := hp767450 60394968 67108864 0 1000000000000000 21780000 10890000 hp767451 BSN.pi_near_15 hp767459 rfl rfl

noncomputable def hp767461 := @hp767440 8388608 10471519 2854748160000 37284408 37284713 33554432 (@hp767441 60394968 67108864 167544304 45675970560000 7549371 8388608 10471519 2854748160000 (hp767448 (hp767460 rfl rfl) rfl rfl) rfl)

noncomputable def hp767462 := @hp767439 Bool.false 74569121 67108864 305 67108864 74569121 67108864 305 67108864 (hp767461 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp767463 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767433 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp767464 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767433 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3403417)) (@Nat.cast Real Real.instNatCast 4194304)) Bool.true

noncomputable def hp767465 := nat_lit 2009022827154931629244006405

noncomputable def hp767466 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767433 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp767465

noncomputable def hp767467 := nat_lit 49143092176520850415111951143021711

noncomputable def hp767468 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767433 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp767469 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp767470 := @hp767469 (Enclosure.sfrac Bool.false 1 16) 1172419735095 17592186044416 1821053689 1125899906842624 1 16 0

noncomputable def hp767471 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1)) 15156655854025

noncomputable def hp767472 := @hp767471 17592186044416 1183519481 1125899906842624 3893155 4194304 19 33554432 4917484784587898880 1172419735095 17592186044416 1821053689

noncomputable def hp767473 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1)) 3893155 4194304 19

noncomputable def hp767474 := @hp767473 33554432 3893155 4194304 19 33554432 15156655854025 17592186044416 1183519481 1125899906842624 (@hp767446 1 3893155 3893155 4194304 19 33554432 (hp767428 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp767475 := hp767474 (@hp767446 1 3893155 3893155 4194304 19 33554432 (hp767428 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp767476 := @hp767472 1125899906842624 (hp767475 rfl) (@hp767446 1 3893155 3893155 4194304 19 33554432 (hp767428 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp767477 := @hp767468 500000000000000 2271931362871 17592186044416 1821053689 1125899906842624 hp767465 hp630709 hp767467 hp682143 hd4948 (@hp767470 1 36350901805936 2271931362871 17592186044416 1821053689 1125899906842624 (hp767476 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp767478 := @hp767464 3403417 4194304 683 67108864 Bool.false 23100760 33554432 1 10890000 (@hp767466 hp630709 hp767467 hp682143 3403417 4194304 683 67108864 (hp767477 rfl) rfl) (Enclosure.sfrac_true_div 3403417 4194304)

noncomputable def hp767479 := nat_lit 69778497323567935150434648394707533986939775536982262721

noncomputable def hp767480 := nat_lit 18002022930327155010127708570892989746875965835183041

noncomputable def hp767481 := nat_lit 209299487924843151141283689766980815981325574679276422081

noncomputable def hp767482 := BSN.cos_dyadic_bound_f 3403417 4194304 3 2 33554432 10890000 hp767479 hp632130 hp767480 hp767481 hp632133

noncomputable def hp767483 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 3403417) (BSN.cosEvenQ 4194304) 0 2 hp767479 hp632130 hp767480 rfl rfl rfl

noncomputable def hp767484 := hp767482 hp767480 23100760 rfl rfl rfl rfl rfl rfl rfl rfl (hp767483 rfl)

noncomputable def hp767485 := @BSN.binarySplit_of_base2 (BSN.cosOddP 3403417) (BSN.cosOddQ 4194304) 0 2 hp767481 hp632133 hp767480 rfl rfl rfl

noncomputable def hp767486 := hp767478 (BSN.cos_neg_of_bound 3403417 4194304 Bool.false 23100760 33554432 1 10890000 (hp767484 (hp767485 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp767487 := hp767438 hp767462 (@hp767463 23100760 33554432 7504978864 730815528960000 2887595 4194304 469061179 45675970560000 (hp767486 rfl) rfl)

noncomputable def hp767488 := @hp767413 33554432 215325420953995 281474976710656 22284312644831627 1532631248189521920000 2091980992427860228805 9444732965739290427392 1813952911326645708299 hp751876 (hp767431 rfl) (@hp767434 Bool.false 215325420953995 281474976710656 22284312644831627 1532631248189521920000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767246 (Enclosure.sfrac Bool.false 11 1)) (hp767435 rfl (hp767249 rfl rfl))) (hp767487 rfl))

noncomputable def hp767489 := @hp767243 348100808003564408268299 hp751876 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 893984 1000))) (@hp767248 348100808003564408268299 hp751876 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 893984 1000) 11 (hp767249 rfl rfl)) (@hp767252 348100808003564408268299 hp751876 hp767412 (hp767488 rfl) rfl rfl))

theorem hd5078 : hp767242 hp751876 := hp767489

noncomputable def hp767490 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 895251 1000)) Bool.false 36072763926487592170395 151115727451828646838272 60842848172876677824331

noncomputable def hp767491 := nat_lit 74802285088655180184944640

noncomputable def hp767492 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 895251 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 895251 1000)) Bool.false 36072763926487592170395 151115727451828646838272

noncomputable def hp767493 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 895251 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp767494 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp767493 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp767495 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 895251 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp767496 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 895251 1000)) (Enclosure.sfrac Bool.false 895251 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp767494 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp767497 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 895251 1000)) hp767496 Bool.false 36072763926487592170395 151115727451828646838272

noncomputable def hp767498 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 895251 1000) 895251 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 895251 1000)) rfl

noncomputable def hp767499 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 895251 1000)) (Enclosure.sfrac Bool.false 895251 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp767494 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp767500 := nat_lit 9683208833787047282602011525120

noncomputable def hp767501 := @hp767499 3306767 268435456 27153 33554432 34211219597862460552091 151115727451828646838272 311159035291094269771 hp767491 hp767500 36072763926487592170395 151115727451828646838272

noncomputable def hp767502 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 895251 1000)) (Enclosure.sfrac Bool.false 895251 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 895251 1000)) (Enclosure.sfrac Bool.false 895251 1000) 11)

noncomputable def hp767503 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 895251 1000)) (Enclosure.sfrac Bool.false 895251 1000) 11) hp767502

noncomputable def hp767504 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 895251 1000)) (Enclosure.sfrac Bool.false 895251 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 895251 1000)) (Enclosure.sfrac Bool.false 895251 1000) 11)

noncomputable def hp767505 := @hp767504 3306767 536870912 217224 536870912 3306767 536870912 217224 536870912 3550614030123008 3306767 268435456

noncomputable def hp767506 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 895251 1000)) (Enclosure.sfrac Bool.false 895251 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp767507 := hp767506 BSN.quadSignNeg 9 10 11 895251 1000 184 238 536870912 268435456 9007199254740992

noncomputable def hp767508 := hp767507 Bool.false 951259190806 4078 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp767509 := hp767508 Bool.true 59076446 186481 Bool.true 272065141 Bool.true 542397654 28296951008113761 1 Bool.false 469397632

noncomputable def hp767510 := hp767509 Bool.false Bool.false 285406710 Bool.true Bool.false 3306767 217224 BSN.abs_quadSignPos (BSN.cos_quad_nat0 184 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 469397632 536870912) BSN.abs_quadSignNeg

noncomputable def hp767511 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 895251 1000)) (Enclosure.sfrac Bool.false 895251 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp767512 := hp767511 BSN.quadSignPos 7 8 9 895251 1000 57 124 536870912 268435456 9007199254740992

noncomputable def hp767513 := hp767512 Bool.false 951259190806 4078 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp767514 := hp767513 Bool.true 178732240 152299 Bool.true 122626702 Bool.true 231076556 28296951008113761 1 Bool.false 121563217

noncomputable def hp767515 := hp767514 Bool.true Bool.false 487904657 Bool.false Bool.true 59076446 186481 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 121563217 536870912) BSN.abs_quadSignPos

noncomputable def hp767516 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 895251 1000)) (Enclosure.sfrac Bool.false 895251 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp767517 := hp767516 BSN.quadSignNeg 5 6 7 895251 1000 106 18 536870912 268435456 9007199254740992

noncomputable def hp767518 := hp767517 Bool.false 951259190806 4078 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp767519 := hp767518 Bool.true 102639420 113176 Bool.false 686906151 Bool.false 808528855 28296951008113761 1 Bool.false 154205532

noncomputable def hp767520 := hp767519 Bool.true Bool.false 34761666 Bool.true Bool.true 178732240 152299 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 106 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 154205532 536870912) BSN.abs_quadSignNeg

noncomputable def hp767521 := hp767511 BSN.quadSignNeg 3 4 5 895251 1000 337 210 536870912 268435456 9007199254740992

noncomputable def hp767522 := hp767521 Bool.false 951259190806 4078 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp767523 := hp767522 Bool.false 262907560 66893 Bool.false 761586537 Bool.false 612148097 28296951008113761 1 Bool.false 530662130

noncomputable def hp767524 := hp767523 Bool.true Bool.false 224089610 Bool.true Bool.true 102639420 113176 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 337 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 530662130 536870912) BSN.abs_quadSignNeg

noncomputable def hp767525 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 895251 1000)) (Enclosure.sfrac Bool.false 895251 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp767526 := hp767525 BSN.quadSignNeg 1 2 3 895251 1000 732 501 536870912 268435456 9007199254740992

noncomputable def hp767527 := hp767526 Bool.false 951259190806 4078 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp767528 := hp767527 Bool.false 536870904 4138 Bool.false 802474177 Bool.false 727791106 28296951008113761 1 Bool.false 40801300

noncomputable def hp767529 := hp767528 Bool.false Bool.false 524489610 Bool.true Bool.false 262907560 66893 BSN.abs_quadSignPos (BSN.cos_quad_nat0 732 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 40801300 536870912) BSN.abs_quadSignNeg

noncomputable def hp767530 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 895251 1000)) (Enclosure.sfrac Bool.false 895251 1000) 1) Bool.false

noncomputable def hp767531 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 895251 1000)) (Enclosure.sfrac Bool.false 895251 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 895251 1000)))

noncomputable def hp767532 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 895251 1000))) Bool.false 67108863 67108864

noncomputable def hp767533 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 895251 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 59453699425) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 59453699425 33554432

noncomputable def hp767534 := nat_lit 16433045305692318544413248326551186517894407016102193195309

noncomputable def hp767535 := nat_lit 9274469151490088296880010302994381970708601434537984000

noncomputable def hp767536 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 895251 1000)) Bool.false hp767534 hp767535 135503874343567326373

noncomputable def hp767537 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 895251 4000) (Real.log (Enclosure.sfrac Bool.false 3205898412004 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1790502))))))

noncomputable def hp767538 := nat_lit 276035954903742663621238752600480000

noncomputable def hp767539 := nat_lit 1482729003815045037696053724242329922880

noncomputable def hp767540 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 895251 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp767537 (Enclosure.sfrac Bool.false 895251 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 895251 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp767538 hp767539)) Bool.false

noncomputable def hp767541 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 895251 1000) 895251 1000 3205898412004 16000000 1790502

noncomputable def hp767542 := hp767541 4000 2000 hp767538 hp767539 (@Eq.refl Real (Enclosure.sfrac Bool.false 895251 1000)) rfl rfl rfl rfl

noncomputable def hp767543 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp767537 (Enclosure.sfrac Bool.false 895251 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 895251 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp767538 hp767539) 31918965185980231214309 18014398509481984000

noncomputable def hp767544 := nat_lit 47327170480393877407910155180467417171535892206374316402489920

noncomputable def hp767545 := @hp767543 135503874343567326373 hp738659 hp767538 hp767539 0 1 hp767544 hp767534 hp767535 135503874343567326373 hp738659

noncomputable def hp767546 := @Enclosure.Real.IsNear.subLit_ff_p (hp767537 (Enclosure.sfrac Bool.false 895251 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 895251 2000) (Real.log Real.pi)) 1645989131140502615213 720575940379279360 11290654074326263 4356000000000000000000

noncomputable def hp767547 := nat_lit 85681819747467281729984701399040

noncomputable def hp767548 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 895251 4000) (Real.log (Enclosure.sfrac Bool.false 3205898412004 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1790502))))))

noncomputable def hp767549 := @hp767548 (Enclosure.sfrac Bool.false 895251 2000) 49213432418518693209317 18014398509481984000 11290654074326263 4356000000000000000000 895251 2000 0

noncomputable def hp767550 := nat_lit 82299456557025130760650000

noncomputable def hp767551 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 895251 4000) (Real.log (Enclosure.sfrac Bool.false 3205898412004 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1790502))))) 49220504141030498929317

noncomputable def hp767552 := nat_lit 110818797950831937243669487942019055616

noncomputable def hp767553 := @hp767551 18014398509481984000 3730218024593921 1452000000000000000000 883965313975715 2251799813685248 200000001089 8712000000000000000 hp767552 49213432418518693209317 18014398509481984000 11290654074326263

noncomputable def hp767554 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 895251 4000) (Real.log (Enclosure.sfrac Bool.false 3205898412004 16000000)) 895251 4000 0 1 54979557845822567 4503599627370496

noncomputable def hp767555 := nat_lit 118067701448174067741884416

noncomputable def hp767556 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3205898412004) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp767555 hp617687

noncomputable def hp767557 := BSN.log_rat_reduce_isNear 3205898412004 16000000 17 6411796824008 4194304000000 113927264 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp767558 := nat_lit 66846229192115607766925371237938863700695960078955201280446603388331764900674542577274946531734638776900599266060326988870226564637718356315912768766250844160

noncomputable def hp767559 := nat_lit 1000393999763030972162101577515767335181354482402735402036680233938313878913145715752712347707447790435852683770008234068233906973616141155295465242259095552

noncomputable def hp767560 := nat_lit 35876595396383321083106556553237998215155116318888670370812870446078610827906018681583776810386930359846574957133457915635914842655116033194794680320

noncomputable def hp767561 := BSN.log_dyadic_bound 1108746412004 5303050412004 7 6 hp767558 268435456 87120000 hp767559 hp767560 113927264 6411796824008

noncomputable def hp767562 := hp767561 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp767563 := @BSN.binarySplit_of_base6 (BSN.artanhP 1108746412004) (BSN.artanhQ 5303050412004) 0 6 hp767559 hp767558 hp767560 rfl rfl rfl

noncomputable def hp767564 := hp767557 rfl rfl rfl rfl (hp767562 (hp767563 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp767565 := @hp767554 12500018513 1089000000000000000 49220504141030498929317 18014398509481984000 3730218024593921 1452000000000000000000 (Enclosure.Real.IsNear.const Bool.false 895251 4000) (BSN.isNear_log_sfrac 3205898412004 16000000 54979557845822567 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp767556 1000001481040000 87120000000000000000000 54979557845822567 4503599627370496 12500018513 1089000000000000000 (hp767564 rfl rfl rfl) rfl)) rfl

noncomputable def hp767566 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1790502)))) 1 4

noncomputable def hp767567 := @hp767566 0 1 883965313975715 562949953421312 200000001089 2178000000000000000 883965313975715 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp767568 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1790502))) 884279719003555 562949953421312 1

noncomputable def hp767569 := @hp767568 2000000000000000 18740 33554432 1 10890000 29660954018156778618880 883965313975715 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp767570 := BSN.arctan_dyadic_bound_f 1000 1790502 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp767571 := hp767570 1 18740 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1790502) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1790502) 0 0 rfl)

noncomputable def hp767572 := hp767567 (hp767569 (hp767571 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp767573 := @hp767546 34387272196011 67108864000 2685753 536870912000 hp767547 31918965185980231214309 18014398509481984000 135503874343567326373 hp738659 (@hp767549 1 hp767550 1645989131140502615213 720575940379279360 11290654074326263 4356000000000000000000 (@hp767553 4356000000000000000000 hp767565 hp767572 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 895251 2000) rfl rfl)

noncomputable def hp767574 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 895251 2000) (Real.log Real.pi) 895251 2000 0 1 38410761 33554432

noncomputable def hp767575 := hp767573 (@hp767574 3 268435456 34387272196011 67108864000 2685753 536870912000 (Enclosure.Real.IsNear.const Bool.false 895251 2000) hd4909 rfl) rfl

noncomputable def hp767576 := @hp767536 hp738659 59453699425 33554432 511 67108864 (@hp767540 hp767534 hp767535 135503874343567326373 hp738659 (hp767542 rfl rfl rfl rfl rfl) (hp767545 (hp767575 rfl) (Enclosure.Real.IsNear.const Bool.true hp767538 hp767539) rfl rfl)) rfl

noncomputable def hp767577 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 59453699425) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 293915699609253969920) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp767578 := BSN.sin_reduce_arg_pos_rat_q0 59453699425 33554432 226375608064910080 72057594037927936 282 293915699609253969920 hp619237 rfl rfl rfl rfl

noncomputable def hp767579 := BSN.cos_dyadic_bound_f 8353586 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp767580 := hp767579 1 67108863 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 8353586) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp767581 := hp767580 (@BSN.binarySplit_of_le (BSN.cosOddP 8353586) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp767582 := @BSN.cos_arg_round Bool.false 67108863 67108864 293915699609253969920 hp619237 8353586 137438953472 21801270 21780000 hp767581 rfl

noncomputable def hp767583 := hp767577 67108863 67108864 282 1000000000000000 21780000 10890000 hp767578 BSN.pi_near_15 hp767582 rfl rfl

noncomputable def hp767584 := @hp767533 511 67108864 Bool.false 67108863 67108864 1 10890000 hp767576 (Enclosure.sfrac_false_div 59453699425 33554432) (hp767583 rfl rfl) rfl

noncomputable def hp767585 := @hp767530 67108863 67108864 351993679 45675970560000 536870904 536870912 4138 536870912 (@hp767531 Bool.false 67108863 67108864 351993679 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 895251 1000)) (Enclosure.sfrac Bool.false 895251 1000)) (@hp767532 5631898864 730815528960000 67108863 67108864 351993679 45675970560000 (hp767584 rfl) rfl))

noncomputable def hp767586 := @hp767536 hp738659 951259190806 536870912 4078 536870912 (@hp767540 hp767534 hp767535 135503874343567326373 hp738659 (hp767542 rfl rfl rfl rfl rfl) (hp767545 (hp767575 rfl) (Enclosure.Real.IsNear.const Bool.true hp767538 hp767539) rfl rfl)) rfl

noncomputable def hp767587 := hp767529 (BSN.cos_quad_nat1 501 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 524489610 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 895251 1000)) rfl rfl (hp767585 rfl) hp767586

noncomputable def hp767588 := nat_lit 57292529150401029611973277298286566918893389678121241972044080710804166005427032775449624022686971246697840544001

noncomputable def hp767589 := nat_lit 71313670896234992787722054227036043842096668116868276753736587961954667342835946080315506677634275037579521

noncomputable def hp767590 := nat_lit 346887874325776929267497809696502636321505099345953066385917469394403344767376259263232965230027819325656742136065

noncomputable def hp767591 := BSN.cos_dyadic_bound_f 802474177 536870912 4 3 536870912 268435456 hp767588 hp716712 hp767589 hp767590 hp716714

noncomputable def hp767592 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 802474177) (BSN.cosEvenQ 536870912) 0 3 hp767588 hp716712 hp767589 rfl rfl rfl

noncomputable def hp767593 := hp767591 hp767589 40801300 rfl rfl rfl rfl rfl rfl rfl rfl (hp767592 rfl)

noncomputable def hp767594 := @BSN.binarySplit_of_base3 (BSN.cosOddP 802474177) (BSN.cosOddQ 536870912) 0 3 hp767590 hp716714 hp767589 rfl rfl rfl

noncomputable def hp767595 := nat_lit 100593489618654393191351431558083063873998088895080665447404133380546773860310637365255631811502284274191082459136

noncomputable def hp767596 := nat_lit 22084162170756275628645867048637738157633636344462852574518195054658600609996049236576124196457463876161536

noncomputable def hp767597 := nat_lit 502620513537945856078724700338872202961843230618667527647276820326391501537577012944498006539986326307786876522496

noncomputable def hp767598 := BSN.sin_dyadic_bound_f 727791106 536870912 4 3 536870912 268435456 hp767595 hp642702 hp767596 hp767597 hp642705

noncomputable def hp767599 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 727791106) (BSN.sinEvenQ 536870912) 0 3 hp767595 hp642702 hp767596 rfl rfl rfl

noncomputable def hp767600 := hp767598 hp767596 524489610 rfl rfl rfl rfl rfl rfl rfl rfl (hp767599 rfl)

noncomputable def hp767601 := @BSN.binarySplit_of_base3 (BSN.sinOddP 727791106) (BSN.sinOddQ 536870912) 0 3 hp767597 hp642705 hp767596 rfl rfl rfl

noncomputable def hp767602 := hp767587 hd4911 hd4913 hd4915 hd4917 hd4918 (hp767593 (hp767594 rfl) rfl rfl rfl rfl) (hp767600 (hp767601 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767603 := hp767524 (BSN.cos_quad_nat2 210 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 224089610 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 895251 1000)) rfl rfl (hp767602 rfl rfl rfl rfl rfl) hp767586

noncomputable def hp767604 := nat_lit 120646968123897937081860744971873333608223172944875335359045162634004486979594860872203669382634719370839617533281

noncomputable def hp767605 := nat_lit 38074227282012139254325696307055511890861894135071599176690962160638780869959076307324161701224412639229281

noncomputable def hp767606 := nat_lit 602735990952658254685582931060600058850058162483112678775758057230441718477532299771912884934957667095247624435041

noncomputable def hp767607 := BSN.sin_dyadic_bound_f 761586537 536870912 4 3 536870912 268435456 hp767604 hp642702 hp767605 hp767606 hp642705

noncomputable def hp767608 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 761586537) (BSN.sinEvenQ 536870912) 0 3 hp767604 hp642702 hp767605 rfl rfl rfl

noncomputable def hp767609 := hp767607 hp767605 530662130 rfl rfl rfl rfl rfl rfl rfl rfl (hp767608 rfl)

noncomputable def hp767610 := @BSN.binarySplit_of_base3 (BSN.sinOddP 761586537) (BSN.sinOddQ 536870912) 0 3 hp767606 hp642705 hp767605 rfl rfl rfl

noncomputable def hp767611 := nat_lit 19361879526223641305565275016169696597438125811695935254731467144914589285282881428744138359700523364959458961921

noncomputable def hp767612 := nat_lit 2768713668656795749992872114832721387112228662840034095420659820616278117434271011257902199691390681623041

noncomputable def hp767613 := nat_lit 117383349278746466262533961956397016872521322105785545300207166030867623895461383720515838709200434449820053154305

noncomputable def hp767614 := BSN.cos_dyadic_bound_f 612148097 536870912 4 3 536870912 268435456 hp767611 hp716712 hp767612 hp767613 hp716714

noncomputable def hp767615 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 612148097) (BSN.cosEvenQ 536870912) 0 3 hp767611 hp716712 hp767612 rfl rfl rfl

noncomputable def hp767616 := hp767614 hp767612 224089610 rfl rfl rfl rfl rfl rfl rfl rfl (hp767615 rfl)

noncomputable def hp767617 := @BSN.binarySplit_of_base3 (BSN.cosOddP 612148097) (BSN.cosOddQ 536870912) 0 3 hp767613 hp716714 hp767612 rfl rfl rfl

noncomputable def hp767618 := hp767603 hd4920 hd4922 hd4924 hd4926 hd4918 (hp767609 (hp767610 rfl) rfl rfl rfl rfl) (hp767616 (hp767617 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767619 := hp767520 (BSN.cos_quad_nat2 18 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 34761666 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 895251 1000)) rfl rfl (hp767618 rfl rfl rfl rfl rfl) hp767586

noncomputable def hp767620 := nat_lit 30716144756446652425827504940289658853846956701534098110096403181574786735590758437100575626677868201542902238881

noncomputable def hp767621 := nat_lit 11034911746110574005467860347544259897489071173409439404693566941381717912662641208037839557949798095408801

noncomputable def hp767622 := nat_lit 186146706523333816886613385337134260399563905081508157875280483465029279219099134897338280053973304585850616958625

noncomputable def hp767623 := BSN.cos_dyadic_bound_f 686906151 536870912 4 3 536870912 268435456 hp767620 hp716712 hp767621 hp767622 hp716714

noncomputable def hp767624 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 686906151) (BSN.cosEvenQ 536870912) 0 3 hp767620 hp716712 hp767621 rfl rfl rfl

noncomputable def hp767625 := hp767623 hp767621 154205532 rfl rfl rfl rfl rfl rfl rfl rfl (hp767624 rfl)

noncomputable def hp767626 := @BSN.binarySplit_of_base3 (BSN.cosOddP 686906151) (BSN.cosOddQ 536870912) 0 3 hp767622 hp716714 hp767621 rfl rfl rfl

noncomputable def hp767627 := nat_lit 59046631515573422209387616722272080135188404112720992430061985468561019000434297702234437241978570771941874390625

noncomputable def hp767628 := nat_lit 78045215633351835684923148387747261135426218148987163715577709867111429846627005898431244901467441650390625

noncomputable def hp767629 := nat_lit 357486850077734666102020961263662340302072224225753418457002024936113534960552176250339339708619997712212875990625

noncomputable def hp767630 := BSN.cos_dyadic_bound_f 808528855 536870912 4 3 536870912 268435456 hp767627 hp716712 hp767628 hp767629 hp716714

noncomputable def hp767631 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 808528855) (BSN.cosEvenQ 536870912) 0 3 hp767627 hp716712 hp767628 rfl rfl rfl

noncomputable def hp767632 := hp767630 hp767628 34761666 rfl rfl rfl rfl rfl rfl rfl rfl (hp767631 rfl)

noncomputable def hp767633 := @BSN.binarySplit_of_base3 (BSN.cosOddP 808528855) (BSN.cosOddQ 536870912) 0 3 hp767629 hp716714 hp767628 rfl rfl rfl

noncomputable def hp767634 := hp767619 hd4928 hd4930 hd4932 hd4934 hd4918 (hp767625 (hp767626 rfl) rfl rfl rfl rfl) (hp767632 (hp767633 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767635 := hp767515 (BSN.cos_quad_nat0 124 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 487904657 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 895251 1000)) rfl rfl (hp767634 rfl rfl rfl rfl rfl) hp767586

noncomputable def hp767636 := nat_lit 226120633192006217810546597414416

noncomputable def hp767637 := BSN.sin_dyadic_bound_f 122626702 536870912 2 1 536870912 268435456 hp767636 hp708890 hp767636 hp767636 hp708891

noncomputable def hp767638 := @BSN.binarySplit_of_base (BSN.sinEvenP 122626702) (BSN.sinEvenQ 536870912) 0 1 hp767636 hp708890 hp767636 rfl rfl rfl

noncomputable def hp767639 := hp767637 hp767636 121563217 rfl rfl rfl rfl rfl rfl rfl rfl (hp767638 rfl)

noncomputable def hp767640 := @BSN.binarySplit_of_base (BSN.sinOddP 122626702) (BSN.sinOddQ 536870912) 0 1 hp767636 hp708891 hp767636 rfl rfl rfl

noncomputable def hp767641 := nat_lit 397943298207664061267374604700658279412680913904252755816653350827524096

noncomputable def hp767642 := nat_lit 8129186532805816217620023930382584139401185856067700323994283606016

noncomputable def hp767643 := nat_lit 1193813636249926572169688574054114073069763939341046132049312063915360256

noncomputable def hp767644 := BSN.cos_dyadic_bound_f 231076556 536870912 3 2 536870912 268435456 hp767641 hp708868 hp767642 hp767643 hp708870

noncomputable def hp767645 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 231076556) (BSN.cosEvenQ 536870912) 0 2 hp767641 hp708868 hp767642 rfl rfl rfl

noncomputable def hp767646 := hp767644 hp767642 487904657 rfl rfl rfl rfl rfl rfl rfl rfl (hp767645 rfl)

noncomputable def hp767647 := @BSN.binarySplit_of_base2 (BSN.cosOddP 231076556) (BSN.cosOddQ 536870912) 0 2 hp767643 hp708870 hp767642 rfl rfl rfl

noncomputable def hp767648 := hp767635 hd4936 hd4938 hd4940 hd4942 hd4918 (hp767639 (hp767640 rfl) rfl rfl rfl rfl) (hp767646 (hp767647 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767649 := hp767510 (BSN.cos_quad_nat2 238 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 285406710 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 895251 1000)) rfl rfl (hp767648 rfl rfl rfl rfl rfl) hp767586

noncomputable def hp767650 := nat_lit 764711160022757036771250683489740023422374144757690088701168000173711201

noncomputable def hp767651 := nat_lit 30018100173910153979556104121333119084518741815616519014153685933921

noncomputable def hp767652 := nat_lit 2294073443867923290005792938260977404028953396789439033065475693149265761

noncomputable def hp767653 := BSN.cos_dyadic_bound_f 272065141 536870912 3 2 536870912 268435456 hp767650 hp708868 hp767651 hp767652 hp708870

noncomputable def hp767654 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 272065141) (BSN.cosEvenQ 536870912) 0 2 hp767650 hp708868 hp767651 rfl rfl rfl

noncomputable def hp767655 := hp767653 hp767651 469397632 rfl rfl rfl rfl rfl rfl rfl rfl (hp767654 rfl)

noncomputable def hp767656 := @BSN.binarySplit_of_base2 (BSN.cosOddP 272065141) (BSN.cosOddQ 536870912) 0 2 hp767652 hp708870 hp767651 rfl rfl rfl

noncomputable def hp767657 := nat_lit 11929580857739845537845168625979741341883817081229799762165638445093222825367594463072712143105325390251807543296

noncomputable def hp767658 := nat_lit 648356141803809041718717013773518948513993286816179746357742686105563947095252929215229424707787275964416

noncomputable def hp767659 := nat_lit 72342885458904416791356391691454384639735465601262337608032905335644562918969318142849442922529046545840417607680

noncomputable def hp767660 := BSN.cos_dyadic_bound_f 542397654 536870912 4 3 536870912 268435456 hp767657 hp716712 hp767658 hp767659 hp716714

noncomputable def hp767661 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 542397654) (BSN.cosEvenQ 536870912) 0 3 hp767657 hp716712 hp767658 rfl rfl rfl

noncomputable def hp767662 := hp767660 hp767658 285406710 rfl rfl rfl rfl rfl rfl rfl rfl (hp767661 rfl)

noncomputable def hp767663 := @BSN.binarySplit_of_base3 (BSN.cosOddP 542397654) (BSN.cosOddQ 536870912) 0 3 hp767659 hp716714 hp767658 rfl rfl rfl

noncomputable def hp767664 := hp767649 hd4944 hd4946 hd4961 hd4963 hd4918 (hp767655 (hp767656 rfl) rfl rfl rfl rfl) (hp767662 (hp767663 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767665 := @hp767505 27153 33554432 (hp767664 rfl rfl rfl rfl rfl) (hp767664 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp767666 := @hp767503 Bool.false 3306767 268435456 27153 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 895251 1000)) (Enclosure.sfrac Bool.false 895251 1000) 11) hp767665

noncomputable def hp767667 := @Enclosure.Real.IsNear.mulLit_tf hp767494 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1))) 19423999 67108864 1

noncomputable def hp767668 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp767493 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp767669 := @hp767668 1 1 0 1 19423999 67108864 1 67108864 19423999 67108864 1

noncomputable def hp767670 := @Enclosure.Real.IsNear.of_eq (hp767493 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp767671 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 895251 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp767672 := @hp767670 (@Inv.inv Real Real.instInv (Real.sqrt hp767495)) Bool.false 19423999 67108864 1 67108864 (hp767671 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 895251 1000) 895251 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 895251 1000))))

noncomputable def hp767673 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp767495)) Bool.false 19423999 67108864 1 67108864 19423999 67108864

noncomputable def hp767674 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp767495) Bool.false 231857484 67108864 6 67108864 57964371 16777216 3 33554432

noncomputable def hp767675 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 895251 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp767676 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 895251 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp767677 := @hp767676 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 895251 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9561913622457

noncomputable def hp767678 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 895251 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 895251 1000 0

noncomputable def hp767679 := @hp767678 1 10680707 67108864 1 67108864 9561913622457 67108864000 895251 67108864000 (Enclosure.Real.IsNear.const Bool.false 895251 1000) hd4949

noncomputable def hp767680 := @hp767677 67108864000 895251 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 895251 1000) 895251 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 895251 1000))) (hp767679 rfl)

noncomputable def hp767681 := @hp767675 9561913622457 67108864000 895251 67108864000 400527496 400527534 33554432 hp767680 rfl rfl rfl

noncomputable def hp767682 := @Enclosure.Real.IsNear.recentre' hp767495 Bool.false 801055030 67108864 38 67108864 400527515 33554432 19 33554432 (hp767681 rfl rfl rfl)

noncomputable def hp767683 := @Enclosure.Real.IsNear.sqrt_image hp767495 400527515 33554432 19 33554432 115928739 115928745 33554432 (hp767682 rfl) rfl rfl

noncomputable def hp767684 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp767495) 57964371 16777216 3 33554432 9711999 9712000 33554432 (hp767674 (hp767683 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp767685 := @hp767669 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp767672 (@hp767673 1 67108864 (hp767684 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp767686 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp767687 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp767688 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1))) (hp767686 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767687 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp767689 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 895251 1000) 895251 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 895251 1000)) rfl

noncomputable def hp767690 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp767691 := @hp767690 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767687 (Enclosure.sfrac Bool.false 1 16)))) 72800173

noncomputable def hp767692 := @hp767691 67108864 291 67108864 24193433 33554432 471783679 45675970560000 1761286107863909 2251799813685248 1996802915643673 139330113471774720000

noncomputable def hp767693 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp767694 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1)))) 61862485

noncomputable def hp767695 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp767696 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 394945483) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp767697 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1))) Bool.false 27791817714269326252465

noncomputable def hp767698 := nat_lit 512735433041807882125680069

noncomputable def hp767699 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp767700 := @Enclosure.Real.IsNear.subLit_ff_p hp767495 (Enclosure.sfrac Bool.false 11 1) 400527515 33554432 19 33554432 11 1 0

noncomputable def hp767701 := @hp767699 500000000000000 31428763 33554432 19 33554432 27791817714269326252465 4722366482869645213696 hp767698 hp682805 hd4948 (@hp767700 1 31428763 31428763 33554432 19 33554432 (hp767682 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp767702 := @hp767696 394945483 67108864 15 4194304 Bool.false 61862485 67108864 1 10890000 (@hp767697 4722366482869645213696 hp767698 hp682805 394945483 67108864 15 4194304 (hp767701 rfl) rfl) (Enclosure.sfrac_false_div 394945483 67108864)

noncomputable def hp767703 := nat_lit 11342212878618676812578816

noncomputable def hp767704 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 394945483) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp767703) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp767705 := BSN.sin_reduce_arg_pos_rat_q3 394945483 67108864 226375608064910080 72057594037927936 0 hp767703 hp617687 rfl rfl rfl rfl

noncomputable def hp767706 := nat_lit 728726731095280405035755072143077048864111291461416770646916510420419618248725918779628724480

noncomputable def hp767707 := nat_lit 455558284649154337689587610077636449474006973016666420567452323205900375913287061701796096

noncomputable def hp767708 := nat_lit 1907832439455350049023099189958409430868762133014064558441957842577813256709470179656272322816

noncomputable def hp767709 := BSN.sin_dyadic_bound_f 161182539366 137438953472 3 2 67108864 21801270 hp767706 hp738039 hp767707 hp767708 hp738042

noncomputable def hp767710 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 161182539366) (BSN.sinEvenQ 137438953472) 0 2 hp767706 hp738039 hp767707 rfl rfl rfl

noncomputable def hp767711 := hp767709 hp767707 61862485 rfl rfl rfl rfl rfl rfl rfl rfl (hp767710 rfl)

noncomputable def hp767712 := @BSN.binarySplit_of_base2 (BSN.sinOddP 161182539366) (BSN.sinOddQ 137438953472) 0 2 hp767708 hp738042 hp767707 rfl rfl rfl

noncomputable def hp767713 := @BSN.sin_arg_round Bool.false 61862485 67108864 hp767703 hp617687 161182539366 137438953472 21801270 21780000 (hp767711 (hp767712 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767714 := hp767704 61862485 67108864 0 1000000000000000 21780000 10890000 hp767705 BSN.pi_near_15 hp767713 rfl rfl

noncomputable def hp767715 := @hp767694 67108864 10471519 2854748160000 36399941 36400232 33554432 (@hp767695 61862485 67108864 167544304 45675970560000 61862485 67108864 10471519 2854748160000 (hp767702 (hp767714 rfl rfl) rfl rfl) rfl)

noncomputable def hp767716 := @hp767693 Bool.false 72800173 67108864 291 67108864 72800173 67108864 291 67108864 (hp767715 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp767717 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767687 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp767718 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767687 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 51373335)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp767719 := nat_lit 121301858696930933347718619605

noncomputable def hp767720 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767687 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp767719

noncomputable def hp767721 := nat_lit 49433836752661713880486693691417133

noncomputable def hp767722 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767687 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp767723 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp767724 := @hp767723 (Enclosure.sfrac Bool.false 1 16) 66807147217447 1125899906842624 1831827563 1125899906842624 1 16 0

noncomputable def hp767725 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1)) 987767143710169

noncomputable def hp767726 := @hp767725 1125899906842624 1194293355 1125899906842624 31428763 33554432 19 33554432 2241675878421814575104 66807147217447 1125899906842624 1831827563

noncomputable def hp767727 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1)) 31428763 33554432 19

noncomputable def hp767728 := @hp767727 33554432 31428763 33554432 19 33554432 987767143710169 1125899906842624 1194293355 1125899906842624 (@hp767700 1 31428763 31428763 33554432 19 33554432 (hp767682 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp767729 := hp767728 (@hp767700 1 31428763 31428763 33554432 19 33554432 (hp767682 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp767730 := @hp767726 1125899906842624 (hp767729 rfl) (@hp767700 1 31428763 31428763 33554432 19 33554432 (hp767682 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp767731 := @hp767722 500000000000000 137175891395111 1125899906842624 1831827563 1125899906842624 hp767719 hp682141 hp767721 hp682143 hd4948 (@hp767724 1 2194814262321776 137175891395111 1125899906842624 1831827563 1125899906842624 (hp767730 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp767732 := @hp767718 51373335 67108864 687 67108864 Bool.false 24193433 33554432 1 10890000 (@hp767720 hp682141 hp767721 hp682143 51373335 67108864 687 67108864 (hp767731 rfl) rfl) (Enclosure.sfrac_true_div 51373335 67108864)

noncomputable def hp767733 := nat_lit 237393399035773907061561781277559537061896725119743821740130690625

noncomputable def hp767734 := nat_lit 48517909233454051607567506364489629771541313052023532437890625

noncomputable def hp767735 := nat_lit 712083161288854813081470208819949631926147092733127418155516290625

noncomputable def hp767736 := BSN.cos_dyadic_bound_f 51373335 67108864 3 2 33554432 10890000 hp767733 hp738066 hp767734 hp767735 hp738069

noncomputable def hp767737 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 51373335) (BSN.cosEvenQ 67108864) 0 2 hp767733 hp738066 hp767734 rfl rfl rfl

noncomputable def hp767738 := hp767736 hp767734 24193433 rfl rfl rfl rfl rfl rfl rfl rfl (hp767737 rfl)

noncomputable def hp767739 := @BSN.binarySplit_of_base2 (BSN.cosOddP 51373335) (BSN.cosOddQ 67108864) 0 2 hp767735 hp738069 hp767734 rfl rfl rfl

noncomputable def hp767740 := hp767732 (BSN.cos_neg_of_bound 51373335 67108864 Bool.false 24193433 33554432 1 10890000 (hp767738 (hp767739 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp767741 := hp767692 hp767716 (@hp767717 24193433 33554432 7548538864 730815528960000 24193433 33554432 471783679 45675970560000 (hp767740 rfl) rfl)

noncomputable def hp767742 := @hp767667 67108864 1761286107863909 2251799813685248 1996802915643673 139330113471774720000 34211219597862460552091 151115727451828646838272 311159035291094269771 hp767491 (hp767685 rfl) (@hp767688 Bool.false 1761286107863909 2251799813685248 1996802915643673 139330113471774720000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767495 (Enclosure.sfrac Bool.false 11 1)) (hp767689 rfl (hp767498 rfl rfl))) (hp767741 rfl))

noncomputable def hp767743 := @hp767492 60842848172876677824331 hp767491 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 895251 1000))) (@hp767497 60842848172876677824331 hp767491 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 895251 1000) 11 (hp767498 rfl rfl)) (@hp767501 60842848172876677824331 hp767491 hp767666 (hp767742 rfl) rfl rfl))

theorem hd5079 : hp767490 hp767491 := hp767743

noncomputable def hp767744 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 896518 1000)) Bool.true 28706274856387143547737 37778931862957161709568 63461597078459511842051

noncomputable def hp767745 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 896518 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 896518 1000)) Bool.true 28706274856387143547737 37778931862957161709568

noncomputable def hp767746 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 896518 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp767747 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp767746 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp767748 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 896518 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp767749 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 896518 1000)) (Enclosure.sfrac Bool.false 896518 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp767747 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp767750 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 896518 1000)) hp767749 Bool.true 28706274856387143547737 37778931862957161709568

noncomputable def hp767751 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 896518 1000) 896518 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 896518 1000)) rfl

noncomputable def hp767752 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 896518 1000)) (Enclosure.sfrac Bool.false 896518 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp767747 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp767753 := nat_lit 3852890990567808695387119681536

noncomputable def hp767754 := @hp767752 133043085 134217728 108763 134217728 8742024395501683066023 37778931862957161709568 320092363748537378051 hp746784 hp767753 28706274856387143547737 37778931862957161709568

noncomputable def hp767755 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 896518 1000)) (Enclosure.sfrac Bool.false 896518 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 896518 1000)) (Enclosure.sfrac Bool.false 896518 1000) 11)

noncomputable def hp767756 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 896518 1000)) (Enclosure.sfrac Bool.false 896518 1000) 11) hp767755

noncomputable def hp767757 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 896518 1000)) (Enclosure.sfrac Bool.false 896518 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 896518 1000)) (Enclosure.sfrac Bool.false 896518 1000) 11)

noncomputable def hp767758 := @hp767757 266086170 536870912 217526 536870912 266086170 536870912 217526 536870912 285707849516974080 133043085 134217728

noncomputable def hp767759 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 896518 1000)) (Enclosure.sfrac Bool.false 896518 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp767760 := hp767759 BSN.quadSignNeg 9 10 11 896518 1000 184 238 536870912 268435456 9007199254740992

noncomputable def hp767761 := hp767760 Bool.false 952946102858 4084 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp767762 := hp767761 Bool.true 329333246 186739 Bool.true 151407031 Bool.true 486571001 28296951008113761 1 Bool.false 515662318

noncomputable def hp767763 := hp767762 Bool.false Bool.false 331064416 Bool.true Bool.true 266086170 217526 BSN.abs_quadSignPos (BSN.cos_quad_nat0 184 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 515662318 536870912) BSN.abs_quadSignNeg

noncomputable def hp767764 := hp767759 BSN.quadSignPos 7 8 9 896518 1000 56 124 536870912 268435456 9007199254740992

noncomputable def hp767765 := hp767764 Bool.false 952946102858 4084 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp767766 := hp767765 Bool.true 560107810 152508 Bool.true 693497760 Bool.true 38750581 28296951008113761 1 Bool.false 147880219

noncomputable def hp767767 := hp767766 Bool.false Bool.false 535473038 Bool.false Bool.true 329333246 186739 BSN.abs_quadSignPos (BSN.cos_quad_nat0 56 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 147880219 536870912) BSN.abs_quadSignPos

noncomputable def hp767768 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 896518 1000)) (Enclosure.sfrac Bool.false 896518 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp767769 := hp767768 BSN.quadSignPos 5 6 7 896518 1000 107 19 536870912 268435456 9007199254740992

noncomputable def hp767770 := hp767769 Bool.false 952946102858 4084 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp767771 := hp767770 Bool.true 796890248 113330 Bool.false 311720890 Bool.false 328487931 28296951008113761 1 Bool.false 294498904

noncomputable def hp767772 := hp767771 Bool.false Bool.false 308372267 Bool.false Bool.true 560107810 152508 BSN.abs_quadSignPos (BSN.cos_quad_nat3 107 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 294498904 536870912) BSN.abs_quadSignPos

noncomputable def hp767773 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 896518 1000)) (Enclosure.sfrac Bool.false 896518 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp767774 := hp767773 BSN.quadSignPos 3 4 5 896518 1000 338 211 536870912 268435456 9007199254740992

noncomputable def hp767775 := hp767774 Bool.false 952946102858 4084 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp767776 := hp767775 Bool.true 857586613 66982 Bool.false 662204914 Bool.false 360980786 28296951008113761 1 Bool.false 177694363

noncomputable def hp767777 := hp767776 Bool.true Bool.false 334389524 Bool.false Bool.true 796890248 113330 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 338 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 177694363 536870912) BSN.abs_quadSignPos

noncomputable def hp767778 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 896518 1000)) (Enclosure.sfrac Bool.false 896518 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp767779 := hp767778 BSN.quadSignNeg 1 2 3 896518 1000 734 502 536870912 268435456 9007199254740992

noncomputable def hp767780 := hp767779 Bool.false 952946102858 4084 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp767781 := hp767780 Bool.true 536870816 4138 Bool.false 331267117 Bool.false 824095261 28296951008113761 1 Bool.false 437871245

noncomputable def hp767782 := hp767781 Bool.true Bool.false 19215490 Bool.true Bool.true 857586613 66982 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 734 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 437871245 536870912) BSN.abs_quadSignNeg

noncomputable def hp767783 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 896518 1000)) (Enclosure.sfrac Bool.false 896518 1000) 1) Bool.true

noncomputable def hp767784 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 896518 1000)) (Enclosure.sfrac Bool.false 896518 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 896518 1000)))

noncomputable def hp767785 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 896518 1000))) Bool.true 67108852 67108864

noncomputable def hp767786 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 896518 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 119118262857) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 119118262857 67108864

noncomputable def hp767787 := nat_lit 1167361205944391738105488008484310498651669652984447392801

noncomputable def hp767788 := nat_lit 657668123505355695520391263488352880300872326709248000

noncomputable def hp767789 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 896518 1000)) Bool.false hp767787 hp767788 7538614773060135373

noncomputable def hp767790 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 896518 4000) (Real.log (Enclosure.sfrac Bool.false 3214979097296 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1793036))))))

noncomputable def hp767791 := nat_lit 277994784186220786164673796592640000

noncomputable def hp767792 := nat_lit 1495364184632662035074625381385778565120

noncomputable def hp767793 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 896518 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp767790 (Enclosure.sfrac Bool.false 896518 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 896518 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp767791 hp767792)) Bool.false

noncomputable def hp767794 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 896518 1000) 896518 1000 3214979097296 16000000 1793036

noncomputable def hp767795 := hp767794 4000 2000 hp767791 hp767792 (@Eq.refl Real (Enclosure.sfrac Bool.false 896518 1000)) rfl rfl rfl rfl

noncomputable def hp767796 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp767790 (Enclosure.sfrac Bool.false 896518 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 896518 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp767791 hp767792) 15987784278495660159829 9007199254740992000

noncomputable def hp767797 := nat_lit 23907557497741142796400394413758679012386194493121482604564480

noncomputable def hp767798 := @hp767796 7538614773060135373 991232000000000000000000 hp767791 hp767792 0 1 hp767797 hp767787 hp767788 7538614773060135373 991232000000000000000000

noncomputable def hp767799 := @Enclosure.Real.IsNear.subLit_ff_p (hp767790 (Enclosure.sfrac Bool.false 896518 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 896518 2000) (Real.log Real.pi)) 20609697722988267909973 9007199254740992000 628138422099013 242000000000000000000

noncomputable def hp767800 := nat_lit 536461020403451691128091312128000

noncomputable def hp767801 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 896518 4000) (Real.log (Enclosure.sfrac Bool.false 3214979097296 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1793036))))))

noncomputable def hp767802 := @hp767801 (Enclosure.sfrac Bool.false 896518 2000) 24647255853719210242901 9007199254740992000 628138422099013 242000000000000000000 896518 2000 0

noncomputable def hp767803 := nat_lit 41219395445976535819946000

noncomputable def hp767804 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 896518 4000) (Real.log (Enclosure.sfrac Bool.false 3214979097296 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1793036))))) 24650791716787052430901

noncomputable def hp767805 := nat_lit 55500686139257555758721537758040424448

noncomputable def hp767806 := @hp767804 9007199254740992000 5603245798618867 2178000000000000000000 883965766960547 2251799813685248 200000001089 8712000000000000000 hp767805 24647255853719210242901 9007199254740992000 628138422099013

noncomputable def hp767807 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 896518 4000) (Real.log (Enclosure.sfrac Bool.false 3214979097296 16000000)) 896518 4000 0 1 54992296232283239 4503599627370496

noncomputable def hp767808 := nat_lit 118095056924800265456975872

noncomputable def hp767809 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3214979097296) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp767808 hp617687

noncomputable def hp767810 := BSN.log_rat_reduce_isNear 3214979097296 16000000 17 6429958194592 4194304000000 114686531 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp767811 := nat_lit 68232810244363824991768390601021604505323022943447699745394708178154282746729875275831671085417267965695419627696749852420178202681545591549067458309689180160

noncomputable def hp767812 := nat_lit 1034759876202909481089123244064652198006012947228485867892449226223144819355061096177541760766540605925698890314904983451035759700224669710410850790384074752

noncomputable def hp767813 := nat_lit 39565812774172195571825202801320615371589512435756947194181874172727830354287416909528331602191939824375419592913181840927332225016754025695354552320

noncomputable def hp767814 := BSN.log_dyadic_bound 1117827097296 5312131097296 7 6 hp767811 268435456 87120000 hp767812 hp767813 114686531 6429958194592

noncomputable def hp767815 := hp767814 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp767816 := @BSN.binarySplit_of_base6 (BSN.artanhP 1117827097296) (BSN.artanhQ 5312131097296) 0 6 hp767812 hp767811 hp767813 rfl rfl rfl

noncomputable def hp767817 := hp767810 rfl rfl rfl rfl (hp767815 (hp767816 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp767818 := @hp767807 12500018513 1089000000000000000 24650791716787052430901 9007199254740992000 5603245798618867 2178000000000000000000 (Enclosure.Real.IsNear.const Bool.false 896518 4000) (BSN.isNear_log_sfrac 3214979097296 16000000 54992296232283239 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp767809 1000001481040000 87120000000000000000000 54992296232283239 4503599627370496 12500018513 1089000000000000000 (hp767817 rfl rfl rfl) rfl)) rfl

noncomputable def hp767819 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1793036)))) 1 4

noncomputable def hp767820 := @hp767819 0 1 883965766960547 562949953421312 200000001089 2178000000000000000 883965766960547 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp767821 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1793036))) 884279719003555 562949953421312 1

noncomputable def hp767822 := @hp767821 2000000000000000 18713 33554432 1 10890000 29660969217805520994304 883965766960547 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp767823 := BSN.arctan_dyadic_bound_f 1000 1793036 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp767824 := hp767823 1 18713 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1793036) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1793036) 0 0 rfl)

noncomputable def hp767825 := hp767820 (hp767822 (hp767824 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp767826 := @hp767799 17217969315099 33554432000 1344777 268435456000 hp767800 15987784278495660159829 9007199254740992000 7538614773060135373 991232000000000000000000 (@hp767802 1 hp767803 20609697722988267909973 9007199254740992000 628138422099013 242000000000000000000 (@hp767806 242000000000000000000 hp767818 hp767825 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 896518 2000) rfl rfl)

noncomputable def hp767827 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 896518 2000) (Real.log Real.pi) 896518 2000 0 1 38410761 33554432

noncomputable def hp767828 := hp767826 (@hp767827 3 268435456 17217969315099 33554432000 1344777 268435456000 (Enclosure.Real.IsNear.const Bool.false 896518 2000) hd4909 rfl) rfl

noncomputable def hp767829 := @hp767789 991232000000000000000000 119118262857 67108864 511 67108864 (@hp767793 hp767787 hp767788 7538614773060135373 991232000000000000000000 (hp767795 rfl rfl rfl rfl rfl) (hp767798 (hp767828 rfl) (Enclosure.Real.IsNear.const Bool.true hp767791 hp767792) rfl rfl)) rfl

noncomputable def hp767830 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 119118262857) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 5674069542100170440704) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp767831 := BSN.sin_reduce_arg_pos_rat_q2 119118262857 67108864 226375608064910080 72057594037927936 282 5674069542100170440704 hp617687 rfl rfl rfl rfl

noncomputable def hp767832 := BSN.cos_dyadic_bound_f 80633377 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp767833 := hp767832 1 67108852 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 80633377) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp767834 := hp767833 (@BSN.binarySplit_of_le (BSN.cosOddP 80633377) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp767835 := @BSN.cos_arg_round Bool.false 67108852 67108864 5674069542100170440704 hp617687 80633377 137438953472 21801270 21780000 hp767834 rfl

noncomputable def hp767836 := hp767830 67108852 67108864 282 1000000000000000 21780000 10890000 hp767831 BSN.pi_near_15 hp767835 rfl rfl

noncomputable def hp767837 := @hp767786 511 67108864 Bool.true 67108852 67108864 1 10890000 hp767829 (Enclosure.sfrac_false_div 119118262857 67108864) (hp767836 rfl rfl) rfl

noncomputable def hp767838 := @hp767783 16777213 16777216 351993679 45675970560000 536870816 536870912 4138 536870912 (@hp767784 Bool.true 16777213 16777216 351993679 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 896518 1000)) (Enclosure.sfrac Bool.false 896518 1000)) (@hp767785 5631898864 730815528960000 16777213 16777216 351993679 45675970560000 (hp767837 rfl) rfl))

noncomputable def hp767839 := @hp767789 991232000000000000000000 952946102858 536870912 4084 536870912 (@hp767793 hp767787 hp767788 7538614773060135373 991232000000000000000000 (hp767795 rfl rfl rfl rfl rfl) (hp767798 (hp767828 rfl) (Enclosure.Real.IsNear.const Bool.true hp767791 hp767792) rfl rfl)) rfl

noncomputable def hp767840 := hp767782 (BSN.cos_quad_nat2 502 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 19215490 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 896518 1000)) rfl rfl (hp767838 rfl) hp767839

noncomputable def hp767841 := nat_lit 1680891037848778253782645885781125835650107177980803292970841852025029921

noncomputable def hp767842 := nat_lit 145019573871664555931481035060929370999466458500398532915100504343841

noncomputable def hp767843 := nat_lit 5042383074398591432236074695273255648208322601025409081846695355066402081

noncomputable def hp767844 := BSN.cos_dyadic_bound_f 331267117 536870912 3 2 536870912 268435456 hp767841 hp708868 hp767842 hp767843 hp708870

noncomputable def hp767845 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 331267117) (BSN.cosEvenQ 536870912) 0 2 hp767841 hp708868 hp767842 rfl rfl rfl

noncomputable def hp767846 := hp767844 hp767842 437871245 rfl rfl rfl rfl rfl rfl rfl rfl (hp767845 rfl)

noncomputable def hp767847 := @BSN.binarySplit_of_base2 (BSN.cosOddP 331267117) (BSN.cosOddQ 536870912) 0 2 hp767843 hp708870 hp767842 rfl rfl rfl

noncomputable def hp767848 := nat_lit 63742319338055566307214879859200392176226997558484148198779887716753296284144378601915852638031158854193648313201

noncomputable def hp767849 := nat_lit 98113552418071781072670740266101570628273115227800359364463176848022965489900716429099841923381920425124721

noncomputable def hp767850 := nat_lit 385853776952365706564625538192768917146052382859706014646529369117425093795415991297801705815316424148261109572465

noncomputable def hp767851 := BSN.cos_dyadic_bound_f 824095261 536870912 4 3 536870912 268435456 hp767848 hp716712 hp767849 hp767850 hp716714

noncomputable def hp767852 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 824095261) (BSN.cosEvenQ 536870912) 0 3 hp767848 hp716712 hp767849 rfl rfl rfl

noncomputable def hp767853 := hp767851 hp767849 19215490 rfl rfl rfl rfl rfl rfl rfl rfl (hp767852 rfl)

noncomputable def hp767854 := @BSN.binarySplit_of_base3 (BSN.cosOddP 824095261) (BSN.cosOddQ 536870912) 0 3 hp767850 hp716714 hp767849 rfl rfl rfl

noncomputable def hp767855 := hp767840 hd4911 hd4913 hd4915 hd4917 hd4918 (hp767846 (hp767847 rfl) rfl rfl rfl rfl) (hp767853 (hp767854 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767856 := hp767777 (BSN.cos_quad_nat3 211 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 334389524 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 896518 1000)) rfl rfl (hp767855 rfl rfl rfl rfl rfl) hp767839

noncomputable def hp767857 := nat_lit 26524816082858577611619161750900081488966330361529656309985650541971231474629042476410990302623586131450221694976

noncomputable def hp767858 := nat_lit 7110641614263442409260473584353299531782808735831207581065519079553758636580645381272130140593526646378496

noncomputable def hp767859 := nat_lit 160769578942861370993996596910623399177385923881612756541081876484335812349277343977898215854853751479884916592640

noncomputable def hp767860 := BSN.cos_dyadic_bound_f 662204914 536870912 4 3 536870912 268435456 hp767857 hp716712 hp767858 hp767859 hp716714

noncomputable def hp767861 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 662204914) (BSN.cosEvenQ 536870912) 0 3 hp767857 hp716712 hp767858 rfl rfl rfl

noncomputable def hp767862 := hp767860 hp767858 177694363 rfl rfl rfl rfl rfl rfl rfl rfl (hp767861 rfl)

noncomputable def hp767863 := @BSN.binarySplit_of_base3 (BSN.cosOddP 662204914) (BSN.cosOddQ 536870912) 0 3 hp767859 hp716714 hp767858 rfl rfl rfl

noncomputable def hp767864 := nat_lit 4266060215932378707840108661915958843545824175000553084941667641316327680

noncomputable def hp767865 := nat_lit 288318619528489094133362298897701271060590494513517234179114339123456

noncomputable def hp767866 := nat_lit 11172548049676993347714544861295962597704965216581760004087125256422277376

noncomputable def hp767867 := BSN.sin_dyadic_bound_f 360980786 536870912 3 2 536870912 268435456 hp767864 hp708845 hp767865 hp767866 hp708848

noncomputable def hp767868 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 360980786) (BSN.sinEvenQ 536870912) 0 2 hp767864 hp708845 hp767865 rfl rfl rfl

noncomputable def hp767869 := hp767867 hp767865 334389524 rfl rfl rfl rfl rfl rfl rfl rfl (hp767868 rfl)

noncomputable def hp767870 := @BSN.binarySplit_of_base2 (BSN.sinOddP 360980786) (BSN.sinOddQ 536870912) 0 2 hp767866 hp708848 hp767865 rfl rfl rfl

noncomputable def hp767871 := hp767856 hd4920 hd4922 hd4924 hd4926 hd4918 (hp767862 (hp767863 rfl) rfl rfl rfl rfl) (hp767869 (hp767870 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767872 := hp767772 (BSN.cos_quad_nat3 19 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 308372267 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 896518 1000)) rfl rfl (hp767871 rfl rfl rfl rfl rfl) hp767839

noncomputable def hp767873 := nat_lit 2372145021471392653009292421069114850573677604979132003152629135982240000

noncomputable def hp767874 := nat_lit 89151213748021772279671864880510545336917002462904651760608100000000

noncomputable def hp767875 := nat_lit 6212616430459960151202551157875970448714800623608024829296892466839200000

noncomputable def hp767876 := BSN.sin_dyadic_bound_f 311720890 536870912 3 2 536870912 268435456 hp767873 hp708845 hp767874 hp767875 hp708848

noncomputable def hp767877 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 311720890) (BSN.sinEvenQ 536870912) 0 2 hp767873 hp708845 hp767874 rfl rfl rfl

noncomputable def hp767878 := hp767876 hp767874 294498904 rfl rfl rfl rfl rfl rfl rfl rfl (hp767877 rfl)

noncomputable def hp767879 := @BSN.binarySplit_of_base2 (BSN.sinOddP 311720890) (BSN.sinOddQ 536870912) 0 2 hp767875 hp708848 hp767874 rfl rfl rfl

noncomputable def hp767880 := nat_lit 2925223693004489606977537651924411571845526006069053921247351137100617185

noncomputable def hp767881 := nat_lit 135567423408941060967179218122361561985041806224064233947569322972641

noncomputable def hp767882 := nat_lit 7661080658231001161318651750591736959923639948208873689745242627788232161

noncomputable def hp767883 := BSN.sin_dyadic_bound_f 328487931 536870912 3 2 536870912 268435456 hp767880 hp708845 hp767881 hp767882 hp708848

noncomputable def hp767884 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 328487931) (BSN.sinEvenQ 536870912) 0 2 hp767880 hp708845 hp767881 rfl rfl rfl

noncomputable def hp767885 := hp767883 hp767881 308372267 rfl rfl rfl rfl rfl rfl rfl rfl (hp767884 rfl)

noncomputable def hp767886 := @BSN.binarySplit_of_base2 (BSN.sinOddP 328487931) (BSN.sinOddQ 536870912) 0 2 hp767882 hp708848 hp767881 rfl rfl rfl

noncomputable def hp767887 := hp767872 hd4928 hd4930 hd4932 hd4934 hd4918 (hp767878 (hp767879 rfl) rfl rfl rfl rfl) (hp767885 (hp767886 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767888 := hp767767 (BSN.cos_quad_nat0 124 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 535473038 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 896518 1000)) rfl rfl (hp767887 rfl rfl rfl rfl rfl) hp767839

noncomputable def hp767889 := nat_lit 31914223332727767295370110795011056552643495716236774369473761558874965653041688882632140705819980688523264000000

noncomputable def hp767890 := nat_lit 12374873030977004003387371916021407517347997077845293545490843467049173590999017740928261554176000000000000

noncomputable def hp767891 := nat_lit 193399334447456022487671958471922758976364894909229219214679495021131313291524449680761622935222559736175001600000

noncomputable def hp767892 := BSN.cos_dyadic_bound_f 693497760 536870912 4 3 536870912 268435456 hp767889 hp716712 hp767890 hp767891 hp716714

noncomputable def hp767893 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 693497760) (BSN.cosEvenQ 536870912) 0 3 hp767889 hp716712 hp767890 rfl rfl rfl

noncomputable def hp767894 := hp767892 hp767890 147880219 rfl rfl rfl rfl rfl rfl rfl rfl (hp767893 rfl)

noncomputable def hp767895 := @BSN.binarySplit_of_base3 (BSN.cosOddP 693497760) (BSN.cosOddQ 536870912) 0 3 hp767891 hp716714 hp767890 rfl rfl rfl

noncomputable def hp767896 := nat_lit 2254825167658431533544802428721

noncomputable def hp767897 := BSN.cos_dyadic_bound_f 38750581 536870912 2 1 536870912 268435456 hp767896 hp708767 hp767896 hp767896 hp708768

noncomputable def hp767898 := @BSN.binarySplit_of_base (BSN.cosEvenP 38750581) (BSN.cosEvenQ 536870912) 0 1 hp767896 hp708767 hp767896 rfl rfl rfl

noncomputable def hp767899 := hp767897 hp767896 535473038 rfl rfl rfl rfl rfl rfl rfl rfl (hp767898 rfl)

noncomputable def hp767900 := @BSN.binarySplit_of_base (BSN.cosOddP 38750581) (BSN.cosOddQ 536870912) 0 1 hp767896 hp708768 hp767896 rfl rfl rfl

noncomputable def hp767901 := hp767888 hd4936 hd4938 hd4940 hd4942 hd4918 (hp767894 (hp767895 rfl) rfl rfl rfl rfl) (hp767899 (hp767900 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767902 := hp767763 (BSN.cos_quad_nat2 238 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 331064416 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 896518 1000)) rfl rfl (hp767901 rfl rfl rfl rfl rfl) hp767839

noncomputable def hp767903 := nat_lit 73345688068312714978355642034117084766263537528231906228936786048563521

noncomputable def hp767904 := nat_lit 276164815098478646453911243572395162867833578976639918241656453441

noncomputable def hp767905 := nat_lit 220036511875307947977774018279864109508464876917537765406973874832783681

noncomputable def hp767906 := BSN.cos_dyadic_bound_f 151407031 536870912 3 2 536870912 268435456 hp767903 hp708868 hp767904 hp767905 hp708870

noncomputable def hp767907 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 151407031) (BSN.cosEvenQ 536870912) 0 2 hp767903 hp708868 hp767904 rfl rfl rfl

noncomputable def hp767908 := hp767906 hp767904 515662318 rfl rfl rfl rfl rfl rfl rfl rfl (hp767907 rfl)

noncomputable def hp767909 := @BSN.binarySplit_of_base2 (BSN.cosOddP 151407031) (BSN.cosOddQ 536870912) 0 2 hp767905 hp708870 hp767904 rfl rfl rfl

noncomputable def hp767910 := nat_lit 7826147796548955184810991122899159154146741347267486482215893861893068481

noncomputable def hp767911 := nat_lit 3141736631882960960155525237940252569837889173156995431762485040568001

noncomputable def hp767912 := nat_lit 23472159916383099632512662318221596957300548263456145455784156615598069441

noncomputable def hp767913 := BSN.cos_dyadic_bound_f 486571001 536870912 3 2 536870912 268435456 hp767910 hp708868 hp767911 hp767912 hp708870

noncomputable def hp767914 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 486571001) (BSN.cosEvenQ 536870912) 0 2 hp767910 hp708868 hp767911 rfl rfl rfl

noncomputable def hp767915 := hp767913 hp767911 331064416 rfl rfl rfl rfl rfl rfl rfl rfl (hp767914 rfl)

noncomputable def hp767916 := @BSN.binarySplit_of_base2 (BSN.cosOddP 486571001) (BSN.cosOddQ 536870912) 0 2 hp767912 hp708870 hp767911 rfl rfl rfl

noncomputable def hp767917 := hp767902 hd4944 hd4946 hd4961 hd4963 hd4918 (hp767908 (hp767909 rfl) rfl rfl rfl rfl) (hp767915 (hp767916 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767918 := @hp767758 108763 134217728 (hp767917 rfl rfl rfl rfl rfl) (hp767917 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp767919 := @hp767756 Bool.true 133043085 134217728 108763 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 896518 1000)) (Enclosure.sfrac Bool.false 896518 1000) 11) hp767918

noncomputable def hp767920 := @Enclosure.Real.IsNear.mulLit_tf hp767747 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1))) 19417133 67108864 1

noncomputable def hp767921 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp767746 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp767922 := @hp767921 1 1 0 1 19417133 67108864 1 67108864 19417133 67108864 1

noncomputable def hp767923 := @Enclosure.Real.IsNear.of_eq (hp767746 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp767924 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 896518 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp767925 := @hp767923 (@Inv.inv Real Real.instInv (Real.sqrt hp767748)) Bool.false 19417133 67108864 1 67108864 (hp767924 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 896518 1000) 896518 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 896518 1000))))

noncomputable def hp767926 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp767748)) Bool.false 19417133 67108864 1 67108864 19417133 67108864

noncomputable def hp767927 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp767748) Bool.false 231939475 67108864 7 67108864 231939475 67108864 7 67108864

noncomputable def hp767928 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 896518 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp767929 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 896518 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp767930 := @hp767929 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 896518 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 4787723039113

noncomputable def hp767931 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 896518 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 896518 1000 0

noncomputable def hp767932 := @hp767931 1 10680707 67108864 1 67108864 4787723039113 33554432000 448259 33554432000 (Enclosure.Real.IsNear.const Bool.false 896518 1000) hd4949

noncomputable def hp767933 := @hp767930 33554432000 448259 33554432000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 896518 1000) 896518 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 896518 1000))) (hp767932 rfl)

noncomputable def hp767934 := @hp767928 4787723039113 33554432000 448259 33554432000 400810818 400810856 33554432 hp767933 rfl rfl rfl

noncomputable def hp767935 := @Enclosure.Real.IsNear.recentre' hp767748 Bool.false 801621674 67108864 38 67108864 400810837 33554432 19 33554432 (hp767934 rfl rfl rfl)

noncomputable def hp767936 := @Enclosure.Real.IsNear.sqrt_image hp767748 400810837 33554432 19 33554432 115969734 115969741 33554432 (hp767935 rfl) rfl rfl

noncomputable def hp767937 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp767748) 231939475 67108864 7 67108864 9708566 9708567 33554432 (hp767927 (hp767936 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp767938 := @hp767922 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp767925 (@hp767926 1 67108864 (hp767937 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp767939 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp767940 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp767941 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1))) (hp767939 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767940 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp767942 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 896518 1000) 896518 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 896518 1000)) rfl

noncomputable def hp767943 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp767944 := @hp767943 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767940 (Enclosure.sfrac Bool.false 1 16)))) 35655231

noncomputable def hp767945 := @hp767944 33554432 139 33554432 12627101 16777216 474506179 45675970560000 450222203015331 562949953421312 2169713564320873 153263124818952192000

noncomputable def hp767946 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp767947 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1)))) 63154823

noncomputable def hp767948 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp767949 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 398505813) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp767950 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1))) Bool.false 28042353612816851462175

noncomputable def hp767951 := nat_lit 512735433044241599574154693

noncomputable def hp767952 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp767953 := @Enclosure.Real.IsNear.subLit_ff_p hp767748 (Enclosure.sfrac Bool.false 11 1) 400810837 33554432 19 33554432 11 1 0

noncomputable def hp767954 := @hp767952 500000000000000 31712085 33554432 19 33554432 28042353612816851462175 4722366482869645213696 hp767951 hp682805 hd4948 (@hp767953 1 31712085 31712085 33554432 19 33554432 (hp767935 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp767955 := @hp767949 398505813 67108864 239 67108864 Bool.false 63154823 67108864 1 10890000 (@hp767950 4722366482869645213696 hp767951 hp682805 398505813 67108864 239 67108864 (hp767954 rfl) rfl) (Enclosure.sfrac_false_div 398505813 67108864)

noncomputable def hp767956 := nat_lit 11855310506180788749336576

noncomputable def hp767957 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 398505813) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp767956) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp767958 := BSN.sin_reduce_arg_pos_rat_q3 398505813 67108864 226375608064910080 72057594037927936 0 hp767956 hp617687 rfl rfl rfl rfl

noncomputable def hp767959 := nat_lit 869916997059760664961074710570743418293214719703309435694211651687474161122477867107445776640

noncomputable def hp767960 := nat_lit 649030432956279912090331444403874242087899243756555067719874041826525396591502306799657216

noncomputable def hp767961 := nat_lit 2277303228741253478849906562489578870566467667114014099565674529780427476107246267260872827136

noncomputable def hp767962 := BSN.sin_dyadic_bound_f 168474095206 137438953472 3 2 67108864 21801270 hp767959 hp738039 hp767960 hp767961 hp738042

noncomputable def hp767963 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 168474095206) (BSN.sinEvenQ 137438953472) 0 2 hp767959 hp738039 hp767960 rfl rfl rfl

noncomputable def hp767964 := hp767962 hp767960 63154823 rfl rfl rfl rfl rfl rfl rfl rfl (hp767963 rfl)

noncomputable def hp767965 := @BSN.binarySplit_of_base2 (BSN.sinOddP 168474095206) (BSN.sinOddQ 137438953472) 0 2 hp767961 hp738042 hp767960 rfl rfl rfl

noncomputable def hp767966 := @BSN.sin_arg_round Bool.false 63154823 67108864 hp767956 hp617687 168474095206 137438953472 21801270 21780000 (hp767964 (hp767965 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp767967 := hp767957 63154823 67108864 0 1000000000000000 21780000 10890000 hp767958 BSN.pi_near_15 hp767966 rfl rfl

noncomputable def hp767968 := @hp767947 67108864 166863679 45675970560000 35655092 35655370 33554432 (@hp767948 63154823 67108864 2669818864 730815528960000 63154823 67108864 166863679 45675970560000 (hp767955 (hp767967 rfl rfl) rfl rfl) rfl)

noncomputable def hp767969 := @hp767946 Bool.false 71310462 67108864 278 67108864 35655231 33554432 139 33554432 (hp767968 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp767970 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767940 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp767971 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767940 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 12058509)) (@Nat.cast Real Real.instNatCast 16777216)) Bool.true

noncomputable def hp767972 := nat_lit 113889399379570056722751320245

noncomputable def hp767973 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767940 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp767972

noncomputable def hp767974 := nat_lit 49724375209157273631394741418907761

noncomputable def hp767975 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp767940 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp767976 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp767977 := @hp767976 (Enclosure.sfrac Bool.false 1 16) 58424664663495 1125899906842624 1842593799 1125899906842624 1 16 0

noncomputable def hp767978 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1)) 1005656335047225

noncomputable def hp767979 := @hp767978 1125899906842624 1205059591 1125899906842624 31712085 33554432 19 33554432 1960406437574045859840 58424664663495 1125899906842624 1842593799

noncomputable def hp767980 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1)) 31712085 33554432 19

noncomputable def hp767981 := @hp767980 33554432 31712085 33554432 19 33554432 1005656335047225 1125899906842624 1205059591 1125899906842624 (@hp767953 1 31712085 31712085 33554432 19 33554432 (hp767935 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp767982 := hp767981 (@hp767953 1 31712085 31712085 33554432 19 33554432 (hp767935 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp767983 := @hp767979 1125899906842624 (hp767982 rfl) (@hp767953 1 31712085 31712085 33554432 19 33554432 (hp767935 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp767984 := @hp767975 500000000000000 128793408841159 1125899906842624 1842593799 1125899906842624 hp767972 hp682141 hp767974 hp682143 hd4948 (@hp767977 1 2060694541458544 128793408841159 1125899906842624 1842593799 1125899906842624 (hp767983 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp767985 := @hp767971 12058509 16777216 691 67108864 Bool.false 25254202 33554432 1 10890000 (@hp767973 hp682141 hp767974 hp682143 12058509 16777216 691 67108864 (hp767984 rfl) rfl) (Enclosure.sfrac_true_div 12058509 16777216)

noncomputable def hp767986 := nat_lit 2814701177774124789591618318776056455881810980827651164372001

noncomputable def hp767987 := nat_lit 447042584117140716277877053539327032170573176900439538721

noncomputable def hp767988 := nat_lit 8443209448154140087342299202221090713581091796129152614038561

noncomputable def hp767989 := BSN.cos_dyadic_bound_f 12058509 16777216 3 2 33554432 10890000 hp767986 hp631348 hp767987 hp767988 hp631351

noncomputable def hp767990 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 12058509) (BSN.cosEvenQ 16777216) 0 2 hp767986 hp631348 hp767987 rfl rfl rfl

noncomputable def hp767991 := hp767989 hp767987 25254202 rfl rfl rfl rfl rfl rfl rfl rfl (hp767990 rfl)

noncomputable def hp767992 := @BSN.binarySplit_of_base2 (BSN.cosOddP 12058509) (BSN.cosOddQ 16777216) 0 2 hp767988 hp631351 hp767987 rfl rfl rfl

noncomputable def hp767993 := hp767985 (BSN.cos_neg_of_bound 12058509 16777216 Bool.false 25254202 33554432 1 10890000 (hp767991 (hp767992 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp767994 := hp767945 hp767969 (@hp767970 25254202 33554432 7592098864 730815528960000 12627101 16777216 474506179 45675970560000 (hp767993 rfl) rfl)

noncomputable def hp767995 := @hp767920 67108864 450222203015331 562949953421312 2169713564320873 153263124818952192000 8742024395501683066023 37778931862957161709568 320092363748537378051 hp746784 (hp767938 rfl) (@hp767941 Bool.false 450222203015331 562949953421312 2169713564320873 153263124818952192000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp767748 (Enclosure.sfrac Bool.false 11 1)) (hp767942 rfl (hp767751 rfl rfl))) (hp767994 rfl))

noncomputable def hp767996 := @hp767745 63461597078459511842051 hp746784 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 896518 1000))) (@hp767750 63461597078459511842051 hp746784 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 896518 1000) 11 (hp767751 rfl rfl)) (@hp767754 63461597078459511842051 hp746784 hp767919 (hp767995 rfl) rfl rfl))

theorem hd5080 : hp767744 hp746784 := hp767996

noncomputable def hp767997 := nat_lit 4198011428289153937617517

noncomputable def hp767998 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 898496 1000)) Bool.false 210791723592354924923981 37778931862957161709568 hp767997

noncomputable def hp767999 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 898496 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 898496 1000)) Bool.false 210791723592354924923981 37778931862957161709568

noncomputable def hp768000 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 898496 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp768001 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp768000 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp768002 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 898496 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp768003 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 898496 1000)) (Enclosure.sfrac Bool.false 898496 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp768001 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp768004 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 898496 1000)) hp768003 Bool.false 210791723592354924923981 37778931862957161709568

noncomputable def hp768005 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 898496 1000) 898496 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 898496 1000)) rfl

noncomputable def hp768006 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 898496 1000)) (Enclosure.sfrac Bool.false 898496 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp768001 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp768007 := nat_lit 28291986221769876192907302535168

noncomputable def hp768008 := @hp768006 716745041 134217728 109003 134217728 9045929869401745067085 37778931862957161709568 21476329629092491473517 hp743344 hp768007 210791723592354924923981 37778931862957161709568

noncomputable def hp768009 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 898496 1000)) (Enclosure.sfrac Bool.false 898496 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 898496 1000)) (Enclosure.sfrac Bool.false 898496 1000) 11)

noncomputable def hp768010 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 898496 1000)) (Enclosure.sfrac Bool.false 898496 1000) 11) hp768009

noncomputable def hp768011 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 898496 1000)) (Enclosure.sfrac Bool.false 898496 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 898496 1000)) (Enclosure.sfrac Bool.false 898496 1000) 11)

noncomputable def hp768012 := @hp768011 1433490082 536870912 218006 536870912 1433490082 536870912 218006 536870912 1539198255332589568 716745041 134217728

noncomputable def hp768013 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 898496 1000)) (Enclosure.sfrac Bool.false 898496 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp768014 := hp768013 BSN.quadSignNeg 9 10 11 898496 1000 183 238 536870912 268435456 9007199254740992

noncomputable def hp768015 := hp768014 Bool.false 955580616457 4093 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp768016 := hp768015 Bool.false 1383439342 187151 Bool.true 805393999 Bool.true 398455917 28296951008113761 1 Bool.false 535532234

noncomputable def hp768017 := hp768016 Bool.false Bool.false 395671456 Bool.true Bool.false 1433490082 218006 BSN.abs_quadSignPos (BSN.cos_quad_nat3 183 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 535532234 536870912) BSN.abs_quadSignNeg

noncomputable def hp768018 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 898496 1000)) (Enclosure.sfrac Bool.false 898496 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp768019 := hp768018 BSN.quadSignPos 7 8 9 898496 1000 56 123 536870912 268435456 9007199254740992

noncomputable def hp768020 := hp768019 Bool.false 955580616457 4093 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp768021 := hp768020 Bool.false 1058661121 152845 Bool.true 267206896 Bool.true 580851963 28296951008113761 1 Bool.false 471736319

noncomputable def hp768022 := hp768021 Bool.false Bool.false 473982735 Bool.false Bool.false 1383439342 187151 BSN.abs_quadSignPos (BSN.cos_quad_nat0 56 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 471736319 536870912) BSN.abs_quadSignPos

noncomputable def hp768023 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 898496 1000)) (Enclosure.sfrac Bool.false 898496 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp768024 := hp768023 BSN.quadSignPos 5 6 7 898496 1000 108 20 536870912 268435456 9007199254740992

noncomputable def hp768025 := hp768024 Bool.false 955580616457 4093 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp768026 := hp768025 Bool.false 652626636 113580 Bool.false 200195325 Bool.false 53265048 28296951008113761 1 Bool.false 499975718

noncomputable def hp768027 := hp768026 Bool.false Bool.false 534230762 Bool.false Bool.false 1058661121 152845 BSN.abs_quadSignPos (BSN.cos_quad_nat0 108 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 499975718 536870912) BSN.abs_quadSignPos

noncomputable def hp768028 := hp768023 BSN.quadSignPos 3 4 5 898496 1000 340 212 536870912 268435456 9007199254740992

noncomputable def hp768029 := hp768028 Bool.false 955580616457 4093 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp768030 := hp768029 Bool.false 230133288 67129 Bool.false 137940336 Bool.false 443068089 28296951008113761 1 Bool.false 519247409

noncomputable def hp768031 := hp768030 Bool.false Bool.false 364187604 Bool.false Bool.false 652626636 113580 BSN.abs_quadSignPos (BSN.cos_quad_nat0 340 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 519247409 536870912) BSN.abs_quadSignPos

noncomputable def hp768032 := hp768023 BSN.quadSignPos 1 2 3 898496 1000 736 504 536870912 268435456 9007199254740992

noncomputable def hp768033 := hp768032 Bool.false 955580616457 4093 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp768034 := hp768033 Bool.true 104218104 4146 Bool.false 543076787 Bool.false 605329080 28296951008113761 1 Bool.false 284831264

noncomputable def hp768035 := hp768034 Bool.false Bool.false 230267966 Bool.false Bool.false 230133288 67129 BSN.abs_quadSignPos (BSN.cos_quad_nat0 736 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 284831264 536870912) BSN.abs_quadSignPos

noncomputable def hp768036 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 898496 1000)) (Enclosure.sfrac Bool.false 898496 1000) 1) Bool.true

noncomputable def hp768037 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 898496 1000)) (Enclosure.sfrac Bool.false 898496 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 898496 1000)))

noncomputable def hp768038 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 898496 1000))) Bool.true 13027263 67108864

noncomputable def hp768039 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 898496 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 119447577057) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 119447577057 67108864

noncomputable def hp768040 := nat_lit 289592364368307187420997897970495181004876543194450453

noncomputable def hp768041 := nat_lit 162700785354014905718143892610315982734939389952000

noncomputable def hp768042 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 898496 1000)) Bool.false hp768040 hp768041 2124899189064551297

noncomputable def hp768043 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 898496 4000) (Real.log (Enclosure.sfrac Bool.false 3229181248064 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1796992))))))

noncomputable def hp768044 := nat_lit 281075063976984004272993381908480000

noncomputable def hp768045 := nat_lit 1515269143078615010884999228737465876480

noncomputable def hp768046 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 898496 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp768043 (Enclosure.sfrac Bool.false 898496 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 898496 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp768044 hp768045)) Bool.false

noncomputable def hp768047 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 898496 1000) 898496 1000 3229181248064 16000000 1796992

noncomputable def hp768048 := hp768047 4000 2000 hp768044 hp768045 (@Eq.refl Real (Enclosure.sfrac Bool.false 898496 1000)) rfl rfl rfl rfl

noncomputable def hp768049 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp768043 (Enclosure.sfrac Bool.false 898496 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 898496 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp768044 hp768045) 250499751226659209717 140737488355328000

noncomputable def hp768050 := nat_lit 379574503824827596696450364827887443646711782695830097756160

noncomputable def hp768051 := @hp768049 2124899189064551297 278784000000000000000000 hp768044 hp768045 0 1 hp768050 hp768040 hp768041 2124899189064551297 278784000000000000000000

noncomputable def hp768052 := @Enclosure.Real.IsNear.subLit_ff_p (hp768043 (Enclosure.sfrac Bool.false 898496 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 898496 2000) (Real.log Real.pi)) 322876483034867991029 140737488355328000 2832804158600237 1089000000000000000000

noncomputable def hp768053 := nat_lit 262668027142245407488212992000

noncomputable def hp768054 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 898496 4000) (Real.log (Enclosure.sfrac Bool.false 3229181248064 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1796992))))))

noncomputable def hp768055 := @hp768054 (Enclosure.sfrac Bool.false 898496 2000) 386102518203522384373 140737488355328000 2832804158600237 1089000000000000000000 898496 2000 0

noncomputable def hp768056 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 898496 4000) (Real.log (Enclosure.sfrac Bool.false 3229181248064 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1796992))))) 772315532213898069121

noncomputable def hp768057 := nat_lit 1738851157108193558932725658191659008

noncomputable def hp768058 := @hp768056 281474976710656000 175487759904007 68062500000000000000 883966454826403 2251799813685248 200000001089 8712000000000000000 hp768057 386102518203522384373 140737488355328000 2832804158600237

noncomputable def hp768059 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 898496 4000) (Real.log (Enclosure.sfrac Bool.false 3229181248064 16000000)) 898496 4000 0 1 55012147034254439 4503599627370496

noncomputable def hp768060 := nat_lit 118137686197433103623913472

noncomputable def hp768061 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3229181248064) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp768060 hp617687

noncomputable def hp768062 := BSN.log_rat_reduce_isNear 3229181248064 16000000 17 6458362496128 4194304000000 115869731 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp768063 := nat_lit 70454358822933958236380314049089638065054078498778058266163533199778892413184171603643446337871042589265258971291650359611642904267211389195926603685649448960

noncomputable def hp768064 := nat_lit 1090541281442679815186480080858658758110386185195136934508741496199302092067233368250656447041434877939816409660799936204411510723945214056752626288780378112

noncomputable def hp768065 := nat_lit 46037980774595246579908646194205503579665660619134063343858636726156265523891138355829358450485264857236240675645686991367435300313706750631917649920

noncomputable def hp768066 := BSN.log_dyadic_bound 1132029248064 5326333248064 7 6 hp768063 268435456 87120000 hp768064 hp768065 115869731 6458362496128

noncomputable def hp768067 := hp768066 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp768068 := @BSN.binarySplit_of_base6 (BSN.artanhP 1132029248064) (BSN.artanhQ 5326333248064) 0 6 hp768064 hp768063 hp768065 rfl rfl rfl

noncomputable def hp768069 := hp768062 rfl rfl rfl rfl (hp768067 (hp768068 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp768070 := @hp768059 12500018513 1089000000000000000 772315532213898069121 281474976710656000 175487759904007 68062500000000000000 (Enclosure.Real.IsNear.const Bool.false 898496 4000) (BSN.isNear_log_sfrac 3229181248064 16000000 55012147034254439 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp768061 1000001481040000 87120000000000000000000 55012147034254439 4503599627370496 12500018513 1089000000000000000 (hp768069 rfl rfl rfl) rfl)) rfl

noncomputable def hp768071 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1796992)))) 1 4

noncomputable def hp768072 := @hp768071 0 1 883966454826403 562949953421312 200000001089 2178000000000000000 883966454826403 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp768073 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1796992))) 884279719003555 562949953421312 1

noncomputable def hp768074 := @hp768073 2000000000000000 18672 33554432 1 10890000 29660992298753611268096 883966454826403 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp768075 := BSN.arctan_dyadic_bound_f 1000 1796992 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp768076 := hp768075 1 18672 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1796992) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1796992) 0 0 rfl)

noncomputable def hp768077 := hp768072 (hp768074 (hp768076 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp768078 := @hp768052 539248673679 1048576000 42117 8388608000 hp768053 250499751226659209717 140737488355328000 2124899189064551297 278784000000000000000000 (@hp768055 1 645752966069735982058000 322876483034867991029 140737488355328000 2832804158600237 1089000000000000000000 (@hp768058 1089000000000000000000 hp768070 hp768077 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 898496 2000) rfl rfl)

noncomputable def hp768079 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 898496 2000) (Real.log Real.pi) 898496 2000 0 1 38410761 33554432

noncomputable def hp768080 := hp768078 (@hp768079 3 268435456 539248673679 1048576000 42117 8388608000 (Enclosure.Real.IsNear.const Bool.false 898496 2000) hd4909 rfl) rfl

noncomputable def hp768081 := @hp768042 278784000000000000000000 119447577057 67108864 1 131072 (@hp768046 hp768040 hp768041 2124899189064551297 278784000000000000000000 (hp768048 rfl rfl rfl rfl rfl) (hp768051 (hp768080 rfl) (Enclosure.Real.IsNear.const Bool.true hp768044 hp768045) rfl rfl)) rfl

noncomputable def hp768082 := nat_lit 1889422254956054780575744

noncomputable def hp768083 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 119447577057) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp768082) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp768084 := BSN.sin_reduce_arg_pos_rat_q1 119447577057 67108864 226375608064910080 72057594037927936 283 hp768082 hp617687 rfl rfl rfl rfl

noncomputable def hp768085 := nat_lit 519752879055722968351433800909037775360000

noncomputable def hp768086 := BSN.sin_dyadic_bound_f 26850305160 137438953472 2 1 67108864 21801270 hp768085 hp749778 hp768085 hp768085 hp749779

noncomputable def hp768087 := @BSN.binarySplit_of_base (BSN.sinEvenP 26850305160) (BSN.sinEvenQ 137438953472) 0 1 hp768085 hp749778 hp768085 rfl rfl rfl

noncomputable def hp768088 := hp768086 hp768085 13027263 rfl rfl rfl rfl rfl rfl rfl rfl (hp768087 rfl)

noncomputable def hp768089 := @BSN.binarySplit_of_base (BSN.sinOddP 26850305160) (BSN.sinOddQ 137438953472) 0 1 hp768085 hp749779 hp768085 rfl rfl rfl

noncomputable def hp768090 := @BSN.sin_arg_round Bool.false 13027263 67108864 hp768082 hp617687 26850305160 137438953472 21801270 21780000 (hp768088 (hp768089 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768091 := hp768083 13027263 67108864 283 1000000000000000 21780000 10890000 hp768084 BSN.pi_near_15 hp768090 rfl rfl

noncomputable def hp768092 := @hp768039 1 131072 Bool.true 13027263 67108864 1 10890000 hp768081 (Enclosure.sfrac_false_div 119447577057 67108864) (hp768091 rfl rfl) rfl

noncomputable def hp768093 := @hp768036 13027263 67108864 688817 89210880000 104218104 536870912 4146 536870912 (@hp768037 Bool.true 13027263 67108864 688817 89210880000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 898496 1000)) (Enclosure.sfrac Bool.false 898496 1000)) (@hp768038 11021072 1427374080000 13027263 67108864 688817 89210880000 (hp768092 rfl) rfl))

noncomputable def hp768094 := @hp768042 278784000000000000000000 955580616457 536870912 4093 536870912 (@hp768046 hp768040 hp768041 2124899189064551297 278784000000000000000000 (hp768048 rfl rfl rfl rfl rfl) (hp768051 (hp768080 rfl) (Enclosure.Real.IsNear.const Bool.true hp768044 hp768045) rfl rfl)) rfl

noncomputable def hp768095 := hp768035 (BSN.cos_quad_nat0 504 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 230267966 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 898496 1000)) rfl rfl (hp768093 rfl) hp768094

noncomputable def hp768096 := nat_lit 11989478296890446158040179110619308471561830524934546979458054587755648313428361482402844554220214933112850806961

noncomputable def hp768097 := nat_lit 658165144743442162144661062952011044833320336312534363379466211890628536956356675201674662980242548783281

noncomputable def hp768098 := nat_lit 72705962371924026272432005966243687742913903616986629172031328116988646652251446101393306000404070638134094788785

noncomputable def hp768099 := BSN.cos_dyadic_bound_f 543076787 536870912 4 3 536870912 268435456 hp768096 hp716712 hp768097 hp768098 hp716714

noncomputable def hp768100 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 543076787) (BSN.cosEvenQ 536870912) 0 3 hp768096 hp716712 hp768097 rfl rfl rfl

noncomputable def hp768101 := hp768099 hp768097 284831264 rfl rfl rfl rfl rfl rfl rfl rfl (hp768100 rfl)

noncomputable def hp768102 := @BSN.binarySplit_of_base3 (BSN.cosOddP 543076787) (BSN.cosOddQ 536870912) 0 3 hp768098 hp716714 hp768097 rfl rfl rfl

noncomputable def hp768103 := nat_lit 18512646891809452124340624371526085167475167895492305979024210375213234587755924466930877985202627353247744000000

noncomputable def hp768104 := nat_lit 2420463037406639156012680579588497937356747067109627023489908504031388745991836370161773838336000000000000

noncomputable def hp768105 := nat_lit 112238086215946447995719923865793054341029677920048091604528267659287577350248773366501776257409008159791513600000

noncomputable def hp768106 := BSN.cos_dyadic_bound_f 605329080 536870912 4 3 536870912 268435456 hp768103 hp716712 hp768104 hp768105 hp716714

noncomputable def hp768107 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 605329080) (BSN.cosEvenQ 536870912) 0 3 hp768103 hp716712 hp768104 rfl rfl rfl

noncomputable def hp768108 := hp768106 hp768104 230267966 rfl rfl rfl rfl rfl rfl rfl rfl (hp768107 rfl)

noncomputable def hp768109 := @BSN.binarySplit_of_base3 (BSN.cosOddP 605329080) (BSN.cosOddQ 536870912) 0 3 hp768105 hp716714 hp768104 rfl rfl rfl

noncomputable def hp768110 := hp768095 hd4911 hd4913 hd4915 hd4917 hd4918 (hp768101 (hp768102 rfl) rfl rfl rfl rfl) (hp768108 (hp768109 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768111 := hp768031 (BSN.cos_quad_nat0 212 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 364187604 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 898496 1000)) rfl rfl (hp768110 rfl rfl rfl rfl rfl) hp768094

noncomputable def hp768112 := nat_lit 362047137487716041861949324066816

noncomputable def hp768113 := BSN.cos_dyadic_bound_f 137940336 536870912 2 1 536870912 268435456 hp768112 hp708767 hp768112 hp768112 hp708768

noncomputable def hp768114 := @BSN.binarySplit_of_base (BSN.cosEvenP 137940336) (BSN.cosEvenQ 536870912) 0 1 hp768112 hp708767 hp768112 rfl rfl rfl

noncomputable def hp768115 := hp768113 hp768112 519247409 rfl rfl rfl rfl rfl rfl rfl rfl (hp768114 rfl)

noncomputable def hp768116 := @BSN.binarySplit_of_base (BSN.cosOddP 137940336) (BSN.cosOddQ 536870912) 0 1 hp768112 hp708768 hp768112 rfl rfl rfl

noncomputable def hp768117 := nat_lit 5380102707126263378718730951413679665837660606037278259882102522289773761

noncomputable def hp768118 := nat_lit 1485127624810969135582709153033893011116324604215483058511221341478081

noncomputable def hp768119 := nat_lit 16137337866129168197885027435934971211490749168903403813529285124186365121

noncomputable def hp768120 := BSN.cos_dyadic_bound_f 443068089 536870912 3 2 536870912 268435456 hp768117 hp708868 hp768118 hp768119 hp708870

noncomputable def hp768121 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 443068089) (BSN.cosEvenQ 536870912) 0 2 hp768117 hp708868 hp768118 rfl rfl rfl

noncomputable def hp768122 := hp768120 hp768118 364187604 rfl rfl rfl rfl rfl rfl rfl rfl (hp768121 rfl)

noncomputable def hp768123 := @BSN.binarySplit_of_base2 (BSN.cosOddP 443068089) (BSN.cosOddQ 536870912) 0 2 hp768119 hp708870 hp768118 rfl rfl rfl

noncomputable def hp768124 := hp768111 hd4920 hd4922 hd4924 hd4926 hd4918 (hp768115 (hp768116 rfl) rfl rfl rfl rfl) (hp768122 (hp768123 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768125 := hp768027 (BSN.cos_quad_nat0 20 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 534230762 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 898496 1000)) rfl rfl (hp768124 rfl rfl rfl rfl rfl) hp768094

noncomputable def hp768126 := nat_lit 224186523849083576195655063997519107222522493639387294667686582775390625

noncomputable def hp768127 := nat_lit 2580069781828471313197205694959116063509836198409251635894775390625

noncomputable def hp768128 := nat_lit 672554411407687071644338797581167403435440461245765065499787958775390625

noncomputable def hp768129 := BSN.cos_dyadic_bound_f 200195325 536870912 3 2 536870912 268435456 hp768126 hp708868 hp768127 hp768128 hp708870

noncomputable def hp768130 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 200195325) (BSN.cosEvenQ 536870912) 0 2 hp768126 hp708868 hp768127 rfl rfl rfl

noncomputable def hp768131 := hp768129 hp768127 499975718 rfl rfl rfl rfl rfl rfl rfl rfl (hp768130 rfl)

noncomputable def hp768132 := @BSN.binarySplit_of_base2 (BSN.cosOddP 200195325) (BSN.cosOddQ 536870912) 0 2 hp768128 hp708870 hp768127 rfl rfl rfl

noncomputable def hp768133 := nat_lit 8049507157658433399513136828416

noncomputable def hp768134 := BSN.cos_dyadic_bound_f 53265048 536870912 2 1 536870912 268435456 hp768133 hp708767 hp768133 hp768133 hp708768

noncomputable def hp768135 := @BSN.binarySplit_of_base (BSN.cosEvenP 53265048) (BSN.cosEvenQ 536870912) 0 1 hp768133 hp708767 hp768133 rfl rfl rfl

noncomputable def hp768136 := hp768134 hp768133 534230762 rfl rfl rfl rfl rfl rfl rfl rfl (hp768135 rfl)

noncomputable def hp768137 := @BSN.binarySplit_of_base (BSN.cosOddP 53265048) (BSN.cosOddQ 536870912) 0 1 hp768133 hp708768 hp768133 rfl rfl rfl

noncomputable def hp768138 := hp768125 hd4928 hd4930 hd4932 hd4934 hd4918 (hp768131 (hp768132 rfl) rfl rfl rfl rfl) (hp768136 (hp768137 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768139 := hp768022 (BSN.cos_quad_nat3 123 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 473982735 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 898496 1000)) rfl rfl (hp768138 rfl rfl rfl rfl rfl) hp768094

noncomputable def hp768140 := nat_lit 711533398061701384501768335472155936948724262998449250138755927812079616

noncomputable def hp768141 := nat_lit 25988504972287995213797829079248766343602371896079173230408536948736

noncomputable def hp768142 := nat_lit 2134548217175159577514877410758309313313485584251555592069806966362341376

noncomputable def hp768143 := BSN.cos_dyadic_bound_f 267206896 536870912 3 2 536870912 268435456 hp768140 hp708868 hp768141 hp768142 hp708870

noncomputable def hp768144 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 267206896) (BSN.cosEvenQ 536870912) 0 2 hp768140 hp708868 hp768141 rfl rfl rfl

noncomputable def hp768145 := hp768143 hp768141 471736319 rfl rfl rfl rfl rfl rfl rfl rfl (hp768144 rfl)

noncomputable def hp768146 := @BSN.binarySplit_of_base2 (BSN.cosOddP 267206896) (BSN.cosOddQ 536870912) 0 2 hp768142 hp708870 hp768141 rfl rfl rfl

noncomputable def hp768147 := nat_lit 28610132337896557487998952698517230044564858766121306923104062179630829025

noncomputable def hp768148 := nat_lit 12957573805009303179225391566148118918334769540503320852157009428925921

noncomputable def hp768149 := nat_lit 74910320051187635501516606433580886495611611903442607993416670550433910241

noncomputable def hp768150 := BSN.sin_dyadic_bound_f 580851963 536870912 3 2 536870912 268435456 hp768147 hp708845 hp768148 hp768149 hp708848

noncomputable def hp768151 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 580851963) (BSN.sinEvenQ 536870912) 0 2 hp768147 hp708845 hp768148 rfl rfl rfl

noncomputable def hp768152 := hp768150 hp768148 473982735 rfl rfl rfl rfl rfl rfl rfl rfl (hp768151 rfl)

noncomputable def hp768153 := @BSN.binarySplit_of_base2 (BSN.sinOddP 580851963) (BSN.sinOddQ 536870912) 0 2 hp768149 hp708848 hp768148 rfl rfl rfl

noncomputable def hp768154 := hp768139 hd4936 hd4938 hd4940 hd4942 hd4918 (hp768145 (hp768146 rfl) rfl rfl rfl rfl) (hp768152 (hp768153 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768155 := hp768017 (BSN.cos_quad_nat2 238 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 395671456 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 898496 1000)) rfl rfl (hp768154 rfl rfl rfl rfl rfl) hp768094

noncomputable def hp768156 := nat_lit 150944954099904683761918352013297576738358790039951100768502390185630273072966166883027528671683146056522948814401

noncomputable def hp768157 := nat_lit 74490462749026590400086355840868715061212499376479812542744682525414414714653120256943684430390195911272001

noncomputable def hp768158 := nat_lit 753944372808332142643500533137617226756434634213181697166788548956011284092719670512774201468391199285929111594561

noncomputable def hp768159 := BSN.sin_dyadic_bound_f 805393999 536870912 4 3 536870912 268435456 hp768156 hp642702 hp768157 hp768158 hp642705

noncomputable def hp768160 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 805393999) (BSN.sinEvenQ 536870912) 0 3 hp768156 hp642702 hp768157 rfl rfl rfl

noncomputable def hp768161 := hp768159 hp768157 535532234 rfl rfl rfl rfl rfl rfl rfl rfl (hp768160 rfl)

noncomputable def hp768162 := @BSN.binarySplit_of_base3 (BSN.sinOddP 805393999) (BSN.sinOddQ 536870912) 0 3 hp768158 hp642705 hp768157 rfl rfl rfl

noncomputable def hp768163 := nat_lit 3518749330042144719514181006257358561633588549276302982834875493496377121

noncomputable def hp768164 := nat_lit 635392732648401462952177734844131541814957202959740471360792456843041

noncomputable def hp768165 := nat_lit 10554977204661137355616638663302387421817135733422989467561904895575445281

noncomputable def hp768166 := BSN.cos_dyadic_bound_f 398455917 536870912 3 2 536870912 268435456 hp768163 hp708868 hp768164 hp768165 hp708870

noncomputable def hp768167 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 398455917) (BSN.cosEvenQ 536870912) 0 2 hp768163 hp708868 hp768164 rfl rfl rfl

noncomputable def hp768168 := hp768166 hp768164 395671456 rfl rfl rfl rfl rfl rfl rfl rfl (hp768167 rfl)

noncomputable def hp768169 := @BSN.binarySplit_of_base2 (BSN.cosOddP 398455917) (BSN.cosOddQ 536870912) 0 2 hp768165 hp708870 hp768164 rfl rfl rfl

noncomputable def hp768170 := hp768155 hd4944 hd4946 hd4961 hd4963 hd4918 (hp768161 (hp768162 rfl) rfl rfl rfl rfl) (hp768168 (hp768169 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768171 := @hp768012 109003 134217728 (hp768170 rfl rfl rfl rfl rfl) (hp768170 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp768172 := @hp768010 Bool.false 716745041 134217728 109003 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 898496 1000)) (Enclosure.sfrac Bool.false 898496 1000) 11) hp768171

noncomputable def hp768173 := @Enclosure.Real.IsNear.mulLit_tf hp768001 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1))) 9703219 33554432 1

noncomputable def hp768174 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp768000 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp768175 := @hp768174 1 1 0 1 9703219 33554432 1 33554432 9703219 33554432 1

noncomputable def hp768176 := @Enclosure.Real.IsNear.of_eq (hp768000 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp768177 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 898496 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp768178 := @hp768176 (@Inv.inv Real Real.instInv (Real.sqrt hp768002)) Bool.false 9703219 33554432 1 33554432 (hp768177 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 898496 1000) 898496 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 898496 1000))))

noncomputable def hp768179 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp768002)) Bool.false 19406438 67108864 2 67108864 9703219 33554432

noncomputable def hp768180 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp768002) Bool.false 232067302 67108864 6 67108864 116033651 33554432 3 33554432

noncomputable def hp768181 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 898496 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp768182 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 898496 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp768183 := @hp768182 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 898496 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 149946445573

noncomputable def hp768184 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 898496 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 898496 1000 0

noncomputable def hp768185 := @hp768184 1 10680707 67108864 1 67108864 149946445573 1048576000 14039 1048576000 (Enclosure.Real.IsNear.const Bool.false 898496 1000) hd4949

noncomputable def hp768186 := @hp768183 1048576000 14039 1048576000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 898496 1000) 898496 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 898496 1000))) (hp768185 rfl)

noncomputable def hp768187 := @hp768181 149946445573 1048576000 14039 1048576000 401252731 401252770 33554432 hp768186 rfl rfl rfl

noncomputable def hp768188 := @Enclosure.Real.IsNear.recentre' hp768002 Bool.false 802505501 67108864 39 67108864 802505501 67108864 39 67108864 (hp768187 rfl rfl rfl)

noncomputable def hp768189 := @Enclosure.Real.IsNear.sqrt_image hp768002 802505501 67108864 39 67108864 116033648 116033654 33554432 (hp768188 rfl) rfl rfl

noncomputable def hp768190 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp768002) 116033651 33554432 3 33554432 9703218 9703220 33554432 (hp768180 (hp768189 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp768191 := @hp768175 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp768178 (@hp768179 1 33554432 (hp768190 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp768192 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp768193 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp768194 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1))) (hp768192 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768193 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp768195 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 898496 1000) 898496 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 898496 1000)) rfl

noncomputable def hp768196 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp768197 := @hp768196 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768193 (Enclosure.sfrac Bool.false 1 16)))) 69484347

noncomputable def hp768198 := @hp768197 67108864 271 67108864 13416845 16777216 490841179 45675970560000 932260713625215 1125899906842624 22002413260186061 1532631248189521920000

noncomputable def hp768199 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp768200 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1)))) 126591

noncomputable def hp768201 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp768202 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 404059061) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp768203 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1))) Bool.false 56866257516841457929335

noncomputable def hp768204 := nat_lit 1052456941505119260724121937

noncomputable def hp768205 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp768206 := @Enclosure.Real.IsNear.subLit_ff_p hp768002 (Enclosure.sfrac Bool.false 11 1) 802505501 67108864 39 67108864 11 1 0

noncomputable def hp768207 := @hp768205 500000000000000 64307997 67108864 39 67108864 56866257516841457929335 9444732965739290427392 hp768204 hp738031 hd4948 (@hp768206 1 64307997 64307997 67108864 39 67108864 (hp768188 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp768208 := @hp768202 404059061 67108864 123 33554432 Bool.false 64814592 67108864 1 10890000 (@hp768203 9444732965739290427392 hp768204 hp738031 404059061 67108864 123 33554432 (hp768207 rfl) rfl) (Enclosure.sfrac_false_div 404059061 67108864)

noncomputable def hp768209 := nat_lit 12655617886132659218808832

noncomputable def hp768210 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 404059061) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp768209) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp768211 := BSN.sin_reduce_arg_pos_rat_q3 404059061 67108864 226375608064910080 72057594037927936 0 hp768209 hp617687 rfl rfl rfl rfl

noncomputable def hp768212 := nat_lit 1129942244562409642006176122728195580681235748159104343668334283310957776825807235235131040000

noncomputable def hp768213 := nat_lit 1094531902284525248919615942789288156937355574412527414153972187897813948756498848100000000

noncomputable def hp768214 := nat_lit 2957600446012136021517924752761710530482480764724795855698911929891150097674365570337943200000

noncomputable def hp768215 := BSN.sin_dyadic_bound_f 179847147110 137438953472 3 2 67108864 21801270 hp768212 hp738039 hp768213 hp768214 hp738042

noncomputable def hp768216 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 179847147110) (BSN.sinEvenQ 137438953472) 0 2 hp768212 hp738039 hp768213 rfl rfl rfl

noncomputable def hp768217 := hp768215 hp768213 64814592 rfl rfl rfl rfl rfl rfl rfl rfl (hp768216 rfl)

noncomputable def hp768218 := @BSN.binarySplit_of_base2 (BSN.sinOddP 179847147110) (BSN.sinOddQ 137438953472) 0 2 hp768214 hp738042 hp768213 rfl rfl rfl

noncomputable def hp768219 := @BSN.sin_arg_round Bool.false 64814592 67108864 hp768209 hp617687 179847147110 137438953472 21801270 21780000 (hp768217 (hp768218 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768220 := hp768210 64814592 67108864 0 1000000000000000 21780000 10890000 hp768211 BSN.pi_near_15 hp768219 rfl rfl

noncomputable def hp768221 := @hp768200 131072 85814027 22837985280000 34742038 34742309 33554432 (@hp768201 64814592 67108864 1373024432 365407764480000 126591 131072 85814027 22837985280000 (hp768208 (hp768220 rfl rfl) rfl rfl) rfl)

noncomputable def hp768222 := @hp768199 Bool.false 69484347 67108864 271 67108864 69484347 67108864 271 67108864 (hp768221 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp768223 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768193 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp768224 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768193 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 43217467)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp768225 := nat_lit 408177437404654259274033115525

noncomputable def hp768226 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768193 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp768225

noncomputable def hp768227 := nat_lit 205992026368870822679516723925235121

noncomputable def hp768228 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768193 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp768229 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp768230 := @hp768229 (Enclosure.sfrac Bool.false 1 16) 180118146633399 4503599627370496 7633270983 4503599627370496 1 16 0

noncomputable def hp768231 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1)) 4135518478152009

noncomputable def hp768232 := @hp768231 4503599627370496 5016025287 4503599627370496 64307997 67108864 39 67108864 12087524206352831348736 180118146633399 4503599627370496 7633270983

noncomputable def hp768233 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1)) 64307997 67108864 39

noncomputable def hp768234 := @hp768233 67108864 64307997 67108864 39 67108864 4135518478152009 4503599627370496 5016025287 4503599627370496 (@hp768206 1 64307997 64307997 67108864 39 67108864 (hp768188 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp768235 := hp768234 (@hp768206 1 64307997 64307997 67108864 39 67108864 (hp768188 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp768236 := @hp768232 4503599627370496 (hp768235 rfl) (@hp768206 1 64307997 64307997 67108864 39 67108864 (hp768188 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp768237 := @hp768228 500000000000000 461593123344055 4503599627370496 7633270983 4503599627370496 hp768225 hp627574 hp768227 hp738055 hd4948 (@hp768230 1 7385489973504880 461593123344055 4503599627370496 7633270983 4503599627370496 (hp768236 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp768238 := @hp768224 43217467 67108864 715 67108864 Bool.false 26833690 33554432 1 10890000 (@hp768226 hp627574 hp768227 hp738055 43217467 67108864 715 67108864 (hp768237 rfl) rfl) (Enclosure.sfrac_true_div 43217467 67108864)

noncomputable def hp768239 := nat_lit 118880473738902959227418368287317071364222079393251488670368074721

noncomputable def hp768240 := nat_lit 12169548683329260441258243961780909183087515785778279715638241

noncomputable def hp768241 := nat_lit 356617082119342219161372588374027652274300063148182909451672947681

noncomputable def hp768242 := BSN.cos_dyadic_bound_f 43217467 67108864 3 2 33554432 10890000 hp768239 hp738066 hp768240 hp768241 hp738069

noncomputable def hp768243 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 43217467) (BSN.cosEvenQ 67108864) 0 2 hp768239 hp738066 hp768240 rfl rfl rfl

noncomputable def hp768244 := hp768242 hp768240 26833690 rfl rfl rfl rfl rfl rfl rfl rfl (hp768243 rfl)

noncomputable def hp768245 := @BSN.binarySplit_of_base2 (BSN.cosOddP 43217467) (BSN.cosOddQ 67108864) 0 2 hp768241 hp738069 hp768240 rfl rfl rfl

noncomputable def hp768246 := hp768238 (BSN.cos_neg_of_bound 43217467 67108864 Bool.false 26833690 33554432 1 10890000 (hp768244 (hp768245 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp768247 := hp768198 hp768222 (@hp768223 26833690 33554432 7853458864 730815528960000 13416845 16777216 490841179 45675970560000 (hp768246 rfl) rfl)

noncomputable def hp768248 := @hp768173 33554432 932260713625215 1125899906842624 22002413260186061 1532631248189521920000 9045929869401745067085 37778931862957161709568 21476329629092491473517 hp743344 (hp768191 rfl) (@hp768194 Bool.false 932260713625215 1125899906842624 22002413260186061 1532631248189521920000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768002 (Enclosure.sfrac Bool.false 11 1)) (hp768195 rfl (hp768005 rfl rfl))) (hp768247 rfl))

noncomputable def hp768249 := @hp767999 hp767997 hp743344 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 898496 1000))) (@hp768004 hp767997 hp743344 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 898496 1000) 11 (hp768005 rfl rfl)) (@hp768008 hp767997 hp743344 hp768172 (hp768248 rfl) rfl rfl))

theorem hd5081 : hp767998 hp743344 := hp768249

noncomputable def hp768250 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 899604 1000)) Bool.true 8348607052700988353101 18889465931478580854784 56041924141545412297637

noncomputable def hp768251 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 899604 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 899604 1000)) Bool.true 8348607052700988353101 18889465931478580854784

noncomputable def hp768252 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 899604 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp768253 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp768252 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp768254 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 899604 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp768255 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 899604 1000)) (Enclosure.sfrac Bool.false 899604 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp768253 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp768256 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 899604 1000)) hp768255 Bool.true 8348607052700988353101 18889465931478580854784

noncomputable def hp768257 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 899604 1000) 899604 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 899604 1000)) rfl

noncomputable def hp768258 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 899604 1000)) (Enclosure.sfrac Bool.false 899604 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp768253 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp768259 := nat_lit 2241062141156605840215355949056

noncomputable def hp768260 := @hp768258 184157059 268435456 218277 268435456 4610293920580987377075 18889465931478580854784 285565648034699608997 hp763445 hp768259 8348607052700988353101 18889465931478580854784

noncomputable def hp768261 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 899604 1000)) (Enclosure.sfrac Bool.false 899604 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 899604 1000)) (Enclosure.sfrac Bool.false 899604 1000) 11)

noncomputable def hp768262 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 899604 1000)) (Enclosure.sfrac Bool.false 899604 1000) 11) hp768261

noncomputable def hp768263 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 899604 1000)) (Enclosure.sfrac Bool.false 899604 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 899604 1000)) (Enclosure.sfrac Bool.false 899604 1000) 11)

noncomputable def hp768264 := @hp768263 184157059 536870912 218277 536870912 184157059 536870912 218277 536870912 197737136433135616 184157059 268435456

noncomputable def hp768265 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 899604 1000)) (Enclosure.sfrac Bool.false 899604 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp768266 := hp768265 BSN.quadSignNeg 9 10 11 899604 1000 183 238 536870912 268435456 9007199254740992

noncomputable def hp768267 := hp768266 Bool.false 957056881344 4098 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp768268 := hp768267 Bool.true 218885807 187384 Bool.true 698828691 Bool.true 348586154 28296951008113761 1 Bool.false 517545454

noncomputable def hp768269 := hp768268 Bool.false Bool.false 427624061 Bool.true Bool.true 184157059 218277 BSN.abs_quadSignPos (BSN.cos_quad_nat3 183 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 517545454 536870912) BSN.abs_quadSignNeg

noncomputable def hp768270 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 899604 1000)) (Enclosure.sfrac Bool.false 899604 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp768271 := hp768270 BSN.quadSignPos 7 8 9 899604 1000 56 123 536870912 268435456 9007199254740992

noncomputable def hp768272 := hp768271 Bool.false 957056881344 4098 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp768273 := hp768272 Bool.true 532594111 153035 Bool.true 27903986 Bool.true 411612627 28296951008113761 1 Bool.false 536145917

noncomputable def hp768274 := hp768273 Bool.false Bool.false 372456285 Bool.false Bool.true 218885807 187384 BSN.abs_quadSignPos (BSN.cos_quad_nat0 56 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536145917 536870912) BSN.abs_quadSignPos

noncomputable def hp768275 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 899604 1000)) (Enclosure.sfrac Bool.false 899604 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp768276 := hp768275 BSN.quadSignPos 5 6 7 899604 1000 108 20 536870912 268435456 9007199254740992

noncomputable def hp768277 := hp768276 Bool.false 957056881344 4098 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp768278 := hp768277 Bool.true 780766495 113722 Bool.false 610626777 Bool.false 371999519 28296951008113761 1 Bool.false 225471167

noncomputable def hp768279 := hp768278 Bool.false Bool.false 413065707 Bool.false Bool.true 532594111 153035 BSN.abs_quadSignPos (BSN.cos_quad_nat0 108 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 225471167 536870912) BSN.abs_quadSignPos

noncomputable def hp768280 := hp768270 BSN.quadSignNeg 3 4 5 899604 1000 340 213 536870912 268435456 9007199254740992

noncomputable def hp768281 := hp768280 Bool.false 957056881344 4098 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp768282 := hp768281 Bool.true 754970788 67214 Bool.false 789563920 Bool.false 118639214 28296951008113761 1 Bool.false 53661183

noncomputable def hp768283 := hp768282 Bool.false Bool.false 117675976 Bool.true Bool.true 780766495 113722 BSN.abs_quadSignPos (BSN.cos_quad_nat0 340 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 53661183 536870912) BSN.abs_quadSignNeg

noncomputable def hp768284 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 899604 1000)) (Enclosure.sfrac Bool.false 899604 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp768285 := hp768284 BSN.quadSignNeg 1 2 3 899604 1000 737 505 536870912 268435456 9007199254740992

noncomputable def hp768286 := hp768285 Bool.false 957056881344 4098 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp768287 := hp768286 Bool.true 104803504 4154 Bool.false 763706174 Bool.false 584766333 28296951008113761 1 Bool.false 530979422

noncomputable def hp768288 := hp768287 Bool.true Bool.false 475808438 Bool.true Bool.true 754970788 67214 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 737 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 530979422 536870912) BSN.abs_quadSignNeg

noncomputable def hp768289 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 899604 1000)) (Enclosure.sfrac Bool.false 899604 1000) 1) Bool.true

noncomputable def hp768290 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 899604 1000)) (Enclosure.sfrac Bool.false 899604 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 899604 1000)))

noncomputable def hp768291 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 899604 1000))) Bool.true 13100438 67108864

noncomputable def hp768292 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 899604 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 14954013771) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false 14954013771 8388608

noncomputable def hp768293 := nat_lit 129863285118917244343875247302740369640971874561172899

noncomputable def hp768294 := nat_lit 72848146934774908823423391234151065923052634112000

noncomputable def hp768295 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 899604 1000)) Bool.false hp768293 hp768294 34040186603019944323

noncomputable def hp768296 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 899604 4000) (Real.log (Enclosure.sfrac Bool.false 3237150427264 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1799208))))))

noncomputable def hp768297 := nat_lit 282812412372738254497325322731520000

noncomputable def hp768298 := nat_lit 1526515284583378069593595622823013908480

noncomputable def hp768299 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 899604 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp768296 (Enclosure.sfrac Bool.false 899604 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 899604 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp768297 hp768298)) Bool.false

noncomputable def hp768300 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 899604 1000) 899604 1000 3237150427264 16000000 1799208

noncomputable def hp768301 := hp768300 4000 2000 hp768297 hp768298 (@Eq.refl Real (Enclosure.sfrac Bool.false 899604 1000)) rfl rfl rfl rfl

noncomputable def hp768302 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp768296 (Enclosure.sfrac Bool.false 899604 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 899604 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp768297 hp768298) 8028375845667022965267 4503599627370496000

noncomputable def hp768303 := nat_lit 12255437165116839156461099818414645725298655190587079036764160

noncomputable def hp768304 := @hp768302 34040186603019944323 hp739140 hp768297 hp768298 0 1 hp768303 hp768293 hp768294 34040186603019944323 hp739140

noncomputable def hp768305 := @Enclosure.Real.IsNear.subLit_ff_p (hp768296 (Enclosure.sfrac Bool.false 899604 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 899604 2000) (Real.log Real.pi)) 10347287357939686705683 4503599627370496000 1418133331864169 544500000000000000000

noncomputable def hp768306 := nat_lit 134693795691938308365244956672000

noncomputable def hp768307 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 899604 4000) (Real.log (Enclosure.sfrac Bool.false 3237150427264 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1799208))))))

noncomputable def hp768308 := @hp768307 (Enclosure.sfrac Bool.false 899604 2000) 494920619101207621899 180143985094819840 1418133331864169 544500000000000000000 899604 2000 0

noncomputable def hp768309 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 899604 4000) (Real.log (Enclosure.sfrac Bool.false 3237150427264 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1799208))))) 494991336448463811579

noncomputable def hp768310 := nat_lit 1114462157881086915464207225378045952

noncomputable def hp768311 := @hp768309 180143985094819840 312362962621357 121000000000000000000 883966840702371 2251799813685248 200000001089 8712000000000000000 hp768310 494920619101207621899 180143985094819840 1418133331864169

noncomputable def hp768312 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 899604 4000) (Real.log (Enclosure.sfrac Bool.false 3237150427264 16000000)) 899604 4000 0 1 55023247612111975 4503599627370496

noncomputable def hp768313 := nat_lit 118161524506865513057484800

noncomputable def hp768314 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3237150427264) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp768313 hp617687

noncomputable def hp768315 := BSN.log_rat_reduce_isNear 3237150427264 16000000 17 6474300854528 4194304000000 116531377 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp768316 := nat_lit 71729773176780156914626845626031274232526466795948045721855025585260273169658993001285339739400492137005021906176236689551379634775816982534642478217124904960

noncomputable def hp768317 := nat_lit 1122959524763442296164993817966509386916304963129860689060755998022849281003350488519033645318118824854638506675485708298141040210606176589247795189159821312

noncomputable def hp768318 := nat_lit 50081291493102691658125714916539169694476131972870485891421029369790147019641844053154711301741303239560571803508777532060203382520338552505415761920

noncomputable def hp768319 := BSN.log_dyadic_bound 1139998427264 5334302427264 7 6 hp768316 268435456 87120000 hp768317 hp768318 116531377 6474300854528

noncomputable def hp768320 := hp768319 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp768321 := @BSN.binarySplit_of_base6 (BSN.artanhP 1139998427264) (BSN.artanhQ 5334302427264) 0 6 hp768317 hp768316 hp768318 rfl rfl rfl

noncomputable def hp768322 := hp768315 rfl rfl rfl rfl (hp768320 (hp768321 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp768323 := @hp768312 12500018513 1089000000000000000 494991336448463811579 180143985094819840 312362962621357 121000000000000000000 (Enclosure.Real.IsNear.const Bool.false 899604 4000) (BSN.isNear_log_sfrac 3237150427264 16000000 55023247612111975 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp768314 1000001481040000 87120000000000000000000 55023247612111975 4503599627370496 12500018513 1089000000000000000 (hp768322 rfl rfl rfl) rfl)) rfl

noncomputable def hp768324 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1799208)))) 1 4

noncomputable def hp768325 := @hp768324 0 1 883966840702371 562949953421312 200000001089 2178000000000000000 883966840702371 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp768326 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1799208))) 884279719003555 562949953421312 1

noncomputable def hp768327 := @hp768326 2000000000000000 18649 33554432 1 10890000 29661005246602539958272 883966840702371 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp768328 := BSN.arctan_dyadic_bound_f 1000 1799208 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp768329 := hp768328 1 18649 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1799208) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1799208) 0 0 rfl)

noncomputable def hp768330 := hp768325 (hp768327 (hp768329 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp768331 := @hp768305 8638618559661 16777216000 674703 134217728000 hp768306 8028375845667022965267 4503599627370496000 34040186603019944323 hp739140 (@hp768308 1 827782988635174936454640 10347287357939686705683 4503599627370496000 1418133331864169 544500000000000000000 (@hp768311 544500000000000000000 hp768323 hp768330 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 899604 2000) rfl rfl)

noncomputable def hp768332 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 899604 2000) (Real.log Real.pi) 899604 2000 0 1 38410761 33554432

noncomputable def hp768333 := hp768331 (@hp768332 3 268435456 8638618559661 16777216000 674703 134217728000 (Enclosure.Real.IsNear.const Bool.false 899604 2000) hd4909 rfl) rfl

noncomputable def hp768334 := @hp768295 hp739140 14954013771 8388608 513 67108864 (@hp768299 hp768293 hp768294 34040186603019944323 hp739140 (hp768301 rfl rfl rfl rfl rfl) (hp768304 (hp768333 rfl) (Enclosure.Real.IsNear.const Bool.true hp768297 hp768298) rfl rfl)) rfl

noncomputable def hp768335 := nat_lit 1661454544799811137175552

noncomputable def hp768336 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 14954013771) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp768335) (@Nat.cast Real Real.instNatCast hp630689)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp768337 := BSN.sin_reduce_arg_pos_rat_q2 14954013771 8388608 226375608064910080 72057594037927936 283 hp768335 hp630689 rfl rfl rfl rfl

noncomputable def hp768338 := nat_lit 3241309860852794791361267685062865225058907149561906886905457054669521588697825890082360021826629014077739361069388128533283977877467049230336

noncomputable def hp768339 := nat_lit 2062451791692289228120155693417386073240019537259834628650853213463944829365501391451763730546431806093307556852017479088585614144045056

noncomputable def hp768340 := nat_lit 19636157853701719248029014466314372949647536473941137377491247650838472880177842117814914937038425012413461719283252183743509634631883124899840

noncomputable def hp768341 := BSN.cos_dyadic_bound_f 188885513216 137438953472 4 3 67108864 21801270 hp768338 hp740177 hp768339 hp768340 hp740180

noncomputable def hp768342 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 188885513216) (BSN.cosEvenQ 137438953472) 0 3 hp768338 hp740177 hp768339 rfl rfl rfl

noncomputable def hp768343 := hp768341 hp768339 13100438 rfl rfl rfl rfl rfl rfl rfl rfl (hp768342 rfl)

noncomputable def hp768344 := @BSN.binarySplit_of_base3 (BSN.cosOddP 188885513216) (BSN.cosOddQ 137438953472) 0 3 hp768340 hp740180 hp768339 rfl rfl rfl

noncomputable def hp768345 := @BSN.cos_arg_round Bool.false 13100438 67108864 hp768335 hp630689 188885513216 137438953472 21801270 21780000 (hp768343 (hp768344 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768346 := hp768336 13100438 67108864 283 1000000000000000 21780000 10890000 hp768337 BSN.pi_near_15 hp768345 rfl rfl

noncomputable def hp768347 := @hp768292 513 67108864 Bool.true 13100438 67108864 1 10890000 hp768334 (Enclosure.sfrac_false_div 14954013771 8388608) (hp768346 rfl rfl) rfl

noncomputable def hp768348 := @hp768289 6550219 33554432 353354929 45675970560000 104803504 536870912 4154 536870912 (@hp768290 Bool.true 6550219 33554432 353354929 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 899604 1000)) (Enclosure.sfrac Bool.false 899604 1000)) (@hp768291 5653678864 730815528960000 6550219 33554432 353354929 45675970560000 (hp768347 rfl) rfl))

noncomputable def hp768349 := @hp768295 hp739140 957056881344 536870912 4098 536870912 (@hp768299 hp768293 hp768294 34040186603019944323 hp739140 (hp768301 rfl rfl rfl rfl rfl) (hp768304 (hp768333 rfl) (Enclosure.Real.IsNear.const Bool.true hp768297 hp768298) rfl rfl)) rfl

noncomputable def hp768350 := hp768288 (BSN.cos_quad_nat1 505 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 475808438 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 899604 1000)) rfl rfl (hp768348 rfl) hp768349

noncomputable def hp768351 := nat_lit 121997542367850031444020443696812539068867454578878678007514455355451308355356659427948951225449551733305788338176

noncomputable def hp768352 := nat_lit 39365486114129955882692701503035381819494866478352978366849311320804308491794468696654706265064457363787776

noncomputable def hp768353 := nat_lit 609477644499624415386756603001678718559797495627734293553395655529612186193401439098082898684058580588536321806336

noncomputable def hp768354 := BSN.sin_dyadic_bound_f 763706174 536870912 4 3 536870912 268435456 hp768351 hp642702 hp768352 hp768353 hp642705

noncomputable def hp768355 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 763706174) (BSN.sinEvenQ 536870912) 0 3 hp768351 hp642702 hp768352 rfl rfl rfl

noncomputable def hp768356 := hp768354 hp768352 530979422 rfl rfl rfl rfl rfl rfl rfl rfl (hp768355 rfl)

noncomputable def hp768357 := @BSN.binarySplit_of_base3 (BSN.sinOddP 763706174) (BSN.sinOddQ 536870912) 0 3 hp768353 hp642705 hp768352 rfl rfl rfl

noncomputable def hp768358 := nat_lit 29389542144782072018345072293493130585749833248323569927105131568646612385

noncomputable def hp768359 := nat_lit 13672844882737012435987851812249363467187521453551680954678172095899041

noncomputable def hp768360 := nat_lit 76950473392238138218388351865738366850397926329922647087539198972585862561

noncomputable def hp768361 := BSN.sin_dyadic_bound_f 584766333 536870912 3 2 536870912 268435456 hp768358 hp708845 hp768359 hp768360 hp708848

noncomputable def hp768362 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 584766333) (BSN.sinEvenQ 536870912) 0 2 hp768358 hp708845 hp768359 rfl rfl rfl

noncomputable def hp768363 := hp768361 hp768359 475808438 rfl rfl rfl rfl rfl rfl rfl rfl (hp768362 rfl)

noncomputable def hp768364 := @BSN.binarySplit_of_base2 (BSN.sinOddP 584766333) (BSN.sinOddQ 536870912) 0 2 hp768360 hp708848 hp768359 rfl rfl rfl

noncomputable def hp768365 := hp768350 hd4911 hd4913 hd4915 hd4917 hd4918 (hp768356 (hp768357 rfl) rfl rfl rfl rfl) (hp768363 (hp768364 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768366 := hp768283 (BSN.cos_quad_nat1 213 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 117675976 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 899604 1000)) rfl rfl (hp768365 rfl rfl rfl rfl rfl) hp768349

noncomputable def hp768367 := nat_lit 53683647812490595671853212969283986394483839242523522344234080064645545176451273346301665119894517416198144000000

noncomputable def hp768368 := nat_lit 58701275036440807216375074915633144602770978780484041437431381905287566402408761797650610651136000000000000

noncomputable def hp768369 := nat_lit 325077588363891304382078201737823121373497768653790975884892323498428466401745681393011246670807811912997273600000

noncomputable def hp768370 := BSN.cos_dyadic_bound_f 789563920 536870912 4 3 536870912 268435456 hp768367 hp716712 hp768368 hp768369 hp716714

noncomputable def hp768371 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 789563920) (BSN.cosEvenQ 536870912) 0 3 hp768367 hp716712 hp768368 rfl rfl rfl

noncomputable def hp768372 := hp768370 hp768368 53661183 rfl rfl rfl rfl rfl rfl rfl rfl (hp768371 rfl)

noncomputable def hp768373 := @BSN.binarySplit_of_base3 (BSN.cosOddP 789563920) (BSN.cosOddQ 536870912) 0 3 hp768369 hp716714 hp768368 rfl rfl rfl

noncomputable def hp768374 := nat_lit 198113031293059797990393240537616

noncomputable def hp768375 := BSN.sin_dyadic_bound_f 118639214 536870912 2 1 536870912 268435456 hp768374 hp708890 hp768374 hp768374 hp708891

noncomputable def hp768376 := @BSN.binarySplit_of_base (BSN.sinEvenP 118639214) (BSN.sinEvenQ 536870912) 0 1 hp768374 hp708890 hp768374 rfl rfl rfl

noncomputable def hp768377 := hp768375 hp768374 117675976 rfl rfl rfl rfl rfl rfl rfl rfl (hp768376 rfl)

noncomputable def hp768378 := @BSN.binarySplit_of_base (BSN.sinOddP 118639214) (BSN.sinOddQ 536870912) 0 1 hp768374 hp708891 hp768374 rfl rfl rfl

noncomputable def hp768379 := hp768366 hd4920 hd4922 hd4924 hd4926 hd4918 (hp768372 (hp768373 rfl) rfl rfl rfl rfl) (hp768377 (hp768378 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768380 := hp768279 (BSN.cos_quad_nat0 20 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 413065707 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 899604 1000)) rfl rfl (hp768379 rfl rfl rfl rfl rfl) hp768349

noncomputable def hp768381 := nat_lit 19169931189542983262430718388126115668759616832312113967097767975811694618589973634978557844238869429493588733601

noncomputable def hp768382 := nat_lit 2687262792511913537739667379499294243313088888739811846683549198239157386397140290330591449320466330857121

noncomputable def hp768383 := nat_lit 116220414379348646520935674993691388978082783901069638417678910404998869827800984965312832119722864421114492399265

noncomputable def hp768384 := BSN.cos_dyadic_bound_f 610626777 536870912 4 3 536870912 268435456 hp768381 hp716712 hp768382 hp768383 hp716714

noncomputable def hp768385 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 610626777) (BSN.cosEvenQ 536870912) 0 3 hp768381 hp716712 hp768382 rfl rfl rfl

noncomputable def hp768386 := hp768384 hp768382 225471167 rfl rfl rfl rfl rfl rfl rfl rfl (hp768385 rfl)

noncomputable def hp768387 := @BSN.binarySplit_of_base3 (BSN.cosOddP 610626777) (BSN.cosOddQ 536870912) 0 3 hp768383 hp716714 hp768382 rfl rfl rfl

noncomputable def hp768388 := nat_lit 2673116439819202403079879600791721411872491644515401580561440914659301121

noncomputable def hp768389 := nat_lit 366723741338081846365698839107793968618082665759871170951243927607041

noncomputable def hp768390 := nat_lit 8018615871974931045546907404696948647680238768214684999342420256122689281

noncomputable def hp768391 := BSN.cos_dyadic_bound_f 371999519 536870912 3 2 536870912 268435456 hp768388 hp708868 hp768389 hp768390 hp708870

noncomputable def hp768392 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 371999519) (BSN.cosEvenQ 536870912) 0 2 hp768388 hp708868 hp768389 rfl rfl rfl

noncomputable def hp768393 := hp768391 hp768389 413065707 rfl rfl rfl rfl rfl rfl rfl rfl (hp768392 rfl)

noncomputable def hp768394 := @BSN.binarySplit_of_base2 (BSN.cosOddP 371999519) (BSN.cosOddQ 536870912) 0 2 hp768390 hp708870 hp768389 rfl rfl rfl

noncomputable def hp768395 := hp768380 hd4928 hd4930 hd4932 hd4934 hd4918 (hp768386 (hp768387 rfl) rfl rfl rfl rfl) (hp768393 (hp768394 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768396 := hp768274 (BSN.cos_quad_nat3 123 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 372456285 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 899604 1000)) rfl rfl (hp768395 rfl rfl rfl rfl rfl) hp768349

noncomputable def hp768397 := nat_lit 606268468348467809571741734416

noncomputable def hp768398 := BSN.cos_dyadic_bound_f 27903986 536870912 2 1 536870912 268435456 hp768397 hp708767 hp768397 hp768397 hp708768

noncomputable def hp768399 := @BSN.binarySplit_of_base (BSN.cosEvenP 27903986) (BSN.cosEvenQ 536870912) 0 1 hp768397 hp708767 hp768397 rfl rfl rfl

noncomputable def hp768400 := hp768398 hp768397 536145917 rfl rfl rfl rfl rfl rfl rfl rfl (hp768399 rfl)

noncomputable def hp768401 := @BSN.binarySplit_of_base (BSN.cosOddP 27903986) (BSN.cosOddQ 536870912) 0 1 hp768397 hp708768 hp768397 rfl rfl rfl

noncomputable def hp768402 := nat_lit 7212165097563600583580003459935444357170372561170813032489453607392572705

noncomputable def hp768403 := nat_lit 823966420091073981945033047495695912014418245529721289147183444718881

noncomputable def hp768404 := nat_lit 18887669786081663599119717103468313618255333364002224107766140198546240801

noncomputable def hp768405 := BSN.sin_dyadic_bound_f 411612627 536870912 3 2 536870912 268435456 hp768402 hp708845 hp768403 hp768404 hp708848

noncomputable def hp768406 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 411612627) (BSN.sinEvenQ 536870912) 0 2 hp768402 hp708845 hp768403 rfl rfl rfl

noncomputable def hp768407 := hp768405 hp768403 372456285 rfl rfl rfl rfl rfl rfl rfl rfl (hp768406 rfl)

noncomputable def hp768408 := @BSN.binarySplit_of_base2 (BSN.sinOddP 411612627) (BSN.sinOddQ 536870912) 0 2 hp768404 hp708848 hp768403 rfl rfl rfl

noncomputable def hp768409 := hp768396 hd4936 hd4938 hd4940 hd4942 hd4918 (hp768400 (hp768401 rfl) rfl rfl rfl rfl) (hp768407 (hp768408 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768410 := hp768269 (BSN.cos_quad_nat2 238 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 427624061 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 899604 1000)) rfl rfl (hp768409 rfl rfl rfl rfl rfl) hp768349

noncomputable def hp768411 := nat_lit 85497445434332784138397892491747047207388714821774548964453327966098627465352458449911919462290934472007265912881

noncomputable def hp768412 := nat_lit 13565903519000600455330660158194166530953846598693652559767680906529334065681035101595447996050070089336881

noncomputable def hp768413 := nat_lit 427236533804567281416494027018537228902400830209132574662639145777923064451806500066323841498894577261619238766641

noncomputable def hp768414 := BSN.sin_dyadic_bound_f 698828691 536870912 4 3 536870912 268435456 hp768411 hp642702 hp768412 hp768413 hp642705

noncomputable def hp768415 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 698828691) (BSN.sinEvenQ 536870912) 0 3 hp768411 hp642702 hp768412 rfl rfl rfl

noncomputable def hp768416 := hp768414 hp768412 517545454 rfl rfl rfl rfl rfl rfl rfl rfl (hp768415 rfl)

noncomputable def hp768417 := @BSN.binarySplit_of_base3 (BSN.sinOddP 698828691) (BSN.sinOddQ 536870912) 0 3 hp768413 hp642705 hp768412 rfl rfl rfl

noncomputable def hp768418 := nat_lit 2060986998340732786915428158103923914460010415825783320361472629839913216

noncomputable def hp768419 := nat_lit 218012332759452235954559796276503796978490091086313637084385018798336

noncomputable def hp768420 := nat_lit 6182524970356679456274375354719218735786074267295177333810249119482142976

noncomputable def hp768421 := BSN.cos_dyadic_bound_f 348586154 536870912 3 2 536870912 268435456 hp768418 hp708868 hp768419 hp768420 hp708870

noncomputable def hp768422 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 348586154) (BSN.cosEvenQ 536870912) 0 2 hp768418 hp708868 hp768419 rfl rfl rfl

noncomputable def hp768423 := hp768421 hp768419 427624061 rfl rfl rfl rfl rfl rfl rfl rfl (hp768422 rfl)

noncomputable def hp768424 := @BSN.binarySplit_of_base2 (BSN.cosOddP 348586154) (BSN.cosOddQ 536870912) 0 2 hp768420 hp708870 hp768419 rfl rfl rfl

noncomputable def hp768425 := hp768410 hd4944 hd4946 hd4961 hd4963 hd4918 (hp768416 (hp768417 rfl) rfl rfl rfl rfl) (hp768423 (hp768424 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768426 := @hp768264 218277 268435456 (hp768425 rfl rfl rfl rfl rfl) (hp768425 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp768427 := @hp768262 Bool.true 184157059 268435456 218277 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 899604 1000)) (Enclosure.sfrac Bool.false 899604 1000) 11) hp768426

noncomputable def hp768428 := @Enclosure.Real.IsNear.mulLit_tf hp768253 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1))) 4850115 16777216 1

noncomputable def hp768429 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp768252 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp768430 := @hp768429 1 1 0 1 4850115 16777216 1 33554432 4850115 16777216 1

noncomputable def hp768431 := @Enclosure.Real.IsNear.of_eq (hp768252 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp768432 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 899604 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp768433 := @hp768431 (@Inv.inv Real Real.instInv (Real.sqrt hp768254)) Bool.false 4850115 16777216 1 33554432 (hp768432 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 899604 1000) 899604 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 899604 1000))))

noncomputable def hp768434 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp768254)) Bool.false 19400460 67108864 2 67108864 4850115 16777216

noncomputable def hp768435 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp768254) Bool.false 232138813 67108864 7 67108864 232138813 67108864 7 67108864

noncomputable def hp768436 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 899604 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp768437 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 899604 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp768438 := @hp768437 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 899604 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 2402101685007

noncomputable def hp768439 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 899604 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 899604 1000 0

noncomputable def hp768440 := @hp768439 1 10680707 67108864 1 67108864 2402101685007 16777216000 224901 16777216000 (Enclosure.Real.IsNear.const Bool.false 899604 1000) hd4949

noncomputable def hp768441 := @hp768438 16777216000 224901 16777216000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 899604 1000) 899604 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 899604 1000))) (hp768440 rfl)

noncomputable def hp768442 := @hp768436 2402101685007 16777216000 224901 16777216000 401500062 401500101 33554432 hp768441 rfl rfl rfl

noncomputable def hp768443 := @Enclosure.Real.IsNear.recentre' hp768254 Bool.false 803000163 67108864 39 67108864 803000163 67108864 39 67108864 (hp768442 rfl rfl rfl)

noncomputable def hp768444 := @Enclosure.Real.IsNear.sqrt_image hp768254 803000163 67108864 39 67108864 116069403 116069410 33554432 (hp768443 rfl) rfl rfl

noncomputable def hp768445 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp768254) 232138813 67108864 7 67108864 9700229 9700231 33554432 (hp768435 (hp768444 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp768446 := @hp768430 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp768433 (@hp768434 1 33554432 (hp768445 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp768447 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp768448 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp768449 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1))) (hp768447 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768448 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp768450 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 899604 1000) 899604 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 899604 1000)) rfl

noncomputable def hp768451 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp768452 := @hp768451 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768448 (Enclosure.sfrac Bool.false 1 16)))) 68704235

noncomputable def hp768453 := @hp768452 67108864 265 67108864 13835443 16777216 493563679 45675970560000 950553527201105 1125899906842624 14630599693081 1021754165459681280

noncomputable def hp768454 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp768455 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1)))) 65550539

noncomputable def hp768456 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp768457 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 203583557) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp768458 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1))) Bool.false 57303677091203194452745

noncomputable def hp768459 := nat_lit 1052456941509368374949269841

noncomputable def hp768460 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp768461 := @Enclosure.Real.IsNear.subLit_ff_p hp768254 (Enclosure.sfrac Bool.false 11 1) 803000163 67108864 39 67108864 11 1 0

noncomputable def hp768462 := @hp768460 500000000000000 64802659 67108864 39 67108864 57303677091203194452745 9444732965739290427392 hp768459 hp738031 hd4948 (@hp768461 1 64802659 64802659 67108864 39 67108864 (hp768443 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp768463 := @hp768457 203583557 33554432 123 33554432 Bool.false 65550539 67108864 1 10890000 (@hp768458 9444732965739290427392 hp768459 hp738031 203583557 33554432 123 33554432 (hp768462 rfl) rfl) (Enclosure.sfrac_false_div 203583557 33554432)

noncomputable def hp768464 := nat_lit 6551767764388693644673024

noncomputable def hp768465 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 203583557) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp768464) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp768466 := BSN.sin_reduce_arg_pos_rat_q3 203583557 33554432 226375608064910080 72057594037927936 0 hp768464 hp619237 rfl rfl rfl rfl

noncomputable def hp768467 := nat_lit 1298791934304450246697848631718493257759826235021002278956757669596783186076836556497589510400

noncomputable def hp768468 := nat_lit 1445671169928791949012440882480752000347803678060705166885246673024414316072029225311150336

noncomputable def hp768469 := nat_lit 3399257312712723078195964369262513505179934171481002922235598735282868816546645791128897331456

noncomputable def hp768470 := BSN.sin_dyadic_bound_f 186212439654 137438953472 3 2 67108864 21801270 hp768467 hp738039 hp768468 hp768469 hp738042

noncomputable def hp768471 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 186212439654) (BSN.sinEvenQ 137438953472) 0 2 hp768467 hp738039 hp768468 rfl rfl rfl

noncomputable def hp768472 := hp768470 hp768468 65550539 rfl rfl rfl rfl rfl rfl rfl rfl (hp768471 rfl)

noncomputable def hp768473 := @BSN.binarySplit_of_base2 (BSN.sinOddP 186212439654) (BSN.sinOddQ 137438953472) 0 2 hp768469 hp738042 hp768468 rfl rfl rfl

noncomputable def hp768474 := @BSN.sin_arg_round Bool.false 65550539 67108864 hp768464 hp619237 186212439654 137438953472 21801270 21780000 (hp768472 (hp768473 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768475 := hp768465 65550539 67108864 0 1000000000000000 21780000 10890000 hp768466 BSN.pi_near_15 hp768474 rfl rfl

noncomputable def hp768476 := @hp768455 67108864 85814027 22837985280000 34351985 34352250 33554432 (@hp768456 65550539 67108864 1373024432 365407764480000 65550539 67108864 85814027 22837985280000 (hp768463 (hp768475 rfl rfl) rfl rfl) rfl)

noncomputable def hp768477 := @hp768454 Bool.false 68704235 67108864 265 67108864 68704235 67108864 265 67108864 (hp768476 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp768478 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768448 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp768479 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768448 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 40345941)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp768480 := nat_lit 381056639938349338590763164805

noncomputable def hp768481 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768448 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp768480

noncomputable def hp768482 := nat_lit 41406649455851695308190911230683033

noncomputable def hp768483 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768448 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp768484 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp768485 := @hp768484 (Enclosure.sfrac Bool.false 1 16) 149448216199095 4503599627370496 7671854619 4503599627370496 1 16 0

noncomputable def hp768486 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1)) 4199384613470281

noncomputable def hp768487 := @hp768486 4503599627370496 5054608923 4503599627370496 64802659 67108864 39 67108864 10029300015947663278080 149448216199095 4503599627370496 7671854619

noncomputable def hp768488 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1)) 64802659 67108864 39

noncomputable def hp768489 := @hp768488 67108864 64802659 67108864 39 67108864 4199384613470281 4503599627370496 5054608923 4503599627370496 (@hp768461 1 64802659 64802659 67108864 39 67108864 (hp768443 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp768490 := hp768489 (@hp768461 1 64802659 64802659 67108864 39 67108864 (hp768443 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp768491 := @hp768487 4503599627370496 (hp768490 rfl) (@hp768461 1 64802659 64802659 67108864 39 67108864 (hp768443 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp768492 := @hp768483 500000000000000 430923192909751 4503599627370496 7671854619 4503599627370496 hp768480 hp627574 hp768482 hp742826 hd4948 (@hp768485 1 6894771086556016 430923192909751 4503599627370496 7671854619 4503599627370496 (hp768491 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp768493 := @hp768479 40345941 67108864 719 67108864 Bool.false 27670886 33554432 1 10890000 (@hp768481 hp627574 hp768482 hp742826 40345941 67108864 719 67108864 (hp768492 rfl) rfl) (Enclosure.sfrac_true_div 40345941 67108864)

noncomputable def hp768494 := nat_lit 90294645587471712639263094278163405193253448254829168616226876001

noncomputable def hp768495 := nat_lit 7020997085721986168543102960102733567883433277943681146612321

noncomputable def hp768496 := nat_lit 270869894768243693945452196628570010112624577897931618486387403361

noncomputable def hp768497 := BSN.cos_dyadic_bound_f 40345941 67108864 3 2 33554432 10890000 hp768494 hp738066 hp768495 hp768496 hp738069

noncomputable def hp768498 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 40345941) (BSN.cosEvenQ 67108864) 0 2 hp768494 hp738066 hp768495 rfl rfl rfl

noncomputable def hp768499 := hp768497 hp768495 27670886 rfl rfl rfl rfl rfl rfl rfl rfl (hp768498 rfl)

noncomputable def hp768500 := @BSN.binarySplit_of_base2 (BSN.cosOddP 40345941) (BSN.cosOddQ 67108864) 0 2 hp768496 hp738069 hp768495 rfl rfl rfl

noncomputable def hp768501 := hp768493 (BSN.cos_neg_of_bound 40345941 67108864 Bool.false 27670886 33554432 1 10890000 (hp768499 (hp768500 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp768502 := hp768453 hp768477 (@hp768478 27670886 33554432 7897018864 730815528960000 13835443 16777216 493563679 45675970560000 (hp768501 rfl) rfl)

noncomputable def hp768503 := @hp768428 33554432 950553527201105 1125899906842624 14630599693081 1021754165459681280 4610293920580987377075 18889465931478580854784 285565648034699608997 hp763445 (hp768446 rfl) (@hp768449 Bool.false 950553527201105 1125899906842624 14630599693081 1021754165459681280 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768254 (Enclosure.sfrac Bool.false 11 1)) (hp768450 rfl (hp768257 rfl rfl))) (hp768502 rfl))

noncomputable def hp768504 := @hp768251 56041924141545412297637 hp763445 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 899604 1000))) (@hp768256 56041924141545412297637 hp763445 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 899604 1000) 11 (hp768257 rfl rfl)) (@hp768260 56041924141545412297637 hp763445 hp768427 (hp768503 rfl) rfl rfl))

theorem hd5082 : hp768250 hp763445 := hp768504

noncomputable def hp768505 := nat_lit 10514610670727736457957277

noncomputable def hp768506 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 900158 1000)) Bool.false 5744317286022241142573 9444732965739290427392 hp768505

noncomputable def hp768507 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 900158 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 900158 1000)) Bool.false 5744317286022241142573 9444732965739290427392

noncomputable def hp768508 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 900158 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp768509 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp768508 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp768510 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 900158 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp768511 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000)) (Enclosure.sfrac Bool.false 900158 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp768509 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp768512 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 900158 1000)) hp768511 Bool.false 5744317286022241142573 9444732965739290427392

noncomputable def hp768513 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 900158 1000) 900158 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 900158 1000)) rfl

noncomputable def hp768514 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000)) (Enclosure.sfrac Bool.false 900158 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp768509 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp768515 := nat_lit 1541978430082062727248544268288

noncomputable def hp768516 := @hp768514 97118339 268435456 218419 268435456 2327269509996916852525 9444732965739290427392 53492402030636825317277 hp742094 hp768515 5744317286022241142573 9444732965739290427392

noncomputable def hp768517 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000)) (Enclosure.sfrac Bool.false 900158 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000)) (Enclosure.sfrac Bool.false 900158 1000) 11)

noncomputable def hp768518 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000)) (Enclosure.sfrac Bool.false 900158 1000) 11) hp768517

noncomputable def hp768519 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000)) (Enclosure.sfrac Bool.false 900158 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000)) (Enclosure.sfrac Bool.false 900158 1000) 11)

noncomputable def hp768520 := @hp768519 97118339 536870912 218419 536870912 97118339 536870912 218419 536870912 104280022461710336 97118339 268435456

noncomputable def hp768521 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000)) (Enclosure.sfrac Bool.false 900158 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp768522 := hp768521 BSN.quadSignNeg 9 10 11 900158 1000 183 238 536870912 268435456 9007199254740992

noncomputable def hp768523 := hp768522 Bool.false 957795151429 4101 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp768524 := hp768523 Bool.false 72111877 187507 Bool.true 645408396 Bool.true 323513630 28296951008113761 1 Bool.false 500805030

noncomputable def hp768525 := hp768524 Bool.false Bool.false 442311733 Bool.true Bool.false 97118339 218419 BSN.abs_quadSignPos (BSN.cos_quad_nat3 183 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 500805030 536870912) BSN.abs_quadSignNeg

noncomputable def hp768526 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000)) (Enclosure.sfrac Bool.false 900158 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp768527 := hp768526 BSN.quadSignPos 7 8 9 900158 1000 55 123 536870912 268435456 9007199254740992

noncomputable def hp768528 := hp768527 Bool.false 957795151429 4101 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp768529 := hp768528 Bool.true 217272237 153137 Bool.true 751429746 Bool.true 326855317 28296951008113761 1 Bool.false 529027048

noncomputable def hp768530 := hp768529 Bool.false Bool.false 307034413 Bool.false Bool.false 72111877 187507 BSN.abs_quadSignPos (BSN.cos_quad_nat3 55 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 529027048 536870912) BSN.abs_quadSignPos

noncomputable def hp768531 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000)) (Enclosure.sfrac Bool.false 900158 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp768532 := hp768531 BSN.quadSignPos 5 6 7 900158 1000 108 20 536870912 268435456 9007199254740992

noncomputable def hp768533 := hp768532 Bool.false 957795151429 4101 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp768534 := hp768533 Bool.true 339765195 113799 Bool.false 815980145 Bool.false 531504396 28296951008113761 1 Bool.false 27322902

noncomputable def hp768535 := hp768534 Bool.false Bool.false 294573792 Bool.false Bool.true 217272237 153137 BSN.abs_quadSignPos (BSN.cos_quad_nat0 108 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 27322902 536870912) BSN.abs_quadSignPos

noncomputable def hp768536 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000)) (Enclosure.sfrac Bool.false 900158 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp768537 := hp768536 BSN.quadSignNeg 3 4 5 900158 1000 341 213 536870912 268435456 9007199254740992

noncomputable def hp768538 := hp768537 Bool.false 957795151429 4101 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp768539 := hp768538 Bool.true 53925452 67262 Bool.false 272198496 Bool.false 378219846 28296951008113761 1 Bool.false 260685654

noncomputable def hp768540 := hp768539 Bool.true Bool.false 347701674 Bool.true Bool.true 339765195 113799 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 341 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 260685654 536870912) BSN.abs_quadSignNeg

noncomputable def hp768541 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000)) (Enclosure.sfrac Bool.false 900158 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp768542 := hp768541 BSN.quadSignNeg 1 2 3 900158 1000 738 506 536870912 268435456 9007199254740992

noncomputable def hp768543 := hp768542 Bool.false 957795151429 4101 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp768544 := hp768543 Bool.false 496119960 4162 Bool.false 452501081 Bool.false 152965173 28296951008113761 1 Bool.false 357200980

noncomputable def hp768545 := hp768544 Bool.true Bool.false 515226525 Bool.true Bool.true 53925452 67262 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 738 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 357200980 536870912) BSN.abs_quadSignNeg

noncomputable def hp768546 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000)) (Enclosure.sfrac Bool.false 900158 1000) 1) Bool.false

noncomputable def hp768547 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000)) (Enclosure.sfrac Bool.false 900158 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000)))

noncomputable def hp768548 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000))) Bool.false 62014995 67108864

noncomputable def hp768549 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 14965549241) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false 14965549241 8388608

noncomputable def hp768550 := nat_lit 240435137651555081896496485827534208495453345833847087001

noncomputable def hp768551 := nat_lit 134770604586130546748098258366414654368265931430297600

noncomputable def hp768552 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000)) Bool.false hp768550 hp768551 68122172784027012217

noncomputable def hp768553 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 900158 4000) (Real.log (Enclosure.sfrac Bool.false 3241138699856 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1800316))))))

noncomputable def hp768554 := nat_lit 283684302222087680024333794288640000

noncomputable def hp768555 := nat_lit 1532164385322750453589131420431097630720

noncomputable def hp768556 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp768553 (Enclosure.sfrac Bool.false 900158 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 900158 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp768554 hp768555)) Bool.false

noncomputable def hp768557 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 900158 1000) 900158 1000 3241138699856 16000000 1800316

noncomputable def hp768558 := hp768557 4000 2000 hp768554 hp768555 (@Eq.refl Real (Enclosure.sfrac Bool.false 900158 1000)) rfl rfl rfl rfl

noncomputable def hp768559 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp768553 (Enclosure.sfrac Bool.false 900158 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 900158 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp768554 hp768555) 3213827561398897080709 1801439850948198400

noncomputable def hp768560 := nat_lit 4924111619103848077240248029747900589986884522677188341780480

noncomputable def hp768561 := @hp768559 68122172784027012217 hp739631 hp768554 hp768555 0 1 hp768560 hp768550 hp768551 68122172784027012217 hp739631

noncomputable def hp768562 := @Enclosure.Real.IsNear.subLit_ff_p (hp768553 (Enclosure.sfrac Bool.false 900158 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 900158 2000) (Real.log Real.pi)) 20709816925949795622809 9007199254740992000 5675995832584777 2178000000000000000000

noncomputable def hp768563 := nat_lit 539190791843425584848243261440000

noncomputable def hp768564 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 900158 4000) (Real.log (Enclosure.sfrac Bool.false 3241138699856 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1800316))))))

noncomputable def hp768565 := @hp768564 (Enclosure.sfrac Bool.false 900158 2000) 24763768159324366561177 9007199254740992000 5675995832584777 2178000000000000000000 900158 2000 0

noncomputable def hp768566 := nat_lit 41419633851899591245618000

noncomputable def hp768567 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 900158 4000) (Real.log (Enclosure.sfrac Bool.false 3241138699856 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1800316))))) 24767304027425373549177

noncomputable def hp768568 := nat_lit 55763048527311285432442525197214416896

noncomputable def hp768569 := @hp768567 9007199254740992000 5625995832312527 2178000000000000000000 883967025251747 2251799813685248 200000001089 8712000000000000000 hp768568 24763768159324366561177 9007199254740992000 5675995832584777

noncomputable def hp768570 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 900158 4000) (Real.log (Enclosure.sfrac Bool.false 3241138699856 16000000)) 900158 4000 0 1 55028792783989863 4503599627370496

noncomputable def hp768571 := nat_lit 118173432672798626990260224

noncomputable def hp768572 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3241138699856) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp768571 hp617687

noncomputable def hp768573 := BSN.log_rat_reduce_isNear 3241138699856 16000000 17 6482277399712 4194304000000 116861895 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp768574 := nat_lit 72375984508416550385235578952094039193636739061651847009360651793113440558285135262386836302413114915300352201439024222975434496363730960515524032573325967360

noncomputable def hp768575 := nat_lit 1139492613924603916952633879784762427379561568861430602063596998893517612049600281377579023390475462424506335057080794747504246617686024913991565635162734592

noncomputable def hp768576 := nat_lit 52224729294901628113534623147937672922836176172845263556748124031588438216143098330572962814746969205942661246007945420091741891877599885543572766720

noncomputable def hp768577 := BSN.log_dyadic_bound 1143986699856 5338290699856 7 6 hp768574 268435456 87120000 hp768575 hp768576 116861895 6482277399712

noncomputable def hp768578 := hp768577 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp768579 := @BSN.binarySplit_of_base6 (BSN.artanhP 1143986699856) (BSN.artanhQ 5338290699856) 0 6 hp768575 hp768574 hp768576 rfl rfl rfl

noncomputable def hp768580 := hp768573 rfl rfl rfl rfl (hp768578 (hp768579 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp768581 := @hp768570 12500018513 1089000000000000000 24767304027425373549177 9007199254740992000 5625995832312527 2178000000000000000000 (Enclosure.Real.IsNear.const Bool.false 900158 4000) (BSN.isNear_log_sfrac 3241138699856 16000000 55028792783989863 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp768572 1000001481040000 87120000000000000000000 55028792783989863 4503599627370496 12500018513 1089000000000000000 (hp768580 rfl rfl rfl) rfl)) rfl

noncomputable def hp768582 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1800316)))) 1 4

noncomputable def hp768583 := @hp768582 0 1 883967025251747 562949953421312 200000001089 2178000000000000000 883967025251747 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp768584 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1800316))) 884279719003555 562949953421312 1

noncomputable def hp768585 := @hp768584 2000000000000000 18638 33554432 1 10890000 29661011439052027592704 883967025251747 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp768586 := BSN.arctan_dyadic_bound_f 1000 1800316 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp768587 := hp768586 1 18638 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1800316) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1800316) 0 0 rfl)

noncomputable def hp768588 := hp768583 (hp768585 (hp768587 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp768589 := @hp768562 17287876900119 33554432000 1350237 268435456000 hp768563 3213827561398897080709 1801439850948198400 68122172784027012217 hp739631 (@hp768565 1 hp768566 20709816925949795622809 9007199254740992000 5675995832584777 2178000000000000000000 (@hp768569 2178000000000000000000 hp768581 hp768588 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 900158 2000) rfl rfl)

noncomputable def hp768590 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 900158 2000) (Real.log Real.pi) 900158 2000 0 1 38410761 33554432

noncomputable def hp768591 := hp768589 (@hp768590 3 268435456 17287876900119 33554432000 1350237 268435456000 (Enclosure.Real.IsNear.const Bool.false 900158 2000) hd4909 rfl) rfl

noncomputable def hp768592 := @hp768552 hp739631 14965549241 8388608 257 33554432 (@hp768556 hp768550 hp768551 68122172784027012217 hp739631 (hp768558 rfl rfl rfl rfl rfl) (hp768561 (hp768591 rfl) (Enclosure.Real.IsNear.const Bool.true hp768554 hp768555) rfl rfl)) rfl

noncomputable def hp768593 := nat_lit 1424914736575035056586752

noncomputable def hp768594 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 14965549241) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp768593) (@Nat.cast Real Real.instNatCast hp630689)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp768595 := BSN.sin_reduce_arg_pos_rat_q3 14965549241 8388608 226375608064910080 72057594037927936 283 hp768593 hp630689 rfl rfl rfl rfl

noncomputable def hp768596 := nat_lit 743523146292032405307592026273090648032051184077010408222622868747413458528240421704742993920

noncomputable def hp768597 := nat_lit 474233812471377863931590882587782193498428301460863949068445248810509760965183203469950976

noncomputable def hp768598 := nat_lit 1946554718877988354502089874048190526056374693427900146570282411554675375580019379278232682496

noncomputable def hp768599 := BSN.sin_dyadic_bound_f 161994050424 137438953472 3 2 67108864 21801270 hp768596 hp738039 hp768597 hp768598 hp738042

noncomputable def hp768600 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 161994050424) (BSN.sinEvenQ 137438953472) 0 2 hp768596 hp738039 hp768597 rfl rfl rfl

noncomputable def hp768601 := hp768599 hp768597 62014995 rfl rfl rfl rfl rfl rfl rfl rfl (hp768600 rfl)

noncomputable def hp768602 := @BSN.binarySplit_of_base2 (BSN.sinOddP 161994050424) (BSN.sinOddQ 137438953472) 0 2 hp768598 hp738042 hp768597 rfl rfl rfl

noncomputable def hp768603 := @BSN.sin_arg_round Bool.false 62014995 67108864 hp768593 hp630689 161994050424 137438953472 21801270 21780000 (hp768601 (hp768602 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768604 := hp768594 62014995 67108864 283 1000000000000000 21780000 10890000 hp768595 BSN.pi_near_15 hp768603 rfl rfl

noncomputable def hp768605 := @hp768549 257 33554432 Bool.false 62014995 67108864 1 10890000 hp768592 (Enclosure.sfrac_false_div 14965549241 8388608) (hp768604 rfl rfl) rfl

noncomputable def hp768606 := @hp768546 62014995 67108864 177017777 22837985280000 496119960 536870912 4162 536870912 (@hp768547 Bool.false 62014995 67108864 177017777 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000)) (Enclosure.sfrac Bool.false 900158 1000)) (@hp768548 2832284432 365407764480000 62014995 67108864 177017777 22837985280000 (hp768605 rfl) rfl))

noncomputable def hp768607 := @hp768552 hp739631 957795151429 536870912 4101 536870912 (@hp768556 hp768550 hp768551 68122172784027012217 hp739631 (hp768558 rfl rfl rfl rfl rfl) (hp768561 (hp768591 rfl) (Enclosure.Real.IsNear.const Bool.true hp768554 hp768555) rfl rfl)) rfl

noncomputable def hp768608 := hp768545 (BSN.cos_quad_nat2 506 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 515226525 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 900158 1000)) rfl rfl (hp768606 rfl) hp768607

noncomputable def hp768609 := nat_lit 5853258471244763740566983609436445496580113899924873115052362882911465921

noncomputable def hp768610 := nat_lit 1757749440555960780929492937586867061921500581551898133601336116539841

noncomputable def hp768611 := nat_lit 17556259914853179300139091842434162755616498698611515548889885976501318081

noncomputable def hp768612 := BSN.cos_dyadic_bound_f 452501081 536870912 3 2 536870912 268435456 hp768609 hp708868 hp768610 hp768611 hp708870

noncomputable def hp768613 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 452501081) (BSN.cosEvenQ 536870912) 0 2 hp768609 hp708868 hp768610 rfl rfl rfl

noncomputable def hp768614 := hp768612 hp768610 357200980 rfl rfl rfl rfl rfl rfl rfl rfl (hp768613 rfl)

noncomputable def hp768615 := @BSN.binarySplit_of_base2 (BSN.cosOddP 452501081) (BSN.cosOddQ 536870912) 0 2 hp768611 hp708870 hp768610 rfl rfl rfl

noncomputable def hp768616 := nat_lit 76411852945143550818455584944687283002268554320295478642776692591531361

noncomputable def hp768617 := nat_lit 299737097666288204201477020241714716410536455567930250614712931681

noncomputable def hp768618 := nat_lit 229234959361235319878958351880021365577372841887975300067828848348730721

noncomputable def hp768619 := BSN.cos_dyadic_bound_f 152965173 536870912 3 2 536870912 268435456 hp768616 hp708868 hp768617 hp768618 hp708870

noncomputable def hp768620 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 152965173) (BSN.cosEvenQ 536870912) 0 2 hp768616 hp708868 hp768617 rfl rfl rfl

noncomputable def hp768621 := hp768619 hp768617 515226525 rfl rfl rfl rfl rfl rfl rfl rfl (hp768620 rfl)

noncomputable def hp768622 := @BSN.binarySplit_of_base2 (BSN.cosOddP 152965173) (BSN.cosOddQ 536870912) 0 2 hp768618 hp708870 hp768617 rfl rfl rfl

noncomputable def hp768623 := hp768608 hd4911 hd4913 hd4915 hd4917 hd4918 (hp768614 (hp768615 rfl) rfl rfl rfl rfl) (hp768621 (hp768622 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768624 := hp768540 (BSN.cos_quad_nat1 213 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 347701674 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 900158 1000)) rfl rfl (hp768623 rfl rfl rfl rfl rfl) hp768607

noncomputable def hp768625 := nat_lit 1379156843166258796677978238644180674973665860083167243640327100925214720

noncomputable def hp768626 := nat_lit 30136011287205258852950000007078864161975979753569502179415646273536

noncomputable def hp768627 := nat_lit 3612028654750498516118466801210937925817624529583932239863994781853024256

noncomputable def hp768628 := BSN.sin_dyadic_bound_f 272198496 536870912 3 2 536870912 268435456 hp768625 hp708845 hp768626 hp768627 hp708848

noncomputable def hp768629 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 272198496) (BSN.sinEvenQ 536870912) 0 2 hp768625 hp708845 hp768626 rfl rfl rfl

noncomputable def hp768630 := hp768628 hp768626 260685654 rfl rfl rfl rfl rfl rfl rfl rfl (hp768629 rfl)

noncomputable def hp768631 := @BSN.binarySplit_of_base2 (BSN.sinOddP 272198496) (BSN.sinOddQ 536870912) 0 2 hp768627 hp708848 hp768626 rfl rfl rfl

noncomputable def hp768632 := nat_lit 5141311429256480941781313528316169192565922061550199062470982399928869120

noncomputable def hp768633 := nat_lit 418749698833774120751914571247742126678662112643687610186988776366336

noncomputable def hp768634 := nat_lit 13464661481873623975136508521998422969467554232068145859864651160842445056

noncomputable def hp768635 := BSN.sin_dyadic_bound_f 378219846 536870912 3 2 536870912 268435456 hp768632 hp708845 hp768633 hp768634 hp708848

noncomputable def hp768636 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 378219846) (BSN.sinEvenQ 536870912) 0 2 hp768632 hp708845 hp768633 rfl rfl rfl

noncomputable def hp768637 := hp768635 hp768633 347701674 rfl rfl rfl rfl rfl rfl rfl rfl (hp768636 rfl)

noncomputable def hp768638 := @BSN.binarySplit_of_base2 (BSN.sinOddP 378219846) (BSN.sinOddQ 536870912) 0 2 hp768634 hp708848 hp768633 rfl rfl rfl

noncomputable def hp768639 := hp768624 hd4920 hd4922 hd4924 hd4926 hd4918 (hp768630 (hp768631 rfl) rfl rfl rfl rfl) (hp768637 (hp768638 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768640 := hp768535 (BSN.cos_quad_nat0 20 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 294573792 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 900158 1000)) rfl rfl (hp768639 rfl rfl rfl rfl rfl) hp768607

noncomputable def hp768641 := nat_lit 61260563648846701315461392800514447477269305836205522992655510670699566410369121049470751207452269774804761890625

noncomputable def hp768642 := nat_lit 87127468533533531214635116381159991975256576927705132435830983498620378975329176806794328001776621337890625

noncomputable def hp768643 := nat_lit 370862480562590629045364514173832594485025385229381136365066664903128327140611438177664615619108768390590643490625

noncomputable def hp768644 := BSN.cos_dyadic_bound_f 815980145 536870912 4 3 536870912 268435456 hp768641 hp716712 hp768642 hp768643 hp716714

noncomputable def hp768645 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 815980145) (BSN.cosEvenQ 536870912) 0 3 hp768641 hp716712 hp768642 rfl rfl rfl

noncomputable def hp768646 := hp768644 hp768642 27322902 rfl rfl rfl rfl rfl rfl rfl rfl (hp768645 rfl)

noncomputable def hp768647 := @BSN.binarySplit_of_base3 (BSN.cosOddP 815980145) (BSN.cosOddQ 536870912) 0 3 hp768643 hp716714 hp768642 rfl rfl rfl

noncomputable def hp768648 := nat_lit 10999183194872586984590339448602174277241639174427793542058889627628297716099516675684943374779276794049274576896

noncomputable def hp768649 := nat_lit 508255784842770542008561002231182826473783189466604000723102962732119587052400220742809905104734195286016

noncomputable def hp768650 := nat_lit 66702953474643839505458394012894208560967609218395364168422094389576085673860052991446858598151061110562624634880

noncomputable def hp768651 := BSN.cos_dyadic_bound_f 531504396 536870912 4 3 536870912 268435456 hp768648 hp716712 hp768649 hp768650 hp716714

noncomputable def hp768652 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 531504396) (BSN.cosEvenQ 536870912) 0 3 hp768648 hp716712 hp768649 rfl rfl rfl

noncomputable def hp768653 := hp768651 hp768649 294573792 rfl rfl rfl rfl rfl rfl rfl rfl (hp768652 rfl)

noncomputable def hp768654 := @BSN.binarySplit_of_base3 (BSN.cosOddP 531504396) (BSN.cosOddQ 536870912) 0 3 hp768650 hp716714 hp768649 rfl rfl rfl

noncomputable def hp768655 := hp768640 hd4928 hd4930 hd4932 hd4934 hd4918 (hp768646 (hp768647 rfl) rfl rfl rfl rfl) (hp768653 (hp768654 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768656 := hp768530 (BSN.cos_quad_nat3 123 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 307034413 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 900158 1000)) rfl rfl (hp768655 rfl rfl rfl rfl rfl) hp768607

noncomputable def hp768657 := nat_lit 114330612093332431479235005301355977241922189810287172041118297165036023203619353980662533038076940971054489276416

noncomputable def hp768658 := nat_lit 32408624275262767427304170230544273490089850369558916528648644778893504157701102249131314531638364679049216

noncomputable def hp768659 := nat_lit 571205021535768755685145011493803340067104985371422932539980777654693354256922752353833336205495998635781372645376

noncomputable def hp768660 := BSN.sin_dyadic_bound_f 751429746 536870912 4 3 536870912 268435456 hp768657 hp642702 hp768658 hp768659 hp642705

noncomputable def hp768661 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 751429746) (BSN.sinEvenQ 536870912) 0 3 hp768657 hp642702 hp768658 rfl rfl rfl

noncomputable def hp768662 := hp768660 hp768658 529027048 rfl rfl rfl rfl rfl rfl rfl rfl (hp768661 rfl)

noncomputable def hp768663 := @BSN.binarySplit_of_base3 (BSN.sinOddP 751429746) (BSN.sinOddQ 536870912) 0 3 hp768659 hp642705 hp768658 rfl rfl rfl

noncomputable def hp768664 := nat_lit 2867498705893019629214860536349210854540540244902829385560155295293017185

noncomputable def hp768665 := nat_lit 130270005864325550261562369866740635226674972165214067144928769772641

noncomputable def hp768666 := nat_lit 7509904744948413930386116018030053705625333643838190425120267317283032161

noncomputable def hp768667 := BSN.sin_dyadic_bound_f 326855317 536870912 3 2 536870912 268435456 hp768664 hp708845 hp768665 hp768666 hp708848

noncomputable def hp768668 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 326855317) (BSN.sinEvenQ 536870912) 0 2 hp768664 hp708845 hp768665 rfl rfl rfl

noncomputable def hp768669 := hp768667 hp768665 307034413 rfl rfl rfl rfl rfl rfl rfl rfl (hp768668 rfl)

noncomputable def hp768670 := @BSN.binarySplit_of_base2 (BSN.sinOddP 326855317) (BSN.sinOddQ 536870912) 0 2 hp768666 hp708848 hp768665 rfl rfl rfl

noncomputable def hp768671 := hp768656 hd4936 hd4938 hd4940 hd4942 hd4918 (hp768662 (hp768663 rfl) rfl rfl rfl rfl) (hp768669 (hp768670 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768672 := hp768525 (BSN.cos_quad_nat2 238 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 442311733 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 900158 1000)) rfl rfl (hp768671 rfl rfl rfl rfl rfl) hp768607

noncomputable def hp768673 := nat_lit 62186540763268941534897776645349218412290153907220685083927643598876522074173722077735069888445065873221239177216

noncomputable def hp768674 := nat_lit 5224146281682422902489345209454863240206300748067028234081382000158054965856055399474210355520320900694016

noncomputable def hp768675 := nat_lit 310800016839250936108864127436476285498842833778626400556368527162184415685665511124177335289695208798046625202176

noncomputable def hp768676 := BSN.sin_dyadic_bound_f 645408396 536870912 4 3 536870912 268435456 hp768673 hp642702 hp768674 hp768675 hp642705

noncomputable def hp768677 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 645408396) (BSN.sinEvenQ 536870912) 0 3 hp768673 hp642702 hp768674 rfl rfl rfl

noncomputable def hp768678 := hp768676 hp768674 500805030 rfl rfl rfl rfl rfl rfl rfl rfl (hp768677 rfl)

noncomputable def hp768679 := @BSN.binarySplit_of_base3 (BSN.sinOddP 645408396) (BSN.sinOddQ 536870912) 0 3 hp768675 hp642705 hp768674 rfl rfl rfl

noncomputable def hp768680 := nat_lit 1528949683861115672401599389522861058251834731428635402703767437232800000

noncomputable def hp768681 := nat_lit 119988786658541836380367710402474359006001324478641847308432100000000

noncomputable def hp768682 := nat_lit 4586609074010029933532037433147778226037492191636948924416685447498400000

noncomputable def hp768683 := BSN.cos_dyadic_bound_f 323513630 536870912 3 2 536870912 268435456 hp768680 hp708868 hp768681 hp768682 hp708870

noncomputable def hp768684 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 323513630) (BSN.cosEvenQ 536870912) 0 2 hp768680 hp708868 hp768681 rfl rfl rfl

noncomputable def hp768685 := hp768683 hp768681 442311733 rfl rfl rfl rfl rfl rfl rfl rfl (hp768684 rfl)

noncomputable def hp768686 := @BSN.binarySplit_of_base2 (BSN.cosOddP 323513630) (BSN.cosOddQ 536870912) 0 2 hp768682 hp708870 hp768681 rfl rfl rfl

noncomputable def hp768687 := hp768672 hd4944 hd4946 hd4961 hd4963 hd4918 (hp768678 (hp768679 rfl) rfl rfl rfl rfl) (hp768685 (hp768686 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768688 := @hp768520 218419 268435456 (hp768687 rfl rfl rfl rfl rfl) (hp768687 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp768689 := @hp768518 Bool.false 97118339 268435456 218419 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 900158 1000)) (Enclosure.sfrac Bool.false 900158 1000) 11) hp768688

noncomputable def hp768690 := @Enclosure.Real.IsNear.mulLit_tf hp768509 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1))) 9698737 33554432 1

noncomputable def hp768691 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp768508 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp768692 := @hp768691 1 1 0 1 9698737 33554432 1 33554432 9698737 33554432 1

noncomputable def hp768693 := @Enclosure.Real.IsNear.of_eq (hp768508 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp768694 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 900158 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp768695 := @hp768693 (@Inv.inv Real Real.instInv (Real.sqrt hp768510)) Bool.false 9698737 33554432 1 33554432 (hp768694 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 900158 1000) 900158 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 900158 1000))))

noncomputable def hp768696 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp768510)) Bool.false 19397474 67108864 2 67108864 9698737 33554432

noncomputable def hp768697 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp768510) Bool.false 232174545 67108864 7 67108864 232174545 67108864 7 67108864

noncomputable def hp768698 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 900158 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp768699 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 900158 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp768700 := @hp768699 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 900158 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 4807161925853

noncomputable def hp768701 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 900158 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 900158 1000 0

noncomputable def hp768702 := @hp768701 1 10680707 67108864 1 67108864 4807161925853 33554432000 450079 33554432000 (Enclosure.Real.IsNear.const Bool.false 900158 1000) hd4949

noncomputable def hp768703 := @hp768700 33554432000 450079 33554432000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 900158 1000) 900158 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 900158 1000))) (hp768702 rfl)

noncomputable def hp768704 := @hp768698 4807161925853 33554432000 450079 33554432000 401623670 401623709 33554432 hp768703 rfl rfl rfl

noncomputable def hp768705 := @Enclosure.Real.IsNear.recentre' hp768510 Bool.false 803247379 67108864 39 67108864 803247379 67108864 39 67108864 (hp768704 rfl rfl rfl)

noncomputable def hp768706 := @Enclosure.Real.IsNear.sqrt_image hp768510 803247379 67108864 39 67108864 116087269 116087276 33554432 (hp768705 rfl) rfl rfl

noncomputable def hp768707 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp768510) 232174545 67108864 7 67108864 9698736 9698738 33554432 (hp768697 (hp768706 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp768708 := @hp768692 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp768695 (@hp768696 1 33554432 (hp768707 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp768709 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp768710 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp768711 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1))) (hp768709 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768710 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp768712 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 900158 1000) 900158 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 900158 1000)) rfl

noncomputable def hp768713 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp768714 := @hp768713 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768710 (Enclosure.sfrac Bool.false 1 16)))) 34187723

noncomputable def hp768715 := @hp768714 33554432 131 33554432 7018775 8388608 494924929 45675970560000 239955935499325 281474976710656 10963439163618683 766315624094760960000

noncomputable def hp768716 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp768717 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1)))) 4116609

noncomputable def hp768718 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp768719 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 204360209) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp768720 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1))) Bool.false 57522285186216377305625

noncomputable def hp768721 := nat_lit 1052456941511491944219365713

noncomputable def hp768722 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp768723 := @Enclosure.Real.IsNear.subLit_ff_p hp768510 (Enclosure.sfrac Bool.false 11 1) 803247379 67108864 39 67108864 11 1 0

noncomputable def hp768724 := @hp768722 500000000000000 65049875 67108864 39 67108864 57522285186216377305625 9444732965739290427392 hp768721 hp738031 hd4948 (@hp768723 1 65049875 65049875 67108864 39 67108864 (hp768705 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp768725 := @hp768719 204360209 33554432 123 33554432 Bool.false 65865744 67108864 1 10890000 (@hp768720 9444732965739290427392 hp768721 hp738031 204360209 33554432 123 33554432 (hp768724 rfl) rfl) (Enclosure.sfrac_false_div 204360209 33554432)

noncomputable def hp768726 := nat_lit 6663695113438183259373568

noncomputable def hp768727 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 204360209) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp768726) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp768728 := BSN.sin_reduce_arg_pos_rat_q3 204360209 33554432 226375608064910080 72057594037927936 0 hp768726 hp619237 rfl rfl rfl rfl

noncomputable def hp768729 := nat_lit 1389952519440382292062524666571218318506191151814220741802237157628416491940159040900771488000

noncomputable def hp768730 := nat_lit 1655474548592304311956158482510568619304108839662314761877611317055886137927094783741665536

noncomputable def hp768731 := nat_lit 3637671544503280367468207013000554675465913030915886766534247851656333663239010763185486438656

noncomputable def hp768732 := BSN.sin_dyadic_bound_f 189393606246 137438953472 3 2 67108864 21801270 hp768729 hp738039 hp768730 hp768731 hp738042

noncomputable def hp768733 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 189393606246) (BSN.sinEvenQ 137438953472) 0 2 hp768729 hp738039 hp768730 rfl rfl rfl

noncomputable def hp768734 := hp768732 hp768730 65865744 rfl rfl rfl rfl rfl rfl rfl rfl (hp768733 rfl)

noncomputable def hp768735 := @BSN.binarySplit_of_base2 (BSN.sinOddP 189393606246) (BSN.sinOddQ 137438953472) 0 2 hp768731 hp738042 hp768730 rfl rfl rfl

noncomputable def hp768736 := @BSN.sin_arg_round Bool.false 65865744 67108864 hp768726 hp619237 189393606246 137438953472 21801270 21780000 (hp768734 (hp768735 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768737 := hp768727 65865744 67108864 0 1000000000000000 21780000 10890000 hp768728 BSN.pi_near_15 hp768736 rfl rfl

noncomputable def hp768738 := @hp768717 4194304 85814027 22837985280000 34187592 34187854 33554432 (@hp768718 65865744 67108864 1373024432 365407764480000 4116609 4194304 85814027 22837985280000 (hp768725 (hp768737 rfl rfl) rfl rfl) rfl)

noncomputable def hp768739 := @hp768716 Bool.false 68375446 67108864 262 67108864 34187723 33554432 131 33554432 (hp768738 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp768740 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768710 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp768741 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768710 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 19446837)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp768742 := nat_lit 367340365765513548020001895205

noncomputable def hp768743 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768710 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp768742

noncomputable def hp768744 := nat_lit 207553615669354370165266633897262941

noncomputable def hp768745 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768710 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp768746 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp768747 := @hp768746 (Enclosure.sfrac Bool.false 1 16) 133936977076375 4503599627370496 7691137467 4503599627370496 1 16 0

noncomputable def hp768748 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1)) 4231486237515625

noncomputable def hp768749 := @hp768748 4503599627370496 5073891771 4503599627370496 65049875 67108864 39 67108864 8988358379189567488000 133936977076375 4503599627370496 7691137467

noncomputable def hp768750 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1)) 65049875 67108864 39

noncomputable def hp768751 := @hp768750 67108864 65049875 67108864 39 67108864 4231486237515625 4503599627370496 5073891771 4503599627370496 (@hp768723 1 65049875 65049875 67108864 39 67108864 (hp768705 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp768752 := hp768751 (@hp768723 1 65049875 65049875 67108864 39 67108864 (hp768705 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp768753 := @hp768749 4503599627370496 (hp768752 rfl) (@hp768723 1 65049875 65049875 67108864 39 67108864 (hp768705 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp768754 := @hp768745 500000000000000 415411953787031 4503599627370496 7691137467 4503599627370496 hp768742 hp627574 hp768744 hp738055 hd4948 (@hp768747 1 6646591260592496 415411953787031 4503599627370496 7691137467 4503599627370496 (hp768753 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp768755 := @hp768741 19446837 33554432 721 67108864 Bool.false 28075100 33554432 1 10890000 (@hp768743 hp627574 hp768744 hp738055 19446837 33554432 721 67108864 (hp768754 rfl) rfl) (Enclosure.sfrac_true_div 19446837 33554432)

noncomputable def hp768756 := nat_lit 304602812434436389192338714275700396271116703045293303533237601

noncomputable def hp768757 := nat_lit 20454637735520496096701804855933370366893288065572692129121

noncomputable def hp768758 := nat_lit 913767528027838126584822739217389322072616322559748765215454561

noncomputable def hp768759 := BSN.cos_dyadic_bound_f 19446837 33554432 3 2 33554432 10890000 hp768756 hp684401 hp768757 hp768758 hp684404

noncomputable def hp768760 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 19446837) (BSN.cosEvenQ 33554432) 0 2 hp768756 hp684401 hp768757 rfl rfl rfl

noncomputable def hp768761 := hp768759 hp768757 28075100 rfl rfl rfl rfl rfl rfl rfl rfl (hp768760 rfl)

noncomputable def hp768762 := @BSN.binarySplit_of_base2 (BSN.cosOddP 19446837) (BSN.cosOddQ 33554432) 0 2 hp768758 hp684404 hp768757 rfl rfl rfl

noncomputable def hp768763 := hp768755 (BSN.cos_neg_of_bound 19446837 33554432 Bool.false 28075100 33554432 1 10890000 (hp768761 (hp768762 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp768764 := hp768715 hp768739 (@hp768740 28075100 33554432 7918798864 730815528960000 7018775 8388608 494924929 45675970560000 (hp768763 rfl) rfl)

noncomputable def hp768765 := @hp768690 33554432 239955935499325 281474976710656 10963439163618683 766315624094760960000 2327269509996916852525 9444732965739290427392 53492402030636825317277 hp742094 (hp768708 rfl) (@hp768711 Bool.false 239955935499325 281474976710656 10963439163618683 766315624094760960000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768510 (Enclosure.sfrac Bool.false 11 1)) (hp768712 rfl (hp768513 rfl rfl))) (hp768764 rfl))

noncomputable def hp768766 := @hp768507 hp768505 hp742094 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 900158 1000))) (@hp768512 hp768505 hp742094 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 900158 1000) 11 (hp768513 rfl rfl)) (@hp768516 hp768505 hp742094 hp768689 (hp768765 rfl) rfl rfl))

theorem hd5083 : hp768506 hp742094 := hp768766

noncomputable def hp768767 := nat_lit 2340120793355993197407173

noncomputable def hp768768 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 901581 1000)) Bool.true 57388786245359528123709 37778931862957161709568 hp768767

noncomputable def hp768769 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 901581 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 901581 1000)) Bool.true 57388786245359528123709 37778931862957161709568

noncomputable def hp768770 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 901581 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp768771 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp768770 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp768772 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 901581 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp768773 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000)) (Enclosure.sfrac Bool.false 901581 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp768771 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp768774 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 901581 1000)) hp768773 Bool.true 57388786245359528123709 37778931862957161709568

noncomputable def hp768775 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 901581 1000) 901581 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 901581 1000)) rfl

noncomputable def hp768776 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000)) (Enclosure.sfrac Bool.false 901581 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp768771 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp768777 := nat_lit 7702592502529806407916324913152

noncomputable def hp768778 := @hp768776 237778239 134217728 109377 134217728 9539838039466268091075 37778931862957161709568 11862348450085710687173 hp743845 hp768777 57388786245359528123709 37778931862957161709568

noncomputable def hp768779 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000)) (Enclosure.sfrac Bool.false 901581 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000)) (Enclosure.sfrac Bool.false 901581 1000) 11)

noncomputable def hp768780 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000)) (Enclosure.sfrac Bool.false 901581 1000) 11) hp768779

noncomputable def hp768781 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000)) (Enclosure.sfrac Bool.false 901581 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000)) (Enclosure.sfrac Bool.false 901581 1000) 11)

noncomputable def hp768782 := @hp768781 475556478 536870912 218754 536870912 475556478 536870912 218754 536870912 510624880102735872 237778239 134217728

noncomputable def hp768783 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000)) (Enclosure.sfrac Bool.false 901581 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp768784 := hp768783 BSN.quadSignNeg 9 10 11 901581 1000 183 238 536870912 268435456 9007199254740992

noncomputable def hp768785 := hp768784 Bool.false 959691884755 4107 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp768786 := hp768785 Bool.true 469795982 187794 Bool.true 507774800 Bool.true 258693898 28296951008113761 1 Bool.false 435385004

noncomputable def hp768787 := hp768786 Bool.false Bool.false 475741086 Bool.true Bool.true 475556478 218754 BSN.abs_quadSignPos (BSN.cos_quad_nat3 183 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 435385004 536870912) BSN.abs_quadSignNeg

noncomputable def hp768788 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000)) (Enclosure.sfrac Bool.false 901581 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp768789 := hp768788 BSN.quadSignPos 7 8 9 901581 1000 55 123 536870912 268435456 9007199254740992

noncomputable def hp768790 := hp768789 Bool.false 959691884755 4107 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp768791 := hp768790 Bool.true 645315051 153370 Bool.true 443321775 Bool.true 108729715 28296951008113761 1 Bool.false 394630869

noncomputable def hp768792 := hp768791 Bool.false Bool.false 107987955 Bool.false Bool.true 469795982 187794 BSN.abs_quadSignPos (BSN.cos_quad_nat3 55 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 394630869 536870912) BSN.abs_quadSignPos

noncomputable def hp768793 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000)) (Enclosure.sfrac Bool.false 901581 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp768794 := hp768793 BSN.quadSignNeg 5 6 7 901581 1000 109 21 536870912 268435456 9007199254740992

noncomputable def hp768795 := hp768794 Bool.false 959691884755 4107 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp768796 := hp768795 Bool.true 432360117 113971 Bool.false 500552967 Bool.false 98311150 28296951008113761 1 Bool.false 431120312

noncomputable def hp768797 := hp768796 Bool.true Bool.false 97762634 Bool.true Bool.true 645315051 153370 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 109 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 431120312 536870912) BSN.abs_quadSignNeg

noncomputable def hp768798 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000)) (Enclosure.sfrac Bool.false 901581 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp768799 := hp768798 BSN.quadSignNeg 3 4 5 901581 1000 342 214 536870912 268435456 9007199254740992

noncomputable def hp768800 := hp768799 Bool.false 959691884755 4107 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp768801 := hp768800 Bool.false 26956057 67361 Bool.false 266533415 Bool.false 202080389 28296951008113761 1 Bool.false 472057478

noncomputable def hp768802 := hp768801 Bool.true Bool.false 499285888 Bool.true Bool.true 432360117 113971 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 342 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 472057478 536870912) BSN.abs_quadSignNeg

noncomputable def hp768803 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000)) (Enclosure.sfrac Bool.false 901581 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp768804 := hp768803 BSN.quadSignPos 1 2 3 901581 1000 740 507 536870912 268435456 9007199254740992

noncomputable def hp768805 := hp768804 Bool.false 959691884755 4107 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp768806 := hp768805 Bool.true 536870744 4162 Bool.false 133062930 Bool.false 367079777 28296951008113761 1 Bool.false 520465393

noncomputable def hp768807 := hp768806 Bool.false Bool.false 339139341 Bool.false Bool.false 26956057 67361 BSN.abs_quadSignPos (BSN.cos_quad_nat0 740 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 520465393 536870912) BSN.abs_quadSignPos

noncomputable def hp768808 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000)) (Enclosure.sfrac Bool.false 901581 1000) 1) Bool.true

noncomputable def hp768809 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000)) (Enclosure.sfrac Bool.false 901581 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000)))

noncomputable def hp768810 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000))) Bool.true 67108843 67108864

noncomputable def hp768811 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 59980742797) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 59980742797 33554432

noncomputable def hp768812 := nat_lit 17294603882580235243754667114986444456106268376019949114163

noncomputable def hp768813 := nat_lit 9674948706565094958262255029983001199369369686114304000

noncomputable def hp768814 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000)) Bool.false hp768812 hp768813 136459077696125059963

noncomputable def hp768815 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 901581 4000) (Real.log (Enclosure.sfrac Bool.false 3251394198244 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1803162))))))

noncomputable def hp768816 := nat_lit 285933690467925631718488076112480000

noncomputable def hp768817 := nat_lit 1546754517517816200899721495251650985280

noncomputable def hp768818 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp768815 (Enclosure.sfrac Bool.false 901581 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 901581 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp768816 hp768817)) Bool.false

noncomputable def hp768819 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 901581 1000) 901581 1000 3251394198244 16000000 1803162

noncomputable def hp768820 := hp768819 4000 2000 hp768816 hp768817 (@Eq.refl Real (Enclosure.sfrac Bool.false 901581 1000)) rfl rfl rfl rfl

noncomputable def hp768821 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp768815 (Enclosure.sfrac Bool.false 901581 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 901581 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp768816 hp768817) 32201919418141158920123 18014398509481984000

noncomputable def hp768822 := nat_lit 49808459181831077502013441291160960033586052922937453448789440

noncomputable def hp768823 := @hp768821 136459077696125059963 hp738659 hp768816 hp768817 0 1 hp768822 hp768812 hp768813 136459077696125059963 hp738659

noncomputable def hp768824 := @Enclosure.Real.IsNear.subLit_ff_p (hp768815 (Enclosure.sfrac Bool.false 901581 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 901581 2000) (Real.log Real.pi)) 41497949938887178047419 18014398509481984000 11369779191513553 4356000000000000000000

noncomputable def hp768825 := nat_lit 2161034230770994166772921270272000

noncomputable def hp768826 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 901581 4000) (Real.log (Enclosure.sfrac Bool.false 3251394198244 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1803162))))))

noncomputable def hp768827 := @hp768826 (Enclosure.sfrac Bool.false 901581 2000) 49618669650175816355771 18014398509481984000 11369779191513553 4356000000000000000000 901581 2000 0

noncomputable def hp768828 := nat_lit 82995899877774356094838000

noncomputable def hp768829 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 901581 4000) (Real.log (Enclosure.sfrac Bool.false 3251394198244 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1803162))))) 49625741390404362171771

noncomputable def hp768830 := nat_lit 111731311073575772827491157076982366208

noncomputable def hp768831 := @hp768829 18014398509481984000 3756593063656351 1452000000000000000000 883967528568227 2251799813685248 200000001089 8712000000000000000 hp768830 49618669650175816355771 18014398509481984000 11369779191513553

noncomputable def hp768832 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 901581 4000) (Real.log (Enclosure.sfrac Bool.false 3251394198244 16000000)) 901581 4000 0 1 55043020416805991 4503599627370496

noncomputable def hp768833 := nat_lit 118203986281621010060935168

noncomputable def hp768834 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3251394198244) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp768833 hp617687

noncomputable def hp768835 := BSN.log_rat_reduce_isNear 3251394198244 16000000 17 6502788396488 4194304000000 117709928 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp768836 := nat_lit 74062243337386342116197622902077488107836926988809000821461865239595999657196341400034885962472562640644378079441392660386616380865823217632291737853870735360

noncomputable def hp768837 := nat_lit 1182971736466089783521396461372648841044157154030824797184508662297623826793079728341814560125329723868421388503536772879543294023348452652225574257601544192

noncomputable def hp768838 := nat_lit 58128332757164842163145503111190371873240733175601091307499920251301924333197343314128578565655183702981394750747426668864248670156140135137903902720

noncomputable def hp768839 := BSN.log_dyadic_bound 1154242198244 5348546198244 7 6 hp768836 268435456 87120000 hp768837 hp768838 117709928 6502788396488

noncomputable def hp768840 := hp768839 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp768841 := @BSN.binarySplit_of_base6 (BSN.artanhP 1154242198244) (BSN.artanhQ 5348546198244) 0 6 hp768837 hp768836 hp768838 rfl rfl rfl

noncomputable def hp768842 := hp768835 rfl rfl rfl rfl (hp768840 (hp768841 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp768843 := @hp768832 12500018513 1089000000000000000 49625741390404362171771 18014398509481984000 3756593063656351 1452000000000000000000 (Enclosure.Real.IsNear.const Bool.false 901581 4000) (BSN.isNear_log_sfrac 3251394198244 16000000 55043020416805991 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp768834 1000001481040000 87120000000000000000000 55043020416805991 4503599627370496 12500018513 1089000000000000000 (hp768842 rfl rfl rfl) rfl)) rfl

noncomputable def hp768844 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1803162)))) 1 4

noncomputable def hp768845 := @hp768844 0 1 883967528568227 562949953421312 200000001089 2178000000000000000 883967528568227 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp768846 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1803162))) 884279719003555 562949953421312 1

noncomputable def hp768847 := @hp768846 2000000000000000 18608 33554432 1 10890000 29661028327550630232064 883967528568227 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp768848 := BSN.arctan_dyadic_bound_f 1000 1803162 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp768849 := hp768848 1 18608 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1803162) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1803162) 0 0 rfl)

noncomputable def hp768850 := hp768845 (hp768847 (hp768849 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp768851 := @hp768824 34630412313141 67108864000 2704743 536870912000 hp768825 32201919418141158920123 18014398509481984000 136459077696125059963 hp738659 (@hp768827 1 hp768828 41497949938887178047419 18014398509481984000 11369779191513553 4356000000000000000000 (@hp768831 4356000000000000000000 hp768843 hp768850 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 901581 2000) rfl rfl)

noncomputable def hp768852 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 901581 2000) (Real.log Real.pi) 901581 2000 0 1 38410761 33554432

noncomputable def hp768853 := hp768851 (@hp768852 3 268435456 34630412313141 67108864000 2704743 536870912000 (Enclosure.Real.IsNear.const Bool.false 901581 2000) hd4909 rfl) rfl

noncomputable def hp768854 := @hp768814 hp738659 59980742797 33554432 257 33554432 (@hp768818 hp768812 hp768813 136459077696125059963 hp738659 (hp768820 rfl rfl rfl rfl rfl) (hp768823 (hp768853 rfl) (Enclosure.Real.IsNear.const Bool.true hp768816 hp768817) rfl rfl)) rfl

noncomputable def hp768855 := nat_lit 7592104070158788029579264

noncomputable def hp768856 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 59980742797) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp768855) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp768857 := BSN.sin_reduce_arg_pos_rat_q1 59980742797 33554432 226375608064910080 72057594037927936 284 hp768855 hp619237 rfl rfl rfl rfl

noncomputable def hp768858 := nat_lit 14351563121130686582082008855977432728661472452520355215413679211633039493823862609432790100846906082628853564935326043358249984686542924251041

noncomputable def hp768859 := nat_lit 10189389713485839745920699645628229100987136432098710505793061043268229219203978713313158462044108824887734294334416146931831993117147041

noncomputable def hp768860 := nat_lit 71668825728127609572734018848453177225016836658822047424317347403488961255141305492347345421952166188502483701328775878902088897221285866602401

noncomputable def hp768861 := BSN.sin_dyadic_bound_f 215780575847 137438953472 4 3 67108864 21801270 hp768858 hp737934 hp768859 hp768860 hp737937

noncomputable def hp768862 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215780575847) (BSN.sinEvenQ 137438953472) 0 3 hp768858 hp737934 hp768859 rfl rfl rfl

noncomputable def hp768863 := hp768861 hp768859 67108843 rfl rfl rfl rfl rfl rfl rfl rfl (hp768862 rfl)

noncomputable def hp768864 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215780575847) (BSN.sinOddQ 137438953472) 0 3 hp768860 hp737937 hp768859 rfl rfl rfl

noncomputable def hp768865 := @BSN.sin_arg_round Bool.false 67108843 67108864 hp768855 hp619237 215780575847 137438953472 21801270 21780000 (hp768863 (hp768864 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768866 := hp768856 67108843 67108864 284 1000000000000000 21780000 10890000 hp768857 BSN.pi_near_15 hp768865 rfl rfl

noncomputable def hp768867 := @hp768811 257 33554432 Bool.true 67108843 67108864 1 10890000 hp768854 (Enclosure.sfrac_false_div 59980742797 33554432) (hp768866 rfl rfl) rfl

noncomputable def hp768868 := @hp768808 67108843 67108864 177017777 22837985280000 536870744 536870912 4162 536870912 (@hp768809 Bool.true 67108843 67108864 177017777 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000)) (Enclosure.sfrac Bool.false 901581 1000)) (@hp768810 2832284432 365407764480000 67108843 67108864 177017777 22837985280000 (hp768867 rfl) rfl))

noncomputable def hp768869 := @hp768814 hp738659 959691884755 536870912 4107 536870912 (@hp768818 hp768812 hp768813 136459077696125059963 hp738659 (hp768820 rfl rfl rfl rfl rfl) (hp768823 (hp768853 rfl) (Enclosure.Real.IsNear.const Bool.true hp768816 hp768817) rfl rfl)) rfl

noncomputable def hp768870 := hp768807 (BSN.cos_quad_nat3 507 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 339139341 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 901581 1000)) rfl rfl (hp768868 rfl) hp768869

noncomputable def hp768871 := nat_lit 313493347228501939487166188010000

noncomputable def hp768872 := BSN.cos_dyadic_bound_f 133062930 536870912 2 1 536870912 268435456 hp768871 hp708767 hp768871 hp768871 hp708768

noncomputable def hp768873 := @BSN.binarySplit_of_base (BSN.cosEvenP 133062930) (BSN.cosEvenQ 536870912) 0 1 hp768871 hp708767 hp768871 rfl rfl rfl

noncomputable def hp768874 := hp768872 hp768871 520465393 rfl rfl rfl rfl rfl rfl rfl rfl (hp768873 rfl)

noncomputable def hp768875 := @BSN.binarySplit_of_base (BSN.cosOddP 133062930) (BSN.cosOddQ 536870912) 0 1 hp768871 hp708768 hp768871 rfl rfl rfl

noncomputable def hp768876 := nat_lit 4561781793917314243762650238629044928910752828636337735253470086581877505

noncomputable def hp768877 := nat_lit 329673222740847368607529124648722373174233583842630508643489069300481

noncomputable def hp768878 := nat_lit 11946989989327575933162528911159972120447784839673710761983189339697478401

noncomputable def hp768879 := BSN.sin_dyadic_bound_f 367079777 536870912 3 2 536870912 268435456 hp768876 hp708845 hp768877 hp768878 hp708848

noncomputable def hp768880 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 367079777) (BSN.sinEvenQ 536870912) 0 2 hp768876 hp708845 hp768877 rfl rfl rfl

noncomputable def hp768881 := hp768879 hp768877 339139341 rfl rfl rfl rfl rfl rfl rfl rfl (hp768880 rfl)

noncomputable def hp768882 := @BSN.binarySplit_of_base2 (BSN.sinOddP 367079777) (BSN.sinOddQ 536870912) 0 2 hp768878 hp708848 hp768877 rfl rfl rfl

noncomputable def hp768883 := hp768870 hd4911 hd4913 hd4915 hd4917 hd4918 (hp768874 (hp768875 rfl) rfl rfl rfl rfl) (hp768881 (hp768882 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768884 := hp768802 (BSN.cos_quad_nat2 214 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 499285888 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 901581 1000)) rfl rfl (hp768883 rfl rfl rfl rfl rfl) hp768869

noncomputable def hp768885 := nat_lit 704386684085061378744331414079969286539265385422329321551237032336690625

noncomputable def hp768886 := nat_lit 25469083096660532732200980385682699820534535999650513291861187890625

noncomputable def hp768887 := nat_lit 2113109114088990815167529840279136494218155087194988663627127374634290625

noncomputable def hp768888 := BSN.cos_dyadic_bound_f 266533415 536870912 3 2 536870912 268435456 hp768885 hp708868 hp768886 hp768887 hp708870

noncomputable def hp768889 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 266533415) (BSN.cosEvenQ 536870912) 0 2 hp768885 hp708868 hp768886 rfl rfl rfl

noncomputable def hp768890 := hp768888 hp768886 472057478 rfl rfl rfl rfl rfl rfl rfl rfl (hp768889 rfl)

noncomputable def hp768891 := @BSN.binarySplit_of_base2 (BSN.cosOddP 266533415) (BSN.cosOddQ 536870912) 0 2 hp768887 hp708870 hp768886 rfl rfl rfl

noncomputable def hp768892 := nat_lit 232750511832114611681402006511275214428156021735014470487780366134651361

noncomputable def hp768893 := nat_lit 2780951109058214819761286257364982459619430954286507660790451251681

noncomputable def hp768894 := nat_lit 698245973594125718614566496961310913319548826343134838448019517501450721

noncomputable def hp768895 := BSN.cos_dyadic_bound_f 202080389 536870912 3 2 536870912 268435456 hp768892 hp708868 hp768893 hp768894 hp708870

noncomputable def hp768896 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 202080389) (BSN.cosEvenQ 536870912) 0 2 hp768892 hp708868 hp768893 rfl rfl rfl

noncomputable def hp768897 := hp768895 hp768893 499285888 rfl rfl rfl rfl rfl rfl rfl rfl (hp768896 rfl)

noncomputable def hp768898 := @BSN.binarySplit_of_base2 (BSN.cosOddP 202080389) (BSN.cosOddQ 536870912) 0 2 hp768894 hp708870 hp768893 rfl rfl rfl

noncomputable def hp768899 := hp768884 hd4920 hd4922 hd4924 hd4926 hd4918 (hp768890 (hp768891 rfl) rfl rfl rfl rfl) (hp768897 (hp768898 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768900 := hp768797 (BSN.cos_quad_nat1 21 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 97762634 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 901581 1000)) rfl rfl (hp768899 rfl rfl rfl rfl rfl) hp768869

noncomputable def hp768901 := nat_lit 15775021271846102718091195274042875392939366156430900680322051688413793985

noncomputable def hp768902 := nat_lit 3940944509273193648065715122270309912232668953880714233226184466370241

noncomputable def hp768903 := nat_lit 41309151325629540995761024083723855051173772755203218720656340599566765761

noncomputable def hp768904 := BSN.sin_dyadic_bound_f 500552967 536870912 3 2 536870912 268435456 hp768901 hp708845 hp768902 hp768903 hp708848

noncomputable def hp768905 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 500552967) (BSN.sinEvenQ 536870912) 0 2 hp768901 hp708845 hp768902 rfl rfl rfl

noncomputable def hp768906 := hp768904 hp768902 431120312 rfl rfl rfl rfl rfl rfl rfl rfl (hp768905 rfl)

noncomputable def hp768907 := @BSN.binarySplit_of_base2 (BSN.sinOddP 500552967) (BSN.sinOddQ 536870912) 0 2 hp768903 hp708848 hp768902 rfl rfl rfl

noncomputable def hp768908 := nat_lit 93413814209613119824134006250000

noncomputable def hp768909 := BSN.sin_dyadic_bound_f 98311150 536870912 2 1 536870912 268435456 hp768908 hp708890 hp768908 hp768908 hp708891

noncomputable def hp768910 := @BSN.binarySplit_of_base (BSN.sinEvenP 98311150) (BSN.sinEvenQ 536870912) 0 1 hp768908 hp708890 hp768908 rfl rfl rfl

noncomputable def hp768911 := hp768909 hp768908 97762634 rfl rfl rfl rfl rfl rfl rfl rfl (hp768910 rfl)

noncomputable def hp768912 := @BSN.binarySplit_of_base (BSN.sinOddP 98311150) (BSN.sinOddQ 536870912) 0 1 hp768908 hp708891 hp768908 rfl rfl rfl

noncomputable def hp768913 := hp768900 hd4928 hd4930 hd4932 hd4934 hd4918 (hp768906 (hp768907 rfl) rfl rfl rfl rfl) (hp768911 (hp768912 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768914 := hp768792 (BSN.cos_quad_nat3 123 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 107987955 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 901581 1000)) rfl rfl (hp768913 rfl rfl rfl rfl rfl) hp768869

noncomputable def hp768915 := nat_lit 9705195879562747423451382760370468669443408307898610905142218410862890625

noncomputable def hp768916 := nat_lit 1491943948966501128173097075922749802425798468139625940576324462890625

noncomputable def hp768917 := nat_lit 25415954632461249869117531739037828729814522846976516785754400836462890625

noncomputable def hp768918 := BSN.sin_dyadic_bound_f 443321775 536870912 3 2 536870912 268435456 hp768915 hp708845 hp768916 hp768917 hp708848

noncomputable def hp768919 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 443321775) (BSN.sinEvenQ 536870912) 0 2 hp768915 hp708845 hp768916 rfl rfl rfl

noncomputable def hp768920 := hp768918 hp768916 394630869 rfl rfl rfl rfl rfl rfl rfl rfl (hp768919 rfl)

noncomputable def hp768921 := @BSN.binarySplit_of_base2 (BSN.sinOddP 443321775) (BSN.sinOddQ 536870912) 0 2 hp768917 hp708848 hp768916 rfl rfl rfl

noncomputable def hp768922 := nat_lit 139763252469390132008804152500625

noncomputable def hp768923 := BSN.sin_dyadic_bound_f 108729715 536870912 2 1 536870912 268435456 hp768922 hp708890 hp768922 hp768922 hp708891

noncomputable def hp768924 := @BSN.binarySplit_of_base (BSN.sinEvenP 108729715) (BSN.sinEvenQ 536870912) 0 1 hp768922 hp708890 hp768922 rfl rfl rfl

noncomputable def hp768925 := hp768923 hp768922 107987955 rfl rfl rfl rfl rfl rfl rfl rfl (hp768924 rfl)

noncomputable def hp768926 := @BSN.binarySplit_of_base (BSN.sinOddP 108729715) (BSN.sinOddQ 536870912) 0 1 hp768922 hp708891 hp768922 rfl rfl rfl

noncomputable def hp768927 := hp768914 hd4936 hd4938 hd4940 hd4942 hd4918 (hp768920 (hp768921 rfl) rfl rfl rfl rfl) (hp768925 (hp768926 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768928 := hp768787 (BSN.cos_quad_nat2 238 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 475741086 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 901581 1000)) rfl rfl (hp768927 rfl rfl rfl rfl rfl) hp768869

noncomputable def hp768929 := nat_lit 16705549552001230993308707071457836228229572623237708049287636582400000000

noncomputable def hp768930 := nat_lit 4419459416907930977877469252605692238361148270523842560000000000000000

noncomputable def hp768931 := nat_lit 43745474463804420713272907379790114238882010249375053907799048192000000000

noncomputable def hp768932 := BSN.sin_dyadic_bound_f 507774800 536870912 3 2 536870912 268435456 hp768929 hp708845 hp768930 hp768931 hp708848

noncomputable def hp768933 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 507774800) (BSN.sinEvenQ 536870912) 0 2 hp768929 hp708845 hp768930 rfl rfl rfl

noncomputable def hp768934 := hp768932 hp768930 435385004 rfl rfl rfl rfl rfl rfl rfl rfl (hp768933 rfl)

noncomputable def hp768935 := @BSN.binarySplit_of_base2 (BSN.sinOddP 507774800) (BSN.sinOddQ 536870912) 0 2 hp768931 hp708848 hp768930 rfl rfl rfl

noncomputable def hp768936 := nat_lit 625097056497694259512222819440029032965636163788244482085067734725550336

noncomputable def hp768937 := nat_lit 20058085515835744043215147130656899881557551195204812513548849766656

noncomputable def hp768938 := nat_lit 1875251053322051107048582028025825785097145376262343036630176106477117696

noncomputable def hp768939 := BSN.cos_dyadic_bound_f 258693898 536870912 3 2 536870912 268435456 hp768936 hp708868 hp768937 hp768938 hp708870

noncomputable def hp768940 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 258693898) (BSN.cosEvenQ 536870912) 0 2 hp768936 hp708868 hp768937 rfl rfl rfl

noncomputable def hp768941 := hp768939 hp768937 475741086 rfl rfl rfl rfl rfl rfl rfl rfl (hp768940 rfl)

noncomputable def hp768942 := @BSN.binarySplit_of_base2 (BSN.cosOddP 258693898) (BSN.cosOddQ 536870912) 0 2 hp768938 hp708870 hp768937 rfl rfl rfl

noncomputable def hp768943 := hp768928 hd4944 hd4946 hd4961 hd4963 hd4918 (hp768934 (hp768935 rfl) rfl rfl rfl rfl) (hp768941 (hp768942 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768944 := @hp768782 109377 134217728 (hp768943 rfl rfl rfl rfl rfl) (hp768943 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp768945 := @hp768780 Bool.true 237778239 134217728 109377 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 901581 1000)) (Enclosure.sfrac Bool.false 901581 1000) 11) hp768944

noncomputable def hp768946 := @Enclosure.Real.IsNear.mulLit_tf hp768771 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1))) 19389815 67108864 1

noncomputable def hp768947 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp768770 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp768948 := @hp768947 1 1 0 1 19389815 67108864 1 67108864 19389815 67108864 1

noncomputable def hp768949 := @Enclosure.Real.IsNear.of_eq (hp768770 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp768950 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 901581 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp768951 := @hp768949 (@Inv.inv Real Real.instInv (Real.sqrt hp768772)) Bool.false 19389815 67108864 1 67108864 (hp768950 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 901581 1000) 901581 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 901581 1000))))

noncomputable def hp768952 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp768772)) Bool.false 19389815 67108864 1 67108864 19389815 67108864

noncomputable def hp768953 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp768772) Bool.false 232266247 67108864 7 67108864 232266247 67108864 7 67108864

noncomputable def hp768954 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 901581 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp768955 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 901581 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp768956 := @hp768955 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 901581 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9629522497767

noncomputable def hp768957 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 901581 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 901581 1000 0

noncomputable def hp768958 := @hp768957 1 10680707 67108864 1 67108864 9629522497767 67108864000 901581 67108864000 (Enclosure.Real.IsNear.const Bool.false 901581 1000) hd4949

noncomputable def hp768959 := @hp768956 67108864000 901581 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 901581 1000) 901581 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 901581 1000))) (hp768958 rfl)

noncomputable def hp768960 := @hp768954 9629522497767 67108864000 901581 67108864000 401940995 401941034 33554432 hp768959 rfl rfl rfl

noncomputable def hp768961 := @Enclosure.Real.IsNear.recentre' hp768772 Bool.false 803882029 67108864 39 67108864 803882029 67108864 39 67108864 (hp768960 rfl rfl rfl)

noncomputable def hp768962 := @Enclosure.Real.IsNear.sqrt_image hp768772 803882029 67108864 39 67108864 116133120 116133127 33554432 (hp768961 rfl) rfl rfl

noncomputable def hp768963 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp768772) 232266247 67108864 7 67108864 9694907 9694908 33554432 (hp768953 (hp768962 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp768964 := @hp768948 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp768951 (@hp768952 1 67108864 (hp768963 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp768965 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp768966 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp768967 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1))) (hp768965 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768966 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp768968 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 901581 1000) 901581 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 901581 1000)) rfl

noncomputable def hp768969 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp768970 := @hp768969 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768966 (Enclosure.sfrac Bool.false 1 16)))) 67710047

noncomputable def hp768971 := @hp768970 67108864 257 67108864 7266315 8388608 249164027 22837985280000 492002530166805 562949953421312 5488771364755427 383157812047380480000

noncomputable def hp768972 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp768973 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1)))) 66513019

noncomputable def hp768974 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp768975 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 206354021) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp768976 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1))) Bool.false 58083493309881983486375

noncomputable def hp768977 := nat_lit 1052456941516943546208178513

noncomputable def hp768978 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp768979 := @Enclosure.Real.IsNear.subLit_ff_p hp768772 (Enclosure.sfrac Bool.false 11 1) 803882029 67108864 39 67108864 11 1 0

noncomputable def hp768980 := @hp768978 500000000000000 65684525 67108864 39 67108864 58083493309881983486375 9444732965739290427392 hp768977 hp738031 hd4948 (@hp768979 1 65684525 65684525 67108864 39 67108864 (hp768961 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp768981 := @hp768975 206354021 33554432 123 33554432 Bool.false 66513019 67108864 1 10890000 (@hp768976 9444732965739290427392 hp768977 hp738031 206354021 33554432 123 33554432 (hp768980 rfl) rfl) (Enclosure.sfrac_false_div 206354021 33554432)

noncomputable def hp768982 := nat_lit 6951033704806081607237632

noncomputable def hp768983 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 206354021) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp768982) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp768984 := BSN.sin_reduce_arg_pos_rat_q3 206354021 33554432 226375608064910080 72057594037927936 0 hp768982 hp619237 rfl rfl rfl rfl

noncomputable def hp768985 := nat_lit 10078340043243570521676611227346681292524098696972833644596865514617569329096557176673113086947487057475234266760611547404700206047214126698496

noncomputable def hp768986 := nat_lit 3535046035078400332453934916374269593737158765657886336861565928030376934071256654347175344270861274606024356238578448744034447764688896

noncomputable def hp768987 := nat_lit 50347768375854807136412013617793722260813459640137827100222134506949290565584966964612218077357034343815678124972403874933077681202358821523456

noncomputable def hp768988 := BSN.sin_dyadic_bound_f 197560260198 137438953472 4 3 67108864 21801270 hp768985 hp737934 hp768986 hp768987 hp737937

noncomputable def hp768989 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 197560260198) (BSN.sinEvenQ 137438953472) 0 3 hp768985 hp737934 hp768986 rfl rfl rfl

noncomputable def hp768990 := hp768988 hp768986 66513019 rfl rfl rfl rfl rfl rfl rfl rfl (hp768989 rfl)

noncomputable def hp768991 := @BSN.binarySplit_of_base3 (BSN.sinOddP 197560260198) (BSN.sinOddQ 137438953472) 0 3 hp768987 hp737937 hp768986 rfl rfl rfl

noncomputable def hp768992 := @BSN.sin_arg_round Bool.false 66513019 67108864 hp768982 hp619237 197560260198 137438953472 21801270 21780000 (hp768990 (hp768991 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp768993 := hp768983 66513019 67108864 0 1000000000000000 21780000 10890000 hp768984 BSN.pi_near_15 hp768992 rfl rfl

noncomputable def hp768994 := @hp768973 67108864 85814027 22837985280000 33854895 33855152 33554432 (@hp768974 66513019 67108864 1373024432 365407764480000 66513019 67108864 85814027 22837985280000 (hp768981 (hp768993 rfl rfl) rfl rfl) rfl)

noncomputable def hp768995 := @hp768972 Bool.false 67710047 67108864 257 67108864 67710047 67108864 257 67108864 (hp768994 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp768996 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768966 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp768997 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768966 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 17556515)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp768998 := nat_lit 331633198089735070004870263205

noncomputable def hp768999 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768966 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp768998

noncomputable def hp769000 := nat_lit 208889499264158793735623346316313041

noncomputable def hp769001 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp768966 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp769002 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp769003 := @hp769002 (Enclosure.sfrac Bool.false 1 16) 93557030653975 4503599627370496 7740640167 4503599627370496 1 16 0

noncomputable def hp769004 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1)) 4314456824475625

noncomputable def hp769005 := @hp769004 4503599627370496 5123394471 4503599627370496 65684525 67108864 39 67108864 6278506046401439334400 93557030653975 4503599627370496 7740640167

noncomputable def hp769006 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1)) 65684525 67108864 39

noncomputable def hp769007 := @hp769006 67108864 65684525 67108864 39 67108864 4314456824475625 4503599627370496 5123394471 4503599627370496 (@hp768979 1 65684525 65684525 67108864 39 67108864 (hp768961 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp769008 := hp769007 (@hp768979 1 65684525 65684525 67108864 39 67108864 (hp768961 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp769009 := @hp769005 4503599627370496 (hp769008 rfl) (@hp768979 1 65684525 65684525 67108864 39 67108864 (hp768961 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp769010 := @hp769001 500000000000000 375032007364631 4503599627370496 7740640167 4503599627370496 hp768998 hp627574 hp769000 hp738055 hd4948 (@hp769003 1 6000512117834096 375032007364631 4503599627370496 7740640167 4503599627370496 (hp769009 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp769011 := @hp768997 17556515 33554432 363 33554432 Bool.false 29065260 33554432 1 10890000 (@hp768999 hp627574 hp769000 hp738055 17556515 33554432 363 33554432 (hp769010 rfl) rfl) (Enclosure.sfrac_true_div 17556515 33554432)

noncomputable def hp769012 := nat_lit 202339871406619785812562036013127128659154120111697807024190625

noncomputable def hp769013 := nat_lit 9026232065213821324530806754593951028691018132027875390625

noncomputable def hp769014 := nat_lit 607001561755728929795037046425872198075404978298829365321790625

noncomputable def hp769015 := BSN.cos_dyadic_bound_f 17556515 33554432 3 2 33554432 10890000 hp769012 hp684401 hp769013 hp769014 hp684404

noncomputable def hp769016 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 17556515) (BSN.cosEvenQ 33554432) 0 2 hp769012 hp684401 hp769013 rfl rfl rfl

noncomputable def hp769017 := hp769015 hp769013 29065260 rfl rfl rfl rfl rfl rfl rfl rfl (hp769016 rfl)

noncomputable def hp769018 := @BSN.binarySplit_of_base2 (BSN.cosOddP 17556515) (BSN.cosOddQ 33554432) 0 2 hp769014 hp684404 hp769013 rfl rfl rfl

noncomputable def hp769019 := hp769011 (BSN.cos_neg_of_bound 17556515 33554432 Bool.false 29065260 33554432 1 10890000 (hp769017 (hp769018 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp769020 := hp768971 hp768995 (@hp768996 29065260 33554432 3986624432 365407764480000 7266315 8388608 249164027 22837985280000 (hp769019 rfl) rfl)

noncomputable def hp769021 := @hp768946 67108864 492002530166805 562949953421312 5488771364755427 383157812047380480000 9539838039466268091075 37778931862957161709568 11862348450085710687173 hp743845 (hp768964 rfl) (@hp768967 Bool.false 492002530166805 562949953421312 5488771364755427 383157812047380480000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp768772 (Enclosure.sfrac Bool.false 11 1)) (hp768968 rfl (hp768775 rfl rfl))) (hp769020 rfl))

noncomputable def hp769022 := @hp768769 hp768767 hp743845 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 901581 1000))) (@hp768774 hp768767 hp743845 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 901581 1000) 11 (hp768775 rfl rfl)) (@hp768778 hp768767 hp743845 hp768945 (hp769021 rfl) rfl rfl))

theorem hd5084 : hp768768 hp743845 := hp769022

noncomputable def hp769023 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 902846 1000)) Bool.false 26132554518388758315785 37778931862957161709568 174307341680709133092761

noncomputable def hp769024 := nat_lit 212506491729134034616320000

noncomputable def hp769025 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 902846 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 902846 1000)) Bool.false 26132554518388758315785 37778931862957161709568

noncomputable def hp769026 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 902846 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp769027 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp769026 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp769028 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 902846 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp769029 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 902846 1000)) (Enclosure.sfrac Bool.false 902846 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp769027 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp769030 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 902846 1000)) hp769029 Bool.false 26132554518388758315785 37778931862957161709568

noncomputable def hp769031 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 902846 1000) 902846 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 902846 1000)) rfl

noncomputable def hp769032 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 902846 1000)) (Enclosure.sfrac Bool.false 902846 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp769027 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp769033 := nat_lit 876863023573568340471442309120

noncomputable def hp769034 := @hp769032 14551485 33554432 54765 67108864 9749038912466917819145 37778931862957161709568 888849310669529892761 hp769024 hp769033 26132554518388758315785 37778931862957161709568

noncomputable def hp769035 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 902846 1000)) (Enclosure.sfrac Bool.false 902846 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 902846 1000)) (Enclosure.sfrac Bool.false 902846 1000) 11)

noncomputable def hp769036 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 902846 1000)) (Enclosure.sfrac Bool.false 902846 1000) 11) hp769035

noncomputable def hp769037 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 902846 1000)) (Enclosure.sfrac Bool.false 902846 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 902846 1000)) (Enclosure.sfrac Bool.false 902846 1000) 11)

noncomputable def hp769038 := @hp769037 116411880 536870912 219060 536870912 116411880 536870912 219060 536870912 124996304366469120 14551485 33554432

noncomputable def hp769039 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 902846 1000)) (Enclosure.sfrac Bool.false 902846 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp769040 := hp769039 BSN.quadSignNeg 9 10 11 902846 1000 183 238 536870912 268435456 9007199254740992

noncomputable def hp769041 := hp769040 Bool.false 961378524148 4112 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp769042 := hp769041 Bool.false 155561578 188057 Bool.true 384916967 Bool.true 200565183 28296951008113761 1 Bool.false 352777309

noncomputable def hp769043 := hp769042 Bool.false Bool.false 499840856 Bool.true Bool.false 116411880 219060 BSN.abs_quadSignPos (BSN.cos_quad_nat3 183 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 352777309 536870912) BSN.abs_quadSignNeg

noncomputable def hp769044 := hp769039 BSN.quadSignNeg 7 8 9 902846 1000 55 122 536870912 268435456 9007199254740992

noncomputable def hp769045 := hp769044 Bool.false 961378524148 4112 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp769046 := hp769045 Bool.false 125260441 153585 Bool.true 168917852 Bool.true 757632003 28296951008113761 1 Bool.false 166144622

noncomputable def hp769047 := hp769046 Bool.false Bool.false 85319576 Bool.true Bool.false 155561578 188057 BSN.abs_quadSignPos (BSN.cos_quad_nat3 55 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 166144622 536870912) BSN.abs_quadSignNeg

noncomputable def hp769048 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 902846 1000)) (Enclosure.sfrac Bool.false 902846 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp769049 := hp769048 BSN.quadSignNeg 5 6 7 902846 1000 110 21 536870912 268435456 9007199254740992

noncomputable def hp769050 := hp769049 Bool.false 961378524148 4112 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp769051 := hp769050 Bool.false 492528072 114131 Bool.false 127018934 Bool.false 463401829 28296951008113761 1 Bool.false 521915089

noncomputable def hp769052 := hp769051 Bool.true Bool.false 407966078 Bool.true Bool.false 125260441 153585 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 110 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 521915089 536870912) BSN.abs_quadSignNeg

noncomputable def hp769053 := hp769039 BSN.quadSignNeg 3 4 5 902846 1000 343 214 536870912 268435456 9007199254740992

noncomputable def hp769054 := hp769053 Bool.false 961378524148 4112 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp769055 := hp769054 Bool.false 430990904 67456 Bool.false 168367655 Bool.false 795683397 28296951008113761 1 Bool.false 165621347

noncomputable def hp769056 := hp769055 Bool.false Bool.false 47568996 Bool.true Bool.false 492528072 114131 BSN.abs_quadSignPos (BSN.cos_quad_nat3 343 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 165621347 536870912) BSN.abs_quadSignNeg

noncomputable def hp769057 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 902846 1000)) (Enclosure.sfrac Bool.false 902846 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp769058 := hp769057 BSN.quadSignPos 1 2 3 902846 1000 741 508 536870912 268435456 9007199254740992

noncomputable def hp769059 := hp769058 Bool.false 961378524148 4112 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp769060 := hp769059 Bool.false 536870752 4170 Bool.false 505642329 Bool.false 464290899 28296951008113761 1 Bool.false 434133883

noncomputable def hp769061 := hp769060 Bool.true Bool.false 348313970 Bool.false Bool.false 430990904 67456 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 741 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 434133883 536870912) BSN.abs_quadSignPos

noncomputable def hp769062 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 902846 1000)) (Enclosure.sfrac Bool.false 902846 1000) 1) Bool.false

noncomputable def hp769063 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 902846 1000)) (Enclosure.sfrac Bool.false 902846 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 902846 1000)))

noncomputable def hp769064 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 902846 1000))) Bool.false 67108844 67108864

noncomputable def hp769065 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 902846 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 60086157759) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 60086157759 33554432

noncomputable def hp769066 := nat_lit 1228455182957907511762319634735054599506232214041247656509

noncomputable def hp769067 := nat_lit 686016837135111529359135925040689190061824217710592000

noncomputable def hp769068 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 902846 1000)) Bool.false hp769066 hp769067 68324983732816521529

noncomputable def hp769069 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 902846 4000) (Real.log (Enclosure.sfrac Bool.false 3260524598864 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1805692))))))

noncomputable def hp769070 := nat_lit 287945281458426877647554022548480000

noncomputable def hp769071 := nat_lit 1559821696753514355257575346151245844480

noncomputable def hp769072 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 902846 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp769069 (Enclosure.sfrac Bool.false 902846 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 902846 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp769070 hp769071)) Bool.false

noncomputable def hp769073 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 902846 1000) 902846 1000 3260524598864 16000000 1805692

noncomputable def hp769074 := hp769073 4000 2000 hp769070 hp769071 (@Eq.refl Real (Enclosure.sfrac Bool.false 902846 1000)) rfl rfl rfl rfl

noncomputable def hp769075 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp769069 (Enclosure.sfrac Bool.false 902846 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 902846 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp769070 hp769071) 16129256820136475294809 9007199254740992000

noncomputable def hp769076 := nat_lit 25158762146977945840892306119373918197887635743564752005304320

noncomputable def hp769077 := @hp769075 68324983732816521529 hp739631 hp769070 hp769071 0 1 hp769076 hp769066 hp769067 68324983732816521529 hp739631

noncomputable def hp769078 := @Enclosure.Real.IsNear.subLit_ff_p (hp769069 (Enclosure.sfrac Bool.false 902846 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 902846 2000) (Real.log Real.pi)) 20783793667925781183577 9007199254740992000 5692795857466249 2178000000000000000000

noncomputable def hp769079 := nat_lit 541208051181805590999348543488000

noncomputable def hp769080 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 902846 4000) (Real.log (Enclosure.sfrac Bool.false 3260524598864 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1805692))))))

noncomputable def hp769081 := @hp769080 (Enclosure.sfrac Bool.false 902846 2000) 24849850577098724015193 9007199254740992000 5692795857466249 2178000000000000000000 902846 2000 0

noncomputable def hp769082 := nat_lit 41567587335851562367154000

noncomputable def hp769083 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 902846 4000) (Real.log (Enclosure.sfrac Bool.false 3260524598864 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1805692))))) 24853386448957827387193

noncomputable def hp769084 := nat_lit 55956888899617159228205952992871972864

noncomputable def hp769085 := @hp769083 9007199254740992000 5642795857193999 2178000000000000000000 883967964775843 2251799813685248 200000001089 8712000000000000000 hp769084 24849850577098724015193 9007199254740992000 5692795857466249

noncomputable def hp769086 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 902846 4000) (Real.log (Enclosure.sfrac Bool.false 3260524598864 16000000)) 902846 4000 0 1 55055649466149991 4503599627370496

noncomputable def hp769087 := nat_lit 118231106958577035187847168

noncomputable def hp769088 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3260524598864) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp769087 hp617687

noncomputable def hp769089 := BSN.log_rat_reduce_isNear 3260524598864 16000000 17 6521049197728 4194304000000 118462678 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp769090 := nat_lit 75593732081847719988478630766398002024052990844716523212617286590042228564442724754651757926774626815939789563360003354863216554161949073376543134775729192960

noncomputable def hp769091 := nat_lit 1222876076345116669539678297058411066176311060610107563509485116649359951526358237697575654675258314315869131412527325790846916632846168973461355709870374912

noncomputable def hp769092 := nat_lit 63892585148846252808183254136595450496894741290767848543373559798523944554496306960932685181870256461815669520017755840135297923267733219467769937920

noncomputable def hp769093 := BSN.log_dyadic_bound 1163372598864 5357676598864 7 6 hp769090 268435456 87120000 hp769091 hp769092 118462678 6521049197728

noncomputable def hp769094 := hp769093 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp769095 := @BSN.binarySplit_of_base6 (BSN.artanhP 1163372598864) (BSN.artanhQ 5357676598864) 0 6 hp769091 hp769090 hp769092 rfl rfl rfl

noncomputable def hp769096 := hp769089 rfl rfl rfl rfl (hp769094 (hp769095 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp769097 := @hp769086 12500018513 1089000000000000000 24853386448957827387193 9007199254740992000 5642795857193999 2178000000000000000000 (Enclosure.Real.IsNear.const Bool.false 902846 4000) (BSN.isNear_log_sfrac 3260524598864 16000000 55055649466149991 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp769088 1000001481040000 87120000000000000000000 55055649466149991 4503599627370496 12500018513 1089000000000000000 (hp769096 rfl rfl rfl) rfl)) rfl

noncomputable def hp769098 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1805692)))) 1 4

noncomputable def hp769099 := @hp769098 0 1 883967964775843 562949953421312 200000001089 2178000000000000000 883967964775843 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp769100 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1805692))) 884279719003555 562949953421312 1

noncomputable def hp769101 := @hp769100 2000000000000000 18582 33554432 1 10890000 29661042964249419186176 883967964775843 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp769102 := BSN.arctan_dyadic_bound_f 1000 1805692 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp769103 := hp769102 1 18582 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1805692) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1805692) 0 0 rfl)

noncomputable def hp769104 := hp769099 (hp769101 (hp769103 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp769105 := @hp769078 17339500962903 33554432000 1354269 268435456000 hp769079 16129256820136475294809 9007199254740992000 68324983732816521529 hp739631 (@hp769081 1 hp769082 20783793667925781183577 9007199254740992000 5692795857466249 2178000000000000000000 (@hp769085 2178000000000000000000 hp769097 hp769104 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 902846 2000) rfl rfl)

noncomputable def hp769106 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 902846 2000) (Real.log Real.pi) 902846 2000 0 1 38410761 33554432

noncomputable def hp769107 := hp769105 (@hp769106 3 268435456 17339500962903 33554432000 1354269 268435456000 (Enclosure.Real.IsNear.const Bool.false 902846 2000) hd4909 rfl) rfl

noncomputable def hp769108 := @hp769068 hp739631 60086157759 33554432 515 67108864 (@hp769072 hp769066 hp769067 68324983732816521529 hp739631 (hp769074 rfl rfl rfl rfl rfl) (hp769077 (hp769107 rfl) (Enclosure.Real.IsNear.const Bool.true hp769070 hp769071) rfl rfl)) rfl

noncomputable def hp769109 := nat_lit 7592191250252634162987008

noncomputable def hp769110 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 60086157759) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp769109) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp769111 := BSN.sin_reduce_arg_pos_rat_q3 60086157759 33554432 226375608064910080 72057594037927936 284 hp769109 hp619237 rfl rfl rfl rfl

noncomputable def hp769112 := nat_lit 14352223650956752964262745907357985330600668348612055723682624897608429761444630738955897766132830521161356095175550232412078338193555046076416

noncomputable def hp769113 := nat_lit 10190793858543061532100494272198401485868914637026672974865936899649180304506701697410721803848631585014978035350884939454647252401852416

noncomputable def hp769114 := nat_lit 71672120200095451990972768337441027402758762990968929860525495147520742986460687996775518376587205545897308812551368324943058370935307862347776

noncomputable def hp769115 := BSN.sin_dyadic_bound_f 215783053654 137438953472 4 3 67108864 21801270 hp769112 hp737934 hp769113 hp769114 hp737937

noncomputable def hp769116 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215783053654) (BSN.sinEvenQ 137438953472) 0 3 hp769112 hp737934 hp769113 rfl rfl rfl

noncomputable def hp769117 := hp769115 hp769113 67108844 rfl rfl rfl rfl rfl rfl rfl rfl (hp769116 rfl)

noncomputable def hp769118 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215783053654) (BSN.sinOddQ 137438953472) 0 3 hp769114 hp737937 hp769113 rfl rfl rfl

noncomputable def hp769119 := @BSN.sin_arg_round Bool.false 67108844 67108864 hp769109 hp619237 215783053654 137438953472 21801270 21780000 (hp769117 (hp769118 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769120 := hp769110 67108844 67108864 284 1000000000000000 21780000 10890000 hp769111 BSN.pi_near_15 hp769119 rfl rfl

noncomputable def hp769121 := @hp769065 515 67108864 Bool.false 67108844 67108864 1 10890000 hp769108 (Enclosure.sfrac_false_div 60086157759 33554432) (hp769120 rfl rfl) rfl

noncomputable def hp769122 := @hp769062 16777211 16777216 354716179 45675970560000 536870752 536870912 4170 536870912 (@hp769063 Bool.false 16777211 16777216 354716179 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 902846 1000)) (Enclosure.sfrac Bool.false 902846 1000)) (@hp769064 5675458864 730815528960000 16777211 16777216 354716179 45675970560000 (hp769121 rfl) rfl))

noncomputable def hp769123 := @hp769068 hp739631 961378524148 536870912 4112 536870912 (@hp769072 hp769066 hp769067 68324983732816521529 hp739631 (hp769074 rfl rfl rfl rfl rfl) (hp769077 (hp769107 rfl) (Enclosure.Real.IsNear.const Bool.true hp769070 hp769071) rfl rfl)) rfl

noncomputable def hp769124 := hp769061 (BSN.cos_quad_nat0 508 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 348313970 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 902846 1000)) rfl rfl (hp769122 rfl) hp769123

noncomputable def hp769125 := nat_lit 16426610747797912027915192586597031522475653555606129401411060670988036545

noncomputable def hp769126 := nat_lit 4273142582764957453080943135265280356761947701165348852291248459098561

noncomputable def hp769127 := nat_lit 43015157346717673951520516199820843533525287587452261676982401640796793281

noncomputable def hp769128 := BSN.sin_dyadic_bound_f 505642329 536870912 3 2 536870912 268435456 hp769125 hp708845 hp769126 hp769127 hp708848

noncomputable def hp769129 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 505642329) (BSN.sinEvenQ 536870912) 0 2 hp769125 hp708845 hp769126 rfl rfl rfl

noncomputable def hp769130 := hp769128 hp769126 434133883 rfl rfl rfl rfl rfl rfl rfl rfl (hp769129 rfl)

noncomputable def hp769131 := @BSN.binarySplit_of_base2 (BSN.sinOddP 505642329) (BSN.sinOddQ 536870912) 0 2 hp769127 hp708848 hp769126 rfl rfl rfl

noncomputable def hp769132 := nat_lit 6487748913337897448034209837803436403798729823600296800601106582062805281

noncomputable def hp769133 := nat_lit 2159341671201251764106059036433727542229337631802553822125854300352801

noncomputable def hp769134 := nat_lit 19458928056671289840574417395337441756311730795537285294159068037587710241

noncomputable def hp769135 := BSN.cos_dyadic_bound_f 464290899 536870912 3 2 536870912 268435456 hp769132 hp708868 hp769133 hp769134 hp708870

noncomputable def hp769136 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 464290899) (BSN.cosEvenQ 536870912) 0 2 hp769132 hp708868 hp769133 rfl rfl rfl

noncomputable def hp769137 := hp769135 hp769133 348313970 rfl rfl rfl rfl rfl rfl rfl rfl (hp769136 rfl)

noncomputable def hp769138 := @BSN.binarySplit_of_base2 (BSN.cosOddP 464290899) (BSN.cosOddQ 536870912) 0 2 hp769134 hp708870 hp769133 rfl rfl rfl

noncomputable def hp769139 := hp769124 hd4911 hd4913 hd4915 hd4917 hd4918 (hp769130 (hp769131 rfl) rfl rfl rfl rfl) (hp769137 (hp769138 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769140 := hp769056 (BSN.cos_quad_nat2 214 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 47568996 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 902846 1000)) rfl rfl (hp769139 rfl rfl rfl rfl rfl) hp769123

noncomputable def hp769141 := nat_lit 803590238528006351448902110950625

noncomputable def hp769142 := BSN.sin_dyadic_bound_f 168367655 536870912 2 1 536870912 268435456 hp769141 hp708890 hp769141 hp769141 hp708891

noncomputable def hp769143 := @BSN.binarySplit_of_base (BSN.sinEvenP 168367655) (BSN.sinEvenQ 536870912) 0 1 hp769141 hp708890 hp769141 rfl rfl rfl

noncomputable def hp769144 := hp769142 hp769141 165621347 rfl rfl rfl rfl rfl rfl rfl rfl (hp769143 rfl)

noncomputable def hp769145 := @BSN.binarySplit_of_base (BSN.sinOddP 168367655) (BSN.sinOddQ 536870912) 0 1 hp769141 hp708891 hp769141 rfl rfl rfl

noncomputable def hp769146 := nat_lit 55372212537682731739320756582531290241881091595443208949232261231407286500655448835098432494605632093248984848721

noncomputable def hp769147 := nat_lit 64399656698997236751199942013209162925177896576032778322358343931119379777080343737248550164223661474453841

noncomputable def hp769148 := nat_lit 335283106231979613699512151635038506194561521255728451992393810162719587377268964478539967360946384855899093997905

noncomputable def hp769149 := BSN.cos_dyadic_bound_f 795683397 536870912 4 3 536870912 268435456 hp769146 hp716712 hp769147 hp769148 hp716714

noncomputable def hp769150 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 795683397) (BSN.cosEvenQ 536870912) 0 3 hp769146 hp716712 hp769147 rfl rfl rfl

noncomputable def hp769151 := hp769149 hp769147 47568996 rfl rfl rfl rfl rfl rfl rfl rfl (hp769150 rfl)

noncomputable def hp769152 := @BSN.binarySplit_of_base3 (BSN.cosOddP 795683397) (BSN.cosOddQ 536870912) 0 3 hp769148 hp716714 hp769147 rfl rfl rfl

noncomputable def hp769153 := hp769140 hd4920 hd4922 hd4924 hd4926 hd4918 (hp769144 (hp769145 rfl) rfl rfl rfl rfl) (hp769151 (hp769152 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769154 := hp769052 (BSN.cos_quad_nat1 21 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 407966078 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 902846 1000)) rfl rfl (hp769153 rfl rfl rfl rfl rfl) hp769123

noncomputable def hp769155 := nat_lit 260299812031462671225925297278736

noncomputable def hp769156 := BSN.cos_dyadic_bound_f 127018934 536870912 2 1 536870912 268435456 hp769155 hp708767 hp769155 hp769155 hp708768

noncomputable def hp769157 := @BSN.binarySplit_of_base (BSN.cosEvenP 127018934) (BSN.cosEvenQ 536870912) 0 1 hp769155 hp708767 hp769155 rfl rfl rfl

noncomputable def hp769158 := hp769156 hp769155 521915089 rfl rfl rfl rfl rfl rfl rfl rfl (hp769157 rfl)

noncomputable def hp769159 := @BSN.binarySplit_of_base (BSN.cosOddP 127018934) (BSN.cosOddQ 536870912) 0 1 hp769155 hp708768 hp769155 rfl rfl rfl

noncomputable def hp769160 := nat_lit 11587025650924717653783101449960357798427347091454846432241951825120568545

noncomputable def hp769161 := nat_lit 2126483163822487259145170950419630515224728057447528977662102199182561

noncomputable def hp769162 := nat_lit 30343529065394738399583792568357400546475545203622063704193658995564717281

noncomputable def hp769163 := BSN.sin_dyadic_bound_f 463401829 536870912 3 2 536870912 268435456 hp769160 hp708845 hp769161 hp769162 hp708848

noncomputable def hp769164 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 463401829) (BSN.sinEvenQ 536870912) 0 2 hp769160 hp708845 hp769161 rfl rfl rfl

noncomputable def hp769165 := hp769163 hp769161 407966078 rfl rfl rfl rfl rfl rfl rfl rfl (hp769164 rfl)

noncomputable def hp769166 := @BSN.binarySplit_of_base2 (BSN.sinOddP 463401829) (BSN.sinOddQ 536870912) 0 2 hp769162 hp708848 hp769161 rfl rfl rfl

noncomputable def hp769167 := hp769154 hd4928 hd4930 hd4932 hd4934 hd4918 (hp769158 (hp769159 rfl) rfl rfl rfl rfl) (hp769165 (hp769166 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769168 := hp769047 (BSN.cos_quad_nat2 122 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 85319576 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 902846 1000)) rfl rfl (hp769167 rfl rfl rfl rfl rfl) hp769123

noncomputable def hp769169 := nat_lit 814145826230504111339579371561216

noncomputable def hp769170 := BSN.sin_dyadic_bound_f 168917852 536870912 2 1 536870912 268435456 hp769169 hp708890 hp769169 hp769169 hp708891

noncomputable def hp769171 := @BSN.binarySplit_of_base (BSN.sinEvenP 168917852) (BSN.sinEvenQ 536870912) 0 1 hp769169 hp708890 hp769169 rfl rfl rfl

noncomputable def hp769172 := hp769170 hp769169 166144622 rfl rfl rfl rfl rfl rfl rfl rfl (hp769171 rfl)

noncomputable def hp769173 := @BSN.binarySplit_of_base (BSN.sinOddP 168917852) (BSN.sinOddQ 536870912) 0 1 hp769169 hp708891 hp769169 rfl rfl rfl

noncomputable def hp769174 := nat_lit 45492765947157539605670334660197605265564841966466432298818496565734623072743314668164613454645608304249959566321

noncomputable def hp769175 := nat_lit 35768418320642903460381079344417835203589232094715341913514670479912896004085669506453890759435452047379441

noncomputable def hp769176 := nat_lit 275555932979338010804717047561594956156977190686821868521159167169059488961288093036698141817590277449085891333105

noncomputable def hp769177 := BSN.cos_dyadic_bound_f 757632003 536870912 4 3 536870912 268435456 hp769174 hp716712 hp769175 hp769176 hp716714

noncomputable def hp769178 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 757632003) (BSN.cosEvenQ 536870912) 0 3 hp769174 hp716712 hp769175 rfl rfl rfl

noncomputable def hp769179 := hp769177 hp769175 85319576 rfl rfl rfl rfl rfl rfl rfl rfl (hp769178 rfl)

noncomputable def hp769180 := @BSN.binarySplit_of_base3 (BSN.cosOddP 757632003) (BSN.cosOddQ 536870912) 0 3 hp769176 hp716714 hp769175 rfl rfl rfl

noncomputable def hp769181 := hp769168 hd4936 hd4938 hd4940 hd4942 hd4918 (hp769172 (hp769173 rfl) rfl rfl rfl rfl) (hp769179 (hp769180 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769182 := hp769043 (BSN.cos_quad_nat2 238 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 499840856 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 902846 1000)) rfl rfl (hp769181 rfl rfl rfl rfl rfl) hp769123

noncomputable def hp769183 := nat_lit 5515278539793810233775297883428925724996840779521339762733342931413761985

noncomputable def hp769184 := nat_lit 481877269141090993565897343817599561465904602597304274987335733346241

noncomputable def hp769185 := nat_lit 14443996945786131703040959194233386499511257243675494219284966276801101761

noncomputable def hp769186 := BSN.sin_dyadic_bound_f 384916967 536870912 3 2 536870912 268435456 hp769183 hp708845 hp769184 hp769185 hp708848

noncomputable def hp769187 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 384916967) (BSN.sinEvenQ 536870912) 0 2 hp769183 hp708845 hp769184 rfl rfl rfl

noncomputable def hp769188 := hp769186 hp769184 352777309 rfl rfl rfl rfl rfl rfl rfl rfl (hp769187 rfl)

noncomputable def hp769189 := @BSN.binarySplit_of_base2 (BSN.sinOddP 384916967) (BSN.sinOddQ 536870912) 0 2 hp769185 hp708848 hp769184 rfl rfl rfl

noncomputable def hp769190 := nat_lit 225847865519965351939090631240342389006786075636334439263048899446878721

noncomputable def hp769191 := nat_lit 2618450407712532384960189452690563354829211479356108892984705200641

noncomputable def hp769192 := nat_lit 677538359659080630752501973342121785893648568486044605571360728930234881

noncomputable def hp769193 := BSN.cos_dyadic_bound_f 200565183 536870912 3 2 536870912 268435456 hp769190 hp708868 hp769191 hp769192 hp708870

noncomputable def hp769194 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 200565183) (BSN.cosEvenQ 536870912) 0 2 hp769190 hp708868 hp769191 rfl rfl rfl

noncomputable def hp769195 := hp769193 hp769191 499840856 rfl rfl rfl rfl rfl rfl rfl rfl (hp769194 rfl)

noncomputable def hp769196 := @BSN.binarySplit_of_base2 (BSN.cosOddP 200565183) (BSN.cosOddQ 536870912) 0 2 hp769192 hp708870 hp769191 rfl rfl rfl

noncomputable def hp769197 := hp769182 hd4944 hd4946 hd4961 hd4963 hd4918 (hp769188 (hp769189 rfl) rfl rfl rfl rfl) (hp769195 (hp769196 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769198 := @hp769038 54765 67108864 (hp769197 rfl rfl rfl rfl rfl) (hp769197 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp769199 := @hp769036 Bool.false 14551485 33554432 54765 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 902846 1000)) (Enclosure.sfrac Bool.false 902846 1000) 11) hp769198

noncomputable def hp769200 := @Enclosure.Real.IsNear.mulLit_tf hp769027 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1))) 4845755 16777216 1

noncomputable def hp769201 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp769026 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp769202 := @hp769201 1 1 0 1 4845755 16777216 1 33554432 4845755 16777216 1

noncomputable def hp769203 := @Enclosure.Real.IsNear.of_eq (hp769026 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp769204 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 902846 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp769205 := @hp769203 (@Inv.inv Real Real.instInv (Real.sqrt hp769028)) Bool.false 4845755 16777216 1 33554432 (hp769204 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 902846 1000) 902846 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 902846 1000))))

noncomputable def hp769206 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp769028)) Bool.false 19383020 67108864 2 67108864 4845755 16777216

noncomputable def hp769207 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp769028) Bool.false 232347677 67108864 7 67108864 232347677 67108864 7 67108864

noncomputable def hp769208 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 902846 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp769209 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 902846 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp769210 := @hp769209 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 902846 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 4821516796061

noncomputable def hp769211 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 902846 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 902846 1000 0

noncomputable def hp769212 := @hp769211 1 10680707 67108864 1 67108864 4821516796061 33554432000 451423 33554432000 (Enclosure.Real.IsNear.const Bool.false 902846 1000) hd4949

noncomputable def hp769213 := @hp769210 33554432000 451423 33554432000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 902846 1000) 902846 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 902846 1000))) (hp769212 rfl)

noncomputable def hp769214 := @hp769208 4821516796061 33554432000 451423 33554432000 402222876 402222915 33554432 hp769213 rfl rfl rfl

noncomputable def hp769215 := @Enclosure.Real.IsNear.recentre' hp769028 Bool.false 804445791 67108864 39 67108864 804445791 67108864 39 67108864 (hp769214 rfl rfl rfl)

noncomputable def hp769216 := @Enclosure.Real.IsNear.sqrt_image hp769028 804445791 67108864 39 67108864 116173835 116173842 33554432 (hp769215 rfl) rfl rfl

noncomputable def hp769217 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp769028) 232347677 67108864 7 67108864 9691509 9691511 33554432 (hp769207 (hp769216 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp769218 := @hp769202 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp769205 (@hp769206 1 33554432 (hp769217 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp769219 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp769220 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp769221 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1))) (hp769219 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp769220 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp769222 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 902846 1000) 902846 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 902846 1000)) rfl

noncomputable def hp769223 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp769224 := @hp769223 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp769220 (Enclosure.sfrac Bool.false 1 16)))) 67327291

noncomputable def hp769225 := @hp769224 67108864 255 67108864 29881969 33554432 250525277 22837985280000 2011872022515979 2251799813685248 182260727064377 12666373951979520000

noncomputable def hp769226 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp769227 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1)))) 66891145

noncomputable def hp769228 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp769229 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 416250263) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp769230 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1))) Bool.false 58582016612826865660285

noncomputable def hp769231 := nat_lit 1052456941521786224913633617

noncomputable def hp769232 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp769233 := @Enclosure.Real.IsNear.subLit_ff_p hp769028 (Enclosure.sfrac Bool.false 11 1) 804445791 67108864 39 67108864 11 1 0

noncomputable def hp769234 := @hp769232 500000000000000 66248287 67108864 39 67108864 58582016612826865660285 9444732965739290427392 hp769231 hp738031 hd4948 (@hp769233 1 66248287 66248287 67108864 39 67108864 (hp769215 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp769235 := @hp769229 416250263 67108864 123 33554432 Bool.false 66891145 67108864 1 10890000 (@hp769230 9444732965739290427392 hp769231 hp738031 416250263 67108864 123 33554432 (hp769234 rfl) rfl) (Enclosure.sfrac_false_div 416250263 67108864)

noncomputable def hp769236 := nat_lit 14412555255233409477246976

noncomputable def hp769237 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 416250263) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp769236) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp769238 := BSN.sin_reduce_arg_pos_rat_q3 416250263 67108864 226375608064910080 72057594037927936 0 hp769236 hp617687 rfl rfl rfl rfl

noncomputable def hp769239 := nat_lit 11644757182717768020615684074587256276149949159016572879062829521560041950034780453618138427311861219381816623929834853895106526947136812814336

noncomputable def hp769240 := nat_lit 5449218435656132654150418157277347009954742099620154585483148364535934969751379974414074155525859507376980619575800928044421034692775936

noncomputable def hp769241 := nat_lit 58165159429573017826707478130932009809624235914990746699392330943567119997499034498292813211796025899988466490216214701920517863346942304260096

noncomputable def hp769242 := BSN.sin_dyadic_bound_f 204814728806 137438953472 4 3 67108864 21801270 hp769239 hp737934 hp769240 hp769241 hp737937

noncomputable def hp769243 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 204814728806) (BSN.sinEvenQ 137438953472) 0 3 hp769239 hp737934 hp769240 rfl rfl rfl

noncomputable def hp769244 := hp769242 hp769240 66891145 rfl rfl rfl rfl rfl rfl rfl rfl (hp769243 rfl)

noncomputable def hp769245 := @BSN.binarySplit_of_base3 (BSN.sinOddP 204814728806) (BSN.sinOddQ 137438953472) 0 3 hp769241 hp737937 hp769240 rfl rfl rfl

noncomputable def hp769246 := @BSN.sin_arg_round Bool.false 66891145 67108864 hp769236 hp617687 204814728806 137438953472 21801270 21780000 (hp769244 (hp769245 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769247 := hp769237 66891145 67108864 0 1000000000000000 21780000 10890000 hp769238 BSN.pi_near_15 hp769246 rfl rfl

noncomputable def hp769248 := @hp769227 67108864 85814027 22837985280000 33663518 33663773 33554432 (@hp769228 66891145 67108864 1373024432 365407764480000 66891145 67108864 85814027 22837985280000 (hp769235 (hp769247 rfl rfl) rfl rfl) rfl)

noncomputable def hp769249 := @hp769226 Bool.false 67327291 67108864 255 67108864 67327291 67108864 255 67108864 (hp769248 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp769250 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp769220 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp769251 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp769220 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15845707)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp769252 := nat_lit 299316949422847781097201466525

noncomputable def hp769253 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp769220 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp769252

noncomputable def hp769254 := nat_lit 210076169723735644337044180777843061

noncomputable def hp769255 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp769220 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp769256 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp769257 := @hp769256 (Enclosure.sfrac Bool.false 1 16) 57011752081599 4503599627370496 7784613603 4503599627370496 1 16 0

noncomputable def hp769258 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1)) 4388835530434369

noncomputable def hp769259 := @hp769258 4503599627370496 5167367907 4503599627370496 66248287 67108864 39 67108864 3825993916845744193536 57011752081599 4503599627370496 7784613603

noncomputable def hp769260 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1)) 66248287 67108864 39

noncomputable def hp769261 := @hp769260 67108864 66248287 67108864 39 67108864 4388835530434369 4503599627370496 5167367907 4503599627370496 (@hp769233 1 66248287 66248287 67108864 39 67108864 (hp769215 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp769262 := hp769261 (@hp769233 1 66248287 66248287 67108864 39 67108864 (hp769215 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp769263 := @hp769259 4503599627370496 (hp769262 rfl) (@hp769233 1 66248287 66248287 67108864 39 67108864 (hp769215 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp769264 := @hp769255 500000000000000 338486728792255 4503599627370496 7784613603 4503599627370496 hp769252 hp627574 hp769254 hp738055 hd4948 (@hp769257 1 5415787660676080 338486728792255 4503599627370496 7784613603 4503599627370496 (hp769263 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp769265 := @hp769251 15845707 33554432 365 33554432 Bool.false 29881969 33554432 1 10890000 (@hp769253 hp627574 hp769254 hp738055 15845707 33554432 365 33554432 (hp769264 rfl) rfl) (Enclosure.sfrac_true_div 15845707 33554432)

noncomputable def hp769266 := nat_lit 134266661125118804164471115590588497182052553767116219583101281

noncomputable def hp769267 := nat_lit 3974595803429096686700856574671981460749365347409504565601

noncomputable def hp769268 := nat_lit 402792034183749554300039945058616147583236162570653839740172641

noncomputable def hp769269 := BSN.cos_dyadic_bound_f 15845707 33554432 3 2 33554432 10890000 hp769266 hp684401 hp769267 hp769268 hp684404

noncomputable def hp769270 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 15845707) (BSN.cosEvenQ 33554432) 0 2 hp769266 hp684401 hp769267 rfl rfl rfl

noncomputable def hp769271 := hp769269 hp769267 29881969 rfl rfl rfl rfl rfl rfl rfl rfl (hp769270 rfl)

noncomputable def hp769272 := @BSN.binarySplit_of_base2 (BSN.cosOddP 15845707) (BSN.cosOddQ 33554432) 0 2 hp769268 hp684404 hp769267 rfl rfl rfl

noncomputable def hp769273 := hp769265 (BSN.cos_neg_of_bound 15845707 33554432 Bool.false 29881969 33554432 1 10890000 (hp769271 (hp769272 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp769274 := hp769225 hp769249 (@hp769250 29881969 33554432 4008404432 365407764480000 29881969 33554432 250525277 22837985280000 (hp769273 rfl) rfl)

noncomputable def hp769275 := @hp769200 33554432 2011872022515979 2251799813685248 182260727064377 12666373951979520000 9749038912466917819145 37778931862957161709568 888849310669529892761 hp769024 (hp769218 rfl) (@hp769221 Bool.false 2011872022515979 2251799813685248 182260727064377 12666373951979520000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769028 (Enclosure.sfrac Bool.false 11 1)) (hp769222 rfl (hp769031 rfl rfl))) (hp769274 rfl))

noncomputable def hp769276 := @hp769025 174307341680709133092761 hp769024 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 902846 1000))) (@hp769030 174307341680709133092761 hp769024 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 902846 1000) 11 (hp769031 rfl rfl)) (@hp769034 174307341680709133092761 hp769024 hp769199 (hp769275 rfl) rfl rfl))

theorem hd5085 : hp769023 hp769024 := hp769276

noncomputable def hp769277 := nat_lit 14078618875882207297226617

noncomputable def hp769278 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 904111 1000)) Bool.true 104447443071669232417367 37778931862957161709568 hp769277

noncomputable def hp769279 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 904111 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 904111 1000)) Bool.true 104447443071669232417367 37778931862957161709568

noncomputable def hp769280 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 904111 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp769281 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp769280 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp769282 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 904111 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp769283 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000)) (Enclosure.sfrac Bool.false 904111 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp769281 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp769284 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 904111 1000)) hp769283 Bool.true 104447443071669232417367 37778931862957161709568

noncomputable def hp769285 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 904111 1000) 904111 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 904111 1000)) rfl

noncomputable def hp769286 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000)) (Enclosure.sfrac Bool.false 904111 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp769281 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp769287 := nat_lit 28037397008977571085125892964352

noncomputable def hp769288 := @hp769286 812927299 268435456 219361 268435456 9961903205071510881705 37778931862957161709568 70305407794635718346617 hp741590 hp769287 104447443071669232417367 37778931862957161709568

noncomputable def hp769289 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000)) (Enclosure.sfrac Bool.false 904111 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000)) (Enclosure.sfrac Bool.false 904111 1000) 11)

noncomputable def hp769290 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000)) (Enclosure.sfrac Bool.false 904111 1000) 11) hp769289

noncomputable def hp769291 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000)) (Enclosure.sfrac Bool.false 904111 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000)) (Enclosure.sfrac Bool.false 904111 1000) 11)

noncomputable def hp769292 := @hp769291 812927299 536870912 219361 536870912 812927299 536870912 219361 536870912 872874040807653376 812927299 268435456

noncomputable def hp769293 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000)) (Enclosure.sfrac Bool.false 904111 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp769294 := hp769293 BSN.quadSignNeg 9 10 11 904111 1000 183 238 536870912 268435456 9007199254740992

noncomputable def hp769295 := hp769294 Bool.false 963065639754 4118 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp769296 := hp769295 Bool.true 736166191 188314 Bool.true 261582920 Bool.true 141960255 28296951008113761 1 Bool.false 251355157

noncomputable def hp769297 := hp769296 Bool.false Bool.false 518211336 Bool.true Bool.true 812927299 219361 BSN.abs_quadSignPos (BSN.cos_quad_nat3 183 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 251355157 536870912) BSN.abs_quadSignNeg

noncomputable def hp769298 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000)) (Enclosure.sfrac Bool.false 904111 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp769299 := hp769298 BSN.quadSignNeg 7 8 9 904111 1000 54 122 536870912 268435456 9007199254740992

noncomputable def hp769300 := hp769299 Bool.false 963065639754 4118 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp769301 := hp769300 Bool.true 609621138 153794 Bool.true 737352573 Bool.true 562743221 28296951008113761 1 Bool.false 105275662

noncomputable def hp769302 := hp769301 Bool.true Bool.false 267973457 Bool.true Bool.true 736166191 188314 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 54 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 105275662 536870912) BSN.abs_quadSignNeg

noncomputable def hp769303 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000)) (Enclosure.sfrac Bool.false 904111 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp769304 := hp769303 BSN.quadSignNeg 5 6 7 904111 1000 110 21 536870912 268435456 9007199254740992

noncomputable def hp769305 := hp769304 Bool.false 963065639754 4118 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp769306 := hp769305 Bool.true 309809718 114285 Bool.false 597275971 Bool.false 828968720 28296951008113761 1 Bool.false 237516552

noncomputable def hp769307 := hp769306 Bool.true Bool.false 536679246 Bool.true Bool.true 609621138 153794 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 110 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 237516552 536870912) BSN.abs_quadSignNeg

noncomputable def hp769308 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000)) (Enclosure.sfrac Bool.false 904111 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp769309 := hp769308 BSN.quadSignPos 3 4 5 904111 1000 344 215 536870912 268435456 9007199254740992

noncomputable def hp769310 := hp769309 Bool.false 963065639754 4118 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp769311 := hp769310 Bool.true 780237951 67545 Bool.false 70678108 Bool.false 546447760 28296951008113761 1 Bool.false 532225303

noncomputable def hp769312 := hp769311 Bool.false Bool.false 456863539 Bool.false Bool.true 309809718 114285 BSN.abs_quadSignPos (BSN.cos_quad_nat0 344 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 532225303 536870912) BSN.abs_quadSignPos

noncomputable def hp769313 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000)) (Enclosure.sfrac Bool.false 904111 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp769314 := hp769313 BSN.quadSignNeg 1 2 3 904111 1000 743 509 536870912 268435456 9007199254740992

noncomputable def hp769315 := hp769314 Bool.false 963065639754 4118 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp769316 := hp769315 Bool.true 536870904 4170 Bool.false 35383083 Bool.false 561978234 28296951008113761 1 Bool.false 35357473

noncomputable def hp769317 := hp769316 Bool.false Bool.false 464827969 Bool.true Bool.true 780237951 67545 BSN.abs_quadSignPos (BSN.cos_quad_nat3 743 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 35357473 536870912) BSN.abs_quadSignNeg

noncomputable def hp769318 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000)) (Enclosure.sfrac Bool.false 904111 1000) 1) Bool.true

noncomputable def hp769319 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000)) (Enclosure.sfrac Bool.false 904111 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000)))

noncomputable def hp769320 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000))) Bool.true 67108863 67108864

noncomputable def hp769321 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 120383204969) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 120383204969 67108864

noncomputable def hp769322 := nat_lit 31769413890482585869803485474587301629252737930283908189773

noncomputable def hp769323 := nat_lit 17710188698496996528822362464667519630214305649210163200

noncomputable def hp769324 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000)) Bool.false hp769322 hp769323 45613619078380342051

noncomputable def hp769325 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 904111 4000) (Real.log (Enclosure.sfrac Bool.false 3269667801284 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1808222))))))

noncomputable def hp769326 := nat_lit 289968178054932321582833056744480000

noncomputable def hp769327 := nat_lit 1572980741082208003051899899619627343680

noncomputable def hp769328 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp769325 (Enclosure.sfrac Bool.false 904111 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 904111 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp769326 hp769327)) Bool.false

noncomputable def hp769329 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 904111 1000) 904111 1000 3269667801284 16000000 1808222

noncomputable def hp769330 := hp769329 4000 2000 hp769326 hp769327 (@Eq.refl Real (Enclosure.sfrac Bool.false 904111 1000)) rfl rfl rfl rfl

noncomputable def hp769331 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp769325 (Enclosure.sfrac Bool.false 904111 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 904111 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp769326 hp769327) 6463024768301074849877 3602879701896396800

noncomputable def hp769332 := nat_lit 10166212444954427478337115351867936521360876137690850620727360

noncomputable def hp769333 := @hp769331 45613619078380342051 hp737908 hp769326 hp769327 0 1 hp769332 hp769322 hp769323 45613619078380342051 hp737908

noncomputable def hp769334 := @Enclosure.Real.IsNear.subLit_ff_p (hp769325 (Enclosure.sfrac Bool.false 904111 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 904111 2000) (Real.log Real.pi)) 41637240711916578677161 18014398509481984000 3800468079450481 1452000000000000000000

noncomputable def hp769335 := nat_lit 2168631251022741715771080048640000

noncomputable def hp769336 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 904111 4000) (Real.log (Enclosure.sfrac Bool.false 3269667801284 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1808222))))))

noncomputable def hp769337 := @hp769336 (Enclosure.sfrac Bool.false 904111 2000) 49780748637319711695273 18014398509481984000 3800468079450481 1452000000000000000000 904111 2000 0

noncomputable def hp769338 := nat_lit 83274481423833157354322000

noncomputable def hp769339 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 904111 4000) (Real.log (Enclosure.sfrac Bool.false 3269667801284 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1808222))))) 49787820384527579367273

noncomputable def hp769340 := nat_lit 112096280506628690058855712183711432704

noncomputable def hp769341 := @hp769339 18014398509481984000 11301404237806943 4356000000000000000000 883968400983459 2251799813685248 200000001089 8712000000000000000 hp769340 49780748637319711695273 18014398509481984000 3800468079450481

noncomputable def hp769342 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 904111 4000) (Real.log (Enclosure.sfrac Bool.false 3269667801284 16000000)) 904111 4000 0 1 55068260849085543 4503599627370496

noncomputable def hp769343 := nat_lit 118258189697209799345700864

noncomputable def hp769344 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3269667801284) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp769343 hp617687

noncomputable def hp769345 := BSN.log_rat_reduce_isNear 3269667801284 16000000 17 6539335602568 4194304000000 119214375 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp769346 := nat_lit 77156409178994158534466988986980912037341827737652093097484508808092951960597843464501332295469119377206853977324539778901222153849295390886009336601572802560

noncomputable def hp769347 := nat_lit 1263993926428240850835013483377837965628195404745424048593264638254184349561173681470446077758325095858038950746185966401321113987637840435873314185551020032

noncomputable def hp769348 := nat_lit 70185749733624496379223336861584540866841342235405231745651883319115288490054886503884374166847904843473395187141649287235383352858039511283788677120

noncomputable def hp769349 := BSN.log_dyadic_bound 1172515801284 5366819801284 7 6 hp769346 268435456 87120000 hp769347 hp769348 119214375 6539335602568

noncomputable def hp769350 := hp769349 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp769351 := @BSN.binarySplit_of_base6 (BSN.artanhP 1172515801284) (BSN.artanhQ 5366819801284) 0 6 hp769347 hp769346 hp769348 rfl rfl rfl

noncomputable def hp769352 := hp769345 rfl rfl rfl rfl (hp769350 (hp769351 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp769353 := @hp769342 12500018513 1089000000000000000 49787820384527579367273 18014398509481984000 11301404237806943 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 904111 4000) (BSN.isNear_log_sfrac 3269667801284 16000000 55068260849085543 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp769344 1000001481040000 87120000000000000000000 55068260849085543 4503599627370496 12500018513 1089000000000000000 (hp769352 rfl rfl rfl) rfl)) rfl

noncomputable def hp769354 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1808222)))) 1 4

noncomputable def hp769355 := @hp769354 0 1 883968400983459 562949953421312 200000001089 2178000000000000000 883968400983459 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp769356 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1808222))) 884279719003555 562949953421312 1

noncomputable def hp769357 := @hp769356 2000000000000000 18556 33554432 1 10890000 29661057600948208140288 883968400983459 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp769358 := BSN.arctan_dyadic_bound_f 1000 1808222 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp769359 := hp769358 1 18556 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1808222) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1808222) 0 0 rfl)

noncomputable def hp769360 := hp769355 (hp769357 (hp769359 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp769361 := @hp769334 34727591538471 67108864000 2712333 536870912000 hp769335 6463024768301074849877 3602879701896396800 45613619078380342051 hp737908 (@hp769337 1 hp769338 41637240711916578677161 18014398509481984000 3800468079450481 1452000000000000000000 (@hp769341 1452000000000000000000 hp769353 hp769360 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 904111 2000) rfl rfl)

noncomputable def hp769362 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 904111 2000) (Real.log Real.pi) 904111 2000 0 1 38410761 33554432

noncomputable def hp769363 := hp769361 (@hp769362 3 268435456 34727591538471 67108864000 2712333 536870912000 (Enclosure.Real.IsNear.const Bool.false 904111 2000) hd4909 rfl) rfl

noncomputable def hp769364 := @hp769324 hp737908 120383204969 67108864 515 67108864 (@hp769328 hp769322 hp769323 45613619078380342051 hp737908 (hp769330 rfl rfl rfl rfl rfl) (hp769333 (hp769363 rfl) (Enclosure.Real.IsNear.const Bool.true hp769326 hp769327) rfl rfl)) rfl

noncomputable def hp769365 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 120383204969) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1325710948198334332928) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp769366 := BSN.sin_reduce_arg_pos_rat_q2 120383204969 67108864 226375608064910080 72057594037927936 285 1325710948198334332928 hp617687 rfl rfl rfl rfl

noncomputable def hp769367 := BSN.cos_dyadic_bound_f 18839485 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp769368 := hp769367 1 67108863 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 18839485) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp769369 := hp769368 (@BSN.binarySplit_of_le (BSN.cosOddP 18839485) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp769370 := @BSN.cos_arg_round Bool.false 67108863 67108864 1325710948198334332928 hp617687 18839485 137438953472 21801270 21780000 hp769369 rfl

noncomputable def hp769371 := hp769365 67108863 67108864 285 1000000000000000 21780000 10890000 hp769366 BSN.pi_near_15 hp769370 rfl rfl

noncomputable def hp769372 := @hp769321 515 67108864 Bool.true 67108863 67108864 1 10890000 hp769364 (Enclosure.sfrac_false_div 120383204969 67108864) (hp769371 rfl rfl) rfl

noncomputable def hp769373 := @hp769318 67108863 67108864 354716179 45675970560000 536870904 536870912 4170 536870912 (@hp769319 Bool.true 67108863 67108864 354716179 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000)) (Enclosure.sfrac Bool.false 904111 1000)) (@hp769320 5675458864 730815528960000 67108863 67108864 354716179 45675970560000 (hp769372 rfl) rfl))

noncomputable def hp769374 := @hp769324 hp737908 963065639754 536870912 4118 536870912 (@hp769328 hp769322 hp769323 45613619078380342051 hp737908 (hp769330 rfl rfl rfl rfl rfl) (hp769333 (hp769363 rfl) (Enclosure.Real.IsNear.const Bool.true hp769326 hp769327) rfl rfl)) rfl

noncomputable def hp769375 := hp769317 (BSN.cos_quad_nat1 509 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 464827969 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 904111 1000)) rfl rfl (hp769373 rfl) hp769374

noncomputable def hp769376 := nat_lit 1567410258114122106193331142321

noncomputable def hp769377 := BSN.sin_dyadic_bound_f 35383083 536870912 2 1 536870912 268435456 hp769376 hp708890 hp769376 hp769376 hp708891

noncomputable def hp769378 := @BSN.binarySplit_of_base (BSN.sinEvenP 35383083) (BSN.sinEvenQ 536870912) 0 1 hp769376 hp708890 hp769376 rfl rfl rfl

noncomputable def hp769379 := hp769377 hp769376 35357473 rfl rfl rfl rfl rfl rfl rfl rfl (hp769378 rfl)

noncomputable def hp769380 := @BSN.binarySplit_of_base (BSN.sinOddP 35383083) (BSN.sinOddQ 536870912) 0 1 hp769376 hp708891 hp769376 rfl rfl rfl

noncomputable def hp769381 := nat_lit 25067536490710796984646554554887455378061725957093158208744848262923526400

noncomputable def hp769382 := nat_lit 9948462374231404241159218743914494178070044556238658148813829220311296

noncomputable def hp769383 := nat_lit 65636964727065236495779099384834140618635264101200551766852713536538255616

noncomputable def hp769384 := BSN.sin_dyadic_bound_f 561978234 536870912 3 2 536870912 268435456 hp769381 hp708845 hp769382 hp769383 hp708848

noncomputable def hp769385 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 561978234) (BSN.sinEvenQ 536870912) 0 2 hp769381 hp708845 hp769382 rfl rfl rfl

noncomputable def hp769386 := hp769384 hp769382 464827969 rfl rfl rfl rfl rfl rfl rfl rfl (hp769385 rfl)

noncomputable def hp769387 := @BSN.binarySplit_of_base2 (BSN.sinOddP 561978234) (BSN.sinOddQ 536870912) 0 2 hp769383 hp708848 hp769382 rfl rfl rfl

noncomputable def hp769388 := hp769375 hd4911 hd4913 hd4915 hd4917 hd4918 (hp769379 (hp769380 rfl) rfl rfl rfl rfl) (hp769386 (hp769387 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769389 := hp769312 (BSN.cos_quad_nat3 215 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 456863539 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 904111 1000)) rfl rfl (hp769388 rfl rfl rfl rfl rfl) hp769374

noncomputable def hp769390 := nat_lit 24953970711077908948804890992896

noncomputable def hp769391 := BSN.cos_dyadic_bound_f 70678108 536870912 2 1 536870912 268435456 hp769390 hp708767 hp769390 hp769390 hp708768

noncomputable def hp769392 := @BSN.binarySplit_of_base (BSN.cosEvenP 70678108) (BSN.cosEvenQ 536870912) 0 1 hp769390 hp708767 hp769390 rfl rfl rfl

noncomputable def hp769393 := hp769391 hp769390 532225303 rfl rfl rfl rfl rfl rfl rfl rfl (hp769392 rfl)

noncomputable def hp769394 := @BSN.binarySplit_of_base (BSN.cosOddP 70678108) (BSN.cosOddQ 536870912) 0 1 hp769390 hp708768 hp769390 rfl rfl rfl

noncomputable def hp769395 := nat_lit 22408356102908007190393451366199692634119771797598984637583756770672640000

noncomputable def hp769396 := nat_lit 7950404044275258501001481695225438855495840210440828577487257600000000

noncomputable def hp769397 := nat_lit 58675679615354049365838370226825972855023837633370912709308193125171200000

noncomputable def hp769398 := BSN.sin_dyadic_bound_f 546447760 536870912 3 2 536870912 268435456 hp769395 hp708845 hp769396 hp769397 hp708848

noncomputable def hp769399 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 546447760) (BSN.sinEvenQ 536870912) 0 2 hp769395 hp708845 hp769396 rfl rfl rfl

noncomputable def hp769400 := hp769398 hp769396 456863539 rfl rfl rfl rfl rfl rfl rfl rfl (hp769399 rfl)

noncomputable def hp769401 := @BSN.binarySplit_of_base2 (BSN.sinOddP 546447760) (BSN.sinOddQ 536870912) 0 2 hp769397 hp708848 hp769396 rfl rfl rfl

noncomputable def hp769402 := hp769389 hd4920 hd4922 hd4924 hd4926 hd4918 (hp769393 (hp769394 rfl) rfl rfl rfl rfl) (hp769400 (hp769401 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769403 := hp769307 (BSN.cos_quad_nat1 21 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536679246 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 904111 1000)) rfl rfl (hp769402 rfl rfl rfl rfl rfl) hp769374

noncomputable def hp769404 := nat_lit 17546106435787748761877355260684778497885327229449956703214513372956951675139724653613738592744260526020360519921

noncomputable def hp769405 := nat_lit 2061106894580846515518296578172545342057308818332566895363875454787670019174956354181728031502581359821041

noncomputable def hp769406 := nat_lit 106381720591585546253591152829185178662430708551018667901989492051359298821196776981572005998700757258430796120305

noncomputable def hp769407 := BSN.cos_dyadic_bound_f 597275971 536870912 4 3 536870912 268435456 hp769404 hp716712 hp769405 hp769406 hp716714

noncomputable def hp769408 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 597275971) (BSN.cosEvenQ 536870912) 0 3 hp769404 hp716712 hp769405 rfl rfl rfl

noncomputable def hp769409 := hp769407 hp769405 237516552 rfl rfl rfl rfl rfl rfl rfl rfl (hp769408 rfl)

noncomputable def hp769410 := @BSN.binarySplit_of_base3 (BSN.cosOddP 597275971) (BSN.cosOddQ 536870912) 0 3 hp769406 hp716714 hp769405 rfl rfl rfl

noncomputable def hp769411 := nat_lit 169444115020698739487419262113375410113989435475547121462474796129430008433166689489281851214402410122733158400000

noncomputable def hp769412 := nat_lit 105307116272067164892993899530176179933406985128112949926904026499049497650686737893392243490816000000000000

noncomputable def hp769413 := nat_lit 846237528083244545531276004903940581533008084424403815619793873674700104677471124160533738308121830770081792000000

noncomputable def hp769414 := BSN.sin_dyadic_bound_f 828968720 536870912 4 3 536870912 268435456 hp769411 hp642702 hp769412 hp769413 hp642705

noncomputable def hp769415 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 828968720) (BSN.sinEvenQ 536870912) 0 3 hp769411 hp642702 hp769412 rfl rfl rfl

noncomputable def hp769416 := hp769414 hp769412 536679246 rfl rfl rfl rfl rfl rfl rfl rfl (hp769415 rfl)

noncomputable def hp769417 := @BSN.binarySplit_of_base3 (BSN.sinOddP 828968720) (BSN.sinOddQ 536870912) 0 3 hp769413 hp642705 hp769412 rfl rfl rfl

noncomputable def hp769418 := hp769403 hd4928 hd4930 hd4932 hd4934 hd4918 (hp769409 (hp769410 rfl) rfl rfl rfl rfl) (hp769416 (hp769417 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769419 := hp769302 (BSN.cos_quad_nat2 122 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267973457 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 904111 1000)) rfl rfl (hp769418 rfl rfl rfl rfl rfl) hp769374

noncomputable def hp769420 := nat_lit 40804177218532301820535677605132102510943649586725417381227823349861830577789084573863829926686370820031963926001

noncomputable def hp769421 := nat_lit 25828691244068699510939474569294019218951611723703887559860765622809603263866380624014069058362612593921521

noncomputable def hp769422 := nat_lit 247196427040825208836189297769925532028659148174172205780679753236446593888843015051972500250244946874637163630065

noncomputable def hp769423 := BSN.cos_dyadic_bound_f 737352573 536870912 4 3 536870912 268435456 hp769420 hp716712 hp769421 hp769422 hp716714

noncomputable def hp769424 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 737352573) (BSN.cosEvenQ 536870912) 0 3 hp769420 hp716712 hp769421 rfl rfl rfl

noncomputable def hp769425 := hp769423 hp769421 105275662 rfl rfl rfl rfl rfl rfl rfl rfl (hp769424 rfl)

noncomputable def hp769426 := @BSN.binarySplit_of_base3 (BSN.cosOddP 737352573) (BSN.cosOddQ 536870912) 0 3 hp769422 hp716714 hp769421 rfl rfl rfl

noncomputable def hp769427 := nat_lit 13824129170814701356208830372005025574576564943173180381881131832046729785322081399095864749338684087690114731921

noncomputable def hp769428 := nat_lit 1008609987899736664168636900176984145744982230338580953433248867334833457652571776825029946655368978993041

noncomputable def hp769429 := nat_lit 83826233015177093714001672516156024605282015445457773177703737346419739695660022636930794068057934503877152444305

noncomputable def hp769430 := BSN.cos_dyadic_bound_f 562743221 536870912 4 3 536870912 268435456 hp769427 hp716712 hp769428 hp769429 hp716714

noncomputable def hp769431 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 562743221) (BSN.cosEvenQ 536870912) 0 3 hp769427 hp716712 hp769428 rfl rfl rfl

noncomputable def hp769432 := hp769430 hp769428 267973457 rfl rfl rfl rfl rfl rfl rfl rfl (hp769431 rfl)

noncomputable def hp769433 := @BSN.binarySplit_of_base3 (BSN.cosOddP 562743221) (BSN.cosOddQ 536870912) 0 3 hp769429 hp716714 hp769428 rfl rfl rfl

noncomputable def hp769434 := hp769419 hd4936 hd4938 hd4940 hd4942 hd4918 (hp769425 (hp769426 rfl) rfl rfl rfl rfl) (hp769432 (hp769433 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769435 := hp769297 (BSN.cos_quad_nat2 238 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 518211336 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 904111 1000)) rfl rfl (hp769434 rfl rfl rfl rfl rfl) hp769374

noncomputable def hp769436 := nat_lit 1176269703746212794328564801629747401301608675817262325048972872253440000

noncomputable def hp769437 := nat_lit 21921742259449466579524668381999305931389093666577095596441600000000

noncomputable def hp769438 := nat_lit 3080670874609756305057493345281481861675562378131655440783010902835200000

noncomputable def hp769439 := BSN.sin_dyadic_bound_f 261582920 536870912 3 2 536870912 268435456 hp769436 hp708845 hp769437 hp769438 hp708848

noncomputable def hp769440 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 261582920) (BSN.sinEvenQ 536870912) 0 2 hp769436 hp708845 hp769437 rfl rfl rfl

noncomputable def hp769441 := hp769439 hp769437 251355157 rfl rfl rfl rfl rfl rfl rfl rfl (hp769440 rfl)

noncomputable def hp769442 := @BSN.binarySplit_of_base2 (BSN.sinOddP 261582920) (BSN.sinOddQ 536870912) 0 2 hp769438 hp708848 hp769437 rfl rfl rfl

noncomputable def hp769443 := nat_lit 406131881552294689255812208250625

noncomputable def hp769444 := BSN.cos_dyadic_bound_f 141960255 536870912 2 1 536870912 268435456 hp769443 hp708767 hp769443 hp769443 hp708768

noncomputable def hp769445 := @BSN.binarySplit_of_base (BSN.cosEvenP 141960255) (BSN.cosEvenQ 536870912) 0 1 hp769443 hp708767 hp769443 rfl rfl rfl

noncomputable def hp769446 := hp769444 hp769443 518211336 rfl rfl rfl rfl rfl rfl rfl rfl (hp769445 rfl)

noncomputable def hp769447 := @BSN.binarySplit_of_base (BSN.cosOddP 141960255) (BSN.cosOddQ 536870912) 0 1 hp769443 hp708768 hp769443 rfl rfl rfl

noncomputable def hp769448 := hp769435 hd4944 hd4946 hd4961 hd4963 hd4918 (hp769441 (hp769442 rfl) rfl rfl rfl rfl) (hp769446 (hp769447 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769449 := @hp769292 219361 268435456 (hp769448 rfl rfl rfl rfl rfl) (hp769448 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp769450 := @hp769290 Bool.true 812927299 268435456 219361 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 904111 1000)) (Enclosure.sfrac Bool.false 904111 1000) 11) hp769449

noncomputable def hp769451 := @Enclosure.Real.IsNear.mulLit_tf hp769281 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1))) 4844059 16777216 1

noncomputable def hp769452 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp769280 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp769453 := @hp769452 1 1 0 1 4844059 16777216 1 33554432 4844059 16777216 1

noncomputable def hp769454 := @Enclosure.Real.IsNear.of_eq (hp769280 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp769455 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 904111 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp769456 := @hp769454 (@Inv.inv Real Real.instInv (Real.sqrt hp769282)) Bool.false 4844059 16777216 1 33554432 (hp769455 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 904111 1000) 904111 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 904111 1000))))

noncomputable def hp769457 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp769282)) Bool.false 19376236 67108864 2 67108864 4844059 16777216

noncomputable def hp769458 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp769282) Bool.false 232429022 67108864 6 67108864 116214511 33554432 3 33554432

noncomputable def hp769459 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 904111 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp769460 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 904111 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp769461 := @hp769460 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 904111 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9656544686477

noncomputable def hp769462 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 904111 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 904111 1000 0

noncomputable def hp769463 := @hp769462 1 10680707 67108864 1 67108864 9656544686477 67108864000 904111 67108864000 (Enclosure.Real.IsNear.const Bool.false 904111 1000) hd4949

noncomputable def hp769464 := @hp769461 67108864000 904111 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 904111 1000) 904111 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 904111 1000))) (hp769463 rfl)

noncomputable def hp769465 := @hp769459 9656544686477 67108864000 904111 67108864000 402504560 402504598 33554432 hp769464 rfl rfl rfl

noncomputable def hp769466 := @Enclosure.Real.IsNear.recentre' hp769282 Bool.false 805009158 67108864 38 67108864 402504579 33554432 19 33554432 (hp769465 rfl rfl rfl)

noncomputable def hp769467 := @Enclosure.Real.IsNear.sqrt_image hp769282 402504579 33554432 19 33554432 116214508 116214514 33554432 (hp769466 rfl) rfl rfl

noncomputable def hp769468 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp769282) 116214511 33554432 3 33554432 9688117 9688119 33554432 (hp769458 (hp769467 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp769469 := @hp769453 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp769456 (@hp769457 1 33554432 (hp769468 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp769470 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp769471 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp769472 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1))) (hp769470 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp769471 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp769473 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 904111 1000) 904111 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 904111 1000)) rfl

noncomputable def hp769474 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp769475 := @hp769474 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp769471 (Enclosure.sfrac Bool.false 1 16)))) 67134855

noncomputable def hp769476 := @hp769475 67108864 247 67108864 30632669 33554432 490841179 45675970560000 2056519791577995 2251799813685248 1351633019531219 95789453011845120000

noncomputable def hp769477 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp769478 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1)))) 67082883

noncomputable def hp769479 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp769480 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 209895001) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp769481 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1))) Bool.false 29540095312641370714985

noncomputable def hp769482 := nat_lit 512735433058790732569877957

noncomputable def hp769483 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp769484 := @Enclosure.Real.IsNear.subLit_ff_p hp769282 (Enclosure.sfrac Bool.false 11 1) 402504579 33554432 19 33554432 11 1 0

noncomputable def hp769485 := @hp769483 500000000000000 33405827 33554432 19 33554432 29540095312641370714985 4722366482869645213696 hp769482 hp682805 hd4948 (@hp769484 1 33405827 33405827 33554432 19 33554432 (hp769466 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp769486 := @hp769480 209895001 33554432 15 4194304 Bool.false 67082883 67108864 1 10890000 (@hp769481 4722366482869645213696 hp769482 hp682805 209895001 33554432 15 4194304 (hp769485 rfl) rfl) (Enclosure.sfrac_false_div 209895001 33554432)

noncomputable def hp769487 := nat_lit 7461342703478925732872192

noncomputable def hp769488 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 209895001) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp769487) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp769489 := BSN.sin_reduce_arg_pos_rat_q3 209895001 33554432 226375608064910080 72057594037927936 0 hp769487 hp619237 rfl rfl rfl rfl

noncomputable def hp769490 := nat_lit 13386284139068088076656799760754164241938431996112709121113677480297859746941153940846563956752879325009794031127597030170812683790918745788416

noncomputable def hp769491 := nat_lit 8271917519278445130877839233405718773824498371858601846187742177183757674256474107642011718874583513999163169763970609671712074497724416

noncomputable def hp769492 := nat_lit 66853980589660606791811519551545671206398463988311979469802269018530927271211832229726082988034499247222372621087715246154843332588727943499776

noncomputable def hp769493 := BSN.sin_dyadic_bound_f 212064114278 137438953472 4 3 67108864 21801270 hp769490 hp737934 hp769491 hp769492 hp737937

noncomputable def hp769494 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 212064114278) (BSN.sinEvenQ 137438953472) 0 3 hp769490 hp737934 hp769491 rfl rfl rfl

noncomputable def hp769495 := hp769493 hp769491 67082883 rfl rfl rfl rfl rfl rfl rfl rfl (hp769494 rfl)

noncomputable def hp769496 := @BSN.binarySplit_of_base3 (BSN.sinOddP 212064114278) (BSN.sinOddQ 137438953472) 0 3 hp769492 hp737937 hp769491 rfl rfl rfl

noncomputable def hp769497 := @BSN.sin_arg_round Bool.false 67082883 67108864 hp769487 hp619237 212064114278 137438953472 21801270 21780000 (hp769495 (hp769496 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769498 := hp769488 67082883 67108864 0 1000000000000000 21780000 10890000 hp769489 BSN.pi_near_15 hp769497 rfl rfl

noncomputable def hp769499 := @hp769478 67108864 10471519 2854748160000 33567304 33567551 33554432 (@hp769479 67082883 67108864 167544304 45675970560000 67082883 67108864 10471519 2854748160000 (hp769486 (hp769498 rfl rfl) rfl rfl) rfl)

noncomputable def hp769500 := @hp769477 Bool.false 67134855 67108864 247 67108864 67134855 67108864 247 67108864 (hp769499 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp769501 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp769471 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp769502 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp769471 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3526593)) (@Nat.cast Real Real.instNatCast 8388608)) Bool.true

noncomputable def hp769503 := nat_lit 66615459191992839777067941445

noncomputable def hp769504 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp769471 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp769503

noncomputable def hp769505 := nat_lit 51461258283445725389285384357280573

noncomputable def hp769506 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp769471 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp769507 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp769508 := @hp769507 (Enclosure.sfrac Bool.false 1 16) 4964272921335 1125899906842624 1906955995 1125899906842624 1 16 0

noncomputable def hp769509 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1)) 1115949277553929

noncomputable def hp769510 := @hp769509 1125899906842624 1269421787 1125899906842624 33405827 33554432 19 33554432 166573358168376606720 4964272921335 1125899906842624 1906955995

noncomputable def hp769511 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1)) 33405827 33554432 19

noncomputable def hp769512 := @hp769511 33554432 33405827 33554432 19 33554432 1115949277553929 1125899906842624 1269421787 1125899906842624 (@hp769484 1 33405827 33405827 33554432 19 33554432 (hp769466 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp769513 := hp769512 (@hp769484 1 33405827 33405827 33554432 19 33554432 (hp769466 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp769514 := @hp769510 1125899906842624 (hp769513 rfl) (@hp769484 1 33405827 33405827 33554432 19 33554432 (hp769466 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp769515 := @hp769506 500000000000000 75333017098999 1125899906842624 1906955995 1125899906842624 hp769503 hp682141 hp769505 hp682143 hd4948 (@hp769508 1 1205328273583984 75333017098999 1125899906842624 1906955995 1125899906842624 (hp769514 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp769516 := @hp769502 3526593 8388608 715 67108864 Bool.false 30632669 33554432 1 10890000 (@hp769504 hp682141 hp769505 hp682143 3526593 8388608 715 67108864 (hp769515 rfl) rfl) (Enclosure.sfrac_true_div 3526593 8388608)

noncomputable def hp769517 := nat_lit 1286762281848578519119273646929281645657010584211248135681

noncomputable def hp769518 := nat_lit 23924492227872703202382481833872975933842941860134401

noncomputable def hp769519 := nat_lit 3860238996561279811951416175824177191019164066750024138241

noncomputable def hp769520 := BSN.cos_dyadic_bound_f 3526593 8388608 3 2 33554432 10890000 hp769517 hp630724 hp769518 hp769519 hp630727

noncomputable def hp769521 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 3526593) (BSN.cosEvenQ 8388608) 0 2 hp769517 hp630724 hp769518 rfl rfl rfl

noncomputable def hp769522 := hp769520 hp769518 30632669 rfl rfl rfl rfl rfl rfl rfl rfl (hp769521 rfl)

noncomputable def hp769523 := @BSN.binarySplit_of_base2 (BSN.cosOddP 3526593) (BSN.cosOddQ 8388608) 0 2 hp769519 hp630727 hp769518 rfl rfl rfl

noncomputable def hp769524 := hp769516 (BSN.cos_neg_of_bound 3526593 8388608 Bool.false 30632669 33554432 1 10890000 (hp769522 (hp769523 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp769525 := hp769476 hp769500 (@hp769501 30632669 33554432 7853458864 730815528960000 30632669 33554432 490841179 45675970560000 (hp769524 rfl) rfl)

noncomputable def hp769526 := @hp769451 33554432 2056519791577995 2251799813685248 1351633019531219 95789453011845120000 9961903205071510881705 37778931862957161709568 70305407794635718346617 hp741590 (hp769469 rfl) (@hp769472 Bool.false 2056519791577995 2251799813685248 1351633019531219 95789453011845120000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769282 (Enclosure.sfrac Bool.false 11 1)) (hp769473 rfl (hp769285 rfl rfl))) (hp769525 rfl))

noncomputable def hp769527 := @hp769279 hp769277 hp741590 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 904111 1000))) (@hp769284 hp769277 hp741590 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 904111 1000) 11 (hp769285 rfl rfl)) (@hp769288 hp769277 hp741590 hp769450 (hp769526 rfl) rfl rfl))

theorem hd5086 : hp769278 hp741590 := hp769527

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

noncomputable def hp769544 := nat_lit 2810888003980790159521049

noncomputable def hp769545 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 905375 1000)) Bool.false 9620814688232979079561 4722366482869645213696 hp769544

noncomputable def hp769546 := nat_lit 3214160687403152273571840000

noncomputable def hp769547 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 905375 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 905375 1000)) Bool.false 9620814688232979079561 4722366482869645213696

noncomputable def hp769548 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 905375 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp769549 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 12) (hp769548 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp769550 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 905375 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp769551 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 905375 1000)) (Enclosure.sfrac Bool.false 905375 1000) 12) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp769549 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1))))

noncomputable def hp769552 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 905375 1000)) hp769551 Bool.false 9620814688232979079561 4722366482869645213696

noncomputable def hp769553 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 905375 1000) 905375 1000 12 (@Eq.refl Real (Enclosure.sfrac Bool.false 905375 1000)) rfl

noncomputable def hp769554 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 905375 1000)) (Enclosure.sfrac Bool.false 905375 1000) 12) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp769549 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1))))

noncomputable def hp769555 := nat_lit 2582567777927317573460417314816

noncomputable def hp769556 := @hp769554 617726641 268435456 117101 134217728 1246347304831193407095 4722366482869645213696 6627819695771310241049 hp769546 hp769555 9620814688232979079561 4722366482869645213696

noncomputable def hp769557 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 905375 1000)) (Enclosure.sfrac Bool.false 905375 1000) 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 905375 1000)) (Enclosure.sfrac Bool.false 905375 1000) 12)

noncomputable def hp769558 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 905375 1000)) (Enclosure.sfrac Bool.false 905375 1000) 12) hp769557

noncomputable def hp769559 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 905375 1000)) (Enclosure.sfrac Bool.false 905375 1000) 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 905375 1000)) (Enclosure.sfrac Bool.false 905375 1000) 12)

noncomputable def hp769560 := @hp769559 617726641 536870912 234202 536870912 617726641 536870912 234202 536870912 663278930240733184 617726641 268435456

noncomputable def hp769561 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 905375 1000)) (Enclosure.sfrac Bool.false 905375 1000) Real.cos BSN.quadSignPos 11

noncomputable def hp769562 := hp769561 12 905375 1000 288 536870912 268435456 9007199254740992 Bool.false 964751895769 4124 1334074092

noncomputable def hp769563 := hp769562 51 154981288 8 Bool.false 474534636 219672 Bool.true 210756594 28296951008113761 1 Bool.false

noncomputable def hp769564 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 905375 1000)) (Enclosure.sfrac Bool.false 905375 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp769565 := hp769564 BSN.quadSignNeg 9 10 11 905375 1000 183 238 536870912 268435456 9007199254740992

noncomputable def hp769566 := hp769565 Bool.false 964751895769 4124 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp769567 := hp769566 Bool.false 591358656 188582 Bool.true 137872274 Bool.true 82927558 28296951008113761 1 Bool.false 136361819

noncomputable def hp769568 := hp769567 Bool.false Bool.false 530478949 Bool.true Bool.false 474534636 219672 BSN.abs_quadSignPos (BSN.cos_quad_nat3 183 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 136361819 536870912) BSN.abs_quadSignNeg

noncomputable def hp769569 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 905375 1000)) (Enclosure.sfrac Bool.false 905375 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp769570 := hp769569 BSN.quadSignNeg 7 8 9 905375 1000 54 122 536870912 268435456 9007199254740992

noncomputable def hp769571 := hp769570 Bool.false 964751895769 4124 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp769572 := hp769571 Bool.false 853698187 154013 Bool.true 462215636 Bool.true 367534404 28296951008113761 1 Bool.false 349890580

noncomputable def hp769573 := hp769572 Bool.true Bool.false 415903585 Bool.true Bool.false 591358656 188582 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 54 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 349890580 536870912) BSN.abs_quadSignNeg

noncomputable def hp769574 := hp769564 BSN.quadSignNeg 5 6 7 905375 1000 111 22 536870912 268435456 9007199254740992

noncomputable def hp769575 := hp769574 Bool.false 964751895769 4124 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp769576 := hp769575 Bool.false 925741315 114448 Bool.false 224320504 Bool.false 351405867 28296951008113761 1 Bool.false 217850208

noncomputable def hp769577 := hp769576 Bool.false Bool.false 425913308 Bool.true Bool.false 853698187 154013 BSN.abs_quadSignPos (BSN.cos_quad_nat3 111 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 217850208 536870912) BSN.abs_quadSignNeg

noncomputable def hp769578 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 905375 1000)) (Enclosure.sfrac Bool.false 905375 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp769579 := hp769578 BSN.quadSignPos 3 4 5 905375 1000 344 216 536870912 268435456 9007199254740992

noncomputable def hp769580 := hp769579 Bool.false 964751895769 4124 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp769581 := hp769580 Bool.false 707950245 67642 Bool.false 816188087 Bool.false 297216593 28296951008113761 1 Bool.false 27115228

noncomputable def hp769582 := hp769581 Bool.false Bool.false 456679884 Bool.false Bool.false 925741315 114448 BSN.abs_quadSignPos (BSN.cos_quad_nat0 344 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 27115228 536870912) BSN.abs_quadSignPos

noncomputable def hp769583 := hp769578 BSN.quadSignNeg 1 2 3 905375 1000 744 510 536870912 268435456 9007199254740992

noncomputable def hp769584 := hp769583 Bool.false 964751895769 4124 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp769585 := hp769584 Bool.false 536870824 4178 Bool.false 407951234 Bool.false 659395791 28296951008113761 1 Bool.false 389192045

noncomputable def hp769586 := hp769585 Bool.false Bool.false 180342711 Bool.true Bool.false 707950245 67642 BSN.abs_quadSignPos (BSN.cos_quad_nat0 744 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 389192045 536870912) BSN.abs_quadSignNeg

noncomputable def hp769587 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 905375 1000)) (Enclosure.sfrac Bool.false 905375 1000) 1) Bool.false

noncomputable def hp769588 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 905375 1000)) (Enclosure.sfrac Bool.false 905375 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 905375 1000)))

noncomputable def hp769589 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 905375 1000))) Bool.false 67108853 67108864

noncomputable def hp769590 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 905375 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 120593986971) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 120593986971 67108864

noncomputable def hp769591 := nat_lit 1682594021931032089646275012853864923121543873

noncomputable def hp769592 := nat_lit 936339996885244926900602837494042460160000

noncomputable def hp769593 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 905375 1000)) Bool.false hp769591 hp769592 219250553765832713

noncomputable def hp769594 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 905375 4000) (Real.log (Enclosure.sfrac Bool.false 3278816562500 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1810750))))))

noncomputable def hp769595 := nat_lit 292000815246682369364257812500000000

noncomputable def hp769596 := nat_lit 1586221654387582819881134033203125000000

noncomputable def hp769597 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 905375 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp769594 (Enclosure.sfrac Bool.false 905375 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 905375 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp769595 hp769596)) Bool.false

noncomputable def hp769598 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 905375 1000) 905375 1000 3278816562500 16000000 1810750

noncomputable def hp769599 := hp769598 4000 2000 hp769595 hp769596 (@Eq.refl Real (Enclosure.sfrac Bool.false 905375 1000)) rfl rfl rfl rfl

noncomputable def hp769600 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp769594 (Enclosure.sfrac Bool.false 905375 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 905375 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp769595 hp769596) 258973641597307657581 144115188075855872

noncomputable def hp769601 := nat_lit 410789556135505881261297610560025615996470672119140625000000

noncomputable def hp769602 := @hp769600 219250553765832713 28547481600000000000000 hp769595 hp769596 0 1 hp769601 hp769591 hp769592 219250553765832713 28547481600000000000000

noncomputable def hp769603 := @Enclosure.Real.IsNear.subLit_ff_p (hp769594 (Enclosure.sfrac Bool.false 905375 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 905375 2000) (Real.log Real.pi)) 333654839472776879469 144115188075855872 18267526818803 6969600000000000000

noncomputable def hp769604 := nat_lit 139035415148307698870095183872

noncomputable def hp769605 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 905375 4000) (Real.log (Enclosure.sfrac Bool.false 3278816562500 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1810750))))))

noncomputable def hp769606 := @hp769605 (Enclosure.sfrac Bool.false 905375 2000) 398893983674865884525 144115188075855872 18267526818803 6969600000000000000 905375 2000 0

noncomputable def hp769607 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 905375 4000) (Real.log (Enclosure.sfrac Bool.false 3278816562500 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1810750))))) 398950557680446113325

noncomputable def hp769608 := nat_lit 898229398119229356098709091463987200

noncomputable def hp769609 := @hp769607 144115188075855872 90537634089659 34848000000000000000 883968837191075 2251799813685248 200000001089 8712000000000000000 hp769608 398893983674865884525 144115188075855872 18267526818803

noncomputable def hp769610 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 905375 4000) (Real.log (Enclosure.sfrac Bool.false 3278816562500 16000000)) 905375 4000 0 1 55080844633500775 4503599627370496

noncomputable def hp769611 := nat_lit 118285213168471467307827200

noncomputable def hp769612 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3278816562500) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp769611 hp617687

noncomputable def hp769613 := BSN.log_rat_reduce_isNear 3278816562500 16000000 17 6557633125000 4194304000000 119964427 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp769614 := nat_lit 78749624329792733387809099846660359344765838137031766380993689140760595841295447153343611657279444440149518413818441331386566162109375000000000000000000000000

noncomputable def hp769615 := nat_lit 1306325121322173977111427878228928827849527178128882730485395100108057026597743281866462040740329200616542948409914970397949218750000000000000000000000000000

noncomputable def hp769616 := nat_lit 77046875469535383645796965391818818594605867677901402833692370457616142756774691876055163657355251416447572410106658935546875000000000000000000000000

noncomputable def hp769617 := BSN.log_dyadic_bound 1181664562500 5375968562500 7 6 hp769614 268435456 87120000 hp769615 hp769616 119964427 6557633125000

noncomputable def hp769618 := hp769617 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp769619 := @BSN.binarySplit_of_base6 (BSN.artanhP 1181664562500) (BSN.artanhQ 5375968562500) 0 6 hp769615 hp769614 hp769616 rfl rfl rfl

noncomputable def hp769620 := hp769613 rfl rfl rfl rfl (hp769618 (hp769619 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp769621 := @hp769610 12500018513 1089000000000000000 398950557680446113325 144115188075855872 90537634089659 34848000000000000000 (Enclosure.Real.IsNear.const Bool.false 905375 4000) (BSN.isNear_log_sfrac 3278816562500 16000000 55080844633500775 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp769612 1000001481040000 87120000000000000000000 55080844633500775 4503599627370496 12500018513 1089000000000000000 (hp769620 rfl rfl rfl) rfl)) rfl

noncomputable def hp769622 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1810750)))) 1 4

noncomputable def hp769623 := @hp769622 0 1 883968837191075 562949953421312 200000001089 2178000000000000000 883968837191075 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp769624 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1810750))) 884279719003555 562949953421312 1

noncomputable def hp769625 := @hp769624 2000000000000000 18530 33554432 1 10890000 29661072237646997094400 883968837191075 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp769626 := BSN.arctan_dyadic_bound_f 1000 1810750 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp769627 := hp769626 1 18530 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1810750) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1810750) 0 0 rfl)

noncomputable def hp769628 := hp769623 (hp769625 (hp769627 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp769629 := @hp769603 278209141923 536870912 21729 4294967296 hp769604 258973641597307657581 144115188075855872 219250553765832713 28547481600000000000000 (@hp769606 1 667309678945553758938000 333654839472776879469 144115188075855872 18267526818803 6969600000000000000 (@hp769609 6969600000000000000 hp769621 hp769628 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 905375 2000) rfl rfl)

noncomputable def hp769630 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 905375 2000) (Real.log Real.pi) 905375 2000 0 1 38410761 33554432

noncomputable def hp769631 := hp769629 (@hp769630 3 268435456 278209141923 536870912 21729 4294967296 (Enclosure.Real.IsNear.const Bool.false 905375 2000) hd4909 rfl) rfl

noncomputable def hp769632 := @hp769593 28547481600000000000000 120593986971 67108864 129 16777216 (@hp769597 hp769591 hp769592 219250553765832713 28547481600000000000000 (hp769599 rfl rfl rfl rfl rfl) (hp769602 (hp769631 rfl) (Enclosure.Real.IsNear.const Bool.true hp769595 hp769596) rfl rfl)) rfl

noncomputable def hp769633 := nat_lit 15186403677638273166999552

noncomputable def hp769634 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 120593986971) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp769633) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp769635 := BSN.sin_reduce_arg_pos_rat_q3 120593986971 67108864 226375608064910080 72057594037927936 285 hp769633 hp617687 rfl rfl rfl rfl

noncomputable def hp769636 := nat_lit 14359882160089338943853880560714524767356887845511253428053097562435048578348472320189854994289544239669225004980002333914445987940768427745681

noncomputable def hp769637 := nat_lit 10207083610864242287538850786555525636215199393760871925666995541677093505161492108497361154527794460719810281061842335464137153798676881

noncomputable def hp769638 := nat_lit 71710317908364536986351354658800882755613433941320692380638426269762713366875142996241019130455626105993808342180302980741618241870183710269841

noncomputable def hp769639 := BSN.sin_dyadic_bound_f 215811776309 137438953472 4 3 67108864 21801270 hp769636 hp737934 hp769637 hp769638 hp737937

noncomputable def hp769640 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215811776309) (BSN.sinEvenQ 137438953472) 0 3 hp769636 hp737934 hp769637 rfl rfl rfl

noncomputable def hp769641 := hp769639 hp769637 67108853 rfl rfl rfl rfl rfl rfl rfl rfl (hp769640 rfl)

noncomputable def hp769642 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215811776309) (BSN.sinOddQ 137438953472) 0 3 hp769638 hp737937 hp769637 rfl rfl rfl

noncomputable def hp769643 := @BSN.sin_arg_round Bool.false 67108853 67108864 hp769633 hp617687 215811776309 137438953472 21801270 21780000 (hp769641 (hp769642 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769644 := hp769634 67108853 67108864 285 1000000000000000 21780000 10890000 hp769635 BSN.pi_near_15 hp769643 rfl rfl

noncomputable def hp769645 := @hp769590 129 16777216 Bool.false 67108853 67108864 1 10890000 hp769632 (Enclosure.sfrac_false_div 120593986971 67108864) (hp769644 rfl rfl) rfl

noncomputable def hp769646 := @hp769587 67108853 67108864 88849201 11418992640000 536870824 536870912 4178 536870912 (@hp769588 Bool.false 67108853 67108864 88849201 11418992640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 905375 1000)) (Enclosure.sfrac Bool.false 905375 1000)) (@hp769589 1421587216 182703882240000 67108853 67108864 88849201 11418992640000 (hp769645 rfl) rfl))

noncomputable def hp769647 := @hp769593 28547481600000000000000 964751895769 536870912 4124 536870912 (@hp769597 hp769591 hp769592 219250553765832713 28547481600000000000000 (hp769599 rfl rfl rfl rfl rfl) (hp769602 (hp769631 rfl) (Enclosure.Real.IsNear.const Bool.true hp769595 hp769596) rfl rfl)) rfl

noncomputable def hp769648 := hp769586 (BSN.cos_quad_nat2 510 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 180342711 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 905375 1000)) rfl rfl (hp769646 rfl) hp769647

noncomputable def hp769649 := nat_lit 3866410478965064621602480325370665197445580989239560148398740047388344576

noncomputable def hp769650 := nat_lit 767124775542166176093468707495866171201817048290503622763855438807296

noncomputable def hp769651 := nat_lit 11597697187344109532455254038697003859994339333622099437950692431287419136

noncomputable def hp769652 := BSN.cos_dyadic_bound_f 407951234 536870912 3 2 536870912 268435456 hp769649 hp708868 hp769650 hp769651 hp708870

noncomputable def hp769653 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 407951234) (BSN.cosEvenQ 536870912) 0 2 hp769649 hp708868 hp769650 rfl rfl rfl

noncomputable def hp769654 := hp769652 hp769650 389192045 rfl rfl rfl rfl rfl rfl rfl rfl (hp769653 rfl)

noncomputable def hp769655 := @BSN.binarySplit_of_base2 (BSN.cosOddP 407951234) (BSN.cosOddQ 536870912) 0 2 hp769651 hp708870 hp769650 rfl rfl rfl

noncomputable def hp769656 := nat_lit 26076985667310907561319351835065978749227512993891052244127897886743520492375775545005228900908090273553106589761

noncomputable def hp769657 := nat_lit 6757002007689340343750376217297164919796539525408483693650656918812242258891066222762084094414188438870081

noncomputable def hp769658 := nat_lit 158057678266610818509958856891285364596060706328889875423408841642501701733377703174003412925316300818455721400385

noncomputable def hp769659 := BSN.cos_dyadic_bound_f 659395791 536870912 4 3 536870912 268435456 hp769656 hp716712 hp769657 hp769658 hp716714

noncomputable def hp769660 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 659395791) (BSN.cosEvenQ 536870912) 0 3 hp769656 hp716712 hp769657 rfl rfl rfl

noncomputable def hp769661 := hp769659 hp769657 180342711 rfl rfl rfl rfl rfl rfl rfl rfl (hp769660 rfl)

noncomputable def hp769662 := @BSN.binarySplit_of_base3 (BSN.cosOddP 659395791) (BSN.cosOddQ 536870912) 0 3 hp769658 hp716714 hp769657 rfl rfl rfl

noncomputable def hp769663 := hp769648 hd4911 hd4913 hd4915 hd4917 hd4918 (hp769654 (hp769655 rfl) rfl rfl rfl rfl) (hp769661 (hp769662 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769664 := hp769582 (BSN.cos_quad_nat0 216 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 456679884 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 905375 1000)) rfl rfl (hp769663 rfl rfl rfl rfl rfl) hp769647

noncomputable def hp769665 := nat_lit 61323231553966056433914804472358899218917671842399602850668338679034259188225041168965070919034253774527597985761

noncomputable def hp769666 := nat_lit 87394282013146911096757107735579631503588527355522784172205356129155997139439123439561146362924542995546081

noncomputable def hp769667 := nat_lit 371241063722198163047534285438521337091576877516663910253547660997524810134852628605432322766051455253690727612385

noncomputable def hp769668 := BSN.cos_dyadic_bound_f 816188087 536870912 4 3 536870912 268435456 hp769665 hp716712 hp769666 hp769667 hp716714

noncomputable def hp769669 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 816188087) (BSN.cosEvenQ 536870912) 0 3 hp769665 hp716712 hp769666 rfl rfl rfl

noncomputable def hp769670 := hp769668 hp769666 27115228 rfl rfl rfl rfl rfl rfl rfl rfl (hp769669 rfl)

noncomputable def hp769671 := @BSN.binarySplit_of_base3 (BSN.cosOddP 816188087) (BSN.cosOddQ 536870912) 0 3 hp769667 hp716714 hp769666 rfl rfl rfl

noncomputable def hp769672 := nat_lit 1089194065565984664191797142361275228345938051827747076171163186243210881

noncomputable def hp769673 := nat_lit 60895389459502353135589871521180412549772636234191198375986886774401

noncomputable def hp769674 := nat_lit 3267460405919034987869120247340783324212714610210772846116737584956083841

noncomputable def hp769675 := BSN.cos_dyadic_bound_f 297216593 536870912 3 2 536870912 268435456 hp769672 hp708868 hp769673 hp769674 hp708870

noncomputable def hp769676 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 297216593) (BSN.cosEvenQ 536870912) 0 2 hp769672 hp708868 hp769673 rfl rfl rfl

noncomputable def hp769677 := hp769675 hp769673 456679884 rfl rfl rfl rfl rfl rfl rfl rfl (hp769676 rfl)

noncomputable def hp769678 := @BSN.binarySplit_of_base2 (BSN.cosOddP 297216593) (BSN.cosOddQ 536870912) 0 2 hp769674 hp708870 hp769673 rfl rfl rfl

noncomputable def hp769679 := hp769664 hd4920 hd4922 hd4924 hd4926 hd4918 (hp769670 (hp769671 rfl) rfl rfl rfl rfl) (hp769677 (hp769678 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769680 := hp769577 (BSN.cos_quad_nat2 22 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 425913308 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 905375 1000)) rfl rfl (hp769679 rfl rfl rfl rfl rfl) hp769647

noncomputable def hp769681 := nat_lit 636123660342077007101037406017790125989298389894185004554295500834078720

noncomputable def hp769682 := nat_lit 6411383813530533004830485482505302070966284145447383332102168641536

noncomputable def hp769683 := nat_lit 1666027777703075016782613956879621511863857075739010954259664812959072256

noncomputable def hp769684 := BSN.sin_dyadic_bound_f 224320504 536870912 3 2 536870912 268435456 hp769681 hp708845 hp769682 hp769683 hp708848

noncomputable def hp769685 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 224320504) (BSN.sinEvenQ 536870912) 0 2 hp769681 hp708845 hp769682 rfl rfl rfl

noncomputable def hp769686 := hp769684 hp769682 217850208 rfl rfl rfl rfl rfl rfl rfl rfl (hp769685 rfl)

noncomputable def hp769687 := @BSN.binarySplit_of_base2 (BSN.sinOddP 224320504) (BSN.sinOddQ 536870912) 0 2 hp769683 hp708848 hp769682 rfl rfl rfl

noncomputable def hp769688 := nat_lit 2128493156076639278462016173542633824890758583569643667439338206314509921

noncomputable def hp769689 := nat_lit 232526291324292790777306676679521740759091516553198528103789590623841

noncomputable def hp769690 := nat_lit 6385014415647269249804493907274542431190757567675824605261807039762282081

noncomputable def hp769691 := BSN.cos_dyadic_bound_f 351405867 536870912 3 2 536870912 268435456 hp769688 hp708868 hp769689 hp769690 hp708870

noncomputable def hp769692 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 351405867) (BSN.cosEvenQ 536870912) 0 2 hp769688 hp708868 hp769689 rfl rfl rfl

noncomputable def hp769693 := hp769691 hp769689 425913308 rfl rfl rfl rfl rfl rfl rfl rfl (hp769692 rfl)

noncomputable def hp769694 := @BSN.binarySplit_of_base2 (BSN.cosOddP 351405867) (BSN.cosOddQ 536870912) 0 2 hp769690 hp708870 hp769689 rfl rfl rfl

noncomputable def hp769695 := hp769680 hd4928 hd4930 hd4932 hd4934 hd4918 (hp769686 (hp769687 rfl) rfl rfl rfl rfl) (hp769693 (hp769694 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769696 := hp769573 (BSN.cos_quad_nat2 122 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 415903585 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 905375 1000)) rfl rfl (hp769695 rfl rfl rfl rfl rfl) hp769647

noncomputable def hp769697 := nat_lit 6372492236051236690581656005186317634224006250523699795800555335607975936

noncomputable def hp769698 := nat_lit 2083325179761198045315066703979173222815400678873437364890131465568256

noncomputable def hp769699 := nat_lit 19113310057794187675654337882150994556226387950213352512671885743892791296

noncomputable def hp769700 := BSN.cos_dyadic_bound_f 462215636 536870912 3 2 536870912 268435456 hp769697 hp708868 hp769698 hp769699 hp708870

noncomputable def hp769701 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 462215636) (BSN.cosEvenQ 536870912) 0 2 hp769697 hp708868 hp769698 rfl rfl rfl

noncomputable def hp769702 := hp769700 hp769698 349890580 rfl rfl rfl rfl rfl rfl rfl rfl (hp769701 rfl)

noncomputable def hp769703 := @BSN.binarySplit_of_base2 (BSN.cosOddP 462215636) (BSN.cosOddQ 536870912) 0 2 hp769699 hp708870 hp769698 rfl rfl rfl

noncomputable def hp769704 := nat_lit 2547050456314252712847860194114730235350383851399644755371322088546697216

noncomputable def hp769705 := nat_lit 332953809746250032888763472099273506645728386495588806062371556622336

noncomputable def hp769706 := nat_lit 7640485461323265638477803055399992159037860097425943088501841522526846976

noncomputable def hp769707 := BSN.cos_dyadic_bound_f 367534404 536870912 3 2 536870912 268435456 hp769704 hp708868 hp769705 hp769706 hp708870

noncomputable def hp769708 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 367534404) (BSN.cosEvenQ 536870912) 0 2 hp769704 hp708868 hp769705 rfl rfl rfl

noncomputable def hp769709 := hp769707 hp769705 415903585 rfl rfl rfl rfl rfl rfl rfl rfl (hp769708 rfl)

noncomputable def hp769710 := @BSN.binarySplit_of_base2 (BSN.cosOddP 367534404) (BSN.cosOddQ 536870912) 0 2 hp769706 hp708870 hp769705 rfl rfl rfl

noncomputable def hp769711 := hp769696 hd4936 hd4938 hd4940 hd4942 hd4918 (hp769702 (hp769703 rfl) rfl rfl rfl rfl) (hp769709 (hp769710 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769712 := hp769568 (BSN.cos_quad_nat2 238 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 530478949 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 905375 1000)) rfl rfl (hp769711 rfl rfl rfl rfl rfl) hp769647

noncomputable def hp769713 := nat_lit 361333106447988947752679326517776

noncomputable def hp769714 := BSN.sin_dyadic_bound_f 137872274 536870912 2 1 536870912 268435456 hp769713 hp708890 hp769713 hp769713 hp708891

noncomputable def hp769715 := @BSN.binarySplit_of_base (BSN.sinEvenP 137872274) (BSN.sinEvenQ 536870912) 0 1 hp769713 hp708890 hp769713 rfl rfl rfl

noncomputable def hp769716 := hp769714 hp769713 136361819 rfl rfl rfl rfl rfl rfl rfl rfl (hp769715 rfl)

noncomputable def hp769717 := @BSN.binarySplit_of_base (BSN.sinOddP 137872274) (BSN.sinOddQ 536870912) 0 1 hp769713 hp708891 hp769713 rfl rfl rfl

noncomputable def hp769718 := nat_lit 47292852212754610136310262836496

noncomputable def hp769719 := BSN.cos_dyadic_bound_f 82927558 536870912 2 1 536870912 268435456 hp769718 hp708767 hp769718 hp769718 hp708768

noncomputable def hp769720 := @BSN.binarySplit_of_base (BSN.cosEvenP 82927558) (BSN.cosEvenQ 536870912) 0 1 hp769718 hp708767 hp769718 rfl rfl rfl

noncomputable def hp769721 := hp769719 hp769718 530478949 rfl rfl rfl rfl rfl rfl rfl rfl (hp769720 rfl)

noncomputable def hp769722 := @BSN.binarySplit_of_base (BSN.cosOddP 82927558) (BSN.cosOddQ 536870912) 0 1 hp769718 hp708768 hp769718 rfl rfl rfl

noncomputable def hp769723 := hp769712 hd4944 hd4946 hd4961 hd4963 hd4918 (hp769716 (hp769717 rfl) rfl rfl rfl rfl) (hp769721 (hp769722 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769724 := hp769563 496031641 Bool.false Bool.false 617726641 234202 BSN.abs_quadSignPos (BSN.cos_quad_nat0 288 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 496031641 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 905375 1000)) rfl (hp769723 rfl rfl rfl rfl rfl)

noncomputable def hp769725 := nat_lit 275371888912440980969480822485239335716574088072411258375195238200688896

noncomputable def hp769726 := nat_lit 3892685982530431274067130549617497896052848388313897870871539138816

noncomputable def hp769727 := nat_lit 826107881365357882045894333194618772153930158520457147329843971523789056

noncomputable def hp769728 := BSN.cos_dyadic_bound_f 210756594 536870912 3 2 536870912 268435456 hp769725 hp708868 hp769726 hp769727 hp708870

noncomputable def hp769729 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 210756594) (BSN.cosEvenQ 536870912) 0 2 hp769725 hp708868 hp769726 rfl rfl rfl

noncomputable def hp769730 := hp769728 hp769726 496031641 rfl rfl rfl rfl rfl rfl rfl rfl (hp769729 rfl)

noncomputable def hp769731 := @BSN.binarySplit_of_base2 (BSN.cosOddP 210756594) (BSN.cosOddQ 536870912) 0 2 hp769727 hp708870 hp769726 rfl rfl rfl

noncomputable def hp769732 := hp769724 hp769647 hd5088 hd5090 hd4918 (hp769730 (hp769731 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp769733 := @hp769558 Bool.false 617726641 268435456 117101 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 905375 1000)) (Enclosure.sfrac Bool.false 905375 1000) 12) (@hp769560 117101 134217728 (hp769732 rfl rfl rfl) (hp769732 rfl rfl rfl) rfl rfl)

noncomputable def hp769734 := @Enclosure.Real.IsNear.mulLit_ff hp769549 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1))) 9684735 33554432 1

noncomputable def hp769735 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 12) (hp769548 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp769736 := @hp769735 1 1 0 1 9684735 33554432 1 33554432 9684735 33554432 1

noncomputable def hp769737 := @Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 12) (Enclosure.sfrac Bool.false 1 1) Bool.false 1

noncomputable def hp769738 := @Enclosure.Real.IsNear.of_eq (hp769548 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp769739 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 905375 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp769740 := @hp769738 (@Inv.inv Real Real.instInv (Real.sqrt hp769550)) Bool.false 9684735 33554432 1 33554432 (hp769739 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 905375 1000) 905375 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 905375 1000))))

noncomputable def hp769741 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp769550)) Bool.false 19369470 67108864 2 67108864 9684735 33554432

noncomputable def hp769742 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp769550) Bool.false 232510216 67108864 6 67108864 29063777 8388608 3 33554432

noncomputable def hp769743 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 905375 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp769744 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 905375 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp769745 := @hp769744 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 905375 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 77360360801

noncomputable def hp769746 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 905375 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 905375 1000 0

noncomputable def hp769747 := @hp769746 1 10680707 67108864 1 67108864 77360360801 536870912 7243 536870912 (Enclosure.Real.IsNear.const Bool.false 905375 1000) hd4949

noncomputable def hp769748 := @hp769745 536870912 7243 536870912 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 905375 1000) 905375 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 905375 1000))) (hp769747 rfl)

noncomputable def hp769749 := @hp769743 77360360801 536870912 7243 536870912 402785824 402785862 33554432 hp769748 rfl rfl rfl

noncomputable def hp769750 := @Enclosure.Real.IsNear.recentre' hp769550 Bool.false 805571686 67108864 38 67108864 402785843 33554432 19 33554432 (hp769749 rfl rfl rfl)

noncomputable def hp769751 := @Enclosure.Real.IsNear.sqrt_image hp769550 402785843 33554432 19 33554432 116255105 116255111 33554432 (hp769750 rfl) rfl rfl

noncomputable def hp769752 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp769550) 29063777 8388608 3 33554432 9684734 9684736 33554432 (hp769742 (hp769751 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp769753 := @hp769736 33554432 (@hp769737 1 0 1 (BSN.neg_one_pow_even_mk 12 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1)) (hp769740 (@hp769741 1 33554432 (hp769752 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp769754 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp769755 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1)))

noncomputable def hp769756 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1))) (hp769754 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp769755 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp769757 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 905375 1000) 905375 1000 12 (@Eq.refl Real (Enclosure.sfrac Bool.false 905375 1000)) rfl

noncomputable def hp769758 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp769759 := @hp769758 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp769755 (Enclosure.sfrac Bool.false 1 16)))) 8391197

noncomputable def hp769760 := @hp769759 8388608 123 33554432 15336541 16777216 84452777 22837985280000 128691936829577 140737488355328 5402504515366597 766315624094760960000

noncomputable def hp769761 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp769762 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1)))) 33544079

noncomputable def hp769763 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1)))) Bool.false

noncomputable def hp769764 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 833521) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp769765 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1))) Bool.false 117307663243292602745

noncomputable def hp769766 := nat_lit 512735432772976395781250501

noncomputable def hp769767 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1)) 884279719003555 140737488355328 1

noncomputable def hp769768 := @Enclosure.Real.IsNear.subLit_ff_p hp769550 (Enclosure.sfrac Bool.false 12 1) 402785843 33554432 19 33554432 12 1 0

noncomputable def hp769769 := @hp769767 500000000000000 132659 33554432 19 33554432 117307663243292602745 4722366482869645213696 hp769766 hp682805 hd4948 (@hp769768 1 132659 132659 33554432 19 33554432 (hp769750 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp769770 := @hp769764 833521 33554432 239 67108864 Bool.false 33544079 33554432 1 10890000 (@hp769765 4722366482869645213696 hp769766 hp682805 833521 33554432 239 67108864 (hp769769 rfl) rfl) (Enclosure.sfrac_false_div 833521 33554432)

noncomputable def hp769771 := BSN.cos_dyadic_bound_f 833521 33554432 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp769772 := hp769771 1 33544079 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 833521) (BSN.cosEvenQ 33554432) 0 0 rfl)

noncomputable def hp769773 := hp769772 (@BSN.binarySplit_of_le (BSN.cosOddP 833521) (BSN.cosOddQ 33554432) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp769774 := @hp769762 33554432 166863679 45675970560000 33564665 33564911 33554432 (@hp769763 33544079 33554432 2669818864 730815528960000 33544079 33554432 166863679 45675970560000 (hp769770 hp769773 rfl rfl) rfl)

noncomputable def hp769775 := @hp769761 Bool.false 67129576 67108864 246 67108864 8391197 8388608 123 33554432 (hp769774 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp769776 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp769755 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp769777 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp769755 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3501755)) (@Nat.cast Real Real.instNatCast 8388608)) Bool.true

noncomputable def hp769778 := nat_lit 66146283420135538023490162405

noncomputable def hp769779 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp769755 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp769778

noncomputable def hp769780 := nat_lit 17340593895101100528350959623523869

noncomputable def hp769781 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp769755 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp769782 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1)))

noncomputable def hp769783 := @hp769782 (Enclosure.sfrac Bool.false 1 16) 4433698984407 1125899906842624 642575611 1125899906842624 1 16 0

noncomputable def hp769784 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1)) 17598410281

noncomputable def hp769785 := @hp769784 1125899906842624 5041403 1125899906842624 132659 33554432 19 33554432 148770251080753741824 4433698984407 1125899906842624 642575611

noncomputable def hp769786 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1)) 132659 33554432 19

noncomputable def hp769787 := @hp769786 33554432 132659 33554432 19 33554432 17598410281 1125899906842624 5041403 1125899906842624 (@hp769768 1 132659 132659 33554432 19 33554432 (hp769750 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp769788 := hp769787 (@hp769768 1 132659 132659 33554432 19 33554432 (hp769750 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp769789 := @hp769785 1125899906842624 (hp769788 rfl) (@hp769768 1 132659 132659 33554432 19 33554432 (hp769750 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp769790 := @hp769781 500000000000000 74802443162071 1125899906842624 642575611 1125899906842624 hp769778 hp682141 hp769780 hp682143 hd4948 (@hp769783 1 1196839090593136 74802443162071 1125899906842624 642575611 1125899906842624 (hp769789 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp769791 := @hp769777 3501755 8388608 121 33554432 Bool.false 30673082 33554432 1 10890000 (@hp769779 hp682141 hp769780 hp682143 3501755 8388608 121 33554432 (hp769790 rfl) rfl) (Enclosure.sfrac_true_div 3501755 8388608)

noncomputable def hp769792 := nat_lit 150363708957523200804000625

noncomputable def hp769793 := BSN.cos_dyadic_bound_f 3501755 8388608 2 1 33554432 10890000 hp769792 hp631536 hp769792 hp769792 hp631537

noncomputable def hp769794 := @BSN.binarySplit_of_base (BSN.cosEvenP 3501755) (BSN.cosEvenQ 8388608) 0 1 hp769792 hp631536 hp769792 rfl rfl rfl

noncomputable def hp769795 := hp769793 hp769792 30673082 rfl rfl rfl rfl rfl rfl rfl rfl (hp769794 rfl)

noncomputable def hp769796 := @BSN.binarySplit_of_base (BSN.cosOddP 3501755) (BSN.cosOddQ 8388608) 0 1 hp769792 hp631537 hp769792 rfl rfl rfl

noncomputable def hp769797 := hp769791 (BSN.cos_neg_of_bound 3501755 8388608 Bool.false 30673082 33554432 1 10890000 (hp769795 (hp769796 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp769798 := hp769760 hp769775 (@hp769776 30673082 33554432 1351244432 365407764480000 15336541 16777216 84452777 22837985280000 (hp769797 rfl) rfl)

noncomputable def hp769799 := @hp769734 33554432 128691936829577 140737488355328 5402504515366597 766315624094760960000 1246347304831193407095 4722366482869645213696 6627819695771310241049 hp769546 (hp769753 rfl) (@hp769756 Bool.false 128691936829577 140737488355328 5402504515366597 766315624094760960000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769550 (Enclosure.sfrac Bool.false 12 1)) (hp769757 rfl (hp769553 rfl rfl))) (hp769798 rfl))

noncomputable def hp769800 := @hp769547 hp769544 hp769546 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 905375 1000))) (@hp769552 hp769544 hp769546 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 905375 1000) 12 (hp769553 rfl rfl)) (@hp769556 hp769544 hp769546 hp769733 (hp769799 rfl) rfl rfl))

theorem hd5091 : hp769545 hp769546 := hp769800

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

noncomputable def hp790762 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000)) Bool.false 556919581 10737418240 1213 10737418240

noncomputable def hp793497 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 891448 1000) (Enclosure.sfrac Bool.false 892716 1000) 891448 1000 892716 1000

noncomputable def hp793498 := hp793497 (@Eq.refl Real (Enclosure.sfrac Bool.false 891448 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 892716 1000)) rfl rfl rfl

noncomputable def hp793499 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 891448 1000) (Enclosure.sfrac Bool.false 892716 1000) hp793498)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 891448 1000) (Enclosure.sfrac Bool.false 892716 1000) hp793498))

noncomputable def hp793500 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 891448 1000) 891448 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 891448 1000)) rfl rfl

noncomputable def hp793501 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 891448 1000) (Enclosure.sfrac Bool.false 892716 1000) hp793498)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 891448 1000) (Enclosure.sfrac Bool.false 892716 1000) hp793498))

noncomputable def hp793502 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 891448 1000) (Enclosure.sfrac Bool.false 892716 1000) hp793498)) 43591284853012421774541

noncomputable def hp793503 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 891448 1000) (Enclosure.sfrac Bool.false 892716 1000) hp793498)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 891448 1000))

noncomputable def hp793504 := @hp793502 18889465931478580854784 hp766732 hp756249 (@hp793503 Bool.true 43591284853012421774541 18889465931478580854784 hp766732 hp756249 (hd4340 (Enclosure.sfrac Bool.false 891448 1000) (Enclosure.sfrac Bool.false 892716 1000) hp793498) hd5076)

noncomputable def hp793505 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 891448 1000) (Enclosure.sfrac Bool.false 892716 1000) hp793498)) 22990705254852030015421

noncomputable def hp793506 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 891448 1000) (Enclosure.sfrac Bool.false 892716 1000) hp793498)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 892716 1000))

noncomputable def hp793507 := @hp793505 37778931862957161709568 hp766987 hp743845 (@hp793506 Bool.false 22990705254852030015421 37778931862957161709568 hp766987 hp743845 (hd4359 (Enclosure.sfrac Bool.false 891448 1000) (Enclosure.sfrac Bool.false 892716 1000) hp793498) hd5077)

noncomputable def hp793508 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 891448 1000) (Enclosure.sfrac Bool.false 892716 1000) hp793498) hp793500 (hp793501 (hp793504 rfl rfl rfl) (hp793507 rfl rfl rfl))

noncomputable def hp793509 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 891448 1000) (Enclosure.sfrac Bool.false 892716 1000) hp793498)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793510 := hp793509 (Enclosure.sfrac Bool.false 891448 1000) 749551 1000 891448 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793511 := hp793510 (@Eq.refl Real (Enclosure.sfrac Bool.false 891448 1000)) rfl rfl rfl rfl

noncomputable def hp793512 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 891448 1000) (Enclosure.sfrac Bool.false 892716 1000) hp793498)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793513 := @hp793512 Bool.true Bool.false 43591284853012421774541 18889465931478580854784 hp766732 hp756249 556919581 10737418240 1213 10737418240 (@hp793503 Bool.true 43591284853012421774541 18889465931478580854784 hp766732 hp756249 (hd4340 (Enclosure.sfrac Bool.false 891448 1000) (Enclosure.sfrac Bool.false 892716 1000) hp793498) hd5076)

noncomputable def hp793514 := hp793513 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793515 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 891448 1000) (Enclosure.sfrac Bool.false 892716 1000) hp793498)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793516 := hp793515 (Enclosure.sfrac Bool.false 892716 1000) 749551 1000 892716 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793517 := hp793516 (@Eq.refl Real (Enclosure.sfrac Bool.false 892716 1000)) rfl rfl rfl rfl

noncomputable def hp793518 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 891448 1000) (Enclosure.sfrac Bool.false 892716 1000) hp793498)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793519 := @hp793518 Bool.false Bool.false 22990705254852030015421 37778931862957161709568 hp766987 hp743845 556919581 10737418240 1213 10737418240 (@hp793506 Bool.false 22990705254852030015421 37778931862957161709568 hp766987 hp743845 (hd4359 (Enclosure.sfrac Bool.false 891448 1000) (Enclosure.sfrac Bool.false 892716 1000) hp793498) hd5077)

noncomputable def hp793520 := hp793519 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793522 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 892716 1000) (Enclosure.sfrac Bool.false 893984 1000) 892716 1000 893984 1000

noncomputable def hp793523 := hp793522 (@Eq.refl Real (Enclosure.sfrac Bool.false 892716 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 893984 1000)) rfl rfl rfl

noncomputable def hp793524 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 892716 1000) (Enclosure.sfrac Bool.false 893984 1000) hp793523)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 892716 1000) (Enclosure.sfrac Bool.false 893984 1000) hp793523))

noncomputable def hp793525 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 892716 1000) 892716 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 892716 1000)) rfl rfl

noncomputable def hp793526 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 892716 1000) (Enclosure.sfrac Bool.false 893984 1000) hp793523)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 892716 1000) (Enclosure.sfrac Bool.false 893984 1000) hp793523))

noncomputable def hp793527 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 892716 1000) (Enclosure.sfrac Bool.false 893984 1000) hp793523)) 22990705254852030015421

noncomputable def hp793528 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 892716 1000) (Enclosure.sfrac Bool.false 893984 1000) hp793523)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 892716 1000))

noncomputable def hp793529 := @hp793527 37778931862957161709568 hp766987 hp743845 (@hp793528 Bool.false 22990705254852030015421 37778931862957161709568 hp766987 hp743845 (hd4340 (Enclosure.sfrac Bool.false 892716 1000) (Enclosure.sfrac Bool.false 893984 1000) hp793523) hd5077)

noncomputable def hp793530 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 892716 1000) (Enclosure.sfrac Bool.false 893984 1000) hp793523)) 21767116352174073775419

noncomputable def hp793531 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 892716 1000) (Enclosure.sfrac Bool.false 893984 1000) hp793523)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 893984 1000))

noncomputable def hp793532 := @hp793530 9444732965739290427392 348100808003564408268299 hp751876 (@hp793531 Bool.true 21767116352174073775419 9444732965739290427392 348100808003564408268299 hp751876 (hd4359 (Enclosure.sfrac Bool.false 892716 1000) (Enclosure.sfrac Bool.false 893984 1000) hp793523) hd5078)

noncomputable def hp793533 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 892716 1000) (Enclosure.sfrac Bool.false 893984 1000) hp793523) hp793525 (hp793526 (hp793529 rfl rfl rfl) (hp793532 rfl rfl rfl))

noncomputable def hp793534 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 892716 1000) (Enclosure.sfrac Bool.false 893984 1000) hp793523)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793535 := hp793534 (Enclosure.sfrac Bool.false 892716 1000) 749551 1000 892716 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793536 := hp793535 (@Eq.refl Real (Enclosure.sfrac Bool.false 892716 1000)) rfl rfl rfl rfl

noncomputable def hp793537 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 892716 1000) (Enclosure.sfrac Bool.false 893984 1000) hp793523)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793538 := @hp793537 Bool.false Bool.false 22990705254852030015421 37778931862957161709568 hp766987 hp743845 556919581 10737418240 1213 10737418240 (@hp793528 Bool.false 22990705254852030015421 37778931862957161709568 hp766987 hp743845 (hd4340 (Enclosure.sfrac Bool.false 892716 1000) (Enclosure.sfrac Bool.false 893984 1000) hp793523) hd5077)

noncomputable def hp793539 := hp793538 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793540 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 892716 1000) (Enclosure.sfrac Bool.false 893984 1000) hp793523)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793541 := hp793540 (Enclosure.sfrac Bool.false 893984 1000) 749551 1000 893984 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793542 := hp793541 (@Eq.refl Real (Enclosure.sfrac Bool.false 893984 1000)) rfl rfl rfl rfl

noncomputable def hp793543 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 892716 1000) (Enclosure.sfrac Bool.false 893984 1000) hp793523)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793544 := @hp793543 Bool.true Bool.false 21767116352174073775419 9444732965739290427392 348100808003564408268299 hp751876 556919581 10737418240 1213 10737418240 (@hp793531 Bool.true 21767116352174073775419 9444732965739290427392 348100808003564408268299 hp751876 (hd4359 (Enclosure.sfrac Bool.false 892716 1000) (Enclosure.sfrac Bool.false 893984 1000) hp793523) hd5078)

noncomputable def hp793545 := hp793544 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793547 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 893984 1000) (Enclosure.sfrac Bool.false 895251 1000) 893984 1000 895251 1000

noncomputable def hp793548 := hp793547 (@Eq.refl Real (Enclosure.sfrac Bool.false 893984 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 895251 1000)) rfl rfl rfl

noncomputable def hp793549 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 893984 1000) (Enclosure.sfrac Bool.false 895251 1000) hp793548)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 893984 1000) (Enclosure.sfrac Bool.false 895251 1000) hp793548))

noncomputable def hp793550 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 893984 1000) 893984 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 893984 1000)) rfl rfl

noncomputable def hp793551 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 893984 1000) (Enclosure.sfrac Bool.false 895251 1000) hp793548)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 893984 1000) (Enclosure.sfrac Bool.false 895251 1000) hp793548))

noncomputable def hp793552 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 893984 1000) (Enclosure.sfrac Bool.false 895251 1000) hp793548)) 21767116352174073775419

noncomputable def hp793553 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 893984 1000) (Enclosure.sfrac Bool.false 895251 1000) hp793548)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 893984 1000))

noncomputable def hp793554 := @hp793552 9444732965739290427392 348100808003564408268299 hp751876 (@hp793553 Bool.true 21767116352174073775419 9444732965739290427392 348100808003564408268299 hp751876 (hd4340 (Enclosure.sfrac Bool.false 893984 1000) (Enclosure.sfrac Bool.false 895251 1000) hp793548) hd5078)

noncomputable def hp793555 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 893984 1000) (Enclosure.sfrac Bool.false 895251 1000) hp793548)) 36072763926487592170395

noncomputable def hp793556 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 893984 1000) (Enclosure.sfrac Bool.false 895251 1000) hp793548)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 895251 1000))

noncomputable def hp793557 := @hp793555 151115727451828646838272 60842848172876677824331 hp767491 (@hp793556 Bool.false 36072763926487592170395 151115727451828646838272 60842848172876677824331 hp767491 (hd4359 (Enclosure.sfrac Bool.false 893984 1000) (Enclosure.sfrac Bool.false 895251 1000) hp793548) hd5079)

noncomputable def hp793558 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 893984 1000) (Enclosure.sfrac Bool.false 895251 1000) hp793548) hp793550 (hp793551 (hp793554 rfl rfl rfl) (hp793557 rfl rfl rfl))

noncomputable def hp793559 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 893984 1000) (Enclosure.sfrac Bool.false 895251 1000) hp793548)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793560 := hp793559 (Enclosure.sfrac Bool.false 893984 1000) 749551 1000 893984 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793561 := hp793560 (@Eq.refl Real (Enclosure.sfrac Bool.false 893984 1000)) rfl rfl rfl rfl

noncomputable def hp793562 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 893984 1000) (Enclosure.sfrac Bool.false 895251 1000) hp793548)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793563 := @hp793562 Bool.true Bool.false 21767116352174073775419 9444732965739290427392 348100808003564408268299 hp751876 556919581 10737418240 1213 10737418240 (@hp793553 Bool.true 21767116352174073775419 9444732965739290427392 348100808003564408268299 hp751876 (hd4340 (Enclosure.sfrac Bool.false 893984 1000) (Enclosure.sfrac Bool.false 895251 1000) hp793548) hd5078)

noncomputable def hp793564 := hp793563 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793565 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 893984 1000) (Enclosure.sfrac Bool.false 895251 1000) hp793548)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793566 := hp793565 (Enclosure.sfrac Bool.false 895251 1000) 749551 1000 895251 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793567 := hp793566 (@Eq.refl Real (Enclosure.sfrac Bool.false 895251 1000)) rfl rfl rfl rfl

noncomputable def hp793568 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 893984 1000) (Enclosure.sfrac Bool.false 895251 1000) hp793548)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793569 := @hp793568 Bool.false Bool.false 36072763926487592170395 151115727451828646838272 60842848172876677824331 hp767491 556919581 10737418240 1213 10737418240 (@hp793556 Bool.false 36072763926487592170395 151115727451828646838272 60842848172876677824331 hp767491 (hd4359 (Enclosure.sfrac Bool.false 893984 1000) (Enclosure.sfrac Bool.false 895251 1000) hp793548) hd5079)

noncomputable def hp793570 := hp793569 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793572 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 895251 1000) (Enclosure.sfrac Bool.false 896518 1000) 895251 1000 896518 1000

noncomputable def hp793573 := hp793572 (@Eq.refl Real (Enclosure.sfrac Bool.false 895251 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 896518 1000)) rfl rfl rfl

noncomputable def hp793574 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 895251 1000) (Enclosure.sfrac Bool.false 896518 1000) hp793573)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 895251 1000) (Enclosure.sfrac Bool.false 896518 1000) hp793573))

noncomputable def hp793575 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 895251 1000) 895251 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 895251 1000)) rfl rfl

noncomputable def hp793576 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 895251 1000) (Enclosure.sfrac Bool.false 896518 1000) hp793573)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 895251 1000) (Enclosure.sfrac Bool.false 896518 1000) hp793573))

noncomputable def hp793577 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 895251 1000) (Enclosure.sfrac Bool.false 896518 1000) hp793573)) 36072763926487592170395

noncomputable def hp793578 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 895251 1000) (Enclosure.sfrac Bool.false 896518 1000) hp793573)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 895251 1000))

noncomputable def hp793579 := @hp793577 151115727451828646838272 60842848172876677824331 hp767491 (@hp793578 Bool.false 36072763926487592170395 151115727451828646838272 60842848172876677824331 hp767491 (hd4340 (Enclosure.sfrac Bool.false 895251 1000) (Enclosure.sfrac Bool.false 896518 1000) hp793573) hd5079)

noncomputable def hp793580 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 895251 1000) (Enclosure.sfrac Bool.false 896518 1000) hp793573)) 28706274856387143547737

noncomputable def hp793581 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 895251 1000) (Enclosure.sfrac Bool.false 896518 1000) hp793573)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 896518 1000))

noncomputable def hp793582 := @hp793580 37778931862957161709568 63461597078459511842051 hp746784 (@hp793581 Bool.true 28706274856387143547737 37778931862957161709568 63461597078459511842051 hp746784 (hd4359 (Enclosure.sfrac Bool.false 895251 1000) (Enclosure.sfrac Bool.false 896518 1000) hp793573) hd5080)

noncomputable def hp793583 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 895251 1000) (Enclosure.sfrac Bool.false 896518 1000) hp793573) hp793575 (hp793576 (hp793579 rfl rfl rfl) (hp793582 rfl rfl rfl))

noncomputable def hp793584 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 895251 1000) (Enclosure.sfrac Bool.false 896518 1000) hp793573)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793585 := hp793584 (Enclosure.sfrac Bool.false 895251 1000) 749551 1000 895251 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793586 := hp793585 (@Eq.refl Real (Enclosure.sfrac Bool.false 895251 1000)) rfl rfl rfl rfl

noncomputable def hp793587 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 895251 1000) (Enclosure.sfrac Bool.false 896518 1000) hp793573)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793588 := @hp793587 Bool.false Bool.false 36072763926487592170395 151115727451828646838272 60842848172876677824331 hp767491 556919581 10737418240 1213 10737418240 (@hp793578 Bool.false 36072763926487592170395 151115727451828646838272 60842848172876677824331 hp767491 (hd4340 (Enclosure.sfrac Bool.false 895251 1000) (Enclosure.sfrac Bool.false 896518 1000) hp793573) hd5079)

noncomputable def hp793589 := hp793588 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793590 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 895251 1000) (Enclosure.sfrac Bool.false 896518 1000) hp793573)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793591 := hp793590 (Enclosure.sfrac Bool.false 896518 1000) 749551 1000 896518 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793592 := hp793591 (@Eq.refl Real (Enclosure.sfrac Bool.false 896518 1000)) rfl rfl rfl rfl

noncomputable def hp793593 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 895251 1000) (Enclosure.sfrac Bool.false 896518 1000) hp793573)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793594 := @hp793593 Bool.true Bool.false 28706274856387143547737 37778931862957161709568 63461597078459511842051 hp746784 556919581 10737418240 1213 10737418240 (@hp793581 Bool.true 28706274856387143547737 37778931862957161709568 63461597078459511842051 hp746784 (hd4359 (Enclosure.sfrac Bool.false 895251 1000) (Enclosure.sfrac Bool.false 896518 1000) hp793573) hd5080)

noncomputable def hp793595 := hp793594 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793597 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 896518 1000) (Enclosure.sfrac Bool.false 898496 1000) 896518 1000 898496 1000

noncomputable def hp793598 := hp793597 (@Eq.refl Real (Enclosure.sfrac Bool.false 896518 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 898496 1000)) rfl rfl rfl

noncomputable def hp793599 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 896518 1000) (Enclosure.sfrac Bool.false 898496 1000) hp793598)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 896518 1000) (Enclosure.sfrac Bool.false 898496 1000) hp793598))

noncomputable def hp793600 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 896518 1000) 896518 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 896518 1000)) rfl rfl

noncomputable def hp793601 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 896518 1000) (Enclosure.sfrac Bool.false 898496 1000) hp793598)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 896518 1000) (Enclosure.sfrac Bool.false 898496 1000) hp793598))

noncomputable def hp793602 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 896518 1000) (Enclosure.sfrac Bool.false 898496 1000) hp793598)) 28706274856387143547737

noncomputable def hp793603 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 896518 1000) (Enclosure.sfrac Bool.false 898496 1000) hp793598)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 896518 1000))

noncomputable def hp793604 := @hp793602 37778931862957161709568 63461597078459511842051 hp746784 (@hp793603 Bool.true 28706274856387143547737 37778931862957161709568 63461597078459511842051 hp746784 (hd4340 (Enclosure.sfrac Bool.false 896518 1000) (Enclosure.sfrac Bool.false 898496 1000) hp793598) hd5080)

noncomputable def hp793605 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 896518 1000) (Enclosure.sfrac Bool.false 898496 1000) hp793598)) 210791723592354924923981

noncomputable def hp793606 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 896518 1000) (Enclosure.sfrac Bool.false 898496 1000) hp793598)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 898496 1000))

noncomputable def hp793607 := @hp793605 37778931862957161709568 hp767997 hp743344 (@hp793606 Bool.false 210791723592354924923981 37778931862957161709568 hp767997 hp743344 (hd4359 (Enclosure.sfrac Bool.false 896518 1000) (Enclosure.sfrac Bool.false 898496 1000) hp793598) hd5081)

noncomputable def hp793608 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 896518 1000) (Enclosure.sfrac Bool.false 898496 1000) hp793598) hp793600 (hp793601 (hp793604 rfl rfl rfl) (hp793607 rfl rfl rfl))

noncomputable def hp793609 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 896518 1000) (Enclosure.sfrac Bool.false 898496 1000) hp793598)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793610 := hp793609 (Enclosure.sfrac Bool.false 896518 1000) 749551 1000 896518 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793611 := hp793610 (@Eq.refl Real (Enclosure.sfrac Bool.false 896518 1000)) rfl rfl rfl rfl

noncomputable def hp793612 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 896518 1000) (Enclosure.sfrac Bool.false 898496 1000) hp793598)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793613 := @hp793612 Bool.true Bool.false 28706274856387143547737 37778931862957161709568 63461597078459511842051 hp746784 556919581 10737418240 1213 10737418240 (@hp793603 Bool.true 28706274856387143547737 37778931862957161709568 63461597078459511842051 hp746784 (hd4340 (Enclosure.sfrac Bool.false 896518 1000) (Enclosure.sfrac Bool.false 898496 1000) hp793598) hd5080)

noncomputable def hp793614 := hp793613 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793615 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 896518 1000) (Enclosure.sfrac Bool.false 898496 1000) hp793598)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793616 := hp793615 (Enclosure.sfrac Bool.false 898496 1000) 749551 1000 898496 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793617 := hp793616 (@Eq.refl Real (Enclosure.sfrac Bool.false 898496 1000)) rfl rfl rfl rfl

noncomputable def hp793618 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 896518 1000) (Enclosure.sfrac Bool.false 898496 1000) hp793598)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793619 := @hp793618 Bool.false Bool.false 210791723592354924923981 37778931862957161709568 hp767997 hp743344 556919581 10737418240 1213 10737418240 (@hp793606 Bool.false 210791723592354924923981 37778931862957161709568 hp767997 hp743344 (hd4359 (Enclosure.sfrac Bool.false 896518 1000) (Enclosure.sfrac Bool.false 898496 1000) hp793598) hd5081)

noncomputable def hp793620 := hp793619 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793622 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 898496 1000) (Enclosure.sfrac Bool.false 899604 1000) 898496 1000 899604 1000

noncomputable def hp793623 := hp793622 (@Eq.refl Real (Enclosure.sfrac Bool.false 898496 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 899604 1000)) rfl rfl rfl

noncomputable def hp793624 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 898496 1000) (Enclosure.sfrac Bool.false 899604 1000) hp793623)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 898496 1000) (Enclosure.sfrac Bool.false 899604 1000) hp793623))

noncomputable def hp793625 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 898496 1000) 898496 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 898496 1000)) rfl rfl

noncomputable def hp793626 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 898496 1000) (Enclosure.sfrac Bool.false 899604 1000) hp793623)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 898496 1000) (Enclosure.sfrac Bool.false 899604 1000) hp793623))

noncomputable def hp793627 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 898496 1000) (Enclosure.sfrac Bool.false 899604 1000) hp793623)) 210791723592354924923981

noncomputable def hp793628 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 898496 1000) (Enclosure.sfrac Bool.false 899604 1000) hp793623)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 898496 1000))

noncomputable def hp793629 := @hp793627 37778931862957161709568 hp767997 hp743344 (@hp793628 Bool.false 210791723592354924923981 37778931862957161709568 hp767997 hp743344 (hd4340 (Enclosure.sfrac Bool.false 898496 1000) (Enclosure.sfrac Bool.false 899604 1000) hp793623) hd5081)

noncomputable def hp793630 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 898496 1000) (Enclosure.sfrac Bool.false 899604 1000) hp793623)) 8348607052700988353101

noncomputable def hp793631 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 898496 1000) (Enclosure.sfrac Bool.false 899604 1000) hp793623)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 899604 1000))

noncomputable def hp793632 := @hp793630 18889465931478580854784 56041924141545412297637 hp763445 (@hp793631 Bool.true 8348607052700988353101 18889465931478580854784 56041924141545412297637 hp763445 (hd4359 (Enclosure.sfrac Bool.false 898496 1000) (Enclosure.sfrac Bool.false 899604 1000) hp793623) hd5082)

noncomputable def hp793633 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 898496 1000) (Enclosure.sfrac Bool.false 899604 1000) hp793623) hp793625 (hp793626 (hp793629 rfl rfl rfl) (hp793632 rfl rfl rfl))

noncomputable def hp793634 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 898496 1000) (Enclosure.sfrac Bool.false 899604 1000) hp793623)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793635 := hp793634 (Enclosure.sfrac Bool.false 898496 1000) 749551 1000 898496 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793636 := hp793635 (@Eq.refl Real (Enclosure.sfrac Bool.false 898496 1000)) rfl rfl rfl rfl

noncomputable def hp793637 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 898496 1000) (Enclosure.sfrac Bool.false 899604 1000) hp793623)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793638 := @hp793637 Bool.false Bool.false 210791723592354924923981 37778931862957161709568 hp767997 hp743344 556919581 10737418240 1213 10737418240 (@hp793628 Bool.false 210791723592354924923981 37778931862957161709568 hp767997 hp743344 (hd4340 (Enclosure.sfrac Bool.false 898496 1000) (Enclosure.sfrac Bool.false 899604 1000) hp793623) hd5081)

noncomputable def hp793639 := hp793638 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793640 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 898496 1000) (Enclosure.sfrac Bool.false 899604 1000) hp793623)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793641 := hp793640 (Enclosure.sfrac Bool.false 899604 1000) 749551 1000 899604 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793642 := hp793641 (@Eq.refl Real (Enclosure.sfrac Bool.false 899604 1000)) rfl rfl rfl rfl

noncomputable def hp793643 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 898496 1000) (Enclosure.sfrac Bool.false 899604 1000) hp793623)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793644 := @hp793643 Bool.true Bool.false 8348607052700988353101 18889465931478580854784 56041924141545412297637 hp763445 556919581 10737418240 1213 10737418240 (@hp793631 Bool.true 8348607052700988353101 18889465931478580854784 56041924141545412297637 hp763445 (hd4359 (Enclosure.sfrac Bool.false 898496 1000) (Enclosure.sfrac Bool.false 899604 1000) hp793623) hd5082)

noncomputable def hp793645 := hp793644 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793647 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 899604 1000) (Enclosure.sfrac Bool.false 900158 1000) 899604 1000 900158 1000

noncomputable def hp793648 := hp793647 (@Eq.refl Real (Enclosure.sfrac Bool.false 899604 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 900158 1000)) rfl rfl rfl

noncomputable def hp793649 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 899604 1000) (Enclosure.sfrac Bool.false 900158 1000) hp793648)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 899604 1000) (Enclosure.sfrac Bool.false 900158 1000) hp793648))

noncomputable def hp793650 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 899604 1000) 899604 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 899604 1000)) rfl rfl

noncomputable def hp793651 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 899604 1000) (Enclosure.sfrac Bool.false 900158 1000) hp793648)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 899604 1000) (Enclosure.sfrac Bool.false 900158 1000) hp793648))

noncomputable def hp793652 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 899604 1000) (Enclosure.sfrac Bool.false 900158 1000) hp793648)) 8348607052700988353101

noncomputable def hp793653 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 899604 1000) (Enclosure.sfrac Bool.false 900158 1000) hp793648)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 899604 1000))

noncomputable def hp793654 := @hp793652 18889465931478580854784 56041924141545412297637 hp763445 (@hp793653 Bool.true 8348607052700988353101 18889465931478580854784 56041924141545412297637 hp763445 (hd4340 (Enclosure.sfrac Bool.false 899604 1000) (Enclosure.sfrac Bool.false 900158 1000) hp793648) hd5082)

noncomputable def hp793655 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 899604 1000) (Enclosure.sfrac Bool.false 900158 1000) hp793648)) 5744317286022241142573

noncomputable def hp793656 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 899604 1000) (Enclosure.sfrac Bool.false 900158 1000) hp793648)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 900158 1000))

noncomputable def hp793657 := @hp793655 9444732965739290427392 hp768505 hp742094 (@hp793656 Bool.false 5744317286022241142573 9444732965739290427392 hp768505 hp742094 (hd4359 (Enclosure.sfrac Bool.false 899604 1000) (Enclosure.sfrac Bool.false 900158 1000) hp793648) hd5083)

noncomputable def hp793658 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 899604 1000) (Enclosure.sfrac Bool.false 900158 1000) hp793648) hp793650 (hp793651 (hp793654 rfl rfl rfl) (hp793657 rfl rfl rfl))

noncomputable def hp793659 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 899604 1000) (Enclosure.sfrac Bool.false 900158 1000) hp793648)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793660 := hp793659 (Enclosure.sfrac Bool.false 899604 1000) 749551 1000 899604 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793661 := hp793660 (@Eq.refl Real (Enclosure.sfrac Bool.false 899604 1000)) rfl rfl rfl rfl

noncomputable def hp793662 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 899604 1000) (Enclosure.sfrac Bool.false 900158 1000) hp793648)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793663 := @hp793662 Bool.true Bool.false 8348607052700988353101 18889465931478580854784 56041924141545412297637 hp763445 556919581 10737418240 1213 10737418240 (@hp793653 Bool.true 8348607052700988353101 18889465931478580854784 56041924141545412297637 hp763445 (hd4340 (Enclosure.sfrac Bool.false 899604 1000) (Enclosure.sfrac Bool.false 900158 1000) hp793648) hd5082)

noncomputable def hp793664 := hp793663 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793665 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 899604 1000) (Enclosure.sfrac Bool.false 900158 1000) hp793648)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793666 := hp793665 (Enclosure.sfrac Bool.false 900158 1000) 749551 1000 900158 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793667 := hp793666 (@Eq.refl Real (Enclosure.sfrac Bool.false 900158 1000)) rfl rfl rfl rfl

noncomputable def hp793668 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 899604 1000) (Enclosure.sfrac Bool.false 900158 1000) hp793648)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793669 := @hp793668 Bool.false Bool.false 5744317286022241142573 9444732965739290427392 hp768505 hp742094 556919581 10737418240 1213 10737418240 (@hp793656 Bool.false 5744317286022241142573 9444732965739290427392 hp768505 hp742094 (hd4359 (Enclosure.sfrac Bool.false 899604 1000) (Enclosure.sfrac Bool.false 900158 1000) hp793648) hd5083)

noncomputable def hp793670 := hp793669 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793672 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 900158 1000) (Enclosure.sfrac Bool.false 901581 1000) 900158 1000 901581 1000

noncomputable def hp793673 := hp793672 (@Eq.refl Real (Enclosure.sfrac Bool.false 900158 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 901581 1000)) rfl rfl rfl

noncomputable def hp793674 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 900158 1000) (Enclosure.sfrac Bool.false 901581 1000) hp793673)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 900158 1000) (Enclosure.sfrac Bool.false 901581 1000) hp793673))

noncomputable def hp793675 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 900158 1000) 900158 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 900158 1000)) rfl rfl

noncomputable def hp793676 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 900158 1000) (Enclosure.sfrac Bool.false 901581 1000) hp793673)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 900158 1000) (Enclosure.sfrac Bool.false 901581 1000) hp793673))

noncomputable def hp793677 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 900158 1000) (Enclosure.sfrac Bool.false 901581 1000) hp793673)) 5744317286022241142573

noncomputable def hp793678 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 900158 1000) (Enclosure.sfrac Bool.false 901581 1000) hp793673)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 900158 1000))

noncomputable def hp793679 := @hp793677 9444732965739290427392 hp768505 hp742094 (@hp793678 Bool.false 5744317286022241142573 9444732965739290427392 hp768505 hp742094 (hd4340 (Enclosure.sfrac Bool.false 900158 1000) (Enclosure.sfrac Bool.false 901581 1000) hp793673) hd5083)

noncomputable def hp793680 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 900158 1000) (Enclosure.sfrac Bool.false 901581 1000) hp793673)) 57388786245359528123709

noncomputable def hp793681 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 900158 1000) (Enclosure.sfrac Bool.false 901581 1000) hp793673)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 901581 1000))

noncomputable def hp793682 := @hp793680 37778931862957161709568 hp768767 hp743845 (@hp793681 Bool.true 57388786245359528123709 37778931862957161709568 hp768767 hp743845 (hd4359 (Enclosure.sfrac Bool.false 900158 1000) (Enclosure.sfrac Bool.false 901581 1000) hp793673) hd5084)

noncomputable def hp793683 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 900158 1000) (Enclosure.sfrac Bool.false 901581 1000) hp793673) hp793675 (hp793676 (hp793679 rfl rfl rfl) (hp793682 rfl rfl rfl))

noncomputable def hp793684 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 900158 1000) (Enclosure.sfrac Bool.false 901581 1000) hp793673)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793685 := hp793684 (Enclosure.sfrac Bool.false 900158 1000) 749551 1000 900158 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793686 := hp793685 (@Eq.refl Real (Enclosure.sfrac Bool.false 900158 1000)) rfl rfl rfl rfl

noncomputable def hp793687 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 900158 1000) (Enclosure.sfrac Bool.false 901581 1000) hp793673)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793688 := @hp793687 Bool.false Bool.false 5744317286022241142573 9444732965739290427392 hp768505 hp742094 556919581 10737418240 1213 10737418240 (@hp793678 Bool.false 5744317286022241142573 9444732965739290427392 hp768505 hp742094 (hd4340 (Enclosure.sfrac Bool.false 900158 1000) (Enclosure.sfrac Bool.false 901581 1000) hp793673) hd5083)

noncomputable def hp793689 := hp793688 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793690 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 900158 1000) (Enclosure.sfrac Bool.false 901581 1000) hp793673)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793691 := hp793690 (Enclosure.sfrac Bool.false 901581 1000) 749551 1000 901581 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793692 := hp793691 (@Eq.refl Real (Enclosure.sfrac Bool.false 901581 1000)) rfl rfl rfl rfl

noncomputable def hp793693 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 900158 1000) (Enclosure.sfrac Bool.false 901581 1000) hp793673)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793694 := @hp793693 Bool.true Bool.false 57388786245359528123709 37778931862957161709568 hp768767 hp743845 556919581 10737418240 1213 10737418240 (@hp793681 Bool.true 57388786245359528123709 37778931862957161709568 hp768767 hp743845 (hd4359 (Enclosure.sfrac Bool.false 900158 1000) (Enclosure.sfrac Bool.false 901581 1000) hp793673) hd5084)

noncomputable def hp793695 := hp793694 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793697 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 901581 1000) (Enclosure.sfrac Bool.false 902846 1000) 901581 1000 902846 1000

noncomputable def hp793698 := hp793697 (@Eq.refl Real (Enclosure.sfrac Bool.false 901581 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 902846 1000)) rfl rfl rfl

noncomputable def hp793699 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 901581 1000) (Enclosure.sfrac Bool.false 902846 1000) hp793698)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 901581 1000) (Enclosure.sfrac Bool.false 902846 1000) hp793698))

noncomputable def hp793700 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 901581 1000) 901581 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 901581 1000)) rfl rfl

noncomputable def hp793701 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 901581 1000) (Enclosure.sfrac Bool.false 902846 1000) hp793698)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 901581 1000) (Enclosure.sfrac Bool.false 902846 1000) hp793698))

noncomputable def hp793702 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 901581 1000) (Enclosure.sfrac Bool.false 902846 1000) hp793698)) 57388786245359528123709

noncomputable def hp793703 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 901581 1000) (Enclosure.sfrac Bool.false 902846 1000) hp793698)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 901581 1000))

noncomputable def hp793704 := @hp793702 37778931862957161709568 hp768767 hp743845 (@hp793703 Bool.true 57388786245359528123709 37778931862957161709568 hp768767 hp743845 (hd4340 (Enclosure.sfrac Bool.false 901581 1000) (Enclosure.sfrac Bool.false 902846 1000) hp793698) hd5084)

noncomputable def hp793705 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 901581 1000) (Enclosure.sfrac Bool.false 902846 1000) hp793698)) 26132554518388758315785

noncomputable def hp793706 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 901581 1000) (Enclosure.sfrac Bool.false 902846 1000) hp793698)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 902846 1000))

noncomputable def hp793707 := @hp793705 37778931862957161709568 174307341680709133092761 hp769024 (@hp793706 Bool.false 26132554518388758315785 37778931862957161709568 174307341680709133092761 hp769024 (hd4359 (Enclosure.sfrac Bool.false 901581 1000) (Enclosure.sfrac Bool.false 902846 1000) hp793698) hd5085)

noncomputable def hp793708 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 901581 1000) (Enclosure.sfrac Bool.false 902846 1000) hp793698) hp793700 (hp793701 (hp793704 rfl rfl rfl) (hp793707 rfl rfl rfl))

noncomputable def hp793709 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 901581 1000) (Enclosure.sfrac Bool.false 902846 1000) hp793698)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793710 := hp793709 (Enclosure.sfrac Bool.false 901581 1000) 749551 1000 901581 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793711 := hp793710 (@Eq.refl Real (Enclosure.sfrac Bool.false 901581 1000)) rfl rfl rfl rfl

noncomputable def hp793712 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 901581 1000) (Enclosure.sfrac Bool.false 902846 1000) hp793698)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793713 := @hp793712 Bool.true Bool.false 57388786245359528123709 37778931862957161709568 hp768767 hp743845 556919581 10737418240 1213 10737418240 (@hp793703 Bool.true 57388786245359528123709 37778931862957161709568 hp768767 hp743845 (hd4340 (Enclosure.sfrac Bool.false 901581 1000) (Enclosure.sfrac Bool.false 902846 1000) hp793698) hd5084)

noncomputable def hp793714 := hp793713 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793715 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 901581 1000) (Enclosure.sfrac Bool.false 902846 1000) hp793698)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793716 := hp793715 (Enclosure.sfrac Bool.false 902846 1000) 749551 1000 902846 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793717 := hp793716 (@Eq.refl Real (Enclosure.sfrac Bool.false 902846 1000)) rfl rfl rfl rfl

noncomputable def hp793718 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 901581 1000) (Enclosure.sfrac Bool.false 902846 1000) hp793698)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793719 := @hp793718 Bool.false Bool.false 26132554518388758315785 37778931862957161709568 174307341680709133092761 hp769024 556919581 10737418240 1213 10737418240 (@hp793706 Bool.false 26132554518388758315785 37778931862957161709568 174307341680709133092761 hp769024 (hd4359 (Enclosure.sfrac Bool.false 901581 1000) (Enclosure.sfrac Bool.false 902846 1000) hp793698) hd5085)

noncomputable def hp793720 := hp793719 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793722 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 902846 1000) (Enclosure.sfrac Bool.false 904111 1000) 902846 1000 904111 1000

noncomputable def hp793723 := hp793722 (@Eq.refl Real (Enclosure.sfrac Bool.false 902846 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 904111 1000)) rfl rfl rfl

noncomputable def hp793724 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 902846 1000) (Enclosure.sfrac Bool.false 904111 1000) hp793723)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 902846 1000) (Enclosure.sfrac Bool.false 904111 1000) hp793723))

noncomputable def hp793725 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 902846 1000) 902846 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 902846 1000)) rfl rfl

noncomputable def hp793726 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 902846 1000) (Enclosure.sfrac Bool.false 904111 1000) hp793723)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 902846 1000) (Enclosure.sfrac Bool.false 904111 1000) hp793723))

noncomputable def hp793727 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 902846 1000) (Enclosure.sfrac Bool.false 904111 1000) hp793723)) 26132554518388758315785

noncomputable def hp793728 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 902846 1000) (Enclosure.sfrac Bool.false 904111 1000) hp793723)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 902846 1000))

noncomputable def hp793729 := @hp793727 37778931862957161709568 174307341680709133092761 hp769024 (@hp793728 Bool.false 26132554518388758315785 37778931862957161709568 174307341680709133092761 hp769024 (hd4340 (Enclosure.sfrac Bool.false 902846 1000) (Enclosure.sfrac Bool.false 904111 1000) hp793723) hd5085)

noncomputable def hp793730 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 902846 1000) (Enclosure.sfrac Bool.false 904111 1000) hp793723)) 104447443071669232417367

noncomputable def hp793731 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 902846 1000) (Enclosure.sfrac Bool.false 904111 1000) hp793723)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 904111 1000))

noncomputable def hp793732 := @hp793730 37778931862957161709568 hp769277 hp741590 (@hp793731 Bool.true 104447443071669232417367 37778931862957161709568 hp769277 hp741590 (hd4359 (Enclosure.sfrac Bool.false 902846 1000) (Enclosure.sfrac Bool.false 904111 1000) hp793723) hd5086)

noncomputable def hp793733 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 902846 1000) (Enclosure.sfrac Bool.false 904111 1000) hp793723) hp793725 (hp793726 (hp793729 rfl rfl rfl) (hp793732 rfl rfl rfl))

noncomputable def hp793734 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 902846 1000) (Enclosure.sfrac Bool.false 904111 1000) hp793723)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793735 := hp793734 (Enclosure.sfrac Bool.false 902846 1000) 749551 1000 902846 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793736 := hp793735 (@Eq.refl Real (Enclosure.sfrac Bool.false 902846 1000)) rfl rfl rfl rfl

noncomputable def hp793737 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 902846 1000) (Enclosure.sfrac Bool.false 904111 1000) hp793723)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793738 := @hp793737 Bool.false Bool.false 26132554518388758315785 37778931862957161709568 174307341680709133092761 hp769024 556919581 10737418240 1213 10737418240 (@hp793728 Bool.false 26132554518388758315785 37778931862957161709568 174307341680709133092761 hp769024 (hd4340 (Enclosure.sfrac Bool.false 902846 1000) (Enclosure.sfrac Bool.false 904111 1000) hp793723) hd5085)

noncomputable def hp793739 := hp793738 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793740 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 902846 1000) (Enclosure.sfrac Bool.false 904111 1000) hp793723)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793741 := hp793740 (Enclosure.sfrac Bool.false 904111 1000) 749551 1000 904111 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793742 := hp793741 (@Eq.refl Real (Enclosure.sfrac Bool.false 904111 1000)) rfl rfl rfl rfl

noncomputable def hp793743 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 902846 1000) (Enclosure.sfrac Bool.false 904111 1000) hp793723)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793744 := @hp793743 Bool.true Bool.false 104447443071669232417367 37778931862957161709568 hp769277 hp741590 556919581 10737418240 1213 10737418240 (@hp793731 Bool.true 104447443071669232417367 37778931862957161709568 hp769277 hp741590 (hd4359 (Enclosure.sfrac Bool.false 902846 1000) (Enclosure.sfrac Bool.false 904111 1000) hp793723) hd5086)

noncomputable def hp793745 := hp793744 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793747 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 904111 1000) (Enclosure.sfrac Bool.false 905375 1000) 904111 1000 905375 1000

noncomputable def hp793748 := hp793747 (@Eq.refl Real (Enclosure.sfrac Bool.false 904111 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 905375 1000)) rfl rfl rfl

noncomputable def hp793749 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 904111 1000) (Enclosure.sfrac Bool.false 905375 1000) hp793748)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 904111 1000) (Enclosure.sfrac Bool.false 905375 1000) hp793748))

noncomputable def hp793750 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 904111 1000) 904111 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 904111 1000)) rfl rfl

noncomputable def hp793751 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 904111 1000) (Enclosure.sfrac Bool.false 905375 1000) hp793748)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 904111 1000) (Enclosure.sfrac Bool.false 905375 1000) hp793748))

noncomputable def hp793752 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 904111 1000) (Enclosure.sfrac Bool.false 905375 1000) hp793748)) 104447443071669232417367

noncomputable def hp793753 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 904111 1000) (Enclosure.sfrac Bool.false 905375 1000) hp793748)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 904111 1000))

noncomputable def hp793754 := @hp793752 37778931862957161709568 hp769277 hp741590 (@hp793753 Bool.true 104447443071669232417367 37778931862957161709568 hp769277 hp741590 (hd4340 (Enclosure.sfrac Bool.false 904111 1000) (Enclosure.sfrac Bool.false 905375 1000) hp793748) hd5086)

noncomputable def hp793755 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 904111 1000) (Enclosure.sfrac Bool.false 905375 1000) hp793748)) 9620814688232979079561

noncomputable def hp793756 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 904111 1000) (Enclosure.sfrac Bool.false 905375 1000) hp793748)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 905375 1000))

noncomputable def hp793757 := @hp793755 4722366482869645213696 hp769544 hp769546 (@hp793756 Bool.false 9620814688232979079561 4722366482869645213696 hp769544 hp769546 (hd4359 (Enclosure.sfrac Bool.false 904111 1000) (Enclosure.sfrac Bool.false 905375 1000) hp793748) hd5091)

noncomputable def hp793758 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 904111 1000) (Enclosure.sfrac Bool.false 905375 1000) hp793748) hp793750 (hp793751 (hp793754 rfl rfl rfl) (hp793757 rfl rfl rfl))

noncomputable def hp793759 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 904111 1000) (Enclosure.sfrac Bool.false 905375 1000) hp793748)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793760 := hp793759 (Enclosure.sfrac Bool.false 904111 1000) 749551 1000 904111 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793761 := hp793760 (@Eq.refl Real (Enclosure.sfrac Bool.false 904111 1000)) rfl rfl rfl rfl

noncomputable def hp793762 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 904111 1000) (Enclosure.sfrac Bool.false 905375 1000) hp793748)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793763 := @hp793762 Bool.true Bool.false 104447443071669232417367 37778931862957161709568 hp769277 hp741590 556919581 10737418240 1213 10737418240 (@hp793753 Bool.true 104447443071669232417367 37778931862957161709568 hp769277 hp741590 (hd4340 (Enclosure.sfrac Bool.false 904111 1000) (Enclosure.sfrac Bool.false 905375 1000) hp793748) hd5086)

noncomputable def hp793764 := hp793763 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793765 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 904111 1000) (Enclosure.sfrac Bool.false 905375 1000) hp793748)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793766 := hp793765 (Enclosure.sfrac Bool.false 905375 1000) 749551 1000 905375 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793767 := hp793766 (@Eq.refl Real (Enclosure.sfrac Bool.false 905375 1000)) rfl rfl rfl rfl

noncomputable def hp793768 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 904111 1000) (Enclosure.sfrac Bool.false 905375 1000) hp793748)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793769 := @hp793768 Bool.false Bool.false 9620814688232979079561 4722366482869645213696 hp769544 hp769546 556919581 10737418240 1213 10737418240 (@hp793756 Bool.false 9620814688232979079561 4722366482869645213696 hp769544 hp769546 (hd4359 (Enclosure.sfrac Bool.false 904111 1000) (Enclosure.sfrac Bool.false 905375 1000) hp793748) hd5091)

noncomputable def hp793770 := hp793769 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793772 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 905375 1000) (Enclosure.sfrac Bool.false 906639 1000) 905375 1000 906639 1000

noncomputable def hp793773 := hp793772 (@Eq.refl Real (Enclosure.sfrac Bool.false 905375 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 906639 1000)) rfl rfl rfl

noncomputable def hp793774 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 905375 1000) (Enclosure.sfrac Bool.false 906639 1000) hp793773)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 905375 1000) (Enclosure.sfrac Bool.false 906639 1000) hp793773))

noncomputable def hp793775 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 905375 1000) 905375 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 905375 1000)) rfl rfl

noncomputable def hp793776 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 905375 1000) (Enclosure.sfrac Bool.false 906639 1000) hp793773)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 905375 1000) (Enclosure.sfrac Bool.false 906639 1000) hp793773))

noncomputable def hp793777 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 905375 1000) (Enclosure.sfrac Bool.false 906639 1000) hp793773)) 9620814688232979079561

noncomputable def hp793778 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 905375 1000) (Enclosure.sfrac Bool.false 906639 1000) hp793773)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 905375 1000))

noncomputable def hp793779 := @hp793777 4722366482869645213696 hp769544 hp769546 (@hp793778 Bool.false 9620814688232979079561 4722366482869645213696 hp769544 hp769546 (hd4340 (Enclosure.sfrac Bool.false 905375 1000) (Enclosure.sfrac Bool.false 906639 1000) hp793773) hd5091)

noncomputable def hp793780 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 905375 1000) (Enclosure.sfrac Bool.false 906639 1000) hp793773)) 652345635981816454823077

noncomputable def hp793781 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 905375 1000) (Enclosure.sfrac Bool.false 906639 1000) hp793773)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 906639 1000))

noncomputable def hp793782 := @hp793780 151115727451828646838272 hp769801 hp755229 (@hp793781 Bool.true 652345635981816454823077 151115727451828646838272 hp769801 hp755229 (hd4359 (Enclosure.sfrac Bool.false 905375 1000) (Enclosure.sfrac Bool.false 906639 1000) hp793773) hd5092)

noncomputable def hp793783 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 905375 1000) (Enclosure.sfrac Bool.false 906639 1000) hp793773) hp793775 (hp793776 (hp793779 rfl rfl rfl) (hp793782 rfl rfl rfl))

noncomputable def hp793784 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 905375 1000) (Enclosure.sfrac Bool.false 906639 1000) hp793773)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793785 := hp793784 (Enclosure.sfrac Bool.false 905375 1000) 749551 1000 905375 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793786 := hp793785 (@Eq.refl Real (Enclosure.sfrac Bool.false 905375 1000)) rfl rfl rfl rfl

noncomputable def hp793787 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 905375 1000) (Enclosure.sfrac Bool.false 906639 1000) hp793773)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793788 := @hp793787 Bool.false Bool.false 9620814688232979079561 4722366482869645213696 hp769544 hp769546 556919581 10737418240 1213 10737418240 (@hp793778 Bool.false 9620814688232979079561 4722366482869645213696 hp769544 hp769546 (hd4340 (Enclosure.sfrac Bool.false 905375 1000) (Enclosure.sfrac Bool.false 906639 1000) hp793773) hd5091)

noncomputable def hp793789 := hp793788 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793790 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 905375 1000) (Enclosure.sfrac Bool.false 906639 1000) hp793773)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793791 := hp793790 (Enclosure.sfrac Bool.false 906639 1000) 749551 1000 906639 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793792 := hp793791 (@Eq.refl Real (Enclosure.sfrac Bool.false 906639 1000)) rfl rfl rfl rfl

noncomputable def hp793793 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 905375 1000) (Enclosure.sfrac Bool.false 906639 1000) hp793773)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793794 := @hp793793 Bool.true Bool.false 652345635981816454823077 151115727451828646838272 hp769801 hp755229 556919581 10737418240 1213 10737418240 (@hp793781 Bool.true 652345635981816454823077 151115727451828646838272 hp769801 hp755229 (hd4359 (Enclosure.sfrac Bool.false 905375 1000) (Enclosure.sfrac Bool.false 906639 1000) hp793773) hd5092)

noncomputable def hp793795 := hp793794 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl
open Zeta.Certificates
noncomputable def certificatePairs : List (Σ' I : ZIntervalRS, I.Certified) := [(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 891448 1000) (Enclosure.sfrac Bool.false 892716 1000) hp793498) (hp793499 (hp793508 (hp793511 (hp793514 rfl rfl)) (hp793517 (hp793520 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 892716 1000) (Enclosure.sfrac Bool.false 893984 1000) hp793523) (hp793524 (hp793533 (hp793536 (hp793539 rfl rfl)) (hp793542 (hp793545 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 893984 1000) (Enclosure.sfrac Bool.false 895251 1000) hp793548) (hp793549 (hp793558 (hp793561 (hp793564 rfl rfl)) (hp793567 (hp793570 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 895251 1000) (Enclosure.sfrac Bool.false 896518 1000) hp793573) (hp793574 (hp793583 (hp793586 (hp793589 rfl rfl)) (hp793592 (hp793595 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 896518 1000) (Enclosure.sfrac Bool.false 898496 1000) hp793598) (hp793599 (hp793608 (hp793611 (hp793614 rfl rfl)) (hp793617 (hp793620 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 898496 1000) (Enclosure.sfrac Bool.false 899604 1000) hp793623) (hp793624 (hp793633 (hp793636 (hp793639 rfl rfl)) (hp793642 (hp793645 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 899604 1000) (Enclosure.sfrac Bool.false 900158 1000) hp793648) (hp793649 (hp793658 (hp793661 (hp793664 rfl rfl)) (hp793667 (hp793670 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 900158 1000) (Enclosure.sfrac Bool.false 901581 1000) hp793673) (hp793674 (hp793683 (hp793686 (hp793689 rfl rfl)) (hp793692 (hp793695 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 901581 1000) (Enclosure.sfrac Bool.false 902846 1000) hp793698) (hp793699 (hp793708 (hp793711 (hp793714 rfl rfl)) (hp793717 (hp793720 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 902846 1000) (Enclosure.sfrac Bool.false 904111 1000) hp793723) (hp793724 (hp793733 (hp793736 (hp793739 rfl rfl)) (hp793742 (hp793745 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 904111 1000) (Enclosure.sfrac Bool.false 905375 1000) hp793748) (hp793749 (hp793758 (hp793761 (hp793764 rfl rfl)) (hp793767 (hp793770 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 905375 1000) (Enclosure.sfrac Bool.false 906639 1000) hp793773) (hp793774 (hp793783 (hp793786 (hp793789 rfl rfl)) (hp793792 (hp793795 rfl rfl)))))]

theorem solution : Zeta.Certificates.BatchSpec 12 891448 1000 906639 1000 :=
  ⟨CertifiedZeroIntervals.ofCertifiedRS certificatePairs (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.singleton _)))))))))))), rfl, rfl, rfl⟩
#print axioms solution
