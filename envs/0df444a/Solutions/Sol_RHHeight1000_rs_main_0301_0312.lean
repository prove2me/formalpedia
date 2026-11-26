-- Prove2me | solution 1 for RHHeight1000.rs_main_0301_0312
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:15:02.27877+00:00
-- url     : https://prove2.me/submissions/57c10cfc-db34-43e9-93d7-fb5febc62070

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

noncomputable abbrev RSCompact.c2 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi) 

noncomputable abbrev RSCompact.c3 := (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup) (@RCLike.toInnerProductSpaceReal Real Real.instRCLike)) 

noncomputable abbrev RSCompact.c4 := (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) 

noncomputable abbrev RSCompact.c5 := (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup) (@RCLike.toInnerProductSpaceReal Real Real.instRCLike)) 

noncomputable abbrev RSCompact.c6 := (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup) (@RCLike.toInnerProductSpaceReal Real Real.instRCLike)) 

noncomputable abbrev RSCompact.c7 := (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup) (@RCLike.toInnerProductSpaceReal Real Real.instRCLike)) 

noncomputable abbrev RSCompact.c8 := (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup) (@RCLike.toInnerProductSpaceReal Real Real.instRCLike)) 

noncomputable abbrev RSCompact.c9 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) RSCompact.c2 Real.pi) 

noncomputable abbrev RSCompact.c10 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) RSCompact.c2 Real.pi) 

noncomputable abbrev RSCompact.c11 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) RSCompact.c2 Real.pi) 

noncomputable def RS301to312.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS301to312.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS301to312.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS301to312.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS301to312.d2 a b h 

theorem RS301to312.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS301to312.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS301to312.d3 a b h)) 

noncomputable def Ns300p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns300p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns300p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns300p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns300p0 Ns300p1 Ns300p2 Ns300p1 307286088 268435456 1 70560000 307286088 268435456 1 70560000 153643044 134217728 2 134217728 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns300p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns300p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns300p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns300p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns300p8 := nat_lit 167537954069964697925743468333314178468718661948561187618563575975392713740913527107727581163208035826476740967700482432525301063254420572874757592895482956004842597348203117269212172556829666669574421653274845612596416189641484794702002223261246862056663160605878293700340502480877986491439034432953223334258717026053687371824342493299510132312376251152844516906794910572262907940062760396663270105627554083664899640691826599584783763757814813433640133591539937449421955686657622469485188711283992428713614179785896055117030632677201478317872225272595773536303110412989181984739022579128493081560758017763072115692678596043664844667144619713966763611484179303468167142547433165016751768184247559143333542643815355903304572487929375 

noncomputable def Ns300p9 := nat_lit 17907736863639440849562382641391758203535690054199171304015283257442503423240620144819838407313611418261944516207295868563739563278604805791797182761045687776939279949642059267526948014748996956777332184087524644234759874591635243045607722412471722018588244283882362848653445974523544951031470230725674276297342086185092985546835544820091590454230569790847977790484558207349923322458845585052164126500435851662252152223728079705692133047658564669873831757357628115566356048471439549797170528303905720944834637690907185213991407615774042056720704508980680095051114888612186461088301140868302968264130481206655302741383410655080008578156649725227045954510069588220729495895148666460653631514375880874422615237249871322129146554264800 

noncomputable def Ns300p10 := nat_lit 55164646516618494962085419356369025784335016154267579706247610053041231157772817011486486467101704279863254798704146668052276438579475100451766223896220272709675360577301802978530276301158911649961092601279696986330335403118086533522541958716560166657634553390183479955483588238249446822384543398154260439705049143284278540285021213103458182619368483938376641172730818250587232036579805400979202432024046862170503602539341971086573372247299262086029843105216008583038025403798224342134620653974939981235680083776396058604459065501719125356177784467570909658245422960948263734871602033841948787585406240093531041217463298165642337705122589129757920995868559518021463265498464182174549661735402095023640043996665674913376875 

noncomputable def Ns300p11 := BSN.log_dyadic_bound Ns300p6 Ns300p7 15 14 Ns300p8 268435456 70560000 Ns300p9 Ns300p10 307286088 Ns300p4 Ns300p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns300p6) (BSN.artanhQ Ns300p7) 0 14 Ns300p9 Ns300p8 Ns300p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns300p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns300p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns300p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns300p15 := nat_lit 167537954069966963268140139327979112712430526945422964221951926912223381190141639739514890494967825643602350173964944759828460064784215684919760383437959917620844610857567326816719640593037578236900835917107172977527392439886629774248115214831425484905681376157923696414882114961796820014026232307332015059110330001516939277521159573995394989771587717775443426002499543257897301982481613760098955890450106043861450716722534643739571053080256776912576113428445260435254713579381797931690799491102381747484553243404562568585572234105168360737285205910186933811836504830286397217473365026331067977496463917110493303316865058355012304571237619413071097245713770677768486493924969821719264401216877841676972336093778875903304572487929375 

noncomputable def Ns300p16 := nat_lit 17907736863639702486765313263906285882628955290251965205176678923530777959693011244026517850256414903756943142851250712732214241881959351517241344993825585048584379523049477943740273636414656012170312373198803997844271825165684859407921203335666024680974464565759223251918458072775203410604089667122984485578465112081892102496937045858735135721609691262763214794451343726045584198128451069547586972080574568545086657023793200560105564573365716615162566961587407171758966967827997201380802107846920231945878242774600967607639551032178207663699700360114112068650063802902647517702890145150192721997537569966984346993833704449560383184487996362781528900358997452380059737141488304159449328022742959995775545894292303322129146554264800 

noncomputable def Ns300p17 := nat_lit 55164646516619937449385584700664297411818070214438189962773666351465523500358685366424500506990751111492356556545320273548942244833046464529601272738875466881799996765940232256588350019911833156887888425998391295014189841212513610526066550079316346993943774342801096070086869790972589246312728227659319758310961510342377923950694747797317942483020440897997204711883064182772445608288320382376665481938194224815739627075458138172195220395246294556718284728034954178416253903237031389214179719385823921869528509431462690683227358218086518156757026652846493301460983550768858152506145788622699720737745394141184245149692548799188169247529408201840608223422296381897323845616153036586108326210125693898345963996665674913376875 

noncomputable def Ns300p18 := BSN.log_dyadic_bound Ns300p13 Ns300p14 15 14 Ns300p15 268435456 70560000 Ns300p16 Ns300p17 307286088 Ns300p12 Ns300p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns300p13) (BSN.artanhQ Ns300p14) 0 14 Ns300p16 Ns300p15 Ns300p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns300p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 153643044 134217728 2 134217728 38410761 33554432 1 67108864 (Ns300p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns300p0 Ns300p1 307286088 268435456 1 70560000 Bool.false (BSN.logfrac_isNear Ns300p4 Ns300p5 1 Ns300p0 Ns300p1 307286088 268435456 70560000 rfl rfl rfl (Ns300p11 rfl))) (BSN.isNear_log_sfrac Ns300p2 Ns300p1 307286088 268435456 1 70560000 Bool.false (BSN.logfrac_isNear Ns300p12 Ns300p5 1 Ns300p2 Ns300p1 307286088 268435456 70560000 rfl rfl rfl (Ns300p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS301to312.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 67108864 := Ns300p19 

noncomputable def Ns300p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 16777216 4410000 385100712855 135135 11629079 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz803 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz594 := qz803

noncomputable abbrev qz317 := qz594

noncomputable abbrev qz0 := qz317

theorem RS301to312.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 11629079 16777216 1 4410000 := BSN.isNear_log_sfrac 2 1 11629079 16777216 1 4410000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 11629079 16777216 4410000 rfl rfl rfl (Ns300p20 rfl)) 

theorem RS301to312.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 186065264 268435456 61 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 11629079 16777216 1 4410000 186065264 268435456 61 268435456 RS301to312.d6 rfl 

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz595 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz596 := (@Nat.cast Real Real.instNatCast 2)

noncomputable def Ns300p21 := @Enclosure.Real.IsNear.inv_image qz595 47453133 33554432 1 33554432 11863282 11863284 16777216 (@Enclosure.Real.IsNear.of_eq qz595 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz596 qz318)) Bool.false 47453133 33554432 1 33554432 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz596 qz318)) Bool.false 47453133 33554432 1 33554432 47453133 33554432 1 33554432 (BSN.sqrt_enclosure 2 1 23726566 23726567 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz597 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS301to312.d8 : Enclosure.Real.IsNear qz597 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz597 Bool.false 23726566 33554432 2 33554432 11863283 16777216 1 16777216 (Ns300p21 rfl rfl) rfl 

theorem RS301to312.d9 : Enclosure.Real.IsNear qz597 Bool.false 189812528 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz597 Bool.false 11863283 16777216 1 16777216 189812528 268435456 16 268435456 RS301to312.d8 rfl 

noncomputable def Ns300p22 := BSN.log_dyadic_bound 1 2 13 12 132638213186519040000 16777216 4410000 13079757671720842725 316234143225 18431655 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz319 := (Enclosure.sfrac Bool.false 3 1)

theorem RS301to312.d10 : Enclosure.Real.IsNear (Real.log qz319) Bool.false 18431655 16777216 1 4410000 := BSN.isNear_log_sfrac 3 1 18431655 16777216 1 4410000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 18431655 16777216 4410000 rfl rfl rfl (Ns300p22 rfl)) 

theorem RS301to312.d11 : Enclosure.Real.IsNear (Real.log qz319) Bool.false 294906480 268435456 61 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz319) Bool.false 18431655 16777216 1 4410000 294906480 268435456 61 268435456 RS301to312.d10 rfl 

noncomputable abbrev qz598 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz599 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns300p23 := @Enclosure.Real.IsNear.inv_image qz598 58117981 33554432 1 33554432 9686330 9686331 16777216 (@Enclosure.Real.IsNear.of_eq qz598 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz599 qz318)) Bool.false 58117981 33554432 1 33554432 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz599 qz318)) Bool.false 58117981 33554432 1 33554432 58117981 33554432 1 33554432 (BSN.sqrt_enclosure 3 1 29058990 29058991 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz600 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS301to312.d12 : Enclosure.Real.IsNear qz600 Bool.false 19372661 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz600 Bool.false 19372661 33554432 1 33554432 19372661 33554432 1 33554432 (Ns300p23 rfl rfl) rfl 

theorem RS301to312.d13 : Enclosure.Real.IsNear qz600 Bool.false 154981288 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz600 Bool.false 19372661 33554432 1 33554432 154981288 268435456 8 268435456 RS301to312.d12 rfl 

noncomputable def Ns300p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns300p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns300p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns300p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns300p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns300p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns300p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns300p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns300p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns300p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns300p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns300p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns300p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns300p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns300p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns300p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns300p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns300p25 Ns300p26 Ns300p27 Ns300p28 200200021673987500790625 Ns300p29 Ns300p30 Ns300p31 Ns300p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns300p32 Ns300p33 151412625 Ns300p34 Ns300p35 1322214852783825 Ns300p27 Ns300p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns300p32 Ns300p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns300p34 Ns300p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns300p36 Ns300p37 1267389585 Ns300p38 Ns300p39 1927077560082675 Ns300p29 Ns300p30 Ns300p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns300p36 Ns300p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns300p38 Ns300p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz601 := (@Nat.cast Real Real.instNatCast 5)

theorem RS301to312.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz601)) Bool.false Ns300p24 Ns300p25 1 Ns300p26 := Ns300p40 rfl rfl rfl 

noncomputable def Ns300p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns300p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns300p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns300p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns300p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns300p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns300p25 Ns300p26 Ns300p42 Ns300p43 9945 Ns300p44 Ns300p45 65835 Ns300p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns300p42 Ns300p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns300p44 Ns300p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS301to312.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns300p41 Ns300p25 1 Ns300p26 := Ns300p46 rfl 

noncomputable def Ns300p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns300p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS301to312.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns300p47 Ns300p25 1 Ns300p48 := BSN.pi_combine Ns300p24 Ns300p41 Ns300p25 Ns300p26 Ns300p48 Ns300p47 rfl rfl rfl rfl RS301to312.d14 RS301to312.d15 

theorem RS301to312.d17 : Enclosure.Real.IsNear Real.pi Bool.false 14148475504056880 4503599627370496 1 4503599627370496 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns300p47 Ns300p25 1 Ns300p48 14148475504056880 4503599627370496 1 4503599627370496 RS301to312.d16 rfl 

noncomputable def Ns300p49 := nat_lit 147443727375074537121690809726715087890625 

noncomputable def Ns300p50 := nat_lit 22889945643899497138335355216896171420000 

noncomputable def Ns300p51 := nat_lit 355592320898650075318906513310625 

noncomputable def Ns300p52 := BSN.log_dyadic_bound 3 5 17 16 Ns300p49 16777216 4410000 Ns300p50 Ns300p51 23258159 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 3) (BSN.artanhQ 5) 0 16 Ns300p50 Ns300p49 Ns300p51 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz602 := (Enclosure.sfrac Bool.false 4 1)

noncomputable abbrev qz320 := qz602

theorem RS301to312.d18 : Enclosure.Real.IsNear (Real.log qz320) Bool.false 23258159 16777216 1 4410000 := BSN.isNear_log_sfrac 4 1 23258159 16777216 1 4410000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 23258159 16777216 4410000 rfl rfl rfl (Ns300p52 rfl)) 

theorem RS301to312.d19 : Enclosure.Real.IsNear (Real.log qz320) Bool.false 372130544 268435456 61 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz320) Bool.false 23258159 16777216 1 4410000 372130544 268435456 61 268435456 RS301to312.d18 rfl 

noncomputable abbrev qz603 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz604 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns300p53 := @Enclosure.Real.IsNear.inv_image qz603 67108865 33554432 1 33554432 8388607 8388608 16777216 (@Enclosure.Real.IsNear.of_eq qz603 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz604 qz318)) Bool.false 67108865 33554432 1 33554432 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz604 qz318)) Bool.false 67108865 33554432 1 33554432 67108865 33554432 1 33554432 (BSN.sqrt_enclosure 4 1 33554432 33554433 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz605 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS301to312.d20 : Enclosure.Real.IsNear qz605 Bool.false 16777215 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz605 Bool.false 16777215 33554432 1 33554432 16777215 33554432 1 33554432 (Ns300p53 rfl rfl) rfl 

theorem RS301to312.d21 : Enclosure.Real.IsNear qz605 Bool.false 134217720 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz605 Bool.false 16777215 33554432 1 33554432 134217720 268435456 8 268435456 RS301to312.d20 rfl 

noncomputable def Ns300p54 := nat_lit 159424323765613091421820433543167414255940625 

noncomputable def Ns300p55 := nat_lit 33013339099500162583200499609923570567289500 

noncomputable def Ns300p56 := nat_lit 351657888879851162997374110924800000 

noncomputable def Ns300p57 := nat_lit 2289063575687431840984260 

noncomputable def Ns300p58 := nat_lit 3325435793429257756623375 

noncomputable def Ns300p59 := BSN.log_dyadic_bound 2 3 21 20 Ns300p54 16777216 4410000 Ns300p55 Ns300p56 27001887 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 20 10 9927050056596826020 47940881637414340575 686533194547200 Ns300p57 Ns300p58 512222703392784384000 Ns300p55 Ns300p54 Ns300p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 10 20 Ns300p57 Ns300p58 512222703392784384000 rfl rfl rfl rfl)) rfl rfl 

theorem RS301to312.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 4410000 := BSN.isNear_log_sfrac 5 1 27001887 16777216 1 4410000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 27001887 16777216 4410000 rfl rfl rfl (Ns300p59 rfl rfl)) 

theorem RS301to312.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 432030192 268435456 61 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 4410000 432030192 268435456 61 268435456 RS301to312.d22 rfl 

noncomputable abbrev qz606 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns300p60 := @Enclosure.Real.IsNear.inv_image qz606 75029991 33554432 1 33554432 7502998 7503000 16777216 (@Enclosure.Real.IsNear.of_eq qz606 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz601 qz318)) Bool.false 75029991 33554432 1 33554432 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz601 qz318)) Bool.false 75029991 33554432 1 33554432 75029991 33554432 1 33554432 (BSN.sqrt_enclosure 5 1 37514995 37514996 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz607 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS301to312.d24 : Enclosure.Real.IsNear qz607 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz607 Bool.false 15005998 33554432 2 33554432 7502999 16777216 1 16777216 (Ns300p60 rfl rfl) rfl 

theorem RS301to312.d25 : Enclosure.Real.IsNear qz607 Bool.false 120047984 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz607 Bool.false 7502999 16777216 1 16777216 120047984 268435456 16 268435456 RS301to312.d24 rfl 

noncomputable def Ns300p61 := BSN.log_dyadic_bound 2 10 5 4 94500000000 16777216 4410000 1291130880 26880 6802575 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz608 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz318)

theorem RS301to312.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 50000000441 220500000000000000 := BSN.isNear_log_sfrac 6 1 4034683545132279 2251799813685248 50000000441 220500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz608) Bool.false 1083052117253279893684224 604462909807314587353088 1000000008820000 4410000000000000000000 4034683545132279 2251799813685248 50000000441 220500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 6802575 16777216 24973259072661432 36028797018963968 4410000 1000000000000000 rfl rfl rfl rfl (Ns300p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS301to312.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 480971758 268435456 62 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 50000000441 220500000000000000 480971758 268435456 62 268435456 RS301to312.d26 rfl 

noncomputable abbrev qz609 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns300p62 := @Enclosure.Real.IsNear.inv_image qz609 82191237 33554432 1 33554432 6849269 6849270 16777216 (@Enclosure.Real.IsNear.of_eq qz609 (Real.sqrt qz608) Bool.false 82191237 33554432 1 33554432 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz608) Bool.false 82191237 33554432 1 33554432 82191237 33554432 1 33554432 (BSN.sqrt_enclosure 6 1 41095618 41095619 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz610 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS301to312.d28 : Enclosure.Real.IsNear qz610 Bool.false 13698539 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz610 Bool.false 13698539 33554432 1 33554432 13698539 33554432 1 33554432 (Ns300p62 rfl rfl) rfl 

theorem RS301to312.d29 : Enclosure.Real.IsNear qz610 Bool.false 109588312 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz610 Bool.false 13698539 33554432 1 33554432 109588312 268435456 8 268435456 RS301to312.d28 rfl 

noncomputable def Ns300p63 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 16777216 4410000 11010900719820672 5524329195 9388794 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz611 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz318)

theorem RS301to312.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 50000000441 220500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 50000000441 220500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz611) Bool.false 1176230476650867868041216 604462909807314587353088 1000000008820000 4410000000000000000000 4381799983422711 2251799813685248 50000000441 220500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 9388794 16777216 24973259072661432 36028797018963968 4410000 1000000000000000 rfl rfl rfl rfl (Ns300p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS301to312.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 522351262 268435456 62 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 50000000441 220500000000000000 522351262 268435456 62 268435456 RS301to312.d30 rfl 

noncomputable abbrev qz612 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns300p64 := @Enclosure.Real.IsNear.inv_image qz612 88776683 33554432 1 33554432 6341191 6341192 16777216 (@Enclosure.Real.IsNear.of_eq qz612 (Real.sqrt qz611) Bool.false 88776683 33554432 1 33554432 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz611) Bool.false 88776683 33554432 1 33554432 88776683 33554432 1 33554432 (BSN.sqrt_enclosure 7 1 44388341 44388342 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz613 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS301to312.d32 : Enclosure.Real.IsNear qz613 Bool.false 12682383 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz613 Bool.false 12682383 33554432 1 33554432 12682383 33554432 1 33554432 (Ns300p64 rfl rfl) rfl 

theorem RS301to312.d33 : Enclosure.Real.IsNear qz613 Bool.false 101459064 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz613 Bool.false 12682383 33554432 1 33554432 101459064 268435456 8 268435456 RS301to312.d32 rfl 

noncomputable def Ns300p65 := nat_lit 1256945285058001618599936 

noncomputable def Ns300p66 := BSN.log_dyadic_bound 0 16 1 0 1 16777216 4410000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz321 := (Enclosure.sfrac Bool.false 8 1)

noncomputable abbrev qz614 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz318)

theorem RS301to312.d34 : Enclosure.Real.IsNear (Real.log qz321) Bool.false 9364972152248037 4503599627370496 100000001323 441000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 100000001323 441000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz614) Bool.false Ns300p65 604462909807314587353088 1000000013230000 4410000000000000000000 9364972152248037 4503599627370496 100000001323 441000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 16777216 24973259072661432 36028797018963968 4410000 1000000000000000 rfl rfl rfl rfl (Ns300p66 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS301to312.d35 : Enclosure.Real.IsNear (Real.log qz321) Bool.false 558195838 268435456 62 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz321) Bool.false 9364972152248037 4503599627370496 100000001323 441000000000000000 558195838 268435456 62 268435456 RS301to312.d34 rfl 

noncomputable abbrev qz615 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns300p67 := @Enclosure.Real.IsNear.inv_image qz615 94906265 33554432 1 33554432 5931641 5931642 16777216 (@Enclosure.Real.IsNear.of_eq qz615 (Real.sqrt qz614) Bool.false 94906265 33554432 1 33554432 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz614) Bool.false 94906265 33554432 1 33554432 94906265 33554432 1 33554432 (BSN.sqrt_enclosure 8 1 47453132 47453133 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz616 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS301to312.d36 : Enclosure.Real.IsNear qz616 Bool.false 11863283 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz616 Bool.false 11863283 33554432 1 33554432 11863283 33554432 1 33554432 (Ns300p67 rfl rfl) rfl 

theorem RS301to312.d37 : Enclosure.Real.IsNear qz616 Bool.false 94906264 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz616 Bool.false 11863283 33554432 1 33554432 94906264 268435456 8 268435456 RS301to312.d36 rfl 

noncomputable def Ns300p68 := nat_lit 1328140746012062765809664 

noncomputable def Ns300p69 := BSN.log_dyadic_bound 1 17 3 2 1252815 16777216 4410000 1448 3 1976071 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz804 := (Enclosure.sfrac Bool.false 9 1)

noncomputable abbrev qz617 := qz804

noncomputable abbrev qz322 := qz617

noncomputable abbrev qz1 := qz322

noncomputable abbrev qz618 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz318)

theorem RS301to312.d38 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 9895419672221413 4503599627370496 100000001323 441000000000000000 := BSN.isNear_log_sfrac 9 1 9895419672221413 4503599627370496 100000001323 441000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz618) Bool.false Ns300p68 604462909807314587353088 1000000013230000 4410000000000000000000 9895419672221413 4503599627370496 100000001323 441000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 1976071 16777216 24973259072661432 36028797018963968 4410000 1000000000000000 rfl rfl rfl rfl (Ns300p69 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS301to312.d39 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 589812974 268435456 62 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 9895419672221413 4503599627370496 100000001323 441000000000000000 589812974 268435456 62 268435456 RS301to312.d38 rfl 

noncomputable abbrev qz619 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns300p70 := @Enclosure.Real.IsNear.inv_image qz619 100663297 33554432 1 33554432 5592405 5592406 16777216 (@Enclosure.Real.IsNear.of_eq qz619 (Real.sqrt qz618) Bool.false 100663297 33554432 1 33554432 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz618) Bool.false 100663297 33554432 1 33554432 100663297 33554432 1 33554432 (BSN.sqrt_enclosure 9 1 50331648 50331649 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz620 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS301to312.d40 : Enclosure.Real.IsNear qz620 Bool.false 11184811 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz620 Bool.false 11184811 33554432 1 33554432 11184811 33554432 1 33554432 (Ns300p70 rfl rfl) rfl 

theorem RS301to312.d41 : Enclosure.Real.IsNear qz620 Bool.false 89478488 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz620 Bool.false 11184811 33554432 1 33554432 89478488 268435456 8 268435456 RS301to312.d40 rfl 

theorem RS301to312.d42 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz805 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz621 := qz805

noncomputable abbrev qz323 := qz621

noncomputable abbrev qz2 := qz323

noncomputable abbrev qz324 := (Enclosure.Real.IsNear.const Bool.false 2 1)

theorem RS301to312.d43 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 qz324 RS301to312.d42 rfl 

noncomputable abbrev qz325 := (@Inv.inv Real Real.instInv qz621)

noncomputable abbrev qz3 := qz325

theorem RS301to312.d44 : Enclosure.Real.IsNear qz3 Bool.false 5340353 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 5340353 33554432 1 33554432 5340353 33554432 1 33554432 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 2670176 2670177 16777216 RS301to312.d43 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns300p71 := nat_lit 347093936490918923206656000 

noncomputable def Ns300p72 := nat_lit 682097716581042958485587755008 

noncomputable abbrev qz806 := (Enclosure.sfrac Bool.false 615476 1000)

noncomputable abbrev qz622 := qz806

noncomputable abbrev qz326 := qz622

noncomputable abbrev qz4 := qz326

noncomputable abbrev qz807 := (@instHMul Real Real.instMul)

noncomputable abbrev qz623 := qz807

noncomputable abbrev qz327 := qz623

noncomputable abbrev qz5 := qz327

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 9)

noncomputable abbrev qz808 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 615476 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz624 := qz808

noncomputable abbrev qz328 := qz624

noncomputable abbrev qz7 := qz328

noncomputable abbrev qz625 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz8 := qz625

noncomputable abbrev qz809 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 615476 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz626 := qz809

noncomputable abbrev qz329 := qz626

noncomputable abbrev qz9 := qz329

noncomputable abbrev qz627 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz330 := (@HPow.hPow Real Real Real qz627 qz7 qz8)

noncomputable def Ns300p73 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz330) (Zeta.RiemannSiegel.correction qz9)) 66219655 134217728 151547 134217728 4237563912091570389329 18889465931478580854784 2965872649622653110089 Ns300p71 Ns300p72 

noncomputable def Ns300p74 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 615476 1000 112 158 268435456 134217728 4503599627370496 Bool.false 296003779591 2418 

noncomputable def Ns300p75 := Ns300p74 558195838 62 94906264 8 589812974 62 89478488 8 Bool.true 88583767 123655 Bool.true 326730032 Bool.true 390076728 14148475504056880 1 Bool.false 92961196 Bool.false Bool.false 31507899 Bool.true Bool.true 66219655 

noncomputable def Ns300p76 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 615476 1000 0 60 268435456 134217728 4503599627370496 Bool.false 296003779591 2418 

noncomputable def Ns300p77 := Ns300p76 480971758 62 109588312 8 522351262 62 101459064 8 Bool.true 274509892 91733 Bool.true 22794135 Bool.true 191440043 14148475504056880 1 Bool.false 267468258 Bool.false Bool.false 203015568 Bool.false Bool.true 88583767 

noncomputable def Ns300p78 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 615476 1000 158 71 268435456 134217728 4503599627370496 Bool.false 296003779591 2418 

noncomputable def Ns300p79 := Ns300p78 372130544 61 134217720 8 432030192 61 120047984 16 Bool.true 304542997 53852 Bool.false 344487225 Bool.false 161887732 14148475504056880 1 Bool.false 76111624 Bool.true Bool.false 152251445 Bool.false Bool.true 274509892 

noncomputable def Ns300p80 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 615476 1000 430 271 268435456 134217728 4503599627370496 Bool.false 296003779591 2418 

noncomputable def Ns300p81 := Ns300p80 186065264 61 189812528 16 294906480 61 154981288 8 Bool.true 268435320 2493 Bool.false 172381010 Bool.false 226755846 14148475504056880 1 Bool.false 214962676 Bool.true Bool.false 200734094 Bool.false Bool.true 304542997 

noncomputable def Ns300p82 := nat_lit 1158503495565285044775792446120881619832885762215437 

noncomputable def Ns300p83 := nat_lit 1050606227187316692106206975869742145477804032000 

noncomputable def Ns300p84 := nat_lit 42393334375984504764472389140480000 

noncomputable def Ns300p85 := nat_lit 156552527425783379689783897380492410880 

noncomputable abbrev qz10 := (@Eq.refl Real qz326)

noncomputable def Ns300p86 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 615476 1000 1515243826304 16000000 1230952 4000 2000 Ns300p84 Ns300p85 qz10 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns300p87 := nat_lit 12147789613658643311108213399836495653978880210008140677120 

noncomputable abbrev qz810 := (@instHSub Real Real.instSub)

noncomputable abbrev qz628 := qz810

noncomputable abbrev qz331 := qz628

noncomputable abbrev qz11 := qz331

noncomputable abbrev qz629 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz630 := (@HMul.hMul Real Real Real qz807 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz631 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz332 := (@HMul.hMul Real Real Real qz623 qz629 (@HSub.hSub Real Real Real qz628 qz630 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz631 (@Nat.cast Real Real.instNatCast 1230952)))))

noncomputable abbrev qz632 := (Real.log (Enclosure.sfrac Bool.false 1515243826304 16000000))

noncomputable abbrev qz633 := (Enclosure.sfrac Bool.false 615476 2000)

noncomputable abbrev qz12 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 615476 4000) qz632) qz332) qz633)

noncomputable abbrev qz333 := (@HSub.hSub Real Real Real qz11 qz12 (@HMul.hMul Real Real Real qz5 qz633 (Real.log Real.pi)))

noncomputable def Ns300p88 := @Enclosure.Real.IsNear.addLit_ft_p qz333 (Enclosure.sfrac Bool.true Ns300p84 Ns300p85) 77595633852562556349 70368744177664000 82978205746699889 9216000000000000000000 Ns300p84 Ns300p85 0 1 Ns300p87 

noncomputable def Ns300p89 := nat_lit 260367741960270832275868876800 

noncomputable abbrev qz334 := (@HMul.hMul Real Real Real qz5 qz633 (Real.log Real.pi))

noncomputable def Ns300p90 := @Enclosure.Real.IsNear.subLit_ff_p qz12 qz334 20476983164574266457 14073748835532800 39762522158261 9000000000000000000 5910225384309 16777216000 153869 33554432000 Ns300p89 77595633852562556349 70368744177664000 

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 615476 4000) qz632) qz332)

noncomputable def Ns300p91 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz633 124040052418617296317 70368744177664000 39762522158261 9000000000000000000 615476 2000 0 1 204769831645742664570000 20476983164574266457 14073748835532800 39762522158261 9000000000000000000 

noncomputable def Ns300p92 := nat_lit 1117253467703003293619755415150526464 

noncomputable def Ns300p93 := nat_lit 55409897319650227491176448 

noncomputable def Ns300p94 := nat_lit 4835703278458516698824704 

noncomputable def Ns300p95 := nat_lit 127555594224698098667565172151380056077138850872967730892486212401994673238409492545678242277215340984005056066959598580945387520 

noncomputable def Ns300p96 := nat_lit 1437385147147709748431848995188575409576837064188220206144490700685676022385016629013118552437970381999761497173598490071138304 

noncomputable def Ns300p97 := nat_lit 462924759938076090358779303750112608794049149976846280612359590931672949567900386782992852345909001625985713858485944320 

noncomputable def Ns300p98 := BSN.log_dyadic_bound 466667826304 2563819826304 6 5 Ns300p95 134217728 35280000 Ns300p96 Ns300p97 49411359 3030487652608 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 466667826304) (BSN.artanhQ 2563819826304) 0 5 Ns300p96 Ns300p95 Ns300p97 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz335 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns300p99 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 615476 4000) qz632 615476 4000 0 1 3225280514432247 281474976710656 781250441 27562500000000000 496270687475175413643 281474976710656000 120210224106229 27562500000000000000 (Enclosure.Real.IsNear.const Bool.false 615476 4000) (BSN.isNear_log_sfrac 1515243826304 16000000 3225280514432247 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1515243826304) qz335)) Bool.false Ns300p93 Ns300p94 1000000564480000 35280000000000000000000 3225280514432247 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1515243826304 16000000 16 3030487652608 2097152000000 49411359 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns300p98 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns300p100 := BSN.arctan_dyadic_bound_f 1000 1230952 1 0 16777216 4410000 0 1 1 0 1 1 13629 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1230952) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1230952) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz336 := qz630

noncomputable abbrev qz14 := qz336

noncomputable abbrev qz337 := qz631

noncomputable abbrev qz15 := qz337

noncomputable abbrev qz634 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz338 := qz634

noncomputable abbrev qz16 := (@Enclosure.Real.IsNear.mulLit_ff qz338 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def Ns300p101 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1230952))) 884279719003555 562949953421312 1 2000000000000000 13629 16777216 1 4410000 14828079405226767941632 883822405649827 562949953421312 200000000441 882000000000000000 qz16 (Ns300p100 rfl) rfl rfl 

noncomputable abbrev qz17 := qz332

noncomputable abbrev qz339 := qz629

noncomputable abbrev qz18 := qz339

noncomputable abbrev qz340 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns300p102 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 615476 4000) qz632) qz17 496270687475175413643 281474976710656000 120210224106229 27562500000000000000 883822405649827 2251799813685248 200000000441 3528000000000000000 Ns300p92 124040052418617296317 70368744177664000 39762522158261 9000000000000000000 (Ns300p99 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1230952)))) 1 4 0 1 883822405649827 562949953421312 200000000441 882000000000000000 883822405649827 2251799813685248 200000000441 3528000000000000000 qz340 Ns300p101 rfl) 

noncomputable def Ns300p103 := @Ns300p88 Ns300p82 Ns300p83 82978205746699889 9216000000000000000000 (@Ns300p90 82978205746699889 9216000000000000000000 (Ns300p91 (Ns300p102 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 615476 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz633 (Real.log Real.pi) 615476 2000 0 1 38410761 33554432 1 67108864 5910225384309 16777216000 153869 33554432000 (Enclosure.Real.IsNear.const Bool.false 615476 2000) RS301to312.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns300p84 Ns300p85) 

noncomputable abbrev qz341 := (@instHAdd Real Real.instAdd)

noncomputable def Ns300p104 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns300p82 Ns300p83 82978205746699889 9216000000000000000000 289066191 262144 19 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz341 qz333 (Enclosure.sfrac Bool.true Ns300p84 Ns300p85)) Bool.false Ns300p82 Ns300p83 82978205746699889 9216000000000000000000 Ns300p86 (Ns300p103 rfl rfl)) 

noncomputable def Ns300p105 := BSN.cos_dyadic_bound_f 67824908 68719476736 1 0 33554432 8828614 0 1 1 0 1 1 33554415 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 67824908) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 67824908) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns300p106 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 289066191) (@Nat.cast Real Real.instNatCast 262144)) Bool.false 289066191 262144 19 2097152 Bool.true 33554415 33554432 1 4410000 (Ns300p104 rfl) (Enclosure.sfrac_false_div 289066191 262144) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 289066191) (@Nat.cast Real Real.instNatCast 262144)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 37287137688799936512) (@Nat.cast Real Real.instNatCast 37778931862957161709568)) 226375608064910080 72057594037927936 Bool.false 33554415 33554432 175 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q2 289066191 262144 226375608064910080 72057594037927936 175 37287137688799936512 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554415 33554432 37287137688799936512 37778931862957161709568 67824908 68719476736 8828614 8820000 (Ns300p105 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p107 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns300p82 Ns300p83 82978205746699889 9216000000000000000000 296003779591 268435456 2418 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz341 qz333 (Enclosure.sfrac Bool.true Ns300p84 Ns300p85)) Bool.false Ns300p82 Ns300p83 82978205746699889 9216000000000000000000 Ns300p86 (Ns300p103 rfl rfl)) 

noncomputable def Ns300p108 := Ns300p81 53852 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 430 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 214962676 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 271 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 200734094 268435456) qz10 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 33554415 33554432 5367947 578027520000 268435320 268435456 2493 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 33554415 33554432 5367947 578027520000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 33554415 33554432 85887152 9248440320000 33554415 33554432 5367947 578027520000 (Ns300p106 rfl rfl) rfl)) rfl) (Ns300p107 rfl) RS301to312.d7 

noncomputable def Ns300p109 := nat_lit 7703186973677275016696144488667452820851526995400365339377056432800000 

noncomputable def Ns300p110 := nat_lit 1087025049619513796520974048308631508761049663116835882438097565248389120 

noncomputable def Ns300p111 := nat_lit 779678157460819103152684180906135170373560410167679898480100000000 

noncomputable def Ns300p112 := nat_lit 23108001564716903411882128097640546192213833865380760658334209098400000 

noncomputable def Ns300p113 := nat_lit 48916127232878120843443832173888417894247234840257614709714390436177510400 

noncomputable abbrev qz342 := (BSN.cosEvenQ 268435456)

noncomputable abbrev qz343 := (BSN.cosOddQ 268435456)

noncomputable def Ns300p114 := BSN.cos_dyadic_bound_f 172381010 268435456 3 2 268435456 134217728 Ns300p109 Ns300p110 Ns300p111 Ns300p112 Ns300p113 Ns300p111 214962676 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 172381010) qz342 0 2 Ns300p109 Ns300p110 Ns300p111 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 172381010) qz343 0 2 Ns300p112 Ns300p113 Ns300p111 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p115 := nat_lit 41519144054555946687342000076859191109436779172096187151805184411541760 

noncomputable def Ns300p116 := nat_lit 9783225446575624168688766434777683578849446968051522941942878087235502080 

noncomputable def Ns300p117 := nat_lit 6989851343488794312555006738405190695988466564173637673252883374336 

noncomputable def Ns300p118 := nat_lit 108729298478804688037961101618959511168350440314386113793733073552384256 

noncomputable def Ns300p119 := nat_lit 179359133187219776425960717970924198945573194414277920602286098265984204800 

noncomputable abbrev qz344 := (BSN.sinEvenQ 268435456)

noncomputable abbrev qz345 := (BSN.sinOddQ 268435456)

noncomputable def Ns300p120 := BSN.sin_dyadic_bound_f 226755846 268435456 3 2 268435456 134217728 Ns300p115 Ns300p116 Ns300p117 Ns300p118 Ns300p119 Ns300p117 200734094 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 226755846) qz344 0 2 Ns300p115 Ns300p116 Ns300p117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 226755846) qz345 0 2 Ns300p118 Ns300p119 Ns300p117 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p121 := nat_lit 7589933578478918701310595417032202579433549576364121469738847039904990504634069039717004632342082078525390625 

noncomputable def Ns300p122 := nat_lit 67052582193422231333984484018745857420694574238012043916021913709013615522643186318434558042568065189255577600 

noncomputable def Ns300p123 := nat_lit 2793041916725858807959672212320442895817844519611694974580834409610899743149224137229979038238525390625 

noncomputable def Ns300p124 := nat_lit 45996104018449218320492174068510696278279421976621066973903047961727174223368398128400524476634837534525390625 

noncomputable def Ns300p125 := nat_lit 6101784979601423051392588045705873025283206255659095996357994147520239012560529954977544781873693932222257561600 

noncomputable def Ns300p126 := BSN.cos_dyadic_bound_f 344487225 268435456 4 3 268435456 134217728 Ns300p121 Ns300p122 Ns300p123 Ns300p124 Ns300p125 Ns300p123 76111624 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 344487225) qz342 0 3 Ns300p121 Ns300p122 Ns300p123 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 344487225) qz343 0 3 Ns300p124 Ns300p125 Ns300p123 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p127 := nat_lit 10784898283339375143806747573851482503048799971960828292313998629601280 

noncomputable def Ns300p128 := nat_lit 471749566925132483628069024184663587591887510448237740419228696576 

noncomputable def Ns300p129 := nat_lit 28245398385637627543091798200714726624081232108690015047337889088208896 

noncomputable def Ns300p130 := BSN.sin_dyadic_bound_f 161887732 268435456 3 2 268435456 134217728 Ns300p127 Ns300p116 Ns300p128 Ns300p129 Ns300p119 Ns300p128 152251445 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 161887732) qz344 0 2 Ns300p127 Ns300p116 Ns300p128 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 161887732) qz345 0 2 Ns300p129 Ns300p119 Ns300p128 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz635 := (BSN.cos_quad_nat2 158 rfl)

noncomputable def Ns300p131 := Ns300p79 91733 BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 76111624 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 71 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 152251445 268435456) qz10 rfl rfl (Ns300p108 RS301to312.d9 RS301to312.d11 RS301to312.d13 RS301to312.d17 (Ns300p114 rfl rfl) (Ns300p120 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns300p107 rfl) RS301to312.d19 RS301to312.d21 RS301to312.d23 RS301to312.d25 RS301to312.d17 (Ns300p126 rfl rfl) (Ns300p130 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns300p132 := nat_lit 269955676693121689464083150625 

noncomputable def Ns300p133 := nat_lit 124615124604835863084731911901282304 

noncomputable def Ns300p134 := nat_lit 1869226869072537946270978678519234560 

noncomputable def Ns300p135 := BSN.cos_dyadic_bound_f 22794135 268435456 2 1 268435456 134217728 Ns300p132 Ns300p133 Ns300p132 Ns300p132 Ns300p134 Ns300p132 267468258 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 22794135) qz342 0 1 Ns300p132 Ns300p133 Ns300p132 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 22794135) qz343 0 1 Ns300p132 Ns300p134 Ns300p132 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p136 := nat_lit 11718358922628730136449636619550812334138448516561808628641532956342881 

noncomputable def Ns300p137 := nat_lit 1804106890482550984055673393430786734192495968415251196749992917601 

noncomputable def Ns300p138 := nat_lit 35151468554105225307380798511865575428946960557748595383531098883193441 

noncomputable def Ns300p139 := BSN.cos_dyadic_bound_f 191440043 268435456 3 2 268435456 134217728 Ns300p136 Ns300p110 Ns300p137 Ns300p138 Ns300p113 Ns300p137 203015568 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 191440043) qz342 0 2 Ns300p136 Ns300p110 Ns300p137 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 191440043) qz343 0 2 Ns300p138 Ns300p113 Ns300p137 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p140 := Ns300p77 123655 BSN.abs_quadSignPos (BSN.cos_quad_nat0 0 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 267468258 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 203015568 268435456) qz10 rfl rfl (Ns300p131 rfl rfl) (Ns300p107 rfl) RS301to312.d27 RS301to312.d29 RS301to312.d31 RS301to312.d33 RS301to312.d17 (Ns300p135 rfl rfl) (Ns300p139 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p141 := nat_lit 6139995936072046877684105146601064695641863038145614857870198471864991963692023612900230685451049058860793856 

noncomputable def Ns300p142 := nat_lit 1480023678344367400370733818326730654281977715414001197193801607145792196671242698762671181065382526976 

noncomputable def Ns300p143 := nat_lit 37216901011341741774644222432122859204611340449599783689675875404033158492138684434431370796788581891561226240 

noncomputable def Ns300p144 := BSN.cos_dyadic_bound_f 326730032 268435456 4 3 268435456 134217728 Ns300p141 Ns300p122 Ns300p142 Ns300p143 Ns300p125 Ns300p142 92961196 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 326730032) qz342 0 3 Ns300p141 Ns300p122 Ns300p142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 326730032) qz343 0 3 Ns300p143 Ns300p125 Ns300p142 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p145 := nat_lit 12490980148498656796000254299101020231516295972584244442865776473090583543008503431039453618186836132963024896 

noncomputable def Ns300p146 := nat_lit 12410820449479469718187699904847556817218155673417578815943100268240943154127082812386723504465133961216 

noncomputable def Ns300p147 := nat_lit 75644818075452093197883135536297408720520796704260090179000348425641679925989058232103425969449489949597368320 

noncomputable def Ns300p148 := BSN.cos_dyadic_bound_f 390076728 268435456 4 3 268435456 134217728 Ns300p145 Ns300p122 Ns300p146 Ns300p147 Ns300p125 Ns300p146 31507899 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 390076728) qz342 0 3 Ns300p145 Ns300p122 Ns300p146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 390076728) qz343 0 3 Ns300p147 Ns300p125 Ns300p146 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p149 := Ns300p75 151547 BSN.abs_quadSignPos (BSN.cos_quad_nat0 112 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 92961196 268435456) BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 31507899 268435456) qz10 rfl rfl (Ns300p140 rfl) (Ns300p107 rfl) RS301to312.d35 RS301to312.d37 RS301to312.d39 RS301to312.d41 RS301to312.d17 (Ns300p144 rfl rfl) (Ns300p148 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p150 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) 66219655 268435456 151547 268435456 66219655 268435456 151547 268435456 35551406572175360 66219655 134217728 151547 134217728 (Ns300p149 rfl) 

noncomputable def Ns300p151 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz330) (Zeta.RiemannSiegel.correction qz9) 10665767 33554432 1 33554432 397305126962887 562949953421312 832168532424869 31032616182349824000 4237563912091570389329 18889465931478580854784 

noncomputable def Ns300p152 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz330 1 1 0 1 10665767 33554432 1 33554432 10665767 33554432 1 33554432 

noncomputable abbrev qz19 := (@Enclosure.Real.IsNear.of_eq qz328 (@HMul.hMul Real Real Real qz327 qz326 qz325) Bool.false 821714775757 8388608000 153869 8388608000 (BSN.t_div_two_pi_mk qz326 615476 1000 (@Eq.refl Real qz326)) (@Enclosure.Real.IsNear.mulLit_ff qz326 qz325 615476 1000 0 1 5340353 33554432 1 33554432 821714775757 8388608000 153869 8388608000 (Enclosure.Real.IsNear.const Bool.false 615476 1000) RS301to312.d44 rfl))

noncomputable def Ns300p153 := @Enclosure.Real.IsNear.sqrt_image qz7 821714775757 8388608000 153869 8388608000 166048689 166048721 16777216 qz19 

noncomputable abbrev qz811 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 615476 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz636 := qz811

noncomputable abbrev qz346 := qz636

noncomputable abbrev qz20 := qz346

noncomputable def Ns300p154 := @Enclosure.Real.IsNear.sqrt_image qz20 166048705 16777216 1 1048576 52781007 52781013 16777216 (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 332097410 33554432 32 33554432 166048705 16777216 1 1048576 (Ns300p153 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz812 := (Real.sqrt (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 615476 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))))

noncomputable abbrev qz637 := qz812

noncomputable abbrev qz347 := qz637

noncomputable abbrev qz21 := qz347

noncomputable def Ns300p155 := @Enclosure.Real.IsNear.inv_image qz21 26390505 8388608 3 16777216 5332883 5332884 16777216 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 105562020 33554432 6 33554432 26390505 8388608 3 16777216 (Ns300p154 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns300p156 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz21) Bool.false 10665767 33554432 1 33554432 10665767 33554432 1 33554432 (Ns300p155 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz22 := (@HMul.hMul Real Real Real qz327 qz323 qz329)

noncomputable abbrev qz638 := (@HMul.hMul Real Real Real qz807 qz809 qz809)

noncomputable abbrev qz639 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz348 := (@HSub.hSub Real Real Real qz628 (@HSub.hSub Real Real Real qz628 qz638 qz626) qz639)

noncomputable abbrev qz23 := (Real.cos (@HMul.hMul Real Real Real qz327 qz323 qz348))

noncomputable def Ns300p157 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz9) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz22)) qz23) Bool.false 397305126962887 

noncomputable def Ns300p158 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz22)) qz23 42004391 33554432 329 

noncomputable def Ns300p159 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz22)) Bool.false 42004391 33554432 329 33554432 42004391 33554432 329 

noncomputable def Ns300p160 := @Enclosure.Real.IsNear.recentre' (Real.cos qz22) Bool.false 26804338 33554432 462187216 73987522560000 13402169 16777216 28886701 4624220160000 

noncomputable abbrev qz349 := (@Nat.cast Real Real.instNatCast 33554432)

noncomputable def Ns300p161 := @Enclosure.Real.IsNear.cos_image qz22 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 189171139) qz349) Bool.false 189171139 33554432 101 16777216 Bool.false 26804338 33554432 1 

noncomputable def Ns300p162 := nat_lit 26986075417125971852268999 

noncomputable def Ns300p163 := nat_lit 4503599627370496000000000000000 

noncomputable def Ns300p164 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz9 884279719003555 140737488355328 1 500000000000000 15053761 16777216 1 1048576 13311735547026675120355 2361183241434822606848 Ns300p162 

noncomputable def Ns300p165 := @Enclosure.Real.IsNear.subLit_ff_p qz20 qz1 166048705 16777216 1 1048576 9 1 0 1 15053761 15053761 16777216 1 

noncomputable abbrev qz350 := (Enclosure.Real.IsNear.const Bool.false 9 1)

noncomputable def Ns300p166 := @Ns300p165 1048576 (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 332097410 33554432 32 33554432 166048705 16777216 1 1048576 (Ns300p153 rfl rfl rfl rfl rfl rfl) rfl) qz350 

noncomputable def Ns300p167 := @Enclosure.Real.IsNear.recentre' qz22 Bool.false 13311735547026675120355 2361183241434822606848 Ns300p162 Ns300p163 189171139 33554432 101 16777216 (@Ns300p164 Ns300p163 RS301to312.d43 (Ns300p166 rfl rfl) rfl) 

noncomputable def Ns300p168 := nat_lit 4474719433690843109654528 

noncomputable def Ns300p169 := nat_lit 1102936445032646051898985898728755222937391178367914826982133834714256864077469339216563745 

noncomputable def Ns300p170 := nat_lit 180468656028383376705345110207518346455653528001341539704795567934989718275908111313435361280 

noncomputable def Ns300p171 := nat_lit 267354855889549111560758489214253123184542496348222047320820927152642355960192324914721 

noncomputable def Ns300p172 := nat_lit 2888210210080728008792912316259440602636582874540927425448021571321949413531341291326852641 

noncomputable def Ns300p173 := nat_lit 3308592027187028572931327020471169685020314680024594894587918745474811501724982040746314956800 

noncomputable abbrev qz351 := (BSN.sinEvenQ 68719476736)

noncomputable abbrev qz352 := (BSN.sinOddQ 68719476736)

noncomputable def Ns300p174 := BSN.sin_dyadic_bound_f 63589587763 68719476736 3 2 33554432 8828614 Ns300p169 Ns300p170 Ns300p171 Ns300p172 Ns300p173 Ns300p171 26804338 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 63589587763) qz351 0 2 Ns300p169 Ns300p170 Ns300p171 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 63589587763) qz352 0 2 Ns300p172 Ns300p173 Ns300p171 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz353 := (@Nat.cast Real Real.instNatCast Ns300p94)

noncomputable def Ns300p175 := @Ns300p161 4410000 (Ns300p167 rfl) (Enclosure.sfrac_false_div 189171139 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 189171139) qz349) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns300p168) qz353) 226375608064910080 72057594037927936 Bool.false 26804338 33554432 0 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q3 189171139 33554432 226375608064910080 72057594037927936 0 Ns300p168 Ns300p94 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 26804338 33554432 Ns300p168 Ns300p94 63589587763 68719476736 8828614 8820000 (Ns300p174 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p176 := @Enclosure.Real.IsNear.inv_image (Real.cos qz22) 13402169 16777216 28886701 4624220160000 21002031 21002360 16777216 (Ns300p160 (Ns300p175 rfl rfl) rfl) rfl 

noncomputable def Ns300p177 := @Enclosure.Real.IsNear.recentre' qz23 Bool.false 9458657 16777216 

noncomputable abbrev qz24 := (@HMul.hMul Real Real Real qz327 qz323 qz348)

noncomputable abbrev qz354 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable def Ns300p178 := @Enclosure.Real.IsNear.cos_image qz24 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16304787)) qz354) Bool.true 16304787 16777216 

noncomputable def Ns300p179 := nat_lit 38498590519215300590043325405 

noncomputable def Ns300p180 := nat_lit 39614081257132168796771975168 

noncomputable def Ns300p181 := nat_lit 126523550700185301575486837230707 

noncomputable def Ns300p182 := @Enclosure.Real.IsNear.recentre' qz24 Bool.true Ns300p179 Ns300p180 Ns300p181 

noncomputable def Ns300p183 := nat_lit 7555786372591432341913600000000000000 

noncomputable abbrev qz25 := qz348

noncomputable def Ns300p184 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz25 884279719003555 140737488355328 1 500000000000000 43536665708671 

noncomputable abbrev qz355 := (@HSub.hSub Real Real Real qz628 qz638 qz626)

noncomputable abbrev qz26 := qz355

noncomputable abbrev qz356 := qz639

noncomputable abbrev qz27 := qz356

noncomputable def Ns300p185 := @Enclosure.Real.IsNear.subLit_tf qz26 qz27 25944479664255 281474976710656 23442377 8796093022208 1 16 

noncomputable abbrev qz357 := qz638

noncomputable abbrev qz28 := qz357

noncomputable def Ns300p186 := @Enclosure.Real.IsNear.subLit_ff_n qz28 qz9 226615720245121 281474976710656 15053769 8796093022208 15053761 16777216 1 1048576 

noncomputable def Ns300p187 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz9 15053761 16777216 1 1048576 15053761 16777216 1 1048576 226615720245121 281474976710656 

noncomputable def Ns300p188 := nat_lit 9411956717516300567700511680121591088150184241956167935719201 

noncomputable def Ns300p189 := nat_lit 253092741970790968397859029543733109897246971520789871559966720 

noncomputable def Ns300p190 := nat_lit 4994833751089896575928164093517486359701554435199101957921 

noncomputable def Ns300p191 := nat_lit 28225880485046721909949678712177738291731149616998105603241761 

noncomputable def Ns300p192 := nat_lit 11389173388685593577903656329467989945376113718435544220198502400 

noncomputable def Ns300p193 := BSN.cos_dyadic_bound_f 16304787 16777216 3 2 16777216 4410000 Ns300p188 Ns300p189 Ns300p190 Ns300p191 Ns300p192 Ns300p190 9458657 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 16304787) (BSN.cosEvenQ 16777216) 0 2 Ns300p188 Ns300p189 Ns300p190 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 16304787) (BSN.cosOddQ 16777216) 0 2 Ns300p191 Ns300p192 Ns300p190 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz358 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns300p194 := @Ns300p177 2516384432 147975045120000 9458657 16777216 157274027 9248440320000 (@Ns300p178 563 33554432 Bool.false 9458657 16777216 1 4410000 (@Ns300p182 Ns300p183 16304787 16777216 563 33554432 (@Ns300p184 281474976710656 23442377 8796093022208 Ns300p179 Ns300p180 Ns300p181 Ns300p183 RS301to312.d43 (@Ns300p185 0 1 696586651338736 43536665708671 281474976710656 23442377 8796093022208 (@Ns300p186 435276139334813614080 25944479664255 281474976710656 23442377 8796093022208 (@Ns300p187 15053769 8796093022208 (Ns300p166 rfl rfl) (Ns300p166 rfl rfl) rfl) (Ns300p166 rfl rfl) rfl rfl) qz358 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16304787 16777216) (BSN.cos_neg_of_bound 16304787 16777216 Bool.false 9458657 16777216 1 4410000 (Ns300p193 rfl rfl)) rfl rfl) 

noncomputable abbrev qz29 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 9) (Enclosure.sfrac Bool.true 1 1) Bool.true 1 1 0 1 (BSN.neg_one_pow_odd_mk 9 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1))

noncomputable def Ns300p195 := @Ns300p151 2965872649622653110089 Ns300p71 (Ns300p152 qz29 (@Enclosure.Real.IsNear.of_eq qz330 (@Inv.inv Real Real.instInv qz21) Bool.false 10665767 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz7 (BSN.t_div_two_pi_nonneg qz4 615476 1000 qz10)) Ns300p156) rfl) (@Ns300p157 562949953421312 832168532424869 31032616182349824000 (BSN.correction_mk qz9 (BSN.cos_two_pi_p_ne_zero_mk qz4 615476 1000 9 qz10 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 615476 1000 9 qz10 rfl rfl rfl))) (@Ns300p158 33554432 9458657 16777216 157274027 9248440320000 397305126962887 562949953421312 832168532424869 31032616182349824000 (@Ns300p159 33554432 (Ns300p176 rfl rfl rfl rfl rfl) rfl) (Ns300p194 rfl) rfl)) 

noncomputable def Ns300p196 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 5082024012364767182511 18889465931478580854784 394874196365170051254089 Ns300p71 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz330) (Zeta.RiemannSiegel.correction qz9))) Bool.true 5082024012364767182511 18889465931478580854784 394874196365170051254089 Ns300p71 (BSN.hardyZApproximantRS₀_eq qz4 9 (@BSN.floor_sqrt_eq_dec qz4 615476 1000 9 qz10 rfl rfl rfl)) (@Ns300p73 5082024012364767182511 18889465931478580854784 394874196365170051254089 Ns300p71 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9)) Bool.true 66219655 134217728 151547 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (Ns300p150 (Ns300p149 rfl) rfl rfl)) (Ns300p195 rfl) rfl rfl)) 

theorem RS301to312.d45 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 5082024012364767182511 18889465931478580854784 394874196365170051254089 Ns300p71 := Ns300p196 

theorem RS301to312.d46 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS301to312.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS301to312.d3 a b h)) 

noncomputable def Ns300p197 := nat_lit 81350141365059122626560000 

noncomputable def Ns300p198 := nat_lit 296584216236148294745587712 

noncomputable abbrev qz813 := (Enclosure.sfrac Bool.false 616846 1000)

noncomputable abbrev qz640 := qz813

noncomputable abbrev qz359 := qz640

noncomputable abbrev qz30 := qz359

noncomputable abbrev qz814 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 616846 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz641 := qz814

noncomputable abbrev qz360 := qz641

noncomputable abbrev qz31 := qz360

noncomputable abbrev qz815 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 616846 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz642 := qz815

noncomputable abbrev qz361 := qz642

noncomputable abbrev qz32 := qz361

noncomputable abbrev qz362 := (@HPow.hPow Real Real Real qz627 qz31 qz8)

noncomputable def Ns300p199 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz30) qz30 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz362) (Zeta.RiemannSiegel.correction qz32)) 998019233 134217728 151877 134217728 66494623585905495 288230376151711744 672950406235914221243 Ns300p197 Ns300p198 

noncomputable def Ns300p200 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz30) qz30 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 616846 1000 112 158 268435456 134217728 4503599627370496 Bool.false 296846977463 2423 

noncomputable def Ns300p201 := Ns300p200 558195838 62 94906264 8 589812974 62 89478488 8 Bool.false 962905906 123924 Bool.true 248260458 Bool.true 354922630 14148475504056880 1 Bool.false 161587553 Bool.false Bool.false 66049493 Bool.true Bool.false 998019233 

noncomputable def Ns300p202 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz30) qz30 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 616846 1000 0 60 268435456 134217728 4503599627370496 Bool.false 296846977463 2423 

noncomputable def Ns300p203 := Ns300p202 480971758 62 109588312 8 522351262 62 101459064 8 Bool.false 773952415 91931 Bool.false 161472427 Bool.true 63863400 14148475504056880 1 Bool.false 221316927 Bool.false Bool.false 260874359 Bool.false Bool.false 962905906 

noncomputable def Ns300p204 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz30) qz30 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 616846 1000 159 71 268435456 134217728 4503599627370496 Bool.false 296846977463 2423 

noncomputable def Ns300p205 := Ns300p204 372130544 61 134217720 8 432030192 61 120047984 16 Bool.false 544442662 53966 Bool.false 256208824 Bool.false 413204241 14148475504056880 1 Bool.false 219042588 Bool.false Bool.false 268302369 Bool.false Bool.false 773952415 

noncomputable def Ns300p206 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz30) qz30 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 616846 1000 431 272 268435456 134217728 4503599627370496 Bool.false 296846977463 2423 

noncomputable def Ns300p207 := Ns300p206 186065264 61 189812528 16 294906480 61 154981288 8 Bool.false 268435408 2493 Bool.false 339012042 Bool.false 244274412 14148475504056880 1 Bool.false 255813283 Bool.false Bool.false 164752582 Bool.false Bool.false 544442662 

noncomputable def Ns300p208 := nat_lit 4822657820992526723643302023804781002311747508610703503 

noncomputable def Ns300p209 := nat_lit 4361076411730133602789253692225340978898678054912000 

noncomputable def Ns300p210 := nat_lit 42867259946476718565068544148480000 

noncomputable def Ns300p211 := nat_lit 158655035619817994403611144379295764480 

noncomputable abbrev qz33 := (@Eq.refl Real qz359)

noncomputable def Ns300p212 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz30 616846 1000 1521996950864 16000000 1233692 4000 2000 Ns300p210 Ns300p211 qz33 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns300p213 := nat_lit 98768032173926947300214825447521914927344588976347207741440 

noncomputable abbrev qz363 := (@HMul.hMul Real Real Real qz623 qz629 (@HSub.hSub Real Real Real qz628 qz630 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz631 (@Nat.cast Real Real.instNatCast 1233692)))))

noncomputable abbrev qz643 := (Real.log (Enclosure.sfrac Bool.false 1521996950864 16000000))

noncomputable abbrev qz644 := (Enclosure.sfrac Bool.false 616846 2000)

noncomputable abbrev qz34 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 616846 4000) qz643) qz363) qz644)

noncomputable abbrev qz364 := (@HSub.hSub Real Real Real qz11 qz34 (@HMul.hMul Real Real Real qz5 qz644 (Real.log Real.pi)))

noncomputable def Ns300p214 := @Enclosure.Real.IsNear.addLit_ft_p qz364 (Enclosure.sfrac Bool.true Ns300p210 Ns300p211) 622533384586196987603 562949953421312000 2716617023571280129 301056000000000000000000 Ns300p210 Ns300p211 0 1 Ns300p213 

noncomputable def Ns300p215 := nat_lit 20888754120827394959129706496000 

noncomputable abbrev qz365 := (@HMul.hMul Real Real Real qz5 qz644 (Real.log Real.pi))

noncomputable def Ns300p216 := @Enclosure.Real.IsNear.subLit_ff_p qz34 qz365 821289071907971837651 562949953421312000 650881612723823 147000000000000000000 11846762139903 33554432000 308423 67108864000 Ns300p215 622533384586196987603 562949953421312000 

noncomputable def Ns300p217 := nat_lit 1642578143815943675302000 

noncomputable abbrev qz35 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 616846 4000) qz643) qz363)

noncomputable def Ns300p218 := @Enclosure.Real.IsNear.subLit_ff_p qz35 qz644 994915785392033148627 562949953421312000 650881612723823 147000000000000000000 616846 2000 0 1 Ns300p217 821289071907971837651 562949953421312000 650881612723823 147000000000000000000 

noncomputable def Ns300p219 := nat_lit 2240351180178292427876399737781354496 

noncomputable def Ns300p220 := nat_lit 55431401143179793154441216 

noncomputable def Ns300p221 := nat_lit 130955525259684863531563709759069598731650381047437763884615016552541360438740012147952958085535063798122434565679012298379755520 

noncomputable def Ns300p222 := nat_lit 1511481214370173426125275650664457829030076287700364805065616769940614858652312063003389737292086491723049424557389701556731904 

noncomputable def Ns300p223 := nat_lit 534449336478253387761963770378799013964709079538293318702909899413469564341858273119357929345976078267000108129525432320 

noncomputable def Ns300p224 := BSN.log_dyadic_bound 473420950864 2570572950864 6 5 Ns300p221 134217728 35280000 Ns300p222 Ns300p223 50008210 3043993901728 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 473420950864) (BSN.artanhQ 2570572950864) 0 5 Ns300p222 Ns300p221 Ns300p223 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns300p225 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 616846 4000) qz643 616846 4000 0 1 3226532201700599 281474976710656 781250441 27562500000000000 995136741245103845377 562949953421312000 240955604764543 55125000000000000000 (Enclosure.Real.IsNear.const Bool.false 616846 4000) (BSN.isNear_log_sfrac 1521996950864 16000000 3226532201700599 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1521996950864) qz335)) Bool.false Ns300p220 Ns300p94 1000000564480000 35280000000000000000000 3226532201700599 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1521996950864 16000000 16 3043993901728 2097152000000 50008210 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns300p224 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns300p226 := BSN.arctan_dyadic_bound_f 1000 1233692 1 0 16777216 4410000 0 1 1 0 1 1 13599 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1233692) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1233692) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns300p227 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1233692))) 884279719003555 562949953421312 1 2000000000000000 13599 16777216 1 4410000 14828096293725370580992 883823412282787 562949953421312 200000000441 882000000000000000 qz16 (Ns300p226 rfl) rfl rfl 

noncomputable abbrev qz36 := qz363

noncomputable def Ns300p228 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 616846 4000) qz643) qz36 995136741245103845377 562949953421312000 240955604764543 55125000000000000000 883823412282787 2251799813685248 200000000441 3528000000000000000 Ns300p219 994915785392033148627 562949953421312000 650881612723823 147000000000000000000 (Ns300p225 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1233692)))) 1 4 0 1 883823412282787 562949953421312 200000000441 882000000000000000 883823412282787 2251799813685248 200000000441 3528000000000000000 qz340 Ns300p227 rfl) 

noncomputable def Ns300p229 := @Ns300p214 Ns300p208 Ns300p209 2716617023571280129 301056000000000000000000 (@Ns300p216 2716617023571280129 301056000000000000000000 (Ns300p218 (Ns300p228 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 616846 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz644 (Real.log Real.pi) 616846 2000 0 1 38410761 33554432 1 67108864 11846762139903 33554432000 308423 67108864000 (Enclosure.Real.IsNear.const Bool.false 616846 2000) RS301to312.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns300p210 Ns300p211) 

noncomputable def Ns300p230 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz30) Bool.false Ns300p208 Ns300p209 2716617023571280129 301056000000000000000000 18552936091 16777216 19 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz30) (@HAdd.hAdd Real Real Real qz341 qz364 (Enclosure.sfrac Bool.true Ns300p210 Ns300p211)) Bool.false Ns300p208 Ns300p209 2716617023571280129 301056000000000000000000 Ns300p212 (Ns300p229 rfl rfl)) 

noncomputable def Ns300p231 := nat_lit 2417851639229258349412352 

noncomputable def Ns300p232 := BSN.cos_dyadic_bound_f 37876867 68719476736 1 0 33554432 8828614 0 1 1 0 1 1 33554426 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 37876867) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 37876867) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable abbrev qz645 := (@Nat.cast Real Real.instNatCast Ns300p231)

noncomputable def Ns300p233 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz30) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18552936091) qz354) Bool.false 18552936091 16777216 19 2097152 Bool.false 33554426 33554432 1 4410000 (Ns300p230 rfl) (Enclosure.sfrac_false_div 18552936091 16777216) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18552936091) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1332673816996696031232) qz645) 226375608064910080 72057594037927936 Bool.false 33554426 33554432 176 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q0 18552936091 16777216 226375608064910080 72057594037927936 176 1332673816996696031232 Ns300p231 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554426 33554432 1332673816996696031232 Ns300p231 37876867 68719476736 8828614 8820000 (Ns300p232 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p234 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz30) Bool.false Ns300p208 Ns300p209 2716617023571280129 301056000000000000000000 296846977463 268435456 2423 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz30) (@HAdd.hAdd Real Real Real qz341 qz364 (Enclosure.sfrac Bool.true Ns300p210 Ns300p211)) Bool.false Ns300p208 Ns300p209 2716617023571280129 301056000000000000000000 Ns300p212 (Ns300p229 rfl rfl)) 

noncomputable def Ns300p235 := Ns300p207 53966 BSN.abs_quadSignPos (BSN.cos_quad_nat3 431 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 255813283 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 272 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 164752582 268435456) qz33 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 1) Bool.false 16777213 16777216 5367947 578027520000 268435408 268435456 2493 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz30)) Bool.false 16777213 16777216 5367947 578027520000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz30) qz30) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz30)) Bool.false 33554426 33554432 85887152 9248440320000 16777213 16777216 5367947 578027520000 (Ns300p233 rfl rfl) rfl)) rfl) (Ns300p234 rfl) RS301to312.d7 

noncomputable def Ns300p236 := nat_lit 18494553241186181869519492922743273896318073564875854636347757996562533909523752135562983453025866241878593536 

noncomputable def Ns300p237 := nat_lit 871683568514489007341798292243696146469029465094156570908284878217177001794361422139649254553384847460322508800 

noncomputable def Ns300p238 := nat_lit 2304525403753328788113282905060244287514851246952848950272221760848910156148451418963655121474759233536 

noncomputable def Ns300p239 := nat_lit 92424708023656758736648418405429149955150011711461449038166389268952019456973277906761104122182813738737668096 

noncomputable def Ns300p240 := nat_lit 30508924898007115256962940228529365126416031278295479981789970737601195062802649774887723909368469661111287808000 

noncomputable def Ns300p241 := BSN.sin_dyadic_bound_f 339012042 268435456 4 3 268435456 134217728 Ns300p236 Ns300p237 Ns300p238 Ns300p239 Ns300p240 Ns300p238 255813283 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 339012042) qz344 0 3 Ns300p236 Ns300p237 Ns300p238 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 339012042) qz345 0 3 Ns300p239 Ns300p240 Ns300p238 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p242 := nat_lit 31071193310350484927708066452433646927106144953914817708477156782309376 

noncomputable def Ns300p243 := nat_lit 12677213733305197114367223191502664973279187105826101091352717623296 

noncomputable def Ns300p244 := nat_lit 93188225503584844388895464910917935451371876487532800923248764911681536 

noncomputable def Ns300p245 := BSN.cos_dyadic_bound_f 244274412 268435456 3 2 268435456 134217728 Ns300p242 Ns300p110 Ns300p243 Ns300p244 Ns300p113 Ns300p243 164752582 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 244274412) qz342 0 2 Ns300p242 Ns300p110 Ns300p243 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 244274412) qz343 0 2 Ns300p244 Ns300p113 Ns300p243 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p246 := nat_lit 67676330311091137275336466824207432067888836183417098470209866306682880 

noncomputable def Ns300p247 := nat_lit 18567467158588266453362522516269572765926725343920399332414142283776 

noncomputable def Ns300p248 := nat_lit 177217470153648597575432921407897885631421165782202243918297169810948096 

noncomputable def Ns300p249 := BSN.sin_dyadic_bound_f 256208824 268435456 3 2 268435456 134217728 Ns300p246 Ns300p116 Ns300p247 Ns300p248 Ns300p119 Ns300p247 219042588 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 256208824) qz344 0 2 Ns300p246 Ns300p116 Ns300p247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 256208824) qz345 0 2 Ns300p248 Ns300p119 Ns300p247 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p250 := nat_lit 40858555272045074972520508595876058221116510340765424208165728039558256180021281669708235890692730059167282881 

noncomputable def Ns300p251 := nat_lit 24772922500540357261389399276378440611169768007132432679912178377988001200453367497975456555687522252481 

noncomputable def Ns300p252 := nat_lit 204058642063054592571790432535023634584966044286573850493870800533861733894546199421979666368460051457143387841 

noncomputable def Ns300p253 := BSN.sin_dyadic_bound_f 413204241 268435456 4 3 268435456 134217728 Ns300p250 Ns300p237 Ns300p251 Ns300p252 Ns300p240 Ns300p251 268302369 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 413204241) qz344 0 3 Ns300p250 Ns300p237 Ns300p251 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 413204241) qz345 0 3 Ns300p252 Ns300p240 Ns300p251 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p254 := Ns300p205 91931 BSN.abs_quadSignPos (BSN.cos_quad_nat3 159 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 219042588 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 71 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268302369 268435456) qz33 rfl rfl (Ns300p235 RS301to312.d9 RS301to312.d11 RS301to312.d13 RS301to312.d17 (Ns300p241 rfl rfl) (Ns300p245 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns300p234 rfl) RS301to312.d19 RS301to312.d21 RS301to312.d23 RS301to312.d25 RS301to312.d17 (Ns300p249 rfl rfl) (Ns300p253 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns300p255 := nat_lit 5930565853784204327501714387797027482340537144506456262835515839742561 

noncomputable def Ns300p256 := nat_lit 462154284552379140220428354068048882565235966484886575940544234081 

noncomputable def Ns300p257 := nat_lit 17790773252783508224224702306682946349256480961586399015354666430759521 

noncomputable def Ns300p258 := BSN.cos_dyadic_bound_f 161472427 268435456 3 2 268435456 134217728 Ns300p255 Ns300p110 Ns300p256 Ns300p257 Ns300p113 Ns300p256 221316927 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 161472427) qz342 0 2 Ns300p255 Ns300p110 Ns300p256 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 161472427) qz343 0 2 Ns300p257 Ns300p113 Ns300p256 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p259 := nat_lit 16634438443577389803393600000000 

noncomputable def Ns300p260 := BSN.cos_dyadic_bound_f 63863400 268435456 2 1 268435456 134217728 Ns300p259 Ns300p133 Ns300p259 Ns300p259 Ns300p134 Ns300p259 260874359 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 63863400) qz342 0 1 Ns300p259 Ns300p133 Ns300p259 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 63863400) qz343 0 1 Ns300p259 Ns300p134 Ns300p259 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p261 := Ns300p203 123924 BSN.abs_quadSignPos (BSN.cos_quad_nat0 0 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 221316927 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 260874359 268435456) qz33 rfl rfl (Ns300p254 rfl rfl) (Ns300p234 rfl) RS301to312.d27 RS301to312.d29 RS301to312.d31 RS301to312.d33 RS301to312.d17 (Ns300p258 rfl rfl) (Ns300p260 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p262 := nat_lit 33150347673760585466114256991416107262714965732551193600235646304215296 

noncomputable def Ns300p263 := nat_lit 14429803533004288575645441621169621415187427432125272126101859164416 

noncomputable def Ns300p264 := nat_lit 99422183414215747821191480091005982545314522342789330256454735194317056 

noncomputable def Ns300p265 := BSN.cos_dyadic_bound_f 248260458 268435456 3 2 268435456 134217728 Ns300p262 Ns300p110 Ns300p263 Ns300p264 Ns300p113 Ns300p263 161587553 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 248260458) qz342 0 2 Ns300p262 Ns300p110 Ns300p263 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 248260458) qz343 0 2 Ns300p264 Ns300p113 Ns300p263 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p266 := nat_lit 8553995992660584052861043354307396523062303297620843463254795917040165678886023147299532502822466398784000000 

noncomputable def Ns300p267 := nat_lit 3995805056361207732585622404012731248832387032399328888532761830708874820030265944400056481000000000000 

noncomputable def Ns300p268 := nat_lit 51831401180655257880699085167356763195264080262169393126358715202832362842405199058535652668533746582489600000 

noncomputable def Ns300p269 := BSN.cos_dyadic_bound_f 354922630 268435456 4 3 268435456 134217728 Ns300p266 Ns300p122 Ns300p267 Ns300p268 Ns300p125 Ns300p267 66049493 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 354922630) qz342 0 3 Ns300p266 Ns300p122 Ns300p267 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 354922630) qz343 0 3 Ns300p268 Ns300p125 Ns300p267 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p270 := Ns300p201 151877 BSN.abs_quadSignPos (BSN.cos_quad_nat0 112 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 161587553 268435456) BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66049493 268435456) qz33 rfl rfl (Ns300p261 rfl) (Ns300p234 rfl) RS301to312.d35 RS301to312.d37 RS301to312.d39 RS301to312.d41 RS301to312.d17 (Ns300p265 rfl rfl) (Ns300p269 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p271 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 9) 998019233 268435456 151877 268435456 998019233 268435456 151877 268435456 535807495814250496 998019233 134217728 151877 134217728 (Ns300p270 rfl) 

noncomputable def Ns300p272 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz362) (Zeta.RiemannSiegel.correction qz32) 5205 16384 1 16777216 12775143820539 17592186044416 15699793140001 606105784811520000 66494623585905495 288230376151711744 

noncomputable def Ns300p273 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz362 1 1 0 1 5205 16384 1 16777216 5205 16384 1 16777216 

noncomputable def Ns300p274 := @Enclosure.Real.IsNear.sqrt_image qz31 1647087693319 16777216000 308423 16777216000 166233392 166233424 16777216 (@Enclosure.Real.IsNear.of_eq qz31 (@HMul.hMul Real Real Real qz5 qz30 qz3) Bool.false 1647087693319 16777216000 308423 16777216000 (BSN.t_div_two_pi_mk qz30 616846 1000 qz33) (@Enclosure.Real.IsNear.mulLit_ff qz30 qz3 616846 1000 0 1 5340353 33554432 1 33554432 1647087693319 16777216000 308423 16777216000 (Enclosure.Real.IsNear.const Bool.false 616846 1000) RS301to312.d44 rfl)) 

noncomputable abbrev qz816 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 616846 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz646 := qz816

noncomputable abbrev qz366 := qz646

noncomputable abbrev qz37 := qz366

noncomputable def Ns300p275 := @Enclosure.Real.IsNear.sqrt_image qz37 2597397 262144 1 1048576 52810354 52810360 16777216 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 332466816 33554432 32 33554432 2597397 262144 1 1048576 (Ns300p274 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns300p276 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz37) 52810357 16777216 3 16777216 5329919 5329921 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz37) Bool.false 105620714 33554432 6 33554432 52810357 16777216 3 16777216 (Ns300p275 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns300p277 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz37)) Bool.false 10659840 33554432 2 33554432 5205 16384 1 16777216 (Ns300p276 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz38 := (@HMul.hMul Real Real Real qz327 qz323 qz361)

noncomputable abbrev qz647 := (@HMul.hMul Real Real Real qz807 qz815 qz815)

noncomputable abbrev qz367 := (@HSub.hSub Real Real Real qz628 (@HSub.hSub Real Real Real qz628 qz647 qz642) qz639)

noncomputable abbrev qz39 := (Real.cos (@HMul.hMul Real Real Real qz327 qz323 qz367))

noncomputable def Ns300p278 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz32) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz38)) qz39) Bool.false 12775143820539 

noncomputable def Ns300p279 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz38)) qz39 5002157 4194304 75 

noncomputable def Ns300p280 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz38)) Bool.false 40017256 33554432 300 33554432 5002157 4194304 75 

noncomputable def Ns300p281 := @Enclosure.Real.IsNear.recentre' (Real.cos qz38) Bool.false 28135360 33554432 462187216 73987522560000 439615 524288 28886701 4624220160000 

noncomputable def Ns300p282 := @Enclosure.Real.IsNear.cos_image qz38 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 95746093) qz354) Bool.false 95746093 16777216 101 16777216 Bool.false 28135360 33554432 1 

noncomputable def Ns300p283 := nat_lit 5397215083445026704065627 

noncomputable def Ns300p284 := nat_lit 900719925474099200000000000000 

noncomputable def Ns300p285 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz32 884279719003555 140737488355328 1 500000000000000 238101 262144 1 1048576 210547885374465449055 36893488147419103232 Ns300p283 

noncomputable def Ns300p286 := @Enclosure.Real.IsNear.subLit_ff_p qz37 qz1 2597397 262144 1 1048576 9 1 0 1 238101 238101 262144 1 

noncomputable def Ns300p287 := @Ns300p286 1048576 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 332466816 33554432 32 33554432 2597397 262144 1 1048576 (Ns300p274 rfl rfl rfl rfl rfl rfl) rfl) qz350 

noncomputable def Ns300p288 := @Enclosure.Real.IsNear.recentre' qz38 Bool.false 210547885374465449055 36893488147419103232 Ns300p283 Ns300p284 95746093 16777216 101 16777216 (@Ns300p285 Ns300p284 RS301to312.d43 (Ns300p287 rfl rfl) rfl) 

noncomputable def Ns300p289 := nat_lit 2404608779314372076896256 

noncomputable def Ns300p290 := nat_lit 1471702843696869331290766397822683705225582194105060163223859973671462675278388612301327905 

noncomputable def Ns300p291 := nat_lit 475945240446998307086470981380984375924228076620599013343706626239748264238492351467041 

noncomputable def Ns300p292 := nat_lit 3853689250721553108502438660327650015172647472436819457659933929839918842825107854124912161 

noncomputable def Ns300p293 := BSN.sin_dyadic_bound_f 68343092019 68719476736 3 2 33554432 8828614 Ns300p290 Ns300p170 Ns300p291 Ns300p292 Ns300p173 Ns300p291 28135360 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 68343092019) qz351 0 2 Ns300p290 Ns300p170 Ns300p291 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 68343092019) qz352 0 2 Ns300p292 Ns300p173 Ns300p291 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p294 := @Ns300p282 4410000 (Ns300p288 rfl) (Enclosure.sfrac_false_div 95746093 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 95746093) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns300p289) qz645) 226375608064910080 72057594037927936 Bool.false 28135360 33554432 0 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q3 95746093 16777216 226375608064910080 72057594037927936 0 Ns300p289 Ns300p231 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 28135360 33554432 Ns300p289 Ns300p231 68343092019 68719476736 8828614 8820000 (Ns300p293 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p295 := @Enclosure.Real.IsNear.inv_image (Real.cos qz38) 439615 524288 28886701 4624220160000 20008478 20008778 16777216 (Ns300p281 (Ns300p294 rfl rfl) rfl) rfl 

noncomputable def Ns300p296 := @Enclosure.Real.IsNear.recentre' qz39 Bool.false 10215708 16777216 

noncomputable abbrev qz40 := (@HMul.hMul Real Real Real qz327 qz323 qz367)

noncomputable def Ns300p297 := @Enclosure.Real.IsNear.cos_image qz40 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15369919)) qz354) Bool.true 15369919 16777216 

noncomputable def Ns300p298 := nat_lit 8860155281694611224366645 

noncomputable def Ns300p299 := nat_lit 9671406556917033397649408 

noncomputable def Ns300p300 := nat_lit 79700270323316635598375392759903 

noncomputable def Ns300p301 := @Enclosure.Real.IsNear.recentre' qz40 Bool.true Ns300p298 Ns300p299 Ns300p300 

noncomputable def Ns300p302 := nat_lit 4722366482869645213696000000000000000 

noncomputable abbrev qz41 := qz367

noncomputable def Ns300p303 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz41 884279719003555 140737488355328 1 500000000000000 10019629639 

noncomputable abbrev qz368 := (@HSub.hSub Real Real Real qz628 qz647 qz642)

noncomputable abbrev qz42 := qz368

noncomputable def Ns300p304 := @Enclosure.Real.IsNear.subLit_tf qz42 qz27 5724662343 68719476736 2953385 1099511627776 1 16 

noncomputable abbrev qz369 := qz647

noncomputable abbrev qz43 := qz369

noncomputable def Ns300p305 := @Enclosure.Real.IsNear.subLit_ff_n qz43 qz32 56692086201 68719476736 1904809 1099511627776 238101 262144 1 1048576 

noncomputable def Ns300p306 := @Enclosure.Real.IsNear.mulLit_ff qz32 qz32 238101 262144 1 1048576 238101 262144 1 1048576 56692086201 68719476736 

noncomputable def Ns300p307 := nat_lit 7431170580379976767706910617109810574808940321656002146961921 

noncomputable def Ns300p308 := nat_lit 3114387374186869941210609751925019096259475518527384291841 

noncomputable def Ns300p309 := nat_lit 22287282966391556563238310631825581686234302013930951672302081 

noncomputable def Ns300p310 := BSN.cos_dyadic_bound_f 15369919 16777216 3 2 16777216 4410000 Ns300p307 Ns300p189 Ns300p308 Ns300p309 Ns300p192 Ns300p308 10215708 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 15369919) (BSN.cosEvenQ 16777216) 0 2 Ns300p307 Ns300p189 Ns300p308 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 15369919) (BSN.cosOddQ 16777216) 0 2 Ns300p309 Ns300p192 Ns300p308 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p311 := @Ns300p296 317304304 18496880640000 2553927 4194304 19831519 1156055040000 (@Ns300p297 71 4194304 Bool.false 10215708 16777216 1 4410000 (@Ns300p301 Ns300p302 15369919 16777216 71 4194304 (@Ns300p303 68719476736 2953385 1099511627776 Ns300p298 Ns300p299 Ns300p300 Ns300p302 RS301to312.d43 (@Ns300p304 0 1 160314074224 10019629639 68719476736 2953385 1099511627776 (@Ns300p305 1500685885243392 5724662343 68719476736 2953385 1099511627776 (@Ns300p306 1904809 1099511627776 (Ns300p287 rfl rfl) (Ns300p287 rfl rfl) rfl) (Ns300p287 rfl rfl) rfl rfl) qz358 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 15369919 16777216) (BSN.cos_neg_of_bound 15369919 16777216 Bool.false 10215708 16777216 1 4410000 (Ns300p310 rfl rfl)) rfl rfl) 

noncomputable def Ns300p312 := @Ns300p272 672950406235914221243 Ns300p197 (Ns300p273 qz29 (@Enclosure.Real.IsNear.of_eq qz362 (@Inv.inv Real Real.instInv (Real.sqrt qz37)) Bool.false 5205 16384 1 16777216 (BSN.rpow_neg_quarter_mk qz31 (BSN.t_div_two_pi_nonneg qz30 616846 1000 qz33)) Ns300p277) rfl) (@Ns300p278 17592186044416 15699793140001 606105784811520000 (BSN.correction_mk qz32 (BSN.cos_two_pi_p_ne_zero_mk qz30 616846 1000 9 qz33 rfl rfl (@BSN.floor_sqrt_eq_dec qz30 616846 1000 9 qz33 rfl rfl rfl))) (@Ns300p279 8388608 2553927 4194304 19831519 1156055040000 12775143820539 17592186044416 15699793140001 606105784811520000 (@Ns300p280 8388608 (Ns300p295 rfl rfl rfl rfl rfl) rfl) (Ns300p311 rfl) rfl)) 

noncomputable def Ns300p313 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz30) (hardyZApproximantRS₀ qz30) Bool.false 2209724606842907479 288230376151711744 92726478686055137261243 Ns300p197 (@Eq.refl Real (hardyZApproximantRS₀ qz30)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz30) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz30) qz30 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz362) (Zeta.RiemannSiegel.correction qz32))) Bool.false 2209724606842907479 288230376151711744 92726478686055137261243 Ns300p197 (BSN.hardyZApproximantRS₀_eq qz30 9 (@BSN.floor_sqrt_eq_dec qz30 616846 1000 9 qz33 rfl rfl rfl)) (@Ns300p199 2209724606842907479 288230376151711744 92726478686055137261243 Ns300p197 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz30) qz30 9) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 9)) Bool.false 998019233 134217728 151877 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz30) qz30 9) (Ns300p271 (Ns300p270 rfl) rfl rfl)) (Ns300p312 rfl) rfl rfl)) 

theorem RS301to312.d47 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz30) Bool.false 2209724606842907479 288230376151711744 92726478686055137261243 Ns300p197 := Ns300p313 

noncomputable abbrev qz817 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 615476 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))) (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 615476 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz648 := qz817

noncomputable abbrev qz370 := qz648

noncomputable abbrev qz649 := (@HMul.hMul Real Real Real qz807 qz817 qz817)

noncomputable abbrev qz371 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz623 qz649 qz648))

noncomputable abbrev qz44 := (@HAdd.hAdd Real Real Real qz341 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz370)) (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 1 32) qz371))

noncomputable abbrev qz372 := (@HMul.hMul Real Real Real qz623 qz637 qz637)

noncomputable abbrev qz45 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz327 qz372 qz347))

noncomputable def Ns300p314 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz341 qz44 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz45)) Bool.false 

noncomputable def Ns300p315 := @Enclosure.Real.IsNear.addLit_ff qz44 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz45) 21776601 1073741824 

noncomputable abbrev qz46 := (@Inv.inv Real Real.instInv qz370)

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 1 32) qz371)

noncomputable def Ns300p316 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz46) qz47 2722075 134217728 25 134217728 

noncomputable def Ns300p317 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz46 25 4 0 1 108883 33554432 1 33554432 2722075 

noncomputable def Ns300p318 := @Enclosure.Real.IsNear.recentre' qz46 Bool.false 108883 33554432 1 33554432 108883 33554432 1 33554432 

noncomputable def Ns300p319 := @Enclosure.Real.IsNear.mulLit_ff qz21 qz7 26390505 8388608 3 16777216 821714775757 8388608000 153869 8388608000 4337093579637797457 14073748835532800 1323313252071 

noncomputable def Ns300p320 := @Enclosure.Real.IsNear.sqrt_image qz7 821714775757 8388608000 153869 8388608000 166048689 166048721 16777216 qz19 

noncomputable def Ns300p321 := @Enclosure.Real.IsNear.sqrt_image qz20 166048705 16777216 1 1048576 52781007 52781013 16777216 (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 332097410 33554432 32 33554432 166048705 16777216 1 1048576 (Ns300p320 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz373 := (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 105562020 33554432 6 33554432 26390505 8388608 3 16777216 (Ns300p321 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns300p322 := @Ns300p319 17592186044416000 qz373 

noncomputable def Ns300p323 := Ns300p322 qz19 

noncomputable abbrev qz48 := qz370

noncomputable def Ns300p324 := @Enclosure.Real.IsNear.inv_image qz48 4337093579637797457 14073748835532800 1323313252071 17592186044416000 54441 54442 16777216 (Ns300p323 rfl) rfl rfl 

noncomputable abbrev qz49 := qz371

noncomputable def Ns300p325 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz49 1 32 0 1 1 

noncomputable def Ns300p326 := @Enclosure.Real.IsNear.recentre' qz49 Bool.false 1 33554432 1 33554432 

noncomputable def Ns300p327 := nat_lit 81582381444902518885848681780228056555555501005431402993 

noncomputable def Ns300p328 := nat_lit 2787593149816327892691964784081045188247552000000 

noncomputable def Ns300p329 := nat_lit 1866902411796598514168173403879996933690163540857721 

noncomputable def Ns300p330 := nat_lit 87112285931760246646623899502532662132736000000000 

noncomputable abbrev qz374 := (@HMul.hMul Real Real Real qz623 qz649 qz648)

noncomputable abbrev qz50 := qz374

noncomputable def Ns300p331 := @Enclosure.Real.IsNear.inv_image qz50 Ns300p327 Ns300p328 Ns300p329 Ns300p330 0 1 

noncomputable def Ns300p332 := nat_lit 18810380718535403752321242802155666849 

noncomputable def Ns300p333 := nat_lit 198070406285660843983859875840000 

noncomputable def Ns300p334 := nat_lit 28696670549349668108923390495317 

noncomputable def Ns300p335 := nat_lit 618970019642690137449562112000000 

noncomputable abbrev qz375 := qz649

noncomputable abbrev qz51 := qz375

noncomputable def Ns300p336 := @Enclosure.Real.IsNear.mulLit_ff qz51 qz48 Ns300p332 Ns300p333 Ns300p334 Ns300p335 4337093579637797457 14073748835532800 1323313252071 

noncomputable def Ns300p337 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz48 4337093579637797457 14073748835532800 1323313252071 17592186044416000 4337093579637797457 14073748835532800 1323313252071 17592186044416000 Ns300p332 

noncomputable def Ns300p338 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz45 13 10 0 1 1077647 33554432 1 

noncomputable def Ns300p339 := @Enclosure.Real.IsNear.recentre' qz45 Bool.false 1077647 33554432 1 33554432 1077647 33554432 

noncomputable abbrev qz52 := qz372

noncomputable def Ns300p340 := @Enclosure.Real.IsNear.mulLit_ff qz52 qz21 696458754155025 70368744177664 316686069 281474976710656 26390505 8388608 3 16777216 18379898233821958037625 

noncomputable def Ns300p341 := @Enclosure.Real.IsNear.mulLit_ff qz21 qz21 26390505 8388608 3 16777216 26390505 8388608 3 16777216 696458754155025 70368744177664 316686069 

noncomputable def Ns300p342 := @Ns300p341 281474976710656 qz373 

noncomputable def Ns300p343 := Ns300p342 qz373 

noncomputable def Ns300p344 := @Ns300p340 590295810358705651712 25072516574668197 4722366482869645213696 (Ns300p343 rfl) qz373 

noncomputable abbrev qz53 := (@HMul.hMul Real Real Real qz327 qz372 qz347)

noncomputable def Ns300p345 := @Enclosure.Real.IsNear.inv_image qz53 18379898233821958037625 590295810358705651712 25072516574668197 4722366482869645213696 538823 538824 16777216 (Ns300p344 rfl) 

noncomputable def Ns300p346 := @Ns300p315 201 1073741824 14009411 335544320 13 335544320 22349505294761984 333033581 5368709120 1213 5368709120 (@Ns300p316 1 1073741824 1 1073741824 2922805909782528 21776601 1073741824 201 1073741824 (@Ns300p317 134217728 25 134217728 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns300p318 (Ns300p324 rfl rfl rfl rfl) rfl) rfl) (@Ns300p325 33554432 1 33554432 1 1073741824 1 1073741824 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns300p326 1 33554432 1 33554432 (@Ns300p331 16777216 (@Ns300p336 17592186044416000 Ns300p327 Ns300p328 Ns300p329 Ns300p330 (@Ns300p337 Ns300p333 Ns300p334 Ns300p335 (Ns300p323 rfl) (Ns300p323 rfl) rfl) (Ns300p323 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns300p338 33554432 14009411 335544320 13 335544320 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns300p339 1 33554432 (Ns300p345 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS301to312.d48 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 := @Ns300p314 333033581 5368709120 1213 5368709120 (BSN.hardyZErrorBoundRS₀_mk qz4 615476 1000 qz10 rfl rfl) (Ns300p346 rfl rfl) 

noncomputable def Ns300p347 := nat_lit 144622473537882884669440000 

noncomputable def Ns300p348 := nat_lit 321443403299785492683896651776 

noncomputable abbrev qz818 := (Enclosure.sfrac Bool.false 618215 1000)

noncomputable abbrev qz650 := qz818

noncomputable abbrev qz376 := qz650

noncomputable abbrev qz54 := qz376

noncomputable abbrev qz819 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 618215 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz651 := qz819

noncomputable abbrev qz377 := qz651

noncomputable abbrev qz55 := qz377

noncomputable abbrev qz820 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 618215 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz652 := qz820

noncomputable abbrev qz378 := qz652

noncomputable abbrev qz56 := qz378

noncomputable abbrev qz379 := (@HPow.hPow Real Real Real qz627 qz55 qz8)

noncomputable def Ns300p349 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz54) qz54 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz379) (Zeta.RiemannSiegel.correction qz56)) 99915007 134217728 152207 134217728 1120506799911711282507 4722366482869645213696 1159054913761403779209 Ns300p347 Ns300p348 

noncomputable def Ns300p350 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz54) qz54 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 618215 1000 112 158 268435456 134217728 4503599627370496 Bool.false 297689967907 2428 

noncomputable def Ns300p351 := Ns300p350 558195838 62 94906264 8 589812974 62 89478488 8 Bool.true 143262296 124192 Bool.true 169440116 Bool.true 319386148 14148475504056880 1 Bool.false 216711142 Bool.false Bool.false 99815002 Bool.true Bool.true 99915007 

noncomputable def Ns300p352 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz54) qz54 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 618215 1000 0 59 268435456 134217728 4503599627370496 Bool.false 297689967907 2428 

noncomputable def Ns300p353 := Ns300p352 480971758 62 109588312 8 522351262 62 101459064 8 Bool.true 272323629 92128 Bool.false 346012535 Bool.true 357629262 14148475504056880 1 Bool.false 74647690 Bool.false Bool.false 260835479 Bool.false Bool.true 143262296 

noncomputable def Ns300p354 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz54) qz54 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 618215 1000 160 72 268435456 134217728 4503599627370496 Bool.false 297689967907 2428 

noncomputable def Ns300p355 := Ns300p354 372130544 61 134217720 8 432030192 61 120047984 16 Bool.true 455172480 54079 Bool.false 168095125 Bool.false 243087924 14148475504056880 1 Bool.false 217502131 Bool.false Bool.false 165687702 Bool.false Bool.true 272323629 

noncomputable def Ns300p356 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz54) qz54 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 618215 1000 433 273 268435456 134217728 4503599627370496 Bool.false 297689967907 2428 

noncomputable def Ns300p357 := Ns300p356 186065264 61 189812528 16 294906480 61 154981288 8 Bool.true 268435392 2493 Bool.false 83964283 Bool.false 261880457 14148475504056880 1 Bool.false 82601809 Bool.true Bool.false 222271975 Bool.true Bool.true 455172480 

noncomputable def Ns300p358 := nat_lit 8029983725784446321983166174792117068217441312184961 

noncomputable def Ns300p359 := nat_lit 7240863231830889557368286729059721305272405196800 

noncomputable def Ns300p360 := nat_lit 43345064010461538710705664500000000 

noncomputable def Ns300p361 := nat_lit 160779461562807525373670330483205000000 

noncomputable abbrev qz57 := (@Eq.refl Real qz376)

noncomputable def Ns300p362 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz54 618215 1000 1528760144900 16000000 1236430 4000 2000 Ns300p360 Ns300p361 qz57 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns300p363 := nat_lit 40149918628922231609915830873960585341087206560924805000000 

noncomputable abbrev qz380 := (@HMul.hMul Real Real Real qz623 qz629 (@HSub.hSub Real Real Real qz628 qz630 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz631 (@Nat.cast Real Real.instNatCast 1236430)))))

noncomputable abbrev qz653 := (Real.log (Enclosure.sfrac Bool.false 1528760144900 16000000))

noncomputable abbrev qz654 := (Enclosure.sfrac Bool.false 618215 2000)

noncomputable abbrev qz58 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 618215 4000) qz653) qz380) qz654)

noncomputable abbrev qz381 := (@HSub.hSub Real Real Real qz11 qz58 (@HMul.hMul Real Real Real qz5 qz654 (Real.log Real.pi)))

noncomputable def Ns300p364 := @Enclosure.Real.IsNear.addLit_ft_p qz381 (Enclosure.sfrac Bool.true Ns300p360 Ns300p361) 249720505337546555521 225179981368524800 3267129939648600967 361267200000000000000000 Ns300p360 Ns300p361 0 1 Ns300p363 

noncomputable def Ns300p365 := nat_lit 3351691886141737177625447628800 

noncomputable abbrev qz382 := (@HMul.hMul Real Real Real qz5 qz654 (Real.log Real.pi))

noncomputable def Ns300p366 := @Enclosure.Real.IsNear.subLit_ff_p qz58 qz382 329399224004851548289 225179981368524800 391384593117277 88200000000000000000 4749221722323 13421772800 123643 26843545600 Ns300p365 249720505337546555521 225179981368524800 

noncomputable abbrev qz59 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 618215 4000) qz653) qz380)

noncomputable def Ns300p367 := @Enclosure.Real.IsNear.subLit_ff_p qz59 qz654 79800809019144565581 45035996273704960 391384593117277 88200000000000000000 618215 2000 0 1 131759689601940619315600 329399224004851548289 225179981368524800 391384593117277 88200000000000000000 

noncomputable def Ns300p368 := nat_lit 179695446881241790974012811628249088 

noncomputable def Ns300p369 := nat_lit 55452841628084199479050240 

noncomputable def Ns300p370 := nat_lit 134442053595452295131785720872332977295298232829982854838812534062733667321644367156251094729983359078672039500000000000000000000 

noncomputable def Ns300p371 := nat_lit 1588785330801201857063472291604835409073506631425114217134271314791025058027945769922227265858659065817112900000000000000000000 

noncomputable def Ns300p372 := nat_lit 615899667027611497129898760603532650650044545520916327145539472711239791542184315608458424664461094500000000000000000000 

noncomputable def Ns300p373 := BSN.log_dyadic_bound 480184144900 2577336144900 6 5 Ns300p370 134217728 35280000 Ns300p371 Ns300p372 50603303 3057520289800 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 480184144900) (BSN.artanhQ 2577336144900) 0 5 Ns300p371 Ns300p370 Ns300p372 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns300p374 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 618215 4000) qz653 618215 4000 0 1 3227780202175735 281474976710656 781250441 27562500000000000 79818485507522880521 45035996273704960 96596148276563 22050000000000000000 (Enclosure.Real.IsNear.const Bool.false 618215 4000) (BSN.isNear_log_sfrac 1528760144900 16000000 3227780202175735 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1528760144900) qz335)) Bool.false Ns300p369 Ns300p94 1000000564480000 35280000000000000000000 3227780202175735 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1528760144900 16000000 16 3057520289800 2097152000000 50603303 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns300p373 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns300p375 := BSN.arctan_dyadic_bound_f 1000 1236430 1 0 16777216 4410000 0 1 1 0 1 1 13569 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1236430) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1236430) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns300p376 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1236430))) 884279719003555 562949953421312 1 2000000000000000 13569 16777216 1 4410000 14828113182223973220352 883824418915747 562949953421312 200000000441 882000000000000000 qz16 (Ns300p375 rfl) rfl rfl 

noncomputable abbrev qz60 := qz380

noncomputable def Ns300p377 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 618215 4000) qz653) qz60 79818485507522880521 45035996273704960 96596148276563 22050000000000000000 883824418915747 2251799813685248 200000000441 3528000000000000000 Ns300p368 79800809019144565581 45035996273704960 391384593117277 88200000000000000000 (Ns300p374 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1236430)))) 1 4 0 1 883824418915747 562949953421312 200000000441 882000000000000000 883824418915747 2251799813685248 200000000441 3528000000000000000 qz340 Ns300p376 rfl) 

noncomputable def Ns300p378 := @Ns300p364 Ns300p358 Ns300p359 3267129939648600967 361267200000000000000000 (@Ns300p366 3267129939648600967 361267200000000000000000 (Ns300p367 (Ns300p377 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 618215 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz654 (Real.log Real.pi) 618215 2000 0 1 38410761 33554432 1 67108864 4749221722323 13421772800 123643 26843545600 (Enclosure.Real.IsNear.const Bool.false 618215 2000) RS301to312.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns300p360 Ns300p361) 

noncomputable def Ns300p379 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz54) Bool.false Ns300p358 Ns300p359 3267129939648600967 361267200000000000000000 9302811497 8388608 19 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz54) (@HAdd.hAdd Real Real Real qz341 qz381 (Enclosure.sfrac Bool.true Ns300p360 Ns300p361)) Bool.false Ns300p358 Ns300p359 3267129939648600967 361267200000000000000000 Ns300p362 (Ns300p378 rfl rfl)) 

noncomputable def Ns300p380 := nat_lit 1898181567580016616669184 

noncomputable def Ns300p381 := nat_lit 1208925819614629174706176 

noncomputable def Ns300p382 := nat_lit 3504950632851883695263781192306287288759628439937102431903665335125546379294964434315277977779803078645955208537515314337599881358089084161 

noncomputable def Ns300p383 := nat_lit 69061887427279807374175457422696049589758900585025510522285359577850094671315332446731519433112496475662717985575392155893264493730122956800 

noncomputable def Ns300p384 := nat_lit 2490091532043182873871621778602123566562949881235547750908146893214443572883880306593661393441921549747586658404751628493300387503361 

noncomputable def Ns300p385 := nat_lit 17503012868373520475436867481682126242529960902999534035839561437695080447437146888045764285202614328134489546614630821355059717995984805121 

noncomputable def Ns300p386 := nat_lit 2417166059954793258096141009794361735641561520475892868279987585224753313496036635635603180158937376648195129495138725456264257280554303488000 

noncomputable def Ns300p387 := BSN.sin_dyadic_bound_f 107899129919 68719476736 4 3 33554432 8828614 Ns300p382 Ns300p383 Ns300p384 Ns300p385 Ns300p386 Ns300p384 33554424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107899129919) qz351 0 3 Ns300p382 Ns300p383 Ns300p384 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107899129919) qz352 0 3 Ns300p385 Ns300p386 Ns300p384 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz383 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable abbrev qz655 := (@Nat.cast Real Real.instNatCast Ns300p381)

noncomputable def Ns300p388 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz54) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9302811497) qz383) Bool.false 9302811497 8388608 19 2097152 Bool.true 33554424 33554432 1 4410000 (Ns300p379 rfl) (Enclosure.sfrac_false_div 9302811497 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9302811497) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns300p380) qz655) 226375608064910080 72057594037927936 Bool.false 33554424 33554432 176 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q1 9302811497 8388608 226375608064910080 72057594037927936 176 Ns300p380 Ns300p381 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554424 33554432 Ns300p380 Ns300p381 107899129919 68719476736 8828614 8820000 (Ns300p387 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p389 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz54) Bool.false Ns300p358 Ns300p359 3267129939648600967 361267200000000000000000 297689967907 268435456 2428 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz54) (@HAdd.hAdd Real Real Real qz341 qz381 (Enclosure.sfrac Bool.true Ns300p360 Ns300p361)) Bool.false Ns300p358 Ns300p359 3267129939648600967 361267200000000000000000 Ns300p362 (Ns300p378 rfl rfl)) 

noncomputable def Ns300p390 := Ns300p357 54079 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 433 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 82601809 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 273 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 222271975 268435456) qz57 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz54) qz54 1) Bool.true 4194303 4194304 5367947 578027520000 268435392 268435456 2493 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz54) qz54 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz54)) Bool.true 4194303 4194304 5367947 578027520000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz54) qz54) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz54)) Bool.true 33554424 33554432 85887152 9248440320000 4194303 4194304 5367947 578027520000 (Ns300p388 rfl rfl) rfl)) rfl) (Ns300p389 rfl) RS301to312.d7 

noncomputable def Ns300p391 := nat_lit 49702511557828326814793523319921 

noncomputable def Ns300p392 := nat_lit 623075623024179315423659559506411520 

noncomputable def Ns300p393 := nat_lit 4361529361169255207965616916544880640 

noncomputable def Ns300p394 := BSN.sin_dyadic_bound_f 83964283 268435456 2 1 268435456 134217728 Ns300p391 Ns300p392 Ns300p391 Ns300p391 Ns300p393 Ns300p391 82601809 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 83964283) qz344 0 1 Ns300p391 Ns300p392 Ns300p391 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 83964283) qz345 0 1 Ns300p391 Ns300p393 Ns300p391 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p395 := nat_lit 73872659712325245281030829070554421202538359018358003217471709587639105 

noncomputable def Ns300p396 := nat_lit 22122016962950300525101048176870446871972757303472149373751649569601 

noncomputable def Ns300p397 := nat_lit 193440196933388008582802007773451408140283936774351053518201736725465921 

noncomputable def Ns300p398 := BSN.sin_dyadic_bound_f 261880457 268435456 3 2 268435456 134217728 Ns300p395 Ns300p116 Ns300p396 Ns300p397 Ns300p119 Ns300p396 222271975 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 261880457) qz344 0 2 Ns300p395 Ns300p116 Ns300p396 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 261880457) qz345 0 2 Ns300p397 Ns300p119 Ns300p396 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p399 := nat_lit 6965126653212789192446638444398230232242373600317125226748316650390625 

noncomputable def Ns300p400 := nat_lit 637442400174192116870332348463675721532303942852079868316650390625 

noncomputable def Ns300p401 := nat_lit 20894105074838019193106174668497763345284056193065671520508316650390625 

noncomputable def Ns300p402 := BSN.cos_dyadic_bound_f 168095125 268435456 3 2 268435456 134217728 Ns300p399 Ns300p110 Ns300p400 Ns300p401 Ns300p113 Ns300p400 217502131 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 168095125) qz342 0 2 Ns300p399 Ns300p110 Ns300p400 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 168095125) qz343 0 2 Ns300p401 Ns300p113 Ns300p400 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p403 := nat_lit 30471662388960645967302149395566621398641187364106119809504355779936256 

noncomputable def Ns300p404 := nat_lit 12192901846599944252799339105186349196717217141748767897386945150976 

noncomputable def Ns300p405 := nat_lit 91390601363188738013400849508489491497530127658034861892718293449506816 

noncomputable def Ns300p406 := BSN.cos_dyadic_bound_f 243087924 268435456 3 2 268435456 134217728 Ns300p403 Ns300p110 Ns300p404 Ns300p405 Ns300p113 Ns300p404 165687702 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 243087924) qz342 0 2 Ns300p403 Ns300p110 Ns300p404 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 243087924) qz343 0 2 Ns300p405 Ns300p113 Ns300p404 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p407 := Ns300p355 92128 BSN.abs_quadSignPos (BSN.cos_quad_nat0 160 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 217502131 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 72 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 165687702 268435456) qz57 rfl rfl (Ns300p390 RS301to312.d9 RS301to312.d11 RS301to312.d13 RS301to312.d17 (Ns300p394 rfl rfl) (Ns300p398 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns300p389 rfl) RS301to312.d19 RS301to312.d21 RS301to312.d23 RS301to312.d25 RS301to312.d17 (Ns300p402 rfl rfl) (Ns300p406 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns300p408 := nat_lit 7725477038317695982500999757796121144679671350714360023640179927958219010538770290909339950943021242884390625 

noncomputable def Ns300p409 := nat_lit 2945113166088691722824764703074164816280712379947211497700755798655948276879187038189756659472900390625 

noncomputable def Ns300p410 := nat_lit 46816620186329032859699607391726458470401929938274952580971237446396453906642191232620581987051366560669990625 

noncomputable def Ns300p411 := BSN.cos_dyadic_bound_f 346012535 268435456 4 3 268435456 134217728 Ns300p408 Ns300p122 Ns300p409 Ns300p410 Ns300p125 Ns300p409 74647690 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 346012535) qz342 0 3 Ns300p408 Ns300p122 Ns300p409 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 346012535) qz343 0 3 Ns300p410 Ns300p125 Ns300p409 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p412 := nat_lit 22908813005739751756429236733232502746486576227313123394028784912241007191864061478223667882757439983662534656 

noncomputable def Ns300p413 := nat_lit 4377201686727779064821450834173772203202690610384356926571649111927911975918004372860740553544093536256 

noncomputable def Ns300p414 := nat_lit 114470354322220535064099264008636232696768453554312611058912796686719856249804849118002227096184215797666287616 

noncomputable def Ns300p415 := BSN.sin_dyadic_bound_f 357629262 268435456 4 3 268435456 134217728 Ns300p412 Ns300p237 Ns300p413 Ns300p414 Ns300p240 Ns300p413 260835479 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 357629262) qz344 0 3 Ns300p412 Ns300p237 Ns300p413 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 357629262) qz345 0 3 Ns300p414 Ns300p240 Ns300p413 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p416 := Ns300p353 124192 BSN.abs_quadSignPos (BSN.cos_quad_nat0 0 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 74647690 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 59 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 260835479 268435456) qz57 rfl rfl (Ns300p407 rfl rfl) (Ns300p389 rfl) RS301to312.d27 RS301to312.d29 RS301to312.d31 RS301to312.d33 RS301to312.d17 (Ns300p411 rfl rfl) (Ns300p415 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p417 := nat_lit 7190759967584236443736998786920586503144196006946465966362966506930176 

noncomputable def Ns300p418 := nat_lit 679406849100364524376116317716524341916911027470922458092860932096 

noncomputable def Ns300p419 := nat_lit 21570921089054508602162244128126326460748754198784456054172713798926336 

noncomputable def Ns300p420 := BSN.cos_dyadic_bound_f 169440116 268435456 3 2 268435456 134217728 Ns300p417 Ns300p110 Ns300p418 Ns300p419 Ns300p113 Ns300p418 216711142 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 169440116) qz342 0 2 Ns300p417 Ns300p110 Ns300p418 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 169440116) qz343 0 2 Ns300p419 Ns300p113 Ns300p418 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p421 := nat_lit 5605661840828174521575454265785345985396423463950073645873704276529911883781453289068525745114216637688446976 

noncomputable def Ns300p422 := nat_lit 1126660111332268228367912965364529403536857160821703829103056751998958076298945811485352989953617821696 

noncomputable def Ns300p423 := nat_lit 33980663709181610794488444097656523405641056864229922541727769192459445781945963166414798752690034692723834880 

noncomputable def Ns300p424 := BSN.cos_dyadic_bound_f 319386148 268435456 4 3 268435456 134217728 Ns300p421 Ns300p122 Ns300p422 Ns300p423 Ns300p125 Ns300p422 99815002 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 319386148) qz342 0 3 Ns300p421 Ns300p122 Ns300p422 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 319386148) qz343 0 3 Ns300p423 Ns300p125 Ns300p422 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p425 := Ns300p351 152207 BSN.abs_quadSignPos (BSN.cos_quad_nat0 112 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 216711142 268435456) BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 99815002 268435456) qz57 rfl rfl (Ns300p416 rfl) (Ns300p389 rfl) RS301to312.d35 RS301to312.d37 RS301to312.d39 RS301to312.d41 RS301to312.d17 (Ns300p420 rfl rfl) (Ns300p424 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p426 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz54) qz54 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz54) qz54 9) 99915007 268435456 152207 268435456 99915007 268435456 152207 268435456 53641460930576384 99915007 134217728 152207 134217728 (Ns300p425 rfl) 

noncomputable def Ns300p427 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz379) (Zeta.RiemannSiegel.correction qz56) 5326967 16777216 1 16777216 210346112508621 281474976710656 432746381831401 17240342323527680000 1120506799911711282507 4722366482869645213696 

noncomputable def Ns300p428 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz379 1 1 0 1 5326967 16777216 1 16777216 5326967 16777216 1 16777216 

noncomputable def Ns300p429 := @Enclosure.Real.IsNear.sqrt_image qz55 660297265979 6710886400 123643 6710886400 166417755 166417787 16777216 (@Enclosure.Real.IsNear.of_eq qz55 (@HMul.hMul Real Real Real qz5 qz54 qz3) Bool.false 660297265979 6710886400 123643 6710886400 (BSN.t_div_two_pi_mk qz54 618215 1000 qz57) (@Enclosure.Real.IsNear.mulLit_ff qz54 qz3 618215 1000 0 1 5340353 33554432 1 33554432 660297265979 6710886400 123643 6710886400 (Enclosure.Real.IsNear.const Bool.false 618215 1000) RS301to312.d44 rfl)) 

noncomputable abbrev qz821 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 618215 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz656 := qz821

noncomputable abbrev qz384 := qz656

noncomputable abbrev qz61 := qz384

noncomputable def Ns300p430 := @Enclosure.Real.IsNear.sqrt_image qz61 166417771 16777216 1 1048576 52839631 52839637 16777216 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 332835542 33554432 32 33554432 166417771 16777216 1 1048576 (Ns300p429 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns300p431 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz61) 26419817 8388608 3 16777216 5326966 5326968 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz61) Bool.false 105679268 33554432 6 33554432 26419817 8388608 3 16777216 (Ns300p430 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns300p432 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz61)) Bool.false 10653934 33554432 2 33554432 5326967 16777216 1 16777216 (Ns300p431 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz62 := (@HMul.hMul Real Real Real qz327 qz323 qz378)

noncomputable abbrev qz657 := (@HMul.hMul Real Real Real qz807 qz820 qz820)

noncomputable abbrev qz385 := (@HSub.hSub Real Real Real qz628 (@HSub.hSub Real Real Real qz628 qz657 qz652) qz639)

noncomputable abbrev qz63 := (Real.cos (@HMul.hMul Real Real Real qz327 qz323 qz385))

noncomputable def Ns300p433 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz56) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz62)) qz63) Bool.false 210346112508621 

noncomputable def Ns300p434 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz62)) qz63 19193829 16777216 69 

noncomputable def Ns300p435 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz62)) Bool.false 38387658 33554432 276 33554432 19193829 16777216 69 

noncomputable def Ns300p436 := @Enclosure.Real.IsNear.recentre' (Real.cos qz62) Bool.false 29329737 33554432 462187216 73987522560000 29329737 33554432 28886701 4624220160000 

noncomputable def Ns300p437 := @Enclosure.Real.IsNear.cos_image qz62 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3028265) (@Nat.cast Real Real.instNatCast 524288)) Bool.false 3028265 524288 101 16777216 Bool.false 29329737 33554432 1 

noncomputable def Ns300p438 := nat_lit 26986075417324112652277191 

noncomputable def Ns300p439 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz56 884279719003555 140737488355328 1 500000000000000 15422827 16777216 1 1048576 13638093125800441149985 2361183241434822606848 Ns300p438 

noncomputable def Ns300p440 := @Enclosure.Real.IsNear.subLit_ff_p qz61 qz1 166417771 16777216 1 1048576 9 1 0 1 15422827 15422827 16777216 1 

noncomputable def Ns300p441 := @Ns300p440 1048576 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 332835542 33554432 32 33554432 166417771 16777216 1 1048576 (Ns300p429 rfl rfl rfl rfl rfl rfl) rfl) qz350 

noncomputable def Ns300p442 := @Enclosure.Real.IsNear.recentre' qz62 Bool.false 13638093125800441149985 2361183241434822606848 Ns300p438 Ns300p163 3028265 524288 101 16777216 (@Ns300p439 Ns300p163 RS301to312.d43 (Ns300p441 rfl rfl) rfl) 

noncomputable def Ns300p443 := nat_lit 1925154197369367023124432945360174145459223163787965883874377904004225866169683122918559265 

noncomputable def Ns300p444 := nat_lit 814256554342223440774229429109726571011091104593510542110209159031006231741256342998561 

noncomputable def Ns300p445 := nat_lit 5040752196784169079755118485439040347468709376703902107364716076610731829878731859278990881 

noncomputable def Ns300p446 := BSN.sin_dyadic_bound_f 73087845171 68719476736 3 2 33554432 8828614 Ns300p443 Ns300p170 Ns300p444 Ns300p445 Ns300p173 Ns300p444 29329737 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 73087845171) qz351 0 2 Ns300p443 Ns300p170 Ns300p444 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 73087845171) qz352 0 2 Ns300p445 Ns300p173 Ns300p444 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p447 := @Ns300p437 4410000 (Ns300p442 rfl) (Enclosure.sfrac_false_div 3028265 524288) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3028265) (@Nat.cast Real Real.instNatCast 524288)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 80360935615124954152960) (@Nat.cast Real Real.instNatCast 75557863725914323419136)) 226375608064910080 72057594037927936 Bool.false 29329737 33554432 0 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q3 3028265 524288 226375608064910080 72057594037927936 0 80360935615124954152960 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 29329737 33554432 80360935615124954152960 75557863725914323419136 73087845171 68719476736 8828614 8820000 (Ns300p446 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p448 := @Enclosure.Real.IsNear.inv_image (Real.cos qz62) 29329737 33554432 28886701 4624220160000 19193691 19193967 16777216 (Ns300p436 (Ns300p447 rfl rfl) rfl) rfl 

noncomputable def Ns300p449 := @Enclosure.Real.IsNear.recentre' qz63 Bool.false 10959049 16777216 

noncomputable abbrev qz64 := (@HMul.hMul Real Real Real qz327 qz323 qz385)

noncomputable def Ns300p450 := @Enclosure.Real.IsNear.cos_image qz64 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7205645)) qz383) Bool.true 7205645 8388608 

noncomputable def Ns300p451 := nat_lit 34027696642574175909178933045 

noncomputable def Ns300p452 := nat_lit 128515479281296711058709332700129 

noncomputable def Ns300p453 := @Enclosure.Real.IsNear.recentre' qz64 Bool.true Ns300p451 Ns300p180 Ns300p452 

noncomputable abbrev qz65 := qz385

noncomputable def Ns300p454 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz65 884279719003555 140737488355328 1 500000000000000 38480693282119 

noncomputable abbrev qz386 := (@HSub.hSub Real Real Real qz628 qz657 qz652)

noncomputable abbrev qz66 := qz386

noncomputable def Ns300p455 := @Enclosure.Real.IsNear.subLit_tf qz66 qz27 20888507237703 281474976710656 23811443 8796093022208 1 16 

noncomputable abbrev qz387 := qz657

noncomputable abbrev qz67 := qz387

noncomputable def Ns300p456 := @Enclosure.Real.IsNear.subLit_ff_n qz67 qz56 237863592671929 281474976710656 15422835 8796093022208 15422827 16777216 1 1048576 

noncomputable def Ns300p457 := @Enclosure.Real.IsNear.mulLit_ff qz56 qz56 15422827 16777216 1 1048576 15422827 16777216 1 1048576 237863592671929 281474976710656 

noncomputable def Ns300p458 := nat_lit 22433707051932987031313510019012378257017858622854670190625 

noncomputable def Ns300p459 := nat_lit 988643523323402220304136834155207460536120982503085435781120 

noncomputable def Ns300p460 := nat_lit 7267464109316965352624034094294271415951875426625390625 

noncomputable def Ns300p461 := nat_lit 67286586227580327163235281988848546228221672117710759790625 

noncomputable def Ns300p462 := nat_lit 44488958549553099913686157536984335724125444212638844610150400 

noncomputable def Ns300p463 := BSN.cos_dyadic_bound_f 7205645 8388608 3 2 16777216 4410000 Ns300p458 Ns300p459 Ns300p460 Ns300p461 Ns300p462 Ns300p460 10959049 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 7205645) (BSN.cosEvenQ 8388608) 0 2 Ns300p458 Ns300p459 Ns300p460 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 7205645) (BSN.cosOddQ 8388608) 0 2 Ns300p461 Ns300p462 Ns300p460 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p464 := @Ns300p449 2551664432 147975045120000 10959049 16777216 159479027 9248440320000 (@Ns300p450 571 33554432 Bool.false 10959049 16777216 1 4410000 (@Ns300p453 Ns300p183 7205645 8388608 571 33554432 (@Ns300p454 281474976710656 23811443 8796093022208 Ns300p451 Ns300p180 Ns300p452 Ns300p183 RS301to312.d43 (@Ns300p455 0 1 615691092513904 38480693282119 281474976710656 23811443 8796093022208 (@Ns300p456 350450997844506574848 20888507237703 281474976710656 23811443 8796093022208 (@Ns300p457 15422835 8796093022208 (Ns300p441 rfl rfl) (Ns300p441 rfl rfl) rfl) (Ns300p441 rfl rfl) rfl rfl) qz358 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7205645 8388608) (BSN.cos_neg_of_bound 7205645 8388608 Bool.false 10959049 16777216 1 4410000 (Ns300p463 rfl rfl)) rfl rfl) 

noncomputable def Ns300p465 := @Ns300p427 1159054913761403779209 Ns300p347 (Ns300p428 qz29 (@Enclosure.Real.IsNear.of_eq qz379 (@Inv.inv Real Real.instInv (Real.sqrt qz61)) Bool.false 5326967 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz55 (BSN.t_div_two_pi_nonneg qz54 618215 1000 qz57)) Ns300p432) rfl) (@Ns300p433 281474976710656 432746381831401 17240342323527680000 (BSN.correction_mk qz56 (BSN.cos_two_pi_p_ne_zero_mk qz54 618215 1000 9 qz57 rfl rfl (@BSN.floor_sqrt_eq_dec qz54 618215 1000 9 qz57 rfl rfl rfl))) (@Ns300p434 8388608 10959049 16777216 159479027 9248440320000 210346112508621 281474976710656 432746381831401 17240342323527680000 (@Ns300p435 8388608 (Ns300p448 rfl rfl rfl rfl rfl) rfl) (Ns300p464 rfl) rfl)) 

noncomputable def Ns300p466 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz54) (hardyZApproximantRS₀ qz54) Bool.true 2394939983634542619317 4722366482869645213696 165165353916085003139209 Ns300p347 (@Eq.refl Real (hardyZApproximantRS₀ qz54)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz54) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz54) qz54 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz379) (Zeta.RiemannSiegel.correction qz56))) Bool.true 2394939983634542619317 4722366482869645213696 165165353916085003139209 Ns300p347 (BSN.hardyZApproximantRS₀_eq qz54 9 (@BSN.floor_sqrt_eq_dec qz54 618215 1000 9 qz57 rfl rfl rfl)) (@Ns300p349 2394939983634542619317 4722366482869645213696 165165353916085003139209 Ns300p347 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz54) qz54 9) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz54) qz54 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz54) qz54 9)) Bool.true 99915007 134217728 152207 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz54) qz54 9) (Ns300p426 (Ns300p425 rfl) rfl rfl)) (Ns300p465 rfl) rfl rfl)) 

theorem RS301to312.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz54) Bool.true 2394939983634542619317 4722366482869645213696 165165353916085003139209 Ns300p347 := Ns300p466 

noncomputable def Ns300p467 := nat_lit 162700282730118245253120000 

noncomputable def Ns300p468 := nat_lit 17269597256301716695999840256 

noncomputable abbrev qz822 := (Enclosure.sfrac Bool.false 619584 1000)

noncomputable abbrev qz658 := qz822

noncomputable abbrev qz388 := qz658

noncomputable abbrev qz68 := qz388

noncomputable abbrev qz823 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 619584 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz659 := qz823

noncomputable abbrev qz389 := qz659

noncomputable abbrev qz69 := qz389

noncomputable abbrev qz824 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 619584 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz660 := qz824

noncomputable abbrev qz390 := qz660

noncomputable abbrev qz70 := qz390

noncomputable abbrev qz391 := (@HPow.hPow Real Real Real qz627 qz69 qz8)

noncomputable def Ns300p469 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz68) qz68 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz391) (Zeta.RiemannSiegel.correction qz70)) 42132527 67108864 38137 33554432 72036239092636017771 295147905179352825856 1312692199534887496019 Ns300p467 Ns300p468 

noncomputable def Ns300p470 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz68) qz68 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 619584 1000 112 158 268435456 134217728 4503599627370496 Bool.false 298533365345 2434 

noncomputable def Ns300p471 := Ns300p470 558195838 62 94906264 8 589812974 62 89478488 8 Bool.false 38730715 124470 Bool.true 90212780 Bool.true 283442671 14148475504056880 1 Bool.false 253418742 Bool.false Bool.false 132188140 Bool.true Bool.false 84265054 

noncomputable def Ns300p472 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz68) qz68 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 619584 1000 1 59 268435456 134217728 4503599627370496 Bool.false 298533365345 2434 

noncomputable def Ns300p473 := Ns300p472 480971758 62 109588312 8 522351262 62 101459064 8 Bool.false 5617290 92335 Bool.false 109302208 Bool.true 229330702 14148475504056880 1 Bool.false 106306807 Bool.true Bool.false 202434363 Bool.false Bool.false 38730715 

noncomputable def Ns300p474 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz68) qz68 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 619584 1000 161 73 268435456 134217728 4503599627370496 Bool.false 298533365345 2434 

noncomputable def Ns300p475 := Ns300p474 372130544 61 134217720 8 432030192 61 120047984 16 Bool.false 77622144 54202 Bool.false 80388420 Bool.false 73378601 14148475504056880 1 Bool.false 79192225 Bool.true Bool.false 72468154 Bool.true Bool.false 5617290 

noncomputable def Ns300p476 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz68) qz68 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 619584 1000 434 274 268435456 134217728 4503599627370496 Bool.false 298533365345 2434 

noncomputable def Ns300p477 := Ns300p476 186065264 61 189812528 16 294906480 61 154981288 8 Bool.false 268435432 2501 Bool.false 250980947 Bool.false 279893495 14148475504056880 1 Bool.false 159406911 Bool.true Bool.false 135265510 Bool.true Bool.false 77622144 

noncomputable def Ns300p478 := nat_lit 4323493946127475377118695839618123916552978428851441 

noncomputable def Ns300p479 := nat_lit 3887602538487431137238629638876871025414373376000 

noncomputable def Ns300p480 := nat_lit 43827119142182137119828038123520000 

noncomputable def Ns300p481 := nat_lit 162927540235160292289907423546034094080 

noncomputable abbrev qz71 := (@Eq.refl Real qz388)

noncomputable def Ns300p482 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz68 619584 1000 1535538332224 16000000 1239168 4000 2000 Ns300p480 Ns300p481 qz71 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns300p483 := nat_lit 51002009865613840736673153098138406419138878976377446727680 

noncomputable abbrev qz392 := (@HMul.hMul Real Real Real qz623 qz629 (@HSub.hSub Real Real Real qz628 qz630 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz631 (@Nat.cast Real Real.instNatCast 1239168)))))

noncomputable abbrev qz661 := (Real.log (Enclosure.sfrac Bool.false 1535538332224 16000000))

noncomputable abbrev qz662 := (Enclosure.sfrac Bool.false 619584 2000)

noncomputable abbrev qz72 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 619584 4000) qz661) qz392) qz662)

noncomputable abbrev qz393 := (@HSub.hSub Real Real Real qz11 qz72 (@HMul.hMul Real Real Real qz5 qz662 (Real.log Real.pi)))

noncomputable def Ns300p484 := @Enclosure.Real.IsNear.addLit_ft_p qz393 (Enclosure.sfrac Bool.true Ns300p480 Ns300p481) 313034997817052776921 281474976710656000 255806207110286389 28224000000000000000000 Ns300p480 Ns300p481 0 1 Ns300p483 

noncomputable def Ns300p485 := nat_lit 328240985871013932612714496000 

noncomputable abbrev qz394 := (@HMul.hMul Real Real Real qz5 qz662 (Real.log Real.pi))

noncomputable def Ns300p486 := @Enclosure.Real.IsNear.subLit_ff_p qz72 qz394 412853950824427833817 281474976710656000 1961201093001301 441000000000000000000 371854577241 1048576000 9681 2097152000 Ns300p485 313034997817052776921 281474976710656000 

noncomputable abbrev qz73 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 619584 4000) qz661) qz392)

noncomputable def Ns300p487 := @Enclosure.Real.IsNear.subLit_ff_p qz73 qz662 500052646809575377369 281474976710656000 1961201093001301 441000000000000000000 619584 2000 0 1 825707901648855667634000 412853950824427833817 281474976710656000 1961201093001301 441000000000000000000 

noncomputable def Ns300p488 := nat_lit 70376153557413559843117908761772032 

noncomputable def Ns300p489 := nat_lit 55474234699091728847077376 

noncomputable def Ns300p490 := nat_lit 138019910524115688646684036471311674753076258337578491254733550703317324987796608559349767694129083379918922764982797425201643520 

noncomputable def Ns300p491 := nat_lit 1669476427557621838782929638401808821546484000986065137445078203790305904646001219524359502196919606128229762162452628980629504 

noncomputable def Ns300p492 := nat_lit 708574462168105230143672836299257324489803356691115980441054784384756621532019472137783916497122063963266435510509240320 

noncomputable def Ns300p493 := BSN.log_dyadic_bound 486962332224 2584114332224 6 5 Ns300p490 134217728 35280000 Ns300p491 Ns300p492 51197080 3071076664448 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 486962332224) (BSN.artanhQ 2584114332224) 0 5 Ns300p491 Ns300p490 Ns300p492 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns300p494 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 619584 4000) qz661 619584 4000 0 1 3229025442798839 281474976710656 781250441 27562500000000000 31260195311735560359 17592186044416000 360156453301 82031250000000000 (Enclosure.Real.IsNear.const Bool.false 619584 4000) (BSN.isNear_log_sfrac 1535538332224 16000000 3229025442798839 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1535538332224) qz335)) Bool.false Ns300p489 Ns300p94 1000000564480000 35280000000000000000000 3229025442798839 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1535538332224 16000000 16 3071076664448 2097152000000 51197080 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns300p493 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns300p495 := BSN.arctan_dyadic_bound_f 1000 1239168 1 0 16777216 4410000 0 1 1 0 1 1 13539 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1239168) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1239168) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns300p496 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1239168))) 884279719003555 562949953421312 1 2000000000000000 13539 16777216 1 4410000 14828130070722575859712 883825425548707 562949953421312 200000000441 882000000000000000 qz16 (Ns300p495 rfl) rfl rfl 

noncomputable abbrev qz74 := qz392

noncomputable def Ns300p497 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 619584 4000) qz661) qz74 31260195311735560359 17592186044416000 360156453301 82031250000000000 883825425548707 2251799813685248 200000000441 3528000000000000000 Ns300p488 500052646809575377369 281474976710656000 1961201093001301 441000000000000000000 (Ns300p494 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1239168)))) 1 4 0 1 883825425548707 562949953421312 200000000441 882000000000000000 883825425548707 2251799813685248 200000000441 3528000000000000000 qz340 Ns300p496 rfl) 

noncomputable def Ns300p498 := @Ns300p484 Ns300p478 Ns300p479 255806207110286389 28224000000000000000000 (@Ns300p486 255806207110286389 28224000000000000000000 (Ns300p487 (Ns300p497 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 619584 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz662 (Real.log Real.pi) 619584 2000 0 1 38410761 33554432 1 67108864 371854577241 1048576000 9681 2097152000 (Enclosure.Real.IsNear.const Bool.false 619584 2000) RS301to312.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns300p480 Ns300p481) 

noncomputable def Ns300p499 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz68) Bool.false Ns300p478 Ns300p479 255806207110286389 28224000000000000000000 9329167667 8388608 305 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz68) (@HAdd.hAdd Real Real Real qz341 qz393 (Enclosure.sfrac Bool.true Ns300p480 Ns300p481)) Bool.false Ns300p478 Ns300p479 255806207110286389 28224000000000000000000 Ns300p482 (Ns300p498 rfl rfl)) 

noncomputable def Ns300p500 := nat_lit 1898553490452908441862144 

noncomputable def Ns300p501 := nat_lit 3507703949963622501087845753800971698975618446144176768786737447905922109155527811405534561454307757888624568924232398256096884875435328481 

noncomputable def Ns300p502 := nat_lit 2495952640687641881038259926214073613053281474166000117122035682592759071318631347659609757391460354985624183094996510134387763725281 

noncomputable def Ns300p503 := nat_lit 17516745345008413432370135708647566811951478038124889415301542775295194364071848075327134961158842143618081282364131463126981185531764687841 

noncomputable def Ns300p504 := BSN.sin_dyadic_bound_f 107920271287 68719476736 4 3 33554432 8828614 Ns300p501 Ns300p383 Ns300p502 Ns300p503 Ns300p386 Ns300p502 33554429 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107920271287) qz351 0 3 Ns300p501 Ns300p383 Ns300p502 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107920271287) qz352 0 3 Ns300p503 Ns300p386 Ns300p502 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p505 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz68) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9329167667) qz383) Bool.false 9329167667 8388608 305 33554432 Bool.false 33554429 33554432 1 4410000 (Ns300p499 rfl) (Enclosure.sfrac_false_div 9329167667 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9329167667) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns300p500) qz655) 226375608064910080 72057594037927936 Bool.false 33554429 33554432 176 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q3 9329167667 8388608 226375608064910080 72057594037927936 176 Ns300p500 Ns300p381 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554429 33554432 Ns300p500 Ns300p381 107920271287 68719476736 8828614 8820000 (Ns300p504 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p506 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz68) Bool.false Ns300p478 Ns300p479 255806207110286389 28224000000000000000000 298533365345 268435456 2434 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz68) (@HAdd.hAdd Real Real Real qz341 qz393 (Enclosure.sfrac Bool.true Ns300p480 Ns300p481)) Bool.false Ns300p478 Ns300p479 255806207110286389 28224000000000000000000 Ns300p482 (Ns300p498 rfl rfl)) 

noncomputable def Ns300p507 := Ns300p477 54202 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 434 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 159406911 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 274 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 135265510 268435456) qz71 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz68) qz68 1) Bool.false 33554429 33554432 86162777 9248440320000 268435432 268435456 2501 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz68) qz68 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz68)) Bool.false 33554429 33554432 86162777 9248440320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz68) qz68) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz68)) Bool.false 33554429 33554432 1378604432 147975045120000 33554429 33554432 86162777 9248440320000 (Ns300p505 rfl rfl) rfl)) rfl) (Ns300p506 rfl) RS301to312.d7 

noncomputable def Ns300p508 := nat_lit 34628152099957412392590639295768790404557426644292470123497573210571041 

noncomputable def Ns300p509 := nat_lit 15744396893448623474324580693869173137454434737909391317868181635361 

noncomputable def Ns300p510 := nat_lit 103852967506085339930823268725918632867397371063401591587856983268442401 

noncomputable def Ns300p511 := BSN.cos_dyadic_bound_f 250980947 268435456 3 2 268435456 134217728 Ns300p508 Ns300p110 Ns300p509 Ns300p510 Ns300p113 Ns300p509 159406911 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 250980947) qz342 0 2 Ns300p508 Ns300p110 Ns300p509 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 250980947) qz343 0 2 Ns300p510 Ns300p113 Ns300p509 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p512 := nat_lit 3304619397688565694878347759273985282418665286419260210350114162384156832544709776426527352299326003084390625 

noncomputable def Ns300p513 := nat_lit 231160519512142806028466284098629310159773981147986305974939763304896220973542825610476512597900390625 

noncomputable def Ns300p514 := nat_lit 20038626433466030953673740150235312625212906024019356461617421298689626597750691818028304663539428192549990625 

noncomputable def Ns300p515 := BSN.cos_dyadic_bound_f 279893495 268435456 4 3 268435456 134217728 Ns300p512 Ns300p122 Ns300p513 Ns300p514 Ns300p125 Ns300p513 135265510 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 279893495) qz342 0 3 Ns300p512 Ns300p122 Ns300p513 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 279893495) qz343 0 3 Ns300p514 Ns300p125 Ns300p513 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p516 := nat_lit 41761296346771655967905292960000 

noncomputable def Ns300p517 := BSN.sin_dyadic_bound_f 80388420 268435456 2 1 268435456 134217728 Ns300p516 Ns300p392 Ns300p516 Ns300p516 Ns300p393 Ns300p516 79192225 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 80388420) qz344 0 1 Ns300p516 Ns300p392 Ns300p516 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 80388420) qz345 0 1 Ns300p516 Ns300p393 Ns300p516 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p518 := nat_lit 28991968879866820559442145274401 

noncomputable def Ns300p519 := BSN.sin_dyadic_bound_f 73378601 268435456 2 1 268435456 134217728 Ns300p518 Ns300p392 Ns300p518 Ns300p518 Ns300p393 Ns300p518 72468154 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 73378601) qz344 0 1 Ns300p518 Ns300p392 Ns300p518 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 73378601) qz345 0 1 Ns300p518 Ns300p393 Ns300p518 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p520 := Ns300p475 92335 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 161 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 79192225 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 73 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 72468154 268435456) qz71 rfl rfl (Ns300p507 RS301to312.d9 RS301to312.d11 RS301to312.d13 RS301to312.d17 (Ns300p511 rfl rfl) (Ns300p515 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns300p506 rfl) RS301to312.d19 RS301to312.d21 RS301to312.d23 RS301to312.d25 RS301to312.d17 (Ns300p517 rfl rfl) (Ns300p519 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns300p521 := nat_lit 142730156065543486039577325469696 

noncomputable def Ns300p522 := BSN.sin_dyadic_bound_f 109302208 268435456 2 1 268435456 134217728 Ns300p521 Ns300p392 Ns300p521 Ns300p521 Ns300p393 Ns300p521 106306807 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 109302208) qz344 0 1 Ns300p521 Ns300p392 Ns300p521 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 109302208) qz345 0 1 Ns300p521 Ns300p393 Ns300p521 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p523 := nat_lit 43437678005997262411379937236179576916145718845330494982548993057931520 

noncomputable def Ns300p524 := nat_lit 7650637127452420799156487974037328019602556522918721504433472717056 

noncomputable def Ns300p525 := nat_lit 113752960412738859538986915590417117201683240455780856548049708576850176 

noncomputable def Ns300p526 := BSN.sin_dyadic_bound_f 229330702 268435456 3 2 268435456 134217728 Ns300p523 Ns300p116 Ns300p524 Ns300p525 Ns300p119 Ns300p524 202434363 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 229330702) qz344 0 2 Ns300p523 Ns300p116 Ns300p524 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 229330702) qz345 0 2 Ns300p525 Ns300p119 Ns300p524 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p527 := Ns300p473 124470 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 1 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 106306807 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 59 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 202434363 268435456) qz71 rfl rfl (Ns300p520 rfl rfl) (Ns300p506 rfl) RS301to312.d27 RS301to312.d29 RS301to312.d31 RS301to312.d33 RS301to312.d17 (Ns300p522 rfl rfl) (Ns300p526 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p528 := nat_lit 577755859402410263878397313367598007203413123382538686984302796800000 

noncomputable def Ns300p529 := nat_lit 4386766619193005335603608375854136351009304446221303833600000000 

noncomputable def Ns300p530 := nat_lit 1733258804673992405624520732886042313337537351538723618345241190400000 

noncomputable def Ns300p531 := BSN.cos_dyadic_bound_f 90212780 268435456 3 2 268435456 134217728 Ns300p528 Ns300p110 Ns300p529 Ns300p530 Ns300p113 Ns300p529 253418742 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 90212780) qz342 0 2 Ns300p528 Ns300p110 Ns300p529 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 90212780) qz343 0 2 Ns300p530 Ns300p113 Ns300p529 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p532 := nat_lit 3475577219792382868334342239231593315304019569871054204776338853118592921281636861902296097879714092147645121 

noncomputable def Ns300p533 := nat_lit 268895034585104679293376219540844305830203605411881092573716642686371946470835886808819478159360629441 

noncomputable def Ns300p534 := nat_lit 21074773727254717074125479137679604587846017473569438559318806043940687359354215697423127993528546004924734145 

noncomputable def Ns300p535 := BSN.cos_dyadic_bound_f 283442671 268435456 4 3 268435456 134217728 Ns300p532 Ns300p122 Ns300p533 Ns300p534 Ns300p125 Ns300p533 132188140 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 283442671) qz342 0 3 Ns300p532 Ns300p122 Ns300p533 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 283442671) qz343 0 3 Ns300p534 Ns300p125 Ns300p533 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p536 := Ns300p471 152548 BSN.abs_quadSignPos (BSN.cos_quad_nat0 112 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 253418742 268435456) BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132188140 268435456) qz71 rfl rfl (Ns300p527 rfl) (Ns300p506 rfl) RS301to312.d35 RS301to312.d37 RS301to312.d39 RS301to312.d41 RS301to312.d17 (Ns300p531 rfl rfl) (Ns300p535 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p537 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz68) qz68 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz68) qz68 9) 84265054 268435456 152548 268435456 84265054 268435456 152548 268435456 45239456390709248 42132527 67108864 38137 33554432 (Ns300p536 rfl) 

noncomputable def Ns300p538 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz391) (Zeta.RiemannSiegel.correction qz70) 2662011 8388608 1 16777216 27060834494161 35184372088832 122579631702139 4848846278492160000 72036239092636017771 295147905179352825856 

noncomputable def Ns300p539 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz391 1 1 0 1 2662011 8388608 1 16777216 2662011 8388608 1 16777216 

noncomputable def Ns300p540 := @Enclosure.Real.IsNear.sqrt_image qz69 51699957393 524288000 9681 524288000 166601914 166601947 16777216 (@Enclosure.Real.IsNear.of_eq qz69 (@HMul.hMul Real Real Real qz5 qz68 qz3) Bool.false 51699957393 524288000 9681 524288000 (BSN.t_div_two_pi_mk qz68 619584 1000 qz71) (@Enclosure.Real.IsNear.mulLit_ff qz68 qz3 619584 1000 0 1 5340353 33554432 1 33554432 51699957393 524288000 9681 524288000 (Enclosure.Real.IsNear.const Bool.false 619584 1000) RS301to312.d44 rfl)) 

noncomputable abbrev qz825 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 619584 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz663 := qz825

noncomputable abbrev qz395 := qz663

noncomputable abbrev qz75 := qz395

noncomputable def Ns300p541 := @Enclosure.Real.IsNear.sqrt_image qz75 333203861 33554432 33 33554432 52868859 52868865 16777216 (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 333203861 33554432 33 33554432 333203861 33554432 33 33554432 (Ns300p540 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns300p542 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz75) 26434431 8388608 3 16777216 5324021 5324023 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz75) Bool.false 105737724 33554432 6 33554432 26434431 8388608 3 16777216 (Ns300p541 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns300p543 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz75)) Bool.false 10648044 33554432 2 33554432 2662011 8388608 1 16777216 (Ns300p542 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz327 qz323 qz390)

noncomputable abbrev qz664 := (@HMul.hMul Real Real Real qz807 qz824 qz824)

noncomputable abbrev qz396 := (@HSub.hSub Real Real Real qz628 (@HSub.hSub Real Real Real qz628 qz664 qz660) qz639)

noncomputable abbrev qz77 := (Real.cos (@HMul.hMul Real Real Real qz327 qz323 qz396))

noncomputable def Ns300p544 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz70) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz76)) qz77) Bool.false 27060834494161 

noncomputable def Ns300p545 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz76)) qz77 4632073 4194304 33 

noncomputable def Ns300p546 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz76)) Bool.false 37056584 33554432 264 33554432 4632073 4194304 33 

noncomputable def Ns300p547 := @Enclosure.Real.IsNear.recentre' (Real.cos qz76) Bool.false 30383262 33554432 59427152 9248440320000 15191631 16777216 3714197 578027520000 

noncomputable abbrev qz665 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable def Ns300p548 := @Enclosure.Real.IsNear.cos_image qz76 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24515397) qz665) Bool.false 24515397 4194304 13 2097152 Bool.false 30383262 33554432 1 

noncomputable def Ns300p549 := nat_lit 890540488766579486447029927 

noncomputable def Ns300p550 := nat_lit 144115188075855872000000000000000 

noncomputable def Ns300p551 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz70 884279719003555 140737488355328 1 500000000000000 31213973 33554432 33 33554432 27601883273424552674015 4722366482869645213696 Ns300p549 

noncomputable def Ns300p552 := @Enclosure.Real.IsNear.subLit_ff_p qz75 qz1 333203861 33554432 33 33554432 9 1 0 1 31213973 31213973 33554432 33 

noncomputable def Ns300p553 := @Ns300p552 33554432 (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 333203861 33554432 33 33554432 333203861 33554432 33 33554432 (Ns300p540 rfl rfl rfl rfl rfl rfl) rfl) qz350 

noncomputable def Ns300p554 := @Enclosure.Real.IsNear.recentre' qz76 Bool.false 27601883273424552674015 4722366482869645213696 Ns300p549 Ns300p550 24515397 4194304 13 2097152 (@Ns300p551 Ns300p550 RS301to312.d43 (Ns300p553 rfl rfl) rfl) 

noncomputable def Ns300p555 := nat_lit 2475520661951464560895296201951692732034203506525674967115574236251941623590555140121595425 

noncomputable def Ns300p556 := nat_lit 1346041254172712690613623086383147730151707527009157720491477731747270298162257729064481 

noncomputable def Ns300p557 := nat_lit 6481327190699460886560020377257432059002668323952086277564755845284637243206810283042836001 

noncomputable def Ns300p558 := BSN.sin_dyadic_bound_f 77827359539 68719476736 3 2 33554432 8828614 Ns300p555 Ns300p170 Ns300p556 Ns300p557 Ns300p173 Ns300p556 30383262 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 77827359539) qz351 0 2 Ns300p555 Ns300p170 Ns300p556 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 77827359539) qz352 0 2 Ns300p557 Ns300p173 Ns300p556 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p559 := @Ns300p548 4410000 (Ns300p554 rfl) (Enclosure.sfrac_false_div 24515397 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24515397) qz665) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 684576694182018992308224) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 30383262 33554432 0 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q3 24515397 4194304 226375608064910080 72057594037927936 0 684576694182018992308224 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 30383262 33554432 684576694182018992308224 604462909807314587353088 77827359539 68719476736 8828614 8820000 (Ns300p558 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p560 := @Enclosure.Real.IsNear.inv_image (Real.cos qz76) 15191631 16777216 3714197 578027520000 18528160 18528424 16777216 (Ns300p547 (Ns300p559 rfl rfl) rfl) rfl 

noncomputable def Ns300p561 := @Enclosure.Real.IsNear.recentre' qz77 Bool.false 11684114 16777216 

noncomputable abbrev qz78 := (@HMul.hMul Real Real Real qz327 qz323 qz396)

noncomputable def Ns300p562 := @Enclosure.Real.IsNear.cos_image qz78 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6714151)) qz383) Bool.true 6714151 8388608 

noncomputable def Ns300p563 := nat_lit 126826729452293724008840068405 

noncomputable def Ns300p564 := nat_lit 158456325028528675187087900672 

noncomputable def Ns300p565 := nat_lit 85476223180431337491236412273487853 

noncomputable def Ns300p566 := @Enclosure.Real.IsNear.recentre' qz78 Bool.true Ns300p563 Ns300p564 Ns300p565 

noncomputable def Ns300p567 := nat_lit 4835703278458516698824704000000000000000 

noncomputable abbrev qz79 := qz396

noncomputable def Ns300p568 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz79 884279719003555 140737488355328 1 500000000000000 143423768211271 

noncomputable abbrev qz397 := (@HSub.hSub Real Real Real qz628 qz664 qz660)

noncomputable abbrev qz80 := qz397

noncomputable def Ns300p569 := @Enclosure.Real.IsNear.subLit_tf qz80 qz27 73055024033607 1125899906842624 3167419563 1125899906842624 1 16 

noncomputable abbrev qz398 := qz664

noncomputable abbrev qz81 := qz398

noncomputable def Ns300p570 := @Enclosure.Real.IsNear.subLit_ff_n qz81 qz70 974312110444729 1125899906842624 2060123307 1125899906842624 31213973 33554432 33 33554432 

noncomputable def Ns300p571 := @Enclosure.Real.IsNear.mulLit_ff qz70 qz70 31213973 33554432 33 33554432 31213973 33554432 33 33554432 974312110444729 1125899906842624 

noncomputable def Ns300p572 := nat_lit 16909835316816070252887524453841171846574343094200280876481 

noncomputable def Ns300p573 := nat_lit 4129798229864454668754204685620480149325819804986443201 

noncomputable def Ns300p574 := nat_lit 50721246353988481849325064952152274579424377642990869743041 

noncomputable def Ns300p575 := BSN.cos_dyadic_bound_f 6714151 8388608 3 2 16777216 4410000 Ns300p572 Ns300p459 Ns300p573 Ns300p574 Ns300p462 Ns300p573 11684114 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 6714151) (BSN.cosEvenQ 8388608) 0 2 Ns300p572 Ns300p459 Ns300p573 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 6714151) (BSN.cosOddQ 8388608) 0 2 Ns300p574 Ns300p462 Ns300p573 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p576 := @Ns300p561 1326547216 73987522560000 5842057 8388608 82909201 4624220160000 (@Ns300p562 297 16777216 Bool.false 11684114 16777216 1 4410000 (@Ns300p566 Ns300p567 6714151 8388608 297 16777216 (@Ns300p568 1125899906842624 3167419563 1125899906842624 Ns300p563 Ns300p564 Ns300p565 Ns300p567 RS301to312.d43 (@Ns300p569 0 1 2294780291380336 143423768211271 1125899906842624 3167419563 1125899906842624 (@Ns300p570 2451319836194031796224 73055024033607 1125899906842624 3167419563 1125899906842624 (@Ns300p571 2060123307 1125899906842624 (Ns300p553 rfl rfl) (Ns300p553 rfl rfl) rfl) (Ns300p553 rfl rfl) rfl rfl) qz358 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6714151 8388608) (BSN.cos_neg_of_bound 6714151 8388608 Bool.false 11684114 16777216 1 4410000 (Ns300p575 rfl rfl)) rfl rfl) 

noncomputable def Ns300p577 := @Ns300p538 1312692199534887496019 Ns300p467 (Ns300p539 qz29 (@Enclosure.Real.IsNear.of_eq qz391 (@Inv.inv Real Real.instInv (Real.sqrt qz75)) Bool.false 2662011 8388608 1 16777216 (BSN.rpow_neg_quarter_mk qz69 (BSN.t_div_two_pi_nonneg qz68 619584 1000 qz71)) Ns300p543) rfl) (@Ns300p544 35184372088832 122579631702139 4848846278492160000 (BSN.correction_mk qz70 (BSN.cos_two_pi_p_ne_zero_mk qz68 619584 1000 9 qz71 rfl rfl (@BSN.floor_sqrt_eq_dec qz68 619584 1000 9 qz71 rfl rfl rfl))) (@Ns300p545 4194304 5842057 8388608 82909201 4624220160000 27060834494161 35184372088832 122579631702139 4848846278492160000 (@Ns300p546 4194304 (Ns300p560 rfl rfl rfl rfl rfl) rfl) (Ns300p576 rfl) rfl)) 

noncomputable def Ns300p578 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz68) (hardyZApproximantRS₀ qz68) Bool.false 257337052468981097579 295147905179352825856 186233142722390393416019 Ns300p467 (@Eq.refl Real (hardyZApproximantRS₀ qz68)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz68) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz68) qz68 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz391) (Zeta.RiemannSiegel.correction qz70))) Bool.false 257337052468981097579 295147905179352825856 186233142722390393416019 Ns300p467 (BSN.hardyZApproximantRS₀_eq qz68 9 (@BSN.floor_sqrt_eq_dec qz68 619584 1000 9 qz71 rfl rfl rfl)) (@Ns300p469 257337052468981097579 295147905179352825856 186233142722390393416019 Ns300p467 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz68) qz68 9) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz68) qz68 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz68) qz68 9)) Bool.false 42132527 67108864 38137 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz68) qz68 9) (Ns300p537 (Ns300p536 rfl) rfl rfl)) (Ns300p577 rfl) rfl rfl)) 

theorem RS301to312.d50 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz68) Bool.false 257337052468981097579 295147905179352825856 186233142722390393416019 Ns300p467 := Ns300p578 

noncomputable def Ns300p579 := nat_lit 18077809192235360583680000 

noncomputable def Ns300p580 := nat_lit 101768055301788537473147600896 

noncomputable abbrev qz826 := (Enclosure.sfrac Bool.false 620952 1000)

noncomputable abbrev qz666 := qz826

noncomputable abbrev qz399 := qz666

noncomputable abbrev qz82 := qz399

noncomputable abbrev qz827 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 620952 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz667 := qz827

noncomputable abbrev qz400 := qz667

noncomputable abbrev qz83 := qz400

noncomputable abbrev qz828 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 620952 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz668 := qz828

noncomputable abbrev qz401 := qz668

noncomputable abbrev qz84 := qz401

noncomputable abbrev qz402 := (@HPow.hPow Real Real Real qz627 qz83 qz8)

noncomputable def Ns300p581 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz82) qz82 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz402) (Zeta.RiemannSiegel.correction qz84)) 206099365 134217728 76443 67108864 148203494960823055853 590295810358705651712 139233546596410278331 Ns300p579 Ns300p580 

noncomputable def Ns300p582 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz82) qz82 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 620952 1000 112 158 268435456 134217728 4503599627370496 Bool.false 299376551898 2439 

noncomputable def Ns300p583 := Ns300p582 558195838 62 94906264 8 589812974 62 89478488 8 Bool.true 246765587 124747 Bool.true 10638133 Bool.true 247120267 14148475504056880 1 Bool.false 268224688 Bool.false Bool.false 162496565 Bool.true Bool.true 206099365 

noncomputable def Ns300p584 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz82) qz82 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 620952 1000 1 59 268435456 134217728 4503599627370496 Bool.false 299376551898 2439 

noncomputable def Ns300p585 := Ns300p584 480971758 62 109588312 8 522351262 62 101459064 8 Bool.true 186422578 92541 Bool.false 294519396 Bool.true 100720675 14148475504056880 1 Bool.false 238886142 Bool.true Bool.false 98373922 Bool.false Bool.true 246765587 

noncomputable def Ns300p586 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz82) qz82 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 620952 1000 161 73 268435456 134217728 4503599627370496 Bool.false 299376551898 2439 

noncomputable def Ns300p587 := Ns300p586 372130544 61 134217720 8 432030192 61 120047984 16 Bool.false 60182804 54324 Bool.false 414500389 Bool.false 325547851 14148475504056880 1 Bool.false 268340050 Bool.true Bool.false 251413120 Bool.true Bool.true 186422578 

noncomputable def Ns300p588 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz82) qz82 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 620952 1000 435 275 268435456 134217728 4503599627370496 Bool.false 299376551898 2439 

noncomputable def Ns300p589 := Ns300p588 186065264 61 189812528 16 294906480 61 154981288 8 Bool.true 268435360 2509 Bool.false 417972790 Bool.false 297990555 14148475504056880 1 Bool.false 268410168 Bool.false Bool.false 240449378 Bool.false Bool.false 60182804 

noncomputable def Ns300p590 := nat_lit 4393460978303070462514951201770396650855832896067439 

noncomputable def Ns300p591 := nat_lit 3939389019110952333580085732581670126306197504000 

noncomputable def Ns300p592 := nat_lit 44313096828656201926663332495360000 

noncomputable def Ns300p593 := nat_lit 165097886566066048118382560057728696320 

noncomputable abbrev qz85 := (@Eq.refl Real qz399)

noncomputable def Ns300p594 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz82 620952 1000 1542326545216 16000000 1241904 4000 2000 Ns300p592 Ns300p593 qz85 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns300p595 := nat_lit 51827374561332604649648371552660448683887815641801622814720 

noncomputable abbrev qz403 := (@HMul.hMul Real Real Real qz623 qz629 (@HSub.hSub Real Real Real qz628 qz630 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz631 (@Nat.cast Real Real.instNatCast 1241904)))))

noncomputable abbrev qz669 := (Real.log (Enclosure.sfrac Bool.false 1542326545216 16000000))

noncomputable abbrev qz670 := (Enclosure.sfrac Bool.false 620952 2000)

noncomputable abbrev qz86 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 620952 4000) qz669) qz403) qz670)

noncomputable abbrev qz404 := (@HSub.hSub Real Real Real qz11 qz86 (@HMul.hMul Real Real Real qz5 qz670 (Real.log Real.pi)))

noncomputable def Ns300p596 := @Enclosure.Real.IsNear.addLit_ft_p qz404 (Enclosure.sfrac Bool.true Ns300p592 Ns300p593) 313919142833007164371 281474976710656000 2050939819201809311 225792000000000000000000 Ns300p592 Ns300p593 0 1 Ns300p595 

noncomputable def Ns300p597 := nat_lit 2633344632922106563099885568000 

noncomputable abbrev qz405 := (@HMul.hMul Real Real Real qz5 qz670 (Real.log Real.pi))

noncomputable def Ns300p598 := @Enclosure.Real.IsNear.subLit_ff_p qz86 qz405 413958489407217531859 281474976710656000 1965476095414453 441000000000000000000 2981404858059 8388608000 77619 16777216000 Ns300p597 313919142833007164371 281474976710656000 

noncomputable abbrev qz87 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 620952 4000) qz669) qz403)

noncomputable def Ns300p599 := @Enclosure.Real.IsNear.subLit_ff_p qz87 qz670 100269942855287032823 56294995342131200 1965476095414453 441000000000000000000 620952 2000 0 1 165583395762887012743600 413958489407217531859 281474976710656000 1965476095414453 441000000000000000000 

noncomputable def Ns300p600 := nat_lit 112893919319882902186927995383447552 

noncomputable def Ns300p601 := nat_lit 55495564935877257141944320 

noncomputable def Ns300p602 := nat_lit 141688717768478935544448764214405421386802112077384099840492301790689722475832940520843399542216336639144904429617097880392171520 

noncomputable def Ns300p603 := nat_lit 1753622087914482775468981302084764034446492718438254596016711910253742639254363795940272652777170429811743613256049872919855104 

noncomputable def Ns300p604 := nat_lit 813781271083375855864840974816183874522289701354826720077236075958375900405903115008020706204412811047878350805999288320 

noncomputable def Ns300p605 := BSN.log_dyadic_bound 493750545216 2590902545216 6 5 Ns300p602 134217728 35280000 Ns300p603 Ns300p604 51789113 3084653090432 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 493750545216) (BSN.artanhQ 2590902545216) 0 5 Ns300p603 Ns300p602 Ns300p604 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns300p606 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 620952 4000) qz669 620952 4000 0 1 3230267025988855 281474976710656 781250441 27562500000000000 50146019258045787249 28147497671065600 20213292659993 4593750000000000000 (Enclosure.Real.IsNear.const Bool.false 620952 4000) (BSN.isNear_log_sfrac 1542326545216 16000000 3230267025988855 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1542326545216) qz335)) Bool.false Ns300p601 Ns300p94 1000000564480000 35280000000000000000000 3230267025988855 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1542326545216 16000000 16 3084653090432 2097152000000 51789113 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns300p605 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns300p607 := BSN.arctan_dyadic_bound_f 1000 1241904 1 0 16777216 4410000 0 1 1 0 1 1 13509 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1241904) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1241904) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns300p608 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1241904))) 884279719003555 562949953421312 1 2000000000000000 13509 16777216 1 4410000 14828146959221178499072 883826432181667 562949953421312 200000000441 882000000000000000 qz16 (Ns300p607 rfl) rfl rfl 

noncomputable abbrev qz88 := qz403

noncomputable def Ns300p609 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 620952 4000) qz669) qz88 50146019258045787249 28147497671065600 20213292659993 4593750000000000000 883826432181667 2251799813685248 200000000441 3528000000000000000 Ns300p600 100269942855287032823 56294995342131200 1965476095414453 441000000000000000000 (Ns300p606 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1241904)))) 1 4 0 1 883826432181667 562949953421312 200000000441 882000000000000000 883826432181667 2251799813685248 200000000441 3528000000000000000 qz340 Ns300p608 rfl) 

noncomputable def Ns300p610 := @Ns300p596 Ns300p590 Ns300p591 2050939819201809311 225792000000000000000000 (@Ns300p598 2050939819201809311 225792000000000000000000 (Ns300p599 (Ns300p609 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 620952 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz670 (Real.log Real.pi) 620952 2000 0 1 38410761 33554432 1 67108864 2981404858059 8388608000 77619 16777216000 (Enclosure.Real.IsNear.const Bool.false 620952 2000) RS301to312.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns300p592 Ns300p593) 

noncomputable def Ns300p611 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz82) Bool.false Ns300p590 Ns300p591 2050939819201809311 225792000000000000000000 37422068987 33554432 153 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz82) (@HAdd.hAdd Real Real Real qz341 qz404 (Enclosure.sfrac Bool.true Ns300p592 Ns300p593)) Bool.false Ns300p590 Ns300p591 2050939819201809311 225792000000000000000000 Ns300p594 (Ns300p610 rfl rfl)) 

noncomputable def Ns300p612 := nat_lit 7591902632830333431578624 

noncomputable def Ns300p613 := nat_lit 3503427000935538427924713041979809475463979052997128181113512043422116732318679869915942531371424150815653789992316715343876195095633705921 

noncomputable def Ns300p614 := nat_lit 2486852048335067743757118579114905551494122133093794871456634719653186017633943283083043030966380178719450980126625618918995091241921 

noncomputable def Ns300p615 := nat_lit 17495413572553463320213337398730619808056957028998826180313231114952076478698999345195860147478942960374964807333447385604425202950860422081 

noncomputable def Ns300p616 := BSN.sin_dyadic_bound_f 107887425327 68719476736 4 3 33554432 8828614 Ns300p613 Ns300p383 Ns300p614 Ns300p615 Ns300p386 Ns300p614 33554420 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107887425327) qz351 0 3 Ns300p613 Ns300p383 Ns300p614 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107887425327) qz352 0 3 Ns300p615 Ns300p386 Ns300p614 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p617 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz82) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 37422068987) qz349) Bool.false 37422068987 33554432 153 16777216 Bool.true 33554420 33554432 1 4410000 (Ns300p611 rfl) (Enclosure.sfrac_false_div 37422068987 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 37422068987) qz349) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns300p612) qz353) 226375608064910080 72057594037927936 Bool.false 33554420 33554432 177 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q1 37422068987 33554432 226375608064910080 72057594037927936 177 Ns300p612 Ns300p94 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554420 33554432 Ns300p612 Ns300p94 107887425327 68719476736 8828614 8820000 (Ns300p616 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p618 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz82) Bool.false Ns300p590 Ns300p591 2050939819201809311 225792000000000000000000 299376551898 268435456 2439 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz82) (@HAdd.hAdd Real Real Real qz341 qz404 (Enclosure.sfrac Bool.true Ns300p592 Ns300p593)) Bool.false Ns300p590 Ns300p591 2050939819201809311 225792000000000000000000 Ns300p594 (Ns300p610 rfl rfl)) 

noncomputable def Ns300p619 := Ns300p589 54324 BSN.abs_quadSignPos (BSN.cos_quad_nat3 435 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268410168 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 275 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 240449378 268435456) qz85 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz82) qz82 1) Bool.true 8388605 8388608 43219201 4624220160000 268435360 268435456 2509 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz82) qz82 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz82)) Bool.true 8388605 8388608 43219201 4624220160000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz82) qz82) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz82)) Bool.true 33554420 33554432 691507216 73987522560000 8388605 8388608 43219201 4624220160000 (Ns300p617 rfl rfl) rfl)) rfl) (Ns300p618 rfl) RS301to312.d7 

noncomputable def Ns300p620 := nat_lit 42781281431034826722755911957193956669541076596626238986909995547254905399934229212506117759080381860006400000 

noncomputable def Ns300p621 := nat_lit 28429951699223411736112057549888269912482095944376057580978707744341540944194985807694887041000000000000 

noncomputable def Ns300p622 := nat_lit 213649758148800518551813110260792034828614936694074568433311393550875350748104610558032915984331363476032000000 

noncomputable def Ns300p623 := BSN.sin_dyadic_bound_f 417972790 268435456 4 3 268435456 134217728 Ns300p620 Ns300p237 Ns300p621 Ns300p622 Ns300p240 Ns300p621 268410168 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 417972790) qz344 0 3 Ns300p620 Ns300p237 Ns300p621 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 417972790) qz345 0 3 Ns300p622 Ns300p240 Ns300p621 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p624 := nat_lit 123870913777785067667559282360742429553525606085246601727653879699430625 

noncomputable def Ns300p625 := nat_lit 62175601073231908409700015749077708161905980074319418118765500390625 

noncomputable def Ns300p626 := nat_lit 324323156540080420801420510919303094446019215779335058800234540783590625 

noncomputable def Ns300p627 := BSN.sin_dyadic_bound_f 297990555 268435456 3 2 268435456 134217728 Ns300p624 Ns300p116 Ns300p625 Ns300p626 Ns300p119 Ns300p625 240449378 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 297990555) qz344 0 2 Ns300p624 Ns300p116 Ns300p625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 297990555) qz345 0 2 Ns300p626 Ns300p119 Ns300p625 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p628 := nat_lit 41374603718694641926564149549960408397668562302886034001384965766760590892341275356588724138753728845514311121 

noncomputable def Ns300p629 := nat_lit 25721678734092658333993186703998180584947262556355631134217053172117424329670756893419426045035402003921 

noncomputable def Ns300p630 := nat_lit 206632942602528457120111992651326257168083687162674260629440477097812176004957290287557690468020033090301756881 

noncomputable def Ns300p631 := BSN.sin_dyadic_bound_f 414500389 268435456 4 3 268435456 134217728 Ns300p628 Ns300p237 Ns300p629 Ns300p630 Ns300p240 Ns300p629 268340050 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 414500389) qz344 0 3 Ns300p628 Ns300p237 Ns300p629 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 414500389) qz345 0 3 Ns300p630 Ns300p240 Ns300p629 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p632 := nat_lit 15724905009432530979103008571707106612574099120060650091181239368099725225007053917997941388538286787209178001 

noncomputable def Ns300p633 := nat_lit 1417026571499610972764369543565153328936388859406330774305653663301192763615368156699174836132272909201 

noncomputable def Ns300p634 := nat_lit 78589775228966243208293920906898945537840496191688827190890923025559181606080027079933406161639377784072809361 

noncomputable def Ns300p635 := BSN.sin_dyadic_bound_f 325547851 268435456 4 3 268435456 134217728 Ns300p632 Ns300p237 Ns300p633 Ns300p634 Ns300p240 Ns300p633 251413120 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 325547851) qz344 0 3 Ns300p632 Ns300p237 Ns300p633 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 325547851) qz345 0 3 Ns300p634 Ns300p240 Ns300p633 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p636 := Ns300p587 92541 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 161 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268340050 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 73 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 251413120 268435456) qz85 rfl rfl (Ns300p619 RS301to312.d9 RS301to312.d11 RS301to312.d13 RS301to312.d17 (Ns300p623 rfl rfl) (Ns300p627 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns300p618 rfl) RS301to312.d19 RS301to312.d21 RS301to312.d23 RS301to312.d25 RS301to312.d17 (Ns300p631 rfl rfl) (Ns300p635 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns300p637 := nat_lit 118196595839548857286812813860074389043946319867404288466593159183400960 

noncomputable def Ns300p638 := nat_lit 56612353422277673860912852426049071709042410192723226187929432948736 

noncomputable def Ns300p639 := nat_lit 309470854817087129041115891681981225189473340512413489332011150207942656 

noncomputable def Ns300p640 := BSN.sin_dyadic_bound_f 294519396 268435456 3 2 268435456 134217728 Ns300p637 Ns300p116 Ns300p638 Ns300p639 Ns300p119 Ns300p638 238886142 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 294519396) qz344 0 2 Ns300p637 Ns300p116 Ns300p638 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 294519396) qz345 0 2 Ns300p639 Ns300p119 Ns300p638 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p641 := nat_lit 102914012336583030680692594140625 

noncomputable def Ns300p642 := BSN.sin_dyadic_bound_f 100720675 268435456 2 1 268435456 134217728 Ns300p641 Ns300p392 Ns300p641 Ns300p641 Ns300p393 Ns300p641 98373922 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 100720675) qz344 0 1 Ns300p641 Ns300p392 Ns300p641 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 100720675) qz345 0 1 Ns300p641 Ns300p393 Ns300p641 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p643 := Ns300p585 124747 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 1 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 238886142 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 59 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 98373922 268435456) qz85 rfl rfl (Ns300p636 rfl rfl) (Ns300p618 rfl) RS301to312.d27 RS301to312.d29 RS301to312.d31 RS301to312.d33 RS301to312.d17 (Ns300p640 rfl rfl) (Ns300p642 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p644 := nat_lit 12807420319088393461618524721 

noncomputable def Ns300p645 := BSN.cos_dyadic_bound_f 10638133 268435456 2 1 268435456 134217728 Ns300p644 Ns300p133 Ns300p644 Ns300p644 Ns300p134 Ns300p644 268224688 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 10638133) qz342 0 1 Ns300p644 Ns300p133 Ns300p644 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 10638133) qz343 0 1 Ns300p644 Ns300p134 Ns300p644 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p646 := nat_lit 32545270655562904542830705844616721815837202367595488685187078213140321 

noncomputable def Ns300p647 := nat_lit 13908071548686655846596149117848164227993893773708408240715905433441 

noncomputable def Ns300p648 := nat_lit 97607995823591340316798925235614469119055619315239049239079802828554081 

noncomputable def Ns300p649 := BSN.cos_dyadic_bound_f 247120267 268435456 3 2 268435456 134217728 Ns300p646 Ns300p110 Ns300p647 Ns300p648 Ns300p113 Ns300p647 162496565 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 247120267) qz342 0 2 Ns300p646 Ns300p110 Ns300p647 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 247120267) qz343 0 2 Ns300p648 Ns300p113 Ns300p647 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p650 := Ns300p583 152886 BSN.abs_quadSignPos (BSN.cos_quad_nat0 112 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268224688 268435456) BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 162496565 268435456) qz85 rfl rfl (Ns300p643 rfl) (Ns300p618 rfl) RS301to312.d35 RS301to312.d37 RS301to312.d39 RS301to312.d41 RS301to312.d17 (Ns300p645 rfl rfl) (Ns300p649 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p651 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz82) qz82 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz82) qz82 9) 206099365 268435456 152886 268435456 206099365 268435456 152886 268435456 110648754050170880 206099365 134217728 76443 67108864 (Ns300p650 rfl) 

noncomputable def Ns300p652 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz402) (Zeta.RiemannSiegel.correction qz84) 5321087 16777216 1 16777216 27852108969619 35184372088832 1248291258562601 51721026970583040000 148203494960823055853 590295810358705651712 

noncomputable def Ns300p653 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz402 1 1 0 1 5321087 16777216 1 16777216 5321087 16777216 1 16777216 

noncomputable def Ns300p654 := @Enclosure.Real.IsNear.sqrt_image qz83 414512859507 4194304000 77619 4194304000 166785736 166785768 16777216 (@Enclosure.Real.IsNear.of_eq qz83 (@HMul.hMul Real Real Real qz5 qz82 qz3) Bool.false 414512859507 4194304000 77619 4194304000 (BSN.t_div_two_pi_mk qz82 620952 1000 qz85) (@Enclosure.Real.IsNear.mulLit_ff qz82 qz3 620952 1000 0 1 5340353 33554432 1 33554432 414512859507 4194304000 77619 4194304000 (Enclosure.Real.IsNear.const Bool.false 620952 1000) RS301to312.d44 rfl)) 

noncomputable abbrev qz829 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 620952 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz671 := qz829

noncomputable abbrev qz406 := qz671

noncomputable abbrev qz89 := qz406

noncomputable def Ns300p655 := @Enclosure.Real.IsNear.sqrt_image qz89 20848219 2097152 1 1048576 52898018 52898024 16777216 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 333571504 33554432 32 33554432 20848219 2097152 1 1048576 (Ns300p654 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns300p656 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz89) 52898021 16777216 3 16777216 5321086 5321088 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz89) Bool.false 105796042 33554432 6 33554432 52898021 16777216 3 16777216 (Ns300p655 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns300p657 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 10642174 33554432 2 33554432 5321087 16777216 1 16777216 (Ns300p656 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz90 := (@HMul.hMul Real Real Real qz327 qz323 qz401)

noncomputable abbrev qz672 := (@HMul.hMul Real Real Real qz807 qz828 qz828)

noncomputable abbrev qz407 := (@HSub.hSub Real Real Real qz628 (@HSub.hSub Real Real Real qz628 qz672 qz668) qz639)

noncomputable abbrev qz91 := (Real.cos (@HMul.hMul Real Real Real qz327 qz323 qz407))

noncomputable def Ns300p658 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz84) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz90)) qz91) Bool.false 27852108969619 

noncomputable def Ns300p659 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz90)) qz91 8995459 8388608 121 

noncomputable def Ns300p660 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz90)) Bool.false 35981836 33554432 242 33554432 8995459 8388608 121 

noncomputable def Ns300p661 := @Enclosure.Real.IsNear.recentre' (Real.cos qz90) Bool.false 31290786 33554432 462187216 73987522560000 15645393 16777216 28886701 4624220160000 

noncomputable def Ns300p662 := @Enclosure.Real.IsNear.cos_image qz90 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 198433145) qz349) Bool.false 198433145 33554432 101 16777216 Bool.false 31290786 33554432 1 

noncomputable def Ns300p663 := nat_lit 26986075417521670947345863 

noncomputable def Ns300p664 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz84 884279719003555 140737488355328 1 500000000000000 1973851 2097152 1 1048576 1745436407634886040305 295147905179352825856 Ns300p663 

noncomputable def Ns300p665 := @Enclosure.Real.IsNear.subLit_ff_p qz89 qz1 20848219 2097152 1 1048576 9 1 0 1 1973851 1973851 2097152 1 

noncomputable def Ns300p666 := @Ns300p665 1048576 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 333571504 33554432 32 33554432 20848219 2097152 1 1048576 (Ns300p654 rfl rfl rfl rfl rfl rfl) rfl) qz350 

noncomputable def Ns300p667 := @Enclosure.Real.IsNear.recentre' qz90 Bool.false 1745436407634886040305 295147905179352825856 Ns300p663 Ns300p163 198433145 33554432 101 16777216 (@Ns300p664 Ns300p163 RS301to312.d43 (Ns300p666 rfl rfl) rfl) 

noncomputable def Ns300p668 := nat_lit 5809515170340548651253760 

noncomputable def Ns300p669 := nat_lit 3135021990191815912133512835372439855146360412888892311988017279764149056089262675576049185 

noncomputable def Ns300p670 := nat_lit 2158145477674912805290483179545033124174748235130037424197133781544302407447554950778401 

noncomputable def Ns300p671 := nat_lit 8207277738776615625331587119875221947944184822328316946996107039926461514431249061350297121 

noncomputable def Ns300p672 := BSN.sin_dyadic_bound_f 82558176051 68719476736 3 2 33554432 8828614 Ns300p669 Ns300p170 Ns300p670 Ns300p671 Ns300p173 Ns300p670 31290786 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 82558176051) qz351 0 2 Ns300p669 Ns300p170 Ns300p670 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 82558176051) qz352 0 2 Ns300p671 Ns300p173 Ns300p670 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p673 := @Ns300p662 4410000 (Ns300p667 rfl) (Enclosure.sfrac_false_div 198433145 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 198433145) qz349) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns300p668) qz353) 226375608064910080 72057594037927936 Bool.false 31290786 33554432 0 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q3 198433145 33554432 226375608064910080 72057594037927936 0 Ns300p668 Ns300p94 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 31290786 33554432 Ns300p668 Ns300p94 82558176051 68719476736 8828614 8820000 (Ns300p672 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p674 := @Enclosure.Real.IsNear.inv_image (Real.cos qz90) 15645393 16777216 28886701 4624220160000 17990797 17991039 16777216 (Ns300p661 (Ns300p673 rfl rfl) rfl) rfl 

noncomputable def Ns300p675 := @Enclosure.Real.IsNear.recentre' qz91 Bool.false 12384964 16777216 

noncomputable abbrev qz92 := (@HMul.hMul Real Real Real qz327 qz323 qz407)

noncomputable def Ns300p676 := @Enclosure.Real.IsNear.cos_image qz92 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 24843571)) qz349) Bool.true 24843571 33554432 

noncomputable def Ns300p677 := nat_lit 458283012810514743350832725 

noncomputable def Ns300p678 := nat_lit 618970019642690137449562112 

noncomputable def Ns300p679 := nat_lit 20390867481879780469434896992609 

noncomputable def Ns300p680 := @Enclosure.Real.IsNear.recentre' qz92 Bool.true Ns300p677 Ns300p678 Ns300p679 

noncomputable def Ns300p681 := nat_lit 1180591620717411303424000000000000000 

noncomputable abbrev qz93 := qz407

noncomputable def Ns300p682 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz93 884279719003555 140737488355328 1 500000000000000 518255709095 

noncomputable abbrev qz408 := (@HSub.hSub Real Real Real qz628 qz672 qz668)

noncomputable abbrev qz94 := qz408

noncomputable def Ns300p683 := @Enclosure.Real.IsNear.subLit_tf qz94 qz27 243377802151 4398046511104 755607 274877906944 1 16 

noncomputable abbrev qz409 := qz672

noncomputable abbrev qz95 := qz409

noncomputable def Ns300p684 := @Enclosure.Real.IsNear.subLit_ff_n qz95 qz84 3896087770201 4398046511104 493463 274877906944 1973851 2097152 1 1048576 

noncomputable def Ns300p685 := @Enclosure.Real.IsNear.mulLit_ff qz84 qz84 1973851 2097152 1 1048576 1973851 2097152 1 1048576 3896087770201 4398046511104 

noncomputable def Ns300p686 := nat_lit 811414211823035569143432196269432570745397154569323721455287841 

noncomputable def Ns300p687 := nat_lit 64791741944522487909851911563195676133695224709322207119351480320 

noncomputable def Ns300p688 := nat_lit 145114954419778345072571569492286506908168719739734568713761 

noncomputable def Ns300p689 := nat_lit 2433952405560267150740151445669313139222375126268491695228436001 

noncomputable def Ns300p690 := nat_lit 2915628387503511955943336020343805426016285111919499320370816614400 

noncomputable def Ns300p691 := BSN.cos_dyadic_bound_f 24843571 33554432 3 2 16777216 4410000 Ns300p686 Ns300p687 Ns300p688 Ns300p689 Ns300p690 Ns300p688 12384964 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 24843571) (BSN.cosEvenQ 33554432) 0 2 Ns300p686 Ns300p687 Ns300p688 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 24843571) (BSN.cosOddQ 33554432) 0 2 Ns300p689 Ns300p690 Ns300p688 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p692 := @Ns300p675 2595764432 147975045120000 3096241 4194304 162235277 9248440320000 (@Ns300p676 581 33554432 Bool.false 12384964 16777216 1 4410000 (@Ns300p680 Ns300p681 24843571 33554432 581 33554432 (@Ns300p682 4398046511104 755607 274877906944 Ns300p677 Ns300p678 Ns300p679 Ns300p681 RS301to312.d43 (@Ns300p683 0 1 8292091345520 518255709095 4398046511104 755607 274877906944 (@Ns300p684 510400244536573952 243377802151 4398046511104 755607 274877906944 (@Ns300p685 493463 274877906944 (Ns300p666 rfl rfl) (Ns300p666 rfl rfl) rfl) (Ns300p666 rfl rfl) rfl rfl) qz358 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 24843571 33554432) (BSN.cos_neg_of_bound 24843571 33554432 Bool.false 12384964 16777216 1 4410000 (Ns300p691 rfl rfl)) rfl rfl) 

noncomputable def Ns300p693 := @Ns300p652 139233546596410278331 Ns300p579 (Ns300p653 qz29 (@Enclosure.Real.IsNear.of_eq qz402 (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 5321087 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz83 (BSN.t_div_two_pi_nonneg qz82 620952 1000 qz85)) Ns300p657) rfl) (@Ns300p658 35184372088832 1248291258562601 51721026970583040000 (BSN.correction_mk qz84 (BSN.cos_two_pi_p_ne_zero_mk qz82 620952 1000 9 qz85 rfl rfl (@BSN.floor_sqrt_eq_dec qz82 620952 1000 9 qz85 rfl rfl rfl))) (@Ns300p659 16777216 3096241 4194304 162235277 9248440320000 27852108969619 35184372088832 1248291258562601 51721026970583040000 (@Ns300p660 16777216 (Ns300p674 rfl rfl rfl rfl rfl) rfl) (Ns300p692 rfl) rfl)) 

noncomputable def Ns300p694 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz82) (hardyZApproximantRS₀ qz82) Bool.true 758231098218176793107 590295810358705651712 20731475550306198438331 Ns300p579 (@Eq.refl Real (hardyZApproximantRS₀ qz82)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz82) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz82) qz82 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz402) (Zeta.RiemannSiegel.correction qz84))) Bool.true 758231098218176793107 590295810358705651712 20731475550306198438331 Ns300p579 (BSN.hardyZApproximantRS₀_eq qz82 9 (@BSN.floor_sqrt_eq_dec qz82 620952 1000 9 qz85 rfl rfl rfl)) (@Ns300p581 758231098218176793107 590295810358705651712 20731475550306198438331 Ns300p579 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz82) qz82 9) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz82) qz82 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz82) qz82 9)) Bool.true 206099365 134217728 76443 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz82) qz82 9) (Ns300p651 (Ns300p650 rfl) rfl rfl)) (Ns300p693 rfl) rfl rfl)) 

theorem RS301to312.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz82) Bool.true 758231098218176793107 590295810358705651712 20731475550306198438331 Ns300p579 := Ns300p694 

noncomputable def Ns300p695 := nat_lit 1041281809472756769619968000 

noncomputable def Ns300p696 := nat_lit 337341818453490989603278028800 

noncomputable abbrev qz830 := (Enclosure.sfrac Bool.false 622320 1000)

noncomputable abbrev qz673 := qz830

noncomputable abbrev qz410 := qz673

noncomputable abbrev qz96 := qz410

noncomputable abbrev qz831 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 622320 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz674 := qz831

noncomputable abbrev qz411 := qz674

noncomputable abbrev qz97 := qz411

noncomputable abbrev qz832 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 622320 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz675 := qz832

noncomputable abbrev qz412 := qz675

noncomputable abbrev qz98 := qz412

noncomputable abbrev qz413 := (@HPow.hPow Real Real Real qz627 qz97 qz8)

noncomputable def Ns300p697 := @Enclosure.Real.IsNear.subLit_tt_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz413) (Zeta.RiemannSiegel.correction qz98)) 16805961 134217728 38307 33554432 4878621147638177065433 18889465931478580854784 7896930299600638347799 Ns300p695 Ns300p696 

noncomputable def Ns300p698 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 622320 1000 111 158 268435456 134217728 4503599627370496 Bool.false 300220143221 2445 

noncomputable def Ns300p699 := Ns300p698 558195838 62 94906264 8 589812974 62 89478488 8 Bool.true 45189931 125026 Bool.true 352316145 Bool.true 210393092 14148475504056880 1 Bool.false 259529150 Bool.false Bool.false 190120312 Bool.true Bool.true 16805961 

noncomputable def Ns300p700 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 622320 1000 2 58 268435456 134217728 4503599627370496 Bool.false 300220143221 2445 

noncomputable def Ns300p701 := Ns300p700 480971758 62 109588312 8 522351262 62 101459064 8 Bool.false 72482112 92749 Bool.false 58483925 Bool.true 393363307 14148475504056880 1 Bool.false 262089682 Bool.true Bool.false 28241759 Bool.true Bool.true 45189931 

noncomputable def Ns300p702 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 622320 1000 162 74 268435456 134217728 4503599627370496 Bool.false 300220143221 2445 

noncomputable def Ns300p703 := Ns300p702 372130544 61 134217720 8 432030192 61 120047984 16 Bool.false 218893293 54447 Bool.false 327359699 Bool.false 156464443 14148475504056880 1 Bool.false 92370236 Bool.true Bool.false 224112297 Bool.true Bool.false 72482112 

noncomputable def Ns300p704 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 622320 1000 437 276 268435456 134217728 4503599627370496 Bool.false 300220143221 2445 

noncomputable def Ns300p705 := Ns300p704 186065264 61 189812528 16 294906480 61 154981288 8 Bool.false 268435448 2517 Bool.false 163711976 Bool.false 316492385 14148475504056880 1 Bool.false 153750353 Bool.true Bool.false 102495421 Bool.false Bool.false 218893293 

noncomputable def Ns300p706 := nat_lit 57144331260601938324274922320294906106981303849 

noncomputable def Ns300p707 := nat_lit 51094388454917528309307023584177180324659200 

noncomputable def Ns300p708 := nat_lit 44803376003830857885812736000000000 

noncomputable def Ns300p709 := nat_lit 167292272124271314090497330565120000000 

noncomputable abbrev qz99 := (@Eq.refl Real qz410)

noncomputable def Ns300p710 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz96 622320 1000 1549129729600 16000000 1244640 4000 2000 Ns300p708 Ns300p709 qz99 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns300p711 := nat_lit 10532843137954149271930353682076757093638793925447680000000 

noncomputable abbrev qz414 := (@HMul.hMul Real Real Real qz623 qz629 (@HSub.hSub Real Real Real qz628 qz630 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz631 (@Nat.cast Real Real.instNatCast 1244640)))))

noncomputable abbrev qz676 := (Real.log (Enclosure.sfrac Bool.false 1549129729600 16000000))

noncomputable abbrev qz677 := (Enclosure.sfrac Bool.false 622320 2000)

noncomputable abbrev qz100 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 622320 4000) qz676) qz414) qz677)

noncomputable abbrev qz415 := (@HSub.hSub Real Real Real qz11 qz100 (@HMul.hMul Real Real Real qz5 qz677 (Real.log Real.pi)))

noncomputable def Ns300p712 := @Enclosure.Real.IsNear.addLit_ft_p qz415 (Enclosure.sfrac Bool.true Ns300p708 Ns300p709) 62960742456386619689 56294995342131200 205542998152132751 22579200000000000000000 Ns300p708 Ns300p709 0 1 Ns300p711 

noncomputable def Ns300p713 := nat_lit 10563059757111688980322058240 

noncomputable abbrev qz416 := (@HMul.hMul Real Real Real qz5 qz677 (Real.log Real.pi))

noncomputable def Ns300p714 := @Enclosure.Real.IsNear.subLit_ff_p qz100 qz416 16602538096919151061 11258999068426240 393950219565521 88200000000000000000 298797309819 838860800 7779 1677721600 Ns300p713 62960742456386619689 56294995342131200 

noncomputable abbrev qz101 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 622320 4000) qz676) qz414)

noncomputable def Ns300p715 := @Enclosure.Real.IsNear.subLit_ff_p qz101 qz677 100529441235253299497 56294995342131200 393950219565521 88200000000000000000 622320 2000 0 1 166025380969191510610000 16602538096919151061 11258999068426240 393950219565521 88200000000000000000 

noncomputable def Ns300p716 := nat_lit 56593044260856366840638111758680064 

noncomputable def Ns300p717 := nat_lit 55516848263169066745724928 

noncomputable def Ns300p718 := nat_lit 145453446506818015975376429250956864355512448901099292800491885539030343153105531447636419603503379751370752000000000000000000000 

noncomputable def Ns300p719 := nat_lit 1841414659589581576090406043312049657652499716511328996031190242827391209300686275303821475803166199408230400000000000000000000 

noncomputable def Ns300p720 := nat_lit 933122850807842315497178035143826171680355809662966249841465924065939105739728480408085937029906432000000000000000000000 

noncomputable def Ns300p721 := BSN.log_dyadic_bound 500553729600 2597705729600 6 5 Ns300p718 134217728 35280000 Ns300p719 Ns300p720 52379844 3098259459200 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 500553729600) (BSN.artanhQ 2597705729600) 0 5 Ns300p719 Ns300p718 Ns300p720 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns300p722 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 622320 4000) qz676 622320 4000 0 1 3231505878686967 281474976710656 781250441 27562500000000000 25137884230305916293 14073748835532800 2025782393513 459375000000000000 (Enclosure.Real.IsNear.const Bool.false 622320 4000) (BSN.isNear_log_sfrac 1549129729600 16000000 3231505878686967 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1549129729600) qz335)) Bool.false Ns300p717 Ns300p94 1000000564480000 35280000000000000000000 3231505878686967 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1549129729600 16000000 16 3098259459200 2097152000000 52379844 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns300p721 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns300p723 := BSN.arctan_dyadic_bound_f 1000 1244640 1 0 16777216 4410000 0 1 1 0 1 1 13479 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1244640) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1244640) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns300p724 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1244640))) 884279719003555 562949953421312 1 2000000000000000 13479 16777216 1 4410000 14828163847719781138432 883827438814627 562949953421312 200000000441 882000000000000000 qz16 (Ns300p723 rfl) rfl rfl 

noncomputable abbrev qz102 := qz414

noncomputable def Ns300p725 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 622320 4000) qz676) qz102 25137884230305916293 14073748835532800 2025782393513 459375000000000000 883827438814627 2251799813685248 200000000441 3528000000000000000 Ns300p716 100529441235253299497 56294995342131200 393950219565521 88200000000000000000 (Ns300p722 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1244640)))) 1 4 0 1 883827438814627 562949953421312 200000000441 882000000000000000 883827438814627 2251799813685248 200000000441 3528000000000000000 qz340 Ns300p724 rfl) 

noncomputable def Ns300p726 := @Ns300p712 Ns300p706 Ns300p707 205542998152132751 22579200000000000000000 (@Ns300p714 205542998152132751 22579200000000000000000 (Ns300p715 (Ns300p725 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 622320 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz677 (Real.log Real.pi) 622320 2000 0 1 38410761 33554432 1 67108864 298797309819 838860800 7779 1677721600 (Enclosure.Real.IsNear.const Bool.false 622320 2000) RS301to312.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns300p708 Ns300p709) 

noncomputable def Ns300p727 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz96) Bool.false Ns300p706 Ns300p707 205542998152132751 22579200000000000000000 18763758951 16777216 307 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz96) (@HAdd.hAdd Real Real Real qz341 qz415 (Enclosure.sfrac Bool.true Ns300p708 Ns300p709)) Bool.false Ns300p706 Ns300p707 205542998152132751 22579200000000000000000 Ns300p710 (Ns300p726 rfl rfl)) 

noncomputable def Ns300p728 := nat_lit 3798441477952459549704192 

noncomputable def Ns300p729 := nat_lit 3512647619422660908655009033305418036542155285304356508167122218535130755275892045466117013250850184918181651395293990130953004034081099776 

noncomputable def Ns300p730 := nat_lit 2506499472531399514356765877517262438201946143521886080753421829633712789001555501177041984868753201846392045177056402172169103282176 

noncomputable def Ns300p731 := nat_lit 17541402381771357938713439400876948725582765301925693298222314898427109501375398297662449226907964301664601338729203264912362217539430977536 

noncomputable def Ns300p732 := BSN.sin_dyadic_bound_f 107958199974 68719476736 4 3 33554432 8828614 Ns300p729 Ns300p383 Ns300p730 Ns300p731 Ns300p386 Ns300p730 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107958199974) qz351 0 3 Ns300p729 Ns300p383 Ns300p730 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107958199974) qz352 0 3 Ns300p731 Ns300p386 Ns300p730 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p733 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz96) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18763758951) qz354) Bool.false 18763758951 16777216 307 33554432 Bool.false 33554431 33554432 1 4410000 (Ns300p727 rfl) (Enclosure.sfrac_false_div 18763758951 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18763758951) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns300p728) qz645) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 177 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q3 18763758951 16777216 226375608064910080 72057594037927936 177 Ns300p728 Ns300p231 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554431 33554432 Ns300p728 Ns300p231 107958199974 68719476736 8828614 8820000 (Ns300p732 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p734 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz96) Bool.false Ns300p706 Ns300p707 205542998152132751 22579200000000000000000 300220143221 268435456 2445 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz96) (@HAdd.hAdd Real Real Real qz341 qz415 (Enclosure.sfrac Bool.true Ns300p708 Ns300p709)) Bool.false Ns300p706 Ns300p707 205542998152132751 22579200000000000000000 Ns300p710 (Ns300p726 rfl rfl)) 

noncomputable def Ns300p735 := Ns300p705 54447 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 437 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 153750353 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 276 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 102495421 268435456) qz99 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 1) Bool.false 33554431 33554432 86714027 9248440320000 268435448 268435456 2517 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz96)) Bool.false 33554431 33554432 86714027 9248440320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz96) qz96) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz96)) Bool.false 33554431 33554432 1387424432 147975045120000 33554431 33554432 86714027 9248440320000 (Ns300p733 rfl rfl) rfl)) rfl) (Ns300p734 rfl) RS301to312.d7 

noncomputable def Ns300p736 := nat_lit 11279321378594632603563814157201245648099118687866572187005297444782080 

noncomputable def Ns300p737 := nat_lit 515992754867519505382457375960955887845202131399538766565580210176 

noncomputable def Ns300p738 := nat_lit 29540244384239966549182227385489801816441180521913994569868006177898496 

noncomputable def Ns300p739 := BSN.sin_dyadic_bound_f 163711976 268435456 3 2 268435456 134217728 Ns300p736 Ns300p116 Ns300p737 Ns300p738 Ns300p119 Ns300p737 153750353 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 163711976) qz344 0 2 Ns300p736 Ns300p116 Ns300p737 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 163711976) qz345 0 2 Ns300p738 Ns300p119 Ns300p737 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p740 := nat_lit 5405017987586956907855740596390749771061534595445687658069094891654328337688041966140764549102463094406890625 

noncomputable def Ns300p741 := nat_lit 1010087928855800802541970448847011447952770512759923814204866008678967698254621143230764161699462890625 

noncomputable def Ns300p742 := nat_lit 32765321891058389466179943278322451921376961686132114056631874323164337444033869973258945179069401114656490625 

noncomputable def Ns300p743 := BSN.cos_dyadic_bound_f 316492385 268435456 4 3 268435456 134217728 Ns300p740 Ns300p122 Ns300p741 Ns300p742 Ns300p125 Ns300p741 102495421 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 316492385) qz342 0 3 Ns300p740 Ns300p122 Ns300p741 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 316492385) qz343 0 3 Ns300p742 Ns300p125 Ns300p741 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p744 := nat_lit 6187526837287551518292933500107418294338121451053563350211563762724153827384088681145284904497719358370610481 

noncomputable def Ns300p745 := nat_lit 1514616042593014987319056387795415209838323068800486083125316688369227081669527649277200643217661623601 

noncomputable def Ns300p746 := nat_lit 37504752060529153481972476363917824367687034895943149169660168716171239706609725730415627384970028232936258865 

noncomputable def Ns300p747 := BSN.cos_dyadic_bound_f 327359699 268435456 4 3 268435456 134217728 Ns300p744 Ns300p122 Ns300p745 Ns300p746 Ns300p125 Ns300p745 92370236 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 327359699) qz342 0 3 Ns300p744 Ns300p122 Ns300p745 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 327359699) qz343 0 3 Ns300p746 Ns300p125 Ns300p745 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p748 := nat_lit 5228309243665591134978026463675185536498827984892904267758971692045281 

noncomputable def Ns300p749 := nat_lit 359190851926958096799826140647526645011188820492457782401050924001 

noncomputable def Ns300p750 := nat_lit 15684209349292919488740479738744261556206461577037727887712112974287841 

noncomputable def Ns300p751 := BSN.cos_dyadic_bound_f 156464443 268435456 3 2 268435456 134217728 Ns300p748 Ns300p110 Ns300p749 Ns300p750 Ns300p113 Ns300p749 224112297 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 156464443) qz342 0 2 Ns300p748 Ns300p110 Ns300p749 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 156464443) qz343 0 2 Ns300p750 Ns300p113 Ns300p749 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p752 := Ns300p703 92749 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 162 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 92370236 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 74 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 224112297 268435456) qz99 rfl rfl (Ns300p735 RS301to312.d9 RS301to312.d11 RS301to312.d13 RS301to312.d17 (Ns300p739 rfl rfl) (Ns300p743 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns300p734 rfl) RS301to312.d19 RS301to312.d21 RS301to312.d23 RS301to312.d25 RS301to312.d17 (Ns300p747 rfl rfl) (Ns300p751 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns300p753 := nat_lit 11698927403012462032248281640625 

noncomputable def Ns300p754 := BSN.cos_dyadic_bound_f 58483925 268435456 2 1 268435456 134217728 Ns300p753 Ns300p133 Ns300p753 Ns300p753 Ns300p134 Ns300p753 262089682 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 58483925) qz342 0 1 Ns300p753 Ns300p133 Ns300p753 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 58483925) qz343 0 1 Ns300p753 Ns300p134 Ns300p753 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p755 := nat_lit 12918467750858526587403399766960662906035446277050191511165595759765417927833117532115085225002594474165284881 

noncomputable def Ns300p756 := nat_lit 13725436246298788992500060888071323097187224518507385195774322451949700647460689794777542213655228330001 

noncomputable def Ns300p757 := nat_lit 78228951825808236924441851246579662824196600958333587557934901411424176996650290343418075117237922139488923665 

noncomputable def Ns300p758 := BSN.cos_dyadic_bound_f 393363307 268435456 4 3 268435456 134217728 Ns300p755 Ns300p122 Ns300p756 Ns300p757 Ns300p125 Ns300p756 28241759 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 393363307) qz342 0 3 Ns300p755 Ns300p122 Ns300p756 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 393363307) qz343 0 3 Ns300p757 Ns300p125 Ns300p756 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p759 := Ns300p701 125026 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 2 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 262089682 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 58 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 28241759 268435456) qz99 rfl rfl (Ns300p752 rfl rfl) (Ns300p734 rfl) RS301to312.d27 RS301to312.d29 RS301to312.d31 RS301to312.d33 RS301to312.d17 (Ns300p754 rfl rfl) (Ns300p758 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p760 := nat_lit 21576167527428098438209101909767874764401364345960285890340502289780242910519867554142514869330382626968290625 

noncomputable def Ns300p761 := nat_lit 3657552291175871815407630375478435314101532834780813195966465191925750893917873101926179985996337890625 

noncomputable def Ns300p762 := nat_lit 107815446247126158527635048077590857955112077201727845447332333191229555106159034172555202483563717245489890625 

noncomputable def Ns300p763 := BSN.sin_dyadic_bound_f 352316145 268435456 4 3 268435456 134217728 Ns300p760 Ns300p237 Ns300p761 Ns300p762 Ns300p240 Ns300p761 259529150 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 352316145) qz344 0 3 Ns300p760 Ns300p237 Ns300p761 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 352316145) qz345 0 3 Ns300p762 Ns300p240 Ns300p761 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p764 := nat_lit 17095910795528327965173759889035409944579324570420345439322352082026496 

noncomputable def Ns300p765 := nat_lit 3839297883743083855609900998143119404928348749285250314834888687616 

noncomputable def Ns300p766 := nat_lit 51280053790817497727810059865109943594928117013762465817337386468704256 

noncomputable def Ns300p767 := BSN.cos_dyadic_bound_f 210393092 268435456 3 2 268435456 134217728 Ns300p764 Ns300p110 Ns300p765 Ns300p766 Ns300p113 Ns300p765 190120312 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 210393092) qz342 0 2 Ns300p764 Ns300p110 Ns300p765 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 210393092) qz343 0 2 Ns300p766 Ns300p113 Ns300p765 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p768 := Ns300p699 153228 BSN.abs_quadSignPos (BSN.cos_quad_nat3 111 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 259529150 268435456) BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 190120312 268435456) qz99 rfl rfl (Ns300p759 rfl) (Ns300p734 rfl) RS301to312.d35 RS301to312.d37 RS301to312.d39 RS301to312.d41 RS301to312.d17 (Ns300p763 rfl rfl) (Ns300p767 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p769 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 9) 16805961 268435456 153228 268435456 16805961 268435456 153228 268435456 9022631609106432 16805961 134217728 38307 33554432 (Ns300p768 rfl) 

noncomputable def Ns300p770 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz413) (Zeta.RiemannSiegel.correction qz98) 10636321 33554432 1 33554432 458675621734073 562949953421312 740072160842117 31032616182349824000 4878621147638177065433 18889465931478580854784 

noncomputable def Ns300p771 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz413 1 1 0 1 10636321 33554432 1 33554432 10636321 33554432 1 33554432 

noncomputable def Ns300p772 := @Enclosure.Real.IsNear.sqrt_image qz97 41542605987 419430400 7779 419430400 166969355 166969387 16777216 (@Enclosure.Real.IsNear.of_eq qz97 (@HMul.hMul Real Real Real qz5 qz96 qz3) Bool.false 41542605987 419430400 7779 419430400 (BSN.t_div_two_pi_mk qz96 622320 1000 qz99) (@Enclosure.Real.IsNear.mulLit_ff qz96 qz3 622320 1000 0 1 5340353 33554432 1 33554432 41542605987 419430400 7779 419430400 (Enclosure.Real.IsNear.const Bool.false 622320 1000) RS301to312.d44 rfl)) 

noncomputable abbrev qz833 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 622320 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz678 := qz833

noncomputable abbrev qz417 := qz678

noncomputable abbrev qz103 := qz417

noncomputable def Ns300p773 := @Enclosure.Real.IsNear.sqrt_image qz103 166969371 16777216 1 1048576 52927128 52927134 16777216 (@Enclosure.Real.IsNear.recentre' qz103 Bool.false 333938742 33554432 32 33554432 166969371 16777216 1 1048576 (Ns300p772 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns300p774 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz103) 52927131 16777216 3 16777216 5318160 5318161 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz103) Bool.false 105854262 33554432 6 33554432 52927131 16777216 3 16777216 (Ns300p773 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns300p775 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz103)) Bool.false 10636321 33554432 1 33554432 10636321 33554432 1 33554432 (Ns300p774 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz104 := (@HMul.hMul Real Real Real qz327 qz323 qz412)

noncomputable abbrev qz679 := (@HMul.hMul Real Real Real qz807 qz832 qz832)

noncomputable abbrev qz418 := (@HSub.hSub Real Real Real qz628 (@HSub.hSub Real Real Real qz628 qz679 qz675) qz639)

noncomputable abbrev qz105 := (Real.cos (@HMul.hMul Real Real Real qz327 qz323 qz418))

noncomputable def Ns300p776 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz98) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz104)) qz105) Bool.false 458675621734073 

noncomputable def Ns300p777 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz104)) qz105 35130229 33554432 231 

noncomputable def Ns300p778 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz104)) Bool.false 35130229 33554432 231 33554432 35130229 33554432 231 

noncomputable def Ns300p779 := @Enclosure.Real.IsNear.recentre' (Real.cos qz104) Bool.false 32049319 33554432 462187216 73987522560000 32049319 33554432 28886701 4624220160000 

noncomputable def Ns300p780 := @Enclosure.Real.IsNear.cos_image qz104 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 100370285) qz354) Bool.false 100370285 16777216 101 16777216 Bool.false 32049319 33554432 1 

noncomputable def Ns300p781 := nat_lit 26986075417620250647336391 

noncomputable def Ns300p782 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz98 884279719003555 140737488355328 1 500000000000000 15974427 16777216 1 1048576 14125861818802802087985 2361183241434822606848 Ns300p781 

noncomputable def Ns300p783 := @Enclosure.Real.IsNear.subLit_ff_p qz103 qz1 166969371 16777216 1 1048576 9 1 0 1 15974427 15974427 16777216 1 

noncomputable def Ns300p784 := @Ns300p783 1048576 (@Enclosure.Real.IsNear.recentre' qz103 Bool.false 333938742 33554432 32 33554432 166969371 16777216 1 1048576 (Ns300p772 rfl rfl rfl rfl rfl rfl) rfl) qz350 

noncomputable def Ns300p785 := @Enclosure.Real.IsNear.recentre' qz104 Bool.false 14125861818802802087985 2361183241434822606848 Ns300p781 Ns300p163 100370285 16777216 101 16777216 (@Ns300p782 Ns300p163 RS301to312.d43 (Ns300p784 rfl rfl) rfl) 

noncomputable def Ns300p786 := nat_lit 3071025079093240193351680 

noncomputable def Ns300p787 := nat_lit 3917500093854906421297065855043212070084603156689837100296615100901860255235569055831690785 

noncomputable def Ns300p788 := nat_lit 3368747540423284388040191175639632356601301370244023448506905888679973673696607334829601 

noncomputable def Ns300p789 := nat_lit 10254665130745021976292631215590710302596606160540606843764980749970818806335743496255180321 

noncomputable def Ns300p790 := BSN.sin_dyadic_bound_f 87283782451 68719476736 3 2 33554432 8828614 Ns300p787 Ns300p170 Ns300p788 Ns300p789 Ns300p173 Ns300p788 32049319 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 87283782451) qz351 0 2 Ns300p787 Ns300p170 Ns300p788 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 87283782451) qz352 0 2 Ns300p789 Ns300p173 Ns300p788 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p791 := @Ns300p780 4410000 (Ns300p785 rfl) (Enclosure.sfrac_false_div 100370285 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 100370285) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns300p786) qz645) 226375608064910080 72057594037927936 Bool.false 32049319 33554432 0 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q3 100370285 16777216 226375608064910080 72057594037927936 0 Ns300p786 Ns300p231 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 32049319 33554432 Ns300p786 Ns300p231 87283782451 68719476736 8828614 8820000 (Ns300p790 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p792 := @Enclosure.Real.IsNear.inv_image (Real.cos qz104) 32049319 33554432 28886701 4624220160000 17564999 17565230 16777216 (Ns300p779 (Ns300p791 rfl rfl) rfl) rfl 

noncomputable def Ns300p793 := @Enclosure.Real.IsNear.recentre' qz105 Bool.false 13056437 16777216 

noncomputable abbrev qz106 := (@HMul.hMul Real Real Real qz327 qz323 qz418)

noncomputable def Ns300p794 := @Enclosure.Real.IsNear.cos_image qz106 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 22782221)) qz349) Bool.true 22782221 33554432 

noncomputable def Ns300p795 := nat_lit 26896499815669324905903289045 

noncomputable def Ns300p796 := nat_lit 131492583119989495279222641514609 

noncomputable def Ns300p797 := @Enclosure.Real.IsNear.recentre' qz106 Bool.true Ns300p795 Ns300p180 Ns300p796 

noncomputable abbrev qz107 := qz418

noncomputable def Ns300p798 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz107 884279719003555 140737488355328 1 500000000000000 30416280321319 

noncomputable abbrev qz419 := (@HSub.hSub Real Real Real qz628 qz679 qz675)

noncomputable abbrev qz108 := qz419

noncomputable def Ns300p799 := @Enclosure.Real.IsNear.subLit_tf qz108 qz27 12824094276903 281474976710656 24363043 8796093022208 1 16 

noncomputable abbrev qz420 := qz679

noncomputable abbrev qz109 := qz420

noncomputable def Ns300p800 := @Enclosure.Real.IsNear.subLit_ff_n qz109 qz98 255182317978329 281474976710656 15974435 8796093022208 15974427 16777216 1 1048576 

noncomputable def Ns300p801 := @Enclosure.Real.IsNear.mulLit_ff qz98 qz98 15974427 16777216 1 1048576 15974427 16777216 1 1048576 255182317978329 281474976710656 

noncomputable def Ns300p802 := nat_lit 573783456974898343480284807824803725989002662069995488852523041 

noncomputable def Ns300p803 := nat_lit 72571898335254110059415587499991469225253682791241314940961 

noncomputable def Ns300p804 := nat_lit 1721205227128024522220735592299411195028557478844403983927687201 

noncomputable def Ns300p805 := BSN.cos_dyadic_bound_f 22782221 33554432 3 2 16777216 4410000 Ns300p802 Ns300p687 Ns300p803 Ns300p804 Ns300p690 Ns300p803 13056437 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 22782221) (BSN.cosEvenQ 33554432) 0 2 Ns300p802 Ns300p687 Ns300p803 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 22782221) (BSN.cosOddQ 33554432) 0 2 Ns300p804 Ns300p690 Ns300p803 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p806 := @Ns300p793 2613404432 147975045120000 13056437 16777216 163337777 9248440320000 (@Ns300p794 585 33554432 Bool.false 13056437 16777216 1 4410000 (@Ns300p797 Ns300p183 22782221 33554432 585 33554432 (@Ns300p798 281474976710656 24363043 8796093022208 Ns300p795 Ns300p180 Ns300p796 Ns300p183 RS301to312.d43 (@Ns300p799 0 1 486660485141104 30416280321319 281474976710656 24363043 8796093022208 (@Ns300p800 215152599687965442048 12824094276903 281474976710656 24363043 8796093022208 (@Ns300p801 15974435 8796093022208 (Ns300p784 rfl rfl) (Ns300p784 rfl rfl) rfl) (Ns300p784 rfl rfl) rfl rfl) qz358 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 22782221 33554432) (BSN.cos_neg_of_bound 22782221 33554432 Bool.false 13056437 16777216 1 4410000 (Ns300p805 rfl rfl)) rfl rfl) 

noncomputable def Ns300p807 := @Ns300p770 7896930299600638347799 Ns300p695 (Ns300p771 qz29 (@Enclosure.Real.IsNear.of_eq qz413 (@Inv.inv Real Real.instInv (Real.sqrt qz103)) Bool.false 10636321 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz97 (BSN.t_div_two_pi_nonneg qz96 622320 1000 qz99)) Ns300p775) rfl) (@Ns300p776 562949953421312 740072160842117 31032616182349824000 (BSN.correction_mk qz98 (BSN.cos_two_pi_p_ne_zero_mk qz96 622320 1000 9 qz99 rfl rfl (@BSN.floor_sqrt_eq_dec qz96 622320 1000 9 qz99 rfl rfl rfl))) (@Ns300p777 33554432 13056437 16777216 163337777 9248440320000 458675621734073 562949953421312 740072160842117 31032616182349824000 (@Ns300p778 33554432 (Ns300p792 rfl rfl rfl rfl rfl) rfl) (Ns300p806 rfl) rfl)) 

noncomputable def Ns300p808 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz96) (hardyZApproximantRS₀ qz96) Bool.false 2513392407100580555225 18889465931478580854784 1196663358396875346315799 Ns300p695 (@Eq.refl Real (hardyZApproximantRS₀ qz96)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz96) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz413) (Zeta.RiemannSiegel.correction qz98))) Bool.false 2513392407100580555225 18889465931478580854784 1196663358396875346315799 Ns300p695 (BSN.hardyZApproximantRS₀_eq qz96 9 (@BSN.floor_sqrt_eq_dec qz96 622320 1000 9 qz99 rfl rfl rfl)) (@Ns300p697 2513392407100580555225 18889465931478580854784 1196663358396875346315799 Ns300p695 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 9) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 9)) Bool.true 16805961 134217728 38307 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz96) qz96 9) (Ns300p769 (Ns300p768 rfl) rfl rfl)) (Ns300p807 rfl) rfl rfl)) 

theorem RS301to312.d52 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz96) Bool.false 2513392407100580555225 18889465931478580854784 1196663358396875346315799 Ns300p695 := Ns300p808 

noncomputable def Ns300p809 := nat_lit 20825636189455135392399360 

noncomputable def Ns300p810 := nat_lit 67554529668758922078151770112 

noncomputable abbrev qz834 := (Enclosure.sfrac Bool.false 623687 1000)

noncomputable abbrev qz680 := qz834

noncomputable abbrev qz421 := qz680

noncomputable abbrev qz110 := qz421

noncomputable abbrev qz835 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 623687 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz681 := qz835

noncomputable abbrev qz422 := qz681

noncomputable abbrev qz111 := qz422

noncomputable abbrev qz836 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 623687 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz682 := qz836

noncomputable abbrev qz423 := qz682

noncomputable abbrev qz112 := qz423

noncomputable abbrev qz424 := (@HPow.hPow Real Real Real qz627 qz111 qz8)

noncomputable def Ns300p811 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz110) qz110 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz424) (Zeta.RiemannSiegel.correction qz112)) 246712747 67108864 153557 134217728 78413200219493229255 295147905179352825856 157208246418893708737 Ns300p809 Ns300p810 

noncomputable def Ns300p812 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz110) qz110 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 623687 1000 111 158 268435456 134217728 4503599627370496 Bool.false 301063521228 2450 

noncomputable def Ns300p813 := Ns300p812 558195838 62 94906264 8 589812974 62 89478488 8 Bool.true 502486236 125294 Bool.true 271991849 Bool.true 173289421 14148475504056880 1 Bool.false 227782294 Bool.false Bool.false 214417368 Bool.true Bool.true 493425494 

noncomputable def Ns300p814 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz110) qz110 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 623687 1000 2 58 268435456 134217728 4503599627370496 Bool.false 301063521228 2450 

noncomputable def Ns300p815 := Ns300p814 480971758 62 109588312 8 522351262 62 101459064 8 Bool.true 379048955 92946 Bool.false 244373539 Bool.true 264039475 14148475504056880 1 Bool.false 164674310 Bool.true Bool.false 148715772 Bool.true Bool.true 502486236 

noncomputable def Ns300p816 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz110) qz110 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 623687 1000 163 74 268435456 134217728 4503599627370496 Bool.false 301063521228 2450 

noncomputable def Ns300p817 := Ns300p816 372130544 61 134217720 8 432030192 61 120047984 16 Bool.true 478263300 54560 Bool.false 240377824 Bool.false 409257178 14148475504056880 1 Bool.false 209515879 Bool.false Bool.false 12395840 Bool.true Bool.true 379048955 

noncomputable def Ns300p818 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz110) qz110 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 623687 1000 438 277 268435456 134217728 4503599627370496 Bool.false 301063521228 2450 

noncomputable def Ns300p819 := Ns300p818 186065264 61 189812528 16 294906480 61 154981288 8 Bool.true 268435424 2517 Bool.false 331081338 Bool.false 335075806 14148475504056880 1 Bool.false 88867109 Bool.true Bool.false 254592998 Bool.true Bool.true 478263300 

noncomputable def Ns300p820 := nat_lit 668900528427888990782099574173976733721894585090917048589 

noncomputable def Ns300p821 := nat_lit 596407753535194348277159840360626881941589662367744000 

noncomputable def Ns300p822 := nat_lit 45297622014958921515929459459360000 

noncomputable def Ns300p823 := nat_lit 169509278730173022119390634645875161920 

noncomputable abbrev qz113 := (@Eq.refl Real qz421)

noncomputable def Ns300p824 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz110 623687 1000 1555942895876 16000000 1247374 4000 2000 Ns300p822 Ns300p823 qz113 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns300p825 := nat_lit 214048169096924477050271863735672554791006267229093455548480 

noncomputable abbrev qz425 := (@HMul.hMul Real Real Real qz623 qz629 (@HSub.hSub Real Real Real qz628 qz630 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz631 (@Nat.cast Real Real.instNatCast 1247374)))))

noncomputable abbrev qz683 := (Real.log (Enclosure.sfrac Bool.false 1555942895876 16000000))

noncomputable abbrev qz684 := (Enclosure.sfrac Bool.false 623687 2000)

noncomputable abbrev qz114 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 623687 4000) qz683) qz425) qz684)

noncomputable abbrev qz426 := (@HSub.hSub Real Real Real qz11 qz114 (@HMul.hMul Real Real Real qz5 qz684 (Real.log Real.pi)))

noncomputable def Ns300p826 := @Enclosure.Real.IsNear.addLit_ft_p qz426 (Enclosure.sfrac Bool.true Ns300p822 Ns300p823) 1262752232214010552869 1125899906842624000 2354190698923941029 258048000000000000000000 Ns300p822 Ns300p823 0 1 Ns300p825 

noncomputable def Ns300p827 := nat_lit 84741867817346453087050530816000 

noncomputable abbrev qz427 := (@HMul.hMul Real Real Real qz5 qz684 (Real.log Real.pi))

noncomputable def Ns300p828 := @Enclosure.Real.IsNear.subLit_ff_p qz114 qz427 1664672122619900486181 1125899906842624000 282003282176999 63000000000000000000 23956292295807 67108864000 623687 134217728000 Ns300p827 1262752232214010552869 1125899906842624000 

noncomputable abbrev qz115 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 623687 4000) qz683) qz425)

noncomputable def Ns300p829 := @Enclosure.Real.IsNear.subLit_ff_p qz115 qz684 80631067608775132141 45035996273704960 282003282176999 63000000000000000000 623687 2000 0 1 133173769809592038894480 1664672122619900486181 1125899906842624000 282003282176999 63000000000000000000 

noncomputable def Ns300p830 := nat_lit 181565023018682477530932031382355968 

noncomputable def Ns300p831 := nat_lit 55538069368728424598732800 

noncomputable def Ns300p832 := nat_lit 149313687022228517956165498277733923887568875155021367120057817075624954084701396794376600539631521585192030916095183029686763520 

noncomputable def Ns300p833 := nat_lit 1932925115736065873503491265148987535423705842869319055454822595768116856788805913840372498923574678272229221658817800258453504 

noncomputable def Ns300p834 := nat_lit 1068201252518533380466426026675909541015306120290622195290316657092933297340583663333753042956335922162469488879935160320 

noncomputable def Ns300p835 := BSN.log_dyadic_bound 507366895876 2604518895876 6 5 Ns300p832 134217728 35280000 Ns300p833 Ns300p834 52968848 3111885791752 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 507366895876) (BSN.artanhQ 2604518895876) 0 5 Ns300p833 Ns300p832 Ns300p834 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns300p836 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 623687 4000) qz683 623687 4000 0 1 3232741109603575 281474976710656 781250441 27562500000000000 80648744177012995241 45035996273704960 487255743795967 110250000000000000000 (Enclosure.Real.IsNear.const Bool.false 623687 4000) (BSN.isNear_log_sfrac 1555942895876 16000000 3232741109603575 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1555942895876) qz335)) Bool.false Ns300p831 Ns300p94 1000000564480000 35280000000000000000000 3232741109603575 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1555942895876 16000000 16 3111885791752 2097152000000 52968848 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns300p835 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns300p837 := BSN.arctan_dyadic_bound_f 1000 1247374 1 0 16777216 4410000 0 1 1 0 1 1 13450 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1247374) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1247374) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns300p838 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1247374))) 884279719003555 562949953421312 1 2000000000000000 13450 16777216 1 4410000 14828180173268430356480 883828411893155 562949953421312 200000000441 882000000000000000 qz16 (Ns300p837 rfl) rfl rfl 

noncomputable abbrev qz116 := qz425

noncomputable def Ns300p839 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 623687 4000) qz683) qz116 80648744177012995241 45035996273704960 487255743795967 110250000000000000000 883828411893155 2251799813685248 200000000441 3528000000000000000 Ns300p830 80631067608775132141 45035996273704960 282003282176999 63000000000000000000 (Ns300p836 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1247374)))) 1 4 0 1 883828411893155 562949953421312 200000000441 882000000000000000 883828411893155 2251799813685248 200000000441 3528000000000000000 qz340 Ns300p838 rfl) 

noncomputable def Ns300p840 := @Ns300p826 Ns300p820 Ns300p821 2354190698923941029 258048000000000000000000 (@Ns300p828 2354190698923941029 258048000000000000000000 (Ns300p829 (Ns300p839 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 623687 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz684 (Real.log Real.pi) 623687 2000 0 1 38410761 33554432 1 67108864 23956292295807 67108864000 623687 134217728000 (Enclosure.Real.IsNear.const Bool.false 623687 2000) RS301to312.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns300p822 Ns300p823) 

noncomputable def Ns300p841 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz110) Bool.false Ns300p820 Ns300p821 2354190698923941029 258048000000000000000000 37632940153 33554432 307 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz110) (@HAdd.hAdd Real Real Real qz341 qz426 (Enclosure.sfrac Bool.true Ns300p822 Ns300p823)) Bool.false Ns300p820 Ns300p821 2354190698923941029 258048000000000000000000 Ns300p824 (Ns300p840 rfl rfl)) 

noncomputable def Ns300p842 := nat_lit 7598020591604650146267136 

noncomputable def Ns300p843 := nat_lit 3514756408841902892114569739945503428295780432488918725596550511314469451186011311586952870937720809416210367100671862860257265000000000000 

noncomputable def Ns300p844 := nat_lit 2511007373612752449531862945464942827192647261722549807891881979477481798637983715543059967586804771122992038726806640625000000000000 

noncomputable def Ns300p845 := nat_lit 17551920149894072413838384626936573240389866843016619620228471435607049673311449306719122164884950232882629287691364407074723825000000000000 

noncomputable def Ns300p846 := BSN.sin_dyadic_bound_f 107974366750 68719476736 4 3 33554432 8828614 Ns300p843 Ns300p383 Ns300p844 Ns300p845 Ns300p386 Ns300p844 33554428 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107974366750) qz351 0 3 Ns300p843 Ns300p383 Ns300p844 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107974366750) qz352 0 3 Ns300p845 Ns300p386 Ns300p844 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p847 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz110) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 37632940153) qz349) Bool.false 37632940153 33554432 307 33554432 Bool.true 33554428 33554432 1 4410000 (Ns300p841 rfl) (Enclosure.sfrac_false_div 37632940153 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 37632940153) qz349) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns300p842) qz353) 226375608064910080 72057594037927936 Bool.false 33554428 33554432 178 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q1 37632940153 33554432 226375608064910080 72057594037927936 178 Ns300p842 Ns300p94 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554428 33554432 Ns300p842 Ns300p94 107974366750 68719476736 8828614 8820000 (Ns300p846 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p848 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz110) Bool.false Ns300p820 Ns300p821 2354190698923941029 258048000000000000000000 301063521228 268435456 2450 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz110) (@HAdd.hAdd Real Real Real qz341 qz426 (Enclosure.sfrac Bool.true Ns300p822 Ns300p823)) Bool.false Ns300p820 Ns300p821 2354190698923941029 258048000000000000000000 Ns300p824 (Ns300p840 rfl rfl)) 

noncomputable def Ns300p849 := Ns300p819 54560 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 438 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 88867109 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 277 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 254592998 268435456) qz113 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz110) qz110 1) Bool.true 8388607 8388608 86714027 9248440320000 268435424 268435456 2517 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz110) qz110 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz110)) Bool.true 8388607 8388608 86714027 9248440320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz110) qz110) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz110)) Bool.true 33554428 33554432 1387424432 147975045120000 8388607 8388608 86714027 9248440320000 (Ns300p847 rfl rfl) rfl)) rfl) (Ns300p848 rfl) RS301to312.d7 

noncomputable def Ns300p850 := nat_lit 6474130858349369191034001195579534486450121212954924153671828940172009655973161949504523972910958976435163136 

noncomputable def Ns300p851 := nat_lit 1734668210757730230728155561822904651303804182117258399514622925785157933720626797275870259377886662656 

noncomputable def Ns300p852 := nat_lit 39240367678089493087809949042683126614341639842483682890950565236432842426963388102163707941186255544820633600 

noncomputable def Ns300p853 := BSN.cos_dyadic_bound_f 331081338 268435456 4 3 268435456 134217728 Ns300p850 Ns300p122 Ns300p851 Ns300p852 Ns300p125 Ns300p851 88867109 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 331081338) qz342 0 3 Ns300p850 Ns300p122 Ns300p851 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 331081338) qz343 0 3 Ns300p852 Ns300p125 Ns300p851 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p854 := nat_lit 17649766441082159146624116401598827085013549374801690428131178669110768396052493151583360333266789133250727936 

noncomputable def Ns300p855 := nat_lit 2003165588874104734601122962542925557620386488981818211378604950752796314335532991516835006738133159936 

noncomputable def Ns300p856 := nat_lit 88205061141207116901887428944178162255725541289409835342625093051735291323458725353418443470620864553281130496 

noncomputable def Ns300p857 := BSN.sin_dyadic_bound_f 335075806 268435456 4 3 268435456 134217728 Ns300p854 Ns300p237 Ns300p855 Ns300p856 Ns300p240 Ns300p855 254592998 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 335075806) qz344 0 3 Ns300p854 Ns300p237 Ns300p855 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 335075806) qz345 0 3 Ns300p856 Ns300p240 Ns300p855 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p858 := nat_lit 52433788227888126218321950345127940776461872760483061180998909564026880 

noncomputable def Ns300p859 := nat_lit 11146927989482448600311458849656741297890508589824833265968166731776 

noncomputable def Ns300p860 := nat_lit 137308540808676406607395079970530876833394034501643539077328433731076096 

noncomputable def Ns300p861 := BSN.sin_dyadic_bound_f 240377824 268435456 3 2 268435456 134217728 Ns300p858 Ns300p116 Ns300p859 Ns300p860 Ns300p119 Ns300p859 209515879 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 240377824) qz344 0 2 Ns300p858 Ns300p116 Ns300p859 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 240377824) qz345 0 2 Ns300p860 Ns300p119 Ns300p859 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p862 := nat_lit 15143457972847990143335285385916416593818097963024214552480931661135013280632759228069195943891776309918109696 

noncomputable def Ns300p863 := nat_lit 22077793319266552967671179507884891912809777254758665115762147335802200400415836531957738256747894870016 

noncomputable def Ns300p864 := nat_lit 91673861430294085050071001859486418986008874599485612230096291210295016516127121275601892535657558188245585920 

noncomputable def Ns300p865 := BSN.cos_dyadic_bound_f 409257178 268435456 4 3 268435456 134217728 Ns300p862 Ns300p122 Ns300p863 Ns300p864 Ns300p125 Ns300p863 12395840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 409257178) qz342 0 3 Ns300p862 Ns300p122 Ns300p863 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 409257178) qz343 0 3 Ns300p864 Ns300p125 Ns300p863 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p866 := Ns300p817 92946 BSN.abs_quadSignPos (BSN.cos_quad_nat3 163 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 209515879 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 74 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 12395840 268435456) qz113 rfl rfl (Ns300p849 RS301to312.d9 RS301to312.d11 RS301to312.d13 RS301to312.d17 (Ns300p853 rfl rfl) (Ns300p857 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns300p848 rfl) RS301to312.d19 RS301to312.d21 RS301to312.d23 RS301to312.d25 RS301to312.d17 (Ns300p861 rfl rfl) (Ns300p865 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns300p867 := nat_lit 31121679628974284658251458129237980211148930726750343912130188212556961 

noncomputable def Ns300p868 := nat_lit 12718427725017209712792046661955962313561965732458532334018317112481 

noncomputable def Ns300p869 := nat_lit 93339602031472819555328790294390028708819668248786114671722528003445921 

noncomputable def Ns300p870 := BSN.cos_dyadic_bound_f 244373539 268435456 3 2 268435456 134217728 Ns300p867 Ns300p110 Ns300p868 Ns300p869 Ns300p113 Ns300p868 164674310 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 244373539) qz342 0 2 Ns300p867 Ns300p110 Ns300p868 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 244373539) qz343 0 2 Ns300p869 Ns300p113 Ns300p868 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p871 := nat_lit 42421513329833583908548323127029957037379841219017115017439404025390625 

noncomputable def Ns300p872 := nat_lit 23623861316506394413343509662017084346613808519869863061676025390625 

noncomputable def Ns300p873 := nat_lit 127217292266867738936818282361765836943446296040011605326194860025390625 

noncomputable def Ns300p874 := BSN.cos_dyadic_bound_f 264039475 268435456 3 2 268435456 134217728 Ns300p871 Ns300p110 Ns300p872 Ns300p873 Ns300p113 Ns300p872 148715772 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 264039475) qz342 0 2 Ns300p871 Ns300p110 Ns300p872 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 264039475) qz343 0 2 Ns300p873 Ns300p113 Ns300p872 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p875 := Ns300p815 125294 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 2 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 164674310 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 58 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 148715772 268435456) qz113 rfl rfl (Ns300p866 rfl rfl) (Ns300p848 rfl) RS301to312.d27 RS301to312.d29 RS301to312.d31 RS301to312.d33 RS301to312.d17 (Ns300p870 rfl rfl) (Ns300p874 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p876 := nat_lit 85963920062510615056972572330237747766758749659863587281092329700515905 

noncomputable def Ns300p877 := nat_lit 29953468201964913109250602188694526625807260292715057047012050395201 

noncomputable def Ns300p878 := nat_lit 225095104072343667670846521794698119679354942116311666120022843991187521 

noncomputable def Ns300p879 := BSN.sin_dyadic_bound_f 271991849 268435456 3 2 268435456 134217728 Ns300p876 Ns300p116 Ns300p877 Ns300p878 Ns300p119 Ns300p877 227782294 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 271991849) qz344 0 2 Ns300p876 Ns300p116 Ns300p877 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 271991849) qz345 0 2 Ns300p878 Ns300p119 Ns300p877 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p880 := nat_lit 7866868522446662475885777067839991465798700208402838360057995495966241 

noncomputable def Ns300p881 := nat_lit 813160745139235524969717283458461197535793611440165174405736662561 

noncomputable def Ns300p882 := nat_lit 23598979245849708956607391768953057475001029037985634749825175014573601 

noncomputable def Ns300p883 := BSN.cos_dyadic_bound_f 173289421 268435456 3 2 268435456 134217728 Ns300p880 Ns300p110 Ns300p881 Ns300p882 Ns300p113 Ns300p881 214417368 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 173289421) qz342 0 2 Ns300p880 Ns300p110 Ns300p881 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 173289421) qz343 0 2 Ns300p882 Ns300p113 Ns300p881 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p884 := Ns300p813 153557 BSN.abs_quadSignPos (BSN.cos_quad_nat3 111 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 227782294 268435456) BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 214417368 268435456) qz113 rfl rfl (Ns300p875 rfl) (Ns300p848 rfl) RS301to312.d35 RS301to312.d37 RS301to312.d39 RS301to312.d41 RS301to312.d17 (Ns300p879 rfl rfl) (Ns300p883 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p885 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz110) qz110 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz110) qz110 9) 493425494 268435456 153557 268435456 493425494 268435456 153557 268435456 264905794967830528 246712747 67108864 153557 134217728 (Ns300p884 rfl) 

noncomputable def Ns300p886 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz424) (Zeta.RiemannSiegel.correction qz112) 1328811 4194304 1 16777216 59010047493205 70368744177664 146905090152113 6206523236469964800 78413200219493229255 295147905179352825856 

noncomputable def Ns300p887 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz424 1 1 0 1 1328811 4194304 1 16777216 1328811 4194304 1 16777216 

noncomputable def Ns300p888 := @Enclosure.Real.IsNear.sqrt_image qz111 3330708741511 33554432000 623687 33554432000 167152639 167152671 16777216 (@Enclosure.Real.IsNear.of_eq qz111 (@HMul.hMul Real Real Real qz5 qz110 qz3) Bool.false 3330708741511 33554432000 623687 33554432000 (BSN.t_div_two_pi_mk qz110 623687 1000 qz113) (@Enclosure.Real.IsNear.mulLit_ff qz110 qz3 623687 1000 0 1 5340353 33554432 1 33554432 3330708741511 33554432000 623687 33554432000 (Enclosure.Real.IsNear.const Bool.false 623687 1000) RS301to312.d44 rfl)) 

noncomputable abbrev qz837 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 623687 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz685 := qz837

noncomputable abbrev qz428 := qz685

noncomputable abbrev qz117 := qz428

noncomputable def Ns300p889 := @Enclosure.Real.IsNear.sqrt_image qz117 167152655 16777216 1 1048576 52956169 52956175 16777216 (@Enclosure.Real.IsNear.recentre' qz117 Bool.false 334305310 33554432 32 33554432 167152655 16777216 1 1048576 (Ns300p888 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns300p890 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz117) 13239043 4194304 3 16777216 5315243 5315245 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz117) Bool.false 105912344 33554432 6 33554432 13239043 4194304 3 16777216 (Ns300p889 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns300p891 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz117)) Bool.false 10630488 33554432 2 33554432 1328811 4194304 1 16777216 (Ns300p890 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz118 := (@HMul.hMul Real Real Real qz327 qz323 qz423)

noncomputable abbrev qz686 := (@HMul.hMul Real Real Real qz807 qz836 qz836)

noncomputable abbrev qz429 := (@HSub.hSub Real Real Real qz628 (@HSub.hSub Real Real Real qz628 qz686 qz682) qz639)

noncomputable abbrev qz119 := (Real.cos (@HMul.hMul Real Real Real qz327 qz323 qz429))

noncomputable def Ns300p892 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz112) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz118)) qz119) Bool.false 59010047493205 

noncomputable def Ns300p893 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz118)) qz119 8619557 8388608 111 

noncomputable def Ns300p894 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz118)) Bool.false 34478228 33554432 222 33554432 8619557 8388608 111 

noncomputable def Ns300p895 := @Enclosure.Real.IsNear.recentre' (Real.cos qz118) Bool.false 32655388 33554432 462187216 73987522560000 8163847 8388608 28886701 4624220160000 

noncomputable def Ns300p896 := @Enclosure.Real.IsNear.cos_image qz118 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 25380473) qz665) Bool.false 25380473 4194304 101 16777216 Bool.false 32655388 33554432 1 

noncomputable def Ns300p897 := nat_lit 26986075417718650495571399 

noncomputable def Ns300p898 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz112 884279719003555 140737488355328 1 500000000000000 16157711 16777216 1 1048576 14287936142820649662605 2361183241434822606848 Ns300p897 

noncomputable def Ns300p899 := @Enclosure.Real.IsNear.subLit_ff_p qz117 qz1 167152655 16777216 1 1048576 9 1 0 1 16157711 16157711 16777216 1 

noncomputable def Ns300p900 := @Ns300p899 1048576 (@Enclosure.Real.IsNear.recentre' qz117 Bool.false 334305310 33554432 32 33554432 167152655 16777216 1 1048576 (Ns300p888 rfl rfl rfl rfl rfl rfl) rfl) qz350 

noncomputable def Ns300p901 := @Enclosure.Real.IsNear.recentre' qz118 Bool.false 14287936142820649662605 2361183241434822606848 Ns300p897 Ns300p163 25380473 4194304 101 16777216 (@Ns300p898 Ns300p163 RS301to312.d43 (Ns300p900 rfl rfl) rfl) 

noncomputable def Ns300p902 := nat_lit 4836464854175470573433854392043571681997266972967572022807939054737896220740078283613179425 

noncomputable def Ns300p903 := nat_lit 5132530019805651793083495312239791375869987320500912186636767691649573160247684961832481 

noncomputable def Ns300p904 := nat_lit 12658621950427499494185578701037156647765243044967591916194809424241343173964565919524884001 

noncomputable def Ns300p905 := BSN.sin_dyadic_bound_f 92000764723 68719476736 3 2 33554432 8828614 Ns300p902 Ns300p170 Ns300p903 Ns300p904 Ns300p173 Ns300p903 32655388 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 92000764723) qz351 0 2 Ns300p902 Ns300p170 Ns300p903 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 92000764723) qz352 0 2 Ns300p904 Ns300p173 Ns300p903 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p906 := @Ns300p896 4410000 (Ns300p901 rfl) (Enclosure.sfrac_false_div 25380473 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 25380473) qz665) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 809247284621928086634496) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 32655388 33554432 0 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q3 25380473 4194304 226375608064910080 72057594037927936 0 809247284621928086634496 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 32655388 33554432 809247284621928086634496 604462909807314587353088 92000764723 68719476736 8828614 8820000 (Ns300p905 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p907 := @Enclosure.Real.IsNear.inv_image (Real.cos qz118) 8163847 8388608 28886701 4624220160000 17239003 17239225 16777216 (Ns300p895 (Ns300p906 rfl rfl) rfl) rfl 

noncomputable def Ns300p908 := @Enclosure.Real.IsNear.recentre' qz119 Bool.false 13692130 16777216 

noncomputable abbrev qz120 := (@HMul.hMul Real Real Real qz327 qz323 qz429)

noncomputable def Ns300p909 := @Enclosure.Real.IsNear.cos_image qz120 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 10337131)) qz354) Bool.true 10337131 16777216 

noncomputable def Ns300p910 := nat_lit 24407861212172548789724009405 

noncomputable def Ns300p911 := nat_lit 132481806288892648845217640753197 

noncomputable def Ns300p912 := @Enclosure.Real.IsNear.recentre' qz120 Bool.true Ns300p910 Ns300p180 Ns300p911 

noncomputable abbrev qz121 := qz429

noncomputable def Ns300p913 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz121 884279719003555 140737488355328 1 500000000000000 27601968797471 

noncomputable abbrev qz430 := (@HSub.hSub Real Real Real qz628 qz686 qz682)

noncomputable abbrev qz122 := qz430

noncomputable def Ns300p914 := @Enclosure.Real.IsNear.subLit_tf qz122 qz27 10009782753055 281474976710656 24546327 8796093022208 1 16 

noncomputable abbrev qz431 := qz686

noncomputable abbrev qz123 := qz431

noncomputable def Ns300p915 := @Enclosure.Real.IsNear.subLit_ff_n qz123 qz112 261071624759521 281474976710656 16157719 8796093022208 16157711 16777216 1 1048576 

noncomputable def Ns300p916 := @Enclosure.Real.IsNear.mulLit_ff qz112 qz112 16157711 16777216 1 1048576 16157711 16777216 1 1048576 261071624759521 281474976710656 

noncomputable def Ns300p917 := nat_lit 1519939144241500424560377941858497414655344333645986771508321 

noncomputable def Ns300p918 := nat_lit 130376752791959310297925104498865545364014766369827462241 

noncomputable def Ns300p919 := nat_lit 4559556679218917355060537975366494512875304971405220659600481 

noncomputable def Ns300p920 := BSN.cos_dyadic_bound_f 10337131 16777216 3 2 16777216 4410000 Ns300p917 Ns300p189 Ns300p918 Ns300p919 Ns300p192 Ns300p918 13692130 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 10337131) (BSN.cosEvenQ 16777216) 0 2 Ns300p917 Ns300p189 Ns300p918 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 10337131) (BSN.cosOddQ 16777216) 0 2 Ns300p919 Ns300p192 Ns300p918 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p921 := @Ns300p908 2631044432 147975045120000 6846065 8388608 164440277 9248440320000 (@Ns300p909 589 33554432 Bool.false 13692130 16777216 1 4410000 (@Ns300p912 Ns300p183 10337131 16777216 589 33554432 (@Ns300p913 281474976710656 24546327 8796093022208 Ns300p910 Ns300p180 Ns300p911 Ns300p183 RS301to312.d43 (@Ns300p914 0 1 441631500759536 27601968797471 281474976710656 24546327 8796093022208 (@Ns300p915 167936287361078394880 10009782753055 281474976710656 24546327 8796093022208 (@Ns300p916 16157719 8796093022208 (Ns300p900 rfl rfl) (Ns300p900 rfl rfl) rfl) (Ns300p900 rfl rfl) rfl rfl) qz358 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 10337131 16777216) (BSN.cos_neg_of_bound 10337131 16777216 Bool.false 13692130 16777216 1 4410000 (Ns300p920 rfl rfl)) rfl rfl) 

noncomputable def Ns300p922 := @Ns300p886 157208246418893708737 Ns300p809 (Ns300p887 qz29 (@Enclosure.Real.IsNear.of_eq qz424 (@Inv.inv Real Real.instInv (Real.sqrt qz117)) Bool.false 1328811 4194304 1 16777216 (BSN.rpow_neg_quarter_mk qz111 (BSN.t_div_two_pi_nonneg qz110 623687 1000 qz113)) Ns300p891) rfl) (@Ns300p892 70368744177664 146905090152113 6206523236469964800 (BSN.correction_mk qz112 (BSN.cos_two_pi_p_ne_zero_mk qz110 623687 1000 9 qz113 rfl rfl (@BSN.floor_sqrt_eq_dec qz110 623687 1000 9 qz113 rfl rfl rfl))) (@Ns300p893 16777216 6846065 8388608 164440277 9248440320000 59010047493205 70368744177664 146905090152113 6206523236469964800 (@Ns300p894 16777216 (Ns300p907 rfl rfl rfl rfl rfl) rfl) (Ns300p921 rfl) rfl)) 

noncomputable def Ns300p923 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz110) (hardyZApproximantRS₀ qz110) Bool.true 1006640935968740613433 295147905179352825856 23983585461984353328577 Ns300p809 (@Eq.refl Real (hardyZApproximantRS₀ qz110)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz110) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz110) qz110 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz424) (Zeta.RiemannSiegel.correction qz112))) Bool.true 1006640935968740613433 295147905179352825856 23983585461984353328577 Ns300p809 (BSN.hardyZApproximantRS₀_eq qz110 9 (@BSN.floor_sqrt_eq_dec qz110 623687 1000 9 qz113 rfl rfl rfl)) (@Ns300p811 1006640935968740613433 295147905179352825856 23983585461984353328577 Ns300p809 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz110) qz110 9) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz110) qz110 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz110) qz110 9)) Bool.true 246712747 67108864 153557 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz110) qz110 9) (Ns300p885 (Ns300p884 rfl) rfl rfl)) (Ns300p922 rfl) rfl rfl)) 

theorem RS301to312.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz110) Bool.true 1006640935968740613433 295147905179352825856 23983585461984353328577 Ns300p809 := Ns300p923 

noncomputable def Ns300p924 := nat_lit 433867420613648654008320000 

noncomputable def Ns300p925 := nat_lit 1306780399055621056155634106368 

noncomputable abbrev qz838 := (Enclosure.sfrac Bool.false 625053 1000)

noncomputable abbrev qz687 := qz838

noncomputable abbrev qz432 := qz687

noncomputable abbrev qz124 := qz432

noncomputable abbrev qz839 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 625053 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz688 := qz839

noncomputable abbrev qz433 := qz688

noncomputable abbrev qz125 := qz433

noncomputable abbrev qz840 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 625053 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz689 := qz840

noncomputable abbrev qz434 := qz689

noncomputable abbrev qz126 := qz434

noncomputable abbrev qz435 := (@HPow.hPow Real Real Real qz627 qz125 qz8)

noncomputable def Ns300p926 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz124) qz124 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz435) (Zeta.RiemannSiegel.correction qz126)) 258382933 67108864 76949 67108864 1290462859136877494625 4722366482869645213696 3356242005847902099451 Ns300p924 Ns300p925 

noncomputable def Ns300p927 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz124) qz124 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 625053 1000 111 158 268435456 134217728 4503599627370496 Bool.false 301906683673 2456 

noncomputable def Ns300p928 := Ns300p927 558195838 62 94906264 8 589812974 62 89478488 8 Bool.false 532974402 125572 Bool.true 191324918 Bool.true 135811498 14148475504056880 1 Bool.false 175532598 Bool.false Bool.false 234806033 Bool.true Bool.false 516765866 

noncomputable def Ns300p929 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz124) qz124 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 625053 1000 3 58 268435456 134217728 4503599627370496 Bool.false 301906683673 2456 

noncomputable def Ns300p930 := Ns300p929 480971758 62 109588312 8 522351262 62 101459064 8 Bool.false 618357486 93153 Bool.false 8871135 Bool.true 134408854 14148475504056880 1 Bool.false 8869520 Bool.false Bool.false 235482584 Bool.true Bool.false 532974402 

noncomputable def Ns300p931 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz124) qz124 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 625053 1000 164 75 268435456 134217728 4503599627370496 Bool.false 301906683673 2456 

noncomputable def Ns300p932 := Ns300p931 372130544 61 134217720 8 432030192 61 120047984 16 Bool.false 411743621 54683 Bool.false 153552518 Bool.false 240608952 14148475504056880 1 Bool.false 225701881 Bool.false Bool.false 209660291 Bool.false Bool.false 618357486 

noncomputable def Ns300p933 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz124) qz124 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 625053 1000 440 278 268435456 134217728 4503599627370496 Bool.false 301906683673 2456 

noncomputable def Ns300p934 := Ns300p933 186065264 61 189812528 16 294906480 61 154981288 8 Bool.false 268435448 2525 Bool.false 76763776 Bool.false 353738571 14148475504056880 1 Bool.false 257534084 Bool.false Bool.false 67196503 Bool.true Bool.false 411743621 

noncomputable def Ns300p935 := nat_lit 15103045311070434644025881665834088289295015087424312107 

noncomputable def Ns300p936 := nat_lit 13428629024474419388480264837754923584094846792499200 

noncomputable def Ns300p937 := nat_lit 1806336000000000000000000 

noncomputable def Ns300p938 := nat_lit 45795853896885131432180841836640000 

noncomputable def Ns300p939 := nat_lit 171749066482035707531853153596720051520 

noncomputable abbrev qz436 := (@Eq.refl Real qz687)

noncomputable abbrev qz127 := qz436

noncomputable def Ns300p940 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz124 625053 1000 1562766011236 16000000 1250106 4000 2000 Ns300p938 Ns300p939 qz127 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns300p941 := nat_lit 43496770495882851774794539197602174273169643451782018868160 

noncomputable abbrev qz437 := (@HMul.hMul Real Real Real qz623 qz629 (@HSub.hSub Real Real Real qz628 qz630 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz631 (@Nat.cast Real Real.instNatCast 1250106)))))

noncomputable abbrev qz690 := (Real.log (Enclosure.sfrac Bool.false 1562766011236 16000000))

noncomputable abbrev qz691 := (Enclosure.sfrac Bool.false 625053 2000)

noncomputable abbrev qz128 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 625053 4000) qz690) qz437) qz691)

noncomputable abbrev qz438 := (@HSub.hSub Real Real Real qz11 qz128 (@HMul.hMul Real Real Real qz5 qz691 (Real.log Real.pi)))

noncomputable def Ns300p942 := @Enclosure.Real.IsNear.addLit_ft_p qz438 (Enclosure.sfrac Bool.true Ns300p938 Ns300p939) 253257742234901609683 225179981368524800 16515203674505375857 Ns300p937 Ns300p938 Ns300p939 0 1 Ns300p941 

noncomputable def Ns300p943 := nat_lit 84979196902945340887987650560000 

noncomputable abbrev qz439 := (@HMul.hMul Real Real Real qz5 qz691 (Real.log Real.pi))

noncomputable def Ns300p944 := @Enclosure.Real.IsNear.subLit_ff_p qz128 qz439 1669088886996471181343 1125899906842624000 1978291727648617 441000000000000000000 24008761395333 67108864000 625053 134217728000 Ns300p943 253257742234901609683 225179981368524800 

noncomputable def Ns300p945 := nat_lit 3338177773992942362686000 

noncomputable abbrev qz129 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 625053 4000) qz690) qz437)

noncomputable def Ns300p946 := @Enclosure.Real.IsNear.subLit_ff_p qz129 qz691 2020962444232322510879 1125899906842624000 1978291727648617 441000000000000000000 625053 2000 0 1 Ns300p945 1669088886996471181343 1125899906842624000 1978291727648617 441000000000000000000 

noncomputable def Ns300p947 := nat_lit 4550802855387227231538333201561812992 

noncomputable def Ns300p948 := nat_lit 55559228504756909833715712 

noncomputable def Ns300p949 := nat_lit 153271727011599474476066552533482085212577893401783255332480669798648419817027563078475362239538462170216828038465247708074475520 

noncomputable def Ns300p950 := nat_lit 2028288842538732503669622316459352706536955662384427195442017991612309289300968996603380836933434829678683230912787004500475904 

noncomputable def Ns300p951 := nat_lit 1220866467303752829534446157732152592757147762821777599155043620237227603630271692273876636326659065134574197747424952320 

noncomputable def Ns300p952 := BSN.log_dyadic_bound 514190011236 2611342011236 6 5 Ns300p949 134217728 35280000 Ns300p950 Ns300p951 53556132 3125532022472 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 514190011236) (BSN.artanhQ 2611342011236) 0 5 Ns300p950 Ns300p949 Ns300p951 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns300p953 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 625053 4000) qz690 625053 4000 0 1 3233972733418743 281474976710656 781250441 27562500000000000 2021404358941585568379 1125899906842624000 162774310632791 36750000000000000000 (Enclosure.Real.IsNear.const Bool.false 625053 4000) (BSN.isNear_log_sfrac 1562766011236 16000000 3233972733418743 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1562766011236) qz335)) Bool.false Ns300p948 Ns300p94 1000000564480000 35280000000000000000000 3233972733418743 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1562766011236 16000000 16 3125532022472 2097152000000 53556132 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns300p952 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns300p954 := BSN.arctan_dyadic_bound_f 1000 1250106 1 0 16777216 4410000 0 1 1 0 1 1 13420 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1250106) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1250106) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns300p955 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1250106))) 884279719003555 562949953421312 1 2000000000000000 13420 16777216 1 4410000 14828197061767032995840 883829418526115 562949953421312 200000000441 882000000000000000 qz16 (Ns300p954 rfl) rfl rfl 

noncomputable abbrev qz130 := qz437

noncomputable def Ns300p956 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 625053 4000) qz690) qz130 2021404358941585568379 1125899906842624000 162774310632791 36750000000000000000 883829418526115 2251799813685248 200000000441 3528000000000000000 Ns300p947 2020962444232322510879 1125899906842624000 1978291727648617 441000000000000000000 (Ns300p953 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1250106)))) 1 4 0 1 883829418526115 562949953421312 200000000441 882000000000000000 883829418526115 2251799813685248 200000000441 3528000000000000000 qz340 Ns300p955 rfl) 

noncomputable def Ns300p957 := @Ns300p942 Ns300p935 Ns300p936 16515203674505375857 Ns300p937 (@Ns300p944 16515203674505375857 Ns300p937 (Ns300p946 (Ns300p956 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 625053 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz691 (Real.log Real.pi) 625053 2000 0 1 38410761 33554432 1 67108864 24008761395333 67108864000 625053 134217728000 (Enclosure.Real.IsNear.const Bool.false 625053 2000) RS301to312.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns300p938 Ns300p939) 

noncomputable def Ns300p958 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz124) Bool.false Ns300p935 Ns300p936 16515203674505375857 Ns300p937 37738335459 33554432 77 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz124) (@HAdd.hAdd Real Real Real qz341 qz438 (Enclosure.sfrac Bool.true Ns300p938 Ns300p939)) Bool.false Ns300p935 Ns300p936 16515203674505375857 Ns300p937 Ns300p940 (Ns300p957 rfl rfl)) 

noncomputable def Ns300p959 := nat_lit 7595275043561677256654848 

noncomputable def Ns300p960 := nat_lit 3509668721290619906693794557439936884089956874222757773801360959772579464071813993290767131991452881716322325331978499210841157050471878656 

noncomputable def Ns300p961 := nat_lit 2500140743990551101509877433339784622769198369451448416139351984066593555250293407429717616060750325410005333051369127241339331219456 

noncomputable def Ns300p962 := nat_lit 17526544845174081039142977125055402481630068152160243354888028611716908567063892033862633667297849828074853982401092533785407486209579094016 

noncomputable def Ns300p963 := BSN.sin_dyadic_bound_f 107935350166 68719476736 4 3 33554432 8828614 Ns300p960 Ns300p383 Ns300p961 Ns300p962 Ns300p386 Ns300p961 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107935350166) qz351 0 3 Ns300p960 Ns300p383 Ns300p961 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107935350166) qz352 0 3 Ns300p962 Ns300p386 Ns300p961 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p964 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz124) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 37738335459) qz349) Bool.false 37738335459 33554432 77 8388608 Bool.false 33554431 33554432 1 4410000 (Ns300p958 rfl) (Enclosure.sfrac_false_div 37738335459 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 37738335459) qz349) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns300p959) qz353) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 178 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q3 37738335459 33554432 226375608064910080 72057594037927936 178 Ns300p959 Ns300p94 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554431 33554432 Ns300p959 Ns300p94 107935350166 68719476736 8828614 8820000 (Ns300p963 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p965 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz124) Bool.false Ns300p935 Ns300p936 16515203674505375857 Ns300p937 301906683673 268435456 2456 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz124) (@HAdd.hAdd Real Real Real qz341 qz438 (Enclosure.sfrac Bool.true Ns300p938 Ns300p939)) Bool.false Ns300p935 Ns300p936 16515203674505375857 Ns300p937 Ns300p940 (Ns300p957 rfl rfl)) 

noncomputable def Ns300p966 := Ns300p934 54683 BSN.abs_quadSignPos (BSN.cos_quad_nat0 440 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 257534084 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 278 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 67196503 268435456) qz127 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz124) qz124 1) Bool.false 33554431 33554432 21747413 2312110080000 268435448 268435456 2525 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz124) qz124 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz124)) Bool.false 33554431 33554432 21747413 2312110080000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz124) qz124) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz124)) Bool.false 33554431 33554432 347958608 36993761280000 33554431 33554432 21747413 2312110080000 (Ns300p964 rfl rfl) rfl)) rfl) (Ns300p965 rfl) RS301to312.d7 

noncomputable def Ns300p967 := nat_lit 34723645830033143134596917886976 

noncomputable def Ns300p968 := BSN.cos_dyadic_bound_f 76763776 268435456 2 1 268435456 134217728 Ns300p967 Ns300p133 Ns300p967 Ns300p967 Ns300p134 Ns300p967 257534084 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 76763776) qz342 0 1 Ns300p967 Ns300p133 Ns300p967 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 76763776) qz343 0 1 Ns300p967 Ns300p134 Ns300p967 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p969 := nat_lit 8440214233742979035076973857926330727527561543519521196043612454707171574109030373958883102123558963078187921 

noncomputable def Ns300p970 := nat_lit 3838742710625950001961998473523854247506759862510885735599382848590864913429721738663308695915627236241 

noncomputable def Ns300p971 := nat_lit 51142783143121653447555111594769347134964098748743615677595914723294775113699642219557781000781548550473337745 

noncomputable def Ns300p972 := BSN.cos_dyadic_bound_f 353738571 268435456 4 3 268435456 134217728 Ns300p969 Ns300p122 Ns300p970 Ns300p971 Ns300p125 Ns300p970 67196503 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 353738571) qz342 0 3 Ns300p969 Ns300p122 Ns300p970 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 353738571) qz343 0 3 Ns300p971 Ns300p125 Ns300p970 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p973 := nat_lit 4849804630835747248204260857099059300648858230011223803114552991129856 

noncomputable def Ns300p974 := nat_lit 309069066358849938485903424908919005398411166971162199689929400576 

noncomputable def Ns300p975 := nat_lit 14548795754374524044735810764447360063935777867699729084944279114588416 

noncomputable def Ns300p976 := BSN.cos_dyadic_bound_f 153552518 268435456 3 2 268435456 134217728 Ns300p973 Ns300p110 Ns300p974 Ns300p975 Ns300p113 Ns300p974 225701881 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 153552518) qz342 0 2 Ns300p973 Ns300p110 Ns300p974 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 153552518) qz343 0 2 Ns300p975 Ns300p113 Ns300p974 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p977 := nat_lit 52635786839872017641099498810441553011945096196170489190945643844075520 

noncomputable def Ns300p978 := nat_lit 11232961022629496824705262574249159382026267299776650332067443245056 

noncomputable def Ns300p979 := nat_lit 137837445500866265112782497887940997344666257033389738066224767540658176 

noncomputable def Ns300p980 := BSN.sin_dyadic_bound_f 240608952 268435456 3 2 268435456 134217728 Ns300p977 Ns300p116 Ns300p978 Ns300p979 Ns300p119 Ns300p978 209660291 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 240608952) qz344 0 2 Ns300p977 Ns300p116 Ns300p978 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 240608952) qz345 0 2 Ns300p979 Ns300p119 Ns300p978 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p981 := Ns300p932 93153 BSN.abs_quadSignPos (BSN.cos_quad_nat0 164 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 225701881 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 75 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 209660291 268435456) qz127 rfl rfl (Ns300p966 RS301to312.d9 RS301to312.d11 RS301to312.d13 RS301to312.d17 (Ns300p968 rfl rfl) (Ns300p972 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns300p965 rfl) RS301to312.d19 RS301to312.d21 RS301to312.d23 RS301to312.d25 RS301to312.d17 (Ns300p976 rfl rfl) (Ns300p980 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns300p982 := BSN.sin_dyadic_bound_f 8871135 268435456 1 0 268435456 134217728 0 1 1 0 1 1 8869520 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 8871135) qz344 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 8871135) qz345 0 0 rfl) rfl rfl 

noncomputable def Ns300p983 := nat_lit 2847059593183716146523405296822893922552039046954502505136833047388416 

noncomputable def Ns300p984 := nat_lit 106518005464336012577734115807378992268260252115579998801971732736 

noncomputable def Ns300p985 := nat_lit 8540965743540219767545060422237067009671580620359276355412895198699776 

noncomputable def Ns300p986 := BSN.cos_dyadic_bound_f 134408854 268435456 3 2 268435456 134217728 Ns300p983 Ns300p110 Ns300p984 Ns300p985 Ns300p113 Ns300p984 235482584 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 134408854) qz342 0 2 Ns300p983 Ns300p110 Ns300p984 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 134408854) qz343 0 2 Ns300p985 Ns300p113 Ns300p984 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p987 := Ns300p930 125572 BSN.abs_quadSignPos (BSN.cos_quad_nat3 3 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 8869520 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 58 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 235482584 268435456) qz127 rfl rfl (Ns300p981 rfl rfl) (Ns300p965 rfl) RS301to312.d27 RS301to312.d29 RS301to312.d31 RS301to312.d33 RS301to312.d17 (Ns300p982 rfl rfl) (Ns300p986 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p988 := nat_lit 21040909340295080599986425480403049082894179816585962215483456337076480 

noncomputable def Ns300p989 := nat_lit 1795445748475619553557744461374587391345279104697577196331757854976 

noncomputable def Ns300p990 := nat_lit 55104236598132441044496782767165760170851150020127057344138800893911296 

noncomputable def Ns300p991 := BSN.sin_dyadic_bound_f 191324918 268435456 3 2 268435456 134217728 Ns300p988 Ns300p116 Ns300p989 Ns300p990 Ns300p119 Ns300p989 175532598 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 191324918) qz344 0 2 Ns300p988 Ns300p116 Ns300p989 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 191324918) qz345 0 2 Ns300p990 Ns300p119 Ns300p989 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p992 := nat_lit 2967781284688174315055778031437623129163540922515916485617772358164736 

noncomputable def Ns300p993 := nat_lit 115742355368800254253025297200838316759054707389247259902721024256 

noncomputable def Ns300p994 := nat_lit 8903112369353785344658828043718467710857104658132970962333511632445696 

noncomputable def Ns300p995 := BSN.cos_dyadic_bound_f 135811498 268435456 3 2 268435456 134217728 Ns300p992 Ns300p110 Ns300p993 Ns300p994 Ns300p113 Ns300p993 234806033 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 135811498) qz342 0 2 Ns300p992 Ns300p110 Ns300p993 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 135811498) qz343 0 2 Ns300p994 Ns300p113 Ns300p993 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p996 := Ns300p928 153898 BSN.abs_quadSignPos (BSN.cos_quad_nat3 111 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 175532598 268435456) BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 234806033 268435456) qz127 rfl rfl (Ns300p987 rfl) (Ns300p965 rfl) RS301to312.d35 RS301to312.d37 RS301to312.d39 RS301to312.d41 RS301to312.d17 (Ns300p991 rfl rfl) (Ns300p995 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p997 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz124) qz124 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz124) qz124 9) 516765866 268435456 153898 268435456 516765866 268435456 153898 268435456 277436561769889792 258382933 67108864 76949 67108864 (Ns300p996 rfl) 

noncomputable def Ns300p998 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz435) (Zeta.RiemannSiegel.correction qz126) 10624675 33554432 1 33554432 121459043136555 140737488355328 629681875712677 25860513485291520000 1290462859136877494625 4722366482869645213696 

noncomputable def Ns300p999 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz435 1 1 0 1 10624675 33554432 1 33554432 10624675 33554432 1 33554432 

noncomputable def Ns300p1000 := @Enclosure.Real.IsNear.sqrt_image qz125 3338003663709 33554432000 625053 33554432000 167335587 167335620 16777216 (@Enclosure.Real.IsNear.of_eq qz125 (@HMul.hMul Real Real Real qz5 qz124 qz3) Bool.false 3338003663709 33554432000 625053 33554432000 (BSN.t_div_two_pi_mk qz124 625053 1000 qz127) (@Enclosure.Real.IsNear.mulLit_ff qz124 qz3 625053 1000 0 1 5340353 33554432 1 33554432 3338003663709 33554432000 625053 33554432000 (Enclosure.Real.IsNear.const Bool.false 625053 1000) RS301to312.d44 rfl)) 

noncomputable abbrev qz841 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 625053 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz692 := qz841

noncomputable abbrev qz440 := qz692

noncomputable abbrev qz131 := qz440

noncomputable def Ns300p1001 := @Enclosure.Real.IsNear.sqrt_image qz131 334671207 33554432 33 33554432 52985142 52985148 16777216 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 334671207 33554432 33 33554432 334671207 33554432 33 33554432 (Ns300p1000 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns300p1002 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz131) 52985145 16777216 3 16777216 5312337 5312338 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz131) Bool.false 105970290 33554432 6 33554432 52985145 16777216 3 16777216 (Ns300p1001 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns300p1003 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz131)) Bool.false 10624675 33554432 1 33554432 10624675 33554432 1 33554432 (Ns300p1002 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz132 := (@HMul.hMul Real Real Real qz327 qz323 qz434)

noncomputable abbrev qz693 := (@HMul.hMul Real Real Real qz807 qz840 qz840)

noncomputable abbrev qz441 := (@HSub.hSub Real Real Real qz628 (@HSub.hSub Real Real Real qz628 qz693 qz689) qz639)

noncomputable abbrev qz133 := (Real.cos (@HMul.hMul Real Real Real qz327 qz323 qz441))

noncomputable def Ns300p1004 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz126) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz132)) qz133) Bool.false 121459043136555 

noncomputable def Ns300p1005 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz132)) qz133 8501985 8388608 111 

noncomputable def Ns300p1006 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz132)) Bool.false 34007940 33554432 222 33554432 8501985 8388608 111 

noncomputable def Ns300p1007 := @Enclosure.Real.IsNear.recentre' (Real.cos qz132) Bool.false 33106972 33554432 59427152 9248440320000 8276743 8388608 3714197 578027520000 

noncomputable def Ns300p1008 := @Enclosure.Real.IsNear.cos_image qz132 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 205342783) qz349) Bool.false 205342783 33554432 13 2097152 Bool.false 33106972 33554432 1 

noncomputable def Ns300p1009 := nat_lit 890540488779183892610862759 

noncomputable def Ns300p1010 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz126 884279719003555 140737488355328 1 500000000000000 32681319 33554432 33 33554432 28899427581985543089045 4722366482869645213696 Ns300p1009 

noncomputable def Ns300p1011 := @Enclosure.Real.IsNear.subLit_ff_p qz131 qz1 334671207 33554432 33 33554432 9 1 0 1 32681319 32681319 33554432 33 

noncomputable def Ns300p1012 := @Ns300p1011 33554432 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 334671207 33554432 33 33554432 334671207 33554432 33 33554432 (Ns300p1000 rfl rfl rfl rfl rfl rfl) rfl) qz350 

noncomputable def Ns300p1013 := @Enclosure.Real.IsNear.recentre' qz132 Bool.false 28899427581985543089045 4722366482869645213696 Ns300p1009 Ns300p550 205342783 33554432 13 2097152 (@Ns300p1010 Ns300p550 RS301to312.d43 (Ns300p1012 rfl rfl) rfl) 

noncomputable def Ns300p1014 := nat_lit 6805298950246629266948096 

noncomputable def Ns300p1015 := nat_lit 5906548093725208955496253677478559794617106954213558781262158245260197409538805206425390625 

noncomputable def Ns300p1016 := nat_lit 7651370997485662665151582198283889831207872206636636168265290931962284189624176025390625 

noncomputable def Ns300p1017 := nat_lit 15457142787665332381984704688884720783318086420320004159033223028458292374389860208025390625 

noncomputable def Ns300p1018 := BSN.sin_dyadic_bound_f 96709114675 68719476736 3 2 33554432 8828614 Ns300p1015 Ns300p170 Ns300p1016 Ns300p1017 Ns300p173 Ns300p1016 33106972 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 96709114675) qz351 0 2 Ns300p1015 Ns300p170 Ns300p1016 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 96709114675) qz352 0 2 Ns300p1017 Ns300p173 Ns300p1016 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1019 := @Ns300p1008 4410000 (Ns300p1013 rfl) (Enclosure.sfrac_false_div 205342783 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 205342783) qz349) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns300p1014) qz353) 226375608064910080 72057594037927936 Bool.false 33106972 33554432 0 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q3 205342783 33554432 226375608064910080 72057594037927936 0 Ns300p1014 Ns300p94 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33106972 33554432 Ns300p1014 Ns300p94 96709114675 68719476736 8828614 8820000 (Ns300p1018 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p1020 := @Enclosure.Real.IsNear.inv_image (Real.cos qz132) 8276743 8388608 3714197 578027520000 17003859 17004081 16777216 (Ns300p1007 (Ns300p1019 rfl rfl) rfl) rfl 

noncomputable def Ns300p1021 := @Enclosure.Real.IsNear.recentre' qz133 Bool.false 14285963 16777216 

noncomputable abbrev qz134 := (@HMul.hMul Real Real Real qz327 qz323 qz441)

noncomputable def Ns300p1022 := @Enclosure.Real.IsNear.cos_image qz134 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 18519977)) qz349) Bool.true 18519977 33554432 

noncomputable def Ns300p1023 := nat_lit 87458119242447912365072942605 

noncomputable def Ns300p1024 := nat_lit 17617937045464282493463761443155349 

noncomputable def Ns300p1025 := @Enclosure.Real.IsNear.recentre' qz134 Bool.true Ns300p1023 Ns300p564 Ns300p1024 

noncomputable def Ns300p1026 := nat_lit 967140655691703339764940800000000000000 

noncomputable abbrev qz135 := qz441

noncomputable def Ns300p1027 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz135 884279719003555 140737488355328 1 500000000000000 98903228653711 

noncomputable abbrev qz442 := (@HSub.hSub Real Real Real qz628 qz693 qz689)

noncomputable abbrev qz136 := qz442

noncomputable def Ns300p1028 := @Enclosure.Real.IsNear.subLit_tf qz136 qz27 28534484476047 1125899906842624 3264264399 1125899906842624 1 16 

noncomputable abbrev qz443 := qz693

noncomputable abbrev qz137 := qz443

noncomputable def Ns300p1029 := @Enclosure.Real.IsNear.subLit_ff_n qz137 qz126 1068068611579761 1125899906842624 2156968143 1125899906842624 32681319 33554432 33 33554432 

noncomputable def Ns300p1030 := @Enclosure.Real.IsNear.mulLit_ff qz126 qz126 32681319 33554432 33 33554432 32681319 33554432 33 33554432 1068068611579761 1125899906842624 

noncomputable def Ns300p1031 := nat_lit 250550116968381068769522676926315467823834933313464576049028161 

noncomputable def Ns300p1032 := nat_lit 13839600187509230387276221340492842418161202186176883465281 

noncomputable def Ns300p1033 := nat_lit 751622671704768187847793478336265417786668477536021374380153921 

noncomputable def Ns300p1034 := BSN.cos_dyadic_bound_f 18519977 33554432 3 2 16777216 4410000 Ns300p1031 Ns300p687 Ns300p1032 Ns300p1033 Ns300p690 Ns300p1032 14285963 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 18519977) (BSN.cosEvenQ 33554432) 0 2 Ns300p1031 Ns300p687 Ns300p1032 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 18519977) (BSN.cosOddQ 33554432) 0 2 Ns300p1033 Ns300p690 Ns300p1032 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1035 := @Ns300p1021 683118608 36993761280000 14285963 16777216 42694913 2312110080000 (@Ns300p1022 153 8388608 Bool.false 14285963 16777216 1 4410000 (@Ns300p1025 Ns300p1026 18519977 33554432 153 8388608 (@Ns300p1027 1125899906842624 3264264399 1125899906842624 Ns300p1023 Ns300p564 Ns300p1024 Ns300p1026 RS301to312.d43 (@Ns300p1028 0 1 1582451658459376 98903228653711 1125899906842624 3264264399 1125899906842624 (@Ns300p1029 957458419006574690304 28534484476047 1125899906842624 3264264399 1125899906842624 (@Ns300p1030 2156968143 1125899906842624 (Ns300p1012 rfl rfl) (Ns300p1012 rfl rfl) rfl) (Ns300p1012 rfl rfl) rfl rfl) qz358 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 18519977 33554432) (BSN.cos_neg_of_bound 18519977 33554432 Bool.false 14285963 16777216 1 4410000 (Ns300p1034 rfl rfl)) rfl rfl) 

noncomputable def Ns300p1036 := @Ns300p998 3356242005847902099451 Ns300p924 (Ns300p999 qz29 (@Enclosure.Real.IsNear.of_eq qz435 (@Inv.inv Real Real.instInv (Real.sqrt qz131)) Bool.false 10624675 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz125 (BSN.t_div_two_pi_nonneg qz124 625053 1000 qz127)) Ns300p1003) rfl) (@Ns300p1004 140737488355328 629681875712677 25860513485291520000 (BSN.correction_mk qz126 (BSN.cos_two_pi_p_ne_zero_mk qz124 625053 1000 9 qz127 rfl rfl (@BSN.floor_sqrt_eq_dec qz124 625053 1000 9 qz127 rfl rfl rfl))) (@Ns300p1005 16777216 14285963 16777216 42694913 2312110080000 121459043136555 140737488355328 629681875712677 25860513485291520000 (@Ns300p1006 16777216 (Ns300p1020 rfl rfl rfl rfl rfl) rfl) (Ns300p1035 rfl) rfl)) 

noncomputable def Ns300p1037 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz124) (hardyZApproximantRS₀ qz124) Bool.false 19472545371288374903137 4722366482869645213696 500841405050772195219451 Ns300p924 (@Eq.refl Real (hardyZApproximantRS₀ qz124)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz124) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz124) qz124 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz435) (Zeta.RiemannSiegel.correction qz126))) Bool.false 19472545371288374903137 4722366482869645213696 500841405050772195219451 Ns300p924 (BSN.hardyZApproximantRS₀_eq qz124 9 (@BSN.floor_sqrt_eq_dec qz124 625053 1000 9 qz127 rfl rfl rfl)) (@Ns300p926 19472545371288374903137 4722366482869645213696 500841405050772195219451 Ns300p924 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz124) qz124 9) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz124) qz124 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz124) qz124 9)) Bool.false 258382933 67108864 76949 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz124) qz124 9) (Ns300p997 (Ns300p996 rfl) rfl rfl)) (Ns300p1036 rfl) rfl rfl)) 

theorem RS301to312.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz124) Bool.false 19472545371288374903137 4722366482869645213696 500841405050772195219451 Ns300p924 := Ns300p1037 

noncomputable def Ns300p1038 := nat_lit 520640904736378384809984000 

noncomputable def Ns300p1039 := nat_lit 519395318245508067740620947456 

noncomputable abbrev qz842 := (Enclosure.sfrac Bool.false 626419 1000)

noncomputable abbrev qz694 := qz842

noncomputable abbrev qz444 := qz694

noncomputable abbrev qz138 := qz444

noncomputable abbrev qz843 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 626419 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz695 := qz843

noncomputable abbrev qz445 := qz695

noncomputable abbrev qz139 := qz445

noncomputable abbrev qz844 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 626419 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz696 := qz844

noncomputable abbrev qz446 := qz696

noncomputable abbrev qz140 := qz446

noncomputable abbrev qz447 := (@HPow.hPow Real Real Real qz627 qz139 qz8)

noncomputable def Ns300p1040 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz138) qz138 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz447) (Zeta.RiemannSiegel.correction qz140)) 64423431 33554432 9639 8388608 2654397019333317074103 9444732965739290427392 4059269154128710522429 Ns300p1038 Ns300p1039 

noncomputable def Ns300p1041 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 626419 1000 111 158 268435456 134217728 4503599627370496 Bool.false 302750246818 2460 

noncomputable def Ns300p1042 := Ns300p1041 558195838 62 94906264 8 589812974 62 89478488 8 Bool.true 211999219 125837 Bool.true 110257288 Bool.true 97932876 14148475504056880 1 Bool.false 107183125 Bool.false Bool.false 250768377 Bool.true Bool.true 257693724 

noncomputable def Ns300p1043 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 626419 1000 3 58 268435456 134217728 4503599627370496 Bool.false 302750246818 2460 

noncomputable def Ns300p1044 := Ns300p1043 480971758 62 109588312 8 522351262 62 101459064 8 Bool.true 183473073 93348 Bool.false 195426858 Bool.true 4377533 14148475504056880 1 Bool.false 178615398 Bool.false Bool.false 268399763 Bool.true Bool.true 211999219 

noncomputable def Ns300p1045 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 626419 1000 165 76 268435456 134217728 4503599627370496 Bool.false 302750246818 2460 

noncomputable def Ns300p1046 := Ns300p1045 372130544 61 134217720 8 432030192 61 120047984 16 Bool.true 265970446 54795 Bool.false 67127912 Bool.false 72361427 14148475504056880 1 Bool.false 66430450 Bool.true Bool.false 258741235 Bool.false Bool.true 183473073 

noncomputable def Ns300p1047 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 626419 1000 441 279 268435456 134217728 4503599627370496 Bool.false 302750246818 2460 

noncomputable def Ns300p1048 := Ns300p1047 186065264 61 189812528 16 294906480 61 154981288 8 Bool.true 268435368 2525 Bool.false 244504342 Bool.false 372802036 14148475504056880 1 Bool.false 212070701 Bool.true Bool.false 264001861 Bool.false Bool.true 265970446 

noncomputable def Ns300p1049 := nat_lit 690521620986314679965392925365632244672005576996613480009 

noncomputable def Ns300p1050 := nat_lit 612255442086173360407614555916808391493668669751296000 

noncomputable def Ns300p1051 := nat_lit 46298460238430586857903175087520000 

noncomputable def Ns300p1052 := nat_lit 174013462721567680207389956853151145280 

noncomputable abbrev qz448 := (@Eq.refl Real qz694)

noncomputable abbrev qz141 := qz448

noncomputable def Ns300p1053 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz138 626419 1000 1569604054244 16000000 1252838 4000 2000 Ns300p1051 Ns300p1052 qz141 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns300p1054 := nat_lit 220966918715620697588925736117002318295041784638916313602880 

noncomputable abbrev qz449 := (@HMul.hMul Real Real Real qz623 qz629 (@HSub.hSub Real Real Real qz628 qz630 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz631 (@Nat.cast Real Real.instNatCast 1252838)))))

noncomputable abbrev qz697 := (Real.log (Enclosure.sfrac Bool.false 1569604054244 16000000))

noncomputable abbrev qz698 := (Enclosure.sfrac Bool.false 626419 2000)

noncomputable abbrev qz142 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 626419 4000) qz697) qz449) qz698)

noncomputable abbrev qz450 := (@HSub.hSub Real Real Real qz11 qz142 (@HMul.hMul Real Real Real qz5 qz698 (Real.log Real.pi)))

noncomputable def Ns300p1055 := @Enclosure.Real.IsNear.addLit_ft_p qz450 (Enclosure.sfrac Bool.true Ns300p1051 Ns300p1052) 1269826870789954960921 1125899906842624000 1839008050727018279 200704000000000000000000 Ns300p1051 Ns300p1052 0 1 Ns300p1054 

noncomputable def Ns300p1056 := nat_lit 17043327755077732007714540748800 

noncomputable abbrev qz451 := (@HMul.hMul Real Real Real qz5 qz698 (Real.log Real.pi))

noncomputable def Ns300p1057 := @Enclosure.Real.IsNear.subLit_ff_p qz142 qz451 334701466405598258693 225179981368524800 220284497784249 49000000000000000000 24061230494859 67108864000 626419 134217728000 Ns300p1056 1269826870789954960921 1125899906842624000 

noncomputable def Ns300p1058 := nat_lit 3347014664055982586930000 

noncomputable abbrev qz143 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 626419 4000) qz697) qz449)

noncomputable def Ns300p1059 := @Enclosure.Real.IsNear.subLit_ff_p qz143 qz698 2026149878900216135193 1125899906842624000 220284497784249 49000000000000000000 626419 2000 0 1 Ns300p1058 334701466405598258693 225179981368524800 220284497784249 49000000000000000000 

noncomputable def Ns300p1060 := nat_lit 4562483919805894491103795425117732864 

noncomputable def Ns300p1061 := nat_lit 55580341451867616756891648 

noncomputable def Ns300p1062 := nat_lit 157332916649283346019549538331790276997433524620127850527857914225460554615593630241442460855798817917295985604059020355064299520 

noncomputable def Ns300p1063 := nat_lit 2127719863575332502544236864558926538626246173443598982523165554486955016287285884485315350856239601547673389854494849267400704 

noncomputable def Ns300p1064 := nat_lit 1393294393018691375815160303010281379287493490918200649635065072081473161973865277868549966103152082553414660530314936320 

noncomputable def Ns300p1065 := BSN.log_dyadic_bound 521028054244 2618180054244 6 5 Ns300p1062 134217728 35280000 Ns300p1063 Ns300p1064 54142134 3139208108488 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 521028054244) (BSN.artanhQ 2618180054244) 0 5 Ns300p1063 Ns300p1062 Ns300p1064 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns300p1066 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 626419 4000) qz697 626419 4000 0 1 3235201668685047 281474976710656 781250441 27562500000000000 2026591794096018456693 1125899906842624000 489390120000779 110250000000000000000 (Enclosure.Real.IsNear.const Bool.false 626419 4000) (BSN.isNear_log_sfrac 1569604054244 16000000 3235201668685047 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1569604054244) qz335)) Bool.false Ns300p1061 Ns300p94 1000000564480000 35280000000000000000000 3235201668685047 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1569604054244 16000000 16 3139208108488 2097152000000 54142134 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns300p1065 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns300p1067 := BSN.arctan_dyadic_bound_f 1000 1252838 1 0 16777216 4410000 0 1 1 0 1 1 13391 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1252838) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1252838) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns300p1068 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1252838))) 884279719003555 562949953421312 1 2000000000000000 13391 16777216 1 4410000 14828213387315682213888 883830391604643 562949953421312 200000000441 882000000000000000 qz16 (Ns300p1067 rfl) rfl rfl 

noncomputable abbrev qz144 := qz449

noncomputable def Ns300p1069 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 626419 4000) qz697) qz144 2026591794096018456693 1125899906842624000 489390120000779 110250000000000000000 883830391604643 2251799813685248 200000000441 3528000000000000000 Ns300p1060 2026149878900216135193 1125899906842624000 220284497784249 49000000000000000000 (Ns300p1066 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1252838)))) 1 4 0 1 883830391604643 562949953421312 200000000441 882000000000000000 883830391604643 2251799813685248 200000000441 3528000000000000000 qz340 Ns300p1068 rfl) 

noncomputable def Ns300p1070 := @Ns300p1055 Ns300p1049 Ns300p1050 1839008050727018279 200704000000000000000000 (@Ns300p1057 1839008050727018279 200704000000000000000000 (Ns300p1059 (Ns300p1069 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 626419 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz698 (Real.log Real.pi) 626419 2000 0 1 38410761 33554432 1 67108864 24061230494859 67108864000 626419 134217728000 (Enclosure.Real.IsNear.const Bool.false 626419 2000) RS301to312.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns300p1051 Ns300p1052) 

noncomputable def Ns300p1071 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz138) Bool.false Ns300p1049 Ns300p1050 1839008050727018279 200704000000000000000000 9460945213 8388608 77 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz138) (@HAdd.hAdd Real Real Real qz341 qz450 (Enclosure.sfrac Bool.true Ns300p1051 Ns300p1052)) Bool.false Ns300p1049 Ns300p1050 1839008050727018279 200704000000000000000000 Ns300p1053 (Ns300p1070 rfl rfl)) 

noncomputable def Ns300p1072 := BSN.cos_dyadic_bound_f 54610121 68719476736 1 0 33554432 8828614 0 1 1 0 1 1 33554421 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 54610121) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 54610121) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns300p1073 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz138) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9460945213) qz383) Bool.false 9460945213 8388608 77 8388608 Bool.true 33554421 33554432 1 4410000 (Ns300p1071 rfl) (Enclosure.sfrac_false_div 9460945213 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9460945213) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 960711417795723657216) qz655) 226375608064910080 72057594037927936 Bool.false 33554421 33554432 179 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q2 9460945213 8388608 226375608064910080 72057594037927936 179 960711417795723657216 Ns300p381 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554421 33554432 960711417795723657216 Ns300p381 54610121 68719476736 8828614 8820000 (Ns300p1072 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p1074 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz138) Bool.false Ns300p1049 Ns300p1050 1839008050727018279 200704000000000000000000 302750246818 268435456 2460 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz138) (@HAdd.hAdd Real Real Real qz341 qz450 (Enclosure.sfrac Bool.true Ns300p1051 Ns300p1052)) Bool.false Ns300p1049 Ns300p1050 1839008050727018279 200704000000000000000000 Ns300p1053 (Ns300p1070 rfl rfl)) 

noncomputable def Ns300p1075 := Ns300p1048 54795 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 441 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 212070701 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 279 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 264001861 268435456) qz141 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 1) Bool.true 33554421 33554432 21747413 2312110080000 268435368 268435456 2525 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz138)) Bool.true 33554421 33554432 21747413 2312110080000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz138) qz138) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz138)) Bool.true 33554421 33554432 347958608 36993761280000 33554421 33554432 21747413 2312110080000 (Ns300p1073 rfl rfl) rfl)) rfl) (Ns300p1074 rfl) RS301to312.d7 

noncomputable def Ns300p1076 := nat_lit 56128889051298884068351873267885082567289069364161350493038078464057600 

noncomputable def Ns300p1077 := nat_lit 12772991028683950176640317072131894163295162707225632998648651407616 

noncomputable def Ns300p1078 := nat_lit 146983553148879208069207012331106050323778418071277552647387631494062336 

noncomputable def Ns300p1079 := BSN.sin_dyadic_bound_f 244504342 268435456 3 2 268435456 134217728 Ns300p1076 Ns300p116 Ns300p1077 Ns300p1078 Ns300p119 Ns300p1077 212070701 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 244504342) qz344 0 2 Ns300p1076 Ns300p116 Ns300p1077 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 244504342) qz345 0 2 Ns300p1078 Ns300p119 Ns300p1077 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1080 := nat_lit 27056103570146587610599832693206699257071329942231103548579350159644137224531575756268816872287576771155460096 

noncomputable def Ns300p1081 := nat_lit 7206747501955242843589417450079094621654206551921566712133841917228226917206152862936857521577206480896 

noncomputable def Ns300p1082 := nat_lit 135177737272159438978462842929165841797923025447105971442028338100274210637082858882201679856160554156195577856 

noncomputable def Ns300p1083 := BSN.sin_dyadic_bound_f 372802036 268435456 4 3 268435456 134217728 Ns300p1080 Ns300p237 Ns300p1081 Ns300p1082 Ns300p240 Ns300p1081 264001861 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 372802036) qz344 0 3 Ns300p1080 Ns300p237 Ns300p1081 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 372802036) qz345 0 3 Ns300p1082 Ns300p240 Ns300p1081 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1084 := nat_lit 20305447028665454915306826305536 

noncomputable def Ns300p1085 := BSN.sin_dyadic_bound_f 67127912 268435456 2 1 268435456 134217728 Ns300p1084 Ns300p392 Ns300p1084 Ns300p1084 Ns300p393 Ns300p1084 66430450 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 67127912) qz344 0 1 Ns300p1084 Ns300p392 Ns300p1084 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 67127912) qz345 0 1 Ns300p1084 Ns300p393 Ns300p1084 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1086 := nat_lit 27417540333229482756495875316241 

noncomputable def Ns300p1087 := BSN.cos_dyadic_bound_f 72361427 268435456 2 1 268435456 134217728 Ns300p1086 Ns300p133 Ns300p1086 Ns300p1086 Ns300p134 Ns300p1086 258741235 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 72361427) qz342 0 1 Ns300p1086 Ns300p133 Ns300p1086 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 72361427) qz343 0 1 Ns300p1086 Ns300p134 Ns300p1086 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1088 := Ns300p1046 93348 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 165 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66430450 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 76 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 258741235 268435456) qz141 rfl rfl (Ns300p1075 RS301to312.d9 RS301to312.d11 RS301to312.d13 RS301to312.d17 (Ns300p1079 rfl rfl) (Ns300p1083 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns300p1074 rfl) RS301to312.d19 RS301to312.d21 RS301to312.d23 RS301to312.d25 RS301to312.d17 (Ns300p1085 rfl rfl) (Ns300p1087 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns300p1089 := nat_lit 22904385364617507418067769406230453756291066790255693847247129037267200 

noncomputable def Ns300p1090 := nat_lit 2127521694229994893425375689820883175274756985672201153557098946816 

noncomputable def Ns300p1091 := nat_lit 59984231396017099436540516884248621265145206272692871750446245508833536 

noncomputable def Ns300p1092 := BSN.sin_dyadic_bound_f 195426858 268435456 3 2 268435456 134217728 Ns300p1089 Ns300p116 Ns300p1090 Ns300p1091 Ns300p119 Ns300p1090 178615398 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 195426858) qz344 0 2 Ns300p1089 Ns300p116 Ns300p1090 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 195426858) qz345 0 2 Ns300p1091 Ns300p119 Ns300p1090 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1093 := nat_lit 367212718577483945095555921 

noncomputable def Ns300p1094 := BSN.cos_dyadic_bound_f 4377533 268435456 2 1 268435456 134217728 Ns300p1093 Ns300p133 Ns300p1093 Ns300p1093 Ns300p134 Ns300p1093 268399763 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 4377533) qz342 0 1 Ns300p1093 Ns300p133 Ns300p1093 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 4377533) qz343 0 1 Ns300p1093 Ns300p134 Ns300p1093 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1095 := Ns300p1044 125837 BSN.abs_quadSignPos (BSN.cos_quad_nat3 3 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 178615398 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 58 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268399763 268435456) qz141 rfl rfl (Ns300p1088 rfl rfl) (Ns300p1074 rfl) RS301to312.d27 RS301to312.d29 RS301to312.d31 RS301to312.d33 RS301to312.d17 (Ns300p1092 rfl rfl) (Ns300p1094 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p1096 := nat_lit 147784614720885248700132828123136 

noncomputable def Ns300p1097 := BSN.sin_dyadic_bound_f 110257288 268435456 2 1 268435456 134217728 Ns300p1096 Ns300p392 Ns300p1096 Ns300p1096 Ns300p393 Ns300p1096 107183125 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 110257288) qz344 0 1 Ns300p1096 Ns300p392 Ns300p1096 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 110257288) qz345 0 1 Ns300p1096 Ns300p393 Ns300p1096 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1098 := nat_lit 802393515426265815901515030230504567999891620938510952409847950278656 

noncomputable def Ns300p1099 := nat_lit 8461124182040459880255162388657417603482614038670917904724197376 

noncomputable def Ns300p1100 := nat_lit 2407163624030433366784784580366736389164467897587455515393734402441216 

noncomputable def Ns300p1101 := BSN.cos_dyadic_bound_f 97932876 268435456 3 2 268435456 134217728 Ns300p1098 Ns300p110 Ns300p1099 Ns300p1100 Ns300p113 Ns300p1099 250768377 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 97932876) qz342 0 2 Ns300p1098 Ns300p110 Ns300p1099 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 97932876) qz343 0 2 Ns300p1100 Ns300p113 Ns300p1099 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1102 := Ns300p1042 154224 BSN.abs_quadSignPos (BSN.cos_quad_nat3 111 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 107183125 268435456) BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 250768377 268435456) qz141 rfl rfl (Ns300p1095 rfl) (Ns300p1074 rfl) RS301to312.d35 RS301to312.d37 RS301to312.d39 RS301to312.d41 RS301to312.d17 (Ns300p1097 rfl rfl) (Ns300p1101 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p1103 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 9) 257693724 268435456 154224 268435456 257693724 268435456 154224 268435456 138348264620556288 64423431 33554432 9639 8388608 (Ns300p1102 rfl) 

noncomputable def Ns300p1104 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz447) (Zeta.RiemannSiegel.correction qz140) 5309439 16777216 1 16777216 499939262760777 562949953421312 3796737511177283 155163080911749120000 2654397019333317074103 9444732965739290427392 

noncomputable def Ns300p1105 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz447 1 1 0 1 5309439 16777216 1 16777216 5309439 16777216 1 16777216 

noncomputable def Ns300p1106 := @Enclosure.Real.IsNear.sqrt_image qz139 3345298585907 33554432000 626419 33554432000 167518336 167518369 16777216 (@Enclosure.Real.IsNear.of_eq qz139 (@HMul.hMul Real Real Real qz5 qz138 qz3) Bool.false 3345298585907 33554432000 626419 33554432000 (BSN.t_div_two_pi_mk qz138 626419 1000 qz141) (@Enclosure.Real.IsNear.mulLit_ff qz138 qz3 626419 1000 0 1 5340353 33554432 1 33554432 3345298585907 33554432000 626419 33554432000 (Enclosure.Real.IsNear.const Bool.false 626419 1000) RS301to312.d44 rfl)) 

noncomputable abbrev qz845 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 626419 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz699 := qz845

noncomputable abbrev qz452 := qz699

noncomputable abbrev qz145 := qz452

noncomputable def Ns300p1107 := @Enclosure.Real.IsNear.sqrt_image qz145 335036705 33554432 33 33554432 53014067 53014073 16777216 (@Enclosure.Real.IsNear.recentre' qz145 Bool.false 335036705 33554432 33 33554432 335036705 33554432 33 33554432 (Ns300p1106 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns300p1108 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz145) 26507035 8388608 3 16777216 5309438 5309440 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz145) Bool.false 106028140 33554432 6 33554432 26507035 8388608 3 16777216 (Ns300p1107 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns300p1109 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz145)) Bool.false 10618878 33554432 2 33554432 5309439 16777216 1 16777216 (Ns300p1108 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz146 := (@HMul.hMul Real Real Real qz327 qz323 qz446)

noncomputable abbrev qz700 := (@HMul.hMul Real Real Real qz807 qz844 qz844)

noncomputable abbrev qz453 := (@HSub.hSub Real Real Real qz628 (@HSub.hSub Real Real Real qz628 qz700 qz696) qz639)

noncomputable abbrev qz147 := (Real.cos (@HMul.hMul Real Real Real qz327 qz323 qz453))

noncomputable def Ns300p1110 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz140) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz146)) qz147) Bool.false 499939262760777 

noncomputable def Ns300p1111 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz146)) qz147 33706589 33554432 219 

noncomputable def Ns300p1112 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz146)) Bool.false 33706589 33554432 219 33554432 33706589 33554432 219 

noncomputable def Ns300p1113 := @Enclosure.Real.IsNear.recentre' (Real.cos qz146) Bool.false 33402962 33554432 59427152 9248440320000 16701481 16777216 3714197 578027520000 

noncomputable def Ns300p1114 := @Enclosure.Real.IsNear.cos_image qz146 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 207639275) qz349) Bool.false 207639275 33554432 13 2097152 Bool.false 33402962 33554432 1 

noncomputable def Ns300p1115 := nat_lit 35621619551292939860974783 

noncomputable def Ns300p1116 := nat_lit 5764607523034234880000000000000 

noncomputable def Ns300p1117 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz140 884279719003555 140737488355328 1 500000000000000 33046817 33554432 33 33554432 29222630050721904434435 4722366482869645213696 Ns300p1115 

noncomputable def Ns300p1118 := @Enclosure.Real.IsNear.subLit_ff_p qz145 qz1 335036705 33554432 33 33554432 9 1 0 1 33046817 33046817 33554432 33 

noncomputable def Ns300p1119 := @Ns300p1118 33554432 (@Enclosure.Real.IsNear.recentre' qz145 Bool.false 335036705 33554432 33 33554432 335036705 33554432 33 33554432 (Ns300p1106 rfl rfl rfl rfl rfl rfl) rfl) qz350 

noncomputable def Ns300p1120 := @Enclosure.Real.IsNear.recentre' qz146 Bool.false 29222630050721904434435 4722366482869645213696 Ns300p1115 Ns300p1116 207639275 33554432 13 2097152 (@Ns300p1117 Ns300p1116 RS301to312.d43 (Ns300p1119 rfl rfl) rfl) 

noncomputable def Ns300p1121 := nat_lit 7136258326741327670149120 

noncomputable def Ns300p1122 := nat_lit 7144055718504697250041492241990478351569958369630718863492699943155851182004744070749670945 

noncomputable def Ns300p1123 := nat_lit 11187320952506896171332738803958484029774548099267780599958646468395414664642669149081121 

noncomputable def Ns300p1124 := nat_lit 18692509314541576870593179056673415279968351223538782521509519185411731948174432054293483041 

noncomputable def Ns300p1125 := BSN.sin_dyadic_bound_f 101412330291 68719476736 3 2 33554432 8828614 Ns300p1122 Ns300p170 Ns300p1123 Ns300p1124 Ns300p173 Ns300p1123 33402962 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 101412330291) qz351 0 2 Ns300p1122 Ns300p170 Ns300p1123 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 101412330291) qz352 0 2 Ns300p1124 Ns300p173 Ns300p1123 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1126 := @Ns300p1114 4410000 (Ns300p1120 rfl) (Enclosure.sfrac_false_div 207639275 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 207639275) qz349) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns300p1121) qz353) 226375608064910080 72057594037927936 Bool.false 33402962 33554432 0 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q3 207639275 33554432 226375608064910080 72057594037927936 0 Ns300p1121 Ns300p94 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33402962 33554432 Ns300p1121 Ns300p94 101412330291 68719476736 8828614 8820000 (Ns300p1125 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p1127 := @Enclosure.Real.IsNear.inv_image (Real.cos qz146) 16701481 16777216 3714197 578027520000 16853185 16853404 16777216 (Ns300p1113 (Ns300p1126 rfl rfl) rfl) rfl 

noncomputable def Ns300p1128 := @Enclosure.Real.IsNear.recentre' qz147 Bool.false 14832093 16777216 

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz327 qz323 qz453)

noncomputable def Ns300p1129 := @Enclosure.Real.IsNear.cos_image qz148 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16317983)) qz349) Bool.true 16317983 33554432 

noncomputable def Ns300p1130 := nat_lit 77059498681254968401453318045 

noncomputable def Ns300p1131 := nat_lit 88740666762150815295029438224447637 

noncomputable def Ns300p1132 := @Enclosure.Real.IsNear.recentre' qz148 Bool.true Ns300p1130 Ns300p564 Ns300p1131 

noncomputable abbrev qz149 := qz453

noncomputable def Ns300p1133 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz149 884279719003555 140737488355328 1 500000000000000 87143804189119 

noncomputable abbrev qz454 := (@HSub.hSub Real Real Real qz628 qz700 qz696)

noncomputable abbrev qz150 := qz454

noncomputable def Ns300p1134 := @Enclosure.Real.IsNear.subLit_tf qz150 qz27 16775060011455 1125899906842624 3288387267 1125899906842624 1 16 

noncomputable abbrev qz455 := qz700

noncomputable abbrev qz151 := qz455

noncomputable def Ns300p1135 := @Enclosure.Real.IsNear.subLit_ff_n qz151 qz140 1092092113831489 1125899906842624 2181091011 1125899906842624 33046817 33554432 33 33554432 

noncomputable def Ns300p1136 := @Enclosure.Real.IsNear.mulLit_ff qz140 qz140 33046817 33554432 33 33554432 33046817 33554432 33 33554432 1092092113831489 1125899906842624 

noncomputable def Ns300p1137 := nat_lit 151004264511664057617474345899339833443955175796761076202110721 

noncomputable def Ns300p1138 := nat_lit 5027265372466065671506436934721733304603317547014815645441 

noncomputable def Ns300p1139 := nat_lit 453002739004247240721080024824150056865256320755189198975041281 

noncomputable def Ns300p1140 := BSN.cos_dyadic_bound_f 16317983 33554432 3 2 16777216 4410000 Ns300p1137 Ns300p687 Ns300p1138 Ns300p1139 Ns300p690 Ns300p1138 14832093 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 16317983) (BSN.cosEvenQ 33554432) 0 2 Ns300p1137 Ns300p687 Ns300p1138 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 16317983) (BSN.cosOddQ 33554432) 0 2 Ns300p1139 Ns300p690 Ns300p1138 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1141 := @Ns300p1128 2754524432 147975045120000 14832093 16777216 172157777 9248440320000 (@Ns300p1129 617 33554432 Bool.false 14832093 16777216 1 4410000 (@Ns300p1132 Ns300p567 16317983 33554432 617 33554432 (@Ns300p1133 1125899906842624 3288387267 1125899906842624 Ns300p1130 Ns300p564 Ns300p1131 Ns300p567 RS301to312.d43 (@Ns300p1134 0 1 1394300867025904 87143804189119 1125899906842624 3288387267 1125899906842624 (@Ns300p1135 562877610450286018560 16775060011455 1125899906842624 3288387267 1125899906842624 (@Ns300p1136 2181091011 1125899906842624 (Ns300p1119 rfl rfl) (Ns300p1119 rfl rfl) rfl) (Ns300p1119 rfl rfl) rfl rfl) qz358 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16317983 33554432) (BSN.cos_neg_of_bound 16317983 33554432 Bool.false 14832093 16777216 1 4410000 (Ns300p1140 rfl rfl)) rfl rfl) 

noncomputable def Ns300p1142 := @Ns300p1104 4059269154128710522429 Ns300p1038 (Ns300p1105 qz29 (@Enclosure.Real.IsNear.of_eq qz447 (@Inv.inv Real Real.instInv (Real.sqrt qz145)) Bool.false 5309439 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz139 (BSN.t_div_two_pi_nonneg qz138 626419 1000 qz141)) Ns300p1109) rfl) (@Ns300p1110 562949953421312 3796737511177283 155163080911749120000 (BSN.correction_mk qz140 (BSN.cos_two_pi_p_ne_zero_mk qz138 626419 1000 9 qz141 rfl rfl (@BSN.floor_sqrt_eq_dec qz138 626419 1000 9 qz141 rfl rfl rfl))) (@Ns300p1111 33554432 14832093 16777216 172157777 9248440320000 499939262760777 562949953421312 3796737511177283 155163080911749120000 (@Ns300p1112 33554432 (Ns300p1127 rfl rfl rfl rfl rfl) rfl) (Ns300p1141 rfl) rfl)) 

noncomputable def Ns300p1143 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz138) (hardyZApproximantRS₀ qz138) Bool.true 15479186721012236706633 9444732965739290427392 602306043917468617594429 Ns300p1038 (@Eq.refl Real (hardyZApproximantRS₀ qz138)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz138) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz138) qz138 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz447) (Zeta.RiemannSiegel.correction qz140))) Bool.true 15479186721012236706633 9444732965739290427392 602306043917468617594429 Ns300p1038 (BSN.hardyZApproximantRS₀_eq qz138 9 (@BSN.floor_sqrt_eq_dec qz138 626419 1000 9 qz141 rfl rfl rfl)) (@Ns300p1040 15479186721012236706633 9444732965739290427392 602306043917468617594429 Ns300p1038 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz138) qz138 9) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 9)) Bool.true 64423431 33554432 9639 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz138) qz138 9) (Ns300p1103 (Ns300p1102 rfl) rfl rfl)) (Ns300p1142 rfl) rfl rfl)) 

theorem RS301to312.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz138) Bool.true 15479186721012236706633 9444732965739290427392 602306043917468617594429 Ns300p1038 := Ns300p1143 

noncomputable def Ns300p1144 := nat_lit 86773484122729730801664000 

noncomputable def Ns300p1145 := nat_lit 786261809353017591662502739968 

noncomputable abbrev qz846 := (Enclosure.sfrac Bool.false 627784 1000)

noncomputable abbrev qz701 := qz846

noncomputable abbrev qz456 := qz701

noncomputable abbrev qz152 := qz456

noncomputable abbrev qz847 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 627784 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz702 := qz847

noncomputable abbrev qz457 := qz702

noncomputable abbrev qz153 := qz457

noncomputable abbrev qz848 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 627784 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz703 := qz848

noncomputable abbrev qz458 := qz703

noncomputable abbrev qz154 := qz458

noncomputable abbrev qz459 := (@HPow.hPow Real Real Real qz627 qz153 qz8)

noncomputable def Ns300p1146 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz459) (Zeta.RiemannSiegel.correction qz154)) 127708997 134217728 154565 134217728 1364746111328285334077 4722366482869645213696 661994609465799688501 Ns300p1144 Ns300p1145 

noncomputable def Ns300p1147 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 627784 1000 111 158 268435456 134217728 4503599627370496 Bool.false 303593592117 2466 

noncomputable def Ns300p1148 := Ns300p1147 558195838 62 94906264 8 589812974 62 89478488 8 Bool.false 204804869 126116 Bool.true 28849308 Bool.true 59682286 14148475504056880 1 Bool.false 28793803 Bool.false Bool.false 261828045 Bool.true Bool.false 127708997 

noncomputable def Ns300p1149 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 627784 1000 3 57 268435456 134217728 4503599627370496 Bool.false 303593592117 2466 

noncomputable def Ns300p1150 := Ns300p1149 480971758 62 109588312 8 522351262 62 101459064 8 Bool.false 186888571 93556 Bool.false 382245707 Bool.true 295699135 14148475504056880 1 Bool.false 265547432 Bool.false Bool.false 239421931 Bool.true Bool.false 204804869 

noncomputable def Ns300p1151 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 627784 1000 165 76 268435456 134217728 4503599627370496 Bool.false 303593592117 2466 

noncomputable def Ns300p1152 := Ns300p1151 372130544 61 134217720 8 432030192 61 120047984 16 Bool.false 278879464 54918 Bool.false 402515018 Bool.false 325985514 14148475504056880 1 Bool.false 267753212 Bool.true Bool.false 93659285 Bool.false Bool.false 186888571 

noncomputable def Ns300p1153 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 627784 1000 442 280 268435456 134217728 4503599627370496 Bool.false 303593592117 2466 

noncomputable def Ns300p1154 := Ns300p1153 186065264 61 189812528 16 294906480 61 154981288 8 Bool.false 268435344 2533 Bool.false 412213128 Bool.false 391942562 14148475504056880 1 Bool.false 9442351 Bool.true Bool.false 29654217 Bool.false Bool.false 278879464 

noncomputable def Ns300p1155 := nat_lit 42819082690333749743617727560808748988070063146919083 

noncomputable def Ns300p1156 := nat_lit 37860351094043381605167851921524346392972099584000 

noncomputable def Ns300p1157 := nat_lit 46805097001076732420977242603520000 

noncomputable def Ns300p1158 := nat_lit 176300998283752154582961704216545198080 

noncomputable abbrev qz704 := (@Eq.refl Real qz846)

noncomputable abbrev qz460 := qz704

noncomputable abbrev qz155 := qz460

noncomputable def Ns300p1159 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz152 627784 1000 1576452002624 16000000 1255568 4000 2000 Ns300p1157 Ns300p1158 qz155 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns300p1160 := nat_lit 56123828063874252463954627868503243473643193167929780469760 

noncomputable abbrev qz461 := (@HMul.hMul Real Real Real qz623 qz629 (@HSub.hSub Real Real Real qz628 qz630 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz631 (@Nat.cast Real Real.instNatCast 1255568)))))

noncomputable abbrev qz705 := (Real.log (Enclosure.sfrac Bool.false 1576452002624 16000000))

noncomputable abbrev qz706 := (Enclosure.sfrac Bool.false 627784 2000)

noncomputable abbrev qz156 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 627784 4000) qz705) qz461) qz706)

noncomputable abbrev qz462 := (@HSub.hSub Real Real Real qz11 qz156 (@HMul.hMul Real Real Real qz5 qz706 (Real.log Real.pi)))

noncomputable def Ns300p1161 := @Enclosure.Real.IsNear.addLit_ft_p qz462 (Enclosure.sfrac Bool.true Ns300p1157 Ns300p1158) 318341029175614127047 281474976710656000 691121457513407279 75264000000000000000000 Ns300p1157 Ns300p1158 0 1 Ns300p1160 

noncomputable def Ns300p1162 := nat_lit 2670438104070790071059480576000 

noncomputable abbrev qz463 := (@HMul.hMul Real Real Real qz5 qz706 (Real.log Real.pi))

noncomputable def Ns300p1163 := @Enclosure.Real.IsNear.subLit_ff_p qz156 qz463 419481054732733004743 281474976710656000 662275369155367 147000000000000000000 3014207647953 8388608000 78473 16777216000 Ns300p1162 318341029175614127047 281474976710656000 

noncomputable abbrev qz157 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 627784 4000) qz705) qz461)

noncomputable def Ns300p1164 := @Enclosure.Real.IsNear.subLit_ff_p qz157 qz706 101566759624478847579 56294995342131200 662275369155367 147000000000000000000 627784 2000 0 1 167792421893093201897200 419481054732733004743 281474976710656000 662275369155367 147000000000000000000 

noncomputable def Ns300p1165 := nat_lit 114354005199507919050001292036407296 

noncomputable def Ns300p1166 := nat_lit 55601393041937000384430080 

noncomputable def Ns300p1167 := nat_lit 161496792027331964328068147269130693473846058957514004427626264505277059332079160017392842183766920591892269357972538659459563520 

noncomputable def Ns300p1168 := nat_lit 2231294305294401272131710237140156553318977563391879626053302570816271823566098344539866121906753925696878172941790600709013504 

noncomputable def Ns300p1169 := nat_lit 1587636232392243072033237081325730814559461369140947633093728001525640797164463812230308816041329145250833794037259960320 

noncomputable def Ns300p1170 := BSN.log_dyadic_bound 527876002624 2625028002624 6 5 Ns300p1167 134217728 35280000 Ns300p1168 Ns300p1169 54726433 3152904005248 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 527876002624) (BSN.artanhQ 2625028002624) 0 5 Ns300p1168 Ns300p1167 Ns300p1169 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns300p1171 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 627784 4000) qz705 627784 4000 0 1 3236427032501495 281474976710656 781250441 27562500000000000 50794427704297963427 28147497671065600 61307065856593 13781250000000000000 (Enclosure.Real.IsNear.const Bool.false 627784 4000) (BSN.isNear_log_sfrac 1576452002624 16000000 3236427032501495 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1576452002624) qz335)) Bool.false Ns300p1166 Ns300p94 1000000564480000 35280000000000000000000 3236427032501495 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1576452002624 16000000 16 3152904005248 2097152000000 54726433 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns300p1170 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns300p1172 := BSN.arctan_dyadic_bound_f 1000 1255568 1 0 16777216 4410000 0 1 1 0 1 1 13362 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1255568) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1255568) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns300p1173 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1255568))) 884279719003555 562949953421312 1 2000000000000000 13362 16777216 1 4410000 14828229712864331431936 883831364683171 562949953421312 200000000441 882000000000000000 qz16 (Ns300p1172 rfl) rfl rfl 

noncomputable abbrev qz158 := qz461

noncomputable def Ns300p1174 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 627784 4000) qz705) qz158 50794427704297963427 28147497671065600 61307065856593 13781250000000000000 883831364683171 2251799813685248 200000000441 3528000000000000000 Ns300p1165 101566759624478847579 56294995342131200 662275369155367 147000000000000000000 (Ns300p1171 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1255568)))) 1 4 0 1 883831364683171 562949953421312 200000000441 882000000000000000 883831364683171 2251799813685248 200000000441 3528000000000000000 qz340 Ns300p1173 rfl) 

noncomputable def Ns300p1175 := @Ns300p1161 Ns300p1155 Ns300p1156 691121457513407279 75264000000000000000000 (@Ns300p1163 691121457513407279 75264000000000000000000 (Ns300p1164 (Ns300p1174 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 627784 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz706 (Real.log Real.pi) 627784 2000 0 1 38410761 33554432 1 67108864 3014207647953 8388608000 78473 16777216000 (Enclosure.Real.IsNear.const Bool.false 627784 2000) RS301to312.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns300p1157 Ns300p1158) 

noncomputable def Ns300p1176 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns300p1155 Ns300p1156 691121457513407279 75264000000000000000000 18974599507 16777216 309 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz341 qz462 (Enclosure.sfrac Bool.true Ns300p1157 Ns300p1158)) Bool.false Ns300p1155 Ns300p1156 691121457513407279 75264000000000000000000 Ns300p1159 (Ns300p1175 rfl rfl)) 

noncomputable def Ns300p1177 := BSN.cos_dyadic_bound_f 62402625 68719476736 1 0 33554432 8828614 0 1 1 0 1 1 33554418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 62402625) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 62402625) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns300p1178 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz152) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18974599507) qz354) Bool.false 18974599507 16777216 309 33554432 Bool.false 33554418 33554432 1 4410000 (Ns300p1176 rfl) (Enclosure.sfrac_false_div 18974599507 16777216) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18974599507) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2195597183435883413504) qz645) 226375608064910080 72057594037927936 Bool.false 33554418 33554432 180 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q0 18974599507 16777216 226375608064910080 72057594037927936 180 2195597183435883413504 Ns300p231 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554418 33554432 2195597183435883413504 Ns300p231 62402625 68719476736 8828614 8820000 (Ns300p1177 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p1179 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns300p1155 Ns300p1156 691121457513407279 75264000000000000000000 303593592117 268435456 2466 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz341 qz462 (Enclosure.sfrac Bool.true Ns300p1157 Ns300p1158)) Bool.false Ns300p1155 Ns300p1156 691121457513407279 75264000000000000000000 Ns300p1159 (Ns300p1175 rfl rfl)) 

noncomputable def Ns300p1180 := Ns300p1154 54918 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 442 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 9442351 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 280 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 29654217 268435456) qz155 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) Bool.false 16777209 16777216 87265277 9248440320000 268435344 268435456 2533 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 16777209 16777216 87265277 9248440320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz152) qz152) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 33554418 33554432 1396244432 147975045120000 16777209 16777216 87265277 9248440320000 (Ns300p1178 rfl rfl) rfl)) rfl) (Ns300p1179 rfl) RS301to312.d7 

noncomputable def Ns300p1181 := nat_lit 15587189194636104010912213401880304149003134414700663351717679487653404793733443364080874990176577554529386496 

noncomputable def Ns300p1182 := nat_lit 24069209486308570488934881934922348505745602227838393444933390760232948325426634585193437339198282530816 

noncomputable def Ns300p1183 := nat_lit 94354185002717131797385017766363427673263585402209965016512356100515870604637428374693607223417168874459627520 

noncomputable def Ns300p1184 := BSN.cos_dyadic_bound_f 412213128 268435456 4 3 268435456 134217728 Ns300p1181 Ns300p122 Ns300p1182 Ns300p1183 Ns300p125 Ns300p1182 9442351 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 412213128) qz342 0 3 Ns300p1181 Ns300p122 Ns300p1182 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 412213128) qz343 0 3 Ns300p1183 Ns300p125 Ns300p1182 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1185 := nat_lit 12732340171739687626767207253872617993629263738963281700372500342717411126762882505800038665283400779467329536 

noncomputable def Ns300p1186 := nat_lit 13142231882583625405501847682284344346928775765462683161899278696979208545091592750662682388861869101056 

noncomputable def Ns300p1187 := nat_lit 77103861295584580268867522370816039764581502202087532613789437680187829144343303223060351030545964966711398400 

noncomputable def Ns300p1188 := BSN.cos_dyadic_bound_f 391942562 268435456 4 3 268435456 134217728 Ns300p1185 Ns300p122 Ns300p1186 Ns300p1187 Ns300p125 Ns300p1186 29654217 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 391942562) qz342 0 3 Ns300p1185 Ns300p122 Ns300p1186 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 391942562) qz343 0 3 Ns300p1187 Ns300p125 Ns300p1186 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1189 := nat_lit 36785115102461699108151070381981632414646754500089150634998541261151109478483911528766130773601965680768126976 

noncomputable def Ns300p1190 := nat_lit 18087771563902556914680524009455425810015038676375318444383837001363249746830480689161095105502603186176 

noncomputable def Ns300p1191 := nat_lit 183735736577420125384831286734308680846592102147492085927337719000430743289188474337068975162655385693714190336 

noncomputable def Ns300p1192 := BSN.sin_dyadic_bound_f 402515018 268435456 4 3 268435456 134217728 Ns300p1189 Ns300p237 Ns300p1190 Ns300p1191 Ns300p240 Ns300p1190 267753212 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 402515018) qz344 0 3 Ns300p1189 Ns300p237 Ns300p1190 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 402515018) qz345 0 3 Ns300p1191 Ns300p240 Ns300p1190 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1193 := nat_lit 6084150094909709026477914389050960272253089022284675820785886194721129788512112391999848243064058376310296576 

noncomputable def Ns300p1194 := nat_lit 1440056786295464833665605439889126331104392796857699143766917575359006469204050295846331835150422839296 

noncomputable def Ns300p1195 := nat_lit 36878689062329242468515941568241833417789082113288681402472980380101350733300424285142405349121495175696814080 

noncomputable def Ns300p1196 := BSN.cos_dyadic_bound_f 325985514 268435456 4 3 268435456 134217728 Ns300p1193 Ns300p122 Ns300p1194 Ns300p1195 Ns300p125 Ns300p1194 93659285 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 325985514) qz342 0 3 Ns300p1193 Ns300p122 Ns300p1194 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 325985514) qz343 0 3 Ns300p1195 Ns300p125 Ns300p1194 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1197 := Ns300p1152 93556 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 165 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267753212 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 76 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 93659285 268435456) qz155 rfl rfl (Ns300p1180 RS301to312.d9 RS301to312.d11 RS301to312.d13 RS301to312.d17 (Ns300p1184 rfl rfl) (Ns300p1188 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns300p1179 rfl) RS301to312.d19 RS301to312.d21 RS301to312.d23 RS301to312.d25 RS301to312.d17 (Ns300p1192 rfl rfl) (Ns300p1196 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns300p1198 := nat_lit 29907409468113676184507299903942900485737959083908275055279922304321766661352575103138301299203684384146701201 

noncomputable def Ns300p1199 := nat_lit 9729967701277554928227781377973655613651567064253713254859086274427559664066853711880288957649107008401 

noncomputable def Ns300p1200 := nat_lit 149411491012721788193173513339525832120148291473617793136325876979447978597118372458825521358379520796542876561 

noncomputable def Ns300p1201 := BSN.sin_dyadic_bound_f 382245707 268435456 4 3 268435456 134217728 Ns300p1198 Ns300p237 Ns300p1199 Ns300p1200 Ns300p240 Ns300p1199 265547432 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 382245707) qz344 0 3 Ns300p1198 Ns300p237 Ns300p1199 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 382245707) qz345 0 3 Ns300p1200 Ns300p240 Ns300p1199 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1202 := nat_lit 120102744978766094185821805503419523832430353619204923060225530051930625 

noncomputable def Ns300p1203 := nat_lit 58452142285859704792530637788781001596869200943072959659160812890625 

noncomputable def Ns300p1204 := nat_lit 314460171475924569059869202904916916987113137915438394651618699296090625 

noncomputable def Ns300p1205 := BSN.sin_dyadic_bound_f 295699135 268435456 3 2 268435456 134217728 Ns300p1202 Ns300p116 Ns300p1203 Ns300p1204 Ns300p119 Ns300p1203 239421931 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 295699135) qz344 0 2 Ns300p1202 Ns300p116 Ns300p1203 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 295699135) qz345 0 2 Ns300p1204 Ns300p119 Ns300p1203 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1206 := Ns300p1150 126116 BSN.abs_quadSignPos (BSN.cos_quad_nat3 3 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 265547432 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 239421931 268435456) qz155 rfl rfl (Ns300p1197 rfl rfl) (Ns300p1179 rfl) RS301to312.d27 RS301to312.d29 RS301to312.d31 RS301to312.d33 RS301to312.d17 (Ns300p1201 rfl rfl) (Ns300p1205 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p1207 := nat_lit 692694279786209449522635530496 

noncomputable def Ns300p1208 := BSN.sin_dyadic_bound_f 28849308 268435456 2 1 268435456 134217728 Ns300p1207 Ns300p392 Ns300p1207 Ns300p1207 Ns300p393 Ns300p1207 28793803 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 28849308) qz344 0 1 Ns300p1207 Ns300p392 Ns300p1207 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 28849308) qz345 0 1 Ns300p1207 Ns300p393 Ns300p1207 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1209 := nat_lit 12687667768423570155591624153616 

noncomputable def Ns300p1210 := BSN.cos_dyadic_bound_f 59682286 268435456 2 1 268435456 134217728 Ns300p1209 Ns300p133 Ns300p1209 Ns300p1209 Ns300p134 Ns300p1209 261828045 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 59682286) qz342 0 1 Ns300p1209 Ns300p133 Ns300p1209 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 59682286) qz343 0 1 Ns300p1209 Ns300p134 Ns300p1209 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1211 := Ns300p1148 154565 BSN.abs_quadSignPos (BSN.cos_quad_nat3 111 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 28793803 268435456) BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 261828045 268435456) qz155 rfl rfl (Ns300p1206 rfl) (Ns300p1179 rfl) RS301to312.d35 RS301to312.d37 RS301to312.d39 RS301to312.d41 RS301to312.d17 (Ns300p1208 rfl rfl) (Ns300p1210 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p1212 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) 127708997 268435456 154565 268435456 127708997 268435456 154565 268435456 68563245689995264 127708997 134217728 154565 134217728 (Ns300p1211 rfl) 

noncomputable def Ns300p1213 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz459) (Zeta.RiemannSiegel.correction qz154) 5306551 16777216 1 16777216 257181380397227 281474976710656 123859881444863 5172102697058304000 1364746111328285334077 4722366482869645213696 

noncomputable def Ns300p1214 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz459 1 1 0 1 5306551 16777216 1 16777216 5306551 16777216 1 16777216 

noncomputable def Ns300p1215 := @Enclosure.Real.IsNear.sqrt_image qz153 419073520969 4194304000 78473 4194304000 167700753 167700785 16777216 (@Enclosure.Real.IsNear.of_eq qz153 (@HMul.hMul Real Real Real qz5 qz152 qz3) Bool.false 419073520969 4194304000 78473 4194304000 (BSN.t_div_two_pi_mk qz152 627784 1000 qz155) (@Enclosure.Real.IsNear.mulLit_ff qz152 qz3 627784 1000 0 1 5340353 33554432 1 33554432 419073520969 4194304000 78473 4194304000 (Enclosure.Real.IsNear.const Bool.false 627784 1000) RS301to312.d44 rfl)) 

noncomputable abbrev qz849 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 627784 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz707 := qz849

noncomputable abbrev qz464 := qz707

noncomputable abbrev qz159 := qz464

noncomputable def Ns300p1216 := @Enclosure.Real.IsNear.sqrt_image qz159 167700769 16777216 1 1048576 53042923 53042929 16777216 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 335401538 33554432 32 33554432 167700769 16777216 1 1048576 (Ns300p1215 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns300p1217 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz159) 26521463 8388608 3 16777216 5306550 5306552 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz159) Bool.false 106085852 33554432 6 33554432 26521463 8388608 3 16777216 (Ns300p1216 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns300p1218 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz159)) Bool.false 10613102 33554432 2 33554432 5306551 16777216 1 16777216 (Ns300p1217 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz327 qz323 qz458)

noncomputable abbrev qz708 := (@HMul.hMul Real Real Real qz807 qz848 qz848)

noncomputable abbrev qz465 := (@HSub.hSub Real Real Real qz628 (@HSub.hSub Real Real Real qz628 qz708 qz703) qz639)

noncomputable abbrev qz161 := (Real.cos (@HMul.hMul Real Real Real qz327 qz323 qz465))

noncomputable def Ns300p1219 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz154) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz160)) qz161) Bool.false 257181380397227 

noncomputable def Ns300p1220 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz160)) qz161 33566429 33554432 211 

noncomputable def Ns300p1221 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz160)) Bool.false 33566429 33554432 211 33554432 33566429 33554432 211 

noncomputable def Ns300p1222 := @Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.false 33542439 33554432 462187216 73987522560000 33542439 33554432 28886701 4624220160000 

noncomputable def Ns300p1223 := @Enclosure.Real.IsNear.cos_image qz160 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 52482897) qz383) Bool.false 52482897 8388608 101 16777216 Bool.false 33542439 33554432 1 

noncomputable def Ns300p1224 := nat_lit 26986075418012916958631367 

noncomputable def Ns300p1225 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz154 884279719003555 140737488355328 1 500000000000000 16705825 16777216 1 1048576 14772622236722564207875 2361183241434822606848 Ns300p1224 

noncomputable def Ns300p1226 := @Enclosure.Real.IsNear.subLit_ff_p qz159 qz1 167700769 16777216 1 1048576 9 1 0 1 16705825 16705825 16777216 1 

noncomputable def Ns300p1227 := @Ns300p1226 1048576 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 335401538 33554432 32 33554432 167700769 16777216 1 1048576 (Ns300p1215 rfl rfl rfl rfl rfl rfl) rfl) qz350 

noncomputable def Ns300p1228 := @Enclosure.Real.IsNear.recentre' qz160 Bool.false 14772622236722564207875 2361183241434822606848 Ns300p1224 Ns300p163 52482897 8388608 101 16777216 (@Ns300p1225 Ns300p163 RS301to312.d43 (Ns300p1227 rfl rfl) rfl) 

noncomputable def Ns300p1229 := nat_lit 1866653861466264267915264 

noncomputable def Ns300p1230 := nat_lit 3277400970680480402803843127620300908475471026653841511993133303129424336430390604015958272936474732609022019245759851879321256944000040625 

noncomputable def Ns300p1231 := nat_lit 2036703482395873288811098169919607371194432238549641111595149282589394529433603405559259806807440071537942000368256373663398681640625 

noncomputable def Ns300p1232 := nat_lit 16367991405175517420702057897548839212989988151344787961928171481735246285928248214629966957024558990609858155566520925559517722901273640625 

noncomputable def Ns300p1233 := BSN.sin_dyadic_bound_f 106106987315 68719476736 4 3 33554432 8828614 Ns300p1230 Ns300p383 Ns300p1231 Ns300p1232 Ns300p386 Ns300p1231 33542439 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 106106987315) qz351 0 3 Ns300p1230 Ns300p383 Ns300p1231 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 106106987315) qz352 0 3 Ns300p1232 Ns300p386 Ns300p1231 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1234 := @Ns300p1223 4410000 (Ns300p1228 rfl) (Enclosure.sfrac_false_div 52482897 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 52482897) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns300p1229) qz655) 226375608064910080 72057594037927936 Bool.false 33542439 33554432 0 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q3 52482897 8388608 226375608064910080 72057594037927936 0 Ns300p1229 Ns300p381 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33542439 33554432 Ns300p1229 Ns300p381 106106987315 68719476736 8828614 8820000 (Ns300p1233 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p1235 := @Enclosure.Real.IsNear.inv_image (Real.cos qz160) 33542439 33554432 28886701 4624220160000 16783109 16783320 16777216 (Ns300p1222 (Ns300p1234 rfl rfl) rfl) rfl 

noncomputable def Ns300p1236 := @Enclosure.Real.IsNear.recentre' qz161 Bool.false 15323726 16777216 

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz327 qz323 qz465)

noncomputable def Ns300p1237 := @Enclosure.Real.IsNear.cos_image qz162 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7035051)) qz354) Bool.true 7035051 16777216 

noncomputable def Ns300p1238 := nat_lit 16611045606116302801856303005 

noncomputable def Ns300p1239 := nat_lit 677200477178849179911677274725343 

noncomputable def Ns300p1240 := @Enclosure.Real.IsNear.recentre' qz162 Bool.true Ns300p1238 Ns300p180 Ns300p1239 

noncomputable def Ns300p1241 := nat_lit 37778931862957161709568000000000000000 

noncomputable abbrev qz163 := qz465

noncomputable def Ns300p1242 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz163 884279719003555 140737488355328 1 500000000000000 18784831596991 

noncomputable abbrev qz466 := (@HSub.hSub Real Real Real qz628 qz708 qz703)

noncomputable abbrev qz164 := qz466

noncomputable def Ns300p1243 := @Enclosure.Real.IsNear.subLit_tf qz164 qz27 1192645552575 281474976710656 25094441 8796093022208 1 16 

noncomputable abbrev qz467 := qz708

noncomputable abbrev qz165 := qz467

noncomputable def Ns300p1244 := @Enclosure.Real.IsNear.subLit_ff_n qz165 qz154 279084588930625 281474976710656 16705833 8796093022208 16705825 16777216 1 1048576 

noncomputable def Ns300p1245 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz154 16705825 16777216 1 1048576 16705825 16777216 1 1048576 279084588930625 281474976710656 

noncomputable def Ns300p1246 := nat_lit 2449452379609635290155905201 

noncomputable def Ns300p1247 := nat_lit 1901475900342344102245054808064 

noncomputable def Ns300p1248 := nat_lit 28522138505135161533675822120960 

noncomputable def Ns300p1249 := BSN.cos_dyadic_bound_f 7035051 16777216 2 1 16777216 4410000 Ns300p1246 Ns300p1247 Ns300p1246 Ns300p1246 Ns300p1248 Ns300p1246 15323726 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 7035051) (BSN.cosEvenQ 16777216) 0 1 Ns300p1246 Ns300p1247 Ns300p1246 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 7035051) (BSN.cosOddQ 16777216) 0 1 Ns300p1246 Ns300p1248 Ns300p1246 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1250 := @Ns300p1236 2692784432 147975045120000 7661863 8388608 168299027 9248440320000 (@Ns300p1237 603 33554432 Bool.false 15323726 16777216 1 4410000 (@Ns300p1240 Ns300p1241 7035051 16777216 603 33554432 (@Ns300p1242 281474976710656 25094441 8796093022208 Ns300p1238 Ns300p180 Ns300p1239 Ns300p1241 RS301to312.d43 (@Ns300p1243 0 1 300557305551856 18784831596991 281474976710656 25094441 8796093022208 (@Ns300p1244 20009272046990131200 1192645552575 281474976710656 25094441 8796093022208 (@Ns300p1245 16705833 8796093022208 (Ns300p1227 rfl rfl) (Ns300p1227 rfl rfl) rfl) (Ns300p1227 rfl rfl) rfl rfl) qz358 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7035051 16777216) (BSN.cos_neg_of_bound 7035051 16777216 Bool.false 15323726 16777216 1 4410000 (Ns300p1249 rfl rfl)) rfl rfl) 

noncomputable def Ns300p1251 := @Ns300p1213 661994609465799688501 Ns300p1144 (Ns300p1214 qz29 (@Enclosure.Real.IsNear.of_eq qz459 (@Inv.inv Real Real.instInv (Real.sqrt qz159)) Bool.false 5306551 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz153 (BSN.t_div_two_pi_nonneg qz152 627784 1000 qz155)) Ns300p1218) rfl) (@Ns300p1219 281474976710656 123859881444863 5172102697058304000 (BSN.correction_mk qz154 (BSN.cos_two_pi_p_ne_zero_mk qz152 627784 1000 9 qz155 rfl rfl (@BSN.floor_sqrt_eq_dec qz152 627784 1000 9 qz155 rfl rfl rfl))) (@Ns300p1220 33554432 7661863 8388608 168299027 9248440320000 257181380397227 281474976710656 123859881444863 5172102697058304000 (@Ns300p1221 33554432 (Ns300p1235 rfl rfl rfl rfl rfl) rfl) (Ns300p1250 rfl) rfl)) 

noncomputable def Ns300p1252 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (hardyZApproximantRS₀ qz152) Bool.false 5858106980867814955581 4722366482869645213696 100590251280817894408501 Ns300p1144 (@Eq.refl Real (hardyZApproximantRS₀ qz152)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz459) (Zeta.RiemannSiegel.correction qz154))) Bool.false 5858106980867814955581 4722366482869645213696 100590251280817894408501 Ns300p1144 (BSN.hardyZApproximantRS₀_eq qz152 9 (@BSN.floor_sqrt_eq_dec qz152 627784 1000 9 qz155 rfl rfl rfl)) (@Ns300p1146 5858106980867814955581 4722366482869645213696 100590251280817894408501 Ns300p1144 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 9)) Bool.false 127708997 134217728 154565 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (Ns300p1212 (Ns300p1211 rfl) rfl rfl)) (Ns300p1251 rfl) rfl rfl)) 

theorem RS301to312.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz152) Bool.false 5858106980867814955581 4722366482869645213696 100590251280817894408501 Ns300p1144 := Ns300p1252 

noncomputable def Ns300p1253 := nat_lit 1391827265235416537628672 

noncomputable def Ns300p1254 := BSN.log_dyadic_bound 2 18 4 3 3571283520 16777216 4410000 14806464 960 3743727 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 18) 0 3 14806464 3571283520 960 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz850 := (Enclosure.sfrac Bool.false 10 1)

noncomputable abbrev qz709 := qz850

noncomputable abbrev qz468 := qz709

noncomputable abbrev qz166 := qz468

noncomputable abbrev qz710 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10) qz318)

theorem RS301to312.d57 : Enclosure.Real.IsNear (Real.log qz166) Bool.false 10369921216632549 4503599627370496 100000001323 441000000000000000 := BSN.isNear_log_sfrac 10 1 10369921216632549 4503599627370496 100000001323 441000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz710) Bool.false Ns300p1253 604462909807314587353088 1000000013230000 4410000000000000000000 10369921216632549 4503599627370496 100000001323 441000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 3743727 16777216 24973259072661432 36028797018963968 4410000 1000000000000000 rfl rfl rfl rfl (Ns300p1254 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS301to312.d58 : Enclosure.Real.IsNear (Real.log qz166) Bool.false 618095470 268435456 62 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz166) Bool.false 10369921216632549 4503599627370496 100000001323 441000000000000000 618095470 268435456 62 268435456 RS301to312.d57 rfl 

noncomputable abbrev qz711 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10))

noncomputable def Ns300p1255 := @Enclosure.Real.IsNear.inv_image qz711 106108431 33554432 1 33554432 5305421 5305422 16777216 (@Enclosure.Real.IsNear.of_eq qz711 (Real.sqrt qz710) Bool.false 106108431 33554432 1 33554432 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz710) Bool.false 106108431 33554432 1 33554432 106108431 33554432 1 33554432 (BSN.sqrt_enclosure 10 1 53054215 53054216 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz712 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

theorem RS301to312.d59 : Enclosure.Real.IsNear qz712 Bool.false 10610843 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz712 Bool.false 10610843 33554432 1 33554432 10610843 33554432 1 33554432 (Ns300p1255 rfl rfl) rfl 

theorem RS301to312.d60 : Enclosure.Real.IsNear qz712 Bool.false 84886744 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz712 Bool.false 10610843 33554432 1 33554432 84886744 268435456 8 268435456 RS301to312.d59 rfl 

noncomputable def Ns300p1256 := nat_lit 491726505491473235291207106560 

noncomputable abbrev qz851 := (Enclosure.sfrac Bool.false 629148 1000)

noncomputable abbrev qz713 := qz851

noncomputable abbrev qz469 := qz713

noncomputable abbrev qz167 := qz469

noncomputable abbrev qz470 := qz627

noncomputable abbrev qz852 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 629148 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz714 := qz852

noncomputable abbrev qz471 := qz714

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz327 (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 10) (@HPow.hPow Real Real Real qz470 qz471 qz625))

noncomputable abbrev qz853 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 629148 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz715 := qz853

noncomputable abbrev qz472 := (Zeta.RiemannSiegel.correction qz715)

noncomputable abbrev qz169 := qz472

noncomputable def Ns300p1257 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz167) qz167 10) (@HMul.hMul Real Real Real qz5 qz168 qz169) 377977535 134217728 42005 33554432 338922402643048608615 1180591620717411303424 71776926356280872893 Ns300p579 Ns300p1256 

noncomputable def Ns300p1258 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz167) qz167 Real.cos BSN.quadSignPos 9 10 629148 1000 200 268435456 134217728 4503599627370496 Bool.false 304436717097 2471 618095470 62 84886744 8 

noncomputable def Ns300p1259 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz167) qz167 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 629148 1000 110 158 268435456 134217728 4503599627370496 Bool.false 304436717097 2471 

noncomputable def Ns300p1260 := Ns300p1259 558195838 62 94906264 8 589812974 62 89478488 8 Bool.true 348629196 126383 Bool.true 368760879 Bool.true 21062203 14148475504056880 1 Bool.false 52554878 Bool.true Bool.false 267609579 Bool.true Bool.true 456413347 

noncomputable def Ns300p1261 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz167) qz167 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 629148 1000 4 57 268435456 134217728 4503599627370496 Bool.false 304436717097 2471 

noncomputable def Ns300p1262 := Ns300p1261 480971758 62 109588312 8 522351262 62 101459064 8 Bool.true 383520402 93752 Bool.false 147667781 Bool.true 165061276 14148475504056880 1 Bool.false 228833025 Bool.false Bool.false 154854454 Bool.true Bool.true 348629196 

noncomputable def Ns300p1263 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz167) qz167 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 629148 1000 166 77 268435456 134217728 4503599627370496 Bool.false 304436717097 2471 

noncomputable def Ns300p1264 := Ns300p1263 372130544 61 134217720 8 432030192 61 120047984 16 Bool.true 265517559 55031 Bool.false 316396508 Bool.false 158163884 14148475504056880 1 Bool.false 102584027 Bool.true Bool.false 149169958 Bool.true Bool.true 383520402 

noncomputable def Ns300p1265 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz167) qz167 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 629148 1000 444 281 268435456 134217728 4503599627370496 Bool.false 304436717097 2471 

noncomputable def Ns300p1266 := Ns300p1265 186065264 61 189812528 16 294906480 61 154981288 8 Bool.true 268435448 2533 Bool.false 158230231 Bool.false 411157675 14148475504056880 1 Bool.false 223135518 Bool.false Bool.false 268230135 Bool.true Bool.true 265517559 

noncomputable def Ns300p1267 := nat_lit 302088893041579929809634103611938105108615910957593 

noncomputable def Ns300p1268 := nat_lit 266365274627190866689474353753630933614854144000 

noncomputable def Ns300p1269 := nat_lit 47315783294865229527568383344640000 

noncomputable def Ns300p1270 := nat_lit 178611835214847162381207137091657400320 

noncomputable abbrev qz854 := (@Eq.refl Real (Enclosure.sfrac Bool.false 629148 1000))

noncomputable abbrev qz716 := qz854

noncomputable abbrev qz473 := qz716

noncomputable abbrev qz170 := qz473

noncomputable def Ns300p1271 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz167 629148 1000 1583309823616 16000000 1258296 4000 2000 Ns300p1269 Ns300p1270 qz170 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns300p1272 := nat_lit 28508684679897094483206020084609244945213483370344213381120 

noncomputable abbrev qz474 := (@HMul.hMul Real Real Real qz623 qz629 (@HSub.hSub Real Real Real qz628 qz630 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz631 (@Nat.cast Real Real.instNatCast 1258296)))))

noncomputable abbrev qz717 := (Real.log (Enclosure.sfrac Bool.false 1583309823616 16000000))

noncomputable abbrev qz718 := (Enclosure.sfrac Bool.false 629148 2000)

noncomputable abbrev qz171 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 629148 4000) qz717) qz474) qz718)

noncomputable abbrev qz475 := (@HSub.hSub Real Real Real qz11 qz171 (@HMul.hMul Real Real Real qz5 qz718 (Real.log Real.pi)))

noncomputable def Ns300p1273 := @Enclosure.Real.IsNear.addLit_ft_p qz475 (Enclosure.sfrac Bool.true Ns300p1269 Ns300p1270) 159612554815918499941 140737488355328000 4155682811460301603 451584000000000000000000 Ns300p1269 Ns300p1270 0 1 Ns300p1272 

noncomputable def Ns300p1274 := nat_lit 2677854308458504911906144256000 

noncomputable abbrev qz476 := (@HMul.hMul Real Real Real qz5 qz718 (Real.log Real.pi))

noncomputable def Ns300p1275 := @Enclosure.Real.IsNear.subLit_ff_p qz171 qz476 210292442165078583397 140737488355328000 1991088609872197 441000000000000000000 6041513365407 16777216000 157287 33554432000 Ns300p1274 159612554815918499941 140737488355328000 

noncomputable abbrev qz172 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 629148 4000) qz717) qz474)

noncomputable def Ns300p1276 := @Enclosure.Real.IsNear.subLit_ff_p qz172 qz718 254564796826967533669 140737488355328000 1991088609872197 441000000000000000000 629148 2000 0 1 420584884330157166794000 210292442165078583397 140737488355328000 1991088609872197 441000000000000000000 

noncomputable def Ns300p1277 := nat_lit 1146457924131577007138022504817229824 

noncomputable def Ns300p1278 := nat_lit 55622383491137842830114816 

noncomputable def Ns300p1279 := nat_lit 165765802965813979555461047055149997387442577217071708002804814432589577443818077787113961638929373976934181427002296099164651520 

noncomputable def Ns300p1280 := nat_lit 2339161237087132293916488564624175334961236323650518666530551769491141470308022618334939169137302751967758308183798693813551104 

noncomputable def Ns300p1281 := nat_lit 1806376868535199018530487674956748421937973075781967479402555772556350921039739347939629411731919720850292991458614968320 

noncomputable def Ns300p1282 := BSN.log_dyadic_bound 534733823616 2631885823616 6 5 Ns300p1279 134217728 35280000 Ns300p1280 Ns300p1281 55309035 3166619647232 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 534733823616) (BSN.artanhQ 2631885823616) 0 5 Ns300p1280 Ns300p1279 Ns300p1281 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns300p1283 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 629148 4000) qz717 629148 4000 0 1 3237648837450999 281474976710656 781250441 27562500000000000 509240072696155279713 281474976710656000 40960179371189 9187500000000000000 (Enclosure.Real.IsNear.const Bool.false 629148 4000) (BSN.isNear_log_sfrac 1583309823616 16000000 3237648837450999 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1583309823616) qz335)) Bool.false Ns300p1278 Ns300p94 1000000564480000 35280000000000000000000 3237648837450999 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1583309823616 16000000 16 3166619647232 2097152000000 55309035 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns300p1282 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns300p1284 := BSN.arctan_dyadic_bound_f 1000 1258296 1 0 16777216 4410000 0 1 1 0 1 1 13333 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1258296) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1258296) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns300p1285 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1258296))) 884279719003555 562949953421312 1 2000000000000000 13333 16777216 1 4410000 14828246038412980649984 883832337761699 562949953421312 200000000441 882000000000000000 qz16 (Ns300p1284 rfl) rfl rfl 

noncomputable abbrev qz173 := qz474

noncomputable def Ns300p1286 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 629148 4000) qz717) qz173 509240072696155279713 281474976710656000 40960179371189 9187500000000000000 883832337761699 2251799813685248 200000000441 3528000000000000000 Ns300p1277 254564796826967533669 140737488355328000 1991088609872197 441000000000000000000 (Ns300p1283 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1258296)))) 1 4 0 1 883832337761699 562949953421312 200000000441 882000000000000000 883832337761699 2251799813685248 200000000441 3528000000000000000 qz340 Ns300p1285 rfl) 

noncomputable def Ns300p1287 := @Ns300p1273 Ns300p1267 Ns300p1268 4155682811460301603 451584000000000000000000 (@Ns300p1275 4155682811460301603 451584000000000000000000 (Ns300p1276 (Ns300p1286 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 629148 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz718 (Real.log Real.pi) 629148 2000 0 1 38410761 33554432 1 67108864 6041513365407 16777216000 157287 33554432000 (Enclosure.Real.IsNear.const Bool.false 629148 2000) RS301to312.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns300p1269 Ns300p1270) 

noncomputable def Ns300p1288 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz167) Bool.false Ns300p1267 Ns300p1268 4155682811460301603 451584000000000000000000 38054589637 33554432 309 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz167) (@HAdd.hAdd Real Real Real qz341 qz475 (Enclosure.sfrac Bool.true Ns300p1269 Ns300p1270)) Bool.false Ns300p1267 Ns300p1268 4155682811460301603 451584000000000000000000 Ns300p1271 (Ns300p1287 rfl rfl)) 

noncomputable def Ns300p1289 := nat_lit 7596875702170816509640704 

noncomputable def Ns300p1290 := nat_lit 3512634176492921946517125106076611944827499437179373450752402056121931334956898118626092746008248872478285820172358042912244523101570727936 

noncomputable def Ns300p1291 := nat_lit 2506470753235766487696750682222710040292364121990016451921956628093332776151073154106912413188340261098567245249242093281238514139136 

noncomputable def Ns300p1292 := nat_lit 17541335333956006588295819125110623985480560878592534755096926346848549979438627065375536467108945042982651059648107193614747454788018896896 

noncomputable def Ns300p1293 := BSN.sin_dyadic_bound_f 107958096892 68719476736 4 3 33554432 8828614 Ns300p1290 Ns300p383 Ns300p1291 Ns300p1292 Ns300p386 Ns300p1291 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107958096892) qz351 0 3 Ns300p1290 Ns300p383 Ns300p1291 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107958096892) qz352 0 3 Ns300p1292 Ns300p386 Ns300p1291 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1294 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz167) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 38054589637) qz349) Bool.false 38054589637 33554432 309 33554432 Bool.true 33554431 33554432 1 4410000 (Ns300p1288 rfl) (Enclosure.sfrac_false_div 38054589637 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 38054589637) qz349) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns300p1289) qz353) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 180 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q1 38054589637 33554432 226375608064910080 72057594037927936 180 Ns300p1289 Ns300p94 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554431 33554432 Ns300p1289 Ns300p94 107958096892 68719476736 8828614 8820000 (Ns300p1293 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p1295 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz167) Bool.false Ns300p1267 Ns300p1268 4155682811460301603 451584000000000000000000 304436717097 268435456 2471 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz167) (@HAdd.hAdd Real Real Real qz341 qz475 (Enclosure.sfrac Bool.true Ns300p1269 Ns300p1270)) Bool.false Ns300p1267 Ns300p1268 4155682811460301603 451584000000000000000000 Ns300p1271 (Ns300p1287 rfl rfl)) 

noncomputable def Ns300p1296 := Ns300p1266 55031 BSN.abs_quadSignPos (BSN.cos_quad_nat0 444 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 223135518 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 281 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268230135 268435456) qz170 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz167) qz167 1) Bool.true 33554431 33554432 87265277 9248440320000 268435448 268435456 2533 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz167) qz167 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz167)) Bool.true 33554431 33554432 87265277 9248440320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz167) qz167) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz167)) Bool.true 33554431 33554432 1396244432 147975045120000 33554431 33554432 87265277 9248440320000 (Ns300p1294 rfl rfl) rfl)) rfl) (Ns300p1295 rfl) RS301to312.d7 

noncomputable def Ns300p1297 := nat_lit 5468369494866403360286530835437436468379230156893806527275889810425921 

noncomputable def Ns300p1298 := nat_lit 392930460189235986675568192974782250992909486651476977357768575041 

noncomputable def Ns300p1299 := nat_lit 16404322623678831608886241369926359840635704651708116627872953894127681 

noncomputable def Ns300p1300 := BSN.cos_dyadic_bound_f 158230231 268435456 3 2 268435456 134217728 Ns300p1297 Ns300p110 Ns300p1298 Ns300p1299 Ns300p113 Ns300p1298 223135518 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 158230231) qz342 0 2 Ns300p1297 Ns300p110 Ns300p1298 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 158230231) qz343 0 2 Ns300p1299 Ns300p113 Ns300p1298 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1301 := nat_lit 40053612687509873729372807847443471562887557153025608835619019436297666461554328224247276817535286046119140625 

noncomputable def Ns300p1302 := nat_lit 23339998227784752475931565734278026619838366595530574049526202889722957343307622883200705051422119140625 

noncomputable def Ns300p1303 := nat_lit 200043048955055472323922548532877333414856914259584586269691612345056167300252557031387436270456224542119140625 

noncomputable def Ns300p1304 := BSN.sin_dyadic_bound_f 411157675 268435456 4 3 268435456 134217728 Ns300p1301 Ns300p237 Ns300p1302 Ns300p1303 Ns300p240 Ns300p1302 268230135 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 411157675) qz344 0 3 Ns300p1301 Ns300p237 Ns300p1302 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 411157675) qz345 0 3 Ns300p1303 Ns300p240 Ns300p1302 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1305 := nat_lit 5398463946013632725863119840296366171371731009240796626565803113383905095664290502750593851973339050531618816 

noncomputable def Ns300p1306 := nat_lit 1006422134256533735483508210784107886287230422531407651333858537556034518948205426271567638011876212736 

noncomputable def Ns300p1307 := nat_lit 32725621526619740272019714586603699944896377255284634263284232461330376340323536841270861736765735717264424960 

noncomputable def Ns300p1308 := BSN.cos_dyadic_bound_f 316396508 268435456 4 3 268435456 134217728 Ns300p1305 Ns300p122 Ns300p1306 Ns300p1307 Ns300p125 Ns300p1306 102584027 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 316396508) qz342 0 3 Ns300p1305 Ns300p122 Ns300p1306 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 316396508) qz343 0 3 Ns300p1307 Ns300p125 Ns300p1306 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1309 := nat_lit 9826251942845524508017463669437863062613113596734636457442886606192640 

noncomputable def Ns300p1310 := nat_lit 391614325852088580292949146871650842261883567594144268357531140096 

noncomputable def Ns300p1311 := nat_lit 25734787712829756044249073407051849157861159227576514488296886061039616 

noncomputable def Ns300p1312 := BSN.sin_dyadic_bound_f 158163884 268435456 3 2 268435456 134217728 Ns300p1309 Ns300p116 Ns300p1310 Ns300p1311 Ns300p119 Ns300p1310 149169958 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 158163884) qz344 0 2 Ns300p1309 Ns300p116 Ns300p1310 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 158163884) qz345 0 2 Ns300p1311 Ns300p119 Ns300p1310 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1313 := Ns300p1264 93752 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 166 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 102584027 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 77 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 149169958 268435456) qz170 rfl rfl (Ns300p1296 RS301to312.d9 RS301to312.d11 RS301to312.d13 RS301to312.d17 (Ns300p1300 rfl rfl) (Ns300p1304 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns300p1295 rfl) RS301to312.d19 RS301to312.d21 RS301to312.d23 RS301to312.d25 RS301to312.d17 (Ns300p1308 rfl rfl) (Ns300p1312 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns300p1314 := nat_lit 4147968636149588597491105709752045811318524542613994570615609143396321 

noncomputable def Ns300p1315 := nat_lit 226092413748068167152850132913614831921416235296984171113782249441 

noncomputable def Ns300p1316 := nat_lit 12443453723621269656139011428990310204291730795371389743504599865690081 

noncomputable def Ns300p1317 := BSN.cos_dyadic_bound_f 147667781 268435456 3 2 268435456 134217728 Ns300p1314 Ns300p110 Ns300p1315 Ns300p1316 Ns300p113 Ns300p1315 228833025 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 147667781) qz342 0 2 Ns300p1314 Ns300p110 Ns300p1315 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 147667781) qz343 0 2 Ns300p1316 Ns300p113 Ns300p1315 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1318 := nat_lit 11655814435209057585835375506392826447525261400109624282390716685025280 

noncomputable def Ns300p1319 := nat_lit 551012669394191611600930294586568680446801486923196240660833304576 

noncomputable def Ns300p1320 := nat_lit 30526240928844703081245296248647119584702580274070187945681283302096896 

noncomputable def Ns300p1321 := BSN.sin_dyadic_bound_f 165061276 268435456 3 2 268435456 134217728 Ns300p1318 Ns300p116 Ns300p1319 Ns300p1320 Ns300p119 Ns300p1319 154854454 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 165061276) qz344 0 2 Ns300p1318 Ns300p116 Ns300p1319 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 165061276) qz345 0 2 Ns300p1320 Ns300p119 Ns300p1319 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1322 := Ns300p1262 126383 BSN.abs_quadSignPos (BSN.cos_quad_nat0 4 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 228833025 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 154854454 268435456) qz170 rfl rfl (Ns300p1313 rfl rfl) (Ns300p1295 rfl) RS301to312.d27 RS301to312.d29 RS301to312.d31 RS301to312.d33 RS301to312.d17 (Ns300p1317 rfl rfl) (Ns300p1321 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p1323 := nat_lit 9971122890278089303241712149283655394503269443776425146540000481911238344668214024594227523159711872164163521 

noncomputable def Ns300p1324 := nat_lit 6323217174770146151591784482030701604378708345807991486251895688836559621205373046269374518307897339841 

noncomputable def Ns300p1325 := nat_lit 60406138083411060851135681341954532653903049668242757095170991427315691609521319902192974796088393041550634945 

noncomputable def Ns300p1326 := BSN.cos_dyadic_bound_f 368760879 268435456 4 3 268435456 134217728 Ns300p1323 Ns300p122 Ns300p1324 Ns300p1325 Ns300p125 Ns300p1324 52554878 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 368760879) qz342 0 3 Ns300p1323 Ns300p122 Ns300p1324 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 368760879) qz343 0 3 Ns300p1325 Ns300p125 Ns300p1324 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1327 := nat_lit 196795506101962040968568077681 

noncomputable def Ns300p1328 := BSN.cos_dyadic_bound_f 21062203 268435456 2 1 268435456 134217728 Ns300p1327 Ns300p133 Ns300p1327 Ns300p1327 Ns300p134 Ns300p1327 267609579 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 21062203) qz342 0 1 Ns300p1327 Ns300p133 Ns300p1327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 21062203) qz343 0 1 Ns300p1327 Ns300p134 Ns300p1327 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1329 := Ns300p1260 154893 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 110 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 52554878 268435456) BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267609579 268435456) qz170 rfl rfl (Ns300p1322 rfl) (Ns300p1295 rfl) RS301to312.d35 RS301to312.d37 RS301to312.d39 RS301to312.d41 RS301to312.d17 (Ns300p1326 rfl rfl) (Ns300p1328 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p1330 := nat_lit 1073538035826019647981082836682263014276492500656717557594791386436801 

noncomputable def Ns300p1331 := nat_lit 15145549200041546472237929002735460977986855822602920256034198721 

noncomputable def Ns300p1332 := nat_lit 3220583816379658860850304034188783571907521528258507466943862090912961 

noncomputable def Ns300p1333 := BSN.cos_dyadic_bound_f 105326009 268435456 3 2 268435456 134217728 Ns300p1330 Ns300p110 Ns300p1331 Ns300p1332 Ns300p113 Ns300p1331 248035819 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 105326009) qz342 0 2 Ns300p1330 Ns300p110 Ns300p1331 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 105326009) qz343 0 2 Ns300p1332 Ns300p113 Ns300p1331 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1334 := Ns300p1258 Bool.true 456413347 154893 Bool.true 105326009 14148475504056880 1 Bool.false 248035819 Bool.false Bool.true 377977535 168020 BSN.abs_quadSignPos (BSN.cos_quad_nat0 200 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 248035819 268435456) qz170 rfl (Ns300p1329 rfl) (Ns300p1295 rfl) RS301to312.d58 RS301to312.d60 RS301to312.d17 (Ns300p1333 rfl rfl) rfl 

noncomputable def Ns300p1335 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz167) qz167 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz167) qz167 10) 377977535 268435456 168020 268435456 377977535 268435456 168020 268435456 202925143930961920 377977535 134217728 42005 33554432 (Ns300p1334 rfl rfl rfl rfl) 

noncomputable def Ns300p1336 := @Enclosure.Real.IsNear.mulLit_ff qz168 qz169 662959 2097152 1 16777216 511226791766985 562949953421312 1922247188094679 155163080911749120000 338922402643048608615 1180591620717411303424 

noncomputable abbrev qz174 := (@Neg.neg Real Real.instNeg (1 : Real))

noncomputable abbrev qz175 := (@HPow.hPow Real Real Real qz470 qz471 qz625)

noncomputable abbrev qz719 := (@HPow.hPow Real Nat Real RSCompact.c1 qz174 10)

noncomputable abbrev qz477 := qz719

noncomputable def Ns300p1337 := @Enclosure.Real.IsNear.mulLit_ff qz477 qz175 1 1 0 1 662959 2097152 1 16777216 662959 2097152 1 16777216 

noncomputable abbrev qz176 := qz471

noncomputable def Ns300p1338 := @Enclosure.Real.IsNear.sqrt_image qz176 839968102311 8388608000 157287 8388608000 167882837 167882870 16777216 (@Enclosure.Real.IsNear.of_eq qz176 (@HMul.hMul Real Real Real qz5 qz167 qz3) Bool.false 839968102311 8388608000 157287 8388608000 (BSN.t_div_two_pi_mk qz167 629148 1000 qz170) (@Enclosure.Real.IsNear.mulLit_ff qz167 qz3 629148 1000 0 1 5340353 33554432 1 33554432 839968102311 8388608000 157287 8388608000 (Enclosure.Real.IsNear.const Bool.false 629148 1000) RS301to312.d44 rfl)) 

noncomputable abbrev qz855 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 629148 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz720 := qz855

noncomputable abbrev qz478 := qz720

noncomputable abbrev qz177 := qz478

noncomputable abbrev qz479 := (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 335765707 33554432 33 33554432 335765707 33554432 33 33554432 (Ns300p1338 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns300p1339 := @Enclosure.Real.IsNear.sqrt_image qz177 335765707 33554432 33 33554432 53071712 53071718 16777216 qz479 rfl 

noncomputable def Ns300p1340 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz177) 53071715 16777216 3 16777216 5303671 5303673 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz177) Bool.false 106143430 33554432 6 33554432 53071715 16777216 3 16777216 (Ns300p1339 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns300p1341 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz177)) Bool.false 10607344 33554432 2 33554432 662959 2097152 1 16777216 (Ns300p1340 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz856 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 629148 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1)))

noncomputable abbrev qz721 := (Real.cos qz856)

noncomputable abbrev qz480 := qz721

noncomputable abbrev qz178 := (@Inv.inv Real Real.instInv qz480)

noncomputable abbrev qz722 := (@HSub.hSub Real Real Real qz810 (@HMul.hMul Real Real Real qz807 qz853 qz853) qz853)

noncomputable abbrev qz481 := (@HMul.hMul Real Real Real qz623 qz621 (@HSub.hSub Real Real Real qz628 qz722 qz639))

noncomputable abbrev qz179 := (Real.cos qz481)

noncomputable def Ns300p1342 := @Enclosure.Real.IsNear.of_eq qz169 (@HMul.hMul Real Real Real qz5 qz178 qz179) Bool.false 511226791766985 

noncomputable def Ns300p1343 := @Enclosure.Real.IsNear.mulLit_ff qz178 qz179 33583287 33554432 217 

noncomputable def Ns300p1344 := @Enclosure.Real.IsNear.recentre' qz178 Bool.false 33583287 33554432 217 33554432 33583287 33554432 217 

noncomputable abbrev qz180 := qz480

noncomputable def Ns300p1345 := @Enclosure.Real.IsNear.recentre' qz180 Bool.false 16762801 16777216 59427152 9248440320000 16762801 16777216 3714197 578027520000 

noncomputable abbrev qz723 := qz856

noncomputable abbrev qz482 := qz723

noncomputable abbrev qz181 := qz482

noncomputable def Ns300p1346 := @Enclosure.Real.IsNear.cos_image qz181 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1391015) qz349) Bool.false 1391015 33554432 13 2097152 Bool.false 16762801 16777216 1 

noncomputable def Ns300p1347 := nat_lit 178108097700071039974019003 

noncomputable def Ns300p1348 := nat_lit 28823037615171174400000000000000 

noncomputable abbrev qz483 := qz715

noncomputable abbrev qz182 := qz483

noncomputable def Ns300p1349 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz182 884279719003555 140737488355328 1 500000000000000 221387 33554432 33 33554432 195768034151040030785 4722366482869645213696 Ns300p1347 

noncomputable def Ns300p1350 := @Enclosure.Real.IsNear.subLit_ff_p qz177 qz166 335765707 33554432 33 33554432 10 1 0 1 221387 221387 33554432 33 

noncomputable abbrev qz724 := (Enclosure.Real.IsNear.const Bool.false 10 1)

noncomputable def Ns300p1351 := @Ns300p1350 33554432 qz479 qz724 

noncomputable def Ns300p1352 := @Enclosure.Real.IsNear.recentre' qz181 Bool.false 195768034151040030785 4722366482869645213696 Ns300p1347 Ns300p1348 1391015 33554432 13 2097152 (@Ns300p1349 Ns300p1348 RS301to312.d43 (Ns300p1351 rfl rfl) rfl) 

noncomputable def Ns300p1353 := nat_lit 3743925971941368128550625 

noncomputable def Ns300p1354 := nat_lit 30423614405477505635920876929024 

noncomputable def Ns300p1355 := nat_lit 456354216082162584538813153935360 

noncomputable def Ns300p1356 := BSN.cos_dyadic_bound_f 1391015 33554432 2 1 16777216 4410000 Ns300p1353 Ns300p1354 Ns300p1353 Ns300p1353 Ns300p1355 Ns300p1353 16762801 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1391015) (BSN.cosEvenQ 33554432) 0 1 Ns300p1353 Ns300p1354 Ns300p1353 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1391015) (BSN.cosOddQ 33554432) 0 1 Ns300p1353 Ns300p1355 Ns300p1353 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1357 := @Enclosure.Real.IsNear.inv_image qz180 16762801 16777216 3714197 578027520000 16791535 16791752 16777216 (Ns300p1345 (@Ns300p1346 4410000 (Ns300p1352 rfl) (Enclosure.sfrac_false_div 1391015 33554432) (Ns300p1356 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns300p1358 := @Enclosure.Real.IsNear.recentre' qz179 Bool.false 15222655 16777216 

noncomputable abbrev qz183 := qz481

noncomputable def Ns300p1359 := @Enclosure.Real.IsNear.cos_image qz183 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1819829)) qz665) Bool.true 1819829 4194304 

noncomputable def Ns300p1360 := nat_lit 68751198019975923024925385845 

noncomputable def Ns300p1361 := nat_lit 30275917827326527127053852273254497 

noncomputable def Ns300p1362 := @Enclosure.Real.IsNear.recentre' qz183 Bool.true Ns300p1360 Ns300p564 Ns300p1361 

noncomputable abbrev qz484 := (@HSub.hSub Real Real Real qz628 qz722 qz639)

noncomputable abbrev qz184 := qz484

noncomputable def Ns300p1363 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz184 884279719003555 140737488355328 1 500000000000000 77748247011079 

noncomputable abbrev qz485 := qz722

noncomputable abbrev qz185 := qz485

noncomputable def Ns300p1364 := @Enclosure.Real.IsNear.subLit_tf qz185 qz27 7379502833415 1125899906842624 1121908887 1125899906842624 1 16 

noncomputable abbrev qz725 := (@HMul.hMul Real Real Real qz807 qz853 qz853)

noncomputable abbrev qz486 := qz725

noncomputable abbrev qz186 := qz486

noncomputable def Ns300p1365 := @Enclosure.Real.IsNear.subLit_ff_n qz186 qz182 49012203769 1125899906842624 14612631 1125899906842624 221387 33554432 33 33554432 

noncomputable def Ns300p1366 := @Enclosure.Real.IsNear.mulLit_ff qz182 qz182 221387 33554432 33 33554432 221387 33554432 33 33554432 49012203769 1125899906842624 

noncomputable def Ns300p1367 := nat_lit 10967870800598929718956081 

noncomputable def Ns300p1368 := nat_lit 7427640235712281649394745344 

noncomputable def Ns300p1369 := nat_lit 111414603535684224740921180160 

noncomputable def Ns300p1370 := BSN.cos_dyadic_bound_f 1819829 4194304 2 1 16777216 4410000 Ns300p1367 Ns300p1368 Ns300p1367 Ns300p1367 Ns300p1369 Ns300p1367 15222655 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1819829) (BSN.cosEvenQ 4194304) 0 1 Ns300p1367 Ns300p1368 Ns300p1367 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1819829) (BSN.cosOddQ 4194304) 0 1 Ns300p1367 Ns300p1369 Ns300p1367 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1371 := @Ns300p1358 964064432 147975045120000 15222655 16777216 60254027 9248440320000 (@Ns300p1359 211 33554432 Bool.false 15222655 16777216 1 4410000 (@Ns300p1362 Ns300p567 1819829 4194304 211 33554432 (@Ns300p1363 1125899906842624 1121908887 1125899906842624 Ns300p1360 Ns300p564 Ns300p1361 Ns300p567 RS301to312.d43 (@Ns300p1364 0 1 1243971952177264 77748247011079 1125899906842624 1121908887 1125899906842624 (@Ns300p1365 247615026017630945280 7379502833415 1125899906842624 1121908887 1125899906842624 (@Ns300p1366 14612631 1125899906842624 (Ns300p1351 rfl rfl) (Ns300p1351 rfl rfl) rfl) (Ns300p1351 rfl rfl) rfl rfl) qz358 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 1819829 4194304) (BSN.cos_neg_of_bound 1819829 4194304 Bool.false 15222655 16777216 1 4410000 (Ns300p1370 rfl rfl)) rfl rfl) 

noncomputable abbrev qz857 := (Enclosure.sfrac Bool.false 1 1)

noncomputable abbrev qz726 := qz857

noncomputable abbrev qz487 := qz726

noncomputable abbrev qz187 := qz487

noncomputable abbrev qz188 := (BSN.correction_mk qz483 (BSN.cos_two_pi_p_ne_zero_mk qz469 629148 1000 10 qz473 rfl rfl (@BSN.floor_sqrt_eq_dec qz469 629148 1000 10 qz473 rfl rfl rfl)))

noncomputable abbrev qz727 := (Enclosure.Real.IsNear.const Bool.false 1 1)

noncomputable abbrev qz488 := (@Enclosure.Real.IsNear.of_eq qz719 qz187 Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 10 rfl) qz727)

noncomputable def Ns300p1372 := @Ns300p1336 71776926356280872893 Ns300p579 (Ns300p1337 qz488 (@Enclosure.Real.IsNear.of_eq qz175 (@Inv.inv Real Real.instInv (Real.sqrt qz177)) Bool.false 662959 2097152 1 16777216 (BSN.rpow_neg_quarter_mk qz176 (BSN.t_div_two_pi_nonneg qz167 629148 1000 qz170)) Ns300p1341) rfl) (@Ns300p1342 562949953421312 1922247188094679 155163080911749120000 qz188 (@Ns300p1343 33554432 15222655 16777216 60254027 9248440320000 511226791766985 562949953421312 1922247188094679 155163080911749120000 (@Ns300p1344 33554432 (Ns300p1357 rfl rfl rfl rfl rfl) rfl) (Ns300p1371 rfl) rfl)) 

noncomputable def Ns300p1373 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz167) (hardyZApproximantRS₀ qz167) Bool.true 3663647960807928705895 1180591620717411303424 22702420029474412072893 Ns300p579 (@Eq.refl Real (hardyZApproximantRS₀ qz167)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz167) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz167) qz167 10) (@HMul.hMul Real Real Real qz5 qz168 qz169)) Bool.true 3663647960807928705895 1180591620717411303424 22702420029474412072893 Ns300p579 (BSN.hardyZApproximantRS₀_eq qz167 10 (@BSN.floor_sqrt_eq_dec qz167 629148 1000 10 qz170 rfl rfl rfl)) (@Ns300p1257 3663647960807928705895 1180591620717411303424 22702420029474412072893 Ns300p579 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz167) qz167 10) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz167) qz167 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz167) qz167 10)) Bool.true 377977535 134217728 42005 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz167) qz167 10) (Ns300p1335 (Ns300p1334 rfl rfl rfl rfl) rfl rfl)) (Ns300p1372 rfl) rfl rfl)) 

theorem RS301to312.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz167) Bool.true 3663647960807928705895 1180591620717411303424 22702420029474412072893 Ns300p579 := Ns300p1373 

theorem RS301to312.d62 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal (RS301to312.d3 a b h)) (hardyZApproximantRS a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal (RS301to312.d3 a b h)) 

theorem RS301to312.d63 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

theorem RS301to312.d64 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 qz324 RS301to312.d63 rfl 

theorem RS301to312.d65 : Enclosure.Real.IsNear qz3 Bool.false 85445659 536870912 1 536870912 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 85445659 536870912 1 536870912 85445659 536870912 1 536870912 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 42722829 42722830 268435456 RS301to312.d64 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz189 := (@HMul.hMul Real Real Real qz327 qz320 Real.pi)

theorem RS301to312.d66 : Enclosure.Real.IsNear qz189 Bool.false 884279719003555 70368744177664 1 250000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz320 Real.pi 4 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 70368744177664 1 250000000000000 (Enclosure.Real.IsNear.const Bool.false 4 1) RS301to312.d63 rfl 

noncomputable def Ns300p1374 := nat_lit 781950621441006189802102638025 

noncomputable def Ns300p1375 := nat_lit 79228162514264337593543950336 

noncomputable def Ns300p1376 := nat_lit 26986075409044041160201671 

noncomputable def Ns300p1377 := nat_lit 4294967296000000000000000000000000000000 

theorem RS301to312.d67 : Enclosure.Real.IsNear RSCompact.c2 Bool.false Ns300p1374 Ns300p1375 Ns300p1376 Ns300p1377 := @Enclosure.Real.IsNear.mulLit_ff Real.pi Real.pi 226375608064910080 72057594037927936 1 1000000000000000 226375608064910080 72057594037927936 1 1000000000000000 Ns300p1374 Ns300p1375 Ns300p1376 Ns300p1377 RS301to312.d63 RS301to312.d63 rfl 

noncomputable def Ns300p1378 := nat_lit 19807040628566084398385987584 

noncomputable def Ns300p1379 := nat_lit 1073741824000000000000000000000000000000 

noncomputable abbrev qz728 := (@HMul.hMul Real Real Real qz807 (Enclosure.sfrac Bool.false 4 1) RSCompact.c2)

noncomputable abbrev qz489 := qz728

noncomputable abbrev qz190 := qz489

theorem RS301to312.d68 : Enclosure.Real.IsNear qz190 Bool.false Ns300p1374 Ns300p1378 Ns300p1376 Ns300p1379 := @Enclosure.Real.IsNear.mulLit_ff qz320 RSCompact.c2 4 1 0 1 Ns300p1374 Ns300p1375 Ns300p1376 Ns300p1377 Ns300p1374 Ns300p1378 Ns300p1376 Ns300p1379 (Enclosure.Real.IsNear.const Bool.false 4 1) RS301to312.d67 rfl 

noncomputable def Ns300p1380 := nat_lit 691463075802508163054686763366652189853178875 

noncomputable def Ns300p1381 := nat_lit 2787593149816327892691964784081045188247552 

noncomputable def Ns300p1382 := nat_lit 2184744797947834540264818678394244808492865883128339 

noncomputable def Ns300p1383 := nat_lit 9223372036854775808000000000000000000000000000000000000000000000 

noncomputable def Ns300p1384 := nat_lit 22300745198530623141535718272648361505980416 

noncomputable def Ns300p1385 := nat_lit 73786976294838206464000000000000000000000000000000000000000000000 

noncomputable def Ns300p1386 := @Enclosure.Real.IsNear.mulLit_ff qz321 (@HMul.hMul Real Real Real qz5 RSCompact.c2 Real.pi) 8 1 0 1 Ns300p1380 Ns300p1384 Ns300p1382 Ns300p1385 Ns300p1380 Ns300p1381 Ns300p1382 Ns300p1383 (Enclosure.Real.IsNear.const Bool.false 8 1) (@Enclosure.Real.IsNear.mulLit_ff RSCompact.c2 Real.pi Ns300p1374 Ns300p1375 Ns300p1376 Ns300p1377 226375608064910080 72057594037927936 1 1000000000000000 Ns300p1380 Ns300p1384 Ns300p1382 Ns300p1385 RS301to312.d67 RS301to312.d63 rfl) rfl 

noncomputable abbrev qz729 := (@HMul.hMul Real Real Real qz5 qz321 RSCompact.c10)

theorem RS301to312.d69 : Enclosure.Real.IsNear qz729 Bool.false Ns300p1380 Ns300p1381 Ns300p1382 Ns300p1383 := Ns300p1386 

noncomputable def Ns300p1387 := nat_lit 2345851864323018569406307914075 

noncomputable def Ns300p1388 := nat_lit 2475880078570760549798248448 

noncomputable def Ns300p1389 := nat_lit 80958226227132123480605013 

noncomputable def Ns300p1390 := nat_lit 134217728000000000000000000000000000000 

noncomputable abbrev qz490 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 96 1) RSCompact.c2)

noncomputable abbrev qz491 := (Enclosure.sfrac Bool.false 96 1)

noncomputable def Ns300p1391 := @Enclosure.Real.IsNear.inv_image qz490 Ns300p1387 Ns300p1388 Ns300p1389 Ns300p1390 283314 283315 268435456 (@Enclosure.Real.IsNear.mulLit_ff qz491 RSCompact.c2 96 1 0 1 Ns300p1374 Ns300p1375 Ns300p1376 Ns300p1377 Ns300p1387 Ns300p1388 Ns300p1389 Ns300p1390 (Enclosure.Real.IsNear.const Bool.false 96 1) RS301to312.d67 rfl) rfl rfl 

noncomputable abbrev qz492 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 96 1) RSCompact.c2))

theorem RS301to312.d70 : Enclosure.Real.IsNear qz492 Bool.false 566629 536870912 1 536870912 := @Enclosure.Real.IsNear.recentre' qz492 Bool.false 566629 536870912 1 536870912 566629 536870912 1 536870912 (Ns300p1391 rfl rfl rfl rfl) rfl 

noncomputable def Ns300p1392 := nat_lit 16800416949573630512836379124916777165372178945158405036328527291546601056849282225032016064801681826330922753850380589249665585 

noncomputable def Ns300p1393 := nat_lit 5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991351228465152 

noncomputable def Ns300p1394 := nat_lit 35657838690899364278180586904234488227645401538924612840500751111691291616846507041172906342449725021496840862268253008854368692888761612957549441587281399105435937158845141654527 

noncomputable def Ns300p1395 := nat_lit 28393090590372636269678177831043500625892185753264809677104373720636142639256111403736446690053352071379711230643590397952000000000000000000000000000000000000000000000000000000000000 

noncomputable abbrev qz191 := (@HAdd.hAdd Real Real Real qz341 qz472 (@HMul.hMul Real Real Real qz327 (Zeta.RiemannSiegel.correctionLinear qz483) (@Inv.inv Real Real.instInv qz478)))

noncomputable def Ns300p1396 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz167) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz167) qz167 10) (@HMul.hMul Real Real Real qz5 qz168 qz191)) Bool.true Ns300p1392 Ns300p1393 Ns300p1394 Ns300p1395 

noncomputable def Ns300p1397 := nat_lit 1549910017177689505204022456277098402327304369395739734082066416391599252575260924523131868598077732793607262585690202942020145 

noncomputable def Ns300p1398 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz167) qz167 10) (@HMul.hMul Real Real Real qz5 qz168 qz191) 377977535 134217728 42005 33554432 Ns300p1397 Ns300p1393 

noncomputable def Ns300p1399 := nat_lit 114046137694989174831143832363021478018965824981121545915010004962941348185933096307755794954507288164183935064597328854368692888761612957549441587281399105435937158845141654527 

noncomputable def Ns300p1400 := nat_lit 2254913792424463256144373641892958020218534132428597724079772394657378399972709498674581923477182505309027028165301334624391339578490880 

noncomputable def Ns300p1401 := nat_lit 2337867073495781044082699618343062545839643732713093470459057673840462611677737121787519090317919709655660851705294298655 

noncomputable def Ns300p1402 := nat_lit 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376 

noncomputable def Ns300p1403 := nat_lit 21214343664566584772439127424718658701771452769899252424517082550431528412842987034272355606983373255920015413675017520206070033079637808034744954170734175777510634393399 

noncomputable def Ns300p1404 := @Enclosure.Real.IsNear.mulLit_ff qz168 qz191 662959 2097152 1 16777216 Ns300p1401 Ns300p1402 Ns300p1403 

noncomputable def Ns300p1405 := nat_lit 1692360078714647070746313204231470860594045266703653912371657712497481265023714983685996931198439125500900222697472000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns300p1406 := nat_lit 7128805253468121370228792684654147619768378331513561723893458413668518891034403409706927151151898946663195162070278625 

noncomputable def Ns300p1407 := nat_lit 2235948639446137666676558906760941079868650605073390701002387719769105809738242292882917189027542257683199133033557681854630297716740272312704587536607581997595709540591 

noncomputable def Ns300p1408 := nat_lit 15231240708431823636716818838083237745346407400332885211344919412477331385213434853173972380785952129508102004277248000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns300p1409 := @Enclosure.Real.IsNear.addLit_ft_p qz169 (@HMul.hMul Real Real Real qz5 (Zeta.RiemannSiegel.correctionLinear qz182) (@Inv.inv Real Real.instInv qz177)) 511226791766985 562949953421312 1922247188094679 155163080911749120000 Ns300p1406 Ns300p1402 Ns300p1407 Ns300p1408 

noncomputable def Ns300p1410 := nat_lit 1316102160129668936933301181503915339659840152180372511996352242138824263423312347707809930135618898588451311365881180032661164769935360 

noncomputable def Ns300p1411 := nat_lit 2125951135924760736802442982500802247077036545204777638013443873585959002238260176440849780749342633019674207375 

noncomputable def Ns300p1412 := nat_lit 76957043352332967211482500195592995713046365762627825523336510555167425334955489475418488779072100860950445293568 

noncomputable def Ns300p1413 := nat_lit 31827092408430053988543120674915350067664181302230959383964434797579778237610357805033557341125303160948543487284363712963947612098107424168090236861679697642332549 

noncomputable def Ns300p1414 := nat_lit 21788464605949149565768459565281731241244898891925170723931674116817471578426506309281309672526291078817513472000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns300p1415 := @Enclosure.Real.IsNear.mulLit_tf (Zeta.RiemannSiegel.correctionLinear qz182) (@Inv.inv Real Real.instInv qz177) Ns300p1411 Ns300p1412 Ns300p1413 Ns300p1414 3353231 33554432 1 33554432 Ns300p1406 

noncomputable def Ns300p1416 := nat_lit 3751927868013745743339015444851573511198750055512121049246409685324893364508805896699339039740893305883875 

noncomputable def Ns300p1417 := nat_lit 143343663499379469475676305956380433799785311823017570233599302461682679755530300504376159569382855409664 

noncomputable def Ns300p1418 := nat_lit 542943856618695805172745312080903975550692360546962299252370050478708543976695289390789413386432288074649889389307185528226327651289386378059143300949114901123 

noncomputable def Ns300p1419 := nat_lit 405841779074615790802397943386467755609096938593781939222136030286875955358641339638853625813988802560000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns300p1420 := @Enclosure.Real.IsNear.mulLit_ff (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz182) qz492 Ns300p1416 Ns300p1417 Ns300p1418 Ns300p1419 566629 536870912 1 536870912 Ns300p1411 

noncomputable abbrev qz858 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 629148 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1)))

noncomputable abbrev qz730 := (@HMul.hMul Real Real Real qz807 qz805 (@HSub.hSub Real Real Real qz810 qz858 qz857))

noncomputable abbrev qz493 := (@HMul.hMul Real Real Real qz623 qz730 qz730)

noncomputable abbrev qz494 := qz730

noncomputable abbrev qz192 := (@HMul.hMul Real Real Real qz327 qz493 qz494)

noncomputable abbrev qz193 := (Real.sin qz481)

noncomputable abbrev qz194 := (@HMul.hMul Real Real Real qz327 qz319 qz494)

noncomputable def Ns300p1421 := @HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 qz192 qz193) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz194 qz189) qz179) 

noncomputable abbrev qz731 := (Real.sin qz856)

noncomputable abbrev qz495 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz623 qz621 qz731))

noncomputable abbrev qz195 := (@HMul.hMul Real Real Real qz327 qz319 qz495)

noncomputable abbrev qz496 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz623 qz728 qz721))

noncomputable abbrev qz196 := (@HMul.hMul Real Real Real qz327 qz319 qz496)

noncomputable abbrev qz497 := qz731

noncomputable abbrev qz197 := qz497

noncomputable abbrev qz498 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 8 1) RSCompact.c9)

noncomputable def Ns300p1422 := @HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns300p1421 (@HMul.hMul Real Real Real qz5 qz195 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz182))) (@HMul.hMul Real Real Real qz5 qz196 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz182))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz498 qz197) qz169) 

noncomputable abbrev qz198 := (BSN.cos_two_pi_p_ne_zero_mk qz469 629148 1000 10 qz473 rfl rfl (@BSN.floor_sqrt_eq_dec qz469 629148 1000 10 qz473 rfl rfl rfl))

noncomputable def Ns300p1423 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz182) (@HMul.hMul Real Real Real qz5 qz178 Ns300p1422) Bool.false Ns300p1416 Ns300p1417 Ns300p1418 Ns300p1419 (BSN.iteratedDeriv_three_correction_mk qz182 qz198) 

noncomputable def Ns300p1424 := nat_lit 111720077344824417098938142925050838859084717323031892533891621441296309063599689997604434888197625 

noncomputable def Ns300p1425 := nat_lit 4271974071841820164790043412339104229205409044713305539894083215644439451561281100045924173873152 

noncomputable def Ns300p1426 := nat_lit 6014530579599771747483135035513089864291211164891667771978354089539929285981610409699042690470383567872926733572398876640640280239665211151504681259637 

noncomputable def Ns300p1427 := @Enclosure.Real.IsNear.mulLit_ff qz178 Ns300p1422 33583291 33554432 109 268435456 Ns300p1424 Ns300p1425 Ns300p1426 

noncomputable def Ns300p1428 := nat_lit 4535635326891568945375061892566842089695076703210718250522047619747474290713384817974868705280000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns300p1429 := @Enclosure.Real.IsNear.recentre' qz178 Bool.false 537332656 536870912 218 536870912 33583291 33554432 109 

noncomputable def Ns300p1430 := @Enclosure.Real.IsNear.recentre' qz180 Bool.false 268204782 268435456 15283910912 37881611550720000 134102391 134217728 59702777 147975045120000 

noncomputable abbrev qz732 := (@Nat.cast Real Real.instNatCast 268435456)

noncomputable def Ns300p1431 := @Enclosure.Real.IsNear.cos_image qz181 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11129233) qz732) Bool.false 11129233 268435456 209 536870912 Bool.false 268204782 268435456 1 

noncomputable def Ns300p1432 := nat_lit 890540488528883729859792551 

noncomputable def Ns300p1433 := nat_lit 2305843009213693952000000000000000 

noncomputable def Ns300p1434 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz182 884279719003555 140737488355328 1 500000000000000 3542545 536870912 33 536870912 3132600697157448747475 75557863725914323419136 Ns300p1432 

noncomputable def Ns300p1435 := @Enclosure.Real.IsNear.subLit_ff_p qz177 qz166 5372251665 536870912 33 536870912 10 1 0 1 3542545 3542545 536870912 33 

noncomputable def Ns300p1436 := @Enclosure.Real.IsNear.sqrt_image qz176 13439491367133 134217728000 157287 134217728000 2686125816 2686125849 268435456 (@Enclosure.Real.IsNear.of_eq qz176 (@HMul.hMul Real Real Real qz5 qz167 qz3) Bool.false 13439491367133 134217728000 157287 134217728000 (BSN.t_div_two_pi_mk qz167 629148 1000 qz170) (@Enclosure.Real.IsNear.mulLit_ff qz167 qz3 629148 1000 0 1 85445659 536870912 1 536870912 13439491367133 134217728000 157287 134217728000 (Enclosure.Real.IsNear.const Bool.false 629148 1000) RS301to312.d65 rfl)) 

noncomputable def Ns300p1437 := @Ns300p1435 536870912 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 5372251665 536870912 33 536870912 5372251665 536870912 33 536870912 (Ns300p1436 rfl rfl rfl rfl rfl rfl) rfl) qz724 

noncomputable def Ns300p1438 := @Enclosure.Real.IsNear.recentre' qz181 Bool.false 3132600697157448747475 75557863725914323419136 Ns300p1432 Ns300p1433 11129233 268435456 209 536870912 (@Ns300p1434 Ns300p1433 RS301to312.d64 (Ns300p1437 rfl rfl) rfl) 

noncomputable def Ns300p1439 := nat_lit 15341256786158421880327187521 

noncomputable def Ns300p1440 := BSN.cos_dyadic_bound_f 11129233 268435456 2 1 268435456 70560000 Ns300p1439 Ns300p133 Ns300p1439 Ns300p1439 Ns300p134 Ns300p1439 268204782 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 11129233) qz342 0 1 Ns300p1439 Ns300p133 Ns300p1439 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 11129233) qz343 0 1 Ns300p1439 Ns300p134 Ns300p1439 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz499 := (Ns300p1430 (@Ns300p1431 70560000 (Ns300p1438 rfl) (Enclosure.sfrac_false_div 11129233 268435456) (Ns300p1440 rfl rfl) rfl rfl) rfl)

noncomputable def Ns300p1441 := @Enclosure.Real.IsNear.inv_image qz180 134102391 134217728 59702777 147975045120000 268666219 268666437 268435456 qz499 rfl 

noncomputable def Ns300p1442 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns300p1421 (@HMul.hMul Real Real Real qz5 qz195 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz182))) (@HMul.hMul Real Real Real qz5 qz196 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz182))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz498 qz197) qz169) 

noncomputable def Ns300p1443 := nat_lit 151605315332225613126205238230730549066196890420506984186617378112504558533004229487858646402565625 

noncomputable def Ns300p1444 := nat_lit 5566127634702417273978956962740352402928006259104744673134316896733762456141549670244886831100633902771199849857267232798649490440266945251267881259637 

noncomputable def Ns300p1445 := nat_lit 15731952471848397276512161442610028187200830223240684151978153730875 

noncomputable def Ns300p1446 := nat_lit 1684996666696914987166688442938726917102321526408785780068975640576 

noncomputable def Ns300p1447 := nat_lit 15346364059050678817767101765488538275605459004883336422525372624336651491970666425333008412671213884670533 

noncomputable def Ns300p1448 := nat_lit 155229825668301526594994629264176708510081251677806841036800000000000000000000000000000000000000000000000000000 

noncomputable def Ns300p1449 := nat_lit 188247957929150671436133911866334127582597038551267680044703531397391463718348148164814195342575120526743434551619883471914446506015335768826614731644414126456832000 

noncomputable def Ns300p1450 := nat_lit 1350757993001005253621592550583133668332588734000068653739634618866798726228677988842124967298565625 

noncomputable def Ns300p1451 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real qz11 Ns300p1421 (@HMul.hMul Real Real Real qz5 qz195 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 2 Zeta.RiemannSiegel.correction qz182))) (@HMul.hMul Real Real Real qz5 qz196 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz182)) Ns300p1450 Ns300p1425 

noncomputable def Ns300p1452 := nat_lit 1659619549603050846804685082168794863088973361475662474012037951106608396704151905190216543709037977923156613564098011003429142704767052841317345579637 

noncomputable def Ns300p1453 := nat_lit 2130123060462060707634512568291290647100296673207896115714663026981935032636659171875 

noncomputable def Ns300p1454 := nat_lit 7588550360256754183279148073529370729071901715047420004889892225542594864082845696 

noncomputable def Ns300p1455 := nat_lit 590080982579815920391722708918594840341093617248697362012998013615507347446165464947545671434370324425950634011300612958830625039 

noncomputable def Ns300p1456 := nat_lit 685111125335818814179800406122118866290511063300174775355141466717362847744000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns300p1457 := nat_lit 1150464570281199495008988778591392524025557194500449161013897180828952381682588424830278960526062100625701892701558221775867343015215016726773339745658795998655182658788445388800000 

noncomputable def Ns300p1458 := nat_lit 565013590420762873297624322301917060885390423844611218101728289293548983037425 

noncomputable def Ns300p1459 := nat_lit 1809251394333065553493296640760748560207343510400633813116524750123642650624 

noncomputable def Ns300p1460 := nat_lit 403318396961576371095769167743353407627813074417835047066671521286878858222662957524607355309300254229424411 

noncomputable def Ns300p1461 := nat_lit 1574799283373810470031122850494339350471758933907136978595348480000000000000000000000000000000000000000000000000 

noncomputable def Ns300p1462 := @Enclosure.Real.IsNear.subLit_ft Ns300p1421 (@HMul.hMul Real Real Real qz5 qz195 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 2 Zeta.RiemannSiegel.correction qz182)) Ns300p1458 Ns300p1459 Ns300p1460 Ns300p1461 

noncomputable def Ns300p1463 := nat_lit 16657372116581136464931321897736824009339322954214058342868480719212957263308345933787495653279225 

noncomputable def Ns300p1464 := nat_lit 498007915309475657128054366123043435852104567902167511384667897369720898318823652561736860445930690430365952921969068375637248813020949545317345579637 

noncomputable def Ns300p1465 := nat_lit 2443860782243601957090564195424057684517676876201726047655584535317958675016247432668697387177627117191966731815737478104378967597639934504920464761507487437162724668211200000 

noncomputable def Ns300p1466 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz5 qz192 qz193) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz194 qz189) qz179) 

noncomputable def Ns300p1467 := nat_lit 181297439447960576084805654438955483257093878806943685662960410956337530416625 

noncomputable def Ns300p1468 := nat_lit 211822980260192829839757643588479476598307087477400788020692787757807751910350792852626000301300254229424411 

noncomputable def Ns300p1469 := nat_lit 151349335102163624928760776931143348244312676025 

noncomputable def Ns300p1470 := nat_lit 713623846352979940529142984724747568191373312 

noncomputable def Ns300p1471 := nat_lit 2475020251377308186715195691208150700716084455022322648615651523447 

noncomputable def Ns300p1472 := nat_lit 20353803685456524303839545610542776320000000000000000000000000000000000 

noncomputable def Ns300p1473 := nat_lit 403207171637772023441539802960349169576363190776655397434716048924768314284732883459137231511870607367647630850503842201600 

noncomputable def Ns300p1474 := nat_lit 12852274764103591228996506332259564836749622937213991955408740432795125 

noncomputable def Ns300p1475 := nat_lit 53919893334301279589334030174039261347274288845081144962207220498432 

noncomputable def Ns300p1476 := @Enclosure.Real.IsNear.mulLit_tt qz192 qz193 Ns300p1474 Ns300p1475 

noncomputable def Ns300p1477 := nat_lit 136519632513642810160127391201206914323185433713359243802740113304687830921229008443126472750567 

noncomputable def Ns300p1478 := nat_lit 1532495540865888858358347027150309183618739122183602176000000000000000000000000000000000000000000000 

noncomputable def Ns300p1479 := nat_lit 54868110053793817090484712694795163657794946025 

noncomputable def Ns300p1480 := nat_lit 1427247692705959881058285969449495136382746624 

noncomputable def Ns300p1481 := nat_lit 12731915830644770259496694168319396160766912230210162201906479 

noncomputable def Ns300p1482 := nat_lit 1329227995784915872903807060280344576000000000000000000000000000000 

noncomputable abbrev qz199 := qz493

noncomputable abbrev qz200 := qz494

noncomputable def Ns300p1483 := @Enclosure.Real.IsNear.mulLit_ft qz199 qz200 Ns300p1479 Ns300p1480 Ns300p1481 Ns300p1482 

noncomputable def Ns300p1484 := nat_lit 890540490773866279395053223 

noncomputable def Ns300p1485 := nat_lit 1152921504606846976000000000000000 

noncomputable def Ns300p1486 := @Enclosure.Real.IsNear.mulLit_tt qz200 qz200 234239428905113703298605 37778931862957161709568 Ns300p1484 Ns300p1485 234239428905113703298605 37778931862957161709568 

noncomputable abbrev qz733 := (@HSub.hSub Real Real Real qz810 qz858 qz857)

noncomputable abbrev qz500 := qz733

noncomputable abbrev qz201 := qz500

noncomputable def Ns300p1487 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz201 884279719003555 140737488355328 1 500000000000000 264892911 268435456 33 268435456 

noncomputable abbrev qz734 := qz858

noncomputable abbrev qz501 := qz734

noncomputable abbrev qz202 := qz501

noncomputable def Ns300p1488 := @Enclosure.Real.IsNear.subLit_ff_n qz202 qz187 3542545 268435456 33 268435456 1 1 0 1 264892911 

noncomputable def Ns300p1489 := @Enclosure.Real.IsNear.mulLit_ff qz0 qz182 2 1 0 1 3542545 536870912 33 536870912 3542545 268435456 33 

noncomputable def Ns300p1490 := @Enclosure.Real.IsNear.recentre' qz193 Bool.true 112850024 268435456 

noncomputable abbrev qz735 := (@Nat.cast Real Real.instNatCast 134217728)

noncomputable def Ns300p1491 := @Enclosure.Real.IsNear.sin_image qz183 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 58235077)) qz735) Bool.true 58235077 134217728 

noncomputable def Ns300p1492 := nat_lit 17600472066260832516160741576445 

noncomputable def Ns300p1493 := nat_lit 40564819207303340847894502572032 

noncomputable def Ns300p1494 := nat_lit 484414873301553679201321508496890293 

noncomputable def Ns300p1495 := @Enclosure.Real.IsNear.recentre' qz183 Bool.true Ns300p1492 Ns300p1493 Ns300p1494 

noncomputable def Ns300p1496 := nat_lit 1237940039285380274899124224000000000000000 

noncomputable def Ns300p1497 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz184 884279719003555 140737488355328 1 500000000000000 19903738249355999 

noncomputable def Ns300p1498 := @Enclosure.Real.IsNear.subLit_tf qz185 qz27 1889339739874015 288230376151711744 17950549155 288230376151711744 1 16 

noncomputable def Ns300p1499 := @Enclosure.Real.IsNear.subLit_ff_n qz186 qz182 12549625077025 288230376151711744 233809059 288230376151711744 3542545 536870912 33 536870912 

noncomputable def Ns300p1500 := @Enclosure.Real.IsNear.mulLit_ff qz182 qz182 3542545 536870912 33 536870912 3542545 536870912 33 536870912 12549625077025 288230376151711744 

noncomputable def Ns300p1501 := nat_lit 11501079783356018764658982173041 

noncomputable def Ns300p1502 := nat_lit 38942226439011207213978722469150720 

noncomputable def Ns300p1503 := nat_lit 272595585073078450497851057284055040 

noncomputable def Ns300p1504 := BSN.sin_dyadic_bound_f 58235077 134217728 2 1 268435456 70560000 Ns300p1501 Ns300p1502 Ns300p1501 Ns300p1501 Ns300p1503 Ns300p1501 112850024 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 58235077) (BSN.sinEvenQ 134217728) 0 1 Ns300p1501 Ns300p1502 Ns300p1501 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 58235077) (BSN.sinOddQ 134217728) 0 1 Ns300p1501 Ns300p1503 Ns300p1501 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1505 := @Ns300p1490 15425030912 37881611550720000 14106253 33554432 60254027 147975045120000 (@Ns300p1491 211 536870912 Bool.true 112850024 268435456 1 70560000 (@Ns300p1495 Ns300p1496 58235077 134217728 211 536870912 (@Ns300p1497 288230376151711744 17950549155 288230376151711744 Ns300p1492 Ns300p1493 Ns300p1494 Ns300p1496 RS301to312.d64 (@Ns300p1498 0 1 318459811989695984 19903738249355999 288230376151711744 17950549155 288230376151711744 (@Ns300p1499 1014331549224005198151680 1889339739874015 288230376151711744 17950549155 288230376151711744 (@Ns300p1500 233809059 288230376151711744 (Ns300p1437 rfl rfl) (Ns300p1437 rfl rfl) rfl) (Ns300p1437 rfl rfl) rfl rfl) qz358 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 58235077 134217728) (BSN.sin_neg_of_bound 58235077 134217728 Bool.false 112850024 268435456 1 70560000 (Ns300p1504 rfl rfl)) rfl rfl) 

noncomputable def Ns300p1506 := nat_lit 621399529115301433157092445121664622325 

noncomputable def Ns300p1507 := nat_lit 2658455991569831745807614120560689152 

noncomputable def Ns300p1508 := nat_lit 72096578700705327883205478037337107303760386268791923 

noncomputable def Ns300p1509 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz194 qz189) qz179 Ns300p1506 Ns300p1507 Ns300p1508 

noncomputable def Ns300p1510 := nat_lit 2475880078570760549798248448000000000000000000000000000000 

noncomputable def Ns300p1511 := nat_lit 2671621472321598838185159669 

noncomputable def Ns300p1512 := @Enclosure.Real.IsNear.mulLit_tf qz194 qz189 702718286715341109895815 37778931862957161709568 Ns300p1511 Ns300p1485 884279719003555 

noncomputable def Ns300p1513 := @Enclosure.Real.IsNear.mulLit_ft qz319 qz200 3 1 0 1 234239428905113703298605 37778931862957161709568 Ns300p1484 

noncomputable def Ns300p1514 := @Enclosure.Real.IsNear.recentre' qz179 Bool.false 243562037 268435456 

noncomputable def Ns300p1515 := @Enclosure.Real.IsNear.cos_image qz183 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 58235077)) qz735) Bool.true 58235077 134217728 

noncomputable def Ns300p1516 := nat_lit 6270419419868359696613544203876761121753517788996540077557363540961 

noncomputable def Ns300p1517 := nat_lit 4246191600076225767660054876205591831097850246550140165773818614251520 

noncomputable def Ns300p1518 := nat_lit 132274836183120527522302858880227813194128439387033838467187681 

noncomputable def Ns300p1519 := nat_lit 18810993709932712848785588005912522909634165110110846164995156247521 

noncomputable def Ns300p1520 := nat_lit 191078622003430159544702469429251632399403261094756307459821837641318400 

noncomputable def Ns300p1521 := BSN.cos_dyadic_bound_f 58235077 134217728 3 2 268435456 70560000 Ns300p1516 Ns300p1517 Ns300p1518 Ns300p1519 Ns300p1520 Ns300p1518 243562037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 58235077) (BSN.cosEvenQ 134217728) 0 2 Ns300p1516 Ns300p1517 Ns300p1518 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 58235077) (BSN.cosOddQ 134217728) 0 2 Ns300p1519 Ns300p1520 Ns300p1518 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1522 := @Ns300p1514 15425030912 37881611550720000 243562037 268435456 60254027 147975045120000 (@Ns300p1515 211 536870912 Bool.false 243562037 268435456 1 70560000 (@Ns300p1495 Ns300p1496 58235077 134217728 211 536870912 (@Ns300p1497 288230376151711744 17950549155 288230376151711744 Ns300p1492 Ns300p1493 Ns300p1494 Ns300p1496 RS301to312.d64 (@Ns300p1498 0 1 318459811989695984 19903738249355999 288230376151711744 17950549155 288230376151711744 (@Ns300p1499 1014331549224005198151680 1889339739874015 288230376151711744 17950549155 288230376151711744 (@Ns300p1500 233809059 288230376151711744 (Ns300p1437 rfl rfl) (Ns300p1437 rfl rfl) rfl) (Ns300p1437 rfl rfl) rfl rfl) qz358 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 58235077 134217728) (BSN.cos_neg_of_bound 58235077 134217728 Bool.false 243562037 268435456 1 70560000 (Ns300p1521 rfl rfl)) rfl rfl) 

noncomputable abbrev qz203 := (@Ns300p1487 234239428905113703298605 37778931862957161709568 Ns300p1484 Ns300p1485 RS301to312.d64 (@Ns300p1488 264892911 268435456 33 268435456 (@Ns300p1489 268435456 qz324 (Ns300p1437 rfl rfl) rfl) qz727 rfl rfl) rfl)

noncomputable abbrev qz502 := (Enclosure.Real.IsNear.const Bool.false 3 1)

noncomputable def Ns300p1523 := @Ns300p1466 Ns300p1467 Ns300p1459 Ns300p1468 Ns300p1461 Ns300p1469 Ns300p1470 Ns300p1471 Ns300p1472 Ns300p1473 Ns300p1458 Ns300p1459 Ns300p1460 Ns300p1461 (@Ns300p1476 Ns300p1477 Ns300p1478 14106253 33554432 60254027 147975045120000 Ns300p1467 Ns300p1459 Ns300p1468 Ns300p1461 (@Ns300p1483 234239428905113703298605 37778931862957161709568 Ns300p1484 Ns300p1485 Ns300p1474 Ns300p1475 Ns300p1477 Ns300p1478 (@Ns300p1486 Ns300p1484 Ns300p1485 Ns300p1479 Ns300p1480 Ns300p1481 Ns300p1482 qz203 qz203 rfl) qz203 rfl) (Ns300p1505 rfl) rfl) (@Ns300p1509 Ns300p1510 243562037 268435456 60254027 147975045120000 Ns300p1469 Ns300p1470 Ns300p1471 Ns300p1472 (@Ns300p1512 70368744177664 1 250000000000000 Ns300p1506 Ns300p1507 Ns300p1508 Ns300p1510 (@Ns300p1513 Ns300p1485 702718286715341109895815 37778931862957161709568 Ns300p1511 Ns300p1485 qz502 qz203 rfl) RS301to312.d66 rfl) (Ns300p1522 rfl) rfl) rfl rfl 

noncomputable def Ns300p1524 := nat_lit 1611143642304024488600843703081359 

noncomputable def Ns300p1525 := nat_lit 211849326471508131840000000000000000000 

noncomputable def Ns300p1526 := nat_lit 2257432569884316207530996043734069762870129707827084912833985856326050707815 

noncomputable def Ns300p1527 := @Enclosure.Real.IsNear.mulLit_tf qz195 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz182) 7378901296455891814815 9444732965739290427392 Ns300p1524 Ns300p1525 Ns300p1526 

noncomputable def Ns300p1528 := nat_lit 452312848583266388373324160190187140051835877600158453279131187530910662656 

noncomputable def Ns300p1529 := nat_lit 1968735953342563132814568009683049917757982859081434048346963551034683823277691771802369400604363641006488141843 

noncomputable def Ns300p1530 := nat_lit 21409722666744337943118762691316214571578470728130461729848170834917588992000000000000000000000000000000000000000000 

noncomputable abbrev qz204 := qz495

noncomputable def Ns300p1531 := @Enclosure.Real.IsNear.mulLit_ft qz319 qz204 3 1 0 1 2459633765485297271605 9444732965739290427392 Ns300p1524 

noncomputable def Ns300p1532 := nat_lit 635547979414524395520000000000000000000 

noncomputable def Ns300p1533 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz197 884279719003555 140737488355328 1 500000000000000 2781511 67108864 59702777 147975045120000 2459633765485297271605 

noncomputable def Ns300p1534 := @Enclosure.Real.IsNear.recentre' qz197 Bool.false 11126044 268435456 15283910912 37881611550720000 2781511 67108864 59702777 147975045120000 

noncomputable def Ns300p1535 := @Enclosure.Real.IsNear.sin_image qz181 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11129233) qz732) Bool.false 11129233 268435456 209 536870912 Bool.false 11126044 268435456 1 

noncomputable def Ns300p1536 := BSN.sin_dyadic_bound_f 11129233 268435456 1 0 268435456 70560000 0 1 1 0 1 1 11126044 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 11129233) qz344 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 11129233) qz345 0 0 rfl) rfl rfl 

noncomputable abbrev qz503 := (@HMul.hMul Real Real Real qz623 qz621 qz731)

noncomputable abbrev qz205 := qz503

noncomputable abbrev qz504 := (@Enclosure.Real.IsNear.neg qz205 Bool.false 2459633765485297271605 9444732965739290427392 Ns300p1524 Ns300p1532 (@Ns300p1533 9444732965739290427392 Ns300p1524 Ns300p1532 RS301to312.d64 (Ns300p1534 (@Ns300p1535 70560000 (Ns300p1438 rfl) (Enclosure.sfrac_false_div 11129233 268435456) (Ns300p1536 rfl rfl) rfl rfl) rfl) rfl))

noncomputable def Ns300p1537 := @Ns300p1531 Ns300p1532 7378901296455891814815 9444732965739290427392 Ns300p1524 Ns300p1525 qz502 qz504 rfl 

noncomputable abbrev qz206 := (@HMul.hMul Real Real Real qz327 qz493 (Real.cos qz481))

noncomputable def Ns300p1538 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz206) (@HMul.hMul Real Real Real qz5 qz189 qz193) 

noncomputable abbrev qz207 := (@HMul.hMul Real Real Real qz327 qz317 qz495)

noncomputable abbrev qz208 := (@HMul.hMul Real Real Real qz327 qz496 qz472)

noncomputable def Ns300p1539 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz182) (@HMul.hMul Real Real Real qz5 qz178 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns300p1538 (@HMul.hMul Real Real Real qz5 qz207 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c8 1 Zeta.RiemannSiegel.correction qz182))) qz208)) 

noncomputable def Ns300p1540 := @Enclosure.Real.IsNear.mulLit_ff qz178 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns300p1538 (@HMul.hMul Real Real Real qz5 qz207 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 1 Zeta.RiemannSiegel.correction qz182))) qz208) 33583291 

noncomputable def Ns300p1541 := nat_lit 67218920560355928414847611085348060821976312798739257353723488752965 

noncomputable def Ns300p1542 := nat_lit 13479973333575319897333507543509815336818572211270286240551805124608 

noncomputable def Ns300p1543 := nat_lit 21499352924413343803258349049487237792467479363052566509189453952564708813505483289515518511179197545317 

noncomputable def Ns300p1544 := nat_lit 239272296429548464079783439911710633764920429082182739636095287296000000000000000000000000000000000000000000 

noncomputable def Ns300p1545 := nat_lit 415638030902340715842911634890237294239445819816597615005595660200635 

noncomputable def Ns300p1546 := @Enclosure.Real.IsNear.subLit_tt_p (@HSub.hSub Real Real Real qz11 Ns300p1538 (@HMul.hMul Real Real Real qz5 qz207 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz182))) qz208 Ns300p1545 Ns300p1542 

noncomputable def Ns300p1547 := nat_lit 10714748768692008267919609778908231684153677353574795621665785112247712553813888771082216253968706665317 

noncomputable def Ns300p1548 := nat_lit 857726248182715956605476119235450047748909221594958425 

noncomputable def Ns300p1549 := nat_lit 23945242826029513411849172299223580994042798784118784 

noncomputable def Ns300p1550 := nat_lit 1629022563965982838529456483397090421561707412470927337601773326506343254818675999 

noncomputable def Ns300p1551 := nat_lit 36142260224628617659908400211524383283704810700800000000000000000000000000000000000000 

noncomputable def Ns300p1552 := nat_lit 1609573375321310554568753891369827388226453875761582904617273702871727602566721820495505550620358602283579269282592194560 

noncomputable def Ns300p1553 := nat_lit 11339786967565565519199146815580310084188777824927167805 

noncomputable def Ns300p1554 := nat_lit 383123885216472214589586756787577295904684780545900544 

noncomputable def Ns300p1555 := nat_lit 2897433030178805927996091996200068832691603005402811360310070798740583745779 

noncomputable def Ns300p1556 := nat_lit 98346286325520048054172517582379274241373634560000000000000000000000000000000000 

noncomputable def Ns300p1557 := @Enclosure.Real.IsNear.subLit_tf Ns300p1538 (@HMul.hMul Real Real Real qz5 qz207 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz182)) Ns300p1553 Ns300p1554 Ns300p1555 Ns300p1556 

noncomputable def Ns300p1558 := nat_lit 16654746827425968322251395046745658440366437200351758304122029746875 

noncomputable def Ns300p1559 := nat_lit 3665418480947235081457213340459082997408843492622442654749505647118562291017371038859803050922306665317 

noncomputable def Ns300p1560 := nat_lit 159240857243028915664502146448995110465707304139456900377218758613347730195415783567918931690883897460548464782865795645440 

noncomputable def Ns300p1561 := @Enclosure.Real.IsNear.subLit_tt_n (@Neg.neg Real Real.instNeg qz206) (@HMul.hMul Real Real Real qz5 qz189 qz193) 

noncomputable def Ns300p1562 := nat_lit 13363788651042201668563869941304069358240907982154052925 

noncomputable def Ns300p1563 := nat_lit 266022700237583665988917411162376371776611875376067841792774088748953749531 

noncomputable def Ns300p1564 := nat_lit 10927365147280005339352501953597697137930403840000000000000000000000000000000000 

noncomputable def Ns300p1565 := nat_lit 1626019716854943555627156879340109 

noncomputable def Ns300p1566 := nat_lit 317773989707262197760000000000000000000 

noncomputable def Ns300p1567 := nat_lit 26775314949256819602958325225864261471977949613197607387942682465707638128640 

noncomputable def Ns300p1568 := @Enclosure.Real.IsNear.neg qz206 Bool.false Ns300p1562 

noncomputable def Ns300p1569 := @Enclosure.Real.IsNear.mulLit_ff qz199 qz179 Ns300p1479 Ns300p1480 Ns300p1481 

noncomputable def Ns300p1570 := @Enclosure.Real.IsNear.mulLit_ft qz189 qz193 884279719003555 70368744177664 1 

noncomputable def Ns300p1571 := nat_lit 6771230360036917407952617369273886391756899375 

noncomputable def Ns300p1572 := @Enclosure.Real.IsNear.mulLit_tt qz207 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz182) 2459633765485297271605 4722366482869645213696 Ns300p1524 Ns300p1566 Ns300p1571 

noncomputable def Ns300p1573 := nat_lit 2854495385411919762116571938898990272765493248 

noncomputable def Ns300p1574 := nat_lit 4759198620403645543134980337259895746435174302477943829817523363 

noncomputable def Ns300p1575 := nat_lit 752963754679762867914758337740091318410516889600000000000000000000000 

noncomputable def Ns300p1576 := @Enclosure.Real.IsNear.mulLit_ft qz0 qz204 2 1 0 1 2459633765485297271605 9444732965739290427392 Ns300p1524 

noncomputable def Ns300p1577 := @Ns300p1576 Ns300p1532 2459633765485297271605 4722366482869645213696 Ns300p1524 Ns300p1566 qz324 qz504 rfl 

noncomputable abbrev qz209 := (@HMul.hMul Real Real Real qz327 qz494 (Real.sin qz481))

noncomputable def Ns300p1578 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz209) (@HMul.hMul Real Real Real qz5 qz204 qz169) 

noncomputable def Ns300p1579 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz182) (@HMul.hMul Real Real Real qz5 qz178 Ns300p1578) Bool.true Ns300p1571 Ns300p1573 Ns300p1574 Ns300p1575 (BSN.deriv_correction_mk qz182 qz198) 

noncomputable def Ns300p1580 := nat_lit 201624979518443186760720304906207268125 

noncomputable def Ns300p1581 := nat_lit 85070591730234615865843651857942052864 

noncomputable def Ns300p1582 := nat_lit 45050880300124992574708099390128412167288819956114186197 

noncomputable def Ns300p1583 := @Enclosure.Real.IsNear.mulLit_ft qz178 Ns300p1578 33583291 33554432 109 268435456 Ns300p1580 Ns300p1581 Ns300p1582 

noncomputable def Ns300p1584 := nat_lit 8415025711205931766868662138358779084800000000000000000000000 

noncomputable def Ns300p1585 := @Enclosure.Real.IsNear.subLit_tt_n (@Neg.neg Real Real.instNeg qz209) (@HMul.hMul Real Real Real qz5 qz204 qz169) 

noncomputable def Ns300p1586 := nat_lit 3304240646711046892497056677065 

noncomputable def Ns300p1587 := nat_lit 1267650600228229401496703205376 

noncomputable def Ns300p1588 := nat_lit 316484638814544036662557433609385396511 

noncomputable def Ns300p1589 := nat_lit 111070059677094055426129920000000000000000000 

noncomputable def Ns300p1590 := nat_lit 20118856664960506445487292035239736035 

noncomputable def Ns300p1591 := nat_lit 21072984001440035320375237718223025413146450381038346197 

noncomputable def Ns300p1592 := nat_lit 255590026307558965165418481524147992453696152763536352241715773440000 

noncomputable def Ns300p1593 := @Enclosure.Real.IsNear.neg qz209 Bool.false Ns300p1586 

noncomputable def Ns300p1594 := @Enclosure.Real.IsNear.mulLit_tt qz200 qz193 234239428905113703298605 37778931862957161709568 Ns300p1484 

noncomputable def Ns300p1595 := @Enclosure.Real.IsNear.mulLit_tf qz204 qz169 2459633765485297271605 9444732965739290427392 Ns300p1524 Ns300p1532 8179614765123767 9007199254740992 

noncomputable def Ns300p1596 := @Enclosure.Real.IsNear.of_eq qz169 (@HMul.hMul Real Real Real qz5 qz178 qz179) Bool.false 8179614765123767 

noncomputable def Ns300p1597 := @Enclosure.Real.IsNear.mulLit_ff qz178 qz179 33583291 33554432 109 

noncomputable abbrev qz505 := (@Ns300p1596 9007199254740992 10274321398227683 13240582904469258240000 qz188 (@Ns300p1597 268435456 243562037 268435456 60254027 147975045120000 8179614765123767 9007199254740992 10274321398227683 13240582904469258240000 (@Ns300p1429 268435456 (Ns300p1441 rfl rfl rfl rfl rfl) rfl) (Ns300p1522 rfl) rfl))

noncomputable def Ns300p1598 := @Ns300p1595 10274321398227683 13240582904469258240000 Ns300p1590 Ns300p1581 Ns300p1591 Ns300p1584 qz504 qz505 

noncomputable abbrev qz506 := (@Ns300p1429 268435456 (Ns300p1441 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns300p1599 := @Ns300p1572 Ns300p1573 Ns300p1574 Ns300p1575 Ns300p1558 Ns300p1542 Ns300p1559 Ns300p1544 Ns300p1577 (Ns300p1579 (@Ns300p1583 Ns300p1584 Ns300p1571 Ns300p1573 Ns300p1574 Ns300p1575 qz506 (@Ns300p1585 Ns300p1586 Ns300p1587 Ns300p1588 Ns300p1589 Ns300p1590 Ns300p1581 Ns300p1591 Ns300p1584 Ns300p1592 Ns300p1580 Ns300p1581 Ns300p1582 Ns300p1584 (@Ns300p1593 Ns300p1587 Ns300p1588 Ns300p1589 (@Ns300p1594 Ns300p1485 14106253 33554432 60254027 147975045120000 Ns300p1586 Ns300p1587 Ns300p1588 Ns300p1589 qz203 (Ns300p1505 rfl) rfl)) (Ns300p1598 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns300p1600 := @Ns300p1557 Ns300p1558 Ns300p1542 Ns300p1559 Ns300p1544 Ns300p1560 Ns300p1545 Ns300p1542 Ns300p1547 Ns300p1544 (@Ns300p1561 Ns300p1562 Ns300p1554 Ns300p1563 Ns300p1564 12473873439033054729415 2361183241434822606848 Ns300p1565 Ns300p1566 Ns300p1567 Ns300p1553 Ns300p1554 Ns300p1555 Ns300p1556 (@Ns300p1568 Ns300p1554 Ns300p1563 Ns300p1564 (@Ns300p1569 Ns300p1482 243562037 268435456 60254027 147975045120000 Ns300p1562 Ns300p1554 Ns300p1563 Ns300p1564 (@Ns300p1486 Ns300p1484 Ns300p1485 Ns300p1479 Ns300p1480 Ns300p1481 Ns300p1482 qz203 qz203 rfl) (Ns300p1522 rfl) rfl)) (@Ns300p1570 250000000000000 14106253 33554432 60254027 147975045120000 12473873439033054729415 2361183241434822606848 Ns300p1565 Ns300p1566 RS301to312.d66 (Ns300p1505 rfl) rfl) rfl rfl) Ns300p1599 

noncomputable def Ns300p1601 := nat_lit 104861447979174795498261780586560017775 

noncomputable def Ns300p1602 := nat_lit 43478443893141384572243880686876994909750623228796933626153 

noncomputable def Ns300p1603 := nat_lit 2729657786624263506152568913920000000000000000000000000000000000 

noncomputable abbrev qz210 := qz496

noncomputable def Ns300p1604 := @Enclosure.Real.IsNear.mulLit_tf qz210 qz169 Ns300p1601 Ns300p1507 Ns300p1602 Ns300p1603 8179614765123767 9007199254740992 

noncomputable def Ns300p1605 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz180 Ns300p1374 Ns300p1378 Ns300p1376 Ns300p1379 134102391 134217728 59702777 147975045120000 Ns300p1601 

noncomputable abbrev qz507 := (@HMul.hMul Real Real Real qz623 qz728 qz721)

noncomputable abbrev qz211 := qz507

noncomputable def Ns300p1606 := @Ns300p1604 10274321398227683 13240582904469258240000 Ns300p1548 Ns300p1549 Ns300p1550 Ns300p1551 (@Enclosure.Real.IsNear.neg qz211 Bool.false Ns300p1601 Ns300p1507 Ns300p1602 Ns300p1603 (@Ns300p1605 Ns300p1507 Ns300p1602 Ns300p1603 RS301to312.d68 qz499 rfl)) qz505 

noncomputable def Ns300p1607 := nat_lit 314584343937524386494785341759680053325 

noncomputable def Ns300p1608 := nat_lit 909885928874754502050856304640000000000000000000000000000000000 

noncomputable def Ns300p1609 := @Enclosure.Real.IsNear.mulLit_tt qz196 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz182) Ns300p1607 Ns300p1507 Ns300p1602 Ns300p1608 Ns300p1571 

noncomputable def Ns300p1610 := @Enclosure.Real.IsNear.mulLit_ft qz319 qz210 3 1 0 1 Ns300p1601 Ns300p1507 Ns300p1602 

noncomputable def Ns300p1611 := @Ns300p1610 Ns300p1603 Ns300p1607 Ns300p1507 Ns300p1602 Ns300p1608 qz502 (@Enclosure.Real.IsNear.neg qz211 Bool.false Ns300p1601 Ns300p1507 Ns300p1602 Ns300p1603 (@Ns300p1605 Ns300p1507 Ns300p1602 Ns300p1603 RS301to312.d68 qz499 rfl)) rfl 

noncomputable def Ns300p1612 := @Ns300p1609 Ns300p1573 Ns300p1574 Ns300p1575 Ns300p1453 Ns300p1454 Ns300p1455 Ns300p1456 Ns300p1611 (Ns300p1579 (@Ns300p1583 Ns300p1584 Ns300p1571 Ns300p1573 Ns300p1574 Ns300p1575 qz506 (@Ns300p1585 Ns300p1586 Ns300p1587 Ns300p1588 Ns300p1589 Ns300p1590 Ns300p1581 Ns300p1591 Ns300p1584 Ns300p1592 Ns300p1580 Ns300p1581 Ns300p1582 Ns300p1584 (@Ns300p1593 Ns300p1587 Ns300p1588 Ns300p1589 (@Ns300p1594 Ns300p1485 14106253 33554432 60254027 147975045120000 Ns300p1586 Ns300p1587 Ns300p1588 Ns300p1589 qz203 (Ns300p1505 rfl) rfl)) (Ns300p1598 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns300p1613 := @Ns300p1451 Ns300p1452 Ns300p1428 Ns300p1453 Ns300p1454 Ns300p1455 Ns300p1456 Ns300p1457 Ns300p1443 Ns300p1425 Ns300p1444 Ns300p1428 (@Ns300p1462 Ns300p1463 Ns300p1425 Ns300p1464 Ns300p1428 Ns300p1465 Ns300p1450 Ns300p1425 Ns300p1452 Ns300p1428 Ns300p1523 (@Ns300p1527 Ns300p1528 Ns300p1529 Ns300p1530 Ns300p1463 Ns300p1425 Ns300p1464 Ns300p1428 Ns300p1537 (@Ns300p1539 Bool.false Ns300p1526 Ns300p1528 Ns300p1529 Ns300p1530 (BSN.iteratedDeriv_two_correction_mk qz182 qz198) (@Ns300p1540 33554432 109 268435456 Ns300p1541 Ns300p1542 Ns300p1543 Ns300p1544 Ns300p1526 Ns300p1528 Ns300p1529 Ns300p1530 qz506 (@Ns300p1546 Ns300p1547 Ns300p1544 Ns300p1548 Ns300p1549 Ns300p1550 Ns300p1551 Ns300p1552 Ns300p1541 Ns300p1542 Ns300p1543 Ns300p1544 (Ns300p1600 rfl rfl) (Ns300p1606 rfl) rfl rfl) rfl)) rfl) rfl rfl) Ns300p1612 

noncomputable def Ns300p1614 := nat_lit 1923312151438510283126404833858740099250705425780125 

noncomputable def Ns300p1615 := nat_lit 187072209578355573530071658587684226515959365500928 

noncomputable def Ns300p1616 := nat_lit 1173312563833549252638245251840782555551842172934636914657509788791409221486806313951 

noncomputable def Ns300p1617 := nat_lit 11723790922822957999011578271672639160320000000000000000000000000000000000000000000000000 

noncomputable def Ns300p1618 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz321 RSCompact.c11) qz197) qz169 Ns300p1614 Ns300p1615 Ns300p1616 Ns300p1617 8179614765123767 9007199254740992 10274321398227683 

noncomputable def Ns300p1619 := @Enclosure.Real.IsNear.mulLit_ff qz729 qz197 Ns300p1380 Ns300p1381 Ns300p1382 Ns300p1383 2781511 67108864 59702777 147975045120000 Ns300p1614 

noncomputable abbrev qz508 := (Ns300p1534 (@Ns300p1535 70560000 (Ns300p1438 rfl) (Enclosure.sfrac_false_div 11129233 268435456) (Ns300p1536 rfl rfl) rfl rfl) rfl)

noncomputable def Ns300p1620 := Ns300p1423 (@Ns300p1427 Ns300p1428 Ns300p1416 Ns300p1417 Ns300p1418 Ns300p1419 qz506 (@Ns300p1442 Ns300p1443 Ns300p1425 Ns300p1444 Ns300p1428 Ns300p1445 Ns300p1446 Ns300p1447 Ns300p1448 Ns300p1449 Ns300p1424 Ns300p1425 Ns300p1426 Ns300p1428 (Ns300p1613 rfl rfl) (@Ns300p1618 13240582904469258240000 Ns300p1445 Ns300p1446 Ns300p1447 Ns300p1448 (@Ns300p1619 Ns300p1615 Ns300p1616 Ns300p1617 RS301to312.d69 qz508 rfl) qz505 rfl) rfl rfl) rfl) 

noncomputable def Ns300p1621 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correctionLinear qz182) (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz182) qz492)) Bool.true Ns300p1411 Ns300p1412 Ns300p1413 Ns300p1414 (BSN.correctionLinear_mk qz182) (@Enclosure.Real.IsNear.neg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz182) qz492) Bool.false Ns300p1411 Ns300p1412 Ns300p1413 Ns300p1414 (@Ns300p1420 Ns300p1412 Ns300p1413 Ns300p1414 Ns300p1620 RS301to312.d70 rfl)) 

noncomputable def Ns300p1622 := @Enclosure.Real.IsNear.inv_image qz177 335765707 33554432 33 33554432 1676615 1676616 16777216 qz479 rfl 

noncomputable def Ns300p1623 := @Ns300p1415 Ns300p1402 Ns300p1407 Ns300p1408 Ns300p1621 (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz177) Bool.false 3353231 33554432 1 33554432 3353231 33554432 1 33554432 (Ns300p1622 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns300p1624 := @Ns300p1404 Ns300p1405 Ns300p1397 Ns300p1393 Ns300p1399 Ns300p1395 (Ns300p1337 qz488 (@Enclosure.Real.IsNear.of_eq qz175 (@Inv.inv Real Real.instInv (Real.sqrt qz177)) Bool.false 662959 2097152 1 16777216 (BSN.rpow_neg_quarter_mk qz176 (BSN.t_div_two_pi_nonneg qz167 629148 1000 qz170)) Ns300p1341) rfl) (@Ns300p1409 Ns300p1410 Ns300p1401 Ns300p1402 Ns300p1403 Ns300p1405 (@Ns300p1342 562949953421312 1922247188094679 155163080911749120000 qz188 (@Ns300p1343 33554432 15222655 16777216 60254027 9248440320000 511226791766985 562949953421312 1922247188094679 155163080911749120000 (@Ns300p1344 33554432 (Ns300p1357 rfl rfl rfl rfl rfl) rfl) (Ns300p1371 rfl) rfl)) (Ns300p1623 rfl) rfl rfl) 

noncomputable def Ns300p1625 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz167) (hardyZApproximantRS qz167) Bool.true Ns300p1392 Ns300p1393 Ns300p1394 Ns300p1395 (@Eq.refl Real (hardyZApproximantRS qz167)) (Ns300p1396 (BSN.hardyZApproximantRS_eq qz167 10 (@BSN.floor_sqrt_eq_dec qz167 629148 1000 10 qz170 rfl rfl rfl)) (@Ns300p1398 Ns300p1399 Ns300p1395 Ns300p1400 Ns300p1392 Ns300p1393 Ns300p1394 Ns300p1395 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz167) qz167 10) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz167) qz167 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz167) qz167 10)) Bool.true 377977535 134217728 42005 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz167) qz167 10) (Ns300p1335 (Ns300p1334 rfl rfl rfl rfl) rfl rfl)) (Ns300p1624 rfl) rfl rfl)) 

theorem RS301to312.d71 : Enclosure.Real.IsNear (hardyZApproximantRS qz167) Bool.true Ns300p1392 Ns300p1393 Ns300p1394 Ns300p1395 := Ns300p1625 

theorem RS301to312.d72 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal (RS301to312.d3 a b h)) (hardyZApproximantRS b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal (RS301to312.d3 a b h)) 

noncomputable def Ns300p1626 := nat_lit 458530089352698006227865918635131306278335019800713750425059187821975517438364245806234840383547667791694297383575578203586242443689 

noncomputable def Ns300p1627 := nat_lit 11356855067118857664833184498250070849275646260739344691898284362197488876771842551971735167402555711886914400097909030211478150447104 

noncomputable def Ns300p1628 := nat_lit 643223772160247058155929649648850086320610070289207276724106585952102434613208948827001554723251416311883792766014342687501205577271173510476631800543116658150122515540486719337883 

noncomputable def Ns300p1629 := nat_lit 511075630626707452854207200958783011266059343558766574187878726971450567506610005267256040420960337284834802151584627163136000000000000000000000000000000000000000000000000000000000000 

noncomputable abbrev qz859 := (Enclosure.sfrac Bool.false 630512 1000)

noncomputable abbrev qz736 := qz859

noncomputable abbrev qz509 := qz736

noncomputable abbrev qz212 := qz509

noncomputable abbrev qz860 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 630512 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz737 := qz860

noncomputable abbrev qz510 := qz737

noncomputable abbrev qz213 := qz510

noncomputable abbrev qz861 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 630512 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz738 := qz861

noncomputable abbrev qz511 := (Zeta.RiemannSiegel.correction qz738)

noncomputable abbrev qz512 := qz738

noncomputable abbrev qz862 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 630512 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz739 := qz862

noncomputable abbrev qz513 := qz739

noncomputable abbrev qz214 := (@HAdd.hAdd Real Real Real qz341 qz511 (@HMul.hMul Real Real Real qz327 (Zeta.RiemannSiegel.correctionLinear qz512) (@Inv.inv Real Real.instInv qz513)))

noncomputable abbrev qz514 := (@HMul.hMul Real Real Real qz5 qz719 (@HPow.hPow Real Real Real qz627 qz213 qz8))

noncomputable def Ns300p1630 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz212) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz212) qz212 10) (@HMul.hMul Real Real Real qz5 qz514 qz214)) Bool.false Ns300p1626 Ns300p1627 Ns300p1628 Ns300p1629 

noncomputable def Ns300p1631 := nat_lit 3159074732606732992283287003932800173035789589081129669130294960090488706245982530517958875687780526219381176156381570869576038450775 

noncomputable def Ns300p1632 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz212) qz212 10) (@HMul.hMul Real Real Real qz5 qz514 qz214) 42753623 134217728 168399 134217728 Ns300p1631 Ns300p1627 

noncomputable def Ns300p1633 := nat_lit 1992346145444391006060755770255298050962655337042892547788314916659902628569644867090610985258028147625075411443271199501205577271173510476631800543116658150122515540486719337883 

noncomputable def Ns300p1634 := nat_lit 61542866812556117066034013887840184910350261980486812360410478454990822422201629108546368510722416550699985865379858622771666912849105518592 

noncomputable def Ns300p1635 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz212) qz212 Real.cos BSN.quadSignPos 9 10 630512 1000 200 268435456 134217728 4503599627370496 Bool.false 305280239206 2477 618095470 62 84886744 8 

noncomputable def Ns300p1636 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz212) qz212 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 630512 1000 110 157 268435456 134217728 4503599627370496 Bool.false 305280239206 2477 

noncomputable def Ns300p1637 := Ns300p1636 558195838 62 94906264 8 589812974 62 89478488 8 Bool.false 99298384 126670 Bool.true 286617893 Bool.true 403702418 14148475504056880 1 Bool.false 129415412 Bool.true Bool.false 267835195 Bool.true Bool.true 35735274 

noncomputable def Ns300p1638 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz212) qz212 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 630512 1000 4 57 268435456 134217728 4503599627370496 Bool.false 305280239206 2477 

noncomputable def Ns300p1639 := Ns300p1638 480971758 62 109588312 8 522351262 62 101459064 8 Bool.false 77414160 93968 Bool.false 335144412 Bool.true 34026288 14148475504056880 1 Bool.false 85023114 Bool.false Bool.false 33935241 Bool.true Bool.false 99298384 

noncomputable def Ns300p1640 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz212) qz212 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 630512 1000 167 77 268435456 134217728 4503599627370496 Bool.false 305280239206 2477 

noncomputable def Ns300p1641 := Ns300p1640 372130544 61 134217720 8 432030192 61 120047984 16 Bool.false 95733349 55162 Bool.false 230675126 Bool.false 412396811 14148475504056880 1 Bool.false 203314743 Bool.false Bool.false 268275733 Bool.true Bool.false 77414160 

noncomputable def Ns300p1642 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz212) qz212 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 630512 1000 445 283 268435456 134217728 4503599627370496 Bool.false 305280239206 2477 

noncomputable def Ns300p1643 := Ns300p1642 186065264 61 189812528 16 294906480 61 154981288 8 Bool.false 268435328 2549 Bool.false 326301892 Bool.false 9112488 14148475504056880 1 Bool.false 251676370 Bool.true Bool.false 9110737 Bool.false Bool.false 95733349 

noncomputable def Ns300p1644 := nat_lit 44191844291621902610342817531226151806307548464584669 

noncomputable def Ns300p1645 := nat_lit 38858256612744831928317932458297048978755158016000 

noncomputable def Ns300p1646 := nat_lit 47830917536269867747512746639360000 

noncomputable def Ns300p1647 := nat_lit 180947857968252300882329849797752913920 

noncomputable abbrev qz863 := (@Eq.refl Real (Enclosure.sfrac Bool.false 630512 1000))

noncomputable abbrev qz740 := qz863

noncomputable abbrev qz515 := qz740

noncomputable abbrev qz215 := qz515

noncomputable def Ns300p1648 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz212 630512 1000 1590182528576 16000000 1261024 4000 2000 Ns300p1646 Ns300p1647 qz215 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns300p1649 := nat_lit 57923134149914660189428537794528741695563429923500417351680 

noncomputable abbrev qz516 := (@HMul.hMul Real Real Real qz623 qz629 (@HSub.hSub Real Real Real qz628 qz630 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz631 (@Nat.cast Real Real.instNatCast 1261024)))))

noncomputable abbrev qz741 := (Real.log (Enclosure.sfrac Bool.false 1590182528576 16000000))

noncomputable abbrev qz742 := (Enclosure.sfrac Bool.false 630512 2000)

noncomputable abbrev qz216 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 630512 4000) qz741) qz516) qz742)

noncomputable abbrev qz517 := (@HSub.hSub Real Real Real qz11 qz216 (@HMul.hMul Real Real Real qz5 qz742 (Real.log Real.pi)))

noncomputable def Ns300p1650 := @Enclosure.Real.IsNear.addLit_ft_p qz517 (Enclosure.sfrac Bool.true Ns300p1646 Ns300p1647) 320109606510422484429 281474976710656000 148737031351434269 16128000000000000000000 Ns300p1646 Ns300p1647 0 1 Ns300p1649 

noncomputable def Ns300p1651 := nat_lit 1342637003025091068130492416000 

noncomputable abbrev qz518 := (@HMul.hMul Real Real Real qz5 qz742 (Real.log Real.pi))

noncomputable def Ns300p1652 := @Enclosure.Real.IsNear.subLit_ff_p qz216 qz518 421689130349943940557 281474976710656000 285050158896899 63000000000000000000 1513652858727 4194304000 39407 8388608000 Ns300p1651 320109606510422484429 281474976710656000 

noncomputable abbrev qz217 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 630512 4000) qz741) qz516)

noncomputable def Ns300p1653 := @Enclosure.Real.IsNear.subLit_ff_p qz217 qz742 510425805607838508493 281474976710656000 285050158896899 63000000000000000000 630512 2000 0 1 843378260699887881114000 421689130349943940557 281474976710656000 285050158896899 63000000000000000000 

noncomputable def Ns300p1654 := nat_lit 287344183491968341799974108519202816 

noncomputable def Ns300p1655 := nat_lit 55643328508025644362235904 

noncomputable def Ns300p1656 := nat_lit 170145706088892576911331736855137489204412190696148771873832441443710667726764574414832793756198578298528263598008372423053803520 

noncomputable def Ns300p1657 := nat_lit 2451558543735850389412839474982012208045443326741234403463978212528151169517986232395776301011676016317558552639602913133461504 

noncomputable def Ns300p1658 := nat_lit 2052441161774489799901813610253782284807411476807204008071119739441365443274374194100378800351666612027154644395695800320 

noncomputable def Ns300p1659 := BSN.log_dyadic_bound 541606528576 2638758528576 6 5 Ns300p1656 134217728 35280000 Ns300p1657 Ns300p1658 55890376 3180365057152 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 541606528576) (BSN.artanhQ 2638758528576) 0 5 Ns300p1657 Ns300p1656 Ns300p1658 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns300p1660 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 630512 4000) qz741 630512 4000 0 1 3238867997891831 281474976710656 781250441 27562500000000000 127634071192923384217 70368744177664000 30786736128487 6890625000000000000 (Enclosure.Real.IsNear.const Bool.false 630512 4000) (BSN.isNear_log_sfrac 1590182528576 16000000 3238867997891831 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1590182528576) qz335)) Bool.false Ns300p1655 Ns300p94 1000000564480000 35280000000000000000000 3238867997891831 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1590182528576 16000000 16 3180365057152 2097152000000 55890376 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns300p1659 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns300p1661 := BSN.arctan_dyadic_bound_f 1000 1261024 1 0 16777216 4410000 0 1 1 0 1 1 13304 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1261024) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1261024) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns300p1662 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1261024))) 884279719003555 562949953421312 1 2000000000000000 13304 16777216 1 4410000 14828262363961629868032 883833310840227 562949953421312 200000000441 882000000000000000 qz16 (Ns300p1661 rfl) rfl rfl 

noncomputable abbrev qz218 := qz516

noncomputable def Ns300p1663 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 630512 4000) qz741) qz218 127634071192923384217 70368744177664000 30786736128487 6890625000000000000 883833310840227 2251799813685248 200000000441 3528000000000000000 Ns300p1654 510425805607838508493 281474976710656000 285050158896899 63000000000000000000 (Ns300p1660 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1261024)))) 1 4 0 1 883833310840227 562949953421312 200000000441 882000000000000000 883833310840227 2251799813685248 200000000441 3528000000000000000 qz340 Ns300p1662 rfl) 

noncomputable def Ns300p1664 := @Ns300p1650 Ns300p1644 Ns300p1645 148737031351434269 16128000000000000000000 (@Ns300p1652 148737031351434269 16128000000000000000000 (Ns300p1653 (Ns300p1663 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 630512 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz742 (Real.log Real.pi) 630512 2000 0 1 38410761 33554432 1 67108864 1513652858727 4194304000 39407 8388608000 (Enclosure.Real.IsNear.const Bool.false 630512 2000) RS301to312.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns300p1646 Ns300p1647) 

noncomputable def Ns300p1665 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz212) Bool.false Ns300p1644 Ns300p1645 148737031351434269 16128000000000000000000 9540007475 8388608 311 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz212) (@HAdd.hAdd Real Real Real qz341 qz517 (Enclosure.sfrac Bool.true Ns300p1646 Ns300p1647)) Bool.false Ns300p1644 Ns300p1645 148737031351434269 16128000000000000000000 Ns300p1648 (Ns300p1664 rfl rfl)) 

noncomputable def Ns300p1666 := BSN.cos_dyadic_bound_f 66850608 68719476736 1 0 33554432 8828614 0 1 1 0 1 1 33554416 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 66850608) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 66850608) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns300p1667 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz212) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9540007475) qz383) Bool.false 9540007475 8388608 311 33554432 Bool.false 33554416 33554432 1 4410000 (Ns300p1665 rfl) (Enclosure.sfrac_false_div 9540007475 8388608) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9540007475) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1176048341373251747840) qz655) 226375608064910080 72057594037927936 Bool.false 33554416 33554432 181 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q0 9540007475 8388608 226375608064910080 72057594037927936 181 1176048341373251747840 Ns300p381 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554416 33554432 1176048341373251747840 Ns300p381 66850608 68719476736 8828614 8820000 (Ns300p1666 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p1668 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz212) Bool.false Ns300p1644 Ns300p1645 148737031351434269 16128000000000000000000 305280239206 268435456 2477 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz212) (@HAdd.hAdd Real Real Real qz341 qz517 (Enclosure.sfrac Bool.true Ns300p1646 Ns300p1647)) Bool.false Ns300p1644 Ns300p1645 148737031351434269 16128000000000000000000 Ns300p1648 (Ns300p1664 rfl rfl)) 

noncomputable def Ns300p1669 := Ns300p1643 55162 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 445 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 251676370 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 283 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 9110737 268435456) qz215 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz212) qz212 1) Bool.false 2097151 2097152 87816527 9248440320000 268435328 268435456 2549 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz212) qz212 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz212)) Bool.false 2097151 2097152 87816527 9248440320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz212) qz212) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz212)) Bool.false 33554416 33554432 1405064432 147975045120000 2097151 2097152 87816527 9248440320000 (Ns300p1667 rfl rfl) rfl)) rfl) (Ns300p1668 rfl) RS301to312.d7 

noncomputable def Ns300p1670 := nat_lit 15871206935641282410898228893432732202867908172761436426553369468063969846152959067007579537672725562587611136 

noncomputable def Ns300p1671 := nat_lit 1456917982090610220864183853303640183730957399713288784172660725868997843012374762939173959188281819136 

noncomputable def Ns300p1672 := nat_lit 79320635655806624083847886855350166758437628536133263744805788035181240193436345127099687923830273505488797696 

noncomputable def Ns300p1673 := BSN.sin_dyadic_bound_f 326301892 268435456 4 3 268435456 134217728 Ns300p1670 Ns300p237 Ns300p1671 Ns300p1672 Ns300p240 Ns300p1671 251676370 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 326301892) qz344 0 3 Ns300p1670 Ns300p237 Ns300p1671 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 326301892) qz345 0 3 Ns300p1672 Ns300p240 Ns300p1671 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1674 := BSN.sin_dyadic_bound_f 9112488 268435456 1 0 268435456 134217728 0 1 1 0 1 1 9110737 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 9112488) qz344 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 9112488) qz345 0 0 rfl) rfl rfl 

noncomputable def Ns300p1675 := nat_lit 44465448313546143962985340594063103196424455822531317513401841682407680 

noncomputable def Ns300p1676 := nat_lit 8016893827935969754725084725425561401260862155715176830603818885376 

noncomputable def Ns300p1677 := nat_lit 116444146802613718809168241894895533653128676234568007010707655366205696 

noncomputable def Ns300p1678 := BSN.sin_dyadic_bound_f 230675126 268435456 3 2 268435456 134217728 Ns300p1675 Ns300p116 Ns300p1676 Ns300p1677 Ns300p119 Ns300p1676 203314743 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 230675126) qz344 0 2 Ns300p1675 Ns300p116 Ns300p1676 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 230675126) qz345 0 2 Ns300p1677 Ns300p119 Ns300p1676 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1679 := nat_lit 40539542354758925463265490322390008382273111109764769763000483672266552577441820056604401685590770537914149521 

noncomputable def Ns300p1680 := nat_lit 24198228841804311031799613693784204216528369959337978269346579826242887147458056025475379045679213554321 

noncomputable def Ns300p1681 := nat_lit 202467213420438160916788035849746661565654258057643512945910665616328426162373712621575547749347343230765083281 

noncomputable def Ns300p1682 := BSN.sin_dyadic_bound_f 412396811 268435456 4 3 268435456 134217728 Ns300p1679 Ns300p237 Ns300p1680 Ns300p1681 Ns300p240 Ns300p1680 268275733 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 412396811) qz344 0 3 Ns300p1679 Ns300p237 Ns300p1680 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 412396811) qz345 0 3 Ns300p1681 Ns300p240 Ns300p1680 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1683 := Ns300p1641 93968 BSN.abs_quadSignPos (BSN.cos_quad_nat3 167 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 203314743 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 77 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268275733 268435456) qz215 rfl rfl (Ns300p1669 RS301to312.d9 RS301to312.d11 RS301to312.d13 RS301to312.d17 (Ns300p1673 rfl rfl) (Ns300p1674 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns300p1668 rfl) RS301to312.d19 RS301to312.d21 RS301to312.d23 RS301to312.d25 RS301to312.d17 (Ns300p1678 rfl rfl) (Ns300p1682 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns300p1684 := nat_lit 6798302375559265814432567270308409203459927833665354543162393345430220832701080836432798561810848996587995136 

noncomputable def Ns300p1685 := nat_lit 2008092857592120033812581617742946557908953316740849210367823284876746321037319442294783038486694854656 

noncomputable def Ns300p1686 := nat_lit 41203315078302890009323172412607353763111478287234655584016214022010999596397190736454186498991022761679257600 

noncomputable def Ns300p1687 := BSN.cos_dyadic_bound_f 335144412 268435456 4 3 268435456 134217728 Ns300p1684 Ns300p122 Ns300p1685 Ns300p1686 Ns300p125 Ns300p1685 85023114 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 335144412) qz342 0 3 Ns300p1684 Ns300p122 Ns300p1685 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 335144412) qz343 0 3 Ns300p1686 Ns300p125 Ns300p1685 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1688 := nat_lit 1340473689863964969166674395136 

noncomputable def Ns300p1689 := BSN.sin_dyadic_bound_f 34026288 268435456 2 1 268435456 134217728 Ns300p1688 Ns300p392 Ns300p1688 Ns300p1688 Ns300p393 Ns300p1688 33935241 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 34026288) qz344 0 1 Ns300p1688 Ns300p392 Ns300p1688 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 34026288) qz345 0 1 Ns300p1688 Ns300p393 Ns300p1688 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1690 := Ns300p1639 126670 BSN.abs_quadSignPos (BSN.cos_quad_nat0 4 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 85023114 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 33935241 268435456) qz215 rfl rfl (Ns300p1683 rfl rfl) (Ns300p1668 rfl) RS301to312.d27 RS301to312.d29 RS301to312.d31 RS301to312.d33 RS301to312.d17 (Ns300p1687 rfl rfl) (Ns300p1689 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p1691 := nat_lit 3634074665384079531769544730759501262780504805733958896840175355058936504674235563567387371437804764601481681 

noncomputable def Ns300p1692 := nat_lit 307354509067229467525206456341813326919149360212635717200059709400024324302515848207402122409609230801 

noncomputable def Ns300p1693 := nat_lit 22035355910998676940695197568831460693865005894700757364760630779115092337251294038173139186921809913948109265 

noncomputable def Ns300p1694 := BSN.cos_dyadic_bound_f 286617893 268435456 4 3 268435456 134217728 Ns300p1691 Ns300p122 Ns300p1692 Ns300p1693 Ns300p125 Ns300p1692 129415412 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 286617893) qz342 0 3 Ns300p1691 Ns300p122 Ns300p1692 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 286617893) qz343 0 3 Ns300p1693 Ns300p125 Ns300p1692 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1695 := nat_lit 37221833579515902081562836108457412129186305607070920422423079945385393557705901271287578248849329812041240576 

noncomputable def Ns300p1696 := nat_lit 18738559747946481108597534481888580453620816523096125705641443934569436871971936119122298750397423947776 

noncomputable def Ns300p1697 := nat_lit 185914801428230972699281519083623853577474939482915572671419060693004129052629336371288366379019665536463015936 

noncomputable def Ns300p1698 := BSN.sin_dyadic_bound_f 403702418 268435456 4 3 268435456 134217728 Ns300p1695 Ns300p237 Ns300p1696 Ns300p1697 Ns300p240 Ns300p1696 267835195 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 403702418) qz344 0 3 Ns300p1695 Ns300p237 Ns300p1696 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 403702418) qz345 0 3 Ns300p1697 Ns300p240 Ns300p1696 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1699 := Ns300p1637 155243 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 110 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 129415412 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 157 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267835195 268435456) qz215 rfl rfl (Ns300p1690 rfl) (Ns300p1668 rfl) RS301to312.d35 RS301to312.d37 RS301to312.d39 RS301to312.d41 RS301to312.d17 (Ns300p1694 rfl rfl) (Ns300p1698 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p1700 := nat_lit 1055715549604735913068760486526582525065513839962662912470405369227841 

noncomputable def Ns300p1701 := nat_lit 14646848642673675571525082661206400788750070444433118091635780161 

noncomputable def Ns300p1702 := nat_lit 3167117355116922391855138409414425162394964019747099871175032836123201 

noncomputable def Ns300p1703 := BSN.cos_dyadic_bound_f 104886121 268435456 3 2 268435456 134217728 Ns300p1700 Ns300p110 Ns300p1701 Ns300p1702 Ns300p113 Ns300p1701 248203690 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 104886121) qz342 0 2 Ns300p1700 Ns300p110 Ns300p1701 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 104886121) qz343 0 2 Ns300p1702 Ns300p113 Ns300p1701 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1704 := Ns300p1635 Bool.true 35735274 155243 Bool.true 104886121 14148475504056880 1 Bool.false 248203690 Bool.false Bool.false 42753623 168399 BSN.abs_quadSignPos (BSN.cos_quad_nat0 200 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 248203690 268435456) qz215 rfl (Ns300p1699 rfl) (Ns300p1668 rfl) RS301to312.d58 RS301to312.d60 RS301to312.d17 (Ns300p1703 rfl rfl) rfl 

noncomputable def Ns300p1705 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz212) qz212 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz212) qz212 10) 42753623 268435456 168399 268435456 42753623 268435456 168399 268435456 22953176571314176 42753623 134217728 168399 134217728 (Ns300p1704 rfl rfl rfl rfl) 

noncomputable def Ns300p1706 := nat_lit 297980855593888300880846698742897670572628459024652184120674482914563835888401266347924825678511120084328867639769341567456925 

noncomputable def Ns300p1707 := nat_lit 338460656020607282663380637712778772392143197677711984273740183180495765112991409062496875745134225841966700556811959451779072 

noncomputable def Ns300p1708 := nat_lit 90718646598195885801381183902244897580506428129461259503224461982669301182809555211322770311547739193119193350233503062495759545992701429279424069405275120342469836430354297 

noncomputable def Ns300p1709 := @Enclosure.Real.IsNear.mulLit_ff qz514 qz214 10601603 33554432 1 33554432 Ns300p1706 Ns300p1707 Ns300p1708 

noncomputable def Ns300p1710 := nat_lit 7402382984297866287444373955308453544238353996561782212713630834463983053213729338642550577061972734940937574078742528000000000000000000000000000000000000000000000000000000000000 

noncomputable abbrev qz519 := (@HPow.hPow Real Real Real qz627 qz213 qz8)

noncomputable def Ns300p1711 := @Enclosure.Real.IsNear.mulLit_ff qz477 qz519 1 1 0 1 10601603 33554432 1 33554432 10601603 33554432 1 33554432 

noncomputable def Ns300p1712 := @Enclosure.Real.IsNear.sqrt_image qz213 210447290671 2097152000 39407 2097152000 168064725 168064757 16777216 (@Enclosure.Real.IsNear.of_eq qz213 (@HMul.hMul Real Real Real qz5 qz212 qz3) Bool.false 210447290671 2097152000 39407 2097152000 (BSN.t_div_two_pi_mk qz212 630512 1000 qz215) (@Enclosure.Real.IsNear.mulLit_ff qz212 qz3 630512 1000 0 1 5340353 33554432 1 33554432 210447290671 2097152000 39407 2097152000 (Enclosure.Real.IsNear.const Bool.false 630512 1000) RS301to312.d44 rfl)) 

noncomputable abbrev qz219 := qz513

noncomputable abbrev qz520 := (@Enclosure.Real.IsNear.recentre' qz219 Bool.false 336129482 33554432 32 33554432 168064741 16777216 1 1048576 (Ns300p1712 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns300p1713 := @Enclosure.Real.IsNear.sqrt_image qz219 168064741 16777216 1 1048576 53100453 53100459 16777216 qz520 rfl 

noncomputable def Ns300p1714 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz219) 6637557 2097152 3 16777216 5300801 5300802 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz219) Bool.false 106200912 33554432 6 33554432 6637557 2097152 3 16777216 (Ns300p1713 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns300p1715 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz219)) Bool.false 10601603 33554432 1 33554432 10601603 33554432 1 33554432 (Ns300p1714 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns300p1716 := nat_lit 779299191345392083730737405581907001660132203401524087295108304030092860408272907804496121867585041261648401461685208197475 

noncomputable def Ns300p1717 := nat_lit 1221756688455269886208688976518033745783680932948266061579120402069903023648407035594205844439545528086978393129989462495759545992701429279424069405275120342469836430354297 

noncomputable abbrev qz220 := qz511

noncomputable abbrev qz221 := qz512

noncomputable def Ns300p1718 := @Enclosure.Real.IsNear.addLit_ft_p qz220 (@HMul.hMul Real Real Real qz5 (Zeta.RiemannSiegel.correctionLinear qz221) (@Inv.inv Real Real.instInv qz219)) 970541947075 1099511627776 267995034260717 22166154415964160000 Ns300p1716 Ns300p1707 Ns300p1717 Ns300p1710 

noncomputable def Ns300p1719 := nat_lit 327633415580121320898622608355919310690309331013057840274756459924419183934718603440466555841460805308037439647109639940014302915513548800 

noncomputable abbrev qz864 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 630512 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1)))

noncomputable abbrev qz743 := (Real.cos qz864)

noncomputable abbrev qz521 := qz743

noncomputable abbrev qz222 := (@Inv.inv Real Real.instInv qz521)

noncomputable abbrev qz744 := (@HSub.hSub Real Real Real qz810 (@HMul.hMul Real Real Real qz807 qz861 qz861) qz861)

noncomputable abbrev qz522 := (@HMul.hMul Real Real Real qz623 qz621 (@HSub.hSub Real Real Real qz628 qz744 qz639))

noncomputable abbrev qz223 := (Real.cos qz522)

noncomputable def Ns300p1720 := @Enclosure.Real.IsNear.of_eq qz220 (@HMul.hMul Real Real Real qz5 qz222 qz223) Bool.false 970541947075 

noncomputable def Ns300p1721 := @Enclosure.Real.IsNear.mulLit_ff qz222 qz223 2109805 2097152 107 

noncomputable def Ns300p1722 := @Enclosure.Real.IsNear.recentre' qz222 Bool.false 33756880 33554432 214 33554432 2109805 2097152 107 

noncomputable abbrev qz224 := qz521

noncomputable def Ns300p1723 := @Enclosure.Real.IsNear.recentre' qz224 Bool.false 16676599 16777216 462187216 73987522560000 16676599 16777216 28886701 4624220160000 

noncomputable abbrev qz745 := qz864

noncomputable abbrev qz523 := qz745

noncomputable abbrev qz225 := qz523

noncomputable def Ns300p1724 := @Enclosure.Real.IsNear.cos_image qz225 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3676681) qz349) Bool.false 3676681 33554432 101 16777216 Bool.false 16676599 16777216 1 

noncomputable def Ns300p1725 := nat_lit 26986075409201123683472839 

noncomputable def Ns300p1726 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz221 884279719003555 140737488355328 1 500000000000000 292581 16777216 1 1048576 258723444465779125455 2361183241434822606848 Ns300p1725 

noncomputable def Ns300p1727 := @Enclosure.Real.IsNear.subLit_ff_p qz219 qz166 168064741 16777216 1 1048576 10 1 0 1 292581 292581 16777216 1 

noncomputable def Ns300p1728 := @Ns300p1727 1048576 qz520 qz724 

noncomputable def Ns300p1729 := @Enclosure.Real.IsNear.recentre' qz225 Bool.false 258723444465779125455 2361183241434822606848 Ns300p1725 Ns300p163 3676681 33554432 101 16777216 (@Ns300p1726 Ns300p163 RS301to312.d43 (Ns300p1728 rfl rfl) rfl) 

noncomputable def Ns300p1730 := nat_lit 182735869140157451017929121 

noncomputable def Ns300p1731 := BSN.cos_dyadic_bound_f 3676681 33554432 2 1 16777216 4410000 Ns300p1730 Ns300p1354 Ns300p1730 Ns300p1730 Ns300p1355 Ns300p1730 16676599 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 3676681) (BSN.cosEvenQ 33554432) 0 1 Ns300p1730 Ns300p1354 Ns300p1730 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 3676681) (BSN.cosOddQ 33554432) 0 1 Ns300p1730 Ns300p1355 Ns300p1730 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1732 := @Enclosure.Real.IsNear.inv_image qz224 16676599 16777216 28886701 4624220160000 16878333 16878547 16777216 (Ns300p1723 (@Ns300p1724 4410000 (Ns300p1729 rfl) (Enclosure.sfrac_false_div 3676681 33554432) (Ns300p1731 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns300p1733 := @Enclosure.Real.IsNear.recentre' qz223 Bool.false 14720480 16777216 

noncomputable abbrev qz226 := qz522

noncomputable def Ns300p1734 := @Enclosure.Real.IsNear.cos_image qz226 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16789357)) qz349) Bool.true 16789357 33554432 

noncomputable def Ns300p1735 := nat_lit 19821374879975581094236782805 

noncomputable def Ns300p1736 := nat_lit 46854287377756799077232823106111 

noncomputable def Ns300p1737 := @Enclosure.Real.IsNear.recentre' qz226 Bool.true Ns300p1735 Ns300p180 Ns300p1736 

noncomputable abbrev qz524 := (@HSub.hSub Real Real Real qz628 qz744 qz639)

noncomputable abbrev qz227 := qz524

noncomputable def Ns300p1738 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz227 884279719003555 140737488355328 1 500000000000000 22415277037351 

noncomputable abbrev qz525 := qz744

noncomputable abbrev qz228 := qz525

noncomputable def Ns300p1739 := @Enclosure.Real.IsNear.subLit_tf qz228 qz27 4823090992935 281474976710656 8681197 8796093022208 1 16 

noncomputable abbrev qz746 := (@HMul.hMul Real Real Real qz807 qz861 qz861)

noncomputable abbrev qz526 := qz746

noncomputable abbrev qz229 := qz526

noncomputable def Ns300p1740 := @Enclosure.Real.IsNear.subLit_ff_n qz229 qz221 85603641561 281474976710656 292589 8796093022208 292581 16777216 1 1048576 

noncomputable def Ns300p1741 := @Enclosure.Real.IsNear.mulLit_ff qz221 qz221 292581 16777216 1 1048576 292581 16777216 1 1048576 85603641561 281474976710656 

noncomputable def Ns300p1742 := nat_lit 169223746843574652793304427764869685441986527126016150065710881 

noncomputable def Ns300p1743 := nat_lit 6313533809924378023298299062356689094163267489356247271201 

noncomputable def Ns300p1744 := nat_lit 507658613463104109623866686696484342947771254843069737702590241 

noncomputable def Ns300p1745 := BSN.cos_dyadic_bound_f 16789357 33554432 3 2 16777216 4410000 Ns300p1742 Ns300p687 Ns300p1743 Ns300p1744 Ns300p690 Ns300p1743 14720480 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 16789357) (BSN.cosEvenQ 33554432) 0 2 Ns300p1742 Ns300p687 Ns300p1743 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 16789357) (BSN.cosOddQ 33554432) 0 2 Ns300p1744 Ns300p690 Ns300p1743 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1746 := @Ns300p1733 955244432 147975045120000 460015 524288 59702777 9248440320000 (@Ns300p1734 209 33554432 Bool.false 14720480 16777216 1 4410000 (@Ns300p1737 Ns300p183 16789357 33554432 209 33554432 (@Ns300p1738 281474976710656 8681197 8796093022208 Ns300p1735 Ns300p180 Ns300p1736 Ns300p183 RS301to312.d43 (@Ns300p1739 0 1 358644432597616 22415277037351 281474976710656 8681197 8796093022208 (@Ns300p1740 80918039376124968960 4823090992935 281474976710656 8681197 8796093022208 (@Ns300p1741 292589 8796093022208 (Ns300p1728 rfl rfl) (Ns300p1728 rfl rfl) rfl) (Ns300p1728 rfl rfl) rfl rfl) qz358 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16789357 33554432) (BSN.cos_neg_of_bound 16789357 33554432 Bool.false 14720480 16777216 1 4410000 (Ns300p1745 rfl rfl)) rfl rfl) 

noncomputable def Ns300p1747 := nat_lit 465308529995738051106213457946291530552066904307750047495259618324859407421104303021371567050404818997390377401067475 

noncomputable def Ns300p1748 := nat_lit 20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792 

noncomputable def Ns300p1749 := nat_lit 1446833774211125658206635602035127310536418068109007671497367271508515934420757676038991076147365895061794873686521811659551575847656081211019744908612525710733735247 

noncomputable def Ns300p1750 := nat_lit 882432816540940557413622612393910115270418405122969414319232801731107598926273505525893041737314788692109295616000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns300p1751 := @Enclosure.Real.IsNear.mulLit_tf (Zeta.RiemannSiegel.correctionLinear qz221) (@Inv.inv Real Real.instInv qz219) Ns300p1747 Ns300p1748 Ns300p1749 Ns300p1750 1674801 16777216 1 16777216 Ns300p1716 

noncomputable def Ns300p1752 := nat_lit 821187284794350538193797807641845953087588006098787826770708202942065103305874395806376953968831138182815170775 

noncomputable def Ns300p1753 := nat_lit 37576681324381331646231689548629392438010920782533117931316655544515344401833735095419183974156299248510959616 

noncomputable def Ns300p1754 := nat_lit 24900090655935827844106406516501546140287496314587922380168222173690966960657991898737225811034268132290568444191075502034694090620461937457634470658468471951069 

noncomputable def Ns300p1755 := nat_lit 16436592052521939527497116707151944102168426013048168538496509226618476192024974255373571845466546503680000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns300p1756 := @Enclosure.Real.IsNear.mulLit_ff (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz221) qz492 Ns300p1752 Ns300p1753 Ns300p1754 Ns300p1755 566629 536870912 1 536870912 Ns300p1747 

noncomputable abbrev qz865 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 630512 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1)))

noncomputable abbrev qz747 := (@HMul.hMul Real Real Real qz807 qz805 (@HSub.hSub Real Real Real qz810 qz865 qz857))

noncomputable abbrev qz527 := (@HMul.hMul Real Real Real qz623 qz747 qz747)

noncomputable abbrev qz528 := qz747

noncomputable abbrev qz230 := (@HMul.hMul Real Real Real qz327 qz527 qz528)

noncomputable abbrev qz231 := (Real.sin qz522)

noncomputable abbrev qz232 := (@HMul.hMul Real Real Real qz327 qz319 qz528)

noncomputable def Ns300p1757 := @HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 qz230 qz231) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz232 qz189) qz223) 

noncomputable abbrev qz748 := (Real.sin qz864)

noncomputable abbrev qz529 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz623 qz621 qz748))

noncomputable abbrev qz233 := (@HMul.hMul Real Real Real qz327 qz319 qz529)

noncomputable abbrev qz530 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz623 qz728 qz743))

noncomputable abbrev qz234 := (@HMul.hMul Real Real Real qz327 qz319 qz530)

noncomputable abbrev qz531 := qz748

noncomputable abbrev qz235 := qz531

noncomputable def Ns300p1758 := @HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns300p1757 (@HMul.hMul Real Real Real qz5 qz233 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz221))) (@HMul.hMul Real Real Real qz5 qz234 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz221))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz498 qz235) qz220) 

noncomputable abbrev qz749 := (BSN.cos_two_pi_p_ne_zero_mk qz212 630512 1000 10 qz215 rfl rfl (@BSN.floor_sqrt_eq_dec qz212 630512 1000 10 qz215 rfl rfl rfl))

noncomputable abbrev qz532 := qz749

noncomputable def Ns300p1759 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz221) (@HMul.hMul Real Real Real qz5 qz222 Ns300p1758) Bool.false Ns300p1752 Ns300p1753 Ns300p1754 Ns300p1755 (BSN.iteratedDeriv_three_correction_mk qz221 qz532) 

noncomputable def Ns300p1760 := nat_lit 3040813285120331248317719754500388930142516949746393566340437385780284097845045701411073461772177275475 

noncomputable def Ns300p1761 := nat_lit 139984046386112763159840142535527767382602843577165595931249318810236991948760059086304843329475444736 

noncomputable def Ns300p1762 := nat_lit 91661907073217878199834235968869302702242682308538547031564088181006816507778932884907203570959232900390066522593298520205532376003593099808152088477591 

noncomputable def Ns300p1763 := @Enclosure.Real.IsNear.mulLit_ff qz222 Ns300p1758 270055149 268435456 55 134217728 Ns300p1760 Ns300p1761 Ns300p1762 

noncomputable def Ns300p1764 := nat_lit 61231076913036180762563335549652368210883535493344696382047642866590902924630695042660727521280000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns300p1765 := @Enclosure.Real.IsNear.recentre' qz222 Bool.false 540110298 536870912 220 536870912 270055149 268435456 55 

noncomputable def Ns300p1766 := @Enclosure.Real.IsNear.recentre' qz224 Bool.false 266825477 268435456 15283910912 37881611550720000 266825477 268435456 59702777 147975045120000 

noncomputable abbrev qz750 := (@Nat.cast Real Real.instNatCast 536870912)

noncomputable def Ns300p1767 := @Enclosure.Real.IsNear.cos_image qz225 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 58829105) qz750) Bool.false 58829105 536870912 209 536870912 Bool.false 266825477 268435456 1 

noncomputable def Ns300p1768 := nat_lit 890540488578880567979200167 

noncomputable def Ns300p1769 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz221 884279719003555 140737488355328 1 500000000000000 9362943 536870912 33 536870912 8279460605086302262365 75557863725914323419136 Ns300p1768 

noncomputable def Ns300p1770 := @Enclosure.Real.IsNear.subLit_ff_p qz219 qz166 5378072063 536870912 33 536870912 10 1 0 1 9362943 9362943 536870912 33 

noncomputable def Ns300p1771 := @Enclosure.Real.IsNear.sqrt_image qz213 3367157084213 33554432000 39407 33554432000 2689036015 2689036048 268435456 (@Enclosure.Real.IsNear.of_eq qz213 (@HMul.hMul Real Real Real qz5 qz212 qz3) Bool.false 3367157084213 33554432000 39407 33554432000 (BSN.t_div_two_pi_mk qz212 630512 1000 qz215) (@Enclosure.Real.IsNear.mulLit_ff qz212 qz3 630512 1000 0 1 85445659 536870912 1 536870912 3367157084213 33554432000 39407 33554432000 (Enclosure.Real.IsNear.const Bool.false 630512 1000) RS301to312.d65 rfl)) 

noncomputable def Ns300p1772 := @Ns300p1770 536870912 (@Enclosure.Real.IsNear.recentre' qz219 Bool.false 5378072063 536870912 33 536870912 5378072063 536870912 33 536870912 (Ns300p1771 rfl rfl rfl rfl rfl rfl) rfl) qz724 

noncomputable def Ns300p1773 := @Enclosure.Real.IsNear.recentre' qz225 Bool.false 8279460605086302262365 75557863725914323419136 Ns300p1768 Ns300p1433 58829105 536870912 209 536870912 (@Ns300p1769 Ns300p1433 RS301to312.d64 (Ns300p1772 rfl rfl) rfl) 

noncomputable def Ns300p1774 := nat_lit 11977576823895591514379956050625 

noncomputable def Ns300p1775 := nat_lit 1993841993677373809355710590420516864 

noncomputable def Ns300p1776 := nat_lit 29907629905160607140335658856307752960 

noncomputable def Ns300p1777 := BSN.cos_dyadic_bound_f 58829105 536870912 2 1 268435456 70560000 Ns300p1774 Ns300p1775 Ns300p1774 Ns300p1774 Ns300p1776 Ns300p1774 266825477 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 58829105) (BSN.cosEvenQ 536870912) 0 1 Ns300p1774 Ns300p1775 Ns300p1774 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 58829105) (BSN.cosOddQ 536870912) 0 1 Ns300p1774 Ns300p1776 Ns300p1774 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz533 := (Ns300p1766 (@Ns300p1767 70560000 (Ns300p1773 rfl) (Enclosure.sfrac_false_div 58829105 536870912) (Ns300p1777 rfl rfl) rfl rfl) rfl)

noncomputable def Ns300p1778 := @Enclosure.Real.IsNear.inv_image qz224 266825477 268435456 59702777 147975045120000 270055039 270055259 268435456 qz533 rfl 

noncomputable def Ns300p1779 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns300p1757 (@HMul.hMul Real Real Real qz5 qz233 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz221))) (@HMul.hMul Real Real Real qz5 qz234 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz221))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz498 qz235) qz220) 

noncomputable def Ns300p1780 := nat_lit 6392664941333447444851146608113420594461008331508674043797336568885979356443006885540061083348848507475 

noncomputable def Ns300p1781 := nat_lit 84959547210238196830981909386258826250374307229476599009067920183509560987336020101315435185305801583649449642846711080367311865181608611050494488477591 

noncomputable def Ns300p1782 := nat_lit 1291086294768958252773178866804894164219625823401099944489405878124625 

noncomputable def Ns300p1783 := nat_lit 25487208592808205372957690407556540400287279158129059677446666699536085288753347846205490190947247289113609 

noncomputable def Ns300p1784 := nat_lit 232844738502452289892491943896265062765121877516710261555200000000000000000000000000000000000000000000000000000 

noncomputable def Ns300p1785 := nat_lit 163960327983214525241821032709652299408048534988683272048457515876670070877422456178042998151049240529606320960830557609445265134970859452633218042523280680003793269555200 

noncomputable def Ns300p1786 := nat_lit 44568825053848086878639836018218362851004393733077033174426679723709385806393769314586831602016931707475 

noncomputable def Ns300p1787 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real qz11 Ns300p1757 (@HMul.hMul Real Real Real qz5 qz233 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 2 Zeta.RiemannSiegel.correction qz221))) (@HMul.hMul Real Real Real qz5 qz234 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz221)) Ns300p1786 Ns300p1761 

noncomputable def Ns300p1788 := nat_lit 30269138587111610669014137715229938221696780204994371944519839277372636337287230479880590797525929870157369687184170886246861915739619691387157344157591 

noncomputable def Ns300p1789 := nat_lit 1059601298717256485476220490285629912034598015856633444215765903340759247762436002478125 

noncomputable def Ns300p1790 := nat_lit 3885337784451458141838923813647037813284813678104279042503624819477808570410416996352 

noncomputable def Ns300p1791 := nat_lit 2753675776850491676767572919535717735182375383743630271478657657821483728787204160302873991435629871483176298660187140899002587987 

noncomputable def Ns300p1792 := nat_lit 3083000064011184663809101827549534898307299784850786489098136600228132814848000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns300p1793 := nat_lit 24837662639901007336271647268751385642132953847072836628184811882670154691918844304201723261011905332430678010023422590702620978140700161764078890280397710971687269722905586585767719731200 

noncomputable def Ns300p1794 := nat_lit 4451642684179067209187086484428203437506275987585135620346378798598871224452225 

noncomputable def Ns300p1795 := nat_lit 14474011154664524427946373126085988481658748083205070504932198000989141204992 

noncomputable def Ns300p1796 := nat_lit 28859096056530788311213400303327019988976959254753201474436486923018385912344251622148758122510014831840521643 

noncomputable def Ns300p1797 := nat_lit 113385548402914353842240845235592433233966643241313862458865090560000000000000000000000000000000000000000000000000 

noncomputable def Ns300p1798 := @Enclosure.Real.IsNear.subLit_ft Ns300p1757 (@HMul.hMul Real Real Real qz5 qz233 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 2 Zeta.RiemannSiegel.correction qz221)) Ns300p1794 Ns300p1795 Ns300p1796 Ns300p1797 

noncomputable def Ns300p1799 := nat_lit 1515178809026913777949363830800941008672709395017769712000782398903229212760970058634262481929536174675 

noncomputable def Ns300p1800 := nat_lit 14684493496373427417095499223452986913901119083913837015717792319761488348686031202451620012611863964161197091145252721960389087765290126203157344157591 

noncomputable def Ns300p1801 := nat_lit 645089670979688933076144413246687624586590086641069984337587051539728885259830478825846604097762844547592231713033441311987988691943254875780582465818751054679193656718393553715200 

noncomputable def Ns300p1802 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz5 qz230 qz231) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz232 qz189) qz223) 

noncomputable def Ns300p1803 := nat_lit 1548405585763896395426885938076568247655101040065775343399711019310536259306625 

noncomputable def Ns300p1804 := nat_lit 15165972964165966245281969599434140435291647682404957450982839138967100761896752363374248538126014831840521643 

noncomputable def Ns300p1805 := nat_lit 143140640345438461658218965132196479393411330975 

noncomputable def Ns300p1806 := nat_lit 7374144496944233118012224212563978780196335252745318910917206110269 

noncomputable def Ns300p1807 := nat_lit 61061411056369572911518636831628328960000000000000000000000000000000000 

noncomputable def Ns300p1808 := nat_lit 3176798374872969864431096780141697307213431300391927161713288881486434302978287978043612289631038927300779146623717684019200 

noncomputable def Ns300p1809 := nat_lit 12023558120053555389005747021666672122869178064454497922396684213050875 

noncomputable def Ns300p1810 := @Enclosure.Real.IsNear.mulLit_tt qz230 qz231 Ns300p1809 Ns300p1475 

noncomputable def Ns300p1811 := nat_lit 130586149212406747717383371933875247042026884478728631037561457918871595973176582132685188869793 

noncomputable def Ns300p1812 := nat_lit 52483405169729901009668652498410249482279201225 

noncomputable def Ns300p1813 := nat_lit 12452161975676190976825455500659798495439865840892687646679699 

noncomputable abbrev qz236 := qz527

noncomputable abbrev qz237 := qz528

noncomputable def Ns300p1814 := @Enclosure.Real.IsNear.mulLit_ft qz236 qz237 Ns300p1812 Ns300p1480 Ns300p1813 Ns300p1482 

noncomputable def Ns300p1815 := nat_lit 890540490723869441275645607 

noncomputable def Ns300p1816 := @Enclosure.Real.IsNear.mulLit_tt qz237 qz237 229092568997184849783715 37778931862957161709568 Ns300p1815 Ns300p1485 229092568997184849783715 37778931862957161709568 

noncomputable abbrev qz751 := (@HSub.hSub Real Real Real qz810 qz865 qz857)

noncomputable abbrev qz534 := qz751

noncomputable abbrev qz238 := qz534

noncomputable def Ns300p1817 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz238 884279719003555 140737488355328 1 500000000000000 259072513 268435456 33 268435456 

noncomputable abbrev qz752 := qz865

noncomputable abbrev qz535 := qz752

noncomputable abbrev qz239 := qz535

noncomputable def Ns300p1818 := @Enclosure.Real.IsNear.subLit_ff_n qz239 qz187 9362943 268435456 33 268435456 1 1 0 1 259072513 

noncomputable def Ns300p1819 := @Enclosure.Real.IsNear.mulLit_ff qz0 qz221 2 1 0 1 9362943 536870912 33 536870912 9362943 268435456 33 

noncomputable def Ns300p1820 := @Enclosure.Real.IsNear.recentre' qz231 Bool.true 128780979 268435456 

noncomputable def Ns300p1821 := @Enclosure.Real.IsNear.sin_image qz226 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 268631849)) qz750) Bool.true 268631849 536870912 

noncomputable def Ns300p1822 := nat_lit 20297248700187375209923970739805 

noncomputable def Ns300p1823 := nat_lit 494781473484101137194441802625624633 

noncomputable def Ns300p1824 := @Enclosure.Real.IsNear.recentre' qz226 Bool.true Ns300p1822 Ns300p1493 Ns300p1823 

noncomputable def Ns300p1825 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz227 884279719003555 140737488355328 1 500000000000000 22953425555274751 

noncomputable def Ns300p1826 := @Enclosure.Real.IsNear.subLit_tf qz228 qz27 4939027045792767 288230376151711744 18334695423 288230376151711744 1 16 

noncomputable def Ns300p1827 := @Enclosure.Real.IsNear.subLit_ff_n qz229 qz221 87664701621249 288230376151711744 617955327 288230376151711744 9362943 536870912 33 536870912 

noncomputable def Ns300p1828 := nat_lit 2651619954467428582293504 

noncomputable def Ns300p1829 := @Enclosure.Real.IsNear.mulLit_ff qz221 qz221 9362943 536870912 33 536870912 9362943 536870912 33 536870912 87664701621249 288230376151711744 

noncomputable def Ns300p1830 := nat_lit 1308278762434228082327490679330203307182406935184747034739813076267366465 

noncomputable def Ns300p1831 := nat_lit 2504505714323359787184324207303086996185458423821189873137376790332288532480 

noncomputable def Ns300p1832 := nat_lit 27118147013808537617278268708590429523476439079075347654827181275201 

noncomputable def Ns300p1833 := nat_lit 3426400472232575001796809519144051896210884916011066588041402622406752321 

noncomputable def Ns300p1834 := nat_lit 45915938095928262765045943800556594930066737770055147674185241156091956428800 

noncomputable def Ns300p1835 := BSN.sin_dyadic_bound_f 268631849 536870912 3 2 268435456 70560000 Ns300p1830 Ns300p1831 Ns300p1832 Ns300p1833 Ns300p1834 Ns300p1832 128780979 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 268631849) (BSN.sinEvenQ 536870912) 0 2 Ns300p1830 Ns300p1831 Ns300p1832 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 268631849) (BSN.sinOddQ 536870912) 0 2 Ns300p1833 Ns300p1834 Ns300p1832 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1836 := @Ns300p1820 1972228864 4735201443840000 128780979 268435456 7704019 18496880640000 (@Ns300p1821 27 67108864 Bool.true 128780979 268435456 1 70560000 (@Ns300p1824 Ns300p1496 268631849 536870912 27 67108864 (@Ns300p1825 288230376151711744 18334695423 288230376151711744 Ns300p1822 Ns300p1493 Ns300p1823 Ns300p1496 RS301to312.d64 (@Ns300p1826 0 1 367254808884396016 22953425555274751 288230376151711744 18334695423 288230376151711744 (@Ns300p1827 Ns300p1828 4939027045792767 288230376151711744 18334695423 288230376151711744 (@Ns300p1829 617955327 288230376151711744 (Ns300p1772 rfl rfl) (Ns300p1772 rfl rfl) rfl) (Ns300p1772 rfl rfl) rfl rfl) qz358 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 268631849 536870912) (BSN.sin_neg_of_bound 268631849 536870912 Bool.false 128780979 268435456 1 70560000 (Ns300p1835 rfl rfl)) rfl rfl) 

noncomputable def Ns300p1837 := nat_lit 607745737615899464521757109351198320475 

noncomputable def Ns300p1838 := nat_lit 72096578692610017220980868494084454586189264588833907 

noncomputable def Ns300p1839 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz232 qz189) qz223 Ns300p1837 Ns300p1507 Ns300p1838 

noncomputable def Ns300p1840 := nat_lit 2671621472171608323826936821 

noncomputable def Ns300p1841 := @Enclosure.Real.IsNear.mulLit_tf qz232 qz189 687277706991554549351145 37778931862957161709568 Ns300p1840 Ns300p1485 884279719003555 

noncomputable def Ns300p1842 := @Enclosure.Real.IsNear.mulLit_ft qz319 qz237 3 1 0 1 229092568997184849783715 37778931862957161709568 Ns300p1815 

noncomputable def Ns300p1843 := @Enclosure.Real.IsNear.recentre' qz223 Bool.false 235527181 268435456 

noncomputable def Ns300p1844 := @Enclosure.Real.IsNear.cos_image qz226 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 268631849)) qz750) Bool.true 268631849 536870912 

noncomputable def Ns300p1845 := nat_lit 726833587195466182865324723302872321958903175742227941676631632229103681 

noncomputable def Ns300p1846 := nat_lit 278278412702595531909369356367009666242828713757909985904152976703587614720 

noncomputable def Ns300p1847 := nat_lit 2180446525292370931520739613371199785017662574348525674334585242324760641 

noncomputable def Ns300p1848 := nat_lit 12522528571616798935921621036515434980927292119105949365686883951661442662400 

noncomputable def Ns300p1849 := BSN.cos_dyadic_bound_f 268631849 536870912 3 2 268435456 70560000 Ns300p1845 Ns300p1846 Ns300p1832 Ns300p1847 Ns300p1848 Ns300p1832 235527181 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 268631849) (BSN.cosEvenQ 536870912) 0 2 Ns300p1845 Ns300p1846 Ns300p1832 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 268631849) (BSN.cosOddQ 536870912) 0 2 Ns300p1847 Ns300p1848 Ns300p1832 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1850 := @Ns300p1843 1972228864 4735201443840000 235527181 268435456 7704019 18496880640000 (@Ns300p1844 27 67108864 Bool.false 235527181 268435456 1 70560000 (@Ns300p1824 Ns300p1496 268631849 536870912 27 67108864 (@Ns300p1825 288230376151711744 18334695423 288230376151711744 Ns300p1822 Ns300p1493 Ns300p1823 Ns300p1496 RS301to312.d64 (@Ns300p1826 0 1 367254808884396016 22953425555274751 288230376151711744 18334695423 288230376151711744 (@Ns300p1827 Ns300p1828 4939027045792767 288230376151711744 18334695423 288230376151711744 (@Ns300p1829 617955327 288230376151711744 (Ns300p1772 rfl rfl) (Ns300p1772 rfl rfl) rfl) (Ns300p1772 rfl rfl) rfl rfl) qz358 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 268631849 536870912) (BSN.cos_neg_of_bound 268631849 536870912 Bool.false 235527181 268435456 1 70560000 (Ns300p1849 rfl rfl)) rfl rfl) 

noncomputable abbrev qz240 := (@Ns300p1817 229092568997184849783715 37778931862957161709568 Ns300p1815 Ns300p1485 RS301to312.d64 (@Ns300p1818 259072513 268435456 33 268435456 (@Ns300p1819 268435456 qz324 (Ns300p1772 rfl rfl) rfl) qz727 rfl rfl) rfl)

noncomputable def Ns300p1851 := @Ns300p1802 Ns300p1803 Ns300p1795 Ns300p1804 Ns300p1797 Ns300p1805 Ns300p1470 Ns300p1806 Ns300p1807 Ns300p1808 Ns300p1794 Ns300p1795 Ns300p1796 Ns300p1797 (@Ns300p1810 Ns300p1811 Ns300p1478 128780979 268435456 7704019 18496880640000 Ns300p1803 Ns300p1795 Ns300p1804 Ns300p1797 (@Ns300p1814 229092568997184849783715 37778931862957161709568 Ns300p1815 Ns300p1485 Ns300p1809 Ns300p1475 Ns300p1811 Ns300p1478 (@Ns300p1816 Ns300p1815 Ns300p1485 Ns300p1812 Ns300p1480 Ns300p1813 Ns300p1482 qz240 qz240 rfl) qz240 rfl) (Ns300p1836 rfl) rfl) (@Ns300p1839 Ns300p1510 235527181 268435456 7704019 18496880640000 Ns300p1805 Ns300p1470 Ns300p1806 Ns300p1807 (@Ns300p1841 70368744177664 1 250000000000000 Ns300p1837 Ns300p1507 Ns300p1838 Ns300p1510 (@Ns300p1842 Ns300p1485 687277706991554549351145 37778931862957161709568 Ns300p1840 Ns300p1485 qz502 qz240 rfl) RS301to312.d66 rfl) (Ns300p1850 rfl) rfl) rfl rfl 

noncomputable def Ns300p1852 := nat_lit 1611143642390345690922383430441359 

noncomputable def Ns300p1853 := nat_lit 19456297012183674793137155070306264675166957070472649281500852923771100536284465 

noncomputable def Ns300p1854 := @Enclosure.Real.IsNear.mulLit_tf qz233 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz221) 77876011456758589785795 37778931862957161709568 Ns300p1852 Ns300p1525 Ns300p1853 

noncomputable def Ns300p1855 := nat_lit 3705346855594118253554271520278013051304639509300498049262642688253220148477952 

noncomputable def Ns300p1856 := nat_lit 28026859225449722044690146513530510861512971249285580990307231146861777546471768326829217698226557792004554365299 

noncomputable def Ns300p1857 := nat_lit 289031256001048562232103296332768896716309354829761233352950306271387451392000000000000000000000000000000000000000000 

noncomputable abbrev qz241 := qz529

noncomputable def Ns300p1858 := @Enclosure.Real.IsNear.mulLit_ft qz319 qz241 3 1 0 1 25958670485586196595265 37778931862957161709568 Ns300p1852 

noncomputable def Ns300p1859 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz235 884279719003555 140737488355328 1 500000000000000 29355723 268435456 59702777 147975045120000 25958670485586196595265 

noncomputable def Ns300p1860 := @Enclosure.Real.IsNear.recentre' qz235 Bool.false 29355723 268435456 15283910912 37881611550720000 29355723 268435456 59702777 147975045120000 

noncomputable def Ns300p1861 := @Enclosure.Real.IsNear.sin_image qz225 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 58829105) qz750) Bool.false 58829105 536870912 209 536870912 Bool.false 29355723 268435456 1 

noncomputable def Ns300p1862 := nat_lit 9969209968386869046778552952102584320 

noncomputable def Ns300p1863 := nat_lit 69784469778708083327449870664718090240 

noncomputable def Ns300p1864 := BSN.sin_dyadic_bound_f 58829105 536870912 2 1 268435456 70560000 Ns300p1774 Ns300p1862 Ns300p1774 Ns300p1774 Ns300p1863 Ns300p1774 29355723 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 58829105) (BSN.sinEvenQ 536870912) 0 1 Ns300p1774 Ns300p1862 Ns300p1774 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 58829105) (BSN.sinOddQ 536870912) 0 1 Ns300p1774 Ns300p1863 Ns300p1774 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz536 := (@HMul.hMul Real Real Real qz623 qz621 qz748)

noncomputable abbrev qz242 := qz536

noncomputable abbrev qz537 := (@Enclosure.Real.IsNear.neg qz242 Bool.false 25958670485586196595265 37778931862957161709568 Ns300p1852 Ns300p1532 (@Ns300p1859 37778931862957161709568 Ns300p1852 Ns300p1532 RS301to312.d64 (Ns300p1860 (@Ns300p1861 70560000 (Ns300p1773 rfl) (Enclosure.sfrac_false_div 58829105 536870912) (Ns300p1864 rfl rfl) rfl rfl) rfl) rfl))

noncomputable def Ns300p1865 := @Ns300p1858 Ns300p1532 77876011456758589785795 37778931862957161709568 Ns300p1852 Ns300p1525 qz502 qz537 rfl 

noncomputable abbrev qz243 := (@HMul.hMul Real Real Real qz327 qz527 (Real.cos qz522))

noncomputable def Ns300p1866 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz243) (@HMul.hMul Real Real Real qz5 qz189 qz231) 

noncomputable abbrev qz244 := (@HMul.hMul Real Real Real qz327 qz317 qz529)

noncomputable abbrev qz245 := (@HMul.hMul Real Real Real qz327 qz530 qz511)

noncomputable def Ns300p1867 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz221) (@HMul.hMul Real Real Real qz5 qz222 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns300p1866 (@HMul.hMul Real Real Real qz5 qz244 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c8 1 Zeta.RiemannSiegel.correction qz221))) qz245)) 

noncomputable def Ns300p1868 := @Enclosure.Real.IsNear.mulLit_ff qz222 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns300p1866 (@HMul.hMul Real Real Real qz5 qz244 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 1 Zeta.RiemannSiegel.correction qz221))) qz245) 270055149 

noncomputable def Ns300p1869 := nat_lit 72045643581428898410439695302037231940232167432114576276791719026883285 

noncomputable def Ns300p1870 := nat_lit 13803492693581127574869511724554050904902217944340773110325048447598592 

noncomputable def Ns300p1871 := nat_lit 101492847542585804595265456100219553328289770368533814936483274312758388993734889390036129871219304610561 

noncomputable def Ns300p1872 := nat_lit 1076725333932968088359025479602697851942141930869822328362428792832000000000000000000000000000000000000000000 

noncomputable def Ns300p1873 := nat_lit 406088636060140720000360615009025981016025019199232130094312021735638315 

noncomputable def Ns300p1874 := @Enclosure.Real.IsNear.subLit_tt_p (@HSub.hSub Real Real Real qz11 Ns300p1866 (@HMul.hMul Real Real Real qz5 qz244 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz221))) qz245 Ns300p1873 Ns300p1870 

noncomputable def Ns300p1875 := nat_lit 53458088242586406451088293781394418834976392897769466204211513081555148947858851891209738471556425890561 

noncomputable def Ns300p1876 := nat_lit 13270892153015845749430843001111602146198575520079274325 

noncomputable def Ns300p1877 := nat_lit 2418562165858807208611240276455369531606815692064246734655597135824199424219809527 

noncomputable def Ns300p1878 := nat_lit 54213390336942926489862600317286574925557216051200000000000000000000000000000000000000 

noncomputable def Ns300p1879 := nat_lit 27602406881838233427881940884670113483144411881529421011828705748812210845131937813086032204619195574501887767373035906007040 

noncomputable def Ns300p1880 := nat_lit 10051539954398803437104047634495346526330878403604241205 

noncomputable def Ns300p1881 := nat_lit 44910420811510977732659073708863929115529328619275268721633422940663071873 

noncomputable def Ns300p1882 := nat_lit 1561052163897143619907500279085385305418629120000000000000000000000000000000000 

noncomputable def Ns300p1883 := @Enclosure.Real.IsNear.subLit_tf Ns300p1866 (@HMul.hMul Real Real Real qz5 qz244 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz221)) Ns300p1880 Ns300p1554 Ns300p1881 Ns300p1882 

noncomputable def Ns300p1884 := nat_lit 43943743315099891876096247287931771563149198689840919922489721859736875 

noncomputable def Ns300p1885 := nat_lit 22481424577085459952131960532757170134908573487232888016908143294245753367768426295343950887863625890561 

noncomputable def Ns300p1886 := nat_lit 155582255989619112660838740936268664936585464713695740524326060943703179475481848710497077176466684062082796136570480345743360 

noncomputable def Ns300p1887 := @Enclosure.Real.IsNear.subLit_tt_n (@Neg.neg Real Real.instNeg qz243) (@HMul.hMul Real Real Real qz5 qz189 qz231) 

noncomputable def Ns300p1888 := nat_lit 12361268468907310116216311467019173042067929719455996725 

noncomputable def Ns300p1889 := nat_lit 2314617978237741228055044448804616348316509042449154444487801645261773527999 

noncomputable def Ns300p1890 := nat_lit 207901237762933582735976459898373 

noncomputable def Ns300p1891 := nat_lit 39721748713407774720000000000000000000 

noncomputable def Ns300p1892 := nat_lit 189868221527511965695614316823757040885629358183227698798564369957336614174720 

noncomputable def Ns300p1893 := @Enclosure.Real.IsNear.neg qz243 Bool.false Ns300p1888 

noncomputable def Ns300p1894 := @Enclosure.Real.IsNear.mulLit_ff qz236 qz223 Ns300p1812 Ns300p1480 Ns300p1813 

noncomputable def Ns300p1895 := @Enclosure.Real.IsNear.mulLit_ft qz189 qz231 884279719003555 70368744177664 1 

noncomputable def Ns300p1896 := nat_lit 1692834898439813444948278774916670006463583392875 

noncomputable def Ns300p1897 := @Enclosure.Real.IsNear.mulLit_tt qz244 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz221) 25958670485586196595265 18889465931478580854784 Ns300p1852 Ns300p1566 Ns300p1896 

noncomputable def Ns300p1898 := nat_lit 730750818665451459101842416358141509827966271488 

noncomputable def Ns300p1899 := nat_lit 22521314216758115557638349910832377561025625159415856317738129879 

noncomputable def Ns300p1900 := nat_lit 3388336896058932905616412519830410932847326003200000000000000000000000 

noncomputable def Ns300p1901 := @Enclosure.Real.IsNear.mulLit_ft qz0 qz241 2 1 0 1 25958670485586196595265 37778931862957161709568 Ns300p1852 

noncomputable def Ns300p1902 := @Ns300p1901 Ns300p1532 25958670485586196595265 18889465931478580854784 Ns300p1852 Ns300p1566 qz324 qz537 rfl 

noncomputable abbrev qz246 := (@HMul.hMul Real Real Real qz327 qz528 (Real.sin qz522))

noncomputable def Ns300p1903 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz246) (@HMul.hMul Real Real Real qz5 qz241 qz220) 

noncomputable def Ns300p1904 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz221) (@HMul.hMul Real Real Real qz5 qz222 Ns300p1903) Bool.true Ns300p1896 Ns300p1898 Ns300p1899 Ns300p1900 (BSN.deriv_correction_mk qz221 qz532) 

noncomputable def Ns300p1905 := nat_lit 6268478511549555550034259020614600488375 

noncomputable def Ns300p1906 := nat_lit 2722258935367507707706996859454145691648 

noncomputable def Ns300p1907 := nat_lit 71556085894952709534197337218366985489893813452841854681 

noncomputable def Ns300p1908 := @Enclosure.Real.IsNear.mulLit_ft qz222 Ns300p1903 270055149 268435456 55 134217728 Ns300p1905 Ns300p1906 Ns300p1907 

noncomputable def Ns300p1909 := nat_lit 12622538566808897650302993207538168627200000000000000000000000 

noncomputable def Ns300p1910 := @Enclosure.Real.IsNear.subLit_tt_n (@Neg.neg Real Real.instNeg qz246) (@HMul.hMul Real Real Real qz5 qz241 qz220) 

noncomputable def Ns300p1911 := nat_lit 29502765317082513199114755956985 

noncomputable def Ns300p1912 := nat_lit 10141204801825835211973625643008 

noncomputable def Ns300p1913 := nat_lit 247055975743337158920176657067315345048757 

noncomputable def Ns300p1914 := nat_lit 85301805832008234567267778560000000000000000000 

noncomputable def Ns300p1915 := nat_lit 1651109749602473470196129291027384371785 

noncomputable def Ns300p1916 := nat_lit 34997966737166767903611585910460230429035627777926014681 

noncomputable def Ns300p1917 := nat_lit 63569924381468416973761267860442374575782127187747585899972140204032000 

noncomputable def Ns300p1918 := @Enclosure.Real.IsNear.neg qz246 Bool.false Ns300p1911 

noncomputable def Ns300p1919 := @Enclosure.Real.IsNear.mulLit_tt qz237 qz231 229092568997184849783715 37778931862957161709568 Ns300p1815 

noncomputable def Ns300p1920 := @Enclosure.Real.IsNear.mulLit_tf qz241 qz220 25958670485586196595265 37778931862957161709568 Ns300p1852 Ns300p1532 63605327958504969 72057594037927936 

noncomputable def Ns300p1921 := @Enclosure.Real.IsNear.of_eq qz220 (@HMul.hMul Real Real Real qz5 qz222 qz223) Bool.false 63605327958504969 

noncomputable def Ns300p1922 := @Enclosure.Real.IsNear.mulLit_ff qz222 qz223 270055149 268435456 55 

noncomputable abbrev qz538 := (@Ns300p1921 72057594037927936 7731466552243717 9930437178351943680000 (BSN.correction_mk qz221 qz749) (@Ns300p1922 134217728 235527181 268435456 7704019 18496880640000 63605327958504969 72057594037927936 7731466552243717 9930437178351943680000 (@Ns300p1765 134217728 (Ns300p1778 rfl rfl rfl rfl rfl) rfl) (Ns300p1850 rfl) rfl))

noncomputable def Ns300p1923 := @Ns300p1920 7731466552243717 9930437178351943680000 Ns300p1915 Ns300p1906 Ns300p1916 Ns300p1909 qz537 qz538 

noncomputable abbrev qz539 := (@Ns300p1765 134217728 (Ns300p1778 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns300p1924 := @Ns300p1897 Ns300p1898 Ns300p1899 Ns300p1900 Ns300p1884 Ns300p1870 Ns300p1885 Ns300p1872 Ns300p1902 (Ns300p1904 (@Ns300p1908 Ns300p1909 Ns300p1896 Ns300p1898 Ns300p1899 Ns300p1900 qz539 (@Ns300p1910 Ns300p1911 Ns300p1912 Ns300p1913 Ns300p1914 Ns300p1915 Ns300p1906 Ns300p1916 Ns300p1909 Ns300p1917 Ns300p1905 Ns300p1906 Ns300p1907 Ns300p1909 (@Ns300p1918 Ns300p1912 Ns300p1913 Ns300p1914 (@Ns300p1919 Ns300p1485 128780979 268435456 7704019 18496880640000 Ns300p1911 Ns300p1912 Ns300p1913 Ns300p1914 qz240 (Ns300p1836 rfl) rfl)) (Ns300p1923 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns300p1925 := @Ns300p1883 Ns300p1884 Ns300p1870 Ns300p1885 Ns300p1872 Ns300p1886 Ns300p1873 Ns300p1870 Ns300p1875 Ns300p1872 (@Ns300p1887 Ns300p1888 Ns300p1554 Ns300p1889 Ns300p1556 113878407923122717380345 18889465931478580854784 Ns300p1890 Ns300p1891 Ns300p1892 Ns300p1880 Ns300p1554 Ns300p1881 Ns300p1882 (@Ns300p1893 Ns300p1554 Ns300p1889 Ns300p1556 (@Ns300p1894 Ns300p1482 235527181 268435456 7704019 18496880640000 Ns300p1888 Ns300p1554 Ns300p1889 Ns300p1556 (@Ns300p1816 Ns300p1815 Ns300p1485 Ns300p1812 Ns300p1480 Ns300p1813 Ns300p1482 qz240 qz240 rfl) (Ns300p1850 rfl) rfl)) (@Ns300p1895 250000000000000 128780979 268435456 7704019 18496880640000 113878407923122717380345 18889465931478580854784 Ns300p1890 Ns300p1891 RS301to312.d66 (Ns300p1836 rfl) rfl) rfl rfl) Ns300p1924 

noncomputable def Ns300p1926 := nat_lit 208644347556442903953898571993978962925 

noncomputable def Ns300p1927 := nat_lit 5316911983139663491615228241121378304 

noncomputable def Ns300p1928 := nat_lit 43478443892788876963759658878782804717984186661583263226153 

noncomputable abbrev qz247 := qz530

noncomputable def Ns300p1929 := @Enclosure.Real.IsNear.mulLit_tf qz247 qz220 Ns300p1926 Ns300p1927 Ns300p1928 Ns300p1603 63605327958504969 72057594037927936 

noncomputable def Ns300p1930 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz224 Ns300p1374 Ns300p1378 Ns300p1376 Ns300p1379 266825477 268435456 59702777 147975045120000 Ns300p1926 

noncomputable abbrev qz540 := (@HMul.hMul Real Real Real qz623 qz728 qz743)

noncomputable abbrev qz248 := qz540

noncomputable def Ns300p1931 := @Ns300p1929 7731466552243717 9930437178351943680000 Ns300p1876 Ns300p1554 Ns300p1877 Ns300p1878 (@Enclosure.Real.IsNear.neg qz248 Bool.false Ns300p1926 Ns300p1927 Ns300p1928 Ns300p1603 (@Ns300p1930 Ns300p1927 Ns300p1928 Ns300p1603 RS301to312.d68 qz533 rfl)) qz538 

noncomputable def Ns300p1932 := nat_lit 625933042669328711861695715981936888775 

noncomputable def Ns300p1933 := @Enclosure.Real.IsNear.mulLit_tt qz234 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz221) Ns300p1932 Ns300p1927 Ns300p1928 Ns300p1608 Ns300p1896 

noncomputable def Ns300p1934 := @Enclosure.Real.IsNear.mulLit_ft qz319 qz247 3 1 0 1 Ns300p1926 Ns300p1927 Ns300p1928 

noncomputable def Ns300p1935 := @Ns300p1934 Ns300p1603 Ns300p1932 Ns300p1927 Ns300p1928 Ns300p1608 qz502 (@Enclosure.Real.IsNear.neg qz248 Bool.false Ns300p1926 Ns300p1927 Ns300p1928 Ns300p1603 (@Ns300p1930 Ns300p1927 Ns300p1928 Ns300p1603 RS301to312.d68 qz533 rfl)) rfl 

noncomputable def Ns300p1936 := @Ns300p1933 Ns300p1898 Ns300p1899 Ns300p1900 Ns300p1789 Ns300p1790 Ns300p1791 Ns300p1792 Ns300p1935 (Ns300p1904 (@Ns300p1908 Ns300p1909 Ns300p1896 Ns300p1898 Ns300p1899 Ns300p1900 qz539 (@Ns300p1910 Ns300p1911 Ns300p1912 Ns300p1913 Ns300p1914 Ns300p1915 Ns300p1906 Ns300p1916 Ns300p1909 Ns300p1917 Ns300p1905 Ns300p1906 Ns300p1907 Ns300p1909 (@Ns300p1918 Ns300p1912 Ns300p1913 Ns300p1914 (@Ns300p1919 Ns300p1485 128780979 268435456 7704019 18496880640000 Ns300p1911 Ns300p1912 Ns300p1913 Ns300p1914 qz240 (Ns300p1836 rfl) rfl)) (Ns300p1923 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns300p1937 := @Ns300p1787 Ns300p1788 Ns300p1764 Ns300p1789 Ns300p1790 Ns300p1791 Ns300p1792 Ns300p1793 Ns300p1780 Ns300p1761 Ns300p1781 Ns300p1764 (@Ns300p1798 Ns300p1799 Ns300p1761 Ns300p1800 Ns300p1764 Ns300p1801 Ns300p1786 Ns300p1761 Ns300p1788 Ns300p1764 Ns300p1851 (@Ns300p1854 Ns300p1855 Ns300p1856 Ns300p1857 Ns300p1799 Ns300p1761 Ns300p1800 Ns300p1764 Ns300p1865 (@Ns300p1867 Bool.false Ns300p1853 Ns300p1855 Ns300p1856 Ns300p1857 (BSN.iteratedDeriv_two_correction_mk qz221 qz532) (@Ns300p1868 268435456 55 134217728 Ns300p1869 Ns300p1870 Ns300p1871 Ns300p1872 Ns300p1853 Ns300p1855 Ns300p1856 Ns300p1857 qz539 (@Ns300p1874 Ns300p1875 Ns300p1872 Ns300p1876 Ns300p1554 Ns300p1877 Ns300p1878 Ns300p1879 Ns300p1869 Ns300p1870 Ns300p1871 Ns300p1872 (Ns300p1925 rfl rfl) (Ns300p1931 rfl) rfl rfl) rfl)) rfl) rfl rfl) Ns300p1936 

noncomputable def Ns300p1938 := nat_lit 20298398517986432339872218477157989122673329723951625 

noncomputable def Ns300p1939 := nat_lit 748288838313422294120286634350736906063837462003712 

noncomputable def Ns300p1940 := nat_lit 1173312564022139050362831709336884107762025554736721904429831040101018967436461353951 

noncomputable def Ns300p1941 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz321 RSCompact.c11) qz235) qz220 Ns300p1938 Ns300p1939 Ns300p1940 Ns300p1617 63605327958504969 72057594037927936 7731466552243717 

noncomputable def Ns300p1942 := @Enclosure.Real.IsNear.mulLit_ff qz729 qz235 Ns300p1380 Ns300p1381 Ns300p1382 Ns300p1383 29355723 268435456 59702777 147975045120000 Ns300p1938 

noncomputable abbrev qz541 := (Ns300p1860 (@Ns300p1861 70560000 (Ns300p1773 rfl) (Enclosure.sfrac_false_div 58829105 536870912) (Ns300p1864 rfl rfl) rfl rfl) rfl)

noncomputable def Ns300p1943 := Ns300p1759 (@Ns300p1763 Ns300p1764 Ns300p1752 Ns300p1753 Ns300p1754 Ns300p1755 qz539 (@Ns300p1779 Ns300p1780 Ns300p1761 Ns300p1781 Ns300p1764 Ns300p1782 Ns300p1475 Ns300p1783 Ns300p1784 Ns300p1785 Ns300p1760 Ns300p1761 Ns300p1762 Ns300p1764 (Ns300p1937 rfl rfl) (@Ns300p1941 9930437178351943680000 Ns300p1782 Ns300p1475 Ns300p1783 Ns300p1784 (@Ns300p1942 Ns300p1939 Ns300p1940 Ns300p1617 RS301to312.d69 qz541 rfl) qz538 rfl) rfl rfl) rfl) 

noncomputable def Ns300p1944 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correctionLinear qz221) (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz221) qz492)) Bool.true Ns300p1747 Ns300p1748 Ns300p1749 Ns300p1750 (BSN.correctionLinear_mk qz221) (@Enclosure.Real.IsNear.neg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz221) qz492) Bool.false Ns300p1747 Ns300p1748 Ns300p1749 Ns300p1750 (@Ns300p1756 Ns300p1748 Ns300p1749 Ns300p1750 Ns300p1943 RS301to312.d70 rfl)) 

noncomputable def Ns300p1945 := @Enclosure.Real.IsNear.inv_image qz219 168064741 16777216 1 1048576 1674800 1674802 16777216 qz520 rfl 

noncomputable def Ns300p1946 := @Ns300p1751 Ns300p1707 Ns300p1717 Ns300p1710 Ns300p1944 (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz219) Bool.false 3349602 33554432 2 33554432 1674801 16777216 1 16777216 (Ns300p1945 rfl rfl rfl rfl rfl) rfl) 

noncomputable abbrev qz542 := (BSN.correction_mk qz221 qz749)

noncomputable def Ns300p1947 := @Ns300p1709 Ns300p1710 Ns300p1631 Ns300p1627 Ns300p1633 Ns300p1629 (Ns300p1711 qz488 (@Enclosure.Real.IsNear.of_eq qz519 (@Inv.inv Real Real.instInv (Real.sqrt qz219)) Bool.false 10601603 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz213 (BSN.t_div_two_pi_nonneg qz212 630512 1000 qz215)) Ns300p1715) rfl) (@Ns300p1718 Ns300p1719 Ns300p1706 Ns300p1707 Ns300p1708 Ns300p1710 (@Ns300p1720 1099511627776 267995034260717 22166154415964160000 qz542 (@Ns300p1721 16777216 460015 524288 59702777 9248440320000 970541947075 1099511627776 267995034260717 22166154415964160000 (@Ns300p1722 16777216 (Ns300p1732 rfl rfl rfl rfl rfl) rfl) (Ns300p1746 rfl) rfl)) (Ns300p1946 rfl) rfl rfl) 

noncomputable abbrev qz753 := (@BSN.floor_sqrt_eq_dec qz212 630512 1000 10 qz215 rfl rfl rfl)

noncomputable abbrev qz543 := qz753

noncomputable def Ns300p1948 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz212) (hardyZApproximantRS qz212) Bool.false Ns300p1626 Ns300p1627 Ns300p1628 Ns300p1629 (@Eq.refl Real (hardyZApproximantRS qz212)) (Ns300p1630 (BSN.hardyZApproximantRS_eq qz212 10 qz543) (@Ns300p1632 Ns300p1633 Ns300p1629 Ns300p1634 Ns300p1626 Ns300p1627 Ns300p1628 Ns300p1629 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz212) qz212 10) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz212) qz212 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz212) qz212 10)) Bool.false 42753623 134217728 168399 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz212) qz212 10) (Ns300p1705 (Ns300p1704 rfl rfl rfl rfl) rfl rfl)) (Ns300p1947 rfl) rfl rfl)) 

theorem RS301to312.d73 : Enclosure.Real.IsNear (hardyZApproximantRS qz212) Bool.false Ns300p1626 Ns300p1627 Ns300p1628 Ns300p1629 := Ns300p1948 

noncomputable def Ns300p1949 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) qz44 Bool.false 21776601 1073741824 

theorem RS301to312.d74 : Enclosure.Real.IsNear (hardyZErrorBoundRS qz4) Bool.false 21776601 1073741824 201 1073741824 := @Ns300p1949 201 1073741824 (BSN.hardyZErrorBoundRS_mk qz4 615476 1000 qz10 rfl rfl) (@Ns300p316 1 1073741824 1 1073741824 2922805909782528 21776601 1073741824 201 1073741824 (@Ns300p317 134217728 25 134217728 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns300p318 (Ns300p324 rfl rfl rfl rfl) rfl) rfl) (@Ns300p325 33554432 1 33554432 1 1073741824 1 1073741824 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns300p326 1 33554432 1 33554432 (@Ns300p331 16777216 (@Ns300p336 17592186044416000 Ns300p327 Ns300p328 Ns300p329 Ns300p330 (@Ns300p337 Ns300p333 Ns300p334 Ns300p335 (Ns300p323 rfl) (Ns300p323 rfl) rfl) (Ns300p323 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) 

noncomputable def Ns300p1950 := nat_lit 5928433126034665601334298955732780680711994236933277452755157150032480709964132517747666363477534621260393016464934725400216975322373 

noncomputable def Ns300p1951 := nat_lit 5678427533559428832416592249125035424637823130369672345949142181098744438385921275985867583701277855943457200048954515105739075223552 

noncomputable def Ns300p1952 := nat_lit 156631733376717726901552975802069802992108206622701963531796772559910449600348698632430607365055514623941969474209351938178655062770626643548142306026417668555716235757162911496369769 

noncomputable def Ns300p1953 := nat_lit 124191378242289911043572349832984271737652420484780277527654530654062487904106231279943217822293361960214856922835064400642048000000000000000000000000000000000000000000000000000000000000 

noncomputable abbrev qz866 := (Enclosure.sfrac Bool.false 631875 1000)

noncomputable abbrev qz754 := qz866

noncomputable abbrev qz544 := qz754

noncomputable abbrev qz249 := qz544

noncomputable abbrev qz867 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 631875 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz755 := qz867

noncomputable abbrev qz545 := qz755

noncomputable abbrev qz250 := qz545

noncomputable abbrev qz868 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 631875 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz756 := qz868

noncomputable abbrev qz546 := qz756

noncomputable abbrev qz251 := (Zeta.RiemannSiegel.correction qz546)

noncomputable abbrev qz252 := qz546

noncomputable abbrev qz869 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 631875 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz757 := qz869

noncomputable abbrev qz547 := qz757

noncomputable abbrev qz253 := qz547

noncomputable abbrev qz548 := (@HMul.hMul Real Real Real qz5 qz719 (@HPow.hPow Real Real Real qz627 qz250 qz8))

noncomputable abbrev qz758 := (Zeta.RiemannSiegel.correctionLinear qz252)

noncomputable abbrev qz549 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) qz251 (@HMul.hMul Real Real Real qz5 qz758 (@Inv.inv Real Real.instInv qz253)))

noncomputable def Ns300p1954 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz249) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz249) qz249 10) (@HMul.hMul Real Real Real qz5 qz548 qz549)) Bool.true Ns300p1950 Ns300p1951 Ns300p1952 Ns300p1953 

noncomputable def Ns300p1955 := nat_lit 1535040645954046529162625626102142414622550400813064037488055520028425957651678093886795316341639265533368847024343112797370104294661 

noncomputable def Ns300p1956 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz249) qz249 10) (@HMul.hMul Real Real Real qz5 qz548 qz549) 103844093 134217728 84375 67108864 Ns300p1955 Ns300p1951 

noncomputable def Ns300p1957 := nat_lit 487717301684609900773212682282111043330427007726869982368622145435807071621595395439306130154527246281567520985876738178655062770626643548142306026417668555716235757162911496369769 

noncomputable def Ns300p1958 := nat_lit 795700824776310466250843374311226398087457288830278187302424532960314687095212828023011456607976875906910447056990130511521013134800971628544 

noncomputable def Ns300p1959 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz249) qz249 Real.cos BSN.quadSignPos 9 10 631875 1000 200 268435456 134217728 4503599627370496 Bool.false 306123538538 2481 618095470 62 84886744 8 

noncomputable def Ns300p1960 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz249) qz249 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 631875 1000 110 157 268435456 134217728 4503599627370496 Bool.false 306123538538 2481 

noncomputable def Ns300p1961 := Ns300p1960 558195838 62 94906264 8 589812974 62 89478488 8 Bool.true 26228133 126933 Bool.true 204139488 Bool.true 364318170 14148475504056880 1 Bool.false 194483107 Bool.true Bool.false 262334718 Bool.true Bool.true 182433203 

noncomputable def Ns300p1962 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz249) qz249 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 631875 1000 5 56 268435456 134217728 4503599627370496 Bool.false 306123538538 2481 

noncomputable def Ns300p1963 := Ns300p1962 480971758 62 109588312 8 522351262 62 101459064 8 Bool.true 21855703 94162 Bool.false 101221810 Bool.true 324349155 14148475504056880 1 Bool.false 98840021 Bool.true Bool.false 95191061 Bool.false Bool.true 26228133 

noncomputable def Ns300p1964 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz249) qz249 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 631875 1000 168 78 268435456 134217728 4503599627370496 Bool.false 306123538538 2481 

noncomputable def Ns300p1965 := Ns300p1964 372130544 61 134217720 8 432030192 61 120047984 16 Bool.true 63578473 55274 Bool.false 145103099 Bool.false 245181563 14148475504056880 1 Bool.false 230163318 Bool.false Bool.false 164035448 Bool.true Bool.true 21855703 

noncomputable def Ns300p1966 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz249) qz249 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 631875 1000 447 284 268435456 134217728 4503599627370496 Bool.false 306123538538 2481 

noncomputable def Ns300p1967 := Ns300p1966 186065264 61 189812528 16 294906480 61 154981288 8 Bool.true 268435336 2549 Bool.false 72679412 Bool.false 28796860 14148475504056880 1 Bool.false 71794681 Bool.false Bool.false 266892321 Bool.false Bool.true 63578473 

noncomputable def Ns300p1968 := nat_lit 171385624664198252939137746067425457244333 

noncomputable def Ns300p1969 := nat_lit 150285660907669704957309714886276677632 

noncomputable def Ns300p1970 := nat_lit 48350146123985497954101562500000000 

noncomputable def Ns300p1971 := nat_lit 183307545055704757850694580078125000000 

noncomputable abbrev qz870 := (@Eq.refl Real (Enclosure.sfrac Bool.false 631875 1000))

noncomputable abbrev qz759 := qz870

noncomputable abbrev qz550 := qz759

noncomputable abbrev qz254 := qz550

noncomputable def Ns300p1972 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz249 631875 1000 1597065062500 16000000 1263750 4000 2000 Ns300p1970 Ns300p1971 qz254 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns300p1973 := nat_lit 1882898708468974946841112932869664447264400634765625000000 

noncomputable abbrev qz551 := (@HMul.hMul Real Real Real qz623 qz629 (@HSub.hSub Real Real Real qz628 qz630 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz631 (@Nat.cast Real Real.instNatCast 1263750)))))

noncomputable abbrev qz760 := (Real.log (Enclosure.sfrac Bool.false 1597065062500 16000000))

noncomputable abbrev qz761 := (Enclosure.sfrac Bool.false 631875 2000)

noncomputable abbrev qz255 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 631875 4000) qz760) qz551) qz761)

noncomputable abbrev qz552 := (@HSub.hSub Real Real Real qz11 qz255 (@HMul.hMul Real Real Real qz5 qz761 (Real.log Real.pi)))

noncomputable def Ns300p1974 := @Enclosure.Real.IsNear.addLit_ft_p qz552 (Enclosure.sfrac Bool.true Ns300p1970 Ns300p1971) 10271803833258400445 9007199254740992 133554700148967131 14450688000000000000000 Ns300p1970 Ns300p1971 0 1 Ns300p1973 

noncomputable def Ns300p1975 := nat_lit 5514632691846533378568355840 

noncomputable abbrev qz553 := (@HMul.hMul Real Real Real qz5 qz761 (Real.log Real.pi))

noncomputable def Ns300p1976 := @Enclosure.Real.IsNear.subLit_ff_p qz255 qz553 13529375413236456125 9007199254740992 15996883917461 3528000000000000000 194166396855 536870912 5055 1073741824 Ns300p1975 10271803833258400445 9007199254740992 

noncomputable abbrev qz256 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz327 (Enclosure.sfrac Bool.false 631875 4000) qz760) qz551)

noncomputable def Ns300p1977 := @Enclosure.Real.IsNear.subLit_ff_p qz256 qz761 16375087427781188285 9007199254740992 15996883917461 3528000000000000000 631875 2000 0 1 27058750826472912250000 13529375413236456125 9007199254740992 15996883917461 3528000000000000000 

noncomputable def Ns300p1978 := nat_lit 36873418818957326694792994414919680 

noncomputable def Ns300p1979 := nat_lit 55664212960505657015926784 

noncomputable def Ns300p1980 := nat_lit 174635977436481647848920770106346090969246283468142760737165478507065822341304151450458448380231857299804687500000000000000000000 

noncomputable def Ns300p1981 := nat_lit 2568567757223790179117012395032987980703387113112642490629932366739567800883037307357881218194961547851562500000000000000000000 

noncomputable def Ns300p1982 := nat_lit 2328689179499464102843485673806921272641192733642845629485427366711647323427314404398202896118164062500000000000000000000 

noncomputable def Ns300p1983 := BSN.log_dyadic_bound 548489062500 2645641062500 6 5 Ns300p1980 134217728 35280000 Ns300p1981 Ns300p1982 56470036 3194130125000 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 548489062500) (BSN.artanhQ 2645641062500) 0 5 Ns300p1981 Ns300p1980 Ns300p1982 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns300p1984 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 631875 4000) qz760 631875 4000 0 1 3240083633020151 281474976710656 781250441 27562500000000000 16378622764916863305 9007199254740992 263281398617 58800000000000000 (Enclosure.Real.IsNear.const Bool.false 631875 4000) (BSN.isNear_log_sfrac 1597065062500 16000000 3240083633020151 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1597065062500) qz335)) Bool.false Ns300p1979 Ns300p94 1000000564480000 35280000000000000000000 3240083633020151 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1597065062500 16000000 16 3194130125000 2097152000000 56470036 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns300p1983 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns300p1985 := BSN.arctan_dyadic_bound_f 1000 1263750 1 0 16777216 4410000 0 1 1 0 1 1 13275 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1263750) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1263750) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns300p1986 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1263750))) 884279719003555 562949953421312 1 2000000000000000 13275 16777216 1 4410000 14828278689510279086080 883834283918755 562949953421312 200000000441 882000000000000000 qz16 (Ns300p1985 rfl) rfl rfl 

noncomputable abbrev qz257 := qz551

noncomputable def Ns300p1987 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 631875 4000) qz760) qz257 16378622764916863305 9007199254740992 263281398617 58800000000000000 883834283918755 2251799813685248 200000000441 3528000000000000000 Ns300p1978 16375087427781188285 9007199254740992 15996883917461 3528000000000000000 (Ns300p1984 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1263750)))) 1 4 0 1 883834283918755 562949953421312 200000000441 882000000000000000 883834283918755 2251799813685248 200000000441 3528000000000000000 qz340 Ns300p1986 rfl) 

noncomputable def Ns300p1988 := @Ns300p1974 Ns300p1968 Ns300p1969 133554700148967131 14450688000000000000000 (@Ns300p1976 133554700148967131 14450688000000000000000 (Ns300p1977 (Ns300p1987 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 631875 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz761 (Real.log Real.pi) 631875 2000 0 1 38410761 33554432 1 67108864 194166396855 536870912 5055 1073741824 (Enclosure.Real.IsNear.const Bool.false 631875 2000) RS301to312.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns300p1970 Ns300p1971) 

noncomputable def Ns300p1989 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz249) Bool.false Ns300p1968 Ns300p1969 133554700148967131 14450688000000000000000 38265442317 33554432 311 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz249) (@HAdd.hAdd Real Real Real qz341 qz552 (Enclosure.sfrac Bool.true Ns300p1970 Ns300p1971)) Bool.false Ns300p1968 Ns300p1969 133554700148967131 14450688000000000000000 Ns300p1972 (Ns300p1988 rfl rfl)) 

noncomputable def Ns300p1990 := BSN.cos_dyadic_bound_f 62877352 68719476736 1 0 33554432 8828614 0 1 1 0 1 1 33554417 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 62877352) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 62877352) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns300p1991 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz249) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 38265442317) qz349) Bool.false 38265442317 33554432 311 33554432 Bool.true 33554417 33554432 1 4410000 (Ns300p1989 rfl) (Enclosure.sfrac_false_div 38265442317 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 38265442317) qz349) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4424600305686087204864) qz353) 226375608064910080 72057594037927936 Bool.false 33554417 33554432 181 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q2 38265442317 33554432 226375608064910080 72057594037927936 181 4424600305686087204864 Ns300p94 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554417 33554432 4424600305686087204864 Ns300p94 62877352 68719476736 8828614 8820000 (Ns300p1990 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns300p1992 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz249) Bool.false Ns300p1968 Ns300p1969 133554700148967131 14450688000000000000000 306123538538 268435456 2481 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz249) (@HAdd.hAdd Real Real Real qz341 qz552 (Enclosure.sfrac Bool.true Ns300p1970 Ns300p1971)) Bool.false Ns300p1968 Ns300p1969 133554700148967131 14450688000000000000000 Ns300p1972 (Ns300p1988 rfl rfl)) 

noncomputable def Ns300p1993 := Ns300p1967 55274 BSN.abs_quadSignPos (BSN.cos_quad_nat3 447 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 71794681 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 284 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266892321 268435456) qz254 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz249) qz249 1) Bool.true 33554417 33554432 87816527 9248440320000 268435336 268435456 2549 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz249) qz249 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz249)) Bool.true 33554417 33554432 87816527 9248440320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz249) qz249) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz249)) Bool.true 33554417 33554432 1405064432 147975045120000 33554417 33554432 87816527 9248440320000 (Ns300p1991 rfl rfl) rfl)) rfl) (Ns300p1992 rfl) RS301to312.d7 

noncomputable def Ns300p1994 := nat_lit 27902660842591552156512079073536 

noncomputable def Ns300p1995 := BSN.sin_dyadic_bound_f 72679412 268435456 2 1 268435456 134217728 Ns300p1994 Ns300p392 Ns300p1994 Ns300p1994 Ns300p393 Ns300p1994 71794681 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 72679412) qz344 0 1 Ns300p1994 Ns300p392 Ns300p1994 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 72679412) qz345 0 1 Ns300p1994 Ns300p393 Ns300p1994 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1996 := nat_lit 687670730991793347822912160000 

noncomputable def Ns300p1997 := BSN.cos_dyadic_bound_f 28796860 268435456 2 1 268435456 134217728 Ns300p1996 Ns300p133 Ns300p1996 Ns300p1996 Ns300p134 Ns300p1996 266892321 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 28796860) qz342 0 1 Ns300p1996 Ns300p133 Ns300p1996 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 28796860) qz343 0 1 Ns300p1996 Ns300p134 Ns300p1996 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p1998 := nat_lit 3867208770401752262518753324681933469975698407672988301390187394944481 

noncomputable def Ns300p1999 := nat_lit 196523053268543382418961854226295750519816165859129222839172255201 

noncomputable def Ns300p2000 := nat_lit 11601233265098719700791422050337347818426055590687246645724883840323041 

noncomputable def Ns300p2001 := BSN.cos_dyadic_bound_f 145103099 268435456 3 2 268435456 134217728 Ns300p1998 Ns300p110 Ns300p1999 Ns300p2000 Ns300p113 Ns300p1999 230163318 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 145103099) qz342 0 2 Ns300p1998 Ns300p110 Ns300p1999 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 145103099) qz343 0 2 Ns300p2000 Ns300p113 Ns300p1999 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p2002 := nat_lit 31535513762996869929247784828833911335359174928979324477067136477061601 

noncomputable def Ns300p2003 := nat_lit 13058776057138037453655068424374277321690140304578328315597217751521 

noncomputable def Ns300p2004 := nat_lit 94580423736876333712836044349652985451434144506328816774570214995681761 

noncomputable def Ns300p2005 := BSN.cos_dyadic_bound_f 245181563 268435456 3 2 268435456 134217728 Ns300p2002 Ns300p110 Ns300p2003 Ns300p2004 Ns300p113 Ns300p2003 164035448 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 245181563) qz342 0 2 Ns300p2002 Ns300p110 Ns300p2003 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 245181563) qz343 0 2 Ns300p2004 Ns300p113 Ns300p2003 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p2006 := Ns300p1965 94162 BSN.abs_quadSignPos (BSN.cos_quad_nat0 168 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 230163318 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 78 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 164035448 268435456) qz254 rfl rfl (Ns300p1993 RS301to312.d9 RS301to312.d11 RS301to312.d13 RS301to312.d17 (Ns300p1995 rfl rfl) (Ns300p1997 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns300p1992 rfl) RS301to312.d19 RS301to312.d21 RS301to312.d23 RS301to312.d25 RS301to312.d17 (Ns300p2001 rfl rfl) (Ns300p2005 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns300p2007 := nat_lit 104977540985879967647708911210000 

noncomputable def Ns300p2008 := BSN.sin_dyadic_bound_f 101221810 268435456 2 1 268435456 134217728 Ns300p2007 Ns300p392 Ns300p2007 Ns300p2007 Ns300p393 Ns300p2007 98840021 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 101221810) qz344 0 1 Ns300p2007 Ns300p392 Ns300p2007 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 101221810) qz345 0 1 Ns300p2007 Ns300p393 Ns300p2007 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p2009 := nat_lit 5962750025773649152221913127164970040837331120288786867775316500953248084880208738409720580007612260420640625 

noncomputable def Ns300p2010 := nat_lit 1355667704110843094080854735500867971296380487181507800801287034597136359277566265880333797695556640625 

noncomputable def Ns300p2011 := nat_lit 36143451105070186148696828492858528843721626165360472658952065897108770963384329297190541313917939333598240625 

noncomputable def Ns300p2012 := BSN.cos_dyadic_bound_f 324349155 268435456 4 3 268435456 134217728 Ns300p2009 Ns300p122 Ns300p2010 Ns300p2011 Ns300p125 Ns300p2010 95191061 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 324349155) qz342 0 3 Ns300p2009 Ns300p122 Ns300p2010 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 324349155) qz343 0 3 Ns300p2011 Ns300p125 Ns300p2010 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p2013 := Ns300p1963 126933 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 5 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 98840021 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 56 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 95191061 268435456) qz254 rfl rfl (Ns300p2006 rfl rfl) (Ns300p1992 rfl) RS301to312.d27 RS301to312.d29 RS301to312.d31 RS301to312.d33 RS301to312.d17 (Ns300p2008 rfl rfl) (Ns300p2012 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p2014 := nat_lit 15151768767426571138838895425068476928939684052290312581785328367435776 

noncomputable def Ns300p2015 := nat_lit 3015894668273457761784277623317863811030120692220261038461284253696 

noncomputable def Ns300p2016 := nat_lit 45449274512943166500993117719958795059196991915486497223279062533799936 

noncomputable def Ns300p2017 := BSN.cos_dyadic_bound_f 204139488 268435456 3 2 268435456 134217728 Ns300p2014 Ns300p110 Ns300p2015 Ns300p2016 Ns300p113 Ns300p2015 194483107 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 204139488) qz342 0 2 Ns300p2014 Ns300p110 Ns300p2015 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 204139488) qz343 0 2 Ns300p2016 Ns300p113 Ns300p2015 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p2018 := nat_lit 24673372505436125896746634685865849111643289321937399928363519799189753827667111186386153252410829889702400000 

noncomputable def Ns300p2019 := nat_lit 5467263194383255277202600229120248423068126968887937051847922439769001950664883352650542561000000000000 

noncomputable def Ns300p2020 := nat_lit 123281371449259777845577432109985100263665598680678069228188953985392387755287173622900145784793006504512000000 

noncomputable def Ns300p2021 := BSN.sin_dyadic_bound_f 364318170 268435456 4 3 268435456 134217728 Ns300p2018 Ns300p237 Ns300p2019 Ns300p2020 Ns300p240 Ns300p2019 262334718 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 364318170) qz344 0 3 Ns300p2018 Ns300p237 Ns300p2019 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 364318170) qz345 0 3 Ns300p2020 Ns300p240 Ns300p2019 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p2022 := Ns300p1961 155566 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 110 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 194483107 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 157 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 262334718 268435456) qz254 rfl rfl (Ns300p2013 rfl) (Ns300p1992 rfl) RS301to312.d35 RS301to312.d37 RS301to312.d39 RS301to312.d41 RS301to312.d17 (Ns300p2017 rfl rfl) (Ns300p2021 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns300p2023 := nat_lit 1022488023423283424886235609744438167559842180873615072084622833582336 

noncomputable def Ns300p2024 := nat_lit 13739381914649198391836366340388463965913823561412012074355097856 

noncomputable def Ns300p2025 := nat_lit 3067436591506020976261923156500633725751594714973722392229719790551296 

noncomputable def Ns300p2026 := BSN.cos_dyadic_bound_f 104050914 268435456 3 2 268435456 134217728 Ns300p2023 Ns300p110 Ns300p2024 Ns300p2025 Ns300p113 Ns300p2024 248520589 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 104050914) qz342 0 2 Ns300p2023 Ns300p110 Ns300p2024 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 104050914) qz343 0 2 Ns300p2025 Ns300p113 Ns300p2024 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p2027 := Ns300p1959 Bool.true 182433203 155566 Bool.true 104050914 14148475504056880 1 Bool.false 248520589 Bool.false Bool.true 103844093 168750 BSN.abs_quadSignPos (BSN.cos_quad_nat0 200 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 248520589 268435456) qz254 rfl (Ns300p2022 rfl) (Ns300p1992 rfl) RS301to312.d58 RS301to312.d60 RS301to312.d17 (Ns300p2026 rfl rfl) rfl 

noncomputable def Ns300p2028 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz249) qz249 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz249) qz249 10) 103844093 268435456 168750 268435456 103844093 268435456 168750 268435456 55750872914722816 103844093 134217728 84375 67108864 (Ns300p2027 rfl rfl rfl rfl) 

noncomputable def Ns300p2029 := nat_lit 144871450137468184963819962313859736120342461453942719580189275439052775097387191672574967229401619887328750391245722068544381 

noncomputable def Ns300p2030 := nat_lit 169230328010303641331690318856389386196071598838855992136870091590247882556495704531248437872567112920983350278405979725889536 

noncomputable def Ns300p2031 := nat_lit 91459843877359229310040148911196607686202696296534490389184666933534309057497720087770748684534353163163572610467956767526692004491719994887923581859861002115500356137422559 

noncomputable def Ns300p2032 := @Enclosure.Real.IsNear.mulLit_ff qz548 qz549 10595881 33554432 1 33554432 Ns300p2029 Ns300p2030 Ns300p2031 

noncomputable abbrev qz554 := (@HPow.hPow Real Real Real qz627 qz250 qz8)

noncomputable def Ns300p2033 := @Enclosure.Real.IsNear.mulLit_ff qz477 qz554 1 1 0 1 10595881 33554432 1 33554432 10595881 33554432 1 33554432 

noncomputable def Ns300p2034 := @Enclosure.Real.IsNear.sqrt_image qz250 26995484415 268435456 5055 268435456 168246283 168246315 16777216 (@Enclosure.Real.IsNear.of_eq qz250 (@HMul.hMul Real Real Real qz5 qz249 qz3) Bool.false 26995484415 268435456 5055 268435456 (BSN.t_div_two_pi_mk qz249 631875 1000 qz254) (@Enclosure.Real.IsNear.mulLit_ff qz249 qz3 631875 1000 0 1 5340353 33554432 1 33554432 26995484415 268435456 5055 268435456 (Enclosure.Real.IsNear.const Bool.false 631875 1000) RS301to312.d44 rfl)) 

noncomputable abbrev qz555 := (@Enclosure.Real.IsNear.recentre' qz253 Bool.false 336492598 33554432 32 33554432 168246299 16777216 1 1048576 (Ns300p2034 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns300p2035 := @Enclosure.Real.IsNear.sqrt_image qz253 168246299 16777216 1 1048576 53129127 53129133 16777216 qz555 rfl 

noncomputable def Ns300p2036 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz253) 26564565 8388608 3 16777216 5297940 5297941 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz253) Bool.false 106258260 33554432 6 33554432 26564565 8388608 3 16777216 (Ns300p2035 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns300p2037 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz253)) Bool.false 10595881 33554432 1 33554432 10595881 33554432 1 33554432 (Ns300p2036 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns300p2038 := nat_lit 318925861517083509636773142412832838953375292597335506159734493893572961172042077975617156362426352220514609208673884345475 

noncomputable def Ns300p2039 := nat_lit 1364086833819257645521672987133730857793499236576251224311592812308192552577156175198812028104657660068427190333147167526692004491719994887923581859861002115500356137422559 

noncomputable abbrev qz556 := (@HMul.hMul Real Real Real qz5 qz758 (@Inv.inv Real Real.instInv qz253))

noncomputable def Ns300p2040 := @Enclosure.Real.IsNear.addLit_ft_p qz251 qz556 241490152406001 281474976710656 944259116936117 77581540455874560000 Ns300p2038 Ns300p2030 Ns300p2039 Ns300p1710 

noncomputable def Ns300p2041 := nat_lit 40777688053482819332347375214263012829958032081867544386221623705643759059685946378354230844362043363524620303135380667387319859253331623936 

noncomputable abbrev qz871 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 631875 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1)))

noncomputable abbrev qz762 := (Real.cos qz871)

noncomputable abbrev qz557 := qz762

noncomputable abbrev qz258 := (@Inv.inv Real Real.instInv qz557)

noncomputable abbrev qz763 := (@HSub.hSub Real Real Real qz810 (@HMul.hMul Real Real Real qz807 qz868 qz868) qz868)

noncomputable abbrev qz558 := (@HMul.hMul Real Real Real qz623 qz621 (@HSub.hSub Real Real Real qz628 qz763 qz639))

noncomputable abbrev qz259 := (Real.cos qz558)

noncomputable def Ns300p2042 := @Enclosure.Real.IsNear.of_eq qz251 (@HMul.hMul Real Real Real qz5 qz258 qz259) Bool.false 241490152406001 

noncomputable def Ns300p2043 := @Enclosure.Real.IsNear.mulLit_ff qz258 qz259 34090467 33554432 217 

noncomputable def Ns300p2044 := @Enclosure.Real.IsNear.recentre' qz258 Bool.false 34090467 33554432 217 33554432 34090467 33554432 217 

noncomputable abbrev qz260 := qz557

noncomputable def Ns300p2045 := @Enclosure.Real.IsNear.recentre' qz260 Bool.false 16513413 16777216 462187216 73987522560000 16513413 16777216 28886701 4624220160000 

noncomputable abbrev qz764 := qz871

noncomputable abbrev qz559 := qz764

noncomputable abbrev qz261 := qz559

noncomputable def Ns300p2046 := @Enclosure.Real.IsNear.cos_image qz261 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2979103) qz354) Bool.false 2979103 16777216 101 16777216 Bool.false 16513413 16777216 1 

noncomputable def Ns300p2047 := nat_lit 5397215081859719378502747 

noncomputable def Ns300p2048 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz252 884279719003555 140737488355328 1 500000000000000 474139 16777216 1 1048576 419271501688626564145 2361183241434822606848 Ns300p2047 

noncomputable def Ns300p2049 := @Enclosure.Real.IsNear.subLit_ff_p qz253 qz166 168246299 16777216 1 1048576 10 1 0 1 474139 474139 16777216 1 

noncomputable def Ns300p2050 := @Ns300p2049 1048576 qz555 qz724 

noncomputable def Ns300p2051 := @Enclosure.Real.IsNear.recentre' qz261 Bool.false 419271501688626564145 2361183241434822606848 Ns300p2047 Ns300p284 2979103 16777216 101 16777216 (@Ns300p2048 Ns300p284 RS301to312.d43 (Ns300p2050 rfl rfl) rfl) 

noncomputable def Ns300p2052 := nat_lit 78766595654800156461482881 

noncomputable def Ns300p2053 := BSN.cos_dyadic_bound_f 2979103 16777216 2 1 16777216 4410000 Ns300p2052 Ns300p1247 Ns300p2052 Ns300p2052 Ns300p1248 Ns300p2052 16513413 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 2979103) (BSN.cosEvenQ 16777216) 0 1 Ns300p2052 Ns300p1247 Ns300p2052 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 2979103) (BSN.cosOddQ 16777216) 0 1 Ns300p2052 Ns300p1248 Ns300p2052 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p2054 := @Enclosure.Real.IsNear.inv_image qz260 16513413 16777216 28886701 4624220160000 17045125 17045342 16777216 (Ns300p2045 (@Ns300p2046 4410000 (Ns300p2051 rfl) (Enclosure.sfrac_false_div 2979103 16777216) (Ns300p2053 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns300p2055 := @Enclosure.Real.IsNear.recentre' qz259 Bool.false 14167606 16777216 

noncomputable abbrev qz262 := qz558

noncomputable def Ns300p2056 := @Enclosure.Real.IsNear.cos_image qz262 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 2370827)) qz665) Bool.true 2370827 4194304 

noncomputable def Ns300p2057 := nat_lit 22391828907949751119993273045 

noncomputable def Ns300p2058 := nat_lit 239170974768679511402641897463349 

noncomputable def Ns300p2059 := @Enclosure.Real.IsNear.recentre' qz262 Bool.true Ns300p2057 Ns300p180 Ns300p2058 

noncomputable abbrev qz560 := (@HSub.hSub Real Real Real qz628 qz763 qz639)

noncomputable abbrev qz263 := qz560

noncomputable def Ns300p2060 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz263 884279719003555 140737488355328 1 500000000000000 25322110670119 

noncomputable abbrev qz561 := qz763

noncomputable abbrev qz264 := qz561

noncomputable def Ns300p2061 := @Enclosure.Real.IsNear.subLit_tf qz264 qz27 7729924625703 281474976710656 8862755 8796093022208 1 16 

noncomputable abbrev qz765 := (@HMul.hMul Real Real Real qz807 qz868 qz868)

noncomputable abbrev qz562 := qz765

noncomputable abbrev qz265 := qz562

noncomputable def Ns300p2062 := @Enclosure.Real.IsNear.subLit_ff_n qz265 qz252 224807791321 281474976710656 474147 8796093022208 474139 16777216 1 1048576 

noncomputable def Ns300p2063 := @Enclosure.Real.IsNear.mulLit_ff qz252 qz252 474139 16777216 1 1048576 474139 16777216 1 1048576 224807791321 281474976710656 

noncomputable def Ns300p2064 := nat_lit 16427623740827795753584499003442537028984163620364292961 

noncomputable def Ns300p2065 := nat_lit 3861888762982039923063034508418779142719222587902677483520 

noncomputable def Ns300p2066 := nat_lit 998157136599878994384348446612076538937225749795681 

noncomputable def Ns300p2067 := nat_lit 49280874908210187502764728313434386933874616409593287521 

noncomputable def Ns300p2068 := nat_lit 173784994334191796537836552878845061422365016455620486758400 

noncomputable def Ns300p2069 := BSN.cos_dyadic_bound_f 2370827 4194304 3 2 16777216 4410000 Ns300p2064 Ns300p2065 Ns300p2066 Ns300p2067 Ns300p2068 Ns300p2066 14167606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2370827) (BSN.cosEvenQ 4194304) 0 2 Ns300p2064 Ns300p2065 Ns300p2066 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2370827) (BSN.cosOddQ 4194304) 0 2 Ns300p2067 Ns300p2068 Ns300p2066 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p2070 := @Ns300p2055 488647216 73987522560000 7083803 8388608 30540451 4624220160000 (@Ns300p2056 107 16777216 Bool.false 14167606 16777216 1 4410000 (@Ns300p2059 Ns300p1241 2370827 4194304 107 16777216 (@Ns300p2060 281474976710656 8862755 8796093022208 Ns300p2057 Ns300p180 Ns300p2058 Ns300p1241 RS301to312.d43 (@Ns300p2061 0 1 405153770721904 25322110670119 281474976710656 8862755 8796093022208 (@Ns300p2062 129686615109138382848 7729924625703 281474976710656 8862755 8796093022208 (@Ns300p2063 474147 8796093022208 (Ns300p2050 rfl rfl) (Ns300p2050 rfl rfl) rfl) (Ns300p2050 rfl rfl) rfl rfl) qz358 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 2370827 4194304) (BSN.cos_neg_of_bound 2370827 4194304 Bool.false 14167606 16777216 1 4410000 (Ns300p2069 rfl rfl)) rfl rfl) 

noncomputable def Ns300p2071 := nat_lit 95315929654563364901529247547235789903958172161857026390041113098638148077694885836560977780973551965538003945823425 

noncomputable def Ns300p2072 := nat_lit 5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248382759272448 

noncomputable def Ns300p2073 := nat_lit 1625729171925824594826347734263140575501004895219530721451695649036566105496444339232350273197071970316976836068033896993891725773230481846422306833049822874480910147 

noncomputable def Ns300p2074 := @Enclosure.Real.IsNear.mulLit_tf qz758 (@Inv.inv Real Real.instInv qz253) Ns300p2071 Ns300p2072 Ns300p2073 Ns300p1750 3345987 33554432 1 33554432 Ns300p2038 

noncomputable def Ns300p2075 := nat_lit 168215763144073750022553112437301638115871535275916033930563231141784391687850226226615612298300214012233761325 

noncomputable def Ns300p2076 := nat_lit 9394170331095332911557922387157348109502730195633279482829163886128836100458433773854795993539074812127739904 

noncomputable def Ns300p2077 := nat_lit 28171772659677772208324709117182438321343101030650328694161306305893218944048129623160212906937906165421541632128107039559402930338924027501317729632728207840869 

noncomputable def Ns300p2078 := @Enclosure.Real.IsNear.mulLit_ff (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz252) qz492 Ns300p2075 Ns300p2076 Ns300p2077 Ns300p1755 566629 536870912 1 536870912 Ns300p2071 

noncomputable abbrev qz872 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 631875 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1)))

noncomputable abbrev qz766 := (@HMul.hMul Real Real Real qz807 qz805 (@HSub.hSub Real Real Real qz810 qz872 qz857))

noncomputable abbrev qz563 := (@HMul.hMul Real Real Real qz623 qz766 qz766)

noncomputable abbrev qz564 := qz766

noncomputable abbrev qz266 := (@HMul.hMul Real Real Real qz327 qz563 qz564)

noncomputable abbrev qz267 := (Real.sin qz558)

noncomputable abbrev qz268 := (@HMul.hMul Real Real Real qz327 qz319 qz564)

noncomputable def Ns300p2079 := @HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 qz266 qz267) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz268 qz189) qz259) 

noncomputable abbrev qz767 := (Real.sin qz871)

noncomputable abbrev qz565 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz623 qz621 qz767))

noncomputable abbrev qz269 := (@HMul.hMul Real Real Real qz327 qz319 qz565)

noncomputable abbrev qz566 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz623 qz728 qz762))

noncomputable abbrev qz270 := (@HMul.hMul Real Real Real qz327 qz319 qz566)

noncomputable abbrev qz567 := qz767

noncomputable abbrev qz271 := qz567

noncomputable def Ns300p2080 := @HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns300p2079 (@HMul.hMul Real Real Real qz5 qz269 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz252))) (@HMul.hMul Real Real Real qz5 qz270 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz252))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz498 qz271) qz251) 

noncomputable abbrev qz768 := (BSN.cos_two_pi_p_ne_zero_mk qz249 631875 1000 10 qz254 rfl rfl (@BSN.floor_sqrt_eq_dec qz249 631875 1000 10 qz254 rfl rfl rfl))

noncomputable abbrev qz568 := qz768

noncomputable def Ns300p2081 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz252) (@HMul.hMul Real Real Real qz5 qz258 Ns300p2080) Bool.false Ns300p2075 Ns300p2076 Ns300p2077 Ns300p1755 (BSN.iteratedDeriv_three_correction_mk qz252 qz568) 

noncomputable def Ns300p2082 := nat_lit 308399347408333020588901337341401706370388279435326544752678771899152207481952259694395705176086545725 

noncomputable def Ns300p2083 := nat_lit 17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592 

noncomputable def Ns300p2084 := nat_lit 102852553794074677777355767314820587875340626113718849773110961680531632685914578783361724692685651956140221464832541636363756071821790538855570356044509 

noncomputable def Ns300p2085 := @Enclosure.Real.IsNear.mulLit_ff qz258 Ns300p2080 545447857 536870912 225 536870912 Ns300p2082 Ns300p2083 Ns300p2084 

noncomputable def Ns300p2086 := @Enclosure.Real.IsNear.recentre' qz258 Bool.false 545447857 536870912 225 536870912 545447857 536870912 225 

noncomputable def Ns300p2087 := @Enclosure.Real.IsNear.recentre' qz260 Bool.false 264214418 268435456 15283910912 37881611550720000 132107209 134217728 59702777 147975045120000 

noncomputable def Ns300p2088 := @Enclosure.Real.IsNear.cos_image qz261 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23833361) qz735) Bool.false 23833361 134217728 209 536870912 Bool.false 264214418 268435456 1 

noncomputable def Ns300p2089 := nat_lit 890540488628786765108792999 

noncomputable def Ns300p2090 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz252 884279719003555 140737488355328 1 500000000000000 15172789 536870912 33 536870912 13416989593420230264895 75557863725914323419136 Ns300p2089 

noncomputable def Ns300p2091 := @Enclosure.Real.IsNear.subLit_ff_p qz253 qz166 5383881909 536870912 33 536870912 10 1 0 1 15172789 15172789 536870912 33 

noncomputable def Ns300p2092 := @Enclosure.Real.IsNear.sqrt_image qz250 431927806245 4294967296 5055 4294967296 2691940938 2691940971 268435456 (@Enclosure.Real.IsNear.of_eq qz250 (@HMul.hMul Real Real Real qz5 qz249 qz3) Bool.false 431927806245 4294967296 5055 4294967296 (BSN.t_div_two_pi_mk qz249 631875 1000 qz254) (@Enclosure.Real.IsNear.mulLit_ff qz249 qz3 631875 1000 0 1 85445659 536870912 1 536870912 431927806245 4294967296 5055 4294967296 (Enclosure.Real.IsNear.const Bool.false 631875 1000) RS301to312.d65 rfl)) 

noncomputable def Ns300p2093 := @Ns300p2091 536870912 (@Enclosure.Real.IsNear.recentre' qz253 Bool.false 5383881909 536870912 33 536870912 5383881909 536870912 33 536870912 (Ns300p2092 rfl rfl rfl rfl rfl rfl) rfl) qz724 

noncomputable def Ns300p2094 := @Enclosure.Real.IsNear.recentre' qz261 Bool.false 13416989593420230264895 75557863725914323419136 Ns300p2089 Ns300p1433 23833361 134217728 209 536870912 (@Ns300p2090 Ns300p1433 RS301to312.d64 (Ns300p2093 rfl rfl) rfl) 

noncomputable def Ns300p2095 := nat_lit 322657054534590245741125055041 

noncomputable def Ns300p2096 := nat_lit 7788445287802241442795744493830144 

noncomputable def Ns300p2097 := nat_lit 116826679317033621641936167407452160 

noncomputable def Ns300p2098 := BSN.cos_dyadic_bound_f 23833361 134217728 2 1 268435456 70560000 Ns300p2095 Ns300p2096 Ns300p2095 Ns300p2095 Ns300p2097 Ns300p2095 264214418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 23833361) (BSN.cosEvenQ 134217728) 0 1 Ns300p2095 Ns300p2096 Ns300p2095 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 23833361) (BSN.cosOddQ 134217728) 0 1 Ns300p2095 Ns300p2097 Ns300p2095 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz569 := (Ns300p2087 (@Ns300p2088 70560000 (Ns300p2094 rfl) (Enclosure.sfrac_false_div 23833361 134217728) (Ns300p2098 rfl rfl) rfl rfl) rfl)

noncomputable def Ns300p2099 := @Enclosure.Real.IsNear.inv_image qz260 132107209 134217728 59702777 147975045120000 272723816 272724041 268435456 qz569 rfl 

noncomputable def Ns300p2100 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns300p2079 (@HMul.hMul Real Real Real qz5 qz269 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz252))) (@HMul.hMul Real Real Real qz5 qz270 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz252))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz498 qz271) qz251) 

noncomputable def Ns300p2101 := nat_lit 966174872329148392699731542553385313942427720354307578720101214389540218737689331678007160802891793725 

noncomputable def Ns300p2102 := nat_lit 95490000798485942327556488929608141869336796426308513983180939858453324169860897776637888476567476078940717918941573706343410161933154871217707956044509 

noncomputable def Ns300p2103 := nat_lit 1013463664104024656444644798048049339198573341929486187471813667963375 

noncomputable def Ns300p2104 := nat_lit 26959946667150639794667015087019630673637144422540572481103610249216 

noncomputable def Ns300p2105 := nat_lit 27997739275484182828570838811497737037014386061634606134739392654720381226788389380791021144688003513524441 

noncomputable def Ns300p2106 := nat_lit 8314429958312720120820825724502441992103855546257026438620851637951620914538429857572642577761539654747125464165146623456995837270404494914864032855097581891151829401600 

noncomputable def Ns300p2107 := nat_lit 5573140509417048473839782361265820133349985139968369613957191433603666113947524516854442948911159313725 

noncomputable def Ns300p2108 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real qz11 Ns300p2079 (@HMul.hMul Real Real Real qz5 qz269 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 2 Zeta.RiemannSiegel.correction qz252))) (@HMul.hMul Real Real Real qz5 qz270 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz252)) Ns300p2107 Ns300p2083 

noncomputable def Ns300p2109 := nat_lit 38917943386009241555438267013601905524913635280679690673602495740103593237361398380517986498066653020188644477067416215771752121451668618497113339724509 

noncomputable def Ns300p2110 := nat_lit 511475932395188968142557641573246442968376503880774345849001851684226360196232084606875 

noncomputable def Ns300p2111 := nat_lit 1942668892225729070919461906823518906642406839052139521251812409738904285205208498176 

noncomputable def Ns300p2112 := nat_lit 2848417264841174138657380016117071859107719838585297701420946081155626285899077859338923197085870385248035071105090834661744806937 

noncomputable def Ns300p2113 := nat_lit 1876957868924001923626156755482469804030248255335440549969287001646943254286991349317578664463271980493269146701256852052072318516427786690896321401656356089265111776673770973142030745600 

noncomputable def Ns300p2114 := nat_lit 2173294037003042436445047483512811517232790999631416781557495317799603880717275 

noncomputable def Ns300p2115 := nat_lit 7237005577332262213973186563042994240829374041602535252466099000494570602496 

noncomputable def Ns300p2116 := nat_lit 101300180532928558514019322134258733210843616803982093095025570070305887591517369092068775466294210582817 

noncomputable def Ns300p2117 := nat_lit 403148616543695480327967449726550873720770287080227066520409210880000000000000000000000000000000000000000000 

noncomputable def Ns300p2118 := @Enclosure.Real.IsNear.subLit_ft Ns300p2079 (@HMul.hMul Real Real Real qz5 qz269 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 2 Zeta.RiemannSiegel.correction qz252)) Ns300p2114 Ns300p2115 Ns300p2116 Ns300p2117 

noncomputable def Ns300p2119 := nat_lit 318437959522069867183546410118935758860864568254650584784762352576288999561736854658180287210654532925 

noncomputable def Ns300p2120 := nat_lit 23532254607776974071161422356508057478046300329260690380066112704409037104793992269798912381659577959417775085537473640521286866388116618497113339724509 

noncomputable def Ns300p2121 := nat_lit 40332848949907544828500404876508507262423623149303276486179667751118613933694413477850966322930084514739404636713476984456502226383205083791483708705415534645359783966815132057600 

noncomputable def Ns300p2122 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz5 qz266 qz267) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz268 qz189) qz259) 

noncomputable def Ns300p2123 := nat_lit 807526663265747459545060022056380900574154017372198372609514491906273238182875 

noncomputable def Ns300p2124 := nat_lit 53189948846349849920154314102317528004238367902592667533456307291280950488166418459607707587894210582817 

noncomputable def Ns300p2125 := nat_lit 134675060845965807596424100411770920213935094925 

noncomputable def Ns300p2126 := nat_lit 97157839151787739082022243872117805756952013015889813776994044079 

noncomputable def Ns300p2127 := nat_lit 814152147418260972153581824421711052800000000000000000000000000000000 

noncomputable def Ns300p2128 := nat_lit 1550914449942106657130800345295146679410193058728421162084034135551581659721923871436948590409907375153609898778117852364800 

noncomputable def Ns300p2129 := nat_lit 11232657620742769763744880035858479371132071889419860146408573225506625 

noncomputable def Ns300p2130 := @Enclosure.Real.IsNear.mulLit_tt qz266 qz267 Ns300p2129 Ns300p1475 

noncomputable def Ns300p2131 := nat_lit 7986872782562228607792499288502299661021096772262085614522704038697285102592913952089026131 

noncomputable def Ns300p2132 := nat_lit 98079714615416886934934209737619787751599303819750539264000000000000000000000000000000000000000 

noncomputable def Ns300p2133 := nat_lit 50155859945366017083162654661176655053020004225 

noncomputable def Ns300p2134 := nat_lit 19476664473820602184357025559621869843659391256699539530071 

noncomputable def Ns300p2135 := nat_lit 2126764793255865396646091296448551321600000000000000000000000000 

noncomputable abbrev qz272 := qz563

noncomputable abbrev qz273 := qz564

noncomputable def Ns300p2136 := @Enclosure.Real.IsNear.mulLit_ft qz272 qz273 Ns300p2133 Ns300p1480 Ns300p2134 Ns300p2135 

noncomputable def Ns300p2137 := nat_lit 35621619626958529765842111 

noncomputable def Ns300p2138 := nat_lit 46116860184273879040000000000000 

noncomputable def Ns300p2139 := @Enclosure.Real.IsNear.mulLit_tt qz273 qz273 223955040008850921781185 37778931862957161709568 Ns300p2137 Ns300p2138 223955040008850921781185 37778931862957161709568 

noncomputable abbrev qz769 := (@HSub.hSub Real Real Real qz810 qz872 qz857)

noncomputable abbrev qz570 := qz769

noncomputable abbrev qz274 := qz570

noncomputable def Ns300p2140 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz274 884279719003555 140737488355328 1 500000000000000 253262667 268435456 33 268435456 

noncomputable abbrev qz770 := qz872

noncomputable abbrev qz571 := qz770

noncomputable abbrev qz275 := qz571

noncomputable def Ns300p2141 := @Enclosure.Real.IsNear.subLit_ff_n qz275 qz187 15172789 268435456 33 268435456 1 1 0 1 253262667 

noncomputable def Ns300p2142 := @Enclosure.Real.IsNear.mulLit_ff qz0 qz252 2 1 0 1 15172789 536870912 33 536870912 15172789 268435456 33 

noncomputable def Ns300p2143 := @Enclosure.Real.IsNear.recentre' qz267 Bool.true 143781942 268435456 

noncomputable def Ns300p2144 := @Enclosure.Real.IsNear.sin_image qz262 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 151733945)) qz732) Bool.true 151733945 268435456 

noncomputable def Ns300p2145 := nat_lit 22929385539180656113207218745205 

noncomputable def Ns300p2146 := nat_lit 101025855939910281966101663056698761 

noncomputable def Ns300p2147 := @Enclosure.Real.IsNear.recentre' qz262 Bool.true Ns300p2145 Ns300p1493 Ns300p2146 

noncomputable def Ns300p2148 := nat_lit 247588007857076054979824844800000000000000 

noncomputable def Ns300p2149 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz263 884279719003555 140737488355328 1 500000000000000 25930014051457031 

noncomputable def Ns300p2150 := @Enclosure.Real.IsNear.subLit_tf qz264 qz27 7915615541975047 288230376151711744 18718145259 288230376151711744 1 16 

noncomputable def Ns300p2151 := @Enclosure.Real.IsNear.subLit_ff_n qz265 qz252 230213526038521 288230376151711744 1001405163 288230376151711744 15172789 536870912 33 536870912 

noncomputable def Ns300p2152 := nat_lit 4249663735061517764132864 

noncomputable def Ns300p2153 := @Enclosure.Real.IsNear.mulLit_ff qz252 qz252 15172789 536870912 33 536870912 15172789 536870912 33 536870912 230213526038521 288230376151711744 

noncomputable def Ns300p2154 := nat_lit 8323135402003029152867394088470574231937850682714411462805143542930625 

noncomputable def Ns300p2155 := nat_lit 280971322154803138948342279599040614896136623188881806662687890625 

noncomputable def Ns300p2156 := nat_lit 21798233051676825719094401487065486446460729471624009927278874451090625 

noncomputable def Ns300p2157 := BSN.sin_dyadic_bound_f 151733945 268435456 3 2 268435456 70560000 Ns300p2154 Ns300p116 Ns300p2155 Ns300p2156 Ns300p119 Ns300p2155 143781942 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 151733945) qz344 0 2 Ns300p2154 Ns300p116 Ns300p2155 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 151733945) qz345 0 2 Ns300p2156 Ns300p119 Ns300p2155 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p2158 := @Ns300p2143 4015017728 9470402887680000 71890971 134217728 15683663 36993761280000 (@Ns300p2144 55 134217728 Bool.true 143781942 268435456 1 70560000 (@Ns300p2147 Ns300p2148 151733945 268435456 55 134217728 (@Ns300p2149 288230376151711744 18718145259 288230376151711744 Ns300p2145 Ns300p1493 Ns300p2146 Ns300p2148 RS301to312.d64 (@Ns300p2150 0 1 414880224823312496 25930014051457031 288230376151711744 18718145259 288230376151711744 (@Ns300p2151 Ns300p2152 7915615541975047 288230376151711744 18718145259 288230376151711744 (@Ns300p2153 1001405163 288230376151711744 (Ns300p2093 rfl rfl) (Ns300p2093 rfl rfl) rfl) (Ns300p2093 rfl rfl) rfl rfl) qz358 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 151733945 268435456) (BSN.sin_neg_of_bound 151733945 268435456 Bool.false 143781942 268435456 1 70560000 (Ns300p2157 rfl rfl)) rfl rfl) 

noncomputable def Ns300p2159 := nat_lit 594116699545369832378366148941841338025 

noncomputable def Ns300p2160 := nat_lit 2883863147381175313050960474969608057208301646908011 

noncomputable def Ns300p2161 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz268 qz189) qz259 Ns300p2159 Ns300p1507 Ns300p2160 

noncomputable def Ns300p2162 := nat_lit 99035203142830421991929937920000000000000000000000000000 

noncomputable def Ns300p2163 := nat_lit 106864858880875589297526333 

noncomputable def Ns300p2164 := @Enclosure.Real.IsNear.mulLit_tf qz268 qz189 671865120026552765343555 37778931862957161709568 Ns300p2163 Ns300p2138 884279719003555 

noncomputable def Ns300p2165 := @Enclosure.Real.IsNear.mulLit_ft qz319 qz273 3 1 0 1 223955040008850921781185 37778931862957161709568 Ns300p2137 

noncomputable def Ns300p2166 := @Enclosure.Real.IsNear.recentre' qz259 Bool.false 226681157 268435456 

noncomputable def Ns300p2167 := @Enclosure.Real.IsNear.cos_image qz262 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 151733945)) qz732) Bool.true 151733945 268435456 

noncomputable def Ns300p2168 := nat_lit 4624088988367084997432529312385696369127648662229423649028040940690625 

noncomputable def Ns300p2169 := nat_lit 13871705022456945386019691252597891026153153713441893183470797446290625 

noncomputable def Ns300p2170 := BSN.cos_dyadic_bound_f 151733945 268435456 3 2 268435456 70560000 Ns300p2168 Ns300p110 Ns300p2155 Ns300p2169 Ns300p113 Ns300p2155 226681157 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 151733945) qz342 0 2 Ns300p2168 Ns300p110 Ns300p2155 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 151733945) qz343 0 2 Ns300p2169 Ns300p113 Ns300p2155 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns300p2171 := @Ns300p2166 4015017728 9470402887680000 226681157 268435456 15683663 36993761280000 (@Ns300p2167 55 134217728 Bool.false 226681157 268435456 1 70560000 (@Ns300p2147 Ns300p2148 151733945 268435456 55 134217728 (@Ns300p2149 288230376151711744 18718145259 288230376151711744 Ns300p2145 Ns300p1493 Ns300p2146 Ns300p2148 RS301to312.d64 (@Ns300p2150 0 1 414880224823312496 25930014051457031 288230376151711744 18718145259 288230376151711744 (@Ns300p2151 Ns300p2152 7915615541975047 288230376151711744 18718145259 288230376151711744 (@Ns300p2153 1001405163 288230376151711744 (Ns300p2093 rfl rfl) (Ns300p2093 rfl rfl) rfl) (Ns300p2093 rfl rfl) rfl rfl) qz358 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 151733945 268435456) (BSN.cos_neg_of_bound 151733945 268435456 Bool.false 226681157 268435456 1 70560000 (Ns300p2170 rfl rfl)) rfl rfl) 

noncomputable abbrev qz276 := (@Ns300p2140 223955040008850921781185 37778931862957161709568 Ns300p2137 Ns300p2138 RS301to312.d64 (@Ns300p2141 253262667 268435456 33 268435456 (@Ns300p2142 268435456 qz324 (Ns300p2093 rfl rfl) rfl) qz727 rfl rfl) rfl)

noncomputable def Ns300p2172 := @Ns300p2122 Ns300p2123 Ns300p2115 Ns300p2124 Ns300p2117 Ns300p2125 Ns300p1470 Ns300p2126 Ns300p2127 Ns300p2128 Ns300p2114 Ns300p2115 Ns300p2116 Ns300p2117 (@Ns300p2130 Ns300p2131 Ns300p2132 71890971 134217728 15683663 36993761280000 Ns300p2123 Ns300p2115 Ns300p2124 Ns300p2117 (@Ns300p2136 223955040008850921781185 37778931862957161709568 Ns300p2137 Ns300p2138 Ns300p2129 Ns300p1475 Ns300p2131 Ns300p2132 (@Ns300p2139 Ns300p2137 Ns300p2138 Ns300p2133 Ns300p1480 Ns300p2134 Ns300p2135 qz276 qz276 rfl) qz276 rfl) (Ns300p2158 rfl) rfl) (@Ns300p2161 Ns300p2162 226681157 268435456 15683663 36993761280000 Ns300p2125 Ns300p1470 Ns300p2126 Ns300p2127 (@Ns300p2164 70368744177664 1 250000000000000 Ns300p2159 Ns300p1507 Ns300p2160 Ns300p2162 (@Ns300p2165 Ns300p2138 671865120026552765343555 37778931862957161709568 Ns300p2163 Ns300p2138 qz502 qz276 rfl) RS301to312.d66 rfl) (Ns300p2171 rfl) rfl) rfl rfl 

noncomputable def Ns300p2173 := nat_lit 1611143642475867638592217404201359 

noncomputable def Ns300p2174 := nat_lit 10126127346579309522041654054415928404016469742640041793353083988487620552321165 

noncomputable def Ns300p2175 := @Enclosure.Real.IsNear.mulLit_tf qz269 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz252) 31447161251595445541745 9444732965739290427392 Ns300p2173 Ns300p1525 Ns300p2174 

noncomputable def Ns300p2176 := nat_lit 1852673427797059126777135760139006525652319754650249024631321344126610074238976 

noncomputable def Ns300p2177 := nat_lit 29753046866590158699666624948811574708368402110337715790046974240275692651096504700420075737917345573025829352851 

noncomputable abbrev qz277 := qz565

noncomputable def Ns300p2178 := @Enclosure.Real.IsNear.mulLit_ft qz319 qz277 3 1 0 1 10482387083865148513915 9444732965739290427392 Ns300p2173 

noncomputable def Ns300p2179 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz271 884279719003555 140737488355328 1 500000000000000 11854153 67108864 59702777 147975045120000 10482387083865148513915 

noncomputable def Ns300p2180 := @Enclosure.Real.IsNear.recentre' qz271 Bool.false 47416612 268435456 15283910912 37881611550720000 11854153 67108864 59702777 147975045120000 

noncomputable def Ns300p2181 := @Enclosure.Real.IsNear.sin_image qz261 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23833361) qz735) Bool.false 23833361 134217728 209 536870912 Bool.false 47416612 268435456 1 

noncomputable def Ns300p2182 := BSN.sin_dyadic_bound_f 23833361 134217728 2 1 268435456 70560000 Ns300p2095 Ns300p1502 Ns300p2095 Ns300p2095 Ns300p1503 Ns300p2095 47416612 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 23833361) (BSN.sinEvenQ 134217728) 0 1 Ns300p2095 Ns300p1502 Ns300p2095 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 23833361) (BSN.sinOddQ 134217728) 0 1 Ns300p2095 Ns300p1503 Ns300p2095 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz572 := (@HMul.hMul Real Real Real qz623 qz621 qz767)

noncomputable abbrev qz278 := qz572

noncomputable abbrev qz573 := (@Enclosure.Real.IsNear.neg qz278 Bool.false 10482387083865148513915 9444732965739290427392 Ns300p2173 Ns300p1532 (@Ns300p2179 9444732965739290427392 Ns300p2173 Ns300p1532 RS301to312.d64 (Ns300p2180 (@Ns300p2181 70560000 (Ns300p2094 rfl) (Enclosure.sfrac_false_div 23833361 134217728) (Ns300p2182 rfl rfl) rfl rfl) rfl) rfl))

noncomputable def Ns300p2183 := @Ns300p2178 Ns300p1532 31447161251595445541745 9444732965739290427392 Ns300p2173 Ns300p1525 qz502 qz573 rfl 

noncomputable abbrev qz279 := (@HMul.hMul Real Real Real qz327 qz563 (Real.cos qz558))

noncomputable def Ns300p2184 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz279) (@HMul.hMul Real Real Real qz5 qz189 qz267) 

noncomputable abbrev qz280 := (@HMul.hMul Real Real Real qz327 qz317 qz565)

noncomputable abbrev qz281 := (@HMul.hMul Real Real Real qz327 qz566 (Zeta.RiemannSiegel.correction qz546))

noncomputable def Ns300p2185 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz252) (@HMul.hMul Real Real Real qz5 qz258 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns300p2184 (@HMul.hMul Real Real Real qz5 qz280 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c8 1 Zeta.RiemannSiegel.correction qz252))) qz281)) 

noncomputable def Ns300p2186 := @Enclosure.Real.IsNear.mulLit_ff qz258 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns300p2184 (@HMul.hMul Real Real Real qz5 qz280 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 1 Zeta.RiemannSiegel.correction qz252))) qz281) 545447857 

noncomputable def Ns300p2187 := nat_lit 18564794446665704879727218461536513845019047792573950461690206967826845 

noncomputable def Ns300p2188 := nat_lit 3450873173395281893717377931138512726225554486085193277581262111899648 

noncomputable def Ns300p2189 := nat_lit 106706363165925169056523457580866097348342958501043079514060085394952142802750654450837976271106542467411 

noncomputable def Ns300p2190 := nat_lit 96479286021386836258217505898430341707116986571212694879443556070585955 

noncomputable def Ns300p2191 := @Enclosure.Real.IsNear.subLit_tt_p (@HSub.hSub Real Real Real qz11 Ns300p2184 (@HMul.hMul Real Real Real qz5 qz280 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz252))) qz281 Ns300p2190 Ns300p2188 

noncomputable def Ns300p2192 := nat_lit 59164099190827988389018866205539473298620537525213962309508352285349575987233702364538668086507277187411 

noncomputable def Ns300p2193 := nat_lit 12772458698246118695467901589242971155628407138736451525 

noncomputable def Ns300p2194 := nat_lit 2393764902855329246491160734378051550927670197064446596038340098004099832449023373 

noncomputable def Ns300p2195 := nat_lit 7112616176651752317054736678650405515913493989110535566099380213032721994507910632890110132469260649592906490128365183303680 

noncomputable def Ns300p2196 := nat_lit 8790612724545040468926569529557261287481179706583367365 

noncomputable def Ns300p2197 := nat_lit 628504308925801594243129405883636882224164182364795456210901221980692253 

noncomputable def Ns300p2198 := nat_lit 22479151160118868126668004018829548398028259328000000000000000000000000000000 

noncomputable def Ns300p2199 := @Enclosure.Real.IsNear.subLit_tf Ns300p2184 (@HMul.hMul Real Real Real qz5 qz280 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz252)) Ns300p2196 Ns300p1554 Ns300p2197 Ns300p2198 

noncomputable def Ns300p2200 := nat_lit 17300485640148066553116220023872210279387731023101795147466987810059875 

noncomputable def Ns300p2201 := nat_lit 29059469924085490244248730121344980623872505468424548002523150525357277754319356255095424054507277187411 

noncomputable def Ns300p2202 := nat_lit 36963518903425002502178923172619373718223603234176785918781819121741586241868301082189320063947120424421695846492275233259520 

noncomputable def Ns300p2203 := @Enclosure.Real.IsNear.subLit_tt_n (@Neg.neg Real Real.instNeg qz279) (@HMul.hMul Real Real Real qz5 qz189 qz267) 

noncomputable def Ns300p2204 := nat_lit 11369388362745525540893075777786967148808470901867888325 

noncomputable def Ns300p2205 := nat_lit 395690662183485734584242694616567986466749229927661141750682461540538419 

noncomputable def Ns300p2206 := nat_lit 17483784235648008542964003125756315420688646144000000000000000000000000000000 

noncomputable def Ns300p2207 := nat_lit 423240512578243075914681470806121 

noncomputable def Ns300p2208 := nat_lit 79443497426815549440000000000000000000 

noncomputable def Ns300p2209 := nat_lit 83024989788557824182296285937200667219962631865615934797357062040349394862080 

noncomputable def Ns300p2210 := @Enclosure.Real.IsNear.neg qz279 Bool.false Ns300p2204 

noncomputable def Ns300p2211 := @Enclosure.Real.IsNear.mulLit_ff qz272 qz259 Ns300p2133 Ns300p1480 Ns300p2134 

noncomputable def Ns300p2212 := @Enclosure.Real.IsNear.mulLit_ft qz189 qz267 884279719003555 70368744177664 1 

noncomputable def Ns300p2213 := nat_lit 1650433770641571739898563167473054042170087552825 

noncomputable def Ns300p2214 := @Enclosure.Real.IsNear.mulLit_tt qz280 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz252) 10482387083865148513915 4722366482869645213696 Ns300p2173 Ns300p1566 Ns300p2213 

noncomputable def Ns300p2215 := nat_lit 23717681968410487194669901135932463962857547167769179994566790779 

noncomputable def Ns300p2216 := @Enclosure.Real.IsNear.mulLit_ft qz0 qz277 2 1 0 1 10482387083865148513915 9444732965739290427392 Ns300p2173 

noncomputable def Ns300p2217 := @Ns300p2216 Ns300p1532 10482387083865148513915 4722366482869645213696 Ns300p2173 Ns300p1566 qz324 qz573 rfl 

noncomputable abbrev qz282 := (@HMul.hMul Real Real Real qz327 qz564 (Real.sin qz558))

noncomputable def Ns300p2218 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz282) (@HMul.hMul Real Real Real qz5 qz277 qz251) 

noncomputable def Ns300p2219 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz252) (@HMul.hMul Real Real Real qz5 qz258 Ns300p2218) Bool.true Ns300p2213 Ns300p1898 Ns300p2215 Ns300p1900 (BSN.deriv_correction_mk qz252 qz568) 

noncomputable def Ns300p2220 := nat_lit 3025832349436789041960729836496642505225 

noncomputable def Ns300p2221 := nat_lit 1361129467683753853853498429727072845824 

noncomputable def Ns300p2222 := nat_lit 75390858241005785114019595295005144526674987396443417769 

noncomputable def Ns300p2223 := @Enclosure.Real.IsNear.mulLit_ft qz258 Ns300p2218 545447857 536870912 225 536870912 Ns300p2220 Ns300p2221 Ns300p2222 

noncomputable def Ns300p2224 := @Enclosure.Real.IsNear.subLit_tt_n (@Neg.neg Real Real.instNeg qz282) (@HMul.hMul Real Real Real qz5 qz277 qz251) 

noncomputable def Ns300p2225 := nat_lit 16100345286580141361094439180635 

noncomputable def Ns300p2226 := nat_lit 5070602400912917605986812821504 

noncomputable def Ns300p2227 := nat_lit 554831329874607308993136889698708924177 

noncomputable def Ns300p2228 := nat_lit 189559568515573854593928396800000000000000000 

noncomputable def Ns300p2229 := nat_lit 1296071179323801884849116604021380089335 

noncomputable def Ns300p2230 := nat_lit 38445322258522705893276049434428832209297782156635417769 

noncomputable def Ns300p2231 := nat_lit 15342792775814156789025064123914312125117750864731535371328897312358400 

noncomputable def Ns300p2232 := @Enclosure.Real.IsNear.neg qz282 Bool.false Ns300p2225 

noncomputable def Ns300p2233 := @Enclosure.Real.IsNear.mulLit_tt qz273 qz267 223955040008850921781185 37778931862957161709568 Ns300p2137 

noncomputable def Ns300p2234 := @Enclosure.Real.IsNear.mulLit_tf qz277 qz251 10482387083865148513915 9444732965739290427392 Ns300p2173 Ns300p1532 123642751307930549 144115188075855872 

noncomputable def Ns300p2235 := @Enclosure.Real.IsNear.of_eq qz251 (@HMul.hMul Real Real Real qz5 qz258 qz259) Bool.false 123642751307930549 

noncomputable def Ns300p2236 := @Enclosure.Real.IsNear.mulLit_ff qz258 qz259 545447857 536870912 225 

noncomputable abbrev qz574 := (@Ns300p2235 144115188075855872 31167021431246857 39721748713407774720000 (BSN.correction_mk qz252 qz768) (@Ns300p2236 536870912 226681157 268435456 15683663 36993761280000 123642751307930549 144115188075855872 31167021431246857 39721748713407774720000 (@Ns300p2086 536870912 (Ns300p2099 rfl rfl rfl rfl rfl) rfl) (Ns300p2171 rfl) rfl))

noncomputable def Ns300p2237 := @Ns300p2234 31167021431246857 39721748713407774720000 Ns300p2229 Ns300p2221 Ns300p2230 Ns300p1909 qz573 qz574 

noncomputable abbrev qz575 := (@Ns300p2086 536870912 (Ns300p2099 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns300p2238 := @Ns300p2214 Ns300p1898 Ns300p2215 Ns300p1900 Ns300p2200 Ns300p2188 Ns300p2201 Ns300p1872 Ns300p2217 (Ns300p2219 (@Ns300p2223 Ns300p1909 Ns300p2213 Ns300p1898 Ns300p2215 Ns300p1900 qz575 (@Ns300p2224 Ns300p2225 Ns300p2226 Ns300p2227 Ns300p2228 Ns300p2229 Ns300p2221 Ns300p2230 Ns300p1909 Ns300p2231 Ns300p2220 Ns300p2221 Ns300p2222 Ns300p1909 (@Ns300p2232 Ns300p2226 Ns300p2227 Ns300p2228 (@Ns300p2233 Ns300p2138 71890971 134217728 15683663 36993761280000 Ns300p2225 Ns300p2226 Ns300p2227 Ns300p2228 qz276 (Ns300p2158 rfl) rfl)) (Ns300p2237 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns300p2239 := @Ns300p2199 Ns300p2200 Ns300p2188 Ns300p2201 Ns300p1872 Ns300p2202 Ns300p2190 Ns300p2188 Ns300p2192 Ns300p1872 (@Ns300p2203 Ns300p2204 Ns300p1554 Ns300p2205 Ns300p2206 63571727634772721401905 9444732965739290427392 Ns300p2207 Ns300p2208 Ns300p2209 Ns300p2196 Ns300p1554 Ns300p2197 Ns300p2198 (@Ns300p2210 Ns300p1554 Ns300p2205 Ns300p2206 (@Ns300p2211 Ns300p2135 226681157 268435456 15683663 36993761280000 Ns300p2204 Ns300p1554 Ns300p2205 Ns300p2206 (@Ns300p2139 Ns300p2137 Ns300p2138 Ns300p2133 Ns300p1480 Ns300p2134 Ns300p2135 qz276 qz276 rfl) (Ns300p2171 rfl) rfl)) (@Ns300p2212 250000000000000 71890971 134217728 15683663 36993761280000 63571727634772721401905 9444732965739290427392 Ns300p2207 Ns300p2208 RS301to312.d66 (Ns300p2158 rfl) rfl) rfl rfl) Ns300p2238 

noncomputable def Ns300p2240 := nat_lit 103301314174386885886480041841020022225 

noncomputable def Ns300p2241 := nat_lit 43478443892121571209266487527978879445529232828491699706153 

noncomputable abbrev qz283 := qz566

noncomputable def Ns300p2242 := @Enclosure.Real.IsNear.mulLit_tf qz283 qz251 Ns300p2240 Ns300p1507 Ns300p2241 Ns300p1603 123642751307930549 144115188075855872 

noncomputable def Ns300p2243 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz260 Ns300p1374 Ns300p1378 Ns300p1376 Ns300p1379 132107209 134217728 59702777 147975045120000 Ns300p2240 

noncomputable abbrev qz576 := (@HMul.hMul Real Real Real qz623 qz728 qz762)

noncomputable abbrev qz284 := qz576

noncomputable def Ns300p2244 := @Ns300p2242 31167021431246857 39721748713407774720000 Ns300p2193 Ns300p1554 Ns300p2194 Ns300p1878 (@Enclosure.Real.IsNear.neg qz284 Bool.false Ns300p2240 Ns300p1507 Ns300p2241 Ns300p1603 (@Ns300p2243 Ns300p1507 Ns300p2241 Ns300p1603 RS301to312.d68 qz569 rfl)) qz574 

noncomputable def Ns300p2245 := nat_lit 309903942523160657659440125523060066675 

noncomputable def Ns300p2246 := @Enclosure.Real.IsNear.mulLit_tt qz270 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz252) Ns300p2245 Ns300p1507 Ns300p2241 Ns300p1608 Ns300p2213 

noncomputable def Ns300p2247 := @Enclosure.Real.IsNear.mulLit_ft qz319 qz283 3 1 0 1 Ns300p2240 Ns300p1507 Ns300p2241 

noncomputable def Ns300p2248 := @Ns300p2247 Ns300p1603 Ns300p2245 Ns300p1507 Ns300p2241 Ns300p1608 qz502 (@Enclosure.Real.IsNear.neg qz284 Bool.false Ns300p2240 Ns300p1507 Ns300p2241 Ns300p1603 (@Ns300p2243 Ns300p1507 Ns300p2241 Ns300p1603 RS301to312.d68 qz569 rfl)) rfl 

noncomputable def Ns300p2249 := @Ns300p2246 Ns300p1898 Ns300p2215 Ns300p1900 Ns300p2110 Ns300p2111 Ns300p2112 Ns300p1792 Ns300p2248 (Ns300p2219 (@Ns300p2223 Ns300p1909 Ns300p2213 Ns300p1898 Ns300p2215 Ns300p1900 qz575 (@Ns300p2224 Ns300p2225 Ns300p2226 Ns300p2227 Ns300p2228 Ns300p2229 Ns300p2221 Ns300p2230 Ns300p1909 Ns300p2231 Ns300p2220 Ns300p2221 Ns300p2222 Ns300p1909 (@Ns300p2232 Ns300p2226 Ns300p2227 Ns300p2228 (@Ns300p2233 Ns300p2138 71890971 134217728 15683663 36993761280000 Ns300p2225 Ns300p2226 Ns300p2227 Ns300p2228 qz276 (Ns300p2158 rfl) rfl)) (Ns300p2237 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns300p2250 := @Ns300p2108 Ns300p2109 Ns300p1764 Ns300p2110 Ns300p2111 Ns300p2112 Ns300p1792 Ns300p2113 Ns300p2101 Ns300p2083 Ns300p2102 Ns300p1764 (@Ns300p2118 Ns300p2119 Ns300p2083 Ns300p2120 Ns300p1764 Ns300p2121 Ns300p2107 Ns300p2083 Ns300p2109 Ns300p1764 Ns300p2172 (@Ns300p2175 Ns300p2176 Ns300p2177 Ns300p1857 Ns300p2119 Ns300p2083 Ns300p2120 Ns300p1764 Ns300p2183 (@Ns300p2185 Bool.false Ns300p2174 Ns300p2176 Ns300p2177 Ns300p1857 (BSN.iteratedDeriv_two_correction_mk qz252 qz568) (@Ns300p2186 536870912 225 536870912 Ns300p2187 Ns300p2188 Ns300p2189 Ns300p1872 Ns300p2174 Ns300p2176 Ns300p2177 Ns300p1857 qz575 (@Ns300p2191 Ns300p2192 Ns300p1872 Ns300p2193 Ns300p1554 Ns300p2194 Ns300p1878 Ns300p2195 Ns300p2187 Ns300p2188 Ns300p2189 Ns300p1872 (Ns300p2239 rfl rfl) (Ns300p2244 rfl) rfl rfl) rfl)) rfl) rfl rfl) Ns300p2249 

noncomputable def Ns300p2251 := nat_lit 8196709094413529548599204260023090156304629920617875 

noncomputable def Ns300p2252 := nat_lit 1173312564208982680644868413315067600032834422428362386351867593363639019874845993951 

noncomputable def Ns300p2253 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz321 RSCompact.c11) qz271) qz251 Ns300p2251 Ns300p1615 Ns300p2252 Ns300p1617 123642751307930549 144115188075855872 31167021431246857 

noncomputable def Ns300p2254 := @Enclosure.Real.IsNear.mulLit_ff qz729 qz271 Ns300p1380 Ns300p1381 Ns300p1382 Ns300p1383 11854153 67108864 59702777 147975045120000 Ns300p2251 

noncomputable abbrev qz577 := (Ns300p2180 (@Ns300p2181 70560000 (Ns300p2094 rfl) (Enclosure.sfrac_false_div 23833361 134217728) (Ns300p2182 rfl rfl) rfl rfl) rfl)

noncomputable def Ns300p2255 := Ns300p2081 (@Ns300p2085 Ns300p1764 Ns300p2075 Ns300p2076 Ns300p2077 Ns300p1755 qz575 (@Ns300p2100 Ns300p2101 Ns300p2083 Ns300p2102 Ns300p1764 Ns300p2103 Ns300p2104 Ns300p2105 Ns300p1784 Ns300p2106 Ns300p2082 Ns300p2083 Ns300p2084 Ns300p1764 (Ns300p2250 rfl rfl) (@Ns300p2253 39721748713407774720000 Ns300p2103 Ns300p2104 Ns300p2105 Ns300p1784 (@Ns300p2254 Ns300p1615 Ns300p2252 Ns300p1617 RS301to312.d69 qz577 rfl) qz574 rfl) rfl rfl) rfl) 

noncomputable def Ns300p2256 := @Enclosure.Real.IsNear.of_eq qz758 (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz252) qz492)) Bool.true Ns300p2071 Ns300p2072 Ns300p2073 Ns300p1750 (BSN.correctionLinear_mk qz252) (@Enclosure.Real.IsNear.neg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz252) qz492) Bool.false Ns300p2071 Ns300p2072 Ns300p2073 Ns300p1750 (@Ns300p2078 Ns300p2072 Ns300p2073 Ns300p1750 Ns300p2255 RS301to312.d70 rfl)) 

noncomputable def Ns300p2257 := @Enclosure.Real.IsNear.inv_image qz253 168246299 16777216 1 1048576 1672993 1672994 16777216 qz555 rfl 

noncomputable def Ns300p2258 := @Ns300p2074 Ns300p2030 Ns300p2039 Ns300p1710 Ns300p2256 (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz253) Bool.false 3345987 33554432 1 33554432 3345987 33554432 1 33554432 (Ns300p2257 rfl rfl rfl rfl rfl) rfl) 

noncomputable abbrev qz578 := (BSN.correction_mk qz252 qz768)

noncomputable def Ns300p2259 := @Ns300p2032 Ns300p1710 Ns300p1955 Ns300p1951 Ns300p1957 Ns300p1953 (Ns300p2033 qz488 (@Enclosure.Real.IsNear.of_eq qz554 (@Inv.inv Real Real.instInv (Real.sqrt qz253)) Bool.false 10595881 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz250 (BSN.t_div_two_pi_nonneg qz249 631875 1000 qz254)) Ns300p2037) rfl) (@Ns300p2040 Ns300p2041 Ns300p2029 Ns300p2030 Ns300p2031 Ns300p1710 (@Ns300p2042 281474976710656 944259116936117 77581540455874560000 qz578 (@Ns300p2043 33554432 7083803 8388608 30540451 4624220160000 241490152406001 281474976710656 944259116936117 77581540455874560000 (@Ns300p2044 33554432 (Ns300p2054 rfl rfl rfl rfl rfl) rfl) (Ns300p2070 rfl) rfl)) (Ns300p2258 rfl) rfl rfl) 

noncomputable abbrev qz771 := (@BSN.floor_sqrt_eq_dec qz249 631875 1000 10 qz254 rfl rfl rfl)

noncomputable abbrev qz579 := qz771

noncomputable def Ns300p2260 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz249) (hardyZApproximantRS qz249) Bool.true Ns300p1950 Ns300p1951 Ns300p1952 Ns300p1953 (@Eq.refl Real (hardyZApproximantRS qz249)) (Ns300p1954 (BSN.hardyZApproximantRS_eq qz249 10 qz579) (@Ns300p1956 Ns300p1957 Ns300p1953 Ns300p1958 Ns300p1950 Ns300p1951 Ns300p1952 Ns300p1953 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz249) qz249 10) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz249) qz249 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz249) qz249 10)) Bool.true 103844093 134217728 84375 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz249) qz249 10) (Ns300p2028 (Ns300p2027 rfl rfl rfl rfl) rfl rfl)) (Ns300p2259 rfl) rfl rfl)) 

theorem RS301to312.d75 : Enclosure.Real.IsNear (hardyZApproximantRS qz249) Bool.true Ns300p1950 Ns300p1951 Ns300p1952 Ns300p1953 := Ns300p2260 

noncomputable def RS301to312.d76 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz285 := (RS301to312.d3 qz326 qz359 (@Enclosure.dec_le_dec qz326 qz359 615476 1000 616846 1000 (@Eq.refl Real qz326) (@Eq.refl Real qz359) rfl rfl rfl))

noncomputable abbrev qz772 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz285)

noncomputable def Ns300p2261 := @Enclosure.Real.IsNear.of_eq qz772 (hardyZApproximantRS₀ qz4) Bool.true 5082024012364767182511 18889465931478580854784 394874196365170051254089 Ns300p71 

noncomputable abbrev qz286 := (@Enclosure.dec_le_dec qz326 qz359 615476 1000 616846 1000 (@Eq.refl Real qz326) (@Eq.refl Real qz359) rfl rfl rfl)

noncomputable def Ns300p2262 := @Enclosure.Real.IsNear.neg_val qz772 5082024012364767182511 18889465931478580854784 394874196365170051254089 Ns300p71 (Ns300p2261 (RS301to312.d4 qz4 qz30 qz286) RS301to312.d45) rfl 

noncomputable abbrev qz773 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz285)

noncomputable def Ns300p2263 := @Enclosure.Real.IsNear.of_eq qz773 (hardyZApproximantRS₀ qz30) Bool.false 2209724606842907479 288230376151711744 92726478686055137261243 Ns300p197 

noncomputable def Ns300p2264 := @Enclosure.Real.IsNear.pos_val qz773 2209724606842907479 288230376151711744 92726478686055137261243 Ns300p197 (Ns300p2263 (RS301to312.d46 qz4 qz30 qz286) RS301to312.d47) rfl 

noncomputable def Ns300p2265 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz772 qz4 qz4 615476 1000 615476 1000 

noncomputable def Ns300p2266 := @Enclosure.norm_gt_of_isNear qz772 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 5082024012364767182511 18889465931478580854784 394874196365170051254089 

noncomputable def Ns300p2267 := @Ns300p2266 Ns300p71 333033581 5368709120 1213 5368709120 (Ns300p2261 (RS301to312.d4 qz4 qz30 qz286) RS301to312.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS301to312.d48) rfl rfl rfl rfl 

noncomputable def Ns300p2268 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz773 qz4 qz30 615476 1000 616846 1000 

noncomputable def Ns300p2269 := @Enclosure.norm_gt_of_isNear qz773 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2209724606842907479 288230376151711744 92726478686055137261243 

noncomputable def Ns300p2270 := @Ns300p2269 Ns300p197 333033581 5368709120 1213 5368709120 (Ns300p2263 (RS301to312.d46 qz4 qz30 qz286) RS301to312.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS301to312.d48) rfl rfl rfl rfl 

noncomputable def Ns300p2271 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz285 (@BSN.thirtyTwoPi_le_dec qz4 615476 1000 qz10 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz772 qz773 (Ns300p2262 rfl rfl) (Ns300p2264 rfl rfl)) (Ns300p2265 qz10 qz10 rfl rfl rfl rfl (Ns300p2267 rfl)) (Ns300p2268 qz10 qz33 rfl rfl rfl rfl (Ns300p2270 rfl)) 

noncomputable abbrev qz287 := (RS301to312.d3 qz359 qz376 (@Enclosure.dec_le_dec qz359 qz376 616846 1000 618215 1000 (@Eq.refl Real qz359) (@Eq.refl Real qz376) rfl rfl rfl))

noncomputable abbrev qz774 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz287)

noncomputable def Ns300p2272 := @Enclosure.Real.IsNear.of_eq qz774 (hardyZApproximantRS₀ qz30) Bool.false 2209724606842907479 288230376151711744 92726478686055137261243 Ns300p197 

noncomputable abbrev qz288 := (@Enclosure.dec_le_dec qz359 qz376 616846 1000 618215 1000 (@Eq.refl Real qz359) (@Eq.refl Real qz376) rfl rfl rfl)

noncomputable def Ns300p2273 := @Enclosure.Real.IsNear.pos_val qz774 2209724606842907479 288230376151711744 92726478686055137261243 Ns300p197 (Ns300p2272 (RS301to312.d4 qz30 qz54 qz288) RS301to312.d47) rfl 

noncomputable abbrev qz775 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz287)

noncomputable def Ns300p2274 := @Enclosure.Real.IsNear.of_eq qz775 (hardyZApproximantRS₀ qz54) Bool.true 2394939983634542619317 4722366482869645213696 165165353916085003139209 Ns300p347 

noncomputable def Ns300p2275 := @Enclosure.Real.IsNear.neg_val qz775 2394939983634542619317 4722366482869645213696 165165353916085003139209 Ns300p347 (Ns300p2274 (RS301to312.d46 qz30 qz54 qz288) RS301to312.d49) rfl 

noncomputable def Ns300p2276 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz774 qz4 qz30 615476 1000 616846 1000 

noncomputable def Ns300p2277 := @Enclosure.norm_gt_of_isNear qz774 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2209724606842907479 288230376151711744 92726478686055137261243 

noncomputable def Ns300p2278 := @Ns300p2277 Ns300p197 333033581 5368709120 1213 5368709120 (Ns300p2272 (RS301to312.d4 qz30 qz54 qz288) RS301to312.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS301to312.d48) rfl rfl rfl rfl 

noncomputable def Ns300p2279 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz775 qz4 qz54 615476 1000 618215 1000 

noncomputable def Ns300p2280 := @Enclosure.norm_gt_of_isNear qz775 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2394939983634542619317 4722366482869645213696 165165353916085003139209 

noncomputable def Ns300p2281 := @Ns300p2280 Ns300p347 333033581 5368709120 1213 5368709120 (Ns300p2274 (RS301to312.d46 qz30 qz54 qz288) RS301to312.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS301to312.d48) rfl rfl rfl rfl 

noncomputable def Ns300p2282 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz287 (@BSN.thirtyTwoPi_le_dec qz30 616846 1000 qz33 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz774 qz775 (Ns300p2273 rfl rfl) (Ns300p2275 rfl rfl)) (Ns300p2276 qz10 qz33 rfl rfl rfl rfl (Ns300p2278 rfl)) (Ns300p2279 qz10 qz57 rfl rfl rfl rfl (Ns300p2281 rfl)) 

noncomputable abbrev qz289 := (RS301to312.d3 qz376 qz388 (@Enclosure.dec_le_dec qz376 qz388 618215 1000 619584 1000 (@Eq.refl Real qz376) (@Eq.refl Real qz388) rfl rfl rfl))

noncomputable abbrev qz776 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz289)

noncomputable def Ns300p2283 := @Enclosure.Real.IsNear.of_eq qz776 (hardyZApproximantRS₀ qz54) Bool.true 2394939983634542619317 4722366482869645213696 165165353916085003139209 Ns300p347 

noncomputable abbrev qz290 := (@Enclosure.dec_le_dec qz376 qz388 618215 1000 619584 1000 (@Eq.refl Real qz376) (@Eq.refl Real qz388) rfl rfl rfl)

noncomputable def Ns300p2284 := @Enclosure.Real.IsNear.neg_val qz776 2394939983634542619317 4722366482869645213696 165165353916085003139209 Ns300p347 (Ns300p2283 (RS301to312.d4 qz54 qz68 qz290) RS301to312.d49) rfl 

noncomputable abbrev qz777 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz289)

noncomputable def Ns300p2285 := @Enclosure.Real.IsNear.of_eq qz777 (hardyZApproximantRS₀ qz68) Bool.false 257337052468981097579 295147905179352825856 186233142722390393416019 Ns300p467 

noncomputable def Ns300p2286 := @Enclosure.Real.IsNear.pos_val qz777 257337052468981097579 295147905179352825856 186233142722390393416019 Ns300p467 (Ns300p2285 (RS301to312.d46 qz54 qz68 qz290) RS301to312.d50) rfl 

noncomputable def Ns300p2287 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz776 qz4 qz54 615476 1000 618215 1000 

noncomputable def Ns300p2288 := @Enclosure.norm_gt_of_isNear qz776 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2394939983634542619317 4722366482869645213696 165165353916085003139209 

noncomputable def Ns300p2289 := @Ns300p2288 Ns300p347 333033581 5368709120 1213 5368709120 (Ns300p2283 (RS301to312.d4 qz54 qz68 qz290) RS301to312.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS301to312.d48) rfl rfl rfl rfl 

noncomputable def Ns300p2290 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz777 qz4 qz68 615476 1000 619584 1000 

noncomputable def Ns300p2291 := @Enclosure.norm_gt_of_isNear qz777 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 257337052468981097579 295147905179352825856 186233142722390393416019 

noncomputable def Ns300p2292 := @Ns300p2291 Ns300p467 333033581 5368709120 1213 5368709120 (Ns300p2285 (RS301to312.d46 qz54 qz68 qz290) RS301to312.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS301to312.d48) rfl rfl rfl rfl 

noncomputable def Ns300p2293 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz289 (@BSN.thirtyTwoPi_le_dec qz54 618215 1000 qz57 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz776 qz777 (Ns300p2284 rfl rfl) (Ns300p2286 rfl rfl)) (Ns300p2287 qz10 qz57 rfl rfl rfl rfl (Ns300p2289 rfl)) (Ns300p2290 qz10 qz71 rfl rfl rfl rfl (Ns300p2292 rfl)) 

noncomputable abbrev qz291 := (RS301to312.d3 qz388 qz399 (@Enclosure.dec_le_dec qz388 qz399 619584 1000 620952 1000 (@Eq.refl Real qz388) (@Eq.refl Real qz399) rfl rfl rfl))

noncomputable abbrev qz778 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz291)

noncomputable def Ns300p2294 := @Enclosure.Real.IsNear.of_eq qz778 (hardyZApproximantRS₀ qz68) Bool.false 257337052468981097579 295147905179352825856 186233142722390393416019 Ns300p467 

noncomputable abbrev qz292 := (@Enclosure.dec_le_dec qz388 qz399 619584 1000 620952 1000 (@Eq.refl Real qz388) (@Eq.refl Real qz399) rfl rfl rfl)

noncomputable def Ns300p2295 := @Enclosure.Real.IsNear.pos_val qz778 257337052468981097579 295147905179352825856 186233142722390393416019 Ns300p467 (Ns300p2294 (RS301to312.d4 qz68 qz82 qz292) RS301to312.d50) rfl 

noncomputable abbrev qz779 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz291)

noncomputable def Ns300p2296 := @Enclosure.Real.IsNear.of_eq qz779 (hardyZApproximantRS₀ qz82) Bool.true 758231098218176793107 590295810358705651712 20731475550306198438331 Ns300p579 

noncomputable def Ns300p2297 := @Enclosure.Real.IsNear.neg_val qz779 758231098218176793107 590295810358705651712 20731475550306198438331 Ns300p579 (Ns300p2296 (RS301to312.d46 qz68 qz82 qz292) RS301to312.d51) rfl 

noncomputable def Ns300p2298 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz778 qz4 qz68 615476 1000 619584 1000 

noncomputable def Ns300p2299 := @Enclosure.norm_gt_of_isNear qz778 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 257337052468981097579 295147905179352825856 186233142722390393416019 

noncomputable def Ns300p2300 := @Ns300p2299 Ns300p467 333033581 5368709120 1213 5368709120 (Ns300p2294 (RS301to312.d4 qz68 qz82 qz292) RS301to312.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS301to312.d48) rfl rfl rfl rfl 

noncomputable def Ns300p2301 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz779 qz4 qz82 615476 1000 620952 1000 

noncomputable def Ns300p2302 := @Enclosure.norm_gt_of_isNear qz779 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 758231098218176793107 590295810358705651712 20731475550306198438331 

noncomputable def Ns300p2303 := @Ns300p2302 Ns300p579 333033581 5368709120 1213 5368709120 (Ns300p2296 (RS301to312.d46 qz68 qz82 qz292) RS301to312.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS301to312.d48) rfl rfl rfl rfl 

noncomputable def Ns300p2304 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz291 (@BSN.thirtyTwoPi_le_dec qz68 619584 1000 qz71 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz778 qz779 (Ns300p2295 rfl rfl) (Ns300p2297 rfl rfl)) (Ns300p2298 qz10 qz71 rfl rfl rfl rfl (Ns300p2300 rfl)) (Ns300p2301 qz10 qz85 rfl rfl rfl rfl (Ns300p2303 rfl)) 

noncomputable abbrev qz293 := (RS301to312.d3 qz399 qz410 (@Enclosure.dec_le_dec qz399 qz410 620952 1000 622320 1000 (@Eq.refl Real qz399) (@Eq.refl Real qz410) rfl rfl rfl))

noncomputable abbrev qz780 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz293)

noncomputable def Ns300p2305 := @Enclosure.Real.IsNear.of_eq qz780 (hardyZApproximantRS₀ qz82) Bool.true 758231098218176793107 590295810358705651712 20731475550306198438331 Ns300p579 

noncomputable abbrev qz294 := (@Enclosure.dec_le_dec qz399 qz410 620952 1000 622320 1000 (@Eq.refl Real qz399) (@Eq.refl Real qz410) rfl rfl rfl)

noncomputable def Ns300p2306 := @Enclosure.Real.IsNear.neg_val qz780 758231098218176793107 590295810358705651712 20731475550306198438331 Ns300p579 (Ns300p2305 (RS301to312.d4 qz82 qz96 qz294) RS301to312.d51) rfl 

noncomputable abbrev qz781 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz293)

noncomputable def Ns300p2307 := @Enclosure.Real.IsNear.of_eq qz781 (hardyZApproximantRS₀ qz96) Bool.false 2513392407100580555225 18889465931478580854784 1196663358396875346315799 Ns300p695 

noncomputable def Ns300p2308 := @Enclosure.Real.IsNear.pos_val qz781 2513392407100580555225 18889465931478580854784 1196663358396875346315799 Ns300p695 (Ns300p2307 (RS301to312.d46 qz82 qz96 qz294) RS301to312.d52) rfl 

noncomputable def Ns300p2309 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz780 qz4 qz82 615476 1000 620952 1000 

noncomputable def Ns300p2310 := @Enclosure.norm_gt_of_isNear qz780 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 758231098218176793107 590295810358705651712 20731475550306198438331 

noncomputable def Ns300p2311 := @Ns300p2310 Ns300p579 333033581 5368709120 1213 5368709120 (Ns300p2305 (RS301to312.d4 qz82 qz96 qz294) RS301to312.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS301to312.d48) rfl rfl rfl rfl 

noncomputable def Ns300p2312 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz781 qz4 qz96 615476 1000 622320 1000 

noncomputable def Ns300p2313 := @Enclosure.norm_gt_of_isNear qz781 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2513392407100580555225 18889465931478580854784 1196663358396875346315799 

noncomputable def Ns300p2314 := @Ns300p2313 Ns300p695 333033581 5368709120 1213 5368709120 (Ns300p2307 (RS301to312.d46 qz82 qz96 qz294) RS301to312.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS301to312.d48) rfl rfl rfl rfl 

noncomputable def Ns300p2315 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz293 (@BSN.thirtyTwoPi_le_dec qz82 620952 1000 qz85 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz780 qz781 (Ns300p2306 rfl rfl) (Ns300p2308 rfl rfl)) (Ns300p2309 qz10 qz85 rfl rfl rfl rfl (Ns300p2311 rfl)) (Ns300p2312 qz10 qz99 rfl rfl rfl rfl (Ns300p2314 rfl)) 

noncomputable abbrev qz295 := (RS301to312.d3 qz410 qz421 (@Enclosure.dec_le_dec qz410 qz421 622320 1000 623687 1000 (@Eq.refl Real qz410) (@Eq.refl Real qz421) rfl rfl rfl))

noncomputable abbrev qz782 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz295)

noncomputable def Ns300p2316 := @Enclosure.Real.IsNear.of_eq qz782 (hardyZApproximantRS₀ qz96) Bool.false 2513392407100580555225 18889465931478580854784 1196663358396875346315799 Ns300p695 

noncomputable abbrev qz296 := (@Enclosure.dec_le_dec qz410 qz421 622320 1000 623687 1000 (@Eq.refl Real qz410) (@Eq.refl Real qz421) rfl rfl rfl)

noncomputable def Ns300p2317 := @Enclosure.Real.IsNear.pos_val qz782 2513392407100580555225 18889465931478580854784 1196663358396875346315799 Ns300p695 (Ns300p2316 (RS301to312.d4 qz96 qz110 qz296) RS301to312.d52) rfl 

noncomputable abbrev qz783 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz295)

noncomputable def Ns300p2318 := @Enclosure.Real.IsNear.of_eq qz783 (hardyZApproximantRS₀ qz110) Bool.true 1006640935968740613433 295147905179352825856 23983585461984353328577 Ns300p809 

noncomputable def Ns300p2319 := @Enclosure.Real.IsNear.neg_val qz783 1006640935968740613433 295147905179352825856 23983585461984353328577 Ns300p809 (Ns300p2318 (RS301to312.d46 qz96 qz110 qz296) RS301to312.d53) rfl 

noncomputable def Ns300p2320 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz782 qz4 qz96 615476 1000 622320 1000 

noncomputable def Ns300p2321 := @Enclosure.norm_gt_of_isNear qz782 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2513392407100580555225 18889465931478580854784 1196663358396875346315799 

noncomputable def Ns300p2322 := @Ns300p2321 Ns300p695 333033581 5368709120 1213 5368709120 (Ns300p2316 (RS301to312.d4 qz96 qz110 qz296) RS301to312.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS301to312.d48) rfl rfl rfl rfl 

noncomputable def Ns300p2323 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz783 qz4 qz110 615476 1000 623687 1000 

noncomputable def Ns300p2324 := @Enclosure.norm_gt_of_isNear qz783 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1006640935968740613433 295147905179352825856 23983585461984353328577 

noncomputable def Ns300p2325 := @Ns300p2324 Ns300p809 333033581 5368709120 1213 5368709120 (Ns300p2318 (RS301to312.d46 qz96 qz110 qz296) RS301to312.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS301to312.d48) rfl rfl rfl rfl 

noncomputable def Ns300p2326 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz295 (@BSN.thirtyTwoPi_le_dec qz96 622320 1000 qz99 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz782 qz783 (Ns300p2317 rfl rfl) (Ns300p2319 rfl rfl)) (Ns300p2320 qz10 qz99 rfl rfl rfl rfl (Ns300p2322 rfl)) (Ns300p2323 qz10 qz113 rfl rfl rfl rfl (Ns300p2325 rfl)) 

noncomputable abbrev qz297 := (RS301to312.d3 qz421 qz432 (@Enclosure.dec_le_dec qz421 qz432 623687 1000 625053 1000 (@Eq.refl Real qz421) qz436 rfl rfl rfl))

noncomputable abbrev qz784 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz297)

noncomputable def Ns300p2327 := @Enclosure.Real.IsNear.of_eq qz784 (hardyZApproximantRS₀ qz110) Bool.true 1006640935968740613433 295147905179352825856 23983585461984353328577 Ns300p809 

noncomputable abbrev qz298 := (@Enclosure.dec_le_dec qz421 qz432 623687 1000 625053 1000 (@Eq.refl Real qz421) qz436 rfl rfl rfl)

noncomputable def Ns300p2328 := @Enclosure.Real.IsNear.neg_val qz784 1006640935968740613433 295147905179352825856 23983585461984353328577 Ns300p809 (Ns300p2327 (RS301to312.d4 qz110 qz124 qz298) RS301to312.d53) rfl 

noncomputable abbrev qz785 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz297)

noncomputable def Ns300p2329 := @Enclosure.Real.IsNear.of_eq qz785 (hardyZApproximantRS₀ qz124) Bool.false 19472545371288374903137 4722366482869645213696 500841405050772195219451 Ns300p924 

noncomputable def Ns300p2330 := @Enclosure.Real.IsNear.pos_val qz785 19472545371288374903137 4722366482869645213696 500841405050772195219451 Ns300p924 (Ns300p2329 (RS301to312.d46 qz110 qz124 qz298) RS301to312.d54) rfl 

noncomputable def Ns300p2331 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz784 qz4 qz110 615476 1000 623687 1000 

noncomputable def Ns300p2332 := @Enclosure.norm_gt_of_isNear qz784 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1006640935968740613433 295147905179352825856 23983585461984353328577 

noncomputable def Ns300p2333 := @Ns300p2332 Ns300p809 333033581 5368709120 1213 5368709120 (Ns300p2327 (RS301to312.d4 qz110 qz124 qz298) RS301to312.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS301to312.d48) rfl rfl rfl rfl 

noncomputable def Ns300p2334 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz785 qz4 qz124 615476 1000 625053 1000 

noncomputable def Ns300p2335 := @Enclosure.norm_gt_of_isNear qz785 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 19472545371288374903137 4722366482869645213696 500841405050772195219451 

noncomputable def Ns300p2336 := @Ns300p2335 Ns300p924 333033581 5368709120 1213 5368709120 (Ns300p2329 (RS301to312.d46 qz110 qz124 qz298) RS301to312.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS301to312.d48) rfl rfl rfl rfl 

noncomputable def Ns300p2337 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz297 (@BSN.thirtyTwoPi_le_dec qz110 623687 1000 qz113 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz784 qz785 (Ns300p2328 rfl rfl) (Ns300p2330 rfl rfl)) (Ns300p2331 qz10 qz113 rfl rfl rfl rfl (Ns300p2333 rfl)) (Ns300p2334 qz10 qz127 rfl rfl rfl rfl (Ns300p2336 rfl)) 

noncomputable abbrev qz580 := (@Enclosure.dec_le_dec qz687 qz694 625053 1000 626419 1000 (@Eq.refl Real qz687) (@Eq.refl Real qz694) rfl rfl rfl)

noncomputable abbrev qz299 := (RS301to312.d3 qz432 qz444 qz580)

noncomputable abbrev qz786 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz299)

noncomputable def Ns300p2338 := @Enclosure.Real.IsNear.of_eq qz786 (hardyZApproximantRS₀ qz124) Bool.false 19472545371288374903137 4722366482869645213696 500841405050772195219451 Ns300p924 

noncomputable abbrev qz300 := qz580

noncomputable def Ns300p2339 := @Enclosure.Real.IsNear.pos_val qz786 19472545371288374903137 4722366482869645213696 500841405050772195219451 Ns300p924 (Ns300p2338 (RS301to312.d4 qz124 qz138 qz300) RS301to312.d54) rfl 

noncomputable abbrev qz787 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz299)

noncomputable def Ns300p2340 := @Enclosure.Real.IsNear.of_eq qz787 (hardyZApproximantRS₀ qz138) Bool.true 15479186721012236706633 9444732965739290427392 602306043917468617594429 Ns300p1038 

noncomputable def Ns300p2341 := @Enclosure.Real.IsNear.neg_val qz787 15479186721012236706633 9444732965739290427392 602306043917468617594429 Ns300p1038 (Ns300p2340 (RS301to312.d46 qz124 qz138 qz300) RS301to312.d55) rfl 

noncomputable def Ns300p2342 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz786 qz4 qz124 615476 1000 625053 1000 

noncomputable def Ns300p2343 := @Enclosure.norm_gt_of_isNear qz786 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 19472545371288374903137 4722366482869645213696 500841405050772195219451 

noncomputable def Ns300p2344 := @Ns300p2343 Ns300p924 333033581 5368709120 1213 5368709120 (Ns300p2338 (RS301to312.d4 qz124 qz138 qz300) RS301to312.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS301to312.d48) rfl rfl rfl rfl 

noncomputable def Ns300p2345 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz787 qz4 qz138 615476 1000 626419 1000 

noncomputable def Ns300p2346 := @Enclosure.norm_gt_of_isNear qz787 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 15479186721012236706633 9444732965739290427392 602306043917468617594429 

noncomputable def Ns300p2347 := @Ns300p2346 Ns300p1038 333033581 5368709120 1213 5368709120 (Ns300p2340 (RS301to312.d46 qz124 qz138 qz300) RS301to312.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS301to312.d48) rfl rfl rfl rfl 

noncomputable def Ns300p2348 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz299 (@BSN.thirtyTwoPi_le_dec qz124 625053 1000 qz127 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz786 qz787 (Ns300p2339 rfl rfl) (Ns300p2341 rfl rfl)) (Ns300p2342 qz10 qz127 rfl rfl rfl rfl (Ns300p2344 rfl)) (Ns300p2345 qz10 qz141 rfl rfl rfl rfl (Ns300p2347 rfl)) 

noncomputable abbrev qz581 := (@Enclosure.dec_le_dec qz694 qz701 626419 1000 627784 1000 (@Eq.refl Real qz694) qz704 rfl rfl rfl)

noncomputable abbrev qz301 := (RS301to312.d3 qz444 qz456 qz581)

noncomputable abbrev qz788 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz301)

noncomputable def Ns300p2349 := @Enclosure.Real.IsNear.of_eq qz788 (hardyZApproximantRS₀ qz138) Bool.true 15479186721012236706633 9444732965739290427392 602306043917468617594429 Ns300p1038 

noncomputable abbrev qz302 := qz581

noncomputable def Ns300p2350 := @Enclosure.Real.IsNear.neg_val qz788 15479186721012236706633 9444732965739290427392 602306043917468617594429 Ns300p1038 (Ns300p2349 (RS301to312.d4 qz138 qz152 qz302) RS301to312.d55) rfl 

noncomputable abbrev qz789 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz301)

noncomputable def Ns300p2351 := @Enclosure.Real.IsNear.of_eq qz789 (hardyZApproximantRS₀ qz152) Bool.false 5858106980867814955581 4722366482869645213696 100590251280817894408501 Ns300p1144 

noncomputable def Ns300p2352 := @Enclosure.Real.IsNear.pos_val qz789 5858106980867814955581 4722366482869645213696 100590251280817894408501 Ns300p1144 (Ns300p2351 (RS301to312.d46 qz138 qz152 qz302) RS301to312.d56) rfl 

noncomputable def Ns300p2353 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz788 qz4 qz138 615476 1000 626419 1000 

noncomputable def Ns300p2354 := @Enclosure.norm_gt_of_isNear qz788 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 15479186721012236706633 9444732965739290427392 602306043917468617594429 

noncomputable def Ns300p2355 := @Ns300p2354 Ns300p1038 333033581 5368709120 1213 5368709120 (Ns300p2349 (RS301to312.d4 qz138 qz152 qz302) RS301to312.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS301to312.d48) rfl rfl rfl rfl 

noncomputable def Ns300p2356 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz789 qz4 qz152 615476 1000 627784 1000 

noncomputable def Ns300p2357 := @Enclosure.norm_gt_of_isNear qz789 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 5858106980867814955581 4722366482869645213696 100590251280817894408501 

noncomputable def Ns300p2358 := @Ns300p2357 Ns300p1144 333033581 5368709120 1213 5368709120 (Ns300p2351 (RS301to312.d46 qz138 qz152 qz302) RS301to312.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS301to312.d48) rfl rfl rfl rfl 

noncomputable def Ns300p2359 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz301 (@BSN.thirtyTwoPi_le_dec qz138 626419 1000 qz141 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz788 qz789 (Ns300p2350 rfl rfl) (Ns300p2352 rfl rfl)) (Ns300p2353 qz10 qz141 rfl rfl rfl rfl (Ns300p2355 rfl)) (Ns300p2356 qz10 qz155 rfl rfl rfl rfl (Ns300p2358 rfl)) 

noncomputable abbrev qz790 := (@Enclosure.dec_le_dec qz846 qz851 627784 1000 629148 1000 (@Eq.refl Real qz846) qz854 rfl rfl rfl)

noncomputable abbrev qz582 := qz790

noncomputable abbrev qz303 := (RS301to312.d3 qz456 qz469 qz582)

noncomputable abbrev qz791 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz303)

noncomputable def Ns300p2360 := @Enclosure.Real.IsNear.of_eq qz791 (hardyZApproximantRS₀ qz152) Bool.false 5858106980867814955581 4722366482869645213696 100590251280817894408501 Ns300p1144 

noncomputable abbrev qz304 := qz582

noncomputable def Ns300p2361 := @Enclosure.Real.IsNear.pos_val qz791 5858106980867814955581 4722366482869645213696 100590251280817894408501 Ns300p1144 (Ns300p2360 (RS301to312.d4 qz152 qz167 qz304) RS301to312.d56) rfl 

noncomputable abbrev qz792 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz303)

noncomputable def Ns300p2362 := @Enclosure.Real.IsNear.of_eq qz792 (hardyZApproximantRS₀ qz167) Bool.true 3663647960807928705895 1180591620717411303424 22702420029474412072893 Ns300p579 

noncomputable def Ns300p2363 := @Enclosure.Real.IsNear.neg_val qz792 3663647960807928705895 1180591620717411303424 22702420029474412072893 Ns300p579 (Ns300p2362 (RS301to312.d46 qz152 qz167 qz304) RS301to312.d61) rfl 

noncomputable def Ns300p2364 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz791 qz4 qz152 615476 1000 627784 1000 

noncomputable def Ns300p2365 := @Enclosure.norm_gt_of_isNear qz791 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 5858106980867814955581 4722366482869645213696 100590251280817894408501 

noncomputable def Ns300p2366 := @Ns300p2365 Ns300p1144 333033581 5368709120 1213 5368709120 (Ns300p2360 (RS301to312.d4 qz152 qz167 qz304) RS301to312.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS301to312.d48) rfl rfl rfl rfl 

noncomputable def Ns300p2367 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz792 qz4 qz167 615476 1000 629148 1000 

noncomputable def Ns300p2368 := @Enclosure.norm_gt_of_isNear qz792 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 3663647960807928705895 1180591620717411303424 22702420029474412072893 

noncomputable def Ns300p2369 := @Ns300p2368 Ns300p579 333033581 5368709120 1213 5368709120 (Ns300p2362 (RS301to312.d46 qz152 qz167 qz304) RS301to312.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 333033581 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS301to312.d48) rfl rfl rfl rfl 

noncomputable def Ns300p2370 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz303 (@BSN.thirtyTwoPi_le_dec qz152 627784 1000 qz155 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz791 qz792 (Ns300p2361 rfl rfl) (Ns300p2363 rfl rfl)) (Ns300p2364 qz10 qz155 rfl rfl rfl rfl (Ns300p2366 rfl)) (Ns300p2367 qz10 qz170 rfl rfl rfl rfl (Ns300p2369 rfl)) 

noncomputable abbrev qz793 := (@Enclosure.dec_le_dec qz851 qz859 629148 1000 630512 1000 qz854 qz863 rfl rfl rfl)

noncomputable abbrev qz583 := qz793

noncomputable abbrev qz305 := (RS301to312.d3 qz469 qz509 qz583)

noncomputable abbrev qz794 := (Zeta.Certificates.ZIntervalRS.fstVal qz305)

noncomputable def Ns300p2371 := @Enclosure.Real.IsNear.of_eq qz794 (hardyZApproximantRS qz167) Bool.true Ns300p1392 Ns300p1393 Ns300p1394 Ns300p1395 

noncomputable abbrev qz306 := qz583

noncomputable def Ns300p2372 := @Enclosure.Real.IsNear.neg_val qz794 Ns300p1392 Ns300p1393 Ns300p1394 Ns300p1395 (Ns300p2371 (RS301to312.d62 qz167 qz212 qz306) RS301to312.d71) rfl 

noncomputable abbrev qz795 := (Zeta.Certificates.ZIntervalRS.sndVal qz305)

noncomputable def Ns300p2373 := @Enclosure.Real.IsNear.of_eq qz795 (hardyZApproximantRS qz212) Bool.false Ns300p1626 Ns300p1627 Ns300p1628 Ns300p1629 

noncomputable def Ns300p2374 := @Enclosure.Real.IsNear.pos_val qz795 Ns300p1626 Ns300p1627 Ns300p1628 Ns300p1629 (Ns300p2373 (RS301to312.d72 qz167 qz212 qz306) RS301to312.d73) rfl 

noncomputable def Ns300p2375 := BSN.norm_gt_hardyZErrorBoundRS_of_le qz794 qz4 qz167 615476 1000 629148 1000 

noncomputable def Ns300p2376 := @Enclosure.norm_gt_of_isNear qz794 (hardyZErrorBoundRS qz4) Bool.true Bool.false Ns300p1392 Ns300p1393 Ns300p1394 

noncomputable def Ns300p2377 := @Ns300p2376 Ns300p1395 21776601 1073741824 201 1073741824 (Ns300p2371 (RS301to312.d62 qz167 qz212 qz306) RS301to312.d71) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) (hardyZErrorBoundRS qz4) Bool.false 21776601 1073741824 201 1073741824 (@Eq.refl Real (hardyZErrorBoundRS qz4)) RS301to312.d74) rfl rfl rfl rfl 

noncomputable def Ns300p2378 := BSN.norm_gt_hardyZErrorBoundRS_of_le qz795 qz4 qz212 615476 1000 630512 1000 

noncomputable def Ns300p2379 := @Enclosure.norm_gt_of_isNear qz795 (hardyZErrorBoundRS qz4) Bool.false Bool.false Ns300p1626 Ns300p1627 Ns300p1628 

noncomputable def Ns300p2380 := @Ns300p2379 Ns300p1629 21776601 1073741824 201 1073741824 (Ns300p2373 (RS301to312.d72 qz167 qz212 qz306) RS301to312.d73) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) (hardyZErrorBoundRS qz4) Bool.false 21776601 1073741824 201 1073741824 (@Eq.refl Real (hardyZErrorBoundRS qz4)) RS301to312.d74) rfl rfl rfl rfl 

noncomputable def Ns300p2381 := @Zeta.Certificates.ZIntervalRS.Certificate.mk qz305 (@BSN.thirtyTwoPi_le_dec qz167 629148 1000 qz170 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz794 qz795 (Ns300p2372 rfl rfl) (Ns300p2374 rfl rfl)) (Ns300p2375 qz10 qz170 rfl rfl rfl rfl (Ns300p2377 rfl)) (Ns300p2378 qz10 qz215 rfl rfl rfl rfl (Ns300p2380 rfl)) 

noncomputable abbrev qz873 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 630512 1000) (Enclosure.sfrac Bool.false 631875 1000) 630512 1000 631875 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 630512 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 631875 1000)) rfl rfl rfl)

noncomputable abbrev qz796 := qz873

noncomputable abbrev qz584 := qz796

noncomputable abbrev qz307 := (RS301to312.d3 qz509 qz544 qz584)

noncomputable abbrev qz797 := (Zeta.Certificates.ZIntervalRS.fstVal qz307)

noncomputable def Ns300p2382 := @Enclosure.Real.IsNear.of_eq qz797 (hardyZApproximantRS qz212) Bool.false Ns300p1626 Ns300p1627 Ns300p1628 Ns300p1629 

noncomputable abbrev qz308 := qz584

noncomputable def Ns300p2383 := @Enclosure.Real.IsNear.pos_val qz797 Ns300p1626 Ns300p1627 Ns300p1628 Ns300p1629 (Ns300p2382 (RS301to312.d62 qz212 qz249 qz308) RS301to312.d73) rfl 

noncomputable abbrev qz798 := (Zeta.Certificates.ZIntervalRS.sndVal qz307)

noncomputable def Ns300p2384 := @Enclosure.Real.IsNear.of_eq qz798 (hardyZApproximantRS qz249) Bool.true Ns300p1950 Ns300p1951 Ns300p1952 Ns300p1953 

noncomputable def Ns300p2385 := @Enclosure.Real.IsNear.neg_val qz798 Ns300p1950 Ns300p1951 Ns300p1952 Ns300p1953 (Ns300p2384 (RS301to312.d72 qz212 qz249 qz308) RS301to312.d75) rfl 

noncomputable def Ns300p2386 := BSN.norm_gt_hardyZErrorBoundRS_of_le qz797 qz4 qz212 615476 1000 630512 1000 

noncomputable def Ns300p2387 := @Enclosure.norm_gt_of_isNear qz797 (hardyZErrorBoundRS qz4) Bool.false Bool.false Ns300p1626 Ns300p1627 Ns300p1628 

noncomputable def Ns300p2388 := @Ns300p2387 Ns300p1629 21776601 1073741824 201 1073741824 (Ns300p2382 (RS301to312.d62 qz212 qz249 qz308) RS301to312.d73) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) (hardyZErrorBoundRS qz4) Bool.false 21776601 1073741824 201 1073741824 (@Eq.refl Real (hardyZErrorBoundRS qz4)) RS301to312.d74) rfl rfl rfl rfl 

noncomputable def Ns300p2389 := BSN.norm_gt_hardyZErrorBoundRS_of_le qz798 qz4 qz249 615476 1000 631875 1000 

noncomputable def Ns300p2390 := @Enclosure.norm_gt_of_isNear qz798 (hardyZErrorBoundRS qz4) Bool.true Bool.false Ns300p1950 Ns300p1951 Ns300p1952 

noncomputable def Ns300p2391 := @Ns300p2390 Ns300p1953 21776601 1073741824 201 1073741824 (Ns300p2384 (RS301to312.d72 qz212 qz249 qz308) RS301to312.d75) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) (hardyZErrorBoundRS qz4) Bool.false 21776601 1073741824 201 1073741824 (@Eq.refl Real (hardyZErrorBoundRS qz4)) RS301to312.d74) rfl rfl rfl rfl 

noncomputable def Ns300p2392 := @Zeta.Certificates.ZIntervalRS.Certificate.mk qz307 (@BSN.thirtyTwoPi_le_dec qz212 630512 1000 qz215 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz797 qz798 (Ns300p2383 rfl rfl) (Ns300p2385 rfl rfl)) (Ns300p2386 qz10 qz215 rfl rfl rfl rfl (Ns300p2388 rfl)) (Ns300p2389 qz10 qz254 rfl rfl rfl rfl (Ns300p2391 rfl)) 

noncomputable def Ns300p2393 := @List.cons RS301to312.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz305 (@Or.inl (Zeta.Certificates.ZIntervalRS.Certificate qz305) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz305) Ns300p2381)) (@List.cons RS301to312.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz307 (@Or.inl (Zeta.Certificates.ZIntervalRS.Certificate qz307) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz307) Ns300p2392)) (@List.nil RS301to312.d0)) 

noncomputable def Ns300p2394 := @List.cons RS301to312.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz301 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz301) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz301) Ns300p2359)) (@List.cons RS301to312.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz303 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz303) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz303) Ns300p2370)) Ns300p2393) 

noncomputable def Ns300p2395 := @List.cons RS301to312.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz297 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz297) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz297) Ns300p2337)) (@List.cons RS301to312.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz299 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz299) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz299) Ns300p2348)) Ns300p2394) 

noncomputable def Ns300p2396 := @List.cons RS301to312.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz293 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz293) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz293) Ns300p2315)) (@List.cons RS301to312.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz295 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz295) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz295) Ns300p2326)) Ns300p2395) 

noncomputable def Ns300p2397 := @List.cons RS301to312.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz289 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz289) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz289) Ns300p2293)) (@List.cons RS301to312.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz291 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz291) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz291) Ns300p2304)) Ns300p2396) 

noncomputable def Ns300p2398 := @List.cons RS301to312.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz285 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz285) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz285) Ns300p2271)) (@List.cons RS301to312.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz287 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz287) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz287) Ns300p2282)) Ns300p2397) 

noncomputable abbrev qz799 := (RS301to312.d2 qz851 qz859 (@Enclosure.dec_le_dec qz851 qz859 629148 1000 630512 1000 qz854 qz863 rfl rfl rfl))

noncomputable abbrev qz800 := (@List.cons RS301to312.d1 (RS301to312.d2 qz859 qz866 qz873) (@List.nil RS301to312.d1))

noncomputable abbrev qz585 := (@List.cons RS301to312.d1 (RS301to312.d2 qz701 qz713 qz790) (@List.cons RS301to312.d1 qz799 qz800))

noncomputable abbrev qz309 := (@List.cons RS301to312.d1 (RS301to312.d2 qz432 qz444 qz580) (@List.cons RS301to312.d1 (RS301to312.d2 qz444 qz456 qz581) qz585))

noncomputable def Ns300p2399 := @List.cons RS301to312.d1 (RS301to312.d2 qz96 qz110 qz296) (@List.cons RS301to312.d1 (RS301to312.d2 qz110 qz124 qz298) qz309) 

noncomputable def Ns300p2400 := @List.IsChain.cons_cons RS301to312.d1 RS301to312.d76 (RS301to312.d2 qz82 qz96 qz294) (RS301to312.d2 qz96 qz110 qz296) (@List.cons RS301to312.d1 (RS301to312.d2 qz110 qz124 qz298) qz309) 

noncomputable def Ns300p2401 := @List.IsChain.cons_cons RS301to312.d1 RS301to312.d76 (RS301to312.d2 qz96 qz110 qz296) (RS301to312.d2 qz110 qz124 qz298) qz309 (@Enclosure.dec_le_dec qz110 qz110 623687 1000 623687 1000 qz113 qz113 rfl rfl rfl) 

noncomputable abbrev qz310 := qz585

noncomputable abbrev qz586 := (RS301to312.d2 qz701 qz713 qz790)

noncomputable abbrev qz311 := qz586

noncomputable abbrev qz587 := (@List.cons RS301to312.d1 qz799 qz800)

noncomputable abbrev qz312 := qz587

noncomputable abbrev qz588 := qz799

noncomputable abbrev qz313 := qz588

noncomputable abbrev qz589 := qz800

noncomputable abbrev qz314 := qz589

noncomputable abbrev qz801 := (RS301to312.d2 qz859 qz866 qz873)

noncomputable abbrev qz590 := qz801

noncomputable abbrev qz315 := qz590

noncomputable def Ns300p2402 := @List.IsChain.cons_cons RS301to312.d1 RS301to312.d76 (RS301to312.d2 qz124 qz138 qz300) (RS301to312.d2 qz138 qz152 qz302) qz310 (@Enclosure.dec_le_dec qz138 qz138 626419 1000 626419 1000 qz141 qz141 rfl rfl rfl) (@List.IsChain.cons_cons RS301to312.d1 RS301to312.d76 (RS301to312.d2 qz138 qz152 qz302) qz311 qz312 (@Enclosure.dec_le_dec qz152 qz152 627784 1000 627784 1000 qz155 qz155 rfl rfl rfl) (@List.IsChain.cons_cons RS301to312.d1 RS301to312.d76 qz311 qz313 qz314 (@Enclosure.dec_le_dec qz167 qz167 629148 1000 629148 1000 qz170 qz170 rfl rfl rfl) (@List.IsChain.cons_cons RS301to312.d1 RS301to312.d76 qz313 qz315 (@List.nil RS301to312.d1) (@Enclosure.dec_le_dec qz212 qz212 630512 1000 630512 1000 qz215 qz215 rfl rfl rfl) (@List.IsChain.singleton RS301to312.d1 RS301to312.d76 qz315)))) 

noncomputable abbrev qz316 := (@List.cons RS301to312.d1 (RS301to312.d2 qz444 qz456 qz581) qz585)

noncomputable def Ns300p2403 := @List.IsChain.cons_cons RS301to312.d1 RS301to312.d76 (RS301to312.d2 qz110 qz124 qz298) (RS301to312.d2 qz124 qz138 qz300) qz316 (@Enclosure.dec_le_dec qz124 qz124 625053 1000 625053 1000 qz127 qz127 rfl rfl rfl) Ns300p2402 

noncomputable abbrev qz802 := (@List.cons RS301to312.d1 (RS301to312.d2 qz82 qz96 qz294) Ns300p2399)

noncomputable def Ns300p2404 := @List.IsChain.cons_cons RS301to312.d1 RS301to312.d76 (RS301to312.d2 qz4 qz30 qz286) (RS301to312.d2 qz30 qz54 qz288) (@List.cons RS301to312.d1 (RS301to312.d2 qz54 qz68 qz290) (@List.cons RS301to312.d1 (RS301to312.d2 qz68 qz82 qz292) qz802)) (@Enclosure.dec_le_dec qz30 qz30 616846 1000 616846 1000 qz33 qz33 rfl rfl rfl) (@List.IsChain.cons_cons RS301to312.d1 RS301to312.d76 (RS301to312.d2 qz30 qz54 qz288) (RS301to312.d2 qz54 qz68 qz290) (@List.cons RS301to312.d1 (RS301to312.d2 qz68 qz82 qz292) qz802) (@Enclosure.dec_le_dec qz54 qz54 618215 1000 618215 1000 qz57 qz57 rfl rfl rfl) (@List.IsChain.cons_cons RS301to312.d1 RS301to312.d76 (RS301to312.d2 qz54 qz68 qz290) (RS301to312.d2 qz68 qz82 qz292) qz802 (@Enclosure.dec_le_dec qz68 qz68 619584 1000 619584 1000 qz71 qz71 rfl rfl rfl) (@List.IsChain.cons_cons RS301to312.d1 RS301to312.d76 (RS301to312.d2 qz68 qz82 qz292) (RS301to312.d2 qz82 qz96 qz294) Ns300p2399 (@Enclosure.dec_le_dec qz82 qz82 620952 1000 620952 1000 qz85 qz85 rfl rfl rfl) (Ns300p2400 (@Enclosure.dec_le_dec qz96 qz96 622320 1000 622320 1000 qz99 qz99 rfl rfl rfl) (Ns300p2401 Ns300p2403))))) 

noncomputable abbrev qz591 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz592 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns300p2398 Ns300p2404)

noncomputable abbrev qz593 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns300p2398 Ns300p2404))

theorem RS301to312.d77 : Zeta.Certificates.BatchSpec 12 615476 1000 631875 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz591 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz591 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz591 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz591 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz591 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz249)))) qz592 (@And.intro (@Eq Nat (@List.length qz591 qz593) 12) (And (@Eq (Option Real) (@Option.map qz591 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz591 qz593)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz591 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz591 qz593)) (@Option.some Real qz249))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz591 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz591 qz593)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz591 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz591 qz593)) (@Option.some Real qz249)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz249))))

theorem solution : Zeta.Certificates.BatchSpec 12 615476 1000 631875 1000 := RS301to312.d77
#print axioms solution
#check solution
