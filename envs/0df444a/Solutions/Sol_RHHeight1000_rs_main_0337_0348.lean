-- Prove2me | solution 1 for RHHeight1000.rs_main_0337_0348
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:20:10.930765+00:00
-- url     : https://prove2.me/submissions/738baed9-f90e-4751-9658-8d9be2dccece

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

noncomputable def RS337to348.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS337to348.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS337to348.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS337to348.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS337to348.d2 a b h 

theorem RS337to348.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS337to348.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS337to348.d3 a b h)) 

noncomputable def Ns336p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns336p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns336p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns336p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns336p0 Ns336p1 Ns336p2 Ns336p1 307286088 268435456 1 77440000 307286088 268435456 1 77440000 153643044 134217728 2 134217728 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns336p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns336p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns336p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns336p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns336p8 := nat_lit 167537954069964697925743468333314178468718661948561187618563575975392713740913527107727581163208035826476740967700482432525301063254420572874757592895482956004842597348203117269212172556829666669574421653274845612596416189641484794702002223261246862056663160605878293700340502480877986491439034432953223334258717026053687371824342493299510132312376251152844516906794910572262907940062760396663270105627554083664899640691826599584783763757814813433640133591539937449421955686657622469485188711283992428713614179785896055117030632677201478317872225272595773536303110412989181984739022579128493081560758017763072115692678596043664844667144619713966763611484179303468167142547433165016751768184247559143333542643815355903304572487929375 

noncomputable def Ns336p9 := nat_lit 17907736863639440849562382641391758203535690054199171304015283257442503423240620144819838407313611418261944516207295868563739563278604805791797182761045687776939279949642059267526948014748996956777332184087524644234759874591635243045607722412471722018588244283882362848653445974523544951031470230725674276297342086185092985546835544820091590454230569790847977790484558207349923322458845585052164126500435851662252152223728079705692133047658564669873831757357628115566356048471439549797170528303905720944834637690907185213991407615774042056720704508980680095051114888612186461088301140868302968264130481206655302741383410655080008578156649725227045954510069588220729495895148666460653631514375880874422615237249871322129146554264800 

noncomputable def Ns336p10 := nat_lit 55164646516618494962085419356369025784335016154267579706247610053041231157772817011486486467101704279863254798704146668052276438579475100451766223896220272709675360577301802978530276301158911649961092601279696986330335403118086533522541958716560166657634553390183479955483588238249446822384543398154260439705049143284278540285021213103458182619368483938376641172730818250587232036579805400979202432024046862170503602539341971086573372247299262086029843105216008583038025403798224342134620653974939981235680083776396058604459065501719125356177784467570909658245422960948263734871602033841948787585406240093531041217463298165642337705122589129757920995868559518021463265498464182174549661735402095023640043996665674913376875 

noncomputable def Ns336p11 := BSN.log_dyadic_bound Ns336p6 Ns336p7 15 14 Ns336p8 268435456 77440000 Ns336p9 Ns336p10 307286088 Ns336p4 Ns336p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns336p6) (BSN.artanhQ Ns336p7) 0 14 Ns336p9 Ns336p8 Ns336p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns336p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns336p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns336p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns336p15 := nat_lit 167537954069966963268140139327979112712430526945422964221951926912223381190141639739514890494967825643602350173964944759828460064784215684919760383437959917620844610857567326816719640593037578236900835917107172977527392439886629774248115214831425484905681376157923696414882114961796820014026232307332015059110330001516939277521159573995394989771587717775443426002499543257897301982481613760098955890450106043861450716722534643739571053080256776912576113428445260435254713579381797931690799491102381747484553243404562568585572234105168360737285205910186933811836504830286397217473365026331067977496463917110493303316865058355012304571237619413071097245713770677768486493924969821719264401216877841676972336093778875903304572487929375 

noncomputable def Ns336p16 := nat_lit 17907736863639702486765313263906285882628955290251965205176678923530777959693011244026517850256414903756943142851250712732214241881959351517241344993825585048584379523049477943740273636414656012170312373198803997844271825165684859407921203335666024680974464565759223251918458072775203410604089667122984485578465112081892102496937045858735135721609691262763214794451343726045584198128451069547586972080574568545086657023793200560105564573365716615162566961587407171758966967827997201380802107846920231945878242774600967607639551032178207663699700360114112068650063802902647517702890145150192721997537569966984346993833704449560383184487996362781528900358997452380059737141488304159449328022742959995775545894292303322129146554264800 

noncomputable def Ns336p17 := nat_lit 55164646516619937449385584700664297411818070214438189962773666351465523500358685366424500506990751111492356556545320273548942244833046464529601272738875466881799996765940232256588350019911833156887888425998391295014189841212513610526066550079316346993943774342801096070086869790972589246312728227659319758310961510342377923950694747797317942483020440897997204711883064182772445608288320382376665481938194224815739627075458138172195220395246294556718284728034954178416253903237031389214179719385823921869528509431462690683227358218086518156757026652846493301460983550768858152506145788622699720737745394141184245149692548799188169247529408201840608223422296381897323845616153036586108326210125693898345963996665674913376875 

noncomputable def Ns336p18 := BSN.log_dyadic_bound Ns336p13 Ns336p14 15 14 Ns336p15 268435456 77440000 Ns336p16 Ns336p17 307286088 Ns336p12 Ns336p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns336p13) (BSN.artanhQ Ns336p14) 0 14 Ns336p16 Ns336p15 Ns336p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns336p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 153643044 134217728 2 134217728 38410761 33554432 1 67108864 (Ns336p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns336p0 Ns336p1 307286088 268435456 1 77440000 Bool.false (BSN.logfrac_isNear Ns336p4 Ns336p5 1 Ns336p0 Ns336p1 307286088 268435456 77440000 rfl rfl rfl (Ns336p11 rfl))) (BSN.isNear_log_sfrac Ns336p2 Ns336p1 307286088 268435456 1 77440000 Bool.false (BSN.logfrac_isNear Ns336p12 Ns336p5 1 Ns336p2 Ns336p1 307286088 268435456 77440000 rfl rfl rfl (Ns336p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS337to348.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 67108864 := Ns336p19 

noncomputable def Ns336p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 16777216 4840000 385100712855 135135 11629079 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz820 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz621 := qz820

noncomputable abbrev qz316 := qz621

noncomputable abbrev qz0 := qz316

theorem RS337to348.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 11629079 16777216 1 4840000 := BSN.isNear_log_sfrac 2 1 11629079 16777216 1 4840000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 11629079 16777216 4840000 rfl rfl rfl (Ns336p20 rfl)) 

theorem RS337to348.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 186065264 268435456 56 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 11629079 16777216 1 4840000 186065264 268435456 56 268435456 RS337to348.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz622 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz318 := qz622

noncomputable def Ns336p21 := @Enclosure.Real.IsNear.inv_image qz317 47453133 33554432 1 33554432 11863282 11863284 16777216 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2) qz318)) Bool.false 47453133 33554432 1 33554432 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2) qz318)) Bool.false 47453133 33554432 1 33554432 47453133 33554432 1 33554432 (BSN.sqrt_enclosure 2 1 23726566 23726567 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz319 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS337to348.d8 : Enclosure.Real.IsNear qz319 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz319 Bool.false 23726566 33554432 2 33554432 11863283 16777216 1 16777216 (Ns336p21 rfl rfl) rfl 

theorem RS337to348.d9 : Enclosure.Real.IsNear qz319 Bool.false 189812528 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz319 Bool.false 11863283 16777216 1 16777216 189812528 268435456 16 268435456 RS337to348.d8 rfl 

noncomputable def Ns336p22 := BSN.log_dyadic_bound 1 2 13 12 132638213186519040000 16777216 4840000 13079757671720842725 316234143225 18431655 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz320 := (Enclosure.sfrac Bool.false 3 1)

theorem RS337to348.d10 : Enclosure.Real.IsNear (Real.log qz320) Bool.false 18431655 16777216 1 4840000 := BSN.isNear_log_sfrac 3 1 18431655 16777216 1 4840000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 18431655 16777216 4840000 rfl rfl rfl (Ns336p22 rfl)) 

theorem RS337to348.d11 : Enclosure.Real.IsNear (Real.log qz320) Bool.false 294906480 268435456 56 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz320) Bool.false 18431655 16777216 1 4840000 294906480 268435456 56 268435456 RS337to348.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable def Ns336p23 := @Enclosure.Real.IsNear.inv_image qz321 58117981 33554432 1 33554432 9686330 9686331 16777216 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3) qz318)) Bool.false 58117981 33554432 1 33554432 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3) qz318)) Bool.false 58117981 33554432 1 33554432 58117981 33554432 1 33554432 (BSN.sqrt_enclosure 3 1 29058990 29058991 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz322 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS337to348.d12 : Enclosure.Real.IsNear qz322 Bool.false 19372661 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz322 Bool.false 19372661 33554432 1 33554432 19372661 33554432 1 33554432 (Ns336p23 rfl rfl) rfl 

theorem RS337to348.d13 : Enclosure.Real.IsNear qz322 Bool.false 154981288 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz322 Bool.false 19372661 33554432 1 33554432 154981288 268435456 8 268435456 RS337to348.d12 rfl 

noncomputable def Ns336p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns336p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns336p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns336p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns336p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns336p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns336p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns336p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns336p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns336p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns336p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns336p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns336p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns336p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns336p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns336p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns336p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns336p25 Ns336p26 Ns336p27 Ns336p28 200200021673987500790625 Ns336p29 Ns336p30 Ns336p31 Ns336p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns336p32 Ns336p33 151412625 Ns336p34 Ns336p35 1322214852783825 Ns336p27 Ns336p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns336p32 Ns336p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns336p34 Ns336p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns336p36 Ns336p37 1267389585 Ns336p38 Ns336p39 1927077560082675 Ns336p29 Ns336p30 Ns336p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns336p36 Ns336p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns336p38 Ns336p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz323 := (@Nat.cast Real Real.instNatCast 5)

theorem RS337to348.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz323)) Bool.false Ns336p24 Ns336p25 1 Ns336p26 := Ns336p40 rfl rfl rfl 

noncomputable def Ns336p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns336p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns336p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns336p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns336p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns336p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns336p25 Ns336p26 Ns336p42 Ns336p43 9945 Ns336p44 Ns336p45 65835 Ns336p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns336p42 Ns336p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns336p44 Ns336p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS337to348.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns336p41 Ns336p25 1 Ns336p26 := Ns336p46 rfl 

noncomputable def Ns336p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns336p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS337to348.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns336p47 Ns336p25 1 Ns336p48 := BSN.pi_combine Ns336p24 Ns336p41 Ns336p25 Ns336p26 Ns336p48 Ns336p47 rfl rfl rfl rfl RS337to348.d14 RS337to348.d15 

theorem RS337to348.d17 : Enclosure.Real.IsNear Real.pi Bool.false 14148475504056880 4503599627370496 1 4503599627370496 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns336p47 Ns336p25 1 Ns336p48 14148475504056880 4503599627370496 1 4503599627370496 RS337to348.d16 rfl 

noncomputable def Ns336p49 := nat_lit 147443727375074537121690809726715087890625 

noncomputable def Ns336p50 := nat_lit 22889945643899497138335355216896171420000 

noncomputable def Ns336p51 := nat_lit 355592320898650075318906513310625 

noncomputable def Ns336p52 := BSN.log_dyadic_bound 3 5 17 16 Ns336p49 16777216 4840000 Ns336p50 Ns336p51 23258159 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 3) (BSN.artanhQ 5) 0 16 Ns336p50 Ns336p49 Ns336p51 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz623 := (Enclosure.sfrac Bool.false 4 1)

noncomputable abbrev qz324 := qz623

theorem RS337to348.d18 : Enclosure.Real.IsNear (Real.log qz324) Bool.false 23258159 16777216 1 4840000 := BSN.isNear_log_sfrac 4 1 23258159 16777216 1 4840000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 23258159 16777216 4840000 rfl rfl rfl (Ns336p52 rfl)) 

theorem RS337to348.d19 : Enclosure.Real.IsNear (Real.log qz324) Bool.false 372130544 268435456 56 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz324) Bool.false 23258159 16777216 1 4840000 372130544 268435456 56 268435456 RS337to348.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable def Ns336p53 := @Enclosure.Real.IsNear.inv_image qz325 67108865 33554432 1 33554432 8388607 8388608 16777216 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4) qz318)) Bool.false 67108865 33554432 1 33554432 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4) qz318)) Bool.false 67108865 33554432 1 33554432 67108865 33554432 1 33554432 (BSN.sqrt_enclosure 4 1 33554432 33554433 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz326 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS337to348.d20 : Enclosure.Real.IsNear qz326 Bool.false 16777215 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz326 Bool.false 16777215 33554432 1 33554432 16777215 33554432 1 33554432 (Ns336p53 rfl rfl) rfl 

theorem RS337to348.d21 : Enclosure.Real.IsNear qz326 Bool.false 134217720 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz326 Bool.false 16777215 33554432 1 33554432 134217720 268435456 8 268435456 RS337to348.d20 rfl 

noncomputable def Ns336p54 := nat_lit 61697213297292266380244507781205789317049021875 

noncomputable def Ns336p55 := nat_lit 12776162289178456695994184080609776001208236500 

noncomputable def Ns336p56 := nat_lit 57671893776295590731569354191667200000 

noncomputable def Ns336p57 := nat_lit 885951608314392539099884620 

noncomputable def Ns336p58 := nat_lit 1286943652057122751813246125 

noncomputable def Ns336p59 := BSN.log_dyadic_bound 2 3 22 21 Ns336p54 16777216 4840000 Ns336p55 Ns336p56 27001887 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 21 10 9927050056596826020 47940881637414340575 686533194547200 Ns336p57 Ns336p58 84004523356416638976000 Ns336p55 Ns336p54 Ns336p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 10 21 Ns336p57 Ns336p58 84004523356416638976000 rfl rfl rfl rfl)) rfl rfl 

theorem RS337to348.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 4840000 := BSN.isNear_log_sfrac 5 1 27001887 16777216 1 4840000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 27001887 16777216 4840000 rfl rfl rfl (Ns336p59 rfl rfl)) 

theorem RS337to348.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 432030192 268435456 56 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 4840000 432030192 268435456 56 268435456 RS337to348.d22 rfl 

noncomputable abbrev qz327 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns336p60 := @Enclosure.Real.IsNear.inv_image qz327 75029991 33554432 1 33554432 7502998 7503000 16777216 (@Enclosure.Real.IsNear.of_eq qz327 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz323 qz318)) Bool.false 75029991 33554432 1 33554432 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz323 qz318)) Bool.false 75029991 33554432 1 33554432 75029991 33554432 1 33554432 (BSN.sqrt_enclosure 5 1 37514995 37514996 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz328 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS337to348.d24 : Enclosure.Real.IsNear qz328 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz328 Bool.false 15005998 33554432 2 33554432 7502999 16777216 1 16777216 (Ns336p60 rfl rfl) rfl 

theorem RS337to348.d25 : Enclosure.Real.IsNear qz328 Bool.false 120047984 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz328 Bool.false 7502999 16777216 1 16777216 120047984 268435456 16 268435456 RS337to348.d24 rfl 

noncomputable def Ns336p61 := BSN.log_dyadic_bound 2 10 5 4 94500000000 16777216 4840000 1291130880 26880 6802575 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz329 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz622)

theorem RS337to348.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 12500000121 60500000000000000 := BSN.isNear_log_sfrac 6 1 4034683545132279 2251799813685248 12500000121 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz329) Bool.false 1083052117253279893684224 604462909807314587353088 1000000009680000 4840000000000000000000 4034683545132279 2251799813685248 12500000121 60500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 6802575 16777216 24973259072661432 36028797018963968 4840000 1000000000000000 rfl rfl rfl rfl (Ns336p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS337to348.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 480971758 268435456 57 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 12500000121 60500000000000000 480971758 268435456 57 268435456 RS337to348.d26 rfl 

noncomputable abbrev qz330 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns336p62 := @Enclosure.Real.IsNear.inv_image qz330 82191237 33554432 1 33554432 6849269 6849270 16777216 (@Enclosure.Real.IsNear.of_eq qz330 (Real.sqrt qz329) Bool.false 82191237 33554432 1 33554432 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz329) Bool.false 82191237 33554432 1 33554432 82191237 33554432 1 33554432 (BSN.sqrt_enclosure 6 1 41095618 41095619 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz331 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS337to348.d28 : Enclosure.Real.IsNear qz331 Bool.false 13698539 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz331 Bool.false 13698539 33554432 1 33554432 13698539 33554432 1 33554432 (Ns336p62 rfl rfl) rfl 

theorem RS337to348.d29 : Enclosure.Real.IsNear qz331 Bool.false 109588312 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz331 Bool.false 13698539 33554432 1 33554432 109588312 268435456 8 268435456 RS337to348.d28 rfl 

noncomputable def Ns336p63 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 16777216 4840000 11010900719820672 5524329195 9388794 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz332 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz622)

theorem RS337to348.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 12500000121 60500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 12500000121 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz332) Bool.false 1176230476650867868041216 604462909807314587353088 1000000009680000 4840000000000000000000 4381799983422711 2251799813685248 12500000121 60500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 9388794 16777216 24973259072661432 36028797018963968 4840000 1000000000000000 rfl rfl rfl rfl (Ns336p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS337to348.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 522351262 268435456 57 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 12500000121 60500000000000000 522351262 268435456 57 268435456 RS337to348.d30 rfl 

noncomputable abbrev qz333 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns336p64 := @Enclosure.Real.IsNear.inv_image qz333 88776683 33554432 1 33554432 6341191 6341192 16777216 (@Enclosure.Real.IsNear.of_eq qz333 (Real.sqrt qz332) Bool.false 88776683 33554432 1 33554432 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz332) Bool.false 88776683 33554432 1 33554432 88776683 33554432 1 33554432 (BSN.sqrt_enclosure 7 1 44388341 44388342 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz334 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS337to348.d32 : Enclosure.Real.IsNear qz334 Bool.false 12682383 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz334 Bool.false 12682383 33554432 1 33554432 12682383 33554432 1 33554432 (Ns336p64 rfl rfl) rfl 

theorem RS337to348.d33 : Enclosure.Real.IsNear qz334 Bool.false 101459064 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz334 Bool.false 12682383 33554432 1 33554432 101459064 268435456 8 268435456 RS337to348.d32 rfl 

noncomputable def Ns336p65 := nat_lit 1256945285058001618599936 

noncomputable def Ns336p66 := BSN.log_dyadic_bound 0 16 1 0 1 16777216 4840000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz335 := (Enclosure.sfrac Bool.false 8 1)

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz622)

theorem RS337to348.d34 : Enclosure.Real.IsNear (Real.log qz335) Bool.false 9364972152248037 4503599627370496 25000000363 121000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 25000000363 121000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false Ns336p65 604462909807314587353088 1000000014520000 4840000000000000000000 9364972152248037 4503599627370496 25000000363 121000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 16777216 24973259072661432 36028797018963968 4840000 1000000000000000 rfl rfl rfl rfl (Ns336p66 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS337to348.d35 : Enclosure.Real.IsNear (Real.log qz335) Bool.false 558195838 268435456 56 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz335) Bool.false 9364972152248037 4503599627370496 25000000363 121000000000000000 558195838 268435456 56 268435456 RS337to348.d34 rfl 

noncomputable abbrev qz337 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns336p67 := @Enclosure.Real.IsNear.inv_image qz337 94906265 33554432 1 33554432 5931641 5931642 16777216 (@Enclosure.Real.IsNear.of_eq qz337 (Real.sqrt qz336) Bool.false 94906265 33554432 1 33554432 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 94906265 33554432 1 33554432 94906265 33554432 1 33554432 (BSN.sqrt_enclosure 8 1 47453132 47453133 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz338 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS337to348.d36 : Enclosure.Real.IsNear qz338 Bool.false 11863283 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 11863283 33554432 1 33554432 11863283 33554432 1 33554432 (Ns336p67 rfl rfl) rfl 

theorem RS337to348.d37 : Enclosure.Real.IsNear qz338 Bool.false 94906264 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 11863283 33554432 1 33554432 94906264 268435456 8 268435456 RS337to348.d36 rfl 

noncomputable def Ns336p68 := nat_lit 1328140746012062765809664 

noncomputable def Ns336p69 := BSN.log_dyadic_bound 1 17 3 2 1252815 16777216 4840000 1448 3 1976071 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz622)

theorem RS337to348.d38 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 25000000363 121000000000000000 := BSN.isNear_log_sfrac 9 1 9895419672221413 4503599627370496 25000000363 121000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false Ns336p68 604462909807314587353088 1000000014520000 4840000000000000000000 9895419672221413 4503599627370496 25000000363 121000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 1976071 16777216 24973259072661432 36028797018963968 4840000 1000000000000000 rfl rfl rfl rfl (Ns336p69 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS337to348.d39 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 589812974 268435456 56 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 25000000363 121000000000000000 589812974 268435456 56 268435456 RS337to348.d38 rfl 

noncomputable abbrev qz340 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns336p70 := @Enclosure.Real.IsNear.inv_image qz340 100663297 33554432 1 33554432 5592405 5592406 16777216 (@Enclosure.Real.IsNear.of_eq qz340 (Real.sqrt qz339) Bool.false 100663297 33554432 1 33554432 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 100663297 33554432 1 33554432 100663297 33554432 1 33554432 (BSN.sqrt_enclosure 9 1 50331648 50331649 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz341 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS337to348.d40 : Enclosure.Real.IsNear qz341 Bool.false 11184811 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 11184811 33554432 1 33554432 11184811 33554432 1 33554432 (Ns336p70 rfl rfl) rfl 

theorem RS337to348.d41 : Enclosure.Real.IsNear qz341 Bool.false 89478488 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 11184811 33554432 1 33554432 89478488 268435456 8 268435456 RS337to348.d40 rfl 

noncomputable def Ns336p71 := nat_lit 1391827265235416537628672 

noncomputable def Ns336p72 := BSN.log_dyadic_bound 2 18 4 3 3571283520 16777216 4840000 14806464 960 3743727 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 18) 0 3 14806464 3571283520 960 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz821 := (Enclosure.sfrac Bool.false 10 1)

noncomputable abbrev qz624 := qz821

noncomputable abbrev qz342 := qz624

noncomputable abbrev qz1 := qz342

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10) qz622)

theorem RS337to348.d42 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 10369921216632549 4503599627370496 25000000363 121000000000000000 := BSN.isNear_log_sfrac 10 1 10369921216632549 4503599627370496 25000000363 121000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false Ns336p71 604462909807314587353088 1000000014520000 4840000000000000000000 10369921216632549 4503599627370496 25000000363 121000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 3743727 16777216 24973259072661432 36028797018963968 4840000 1000000000000000 rfl rfl rfl rfl (Ns336p72 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS337to348.d43 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 618095470 268435456 56 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 10369921216632549 4503599627370496 25000000363 121000000000000000 618095470 268435456 56 268435456 RS337to348.d42 rfl 

noncomputable abbrev qz344 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10))

noncomputable def Ns336p73 := @Enclosure.Real.IsNear.inv_image qz344 106108431 33554432 1 33554432 5305421 5305422 16777216 (@Enclosure.Real.IsNear.of_eq qz344 (Real.sqrt qz343) Bool.false 106108431 33554432 1 33554432 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz343) Bool.false 106108431 33554432 1 33554432 106108431 33554432 1 33554432 (BSN.sqrt_enclosure 10 1 53054215 53054216 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz345 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

theorem RS337to348.d44 : Enclosure.Real.IsNear qz345 Bool.false 10610843 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz345 Bool.false 10610843 33554432 1 33554432 10610843 33554432 1 33554432 (Ns336p73 rfl rfl) rfl 

theorem RS337to348.d45 : Enclosure.Real.IsNear qz345 Bool.false 84886744 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz345 Bool.false 10610843 33554432 1 33554432 84886744 268435456 8 268435456 RS337to348.d44 rfl 

theorem RS337to348.d46 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz822 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz625 := qz822

noncomputable abbrev qz346 := qz625

noncomputable abbrev qz2 := qz346

noncomputable abbrev qz347 := (Enclosure.Real.IsNear.const Bool.false 2 1)

theorem RS337to348.d47 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 qz347 RS337to348.d46 rfl 

noncomputable abbrev qz3 := (@Inv.inv Real Real.instInv qz346)

theorem RS337to348.d48 : Enclosure.Real.IsNear qz3 Bool.false 5340353 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 5340353 33554432 1 33554432 5340353 33554432 1 33554432 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 2670176 2670177 16777216 RS337to348.d47 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns336p74 := nat_lit 12544489469398178058448404480 

noncomputable abbrev qz823 := (Enclosure.sfrac Bool.false 664401 1000)

noncomputable abbrev qz626 := qz823

noncomputable abbrev qz348 := qz626

noncomputable abbrev qz4 := qz348

noncomputable abbrev qz824 := (@instHMul Real Real.instMul)

noncomputable abbrev qz627 := qz824

noncomputable abbrev qz349 := qz627

noncomputable abbrev qz5 := qz349

noncomputable abbrev qz350 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 10)

noncomputable abbrev qz6 := qz350

noncomputable abbrev qz825 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 664401 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz628 := qz825

noncomputable abbrev qz351 := qz628

noncomputable abbrev qz7 := qz351

noncomputable abbrev qz352 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz8 := qz352

noncomputable abbrev qz826 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 664401 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz629 := qz826

noncomputable abbrev qz353 := qz629

noncomputable abbrev qz9 := qz353

noncomputable abbrev qz630 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz354 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz630 qz7 qz8))

noncomputable def Ns336p75 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HMul.hMul Real Real Real qz5 qz354 (Zeta.RiemannSiegel.correction qz9)) 8169115 16777216 162829 134217728 172859475119189180045 1180591620717411303424 2024151548530609257 103892062623132194701312 Ns336p74 

noncomputable def Ns336p76 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin BSN.quadSignPos 9 10 664401 1000 199 268435456 134217728 4503599627370496 Bool.false 326362832213 2495 618095470 56 84886744 8 

noncomputable def Ns336p77 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 664401 1000 105 155 268435456 134217728 4503599627370496 Bool.false 326362832213 2495 

noncomputable def Ns336p78 := Ns336p77 558195838 56 94906264 8 589812974 56 89478488 8 Bool.true 126344449 122974 Bool.true 229010782 Bool.true 152596144 14148475504056880 1 Bool.false 202224119 Bool.true Bool.false 144509285 Bool.false Bool.true 149671708 

noncomputable def Ns336p79 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 664401 1000 16 49 268435456 134217728 4503599627370496 Bool.false 326362832213 2495 

noncomputable def Ns336p80 := Ns336p79 480971758 57 109588312 8 522351262 57 101459064 8 Bool.true 223309468 91218 Bool.false 58196373 Bool.true 26654626 14148475504056880 1 Bool.false 262151686 Bool.false Bool.false 26610846 Bool.true Bool.true 126344449 

noncomputable def Ns336p81 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 664401 1000 187 93 268435456 134217728 4503599627370496 Bool.false 326362832213 2495 

noncomputable def Ns336p82 := Ns336p81 372130544 56 134217720 8 432030192 56 120047984 16 Bool.true 289639264 53584 Bool.false 268987563 Bool.false 107399789 14148475504056880 1 Bool.false 226178474 Bool.false Bool.false 104557274 Bool.true Bool.true 223309468 

noncomputable def Ns336p83 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 664401 1000 480 309 268435456 134217728 4503599627370496 Bool.false 326362832213 2495 

noncomputable def Ns336p84 := Ns336p83 186065264 56 189812528 16 294906480 56 154981288 8 Bool.true 268435448 2560 Bool.false 345319178 Bool.false 134526660 14148475504056880 1 Bool.false 75313449 Bool.false Bool.false 128965841 Bool.true Bool.true 289639264 

noncomputable def Ns336p85 := nat_lit 117745142728525929033554588106344072136958136398709598203 

noncomputable def Ns336p86 := nat_lit 96846111016311612112350906979562206830039320756224000 

noncomputable def Ns336p87 := nat_lit 62143147721611037259669226560480000 

noncomputable def Ns336p88 := nat_lit 247727882409323146081066557489992834880 

noncomputable abbrev qz10 := (@Eq.refl Real qz348)

noncomputable def Ns336p89 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 664401 1000 1765715755204 16000000 1328802 4000 2000 Ns336p87 Ns336p88 qz10 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns336p90 := nat_lit 339106011058154675616637213746270927754439432828283642824640 

noncomputable abbrev qz827 := (@instHSub Real Real.instSub)

noncomputable abbrev qz631 := qz827

noncomputable abbrev qz355 := qz631

noncomputable abbrev qz11 := qz355

noncomputable abbrev qz356 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz357 := (@HMul.hMul Real Real Real qz627 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz358 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz359 := (Enclosure.sfrac Bool.false 664401 2000)

noncomputable abbrev qz632 := (Real.log (Enclosure.sfrac Bool.false 1765715755204 16000000))

noncomputable abbrev qz633 := (@Nat.cast Real Real.instNatCast 1328802)

noncomputable abbrev qz12 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 664401 4000) qz632) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz633))))) qz359)

noncomputable abbrev qz360 := (@HSub.hSub Real Real Real qz11 qz12 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 664401 2000) (Real.log Real.pi)))

noncomputable def Ns336p91 := @Enclosure.Real.IsNear.addLit_ft_p qz360 (Enclosure.sfrac Bool.true Ns336p87 Ns336p88) 1368865215037888589003 1125899906842624000 4605069557496219189 495616000000000000000000 Ns336p87 Ns336p88 0 1 Ns336p90 

noncomputable def Ns336p92 := nat_lit 91862989550308420166554222592000 

noncomputable abbrev qz361 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 664401 2000) (Real.log Real.pi))

noncomputable def Ns336p93 := @Enclosure.Real.IsNear.subLit_ff_p qz12 qz361 1797022250707324824779 1125899906842624000 525313602835209 121000000000000000000 25520148019161 67108864000 664401 134217728000 Ns336p92 1368865215037888589003 1125899906842624000 

noncomputable def Ns336p94 := nat_lit 3594044501414649649558000 

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 664401 4000) qz632) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz633)))))

noncomputable def Ns336p95 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz359 2171046762710397938891 1125899906842624000 525313602835209 121000000000000000000 664401 2000 0 1 Ns336p94 1797022250707324824779 1125899906842624000 525313602835209 121000000000000000000 

noncomputable def Ns336p96 := nat_lit 4888762695773234904004113994212179968 

noncomputable def Ns336p97 := nat_lit 56149662089235416003641344 

noncomputable def Ns336p98 := nat_lit 4835703278458516698824704 

noncomputable def Ns336p99 := nat_lit 33357789699102171863473463587799244612257915408902585617019511715215934416229812772415183950811531618109838863825678446354569652080834627326965981548380160 

noncomputable def Ns336p100 := nat_lit 751517622169416262423198802753966495429631987847295210583514987733528920274341158628345205393792562842137364941457800182560796536079986091346117370314752 

noncomputable def Ns336p101 := nat_lit 192340206135202318604308592035650237915951752351649548591810454616892849659320570765565166875490398548965227297447130925585310307493229424352952320 

noncomputable def Ns336p102 := BSN.log_dyadic_bound 717139755204 2814291755204 7 6 Ns336p99 134217728 38720000 Ns336p100 Ns336p101 69943956 3531431510408 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 717139755204) (BSN.artanhQ 2814291755204) 0 6 Ns336p100 Ns336p99 Ns336p101 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz362 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns336p103 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 664401 4000) qz632 664401 4000 0 1 3268340491295991 281474976710656 195312621 7562500000000000 2171488690757547716391 1125899906842624000 129765900705021 30250000000000000000 (Enclosure.Real.IsNear.const Bool.false 664401 4000) (BSN.isNear_log_sfrac 1765715755204 16000000 3268340491295991 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1765715755204) qz362)) Bool.false Ns336p97 Ns336p98 1000000619520000 38720000000000000000000 3268340491295991 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1765715755204 16000000 16 3531431510408 2097152000000 69943956 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns336p102 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p104 := BSN.arctan_dyadic_bound_f 1000 1328802 1 0 16777216 4840000 0 1 1 0 1 1 12625 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1328802) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1328802) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz14 := qz357

noncomputable abbrev qz15 := qz358

noncomputable abbrev qz363 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz16 := (@Enclosure.Real.IsNear.mulLit_ff qz363 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz634 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1328802)))

noncomputable def Ns336p105 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz634 884279719003555 562949953421312 1 2000000000000000 12625 16777216 1 4840000 14828644606980002938880 883856094299555 562949953421312 50000000121 242000000000000000 qz16 (Ns336p104 rfl) rfl rfl 

noncomputable abbrev qz17 := qz356

noncomputable abbrev qz364 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns336p106 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 664401 4000) qz632) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz634)) 2171488690757547716391 1125899906842624000 129765900705021 30250000000000000000 883856094299555 2251799813685248 50000000121 968000000000000000 Ns336p96 2171046762710397938891 1125899906842624000 525313602835209 121000000000000000000 (Ns336p103 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz634) 1 4 0 1 883856094299555 562949953421312 50000000121 242000000000000000 883856094299555 2251799813685248 50000000121 968000000000000000 qz364 Ns336p105 rfl) 

noncomputable def Ns336p107 := @Ns336p91 Ns336p85 Ns336p86 4605069557496219189 495616000000000000000000 (@Ns336p93 4605069557496219189 495616000000000000000000 (Ns336p95 (Ns336p106 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 664401 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz359 (Real.log Real.pi) 664401 2000 0 1 38410761 33554432 1 67108864 25520148019161 67108864000 664401 134217728000 (Enclosure.Real.IsNear.const Bool.false 664401 2000) RS337to348.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns336p87 Ns336p88) 

noncomputable abbrev qz365 := (@instHAdd Real Real.instAdd)

noncomputable def Ns336p108 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns336p85 Ns336p86 4605069557496219189 495616000000000000000000 20397677013 16777216 313 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz365 qz360 (Enclosure.sfrac Bool.true Ns336p87 Ns336p88)) Bool.false Ns336p85 Ns336p86 4605069557496219189 495616000000000000000000 Ns336p89 (Ns336p107 rfl rfl)) 

noncomputable def Ns336p109 := nat_lit 3797796918167412089552896 

noncomputable def Ns336p110 := nat_lit 2417851639229258349412352 

noncomputable def Ns336p111 := nat_lit 3510259181358934501326879663441652121628398601434524276326153984818831770575446496107484793062206827510872539609780190283687163820731880561 

noncomputable def Ns336p112 := nat_lit 69061887427279807374175457422696049589758900585025510522285359577850094671315332446731519433112496475662717985575392155893264493730122956800 

noncomputable def Ns336p113 := nat_lit 2501400280758349895030446992478155093984878898058620666875766168224743623793122445938028290492531996764647205765507383863016071451761 

noncomputable def Ns336p114 := nat_lit 17529489823171729649794242996506117596238377646614729075665876186533138110985995836651045243217113725189903321829755108429939285263043089521 

noncomputable def Ns336p115 := nat_lit 2417166059954793258096141009794361735641561520475892868279987585224753313496036635635603180158937376648195129495138725456264257280554303488000 

noncomputable abbrev qz366 := (BSN.sinEvenQ 68719476736)

noncomputable abbrev qz367 := (BSN.sinOddQ 68719476736)

noncomputable def Ns336p116 := BSN.sin_dyadic_bound_f 107939880483 68719476736 4 3 33554432 9689454 Ns336p111 Ns336p112 Ns336p113 Ns336p114 Ns336p115 Ns336p113 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107939880483) qz366 0 3 Ns336p111 Ns336p112 Ns336p113 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107939880483) qz367 0 3 Ns336p114 Ns336p115 Ns336p113 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz368 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable abbrev qz635 := (@Nat.cast Real Real.instNatCast Ns336p110)

noncomputable def Ns336p117 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20397677013) qz368) Bool.false 20397677013 16777216 313 33554432 Bool.true 33554431 33554432 1 4840000 (Ns336p108 rfl) (Enclosure.sfrac_false_div 20397677013 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20397677013) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns336p109) qz635) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 193 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q1 20397677013 16777216 226375608064910080 72057594037927936 193 Ns336p109 Ns336p110 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554431 33554432 Ns336p109 Ns336p110 107939880483 68719476736 9689454 9680000 (Ns336p116 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p118 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns336p85 Ns336p86 4605069557496219189 495616000000000000000000 326362832213 268435456 2495 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz365 qz360 (Enclosure.sfrac Bool.true Ns336p87 Ns336p88)) Bool.false Ns336p85 Ns336p86 4605069557496219189 495616000000000000000000 Ns336p89 (Ns336p107 rfl rfl)) 

noncomputable def Ns336p119 := Ns336p84 53584 BSN.abs_quadSignPos (BSN.cos_quad_nat0 480 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 75313449 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 309 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 128965841 268435456) qz10 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 33554431 33554432 24194913 2537553920000 268435448 268435456 2560 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 33554431 33554432 24194913 2537553920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 33554431 33554432 1548474432 162403450880000 33554431 33554432 24194913 2537553920000 (Ns336p117 rfl rfl) rfl)) rfl) (Ns336p118 rfl) RS337to348.d7 

noncomputable def Ns336p120 := nat_lit 7663639627868915386623966267027818170350698450669288876019104170936552510765227745568972879795059403700637696 

noncomputable def Ns336p121 := nat_lit 67052582193422231333984484018745857420694574238012043916021913709013615522643186318434558042568065189255577600 

noncomputable def Ns336p122 := nat_lit 2875069723889920685007365905054092451237212039976554869053789042774173155025780175642784331869182038016 

noncomputable def Ns336p123 := nat_lit 46442289565716083693946061985969663361332613328830402584516415033536898976853813460906949411137346383741521920 

noncomputable def Ns336p124 := nat_lit 6101784979601423051392588045705873025283206255659095996357994147520239012560529954977544781873693932222257561600 

noncomputable abbrev qz369 := (BSN.cosEvenQ 268435456)

noncomputable abbrev qz370 := (BSN.cosOddQ 268435456)

noncomputable def Ns336p125 := BSN.cos_dyadic_bound_f 345319178 268435456 4 3 268435456 134217728 Ns336p120 Ns336p121 Ns336p122 Ns336p123 Ns336p124 Ns336p122 75313449 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 345319178) qz369 0 3 Ns336p120 Ns336p121 Ns336p122 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 345319178) qz370 0 3 Ns336p123 Ns336p124 Ns336p122 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p126 := nat_lit 5142612475453161353378803527471753085588338365484763395845647933440000 

noncomputable def Ns336p127 := nat_lit 9783225446575624168688766434777683578849446968051522941942878087235502080 

noncomputable def Ns336p128 := nat_lit 107267183618631187654567856446206771441863954426041831449600000000 

noncomputable def Ns336p129 := nat_lit 13468573288841944808354949462087011841768075558438642921392445235200000 

noncomputable def Ns336p130 := nat_lit 179359133187219776425960717970924198945573194414277920602286098265984204800 

noncomputable abbrev qz371 := (BSN.sinEvenQ 268435456)

noncomputable abbrev qz372 := (BSN.sinOddQ 268435456)

noncomputable def Ns336p131 := BSN.sin_dyadic_bound_f 134526660 268435456 3 2 268435456 134217728 Ns336p126 Ns336p127 Ns336p128 Ns336p129 Ns336p130 Ns336p128 128965841 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 134526660) qz371 0 2 Ns336p126 Ns336p127 Ns336p128 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 134526660) qz372 0 2 Ns336p129 Ns336p130 Ns336p128 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p132 := nat_lit 82227082109737794114769008958930744676653243189048260922085491393837665 

noncomputable def Ns336p133 := nat_lit 27406754038263066233817884636394271738548516640677616718793622567521 

noncomputable def Ns336p134 := nat_lit 215312270780870368193349794507788264379848463134851014845060144928275041 

noncomputable def Ns336p135 := BSN.sin_dyadic_bound_f 268987563 268435456 3 2 268435456 134217728 Ns336p132 Ns336p127 Ns336p133 Ns336p134 Ns336p130 Ns336p133 226178474 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 268987563) qz371 0 2 Ns336p132 Ns336p127 Ns336p133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 268987563) qz372 0 2 Ns336p134 Ns336p130 Ns336p133 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p136 := nat_lit 133049642685440174264129224519441 

noncomputable def Ns336p137 := nat_lit 623075623024179315423659559506411520 

noncomputable def Ns336p138 := nat_lit 4361529361169255207965616916544880640 

noncomputable def Ns336p139 := BSN.sin_dyadic_bound_f 107399789 268435456 2 1 268435456 134217728 Ns336p136 Ns336p137 Ns336p136 Ns336p136 Ns336p138 Ns336p136 104557274 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 107399789) qz371 0 1 Ns336p136 Ns336p137 Ns336p136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 107399789) qz372 0 1 Ns336p136 Ns336p138 Ns336p136 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p140 := Ns336p82 91218 BSN.abs_quadSignPos (BSN.cos_quad_nat3 187 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 226178474 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 93 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 104557274 268435456) qz10 rfl rfl (Ns336p119 RS337to348.d9 RS337to348.d11 RS337to348.d13 RS337to348.d17 (Ns336p125 rfl rfl) (Ns336p131 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns336p118 rfl) RS337to348.d19 RS337to348.d21 RS337to348.d23 RS337to348.d25 RS337to348.d17 (Ns336p135 rfl rfl) (Ns336p139 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns336p141 := nat_lit 11470535016011423358426256606641 

noncomputable def Ns336p142 := nat_lit 124615124604835863084731911901282304 

noncomputable def Ns336p143 := nat_lit 1869226869072537946270978678519234560 

noncomputable def Ns336p144 := BSN.cos_dyadic_bound_f 58196373 268435456 2 1 268435456 134217728 Ns336p141 Ns336p142 Ns336p141 Ns336p141 Ns336p143 Ns336p141 262151686 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 58196373) qz369 0 1 Ns336p141 Ns336p142 Ns336p141 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 58196373) qz370 0 1 Ns336p141 Ns336p143 Ns336p141 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p145 := nat_lit 504766323866625007506374415376 

noncomputable def Ns336p146 := BSN.sin_dyadic_bound_f 26654626 268435456 2 1 268435456 134217728 Ns336p145 Ns336p137 Ns336p145 Ns336p145 Ns336p138 Ns336p145 26610846 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 26654626) qz371 0 1 Ns336p145 Ns336p137 Ns336p145 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 26654626) qz372 0 1 Ns336p145 Ns336p138 Ns336p145 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p147 := Ns336p80 122974 BSN.abs_quadSignPos (BSN.cos_quad_nat0 16 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 262151686 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 26610846 268435456) qz10 rfl rfl (Ns336p140 rfl rfl) (Ns336p118 rfl) RS337to348.d27 RS337to348.d29 RS337to348.d31 RS337to348.d33 RS337to348.d17 (Ns336p144 rfl rfl) (Ns336p146 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p148 := nat_lit 43195757342014574199770065303692117342102635564604040384147719077658880 

noncomputable def Ns336p149 := nat_lit 7565670759197016997828470644162775727023690015681480093784695275776 

noncomputable def Ns336p150 := nat_lit 113119496238332803924258448747674519973377435742509002419282660458660096 

noncomputable def Ns336p151 := BSN.sin_dyadic_bound_f 229010782 268435456 3 2 268435456 134217728 Ns336p148 Ns336p127 Ns336p149 Ns336p150 Ns336p130 Ns336p149 202224119 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 229010782) qz371 0 2 Ns336p148 Ns336p127 Ns336p149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 229010782) qz372 0 2 Ns336p150 Ns336p130 Ns336p149 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p152 := nat_lit 8513939036480834100456516532788512667875917980619638496595141459968000 

noncomputable def Ns336p153 := nat_lit 294000775158245611130417299471831476539750983186139637634790588416 

noncomputable def Ns336p154 := nat_lit 22297935760956690246396665481675531164903482733364370884050152258011136 

noncomputable def Ns336p155 := BSN.sin_dyadic_bound_f 152596144 268435456 3 2 268435456 134217728 Ns336p152 Ns336p127 Ns336p153 Ns336p154 Ns336p130 Ns336p153 144509285 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 152596144) qz371 0 2 Ns336p152 Ns336p127 Ns336p153 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 152596144) qz372 0 2 Ns336p154 Ns336p130 Ns336p153 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p156 := Ns336p78 150264 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 105 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 202224119 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 155 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 144509285 268435456) qz10 rfl rfl (Ns336p147 rfl) (Ns336p118 rfl) RS337to348.d35 RS337to348.d37 RS337to348.d39 RS337to348.d41 RS337to348.d17 (Ns336p151 rfl rfl) (Ns336p155 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p157 := nat_lit 32608948414917122124706709634157414929281536076207793921439789874633986496334696499339226412973224338619140625 

noncomputable def Ns336p158 := nat_lit 871683568514489007341798292243696146469029465094156570908284878217177001794361422139649254553384847460322508800 

noncomputable def Ns336p159 := nat_lit 12607406491083219947348093001670464858272781830462091837720113767147721327445749273047506809234619140625 

noncomputable def Ns336p160 := nat_lit 162895510638248451640291365436702718911844402134319207867001082223519877279251339830874960924438884754619140625 

noncomputable def Ns336p161 := nat_lit 30508924898007115256962940228529365126416031278295479981789970737601195062802649774887723909368469661111287808000 

noncomputable def Ns336p162 := BSN.sin_dyadic_bound_f 390587925 268435456 4 3 268435456 134217728 Ns336p157 Ns336p158 Ns336p159 Ns336p160 Ns336p161 Ns336p159 266639424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 390587925) qz371 0 3 Ns336p157 Ns336p158 Ns336p159 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 390587925) qz372 0 3 Ns336p160 Ns336p161 Ns336p159 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz373 := (BSN.cos_quad_nat3 199 rfl)

noncomputable def Ns336p163 := Ns336p76 Bool.true 149671708 150264 Bool.true 390587925 14148475504056880 1 Bool.false 266639424 Bool.false Bool.true 65352920 162829 BSN.abs_quadSignPos qz373 (BSN.sfrac_eq_quadSignPos_mul Bool.false 266639424 268435456) qz10 rfl (Ns336p156 rfl) (Ns336p118 rfl) RS337to348.d43 RS337to348.d45 RS337to348.d17 (Ns336p162 rfl rfl) rfl 

noncomputable def Ns336p164 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) 65352920 268435456 162829 268435456 65352920 268435456 162829 268435456 35086081762263040 8169115 16777216 162829 134217728 (Ns336p163 rfl rfl rfl rfl) 

noncomputable def Ns336p165 := @Enclosure.Real.IsNear.mulLit_ff qz354 (Zeta.RiemannSiegel.correction qz9) 10463749 33554432 1 33554432 16519841513705 35184372088832 2657947178025497 42573090227486720000 172859475119189180045 1180591620717411303424 

noncomputable abbrev qz374 := (@HPow.hPow Real Real Real qz630 qz7 qz8)

noncomputable def Ns336p166 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz374 1 1 0 1 10463749 33554432 1 33554432 10463749 33554432 1 33554432 

noncomputable abbrev qz375 := (@Enclosure.Real.IsNear.of_eq qz7 (@HMul.hMul Real Real Real qz5 qz4 qz3) Bool.false 3548135873553 33554432000 664401 33554432000 (BSN.t_div_two_pi_mk qz4 664401 1000 qz10) (@Enclosure.Real.IsNear.mulLit_ff qz4 qz3 664401 1000 0 1 5340353 33554432 1 33554432 3548135873553 33554432000 664401 33554432000 (Enclosure.Real.IsNear.const Bool.false 664401 1000) RS337to348.d48 rfl))

noncomputable def Ns336p167 := @Enclosure.Real.IsNear.sqrt_image qz7 3548135873553 33554432000 664401 33554432000 172522217 172522250 16777216 qz375 

noncomputable abbrev qz828 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 664401 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz636 := qz828

noncomputable abbrev qz376 := qz636

noncomputable abbrev qz18 := qz376

noncomputable def Ns336p168 := @Enclosure.Real.IsNear.sqrt_image qz18 345044467 33554432 33 33554432 53800023 53800029 16777216 (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 345044467 33554432 33 33554432 345044467 33554432 33 33554432 (Ns336p167 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz829 := (Real.sqrt (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 664401 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))))

noncomputable abbrev qz637 := qz829

noncomputable abbrev qz377 := qz637

noncomputable abbrev qz19 := qz377

noncomputable def Ns336p169 := @Enclosure.Real.IsNear.inv_image qz19 26900013 8388608 3 16777216 5231874 5231875 16777216 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 107600052 33554432 6 33554432 26900013 8388608 3 16777216 (Ns336p168 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns336p170 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz19) Bool.false 10463749 33554432 1 33554432 10463749 33554432 1 33554432 (Ns336p169 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz20 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz353))

noncomputable abbrev qz638 := (@HMul.hMul Real Real Real qz824 qz826 qz826)

noncomputable abbrev qz639 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz378 := (@HSub.hSub Real Real Real qz631 (@HSub.hSub Real Real Real qz631 qz638 qz629) qz639)

noncomputable abbrev qz21 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz378))

noncomputable def Ns336p171 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz9) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz20) qz21) Bool.false 16519841513705 

noncomputable def Ns336p172 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz20) qz21 162381103 33554432 5035 

noncomputable abbrev qz640 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz20))

noncomputable def Ns336p173 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz20) (@Neg.neg Real Real.instNeg qz640) Bool.true 162381103 33554432 5035 33554432 (BSN.inv_eq_neg_inv_neg qz20) 

noncomputable def Ns336p174 := @Enclosure.Real.IsNear.recentre' qz640 Bool.false 162381103 33554432 5035 33554432 162381103 33554432 

noncomputable def Ns336p175 := @Enclosure.Real.IsNear.recentre' qz20 Bool.true 3466844 16777216 65017152 10150215680000 866711 4194304 1015893 158597120000 

noncomputable abbrev qz22 := (@HMul.hMul Real Real Real qz349 qz346 qz353)

noncomputable def Ns336p176 := @Enclosure.Real.IsNear.cos_image qz22 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3730699) (@Nat.cast Real Real.instNatCast 2097152)) Bool.false 3730699 2097152 13 2097152 Bool.true 3466844 16777216 1 

noncomputable def Ns336p177 := nat_lit 178108097716011828272992187 

noncomputable def Ns336p178 := nat_lit 28823037615171174400000000000000 

noncomputable def Ns336p179 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz9 884279719003555 140737488355328 1 500000000000000 9500147 33554432 33 33554432 8400787319652466022585 4722366482869645213696 Ns336p177 

noncomputable def Ns336p180 := @Enclosure.Real.IsNear.subLit_ff_p qz18 qz1 345044467 33554432 33 33554432 10 1 0 1 9500147 9500147 33554432 33 

noncomputable abbrev qz379 := (Enclosure.Real.IsNear.const Bool.false 10 1)

noncomputable def Ns336p181 := @Ns336p180 33554432 (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 345044467 33554432 33 33554432 345044467 33554432 33 33554432 (Ns336p167 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns336p182 := @Enclosure.Real.IsNear.recentre' qz22 Bool.false 8400787319652466022585 4722366482869645213696 Ns336p177 Ns336p178 3730699 2097152 13 2097152 (@Ns336p179 Ns336p178 RS337to348.d47 (Ns336p181 rfl rfl) rfl) 

noncomputable def Ns336p183 := nat_lit 1455154900336850856541160771158107870326392534614104973638104067728035088182506728081 

noncomputable def Ns336p184 := nat_lit 3466537250751077332112698720796095110148055492926080949987665366995300109908547993600 

noncomputable def Ns336p185 := nat_lit 7269131557606467561616739673612447350597346543519255666266107179178048079571601 

noncomputable def Ns336p186 := nat_lit 8793027704091273653636181576219302402148727009287758600078335068499276000463033510545 

noncomputable def Ns336p187 := nat_lit 315454889818348037222255583592444655023473049856273366448877548396572310001677867417600 

noncomputable def Ns336p188 := BSN.cos_dyadic_bound_t 3730699 2097152 4 3 16777216 4840000 Ns336p183 Ns336p184 Ns336p185 Ns336p186 Ns336p187 Ns336p185 3466844 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3730699) (BSN.cosEvenQ 2097152) 0 3 Ns336p183 Ns336p184 Ns336p185 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3730699) (BSN.cosOddQ 2097152) 0 3 Ns336p186 Ns336p187 Ns336p185 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p189 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz20) 866711 4194304 1015893 158597120000 81188034 81193069 16777216 (@Enclosure.Real.IsNear.neg qz20 Bool.true 866711 4194304 1015893 158597120000 (Ns336p175 (@Ns336p176 4840000 (Ns336p182 rfl) (Enclosure.sfrac_false_div 3730699 2097152) (Ns336p188 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns336p190 := Ns336p173 (@Enclosure.Real.IsNear.neg qz640 Bool.false 162381103 33554432 5035 33554432 (@Ns336p174 5035 33554432 (Ns336p189 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p191 := @Enclosure.Real.IsNear.recentre' qz21 Bool.true 1627760 16777216 

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz349 qz346 qz378)

noncomputable def Ns336p192 := @Enclosure.Real.IsNear.cos_image qz23 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 27983913)) qz368) Bool.true 27983913 16777216 

noncomputable def Ns336p193 := nat_lit 264300585739364287542043622245 

noncomputable def Ns336p194 := nat_lit 158456325028528675187087900672 

noncomputable def Ns336p195 := nat_lit 46802140755345923830600797148191377 

noncomputable def Ns336p196 := @Enclosure.Real.IsNear.recentre' qz23 Bool.true Ns336p193 Ns336p194 Ns336p195 

noncomputable def Ns336p197 := nat_lit 4835703278458516698824704000000000000000 

noncomputable abbrev qz24 := qz378

noncomputable def Ns336p198 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz24 884279719003555 140737488355328 1 500000000000000 298887987657559 

noncomputable abbrev qz380 := (@HSub.hSub Real Real Real qz631 qz638 qz629)

noncomputable abbrev qz25 := qz380

noncomputable abbrev qz381 := qz639

noncomputable abbrev qz26 := qz381

noncomputable def Ns336p199 := @Enclosure.Real.IsNear.subLit_tf qz25 qz26 228519243479895 1125899906842624 1734307047 1125899906842624 1 16 

noncomputable abbrev qz382 := qz638

noncomputable abbrev qz27 := qz382

noncomputable def Ns336p200 := @Enclosure.Real.IsNear.subLit_ff_n qz27 qz9 90252793021609 1125899906842624 627010791 1125899906842624 9500147 33554432 33 33554432 

noncomputable def Ns336p201 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz9 9500147 33554432 33 33554432 9500147 33554432 33 33554432 90252793021609 1125899906842624 

noncomputable def Ns336p202 := nat_lit 77182044344947354627746444972643088442549896212001385175569453495327600778785298210425433777761 

noncomputable def Ns336p203 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600 

noncomputable def Ns336p204 := nat_lit 230622302284198595832148022605080731272141139537273374569564190726399233196042126462314081 

noncomputable def Ns336p205 := nat_lit 466804964752366480013648685311692520404324698252219304420163382205412904487695115804397850879585 

noncomputable def Ns336p206 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600 

noncomputable def Ns336p207 := BSN.cos_dyadic_bound_t 27983913 16777216 4 3 16777216 4840000 Ns336p202 Ns336p203 Ns336p204 Ns336p205 Ns336p206 Ns336p204 1627760 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 27983913) (BSN.cosEvenQ 16777216) 0 3 Ns336p202 Ns336p203 Ns336p204 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 27983913) (BSN.cosOddQ 16777216) 0 3 Ns336p205 Ns336p206 Ns336p204 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz383 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns336p208 := @Ns336p191 1606554432 162403450880000 101735 1048576 25102413 2537553920000 (@Ns336p192 325 33554432 Bool.true 1627760 16777216 1 4840000 (@Ns336p196 Ns336p197 27983913 16777216 325 33554432 (@Ns336p198 1125899906842624 1734307047 1125899906842624 Ns336p193 Ns336p194 Ns336p195 Ns336p197 RS337to348.d47 (@Ns336p199 0 1 4782207802520944 298887987657559 1125899906842624 1734307047 1125899906842624 (@Ns336p200 7667833416037580144640 228519243479895 1125899906842624 1734307047 1125899906842624 (@Ns336p201 627010791 1125899906842624 (Ns336p181 rfl rfl) (Ns336p181 rfl rfl) rfl) (Ns336p181 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 27983913 16777216) (BSN.cos_neg_of_bound 27983913 16777216 Bool.true 1627760 16777216 1 4840000 (Ns336p207 rfl rfl)) rfl rfl) 

noncomputable abbrev qz830 := (Enclosure.sfrac Bool.false 1 1)

noncomputable abbrev qz641 := qz830

noncomputable abbrev qz384 := qz641

noncomputable abbrev qz642 := (Enclosure.Real.IsNear.const Bool.false 1 1)

noncomputable abbrev qz28 := (@Enclosure.Real.IsNear.of_eq qz350 qz384 Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 10 rfl) qz642)

noncomputable def Ns336p209 := @Ns336p165 2024151548530609257 103892062623132194701312 (Ns336p166 qz28 (@Enclosure.Real.IsNear.of_eq qz374 (@Inv.inv Real Real.instInv qz19) Bool.false 10463749 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz7 (BSN.t_div_two_pi_nonneg qz4 664401 1000 qz10)) Ns336p170) rfl) (@Ns336p171 35184372088832 2657947178025497 42573090227486720000 (BSN.correction_mk qz9 (BSN.cos_two_pi_p_ne_zero_mk qz4 664401 1000 10 qz10 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 664401 1000 10 qz10 rfl rfl rfl))) (@Ns336p172 33554432 101735 1048576 25102413 2537553920000 16519841513705 35184372088832 2657947178025497 42573090227486720000 Ns336p190 (Ns336p208 rfl) rfl)) 

noncomputable def Ns336p210 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 747709838712106827405 1180591620717411303424 128062946251283975273 103892062623132194701312 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HMul.hMul Real Real Real qz5 qz354 (Zeta.RiemannSiegel.correction qz9))) Bool.true 747709838712106827405 1180591620717411303424 128062946251283975273 103892062623132194701312 (BSN.hardyZApproximantRS₀_eq qz4 10 (@BSN.floor_sqrt_eq_dec qz4 664401 1000 10 qz10 rfl rfl rfl)) (@Ns336p75 747709838712106827405 1180591620717411303424 128062946251283975273 103892062623132194701312 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10)) Bool.true 8169115 16777216 162829 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (Ns336p164 (Ns336p163 rfl rfl rfl rfl) rfl rfl)) (Ns336p209 rfl) rfl rfl)) 

theorem RS337to348.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 747709838712106827405 1180591620717411303424 128062946251283975273 103892062623132194701312 := Ns336p210 

theorem RS337to348.d50 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS337to348.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS337to348.d3 a b h)) 

noncomputable def Ns336p211 := nat_lit 7142579305340338385715200 

noncomputable def Ns336p212 := nat_lit 7648967524928255016826830848 

noncomputable abbrev qz831 := (Enclosure.sfrac Bool.false 665749 1000)

noncomputable abbrev qz643 := qz831

noncomputable abbrev qz385 := qz643

noncomputable abbrev qz29 := qz385

noncomputable abbrev qz832 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 665749 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz644 := qz832

noncomputable abbrev qz386 := qz644

noncomputable abbrev qz30 := qz386

noncomputable abbrev qz833 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 665749 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz645 := qz833

noncomputable abbrev qz387 := qz645

noncomputable abbrev qz31 := qz387

noncomputable abbrev qz388 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz630 qz30 qz8))

noncomputable def Ns336p213 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz29) qz29 10) (@HMul.hMul Real Real Real qz5 qz388 (Zeta.RiemannSiegel.correction qz31)) 30736985 33554432 81579 67108864 42408383171288225091 295147905179352825856 107358541077903716067 Ns336p211 Ns336p212 

noncomputable def Ns336p214 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz29) qz29 Real.sin BSN.quadSignPos 9 10 665749 1000 199 268435456 134217728 4503599627370496 Bool.false 327206310835 2501 618095470 56 84886744 8 

noncomputable def Ns336p215 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz29) qz29 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 665749 1000 105 155 268435456 134217728 4503599627370496 Bool.false 327206310835 2501 

noncomputable def Ns336p216 := Ns336p215 558195838 56 94906264 8 589812974 56 89478488 8 Bool.false 51866834 123221 Bool.true 137980149 Bool.true 104185411 14148475504056880 1 Bool.false 131983899 Bool.true Bool.false 101589330 Bool.false Bool.false 39066590 

noncomputable def Ns336p217 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz29) qz29 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 665749 1000 16 48 268435456 134217728 4503599627370496 Bool.false 327206310835 2501 

noncomputable def Ns336p218 := Ns336p217 480971758 57 109588312 8 522351262 57 101459064 8 Bool.true 53792608 91400 Bool.false 253325065 Bool.true 308962933 14148475504056880 1 Bool.false 157514814 Bool.false Bool.false 109413171 Bool.false Bool.false 51866834 

noncomputable def Ns336p219 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz29) qz29 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 665749 1000 188 93 268435456 134217728 4503599627370496 Bool.false 327206310835 2501 

noncomputable def Ns336p220 := Ns336p219 372130544 56 134217720 8 432030192 56 120047984 16 Bool.true 38335122 53689 Bool.false 189176783 Bool.false 368501712 14148475504056880 1 Bool.false 204489037 Bool.false Bool.false 263189671 Bool.true Bool.true 53792608 

noncomputable def Ns336p221 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz29) qz29 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 665749 1000 482 310 268435456 134217728 4503599627370496 Bool.false 327206310835 2501 

noncomputable def Ns336p222 := Ns336p221 186065264 56 189812528 16 294906480 56 154981288 8 Bool.false 268435416 2560 Bool.false 94666967 Bool.false 158813918 14148475504056880 1 Bool.false 251915029 Bool.true Bool.false 222810515 Bool.true Bool.true 38335122 

noncomputable def Ns336p223 := nat_lit 1075444386202070921208791799182320977802783283207979292423 

noncomputable def Ns336p224 := nat_lit 882279450770274122697780289707147131556425279471616000 

noncomputable def Ns336p225 := nat_lit 62776120293613039205094593799520000 

noncomputable def Ns336p226 := nat_lit 250758901862091682544866071596955842880 

noncomputable abbrev qz389 := (@Eq.refl Real qz643)

noncomputable abbrev qz32 := qz389

noncomputable def Ns336p227 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz29 665749 1000 1772887924004 16000000 1331498 4000 2000 Ns336p225 Ns336p226 qz32 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns336p228 := nat_lit 344142203584662694786813375738342712896890650626553373575360 

noncomputable abbrev qz390 := (Enclosure.sfrac Bool.false 665749 2000)

noncomputable abbrev qz646 := (Real.log (Enclosure.sfrac Bool.false 1772887924004 16000000))

noncomputable abbrev qz647 := (@Nat.cast Real Real.instNatCast 1331498)

noncomputable abbrev qz33 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 665749 4000) qz646) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz647))))) qz390)

noncomputable abbrev qz391 := (@HSub.hSub Real Real Real qz11 qz33 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 665749 2000) (Real.log Real.pi)))

noncomputable def Ns336p229 := @Enclosure.Real.IsNear.addLit_ft_p qz391 (Enclosure.sfrac Bool.true Ns336p225 Ns336p226) 1372403020226801267047 1125899906842624000 4614360821301393161 495616000000000000000000 Ns336p225 Ns336p226 0 1 Ns336p228 

noncomputable def Ns336p230 := nat_lit 92100407637589655385284804608000 

noncomputable abbrev qz392 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 665749 2000) (Real.log Real.pi))

noncomputable def Ns336p231 := @Enclosure.Real.IsNear.subLit_ff_p qz33 qz392 1801428741650898317671 1125899906842624000 526366728487641 121000000000000000000 25571925724989 67108864000 665749 134217728000 Ns336p230 1372403020226801267047 1125899906842624000 

noncomputable def Ns336p232 := nat_lit 3602857483301796635342000 

noncomputable abbrev qz34 := (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 665749 4000) qz646) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz647)))))

noncomputable def Ns336p233 := @Enclosure.Real.IsNear.subLit_ff_p qz34 qz390 2176212110191183360359 1125899906842624000 526366728487641 121000000000000000000 665749 2000 0 1 Ns336p232 1801428741650898317671 1125899906842624000 526366728487641 121000000000000000000 

noncomputable def Ns336p234 := nat_lit 4900394024268087081189395828186284032 

noncomputable def Ns336p235 := nat_lit 56169264456973508824530944 

noncomputable def Ns336p236 := nat_lit 34392351092313506820401062387514585177270411714954723776332357619445975911631043157497214668371715547858640040637119576611016291682188781061836302880604160 

noncomputable def Ns336p237 := nat_lit 786871297261060331066545688705723303524874885577648074200812880578056223486256113353750819978692107373435478362212570735087321517570088173651266530967552 

noncomputable def Ns336p238 := nat_lit 216736527932567609869778536567997715753420996512411837782848658958819047567538756830742089660860762279618560286292481639371451503097066769686200320 

noncomputable def Ns336p239 := BSN.log_dyadic_bound 724311924004 2821463924004 7 6 Ns336p236 134217728 38720000 Ns336p237 Ns336p238 70488031 3545775848008 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 724311924004) (BSN.artanhQ 2821463924004) 0 6 Ns336p237 Ns336p236 Ns336p238 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns336p240 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 665749 4000) qz646 665749 4000 0 1 3269481499270391 281474976710656 195312621 7562500000000000 2176654038657763537859 1125899906842624000 130029182118129 30250000000000000000 (Enclosure.Real.IsNear.const Bool.false 665749 4000) (BSN.isNear_log_sfrac 1772887924004 16000000 3269481499270391 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1772887924004) qz362)) Bool.false Ns336p235 Ns336p98 1000000619520000 38720000000000000000000 3269481499270391 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1772887924004 16000000 16 3545775848008 2097152000000 70488031 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns336p239 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p241 := BSN.arctan_dyadic_bound_f 1000 1331498 1 0 16777216 4840000 0 1 1 0 1 1 12600 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1331498) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1331498) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz648 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1331498)))

noncomputable def Ns336p242 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz648 884279719003555 562949953421312 1 2000000000000000 12600 16777216 1 4840000 14828658680728838471680 883856933160355 562949953421312 50000000121 242000000000000000 qz16 (Ns336p241 rfl) rfl rfl 

noncomputable def Ns336p243 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 665749 4000) qz646) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz648)) 2176654038657763537859 1125899906842624000 130029182118129 30250000000000000000 883856933160355 2251799813685248 50000000121 968000000000000000 Ns336p234 2176212110191183360359 1125899906842624000 526366728487641 121000000000000000000 (Ns336p240 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz648) 1 4 0 1 883856933160355 562949953421312 50000000121 242000000000000000 883856933160355 2251799813685248 50000000121 968000000000000000 qz364 Ns336p242 rfl) 

noncomputable def Ns336p244 := @Ns336p229 Ns336p223 Ns336p224 4614360821301393161 495616000000000000000000 (@Ns336p231 4614360821301393161 495616000000000000000000 (Ns336p233 (Ns336p243 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 665749 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz390 (Real.log Real.pi) 665749 2000 0 1 38410761 33554432 1 67108864 25571925724989 67108864000 665749 134217728000 (Enclosure.Real.IsNear.const Bool.false 665749 2000) RS337to348.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns336p225 Ns336p226) 

noncomputable def Ns336p245 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz29) Bool.false Ns336p223 Ns336p224 4614360821301393161 495616000000000000000000 20450394427 16777216 313 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz29) (@HAdd.hAdd Real Real Real qz365 qz391 (Enclosure.sfrac Bool.true Ns336p225 Ns336p226)) Bool.false Ns336p223 Ns336p224 4614360821301393161 495616000000000000000000 Ns336p227 (Ns336p244 rfl rfl)) 

noncomputable def Ns336p246 := BSN.cos_dyadic_bound_f 37503319 68719476736 1 0 33554432 9689454 0 1 1 0 1 1 33554427 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 37503319) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 37503319) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns336p247 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz29) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20450394427) qz368) Bool.false 20450394427 16777216 313 33554432 Bool.false 33554427 33554432 1 4840000 (Ns336p245 rfl) (Enclosure.sfrac_false_div 20450394427 16777216) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20450394427) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1319530741154199896064) qz635) 226375608064910080 72057594037927936 Bool.false 33554427 33554432 194 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q0 20450394427 16777216 226375608064910080 72057594037927936 194 1319530741154199896064 Ns336p110 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554427 33554432 1319530741154199896064 Ns336p110 37503319 68719476736 9689454 9680000 (Ns336p246 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p248 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz29) Bool.false Ns336p223 Ns336p224 4614360821301393161 495616000000000000000000 327206310835 268435456 2501 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz29) (@HAdd.hAdd Real Real Real qz365 qz391 (Enclosure.sfrac Bool.true Ns336p225 Ns336p226)) Bool.false Ns336p223 Ns336p224 4614360821301393161 495616000000000000000000 Ns336p227 (Ns336p244 rfl rfl)) 

noncomputable def Ns336p249 := Ns336p222 53689 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 482 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 251915029 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 310 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 222810515 268435456) qz32 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 1) Bool.false 33554427 33554432 24194913 2537553920000 268435416 268435456 2560 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz29)) Bool.false 33554427 33554432 24194913 2537553920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz29) qz29) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz29)) Bool.false 33554427 33554432 1548474432 162403450880000 33554427 33554432 24194913 2537553920000 (Ns336p247 rfl rfl) rfl)) rfl) (Ns336p248 rfl) RS337to348.d7 

noncomputable def Ns336p250 := nat_lit 700594376863449676768637278086594571728256921848478660824162581805121 

noncomputable def Ns336p251 := nat_lit 1087025049619513796520974048308631508761049663116835882438097565248389120 

noncomputable def Ns336p252 := nat_lit 6450415718914029261935580073048600705650070121063116136327346241 

noncomputable def Ns336p253 := nat_lit 2101770229758911202247387963099637617983359465405193856240215090722881 

noncomputable def Ns336p254 := nat_lit 48916127232878120843443832173888417894247234840257614709714390436177510400 

noncomputable def Ns336p255 := BSN.cos_dyadic_bound_f 94666967 268435456 3 2 268435456 134217728 Ns336p250 Ns336p251 Ns336p252 Ns336p253 Ns336p254 Ns336p252 251915029 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 94666967) qz369 0 2 Ns336p250 Ns336p251 Ns336p252 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 94666967) qz370 0 2 Ns336p253 Ns336p254 Ns336p252 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p256 := nat_lit 5549510876239622848123802340589130559846604949382311168908908908544256 

noncomputable def Ns336p257 := nat_lit 404676961763565469599917680673842640569591132883039217620145438976 

noncomputable def Ns336p258 := nat_lit 16647723274795341413432207186406043994258675665881167428291486434754816 

noncomputable def Ns336p259 := BSN.cos_dyadic_bound_f 158813918 268435456 3 2 268435456 134217728 Ns336p256 Ns336p251 Ns336p257 Ns336p258 Ns336p254 Ns336p257 222810515 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 158813918) qz369 0 2 Ns336p256 Ns336p251 Ns336p257 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 158813918) qz370 0 2 Ns336p258 Ns336p254 Ns336p257 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p260 := nat_lit 11173877367239269888023263221769648513106263085374317822160770370805121 

noncomputable def Ns336p261 := nat_lit 1640373282931590168413223334091187376247609046249117142520756346241 

noncomputable def Ns336p262 := nat_lit 33518351355151946483732963218640763164566294038030455232197269599722881 

noncomputable def Ns336p263 := BSN.cos_dyadic_bound_f 189176783 268435456 3 2 268435456 134217728 Ns336p260 Ns336p251 Ns336p261 Ns336p262 Ns336p254 Ns336p261 204489037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 189176783) qz369 0 2 Ns336p260 Ns336p251 Ns336p261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 189176783) qz370 0 2 Ns336p262 Ns336p254 Ns336p261 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p264 := nat_lit 25827714731388849605452103046057286653634829373402375238647498602489612451274391307726911918647367183269625856 

noncomputable def Ns336p265 := nat_lit 6270094961726314836211102687087475014067120646533327462334767975683403321364756603485964816569604243456 

noncomputable def Ns336p266 := nat_lit 129044904759333286733371470099677670795032040452934021414032203416529662989834660356586615733761022891776802816 

noncomputable def Ns336p267 := BSN.sin_dyadic_bound_f 368501712 268435456 4 3 268435456 134217728 Ns336p264 Ns336p158 Ns336p265 Ns336p266 Ns336p161 Ns336p265 263189671 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 368501712) qz371 0 3 Ns336p264 Ns336p158 Ns336p265 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 368501712) qz372 0 3 Ns336p266 Ns336p161 Ns336p265 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p268 := Ns336p220 91400 BSN.abs_quadSignPos (BSN.cos_quad_nat0 188 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 204489037 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 93 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 263189671 268435456) qz32 rfl rfl (Ns336p249 RS337to348.d9 RS337to348.d11 RS337to348.d13 RS337to348.d17 (Ns336p255 rfl rfl) (Ns336p259 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns336p248 rfl) RS337to348.d19 RS337to348.d21 RS337to348.d23 RS337to348.d25 RS337to348.d17 (Ns336p263 rfl rfl) (Ns336p267 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns336p269 := nat_lit 35940691924040922507238323726888592216568292303220674234820358886690625 

noncomputable def Ns336p270 := nat_lit 16959978683282960885340720452497118424901782305478636885222937890625 

noncomputable def Ns336p271 := nat_lit 107788155814756201599944289739760782412855073345051065430690630784290625 

noncomputable def Ns336p272 := BSN.cos_dyadic_bound_f 253325065 268435456 3 2 268435456 134217728 Ns336p269 Ns336p251 Ns336p270 Ns336p271 Ns336p254 Ns336p270 157514814 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 253325065) qz369 0 2 Ns336p269 Ns336p251 Ns336p270 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 253325065) qz370 0 2 Ns336p271 Ns336p254 Ns336p270 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p273 := nat_lit 4908217156919512892979118514029581794291871769479732445979127372615664593983948022216156777657753381577706641 

noncomputable def Ns336p274 := nat_lit 756617794111758917443173372149331504049114045204978715364883280739600496872612433906715945027623996561 

noncomputable def Ns336p275 := nat_lit 29755798540972536212805709998975316198364430803867571075169628650609846842355763869879425082571632076904483985 

noncomputable def Ns336p276 := BSN.cos_dyadic_bound_f 308962933 268435456 4 3 268435456 134217728 Ns336p273 Ns336p121 Ns336p274 Ns336p275 Ns336p124 Ns336p274 109413171 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 308962933) qz369 0 3 Ns336p273 Ns336p121 Ns336p274 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 308962933) qz370 0 3 Ns336p275 Ns336p124 Ns336p274 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p277 := Ns336p218 123221 BSN.abs_quadSignPos (BSN.cos_quad_nat0 16 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 157514814 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 48 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 109413171 268435456) qz32 rfl rfl (Ns336p268 rfl rfl) (Ns336p248 rfl) RS337to348.d27 RS337to348.d29 RS337to348.d31 RS337to348.d33 RS337to348.d17 (Ns336p272 rfl rfl) (Ns336p276 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p278 := nat_lit 5691382380196703903595210217575469190352718973783864422948831056036705 

noncomputable def Ns336p279 := nat_lit 131381094859424553045061985510979164810658974028154490097477288801 

noncomputable def Ns336p280 := nat_lit 14905788759694928298234906183768734865609332435856932667120113993057121 

noncomputable def Ns336p281 := BSN.sin_dyadic_bound_f 137980149 268435456 3 2 268435456 134217728 Ns336p278 Ns336p127 Ns336p279 Ns336p280 Ns336p130 Ns336p279 131983899 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 137980149) qz371 0 2 Ns336p278 Ns336p127 Ns336p279 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 137980149) qz372 0 2 Ns336p280 Ns336p130 Ns336p279 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p282 := nat_lit 117822338234444801933748413244241 

noncomputable def Ns336p283 := BSN.sin_dyadic_bound_f 104185411 268435456 2 1 268435456 134217728 Ns336p282 Ns336p137 Ns336p282 Ns336p282 Ns336p138 Ns336p282 101589330 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 104185411) qz371 0 1 Ns336p282 Ns336p137 Ns336p282 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 104185411) qz372 0 1 Ns336p282 Ns336p138 Ns336p282 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p284 := Ns336p216 150567 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 105 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 131983899 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 155 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 101589330 268435456) qz32 rfl rfl (Ns336p277 rfl) (Ns336p248 rfl) RS337to348.d35 RS337to348.d37 RS337to348.d39 RS337to348.d41 RS337to348.d17 (Ns336p281 rfl rfl) (Ns336p283 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p285 := nat_lit 29302916358440051616730073941383312461205868476401407599990365256361491007597073888364230199756493520819765041 

noncomputable def Ns336p286 := nat_lit 9152574470735490870510697189961663820513599566938688297112334599954417300196550389605694924497435803441 

noncomputable def Ns336p287 := nat_lit 146394043841659455184455393515529267415258133023314116672286732712892825850879076802287916221168414030128529201 

noncomputable def Ns336p288 := BSN.sin_dyadic_bound_f 380301997 268435456 4 3 268435456 134217728 Ns336p285 Ns336p158 Ns336p286 Ns336p287 Ns336p161 Ns336p286 265256122 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 380301997) qz371 0 3 Ns336p285 Ns336p158 Ns336p286 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 380301997) qz372 0 3 Ns336p287 Ns336p161 Ns336p286 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p289 := Ns336p214 Bool.false 39066590 150567 Bool.true 380301997 14148475504056880 1 Bool.false 265256122 Bool.false Bool.false 122947940 163158 BSN.abs_quadSignPos qz373 (BSN.sfrac_eq_quadSignPos_mul Bool.false 265256122 268435456) qz32 rfl (Ns336p284 rfl) (Ns336p248 rfl) RS337to348.d43 RS337to348.d45 RS337to348.d17 (Ns336p288 rfl rfl) rfl 

noncomputable def Ns336p290 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 10) 122947940 268435456 163158 268435456 122947940 268435456 163158 268435456 66007172676321280 30736985 33554432 81579 67108864 (Ns336p289 rfl rfl rfl rfl) 

noncomputable def Ns336p291 := @Enclosure.Real.IsNear.mulLit_ff qz388 (Zeta.RiemannSiegel.correction qz31) 653653 2097152 1 16777216 64879046177847 140737488355328 128080979929167 2660818139217920000 42408383171288225091 295147905179352825856 

noncomputable abbrev qz393 := (@HPow.hPow Real Real Real qz630 qz30 qz8)

noncomputable def Ns336p292 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz393 1 1 0 1 653653 2097152 1 16777216 653653 2097152 1 16777216 

noncomputable def Ns336p293 := @Enclosure.Real.IsNear.sqrt_image qz30 3555334669397 33554432000 665749 33554432000 172697143 172697176 16777216 (@Enclosure.Real.IsNear.of_eq qz30 (@HMul.hMul Real Real Real qz5 qz29 qz3) Bool.false 3555334669397 33554432000 665749 33554432000 (BSN.t_div_two_pi_mk qz29 665749 1000 qz32) (@Enclosure.Real.IsNear.mulLit_ff qz29 qz3 665749 1000 0 1 5340353 33554432 1 33554432 3555334669397 33554432000 665749 33554432000 (Enclosure.Real.IsNear.const Bool.false 665749 1000) RS337to348.d48 rfl)) 

noncomputable abbrev qz834 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 665749 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz649 := qz834

noncomputable abbrev qz394 := qz649

noncomputable abbrev qz35 := qz394

noncomputable def Ns336p294 := @Enclosure.Real.IsNear.sqrt_image qz35 345394319 33554432 33 33554432 53827291 53827297 16777216 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 345394319 33554432 33 33554432 345394319 33554432 33 33554432 (Ns336p293 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns336p295 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz35) 26913647 8388608 3 16777216 5229223 5229225 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz35) Bool.false 107654588 33554432 6 33554432 26913647 8388608 3 16777216 (Ns336p294 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns336p296 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz35)) Bool.false 10458448 33554432 2 33554432 653653 2097152 1 16777216 (Ns336p295 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz36 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz387))

noncomputable abbrev qz650 := (@HMul.hMul Real Real Real qz824 qz833 qz833)

noncomputable abbrev qz395 := (@HSub.hSub Real Real Real qz631 (@HSub.hSub Real Real Real qz631 qz650 qz645) qz639)

noncomputable abbrev qz37 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz395))

noncomputable def Ns336p297 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz31) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz36) qz37) Bool.false 64879046177847 

noncomputable def Ns336p298 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz36) qz37 124161631 33554432 2957 

noncomputable abbrev qz651 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz36))

noncomputable def Ns336p299 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz36) (@Neg.neg Real Real.instNeg qz651) Bool.true 124161631 33554432 2957 33554432 (BSN.inv_eq_neg_inv_neg qz36) 

noncomputable def Ns336p300 := @Enclosure.Real.IsNear.recentre' qz651 Bool.false 124161631 33554432 2957 33554432 124161631 33554432 

noncomputable def Ns336p301 := @Enclosure.Real.IsNear.recentre' qz36 Bool.true 4534009 16777216 1045114432 162403450880000 4534009 16777216 16329913 2537553920000 

noncomputable abbrev qz38 := (@HMul.hMul Real Real Real qz349 qz346 qz387)

noncomputable def Ns336p302 := @Enclosure.Real.IsNear.cos_image qz38 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7736171) (@Nat.cast Real Real.instNatCast 4194304)) Bool.false 7736171 4194304 209 33554432 Bool.true 4534009 16777216 1 

noncomputable def Ns336p303 := nat_lit 890540488583064347161841319 

noncomputable def Ns336p304 := nat_lit 144115188075855872000000000000000 

noncomputable def Ns336p305 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz31 884279719003555 140737488355328 1 500000000000000 9849999 33554432 33 33554432 8710154347905297746445 4722366482869645213696 Ns336p303 

noncomputable def Ns336p306 := @Enclosure.Real.IsNear.subLit_ff_p qz35 qz1 345394319 33554432 33 33554432 10 1 0 1 9849999 9849999 33554432 33 

noncomputable def Ns336p307 := @Ns336p306 33554432 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 345394319 33554432 33 33554432 345394319 33554432 33 33554432 (Ns336p293 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns336p308 := @Enclosure.Real.IsNear.recentre' qz38 Bool.false 8710154347905297746445 4722366482869645213696 Ns336p303 Ns336p304 7736171 4194304 209 33554432 (@Ns336p305 Ns336p304 RS337to348.d47 (Ns336p307 rfl rfl) rfl) 

noncomputable def Ns336p309 := nat_lit 6894355724896488211454966264722799856115764710812874265649075605175327965803831219707921 

noncomputable def Ns336p310 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600 

noncomputable def Ns336p311 := nat_lit 45952879431774340649954906348161270022659949926456284706231988027455321424930791441 

noncomputable def Ns336p312 := nat_lit 41634749376555184159068900804416086582658171429207481691064872499048237796561301724192785 

noncomputable def Ns336p313 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600 

noncomputable def Ns336p314 := BSN.cos_dyadic_bound_t 7736171 4194304 4 3 16777216 4840000 Ns336p309 Ns336p310 Ns336p311 Ns336p312 Ns336p313 Ns336p311 4534009 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 7736171) (BSN.cosEvenQ 4194304) 0 3 Ns336p309 Ns336p310 Ns336p311 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 7736171) (BSN.cosOddQ 4194304) 0 3 Ns336p312 Ns336p313 Ns336p311 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p315 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz36) 4534009 16777216 16329913 2537553920000 62079337 62082294 16777216 (@Enclosure.Real.IsNear.neg qz36 Bool.true 4534009 16777216 16329913 2537553920000 (Ns336p301 (@Ns336p302 4840000 (Ns336p308 rfl) (Enclosure.sfrac_false_div 7736171 4194304) (Ns336p314 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns336p316 := Ns336p299 (@Enclosure.Real.IsNear.neg qz651 Bool.false 124161631 33554432 2957 33554432 (@Ns336p300 2957 33554432 (Ns336p315 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p317 := @Enclosure.Real.IsNear.recentre' qz37 Bool.true 2090148 16777216 

noncomputable abbrev qz39 := (@HMul.hMul Real Real Real qz349 qz346 qz395)

noncomputable abbrev qz396 := (@Nat.cast Real Real.instNatCast 33554432)

noncomputable def Ns336p318 := @Enclosure.Real.IsNear.cos_image qz39 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 56898363)) qz396) Bool.true 56898363 33554432 

noncomputable def Ns336p319 := nat_lit 268694923487637589657624086205 

noncomputable def Ns336p320 := nat_lit 9485051099470586508201388215509509 

noncomputable def Ns336p321 := @Enclosure.Real.IsNear.recentre' qz39 Bool.true Ns336p319 Ns336p194 Ns336p320 

noncomputable def Ns336p322 := nat_lit 967140655691703339764940800000000000000 

noncomputable abbrev qz40 := qz395

noncomputable def Ns336p323 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz40 884279719003555 140737488355328 1 500000000000000 303857385523231 

noncomputable abbrev qz397 := (@HSub.hSub Real Real Real qz631 qz650 qz645)

noncomputable abbrev qz41 := qz397

noncomputable def Ns336p324 := @Enclosure.Real.IsNear.subLit_tf qz41 qz26 233488641345567 1125899906842624 1757397279 1125899906842624 1 16 

noncomputable abbrev qz398 := qz650

noncomputable abbrev qz42 := qz398

noncomputable def Ns336p325 := @Enclosure.Real.IsNear.subLit_ff_n qz42 qz31 97022480300001 1125899906842624 650101023 1125899906842624 9849999 33554432 33 33554432 

noncomputable def Ns336p326 := @Enclosure.Real.IsNear.mulLit_ff qz31 qz31 9849999 33554432 33 33554432 9849999 33554432 33 33554432 97022480300001 1125899906842624 

noncomputable def Ns336p327 := nat_lit 337798350428174800492269371520790323254497334780962077275488408489598817825608222636459640493735761 

noncomputable def Ns336p328 := nat_lit 975743491921780970500323514261193594148711042915413329552712293065467609596717903600577236539801600 

noncomputable def Ns336p329 := nat_lit 1151323210200574067736101657249428153773963971631876915558076159805347540919595712768770604881 

noncomputable def Ns336p330 := nat_lit 2042613436159561168232397351073227662761667150101385528701482389038192496531292009145543428501176145 

noncomputable def Ns336p331 := nat_lit 88792657764882068315529439797768617067532704905302612989296818668957552473301329227652528525121945600 

noncomputable def Ns336p332 := BSN.cos_dyadic_bound_t 56898363 33554432 4 3 16777216 4840000 Ns336p327 Ns336p328 Ns336p329 Ns336p330 Ns336p331 Ns336p329 2090148 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 56898363) (BSN.cosEvenQ 33554432) 0 3 Ns336p327 Ns336p328 Ns336p329 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 56898363) (BSN.cosOddQ 33554432) 0 3 Ns336p330 Ns336p331 Ns336p329 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p333 := @Ns336p317 815377216 81201725440000 522537 4194304 12740269 1268776960000 (@Ns336p318 165 16777216 Bool.true 2090148 16777216 1 4840000 (@Ns336p321 Ns336p322 56898363 33554432 165 16777216 (@Ns336p323 1125899906842624 1757397279 1125899906842624 Ns336p319 Ns336p194 Ns336p320 Ns336p322 RS337to348.d47 (@Ns336p324 0 1 4861718168371696 303857385523231 1125899906842624 1757397279 1125899906842624 (@Ns336p325 7834578738802216402944 233488641345567 1125899906842624 1757397279 1125899906842624 (@Ns336p326 650101023 1125899906842624 (Ns336p307 rfl rfl) (Ns336p307 rfl rfl) rfl) (Ns336p307 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 56898363 33554432) (BSN.cos_neg_of_bound 56898363 33554432 Bool.true 2090148 16777216 1 4840000 (Ns336p332 rfl rfl)) rfl rfl) 

noncomputable def Ns336p334 := @Ns336p291 107358541077903716067 Ns336p211 (Ns336p292 qz28 (@Enclosure.Real.IsNear.of_eq qz393 (@Inv.inv Real Real.instInv (Real.sqrt qz35)) Bool.false 653653 2097152 1 16777216 (BSN.rpow_neg_quarter_mk qz30 (BSN.t_div_two_pi_nonneg qz29 665749 1000 qz32)) Ns336p296) rfl) (@Ns336p297 140737488355328 128080979929167 2660818139217920000 (BSN.correction_mk qz31 (BSN.cos_two_pi_p_ne_zero_mk qz29 665749 1000 10 qz32 rfl rfl (@BSN.floor_sqrt_eq_dec qz29 665749 1000 10 qz32 rfl rfl rfl))) (@Ns336p298 33554432 522537 4194304 12740269 1268776960000 64879046177847 140737488355328 128080979929167 2660818139217920000 Ns336p316 (Ns336p333 rfl) rfl)) 

noncomputable def Ns336p335 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz29) (hardyZApproximantRS₀ qz29) Bool.false 227956996110923737789 295147905179352825856 8790033860248251543267 Ns336p211 (@Eq.refl Real (hardyZApproximantRS₀ qz29)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz29) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz29) qz29 10) (@HMul.hMul Real Real Real qz5 qz388 (Zeta.RiemannSiegel.correction qz31))) Bool.false 227956996110923737789 295147905179352825856 8790033860248251543267 Ns336p211 (BSN.hardyZApproximantRS₀_eq qz29 10 (@BSN.floor_sqrt_eq_dec qz29 665749 1000 10 qz32 rfl rfl rfl)) (@Ns336p213 227956996110923737789 295147905179352825856 8790033860248251543267 Ns336p211 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz29) qz29 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 10)) Bool.false 30736985 33554432 81579 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz29) qz29 10) (Ns336p290 (Ns336p289 rfl rfl rfl rfl) rfl rfl)) (Ns336p334 rfl) rfl rfl)) 

theorem RS337to348.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz29) Bool.false 227956996110923737789 295147905179352825856 8790033860248251543267 Ns336p211 := Ns336p335 

noncomputable abbrev qz835 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 664401 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))) (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 664401 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz652 := qz835

noncomputable abbrev qz399 := qz652

noncomputable abbrev qz653 := (@HMul.hMul Real Real Real qz824 qz835 qz835)

noncomputable abbrev qz400 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz627 qz653 qz652))

noncomputable abbrev qz43 := (@HAdd.hAdd Real Real Real qz365 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz399)) (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 1 32) qz400))

noncomputable abbrev qz401 := (@HMul.hMul Real Real Real qz627 qz637 qz637)

noncomputable abbrev qz44 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz349 qz401 qz377))

noncomputable def Ns336p336 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz365 qz43 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz44)) Bool.false 

noncomputable def Ns336p337 := @Enclosure.Real.IsNear.addLit_ff qz43 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz44) 19791001 1073741824 

noncomputable abbrev qz45 := (@Inv.inv Real Real.instInv qz399)

noncomputable abbrev qz46 := (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 1 32) qz400)

noncomputable def Ns336p338 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz45) qz46 2473875 134217728 25 134217728 

noncomputable def Ns336p339 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz45 25 4 0 1 98955 33554432 1 33554432 2473875 

noncomputable def Ns336p340 := @Enclosure.Real.IsNear.recentre' qz45 Bool.false 98955 33554432 1 33554432 98955 33554432 1 33554432 

noncomputable def Ns336p341 := @Enclosure.Real.IsNear.mulLit_ff qz19 qz7 26900013 8388608 3 16777216 3548135873553 33554432000 664401 33554432000 95444901124342056189 281474976710656000 1449662521509 

noncomputable def Ns336p342 := @Enclosure.Real.IsNear.sqrt_image qz7 3548135873553 33554432000 664401 33554432000 172522217 172522250 16777216 qz375 

noncomputable def Ns336p343 := @Enclosure.Real.IsNear.sqrt_image qz18 345044467 33554432 33 33554432 53800023 53800029 16777216 (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 345044467 33554432 33 33554432 345044467 33554432 33 33554432 (Ns336p342 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz402 := (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 107600052 33554432 6 33554432 26900013 8388608 3 16777216 (Ns336p343 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns336p344 := @Ns336p341 17592186044416000 qz402 

noncomputable def Ns336p345 := Ns336p344 qz375 

noncomputable abbrev qz47 := qz399

noncomputable def Ns336p346 := @Enclosure.Real.IsNear.inv_image qz47 95444901124342056189 281474976710656000 1449662521509 17592186044416000 49477 49478 16777216 (Ns336p345 rfl) rfl rfl 

noncomputable abbrev qz48 := qz400

noncomputable def Ns336p347 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz48 1 32 0 1 1 

noncomputable def Ns336p348 := @Enclosure.Real.IsNear.recentre' qz48 Bool.false 1 33554432 1 33554432 

noncomputable def Ns336p349 := nat_lit 869477198051935300682341553260170940596743691703629865879269 

noncomputable def Ns336p350 := nat_lit 22300745198530623141535718272648361505980416000000000 

noncomputable def Ns336p351 := nat_lit 39618108420139609023373398764506301564621763846990423 

noncomputable def Ns336p352 := nat_lit 1393796574908163946345982392040522594123776000000000 

noncomputable abbrev qz403 := (@HMul.hMul Real Real Real qz627 qz653 qz652)

noncomputable abbrev qz49 := qz403

noncomputable def Ns336p353 := @Enclosure.Real.IsNear.inv_image qz49 Ns336p349 Ns336p350 Ns336p351 Ns336p352 0 1 

noncomputable def Ns336p354 := nat_lit 9109729150635431501652031515308433203721 

noncomputable def Ns336p355 := nat_lit 79228162514264337593543950336000000 

noncomputable def Ns336p356 := nat_lit 138362912841262304456214600165849 

noncomputable def Ns336p357 := nat_lit 2475880078570760549798248448000000 

noncomputable abbrev qz404 := qz653

noncomputable abbrev qz50 := qz404

noncomputable def Ns336p358 := @Enclosure.Real.IsNear.mulLit_ff qz50 qz47 Ns336p354 Ns336p355 Ns336p356 Ns336p357 95444901124342056189 281474976710656000 1449662521509 

noncomputable def Ns336p359 := @Enclosure.Real.IsNear.mulLit_ff qz47 qz47 95444901124342056189 281474976710656000 1449662521509 17592186044416000 95444901124342056189 281474976710656000 1449662521509 17592186044416000 Ns336p354 

noncomputable def Ns336p360 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz44 13 10 0 1 1017565 33554432 1 

noncomputable def Ns336p361 := @Enclosure.Real.IsNear.recentre' qz44 Bool.false 1017565 33554432 1 33554432 1017565 33554432 

noncomputable abbrev qz51 := qz401

noncomputable def Ns336p362 := @Enclosure.Real.IsNear.mulLit_ff qz51 qz19 723610699400169 70368744177664 322800165 281474976710656 26900013 8388608 3 16777216 19465137220803638302197 

noncomputable def Ns336p363 := @Enclosure.Real.IsNear.mulLit_ff qz19 qz19 26900013 8388608 3 16777216 26900013 8388608 3 16777216 723610699400169 70368744177664 322800165 

noncomputable def Ns336p364 := @Ns336p363 281474976710656 qz402 

noncomputable def Ns336p365 := Ns336p364 qz402 

noncomputable def Ns336p366 := @Ns336p362 590295810358705651712 26049986631006813 4722366482869645213696 (Ns336p365 rfl) qz402 

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz349 qz401 qz377)

noncomputable def Ns336p367 := @Enclosure.Real.IsNear.inv_image qz52 19465137220803638302197 590295810358705651712 26049986631006813 4722366482869645213696 508782 508783 16777216 (Ns336p366 rfl) 

noncomputable def Ns336p368 := @Ns336p337 201 1073741824 2645669 67108864 13 335544320 4168917052293120 62121705 1073741824 1213 5368709120 (@Ns336p338 1 1073741824 1 1073741824 2656303189065728 19791001 1073741824 201 1073741824 (@Ns336p339 134217728 25 134217728 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns336p340 (Ns336p346 rfl rfl rfl rfl) rfl) rfl) (@Ns336p347 33554432 1 33554432 1 1073741824 1 1073741824 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns336p348 1 33554432 1 33554432 (@Ns336p353 16777216 (@Ns336p358 17592186044416000 Ns336p349 Ns336p350 Ns336p351 Ns336p352 (@Ns336p359 Ns336p355 Ns336p356 Ns336p357 (Ns336p345 rfl) (Ns336p345 rfl) rfl) (Ns336p345 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns336p360 33554432 2645669 67108864 13 335544320 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns336p361 1 33554432 (Ns336p367 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS337to348.d52 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 := @Ns336p336 62121705 1073741824 1213 5368709120 (BSN.hardyZErrorBoundRS₀_mk qz4 664401 1000 qz10 rfl rfl) (Ns336p368 rfl rfl) 

noncomputable def Ns336p369 := nat_lit 5902958103587056517120000 

noncomputable def Ns336p370 := nat_lit 65373403157736662518403694592 

noncomputable abbrev qz836 := (Enclosure.sfrac Bool.false 667096 1000)

noncomputable abbrev qz654 := qz836

noncomputable abbrev qz405 := qz654

noncomputable abbrev qz53 := qz405

noncomputable abbrev qz837 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 667096 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz655 := qz837

noncomputable abbrev qz406 := qz655

noncomputable abbrev qz54 := qz406

noncomputable abbrev qz838 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 667096 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz656 := qz838

noncomputable abbrev qz407 := qz656

noncomputable abbrev qz55 := qz407

noncomputable abbrev qz408 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz630 qz54 qz8))

noncomputable def Ns336p371 := @Enclosure.Real.IsNear.subLit_ff_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz53) qz53 10) (@HMul.hMul Real Real Real qz5 qz408 (Zeta.RiemannSiegel.correction qz55)) 2548249 67108864 163489 134217728 1332773782207799607675 9444732965739290427392 74404753278974782341 Ns336p369 Ns336p370 

noncomputable def Ns336p372 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz53) qz53 Real.sin BSN.quadSignPos 9 10 667096 1000 199 268435456 134217728 4503599627370496 Bool.false 328049529627 2506 618095470 56 84886744 8 

noncomputable def Ns336p373 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz53) qz53 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 667096 1000 105 155 268435456 134217728 4503599627370496 Bool.false 328049529627 2506 

noncomputable def Ns336p374 := Ns336p373 558195838 56 94906264 8 589812974 56 89478488 8 Bool.true 80142195 123472 Bool.true 46651151 Bool.true 55444695 14148475504056880 1 Bool.false 46416674 Bool.true Bool.false 55051305 Bool.false Bool.true 78202532 

noncomputable def Ns336p375 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz53) qz53 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 667096 1000 17 48 268435456 134217728 4503599627370496 Bool.false 328049529627 2506 

noncomputable def Ns336p376 := Ns336p375 480971758 57 109588312 8 522351262 57 101459064 8 Bool.true 151059890 91587 Bool.false 27017471 Bool.true 169351291 14148475504056880 1 Bool.false 26971879 Bool.true Bool.false 216763548 Bool.false Bool.true 80142195 

noncomputable def Ns336p377 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz53) qz53 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 667096 1000 189 94 268435456 134217728 4503599627370496 Bool.false 328049529627 2506 

noncomputable def Ns336p378 := Ns336p377 372130544 56 134217720 8 432030192 56 120047984 16 Bool.true 12086175 53800 Bool.false 109478304 Bool.false 208118407 14148475504056880 1 Bool.false 106468483 Bool.true Bool.false 191719300 Bool.true Bool.true 151059890 

noncomputable def Ns336p379 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz53) qz53 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 667096 1000 483 311 268435456 134217728 4503599627370496 Bool.false 328049529627 2506 

noncomputable def Ns336p380 := Ns336p379 186065264 56 189812528 16 294906480 56 154981288 8 Bool.true 268435448 2568 Bool.false 265598421 Bool.false 183136254 14148475504056880 1 Bool.false 224335204 Bool.false Bool.false 169256575 Bool.false Bool.true 12086175 

noncomputable def Ns336p381 := nat_lit 66612026397652669128900834903414712601064856484650327 

noncomputable def Ns336p382 := nat_lit 54507103550561222117487827764456066228162658304000 

noncomputable def Ns336p383 := nat_lit 63413764916871483512994057748480000 

noncomputable def Ns336p384 := nat_lit 253818480067705838556810411459096084480 

noncomputable abbrev qz409 := (@Eq.refl Real qz654)

noncomputable abbrev qz56 := qz409

noncomputable def Ns336p385 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz53 667096 1000 1780069292864 16000000 1334192 4000 2000 Ns336p383 Ns336p384 qz56 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns336p386 := nat_lit 87309715239931306480632902324603732100467728691560876605440 

noncomputable abbrev qz410 := (Enclosure.sfrac Bool.false 667096 2000)

noncomputable abbrev qz657 := (Real.log (Enclosure.sfrac Bool.false 1780069292864 16000000))

noncomputable abbrev qz658 := (@Nat.cast Real Real.instNatCast 1334192)

noncomputable abbrev qz57 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 667096 4000) qz657) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz658))))) qz410)

noncomputable abbrev qz411 := (@HSub.hSub Real Real Real qz11 qz57 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 667096 2000) (Real.log Real.pi)))

noncomputable def Ns336p387 := @Enclosure.Real.IsNear.addLit_ft_p qz411 (Enclosure.sfrac Bool.true Ns336p383 Ns336p384) 343984933902486222403 281474976710656000 577955649059703943 61952000000000000000000 Ns336p383 Ns336p384 0 1 Ns336p386 

noncomputable def Ns336p388 := nat_lit 2885554768413867145139585024000 

noncomputable abbrev qz412 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 667096 2000) (Real.log Real.pi))

noncomputable def Ns336p389 := @Enclosure.Real.IsNear.subLit_ff_p qz57 qz412 451458374590767183427 281474976710656000 527419072889589 121000000000000000000 3202958127507 8388608000 83387 16777216000 Ns336p388 343984933902486222403 281474976710656000 

noncomputable abbrev qz58 := (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 667096 4000) qz657) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz658)))))

noncomputable def Ns336p390 := @Enclosure.Real.IsNear.subLit_ff_p qz58 qz410 109068758024530614183 56294995342131200 527419072889589 121000000000000000000 667096 2000 0 1 180583349836306873370800 451458374590767183427 281474976710656000 527419072889589 121000000000000000000 

noncomputable def Ns336p391 := nat_lit 122800504499259717364424051043336192 

noncomputable def Ns336p392 := nat_lit 56188812673429682142576640 

noncomputable def Ns336p393 := nat_lit 35457632892715330855387775926179296493126407643912035571512529331307901971968776545944858664062448541042112434053787029892660181031448479958304272899112960 

noncomputable def Ns336p394 := nat_lit 823723086226707532591856534237199300607700274458672877023952528995680553645242689694181248927948340141221300406779116526258546200223578858019386568998912 

noncomputable def Ns336p395 := nat_lit 243976880637692669267965929917544444085248191951265816710511061476035437752743172497996757654120092848789596313616028757913819249277434712733777920 

noncomputable def Ns336p396 := BSN.log_dyadic_bound 731493292864 2828645292864 7 6 Ns336p393 134217728 38720000 Ns336p394 Ns336p395 71030603 3560138585728 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 731493292864) (BSN.artanhQ 2828645292864) 0 6 Ns336p394 Ns336p393 Ns336p395 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns336p397 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 667096 4000) qz657 667096 4000 0 1 3270619355225335 281474976710656 195312621 7562500000000000 54545427234835001929 28147497671065600 16286533527327 3781250000000000000 (Enclosure.Real.IsNear.const Bool.false 667096 4000) (BSN.isNear_log_sfrac 1780069292864 16000000 3270619355225335 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1780069292864) qz362)) Bool.false Ns336p392 Ns336p98 1000000619520000 38720000000000000000000 3270619355225335 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1780069292864 16000000 16 3560138585728 2097152000000 71030603 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns336p396 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p398 := BSN.arctan_dyadic_bound_f 1000 1334192 1 0 16777216 4840000 0 1 1 0 1 1 12574 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1334192) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1334192) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz659 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1334192)))

noncomputable def Ns336p399 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz659 884279719003555 562949953421312 1 2000000000000000 12574 16777216 1 4840000 14828673317427627425792 883857805575587 562949953421312 50000000121 242000000000000000 qz16 (Ns336p398 rfl) rfl rfl 

noncomputable def Ns336p400 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 667096 4000) qz657) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz659)) 54545427234835001929 28147497671065600 16286533527327 3781250000000000000 883857805575587 2251799813685248 50000000121 968000000000000000 Ns336p391 109068758024530614183 56294995342131200 527419072889589 121000000000000000000 (Ns336p397 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz659) 1 4 0 1 883857805575587 562949953421312 50000000121 242000000000000000 883857805575587 2251799813685248 50000000121 968000000000000000 qz364 Ns336p399 rfl) 

noncomputable def Ns336p401 := @Ns336p387 Ns336p381 Ns336p382 577955649059703943 61952000000000000000000 (@Ns336p389 577955649059703943 61952000000000000000000 (Ns336p390 (Ns336p400 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 667096 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz410 (Real.log Real.pi) 667096 2000 0 1 38410761 33554432 1 67108864 3202958127507 8388608000 83387 16777216000 (Enclosure.Real.IsNear.const Bool.false 667096 2000) RS337to348.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns336p383 Ns336p384) 

noncomputable def Ns336p402 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz53) Bool.false Ns336p381 Ns336p382 577955649059703943 61952000000000000000000 41006191203 33554432 157 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz53) (@HAdd.hAdd Real Real Real qz365 qz411 (Enclosure.sfrac Bool.true Ns336p383 Ns336p384)) Bool.false Ns336p381 Ns336p382 577955649059703943 61952000000000000000000 Ns336p385 (Ns336p401 rfl rfl)) 

noncomputable def Ns336p403 := nat_lit 7596813463981630628560896 

noncomputable def Ns336p404 := nat_lit 3512518835994141487971883275698476214845713668988465950245456784706150806338917784154358631459587791163044591657316939740065842948110040625 

noncomputable def Ns336p405 := nat_lit 2506224350331767375842658766725350765331847045926233300523084005008994368229056035972374038541754141505124034922450258093867431640625 

noncomputable def Ns336p406 := nat_lit 17540760062868096611196502288479694815163294087654772228030636311421663766137782118076018664224907227651557237292747260793606751846823640625 

noncomputable def Ns336p407 := BSN.sin_dyadic_bound_f 107957212435 68719476736 4 3 33554432 9689454 Ns336p404 Ns336p112 Ns336p405 Ns336p406 Ns336p115 Ns336p405 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107957212435) qz366 0 3 Ns336p404 Ns336p112 Ns336p405 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107957212435) qz367 0 3 Ns336p406 Ns336p115 Ns336p405 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz413 := (@Nat.cast Real Real.instNatCast Ns336p98)

noncomputable def Ns336p408 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz53) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 41006191203) qz396) Bool.false 41006191203 33554432 157 16777216 Bool.true 33554431 33554432 1 4840000 (Ns336p402 rfl) (Enclosure.sfrac_false_div 41006191203 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 41006191203) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns336p403) qz413) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 194 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q1 41006191203 33554432 226375608064910080 72057594037927936 194 Ns336p403 Ns336p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554431 33554432 Ns336p403 Ns336p98 107957212435 68719476736 9689454 9680000 (Ns336p407 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p409 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz53) Bool.false Ns336p381 Ns336p382 577955649059703943 61952000000000000000000 328049529627 268435456 2506 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz53) (@HAdd.hAdd Real Real Real qz365 qz411 (Enclosure.sfrac Bool.true Ns336p383 Ns336p384)) Bool.false Ns336p381 Ns336p382 577955649059703943 61952000000000000000000 Ns336p385 (Ns336p401 rfl rfl)) 

noncomputable def Ns336p410 := Ns336p380 53800 BSN.abs_quadSignPos (BSN.cos_quad_nat3 483 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 224335204 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 311 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 169256575 268435456) qz56 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz53) qz53 1) Bool.true 33554431 33554432 12135269 1268776960000 268435448 268435456 2568 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz53) qz53 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz53)) Bool.true 33554431 33554432 12135269 1268776960000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz53) qz53) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz53)) Bool.true 33554431 33554432 776657216 81201725440000 33554431 33554432 12135269 1268776960000 (Ns336p408 rfl rfl) rfl)) rfl) (Ns336p409 rfl) RS337to348.d7 

noncomputable def Ns336p411 := nat_lit 78159338424176751867940107869934064158702431295293394639235638184345185 

noncomputable def Ns336p412 := nat_lit 24763037216339201494988733455866252479420080101354132960471423614561 

noncomputable def Ns336p413 := nat_lit 204662936669731705708851253138517813149730163738937650697014479606480481 

noncomputable def Ns336p414 := BSN.sin_dyadic_bound_f 265598421 268435456 3 2 268435456 134217728 Ns336p411 Ns336p127 Ns336p412 Ns336p413 Ns336p130 Ns336p412 224335204 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 265598421) qz371 0 2 Ns336p411 Ns336p127 Ns336p412 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 265598421) qz372 0 2 Ns336p413 Ns336p130 Ns336p412 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p415 := nat_lit 17663213534685607663688946078415870418450768482124714223593837092143360 

noncomputable def Ns336p416 := nat_lit 1265303218015236164060905473696999317329725017198785975981734625536 

noncomputable def Ns336p417 := nat_lit 46258748766585519213014950644131770239904907422203548741641793385267456 

noncomputable def Ns336p418 := BSN.sin_dyadic_bound_f 183136254 268435456 3 2 268435456 134217728 Ns336p415 Ns336p127 Ns336p416 Ns336p417 Ns336p130 Ns336p416 169256575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 183136254) qz371 0 2 Ns336p415 Ns336p127 Ns336p416 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 183136254) qz372 0 2 Ns336p417 Ns336p130 Ns336p416 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p419 := nat_lit 143652187398840116685591523885056 

noncomputable def Ns336p420 := BSN.sin_dyadic_bound_f 109478304 268435456 2 1 268435456 134217728 Ns336p419 Ns336p137 Ns336p419 Ns336p419 Ns336p138 Ns336p419 106468483 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 109478304) qz371 0 1 Ns336p419 Ns336p137 Ns336p419 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 109478304) qz372 0 1 Ns336p419 Ns336p138 Ns336p419 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p421 := nat_lit 16368322016856879483376030200748932511851691469022818932155490251391681 

noncomputable def Ns336p422 := nat_lit 3519524106123805812861686289024921020219383916817191224797018014401 

noncomputable def Ns336p423 := nat_lit 49097927002358390838502367229668747693514635639234822414016876718146241 

noncomputable def Ns336p424 := BSN.cos_dyadic_bound_f 208118407 268435456 3 2 268435456 134217728 Ns336p421 Ns336p251 Ns336p422 Ns336p423 Ns336p254 Ns336p422 191719300 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 208118407) qz369 0 2 Ns336p421 Ns336p251 Ns336p422 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 208118407) qz370 0 2 Ns336p423 Ns336p254 Ns336p422 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p425 := Ns336p378 91587 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 189 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 106468483 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 94 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 191719300 268435456) qz56 rfl rfl (Ns336p410 RS337to348.d9 RS337to348.d11 RS337to348.d13 RS337to348.d17 (Ns336p414 rfl rfl) (Ns336p418 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns336p409 rfl) RS337to348.d19 RS337to348.d21 RS337to348.d23 RS337to348.d25 RS337to348.d17 (Ns336p420 rfl rfl) (Ns336p424 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns336p426 := nat_lit 532817862449601443754618977281 

noncomputable def Ns336p427 := BSN.sin_dyadic_bound_f 27017471 268435456 2 1 268435456 134217728 Ns336p426 Ns336p137 Ns336p426 Ns336p426 Ns336p138 Ns336p426 26971879 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 27017471) qz371 0 1 Ns336p426 Ns336p137 Ns336p426 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 27017471) qz372 0 1 Ns336p426 Ns336p138 Ns336p426 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p428 := nat_lit 7175692051700334032891842411473977867528723955575691514123560129823201 

noncomputable def Ns336p429 := nat_lit 676562766876631600677553847590609741074518292163360265251999089121 

noncomputable def Ns336p430 := nat_lit 21525723029567248835474172126726752383104022830142747821840176391291361 

noncomputable def Ns336p431 := BSN.cos_dyadic_bound_f 169351291 268435456 3 2 268435456 134217728 Ns336p428 Ns336p251 Ns336p429 Ns336p430 Ns336p254 Ns336p429 216763548 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 169351291) qz369 0 2 Ns336p428 Ns336p251 Ns336p429 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 169351291) qz370 0 2 Ns336p430 Ns336p254 Ns336p429 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p432 := Ns336p376 123472 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 17 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 26971879 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 48 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 216763548 268435456) qz56 rfl rfl (Ns336p425 rfl rfl) (Ns336p409 rfl) RS337to348.d27 RS337to348.d29 RS337to348.d31 RS337to348.d33 RS337to348.d17 (Ns336p427 rfl rfl) (Ns336p431 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p433 := nat_lit 4736411788474298503344554289601 

noncomputable def Ns336p434 := BSN.sin_dyadic_bound_f 46651151 268435456 2 1 268435456 134217728 Ns336p433 Ns336p137 Ns336p433 Ns336p433 Ns336p138 Ns336p433 46416674 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 46651151) qz371 0 1 Ns336p433 Ns336p137 Ns336p433 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 46651151) qz372 0 1 Ns336p433 Ns336p138 Ns336p433 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p435 := nat_lit 9450178137039789780181631150625 

noncomputable def Ns336p436 := BSN.sin_dyadic_bound_f 55444695 268435456 2 1 268435456 134217728 Ns336p435 Ns336p137 Ns336p435 Ns336p435 Ns336p138 Ns336p435 55051305 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 55444695) qz371 0 1 Ns336p435 Ns336p137 Ns336p435 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 55444695) qz372 0 1 Ns336p435 Ns336p138 Ns336p435 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p437 := Ns336p374 150873 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 105 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 46416674 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 155 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 55051305 268435456) qz56 rfl rfl (Ns336p432 rfl) (Ns336p409 rfl) RS337to348.d35 RS337to348.d37 RS337to348.d39 RS337to348.d41 RS337to348.d17 (Ns336p434 rfl rfl) (Ns336p436 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p438 := nat_lit 26153744659062668721004606087845868923242874995655746569891341917482253520326069038714196340893167484981796241 

noncomputable def Ns336p439 := nat_lit 6510263043228946903263837229342836021107132105440770956126613911784144262726950409988856882363840650641 

noncomputable def Ns336p440 := nat_lit 130672677176359035771551424569233393939825431782132718894121466698681872522428618324128464812218980551844224401 

noncomputable def Ns336p441 := BSN.sin_dyadic_bound_f 369657803 268435456 4 3 268435456 134217728 Ns336p438 Ns336p158 Ns336p439 Ns336p440 Ns336p161 Ns336p439 263414666 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 369657803) qz371 0 3 Ns336p438 Ns336p158 Ns336p439 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 369657803) qz372 0 3 Ns336p440 Ns336p161 Ns336p439 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p442 := Ns336p372 Bool.true 78202532 150873 Bool.true 369657803 14148475504056880 1 Bool.false 263414666 Bool.false Bool.false 5096498 163489 BSN.abs_quadSignPos qz373 (BSN.sfrac_eq_quadSignPos_mul Bool.false 263414666 268435456) qz56 rfl (Ns336p437 rfl) (Ns336p409 rfl) RS337to348.d43 RS337to348.d45 RS337to348.d17 (Ns336p441 rfl rfl) rfl 

noncomputable def Ns336p443 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz53) qz53 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz53) qz53 10) 5096498 268435456 163489 268435456 5096498 268435456 163489 268435456 2736161529266176 2548249 67108864 163489 134217728 (Ns336p442 rfl rfl rfl rfl) 

noncomputable def Ns336p444 := @Enclosure.Real.IsNear.mulLit_ff qz408 (Zeta.RiemannSiegel.correction qz55) 10453165 33554432 1 33554432 127499545085895 281474976710656 7110292332801 175921860444160000 1332773782207799607675 9444732965739290427392 

noncomputable abbrev qz414 := (@HPow.hPow Real Real Real qz630 qz54 qz8)

noncomputable def Ns336p445 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz414 1 1 0 1 10453165 33554432 1 33554432 10453165 33554432 1 33554432 

noncomputable def Ns336p446 := @Enclosure.Real.IsNear.sqrt_image qz54 445316015611 4194304000 83387 4194304000 172871762 172871796 16777216 (@Enclosure.Real.IsNear.of_eq qz54 (@HMul.hMul Real Real Real qz5 qz53 qz3) Bool.false 445316015611 4194304000 83387 4194304000 (BSN.t_div_two_pi_mk qz53 667096 1000 qz56) (@Enclosure.Real.IsNear.mulLit_ff qz53 qz3 667096 1000 0 1 5340353 33554432 1 33554432 445316015611 4194304000 83387 4194304000 (Enclosure.Real.IsNear.const Bool.false 667096 1000) RS337to348.d48 rfl)) 

noncomputable abbrev qz839 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 667096 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz660 := qz839

noncomputable abbrev qz415 := qz660

noncomputable abbrev qz59 := qz415

noncomputable def Ns336p447 := @Enclosure.Real.IsNear.sqrt_image qz59 172871779 16777216 17 16777216 53854497 53854503 16777216 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 345743558 33554432 34 33554432 172871779 16777216 17 16777216 (Ns336p446 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns336p448 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz59) 13463625 4194304 3 16777216 5226582 5226583 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz59) Bool.false 107709000 33554432 6 33554432 13463625 4194304 3 16777216 (Ns336p447 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns336p449 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz59)) Bool.false 10453165 33554432 1 33554432 10453165 33554432 1 33554432 (Ns336p448 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz60 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz407))

noncomputable abbrev qz661 := (@HMul.hMul Real Real Real qz824 qz838 qz838)

noncomputable abbrev qz416 := (@HSub.hSub Real Real Real qz631 (@HSub.hSub Real Real Real qz631 qz661 qz656) qz639)

noncomputable abbrev qz61 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz416))

noncomputable def Ns336p450 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz55) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz60) qz61) Bool.false 127499545085895 

noncomputable def Ns336p451 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz60) qz61 50444385 16777216 999 

noncomputable abbrev qz662 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz60))

noncomputable def Ns336p452 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz60) (@Neg.neg Real Real.instNeg qz662) Bool.true 50444385 16777216 999 16777216 (BSN.inv_eq_neg_inv_neg qz60) 

noncomputable def Ns336p453 := @Enclosure.Real.IsNear.recentre' qz662 Bool.false 100888770 33554432 1998 33554432 50444385 16777216 

noncomputable def Ns336p454 := @Enclosure.Real.IsNear.recentre' qz60 Bool.true 5579907 16777216 534657216 81201725440000 5579907 16777216 8354019 1268776960000 

noncomputable abbrev qz62 := (@HMul.hMul Real Real Real qz349 qz346 qz407)

noncomputable def Ns336p455 := @Enclosure.Real.IsNear.cos_image qz62 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 32041851) qz368) Bool.false 32041851 16777216 107 16777216 Bool.true 5579907 16777216 1 

noncomputable def Ns336p456 := nat_lit 458763281997554166391992887 

noncomputable def Ns336p457 := nat_lit 72057594037927936000000000000000 

noncomputable def Ns336p458 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz55 884279719003555 140737488355328 1 500000000000000 5099619 16777216 17 16777216 4509489656345190145545 2361183241434822606848 Ns336p456 

noncomputable def Ns336p459 := @Enclosure.Real.IsNear.subLit_ff_p qz59 qz1 172871779 16777216 17 16777216 10 1 0 1 5099619 5099619 16777216 17 

noncomputable def Ns336p460 := @Ns336p459 16777216 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 345743558 33554432 34 33554432 172871779 16777216 17 16777216 (Ns336p446 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns336p461 := @Enclosure.Real.IsNear.recentre' qz62 Bool.false 4509489656345190145545 2361183241434822606848 Ns336p456 Ns336p457 32041851 16777216 107 16777216 (@Ns336p458 Ns336p457 RS337to348.d47 (Ns336p460 rfl rfl) rfl) 

noncomputable def Ns336p462 := nat_lit 133102072315851528236695023562787435595167051884893472473703975124349008411864895682219875379281 

noncomputable def Ns336p463 := nat_lit 1171146321253498426549115784880878088599295943475942308452518092501130793478076305429637201 

noncomputable def Ns336p464 := nat_lit 803250406892481822518001172391180467015271266944560020086816068961077918584361311695608533100625 

noncomputable def Ns336p465 := BSN.cos_dyadic_bound_t 32041851 16777216 4 3 16777216 4840000 Ns336p462 Ns336p203 Ns336p463 Ns336p464 Ns336p206 Ns336p463 5579907 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32041851) (BSN.cosEvenQ 16777216) 0 3 Ns336p462 Ns336p203 Ns336p463 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32041851) (BSN.cosOddQ 16777216) 0 3 Ns336p464 Ns336p206 Ns336p463 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p466 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz60) 5579907 16777216 8354019 1268776960000 50443386 50445384 16777216 (@Enclosure.Real.IsNear.neg qz60 Bool.true 5579907 16777216 8354019 1268776960000 (Ns336p454 (@Ns336p455 4840000 (Ns336p461 rfl) (Enclosure.sfrac_false_div 32041851 16777216) (Ns336p465 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns336p467 := Ns336p452 (@Enclosure.Real.IsNear.neg qz662 Bool.false 50444385 16777216 999 16777216 (@Ns336p453 999 16777216 (Ns336p466 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p468 := @Enclosure.Real.IsNear.recentre' qz61 Bool.true 2527527 16777216 

noncomputable abbrev qz63 := (@HMul.hMul Real Real Real qz349 qz346 qz416)

noncomputable def Ns336p469 := @Enclosure.Real.IsNear.cos_image qz63 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3611347)) (@Nat.cast Real Real.instNatCast 2097152)) Bool.true 3611347 2097152 

noncomputable def Ns336p470 := nat_lit 68216416214482065628537754245 

noncomputable def Ns336p471 := nat_lit 39614081257132168796771975168 

noncomputable def Ns336p472 := nat_lit 12375814372152784570019811080424497 

noncomputable def Ns336p473 := @Enclosure.Real.IsNear.recentre' qz63 Bool.true Ns336p470 Ns336p471 Ns336p472 

noncomputable def Ns336p474 := nat_lit 1208925819614629174706176000000000000000 

noncomputable abbrev qz64 := qz416

noncomputable def Ns336p475 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz64 884279719003555 140737488355328 1 500000000000000 77143481579959 

noncomputable abbrev qz417 := (@HSub.hSub Real Real Real qz631 qz661 qz656)

noncomputable abbrev qz65 := qz417

noncomputable def Ns336p476 := @Enclosure.Real.IsNear.subLit_tf qz65 qz26 59551295535543 281474976710656 458600007 281474976710656 1 16 

noncomputable abbrev qz418 := qz661

noncomputable abbrev qz66 := qz418

noncomputable def Ns336p477 := @Enclosure.Real.IsNear.subLit_ff_n qz66 qz55 26006113945161 281474976710656 173387335 281474976710656 5099619 16777216 17 16777216 

noncomputable def Ns336p478 := @Enclosure.Real.IsNear.mulLit_ff qz55 qz55 5099619 16777216 17 16777216 5099619 16777216 17 16777216 26006113945161 281474976710656 

noncomputable def Ns336p479 := nat_lit 1276764478499807108746291101161564984770439444330076803711798543635819239329631958321 

noncomputable def Ns336p480 := nat_lit 4920742517710073180633168878167770440783963825919423922940867054483131175925041 

noncomputable def Ns336p481 := nat_lit 7718792177143063532331777426736999703039436259948738230299357709416924282370478699825 

noncomputable def Ns336p482 := BSN.cos_dyadic_bound_t 3611347 2097152 4 3 16777216 4840000 Ns336p479 Ns336p184 Ns336p480 Ns336p481 Ns336p187 Ns336p480 2527527 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3611347) (BSN.cosEvenQ 2097152) 0 3 Ns336p479 Ns336p184 Ns336p480 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3611347) (BSN.cosOddQ 2097152) 0 3 Ns336p481 Ns336p187 Ns336p480 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p483 := @Ns336p468 212314304 20300431360000 2527527 16777216 3317411 317194240000 (@Ns336p469 43 4194304 Bool.true 2527527 16777216 1 4840000 (@Ns336p473 Ns336p474 3611347 2097152 43 4194304 (@Ns336p475 281474976710656 458600007 281474976710656 Ns336p470 Ns336p471 Ns336p472 Ns336p474 RS337to348.d47 (@Ns336p476 0 1 1234295705279344 77143481579959 281474976710656 458600007 281474976710656 (@Ns336p477 999104948279640588288 59551295535543 281474976710656 458600007 281474976710656 (@Ns336p478 173387335 281474976710656 (Ns336p460 rfl rfl) (Ns336p460 rfl rfl) rfl) (Ns336p460 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 3611347 2097152) (BSN.cos_neg_of_bound 3611347 2097152 Bool.true 2527527 16777216 1 4840000 (Ns336p482 rfl rfl)) rfl rfl) 

noncomputable def Ns336p484 := @Ns336p444 74404753278974782341 Ns336p369 (Ns336p445 qz28 (@Enclosure.Real.IsNear.of_eq qz414 (@Inv.inv Real Real.instInv (Real.sqrt qz59)) Bool.false 10453165 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz54 (BSN.t_div_two_pi_nonneg qz53 667096 1000 qz56)) Ns336p449) rfl) (@Ns336p450 281474976710656 7110292332801 175921860444160000 (BSN.correction_mk qz55 (BSN.cos_two_pi_p_ne_zero_mk qz53 667096 1000 10 qz56 rfl rfl (@BSN.floor_sqrt_eq_dec qz53 667096 1000 10 qz56 rfl rfl rfl))) (@Ns336p451 16777216 2527527 16777216 3317411 317194240000 127499545085895 281474976710656 7110292332801 175921860444160000 Ns336p467 (Ns336p483 rfl) rfl)) 

noncomputable def Ns336p485 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz53) (hardyZApproximantRS₀ qz53) Bool.true 974139618243823387003 9444732965739290427392 7264727013817793342341 Ns336p369 (@Eq.refl Real (hardyZApproximantRS₀ qz53)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz53) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz53) qz53 10) (@HMul.hMul Real Real Real qz5 qz408 (Zeta.RiemannSiegel.correction qz55))) Bool.true 974139618243823387003 9444732965739290427392 7264727013817793342341 Ns336p369 (BSN.hardyZApproximantRS₀_eq qz53 10 (@BSN.floor_sqrt_eq_dec qz53 667096 1000 10 qz56 rfl rfl rfl)) (@Ns336p371 974139618243823387003 9444732965739290427392 7264727013817793342341 Ns336p369 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz53) qz53 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz53) qz53 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz53) qz53 10)) Bool.false 2548249 67108864 163489 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz53) qz53 10) (Ns336p443 (Ns336p442 rfl rfl rfl rfl) rfl rfl)) (Ns336p484 rfl) rfl rfl)) 

theorem RS337to348.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz53) Bool.true 974139618243823387003 9444732965739290427392 7264727013817793342341 Ns336p369 := Ns336p485 

noncomputable def Ns336p486 := nat_lit 14285158610680676771430400 

noncomputable def Ns336p487 := nat_lit 105892335040819306491918942208 

noncomputable abbrev qz840 := (Enclosure.sfrac Bool.false 668442 1000)

noncomputable abbrev qz663 := qz840

noncomputable abbrev qz419 := qz663

noncomputable abbrev qz67 := qz419

noncomputable abbrev qz841 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 668442 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz664 := qz841

noncomputable abbrev qz420 := qz664

noncomputable abbrev qz68 := qz420

noncomputable abbrev qz842 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 668442 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz665 := qz842

noncomputable abbrev qz421 := qz665

noncomputable abbrev qz69 := qz421

noncomputable abbrev qz422 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz630 qz68 qz8))

noncomputable def Ns336p488 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz67) qz67 10) (@HMul.hMul Real Real Real qz5 qz422 (Zeta.RiemannSiegel.correction qz69)) 188696369 67108864 163819 134217728 81872061040714942305 590295810358705651712 149235461725961376211 Ns336p486 Ns336p487 

noncomputable def Ns336p489 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz67) qz67 Real.sin BSN.quadSignPos 9 10 668442 1000 199 268435456 134217728 4503599627370496 Bool.false 328892487420 2510 618095470 56 84886744 8 

noncomputable def Ns336p490 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz67) qz67 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 668442 1000 104 155 268435456 134217728 4503599627370496 Bool.false 328892487420 2510 

noncomputable def Ns336p491 := Ns336p490 558195838 56 94906264 8 589812974 56 89478488 8 Bool.false 276881528 123722 Bool.true 376682384 Bool.true 6375165 14148475504056880 1 Bool.false 44764920 Bool.false Bool.false 6374565 Bool.false Bool.false 294833172 

noncomputable def Ns336p492 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz67) qz67 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 668442 1000 17 48 268435456 134217728 4503599627370496 Bool.false 328892487420 2510 

noncomputable def Ns336p493 := Ns336p492 480971758 57 109588312 8 522351262 57 101459064 8 Bool.false 256843242 91773 Bool.false 222587278 Bool.true 29478297 14148475504056880 1 Bool.false 197942356 Bool.true Bool.false 266818499 Bool.false Bool.false 276881528 

noncomputable def Ns336p494 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz67) qz67 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 668442 1000 190 95 268435456 134217728 4503599627370496 Bool.false 328892487420 2510 

noncomputable def Ns336p495 := Ns336p494 372130544 56 134217720 8 432030192 56 120047984 16 Bool.false 368918984 53910 Bool.false 29890956 Bool.false 47906133 14148475504056880 1 Bool.false 266772958 Bool.true Bool.false 47652240 Bool.false Bool.false 256843242 

noncomputable def Ns336p496 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz67) qz67 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 668442 1000 485 312 268435456 134217728 4503599627370496 Bool.false 328892487420 2510 

noncomputable def Ns336p497 := Ns336p496 186065264 56 189812528 16 294906480 56 154981288 8 Bool.false 268435280 2576 Bool.false 14797512 Bool.false 207492496 14148475504056880 1 Bool.false 14790018 Bool.true Bool.false 192156873 Bool.false Bool.false 368918984 

noncomputable def Ns336p498 := nat_lit 961362100672951810001525297789531903868959244253251041 

noncomputable def Ns336p499 := nat_lit 784644477286007470782928596987270980703094833152000 

noncomputable def Ns336p500 := nat_lit 64056101369966374981091483151360000 

noncomputable def Ns336p501 := nat_lit 256906798152124510563093549458624286720 

noncomputable abbrev qz423 := (@Eq.refl Real qz663)

noncomputable abbrev qz70 := qz423

noncomputable def Ns336p502 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz67 668442 1000 1787259829456 16000000 1336884 4000 2000 Ns336p500 Ns336p501 qz70 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns336p503 := nat_lit 177198262396038477619481142888566520521126567900759231877120 

noncomputable abbrev qz424 := (Enclosure.sfrac Bool.false 668442 2000)

noncomputable abbrev qz666 := (Real.log (Enclosure.sfrac Bool.false 1787259829456 16000000))

noncomputable abbrev qz667 := (@Nat.cast Real Real.instNatCast 1336884)

noncomputable abbrev qz71 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 668442 4000) qz666) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz667))))) qz424)

noncomputable abbrev qz425 := (@HSub.hSub Real Real Real qz11 qz71 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 668442 2000) (Real.log Real.pi)))

noncomputable def Ns336p504 := @Enclosure.Real.IsNear.addLit_ft_p qz425 (Enclosure.sfrac Bool.true Ns336p500 Ns336p501) 689737678142295609821 562949953421312000 2316461335512467169 247808000000000000000000 Ns336p500 Ns336p501 0 1 Ns336p503 

noncomputable def Ns336p505 := nat_lit 23143756019063544363637276672000 

noncomputable abbrev qz426 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 668442 2000) (Real.log Real.pi))

noncomputable def Ns336p506 := @Enclosure.Real.IsNear.subLit_ff_p qz71 qz426 905118257970553917917 562949953421312000 528470636041053 121000000000000000000 12837682952181 33554432000 334221 67108864000 Ns336p505 689737678142295609821 562949953421312000 

noncomputable def Ns336p507 := nat_lit 1810236515941107835834000 

noncomputable abbrev qz72 := (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 668442 4000) qz666) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz667)))))

noncomputable def Ns336p508 := @Enclosure.Real.IsNear.subLit_ff_p qz72 qz424 1093267954352978235869 562949953421312000 528470636041053 121000000000000000000 668442 2000 0 1 Ns336p507 905118257970553917917 562949953421312000 528470636041053 121000000000000000000 

noncomputable def Ns336p509 := nat_lit 2461820575920088606707353722669760512 

noncomputable def Ns336p510 := nat_lit 56208307026834312109490176 

noncomputable def Ns336p511 := nat_lit 36554501840952181519686271382758488283758726996799435808569094583768821240244876272642198884606728342808699148596222520712758341989082144614173447144079360 

noncomputable def Ns336p512 := nat_lit 862130572960869510818485146204919619307912568843783671700567922594242950419544802827024055644275943930839907260639467703710569796229060139653167413460992 

noncomputable def Ns336p513 := nat_lit 274364297856254766140064665504520949501035126368692653705723644666319504106166376718443837882778421791465152230204437436745714697282225403823390720 

noncomputable def Ns336p514 := BSN.log_dyadic_bound 738683829456 2835835829456 7 6 Ns336p511 134217728 38720000 Ns336p512 Ns336p513 71571680 3574519658912 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 738683829456) (BSN.artanhQ 2835835829456) 0 6 Ns336p512 Ns336p511 Ns336p513 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns336p515 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 668442 4000) qz666 668442 4000 0 1 3271754075938039 281474976710656 195312621 7562500000000000 1093488919014087332619 562949953421312000 65277579503241 15125000000000000000 (Enclosure.Real.IsNear.const Bool.false 668442 4000) (BSN.isNear_log_sfrac 1787259829456 16000000 3271754075938039 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1787259829456) qz362)) Bool.false Ns336p510 Ns336p98 1000000619520000 38720000000000000000000 3271754075938039 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1787259829456 16000000 16 3574519658912 2097152000000 71571680 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns336p514 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p516 := BSN.arctan_dyadic_bound_f 1000 1336884 1 0 16777216 4840000 0 1 1 0 1 1 12549 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1336884) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1336884) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz668 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1336884)))

noncomputable def Ns336p517 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz668 884279719003555 562949953421312 1 2000000000000000 12549 16777216 1 4840000 14828687391176462958592 883858644436387 562949953421312 50000000121 242000000000000000 qz16 (Ns336p516 rfl) rfl rfl 

noncomputable def Ns336p518 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 668442 4000) qz666) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz668)) 1093488919014087332619 562949953421312000 65277579503241 15125000000000000000 883858644436387 2251799813685248 50000000121 968000000000000000 Ns336p509 1093267954352978235869 562949953421312000 528470636041053 121000000000000000000 (Ns336p515 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz668) 1 4 0 1 883858644436387 562949953421312 50000000121 242000000000000000 883858644436387 2251799813685248 50000000121 968000000000000000 qz364 Ns336p517 rfl) 

noncomputable def Ns336p519 := @Ns336p504 Ns336p498 Ns336p499 2316461335512467169 247808000000000000000000 (@Ns336p506 2316461335512467169 247808000000000000000000 (Ns336p508 (Ns336p518 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 668442 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz424 (Real.log Real.pi) 668442 2000 0 1 38410761 33554432 1 67108864 12837682952181 33554432000 334221 67108864000 (Enclosure.Real.IsNear.const Bool.false 668442 2000) RS337to348.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns336p500 Ns336p501) 

noncomputable def Ns336p520 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz67) Bool.false Ns336p498 Ns336p499 2316461335512467169 247808000000000000000000 41111560927 33554432 315 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz67) (@HAdd.hAdd Real Real Real qz365 qz425 (Enclosure.sfrac Bool.true Ns336p500 Ns336p501)) Bool.false Ns336p498 Ns336p499 2316461335512467169 247808000000000000000000 Ns336p502 (Ns336p519 rfl rfl)) 

noncomputable def Ns336p521 := nat_lit 7590381161197301194031104 

noncomputable def Ns336p522 := nat_lit 3500613768925706652583847524283122181452645575190034627271387491672413007327093549830281522084825791345649420176060375782898541430933098496 

noncomputable def Ns336p523 := nat_lit 2480878040369715871567983665888711672741313157018991965800841546641853470911292435016840424075374151048646911483986176785326114410496 

noncomputable def Ns336p524 := nat_lit 17481382221090867088818664900370851196189428451808654221773846155786588878497294157808230342879689431006056532201565950295337504065721798656 

noncomputable def Ns336p525 := BSN.sin_dyadic_bound_f 107865803914 68719476736 4 3 33554432 9689454 Ns336p522 Ns336p112 Ns336p523 Ns336p524 Ns336p115 Ns336p523 33554410 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107865803914) qz366 0 3 Ns336p522 Ns336p112 Ns336p523 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107865803914) qz367 0 3 Ns336p524 Ns336p115 Ns336p523 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p526 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz67) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 41111560927) qz396) Bool.false 41111560927 33554432 315 33554432 Bool.false 33554410 33554432 1 4840000 (Ns336p520 rfl) (Enclosure.sfrac_false_div 41111560927 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 41111560927) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns336p521) qz413) 226375608064910080 72057594037927936 Bool.false 33554410 33554432 194 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q3 41111560927 33554432 226375608064910080 72057594037927936 194 Ns336p521 Ns336p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554410 33554432 Ns336p521 Ns336p98 107865803914 68719476736 9689454 9680000 (Ns336p525 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p527 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz67) Bool.false Ns336p498 Ns336p499 2316461335512467169 247808000000000000000000 328892487420 268435456 2510 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz67) (@HAdd.hAdd Real Real Real qz365 qz425 (Enclosure.sfrac Bool.true Ns336p500 Ns336p501)) Bool.false Ns336p498 Ns336p499 2316461335512467169 247808000000000000000000 Ns336p502 (Ns336p519 rfl rfl)) 

noncomputable def Ns336p528 := Ns336p497 53910 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 485 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 14790018 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 312 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 192156873 268435456) qz70 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz67) qz67 1) Bool.false 16777205 16777216 24346163 2537553920000 268435280 268435456 2576 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz67) qz67 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz67)) Bool.false 16777205 16777216 24346163 2537553920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz67) qz67) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz67)) Bool.false 33554410 33554432 1558154432 162403450880000 16777205 16777216 24346163 2537553920000 (Ns336p526 rfl rfl) rfl)) rfl) (Ns336p527 rfl) RS337to348.d7 

noncomputable def Ns336p529 := nat_lit 47946267420439145044180340736 

noncomputable def Ns336p530 := BSN.sin_dyadic_bound_f 14797512 268435456 2 1 268435456 134217728 Ns336p529 Ns336p137 Ns336p529 Ns336p529 Ns336p138 Ns336p529 14790018 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 14797512) qz371 0 1 Ns336p529 Ns336p137 Ns336p529 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 14797512) qz372 0 1 Ns336p529 Ns336p138 Ns336p529 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p531 := nat_lit 16172257586309161734706613077455082781035646188526441678566185779593216 

noncomputable def Ns336p532 := nat_lit 3435731051704027232365101997276650493637059496163716404854743105536 

noncomputable def Ns336p533 := nat_lit 48509901296824077149655109028370695042119664446586997602888847852568576 

noncomputable def Ns336p534 := BSN.cos_dyadic_bound_f 207492496 268435456 3 2 268435456 134217728 Ns336p531 Ns336p251 Ns336p532 Ns336p533 Ns336p254 Ns336p532 192156873 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 207492496) qz369 0 2 Ns336p531 Ns336p251 Ns336p532 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 207492496) qz370 0 2 Ns336p533 Ns336p254 Ns336p532 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p535 := nat_lit 798287301756889605288759972096 

noncomputable def Ns336p536 := BSN.cos_dyadic_bound_f 29890956 268435456 2 1 268435456 134217728 Ns336p535 Ns336p142 Ns336p535 Ns336p535 Ns336p143 Ns336p535 266772958 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 29890956) qz369 0 1 Ns336p535 Ns336p142 Ns336p535 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 29890956) qz370 0 1 Ns336p535 Ns336p143 Ns336p535 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p537 := nat_lit 5267013887678693684718049388721 

noncomputable def Ns336p538 := BSN.sin_dyadic_bound_f 47906133 268435456 2 1 268435456 134217728 Ns336p537 Ns336p137 Ns336p537 Ns336p537 Ns336p138 Ns336p537 47652240 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 47906133) qz371 0 1 Ns336p537 Ns336p137 Ns336p537 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 47906133) qz372 0 1 Ns336p537 Ns336p138 Ns336p537 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p539 := Ns336p495 91773 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 190 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 266772958 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 95 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 47652240 268435456) qz70 rfl rfl (Ns336p528 RS337to348.d9 RS337to348.d11 RS337to348.d13 RS337to348.d17 (Ns336p530 rfl rfl) (Ns336p534 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns336p527 rfl) RS337to348.d19 RS337to348.d21 RS337to348.d23 RS337to348.d25 RS337to348.d17 (Ns336p536 rfl rfl) (Ns336p538 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns336p540 := nat_lit 38548771851203704990548347333258837224951319178599570290768601627541760 

noncomputable def Ns336p541 := nat_lit 6025633439504992429518992580031308470797713637001888037429395374336 

noncomputable def Ns336p542 := nat_lit 100951313346631457368455021789595951565919782502824681038047642384384256 

noncomputable def Ns336p543 := BSN.sin_dyadic_bound_f 222587278 268435456 3 2 268435456 134217728 Ns336p540 Ns336p127 Ns336p541 Ns336p542 Ns336p130 Ns336p541 197942356 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 222587278) qz371 0 2 Ns336p540 Ns336p127 Ns336p541 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 222587278) qz372 0 2 Ns336p542 Ns336p130 Ns336p541 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p544 := nat_lit 755108850507482065217900403681 

noncomputable def Ns336p545 := BSN.cos_dyadic_bound_f 29478297 268435456 2 1 268435456 134217728 Ns336p544 Ns336p142 Ns336p544 Ns336p544 Ns336p143 Ns336p544 266818499 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 29478297) qz369 0 1 Ns336p544 Ns336p142 Ns336p544 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 29478297) qz370 0 1 Ns336p544 Ns336p143 Ns336p544 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p546 := Ns336p493 123722 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 17 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 197942356 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 48 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266818499 268435456) qz70 rfl rfl (Ns336p539 rfl rfl) (Ns336p527 rfl) RS337to348.d27 RS337to348.d29 RS337to348.d31 RS337to348.d33 RS337to348.d17 (Ns336p543 rfl rfl) (Ns336p545 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p547 := nat_lit 10857941763928240031965603658151410378654784880234613631797712312721556656971149259617774681016200460381454336 

noncomputable def Ns336p548 := nat_lit 8160254893157470105298514273402500914309495999349318944800019983427964829204860034746514046938939129856 

noncomputable def Ns336p549 := nat_lit 65770351964022860805603319921495808490559425162351501122967123454557380709683171068836680963864774639091712000 

noncomputable def Ns336p550 := BSN.cos_dyadic_bound_f 376682384 268435456 4 3 268435456 134217728 Ns336p547 Ns336p121 Ns336p548 Ns336p549 Ns336p124 Ns336p548 44764920 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 376682384) qz369 0 3 Ns336p547 Ns336p121 Ns336p548 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 376682384) qz370 0 3 Ns336p549 Ns336p124 Ns336p548 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p551 := BSN.sin_dyadic_bound_f 6375165 268435456 1 0 268435456 134217728 0 1 1 0 1 1 6374565 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 6375165) qz371 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 6375165) qz372 0 0 rfl) rfl rfl 

noncomputable def Ns336p552 := Ns336p491 151178 BSN.abs_quadSignPos (BSN.cos_quad_nat0 104 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 44764920 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 155 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 6374565 268435456) qz70 rfl rfl (Ns336p546 rfl) (Ns336p527 rfl) RS337to348.d35 RS337to348.d37 RS337to348.d39 RS337to348.d41 RS337to348.d17 (Ns336p550 rfl rfl) (Ns336p551 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p553 := nat_lit 23173439640406058944883363732210267795125545492851720826681659887613738765016476009526031505557855095180230656 

noncomputable def Ns336p554 := nat_lit 4530484479079955353663293545805401788088151750282299488622306392287762870602813635619541908735452512256 

noncomputable def Ns336p555 := nat_lit 115791776356222101480997817149044081157859881608203142635965386315235193469874693623745951007065686143313903616 

noncomputable def Ns336p556 := BSN.sin_dyadic_bound_f 358656512 268435456 4 3 268435456 134217728 Ns336p553 Ns336p158 Ns336p554 Ns336p555 Ns336p161 Ns336p554 261076275 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 358656512) qz371 0 3 Ns336p553 Ns336p158 Ns336p554 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 358656512) qz372 0 3 Ns336p555 Ns336p161 Ns336p554 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p557 := Ns336p489 Bool.false 294833172 151178 Bool.true 358656512 14148475504056880 1 Bool.false 261076275 Bool.false Bool.false 377392738 163819 BSN.abs_quadSignPos qz373 (BSN.sfrac_eq_quadSignPos_mul Bool.false 261076275 268435456) qz70 rfl (Ns336p552 rfl) (Ns336p527 rfl) RS337to348.d43 RS337to348.d45 RS337to348.d17 (Ns336p556 rfl rfl) rfl 

noncomputable def Ns336p558 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz67) qz67 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz67) qz67 10) 377392738 268435456 163819 268435456 377392738 268435456 163819 268435456 202611183432237056 188696369 67108864 163819 134217728 (Ns336p557 rfl rfl rfl rfl) 

noncomputable def Ns336p559 := @Enclosure.Real.IsNear.mulLit_ff qz422 (Zeta.RiemannSiegel.correction qz69) 5223949 16777216 1 16777216 15672446465445 35184372088832 1424747447061109 42573090227486720000 81872061040714942305 590295810358705651712 

noncomputable abbrev qz427 := (@HPow.hPow Real Real Real qz630 qz68 qz8)

noncomputable def Ns336p560 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz427 1 1 0 1 5223949 16777216 1 16777216 5223949 16777216 1 16777216 

noncomputable def Ns336p561 := @Enclosure.Real.IsNear.sqrt_image qz68 1784858120013 16777216000 334221 16777216000 173046076 173046109 16777216 (@Enclosure.Real.IsNear.of_eq qz68 (@HMul.hMul Real Real Real qz5 qz67 qz3) Bool.false 1784858120013 16777216000 334221 16777216000 (BSN.t_div_two_pi_mk qz67 668442 1000 qz70) (@Enclosure.Real.IsNear.mulLit_ff qz67 qz3 668442 1000 0 1 5340353 33554432 1 33554432 1784858120013 16777216000 334221 16777216000 (Enclosure.Real.IsNear.const Bool.false 668442 1000) RS337to348.d48 rfl)) 

noncomputable abbrev qz843 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 668442 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz669 := qz843

noncomputable abbrev qz428 := qz669

noncomputable abbrev qz73 := qz428

noncomputable def Ns336p562 := @Enclosure.Real.IsNear.sqrt_image qz73 346092185 33554432 33 33554432 53881642 53881648 16777216 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 346092185 33554432 33 33554432 346092185 33554432 33 33554432 (Ns336p561 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns336p563 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz73) 53881645 16777216 3 16777216 5223948 5223950 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz73) Bool.false 107763290 33554432 6 33554432 53881645 16777216 3 16777216 (Ns336p562 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns336p564 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz73)) Bool.false 10447898 33554432 2 33554432 5223949 16777216 1 16777216 (Ns336p563 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz74 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz421))

noncomputable abbrev qz670 := (@HMul.hMul Real Real Real qz824 qz842 qz842)

noncomputable abbrev qz429 := (@HSub.hSub Real Real Real qz631 (@HSub.hSub Real Real Real qz631 qz670 qz665) qz639)

noncomputable abbrev qz75 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz429))

noncomputable def Ns336p565 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz69) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz74) qz75) Bool.false 15672446465445 

noncomputable def Ns336p566 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz74) qz75 10661637 4194304 695 

noncomputable abbrev qz671 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz74))

noncomputable def Ns336p567 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz74) (@Neg.neg Real Real.instNeg qz671) Bool.true 10661637 4194304 695 16777216 (BSN.inv_eq_neg_inv_neg qz74) 

noncomputable def Ns336p568 := @Enclosure.Real.IsNear.recentre' qz671 Bool.false 85293096 33554432 1390 33554432 10661637 4194304 

noncomputable def Ns336p569 := @Enclosure.Real.IsNear.recentre' qz74 Bool.true 6600182 16777216 65017152 10150215680000 3300091 8388608 1015893 158597120000 

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz349 qz346 qz421)

noncomputable def Ns336p570 := @Enclosure.Real.IsNear.cos_image qz76 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 33137095) qz368) Bool.false 33137095 16777216 13 2097152 Bool.true 6600182 16777216 1 

noncomputable def Ns336p571 := nat_lit 890540488589058970455821991 

noncomputable def Ns336p572 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz69 884279719003555 140737488355328 1 500000000000000 10547865 33554432 33 33554432 9327263098287432660075 4722366482869645213696 Ns336p571 

noncomputable def Ns336p573 := @Enclosure.Real.IsNear.subLit_ff_p qz73 qz1 346092185 33554432 33 33554432 10 1 0 1 10547865 10547865 33554432 33 

noncomputable def Ns336p574 := @Ns336p573 33554432 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 346092185 33554432 33 33554432 346092185 33554432 33 33554432 (Ns336p561 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns336p575 := @Enclosure.Real.IsNear.recentre' qz76 Bool.false 9327263098287432660075 4722366482869645213696 Ns336p571 Ns336p304 33137095 16777216 13 2097152 (@Ns336p572 Ns336p304 RS337to348.d47 (Ns336p574 rfl rfl) rfl) 

noncomputable def Ns336p576 := nat_lit 152427762213933715250853002278712219771084873170314817514573438864831545810074772753232109390625 

noncomputable def Ns336p577 := nat_lit 1752964794883344965249155811613509586910630641501228057496743173424208311620222988525390625 

noncomputable def Ns336p578 := nat_lit 919185144745396976504093855773950784123703474035913323302977402779848247368974934532672134990625 

noncomputable def Ns336p579 := BSN.cos_dyadic_bound_t 33137095 16777216 4 3 16777216 4840000 Ns336p576 Ns336p203 Ns336p577 Ns336p578 Ns336p206 Ns336p577 6600182 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 33137095) (BSN.cosEvenQ 16777216) 0 3 Ns336p576 Ns336p203 Ns336p577 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 33137095) (BSN.cosOddQ 16777216) 0 3 Ns336p578 Ns336p206 Ns336p577 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p580 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz74) 3300091 8388608 1015893 158597120000 42645853 42647243 16777216 (@Enclosure.Real.IsNear.neg qz74 Bool.true 3300091 8388608 1015893 158597120000 (Ns336p569 (@Ns336p570 4840000 (Ns336p575 rfl) (Enclosure.sfrac_false_div 33137095 16777216) (Ns336p579 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns336p581 := Ns336p567 (@Enclosure.Real.IsNear.neg qz671 Bool.false 10661637 4194304 695 16777216 (@Ns336p568 695 16777216 (Ns336p580 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p582 := @Enclosure.Real.IsNear.recentre' qz75 Bool.true 2939970 16777216 

noncomputable abbrev qz77 := (@HMul.hMul Real Real Real qz349 qz346 qz429)

noncomputable def Ns336p583 := @Enclosure.Real.IsNear.cos_image qz77 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 58617635)) qz396) Bool.true 58617635 33554432 

noncomputable def Ns336p584 := nat_lit 276813956725435173633971308045 

noncomputable def Ns336p585 := nat_lit 48668211354524724710499300236813093 

noncomputable def Ns336p586 := @Enclosure.Real.IsNear.recentre' qz77 Bool.true Ns336p584 Ns336p194 Ns336p585 

noncomputable abbrev qz78 := qz429

noncomputable def Ns336p587 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz78 884279719003555 140737488355328 1 500000000000000 313038907007119 

noncomputable abbrev qz430 := (@HSub.hSub Real Real Real qz631 qz670 qz665)

noncomputable abbrev qz79 := qz430

noncomputable def Ns336p588 := @Enclosure.Real.IsNear.subLit_tf qz79 qz26 242670162829455 1125899906842624 1803456435 1125899906842624 1 16 

noncomputable abbrev qz431 := qz670

noncomputable abbrev qz80 := qz431

noncomputable def Ns336p589 := @Enclosure.Real.IsNear.subLit_ff_n qz80 qz69 111257456058225 1125899906842624 696160179 1125899906842624 10547865 33554432 33 33554432 

noncomputable def Ns336p590 := @Enclosure.Real.IsNear.mulLit_ff qz69 qz69 10547865 33554432 33 33554432 10547865 33554432 33 33554432 111257456058225 1125899906842624 

noncomputable def Ns336p591 := nat_lit 380750845367972622098430463386883467031796804890673521203530736306059549093504202583639160840640625 

noncomputable def Ns336p592 := nat_lit 1645657706094531686214178068823925917946996846296905832517543583922744303980727584258056640625 

noncomputable def Ns336p593 := nat_lit 2301390250389919438603298681737791673535414478101249965319669833891950356871342114907199050146240625 

noncomputable def Ns336p594 := BSN.cos_dyadic_bound_t 58617635 33554432 4 3 16777216 4840000 Ns336p591 Ns336p328 Ns336p592 Ns336p593 Ns336p331 Ns336p592 2939970 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 58617635) (BSN.cosEvenQ 33554432) 0 3 Ns336p591 Ns336p328 Ns336p592 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 58617635) (BSN.cosOddQ 33554432) 0 3 Ns336p593 Ns336p331 Ns336p592 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p595 := @Ns336p582 1674314432 162403450880000 1469985 8388608 26161163 2537553920000 (@Ns336p583 339 33554432 Bool.true 2939970 16777216 1 4840000 (@Ns336p586 Ns336p197 58617635 33554432 339 33554432 (@Ns336p587 1125899906842624 1803456435 1125899906842624 Ns336p584 Ns336p194 Ns336p585 Ns336p197 RS337to348.d47 (@Ns336p588 0 1 5008622512113904 313038907007119 1125899906842624 1803456435 1125899906842624 (@Ns336p589 8142659477089875394560 242670162829455 1125899906842624 1803456435 1125899906842624 (@Ns336p590 696160179 1125899906842624 (Ns336p574 rfl rfl) (Ns336p574 rfl rfl) rfl) (Ns336p574 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 58617635 33554432) (BSN.cos_neg_of_bound 58617635 33554432 Bool.true 2939970 16777216 1 4840000 (Ns336p594 rfl rfl)) rfl rfl) 

noncomputable def Ns336p596 := @Ns336p559 149235461725961376211 Ns336p486 (Ns336p560 qz28 (@Enclosure.Real.IsNear.of_eq qz427 (@Inv.inv Real Real.instInv (Real.sqrt qz73)) Bool.false 5223949 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz68 (BSN.t_div_two_pi_nonneg qz67 668442 1000 qz70)) Ns336p564) rfl) (@Ns336p565 35184372088832 1424747447061109 42573090227486720000 (BSN.correction_mk qz69 (BSN.cos_two_pi_p_ne_zero_mk qz67 668442 1000 10 qz70 rfl rfl (@BSN.floor_sqrt_eq_dec qz67 668442 1000 10 qz70 rfl rfl rfl))) (@Ns336p566 16777216 1469985 8388608 26161163 2537553920000 15672446465445 35184372088832 1424747447061109 42573090227486720000 Ns336p581 (Ns336p595 rfl) rfl)) 

noncomputable def Ns336p597 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz67) (hardyZApproximantRS₀ qz67) Bool.false 1577918753636171020447 590295810358705651712 17584938131667578835411 Ns336p486 (@Eq.refl Real (hardyZApproximantRS₀ qz67)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz67) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz67) qz67 10) (@HMul.hMul Real Real Real qz5 qz422 (Zeta.RiemannSiegel.correction qz69))) Bool.false 1577918753636171020447 590295810358705651712 17584938131667578835411 Ns336p486 (BSN.hardyZApproximantRS₀_eq qz67 10 (@BSN.floor_sqrt_eq_dec qz67 668442 1000 10 qz70 rfl rfl rfl)) (@Ns336p488 1577918753636171020447 590295810358705651712 17584938131667578835411 Ns336p486 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz67) qz67 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz67) qz67 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz67) qz67 10)) Bool.false 188696369 67108864 163819 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz67) qz67 10) (Ns336p558 (Ns336p557 rfl rfl rfl rfl) rfl rfl)) (Ns336p596 rfl) rfl rfl)) 

theorem RS337to348.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz67) Bool.false 1577918753636171020447 590295810358705651712 17584938131667578835411 Ns336p486 := Ns336p597 

noncomputable def Ns336p598 := nat_lit 8116567392432202711040000 

noncomputable def Ns336p599 := nat_lit 434972068528482113307101102080 

noncomputable abbrev qz844 := (Enclosure.sfrac Bool.false 669788 1000)

noncomputable abbrev qz672 := qz844

noncomputable abbrev qz432 := qz672

noncomputable abbrev qz81 := qz432

noncomputable abbrev qz845 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 669788 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz673 := qz845

noncomputable abbrev qz433 := qz673

noncomputable abbrev qz82 := qz433

noncomputable abbrev qz846 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 669788 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz674 := qz846

noncomputable abbrev qz434 := qz674

noncomputable abbrev qz83 := qz434

noncomputable abbrev qz435 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz630 qz82 qz8))

noncomputable def Ns336p600 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz81) qz81 10) (@HMul.hMul Real Real Real qz5 qz435 (Zeta.RiemannSiegel.correction qz83)) 350124241 134217728 164143 134217728 161069060816158393107 1180591620717411303424 76389716090322737887 Ns336p598 Ns336p599 

noncomputable def Ns336p601 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz81) qz81 Real.sin BSN.quadSignPos 9 10 669788 1000 199 268435456 134217728 4503599627370496 Bool.false 329735808802 2515 618095470 56 84886744 8 

noncomputable def Ns336p602 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz81) qz81 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 669788 1000 104 154 268435456 134217728 4503599627370496 Bool.false 329735808802 2515 

noncomputable def Ns336p603 := Ns336p602 558195838 56 94906264 8 589812974 56 89478488 8 Bool.true 463833577 123965 Bool.true 284692600 Bool.true 378599474 14148475504056880 1 Bool.false 131098839 Bool.false Bool.false 42873550 Bool.true Bool.true 431774323 

noncomputable def Ns336p604 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz81) qz81 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 669788 1000 17 47 268435456 134217728 4503599627370496 Bool.false 329735808802 2515 

noncomputable def Ns336p605 := Ns336p604 480971758 57 109588312 8 522351262 57 101459064 8 Bool.true 447197226 91952 Bool.false 418520674 Bool.true 310899141 14148475504056880 1 Bool.false 268417129 Bool.true Bool.false 245907982 Bool.false Bool.true 463833577 

noncomputable def Ns336p606 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz81) qz81 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 669788 1000 190 95 268435456 134217728 4503599627370496 Bool.false 329735808802 2515 

noncomputable def Ns336p607 := Ns336p606 372130544 56 134217720 8 432030192 56 120047984 16 Bool.true 532429387 54013 Bool.false 372324626 Bool.false 309714877 14148475504056880 1 Bool.false 49055570 Bool.true Bool.false 245430702 Bool.false Bool.true 447197226 

noncomputable def Ns336p608 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz81) qz81 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 669788 1000 486 313 268435456 134217728 4503599627370496 Bool.false 329735808802 2515 

noncomputable def Ns336p609 := Ns336p608 186065264 56 189812528 16 294906480 56 154981288 8 Bool.true 268435288 2576 Bool.false 186017620 Bool.false 232212328 14148475504056880 1 Bool.false 206521444 Bool.true Bool.false 204315110 Bool.true Bool.true 532429387 

noncomputable def Ns336p610 := nat_lit 4287000221876283350361669165090372423800432521340249 

noncomputable def Ns336p611 := nat_lit 3490014820079488663771898964549585518488190976000 

noncomputable def Ns336p612 := nat_lit 64703632440962987432220327280640000 

noncomputable def Ns336p613 := nat_lit 260026367014608432633571249585567825920 

noncomputable abbrev qz436 := (@Eq.refl Real qz672)

noncomputable abbrev qz84 := qz436

noncomputable def Ns336p614 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz81 669788 1000 1794464859776 16000000 1339576 4000 2000 Ns336p612 Ns336p613 qz84 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns336p615 := nat_lit 44952455446541456903888376064538023546589623314968729354240 

noncomputable abbrev qz437 := (Enclosure.sfrac Bool.false 669788 2000)

noncomputable abbrev qz675 := (Real.log (Enclosure.sfrac Bool.false 1794464859776 16000000))

noncomputable abbrev qz676 := (@Nat.cast Real Real.instNatCast 1339576)

noncomputable abbrev qz85 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 669788 4000) qz675) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz676))))) qz437)

noncomputable abbrev qz438 := (@HSub.hSub Real Real Real qz11 qz85 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 669788 2000) (Real.log Real.pi)))

noncomputable def Ns336p616 := @Enclosure.Real.IsNear.addLit_ft_p qz438 (Enclosure.sfrac Bool.true Ns336p612 Ns336p613) 172876562745818459597 140737488355328000 1160550037393059283 123904000000000000000000 Ns336p612 Ns336p613 0 1 Ns336p615 

noncomputable def Ns336p617 := nat_lit 2900387434524149393446141952000 

noncomputable abbrev qz439 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 669788 2000) (Real.log Real.pi))

noncomputable def Ns336p618 := @Enclosure.Real.IsNear.subLit_ff_p qz85 qz439 226830132315807133133 140737488355328000 529522199192517 121000000000000000000 6431766697167 16777216000 167447 33554432000 Ns336p617 172876562745818459597 140737488355328000 

noncomputable abbrev qz86 := (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 669788 4000) qz675) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz676)))))

noncomputable def Ns336p619 := @Enclosure.Real.IsNear.subLit_ff_p qz86 qz437 54792454548215269673 28147497671065600 529522199192517 121000000000000000000 669788 2000 0 1 90732052926322853253200 226830132315807133133 140737488355328000 529522199192517 121000000000000000000 

noncomputable def Ns336p620 := nat_lit 246763277886057127255322776523767808 

noncomputable def Ns336p621 := nat_lit 56227762144878988424642560 

noncomputable def Ns336p622 := nat_lit 37684699993117281366055026425235512027436230912656586071478650226728063189035644908358817789443228308621263177879347583257282870252413319096267735574773760 

noncomputable def Ns336p623 := nat_lit 902183741760646861325915385285438669028663731750946722937483012990181838297247997236963797474301995795657733070110478151490375810088100560958266825244672 

noncomputable def Ns336p624 := nat_lit 308257706752855526046026151603453330436054039371925973624839364478658184103513904341341623782971781943102908086240835702753571887713573588718059520 

noncomputable def Ns336p625 := BSN.log_dyadic_bound 745888859776 2843040859776 7 6 Ns336p622 134217728 38720000 Ns336p623 Ns336p624 72111668 3588929719552 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 745888859776) (BSN.artanhQ 2843040859776) 0 6 Ns336p623 Ns336p622 Ns336p624 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns336p626 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 669788 4000) qz675 669788 4000 0 1 3272886512852215 281474976710656 195312621 7562500000000000 109607005583512969021 56294995342131200 32704512448587 7562500000000000000 (Enclosure.Real.IsNear.const Bool.false 669788 4000) (BSN.isNear_log_sfrac 1794464859776 16000000 3272886512852215 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1794464859776) qz362)) Bool.false Ns336p621 Ns336p98 1000000619520000 38720000000000000000000 3272886512852215 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1794464859776 16000000 16 3588929719552 2097152000000 72111668 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns336p625 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p627 := BSN.arctan_dyadic_bound_f 1000 1339576 1 0 16777216 4840000 0 1 1 0 1 1 12524 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1339576) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1339576) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz677 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1339576)))

noncomputable def Ns336p628 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz677 884279719003555 562949953421312 1 2000000000000000 12524 16777216 1 4840000 14828701464925298491392 883859483297187 562949953421312 50000000121 242000000000000000 qz16 (Ns336p627 rfl) rfl rfl 

noncomputable def Ns336p629 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 669788 4000) qz675) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz677)) 109607005583512969021 56294995342131200 32704512448587 7562500000000000000 883859483297187 2251799813685248 50000000121 968000000000000000 Ns336p620 54792454548215269673 28147497671065600 529522199192517 121000000000000000000 (Ns336p626 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz677) 1 4 0 1 883859483297187 562949953421312 50000000121 242000000000000000 883859483297187 2251799813685248 50000000121 968000000000000000 qz364 Ns336p628 rfl) 

noncomputable def Ns336p630 := @Ns336p616 Ns336p610 Ns336p611 1160550037393059283 123904000000000000000000 (@Ns336p618 1160550037393059283 123904000000000000000000 (Ns336p619 (Ns336p629 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 669788 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz437 (Real.log Real.pi) 669788 2000 0 1 38410761 33554432 1 67108864 6431766697167 16777216000 167447 33554432000 (Enclosure.Real.IsNear.const Bool.false 669788 2000) RS337to348.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns336p612 Ns336p613) 

noncomputable def Ns336p631 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz81) Bool.false Ns336p610 Ns336p611 1160550037393059283 123904000000000000000000 10304244025 8388608 315 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz81) (@HAdd.hAdd Real Real Real qz365 qz438 (Enclosure.sfrac Bool.true Ns336p612 Ns336p613)) Bool.false Ns336p610 Ns336p611 1160550037393059283 123904000000000000000000 Ns336p614 (Ns336p630 rfl rfl)) 

noncomputable def Ns336p632 := nat_lit 1897624687398957833256960 

noncomputable def Ns336p633 := nat_lit 1208925819614629174706176 

noncomputable def Ns336p634 := nat_lit 3500831131673484872820882504476403020354897013437958067125185291611079909867873889482357629128814718974149223187198316475971397894453334016 

noncomputable def Ns336p635 := nat_lit 2481339277909880428968262591978180995919181329834072882934862959775886643251719904741753757973162782499375021025256516037521199599616 

noncomputable def Ns336p636 := nat_lit 17482466346355891860598809460556743913459641618513563537021327174608491029327443699513395258069050838287376084596690954150599069401591320576 

noncomputable def Ns336p637 := BSN.sin_dyadic_bound_f 107867474946 68719476736 4 3 33554432 9689454 Ns336p634 Ns336p112 Ns336p635 Ns336p636 Ns336p115 Ns336p635 33554411 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107867474946) qz366 0 3 Ns336p634 Ns336p112 Ns336p635 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107867474946) qz367 0 3 Ns336p636 Ns336p115 Ns336p635 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p638 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz81) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10304244025) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false 10304244025 8388608 315 33554432 Bool.true 33554411 33554432 1 4840000 (Ns336p631 rfl) (Enclosure.sfrac_false_div 10304244025 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10304244025) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns336p632) (@Nat.cast Real Real.instNatCast Ns336p633)) 226375608064910080 72057594037927936 Bool.false 33554411 33554432 195 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q1 10304244025 8388608 226375608064910080 72057594037927936 195 Ns336p632 Ns336p633 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554411 33554432 Ns336p632 Ns336p633 107867474946 68719476736 9689454 9680000 (Ns336p637 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p639 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz81) Bool.false Ns336p610 Ns336p611 1160550037393059283 123904000000000000000000 329735808802 268435456 2515 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz81) (@HAdd.hAdd Real Real Real qz365 qz438 (Enclosure.sfrac Bool.true Ns336p612 Ns336p613)) Bool.false Ns336p610 Ns336p611 1160550037393059283 123904000000000000000000 Ns336p614 (Ns336p630 rfl rfl)) 

noncomputable def Ns336p640 := Ns336p609 54013 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 486 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 206521444 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 313 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 204315110 268435456) qz84 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz81) qz81 1) Bool.true 33554411 33554432 24346163 2537553920000 268435288 268435456 2576 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz81) qz81 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz81)) Bool.true 33554411 33554432 24346163 2537553920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz81) qz81) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz81)) Bool.true 33554411 33554432 1558154432 162403450880000 33554411 33554432 24346163 2537553920000 (Ns336p638 rfl rfl) rfl)) rfl) (Ns336p639 rfl) RS337to348.d7 

noncomputable def Ns336p641 := nat_lit 10445872911630341081816891393049185724005367719539556116504457420800000 

noncomputable def Ns336p642 := nat_lit 1433615434425550384234057272535598298339132254004493369369600000000 

noncomputable def Ns336p643 := nat_lit 31334751504022172144682206064602485975419424894110659362774633062400000 

noncomputable def Ns336p644 := BSN.cos_dyadic_bound_f 186017620 268435456 3 2 268435456 134217728 Ns336p641 Ns336p251 Ns336p642 Ns336p643 Ns336p254 Ns336p642 206521444 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 186017620) qz369 0 2 Ns336p641 Ns336p251 Ns336p642 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 186017620) qz370 0 2 Ns336p643 Ns336p254 Ns336p642 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p645 := nat_lit 45662828246764132805794391668375366259523344535383172410460629798748160 

noncomputable def Ns336p646 := nat_lit 8454388082114774862127128067004496475394076792489555638897015259136 

noncomputable def Ns336p647 := nat_lit 119579433541773114379684724733636523399696216706434754175410101924397056 

noncomputable def Ns336p648 := BSN.sin_dyadic_bound_f 232212328 268435456 3 2 268435456 134217728 Ns336p645 Ns336p127 Ns336p646 Ns336p647 Ns336p130 Ns336p646 204315110 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 232212328) qz371 0 2 Ns336p645 Ns336p127 Ns336p646 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 232212328) qz372 0 2 Ns336p647 Ns336p130 Ns336p646 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p649 := nat_lit 10363054995575986137097009301448515436847122432941831408934951124946578036431365616329728542943929857953632256 

noncomputable def Ns336p650 := nat_lit 7096776745431337275283030785246871081837003016574860611873195606420140533517943328106929518999321317376 

noncomputable def Ns336p651 := nat_lit 62777032683459247391163519831542108313586773772257743633191415263868659696962263004408638558566782471441879040 

noncomputable def Ns336p652 := BSN.cos_dyadic_bound_f 372324626 268435456 4 3 268435456 134217728 Ns336p649 Ns336p121 Ns336p650 Ns336p651 Ns336p124 Ns336p650 49055570 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 372324626) qz369 0 3 Ns336p649 Ns336p121 Ns336p650 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 372324626) qz370 0 3 Ns336p651 Ns336p124 Ns336p650 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p653 := nat_lit 144558620978924547614334852278592989407227204122594556185934135346851745 

noncomputable def Ns336p654 := nat_lit 84663561898603866764136279893532896623604792805297270050283831422881 

noncomputable def Ns336p655 := nat_lit 378468837749347504158020773419344490424394936370824784906888942562308001 

noncomputable def Ns336p656 := BSN.sin_dyadic_bound_f 309714877 268435456 3 2 268435456 134217728 Ns336p653 Ns336p127 Ns336p654 Ns336p655 Ns336p130 Ns336p654 245430702 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 309714877) qz371 0 2 Ns336p653 Ns336p127 Ns336p654 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 309714877) qz372 0 2 Ns336p655 Ns336p130 Ns336p654 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p657 := Ns336p607 91952 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 190 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 49055570 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 95 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 245430702 268435456) qz84 rfl rfl (Ns336p640 RS337to348.d9 RS337to348.d11 RS337to348.d13 RS337to348.d17 (Ns336p644 rfl rfl) (Ns336p648 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns336p639 rfl) RS337to348.d19 RS337to348.d21 RS337to348.d23 RS337to348.d25 RS337to348.d17 (Ns336p652 rfl rfl) (Ns336p656 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns336p658 := nat_lit 43006474456841093292416671175158976917734673944308740009144918814266275886576027796285414279210045909642776576 

noncomputable def Ns336p659 := nat_lit 28880385941438611291935142897889471483858183742537402880387737213149718493248240974636929582682693963776 

noncomputable def Ns336p660 := nat_lit 214773018944172646334792144029103026615507451324484754214392827748947438464365748475102490561746896722325671936 

noncomputable def Ns336p661 := BSN.sin_dyadic_bound_f 418520674 268435456 4 3 268435456 134217728 Ns336p658 Ns336p158 Ns336p659 Ns336p660 Ns336p161 Ns336p659 268417129 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 418520674) qz371 0 3 Ns336p658 Ns336p158 Ns336p659 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 418520674) qz372 0 3 Ns336p660 Ns336p161 Ns336p659 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p662 := nat_lit 146783665850022797892841420358205455646750387304733669390199643498064865 

noncomputable def Ns336p663 := nat_lit 87288328436664199605817080173984117886058192731299732249568778365921 

noncomputable def Ns336p664 := nat_lit 384292086599257490539032397094065933360149777295594648836404526377577441 

noncomputable def Ns336p665 := BSN.sin_dyadic_bound_f 310899141 268435456 3 2 268435456 134217728 Ns336p662 Ns336p127 Ns336p663 Ns336p664 Ns336p130 Ns336p663 245907982 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 310899141) qz371 0 2 Ns336p662 Ns336p127 Ns336p663 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 310899141) qz372 0 2 Ns336p664 Ns336p130 Ns336p663 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p666 := Ns336p605 123965 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 17 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268417129 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 47 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 245907982 268435456) qz84 rfl rfl (Ns336p657 rfl rfl) (Ns336p639 rfl) RS337to348.d27 RS337to348.d29 RS337to348.d31 RS337to348.d33 RS337to348.d17 (Ns336p661 rfl rfl) (Ns336p665 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p667 := nat_lit 3537336962789513281038829992220821052037753610297416119482372367942618172675994218685084154137149440000000000 

noncomputable def Ns336p668 := nat_lit 283474595590968296632214071809515550699079256875767440792777251817642677374976000000000000000000000000 

noncomputable def Ns336p669 := nat_lit 21449077055437142879947737539954604902932896155112798780177726183101505901339277875792024110352039936000000000 

noncomputable def Ns336p670 := BSN.cos_dyadic_bound_f 284692600 268435456 4 3 268435456 134217728 Ns336p667 Ns336p121 Ns336p668 Ns336p669 Ns336p124 Ns336p668 131098839 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 284692600) qz369 0 3 Ns336p667 Ns336p121 Ns336p668 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 284692600) qz370 0 3 Ns336p669 Ns336p124 Ns336p668 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p671 := nat_lit 11081200649838604239358246541619481228143212385703122378777034656368758897046548202697283280649174120111149056 

noncomputable def Ns336p672 := nat_lit 8672814849194810666292250813078505983112629809045416731374182898820565987726189157187014436357769138176 

noncomputable def Ns336p673 := nat_lit 67120595389715289055180560155025300746736142046272718635516527641904426640303363189823771681722247487694704640 

noncomputable def Ns336p674 := BSN.cos_dyadic_bound_f 378599474 268435456 4 3 268435456 134217728 Ns336p671 Ns336p121 Ns336p672 Ns336p673 Ns336p124 Ns336p672 42873550 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 378599474) qz369 0 3 Ns336p671 Ns336p121 Ns336p672 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 378599474) qz370 0 3 Ns336p673 Ns336p124 Ns336p672 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz678 := (BSN.cos_quad_nat2 154 rfl)

noncomputable def Ns336p675 := Ns336p603 151476 BSN.abs_quadSignPos (BSN.cos_quad_nat0 104 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131098839 268435456) BSN.abs_quadSignNeg qz678 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 42873550 268435456) qz84 rfl rfl (Ns336p666 rfl) (Ns336p639 rfl) RS337to348.d35 RS337to348.d37 RS337to348.d39 RS337to348.d41 RS337to348.d17 (Ns336p670 rfl rfl) (Ns336p674 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p676 := nat_lit 20370309375324184547253128614497829965695341699992132939074786261994938515219006368137877711359452910253015361 

noncomputable def Ns336p677 := nat_lit 3078448157158883639621584616365699679984383857736033909940728634923488312010986119144195238511834071361 

noncomputable def Ns336p678 := nat_lit 101793254824577367691307913229488180499291046987299180334518494515663502722749527223286008813745501237275033921 

noncomputable def Ns336p679 := BSN.sin_dyadic_bound_f 347291633 268435456 4 3 268435456 134217728 Ns336p676 Ns336p158 Ns336p677 Ns336p678 Ns336p161 Ns336p677 258200235 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 347291633) qz371 0 3 Ns336p676 Ns336p158 Ns336p677 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 347291633) qz372 0 3 Ns336p678 Ns336p161 Ns336p677 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p680 := Ns336p601 Bool.true 431774323 151476 Bool.true 347291633 14148475504056880 1 Bool.false 258200235 Bool.false Bool.true 350124241 164143 BSN.abs_quadSignPos qz373 (BSN.sfrac_eq_quadSignPos_mul Bool.false 258200235 268435456) qz84 rfl (Ns336p675 rfl) (Ns336p639 rfl) RS337to348.d43 RS337to348.d45 RS337to348.d17 (Ns336p679 rfl rfl) rfl 

noncomputable def Ns336p681 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz81) qz81 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz81) qz81 10) 350124241 268435456 164143 268435456 350124241 268435456 164143 268435456 187971520578977792 350124241 134217728 164143 134217728 (Ns336p680 rfl rfl rfl rfl) 

noncomputable def Ns336p682 := @Enclosure.Real.IsNear.mulLit_ff qz435 (Zeta.RiemannSiegel.correction qz83) 5221323 16777216 1 16777216 30848323464409 70368744177664 14589715916213 483785116221440000 161069060816158393107 1180591620717411303424 

noncomputable abbrev qz440 := (@HPow.hPow Real Real Real qz630 qz82 qz8)

noncomputable def Ns336p683 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz440 1 1 0 1 5221323 16777216 1 16777216 5221323 16777216 1 16777216 

noncomputable def Ns336p684 := @Enclosure.Real.IsNear.sqrt_image qz82 894226088791 8388608000 167447 8388608000 173220214 173220248 16777216 (@Enclosure.Real.IsNear.of_eq qz82 (@HMul.hMul Real Real Real qz5 qz81 qz3) Bool.false 894226088791 8388608000 167447 8388608000 (BSN.t_div_two_pi_mk qz81 669788 1000 qz84) (@Enclosure.Real.IsNear.mulLit_ff qz81 qz3 669788 1000 0 1 5340353 33554432 1 33554432 894226088791 8388608000 167447 8388608000 (Enclosure.Real.IsNear.const Bool.false 669788 1000) RS337to348.d48 rfl)) 

noncomputable abbrev qz847 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 669788 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz679 := qz847

noncomputable abbrev qz441 := qz679

noncomputable abbrev qz87 := qz441

noncomputable def Ns336p685 := @Enclosure.Real.IsNear.sqrt_image qz87 173220231 16777216 17 16777216 53908746 53908752 16777216 (@Enclosure.Real.IsNear.recentre' qz87 Bool.false 346440462 33554432 34 33554432 173220231 16777216 17 16777216 (Ns336p684 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns336p686 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz87) 53908749 16777216 3 16777216 5221322 5221324 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz87) Bool.false 107817498 33554432 6 33554432 53908749 16777216 3 16777216 (Ns336p685 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns336p687 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz87)) Bool.false 10442646 33554432 2 33554432 5221323 16777216 1 16777216 (Ns336p686 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz88 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz434))

noncomputable abbrev qz680 := (@HMul.hMul Real Real Real qz824 qz846 qz846)

noncomputable abbrev qz442 := (@HSub.hSub Real Real Real qz631 (@HSub.hSub Real Real Real qz631 qz680 qz674) qz639)

noncomputable abbrev qz89 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz442))

noncomputable def Ns336p688 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz83) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz88) qz89) Bool.false 30848323464409 

noncomputable def Ns336p689 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz88) qz89 9269587 4194304 135 

noncomputable abbrev qz681 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz88))

noncomputable def Ns336p690 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz88) (@Neg.neg Real Real.instNeg qz681) Bool.true 9269587 4194304 135 4194304 (BSN.inv_eq_neg_inv_neg qz88) 

noncomputable def Ns336p691 := @Enclosure.Real.IsNear.recentre' qz681 Bool.false 74156696 33554432 1080 33554432 9269587 4194304 

noncomputable def Ns336p692 := @Enclosure.Real.IsNear.recentre' qz88 Bool.true 15182714 33554432 534657216 81201725440000 7591357 16777216 8354019 1268776960000 

noncomputable abbrev qz90 := (@HMul.hMul Real Real Real qz349 qz346 qz434)

noncomputable def Ns336p693 := @Enclosure.Real.IsNear.cos_image qz90 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 68462479) qz396) Bool.false 68462479 33554432 107 16777216 Bool.true 15182714 33554432 1 

noncomputable def Ns336p694 := nat_lit 458763282000547346280444471 

noncomputable def Ns336p695 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz83 884279719003555 140737488355328 1 500000000000000 5448071 16777216 17 16777216 4817618692991416892405 2361183241434822606848 Ns336p694 

noncomputable def Ns336p696 := @Enclosure.Real.IsNear.subLit_ff_p qz87 qz1 173220231 16777216 17 16777216 10 1 0 1 5448071 5448071 16777216 17 

noncomputable def Ns336p697 := @Ns336p696 16777216 (@Enclosure.Real.IsNear.recentre' qz87 Bool.false 346440462 33554432 34 33554432 173220231 16777216 17 16777216 (Ns336p684 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns336p698 := @Enclosure.Real.IsNear.recentre' qz90 Bool.false 4817618692991416892405 2361183241434822606848 Ns336p694 Ns336p457 68462479 33554432 107 16777216 (@Ns336p695 Ns336p457 RS337to348.d47 (Ns336p697 rfl rfl) rfl) 

noncomputable def Ns336p699 := nat_lit 2270578089951656178352128 

noncomputable def Ns336p700 := nat_lit 1083993227756376928342069723962239584800625 

noncomputable def Ns336p701 := nat_lit 2676089423823674776984286192717803380717649920 

noncomputable def Ns336p702 := nat_lit 18732625966765723438890003349024623665023549440 

noncomputable def Ns336p703 := BSN.sin_dyadic_bound_f 32266855355 68719476736 2 1 33554432 9689454 Ns336p700 Ns336p701 Ns336p700 Ns336p700 Ns336p702 Ns336p700 15182714 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 32266855355) qz366 0 1 Ns336p700 Ns336p701 Ns336p700 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 32266855355) qz367 0 1 Ns336p700 Ns336p702 Ns336p700 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p704 := @Ns336p693 4840000 (Ns336p698 rfl) (Enclosure.sfrac_false_div 68462479 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 68462479) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns336p699) qz413) 226375608064910080 72057594037927936 Bool.false 15182714 33554432 0 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q1 68462479 33554432 226375608064910080 72057594037927936 0 Ns336p699 Ns336p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 15182714 33554432 Ns336p699 Ns336p98 32266855355 68719476736 9689454 9680000 (Ns336p703 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p705 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz88) 7591357 16777216 8354019 1268776960000 37077808 37078888 16777216 (@Enclosure.Real.IsNear.neg qz88 Bool.true 7591357 16777216 8354019 1268776960000 (Ns336p692 (Ns336p704 rfl rfl) rfl)) 

noncomputable def Ns336p706 := Ns336p690 (@Enclosure.Real.IsNear.neg qz681 Bool.false 9269587 4194304 135 4194304 (@Ns336p691 135 4194304 (Ns336p705 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p707 := @Enclosure.Real.IsNear.recentre' qz89 Bool.true 3327907 16777216 

noncomputable abbrev qz91 := (@HMul.hMul Real Real Real qz349 qz346 qz442)

noncomputable def Ns336p708 := @Enclosure.Real.IsNear.cos_image qz91 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 59407429)) qz396) Bool.true 59407429 33554432 

noncomputable def Ns336p709 := nat_lit 70135914059624687949997542605 

noncomputable def Ns336p710 := nat_lit 12695528338418125996673711576922537 

noncomputable def Ns336p711 := @Enclosure.Real.IsNear.recentre' qz91 Bool.true Ns336p709 Ns336p471 Ns336p710 

noncomputable abbrev qz92 := qz442

noncomputable def Ns336p712 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz92 884279719003555 140737488355328 1 500000000000000 79314172373711 

noncomputable abbrev qz443 := (@HSub.hSub Real Real Real qz631 qz680 qz674)

noncomputable abbrev qz93 := qz443

noncomputable def Ns336p713 := @Enclosure.Real.IsNear.subLit_tf qz93 qz26 61721986329295 281474976710656 470447375 281474976710656 1 16 

noncomputable abbrev qz444 := qz680

noncomputable abbrev qz94 := qz444

noncomputable def Ns336p714 := @Enclosure.Real.IsNear.subLit_ff_n qz94 qz83 29681477621041 281474976710656 185234703 281474976710656 5448071 16777216 17 16777216 

noncomputable def Ns336p715 := @Enclosure.Real.IsNear.mulLit_ff qz83 qz83 5448071 16777216 17 16777216 5448071 16777216 17 16777216 29681477621041 281474976710656 

noncomputable def Ns336p716 := nat_lit 401811722955845112813075415136335395990997347568358380374193813376215134981142027002502595152810321 

noncomputable def Ns336p717 := nat_lit 1932364683949812516047012199885566251367602335522718826909011232304388675235659081749480444241 

noncomputable def Ns336p718 := nat_lit 2428198666889936437644232654781490073818153634008994937442345931996398585407376530841812163975549265 

noncomputable def Ns336p719 := BSN.cos_dyadic_bound_t 59407429 33554432 4 3 16777216 4840000 Ns336p716 Ns336p328 Ns336p717 Ns336p718 Ns336p331 Ns336p717 3327907 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 59407429) (BSN.cosEvenQ 33554432) 0 3 Ns336p716 Ns336p328 Ns336p717 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 59407429) (BSN.cosOddQ 33554432) 0 3 Ns336p718 Ns336p331 Ns336p717 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p720 := @Ns336p707 873457216 81201725440000 3327907 16777216 13647769 1268776960000 (@Ns336p708 177 16777216 Bool.true 3327907 16777216 1 4840000 (@Ns336p711 Ns336p474 59407429 33554432 177 16777216 (@Ns336p712 281474976710656 470447375 281474976710656 Ns336p709 Ns336p471 Ns336p710 Ns336p474 RS337to348.d47 (@Ns336p713 0 1 1269026757979376 79314172373711 281474976710656 470447375 281474976710656 (@Ns336p714 1035523096595629342720 61721986329295 281474976710656 470447375 281474976710656 (@Ns336p715 185234703 281474976710656 (Ns336p697 rfl rfl) (Ns336p697 rfl rfl) rfl) (Ns336p697 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 59407429 33554432) (BSN.cos_neg_of_bound 59407429 33554432 Bool.true 3327907 16777216 1 4840000 (Ns336p719 rfl rfl)) rfl rfl) 

noncomputable def Ns336p721 := @Ns336p682 76389716090322737887 Ns336p598 (Ns336p683 qz28 (@Enclosure.Real.IsNear.of_eq qz440 (@Inv.inv Real Real.instInv (Real.sqrt qz87)) Bool.false 5221323 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz82 (BSN.t_div_two_pi_nonneg qz81 669788 1000 qz84)) Ns336p687) rfl) (@Ns336p688 70368744177664 14589715916213 483785116221440000 (BSN.correction_mk qz83 (BSN.cos_two_pi_p_ne_zero_mk qz81 669788 1000 10 qz84 rfl rfl (@BSN.floor_sqrt_eq_dec qz81 669788 1000 10 qz84 rfl rfl rfl))) (@Ns336p689 4194304 3327907 16777216 13647769 1268776960000 30848323464409 70368744177664 14589715916213 483785116221440000 Ns336p706 (Ns336p720 rfl) rfl)) 

noncomputable def Ns336p722 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz81) (hardyZApproximantRS₀ qz81) Bool.true 3240794453982130537235 1180591620717411303424 10002632257582300977887 Ns336p598 (@Eq.refl Real (hardyZApproximantRS₀ qz81)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz81) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz81) qz81 10) (@HMul.hMul Real Real Real qz5 qz435 (Zeta.RiemannSiegel.correction qz83))) Bool.true 3240794453982130537235 1180591620717411303424 10002632257582300977887 Ns336p598 (BSN.hardyZApproximantRS₀_eq qz81 10 (@BSN.floor_sqrt_eq_dec qz81 669788 1000 10 qz84 rfl rfl rfl)) (@Ns336p600 3240794453982130537235 1180591620717411303424 10002632257582300977887 Ns336p598 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz81) qz81 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz81) qz81 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz81) qz81 10)) Bool.true 350124241 134217728 164143 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz81) qz81 10) (Ns336p681 (Ns336p680 rfl rfl rfl rfl) rfl rfl)) (Ns336p721 rfl) rfl rfl)) 

theorem RS337to348.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz81) Bool.true 3240794453982130537235 1180591620717411303424 10002632257582300977887 Ns336p598 := Ns336p722 

noncomputable def Ns336p723 := nat_lit 714257930534033838571520000 

noncomputable def Ns336p724 := nat_lit 6292141974517343345963698225152 

noncomputable abbrev qz848 := (Enclosure.sfrac Bool.false 671134 1000)

noncomputable abbrev qz682 := qz848

noncomputable abbrev qz445 := qz682

noncomputable abbrev qz95 := qz445

noncomputable abbrev qz446 := qz630

noncomputable abbrev qz849 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 671134 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz683 := qz849

noncomputable abbrev qz447 := qz683

noncomputable abbrev qz96 := (@HMul.hMul Real Real Real qz349 qz350 (@HPow.hPow Real Real Real qz446 qz447 qz352))

noncomputable abbrev qz850 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 671134 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz684 := qz850

noncomputable abbrev qz448 := qz684

noncomputable abbrev qz97 := (Zeta.RiemannSiegel.correction qz448)

noncomputable def Ns336p725 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz95) qz95 10) (@HMul.hMul Real Real Real qz5 qz96 qz97) 684233445 134217728 164475 134217728 1268537340577828251021 9444732965739290427392 5838142029563427258603 Ns336p723 Ns336p724 

noncomputable def Ns336p726 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz95) qz95 Real.sin BSN.quadSignPos 9 10 671134 1000 199 268435456 134217728 4503599627370496 Bool.false 330579493253 2520 618095470 56 84886744 8 

noncomputable def Ns336p727 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz95) qz95 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 671134 1000 104 154 268435456 134217728 4503599627370496 Bool.false 330579493253 2520 

noncomputable def Ns336p728 := Ns336p727 558195838 56 94906264 8 589812974 56 89478488 8 Bool.false 562444797 124217 Bool.true 192339747 Bool.true 328803286 14148475504056880 1 Bool.false 202425812 Bool.false Bool.false 91013479 Bool.true Bool.false 603675300 

noncomputable def Ns336p729 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz95) qz95 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 671134 1000 18 47 268435456 134217728 4503599627370496 Bool.false 330579493253 2520 

noncomputable def Ns336p730 := Ns336p729 480971758 57 109588312 8 522351262 57 101459064 8 Bool.false 584729106 92140 Bool.false 193159710 Bool.true 170299489 14148475504056880 1 Bool.false 201886345 Bool.true Bool.false 159103432 Bool.false Bool.false 562444797 

noncomputable def Ns336p731 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz95) qz95 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 671134 1000 191 96 268435456 134217728 4503599627370496 Bool.false 330579493253 2520 

noncomputable def Ns336p732 := Ns336p731 372130544 56 134217720 8 432030192 56 120047984 16 Bool.false 363793938 54125 Bool.false 293463937 Bool.false 150229261 14148475504056880 1 Bool.false 238402885 Bool.false Bool.false 227483545 Bool.false Bool.false 584729106 

noncomputable def Ns336p733 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz95) qz95 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 671134 1000 487 314 268435456 134217728 4503599627370496 Bool.false 330579493253 2520 

noncomputable def Ns336p734 := Ns336p733 186065264 56 189812528 16 294906480 56 154981288 8 Bool.false 268435440 2584 Bool.false 357600797 Bool.false 257295229 14148475504056880 1 Bool.false 260828752 Bool.false Bool.false 154282902 Bool.true Bool.false 363793938 

noncomputable def Ns336p735 := nat_lit 1781781800186410033415055596466078388768167552523833259 

noncomputable def Ns336p736 := nat_lit 1446833272441356744915683854577914855752445879910400 

noncomputable def Ns336p737 := nat_lit 65356389573275758558056872043520000 

noncomputable def Ns336p738 := nat_lit 263177439126840316915274134694830510080 

noncomputable abbrev qz449 := (@Eq.refl Real qz682)

noncomputable abbrev qz98 := qz449

noncomputable def Ns336p739 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz95 671134 1000 1801684383824 16000000 1342268 4000 2000 Ns336p737 Ns336p738 qz98 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns336p740 := nat_lit 36490891267817677484340338615625285401972071475688105144320 

noncomputable abbrev qz450 := (Enclosure.sfrac Bool.false 671134 2000)

noncomputable abbrev qz685 := (Real.log (Enclosure.sfrac Bool.false 1801684383824 16000000))

noncomputable abbrev qz686 := (@Nat.cast Real Real.instNatCast 1342268)

noncomputable abbrev qz99 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 671134 4000) qz685) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz686))))) qz450)

noncomputable abbrev qz451 := (@HSub.hSub Real Real Real qz11 qz99 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 671134 2000) (Real.log Real.pi)))

noncomputable def Ns336p741 := @Enclosure.Real.IsNear.addLit_ft_p qz451 (Enclosure.sfrac Bool.true Ns336p737 Ns336p738) 138655117047118585679 112589990684262400 2325738814059769963 247808000000000000000000 Ns336p737 Ns336p738 0 1 Ns336p740 

noncomputable def Ns336p742 := nat_lit 23262468482047906895510896640000 

noncomputable abbrev qz452 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 671134 2000) (Real.log Real.pi))

noncomputable def Ns336p743 := @Enclosure.Real.IsNear.subLit_ff_p qz99 qz452 909523561967244008587 562949953421312000 530573762343981 121000000000000000000 12889383836487 33554432000 335567 67108864000 Ns336p742 138655117047118585679 112589990684262400 

noncomputable def Ns336p744 := nat_lit 1819047123934488017174000 

noncomputable abbrev qz100 := (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 671134 4000) qz685) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz686)))))

noncomputable def Ns336p745 := @Enclosure.Real.IsNear.subLit_ff_p qz100 qz450 1098430988986973412491 562949953421312000 530573762343981 121000000000000000000 671134 2000 0 1 Ns336p744 909523561967244008587 562949953421312000 530573762343981 121000000000000000000 

noncomputable def Ns336p746 := nat_lit 2473446696346969428024551221145632768 

noncomputable def Ns336p747 := nat_lit 56247178207707696182853632 

noncomputable def Ns336p748 := nat_lit 38849218276851449621803445993224052056482321559520974207105245853202467357596579371314858917737331089137829361451608979662920566291177144215091386525941760 

noncomputable def Ns336p749 := nat_lit 943948159308708614236320481513298421484024215181169836073520027434458878919871250905723356272226693731323046592954236724394487882978636023818304222134272 

noncomputable def Ns336p750 := nat_lit 346030421314367399444856707858650909117208852563892664289763777868196936290225749726095557186780610006673897486931586118180639513176778904981995520 

noncomputable def Ns336p751 := BSN.log_dyadic_bound 753108383824 2850260383824 7 6 Ns336p748 134217728 38720000 Ns336p749 Ns336p750 72650572 3603368767648 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 753108383824) (BSN.artanhQ 2850260383824) 0 6 Ns336p749 Ns336p748 Ns336p750 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns336p752 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 671134 4000) qz685 671134 4000 0 1 3274016676453623 281474976710656 195312621 7562500000000000 1098651954067512909241 562949953421312000 65540470291107 15125000000000000000 (Enclosure.Real.IsNear.const Bool.false 671134 4000) (BSN.isNear_log_sfrac 1801684383824 16000000 3274016676453623 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1801684383824) qz362)) Bool.false Ns336p747 Ns336p98 1000000619520000 38720000000000000000000 3274016676453623 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1801684383824 16000000 16 3603368767648 2097152000000 72650572 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns336p751 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p753 := BSN.arctan_dyadic_bound_f 1000 1342268 1 0 16777216 4840000 0 1 1 0 1 1 12499 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1342268) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1342268) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz687 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1342268)))

noncomputable def Ns336p754 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz687 884279719003555 562949953421312 1 2000000000000000 12499 16777216 1 4840000 14828715538674134024192 883860322157987 562949953421312 50000000121 242000000000000000 qz16 (Ns336p753 rfl) rfl rfl 

noncomputable def Ns336p755 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 671134 4000) qz685) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz687)) 1098651954067512909241 562949953421312000 65540470291107 15125000000000000000 883860322157987 2251799813685248 50000000121 968000000000000000 Ns336p746 1098430988986973412491 562949953421312000 530573762343981 121000000000000000000 (Ns336p752 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz687) 1 4 0 1 883860322157987 562949953421312 50000000121 242000000000000000 883860322157987 2251799813685248 50000000121 968000000000000000 qz364 Ns336p754 rfl) 

noncomputable def Ns336p756 := @Ns336p741 Ns336p735 Ns336p736 2325738814059769963 247808000000000000000000 (@Ns336p743 2325738814059769963 247808000000000000000000 (Ns336p745 (Ns336p755 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 671134 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz450 (Real.log Real.pi) 671134 2000 0 1 38410761 33554432 1 67108864 12889383836487 33554432000 335567 67108864000 (Enclosure.Real.IsNear.const Bool.false 671134 2000) RS337to348.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns336p737 Ns336p738) 

noncomputable def Ns336p757 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz95) Bool.false Ns336p735 Ns336p736 2325738814059769963 247808000000000000000000 2582652291 2097152 79 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz95) (@HAdd.hAdd Real Real Real qz365 qz451 (Enclosure.sfrac Bool.true Ns336p737 Ns336p738)) Bool.false Ns336p735 Ns336p736 2325738814059769963 247808000000000000000000 Ns336p739 (Ns336p756 rfl rfl)) 

noncomputable def Ns336p758 := nat_lit 3513154993454908962539315990512285601125861522188164452137850370316084832022679738079057562935872650318361395724455165192542626341370925056 

noncomputable def Ns336p759 := nat_lit 2507583579719581083627341786290613062587149414908995070032283417287545895491804316562228648613936943251786379743208044911205255417856 

noncomputable def Ns336p760 := nat_lit 17543932954707986092510720903562164331843790073847588410835957567777177227717690797202675830340919398459300025283369479605149115914944188416 

noncomputable def Ns336p761 := BSN.sin_dyadic_bound_f 107962090362 68719476736 4 3 33554432 9689454 Ns336p758 Ns336p112 Ns336p759 Ns336p760 Ns336p115 Ns336p759 33554430 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107962090362) qz366 0 3 Ns336p758 Ns336p112 Ns336p759 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107962090362) qz367 0 3 Ns336p760 Ns336p115 Ns336p759 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p762 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz95) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2582652291) (@Nat.cast Real Real.instNatCast 2097152)) Bool.false 2582652291 2097152 79 8388608 Bool.false 33554430 33554432 1 4840000 (Ns336p757 rfl) (Enclosure.sfrac_false_div 2582652291 2097152) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2582652291) (@Nat.cast Real Real.instNatCast 2097152)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474822294848425502441472) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 33554430 33554432 195 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q3 2582652291 2097152 226375608064910080 72057594037927936 195 474822294848425502441472 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554430 33554432 474822294848425502441472 302231454903657293676544 107962090362 68719476736 9689454 9680000 (Ns336p761 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p763 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz95) Bool.false Ns336p735 Ns336p736 2325738814059769963 247808000000000000000000 330579493253 268435456 2520 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz95) (@HAdd.hAdd Real Real Real qz365 qz451 (Enclosure.sfrac Bool.true Ns336p737 Ns336p738)) Bool.false Ns336p735 Ns336p736 2325738814059769963 247808000000000000000000 Ns336p739 (Ns336p756 rfl rfl)) 

noncomputable def Ns336p764 := Ns336p734 54125 BSN.abs_quadSignPos (BSN.cos_quad_nat3 487 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 260828752 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 314 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 154282902 268435456) qz98 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz95) qz95 1) Bool.false 16777215 16777216 6105447 634388480000 268435440 268435456 2584 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz95) qz95 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz95)) Bool.false 16777215 16777216 6105447 634388480000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz95) qz95) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz95)) Bool.false 33554430 33554432 390748608 40600862720000 16777215 16777216 6105447 634388480000 (Ns336p762 rfl rfl) rfl)) rfl) (Ns336p763 rfl) RS337to348.d7 

noncomputable def Ns336p765 := nat_lit 22901512706872048533240192861392620748640400783074658219162577964913090915472787847937605491165572411255337841 

noncomputable def Ns336p766 := nat_lit 4373022749615594865179580985359199078793993599601091850040027722399730796795300803717845845703643280241 

noncomputable def Ns336p767 := nat_lit 114433899755582337852308000705889336586292302570499572811582346212223993764029923737489338736484624578378118001 

noncomputable def Ns336p768 := BSN.sin_dyadic_bound_f 357600797 268435456 4 3 268435456 134217728 Ns336p765 Ns336p158 Ns336p766 Ns336p767 Ns336p161 Ns336p766 260828752 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 357600797) qz371 0 3 Ns336p765 Ns336p158 Ns336p766 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 357600797) qz372 0 3 Ns336p767 Ns336p161 Ns336p766 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p769 := nat_lit 38248452436874902522982200112486326641424739538579137964594257872283041 

noncomputable def Ns336p770 := nat_lit 19206749209156590769437486989935233623546535420841874285685597267361 

noncomputable def Ns336p771 := nat_lit 114706943812206394387407725363479109457027125544895730145211402422314401 

noncomputable def Ns336p772 := BSN.cos_dyadic_bound_f 257295229 268435456 3 2 268435456 134217728 Ns336p769 Ns336p251 Ns336p770 Ns336p771 Ns336p254 Ns336p770 154282902 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 257295229) qz369 0 2 Ns336p769 Ns336p251 Ns336p770 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 257295229) qz370 0 2 Ns336p771 Ns336p254 Ns336p770 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p773 := nat_lit 116510577938779545711694597133194101654775917414421846344890982715505665 

noncomputable def Ns336p774 := nat_lit 55009527747571434797140455363045285823953450694283148080159936363521 

noncomputable def Ns336p775 := nat_lit 305057688699497980255242860325872954823555287641409329615918029119831041 

noncomputable def Ns336p776 := BSN.sin_dyadic_bound_f 293463937 268435456 3 2 268435456 134217728 Ns336p773 Ns336p127 Ns336p774 Ns336p775 Ns336p130 Ns336p774 238402885 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 293463937) qz371 0 2 Ns336p773 Ns336p127 Ns336p774 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 293463937) qz372 0 2 Ns336p775 Ns336p130 Ns336p774 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p777 := nat_lit 4443367948651639181066836200963670741824467401052390293411016083683361 

noncomputable def Ns336p778 := nat_lit 259439588683122766605342803633224497523899497274767339661974222881 

noncomputable def Ns336p779 := nat_lit 13329584966777551297667297917283745776478354404162621345553724302604321 

noncomputable def Ns336p780 := BSN.cos_dyadic_bound_f 150229261 268435456 3 2 268435456 134217728 Ns336p777 Ns336p251 Ns336p778 Ns336p779 Ns336p254 Ns336p778 227483545 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 150229261) qz369 0 2 Ns336p777 Ns336p251 Ns336p778 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 150229261) qz370 0 2 Ns336p779 Ns336p254 Ns336p778 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p781 := Ns336p732 92140 BSN.abs_quadSignPos (BSN.cos_quad_nat3 191 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 238402885 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 96 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 227483545 268435456) qz98 rfl rfl (Ns336p764 RS337to348.d9 RS337to348.d11 RS337to348.d13 RS337to348.d17 (Ns336p768 rfl rfl) (Ns336p772 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns336p763 rfl) RS337to348.d19 RS337to348.d21 RS337to348.d23 RS337to348.d25 RS337to348.d17 (Ns336p776 rfl rfl) (Ns336p780 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns336p782 := nat_lit 12145188987119561880462115788564237026232658118162369325190066096800000 

noncomputable def Ns336p783 := nat_lit 1937904439390102598684927072890548478540481475206369726096100000000 

noncomputable def Ns336p784 := nat_lit 36431691152479905436188977511546929981740893391536695236118006090400000 

noncomputable def Ns336p785 := BSN.cos_dyadic_bound_f 193159710 268435456 3 2 268435456 134217728 Ns336p782 Ns336p251 Ns336p783 Ns336p784 Ns336p254 Ns336p783 201886345 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 193159710) qz369 0 2 Ns336p782 Ns336p251 Ns336p783 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 193159710) qz370 0 2 Ns336p784 Ns336p254 Ns336p783 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p786 := nat_lit 13207418654170877959457391563098869349848639658660869444398635126911745 

noncomputable def Ns336p787 := nat_lit 707467931299432754442639372966861798909820788282499310536919642881 

noncomputable def Ns336p788 := nat_lit 34589712955701624145547880296750330520976773681883153069779365557728001 

noncomputable def Ns336p789 := BSN.sin_dyadic_bound_f 170299489 268435456 3 2 268435456 134217728 Ns336p786 Ns336p127 Ns336p787 Ns336p788 Ns336p130 Ns336p787 159103432 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 170299489) qz371 0 2 Ns336p786 Ns336p127 Ns336p787 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 170299489) qz372 0 2 Ns336p788 Ns336p130 Ns336p787 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p790 := Ns336p730 124217 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 18 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 201886345 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 47 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 159103432 268435456) qz98 rfl rfl (Ns336p781 rfl rfl) (Ns336p763 rfl) RS337to348.d27 RS337to348.d29 RS337to348.d31 RS337to348.d33 RS337to348.d17 (Ns336p785 rfl rfl) (Ns336p789 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p791 := nat_lit 11940240952801816920672207929391332416533769765027121898057078285614241 

noncomputable def Ns336p792 := nat_lit 1873062735089466730631931128811377012598186320075249430724821990561 

noncomputable def Ns336p793 := nat_lit 35816976732935271828555359925916374495576112922441215195309785212861601 

noncomputable def Ns336p794 := BSN.cos_dyadic_bound_f 192339747 268435456 3 2 268435456 134217728 Ns336p791 Ns336p251 Ns336p792 Ns336p793 Ns336p254 Ns336p792 202425812 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 192339747) qz369 0 2 Ns336p791 Ns336p251 Ns336p792 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 192339747) qz370 0 2 Ns336p793 Ns336p254 Ns336p792 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p795 := nat_lit 6297540715964934423160521667884197874998480214965261939984834161631160883201026042569176568047362073683890176 

noncomputable def Ns336p796 := nat_lit 1596738473600579414550571442479098493474950299860786311957313960169747212671746487390755318575885520896 

noncomputable def Ns336p797 := nat_lit 38170990335755571845462688401790118048539642228750083900937853413190408990832505986641243858643939089499361280 

noncomputable def Ns336p798 := BSN.cos_dyadic_bound_f 328803286 268435456 4 3 268435456 134217728 Ns336p795 Ns336p121 Ns336p796 Ns336p797 Ns336p124 Ns336p796 91013479 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 328803286) qz369 0 3 Ns336p795 Ns336p121 Ns336p796 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 328803286) qz370 0 3 Ns336p797 Ns336p124 Ns336p796 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p799 := Ns336p728 151783 BSN.abs_quadSignPos (BSN.cos_quad_nat0 104 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 202425812 268435456) BSN.abs_quadSignNeg qz678 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 91013479 268435456) qz98 rfl rfl (Ns336p790 rfl) (Ns336p763 rfl) RS337to348.d35 RS337to348.d37 RS337to348.d39 RS337to348.d41 RS337to348.d17 (Ns336p794 rfl rfl) (Ns336p798 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p800 := nat_lit 17752868158373085278505527237690870645714347430420467600765462771269017133693274029141057598587407238122438656 

noncomputable def Ns336p801 := nat_lit 2038447093184042036805067957308352814461993178834703820067470130456160752869703938591297694927480160256 

noncomputable def Ns336p802 := nat_lit 88720057221186693069126163225683873471882446129300639262743814925873488985150280725516717019364250893068271616 

noncomputable def Ns336p803 := BSN.sin_dyadic_bound_f 335563684 268435456 4 3 268435456 134217728 Ns336p800 Ns336p158 Ns336p801 Ns336p802 Ns336p161 Ns336p801 254747224 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 335563684) qz371 0 3 Ns336p800 Ns336p158 Ns336p801 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 335563684) qz372 0 3 Ns336p802 Ns336p161 Ns336p801 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p804 := Ns336p726 Bool.false 603675300 151783 Bool.true 335563684 14148475504056880 1 Bool.false 254747224 Bool.false Bool.false 684233445 164475 BSN.abs_quadSignPos qz373 (BSN.sfrac_eq_quadSignPos_mul Bool.false 254747224 268435456) qz98 rfl (Ns336p799 rfl) (Ns336p763 rfl) RS337to348.d43 RS337to348.d45 RS337to348.d17 (Ns336p803 rfl rfl) rfl 

noncomputable def Ns336p805 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz95) qz95 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz95) qz95 10) 684233445 268435456 164475 268435456 684233445 268435456 164475 268435456 367345033638051840 684233445 134217728 164475 134217728 (Ns336p804 rfl rfl rfl rfl) 

noncomputable def Ns336p806 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz97 5218703 16777216 1 16777216 243075212476707 562949953421312 1115173320161457 42573090227486720000 1268537340577828251021 9444732965739290427392 

noncomputable abbrev qz101 := (@HPow.hPow Real Real Real qz446 qz447 qz352)

noncomputable def Ns336p807 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz101 1 1 0 1 5218703 16777216 1 16777216 5218703 16777216 1 16777216 

noncomputable abbrev qz102 := qz447

noncomputable def Ns336p808 := @Enclosure.Real.IsNear.sqrt_image qz102 1792046235151 16777216000 335567 16777216000 173394178 173394211 16777216 (@Enclosure.Real.IsNear.of_eq qz102 (@HMul.hMul Real Real Real qz5 qz95 qz3) Bool.false 1792046235151 16777216000 335567 16777216000 (BSN.t_div_two_pi_mk qz95 671134 1000 qz98) (@Enclosure.Real.IsNear.mulLit_ff qz95 qz3 671134 1000 0 1 5340353 33554432 1 33554432 1792046235151 16777216000 335567 16777216000 (Enclosure.Real.IsNear.const Bool.false 671134 1000) RS337to348.d48 rfl)) 

noncomputable abbrev qz851 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 671134 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz688 := qz851

noncomputable abbrev qz453 := qz688

noncomputable abbrev qz103 := qz453

noncomputable abbrev qz454 := (@Enclosure.Real.IsNear.recentre' qz103 Bool.false 346788389 33554432 33 33554432 346788389 33554432 33 33554432 (Ns336p808 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns336p809 := @Enclosure.Real.IsNear.sqrt_image qz103 346788389 33554432 33 33554432 53935809 53935815 16777216 qz454 rfl 

noncomputable def Ns336p810 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz103) 13483953 4194304 3 16777216 5218702 5218704 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz103) Bool.false 107871624 33554432 6 33554432 13483953 4194304 3 16777216 (Ns336p809 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns336p811 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz103)) Bool.false 10437406 33554432 2 33554432 5218703 16777216 1 16777216 (Ns336p810 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz852 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 671134 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1)))

noncomputable abbrev qz689 := (Real.cos qz852)

noncomputable abbrev qz455 := qz689

noncomputable abbrev qz104 := (@Inv.inv Real Real.instInv qz455)

noncomputable abbrev qz690 := (@HSub.hSub Real Real Real qz827 (@HMul.hMul Real Real Real qz824 qz850 qz850) qz850)

noncomputable abbrev qz456 := (@HMul.hMul Real Real Real qz627 qz625 (@HSub.hSub Real Real Real qz631 qz690 qz639))

noncomputable abbrev qz105 := (Real.cos qz456)

noncomputable def Ns336p812 := @Enclosure.Real.IsNear.of_eq qz97 (@HMul.hMul Real Real Real qz5 qz104 qz105) Bool.false 243075212476707 

noncomputable def Ns336p813 := @Enclosure.Real.IsNear.mulLit_tt qz104 qz105 65847399 33554432 829 

noncomputable abbrev qz106 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz455))

noncomputable abbrev qz107 := qz455

noncomputable def Ns336p814 := @Enclosure.Real.IsNear.of_eq qz104 (@Neg.neg Real Real.instNeg qz106) Bool.true 65847399 33554432 829 33554432 (BSN.inv_eq_neg_inv_neg qz107) 

noncomputable def Ns336p815 := @Enclosure.Real.IsNear.recentre' qz106 Bool.false 65847399 33554432 829 33554432 65847399 33554432 

noncomputable def Ns336p816 := @Enclosure.Real.IsNear.recentre' qz107 Bool.true 17098624 33554432 65017152 10150215680000 133583 262144 1015893 158597120000 

noncomputable abbrev qz691 := qz852

noncomputable abbrev qz457 := qz691

noncomputable abbrev qz108 := qz457

noncomputable def Ns336p817 := @Enclosure.Real.IsNear.cos_image qz108 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 70648569) qz396) Bool.false 70648569 33554432 13 2097152 Bool.true 17098624 33554432 1 

noncomputable def Ns336p818 := nat_lit 890540488595039317278510759 

noncomputable abbrev qz109 := qz448

noncomputable def Ns336p819 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz109 884279719003555 140737488355328 1 500000000000000 11244069 33554432 33 33554432 9942902175776583665295 4722366482869645213696 Ns336p818 

noncomputable def Ns336p820 := @Enclosure.Real.IsNear.subLit_ff_p qz103 qz1 346788389 33554432 33 33554432 10 1 0 1 11244069 11244069 33554432 33 

noncomputable def Ns336p821 := @Ns336p820 33554432 qz454 qz379 

noncomputable def Ns336p822 := @Enclosure.Real.IsNear.recentre' qz108 Bool.false 9942902175776583665295 4722366482869645213696 Ns336p818 Ns336p304 70648569 33554432 13 2097152 (@Ns336p819 Ns336p304 RS337to348.d47 (Ns336p821 rfl rfl) rfl) 

noncomputable def Ns336p823 := nat_lit 2585626861452403941572608 

noncomputable def Ns336p824 := nat_lit 1822821747553126349788855543377265156640625 

noncomputable def Ns336p825 := BSN.sin_dyadic_bound_f 36743967675 68719476736 2 1 33554432 9689454 Ns336p824 Ns336p701 Ns336p824 Ns336p824 Ns336p702 Ns336p824 17098624 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 36743967675) qz366 0 1 Ns336p824 Ns336p701 Ns336p824 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 36743967675) qz367 0 1 Ns336p824 Ns336p702 Ns336p824 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p826 := @Ns336p817 4840000 (Ns336p822 rfl) (Enclosure.sfrac_false_div 70648569 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 70648569) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns336p823) qz413) 226375608064910080 72057594037927936 Bool.false 17098624 33554432 0 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q1 70648569 33554432 226375608064910080 72057594037927936 0 Ns336p823 Ns336p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 17098624 33554432 Ns336p823 Ns336p98 36743967675 68719476736 9689454 9680000 (Ns336p825 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable abbrev qz110 := (@Neg.neg Real Real.instNeg qz455)

noncomputable def Ns336p827 := @Enclosure.Real.IsNear.inv_image qz110 133583 262144 1015893 158597120000 32923285 32924114 16777216 (@Enclosure.Real.IsNear.neg qz107 Bool.true 133583 262144 1015893 158597120000 (Ns336p816 (Ns336p826 rfl rfl) rfl)) 

noncomputable def Ns336p828 := Ns336p814 (@Enclosure.Real.IsNear.neg qz106 Bool.false 65847399 33554432 829 33554432 (@Ns336p815 829 33554432 (Ns336p827 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p829 := @Enclosure.Real.IsNear.recentre' qz105 Bool.true 3691493 16777216 

noncomputable abbrev qz111 := qz456

noncomputable abbrev qz692 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable def Ns336p830 := @Enclosure.Real.IsNear.cos_image qz111 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1879721)) qz692) Bool.true 1879721 1048576 

noncomputable def Ns336p831 := nat_lit 284055410143123157354569547605 

noncomputable def Ns336p832 := nat_lit 9981641411020844633819426657623849 

noncomputable def Ns336p833 := @Enclosure.Real.IsNear.recentre' qz111 Bool.true Ns336p831 Ns336p194 Ns336p832 

noncomputable abbrev qz458 := (@HSub.hSub Real Real Real qz631 qz690 qz639)

noncomputable abbrev qz112 := qz458

noncomputable def Ns336p834 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz112 884279719003555 140737488355328 1 500000000000000 321228005164711 

noncomputable abbrev qz459 := qz690

noncomputable abbrev qz113 := qz459

noncomputable def Ns336p835 := @Enclosure.Real.IsNear.subLit_tf qz113 qz26 250859260987047 1125899906842624 1849405899 1125899906842624 1 16 

noncomputable abbrev qz693 := (@HMul.hMul Real Real Real qz824 qz850 qz850)

noncomputable abbrev qz460 := qz693

noncomputable abbrev qz114 := qz460

noncomputable def Ns336p836 := @Enclosure.Real.IsNear.subLit_ff_n qz114 qz109 126429087676761 1125899906842624 742109643 1125899906842624 11244069 33554432 33 33554432 

noncomputable def Ns336p837 := @Enclosure.Real.IsNear.mulLit_ff qz109 qz109 11244069 33554432 33 33554432 11244069 33554432 33 33554432 126429087676761 1125899906842624 

noncomputable def Ns336p838 := nat_lit 366405811820613716388655950600297176150885470966384556629389575665331450848257121 

noncomputable def Ns336p839 := nat_lit 846322570984149739285326836131859157750990110577656481930582364989086940895641600 

noncomputable def Ns336p840 := nat_lit 1945900904684810006898348640186756942429318417556396866314419609221291091041 

noncomputable def Ns336p841 := nat_lit 2213798448891561061413711212712619295006468070657169158990423723763480189792724065 

noncomputable def Ns336p842 := nat_lit 77015353959557626274964742087999183355340100062566739855682995214006911621503385600 

noncomputable def Ns336p843 := BSN.cos_dyadic_bound_t 1879721 1048576 4 3 16777216 4840000 Ns336p838 Ns336p839 Ns336p840 Ns336p841 Ns336p842 Ns336p840 3691493 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 1879721) (BSN.cosEvenQ 1048576) 0 3 Ns336p838 Ns336p839 Ns336p840 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 1879721) (BSN.cosOddQ 1048576) 0 3 Ns336p841 Ns336p842 Ns336p840 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p844 := @Ns336p829 429468608 40600862720000 3691493 16777216 6710447 634388480000 (@Ns336p830 87 8388608 Bool.true 3691493 16777216 1 4840000 (@Ns336p833 Ns336p322 1879721 1048576 87 8388608 (@Ns336p834 1125899906842624 1849405899 1125899906842624 Ns336p831 Ns336p194 Ns336p832 Ns336p322 RS337to348.d47 (@Ns336p835 0 1 5139648082635376 321228005164711 1125899906842624 1849405899 1125899906842624 (@Ns336p836 8417440014360121442304 250859260987047 1125899906842624 1849405899 1125899906842624 (@Ns336p837 742109643 1125899906842624 (Ns336p821 rfl rfl) (Ns336p821 rfl rfl) rfl) (Ns336p821 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 1879721 1048576) (BSN.cos_neg_of_bound 1879721 1048576 Bool.true 3691493 16777216 1 4840000 (Ns336p843 rfl rfl)) rfl rfl) 

noncomputable abbrev qz115 := (BSN.correction_mk qz448 (BSN.cos_two_pi_p_ne_zero_mk qz445 671134 1000 10 qz449 rfl rfl (@BSN.floor_sqrt_eq_dec qz445 671134 1000 10 qz449 rfl rfl rfl)))

noncomputable def Ns336p845 := @Ns336p806 5838142029563427258603 Ns336p723 (Ns336p807 qz28 (@Enclosure.Real.IsNear.of_eq qz101 (@Inv.inv Real Real.instInv (Real.sqrt qz103)) Bool.false 5218703 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz102 (BSN.t_div_two_pi_nonneg qz95 671134 1000 qz98)) Ns336p811) rfl) (@Ns336p812 562949953421312 1115173320161457 42573090227486720000 qz115 (@Ns336p813 33554432 3691493 16777216 6710447 634388480000 243075212476707 562949953421312 1115173320161457 42573090227486720000 Ns336p828 (Ns336p844 rfl) rfl)) 

noncomputable def Ns336p846 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz95) (hardyZApproximantRS₀ qz95) Bool.false 46880110908428902521459 9444732965739290427392 881114268925298211258603 Ns336p723 (@Eq.refl Real (hardyZApproximantRS₀ qz95)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz95) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz95) qz95 10) (@HMul.hMul Real Real Real qz5 qz96 qz97)) Bool.false 46880110908428902521459 9444732965739290427392 881114268925298211258603 Ns336p723 (BSN.hardyZApproximantRS₀_eq qz95 10 (@BSN.floor_sqrt_eq_dec qz95 671134 1000 10 qz98 rfl rfl rfl)) (@Ns336p725 46880110908428902521459 9444732965739290427392 881114268925298211258603 Ns336p723 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz95) qz95 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz95) qz95 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz95) qz95 10)) Bool.false 684233445 134217728 164475 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz95) qz95 10) (Ns336p805 (Ns336p804 rfl rfl rfl rfl) rfl rfl)) (Ns336p845 rfl) rfl rfl)) 

theorem RS337to348.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz95) Bool.false 46880110908428902521459 9444732965739290427392 881114268925298211258603 Ns336p723 := Ns336p846 

theorem RS337to348.d57 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal (RS337to348.d3 a b h)) (hardyZApproximantRS a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal (RS337to348.d3 a b h)) 

theorem RS337to348.d58 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

theorem RS337to348.d59 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 qz347 RS337to348.d58 rfl 

theorem RS337to348.d60 : Enclosure.Real.IsNear qz3 Bool.false 85445659 536870912 1 536870912 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 85445659 536870912 1 536870912 85445659 536870912 1 536870912 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 42722829 42722830 268435456 RS337to348.d59 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz694 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 4 1) Real.pi)

noncomputable abbrev qz461 := qz694

theorem RS337to348.d61 : Enclosure.Real.IsNear qz461 Bool.false 884279719003555 70368744177664 1 250000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz324 Real.pi 4 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 70368744177664 1 250000000000000 (Enclosure.Real.IsNear.const Bool.false 4 1) RS337to348.d58 rfl 

noncomputable def Ns336p847 := nat_lit 781950621441006189802102638025 

noncomputable def Ns336p848 := nat_lit 79228162514264337593543950336 

noncomputable def Ns336p849 := nat_lit 26986075409044041160201671 

noncomputable def Ns336p850 := nat_lit 4294967296000000000000000000000000000000 

theorem RS337to348.d62 : Enclosure.Real.IsNear RSCompact.c2 Bool.false Ns336p847 Ns336p848 Ns336p849 Ns336p850 := @Enclosure.Real.IsNear.mulLit_ff Real.pi Real.pi 226375608064910080 72057594037927936 1 1000000000000000 226375608064910080 72057594037927936 1 1000000000000000 Ns336p847 Ns336p848 Ns336p849 Ns336p850 RS337to348.d58 RS337to348.d58 rfl 

noncomputable def Ns336p851 := nat_lit 19807040628566084398385987584 

noncomputable def Ns336p852 := nat_lit 1073741824000000000000000000000000000000 

noncomputable abbrev qz695 := (@HMul.hMul Real Real Real qz824 (Enclosure.sfrac Bool.false 4 1) RSCompact.c2)

noncomputable abbrev qz462 := qz695

noncomputable abbrev qz116 := qz462

theorem RS337to348.d63 : Enclosure.Real.IsNear qz116 Bool.false Ns336p847 Ns336p851 Ns336p849 Ns336p852 := @Enclosure.Real.IsNear.mulLit_ff qz324 RSCompact.c2 4 1 0 1 Ns336p847 Ns336p848 Ns336p849 Ns336p850 Ns336p847 Ns336p851 Ns336p849 Ns336p852 (Enclosure.Real.IsNear.const Bool.false 4 1) RS337to348.d62 rfl 

noncomputable def Ns336p853 := nat_lit 691463075802508163054686763366652189853178875 

noncomputable def Ns336p854 := nat_lit 2787593149816327892691964784081045188247552 

noncomputable def Ns336p855 := nat_lit 2184744797947834540264818678394244808492865883128339 

noncomputable def Ns336p856 := nat_lit 9223372036854775808000000000000000000000000000000000000000000000 

noncomputable def Ns336p857 := nat_lit 22300745198530623141535718272648361505980416 

noncomputable def Ns336p858 := nat_lit 73786976294838206464000000000000000000000000000000000000000000000 

noncomputable def Ns336p859 := @Enclosure.Real.IsNear.mulLit_ff qz335 (@HMul.hMul Real Real Real qz5 RSCompact.c2 Real.pi) 8 1 0 1 Ns336p853 Ns336p857 Ns336p855 Ns336p858 Ns336p853 Ns336p854 Ns336p855 Ns336p856 (Enclosure.Real.IsNear.const Bool.false 8 1) (@Enclosure.Real.IsNear.mulLit_ff RSCompact.c2 Real.pi Ns336p847 Ns336p848 Ns336p849 Ns336p850 226375608064910080 72057594037927936 1 1000000000000000 Ns336p853 Ns336p857 Ns336p855 Ns336p858 RS337to348.d62 RS337to348.d58 rfl) rfl 

noncomputable abbrev qz463 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 8 1) RSCompact.c10)

theorem RS337to348.d64 : Enclosure.Real.IsNear qz463 Bool.false Ns336p853 Ns336p854 Ns336p855 Ns336p856 := Ns336p859 

noncomputable def Ns336p860 := nat_lit 2345851864323018569406307914075 

noncomputable def Ns336p861 := nat_lit 2475880078570760549798248448 

noncomputable def Ns336p862 := nat_lit 80958226227132123480605013 

noncomputable def Ns336p863 := nat_lit 134217728000000000000000000000000000000 

noncomputable abbrev qz464 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 96 1) RSCompact.c2)

noncomputable abbrev qz465 := (Enclosure.sfrac Bool.false 96 1)

noncomputable def Ns336p864 := @Enclosure.Real.IsNear.inv_image qz464 Ns336p860 Ns336p861 Ns336p862 Ns336p863 283314 283315 268435456 (@Enclosure.Real.IsNear.mulLit_ff qz465 RSCompact.c2 96 1 0 1 Ns336p847 Ns336p848 Ns336p849 Ns336p850 Ns336p860 Ns336p861 Ns336p862 Ns336p863 (Enclosure.Real.IsNear.const Bool.false 96 1) RS337to348.d62 rfl) rfl rfl 

noncomputable abbrev qz466 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 96 1) RSCompact.c2))

theorem RS337to348.d65 : Enclosure.Real.IsNear qz466 Bool.false 566629 536870912 1 536870912 := @Enclosure.Real.IsNear.recentre' qz466 Bool.false 566629 536870912 1 536870912 566629 536870912 1 536870912 (Ns336p864 rfl rfl rfl rfl) rfl 

noncomputable def Ns336p865 := nat_lit 220188927217116546699896040115463761739777633032502993167220507182649356300043424262279479178308969042721256708859236259000149788743 

noncomputable def Ns336p866 := nat_lit 44362715105933037753254626946289339254982993206013065202727673289833940924890009968639590497666233249558259375382457149263586525184 

noncomputable def Ns336p867 := nat_lit 18511400786299025074112361007643997766368836230265009637316442768078239540236683650418941539679220535772521040017362450490847553623503944452728342235703514202704610691866108623 

noncomputable def Ns336p868 := nat_lit 14996750634613257809875526448190541538624014605448738453314230717318525511320099007961803873993592508065885499619048161280000000000000000000000000000000000000000000000000000000000 

noncomputable abbrev qz696 := (Zeta.RiemannSiegel.correctionLinear qz109)

noncomputable abbrev qz467 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) qz97 (@HMul.hMul Real Real Real qz5 qz696 (@Inv.inv Real Real.instInv qz103)))

noncomputable def Ns336p869 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz95) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz95) qz95 10) (@HMul.hMul Real Real Real qz5 qz96 qz467)) Bool.false Ns336p865 Ns336p866 Ns336p867 Ns336p868 

noncomputable def Ns336p870 := nat_lit 5969374214465593933750160166285788999233139506888482142747333220203841132742636360998311439689208042490560768944343069995070732217 

noncomputable def Ns336p871 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz95) qz95 10) (@HMul.hMul Real Real Real qz5 qz96 qz467) 684233445 134217728 164475 134217728 Ns336p870 Ns336p866 

noncomputable def Ns336p872 := nat_lit 133869014728464899831380684641217391743624259524592565818569571841714932441405784185669492523898939476862410258386450490847553623503944452728342235703514202704610691866108623 

noncomputable def Ns336p873 := nat_lit 29553257541838745609265944340494403767046281130840301896103860549062877623254314705823227796335936706936382012767844162498219656304765435904 

noncomputable def Ns336p874 := nat_lit 1143842486239510838947945527133042251922199731789389459938098263151561055063420233149560616821690761572475147358326977027639 

noncomputable def Ns336p875 := nat_lit 2644223875160994395807661232131084159313618731857124877138595181097623164945245383300756841758861139390364848100093433217024 

noncomputable def Ns336p876 := nat_lit 818485757121486705559282148073732647170154622761170854254128606735414895990816489395001813720624029190478825833152309687844378277488829216612988123253351170332690494409 

noncomputable def Ns336p877 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz467 5218703 16777216 1 16777216 Ns336p874 Ns336p875 Ns336p876 

noncomputable def Ns336p878 := nat_lit 28604031819559589023352673431759913518188504420182682901981793818127680800094793334888084171282944694644709586370560000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns336p879 := nat_lit 2097511602823341091454476729111763677303080729850015981246696239284593514917154295084025632061024605554005003007899819575 

noncomputable def Ns336p880 := nat_lit 69222479220474975183386301613491315793951853974820017837171921672804505265849719705960939411412575241249912308416309687844378277488829216612988123253351170332690494409 

noncomputable abbrev qz468 := (@HMul.hMul Real Real Real qz5 qz696 (@Inv.inv Real Real.instInv qz103))

noncomputable def Ns336p881 := @Enclosure.Real.IsNear.addLit_ff qz97 qz468 243075212476707 562949953421312 1115173320161457 42573090227486720000 Ns336p879 Ns336p875 Ns336p880 Ns336p878 

noncomputable def Ns336p882 := nat_lit 643926074349850339091277294524943186394092795909295215770499052295992983269493323501673896479129506202139268438660895160172910096435642368 

noncomputable def Ns336p883 := nat_lit 5168436129382282505413526145394914822433674928356916995613189330742583772351432727130321813910284343862358969639825 

noncomputable def Ns336p884 := nat_lit 630432099142311667396464641602297820881275828327447146687172694467931548343955369782628260078158650252906047844909056 

noncomputable def Ns336p885 := nat_lit 11724293031099722716573743603199308794975810811850656296878267237036604254550789352931080254206575374213408757890031137518871073602949236120605436052324642519176403 

noncomputable def Ns336p886 := nat_lit 468856617830925403918146204574941171258797569009675848367511826752728952170972118800534197515416728915410944000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns336p887 := @Enclosure.Real.IsNear.mulLit_ff qz696 (@Inv.inv Real Real.instInv qz103) Ns336p883 Ns336p884 Ns336p885 Ns336p886 405831 4194304 1 16777216 Ns336p879 

noncomputable def Ns336p888 := nat_lit 9121375943310848024745514517250113958928461000684604910114359361668011648453278471681332607244395087195252925 

noncomputable def Ns336p889 := nat_lit 1174271291386916613944740298394668513687841274454159935353645485766104512557304221731849499192384351515967488 

noncomputable def Ns336p890 := nat_lit 206792958404825520823110761735869810491110090212079180210624904108900341780797242343087915329938112734216295206148065405220229797673666719838113975885117743481 

noncomputable def Ns336p891 := nat_lit 8733135048876058383251469667534179450176610965461951650073972097648846957291888423273976845953925120000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns336p892 := @Enclosure.Real.IsNear.mulLit_tf (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz109) qz466 Ns336p888 Ns336p889 Ns336p890 Ns336p891 566629 536870912 1 536870912 Ns336p883 

noncomputable abbrev qz853 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 671134 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1)))

noncomputable abbrev qz697 := (@HMul.hMul Real Real Real qz824 qz822 (@HSub.hSub Real Real Real qz827 qz853 qz830))

noncomputable abbrev qz469 := (@HMul.hMul Real Real Real qz627 qz697 qz697)

noncomputable abbrev qz470 := qz697

noncomputable abbrev qz117 := (@HMul.hMul Real Real Real qz349 qz469 qz470)

noncomputable abbrev qz118 := (Real.sin qz456)

noncomputable abbrev qz119 := (@HMul.hMul Real Real Real qz349 qz320 qz470)

noncomputable abbrev qz471 := (@HMul.hMul Real Real Real qz5 qz119 qz694)

noncomputable def Ns336p893 := @HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 qz117 qz118) (@HMul.hMul Real Real Real qz5 qz471 qz105) 

noncomputable abbrev qz698 := (Real.sin qz852)

noncomputable abbrev qz472 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz627 qz625 qz698))

noncomputable abbrev qz120 := (@HMul.hMul Real Real Real qz349 qz320 qz472)

noncomputable abbrev qz473 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz627 qz695 qz689))

noncomputable abbrev qz121 := (@HMul.hMul Real Real Real qz349 qz320 qz473)

noncomputable abbrev qz474 := qz698

noncomputable abbrev qz122 := qz474

noncomputable abbrev qz475 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 8 1) RSCompact.c9)

noncomputable def Ns336p894 := @HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns336p893 (@HMul.hMul Real Real Real qz5 qz120 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz109))) (@HMul.hMul Real Real Real qz5 qz121 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz109))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz475 qz122) qz97) 

noncomputable abbrev qz123 := (BSN.cos_two_pi_p_ne_zero_mk qz445 671134 1000 10 qz449 rfl rfl (@BSN.floor_sqrt_eq_dec qz445 671134 1000 10 qz449 rfl rfl rfl))

noncomputable def Ns336p895 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz109) (@HMul.hMul Real Real Real qz5 qz104 Ns336p894) Bool.true Ns336p888 Ns336p889 Ns336p890 Ns336p891 (BSN.iteratedDeriv_three_correction_mk qz109 qz123) 

noncomputable def Ns336p896 := nat_lit 17315494449289326819918507156106473670642349912091855483656963332660943594299234709054519261991981275 

noncomputable def Ns336p897 := nat_lit 4374501449566023848745004454235242730706338861786424872851541212819905998398751846447026354046107648 

noncomputable def Ns336p898 := nat_lit 392462319622541713569014684502820618779661291981603786581650360164418734982892282050054249050599723875826273081205634773994520068992159139307367691701 

noncomputable def Ns336p899 := @Enclosure.Real.IsNear.mulLit_tf qz104 Ns336p894 526775367 268435456 207 134217728 Ns336p896 Ns336p897 Ns336p898 

noncomputable def Ns336p900 := nat_lit 32533463272735693988395741833501232602360140403590916283704236513558205058022917893804523520000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns336p901 := @Enclosure.Real.IsNear.of_eq qz104 (@Neg.neg Real Real.instNeg qz106) Bool.true 526775367 268435456 207 134217728 (BSN.inv_eq_neg_inv_neg qz107) 

noncomputable def Ns336p902 := @Enclosure.Real.IsNear.recentre' qz106 Bool.false 1053550734 536870912 828 536870912 526775367 268435456 

noncomputable def Ns336p903 := @Enclosure.Real.IsNear.recentre' qz107 Bool.true 273579968 536870912 1040274432 2598455214080000 4274687 8388608 1015893 2537553920000 

noncomputable abbrev qz476 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1130379399) (@Nat.cast Real Real.instNatCast 536870912))

noncomputable def Ns336p904 := @Enclosure.Real.IsNear.cos_image qz108 qz476 Bool.false 1130379399 536870912 13 33554432 Bool.true 273579968 536870912 1 

noncomputable def Ns336p905 := nat_lit 890540490043829711473659559 

noncomputable def Ns336p906 := nat_lit 2305843009213693952000000000000000 

noncomputable def Ns336p907 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz109 884279719003555 140737488355328 1 500000000000000 179905469 536870912 33 536870912 159086757574522774942295 75557863725914323419136 Ns336p905 

noncomputable def Ns336p908 := @Enclosure.Real.IsNear.subLit_ff_p qz103 qz1 5548614589 536870912 33 536870912 10 1 0 1 179905469 179905469 536870912 33 

noncomputable def Ns336p909 := @Enclosure.Real.IsNear.sqrt_image qz102 28672743453653 268435456000 335567 268435456000 2774307278 2774307311 268435456 (@Enclosure.Real.IsNear.of_eq qz102 (@HMul.hMul Real Real Real qz5 qz95 qz3) Bool.false 28672743453653 268435456000 335567 268435456000 (BSN.t_div_two_pi_mk qz95 671134 1000 qz98) (@Enclosure.Real.IsNear.mulLit_ff qz95 qz3 671134 1000 0 1 85445659 536870912 1 536870912 28672743453653 268435456000 335567 268435456000 (Enclosure.Real.IsNear.const Bool.false 671134 1000) RS337to348.d60 rfl)) 

noncomputable def Ns336p910 := @Ns336p908 536870912 (@Enclosure.Real.IsNear.recentre' qz103 Bool.false 5548614589 536870912 33 536870912 5548614589 536870912 33 536870912 (Ns336p909 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns336p911 := @Enclosure.Real.IsNear.recentre' qz108 Bool.false 159086757574522774942295 75557863725914323419136 Ns336p905 Ns336p906 1130379399 536870912 13 33554432 (@Ns336p907 Ns336p906 RS337to348.d59 (Ns336p910 rfl rfl) rfl) 

noncomputable def Ns336p912 := nat_lit 41370360527595097154387968 

noncomputable def Ns336p913 := nat_lit 77371252455336267181195264 

noncomputable def Ns336p914 := nat_lit 527996267607946324403585839614318493284010324606131272227395713838169457661593937275034787725250465 

noncomputable def Ns336p915 := nat_lit 775106975594979850699505476734807071347029417072782157158382458646527094091278842792332482107544698880 

noncomputable def Ns336p916 := nat_lit 14271710933293807072863324347538206928857007479905058138568767315070606566928906389814136344481 

noncomputable def Ns336p917 := nat_lit 1382824260965015040607463991702842896742142224527757295263335853476695608131637665109983792583479201 

noncomputable def Ns336p918 := nat_lit 14210294552574630596157600406804796308028872646334339547903678408519663391673445451192762171971652812800 

noncomputable def Ns336p919 := BSN.sin_dyadic_bound_f 587908182973 1099511627776 3 2 536870912 155031251 Ns336p914 Ns336p915 Ns336p916 Ns336p917 Ns336p918 Ns336p916 273579968 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 587908182973) (BSN.sinEvenQ 1099511627776) 0 2 Ns336p914 Ns336p915 Ns336p916 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 587908182973) (BSN.sinOddQ 1099511627776) 0 2 Ns336p917 Ns336p918 Ns336p916 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz699 := (@Nat.cast Real Real.instNatCast Ns336p913)

noncomputable def Ns336p920 := @Ns336p904 77440000 (Ns336p911 rfl) (Enclosure.sfrac_false_div 1130379399 536870912) (BSN.cos_reduce1 qz476 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns336p912) qz699) 226375608064910080 72057594037927936 Bool.false 273579968 536870912 0 1000000000000000 154880000 77440000 (BSN.sin_reduce_arg_pos_rat_q1 1130379399 536870912 226375608064910080 72057594037927936 0 Ns336p912 Ns336p913 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 273579968 536870912 Ns336p912 Ns336p913 587908182973 1099511627776 155031251 154880000 (Ns336p919 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p921 := @Enclosure.Real.IsNear.inv_image qz110 4274687 8388608 1015893 2537553920000 526774953 526775781 268435456 (@Enclosure.Real.IsNear.neg qz107 Bool.true 4274687 8388608 1015893 2537553920000 (Ns336p903 (Ns336p920 rfl rfl) rfl)) 

noncomputable def Ns336p922 := Ns336p901 (@Enclosure.Real.IsNear.neg qz106 Bool.false 526775367 268435456 207 134217728 (@Ns336p902 207 134217728 (Ns336p921 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p923 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns336p893 (@HMul.hMul Real Real Real qz5 qz120 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz109))) (@HMul.hMul Real Real Real qz5 qz121 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz109))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz475 qz122) qz97) 

noncomputable def Ns336p924 := nat_lit 420450038941564796155337279173268732245975878292814975663360866596638329899094342383677700154266669275 

noncomputable def Ns336p925 := nat_lit 379728107607937301747433529463213683945430827937376776430448909129430188551266255299760854115122859891144524819034037027066171844437746232401767691701 

noncomputable def Ns336p926 := nat_lit 621127112683665401858028942777782184625288444271626548066888764114625 

noncomputable def Ns336p927 := nat_lit 6739986666787659948666753771754907668409286105635143120275902562304 

noncomputable def Ns336p928 := nat_lit 3430613351928529716005960916576914081119225810495079935481405961879641012472862402137244443282440557812783 

noncomputable def Ns336p929 := nat_lit 8764557505397452646572093290823311233344515424957077913600000000000000000000000000000000000000000000000000000 

noncomputable def Ns336p930 := nat_lit 116706201717045797411433612472580056196525010812522479535911814352822999305557994975346558173976415190968945099123702782628977680252843174973802090599588712874088857600 

noncomputable def Ns336p931 := nat_lit 258329276546352190172081509993742807813066083433060875444282161577938598407339355039548698656183341275 

noncomputable def Ns336p932 := @Enclosure.Real.IsNear.subLit_ft (@HSub.hSub Real Real Real qz11 Ns336p893 (@HMul.hMul Real Real Real qz5 qz120 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 2 Zeta.RiemannSiegel.correction qz109))) (@HMul.hMul Real Real Real qz5 qz121 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz109)) Ns336p931 Ns336p897 

noncomputable def Ns336p933 := nat_lit 331463581021563960435032616424072643340099100182961735549816530677647904382488490953120693062451451384754241766614708798275411043785512247466568971701 

noncomputable def Ns336p934 := nat_lit 562469384940466492148385711720169359676239194608373187716644451476440581440801408875 

noncomputable def Ns336p935 := nat_lit 15177100720513508366558296147058741458143803430094840009779784451085189728165691392 

noncomputable def Ns336p936 := nat_lit 8856923750218957462935441567797503204941020132667068409775851649458018389710070440818380405868305653005795007768511857555900617 

noncomputable def Ns336p937 := nat_lit 5970148759700506823160011489321947991977411651292549890649549109588918272000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns336p938 := nat_lit 6381212588959955718372077596312081641539450444273879779233145874918879238525183754683766816026691464013797160016488020109437825552471911258214134203719009527888134837922266371378380800 

noncomputable def Ns336p939 := nat_lit 61579107528308207967361669133512269528368254139765698312605715928166933955025 

noncomputable def Ns336p940 := nat_lit 7237005577332262213973186563042994240829374041602535252466099000494570602496 

noncomputable def Ns336p941 := nat_lit 9143983071038363300356472424794658432597477431940193214281728038028082153854962147137534234625088055956929 

noncomputable def Ns336p942 := nat_lit 124441282147416206937969544430899631939319399838539477165738557440000000000000000000000000000000000000000000000 

noncomputable def Ns336p943 := @Enclosure.Real.IsNear.subLit_tt_p Ns336p893 (@HMul.hMul Real Real Real qz5 qz120 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 2 Zeta.RiemannSiegel.correction qz109)) Ns336p939 Ns336p940 Ns336p941 Ns336p942 

noncomputable def Ns336p944 := nat_lit 295551563066250881192397497216117127570307519118375824122724679125615489677593378685875589482170208475 

noncomputable def Ns336p945 := nat_lit 329073012294895466626036865954205564304488150319888606886378662461761754373651458971307381887134681418477021335254529919905087224912680247466568971701 

noncomputable def Ns336p946 := nat_lit 1869530415154159156640901034082798257843903237360363852984745256453191586960292334716187376412104371670718892893810640872601590951710029221794552913524179287257565650215134822400 

noncomputable def Ns336p947 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz5 qz117 qz118) (@HMul.hMul Real Real Real qz5 qz471 qz105) 

noncomputable def Ns336p948 := nat_lit 62816557450080741311599096451055640540542117480399409153134598916995989667375 

noncomputable def Ns336p949 := nat_lit 1937855738092470734556242898364997774811956502700924388231907513426732282053936398616785260545088055956929 

noncomputable def Ns336p950 := nat_lit 3066589902513175702264573854365058815073772575 

noncomputable def Ns336p951 := nat_lit 178405961588244985132285746181186892047843328 

noncomputable def Ns336p952 := nat_lit 291053165107485303673401203956198229513420806948571490251942816271 

noncomputable def Ns336p953 := nat_lit 5026143359061713144417520446685052928000000000000000000000000000000000 

noncomputable def Ns336p954 := nat_lit 10986079892333761739054102276019633816537140839979929777040543723960850266362981554383159308376716395956362592264598323200 

noncomputable def Ns336p955 := nat_lit 479777851216314896816553701643955801258998723908859798556762567261625 

noncomputable def Ns336p956 := nat_lit 53919893334301279589334030174039261347274288845081144962207220498432 

noncomputable def Ns336p957 := @Enclosure.Real.IsNear.mulLit_tt qz117 qz118 Ns336p955 Ns336p956 

noncomputable def Ns336p958 := nat_lit 121990309613456085264543922566055314173954160708458420822279721577774882466530999272235875407 

noncomputable def Ns336p959 := nat_lit 12259964326927110866866776217202473468949912977468817408000000000000000000000000000000000000000000 

noncomputable def Ns336p960 := nat_lit 6128583816458562499026734340933859624661326225 

noncomputable def Ns336p961 := nat_lit 1427247692705959881058285969449495136382746624 

noncomputable def Ns336p962 := nat_lit 170205609001202301777821455912636212422914991123073308834799 

noncomputable def Ns336p963 := nat_lit 53169119831396634916152282411213783040000000000000000000000000000 

noncomputable abbrev qz124 := qz469

noncomputable abbrev qz125 := qz470

noncomputable def Ns336p964 := @Enclosure.Real.IsNear.mulLit_ft qz124 qz125 Ns336p960 Ns336p961 Ns336p962 Ns336p963 

noncomputable def Ns336p965 := nat_lit 178108097851784059556237243 

noncomputable def Ns336p966 := nat_lit 230584300921369395200000000000000 

noncomputable def Ns336p967 := @Enclosure.Real.IsNear.mulLit_tt qz125 qz125 78285272027748377103785 37778931862957161709568 Ns336p965 Ns336p966 78285272027748377103785 37778931862957161709568 

noncomputable abbrev qz700 := (@HSub.hSub Real Real Real qz827 qz853 qz830)

noncomputable abbrev qz477 := qz700

noncomputable abbrev qz126 := qz477

noncomputable def Ns336p968 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz126 884279719003555 140737488355328 1 500000000000000 88529987 268435456 33 268435456 

noncomputable abbrev qz701 := qz853

noncomputable abbrev qz478 := qz701

noncomputable abbrev qz127 := qz478

noncomputable abbrev qz128 := qz384

noncomputable def Ns336p969 := @Enclosure.Real.IsNear.subLit_ff_n qz127 qz128 179905469 268435456 33 268435456 1 1 0 1 88529987 

noncomputable def Ns336p970 := @Enclosure.Real.IsNear.mulLit_ff qz0 qz109 2 1 0 1 179905469 536870912 33 536870912 179905469 268435456 33 

noncomputable def Ns336p971 := @Enclosure.Real.IsNear.recentre' qz118 Bool.true 261856846 268435456 

noncomputable abbrev qz479 := (@Nat.cast Real Real.instNatCast 536870912)

noncomputable def Ns336p972 := @Enclosure.Real.IsNear.sin_image qz111 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 962417921)) qz479) Bool.true 962417921 536870912 

noncomputable def Ns336p973 := nat_lit 72718242145005916704649338564805 

noncomputable def Ns336p974 := nat_lit 40564819207303340847894502572032 

noncomputable def Ns336p975 := nat_lit 159706304564184307164014951821337401 

noncomputable def Ns336p976 := @Enclosure.Real.IsNear.recentre' qz111 Bool.true Ns336p973 Ns336p974 Ns336p975 

noncomputable def Ns336p977 := nat_lit 247588007857076054979824844800000000000000 

noncomputable def Ns336p978 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz112 884279719003555 140737488355328 1 500000000000000 82234433949189751 

noncomputable def Ns336p979 := @Enclosure.Real.IsNear.subLit_tf qz113 qz26 64220035439707767 288230376151711744 29590502139 288230376151711744 1 16 

noncomputable def Ns336p980 := @Enclosure.Real.IsNear.subLit_ff_n qz114 qz109 32365977776109961 288230376151711744 11873762043 288230376151711744 179905469 536870912 33 536870912 

noncomputable def Ns336p981 := nat_lit 34477868995188229882773504 

noncomputable def Ns336p982 := @Enclosure.Real.IsNear.mulLit_ff qz109 qz109 179905469 536870912 33 536870912 179905469 536870912 33 536870912 32365977776109961 288230376151711744 

noncomputable def Ns336p983 := nat_lit 308314789447978193121828610852961610552667106290908268516140342918493644535115758403207425442043477128486130416641 

noncomputable def Ns336p984 := nat_lit 3570415896635346974072005805030179415937144689025665314440334861177556999349704385084003346650664335197480996044800 

noncomputable def Ns336p985 := nat_lit 631487002042808873400907340347524545165428512599630769885509034920197760514436975434731490933822604304317441 

noncomputable def Ns336p986 := nat_lit 1538328080210868601745025112472209078687087069824878783533805194933795598224623416261499811734614239076375359257601 

noncomputable def Ns336p987 := nat_lit 124964556382237144092520203176056279557800064115898286005411720141214494977239653477940117132773251731911834861568000 

noncomputable def Ns336p988 := BSN.sin_dyadic_bound_f 962417921 536870912 4 3 268435456 77440000 Ns336p983 Ns336p984 Ns336p985 Ns336p986 Ns336p987 Ns336p985 261856846 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 962417921) (BSN.sinEvenQ 536870912) 0 3 Ns336p983 Ns336p984 Ns336p985 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 962417921) (BSN.sinOddQ 536870912) 0 3 Ns336p986 Ns336p987 Ns336p985 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p989 := @Ns336p971 27408550912 41575283425280000 130928423 134217728 26766163 40600862720000 (@Ns336p972 347 536870912 Bool.true 261856846 268435456 1 77440000 (@Ns336p976 Ns336p977 962417921 536870912 347 536870912 (@Ns336p978 288230376151711744 29590502139 288230376151711744 Ns336p973 Ns336p974 Ns336p975 Ns336p977 RS337to348.d59 (@Ns336p979 0 1 1315750943187036016 82234433949189751 288230376151711744 29590502139 288230376151711744 (@Ns336p980 Ns336p981 64220035439707767 288230376151711744 29590502139 288230376151711744 (@Ns336p982 11873762043 288230376151711744 (Ns336p910 rfl rfl) (Ns336p910 rfl rfl) rfl) (Ns336p910 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 962417921 536870912) (BSN.sin_neg_of_bound 962417921 536870912 Bool.false 261856846 268435456 1 77440000 (Ns336p988 rfl rfl)) rfl rfl) 

noncomputable def Ns336p990 := nat_lit 207678235052442597750299037351056867025 

noncomputable def Ns336p991 := nat_lit 2658455991569831745807614120560689152 

noncomputable def Ns336p992 := nat_lit 14419315691082129776089020515477413078940757909713943 

noncomputable def Ns336p993 := @Enclosure.Real.IsNear.mulLit_tt qz471 qz105 Ns336p990 Ns336p991 Ns336p992 

noncomputable def Ns336p994 := nat_lit 495176015714152109959649689600000000000000000000000000000 

noncomputable def Ns336p995 := nat_lit 534324293555352178668711729 

noncomputable def Ns336p996 := @Enclosure.Real.IsNear.mulLit_tf qz119 qz461 234855816083245131311355 37778931862957161709568 Ns336p995 Ns336p966 884279719003555 

noncomputable def Ns336p997 := @Enclosure.Real.IsNear.mulLit_ft qz320 qz125 3 1 0 1 78285272027748377103785 37778931862957161709568 Ns336p965 

noncomputable def Ns336p998 := @Enclosure.Real.IsNear.recentre' qz105 Bool.true 59064252 268435456 

noncomputable def Ns336p999 := @Enclosure.Real.IsNear.cos_image qz111 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 962417921)) qz479) Bool.true 962417921 536870912 

noncomputable def Ns336p1000 := nat_lit 118905866466482970475981673690005660668924606928273230340183742466047211280083087890711642398862124904341828664321 

noncomputable def Ns336p1001 := nat_lit 274647376664257459544000446540783031995164976078897331880025758552119769180746491160307949742358795015190845849600 

noncomputable def Ns336p1002 := nat_lit 718420971579326421647321541609596651585020985897623527577677787005869839095458728842454238960732222445253538479105 

noncomputable def Ns336p1003 := nat_lit 24992911276447428818504040635211255911560012823179657201082344028242898995447930695588023426554650346382366972313600 

noncomputable def Ns336p1004 := BSN.cos_dyadic_bound_t 962417921 536870912 4 3 268435456 77440000 Ns336p1000 Ns336p1001 Ns336p985 Ns336p1002 Ns336p1003 Ns336p985 59064252 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 962417921) (BSN.cosEvenQ 536870912) 0 3 Ns336p1000 Ns336p1001 Ns336p985 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 962417921) (BSN.cosOddQ 536870912) 0 3 Ns336p1002 Ns336p1003 Ns336p985 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1005 := @Ns336p998 27408550912 41575283425280000 14766063 67108864 26766163 40600862720000 (@Ns336p999 347 536870912 Bool.true 59064252 268435456 1 77440000 (@Ns336p976 Ns336p977 962417921 536870912 347 536870912 (@Ns336p978 288230376151711744 29590502139 288230376151711744 Ns336p973 Ns336p974 Ns336p975 Ns336p977 RS337to348.d59 (@Ns336p979 0 1 1315750943187036016 82234433949189751 288230376151711744 29590502139 288230376151711744 (@Ns336p980 Ns336p981 64220035439707767 288230376151711744 29590502139 288230376151711744 (@Ns336p982 11873762043 288230376151711744 (Ns336p910 rfl rfl) (Ns336p910 rfl rfl) rfl) (Ns336p910 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 962417921 536870912) (BSN.cos_neg_of_bound 962417921 536870912 Bool.true 59064252 268435456 1 77440000 (Ns336p1004 rfl rfl)) rfl rfl) 

noncomputable abbrev qz129 := (@Ns336p968 78285272027748377103785 37778931862957161709568 Ns336p965 Ns336p966 RS337to348.d59 (@Ns336p969 88529987 268435456 33 268435456 (@Ns336p970 268435456 qz347 (Ns336p910 rfl rfl) rfl) qz642 rfl rfl) rfl)

noncomputable abbrev qz480 := (Enclosure.Real.IsNear.const Bool.false 3 1)

noncomputable def Ns336p1006 := @Ns336p947 Ns336p948 Ns336p940 Ns336p949 Ns336p942 Ns336p950 Ns336p951 Ns336p952 Ns336p953 Ns336p954 Ns336p939 Ns336p940 Ns336p941 Ns336p942 (@Ns336p957 Ns336p958 Ns336p959 130928423 134217728 26766163 40600862720000 Ns336p948 Ns336p940 Ns336p949 Ns336p942 (@Ns336p964 78285272027748377103785 37778931862957161709568 Ns336p965 Ns336p966 Ns336p955 Ns336p956 Ns336p958 Ns336p959 (@Ns336p967 Ns336p965 Ns336p966 Ns336p960 Ns336p961 Ns336p962 Ns336p963 qz129 qz129 rfl) qz129 rfl) (Ns336p989 rfl) rfl) (@Ns336p993 Ns336p994 14766063 67108864 26766163 40600862720000 Ns336p950 Ns336p951 Ns336p952 Ns336p953 (@Ns336p996 70368744177664 1 250000000000000 Ns336p990 Ns336p991 Ns336p992 Ns336p994 (@Ns336p997 Ns336p966 234855816083245131311355 37778931862957161709568 Ns336p995 Ns336p966 qz480 qz129 rfl) RS337to348.d61 rfl) (Ns336p1005 rfl) rfl) rfl rfl 

noncomputable def Ns336p1007 := nat_lit 82244895372824882974064761057593 

noncomputable def Ns336p1008 := nat_lit 10898711098236600320000000000000000000 

noncomputable def Ns336p1009 := nat_lit 964719425100726647639565570332288940938136867528605981908589665654076099750745 

noncomputable def Ns336p1010 := @Enclosure.Real.IsNear.mulLit_tf qz120 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz109) 306360124380611754441555 18889465931478580854784 Ns336p1007 Ns336p1008 Ns336p1009 

noncomputable def Ns336p1011 := nat_lit 231584178474632390847141970017375815706539969331281128078915168015826259279872 

noncomputable def Ns336p1012 := nat_lit 463972818700873791128207058196581511328955870878281704228796725712754609200496960580396098767618760497220484183 

noncomputable def Ns336p1013 := nat_lit 746268594962563352895001436165243498997176456411568736331193638698614784000000000000000000000000000000000000000000 

noncomputable def Ns336p1014 := nat_lit 27414965124274960991354920352531 

noncomputable abbrev qz130 := qz472

noncomputable def Ns336p1015 := @Enclosure.Real.IsNear.mulLit_ft qz320 qz130 3 1 0 1 102120041460203918147185 18889465931478580854784 Ns336p1014 

noncomputable def Ns336p1016 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz122 884279719003555 140737488355328 1 500000000000000 115483867 134217728 1015893 2537553920000 102120041460203918147185 

noncomputable def Ns336p1017 := @Enclosure.Real.IsNear.recentre' qz122 Bool.false 461935468 536870912 1040274432 2598455214080000 115483867 134217728 1015893 2537553920000 

noncomputable def Ns336p1018 := @Enclosure.Real.IsNear.sin_image qz108 qz476 Bool.false 1130379399 536870912 13 33554432 Bool.false 461935468 536870912 1 

noncomputable def Ns336p1019 := nat_lit 293337602764829421916246739040998068805307450117841775707725871584456396748248600222303688352403361 

noncomputable def Ns336p1020 := nat_lit 86122997288331094522167275192756341260781046341420239684264717627391899343475426976925831345282744320 

noncomputable def Ns336p1021 := nat_lit 879984264872621678134594490474299130002064636338565517006900477218739049031611942854131436784521121 

noncomputable def Ns336p1022 := nat_lit 3875534877974899253497527383674035356735147085363910785791912293232635470456394213961662410537723494400 

noncomputable def Ns336p1023 := BSN.cos_dyadic_bound_f 587908182973 1099511627776 3 2 536870912 155031251 Ns336p1019 Ns336p1020 Ns336p916 Ns336p1021 Ns336p1022 Ns336p916 461935468 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 587908182973) (BSN.cosEvenQ 1099511627776) 0 2 Ns336p1019 Ns336p1020 Ns336p916 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 587908182973) (BSN.cosOddQ 1099511627776) 0 2 Ns336p1021 Ns336p1022 Ns336p916 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1024 := @Ns336p1018 77440000 (Ns336p911 rfl) (Enclosure.sfrac_false_div 1130379399 536870912) (BSN.sin_reduce1 qz476 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns336p912) qz699) 226375608064910080 72057594037927936 Bool.false 461935468 536870912 0 1000000000000000 154880000 77440000 (BSN.sin_reduce_arg_pos_rat_q1 1130379399 536870912 226375608064910080 72057594037927936 0 Ns336p912 Ns336p913 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 461935468 536870912 Ns336p912 Ns336p913 587908182973 1099511627776 155031251 154880000 (Ns336p1023 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable abbrev qz481 := (@HMul.hMul Real Real Real qz627 qz625 qz698)

noncomputable abbrev qz131 := qz481

noncomputable abbrev qz482 := (@Enclosure.Real.IsNear.neg qz131 Bool.false 102120041460203918147185 18889465931478580854784 Ns336p1014 Ns336p1008 (@Ns336p1016 18889465931478580854784 Ns336p1014 Ns336p1008 RS337to348.d59 (Ns336p1017 (Ns336p1024 rfl rfl) rfl) rfl))

noncomputable def Ns336p1025 := @Ns336p1015 Ns336p1008 306360124380611754441555 18889465931478580854784 Ns336p1007 Ns336p1008 qz480 qz482 rfl 

noncomputable abbrev qz132 := (@HMul.hMul Real Real Real qz349 qz469 (Real.cos qz456))

noncomputable def Ns336p1026 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz132) (@HMul.hMul Real Real Real qz5 qz461 qz118) 

noncomputable abbrev qz133 := (@HMul.hMul Real Real Real qz349 qz316 qz472)

noncomputable abbrev qz134 := (@HMul.hMul Real Real Real qz349 qz473 (Zeta.RiemannSiegel.correction qz448))

noncomputable def Ns336p1027 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz109) (@HMul.hMul Real Real Real qz5 qz104 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns336p1026 (@HMul.hMul Real Real Real qz5 qz133 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c8 1 Zeta.RiemannSiegel.correction qz109))) qz134)) 

noncomputable def Ns336p1028 := @Enclosure.Real.IsNear.mulLit_tt qz104 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns336p1026 (@HMul.hMul Real Real Real qz5 qz133 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 1 Zeta.RiemannSiegel.correction qz109))) qz134) 526775367 

noncomputable def Ns336p1029 := nat_lit 1831367762306027965122305292480179584665614911960387817277320914768735 

noncomputable def Ns336p1030 := nat_lit 862718293348820473429344482784628181556388621521298319395315527974912 

noncomputable def Ns336p1031 := nat_lit 876140508986886112920283919094054519879101293514071291622407376394538003639901517441123100753269747643 

noncomputable def Ns336p1032 := nat_lit 2780067156860840890165423736591799180944176228387537361425137664000000000000000000000000000000000000000000 

noncomputable def Ns336p1033 := nat_lit 5662630247868648944926319128936872400186915430976550414000536046562465 

noncomputable def Ns336p1034 := @Enclosure.Real.IsNear.subLit_ff_n (@HSub.hSub Real Real Real qz11 Ns336p1026 (@HMul.hMul Real Real Real qz5 qz133 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz109))) qz134 Ns336p1033 Ns336p1030 

noncomputable def Ns336p1035 := nat_lit 765834544468461177158508639263822145509734173738971165624491478021195909759539542359384713470284787643 

noncomputable def Ns336p1036 := nat_lit 26000028554346982616498564008154267771138098776704175 

noncomputable def Ns336p1037 := nat_lit 2993155353253689176481146537402947624255349848014848 

noncomputable def Ns336p1038 := nat_lit 20242020092866269597499883243211187756857800388255379574744871331351083335723031 

noncomputable def Ns336p1039 := nat_lit 510164391330760708461288205046632282514155110400000000000000000000000000000000000000 

noncomputable def Ns336p1040 := nat_lit 5481568221522517407427061737737044317715741926058035456008064521214580260316894397650185074187866785479991098344766177280 

noncomputable def Ns336p1041 := nat_lit 1264616863370382111573892919889652277962370634168147295 

noncomputable def Ns336p1042 := nat_lit 95780971304118053647396689196894323976171195136475136 

noncomputable def Ns336p1043 := nat_lit 3189383570460768223480374975906642258289199680871848273423353644607676639 

noncomputable def Ns336p1044 := nat_lit 269839016902220540012582191099045174222363033600000000000000000000000000000000 

noncomputable def Ns336p1045 := @Enclosure.Real.IsNear.subLit_ff_p Ns336p1026 (@HMul.hMul Real Real Real qz5 qz133 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz109)) Ns336p1041 Ns336p1042 Ns336p1043 Ns336p1044 

noncomputable def Ns336p1046 := nat_lit 5728025821413947714959540126588447422690023205926185753039105683854175 

noncomputable def Ns336p1047 := nat_lit 732975321155760988854670880384504835885768812681384985739845385678062398889856027946115066110284787643 

noncomputable def Ns336p1048 := nat_lit 542372225276937965909857361113296626571699652373019682297936675672597358750357257940814882679069357161231562223189743370240 

noncomputable def Ns336p1049 := @Enclosure.Real.IsNear.subLit_ft (@Neg.neg Real Real.instNeg qz132) (@HMul.hMul Real Real Real qz5 qz461 qz118) 

noncomputable def Ns336p1050 := nat_lit 90495054734607570750066197962492850050905496701902175 

noncomputable def Ns336p1051 := nat_lit 953930965287386798299164872587667557933317668525959855385593644607676639 

noncomputable def Ns336p1052 := nat_lit 722313693468976238248083559103621 

noncomputable def Ns336p1053 := nat_lit 87189688785892802560000000000000000000 

noncomputable def Ns336p1054 := nat_lit 11943968578504068075236474754721717758593008808128923479089759367113358704640 

noncomputable def Ns336p1055 := @Enclosure.Real.IsNear.neg qz132 Bool.true Ns336p1050 

noncomputable def Ns336p1056 := @Enclosure.Real.IsNear.mulLit_ft qz124 qz105 Ns336p960 Ns336p961 Ns336p962 

noncomputable def Ns336p1057 := @Enclosure.Real.IsNear.mulLit_ft qz461 qz118 884279719003555 70368744177664 1 

noncomputable def Ns336p1058 := nat_lit 5449355549118300160000000000000000000 

noncomputable def Ns336p1059 := nat_lit 56091103563115511107308041038640123552965621455 

noncomputable def Ns336p1060 := @Enclosure.Real.IsNear.mulLit_tt qz133 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz109) 102120041460203918147185 9444732965739290427392 Ns336p1014 Ns336p1058 Ns336p1059 

noncomputable def Ns336p1061 := nat_lit 91343852333181432387730302044767688728495783936 

noncomputable def Ns336p1062 := nat_lit 3073576029108066368307398564606361325315784757680720387645080107 

noncomputable def Ns336p1063 := nat_lit 127541097832690177115322051261658070628538777600000000000000000000000 

noncomputable def Ns336p1064 := @Enclosure.Real.IsNear.mulLit_ft qz0 qz130 2 1 0 1 102120041460203918147185 18889465931478580854784 Ns336p1014 

noncomputable def Ns336p1065 := @Ns336p1064 Ns336p1008 102120041460203918147185 9444732965739290427392 Ns336p1014 Ns336p1058 qz347 qz482 rfl 

noncomputable abbrev qz135 := (@HMul.hMul Real Real Real qz349 qz470 (Real.sin qz456))

noncomputable def Ns336p1066 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz135) (@HMul.hMul Real Real Real qz5 qz130 qz97) 

noncomputable def Ns336p1067 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz109) (@HMul.hMul Real Real Real qz5 qz104 Ns336p1066) Bool.true Ns336p1059 Ns336p1061 Ns336p1062 Ns336p1063 (BSN.deriv_correction_mk qz109 qz123) 

noncomputable def Ns336p1068 := nat_lit 106480118617838694623904160345144087865 

noncomputable def Ns336p1069 := nat_lit 340282366920938463463374607431768211456 

noncomputable def Ns336p1070 := nat_lit 5717849013592643382884263885683664661623142861132276447 

noncomputable def Ns336p1071 := @Enclosure.Real.IsNear.mulLit_tf qz104 Ns336p1066 526775367 268435456 207 134217728 Ns336p1068 Ns336p1069 Ns336p1070 

noncomputable def Ns336p1072 := nat_lit 475127614411302570683218729725696409600000000000000000000000 

noncomputable def Ns336p1073 := @Enclosure.Real.IsNear.subLit_tt_p (@Neg.neg Real Real.instNeg qz135) (@HMul.hMul Real Real Real qz5 qz130 qz97) 

noncomputable def Ns336p1074 := nat_lit 10249767210719107255007877381055 

noncomputable def Ns336p1075 := nat_lit 5070602400912917605986812821504 

noncomputable def Ns336p1076 := nat_lit 2480426422913746283008550559656213456623 

noncomputable def Ns336p1077 := nat_lit 1170240193386961041115578368000000000000000000 

noncomputable def Ns336p1078 := nat_lit 794330352393646605601641122439040259385 

noncomputable def Ns336p1079 := nat_lit 4710774486754826630510859587095853732149471883186676447 

noncomputable def Ns336p1080 := nat_lit 539918345113105142746624690475803405034067890667901031136485137448960 

noncomputable def Ns336p1081 := @Enclosure.Real.IsNear.neg qz135 Bool.false Ns336p1074 

noncomputable def Ns336p1082 := @Enclosure.Real.IsNear.mulLit_tt qz125 qz118 78285272027748377103785 37778931862957161709568 Ns336p965 

noncomputable def Ns336p1083 := @Enclosure.Real.IsNear.mulLit_tf qz130 qz97 102120041460203918147185 18889465931478580854784 Ns336p1014 Ns336p1008 7778398255970121 18014398509481984 

noncomputable def Ns336p1084 := @Enclosure.Real.IsNear.of_eq qz97 (@HMul.hMul Real Real Real qz5 qz104 qz105) Bool.false 7778398255970121 

noncomputable def Ns336p1085 := @Enclosure.Real.IsNear.mulLit_tt qz104 qz105 526775367 268435456 207 

noncomputable abbrev qz483 := (@Ns336p1084 18014398509481984 17798222218308303 10898711098236600320000 qz115 (@Ns336p1085 134217728 14766063 67108864 26766163 40600862720000 7778398255970121 18014398509481984 17798222218308303 10898711098236600320000 Ns336p922 (Ns336p1005 rfl) rfl))

noncomputable def Ns336p1086 := @Ns336p1083 17798222218308303 10898711098236600320000 Ns336p1078 Ns336p1069 Ns336p1079 Ns336p1072 qz482 qz483 

noncomputable def Ns336p1087 := @Ns336p1060 Ns336p1061 Ns336p1062 Ns336p1063 Ns336p1046 Ns336p1030 Ns336p1047 Ns336p1032 Ns336p1065 (Ns336p1067 (@Ns336p1071 Ns336p1072 Ns336p1059 Ns336p1061 Ns336p1062 Ns336p1063 Ns336p922 (@Ns336p1073 Ns336p1074 Ns336p1075 Ns336p1076 Ns336p1077 Ns336p1078 Ns336p1069 Ns336p1079 Ns336p1072 Ns336p1080 Ns336p1068 Ns336p1069 Ns336p1070 Ns336p1072 (@Ns336p1081 Ns336p1075 Ns336p1076 Ns336p1077 (@Ns336p1082 Ns336p966 130928423 134217728 26766163 40600862720000 Ns336p1074 Ns336p1075 Ns336p1076 Ns336p1077 qz129 (Ns336p989 rfl) rfl)) (Ns336p1086 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns336p1088 := @Ns336p1045 Ns336p1046 Ns336p1030 Ns336p1047 Ns336p1032 Ns336p1048 Ns336p1033 Ns336p1030 Ns336p1035 Ns336p1032 (@Ns336p1049 Ns336p1050 Ns336p1042 Ns336p1051 Ns336p1044 115777349100018587543765 9444732965739290427392 Ns336p1052 Ns336p1053 Ns336p1054 Ns336p1041 Ns336p1042 Ns336p1043 Ns336p1044 (@Ns336p1055 Ns336p1042 Ns336p1051 Ns336p1044 (@Ns336p1056 Ns336p963 14766063 67108864 26766163 40600862720000 Ns336p1050 Ns336p1042 Ns336p1051 Ns336p1044 (@Ns336p967 Ns336p965 Ns336p966 Ns336p960 Ns336p961 Ns336p962 Ns336p963 qz129 qz129 rfl) (Ns336p1005 rfl) rfl)) (@Ns336p1057 250000000000000 130928423 134217728 26766163 40600862720000 115777349100018587543765 9444732965739290427392 Ns336p1052 Ns336p1053 RS337to348.d61 (Ns336p989 rfl) rfl) rfl rfl) Ns336p1087 

noncomputable def Ns336p1089 := nat_lit 3342594156115790426466580719431173175 

noncomputable def Ns336p1090 := nat_lit 166153499473114484112975882535043072 

noncomputable def Ns336p1091 := nat_lit 739822316273373523685638258453538781032494164763491105477 

noncomputable def Ns336p1092 := nat_lit 46809607735478441644623134720000000000000000000000000000000000 

noncomputable abbrev qz136 := qz473

noncomputable def Ns336p1093 := @Enclosure.Real.IsNear.mulLit_ff qz136 qz97 Ns336p1089 Ns336p1090 Ns336p1091 Ns336p1092 7778398255970121 18014398509481984 

noncomputable def Ns336p1094 := @Enclosure.Real.IsNear.mulLit_ft qz116 qz107 Ns336p847 Ns336p851 Ns336p849 Ns336p852 4274687 8388608 1015893 2537553920000 Ns336p1089 

noncomputable abbrev qz484 := (@HMul.hMul Real Real Real qz627 qz695 qz689)

noncomputable abbrev qz137 := qz484

noncomputable def Ns336p1095 := @Ns336p1093 17798222218308303 10898711098236600320000 Ns336p1036 Ns336p1037 Ns336p1038 Ns336p1039 (@Enclosure.Real.IsNear.neg qz137 Bool.true Ns336p1089 Ns336p1090 Ns336p1091 Ns336p1092 (@Ns336p1094 Ns336p1090 Ns336p1091 Ns336p1092 RS337to348.d63 (Ns336p903 (Ns336p920 rfl rfl) rfl) rfl)) qz483 

noncomputable def Ns336p1096 := nat_lit 10027782468347371279399742158293519525 

noncomputable def Ns336p1097 := nat_lit 2219466948820120571056914775360616343097482494290473316431 

noncomputable def Ns336p1098 := @Enclosure.Real.IsNear.mulLit_ft qz121 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz109) Ns336p1096 Ns336p1090 Ns336p1097 Ns336p1092 Ns336p1059 

noncomputable def Ns336p1099 := @Enclosure.Real.IsNear.mulLit_ff qz320 qz136 3 1 0 1 Ns336p1089 Ns336p1090 Ns336p1091 

noncomputable def Ns336p1100 := @Ns336p1099 Ns336p1092 Ns336p1096 Ns336p1090 Ns336p1097 Ns336p1092 qz480 (@Enclosure.Real.IsNear.neg qz137 Bool.true Ns336p1089 Ns336p1090 Ns336p1091 Ns336p1092 (@Ns336p1094 Ns336p1090 Ns336p1091 Ns336p1092 RS337to348.d63 (Ns336p903 (Ns336p920 rfl rfl) rfl) rfl)) rfl 

noncomputable def Ns336p1101 := @Ns336p1098 Ns336p1061 Ns336p1062 Ns336p1063 Ns336p934 Ns336p935 Ns336p936 Ns336p937 Ns336p1100 (Ns336p1067 (@Ns336p1071 Ns336p1072 Ns336p1059 Ns336p1061 Ns336p1062 Ns336p1063 Ns336p922 (@Ns336p1073 Ns336p1074 Ns336p1075 Ns336p1076 Ns336p1077 Ns336p1078 Ns336p1069 Ns336p1079 Ns336p1072 Ns336p1080 Ns336p1068 Ns336p1069 Ns336p1070 Ns336p1072 (@Ns336p1081 Ns336p1075 Ns336p1076 Ns336p1077 (@Ns336p1082 Ns336p966 130928423 134217728 26766163 40600862720000 Ns336p1074 Ns336p1075 Ns336p1076 Ns336p1077 qz129 (Ns336p989 rfl) rfl)) (Ns336p1086 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns336p1102 := @Ns336p932 Ns336p933 Ns336p900 Ns336p934 Ns336p935 Ns336p936 Ns336p937 Ns336p938 Ns336p924 Ns336p897 Ns336p925 Ns336p900 (@Ns336p943 Ns336p944 Ns336p897 Ns336p945 Ns336p900 Ns336p946 Ns336p931 Ns336p897 Ns336p933 Ns336p900 Ns336p1006 (@Ns336p1010 Ns336p1011 Ns336p1012 Ns336p1013 Ns336p944 Ns336p897 Ns336p945 Ns336p900 Ns336p1025 (@Ns336p1027 Bool.false Ns336p1009 Ns336p1011 Ns336p1012 Ns336p1013 (BSN.iteratedDeriv_two_correction_mk qz109 qz123) (@Ns336p1028 268435456 207 134217728 Ns336p1029 Ns336p1030 Ns336p1031 Ns336p1032 Ns336p1009 Ns336p1011 Ns336p1012 Ns336p1013 Ns336p922 (@Ns336p1034 Ns336p1035 Ns336p1032 Ns336p1036 Ns336p1037 Ns336p1038 Ns336p1039 Ns336p1040 Ns336p1029 Ns336p1030 Ns336p1031 Ns336p1032 (Ns336p1088 rfl rfl) (Ns336p1095 rfl) rfl rfl) rfl)) rfl) rfl rfl) Ns336p1101 

noncomputable def Ns336p1103 := nat_lit 79852829881387770968621759907294933728263258727709625 

noncomputable def Ns336p1104 := nat_lit 374144419156711147060143317175368453031918731001856 

noncomputable def Ns336p1105 := nat_lit 19964900841043577625122386633632749750905395652519875736894637693782292448094132259 

noncomputable def Ns336p1106 := nat_lit 201045734362468525776700817867402117120000000000000000000000000000000000000000000000000 

noncomputable def Ns336p1107 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz335 RSCompact.c11) qz122) qz97 Ns336p1103 Ns336p1104 Ns336p1105 Ns336p1106 7778398255970121 18014398509481984 17798222218308303 

noncomputable def Ns336p1108 := @Enclosure.Real.IsNear.mulLit_ff qz463 qz122 Ns336p853 Ns336p854 Ns336p855 Ns336p856 115483867 134217728 1015893 2537553920000 Ns336p1103 

noncomputable def Ns336p1109 := Ns336p895 (@Ns336p899 Ns336p900 Ns336p888 Ns336p889 Ns336p890 Ns336p891 Ns336p922 (@Ns336p923 Ns336p924 Ns336p897 Ns336p925 Ns336p900 Ns336p926 Ns336p927 Ns336p928 Ns336p929 Ns336p930 Ns336p896 Ns336p897 Ns336p898 Ns336p900 (Ns336p1102 rfl rfl) (@Ns336p1107 10898711098236600320000 Ns336p926 Ns336p927 Ns336p928 Ns336p929 (@Ns336p1108 Ns336p1104 Ns336p1105 Ns336p1106 RS337to348.d64 (Ns336p1017 (Ns336p1024 rfl rfl) rfl) rfl) qz483 rfl) rfl rfl) rfl) 

noncomputable def Ns336p1110 := @Enclosure.Real.IsNear.of_eq qz696 (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz109) qz466)) Bool.false Ns336p883 Ns336p884 Ns336p885 Ns336p886 (BSN.correctionLinear_mk qz109) (@Enclosure.Real.IsNear.neg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz109) qz466) Bool.true Ns336p883 Ns336p884 Ns336p885 Ns336p886 (@Ns336p892 Ns336p884 Ns336p885 Ns336p886 Ns336p1109 RS337to348.d65 rfl)) 

noncomputable def Ns336p1111 := @Enclosure.Real.IsNear.inv_image qz103 346788389 33554432 33 33554432 1623323 1623325 16777216 qz454 rfl 

noncomputable def Ns336p1112 := @Ns336p887 Ns336p875 Ns336p880 Ns336p878 Ns336p1110 (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz103) Bool.false 3246648 33554432 2 33554432 405831 4194304 1 16777216 (Ns336p1111 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns336p1113 := @Ns336p877 Ns336p878 Ns336p870 Ns336p866 Ns336p872 Ns336p868 (Ns336p807 qz28 (@Enclosure.Real.IsNear.of_eq qz101 (@Inv.inv Real Real.instInv (Real.sqrt qz103)) Bool.false 5218703 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz102 (BSN.t_div_two_pi_nonneg qz95 671134 1000 qz98)) Ns336p811) rfl) (@Ns336p881 Ns336p882 Ns336p874 Ns336p875 Ns336p876 Ns336p878 (@Ns336p812 562949953421312 1115173320161457 42573090227486720000 qz115 (@Ns336p813 33554432 3691493 16777216 6710447 634388480000 243075212476707 562949953421312 1115173320161457 42573090227486720000 Ns336p828 (Ns336p844 rfl) rfl)) (Ns336p1112 rfl) rfl rfl) 

noncomputable def Ns336p1114 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz95) (hardyZApproximantRS qz95) Bool.false Ns336p865 Ns336p866 Ns336p867 Ns336p868 (@Eq.refl Real (hardyZApproximantRS qz95)) (Ns336p869 (BSN.hardyZApproximantRS_eq qz95 10 (@BSN.floor_sqrt_eq_dec qz95 671134 1000 10 qz98 rfl rfl rfl)) (@Ns336p871 Ns336p872 Ns336p868 Ns336p873 Ns336p865 Ns336p866 Ns336p867 Ns336p868 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz95) qz95 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz95) qz95 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz95) qz95 10)) Bool.false 684233445 134217728 164475 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz95) qz95 10) (Ns336p805 (Ns336p804 rfl rfl rfl rfl) rfl rfl)) (Ns336p1113 rfl) rfl rfl)) 

theorem RS337to348.d66 : Enclosure.Real.IsNear (hardyZApproximantRS qz95) Bool.false Ns336p865 Ns336p866 Ns336p867 Ns336p868 := Ns336p1114 

theorem RS337to348.d67 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal (RS337to348.d3 a b h)) (hardyZApproximantRS b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal (RS337to348.d3 a b h)) 

noncomputable def Ns336p1115 := nat_lit 20260207593153270506788207007169760009998123484055434726426281497656513742132022687970493250122476355027282166764238912574718530823 

noncomputable def Ns336p1116 := nat_lit 354901720847464302026037015570314714039863945648104521621821386318671527399120079749116723981329865996466075003059657194108692201472 

noncomputable def Ns336p1117 := nat_lit 334082206079585519489202024739344236476396593212519294986610165655023563130819515969793305008476515164188180227431877301244495256901938620394347527337448057220061322505513 

noncomputable def Ns336p1118 := nat_lit 270277438637253977552700687859869215825697440825239343901010391679801394175215352361090814138662121617366614828334333581852672000000000000000000000000000000000000000000000000 

noncomputable abbrev qz854 := (Enclosure.sfrac Bool.false 672479 1000)

noncomputable abbrev qz702 := qz854

noncomputable abbrev qz485 := qz702

noncomputable abbrev qz138 := qz485

noncomputable abbrev qz855 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 672479 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz703 := qz855

noncomputable abbrev qz486 := qz703

noncomputable abbrev qz139 := qz486

noncomputable abbrev qz856 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 672479 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz704 := qz856

noncomputable abbrev qz487 := qz704

noncomputable abbrev qz140 := (Zeta.RiemannSiegel.correction qz487)

noncomputable abbrev qz141 := qz487

noncomputable abbrev qz857 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 672479 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz705 := qz857

noncomputable abbrev qz488 := qz705

noncomputable abbrev qz142 := qz488

noncomputable abbrev qz489 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz630 qz139 qz8))

noncomputable abbrev qz706 := (Zeta.RiemannSiegel.correctionLinear qz141)

noncomputable abbrev qz490 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) qz140 (@HMul.hMul Real Real Real qz5 qz706 (@Inv.inv Real Real.instInv qz142)))

noncomputable def Ns336p1119 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz138) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz138) qz138 10) (@HMul.hMul Real Real Real qz5 qz489 qz490)) Bool.true Ns336p1115 Ns336p1116 Ns336p1117 Ns336p1118 

noncomputable def Ns336p1120 := nat_lit 47049601208885351097101615556324627380242277178694741708682005192768690141663807896860851431951925110199212867942538311405155177735 

noncomputable def Ns336p1121 := @Enclosure.Real.IsNear.subLit_ff_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz138) qz138 10) (@HMul.hMul Real Real Real qz5 qz489 qz490) 1266411 16777216 164811 134217728 Ns336p1120 Ns336p1116 

noncomputable def Ns336p1122 := nat_lit 2198366269359665461646491487634705754426534832090433102810257619478902626572137873930006167603251940124298320023864464380495256901938620394347527337448057220061322505513 

noncomputable def Ns336p1123 := nat_lit 339909878995172540398815215212000612355900677286670584379154632762986824858717245152981566883846812263185398804751657311871168930820128768 

noncomputable def Ns336p1124 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.sin BSN.quadSignPos 9 10 672479 1000 199 268435456 134217728 4503599627370496 Bool.false 331422912774 2526 618095470 56 84886744 8 

noncomputable def Ns336p1125 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 672479 1000 104 154 268435456 134217728 4503599627370496 Bool.false 331422912774 2526 

noncomputable def Ns336p1126 := Ns336p1125 558195838 56 94906264 8 589812974 56 89478488 8 Bool.true 112140498 124471 Bool.true 99693628 Bool.true 278682215 14148475504056880 1 Bool.false 250134770 Bool.false Bool.false 136310384 Bool.true Bool.true 69141300 

noncomputable def Ns336p1127 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 672479 1000 18 47 268435456 134217728 4503599627370496 Bool.false 331422912774 2526 

noncomputable def Ns336p1128 := Ns336p1127 480971758 57 109588312 8 522351262 57 101459064 8 Bool.true 110219355 92329 Bool.false 389672217 Bool.true 29442415 14148475504056880 1 Bool.false 31909578 Bool.true Bool.false 29383418 Bool.false Bool.true 112140498 

noncomputable def Ns336p1129 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 672479 1000 192 96 268435456 134217728 4503599627370496 Bool.false 331422912774 2526 

noncomputable def Ns336p1130 := Ns336p1129 372130544 56 134217720 8 432030192 56 120047984 16 Bool.true 207807401 54237 Bool.false 214710448 Bool.false 412568174 14148475504056880 1 Bool.false 187047981 Bool.false Bool.false 9087517 Bool.false Bool.true 110219355 

noncomputable def Ns336p1131 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 672479 1000 489 315 268435456 134217728 4503599627370496 Bool.false 331422912774 2526 

noncomputable def Ns336p1132 := Ns336p1131 186065264 56 189812528 16 294906480 56 154981288 8 Bool.true 268435392 2592 Bool.false 107447682 Bool.false 282408106 14148475504056880 1 Bool.false 104601383 Bool.true Bool.false 233120759 Bool.false Bool.true 207807401 

noncomputable def Ns336p1133 := nat_lit 231413143043994054655481634340309590525419393036559362017 

noncomputable def Ns336p1134 := nat_lit 187432703603138010655029073109363160805422889382707200 

noncomputable def Ns336p1135 := nat_lit 66013913510672586831565029631520000 

noncomputable def Ns336p1136 := nat_lit 266357891978171339040712088475065628480 

noncomputable abbrev qz491 := (@Eq.refl Real qz702)

noncomputable abbrev qz143 := qz491

noncomputable def Ns336p1137 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz138 672479 1000 1808913021764 16000000 1344958 4000 2000 Ns336p1135 Ns336p1136 qz143 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns336p1138 := nat_lit 74052205774078097489754122988899068968134205771698995845440 

noncomputable abbrev qz492 := (Enclosure.sfrac Bool.false 672479 2000)

noncomputable abbrev qz707 := (Real.log (Enclosure.sfrac Bool.false 1808913021764 16000000))

noncomputable abbrev qz708 := (@Nat.cast Real Real.instNatCast 1344958)

noncomputable abbrev qz144 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 672479 4000) qz707) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz708))))) qz492)

noncomputable abbrev qz493 := (@HSub.hSub Real Real Real qz11 qz144 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 672479 2000) (Real.log Real.pi)))

noncomputable def Ns336p1139 := @Enclosure.Real.IsNear.addLit_ft_p qz493 (Enclosure.sfrac Bool.true Ns336p1135 Ns336p1136) 278017745557014195753 225179981368524800 4660748214037907131 495616000000000000000000 Ns336p1135 Ns336p1136 0 1 Ns336p1138 

noncomputable def Ns336p1140 := nat_lit 93287275380861349544287272960000 

noncomputable abbrev qz494 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 672479 2000) (Real.log Real.pi))

noncomputable def Ns336p1141 := @Enclosure.Real.IsNear.subLit_ff_p qz144 qz494 1823451433726131889869 1125899906842624000 531624544244961 121000000000000000000 25830430146519 67108864000 672479 134217728000 Ns336p1140 278017745557014195753 225179981368524800 

noncomputable def Ns336p1142 := nat_lit 3646902867452263779738000 

noncomputable abbrev qz145 := (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 672479 4000) qz707) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz708)))))

noncomputable def Ns336p1143 := @Enclosure.Real.IsNear.subLit_ff_p qz145 qz492 2202023455452942362317 1125899906842624000 531624544244961 121000000000000000000 672479 2000 0 1 Ns336p1142 1823451433726131889869 1125899906842624000 531624544244961 121000000000000000000 

noncomputable def Ns336p1144 := nat_lit 4958516006719481610567416694613999616 

noncomputable def Ns336p1145 := nat_lit 56266540983945612893356032 

noncomputable def Ns336p1146 := nat_lit 40048171543686917215707480944199170713284261227470362586356738709767908468847371741730712313132404247070265889716929603155306185982721732718975393946664960 

noncomputable def Ns336p1147 := nat_lit 987458816060883210229078310306988176479004801374074864417573582245663042176670460482233608593331357157699012715534366721150440932831056261090003294093312 

noncomputable def Ns336p1148 := nat_lit 388059340983284626396086238599888502197508701276725686881108823005936639842441532567670094067584133032533622024753348735360265518788074083891281920 

noncomputable def Ns336p1149 := BSN.log_dyadic_bound 760337021764 2857489021764 7 6 Ns336p1146 134217728 38720000 Ns336p1147 Ns336p1148 73187997 3617826043528 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 760337021764) (BSN.artanhQ 2857489021764) 0 6 Ns336p1147 Ns336p1146 Ns336p1148 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns336p1150 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 672479 4000) qz707 672479 4000 0 1 3275143738367223 281474976710656 195312621 7562500000000000 2202465386033451755817 1125899906842624000 131343636057459 30250000000000000000 (Enclosure.Real.IsNear.const Bool.false 672479 4000) (BSN.isNear_log_sfrac 1808913021764 16000000 3275143738367223 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1808913021764) qz362)) Bool.false Ns336p1145 Ns336p98 1000000619520000 38720000000000000000000 3275143738367223 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1808913021764 16000000 16 3617826043528 2097152000000 73187997 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns336p1149 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p1151 := BSN.arctan_dyadic_bound_f 1000 1344958 1 0 16777216 4840000 0 1 1 0 1 1 12474 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1344958) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1344958) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz709 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1344958)))

noncomputable def Ns336p1152 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz709 884279719003555 562949953421312 1 2000000000000000 12474 16777216 1 4840000 14828729612422969556992 883861161018787 562949953421312 50000000121 242000000000000000 qz16 (Ns336p1151 rfl) rfl rfl 

noncomputable def Ns336p1153 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 672479 4000) qz707) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz709)) 2202465386033451755817 1125899906842624000 131343636057459 30250000000000000000 883861161018787 2251799813685248 50000000121 968000000000000000 Ns336p1144 2202023455452942362317 1125899906842624000 531624544244961 121000000000000000000 (Ns336p1150 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz709) 1 4 0 1 883861161018787 562949953421312 50000000121 242000000000000000 883861161018787 2251799813685248 50000000121 968000000000000000 qz364 Ns336p1152 rfl) 

noncomputable def Ns336p1154 := @Ns336p1139 Ns336p1133 Ns336p1134 4660748214037907131 495616000000000000000000 (@Ns336p1141 4660748214037907131 495616000000000000000000 (Ns336p1143 (Ns336p1153 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 672479 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz492 (Real.log Real.pi) 672479 2000 0 1 38410761 33554432 1 67108864 25830430146519 67108864000 672479 134217728000 (Enclosure.Real.IsNear.const Bool.false 672479 2000) RS337to348.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns336p1135 Ns336p1136) 

noncomputable def Ns336p1155 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz138) Bool.false Ns336p1133 Ns336p1134 4660748214037907131 495616000000000000000000 1294620753 1048576 317 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz138) (@HAdd.hAdd Real Real Real qz365 qz493 (Enclosure.sfrac Bool.true Ns336p1135 Ns336p1136)) Bool.false Ns336p1133 Ns336p1134 4660748214037907131 495616000000000000000000 Ns336p1137 (Ns336p1154 rfl rfl)) 

noncomputable def Ns336p1156 := BSN.cos_dyadic_bound_f 44582573 68719476736 1 0 33554432 9689454 0 1 1 0 1 1 33554424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 44582573) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 44582573) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns336p1157 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz138) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1294620753) qz692) Bool.false 1294620753 1048576 317 33554432 Bool.true 33554424 33554432 1 4840000 (Ns336p1155 rfl) (Enclosure.sfrac_false_div 1294620753 1048576) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1294620753) qz692) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 98038116024619892736) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false 33554424 33554432 196 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q2 1294620753 1048576 226375608064910080 72057594037927936 196 98038116024619892736 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554424 33554432 98038116024619892736 151115727451828646838272 44582573 68719476736 9689454 9680000 (Ns336p1156 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p1158 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz138) Bool.false Ns336p1133 Ns336p1134 4660748214037907131 495616000000000000000000 331422912774 268435456 2526 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz138) (@HAdd.hAdd Real Real Real qz365 qz493 (Enclosure.sfrac Bool.true Ns336p1135 Ns336p1136)) Bool.false Ns336p1133 Ns336p1134 4660748214037907131 495616000000000000000000 Ns336p1137 (Ns336p1154 rfl rfl)) 

noncomputable def Ns336p1159 := Ns336p1132 54237 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 489 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 104601383 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 315 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 233120759 268435456) qz143 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 1) Bool.true 4194303 4194304 24497413 2537553920000 268435392 268435456 2592 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz138)) Bool.true 4194303 4194304 24497413 2537553920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz138) qz138) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz138)) Bool.true 33554424 33554432 1567834432 162403450880000 4194303 4194304 24497413 2537553920000 (Ns336p1157 rfl rfl) rfl)) rfl) (Ns336p1158 rfl) RS337to348.d7 

noncomputable def Ns336p1160 := nat_lit 133287125838046505361094987919376 

noncomputable def Ns336p1161 := BSN.sin_dyadic_bound_f 107447682 268435456 2 1 268435456 134217728 Ns336p1160 Ns336p137 Ns336p1160 Ns336p1160 Ns336p138 Ns336p1160 104601383 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 107447682) qz371 0 1 Ns336p1160 Ns336p137 Ns336p1160 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 107447682) qz372 0 1 Ns336p1160 Ns336p138 Ns336p1160 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1162 := nat_lit 99913881972800265232706151170172136658140845983161176787541679429280000 

noncomputable def Ns336p1163 := nat_lit 40459197595231503014132142383685163390882183323955765316872293212416 

noncomputable def Ns336p1164 := nat_lit 261613709323132224604588467691353439078212215944802391775905652887675136 

noncomputable def Ns336p1165 := BSN.sin_dyadic_bound_f 282408106 268435456 3 2 268435456 134217728 Ns336p1162 Ns336p127 Ns336p1163 Ns336p1164 Ns336p130 Ns336p1163 233120759 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 282408106) qz371 0 2 Ns336p1162 Ns336p127 Ns336p1163 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 282408106) qz372 0 2 Ns336p1164 Ns336p130 Ns336p1163 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1166 := nat_lit 18543312017226414775603450519183037344213583828617067908065789724327936 

noncomputable def Ns336p1167 := nat_lit 4516743464490623893380071951218749416931476410084754643373791379456 

noncomputable def Ns336p1168 := nat_lit 55620902564750263079023591413646674533806888533031034214910621590224896 

noncomputable def Ns336p1169 := BSN.cos_dyadic_bound_f 214710448 268435456 3 2 268435456 134217728 Ns336p1166 Ns336p251 Ns336p1167 Ns336p1168 Ns336p254 Ns336p1167 187047981 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 214710448) qz369 0 2 Ns336p1166 Ns336p251 Ns336p1167 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 214710448) qz370 0 2 Ns336p1168 Ns336p254 Ns336p1167 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1170 := nat_lit 15641138804861430796174583817385007088112292754773852872814872638734744634875773349926042377788554362729926656 

noncomputable def Ns336p1171 := nat_lit 24319165890501482406341815822754119444671837853972456830290093826808587331811512323646929579072397643776 

noncomputable def Ns336p1172 := nat_lit 94680040658026496167942368906225721932017574776494615144546193832089108953517661954537789545257879915584163840 

noncomputable def Ns336p1173 := BSN.cos_dyadic_bound_f 412568174 268435456 4 3 268435456 134217728 Ns336p1170 Ns336p121 Ns336p1171 Ns336p1172 Ns336p124 Ns336p1171 9087517 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 412568174) qz369 0 3 Ns336p1170 Ns336p121 Ns336p1171 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 412568174) qz370 0 3 Ns336p1172 Ns336p124 Ns336p1171 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1174 := Ns336p1130 92329 BSN.abs_quadSignPos (BSN.cos_quad_nat0 192 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 187047981 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 96 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 9087517 268435456) qz143 rfl rfl (Ns336p1159 RS337to348.d9 RS337to348.d11 RS337to348.d13 RS337to348.d17 (Ns336p1161 rfl rfl) (Ns336p1165 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns336p1158 rfl) RS337to348.d19 RS337to348.d21 RS337to348.d23 RS337to348.d25 RS337to348.d17 (Ns336p1169 rfl rfl) (Ns336p1173 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns336p1175 := nat_lit 12439111440271657676291408118867105383725771094143517938726589755669010176220089708456870935300408976617499041 

noncomputable def Ns336p1176 := nat_lit 12257257471128416629264898238916000220464761190521538499691813302820497484967823514286721396386752620961 

noncomputable def Ns336p1177 := nat_lit 75331254115997075632192564173705068513514779212279950985521001364028182634288267003060263092733538400422586785 

noncomputable def Ns336p1178 := BSN.cos_dyadic_bound_f 389672217 268435456 4 3 268435456 134217728 Ns336p1175 Ns336p121 Ns336p1176 Ns336p1177 Ns336p124 Ns336p1176 31909578 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 389672217) qz369 0 3 Ns336p1175 Ns336p121 Ns336p1176 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 389672217) qz370 0 3 Ns336p1177 Ns336p124 Ns336p1176 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1179 := nat_lit 751438979783220457375488450625 

noncomputable def Ns336p1180 := BSN.sin_dyadic_bound_f 29442415 268435456 2 1 268435456 134217728 Ns336p1179 Ns336p137 Ns336p1179 Ns336p1179 Ns336p138 Ns336p1179 29383418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 29442415) qz371 0 1 Ns336p1179 Ns336p137 Ns336p1179 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 29442415) qz372 0 1 Ns336p1179 Ns336p138 Ns336p1179 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1181 := Ns336p1128 124471 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 18 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 31909578 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 47 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 29383418 268435456) qz143 rfl rfl (Ns336p1174 rfl rfl) (Ns336p1158 rfl) RS337to348.d27 RS337to348.d29 RS337to348.d31 RS337to348.d33 RS337to348.d17 (Ns336p1178 rfl rfl) (Ns336p1180 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p1182 := nat_lit 861674652464893109371883696667970576205290848410572175940791650287616 

noncomputable def Ns336p1183 := nat_lit 9757514543933834519963281817385047862518743154095119855412903936 

noncomputable def Ns336p1184 := nat_lit 2585004442365591460446611163440276958520147507745408337582664125054976 

noncomputable def Ns336p1185 := BSN.cos_dyadic_bound_f 99693628 268435456 3 2 268435456 134217728 Ns336p1182 Ns336p251 Ns336p1183 Ns336p1184 Ns336p254 Ns336p1183 250134770 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 99693628) qz369 0 2 Ns336p1182 Ns336p251 Ns336p1183 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 99693628) qz370 0 2 Ns336p1184 Ns336p254 Ns336p1183 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1186 := nat_lit 3247745498833096101134953584450780700302054931195878672252075183669125537214451986343925989875043050159390625 

noncomputable def Ns336p1187 := nat_lit 219437599845766641310488604691762936233663367829316393778009268538861288805418087125051863769775390625 

noncomputable def Ns336p1188 := nat_lit 19693911947423442710054221101903924850621110752385222479993016554616267690641490266457503261277080927304990625 

noncomputable def Ns336p1189 := BSN.cos_dyadic_bound_f 278682215 268435456 4 3 268435456 134217728 Ns336p1186 Ns336p121 Ns336p1187 Ns336p1188 Ns336p124 Ns336p1187 136310384 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 278682215) qz369 0 3 Ns336p1186 Ns336p121 Ns336p1187 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 278682215) qz370 0 3 Ns336p1188 Ns336p124 Ns336p1187 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1190 := Ns336p1126 152093 BSN.abs_quadSignPos (BSN.cos_quad_nat0 104 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 250134770 268435456) BSN.abs_quadSignNeg qz678 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 136310384 268435456) qz143 rfl rfl (Ns336p1181 rfl) (Ns336p1158 rfl) RS337to348.d35 RS337to348.d37 RS337to348.d39 RS337to348.d41 RS337to348.d17 (Ns336p1185 rfl rfl) (Ns336p1189 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p1191 := nat_lit 172047197828101558095358329403537028105815830776435922012804684153746785 

noncomputable def Ns336p1192 := nat_lit 119896661211705239484473855126713152160179173882403253322339839505761 

noncomputable def Ns336p1193 := nat_lit 450405685431637510338201714577153728506972600037713047623395146376803681 

noncomputable def Ns336p1194 := BSN.sin_dyadic_bound_f 323482571 268435456 3 2 268435456 134217728 Ns336p1191 Ns336p127 Ns336p1192 Ns336p1193 Ns336p130 Ns336p1192 250681938 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 323482571) qz371 0 2 Ns336p1191 Ns336p127 Ns336p1192 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 323482571) qz372 0 2 Ns336p1193 Ns336p130 Ns336p1192 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1195 := Ns336p1124 Bool.true 69141300 152093 Bool.true 323482571 14148475504056880 1 Bool.false 250681938 Bool.false Bool.false 10131288 164811 BSN.abs_quadSignPos qz373 (BSN.sfrac_eq_quadSignPos_mul Bool.false 250681938 268435456) qz143 rfl (Ns336p1190 rfl) (Ns336p1158 rfl) RS337to348.d43 RS337to348.d45 RS337to348.d17 (Ns336p1194 rfl rfl) rfl 

noncomputable def Ns336p1196 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 10) 10131288 268435456 164811 268435456 10131288 268435456 164811 268435456 5439193828294656 1266411 16777216 164811 134217728 (Ns336p1195 rfl rfl rfl rfl) 

noncomputable def Ns336p1197 := nat_lit 4510043699279944676689587937282602057521640214583538431858605738872553342063095317332992666247507842816715625861101009386545 

noncomputable def Ns336p1198 := nat_lit 10576895500643977583230644928524336637254474927428499508554380724390492659780981533203027367035444557561459392400373732868096 

noncomputable def Ns336p1199 := nat_lit 210400010174646714376554943582047826265295968033204924149625680391258473277682171570319014360196899481050407425173652246001065741902383128272002019799882596818157 

noncomputable def Ns336p1200 := @Enclosure.Real.IsNear.mulLit_ff qz489 qz490 10432183 33554432 1 33554432 Ns336p1197 Ns336p1198 Ns336p1199 

noncomputable def Ns336p1201 := nat_lit 8054895360387980268976112838383591646721882844723443505198073139184754913306693803104484502633277226011950219521949696000000000000000000000000000000000000000000000000 

noncomputable abbrev qz495 := (@HPow.hPow Real Real Real qz630 qz139 qz8)

noncomputable def Ns336p1202 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz495 1 1 0 1 10432183 33554432 1 33554432 10432183 33554432 1 33554432 

noncomputable def Ns336p1203 := @Enclosure.Real.IsNear.sqrt_image qz139 3591275245087 33554432000 672479 33554432000 173567838 173567872 16777216 (@Enclosure.Real.IsNear.of_eq qz139 (@HMul.hMul Real Real Real qz5 qz138 qz3) Bool.false 3591275245087 33554432000 672479 33554432000 (BSN.t_div_two_pi_mk qz138 672479 1000 qz143) (@Enclosure.Real.IsNear.mulLit_ff qz138 qz3 672479 1000 0 1 5340353 33554432 1 33554432 3591275245087 33554432000 672479 33554432000 (Enclosure.Real.IsNear.const Bool.false 672479 1000) RS337to348.d48 rfl)) 

noncomputable abbrev qz496 := (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 347135710 33554432 34 33554432 173567855 16777216 17 16777216 (Ns336p1203 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns336p1204 := @Enclosure.Real.IsNear.sqrt_image qz142 173567855 16777216 17 16777216 53962812 53962818 16777216 qz496 rfl 

noncomputable def Ns336p1205 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz142) 53962815 16777216 3 16777216 5216091 5216092 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz142) Bool.false 107925630 33554432 6 33554432 53962815 16777216 3 16777216 (Ns336p1204 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns336p1206 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz142)) Bool.false 10432183 33554432 1 33554432 10432183 33554432 1 33554432 (Ns336p1205 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns336p1207 := nat_lit 7947259720170746808394364712677881432078694982575177732127770231285914981722091149978336395254530577254003092096254360625 

noncomputable def Ns336p1208 := nat_lit 13404543918967047354225797697978814368578834085132600591254565640471571625129821578050409040825306097143110181585453846001065741902383128272002019799882596818157 

noncomputable abbrev qz497 := (@HMul.hMul Real Real Real qz5 qz706 (@Inv.inv Real Real.instInv qz142))

noncomputable def Ns336p1209 := @Enclosure.Real.IsNear.addLit_ff qz140 qz497 239621822943615 562949953421312 1041193632452713 42573090227486720000 Ns336p1207 Ns336p1198 Ns336p1208 Ns336p1201 

noncomputable def Ns336p1210 := nat_lit 2538928890437726520616035776508051449031918293341270156875115547147047077960285625578415121149577032682871473465668491525200255049049047040 

noncomputable abbrev qz858 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 672479 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1)))

noncomputable abbrev qz710 := (Real.cos qz858)

noncomputable abbrev qz498 := qz710

noncomputable abbrev qz146 := (@Inv.inv Real Real.instInv qz498)

noncomputable abbrev qz711 := (@HSub.hSub Real Real Real qz827 (@HMul.hMul Real Real Real qz824 qz856 qz856) qz856)

noncomputable abbrev qz499 := (@HMul.hMul Real Real Real qz627 qz625 (@HSub.hSub Real Real Real qz631 qz711 qz639))

noncomputable abbrev qz147 := (Real.cos qz499)

noncomputable def Ns336p1211 := @Enclosure.Real.IsNear.of_eq qz140 (@HMul.hMul Real Real Real qz5 qz146 qz147) Bool.false 239621822943615 

noncomputable def Ns336p1212 := @Enclosure.Real.IsNear.mulLit_tt qz146 qz147 59449257 33554432 695 

noncomputable abbrev qz148 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz498))

noncomputable abbrev qz149 := qz498

noncomputable def Ns336p1213 := @Enclosure.Real.IsNear.of_eq qz146 (@Neg.neg Real Real.instNeg qz148) Bool.true 59449257 33554432 695 33554432 (BSN.inv_eq_neg_inv_neg qz149) 

noncomputable def Ns336p1214 := @Enclosure.Real.IsNear.recentre' qz148 Bool.false 59449257 33554432 695 33554432 59449257 33554432 

noncomputable def Ns336p1215 := @Enclosure.Real.IsNear.recentre' qz149 Bool.true 18938839 33554432 534657216 81201725440000 18938839 33554432 8354019 1268776960000 

noncomputable abbrev qz712 := qz858

noncomputable abbrev qz500 := qz712

noncomputable abbrev qz150 := qz500

noncomputable def Ns336p1216 := @Enclosure.Real.IsNear.cos_image qz150 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 72830851) qz396) Bool.false 72830851 33554432 107 16777216 Bool.true 18938839 33554432 1 

noncomputable def Ns336p1217 := nat_lit 458763282003533413703053879 

noncomputable def Ns336p1218 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz141 884279719003555 140737488355328 1 500000000000000 5795695 16777216 17 16777216 5125015546030308695725 2361183241434822606848 Ns336p1217 

noncomputable def Ns336p1219 := @Enclosure.Real.IsNear.subLit_ff_p qz142 qz1 173567855 16777216 17 16777216 10 1 0 1 5795695 5795695 16777216 17 

noncomputable def Ns336p1220 := @Ns336p1219 16777216 qz496 qz379 

noncomputable def Ns336p1221 := @Enclosure.Real.IsNear.recentre' qz150 Bool.false 5125015546030308695725 2361183241434822606848 Ns336p1217 Ns336p457 72830851 33554432 107 16777216 (@Ns336p1218 Ns336p457 RS337to348.d47 (Ns336p1220 rfl rfl) rfl) 

noncomputable def Ns336p1222 := nat_lit 2900126842316958845632512 

noncomputable def Ns336p1223 := nat_lit 194566699168539139989601018249681745878053697644770247617644399833739280919877141085843425 

noncomputable def Ns336p1224 := nat_lit 180468656028383376705345110207518346455653528001341539704795567934989718275908111313435361280 

noncomputable def Ns336p1225 := nat_lit 8323338157878310051110913411007267348750017912902359094123464144209209275216621760481 

noncomputable def Ns336p1226 := nat_lit 509565974322489754137443725365548656009671231897777378036249609194036063689423114027692001 

noncomputable def Ns336p1227 := nat_lit 3308592027187028572931327020471169685020314680024594894587918745474811501724982040746314956800 

noncomputable def Ns336p1228 := BSN.sin_dyadic_bound_f 41213281211 68719476736 3 2 33554432 9689454 Ns336p1223 Ns336p1224 Ns336p1225 Ns336p1226 Ns336p1227 Ns336p1225 18938839 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 41213281211) qz366 0 2 Ns336p1223 Ns336p1224 Ns336p1225 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 41213281211) qz367 0 2 Ns336p1226 Ns336p1227 Ns336p1225 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1229 := @Ns336p1216 4840000 (Ns336p1221 rfl) (Enclosure.sfrac_false_div 72830851 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 72830851) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns336p1222) qz413) 226375608064910080 72057594037927936 Bool.false 18938839 33554432 0 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q1 72830851 33554432 226375608064910080 72057594037927936 0 Ns336p1222 Ns336p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 18938839 33554432 Ns336p1222 Ns336p98 41213281211 68719476736 9689454 9680000 (Ns336p1228 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable abbrev qz151 := (@Neg.neg Real Real.instNeg qz498)

noncomputable def Ns336p1230 := @Enclosure.Real.IsNear.inv_image qz151 18938839 33554432 8354019 1268776960000 29724281 29724976 16777216 (@Enclosure.Real.IsNear.neg qz149 Bool.true 18938839 33554432 8354019 1268776960000 (Ns336p1215 (Ns336p1229 rfl rfl) rfl)) 

noncomputable def Ns336p1231 := Ns336p1213 (@Enclosure.Real.IsNear.neg qz148 Bool.false 59449257 33554432 695 33554432 (@Ns336p1214 695 33554432 (Ns336p1230 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p1232 := @Enclosure.Real.IsNear.recentre' qz147 Bool.true 4030695 16777216 

noncomputable abbrev qz152 := qz499

noncomputable def Ns336p1233 := @Enclosure.Real.IsNear.cos_image qz152 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 60848203)) qz396) Bool.true 60848203 33554432 

noncomputable def Ns336p1234 := nat_lit 71836879176072743799078596605 

noncomputable def Ns336p1235 := nat_lit 13014482592686429178201809943090009 

noncomputable def Ns336p1236 := @Enclosure.Real.IsNear.recentre' qz152 Bool.true Ns336p1234 Ns336p471 Ns336p1235 

noncomputable abbrev qz501 := (@HSub.hSub Real Real Real qz631 qz711 qz639)

noncomputable abbrev qz153 := qz501

noncomputable def Ns336p1237 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz153 884279719003555 140737488355328 1 500000000000000 81237732396511 

noncomputable abbrev qz502 := qz711

noncomputable abbrev qz154 := qz502

noncomputable def Ns336p1238 := @Enclosure.Real.IsNear.subLit_tf qz154 qz26 63645546352095 281474976710656 482266591 281474976710656 1 16 

noncomputable abbrev qz713 := (@HMul.hMul Real Real Real qz824 qz856 qz856)

noncomputable abbrev qz503 := qz713

noncomputable abbrev qz155 := qz503

noncomputable def Ns336p1239 := @Enclosure.Real.IsNear.subLit_ff_n qz155 qz141 33590080533025 281474976710656 197053919 281474976710656 5795695 16777216 17 16777216 

noncomputable def Ns336p1240 := @Enclosure.Real.IsNear.mulLit_ff qz141 qz141 5795695 16777216 17 16777216 5795695 16777216 17 16777216 33590080533025 281474976710656 

noncomputable def Ns336p1241 := nat_lit 442491566079098982440229068419666047530531458137573235054759339769496870223176631980086316776722321 

noncomputable def Ns336p1242 := nat_lit 2576161487367411861490478722193843135675655306325890349559700385924174716485176909816591716241 

noncomputable def Ns336p1243 := nat_lit 2672989697448383272600997642342941065046433766505027059846404972549917086738232242050747740097253265 

noncomputable def Ns336p1244 := BSN.cos_dyadic_bound_t 60848203 33554432 4 3 16777216 4840000 Ns336p1241 Ns336p328 Ns336p1242 Ns336p1243 Ns336p331 Ns336p1242 4030695 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 60848203) (BSN.cosEvenQ 33554432) 0 3 Ns336p1241 Ns336p328 Ns336p1242 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 60848203) (BSN.cosOddQ 33554432) 0 3 Ns336p1243 Ns336p331 Ns336p1242 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1245 := @Ns336p1232 892817216 81201725440000 4030695 16777216 13950269 1268776960000 (@Ns336p1233 181 16777216 Bool.true 4030695 16777216 1 4840000 (@Ns336p1236 Ns336p474 60848203 33554432 181 16777216 (@Ns336p1237 281474976710656 482266591 281474976710656 Ns336p1234 Ns336p471 Ns336p1235 Ns336p474 RS337to348.d47 (@Ns336p1238 0 1 1299803718344176 81237732396511 281474976710656 482266591 281474976710656 (@Ns336p1239 1067795078587109867520 63645546352095 281474976710656 482266591 281474976710656 (@Ns336p1240 197053919 281474976710656 (Ns336p1220 rfl rfl) (Ns336p1220 rfl rfl) rfl) (Ns336p1220 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 60848203 33554432) (BSN.cos_neg_of_bound 60848203 33554432 Bool.true 4030695 16777216 1 4840000 (Ns336p1244 rfl rfl)) rfl rfl) 

noncomputable def Ns336p1246 := nat_lit 19602293198916561160250020873596550365859764401739354337122205663898168543434892150159305408533096324237536146257025 

noncomputable def Ns336p1247 := nat_lit 2521728396569246669585858566409191283525103313309788586748690777871726193375821479130513040312634601011624191379636224 

noncomputable def Ns336p1248 := nat_lit 33053717940105405688322806707384038425181526665650874492399885304973791728369337667545815678804521574414662710152688040631680192369868723341083691891286903 

noncomputable def Ns336p1249 := nat_lit 1920436706635470454448726853938959037476034842663632274913328442379177788092301798606988073023146921637523226624000000000000000000000000000000000000000000000000 

noncomputable def Ns336p1250 := @Enclosure.Real.IsNear.mulLit_ff qz706 (@Inv.inv Real Real.instInv qz142) Ns336p1246 Ns336p1247 Ns336p1248 Ns336p1249 405425 4194304 1 16777216 Ns336p1207 

noncomputable def Ns336p1251 := nat_lit 34594581637926334797989550258805232993475032872901588759350837433132029146822510231843596795315976281195519725 

noncomputable def Ns336p1252 := nat_lit 4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537406063869952 

noncomputable def Ns336p1253 := nat_lit 291436848016139509769422504529410331531456775146903940411722191939402381832257574406002112554889842061706841430473354008833126975019192193085187358803 

noncomputable def Ns336p1254 := nat_lit 17885460580098167568899009879109999513961699257266076979351494855984838568533787490865104580513638645760000000000000000000000000000000000000000000000000 

noncomputable def Ns336p1255 := @Enclosure.Real.IsNear.mulLit_tf (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz141) qz466 Ns336p1251 Ns336p1252 Ns336p1253 Ns336p1254 566629 536870912 1 536870912 Ns336p1246 

noncomputable abbrev qz859 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 672479 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1)))

noncomputable abbrev qz714 := (@HMul.hMul Real Real Real qz824 qz822 (@HSub.hSub Real Real Real qz827 qz859 qz830))

noncomputable abbrev qz504 := (@HMul.hMul Real Real Real qz627 qz714 qz714)

noncomputable abbrev qz505 := qz714

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz349 qz504 qz505)

noncomputable abbrev qz157 := (Real.sin qz499)

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz349 qz320 qz505)

noncomputable abbrev qz506 := (@HMul.hMul Real Real Real qz5 qz158 qz694)

noncomputable def Ns336p1256 := @HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 qz156 qz157) (@HMul.hMul Real Real Real qz5 qz506 qz147) 

noncomputable abbrev qz715 := (Real.sin qz858)

noncomputable abbrev qz507 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz627 qz625 qz715))

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz349 qz320 qz507)

noncomputable abbrev qz508 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz627 qz695 qz710))

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz349 qz320 qz508)

noncomputable abbrev qz509 := qz715

noncomputable abbrev qz161 := qz509

noncomputable def Ns336p1257 := @HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns336p1256 (@HMul.hMul Real Real Real qz5 qz159 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz141))) (@HMul.hMul Real Real Real qz5 qz160 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz141))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz475 qz161) qz140) 

noncomputable abbrev qz716 := (BSN.cos_two_pi_p_ne_zero_mk qz138 672479 1000 10 qz143 rfl rfl (@BSN.floor_sqrt_eq_dec qz138 672479 1000 10 qz143 rfl rfl rfl))

noncomputable abbrev qz510 := qz716

noncomputable def Ns336p1258 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz141) (@HMul.hMul Real Real Real qz5 qz146 Ns336p1257) Bool.true Ns336p1251 Ns336p1252 Ns336p1253 Ns336p1254 (BSN.iteratedDeriv_three_correction_mk qz141 qz510) 

noncomputable def Ns336p1259 := nat_lit 72740170974977486067627760085900406068478412191696957707589554022488591565116210986531994568830773475 

noncomputable def Ns336p1260 := nat_lit 17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592 

noncomputable def Ns336p1261 := nat_lit 9571639425926118676593716984848905975982532261498130111672694965253017107976242709422976608226275678292979561100272527461777016333826183567063 

noncomputable def Ns336p1262 := @Enclosure.Real.IsNear.mulLit_tf qz146 Ns336p1257 475591151 268435456 349 268435456 Ns336p1259 Ns336p1260 Ns336p1261 

noncomputable def Ns336p1263 := nat_lit 1041070824727542207628663738672039443275524492914909321078535568433862561856733372601744752640000000000000000000000000000000000000000000000000000 

noncomputable def Ns336p1264 := @Enclosure.Real.IsNear.of_eq qz146 (@Neg.neg Real Real.instNeg qz148) Bool.true 475591151 268435456 349 268435456 (BSN.inv_eq_neg_inv_neg qz149) 

noncomputable def Ns336p1265 := @Enclosure.Real.IsNear.recentre' qz148 Bool.false 951182302 536870912 698 536870912 475591151 268435456 

noncomputable def Ns336p1266 := @Enclosure.Real.IsNear.recentre' qz149 Bool.true 303023275 536870912 17186470912 41575283425280000 303023275 536870912 16783663 40600862720000 

noncomputable abbrev qz511 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1165295845) (@Nat.cast Real Real.instNatCast 536870912))

noncomputable def Ns336p1267 := @Enclosure.Real.IsNear.cos_image qz150 qz511 Bool.false 1165295845 536870912 215 536870912 Bool.true 303023275 536870912 1 

noncomputable def Ns336p1268 := nat_lit 458763282750304548599198263 

noncomputable def Ns336p1269 := nat_lit 1152921504606846976000000000000000 

noncomputable def Ns336p1270 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz141 884279719003555 140737488355328 1 500000000000000 92731297 268435456 17 268435456 82000405253995202760835 37778931862957161709568 Ns336p1268 

noncomputable def Ns336p1271 := @Enclosure.Real.IsNear.subLit_ff_p qz142 qz1 2777085857 268435456 17 268435456 10 1 0 1 92731297 92731297 268435456 17 

noncomputable def Ns336p1272 := @Enclosure.Real.IsNear.sqrt_image qz139 57460411318661 536870912000 672479 536870912000 2777085840 2777085874 268435456 (@Enclosure.Real.IsNear.of_eq qz139 (@HMul.hMul Real Real Real qz5 qz138 qz3) Bool.false 57460411318661 536870912000 672479 536870912000 (BSN.t_div_two_pi_mk qz138 672479 1000 qz143) (@Enclosure.Real.IsNear.mulLit_ff qz138 qz3 672479 1000 0 1 85445659 536870912 1 536870912 57460411318661 536870912000 672479 536870912000 (Enclosure.Real.IsNear.const Bool.false 672479 1000) RS337to348.d60 rfl)) 

noncomputable def Ns336p1273 := @Ns336p1271 268435456 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 5554171714 536870912 34 536870912 2777085857 268435456 17 268435456 (Ns336p1272 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns336p1274 := @Enclosure.Real.IsNear.recentre' qz150 Bool.false 82000405253995202760835 37778931862957161709568 Ns336p1268 Ns336p1269 1165295845 536870912 215 536870912 (@Ns336p1270 Ns336p1269 RS337to348.d59 (Ns336p1273 rfl rfl) rfl) 

noncomputable def Ns336p1275 := nat_lit 46402350709825562612858880 

noncomputable def Ns336p1276 := nat_lit 835680751534225070372139189630816897431336745588752695460734831856292619554721924325570286922403745 

noncomputable def Ns336p1277 := nat_lit 35750445075880078108430961090074658928853124534914302923360461776436746637444812480855140110241 

noncomputable def Ns336p1278 := nat_lit 2188629800916657092752950894143707943824759047673676722097191499828366439339239653061048414569926561 

noncomputable def Ns336p1279 := BSN.sin_dyadic_bound_f 659417064381 1099511627776 3 2 536870912 155031251 Ns336p1276 Ns336p915 Ns336p1277 Ns336p1278 Ns336p918 Ns336p1277 303023275 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 659417064381) (BSN.sinEvenQ 1099511627776) 0 2 Ns336p1276 Ns336p915 Ns336p1277 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 659417064381) (BSN.sinOddQ 1099511627776) 0 2 Ns336p1278 Ns336p918 Ns336p1277 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1280 := @Ns336p1267 77440000 (Ns336p1274 rfl) (Enclosure.sfrac_false_div 1165295845 536870912) (BSN.cos_reduce1 qz511 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns336p1275) qz699) 226375608064910080 72057594037927936 Bool.false 303023275 536870912 0 1000000000000000 154880000 77440000 (BSN.sin_reduce_arg_pos_rat_q1 1165295845 536870912 226375608064910080 72057594037927936 0 Ns336p1275 Ns336p913 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 303023275 536870912 Ns336p1275 Ns336p913 659417064381 1099511627776 155031251 154880000 (Ns336p1279 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p1281 := @Enclosure.Real.IsNear.inv_image qz151 303023275 536870912 16783663 40600862720000 475590802 475591500 268435456 (@Enclosure.Real.IsNear.neg qz149 Bool.true 303023275 536870912 16783663 40600862720000 (Ns336p1266 (Ns336p1280 rfl rfl) rfl)) 

noncomputable def Ns336p1282 := Ns336p1264 (@Enclosure.Real.IsNear.neg qz148 Bool.false 475591151 268435456 349 268435456 (@Ns336p1265 349 268435456 (Ns336p1281 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p1283 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns336p1256 (@HMul.hMul Real Real Real qz5 qz159 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz141))) (@HMul.hMul Real Real Real qz5 qz160 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz141))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz475 qz161) qz140) 

noncomputable def Ns336p1284 := nat_lit 1597822196262036703426692839260624422576151152793783023767688604327127527260254315899676929954754357475 

noncomputable def Ns336p1285 := nat_lit 9200077752970685915004716467979015050446787886911033094807208573861792704783840793161577917597441552601842593522131550820599320659179996354263 

noncomputable def Ns336p1286 := nat_lit 587440228029415796291080187154341087673304409042790173961471885673625 

noncomputable def Ns336p1287 := nat_lit 12512400009948783772259008072296195598743451112141903309629143522394692014214139496721223760946549814813 

noncomputable def Ns336p1288 := nat_lit 35058230021589810586288373163293244933378061699828311654400000000000000000000000000000000000000000000000000 

noncomputable def Ns336p1289 := nat_lit 490267782511202995082173536563277255844250622180921670680814908139101973941466561979579140404526326045572778517156266023106442290594301264702350028340964095118698086400 

noncomputable def Ns336p1290 := nat_lit 929506290392079018394215537490048863888994256141257537720650726142865782055716000317344663291637557475 

noncomputable def Ns336p1291 := @Enclosure.Real.IsNear.subLit_ft (@HSub.hSub Real Real Real qz11 Ns336p1256 (@HMul.hMul Real Real Real qz5 qz159 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 2 Zeta.RiemannSiegel.correction qz141))) (@HMul.hMul Real Real Real qz5 qz160 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz141)) Ns336p1290 Ns336p1260 

noncomputable def Ns336p1292 := nat_lit 7767282638737213139038554612476604317816402442575715339732857079614387442674331196125713420244016746541742099498150361806261886068130301777623 

noncomputable def Ns336p1293 := nat_lit 37098985321002291572627235325986003660456541233954335437363762816535092415012226684375 

noncomputable def Ns336p1294 := nat_lit 971334446112864535459730953411759453321203419526069760625906204869452142602604249088 

noncomputable def Ns336p1295 := nat_lit 1051717107697476247342087083617614478727353197648639707182934683538948272451185482608479205809927033050053361180999011268791 

noncomputable def Ns336p1296 := nat_lit 764179041241664873364481470633209342973108691365446386003142286027381538816000000000000000000000000000000000000000000000000000 

noncomputable def Ns336p1297 := nat_lit 1552019737993026152082994822990589832432728487609393487198829364712114863864915475045378774412072002132840005050604467567438433644384146910891212271580213477417369607654384851718294732800 

noncomputable def Ns336p1298 := nat_lit 2369972172038814751216729295885882900477231572082232521783039173931111003925 

noncomputable def Ns336p1299 := nat_lit 226156424291633194186662080095093570025917938800079226639565593765455331328 

noncomputable def Ns336p1300 := nat_lit 34657296745548741735851043499962589805627155926791053340295820809124708895424242633635729817542982657949153 

noncomputable def Ns336p1301 := nat_lit 486098758388344558351443532933201687262966405619294832678666240000000000000000000000000000000000000000000000000 

noncomputable def Ns336p1302 := @Enclosure.Real.IsNear.subLit_tt_p Ns336p1256 (@HMul.hMul Real Real Real qz5 qz159 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 2 Zeta.RiemannSiegel.correction qz141)) Ns336p1298 Ns336p1299 Ns336p1300 Ns336p1301 

noncomputable def Ns336p1303 := nat_lit 1112874005627015790431385827766603755656335024254199923437644613582221995046789497949966087436132968675 

noncomputable def Ns336p1304 := nat_lit 7693057597255229549763748487216059900581789180908108752186319373105634738495275019128279086532814061638546548362174877149783861130617145169623 

noncomputable def Ns336p1305 := nat_lit 210213818991653037209103102304736771577800280243548196667978870930874400306870140564023122143188539111938625575693592676088396311242227914155131549814033122642983323714768076800 

noncomputable def Ns336p1306 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz5 qz156 qz157) (@HMul.hMul Real Real Real qz5 qz506 qz147) 

noncomputable def Ns336p1307 := nat_lit 1608152207168264179957008217012705076400878624807549207039784713739287152875 

noncomputable def Ns336p1308 := nat_lit 6696179132188210708517282244532860882150862301442339725865023570356072183060142341281747353542982657949153 

noncomputable def Ns336p1309 := nat_lit 784546699715767979813278928295303255381261075 

noncomputable def Ns336p1310 := nat_lit 44601490397061246283071436545296723011960832 

noncomputable def Ns336p1311 := nat_lit 180694487461615744471544500697284168333993487318540019553789256463 

noncomputable def Ns336p1312 := nat_lit 3141339599413570715260950279178158080000000000000000000000000000000000 

noncomputable def Ns336p1313 := nat_lit 105704291072491580024175012315860196003164638110153408948520512149986303138235248352793599409696516498351436066298265600 

noncomputable def Ns336p1314 := nat_lit 49372738725936842093601675082193533575515583125354981323483075265125 

noncomputable def Ns336p1315 := @Enclosure.Real.IsNear.mulLit_tt qz156 qz157 Ns336p1314 Ns336p927 

noncomputable def Ns336p1316 := nat_lit 1725050021966897644160716760546679582352584666578550356393140014344942297551901787320535974071 

noncomputable def Ns336p1317 := nat_lit 191561942608236107294793378393788647952342390272950272000000000000000000000000000000000000000000000 

noncomputable def Ns336p1318 := nat_lit 1345833947845236902585202269195012073681462025 

noncomputable def Ns336p1319 := nat_lit 356811923176489970264571492362373784095686656 

noncomputable def Ns336p1320 := nat_lit 1027222540138638775344352838618222154976755046262037519094031 

noncomputable def Ns336p1321 := nat_lit 332306998946228968225951765070086144000000000000000000000000000000 

noncomputable abbrev qz162 := qz504

noncomputable abbrev qz163 := qz505

noncomputable def Ns336p1322 := @Enclosure.Real.IsNear.mulLit_ft qz162 qz163 Ns336p1318 Ns336p1319 Ns336p1320 Ns336p1321 

noncomputable def Ns336p1323 := nat_lit 458763282310114501483393591 

noncomputable def Ns336p1324 := nat_lit 576460752303423488000000000000000 

noncomputable def Ns336p1325 := @Enclosure.Real.IsNear.mulLit_tt qz163 qz163 36685609547140373262205 18889465931478580854784 Ns336p1323 Ns336p1324 36685609547140373262205 18889465931478580854784 

noncomputable abbrev qz717 := (@HSub.hSub Real Real Real qz827 qz859 qz830)

noncomputable abbrev qz512 := qz717

noncomputable abbrev qz164 := qz512

noncomputable def Ns336p1326 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz164 884279719003555 140737488355328 1 500000000000000 41486431 134217728 17 134217728 

noncomputable abbrev qz718 := qz859

noncomputable abbrev qz513 := qz718

noncomputable abbrev qz165 := qz513

noncomputable def Ns336p1327 := @Enclosure.Real.IsNear.subLit_ff_n qz165 qz128 92731297 134217728 17 134217728 1 1 0 1 41486431 

noncomputable def Ns336p1328 := @Enclosure.Real.IsNear.mulLit_ff qz0 qz141 2 1 0 1 92731297 268435456 17 268435456 92731297 134217728 17 

noncomputable def Ns336p1329 := @Enclosure.Real.IsNear.recentre' qz157 Bool.true 260573304 268435456 

noncomputable def Ns336p1330 := @Enclosure.Real.IsNear.sin_image qz152 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 973571943)) qz479) Bool.true 973571943 536870912 

noncomputable def Ns336p1331 := nat_lit 18390254055808105699572917926045 

noncomputable def Ns336p1332 := nat_lit 10141204801825835211973625643008 

noncomputable def Ns336p1333 := nat_lit 208231767068026340271317485876175061 

noncomputable def Ns336p1334 := @Enclosure.Real.IsNear.recentre' qz152 Bool.true Ns336p1331 Ns336p1332 Ns336p1333 

noncomputable def Ns336p1335 := nat_lit 309485009821345068724781056000000000000000 

noncomputable def Ns336p1336 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz153 884279719003555 140737488355328 1 500000000000000 20796874179734719 

noncomputable def Ns336p1337 := @Enclosure.Real.IsNear.subLit_tf qz154 qz26 16293274552364223 72057594037927936 7716267139 72057594037927936 1 16 

noncomputable def Ns336p1338 := @Enclosure.Real.IsNear.subLit_ff_n qz155 qz141 8599093443302209 72057594037927936 3152864387 72057594037927936 92731297 268435456 17 268435456 

noncomputable def Ns336p1339 := nat_lit 4373692584197086079090688 

noncomputable def Ns336p1340 := @Enclosure.Real.IsNear.mulLit_ff qz141 qz141 92731297 268435456 17 268435456 92731297 268435456 17 268435456 8599093443302209 72057594037927936 

noncomputable def Ns336p1341 := nat_lit 322910043246699073491469343059613748291916849673198400593286899673314107940562377083959683758397914008037564138401 

noncomputable def Ns336p1342 := nat_lit 725131206394223998498011064856510516055813025800857364338357251421344179004235680101111047559935320438916001 

noncomputable def Ns336p1343 := nat_lit 1610990778067383172651313885249663317018260258652463894040437402356242877968891382385902061782649503116615331398561 

noncomputable def Ns336p1344 := BSN.sin_dyadic_bound_f 973571943 536870912 4 3 268435456 77440000 Ns336p1341 Ns336p984 Ns336p1342 Ns336p1343 Ns336p987 Ns336p1342 260573304 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 973571943) (BSN.sinEvenQ 536870912) 0 3 Ns336p1341 Ns336p984 Ns336p1342 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 973571943) (BSN.sinOddQ 536870912) 0 3 Ns336p1343 Ns336p987 Ns336p1342 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1345 := @Ns336p1329 14285075456 20787641712640000 32571663 33554432 13950269 20300431360000 (@Ns336p1330 181 268435456 Bool.true 260573304 268435456 1 77440000 (@Ns336p1334 Ns336p1335 973571943 536870912 181 268435456 (@Ns336p1336 72057594037927936 7716267139 72057594037927936 Ns336p1331 Ns336p1332 Ns336p1333 Ns336p1335 RS337to348.d59 (@Ns336p1337 0 1 332749986875755504 20796874179734719 72057594037927936 7716267139 72057594037927936 (@Ns336p1338 Ns336p1339 16293274552364223 72057594037927936 7716267139 72057594037927936 (@Ns336p1340 3152864387 72057594037927936 (Ns336p1273 rfl rfl) (Ns336p1273 rfl rfl) rfl) (Ns336p1273 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 973571943 536870912) (BSN.sin_neg_of_bound 973571943 536870912 Bool.false 260573304 268435456 1 77440000 (Ns336p1344 rfl rfl)) rfl rfl) 

noncomputable def Ns336p1346 := nat_lit 97321021505458271591393504242026416325 

noncomputable def Ns336p1347 := nat_lit 1329227995784915872903807060280344576 

noncomputable def Ns336p1348 := nat_lit 37140661622814673581495078348728395804895470409671491 

noncomputable def Ns336p1349 := @Enclosure.Real.IsNear.mulLit_tt qz506 qz147 Ns336p1346 Ns336p1347 Ns336p1348 

noncomputable def Ns336p1350 := nat_lit 1237940039285380274899124224000000000000000000000000000000 

noncomputable def Ns336p1351 := nat_lit 1376289846930343504450180773 

noncomputable def Ns336p1352 := @Enclosure.Real.IsNear.mulLit_tf qz158 qz461 110056828641421119786615 18889465931478580854784 Ns336p1351 Ns336p1324 884279719003555 

noncomputable def Ns336p1353 := @Enclosure.Real.IsNear.mulLit_ft qz320 qz163 3 1 0 1 36685609547140373262205 18889465931478580854784 Ns336p1323 

noncomputable def Ns336p1354 := @Enclosure.Real.IsNear.recentre' qz147 Bool.true 64491448 268435456 

noncomputable def Ns336p1355 := @Enclosure.Real.IsNear.cos_image qz152 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 973571943)) qz479) Bool.true 973571943 536870912 

noncomputable def Ns336p1356 := nat_lit 124550661185166499797554499211145706131343125225994212162691451699579076731287987883235012791853335022159134770081 

noncomputable def Ns336p1357 := nat_lit 752381865838418451420359918707407400562243390437625718973601059158410269757290225473742074944996281426419666437025 

noncomputable def Ns336p1358 := BSN.cos_dyadic_bound_t 973571943 536870912 4 3 268435456 77440000 Ns336p1356 Ns336p1001 Ns336p1342 Ns336p1357 Ns336p1003 Ns336p1342 64491448 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 973571943) (BSN.cosEvenQ 536870912) 0 3 Ns336p1356 Ns336p1001 Ns336p1342 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 973571943) (BSN.cosOddQ 536870912) 0 3 Ns336p1357 Ns336p1003 Ns336p1342 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1359 := @Ns336p1354 14285075456 20787641712640000 8061431 33554432 13950269 20300431360000 (@Ns336p1355 181 268435456 Bool.true 64491448 268435456 1 77440000 (@Ns336p1334 Ns336p1335 973571943 536870912 181 268435456 (@Ns336p1336 72057594037927936 7716267139 72057594037927936 Ns336p1331 Ns336p1332 Ns336p1333 Ns336p1335 RS337to348.d59 (@Ns336p1337 0 1 332749986875755504 20796874179734719 72057594037927936 7716267139 72057594037927936 (@Ns336p1338 Ns336p1339 16293274552364223 72057594037927936 7716267139 72057594037927936 (@Ns336p1340 3152864387 72057594037927936 (Ns336p1273 rfl rfl) (Ns336p1273 rfl rfl) rfl) (Ns336p1273 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 973571943 536870912) (BSN.cos_neg_of_bound 973571943 536870912 Bool.true 64491448 268435456 1 77440000 (Ns336p1358 rfl rfl)) rfl rfl) 

noncomputable abbrev qz166 := (@Ns336p1326 36685609547140373262205 18889465931478580854784 Ns336p1323 Ns336p1324 RS337to348.d59 (@Ns336p1327 41486431 134217728 17 134217728 (@Ns336p1328 134217728 qz347 (Ns336p1273 rfl rfl) rfl) qz642 rfl rfl) rfl)

noncomputable def Ns336p1360 := @Ns336p1306 Ns336p1307 Ns336p1299 Ns336p1308 Ns336p1301 Ns336p1309 Ns336p1310 Ns336p1311 Ns336p1312 Ns336p1313 Ns336p1298 Ns336p1299 Ns336p1300 Ns336p1301 (@Ns336p1315 Ns336p1316 Ns336p1317 32571663 33554432 13950269 20300431360000 Ns336p1307 Ns336p1299 Ns336p1308 Ns336p1301 (@Ns336p1322 36685609547140373262205 18889465931478580854784 Ns336p1323 Ns336p1324 Ns336p1314 Ns336p927 Ns336p1316 Ns336p1317 (@Ns336p1325 Ns336p1323 Ns336p1324 Ns336p1318 Ns336p1319 Ns336p1320 Ns336p1321 qz166 qz166 rfl) qz166 rfl) (Ns336p1345 rfl) rfl) (@Ns336p1349 Ns336p1350 8061431 33554432 13950269 20300431360000 Ns336p1309 Ns336p1310 Ns336p1311 Ns336p1312 (@Ns336p1352 70368744177664 1 250000000000000 Ns336p1346 Ns336p1347 Ns336p1348 Ns336p1350 (@Ns336p1353 Ns336p1324 110056828641421119786615 18889465931478580854784 Ns336p1351 Ns336p1324 qz480 qz166 rfl) RS337to348.d61 rfl) (Ns336p1359 rfl) rfl) rfl rfl 

noncomputable def Ns336p1361 := nat_lit 1358775586937632037285035845438363 

noncomputable def Ns336p1362 := nat_lit 174379377571785605120000000000000000000 

noncomputable def Ns336p1363 := nat_lit 1893155534642424361172563252300332453122009985528481662248466911676120983449705 

noncomputable def Ns336p1364 := @Enclosure.Real.IsNear.mulLit_tf qz159 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz141) 587840769161744192873835 37778931862957161709568 Ns336p1361 Ns336p1362 Ns336p1363 

noncomputable def Ns336p1365 := nat_lit 463168356949264781694283940034751631413079938662562256157830336031652518559744 

noncomputable def Ns336p1366 := nat_lit 45168713985641605135498776103678811942559733133017871868383633981861216014904169324077993190773965938961 

noncomputable def Ns336p1367 := nat_lit 95522380155208109170560183829151167871638586420680798250392785753422692352000000000000000000000000000000000 

noncomputable def Ns336p1368 := nat_lit 452925195645877345761678615146121 

noncomputable abbrev qz167 := qz507

noncomputable def Ns336p1369 := @Enclosure.Real.IsNear.mulLit_ft qz320 qz167 3 1 0 1 195946923053914730957945 37778931862957161709568 Ns336p1368 

noncomputable def Ns336p1370 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz161 884279719003555 140737488355328 1 500000000000000 221589299 268435456 16783663 40600862720000 195946923053914730957945 

noncomputable def Ns336p1371 := @Enclosure.Real.IsNear.recentre' qz161 Bool.false 443178598 536870912 17186470912 41575283425280000 221589299 268435456 16783663 40600862720000 

noncomputable def Ns336p1372 := @Enclosure.Real.IsNear.sin_image qz150 qz511 Bool.false 1165295845 536870912 215 536870912 Bool.false 443178598 536870912 1 

noncomputable def Ns336p1373 := nat_lit 464282973272380985797014407999827198421377682271322570501707511236507649417795488986419428352495521 

noncomputable def Ns336p1374 := nat_lit 1392777418926991197234826362077301445946275340564897882899275812785970074760111577334296574777266081 

noncomputable def Ns336p1375 := BSN.cos_dyadic_bound_f 659417064381 1099511627776 3 2 536870912 155031251 Ns336p1373 Ns336p1020 Ns336p1277 Ns336p1374 Ns336p1022 Ns336p1277 443178598 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 659417064381) (BSN.cosEvenQ 1099511627776) 0 2 Ns336p1373 Ns336p1020 Ns336p1277 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 659417064381) (BSN.cosOddQ 1099511627776) 0 2 Ns336p1374 Ns336p1022 Ns336p1277 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1376 := @Ns336p1372 77440000 (Ns336p1274 rfl) (Enclosure.sfrac_false_div 1165295845 536870912) (BSN.sin_reduce1 qz511 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns336p1275) qz699) 226375608064910080 72057594037927936 Bool.false 443178598 536870912 0 1000000000000000 154880000 77440000 (BSN.sin_reduce_arg_pos_rat_q1 1165295845 536870912 226375608064910080 72057594037927936 0 Ns336p1275 Ns336p913 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 443178598 536870912 Ns336p1275 Ns336p913 659417064381 1099511627776 155031251 154880000 (Ns336p1375 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable abbrev qz514 := (@HMul.hMul Real Real Real qz627 qz625 qz715)

noncomputable abbrev qz168 := qz514

noncomputable abbrev qz515 := (@Enclosure.Real.IsNear.neg qz168 Bool.false 195946923053914730957945 37778931862957161709568 Ns336p1368 Ns336p1362 (@Ns336p1370 37778931862957161709568 Ns336p1368 Ns336p1362 RS337to348.d59 (Ns336p1371 (Ns336p1376 rfl rfl) rfl) rfl))

noncomputable def Ns336p1377 := @Ns336p1369 Ns336p1362 587840769161744192873835 37778931862957161709568 Ns336p1361 Ns336p1362 qz480 qz515 rfl 

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz349 qz504 (Real.cos qz499))

noncomputable def Ns336p1378 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz169) (@HMul.hMul Real Real Real qz5 qz461 qz157) 

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz349 qz316 qz507)

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz349 qz508 (Zeta.RiemannSiegel.correction qz487))

noncomputable def Ns336p1379 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz141) (@HMul.hMul Real Real Real qz5 qz146 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns336p1378 (@HMul.hMul Real Real Real qz5 qz170 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c8 1 Zeta.RiemannSiegel.correction qz141))) qz171)) 

noncomputable def Ns336p1380 := @Enclosure.Real.IsNear.mulLit_tt qz146 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns336p1378 (@HMul.hMul Real Real Real qz5 qz170 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 1 Zeta.RiemannSiegel.correction qz141))) qz171) 475591151 

noncomputable def Ns336p1381 := nat_lit 3980636583884682835851509046055258612500992444934034658370813362076455 

noncomputable def Ns336p1382 := nat_lit 1725436586697640946858688965569256363112777243042596638790631055949824 

noncomputable def Ns336p1383 := nat_lit 23592831802858032250097685553512701409569019171839748457650702883387046228738568929741474214712671 

noncomputable def Ns336p1384 := nat_lit 88962149019546908485293559570937573790213639308401195565604405248000000000000000000000000000000000000 

noncomputable def Ns336p1385 := nat_lit 12384551052355074339439381117826859666271157915097566963022335115363545 

noncomputable def Ns336p1386 := @Enclosure.Real.IsNear.subLit_ff_n (@HSub.hSub Real Real Real qz11 Ns336p1378 (@HMul.hMul Real Real Real qz5 qz170 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz141))) qz171 Ns336p1385 Ns336p1382 

noncomputable def Ns336p1387 := nat_lit 19942195221822204963769446845469521764369954908013358741578039155371513353426825532361674458404191 

noncomputable def Ns336p1388 := nat_lit 908450405803215964311619355025080217934227453381956875 

noncomputable def Ns336p1389 := nat_lit 41870049450463187577617393613777682639083133613404934443703023847506931317933 

noncomputable def Ns336p1390 := nat_lit 1020328782661521416922576410093264565028310220800000000000000000000000000000000000 

noncomputable def Ns336p1391 := nat_lit 381269238413181324213523014111115092683857935083841597592154525161092662017550186619300264433491005274976050733726438522880 

noncomputable def Ns336p1392 := nat_lit 156895175432766473652259589199130232944412630334953135 

noncomputable def Ns336p1393 := nat_lit 11972621413014756705924586149611790497021399392059392 

noncomputable def Ns336p1394 := nat_lit 10093765340533255839648674341649009635236264725594731395127594215022778433 

noncomputable def Ns336p1395 := nat_lit 843246927819439187539319347184516169444884480000000000000000000000000000000000 

noncomputable def Ns336p1396 := @Enclosure.Real.IsNear.subLit_ff_p Ns336p1378 (@HMul.hMul Real Real Real qz5 qz170 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz141)) Ns336p1392 Ns336p1393 Ns336p1394 Ns336p1395 

noncomputable def Ns336p1397 := nat_lit 10226426663332467716098534435665739200058467316760254660563567019195175 

noncomputable def Ns336p1398 := nat_lit 18877307788772304670582685683449913872669373229442277935726321256161834853236502396214237280343391 

noncomputable def Ns336p1399 := nat_lit 148275541120000802293466392546209539087300622348494447251173160514968443771028614858237142993448459682188717249136311664640 

noncomputable def Ns336p1400 := @Enclosure.Real.IsNear.subLit_ft (@Neg.neg Real Real.instNeg qz169) (@HMul.hMul Real Real Real qz5 qz461 qz157) 

noncomputable def Ns336p1401 := nat_lit 10849347508011975968844329714159015376150022093657775 

noncomputable def Ns336p1402 := nat_lit 2811911667144115636816476342418215049368572627182365128759594215022778433 

noncomputable def Ns336p1403 := nat_lit 376463011379721482055047760182123 

noncomputable def Ns336p1404 := nat_lit 43594844392946401280000000000000000000 

noncomputable def Ns336p1405 := nat_lit 370458258893824689037933208428422739825944579798758549480831420572610068480 

noncomputable def Ns336p1406 := @Enclosure.Real.IsNear.neg qz169 Bool.true Ns336p1401 

noncomputable def Ns336p1407 := @Enclosure.Real.IsNear.mulLit_ft qz162 qz147 Ns336p1318 Ns336p1319 Ns336p1320 

noncomputable def Ns336p1408 := @Enclosure.Real.IsNear.mulLit_ft qz461 qz157 884279719003555 70368744177664 1 

noncomputable def Ns336p1409 := nat_lit 52189779272617972203936072861093090558981446815 

noncomputable def Ns336p1410 := @Enclosure.Real.IsNear.mulLit_tt qz170 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz141) 195946923053914730957945 18889465931478580854784 Ns336p1368 Ns336p1053 Ns336p1409 

noncomputable def Ns336p1411 := nat_lit 5144918235777544822032921311591560066393700240046186452749 

noncomputable def Ns336p1412 := nat_lit 255082195665380354230644102523316141257077555200000000000000000 

noncomputable def Ns336p1413 := @Enclosure.Real.IsNear.mulLit_ft qz0 qz167 2 1 0 1 195946923053914730957945 37778931862957161709568 Ns336p1368 

noncomputable def Ns336p1414 := @Ns336p1413 Ns336p1362 195946923053914730957945 18889465931478580854784 Ns336p1368 Ns336p1053 qz347 qz515 rfl 

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz349 qz505 (Real.sin qz499))

noncomputable def Ns336p1415 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz172) (@HMul.hMul Real Real Real qz5 qz167 qz140) 

noncomputable def Ns336p1416 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz141) (@HMul.hMul Real Real Real qz5 qz146 Ns336p1415) Bool.true Ns336p1409 Ns336p1061 Ns336p1411 Ns336p1412 (BSN.deriv_correction_mk qz141 qz510) 

noncomputable def Ns336p1417 := nat_lit 109736649142611932668057721833207722065 

noncomputable def Ns336p1418 := nat_lit 21186118491196385341435669275668717329884466290280237 

noncomputable def Ns336p1419 := @Enclosure.Real.IsNear.mulLit_tf qz146 Ns336p1415 475591151 268435456 349 268435456 Ns336p1417 Ns336p1069 Ns336p1418 

noncomputable def Ns336p1420 := nat_lit 1900510457645210282732874918902785638400000000000000000000 

noncomputable def Ns336p1421 := @Enclosure.Real.IsNear.subLit_tt_p (@Neg.neg Real Real.instNeg qz172) (@HMul.hMul Real Real Real qz5 qz167 qz140) 

noncomputable def Ns336p1422 := nat_lit 1194911311119038851590751896915 

noncomputable def Ns336p1423 := nat_lit 633825300114114700748351602688 

noncomputable def Ns336p1424 := nat_lit 3082304546319246255320720513980664936763 

noncomputable def Ns336p1425 := nat_lit 1462800241733701301394472960000000000000000000 

noncomputable def Ns336p1426 := nat_lit 751249774502206061485017343495693758545 

noncomputable def Ns336p1427 := nat_lit 17181503331313518189238848694560979159265840876668717 

noncomputable def Ns336p1428 := nat_lit 69553864576333315884947501130569421796419333779105943727360410910720 

noncomputable def Ns336p1429 := @Enclosure.Real.IsNear.neg qz172 Bool.false Ns336p1422 

noncomputable def Ns336p1430 := @Enclosure.Real.IsNear.mulLit_tt qz163 qz157 36685609547140373262205 18889465931478580854784 Ns336p1323 

noncomputable def Ns336p1431 := @Enclosure.Real.IsNear.mulLit_tf qz167 qz140 195946923053914730957945 37778931862957161709568 Ns336p1368 Ns336p1362 3833945247997081 9007199254740992 

noncomputable def Ns336p1432 := @Enclosure.Real.IsNear.of_eq qz140 (@HMul.hMul Real Real Real qz5 qz146 qz147) Bool.false 3833945247997081 

noncomputable def Ns336p1433 := @Enclosure.Real.IsNear.mulLit_tt qz146 qz147 475591151 268435456 349 

noncomputable abbrev qz516 := (@Ns336p1432 9007199254740992 16673520415217 10898711098236600320 (BSN.correction_mk qz141 qz716) (@Ns336p1433 268435456 8061431 33554432 13950269 20300431360000 3833945247997081 9007199254740992 16673520415217 10898711098236600320 Ns336p1282 (Ns336p1359 rfl) rfl))

noncomputable def Ns336p1434 := @Ns336p1431 16673520415217 10898711098236600320 Ns336p1426 Ns336p1069 Ns336p1427 Ns336p1420 qz515 qz516 

noncomputable def Ns336p1435 := @Ns336p1410 Ns336p1061 Ns336p1411 Ns336p1412 Ns336p1397 Ns336p1382 Ns336p1398 Ns336p1384 Ns336p1414 (Ns336p1416 (@Ns336p1419 Ns336p1420 Ns336p1409 Ns336p1061 Ns336p1411 Ns336p1412 Ns336p1282 (@Ns336p1421 Ns336p1422 Ns336p1423 Ns336p1424 Ns336p1425 Ns336p1426 Ns336p1069 Ns336p1427 Ns336p1420 Ns336p1428 Ns336p1417 Ns336p1069 Ns336p1418 Ns336p1420 (@Ns336p1429 Ns336p1423 Ns336p1424 Ns336p1425 (@Ns336p1430 Ns336p1324 32571663 33554432 13950269 20300431360000 Ns336p1422 Ns336p1423 Ns336p1424 Ns336p1425 qz166 (Ns336p1345 rfl) rfl)) (Ns336p1434 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns336p1436 := @Ns336p1396 Ns336p1397 Ns336p1382 Ns336p1398 Ns336p1384 Ns336p1399 Ns336p1385 Ns336p1382 Ns336p1387 Ns336p1384 (@Ns336p1400 Ns336p1401 Ns336p1393 Ns336p1402 Ns336p1395 28802461005118489261965 2361183241434822606848 Ns336p1403 Ns336p1404 Ns336p1405 Ns336p1392 Ns336p1393 Ns336p1394 Ns336p1395 (@Ns336p1406 Ns336p1393 Ns336p1402 Ns336p1395 (@Ns336p1407 Ns336p1321 8061431 33554432 13950269 20300431360000 Ns336p1401 Ns336p1393 Ns336p1402 Ns336p1395 (@Ns336p1325 Ns336p1323 Ns336p1324 Ns336p1318 Ns336p1319 Ns336p1320 Ns336p1321 qz166 qz166 rfl) (Ns336p1359 rfl) rfl)) (@Ns336p1408 250000000000000 32571663 33554432 13950269 20300431360000 28802461005118489261965 2361183241434822606848 Ns336p1403 Ns336p1404 RS337to348.d61 (Ns336p1345 rfl) rfl) rfl rfl) Ns336p1435 

noncomputable def Ns336p1437 := nat_lit 236949238197338914929104743260475031875 

noncomputable def Ns336p1438 := nat_lit 10633823966279326983230456482242756608 

noncomputable def Ns336p1439 := nat_lit 12222673487210834853481254325519014684285533826485729307007 

noncomputable def Ns336p1440 := nat_lit 748953723767655066313970155520000000000000000000000000000000000 

noncomputable abbrev qz173 := qz508

noncomputable def Ns336p1441 := @Enclosure.Real.IsNear.mulLit_ff qz173 qz140 Ns336p1437 Ns336p1438 Ns336p1439 Ns336p1440 3833945247997081 9007199254740992 

noncomputable def Ns336p1442 := @Enclosure.Real.IsNear.mulLit_ft qz116 qz149 Ns336p847 Ns336p851 Ns336p849 Ns336p852 303023275 536870912 16783663 40600862720000 Ns336p1437 

noncomputable abbrev qz517 := (@HMul.hMul Real Real Real qz627 qz695 qz710)

noncomputable abbrev qz174 := qz517

noncomputable def Ns336p1443 := @Ns336p1441 16673520415217 10898711098236600320 Ns336p1388 Ns336p1042 Ns336p1389 Ns336p1390 (@Enclosure.Real.IsNear.neg qz174 Bool.true Ns336p1437 Ns336p1438 Ns336p1439 Ns336p1440 (@Ns336p1442 Ns336p1438 Ns336p1439 Ns336p1440 RS337to348.d63 (Ns336p1266 (Ns336p1280 rfl rfl) rfl) rfl)) qz516 

noncomputable def Ns336p1444 := nat_lit 710847714592016744787314229781425095625 

noncomputable def Ns336p1445 := nat_lit 36668020461632504560443762976557044052856601479457187921021 

noncomputable def Ns336p1446 := @Enclosure.Real.IsNear.mulLit_ft qz160 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz141) Ns336p1444 Ns336p1438 Ns336p1445 Ns336p1440 Ns336p1409 

noncomputable def Ns336p1447 := @Enclosure.Real.IsNear.mulLit_ff qz320 qz173 3 1 0 1 Ns336p1437 Ns336p1438 Ns336p1439 

noncomputable def Ns336p1448 := @Ns336p1447 Ns336p1440 Ns336p1444 Ns336p1438 Ns336p1445 Ns336p1440 qz480 (@Enclosure.Real.IsNear.neg qz174 Bool.true Ns336p1437 Ns336p1438 Ns336p1439 Ns336p1440 (@Ns336p1442 Ns336p1438 Ns336p1439 Ns336p1440 RS337to348.d63 (Ns336p1266 (Ns336p1280 rfl rfl) rfl) rfl)) rfl 

noncomputable def Ns336p1449 := @Ns336p1446 Ns336p1061 Ns336p1411 Ns336p1412 Ns336p1293 Ns336p1294 Ns336p1295 Ns336p1296 Ns336p1448 (Ns336p1416 (@Ns336p1419 Ns336p1420 Ns336p1409 Ns336p1061 Ns336p1411 Ns336p1412 Ns336p1282 (@Ns336p1421 Ns336p1422 Ns336p1423 Ns336p1424 Ns336p1425 Ns336p1426 Ns336p1069 Ns336p1427 Ns336p1420 Ns336p1428 Ns336p1417 Ns336p1069 Ns336p1418 Ns336p1420 (@Ns336p1429 Ns336p1423 Ns336p1424 Ns336p1425 (@Ns336p1430 Ns336p1324 32571663 33554432 13950269 20300431360000 Ns336p1422 Ns336p1423 Ns336p1424 Ns336p1425 qz166 (Ns336p1345 rfl) rfl)) (Ns336p1434 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns336p1450 := @Ns336p1291 Ns336p1292 Ns336p1263 Ns336p1293 Ns336p1294 Ns336p1295 Ns336p1296 Ns336p1297 Ns336p1284 Ns336p1260 Ns336p1285 Ns336p1263 (@Ns336p1302 Ns336p1303 Ns336p1260 Ns336p1304 Ns336p1263 Ns336p1305 Ns336p1290 Ns336p1260 Ns336p1292 Ns336p1263 Ns336p1360 (@Ns336p1364 Ns336p1365 Ns336p1366 Ns336p1367 Ns336p1303 Ns336p1260 Ns336p1304 Ns336p1263 Ns336p1377 (@Ns336p1379 Bool.false Ns336p1363 Ns336p1365 Ns336p1366 Ns336p1367 (BSN.iteratedDeriv_two_correction_mk qz141 qz510) (@Ns336p1380 268435456 349 268435456 Ns336p1381 Ns336p1382 Ns336p1383 Ns336p1384 Ns336p1363 Ns336p1365 Ns336p1366 Ns336p1367 Ns336p1282 (@Ns336p1386 Ns336p1387 Ns336p1384 Ns336p1388 Ns336p1042 Ns336p1389 Ns336p1390 Ns336p1391 Ns336p1381 Ns336p1382 Ns336p1383 Ns336p1384 (Ns336p1436 rfl rfl) (Ns336p1443 rfl) rfl rfl) rfl)) rfl) rfl rfl) Ns336p1449 

noncomputable def Ns336p1451 := nat_lit 153220818251461646293065738558995338726380819832858625 

noncomputable def Ns336p1452 := nat_lit 748288838313422294120286634350736906063837462003712 

noncomputable def Ns336p1453 := nat_lit 329841988768263322345785199195693511940505065649488549063773229021276565240311491769 

noncomputable def Ns336p1454 := nat_lit 3216731749799496412427213085878433873920000000000000000000000000000000000000000000000000 

noncomputable def Ns336p1455 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz335 RSCompact.c11) qz161) qz140 Ns336p1451 Ns336p1452 Ns336p1453 Ns336p1454 3833945247997081 9007199254740992 16673520415217 

noncomputable def Ns336p1456 := @Enclosure.Real.IsNear.mulLit_ff qz463 qz161 Ns336p853 Ns336p854 Ns336p855 Ns336p856 221589299 268435456 16783663 40600862720000 Ns336p1451 

noncomputable def Ns336p1457 := Ns336p1258 (@Ns336p1262 Ns336p1263 Ns336p1251 Ns336p1252 Ns336p1253 Ns336p1254 Ns336p1282 (@Ns336p1283 Ns336p1284 Ns336p1260 Ns336p1285 Ns336p1263 Ns336p1286 Ns336p927 Ns336p1287 Ns336p1288 Ns336p1289 Ns336p1259 Ns336p1260 Ns336p1261 Ns336p1263 (Ns336p1450 rfl rfl) (@Ns336p1455 10898711098236600320 Ns336p1286 Ns336p927 Ns336p1287 Ns336p1288 (@Ns336p1456 Ns336p1452 Ns336p1453 Ns336p1454 RS337to348.d64 (Ns336p1371 (Ns336p1376 rfl rfl) rfl) rfl) qz516 rfl) rfl rfl) rfl) 

noncomputable def Ns336p1458 := @Enclosure.Real.IsNear.of_eq qz706 (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz141) qz466)) Bool.false Ns336p1246 Ns336p1247 Ns336p1248 Ns336p1249 (BSN.correctionLinear_mk qz141) (@Enclosure.Real.IsNear.neg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz141) qz466) Bool.true Ns336p1246 Ns336p1247 Ns336p1248 Ns336p1249 (@Ns336p1255 Ns336p1247 Ns336p1248 Ns336p1249 Ns336p1457 RS337to348.d65 rfl)) 

noncomputable def Ns336p1459 := @Enclosure.Real.IsNear.inv_image qz142 173567855 16777216 17 16777216 1621699 1621701 16777216 qz496 rfl 

noncomputable def Ns336p1460 := @Ns336p1250 Ns336p1198 Ns336p1208 Ns336p1201 Ns336p1458 (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz142) Bool.false 3243400 33554432 2 33554432 405425 4194304 1 16777216 (Ns336p1459 rfl rfl rfl rfl rfl) rfl) 

noncomputable abbrev qz518 := (BSN.correction_mk qz141 qz716)

noncomputable def Ns336p1461 := @Ns336p1200 Ns336p1201 Ns336p1120 Ns336p1116 Ns336p1122 Ns336p1118 (Ns336p1202 qz28 (@Enclosure.Real.IsNear.of_eq qz495 (@Inv.inv Real Real.instInv (Real.sqrt qz142)) Bool.false 10432183 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz139 (BSN.t_div_two_pi_nonneg qz138 672479 1000 qz143)) Ns336p1206) rfl) (@Ns336p1209 Ns336p1210 Ns336p1197 Ns336p1198 Ns336p1199 Ns336p1201 (@Ns336p1211 562949953421312 1041193632452713 42573090227486720000 qz518 (@Ns336p1212 33554432 4030695 16777216 13950269 1268776960000 239621822943615 562949953421312 1041193632452713 42573090227486720000 Ns336p1231 (Ns336p1245 rfl) rfl)) (Ns336p1460 rfl) rfl rfl) 

noncomputable abbrev qz719 := (@BSN.floor_sqrt_eq_dec qz138 672479 1000 10 qz143 rfl rfl rfl)

noncomputable abbrev qz519 := qz719

noncomputable def Ns336p1462 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz138) (hardyZApproximantRS qz138) Bool.true Ns336p1115 Ns336p1116 Ns336p1117 Ns336p1118 (@Eq.refl Real (hardyZApproximantRS qz138)) (Ns336p1119 (BSN.hardyZApproximantRS_eq qz138 10 qz519) (@Ns336p1121 Ns336p1122 Ns336p1118 Ns336p1123 Ns336p1115 Ns336p1116 Ns336p1117 Ns336p1118 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz138) qz138 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 10)) Bool.false 1266411 16777216 164811 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz138) qz138 10) (Ns336p1196 (Ns336p1195 rfl rfl rfl rfl) rfl rfl)) (Ns336p1461 rfl) rfl rfl)) 

theorem RS337to348.d68 : Enclosure.Real.IsNear (hardyZApproximantRS qz138) Bool.true Ns336p1115 Ns336p1116 Ns336p1117 Ns336p1118 := Ns336p1462 

noncomputable def Ns336p1463 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) qz43 Bool.false 19791001 1073741824 

theorem RS337to348.d69 : Enclosure.Real.IsNear (hardyZErrorBoundRS qz4) Bool.false 19791001 1073741824 201 1073741824 := @Ns336p1463 201 1073741824 (BSN.hardyZErrorBoundRS_mk qz4 664401 1000 qz10 rfl rfl) (@Ns336p338 1 1073741824 1 1073741824 2656303189065728 19791001 1073741824 201 1073741824 (@Ns336p339 134217728 25 134217728 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns336p340 (Ns336p346 rfl rfl rfl rfl) rfl) rfl) (@Ns336p347 33554432 1 33554432 1 1073741824 1 1073741824 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns336p348 1 33554432 1 33554432 (@Ns336p353 16777216 (@Ns336p358 17592186044416000 Ns336p349 Ns336p350 Ns336p351 Ns336p352 (@Ns336p359 Ns336p355 Ns336p356 Ns336p357 (Ns336p345 rfl) (Ns336p345 rfl) rfl) (Ns336p345 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) 

noncomputable def Ns336p1464 := nat_lit 4156399208697885531804318014286688435494810810362268701382738872077800042412871633619918078009982123326816077003680689159070745520385645 

noncomputable def Ns336p1465 := nat_lit 2907354897182427562197295231552018137414565442749272241125960796722557152453591693304764202855054262243050086425064711734138406514458624 

noncomputable def Ns336p1466 := nat_lit 668984617784159737134158662688976932295831632316971364579331992410168620299217006560420981061983436512881015533674810808702443127221683133584608787370491176934851293772386694948997789 

noncomputable def Ns336p1467 := nat_lit 540554877274507955105401375719738431651394881650478687802020783359602788350430704722181628277324243234733229656668667163705344000000000000000000000000000000000000000000000000000000000000 

noncomputable abbrev qz860 := (Enclosure.sfrac Bool.false 673823 1000)

noncomputable abbrev qz720 := qz860

noncomputable abbrev qz520 := qz720

noncomputable abbrev qz175 := qz520

noncomputable abbrev qz861 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 673823 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz721 := qz861

noncomputable abbrev qz521 := qz721

noncomputable abbrev qz176 := (@HMul.hMul Real Real Real qz349 qz350 (@HPow.hPow Real Real Real qz446 qz521 qz352))

noncomputable abbrev qz862 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 673823 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz722 := qz862

noncomputable abbrev qz522 := qz722

noncomputable abbrev qz177 := (Zeta.RiemannSiegel.correction qz522)

noncomputable abbrev qz178 := qz522

noncomputable abbrev qz863 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 673823 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz723 := qz863

noncomputable abbrev qz523 := qz723

noncomputable abbrev qz179 := qz523

noncomputable abbrev qz724 := (Zeta.RiemannSiegel.correctionLinear qz178)

noncomputable abbrev qz524 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) qz177 (@HMul.hMul Real Real Real qz5 qz724 (@Inv.inv Real Real.instInv qz179)))

noncomputable def Ns336p1468 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz175) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz175) qz175 10) (@HMul.hMul Real Real Real qz5 qz176 qz524)) Bool.false Ns336p1464 Ns336p1465 Ns336p1466 Ns336p1467 

noncomputable def Ns336p1469 := nat_lit 380060576805757341904267721706535271460862287338442464850681378133302759412517889219022626941009564113104157241640615874752801718784403 

noncomputable def Ns336p1470 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz175) qz175 10) (@HMul.hMul Real Real Real qz5 qz176 qz524) 209425181 134217728 165143 134217728 Ns336p1469 Ns336p1465 

noncomputable def Ns336p1471 := nat_lit 3879825533883624354397561454386194638535683003889549189869296197974629975113339197379038952799786045235267982418141485438443127221683133584608787370491176934851293772386694948997789 

noncomputable def Ns336p1472 := nat_lit 557862458452428034482847304467030862455988062756662562025101669827564960930959268620113819976626561913541055329307069736404706055012338955714560 

noncomputable def Ns336p1473 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz175) qz175 Real.sin BSN.quadSignPos 9 10 673823 1000 199 268435456 134217728 4503599627370496 Bool.false 332266065598 2531 618095470 56 84886744 8 

noncomputable def Ns336p1474 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz175) qz175 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 673823 1000 104 154 268435456 134217728 4503599627370496 Bool.false 332266065598 2531 

noncomputable def Ns336p1475 := Ns336p1474 558195838 56 94906264 8 589812974 56 89478488 8 Bool.false 95804209 124723 Bool.true 6756010 Bool.true 228238028 14148475504056880 1 Bool.false 268350442 Bool.false Bool.false 177111866 Bool.true Bool.false 131643125 

noncomputable def Ns336p1476 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz175) qz175 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 673823 1000 19 46 268435456 134217728 4503599627370496 Bool.false 332266065598 2531 

noncomputable def Ns336p1477 := Ns336p1476 480971758 57 109588312 8 522351262 57 101459064 8 Bool.false 73692304 92516 Bool.false 164741570 Bool.true 309987116 14148475504056880 1 Bool.false 154593199 Bool.false Bool.false 108477131 Bool.true Bool.false 95804209 

noncomputable def Ns336p1478 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz175) qz175 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 673823 1000 193 97 268435456 134217728 4503599627370496 Bool.false 332266065598 2531 

noncomputable def Ns336p1479 := Ns336p1478 372130544 56 134217720 8 432030192 56 120047984 16 Bool.false 236078888 54348 Bool.false 136062392 Bool.false 253414992 14148475504056880 1 Bool.false 130310606 Bool.true Bool.false 217415763 Bool.true Bool.false 73692304 

noncomputable def Ns336p1480 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz175) qz175 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 673823 1000 490 316 268435456 134217728 4503599627370496 Bool.false 332266065598 2531 

noncomputable def Ns336p1481 := Ns336p1480 186065264 56 189812528 16 294906480 56 154981288 8 Bool.false 268435448 2600 Bool.false 278871363 Bool.false 307549192 14148475504056880 1 Bool.false 136147404 Bool.true Bool.false 110702623 Bool.false Bool.false 236078888 

noncomputable def Ns336p1482 := nat_lit 1173989211593149078913497453783123000572240955067327839397 

noncomputable def Ns336p1483 := nat_lit 948457763164144879783612992935545011924883445121024000 

noncomputable def Ns336p1484 := nat_lit 66676224134510822260229439364640000 

noncomputable def Ns336p1485 := nat_lit 269567909516622671555868746774974912320 

noncomputable abbrev qz525 := (@Eq.refl Real qz720)

noncomputable abbrev qz180 := qz525

noncomputable def Ns336p1486 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz175 673823 1000 1816150741316 16000000 1347646 4000 2000 Ns336p1484 Ns336p1485 qz180 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns336p1487 := nat_lit 375676547709807705252319185210599360183117105621544908607040 

noncomputable abbrev qz725 := (Real.log (Enclosure.sfrac Bool.false 1816150741316 16000000))

noncomputable abbrev qz726 := (@Nat.cast Real Real.instNatCast 1347646)

noncomputable abbrev qz727 := (Enclosure.sfrac Bool.false 673823 2000)

noncomputable abbrev qz181 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 673823 4000) qz725) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz726))))) qz727)

noncomputable abbrev qz526 := (@HSub.hSub Real Real Real qz11 qz181 (@HMul.hMul Real Real Real qz5 qz727 (Real.log Real.pi)))

noncomputable def Ns336p1488 := @Enclosure.Real.IsNear.addLit_ft_p qz526 (Enclosure.sfrac Bool.true Ns336p1484 Ns336p1485) 1393625166490362509197 1125899906842624000 4670011907327338747 495616000000000000000000 Ns336p1484 Ns336p1485 0 1 Ns336p1487 

noncomputable def Ns336p1489 := nat_lit 18704920352995818988080044441600 

noncomputable abbrev qz527 := (@HMul.hMul Real Real Real qz5 qz727 (Real.log Real.pi))

noncomputable def Ns336p1490 := @Enclosure.Real.IsNear.subLit_ff_p qz181 qz527 365570796096709629929 225179981368524800 532674544895457 121000000000000000000 25882054209303 67108864000 673823 134217728000 Ns336p1489 1393625166490362509197 1125899906842624000 

noncomputable def Ns336p1491 := nat_lit 3655707960967096299290000 

noncomputable abbrev qz182 := (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 673823 4000) qz725) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz726)))))

noncomputable def Ns336p1492 := @Enclosure.Real.IsNear.subLit_ff_p qz182 qz727 2207182606947756865421 1125899906842624000 532674544895457 121000000000000000000 673823 2000 0 1 Ns336p1491 365570796096709629929 225179981368524800 532674544895457 121000000000000000000 

noncomputable def Ns336p1493 := nat_lit 4970133383094278877370210462789009408 

noncomputable def Ns336p1494 := nat_lit 56285850689765520669933568 

noncomputable def Ns336p1495 := nat_lit 41282526745972663063163432599479885289496872417838417030087536036869254706135508826718621847505294749633736150840404694424995162548819932417394676921794560 

noncomputable def Ns336p1496 := nat_lit 1032782068931938921979517775408077725553330478322646934724101975846302302514518922191745805119861093747845365367965547530967096602950770545197819396882432 

noncomputable def Ns336p1497 := nat_lit 434783037810937767968362770574334494683993898290366060887129807594640215189934745673524932864437351653508734955838823335890332942937797382237061120 

noncomputable def Ns336p1498 := BSN.log_dyadic_bound 767574741316 2864726741316 7 6 Ns336p1495 134217728 38720000 Ns336p1496 Ns336p1497 73723949 3632301482632 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 767574741316) (BSN.artanhQ 2864726741316) 0 6 Ns336p1496 Ns336p1495 Ns336p1497 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns336p1499 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 673823 4000) qz725 673823 4000 0 1 3276267711175927 281474976710656 195312621 7562500000000000 2207624537947696658921 1125899906842624000 131606136220083 30250000000000000000 (Enclosure.Real.IsNear.const Bool.false 673823 4000) (BSN.isNear_log_sfrac 1816150741316 16000000 3276267711175927 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1816150741316) qz362)) Bool.false Ns336p1494 Ns336p98 1000000619520000 38720000000000000000000 3276267711175927 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1816150741316 16000000 16 3632301482632 2097152000000 73723949 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns336p1498 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p1500 := BSN.arctan_dyadic_bound_f 1000 1347646 1 0 16777216 4840000 0 1 1 0 1 1 12449 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1347646) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1347646) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz728 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1347646)))

noncomputable def Ns336p1501 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz728 884279719003555 562949953421312 1 2000000000000000 12449 16777216 1 4840000 14828743686171805089792 883861999879587 562949953421312 50000000121 242000000000000000 qz16 (Ns336p1500 rfl) rfl rfl 

noncomputable def Ns336p1502 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 673823 4000) qz725) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz728)) 2207624537947696658921 1125899906842624000 131606136220083 30250000000000000000 883861999879587 2251799813685248 50000000121 968000000000000000 Ns336p1493 2207182606947756865421 1125899906842624000 532674544895457 121000000000000000000 (Ns336p1499 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz728) 1 4 0 1 883861999879587 562949953421312 50000000121 242000000000000000 883861999879587 2251799813685248 50000000121 968000000000000000 qz364 Ns336p1501 rfl) 

noncomputable def Ns336p1503 := @Ns336p1488 Ns336p1482 Ns336p1483 4670011907327338747 495616000000000000000000 (@Ns336p1490 4670011907327338747 495616000000000000000000 (Ns336p1492 (Ns336p1502 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 673823 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz727 (Real.log Real.pi) 673823 2000 0 1 38410761 33554432 1 67108864 25882054209303 67108864000 673823 134217728000 (Enclosure.Real.IsNear.const Bool.false 673823 2000) RS337to348.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns336p1484 Ns336p1485) 

noncomputable def Ns336p1504 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz175) Bool.false Ns336p1482 Ns336p1483 4670011907327338747 495616000000000000000000 41533258199 33554432 159 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz175) (@HAdd.hAdd Real Real Real qz365 qz526 (Enclosure.sfrac Bool.true Ns336p1484 Ns336p1485)) Bool.false Ns336p1482 Ns336p1483 4670011907327338747 495616000000000000000000 Ns336p1486 (Ns336p1503 rfl rfl)) 

noncomputable def Ns336p1505 := nat_lit 7596123248371236557815808 

noncomputable def Ns336p1506 := nat_lit 3511239910576537421536521639477590831441053406442593733660939667701281620134983650612200174028875262509691728822322308707590380738901649761 

noncomputable def Ns336p1507 := nat_lit 2503493250925687415137885659681703703043975509515015754781323028918786318509045784135130307395401682237550420959252825815603227076961 

noncomputable def Ns336p1508 := nat_lit 17534381304448361287730809691941585817729478983096613225082308320887452692546279895291225174521041148005539764709968144705105444326888122721 

noncomputable def Ns336p1509 := BSN.sin_dyadic_bound_f 107947403881 68719476736 4 3 33554432 9689454 Ns336p1506 Ns336p112 Ns336p1507 Ns336p1508 Ns336p115 Ns336p1507 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107947403881) qz366 0 3 Ns336p1506 Ns336p112 Ns336p1507 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107947403881) qz367 0 3 Ns336p1508 Ns336p115 Ns336p1507 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1510 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz175) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 41533258199) qz396) Bool.false 41533258199 33554432 159 16777216 Bool.false 33554431 33554432 1 4840000 (Ns336p1504 rfl) (Enclosure.sfrac_false_div 41533258199 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 41533258199) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns336p1505) qz413) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 196 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q3 41533258199 33554432 226375608064910080 72057594037927936 196 Ns336p1505 Ns336p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554431 33554432 Ns336p1505 Ns336p98 107947403881 68719476736 9689454 9680000 (Ns336p1509 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p1511 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz175) Bool.false Ns336p1482 Ns336p1483 4670011907327338747 495616000000000000000000 332266065598 268435456 2531 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz175) (@HAdd.hAdd Real Real Real qz365 qz526 (Enclosure.sfrac Bool.true Ns336p1484 Ns336p1485)) Bool.false Ns336p1482 Ns336p1483 4670011907327338747 495616000000000000000000 Ns336p1486 (Ns336p1503 rfl rfl)) 

noncomputable def Ns336p1512 := Ns336p1481 54348 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 490 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 136147404 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 316 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 110702623 268435456) qz180 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz175) qz175 1) Bool.false 33554431 33554432 12286519 1268776960000 268435448 268435456 2600 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz175) qz175 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz175)) Bool.false 33554431 33554432 12286519 1268776960000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz175) qz175) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz175)) Bool.false 33554431 33554432 786337216 81201725440000 33554431 33554432 12286519 1268776960000 (Ns336p1510 rfl rfl) rfl)) rfl) (Ns336p1511 rfl) RS337to348.d7 

noncomputable def Ns336p1513 := nat_lit 3256577873122556399543489225224068964886315219805069343672643660324987920706473190665847558671912653412229361 

noncomputable def Ns336p1514 := nat_lit 221231534595223694628671533643183645413812107599923841439753078968592525272115381318838653595036016881 

noncomputable def Ns336p1515 := nat_lit 19747445609449978306173655173346620883139220745220534130886839456829251721120258900261326329657868098343133425 

noncomputable def Ns336p1516 := BSN.cos_dyadic_bound_f 278871363 268435456 4 3 268435456 134217728 Ns336p1513 Ns336p121 Ns336p1514 Ns336p1515 Ns336p124 Ns336p1514 136147404 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 278871363) qz369 0 3 Ns336p1513 Ns336p121 Ns336p1514 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 278871363) qz370 0 3 Ns336p1515 Ns336p124 Ns336p1514 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1517 := nat_lit 4818905093703276125662481750400402178488290676487318260518715981887617439817075682127318468467000211213910016 

noncomputable def Ns336p1518 := nat_lit 716102326167222690153318359349381270891229765654194329671045271031803956544278781747260437056702119936 

noncomputable def Ns336p1519 := nat_lit 29214718492632740362491708261265896207829959149074985570718208024506765087697129840843791802911702174253711360 

noncomputable def Ns336p1520 := BSN.cos_dyadic_bound_f 307549192 268435456 4 3 268435456 134217728 Ns336p1517 Ns336p121 Ns336p1518 Ns336p1519 Ns336p124 Ns336p1518 110702623 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 307549192) qz369 0 3 Ns336p1517 Ns336p121 Ns336p1518 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 307549192) qz370 0 3 Ns336p1519 Ns336p124 Ns336p1518 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1521 := nat_lit 5381498052674443285757799355280156871510341431071729306599385412403200 

noncomputable def Ns336p1522 := nat_lit 117464007442674369332296710950291422865230123637919540651350818816 

noncomputable def Ns336p1523 := nat_lit 14094209481944825228005793640582681810699588613559115361837335797825536 

noncomputable def Ns336p1524 := BSN.sin_dyadic_bound_f 136062392 268435456 3 2 268435456 134217728 Ns336p1521 Ns336p127 Ns336p1522 Ns336p1523 Ns336p130 Ns336p1522 130310606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 136062392) qz371 0 2 Ns336p1521 Ns336p127 Ns336p1522 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 136062392) qz372 0 2 Ns336p1523 Ns336p130 Ns336p1522 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1525 := nat_lit 64771592196659061296563412034998099500363409773229815364669766264422400 

noncomputable def Ns336p1526 := nat_lit 17008203087408299777193350893389486826279091381581171381093024137216 

noncomputable def Ns336p1527 := nat_lit 169612347233870309005645861333072391903233049924793623106184761034407936 

noncomputable def Ns336p1528 := BSN.sin_dyadic_bound_f 253414992 268435456 3 2 268435456 134217728 Ns336p1525 Ns336p127 Ns336p1526 Ns336p1527 Ns336p130 Ns336p1526 217415763 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 253414992) qz371 0 2 Ns336p1525 Ns336p127 Ns336p1526 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 253414992) qz372 0 2 Ns336p1527 Ns336p130 Ns336p1526 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1529 := Ns336p1479 92516 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 193 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 130310606 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 97 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 217415763 268435456) qz180 rfl rfl (Ns336p1512 RS337to348.d9 RS337to348.d11 RS337to348.d13 RS337to348.d17 (Ns336p1516 rfl rfl) (Ns336p1520 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns336p1511 rfl) RS337to348.d19 RS337to348.d21 RS337to348.d23 RS337to348.d25 RS337to348.d17 (Ns336p1524 rfl rfl) (Ns336p1528 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns336p1530 := nat_lit 11565767984274468132359618014508710553909891418629780111567627451040000 

noncomputable def Ns336p1531 := nat_lit 542532306167568335381046219446623035345464864171452284240100000000 

noncomputable def Ns336p1532 := nat_lit 30290418716032669045541715963167518822944870581869336988502635543200000 

noncomputable def Ns336p1533 := BSN.sin_dyadic_bound_f 164741570 268435456 3 2 268435456 134217728 Ns336p1530 Ns336p127 Ns336p1531 Ns336p1532 Ns336p130 Ns336p1531 154593199 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 164741570) qz371 0 2 Ns336p1530 Ns336p127 Ns336p1531 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 164741570) qz372 0 2 Ns336p1532 Ns336p130 Ns336p1531 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1534 := nat_lit 4973691770516520163282086751786694551797906608783460392189996544488861283447493841166244939744842190302478336 

noncomputable def Ns336p1535 := nat_lit 787270038193609643712662117084366230070287578568035844215677682122971268672652874090829131765415673856 

noncomputable def Ns336p1536 := nat_lit 30152455278086991330263229923589689420681981851070737674572358934688419165824212022952543192103387272314880000 

noncomputable def Ns336p1537 := BSN.cos_dyadic_bound_f 309987116 268435456 4 3 268435456 134217728 Ns336p1534 Ns336p121 Ns336p1535 Ns336p1536 Ns336p124 Ns336p1535 108477131 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 309987116) qz369 0 3 Ns336p1534 Ns336p121 Ns336p1535 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 309987116) qz370 0 3 Ns336p1536 Ns336p124 Ns336p1535 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1538 := Ns336p1477 124723 BSN.abs_quadSignPos (BSN.cos_quad_nat3 19 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 154593199 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 46 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 108477131 268435456) qz180 rfl rfl (Ns336p1529 rfl rfl) (Ns336p1511 rfl) RS337to348.d27 RS337to348.d29 RS337to348.d31 RS337to348.d33 RS337to348.d17 (Ns336p1533 rfl rfl) (Ns336p1537 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p1539 := nat_lit 2083344713319850788624010000 

noncomputable def Ns336p1540 := BSN.cos_dyadic_bound_f 6756010 268435456 2 1 268435456 134217728 Ns336p1539 Ns336p142 Ns336p1539 Ns336p1539 Ns336p143 Ns336p1539 268350442 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 6756010) qz369 0 1 Ns336p1539 Ns336p142 Ns336p1539 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 6756010) qz370 0 1 Ns336p1539 Ns336p143 Ns336p1539 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1541 := nat_lit 23678593623191256070095264395539965171578128374225237701824490483286016 

noncomputable def Ns336p1542 := nat_lit 7363835029509270680646479408877791209275075523798523054865304846336 

noncomputable def Ns336p1543 := nat_lit 71021053199514749668924500227802139932315834971628116059363740840165376 

noncomputable def Ns336p1544 := BSN.cos_dyadic_bound_f 228238028 268435456 3 2 268435456 134217728 Ns336p1541 Ns336p251 Ns336p1542 Ns336p1543 Ns336p254 Ns336p1542 177111866 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 228238028) qz369 0 2 Ns336p1541 Ns336p251 Ns336p1542 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 228238028) qz370 0 2 Ns336p1543 Ns336p254 Ns336p1542 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1545 := Ns336p1475 152400 BSN.abs_quadSignPos (BSN.cos_quad_nat0 104 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268350442 268435456) BSN.abs_quadSignNeg qz678 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 177111866 268435456) qz180 rfl rfl (Ns336p1538 rfl) (Ns336p1511 rfl) RS337to348.d35 RS337to348.d37 RS337to348.d39 RS337to348.d41 RS337to348.d17 (Ns336p1540 rfl rfl) (Ns336p1544 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p1546 := nat_lit 147069050928065121066337678602470955698635187558242255460238898099052800 

noncomputable def Ns336p1547 := nat_lit 87627877666455523096635170186039749767142467612996709995879478518016 

noncomputable def Ns336p1548 := nat_lit 385038973962043912898251748921408438663469165324022960103489499675156736 

noncomputable def Ns336p1549 := BSN.sin_dyadic_bound_f 311050058 268435456 3 2 268435456 134217728 Ns336p1546 Ns336p127 Ns336p1547 Ns336p1548 Ns336p130 Ns336p1547 245968461 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 311050058) qz371 0 2 Ns336p1546 Ns336p127 Ns336p1547 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 311050058) qz372 0 2 Ns336p1548 Ns336p130 Ns336p1547 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1550 := Ns336p1473 Bool.false 131643125 152400 Bool.true 311050058 14148475504056880 1 Bool.false 245968461 Bool.false Bool.false 209425181 165143 BSN.abs_quadSignPos qz373 (BSN.sfrac_eq_quadSignPos_mul Bool.false 245968461 268435456) qz180 rfl (Ns336p1545 rfl) (Ns336p1511 rfl) RS337to348.d43 RS337to348.d45 RS337to348.d17 (Ns336p1549 rfl rfl) rfl 

noncomputable def Ns336p1551 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz175) qz175 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz175) qz175 10) 209425181 268435456 165143 268435456 209425181 268435456 165143 268435456 112434287919235072 209425181 134217728 165143 134217728 (Ns336p1550 rfl rfl rfl rfl) 

noncomputable def Ns336p1552 := nat_lit 36449737714560734324461224159843765979426471098808644619690000096221825310683805020287531749711307899989053130321531914259789939 

noncomputable def Ns336p1553 := nat_lit 86645927941275464361825443254471365732388658605494267974077486894206915868925800719999200190754361815543475342543861619655442432 

noncomputable def Ns336p1554 := nat_lit 371444972334409044908356755696147815185255568809842235736680483936018170233931633688650292114980744525895186203497842585247154114472939045987645031579994882839126594726228413 

noncomputable def Ns336p1555 := @Enclosure.Real.IsNear.mulLit_ff qz176 qz524 10426977 33554432 1 33554432 Ns336p1552 Ns336p1553 Ns336p1554 

noncomputable def Ns336p1556 := nat_lit 16109790720775960537952225676767183293443765689446887010396146278369509826613387606208969005266554452023900439043899392000000000000000000000000000000000000000000000000000000000000 

noncomputable abbrev qz183 := (@HPow.hPow Real Real Real qz446 qz521 qz352)

noncomputable def Ns336p1557 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz183 1 1 0 1 10426977 33554432 1 33554432 10426977 33554432 1 33554432 

noncomputable abbrev qz184 := qz521

noncomputable def Ns336p1558 := @Enclosure.Real.IsNear.sqrt_image qz184 3598452679519 33554432000 673823 33554432000 173741196 173741229 16777216 (@Enclosure.Real.IsNear.of_eq qz184 (@HMul.hMul Real Real Real qz5 qz175 qz3) Bool.false 3598452679519 33554432000 673823 33554432000 (BSN.t_div_two_pi_mk qz175 673823 1000 qz180) (@Enclosure.Real.IsNear.mulLit_ff qz175 qz3 673823 1000 0 1 5340353 33554432 1 33554432 3598452679519 33554432000 673823 33554432000 (Enclosure.Real.IsNear.const Bool.false 673823 1000) RS337to348.d48 rfl)) 

noncomputable abbrev qz528 := (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 347482425 33554432 33 33554432 347482425 33554432 33 33554432 (Ns336p1558 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns336p1559 := @Enclosure.Real.IsNear.sqrt_image qz179 347482425 33554432 33 33554432 53989754 53989760 16777216 qz528 rfl 

noncomputable def Ns336p1560 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz179) 53989757 16777216 3 16777216 5213488 5213489 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz179) Bool.false 107979514 33554432 6 33554432 53989757 16777216 3 16777216 (Ns336p1559 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns336p1561 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 10426977 33554432 1 33554432 10426977 33554432 1 33554432 (Ns336p1560 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns336p1562 := nat_lit 61312863572521908378042655657374572298073030623714406347989381024345292862755828551336277437753906691573393131072372901673075 

noncomputable def Ns336p1563 := nat_lit 18171895826346391552861984254219000667569601812060814918945746328746236757029027133833166149742162675325611698981029785247154114472939045987645031579994882839126594726228413 

noncomputable abbrev qz529 := (@HMul.hMul Real Real Real qz5 qz724 (@Inv.inv Real Real.instInv qz179))

noncomputable def Ns336p1564 := @Enclosure.Real.IsNear.addLit_ff qz177 qz529 236420366907749 562949953421312 933589195651273 42573090227486720000 Ns336p1562 Ns336p1553 Ns336p1563 Ns336p1556 

noncomputable def Ns336p1565 := nat_lit 20519378148631004699597944990813919818693227604354310236229456110748905356763068099326845305693369122401736714189197218462574029810543485779968 

noncomputable abbrev qz729 := (@HMul.hMul Real Real Real qz824 qz822 qz862)

noncomputable abbrev qz530 := (Real.cos qz729)

noncomputable abbrev qz185 := (@Inv.inv Real Real.instInv qz530)

noncomputable abbrev qz730 := (@HSub.hSub Real Real Real qz827 (@HMul.hMul Real Real Real qz824 qz862 qz862) qz862)

noncomputable abbrev qz531 := (@HMul.hMul Real Real Real qz627 qz625 (@HSub.hSub Real Real Real qz631 qz730 qz639))

noncomputable abbrev qz186 := (Real.cos qz531)

noncomputable def Ns336p1566 := @Enclosure.Real.IsNear.of_eq qz177 (@HMul.hMul Real Real Real qz5 qz185 qz186) Bool.false 236420366907749 

noncomputable def Ns336p1567 := @Enclosure.Real.IsNear.mulLit_tt qz185 qz186 54401873 33554432 569 

noncomputable abbrev qz187 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz530))

noncomputable abbrev qz188 := qz530

noncomputable def Ns336p1568 := @Enclosure.Real.IsNear.of_eq qz185 (@Neg.neg Real Real.instNeg qz187) Bool.true 54401873 33554432 569 33554432 (BSN.inv_eq_neg_inv_neg qz188) 

noncomputable def Ns336p1569 := @Enclosure.Real.IsNear.recentre' qz187 Bool.false 54401873 33554432 569 33554432 54401873 33554432 

noncomputable def Ns336p1570 := @Enclosure.Real.IsNear.recentre' qz188 Bool.true 20695977 33554432 1045114432 162403450880000 20695977 33554432 16329913 2537553920000 

noncomputable abbrev qz532 := qz729

noncomputable abbrev qz189 := qz532

noncomputable def Ns336p1571 := @Enclosure.Real.IsNear.cos_image qz189 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 75009325) qz396) Bool.false 75009325 33554432 209 33554432 Bool.true 20695977 33554432 1 

noncomputable def Ns336p1572 := nat_lit 890540488601001041123004071 

noncomputable def Ns336p1573 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz178 884279719003555 140737488355328 1 500000000000000 11938105 33554432 33 33554432 10556624134834934963275 4722366482869645213696 Ns336p1572 

noncomputable def Ns336p1574 := @Enclosure.Real.IsNear.subLit_ff_p qz179 qz1 347482425 33554432 33 33554432 10 1 0 1 11938105 11938105 33554432 33 

noncomputable def Ns336p1575 := @Ns336p1574 33554432 qz528 qz379 

noncomputable def Ns336p1576 := @Enclosure.Real.IsNear.recentre' qz189 Bool.false 10556624134834934963275 4722366482869645213696 Ns336p1572 Ns336p304 75009325 33554432 209 33554432 (@Ns336p1573 Ns336p304 RS337to348.d47 (Ns336p1575 rfl rfl) rfl) 

noncomputable def Ns336p1577 := nat_lit 3214078032545320890531840 

noncomputable def Ns336p1578 := nat_lit 293518617527845550165297143280800521188871856838135745432011414430200797815341536618213345 

noncomputable def Ns336p1579 := nat_lit 18941437167926552082622829349496360756465331397188228398600906507145928798860192509921 

noncomputable def Ns336p1580 := nat_lit 768708569293704559824787319249816466148677728801426742809289302992371472298315393688399841 

noncomputable def Ns336p1581 := BSN.sin_dyadic_bound_f 45674795963 68719476736 3 2 33554432 9689454 Ns336p1578 Ns336p1224 Ns336p1579 Ns336p1580 Ns336p1227 Ns336p1579 20695977 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 45674795963) qz366 0 2 Ns336p1578 Ns336p1224 Ns336p1579 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 45674795963) qz367 0 2 Ns336p1580 Ns336p1227 Ns336p1579 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1582 := @Ns336p1571 4840000 (Ns336p1576 rfl) (Enclosure.sfrac_false_div 75009325 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 75009325) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns336p1577) qz413) 226375608064910080 72057594037927936 Bool.false 20695977 33554432 0 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q1 75009325 33554432 226375608064910080 72057594037927936 0 Ns336p1577 Ns336p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 20695977 33554432 Ns336p1577 Ns336p98 45674795963 68719476736 9689454 9680000 (Ns336p1581 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable abbrev qz190 := (@Neg.neg Real Real.instNeg qz530)

noncomputable def Ns336p1583 := @Enclosure.Real.IsNear.inv_image qz190 20695977 33554432 16329913 2537553920000 27200652 27201221 16777216 (@Enclosure.Real.IsNear.neg qz188 Bool.true 20695977 33554432 16329913 2537553920000 (Ns336p1570 (Ns336p1582 rfl rfl) rfl)) 

noncomputable def Ns336p1584 := Ns336p1568 (@Enclosure.Real.IsNear.neg qz187 Bool.false 54401873 33554432 569 33554432 (@Ns336p1569 569 33554432 (Ns336p1583 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p1585 := @Enclosure.Real.IsNear.recentre' qz186 Bool.true 4345813 16777216 

noncomputable abbrev qz191 := qz531

noncomputable def Ns336p1586 := @Enclosure.Real.IsNear.cos_image qz191 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 30749529)) qz368) Bool.true 30749529 16777216 

noncomputable def Ns336p1587 := nat_lit 290421092642741814071852986445 

noncomputable def Ns336p1588 := nat_lit 51144341372117085053617530645391333 

noncomputable def Ns336p1589 := @Enclosure.Real.IsNear.recentre' qz191 Bool.true Ns336p1587 Ns336p194 Ns336p1588 

noncomputable abbrev qz533 := (@HSub.hSub Real Real Real qz631 qz730 qz639)

noncomputable abbrev qz192 := qz533

noncomputable def Ns336p1590 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz192 884279719003555 140737488355328 1 500000000000000 328426725617999 

noncomputable abbrev qz534 := qz730

noncomputable abbrev qz193 := qz534

noncomputable def Ns336p1591 := @Enclosure.Real.IsNear.subLit_tf qz193 qz26 258057981440335 1125899906842624 1895212275 1125899906842624 1 16 

noncomputable abbrev qz731 := (@HMul.hMul Real Real Real qz824 qz862 qz862)

noncomputable abbrev qz535 := qz731

noncomputable abbrev qz194 := qz535

noncomputable def Ns336p1592 := @Enclosure.Real.IsNear.subLit_ff_n qz194 qz178 142518350991025 1125899906842624 787916019 1125899906842624 11938105 33554432 33 33554432 

noncomputable def Ns336p1593 := @Enclosure.Real.IsNear.mulLit_ff qz178 qz178 11938105 33554432 33 33554432 11938105 33554432 33 33554432 142518350991025 1125899906842624 

noncomputable def Ns336p1594 := nat_lit 112758385092643499421062641500891181666991817569173016119855914682740723426785894440697902197921 

noncomputable def Ns336p1595 := nat_lit 714597702024877662347196002516169849807558350555914666347080338804446240938958578687995041 

noncomputable def Ns336p1596 := nat_lit 681021191025552045720688108560803430450486475168453761445993152514523529437661038962476924857505 

noncomputable def Ns336p1597 := BSN.cos_dyadic_bound_t 30749529 16777216 4 3 16777216 4840000 Ns336p1594 Ns336p203 Ns336p1595 Ns336p1596 Ns336p206 Ns336p1595 4345813 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 30749529) (BSN.cosEvenQ 16777216) 0 3 Ns336p1594 Ns336p203 Ns336p1595 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 30749529) (BSN.cosOddQ 16777216) 0 3 Ns336p1596 Ns336p206 Ns336p1595 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1598 := @Ns336p1585 439148608 40600862720000 4345813 16777216 6861697 634388480000 (@Ns336p1586 89 8388608 Bool.true 4345813 16777216 1 4840000 (@Ns336p1589 Ns336p197 30749529 16777216 89 8388608 (@Ns336p1590 1125899906842624 1895212275 1125899906842624 Ns336p1587 Ns336p194 Ns336p1588 Ns336p197 RS337to348.d47 (@Ns336p1591 0 1 5254827609887984 328426725617999 1125899906842624 1895212275 1125899906842624 (@Ns336p1592 8658988990296982814720 258057981440335 1125899906842624 1895212275 1125899906842624 (@Ns336p1593 787916019 1125899906842624 (Ns336p1575 rfl rfl) (Ns336p1575 rfl rfl) rfl) (Ns336p1575 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 30749529 16777216) (BSN.cos_neg_of_bound 30749529 16777216 Bool.true 4345813 16777216 1 4840000 (Ns336p1597 rfl rfl)) rfl rfl) 

noncomputable def Ns336p1599 := nat_lit 18922771345923618156877495254829640452678779007017364974536583815180067441902098305343366194155635593509768839120863025 

noncomputable def Ns336p1600 := nat_lit 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376 

noncomputable def Ns336p1601 := nat_lit 5607240120584812426968660777113019553640805718550913663739511018770094101374033447555472727461349801308367527584600038295205254703740345769310979782044021172113388767 

noncomputable def Ns336p1602 := nat_lit 480109176658867613612181713484739759369008710665908068728332110594794447023075449651747018255786730409380806656000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns336p1603 := @Enclosure.Real.IsNear.mulLit_ff qz724 (@Inv.inv Real Real.instInv qz179) Ns336p1599 Ns336p1600 Ns336p1601 Ns336p1602 3240163 33554432 1 33554432 Ns336p1562 

noncomputable def Ns336p1604 := nat_lit 33395345712844944676106403404749210599314152659001507114066847646661338268782745509572164845349665466309999733725 

noncomputable def Ns336p1605 := nat_lit 4809815209520810450717656262224562232065397860164239095208531909697964083434718092213655548692006303809402830848 

noncomputable def Ns336p1606 := nat_lit 49424060096026854777377825455690999674026880161820078467308440527002783560081331178113505406275489683815247986566830341668255539820133002478072375404674153970367 

noncomputable def Ns336p1607 := nat_lit 4471365145024541892224752469777499878490424814316519244837873713996209642133446872716276145128409661440000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns336p1608 := @Enclosure.Real.IsNear.mulLit_tf (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz178) qz466 Ns336p1604 Ns336p1605 Ns336p1606 Ns336p1607 566629 536870912 1 536870912 Ns336p1599 

noncomputable abbrev qz864 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 673823 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1)))

noncomputable abbrev qz732 := (@HMul.hMul Real Real Real qz824 qz822 (@HSub.hSub Real Real Real qz827 qz864 qz830))

noncomputable abbrev qz536 := (@HMul.hMul Real Real Real qz627 qz732 qz732)

noncomputable abbrev qz537 := qz732

noncomputable abbrev qz195 := (@HMul.hMul Real Real Real qz349 qz536 qz537)

noncomputable abbrev qz196 := (Real.sin qz531)

noncomputable abbrev qz197 := (@HMul.hMul Real Real Real qz349 qz320 qz537)

noncomputable abbrev qz538 := (@HMul.hMul Real Real Real qz5 qz197 qz694)

noncomputable def Ns336p1609 := @HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 qz195 qz196) (@HMul.hMul Real Real Real qz5 qz538 qz186) 

noncomputable abbrev qz733 := (Real.sin (@HMul.hMul Real Real Real qz824 qz822 qz862))

noncomputable abbrev qz539 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz627 qz625 qz733))

noncomputable abbrev qz198 := (@HMul.hMul Real Real Real qz349 qz320 qz539)

noncomputable abbrev qz540 := (@HMul.hMul Real Real Real qz627 qz695 (Real.cos qz729))

noncomputable abbrev qz199 := (@HMul.hMul Real Real Real qz349 qz320 (@Neg.neg Real Real.instNeg qz540))

noncomputable abbrev qz541 := qz733

noncomputable abbrev qz200 := qz541

noncomputable def Ns336p1610 := @HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns336p1609 (@HMul.hMul Real Real Real qz5 qz198 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz178))) (@HMul.hMul Real Real Real qz5 qz199 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz178))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz475 qz200) qz177) 

noncomputable abbrev qz201 := (BSN.cos_two_pi_p_ne_zero_mk qz520 673823 1000 10 qz525 rfl rfl (@BSN.floor_sqrt_eq_dec qz520 673823 1000 10 qz525 rfl rfl rfl))

noncomputable def Ns336p1611 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz178) (@HMul.hMul Real Real Real qz5 qz185 Ns336p1610) Bool.true Ns336p1604 Ns336p1605 Ns336p1606 Ns336p1607 (BSN.iteratedDeriv_three_correction_mk qz178 qz201) 

noncomputable def Ns336p1612 := nat_lit 38366702477069801971750990398109418075625412289436674511809441900126980429052690484086997682283012997175 

noncomputable def Ns336p1613 := nat_lit 8958978968711216842229769122273777112486581988938598139599956403855167484720643781523509973086428463104 

noncomputable def Ns336p1614 := nat_lit 56758323009128120469013153299528908942126718588820401480556303612640055330522765907945982583329163104582123751961831873350249620596666378541983609443101 

noncomputable def Ns336p1615 := @Enclosure.Real.IsNear.mulLit_tf qz185 Ns336p1610 870425227 536870912 565 536870912 Ns336p1612 Ns336p1613 Ns336p1614 

noncomputable def Ns336p1616 := nat_lit 8328566597820337661029309909376315546204195943319274568628284547470900494853866980813958021120000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns336p1617 := @Enclosure.Real.IsNear.of_eq qz185 (@Neg.neg Real Real.instNeg qz187) Bool.true 870425227 536870912 565 536870912 (BSN.inv_eq_neg_inv_neg qz188) 

noncomputable def Ns336p1618 := @Enclosure.Real.IsNear.recentre' qz187 Bool.false 870425227 536870912 565 536870912 870425227 536870912 

noncomputable def Ns336p1619 := @Enclosure.Real.IsNear.recentre' qz188 Bool.true 331137434 536870912 1040274432 2598455214080000 165568717 268435456 1015893 2537553920000 

noncomputable abbrev qz542 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 600075735) (@Nat.cast Real Real.instNatCast 268435456))

noncomputable def Ns336p1620 := @Enclosure.Real.IsNear.cos_image qz189 qz542 Bool.false 600075735 268435456 13 33554432 Bool.true 331137434 536870912 1 

noncomputable def Ns336p1621 := nat_lit 890540490139217241445944999 

noncomputable def Ns336p1622 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz178 884279719003555 140737488355328 1 500000000000000 191010039 536870912 33 536870912 168906303613778081688645 75557863725914323419136 Ns336p1621 

noncomputable def Ns336p1623 := @Enclosure.Real.IsNear.subLit_ff_p qz179 qz1 5559719159 536870912 33 536870912 10 1 0 1 191010039 191010039 536870912 33 

noncomputable def Ns336p1624 := @Enclosure.Real.IsNear.sqrt_image qz184 57575250284357 536870912000 673823 536870912000 2779859563 2779859596 268435456 (@Enclosure.Real.IsNear.of_eq qz184 (@HMul.hMul Real Real Real qz5 qz175 qz3) Bool.false 57575250284357 536870912000 673823 536870912000 (BSN.t_div_two_pi_mk qz175 673823 1000 qz180) (@Enclosure.Real.IsNear.mulLit_ff qz175 qz3 673823 1000 0 1 85445659 536870912 1 536870912 57575250284357 536870912000 673823 536870912000 (Enclosure.Real.IsNear.const Bool.false 673823 1000) RS337to348.d60 rfl)) 

noncomputable def Ns336p1625 := @Ns336p1623 536870912 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 5559719159 536870912 33 536870912 5559719159 536870912 33 536870912 (Ns336p1624 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns336p1626 := @Enclosure.Real.IsNear.recentre' qz189 Bool.false 168906303613778081688645 75557863725914323419136 Ns336p1621 Ns336p906 600075735 268435456 13 33554432 (@Ns336p1622 Ns336p906 RS337to348.d59 (Ns336p1625 rfl rfl) rfl) 

noncomputable def Ns336p1627 := nat_lit 25712787831101033220669440 

noncomputable def Ns336p1628 := nat_lit 38685626227668133590597632 

noncomputable def Ns336p1629 := nat_lit 1260684944064286505993818360914398441701067942164786732835649992281210391427170038052656376722083745 

noncomputable def Ns336p1630 := nat_lit 81356993485592229157587989834745611673342220050565483777953289455317295503348532789067968270241 

noncomputable def Ns336p1631 := nat_lit 3301662180274154652088983421839882521083897294456264337119633293505956701926058963941965352799686561 

noncomputable def Ns336p1632 := BSN.sin_dyadic_bound_f 730801384381 1099511627776 3 2 536870912 155031251 Ns336p1629 Ns336p915 Ns336p1630 Ns336p1631 Ns336p918 Ns336p1630 331137434 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 730801384381) (BSN.sinEvenQ 1099511627776) 0 2 Ns336p1629 Ns336p915 Ns336p1630 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 730801384381) (BSN.sinOddQ 1099511627776) 0 2 Ns336p1631 Ns336p918 Ns336p1630 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1633 := @Ns336p1620 77440000 (Ns336p1626 rfl) (Enclosure.sfrac_false_div 600075735 268435456) (BSN.cos_reduce1 qz542 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns336p1627) (@Nat.cast Real Real.instNatCast Ns336p1628)) 226375608064910080 72057594037927936 Bool.false 331137434 536870912 0 1000000000000000 154880000 77440000 (BSN.sin_reduce_arg_pos_rat_q1 600075735 268435456 226375608064910080 72057594037927936 0 Ns336p1627 Ns336p1628 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 331137434 536870912 Ns336p1627 Ns336p1628 730801384381 1099511627776 155031251 154880000 (Ns336p1632 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p1634 := @Enclosure.Real.IsNear.inv_image qz190 165568717 268435456 1015893 2537553920000 435212331 435212896 268435456 (@Enclosure.Real.IsNear.neg qz188 Bool.true 165568717 268435456 1015893 2537553920000 (Ns336p1619 (Ns336p1633 rfl rfl) rfl)) 

noncomputable def Ns336p1635 := Ns336p1617 (@Enclosure.Real.IsNear.neg qz187 Bool.false 870425227 536870912 565 536870912 (@Ns336p1618 565 536870912 (Ns336p1634 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p1636 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns336p1609 (@HMul.hMul Real Real Real qz5 qz198 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz178))) (@HMul.hMul Real Real Real qz5 qz199 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz178))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz475 qz200) qz177) 

noncomputable def Ns336p1637 := nat_lit 772977586016315118269510294555333559770753857645528577146956723988084740360904495867201779273869484933175 

noncomputable def Ns336p1638 := nat_lit 54185425622294683882876402820198670034888468346889876386229704002456795531059129178764565319787249931982718427734852203891745976109756916646406009443101 

noncomputable def Ns336p1639 := nat_lit 17685113726012461574639139860935523598266999891907313105540928682880125 

noncomputable def Ns336p1640 := nat_lit 215679573337205118357336120696157045389097155380324579848828881993728 

noncomputable def Ns336p1641 := nat_lit 10830342454505970851350252719458188634916632114274243689726354533083885818841788762460393588070583947346287 

noncomputable def Ns336p1642 := nat_lit 35058230021589810586288373163293244933378061699828311654400000000000000000000000000000000000000000000000000000 

noncomputable def Ns336p1643 := nat_lit 8274914020609905630222835166572026925154040839195384869476560834027994789869740476518533190910295618113275756674150610655275726686628364240664772799797544845245350831718400 

noncomputable def Ns336p1644 := nat_lit 426441202586160365550172158228244911077962252827139118788029916823437146505263925882927159171565675397175 

noncomputable def Ns336p1645 := @Enclosure.Real.IsNear.subLit_ft (@HSub.hSub Real Real Real qz11 Ns336p1609 (@HMul.hMul Real Real Real qz5 qz198 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 2 Zeta.RiemannSiegel.correction qz178))) (@HMul.hMul Real Real Real qz5 qz199 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz178)) Ns336p1644 Ns336p1613 

noncomputable def Ns336p1646 := nat_lit 44104144269877906547865991036159670532506426118053358158863084954661988461625799216779301022309258301004378140686364934813490715507449368241975079523101 

noncomputable def Ns336p1647 := nat_lit 1202289599232779340462963975102619359663884429709165343882089374438230911844446048509625 

noncomputable def Ns336p1648 := nat_lit 31082702275611665134711390509176302506278509424834232340028998555822468563283335970816 

noncomputable def Ns336p1649 := nat_lit 462498788230468727872895191524121619537029097926170184758545135793732793269553675447885691159078553789325427148096702938381830203 

noncomputable def Ns336p1650 := nat_lit 382089520620832436682240735316604671486554345682723193001571143013690769408000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns336p1651 := nat_lit 24026232171866129553032156527211547994105757564507789412718086169897699780077873869107576637366145800055899288378347502457679129584967822403385379726737547979971641228587951331944023510220800 

noncomputable def Ns336p1652 := nat_lit 86470468640608387200454701757046847574153941285914100624345146445403646434175 

noncomputable def Ns336p1653 := nat_lit 64812599298209901678489366350832191212976579153465979723746077455166088815908955047359894171071710958827 

noncomputable def Ns336p1654 := nat_lit 995530257179329655503756355447197055514555198708315817325908459520000000000000000000000000000000000000000000 

noncomputable def Ns336p1655 := @Enclosure.Real.IsNear.subLit_tt_p Ns336p1609 (@HMul.hMul Real Real Real qz5 qz198 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 2 Zeta.RiemannSiegel.correction qz178)) Ns336p1652 Ns336p940 Ns336p1653 Ns336p1654 

noncomputable def Ns336p1656 := nat_lit 533486457932140355496143074620464060830252115250631801104693195055399114760410400281626055602413639352375 

noncomputable def Ns336p1657 := nat_lit 43561924637937831033592137212584369724308169437347774627672173932860335798524543393207099277780428115383328604985235531179426723609337368241975079523101 

noncomputable def Ns336p1658 := nat_lit 3086157361520319686603620396923270657497137628620360772337617062299434596541264964923277044689479238794631866493536868678017503627660798712934611816283202321610798637814003846348800 

noncomputable def Ns336p1659 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz5 qz195 qz196) (@HMul.hMul Real Real Real qz5 qz538 qz186) 

noncomputable def Ns336p1660 := nat_lit 41605205395597252567095369603534073441486071791339628356523308172941124330625 

noncomputable def Ns336p1661 := nat_lit 11323776856713676179517033430310313718617973009015905934446994724139458746361402151848438836671710958827 

noncomputable def Ns336p1662 := nat_lit 12629236519624052462649924530135151432170698725 

noncomputable def Ns336p1663 := nat_lit 713623846352979940529142984724747568191373312 

noncomputable def Ns336p1664 := nat_lit 108019816679435989038965388642206776580666680149356702848287652689 

noncomputable def Ns336p1665 := nat_lit 2010457343624685257767008178674021171200000000000000000000000000000000 

noncomputable def Ns336p1666 := nat_lit 61707388427255689932134729161199205013289138292857260158337098311379919058418237993344530871052655116082126331385059737600 

noncomputable def Ns336p1667 := nat_lit 320936899670724088982780608128909109132286110391948981093228937287875 

noncomputable def Ns336p1668 := @Enclosure.Real.IsNear.mulLit_tt qz195 qz196 Ns336p1667 Ns336p956 

noncomputable def Ns336p1669 := nat_lit 746451592597049665584241624440723657560710945392357529661209263984768318056000124752409041 

noncomputable def Ns336p1670 := nat_lit 98079714615416886934934209737619787751599303819750539264000000000000000000000000000000000000000 

noncomputable def Ns336p1671 := nat_lit 4687555635131415416114142975418941078659779225 

noncomputable def Ns336p1672 := nat_lit 5954249424439723602008681730471152335968800040159609104211 

noncomputable def Ns336p1673 := nat_lit 2126764793255865396646091296448551321600000000000000000000000000 

noncomputable abbrev qz202 := qz536

noncomputable abbrev qz203 := qz537

noncomputable def Ns336p1674 := @Enclosure.Real.IsNear.mulLit_ft qz202 qz203 Ns336p1671 Ns336p961 Ns336p1672 Ns336p1673 

noncomputable def Ns336p1675 := nat_lit 35621619566541310712356031 

noncomputable def Ns336p1676 := nat_lit 46116860184273879040000000000000 

noncomputable def Ns336p1677 := @Enclosure.Real.IsNear.mulLit_tt qz203 qz203 68465725988493070357435 37778931862957161709568 Ns336p1675 Ns336p1676 68465725988493070357435 37778931862957161709568 

noncomputable abbrev qz734 := (@HSub.hSub Real Real Real qz827 qz864 qz830)

noncomputable abbrev qz543 := qz734

noncomputable abbrev qz204 := qz543

noncomputable def Ns336p1678 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz204 884279719003555 140737488355328 1 500000000000000 77425417 268435456 33 268435456 

noncomputable abbrev qz735 := qz864

noncomputable abbrev qz544 := qz735

noncomputable abbrev qz205 := qz544

noncomputable def Ns336p1679 := @Enclosure.Real.IsNear.subLit_ff_n qz205 qz128 191010039 268435456 33 268435456 1 1 0 1 77425417 

noncomputable def Ns336p1680 := @Enclosure.Real.IsNear.mulLit_ff qz0 qz178 2 1 0 1 191010039 536870912 33 536870912 191010039 268435456 33 

noncomputable def Ns336p1681 := @Enclosure.Real.IsNear.recentre' qz196 Bool.true 259273430 268435456 

noncomputable def Ns336p1682 := @Enclosure.Real.IsNear.sin_image qz191 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 491992793)) (@Nat.cast Real Real.instNatCast 268435456)) Bool.true 491992793 268435456 

noncomputable def Ns336p1683 := nat_lit 74347848875047130994883778340205 

noncomputable def Ns336p1684 := nat_lit 163661932244296431091726894278646261 

noncomputable def Ns336p1685 := @Enclosure.Real.IsNear.recentre' qz191 Bool.true Ns336p1683 Ns336p974 Ns336p1684 

noncomputable def Ns336p1686 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz192 884279719003555 140737488355328 1 500000000000000 84077297349786031 

noncomputable def Ns336p1687 := @Enclosure.Real.IsNear.subLit_tf qz193 qz26 66062898840304047 288230376151711744 30323403759 288230376151711744 1 16 

noncomputable def Ns336p1688 := @Enclosure.Real.IsNear.subLit_ff_n qz194 qz178 36484834998781521 288230376151711744 12606663663 288230376151711744 191010039 536870912 33 536870912 

noncomputable def Ns336p1689 := nat_lit 35467248749757776070180864 

noncomputable def Ns336p1690 := @Enclosure.Real.IsNear.mulLit_ff qz178 qz178 191010039 536870912 33 536870912 191010039 536870912 33 536870912 36484834998781521 288230376151711744 

noncomputable def Ns336p1691 := nat_lit 82275724756581195098280988989804812521353685848005181428003786663788435750155310526783960514143998094110615201 

noncomputable def Ns336p1692 := nat_lit 201142985602459198763788891316626205322135460343896301234076001660579452583361880475298682759286858442401 

noncomputable def Ns336p1693 := nat_lit 410432381420072366093185181275171503994268794979634282891261706023339246316387295021374798148915350743429670561 

noncomputable def Ns336p1694 := BSN.sin_dyadic_bound_f 491992793 268435456 4 3 268435456 77440000 Ns336p1691 Ns336p158 Ns336p1692 Ns336p1693 Ns336p161 Ns336p1692 259273430 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 491992793) qz371 0 3 Ns336p1691 Ns336p158 Ns336p1692 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 491992793) qz372 0 3 Ns336p1693 Ns336p161 Ns336p1692 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1695 := @Ns336p1681 7026377728 10393820856320000 129636715 134217728 6861697 10150215680000 (@Ns336p1682 89 134217728 Bool.true 259273430 268435456 1 77440000 (@Ns336p1685 Ns336p977 491992793 268435456 89 134217728 (@Ns336p1686 288230376151711744 30323403759 288230376151711744 Ns336p1683 Ns336p974 Ns336p1684 Ns336p977 RS337to348.d59 (@Ns336p1687 0 1 1345236757596576496 84077297349786031 288230376151711744 30323403759 288230376151711744 (@Ns336p1688 Ns336p1689 66062898840304047 288230376151711744 30323403759 288230376151711744 (@Ns336p1690 12606663663 288230376151711744 (Ns336p1625 rfl rfl) (Ns336p1625 rfl rfl) rfl) (Ns336p1625 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 491992793 268435456) (BSN.sin_neg_of_bound 491992793 268435456 Bool.false 259273430 268435456 1 77440000 (Ns336p1694 rfl rfl)) rfl rfl) 

noncomputable def Ns336p1696 := nat_lit 181628558815437135435026832677657044275 

noncomputable def Ns336p1697 := nat_lit 2883863137598633536758313653159123557263571299469931 

noncomputable def Ns336p1698 := @Enclosure.Real.IsNear.mulLit_tt qz538 qz186 Ns336p1696 Ns336p991 Ns336p1697 

noncomputable def Ns336p1699 := nat_lit 99035203142830421991929937920000000000000000000000000000 

noncomputable def Ns336p1700 := nat_lit 106864858699623932137068093 

noncomputable def Ns336p1701 := @Enclosure.Real.IsNear.mulLit_tf qz197 qz461 205397177965479211072305 37778931862957161709568 Ns336p1700 Ns336p1676 884279719003555 

noncomputable def Ns336p1702 := @Enclosure.Real.IsNear.mulLit_ft qz320 qz203 3 1 0 1 68465725988493070357435 37778931862957161709568 Ns336p1675 

noncomputable def Ns336p1703 := @Enclosure.Real.IsNear.recentre' qz186 Bool.true 69533319 268435456 

noncomputable def Ns336p1704 := @Enclosure.Real.IsNear.cos_image qz191 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 491992793)) (@Nat.cast Real Real.instNatCast 268435456)) Bool.true 491992793 268435456 

noncomputable def Ns336p1705 := nat_lit 31738749281244569720164070257126464035510908205027840098983891866847788507391353229062848666600517455951685281 

noncomputable def Ns336p1706 := nat_lit 191690937771184642671058455705108605117664317385012536775789439501022118962164526508589474336779895332658210465 

noncomputable def Ns336p1707 := BSN.cos_dyadic_bound_t 491992793 268435456 4 3 268435456 77440000 Ns336p1705 Ns336p121 Ns336p1692 Ns336p1706 Ns336p124 Ns336p1692 69533319 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 491992793) qz369 0 3 Ns336p1705 Ns336p121 Ns336p1692 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 491992793) qz370 0 3 Ns336p1706 Ns336p124 Ns336p1692 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1708 := @Ns336p1703 7026377728 10393820856320000 69533319 268435456 6861697 10150215680000 (@Ns336p1704 89 134217728 Bool.true 69533319 268435456 1 77440000 (@Ns336p1685 Ns336p977 491992793 268435456 89 134217728 (@Ns336p1686 288230376151711744 30323403759 288230376151711744 Ns336p1683 Ns336p974 Ns336p1684 Ns336p977 RS337to348.d59 (@Ns336p1687 0 1 1345236757596576496 84077297349786031 288230376151711744 30323403759 288230376151711744 (@Ns336p1688 Ns336p1689 66062898840304047 288230376151711744 30323403759 288230376151711744 (@Ns336p1690 12606663663 288230376151711744 (Ns336p1625 rfl rfl) (Ns336p1625 rfl rfl) rfl) (Ns336p1625 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 491992793 268435456) (BSN.cos_neg_of_bound 491992793 268435456 Bool.true 69533319 268435456 1 77440000 (Ns336p1707 rfl rfl)) rfl rfl) 

noncomputable abbrev qz206 := (@Ns336p1678 68465725988493070357435 37778931862957161709568 Ns336p1675 Ns336p1676 RS337to348.d59 (@Ns336p1679 77425417 268435456 33 268435456 (@Ns336p1680 268435456 qz347 (Ns336p1625 rfl rfl) rfl) qz642 rfl rfl) rfl)

noncomputable def Ns336p1709 := @Ns336p1659 Ns336p1660 Ns336p940 Ns336p1661 Ns336p1654 Ns336p1662 Ns336p1663 Ns336p1664 Ns336p1665 Ns336p1666 Ns336p1652 Ns336p940 Ns336p1653 Ns336p1654 (@Ns336p1668 Ns336p1669 Ns336p1670 129636715 134217728 6861697 10150215680000 Ns336p1660 Ns336p940 Ns336p1661 Ns336p1654 (@Ns336p1674 68465725988493070357435 37778931862957161709568 Ns336p1675 Ns336p1676 Ns336p1667 Ns336p956 Ns336p1669 Ns336p1670 (@Ns336p1677 Ns336p1675 Ns336p1676 Ns336p1671 Ns336p961 Ns336p1672 Ns336p1673 qz206 qz206 rfl) qz206 rfl) (Ns336p1695 rfl) rfl) (@Ns336p1698 Ns336p1699 69533319 268435456 6861697 10150215680000 Ns336p1662 Ns336p1663 Ns336p1664 Ns336p1665 (@Ns336p1701 70368744177664 1 250000000000000 Ns336p1696 Ns336p991 Ns336p1697 Ns336p1699 (@Ns336p1702 Ns336p1676 205397177965479211072305 37778931862957161709568 Ns336p1700 Ns336p1676 qz480 qz206 rfl) RS337to348.d61 rfl) (Ns336p1708 rfl) rfl) rfl rfl 

noncomputable def Ns336p1710 := nat_lit 82244895368031936391855593697593 

noncomputable def Ns336p1711 := nat_lit 475880650401628918968233072823520567173449565297196833458115125519097364472236725 

noncomputable def Ns336p1712 := @Enclosure.Real.IsNear.mulLit_tf qz198 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz178) 1121050955700539351725755 75557863725914323419136 Ns336p1710 Ns336p1008 Ns336p1711 

noncomputable def Ns336p1713 := nat_lit 118571099379011784113736688648896417641748464297615937576404566024103044751294464 

noncomputable def Ns336p1714 := nat_lit 16739556220213645466872763697833995123201249275207338069563233404160914568461693777821065030681667311196714859627 

noncomputable def Ns336p1715 := nat_lit 47761190077604054585280091914575583935819293210340399125196392876711346176000000000000000000000000000000000000000000 

noncomputable def Ns336p1716 := nat_lit 27414965122677312130618531232531 

noncomputable abbrev qz207 := qz539

noncomputable def Ns336p1717 := @Enclosure.Real.IsNear.mulLit_ft qz320 qz207 3 1 0 1 373683651900179783908585 75557863725914323419136 Ns336p1716 

noncomputable def Ns336p1718 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz200 884279719003555 140737488355328 1 500000000000000 422585347 536870912 1015893 2537553920000 373683651900179783908585 

noncomputable def Ns336p1719 := @Enclosure.Real.IsNear.recentre' qz200 Bool.false 422585347 536870912 1040274432 2598455214080000 422585347 536870912 1015893 2537553920000 

noncomputable def Ns336p1720 := @Enclosure.Real.IsNear.sin_image qz189 qz542 Bool.false 600075735 268435456 13 33554432 Bool.false 422585347 536870912 1 

noncomputable def Ns336p1721 := nat_lit 700416683143930544320635795170147910105781453300459547345929086062652580701984842710493128387055521 

noncomputable def Ns336p1722 := nat_lit 2101087335444820448503592209530774239093997675461277511070231351609047107514947831065901249224626081 

noncomputable def Ns336p1723 := BSN.cos_dyadic_bound_f 730801384381 1099511627776 3 2 536870912 155031251 Ns336p1721 Ns336p1020 Ns336p1630 Ns336p1722 Ns336p1022 Ns336p1630 422585347 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 730801384381) (BSN.cosEvenQ 1099511627776) 0 2 Ns336p1721 Ns336p1020 Ns336p1630 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 730801384381) (BSN.cosOddQ 1099511627776) 0 2 Ns336p1722 Ns336p1022 Ns336p1630 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1724 := @Ns336p1720 77440000 (Ns336p1626 rfl) (Enclosure.sfrac_false_div 600075735 268435456) (BSN.sin_reduce1 qz542 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns336p1627) (@Nat.cast Real Real.instNatCast Ns336p1628)) 226375608064910080 72057594037927936 Bool.false 422585347 536870912 0 1000000000000000 154880000 77440000 (BSN.sin_reduce_arg_pos_rat_q1 600075735 268435456 226375608064910080 72057594037927936 0 Ns336p1627 Ns336p1628 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 422585347 536870912 Ns336p1627 Ns336p1628 730801384381 1099511627776 155031251 154880000 (Ns336p1723 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable abbrev qz545 := (@HMul.hMul Real Real Real qz627 qz625 qz733)

noncomputable abbrev qz208 := qz545

noncomputable abbrev qz546 := (@Enclosure.Real.IsNear.neg qz208 Bool.false 373683651900179783908585 75557863725914323419136 Ns336p1716 Ns336p1008 (@Ns336p1718 75557863725914323419136 Ns336p1716 Ns336p1008 RS337to348.d59 (Ns336p1719 (Ns336p1724 rfl rfl) rfl) rfl))

noncomputable def Ns336p1725 := @Ns336p1717 Ns336p1008 1121050955700539351725755 75557863725914323419136 Ns336p1710 Ns336p1008 qz480 qz546 rfl 

noncomputable abbrev qz209 := (@HMul.hMul Real Real Real qz349 qz536 (Real.cos qz531))

noncomputable def Ns336p1726 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz209) (@HMul.hMul Real Real Real qz5 qz461 qz196) 

noncomputable abbrev qz210 := (@HMul.hMul Real Real Real qz349 qz316 qz539)

noncomputable abbrev qz211 := (@Neg.neg Real Real.instNeg qz540)

noncomputable def Ns336p1727 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz178) (@HMul.hMul Real Real Real qz5 qz185 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns336p1726 (@HMul.hMul Real Real Real qz5 qz210 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c8 1 Zeta.RiemannSiegel.correction qz178))) (@HMul.hMul Real Real Real qz5 qz211 qz177))) 

noncomputable def Ns336p1728 := @Enclosure.Real.IsNear.mulLit_tt qz185 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns336p1726 (@HMul.hMul Real Real Real qz5 qz210 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 1 Zeta.RiemannSiegel.correction qz178))) (@HMul.hMul Real Real Real qz5 qz211 qz177)) 870425227 

noncomputable def Ns336p1729 := nat_lit 546722033829137765751167817225408343057421019918574618079302434462986175 

noncomputable def Ns336p1730 := nat_lit 220855883097298041197912187592864814478435487109452369765200775161577472 

noncomputable def Ns336p1731 := nat_lit 19088508545921141132302509692227193296450745609948492546656966758649588911791591357610968440551355070881 

noncomputable def Ns336p1732 := nat_lit 88962149019546908485293559570937573790213639308401195565604405248000000000000000000000000000000000000000000 

noncomputable def Ns336p1733 := nat_lit 1711786783170417620494323694215166648474320852475808072685357992311951425 

noncomputable def Ns336p1734 := @Enclosure.Real.IsNear.subLit_ff_n (@HSub.hSub Real Real Real qz11 Ns336p1726 (@HMul.hMul Real Real Real qz5 qz210 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz178))) (@HMul.hMul Real Real Real qz5 qz211 qz177) Ns336p1733 Ns336p1730 

noncomputable def Ns336p1735 := nat_lit 15533273022733600132102720415594984618892236597115632145626501937819088733382139546564797658195407550881 

noncomputable def Ns336p1736 := nat_lit 7835776531099470456639589614202586585519287155890351025 

noncomputable def Ns336p1737 := nat_lit 766247770432944429179173513575154591809369561091801088 

noncomputable def Ns336p1738 := nat_lit 163103484950746802827806525322400871845725693257517753395015432085940805949075543 

noncomputable def Ns336p1739 := nat_lit 4081315130646085667690305640373058260113240883200000000000000000000000000000000000000 

noncomputable def Ns336p1740 := nat_lit 418924539468141632885447556150332980369768507608155759750493047762006969399439664527454464187228389037182249973570001593958400 

noncomputable def Ns336p1741 := nat_lit 4976094134246199099163370455354360999981332528148096175 

noncomputable def Ns336p1742 := nat_lit 383123885216472214589586756787577295904684780545900544 

noncomputable def Ns336p1743 := nat_lit 493935696791428787695171829522000569745192020879005304638247025102511509 

noncomputable def Ns336p1744 := nat_lit 43174242704355286402013150575847227875578085376000000000000000000000000000000 

noncomputable def Ns336p1745 := @Enclosure.Real.IsNear.subLit_ff_p Ns336p1726 (@HMul.hMul Real Real Real qz5 qz210 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz178)) Ns336p1741 Ns336p1742 Ns336p1743 Ns336p1744 

noncomputable def Ns336p1746 := nat_lit 1156736184989799104180437390743598465454158573288008466302019129666006975 

noncomputable def Ns336p1747 := nat_lit 14515499963807423936943829884116284548895891739108801103259249561635917868313532006443230426195407550881 

noncomputable def Ns336p1748 := nat_lit 655826403030457291694325973589571022692551151640653806270909315542487241486290053365056369343669277687403310134653600609075200 

noncomputable def Ns336p1749 := @Enclosure.Real.IsNear.subLit_ft (@Neg.neg Real Real.instNeg qz209) (@HMul.hMul Real Real Real qz5 qz461 qz196) 

noncomputable def Ns336p1750 := nat_lit 325941301307840315050182443921414388664654521321497775 

noncomputable def Ns336p1751 := nat_lit 127168185214984563470165126111073633476212665638038053368205425102511509 

noncomputable def Ns336p1752 := nat_lit 185170272760225099074584772156999 

noncomputable def Ns336p1753 := nat_lit 21797422196473200640000000000000000000 

noncomputable def Ns336p1754 := nat_lit 46997880310336990817071285615964407626604206911714370174769186766486870425600 

noncomputable def Ns336p1755 := @Enclosure.Real.IsNear.neg qz209 Bool.true Ns336p1750 

noncomputable def Ns336p1756 := @Enclosure.Real.IsNear.mulLit_ft qz202 qz186 Ns336p1671 Ns336p961 Ns336p1672 

noncomputable def Ns336p1757 := @Enclosure.Real.IsNear.mulLit_ft qz461 qz196 884279719003555 70368744177664 1 

noncomputable def Ns336p1758 := nat_lit 3095495826771657023194735659672757147644613688935 

noncomputable def Ns336p1759 := @Enclosure.Real.IsNear.mulLit_tt qz210 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz178) 373683651900179783908585 37778931862957161709568 Ns336p1716 Ns336p1058 Ns336p1758 

noncomputable def Ns336p1760 := nat_lit 5846006549323611672814739330865132078623730171904 

noncomputable def Ns336p1761 := nat_lit 16556300639581964713607378916875925558457868921860801106256135061 

noncomputable def Ns336p1762 := nat_lit 1020328782661521416922576410093264565028310220800000000000000000000000 

noncomputable def Ns336p1763 := @Enclosure.Real.IsNear.mulLit_ft qz0 qz207 2 1 0 1 373683651900179783908585 75557863725914323419136 Ns336p1716 

noncomputable def Ns336p1764 := @Ns336p1763 Ns336p1008 373683651900179783908585 37778931862957161709568 Ns336p1716 Ns336p1058 qz347 qz546 rfl 

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz349 qz537 (Real.sin qz531))

noncomputable def Ns336p1765 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz212) (@HMul.hMul Real Real Real qz5 qz207 qz177) 

noncomputable def Ns336p1766 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz178) (@HMul.hMul Real Real Real qz5 qz185 Ns336p1765) Bool.true Ns336p1758 Ns336p1760 Ns336p1761 Ns336p1762 (BSN.deriv_correction_mk qz178 qz201) 

noncomputable def Ns336p1767 := nat_lit 3556302977845168799542083652950877936405 

noncomputable def Ns336p1768 := nat_lit 10889035741470030830827987437816582766592 

noncomputable def Ns336p1769 := nat_lit 18618022381635313579153673171901718337918755907210161183 

noncomputable def Ns336p1770 := @Enclosure.Real.IsNear.mulLit_tf qz185 Ns336p1765 870425227 536870912 565 536870912 Ns336p1767 Ns336p1768 Ns336p1769 

noncomputable def Ns336p1771 := nat_lit 1900510457645210282732874918902785638400000000000000000000000 

noncomputable def Ns336p1772 := @Enclosure.Real.IsNear.subLit_tt_p (@Neg.neg Real Real.instNeg qz212) (@HMul.hMul Real Real Real qz5 qz207 qz177) 

noncomputable def Ns336p1773 := nat_lit 8875671807238369441401749226025 

noncomputable def Ns336p1774 := nat_lit 922702066901216957550389710539923557107 

noncomputable def Ns336p1775 := nat_lit 468096077354784416446231347200000000000000000 

noncomputable def Ns336p1776 := nat_lit 22616663048904175213135234314436221475605 

noncomputable def Ns336p1777 := nat_lit 14871772386663657029709729159888520995779217172106161183 

noncomputable def Ns336p1778 := nat_lit 18032598417835471344061393208642641076735079193105845901962719128453120 

noncomputable def Ns336p1779 := @Enclosure.Real.IsNear.neg qz212 Bool.false Ns336p1773 

noncomputable def Ns336p1780 := @Enclosure.Real.IsNear.mulLit_tt qz203 qz196 68465725988493070357435 37778931862957161709568 Ns336p1675 

noncomputable def Ns336p1781 := @Enclosure.Real.IsNear.mulLit_tf qz207 qz177 373683651900179783908585 75557863725914323419136 Ns336p1716 Ns336p1008 60523554974638413 144115188075855872 

noncomputable def Ns336p1782 := @Enclosure.Real.IsNear.of_eq qz177 (@HMul.hMul Real Real Real qz5 qz185 qz186) Bool.false 60523554974638413 

noncomputable def Ns336p1783 := @Enclosure.Real.IsNear.mulLit_tt qz185 qz186 870425227 536870912 565 

noncomputable abbrev qz213 := (BSN.correction_mk qz522 (BSN.cos_two_pi_p_ne_zero_mk qz520 673823 1000 10 qz525 rfl rfl (@BSN.floor_sqrt_eq_dec qz520 673823 1000 10 qz525 rfl rfl rfl)))

noncomputable abbrev qz547 := (@Ns336p1782 144115188075855872 14916224437274923 10898711098236600320000 qz213 (@Ns336p1783 536870912 69533319 268435456 6861697 10150215680000 60523554974638413 144115188075855872 14916224437274923 10898711098236600320000 Ns336p1635 (Ns336p1708 rfl) rfl))

noncomputable def Ns336p1784 := @Ns336p1781 14916224437274923 10898711098236600320000 Ns336p1776 Ns336p1768 Ns336p1777 Ns336p1771 qz546 qz547 

noncomputable def Ns336p1785 := @Ns336p1759 Ns336p1760 Ns336p1761 Ns336p1762 Ns336p1746 Ns336p1730 Ns336p1747 Ns336p1732 Ns336p1764 (Ns336p1766 (@Ns336p1770 Ns336p1771 Ns336p1758 Ns336p1760 Ns336p1761 Ns336p1762 Ns336p1635 (@Ns336p1772 Ns336p1773 Ns336p1075 Ns336p1774 Ns336p1775 Ns336p1776 Ns336p1768 Ns336p1777 Ns336p1771 Ns336p1778 Ns336p1767 Ns336p1768 Ns336p1769 Ns336p1771 (@Ns336p1779 Ns336p1075 Ns336p1774 Ns336p1775 (@Ns336p1780 Ns336p1676 129636715 134217728 6861697 10150215680000 Ns336p1773 Ns336p1075 Ns336p1774 Ns336p1775 qz206 (Ns336p1695 rfl) rfl)) (Ns336p1784 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns336p1786 := @Ns336p1745 Ns336p1746 Ns336p1730 Ns336p1747 Ns336p1732 Ns336p1748 Ns336p1733 Ns336p1730 Ns336p1735 Ns336p1732 (@Ns336p1749 Ns336p1750 Ns336p1742 Ns336p1751 Ns336p1744 114635117912743943521825 9444732965739290427392 Ns336p1752 Ns336p1753 Ns336p1754 Ns336p1741 Ns336p1742 Ns336p1743 Ns336p1744 (@Ns336p1755 Ns336p1742 Ns336p1751 Ns336p1744 (@Ns336p1756 Ns336p1673 69533319 268435456 6861697 10150215680000 Ns336p1750 Ns336p1742 Ns336p1751 Ns336p1744 (@Ns336p1677 Ns336p1675 Ns336p1676 Ns336p1671 Ns336p961 Ns336p1672 Ns336p1673 qz206 qz206 rfl) (Ns336p1708 rfl) rfl)) (@Ns336p1757 250000000000000 129636715 134217728 6861697 10150215680000 114635117912743943521825 9444732965739290427392 Ns336p1752 Ns336p1753 RS337to348.d61 (Ns336p1695 rfl) rfl) rfl rfl) Ns336p1785 

noncomputable def Ns336p1787 := nat_lit 129466561149340086034592617680114663925 

noncomputable def Ns336p1788 := nat_lit 5316911983139663491615228241121378304 

noncomputable def Ns336p1789 := nat_lit 739822316399500113293276031682531442810919216731142945477 

noncomputable def Ns336p1790 := @Enclosure.Real.IsNear.mulLit_ff qz211 qz177 Ns336p1787 Ns336p1788 Ns336p1789 Ns336p1092 60523554974638413 144115188075855872 

noncomputable def Ns336p1791 := @Enclosure.Real.IsNear.mulLit_ft qz116 qz188 Ns336p847 Ns336p851 Ns336p849 Ns336p852 165568717 268435456 1015893 2537553920000 Ns336p1787 

noncomputable abbrev qz214 := qz540

noncomputable def Ns336p1792 := @Ns336p1790 14916224437274923 10898711098236600320000 Ns336p1736 Ns336p1737 Ns336p1738 Ns336p1739 (@Enclosure.Real.IsNear.neg qz214 Bool.true Ns336p1787 Ns336p1788 Ns336p1789 Ns336p1092 (@Ns336p1791 Ns336p1788 Ns336p1789 Ns336p1092 RS337to348.d63 (Ns336p1619 (Ns336p1633 rfl rfl) rfl) rfl)) qz547 

noncomputable def Ns336p1793 := nat_lit 388399683448020258103777853040343991775 

noncomputable def Ns336p1794 := nat_lit 2219466949198500339879828095047594328432757650193428836431 

noncomputable def Ns336p1795 := @Enclosure.Real.IsNear.mulLit_ft qz199 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz178) Ns336p1793 Ns336p1788 Ns336p1794 Ns336p1092 Ns336p1758 

noncomputable def Ns336p1796 := @Enclosure.Real.IsNear.mulLit_ff qz320 qz211 3 1 0 1 Ns336p1787 Ns336p1788 Ns336p1789 

noncomputable def Ns336p1797 := @Ns336p1796 Ns336p1092 Ns336p1793 Ns336p1788 Ns336p1794 Ns336p1092 qz480 (@Enclosure.Real.IsNear.neg qz214 Bool.true Ns336p1787 Ns336p1788 Ns336p1789 Ns336p1092 (@Ns336p1791 Ns336p1788 Ns336p1789 Ns336p1092 RS337to348.d63 (Ns336p1619 (Ns336p1633 rfl rfl) rfl) rfl)) rfl 

noncomputable def Ns336p1798 := @Ns336p1795 Ns336p1760 Ns336p1761 Ns336p1762 Ns336p1647 Ns336p1648 Ns336p1649 Ns336p1650 Ns336p1797 (Ns336p1766 (@Ns336p1770 Ns336p1771 Ns336p1758 Ns336p1760 Ns336p1761 Ns336p1762 Ns336p1635 (@Ns336p1772 Ns336p1773 Ns336p1075 Ns336p1774 Ns336p1775 Ns336p1776 Ns336p1768 Ns336p1777 Ns336p1771 Ns336p1778 Ns336p1767 Ns336p1768 Ns336p1769 Ns336p1771 (@Ns336p1779 Ns336p1075 Ns336p1774 Ns336p1775 (@Ns336p1780 Ns336p1676 129636715 134217728 6861697 10150215680000 Ns336p1773 Ns336p1075 Ns336p1774 Ns336p1775 qz206 (Ns336p1695 rfl) rfl)) (Ns336p1784 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns336p1799 := @Ns336p1645 Ns336p1646 Ns336p1616 Ns336p1647 Ns336p1648 Ns336p1649 Ns336p1650 Ns336p1651 Ns336p1637 Ns336p1613 Ns336p1638 Ns336p1616 (@Ns336p1655 Ns336p1656 Ns336p1613 Ns336p1657 Ns336p1616 Ns336p1658 Ns336p1644 Ns336p1613 Ns336p1646 Ns336p1616 Ns336p1709 (@Ns336p1712 Ns336p1713 Ns336p1714 Ns336p1715 Ns336p1656 Ns336p1613 Ns336p1657 Ns336p1616 Ns336p1725 (@Ns336p1727 Bool.false Ns336p1711 Ns336p1713 Ns336p1714 Ns336p1715 (BSN.iteratedDeriv_two_correction_mk qz178 qz201) (@Ns336p1728 536870912 565 536870912 Ns336p1729 Ns336p1730 Ns336p1731 Ns336p1732 Ns336p1711 Ns336p1713 Ns336p1714 Ns336p1715 Ns336p1635 (@Ns336p1734 Ns336p1735 Ns336p1732 Ns336p1736 Ns336p1737 Ns336p1738 Ns336p1739 Ns336p1740 Ns336p1729 Ns336p1730 Ns336p1731 Ns336p1732 (Ns336p1786 rfl rfl) (Ns336p1792 rfl) rfl rfl) rfl)) rfl) rfl rfl) Ns336p1798 

noncomputable def Ns336p1800 := nat_lit 292202163825690215554797385873603603877415473944944625 

noncomputable def Ns336p1801 := nat_lit 1496577676626844588240573268701473812127674924007424 

noncomputable def Ns336p1802 := nat_lit 19964900837553122587681276141724654408250909410128029292991123622783852044822452259 

noncomputable def Ns336p1803 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz335 RSCompact.c11) qz200) qz177 Ns336p1800 Ns336p1801 Ns336p1802 Ns336p1106 60523554974638413 144115188075855872 14916224437274923 

noncomputable def Ns336p1804 := @Enclosure.Real.IsNear.mulLit_ff qz463 qz200 Ns336p853 Ns336p854 Ns336p855 Ns336p856 422585347 536870912 1015893 2537553920000 Ns336p1800 

noncomputable def Ns336p1805 := Ns336p1611 (@Ns336p1615 Ns336p1616 Ns336p1604 Ns336p1605 Ns336p1606 Ns336p1607 Ns336p1635 (@Ns336p1636 Ns336p1637 Ns336p1613 Ns336p1638 Ns336p1616 Ns336p1639 Ns336p1640 Ns336p1641 Ns336p1642 Ns336p1643 Ns336p1612 Ns336p1613 Ns336p1614 Ns336p1616 (Ns336p1799 rfl rfl) (@Ns336p1803 10898711098236600320000 Ns336p1639 Ns336p1640 Ns336p1641 Ns336p1642 (@Ns336p1804 Ns336p1801 Ns336p1802 Ns336p1106 RS337to348.d64 (Ns336p1719 (Ns336p1724 rfl rfl) rfl) rfl) qz547 rfl) rfl rfl) rfl) 

noncomputable def Ns336p1806 := @Enclosure.Real.IsNear.of_eq qz724 (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz178) qz466)) Bool.false Ns336p1599 Ns336p1600 Ns336p1601 Ns336p1602 (BSN.correctionLinear_mk qz178) (@Enclosure.Real.IsNear.neg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz178) qz466) Bool.true Ns336p1599 Ns336p1600 Ns336p1601 Ns336p1602 (@Ns336p1608 Ns336p1600 Ns336p1601 Ns336p1602 Ns336p1805 RS337to348.d65 rfl)) 

noncomputable def Ns336p1807 := @Enclosure.Real.IsNear.inv_image qz179 347482425 33554432 33 33554432 1620081 1620082 16777216 qz528 rfl 

noncomputable def Ns336p1808 := @Ns336p1603 Ns336p1553 Ns336p1563 Ns336p1556 Ns336p1806 (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz179) Bool.false 3240163 33554432 1 33554432 3240163 33554432 1 33554432 (Ns336p1807 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns336p1809 := @Ns336p1555 Ns336p1556 Ns336p1469 Ns336p1465 Ns336p1471 Ns336p1467 (Ns336p1557 qz28 (@Enclosure.Real.IsNear.of_eq qz183 (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 10426977 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz184 (BSN.t_div_two_pi_nonneg qz175 673823 1000 qz180)) Ns336p1561) rfl) (@Ns336p1564 Ns336p1565 Ns336p1552 Ns336p1553 Ns336p1554 Ns336p1556 (@Ns336p1566 562949953421312 933589195651273 42573090227486720000 qz213 (@Ns336p1567 33554432 4345813 16777216 6861697 634388480000 236420366907749 562949953421312 933589195651273 42573090227486720000 Ns336p1584 (Ns336p1598 rfl) rfl)) (Ns336p1808 rfl) rfl rfl) 

noncomputable def Ns336p1810 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz175) (hardyZApproximantRS qz175) Bool.false Ns336p1464 Ns336p1465 Ns336p1466 Ns336p1467 (@Eq.refl Real (hardyZApproximantRS qz175)) (Ns336p1468 (BSN.hardyZApproximantRS_eq qz175 10 (@BSN.floor_sqrt_eq_dec qz175 673823 1000 10 qz180 rfl rfl rfl)) (@Ns336p1470 Ns336p1471 Ns336p1467 Ns336p1472 Ns336p1464 Ns336p1465 Ns336p1466 Ns336p1467 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz175) qz175 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz175) qz175 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz175) qz175 10)) Bool.false 209425181 134217728 165143 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz175) qz175 10) (Ns336p1551 (Ns336p1550 rfl rfl rfl rfl) rfl rfl)) (Ns336p1809 rfl) rfl rfl)) 

theorem RS337to348.d70 : Enclosure.Real.IsNear (hardyZApproximantRS qz175) Bool.false Ns336p1464 Ns336p1465 Ns336p1466 Ns336p1467 := Ns336p1810 

noncomputable def Ns336p1811 := nat_lit 1767414353153800768001119 

noncomputable def Ns336p1812 := nat_lit 1428515861068067677143040000 

noncomputable def Ns336p1813 := nat_lit 3625063026010699850064236380160 

noncomputable def Ns336p1814 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz175) qz175 10) (@HMul.hMul Real Real Real qz5 qz176 qz177) 209425181 134217728 165143 134217728 2465149728078659944773 18889465931478580854784 9752393294340917761119 Ns336p1812 Ns336p1813 

noncomputable def Ns336p1815 := @Enclosure.Real.IsNear.mulLit_ff qz176 qz177 10426977 33554432 1 33554432 236420366907749 562949953421312 933589195651273 42573090227486720000 2465149728078659944773 18889465931478580854784 

noncomputable def Ns336p1816 := @Ns336p1815 9752393294340917761119 Ns336p1812 (Ns336p1557 qz28 (@Enclosure.Real.IsNear.of_eq qz183 (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 10426977 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz184 (BSN.t_div_two_pi_nonneg qz175 673823 1000 qz180)) Ns336p1561) rfl) (@Ns336p1566 562949953421312 933589195651273 42573090227486720000 qz213 (@Ns336p1567 33554432 4345813 16777216 6861697 634388480000 236420366907749 562949953421312 933589195651273 42573090227486720000 Ns336p1584 (Ns336p1598 rfl) rfl)) 

noncomputable def Ns336p1817 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz175) (hardyZApproximantRS₀ qz175) Bool.false 27008824244221298769595 18889465931478580854784 Ns336p1811 Ns336p1812 (@Eq.refl Real (hardyZApproximantRS₀ qz175)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz175) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz175) qz175 10) (@HMul.hMul Real Real Real qz5 qz176 qz177)) Bool.false 27008824244221298769595 18889465931478580854784 Ns336p1811 Ns336p1812 (BSN.hardyZApproximantRS₀_eq qz175 10 (@BSN.floor_sqrt_eq_dec qz175 673823 1000 10 qz180 rfl rfl rfl)) (@Ns336p1814 27008824244221298769595 18889465931478580854784 Ns336p1811 Ns336p1812 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz175) qz175 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz175) qz175 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz175) qz175 10)) Bool.false 209425181 134217728 165143 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz175) qz175 10) (Ns336p1551 (Ns336p1550 rfl rfl rfl rfl) rfl rfl)) (Ns336p1816 rfl) rfl rfl)) 

theorem RS337to348.d71 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz175) Bool.false 27008824244221298769595 18889465931478580854784 Ns336p1811 Ns336p1812 := Ns336p1817 

noncomputable def Ns336p1818 := nat_lit 35712896526701691928576000 

noncomputable def Ns336p1819 := nat_lit 433512327984049057452221530112 

noncomputable abbrev qz865 := (Enclosure.sfrac Bool.false 675167 1000)

noncomputable abbrev qz736 := qz865

noncomputable abbrev qz548 := qz736

noncomputable abbrev qz215 := qz548

noncomputable abbrev qz866 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 675167 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz737 := qz866

noncomputable abbrev qz549 := qz737

noncomputable abbrev qz216 := qz549

noncomputable abbrev qz867 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 675167 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz738 := qz867

noncomputable abbrev qz550 := qz738

noncomputable abbrev qz217 := qz550

noncomputable abbrev qz551 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz630 qz216 qz8))

noncomputable def Ns336p1820 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz215) qz215 10) (@HMul.hMul Real Real Real qz5 qz551 (Zeta.RiemannSiegel.correction qz217)) 174955501 67108864 165467 134217728 304137632638450107351 2361183241434822606848 227373954700436894827 Ns336p1818 Ns336p1819 

noncomputable def Ns336p1821 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz215) qz215 Real.sin BSN.quadSignPos 9 10 675167 1000 199 268435456 134217728 4503599627370496 Bool.false 333109578539 2536 618095470 56 84886744 8 

noncomputable def Ns336p1822 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz215) qz215 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 675167 1000 103 154 268435456 134217728 4503599627370496 Bool.false 333109578539 2536 

noncomputable def Ns336p1823 := Ns336p1822 558195838 56 94906264 8 589812974 56 89478488 8 Bool.true 445369092 124966 Bool.true 335115704 Bool.true 177433724 14148475504056880 1 Bool.false 254605642 Bool.false Bool.false 211898533 Bool.true Bool.true 425985252 

noncomputable def Ns336p1824 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz215) qz215 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 675167 1000 19 46 268435456 134217728 4503599627370496 Bool.false 333109578539 2536 

noncomputable def Ns336p1825 := Ns336p1824 480971758 57 109588312 8 522351262 57 101459064 8 Bool.true 470131590 92695 Bool.false 361828468 Bool.true 168514271 14148475504056880 1 Bool.false 261795664 Bool.false Bool.false 217256216 Bool.true Bool.true 445369092 

noncomputable def Ns336p1826 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz215) qz215 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 675167 1000 194 98 268435456 134217728 4503599627370496 Bool.false 333109578539 2536 

noncomputable def Ns336p1827 := Ns336p1826 372130544 56 134217720 8 432030192 56 120047984 16 Bool.true 226343758 54451 Bool.false 57774454 Bool.false 94621926 14148475504056880 1 Bool.false 262242118 Bool.true Bool.false 251930582 Bool.true Bool.true 470131590 

noncomputable def Ns336p1828 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz215) qz215 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 675167 1000 492 317 268435456 134217728 4503599627370496 Bool.false 333109578539 2536 

noncomputable def Ns336p1829 := Ns336p1828 186065264 56 189812528 16 294906480 56 154981288 8 Bool.true 268435368 2600 Bool.false 28997732 Bool.false 333050396 14148475504056880 1 Bool.false 266870738 Bool.false Bool.false 253943746 Bool.true Bool.true 226343758 

noncomputable def Ns336p1830 := nat_lit 1191125419298879798770341417759790770344030987113729610213 

noncomputable def Ns336p1831 := nat_lit 959865208572314307757845574286037853921223381090304000 

noncomputable def Ns336p1832 := nat_lit 67343840038337183551656925091360000 

noncomputable def Ns336p1833 := nat_lit 272810100503964550784373152022805542720 

noncomputable abbrev qz552 := (@Eq.refl Real qz736)

noncomputable abbrev qz218 := qz552

noncomputable def Ns336p1834 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz215 675167 1000 1823402911556 16000000 1350334 4000 2000 Ns336p1832 Ns336p1833 qz218 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns336p1835 := nat_lit 381160134175641535606509253683133046510089915876393475268160 

noncomputable abbrev qz739 := (Real.log (Enclosure.sfrac Bool.false 1823402911556 16000000))

noncomputable abbrev qz740 := (@Nat.cast Real Real.instNatCast 1350334)

noncomputable abbrev qz741 := (Enclosure.sfrac Bool.false 675167 2000)

noncomputable abbrev qz219 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 675167 4000) qz739) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz740))))) qz741)

noncomputable abbrev qz553 := (@HSub.hSub Real Real Real qz11 qz219 (@HMul.hMul Real Real Real qz5 qz741 (Real.log Real.pi)))

noncomputable def Ns336p1836 := @Enclosure.Real.IsNear.addLit_ft_p qz553 (Enclosure.sfrac Bool.true Ns336p1832 Ns336p1833) 1397163115639575218253 1125899906842624000 4679275600616770363 495616000000000000000000 Ns336p1832 Ns336p1833 0 1 Ns336p1835 

noncomputable def Ns336p1837 := nat_lit 18752405902654505267902178918400 

noncomputable abbrev qz554 := (@HMul.hMul Real Real Real qz5 qz741 (Real.log Real.pi))

noncomputable def Ns336p1838 := @Enclosure.Real.IsNear.subLit_ff_p qz219 qz554 366451607536977117609 225179981368524800 533724545545953 121000000000000000000 25933678272087 67108864000 675167 134217728000 Ns336p1837 1397163115639575218253 1125899906842624000 

noncomputable def Ns336p1839 := nat_lit 3664516075369771176090000 

noncomputable abbrev qz220 := (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 675167 4000) qz739) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz740)))))

noncomputable def Ns336p1840 := @Enclosure.Real.IsNear.subLit_ff_p qz220 qz741 2212343268886492547149 1125899906842624000 533724545545953 121000000000000000000 675167 2000 0 1 Ns336p1839 366451607536977117609 225179981368524800 533724545545953 121000000000000000000 

noncomputable def Ns336p1841 := nat_lit 4981754160686416436213943128085757952 

noncomputable def Ns336p1842 := nat_lit 56305121952859009211957248 

noncomputable def Ns336p1843 := nat_lit 42554236762100871700052223347070274954718354115541114956190550422274096043221439896049741283792550073428033182488764257012338165291754104702760941634191360 

noncomputable def Ns336p1844 := nat_lit 1080022454765612166275632279048315674364023768809159293457091818905370927648939758025770195130301672200176853884450564171543231838000004342332942966587392 

noncomputable def Ns336p1845 := nat_lit 486721857917891799253342558716534734785219794921666317602990922301263351966321238974469747098753394141153069991049525239479404550805575476938014720 

noncomputable def Ns336p1846 := BSN.log_dyadic_bound 774826911556 2871978911556 7 6 Ns336p1843 134217728 38720000 Ns336p1844 Ns336p1845 74258834 3646805823112 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 774826911556) (BSN.artanhQ 2871978911556) 0 6 Ns336p1844 Ns336p1843 Ns336p1845 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns336p1847 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 675167 4000) qz739 675167 4000 0 1 3277389446323447 281474976710656 195312621 7562500000000000 2212785200305862740649 1125899906842624000 131868636382707 30250000000000000000 (Enclosure.Real.IsNear.const Bool.false 675167 4000) (BSN.isNear_log_sfrac 1823402911556 16000000 3277389446323447 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1823402911556) qz362)) Bool.false Ns336p1842 Ns336p98 1000000619520000 38720000000000000000000 3277389446323447 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1823402911556 16000000 16 3646805823112 2097152000000 74258834 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns336p1846 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p1848 := BSN.arctan_dyadic_bound_f 1000 1350334 1 0 16777216 4840000 0 1 1 0 1 1 12424 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1350334) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1350334) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz742 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1350334)))

noncomputable def Ns336p1849 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz742 884279719003555 562949953421312 1 2000000000000000 12424 16777216 1 4840000 14828757759920640622592 883862838740387 562949953421312 50000000121 242000000000000000 qz16 (Ns336p1848 rfl) rfl rfl 

noncomputable def Ns336p1850 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 675167 4000) qz739) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz742)) 2212785200305862740649 1125899906842624000 131868636382707 30250000000000000000 883862838740387 2251799813685248 50000000121 968000000000000000 Ns336p1841 2212343268886492547149 1125899906842624000 533724545545953 121000000000000000000 (Ns336p1847 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz742) 1 4 0 1 883862838740387 562949953421312 50000000121 242000000000000000 883862838740387 2251799813685248 50000000121 968000000000000000 qz364 Ns336p1849 rfl) 

noncomputable def Ns336p1851 := @Ns336p1836 Ns336p1830 Ns336p1831 4679275600616770363 495616000000000000000000 (@Ns336p1838 4679275600616770363 495616000000000000000000 (Ns336p1840 (Ns336p1850 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 675167 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz741 (Real.log Real.pi) 675167 2000 0 1 38410761 33554432 1 67108864 25933678272087 67108864000 675167 134217728000 (Enclosure.Real.IsNear.const Bool.false 675167 2000) RS337to348.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns336p1832 Ns336p1833) 

noncomputable def Ns336p1852 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz215) Bool.false Ns336p1830 Ns336p1831 4679275600616770363 495616000000000000000000 41638697317 33554432 159 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz215) (@HAdd.hAdd Real Real Real qz365 qz553 (Enclosure.sfrac Bool.true Ns336p1832 Ns336p1833)) Bool.false Ns336p1830 Ns336p1831 4679275600616770363 495616000000000000000000 Ns336p1834 (Ns336p1851 rfl rfl)) 

noncomputable def Ns336p1853 := BSN.cos_dyadic_bound_f 53812636 68719476736 1 0 33554432 9689454 0 1 1 0 1 1 33554421 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 53812636) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 53812636) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns336p1854 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz215) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 41638697317) qz396) Bool.false 41638697317 33554432 159 16777216 Bool.true 33554421 33554432 1 4840000 (Ns336p1852 rfl) (Enclosure.sfrac_false_div 41638697317 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 41638697317) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3786727675566200193024) qz413) 226375608064910080 72057594037927936 Bool.false 33554421 33554432 197 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q2 41638697317 33554432 226375608064910080 72057594037927936 197 3786727675566200193024 Ns336p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554421 33554432 3786727675566200193024 Ns336p98 53812636 68719476736 9689454 9680000 (Ns336p1853 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p1855 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz215) Bool.false Ns336p1830 Ns336p1831 4679275600616770363 495616000000000000000000 333109578539 268435456 2536 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz215) (@HAdd.hAdd Real Real Real qz365 qz553 (Enclosure.sfrac Bool.true Ns336p1832 Ns336p1833)) Bool.false Ns336p1830 Ns336p1831 4679275600616770363 495616000000000000000000 Ns336p1834 (Ns336p1851 rfl rfl)) 

noncomputable def Ns336p1856 := Ns336p1829 54451 BSN.abs_quadSignPos (BSN.cos_quad_nat0 492 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266870738 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 317 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 253943746 268435456) qz218 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz215) qz215 1) Bool.true 33554421 33554432 12286519 1268776960000 268435368 268435456 2600 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz215) qz215 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz215)) Bool.true 33554421 33554432 12286519 1268776960000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz215) qz215) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz215)) Bool.true 33554421 33554432 786337216 81201725440000 33554421 33554432 12286519 1268776960000 (Ns336p1854 rfl rfl) rfl)) rfl) (Ns336p1855 rfl) RS337to348.d7 

noncomputable def Ns336p1857 := nat_lit 707059768946382652090413342976 

noncomputable def Ns336p1858 := BSN.cos_dyadic_bound_f 28997732 268435456 2 1 268435456 134217728 Ns336p1857 Ns336p142 Ns336p1857 Ns336p1857 Ns336p143 Ns336p1857 266870738 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 28997732) qz369 0 1 Ns336p1857 Ns336p142 Ns336p1857 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 28997732) qz370 0 1 Ns336p1857 Ns336p143 Ns336p1857 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1859 := nat_lit 17226543558132923009117662745419220796023459043652484217614722709934976686680966377576065389830477684582383616 

noncomputable def Ns336p1860 := nat_lit 1862599373240600628384699627351677597951727196985935271956436059491600798750953286030938649805000278016 

noncomputable def Ns336p1861 := nat_lit 86091019306426791089408789615279831936814073193590980309598440199670820916388872626690349607476531133232971776 

noncomputable def Ns336p1862 := BSN.sin_dyadic_bound_f 333050396 268435456 4 3 268435456 134217728 Ns336p1859 Ns336p158 Ns336p1860 Ns336p1861 Ns336p161 Ns336p1860 253943746 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 333050396) qz371 0 3 Ns336p1859 Ns336p158 Ns336p1860 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 333050396) qz372 0 3 Ns336p1861 Ns336p161 Ns336p1860 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1863 := nat_lit 11141493196295799064768123549456 

noncomputable def Ns336p1864 := BSN.cos_dyadic_bound_f 57774454 268435456 2 1 268435456 134217728 Ns336p1863 Ns336p142 Ns336p1863 Ns336p1863 Ns336p143 Ns336p1863 262242118 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 57774454) qz369 0 1 Ns336p1863 Ns336p142 Ns336p1863 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 57774454) qz370 0 1 Ns336p1863 Ns336p143 Ns336p1863 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1865 := nat_lit 699261990335169350341702462464178015410347982043373200457140641997056 

noncomputable def Ns336p1866 := nat_lit 6425904543760324007921950373082880717605447201504602382476779776 

noncomputable def Ns336p1867 := nat_lit 2097773119196420530377091543491787880469608735235716592166656972431616 

noncomputable def Ns336p1868 := BSN.cos_dyadic_bound_f 94621926 268435456 3 2 268435456 134217728 Ns336p1865 Ns336p251 Ns336p1866 Ns336p1867 Ns336p254 Ns336p1866 251930582 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 94621926) qz369 0 2 Ns336p1865 Ns336p251 Ns336p1866 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 94621926) qz370 0 2 Ns336p1867 Ns336p254 Ns336p1866 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1869 := Ns336p1827 92695 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 194 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 262242118 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 98 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 251930582 268435456) qz218 rfl rfl (Ns336p1856 RS337to348.d9 RS337to348.d11 RS337to348.d13 RS337to348.d17 (Ns336p1858 rfl rfl) (Ns336p1862 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns336p1855 rfl) RS337to348.d19 RS337to348.d21 RS337to348.d23 RS337to348.d25 RS337to348.d17 (Ns336p1864 rfl rfl) (Ns336p1868 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns336p1870 := nat_lit 24005068388031193519236269255749323018774929118676384668660043190053036929537990291719304100239715135469387776 

noncomputable def Ns336p1871 := nat_lit 5035386373882339561785437973925929248068893896165639991532583212137575758202670767255133556542564990976 

noncomputable def Ns336p1872 := nat_lit 119944415022415940465735571047506205342061112959542584128647774829833726556655092984212016512335787847514587136 

noncomputable def Ns336p1873 := BSN.sin_dyadic_bound_f 361828468 268435456 4 3 268435456 134217728 Ns336p1870 Ns336p158 Ns336p1871 Ns336p1872 Ns336p161 Ns336p1871 261795664 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 361828468) qz371 0 3 Ns336p1870 Ns336p158 Ns336p1871 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 361828468) qz372 0 3 Ns336p1872 Ns336p161 Ns336p1871 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1874 := nat_lit 7034863674601143640319744900375511994792377492569672394627721278839041 

noncomputable def Ns336p1875 := nat_lit 650269654301673418095109276318067752153162909737554647977972783361 

noncomputable def Ns336p1876 := nat_lit 21103290484494827574123044482573899848872826151889542074587207890950401 

noncomputable def Ns336p1877 := BSN.cos_dyadic_bound_f 168514271 268435456 3 2 268435456 134217728 Ns336p1874 Ns336p251 Ns336p1875 Ns336p1876 Ns336p254 Ns336p1875 217256216 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 168514271) qz369 0 2 Ns336p1874 Ns336p251 Ns336p1875 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 168514271) qz370 0 2 Ns336p1876 Ns336p254 Ns336p1875 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1878 := Ns336p1825 124966 BSN.abs_quadSignPos (BSN.cos_quad_nat3 19 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 261795664 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 46 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 217256216 268435456) qz218 rfl rfl (Ns336p1869 rfl rfl) (Ns336p1855 rfl) RS337to348.d27 RS337to348.d29 RS337to348.d31 RS337to348.d33 RS337to348.d17 (Ns336p1873 rfl rfl) (Ns336p1877 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p1879 := nat_lit 17658181033644640603729055987272642920006194428946730068869652038281891936353497443021932262864570595636412416 

noncomputable def Ns336p1880 := nat_lit 2006029704776798838730364542933460096163008236123243329467676405864891104376057958004982273952832290816 

noncomputable def Ns336p1881 := nat_lit 88247092387705997842040706632428807351023095491067904286893992965467156305162714498267749724168106538304536576 

noncomputable def Ns336p1882 := BSN.sin_dyadic_bound_f 335115704 268435456 4 3 268435456 134217728 Ns336p1879 Ns336p158 Ns336p1880 Ns336p1881 Ns336p161 Ns336p1880 254605642 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 335115704) qz371 0 3 Ns336p1879 Ns336p158 Ns336p1880 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 335115704) qz372 0 3 Ns336p1881 Ns336p161 Ns336p1880 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1883 := nat_lit 8646947275596514864815169875974931487598786623523082762046746730233856 

noncomputable def Ns336p1884 := nat_lit 982402233871322830243705970208747431627803704652980295052600344576 

noncomputable def Ns336p1885 := nat_lit 25938877022321801948785022215984376967933104263159942325550134990012416 

noncomputable def Ns336p1886 := BSN.cos_dyadic_bound_f 177433724 268435456 3 2 268435456 134217728 Ns336p1883 Ns336p251 Ns336p1884 Ns336p1885 Ns336p254 Ns336p1884 211898533 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 177433724) qz369 0 2 Ns336p1883 Ns336p251 Ns336p1884 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 177433724) qz370 0 2 Ns336p1885 Ns336p254 Ns336p1884 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1887 := Ns336p1823 152698 BSN.abs_quadSignPos (BSN.cos_quad_nat3 103 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 254605642 268435456) BSN.abs_quadSignNeg qz678 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 211898533 268435456) qz218 rfl rfl (Ns336p1878 rfl) (Ns336p1855 rfl) RS337to348.d35 RS337to348.d37 RS337to348.d39 RS337to348.d41 RS337to348.d17 (Ns336p1882 rfl rfl) (Ns336p1886 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p1888 := nat_lit 124315478696073522081818888462675215484086898825846057207681699260786785 

noncomputable def Ns336p1889 := nat_lit 62622465061083270759667556067634704002201673376428749357113676785761 

noncomputable def Ns336p1890 := nat_lit 325486769736760327775914769930516060556604979929844503283064361634883681 

noncomputable def Ns336p1891 := BSN.sin_dyadic_bound_f 298257429 268435456 3 2 268435456 134217728 Ns336p1888 Ns336p127 Ns336p1889 Ns336p1890 Ns336p130 Ns336p1889 240567903 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 298257429) qz371 0 2 Ns336p1888 Ns336p127 Ns336p1889 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 298257429) qz372 0 2 Ns336p1890 Ns336p130 Ns336p1889 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1892 := Ns336p1821 Bool.true 425985252 152698 Bool.true 298257429 14148475504056880 1 Bool.false 240567903 Bool.false Bool.true 349911002 165467 BSN.abs_quadSignPos qz373 (BSN.sfrac_eq_quadSignPos_mul Bool.false 240567903 268435456) qz218 rfl (Ns336p1887 rfl) (Ns336p1855 rfl) RS337to348.d43 RS337to348.d45 RS337to348.d17 (Ns336p1891 rfl rfl) rfl 

noncomputable def Ns336p1893 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz215) qz215 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz215) qz215 10) 349911002 268435456 165467 268435456 349911002 268435456 165467 268435456 187857038762573824 174955501 67108864 165467 134217728 (Ns336p1892 rfl rfl rfl rfl) 

noncomputable def Ns336p1894 := @Enclosure.Real.IsNear.mulLit_ff qz551 (Zeta.RiemannSiegel.correction qz217) 1302723 4194304 1 16777216 233463009894237 562949953421312 173859776199031 8514618045497344000 304137632638450107351 2361183241434822606848 

noncomputable abbrev qz555 := (@HPow.hPow Real Real Real qz630 qz216 qz8)

noncomputable def Ns336p1895 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz555 1 1 0 1 1302723 4194304 1 16777216 1302723 4194304 1 16777216 

noncomputable def Ns336p1896 := @Enclosure.Real.IsNear.sqrt_image qz216 3605630113951 33554432000 675167 33554432000 173914381 173914414 16777216 (@Enclosure.Real.IsNear.of_eq qz216 (@HMul.hMul Real Real Real qz5 qz215 qz3) Bool.false 3605630113951 33554432000 675167 33554432000 (BSN.t_div_two_pi_mk qz215 675167 1000 qz218) (@Enclosure.Real.IsNear.mulLit_ff qz215 qz3 675167 1000 0 1 5340353 33554432 1 33554432 3605630113951 33554432000 675167 33554432000 (Enclosure.Real.IsNear.const Bool.false 675167 1000) RS337to348.d48 rfl)) 

noncomputable abbrev qz868 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 675167 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz743 := qz868

noncomputable abbrev qz556 := qz743

noncomputable abbrev qz221 := qz556

noncomputable def Ns336p1897 := @Enclosure.Real.IsNear.sqrt_image qz221 347828795 33554432 33 33554432 54016656 54016662 16777216 (@Enclosure.Real.IsNear.recentre' qz221 Bool.false 347828795 33554432 33 33554432 347828795 33554432 33 33554432 (Ns336p1896 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns336p1898 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz221) 54016659 16777216 3 16777216 5210891 5210893 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz221) Bool.false 108033318 33554432 6 33554432 54016659 16777216 3 16777216 (Ns336p1897 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns336p1899 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz221)) Bool.false 10421784 33554432 2 33554432 1302723 4194304 1 16777216 (Ns336p1898 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz222 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz550))

noncomputable abbrev qz744 := (@HMul.hMul Real Real Real qz824 qz867 qz867)

noncomputable abbrev qz557 := (@HSub.hSub Real Real Real qz631 (@HSub.hSub Real Real Real qz631 qz744 qz738) qz639)

noncomputable abbrev qz223 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz557))

noncomputable def Ns336p1900 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz217) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz222) qz223) Bool.false 233463009894237 

noncomputable def Ns336p1901 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz222) qz223 50343633 33554432 487 

noncomputable abbrev qz745 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz222))

noncomputable def Ns336p1902 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz222) (@Neg.neg Real Real.instNeg qz745) Bool.true 50343633 33554432 487 33554432 (BSN.inv_eq_neg_inv_neg qz222) 

noncomputable def Ns336p1903 := @Enclosure.Real.IsNear.recentre' qz745 Bool.false 50343633 33554432 487 33554432 50343633 33554432 

noncomputable def Ns336p1904 := @Enclosure.Real.IsNear.recentre' qz222 Bool.true 22364296 33554432 1045114432 162403450880000 2795537 4194304 16329913 2537553920000 

noncomputable abbrev qz224 := (@HMul.hMul Real Real Real qz349 qz346 qz550)

noncomputable def Ns336p1905 := @Enclosure.Real.IsNear.cos_image qz224 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2412051) qz692) Bool.false 2412051 1048576 209 33554432 Bool.true 22364296 33554432 1 

noncomputable def Ns336p1906 := nat_lit 890540488603976336767635111 

noncomputable def Ns336p1907 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz217 884279719003555 140737488355328 1 500000000000000 12284475 33554432 33 33554432 10862912101106196308625 4722366482869645213696 Ns336p1906 

noncomputable def Ns336p1908 := @Enclosure.Real.IsNear.subLit_ff_p qz221 qz1 347828795 33554432 33 33554432 10 1 0 1 12284475 12284475 33554432 33 

noncomputable def Ns336p1909 := @Ns336p1908 33554432 (@Enclosure.Real.IsNear.recentre' qz221 Bool.false 347828795 33554432 33 33554432 347828795 33554432 33 33554432 (Ns336p1896 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns336p1910 := @Enclosure.Real.IsNear.recentre' qz224 Bool.false 10862912101106196308625 4722366482869645213696 Ns336p1906 Ns336p304 2412051 1048576 209 33554432 (@Ns336p1907 Ns336p304 RS337to348.d47 (Ns336p1909 rfl rfl) rfl) 

noncomputable def Ns336p1911 := nat_lit 425988180531974391968370831880041499899606679534145023993623191416698998611314205851529185 

noncomputable def Ns336p1912 := nat_lit 39894352938267885513140758258102815309022308342513801168327311752493316807249445138401 

noncomputable def Ns336p1913 := nat_lit 1115618739107556688102521379410547952321802886471158611924264399967564769088134992414257121 

noncomputable def Ns336p1914 := BSN.sin_dyadic_bound_f 50131872699 68719476736 3 2 33554432 9689454 Ns336p1911 Ns336p1224 Ns336p1912 Ns336p1913 Ns336p1227 Ns336p1912 22364296 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 50131872699) qz366 0 2 Ns336p1911 Ns336p1224 Ns336p1912 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 50131872699) qz367 0 2 Ns336p1913 Ns336p1227 Ns336p1912 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1915 := @Ns336p1905 4840000 (Ns336p1910 rfl) (Enclosure.sfrac_false_div 2412051 1048576) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2412051) qz692) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 110241153911285079867392) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false 22364296 33554432 0 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q1 2412051 1048576 226375608064910080 72057594037927936 0 110241153911285079867392 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 22364296 33554432 110241153911285079867392 151115727451828646838272 50131872699 68719476736 9689454 9680000 (Ns336p1914 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p1916 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz222) 2795537 4194304 16329913 2537553920000 25171573 25172060 16777216 (@Enclosure.Real.IsNear.neg qz222 Bool.true 2795537 4194304 16329913 2537553920000 (Ns336p1904 (Ns336p1915 rfl rfl) rfl)) 

noncomputable def Ns336p1917 := Ns336p1902 (@Enclosure.Real.IsNear.neg qz745 Bool.false 50343633 33554432 487 33554432 (@Ns336p1903 487 33554432 (Ns336p1916 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p1918 := @Enclosure.Real.IsNear.recentre' qz223 Bool.true 4637389 16777216 

noncomputable abbrev qz225 := (@HMul.hMul Real Real Real qz349 qz346 qz557)

noncomputable def Ns336p1919 := @Enclosure.Real.IsNear.cos_image qz225 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 62104313)) qz396) Bool.true 62104313 33554432 

noncomputable def Ns336p1920 := nat_lit 293279326613366216799980074645 

noncomputable def Ns336p1921 := nat_lit 51761254390147268749833725861863553 

noncomputable def Ns336p1922 := @Enclosure.Real.IsNear.recentre' qz225 Bool.true Ns336p1920 Ns336p194 Ns336p1921 

noncomputable abbrev qz226 := qz557

noncomputable def Ns336p1923 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz226 884279719003555 140737488355328 1 500000000000000 331658999195239 

noncomputable abbrev qz558 := (@HSub.hSub Real Real Real qz631 qz744 qz738)

noncomputable abbrev qz227 := qz558

noncomputable def Ns336p1924 := @Enclosure.Real.IsNear.subLit_tf qz227 qz26 261290255017575 1125899906842624 1918072695 1125899906842624 1 16 

noncomputable abbrev qz559 := qz744

noncomputable abbrev qz228 := qz559

noncomputable def Ns336p1925 := @Enclosure.Real.IsNear.subLit_ff_n qz228 qz217 150908326025625 1125899906842624 810776439 1125899906842624 12284475 33554432 33 33554432 

noncomputable def Ns336p1926 := @Enclosure.Real.IsNear.mulLit_ff qz217 qz217 12284475 33554432 33 33554432 12284475 33554432 33 33554432 150908326025625 1125899906842624 

noncomputable def Ns336p1927 := nat_lit 480438676606842700069454735332307833676152094686903992392235481541160699921411160309768141047958561 

noncomputable def Ns336p1928 := nat_lit 3292009983316395792699163914833612235518178604586392777822310268875041147998093295005758491681 

noncomputable def Ns336p1929 := nat_lit 2901165895132574872170802525504521365512271630611923849514048517445099650009284587023349246635379745 

noncomputable def Ns336p1930 := BSN.cos_dyadic_bound_t 62104313 33554432 4 3 16777216 4840000 Ns336p1927 Ns336p328 Ns336p1928 Ns336p1929 Ns336p331 Ns336p1928 4637389 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 62104313) (BSN.cosEvenQ 33554432) 0 3 Ns336p1927 Ns336p328 Ns336p1928 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 62104313) (BSN.cosOddQ 33554432) 0 3 Ns336p1929 Ns336p331 Ns336p1928 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1931 := @Ns336p1918 221994304 20300431360000 4637389 16777216 3468661 317194240000 (@Ns336p1919 45 4194304 Bool.true 4637389 16777216 1 4840000 (@Ns336p1922 Ns336p197 62104313 33554432 45 4194304 (@Ns336p1923 1125899906842624 1918072695 1125899906842624 Ns336p1920 Ns336p194 Ns336p1921 Ns336p197 RS337to348.d47 (@Ns336p1924 0 1 5306543987123824 331658999195239 1125899906842624 1918072695 1125899906842624 (@Ns336p1925 8767446094249879142400 261290255017575 1125899906842624 1918072695 1125899906842624 (@Ns336p1926 810776439 1125899906842624 (Ns336p1909 rfl rfl) (Ns336p1909 rfl rfl) rfl) (Ns336p1909 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 62104313 33554432) (BSN.cos_neg_of_bound 62104313 33554432 Bool.true 4637389 16777216 1 4840000 (Ns336p1930 rfl rfl)) rfl rfl) 

noncomputable def Ns336p1932 := @Ns336p1894 227373954700436894827 Ns336p1818 (Ns336p1895 qz28 (@Enclosure.Real.IsNear.of_eq qz555 (@Inv.inv Real Real.instInv (Real.sqrt qz221)) Bool.false 1302723 4194304 1 16777216 (BSN.rpow_neg_quarter_mk qz216 (BSN.t_div_two_pi_nonneg qz215 675167 1000 qz218)) Ns336p1899) rfl) (@Ns336p1900 562949953421312 173859776199031 8514618045497344000 (BSN.correction_mk qz217 (BSN.cos_two_pi_p_ne_zero_mk qz215 675167 1000 10 qz218 rfl rfl (@BSN.floor_sqrt_eq_dec qz215 675167 1000 10 qz218 rfl rfl rfl))) (@Ns336p1901 33554432 4637389 16777216 3468661 317194240000 233463009894237 562949953421312 173859776199031 8514618045497344000 Ns336p1917 (Ns336p1931 rfl) rfl)) 

noncomputable def Ns336p1933 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz215) (hardyZApproximantRS₀ qz215) Bool.true 6459837078810469172183 2361183241434822606848 44255133458897593758827 Ns336p1818 (@Eq.refl Real (hardyZApproximantRS₀ qz215)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz215) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz215) qz215 10) (@HMul.hMul Real Real Real qz5 qz551 (Zeta.RiemannSiegel.correction qz217))) Bool.true 6459837078810469172183 2361183241434822606848 44255133458897593758827 Ns336p1818 (BSN.hardyZApproximantRS₀_eq qz215 10 (@BSN.floor_sqrt_eq_dec qz215 675167 1000 10 qz218 rfl rfl rfl)) (@Ns336p1820 6459837078810469172183 2361183241434822606848 44255133458897593758827 Ns336p1818 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz215) qz215 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz215) qz215 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz215) qz215 10)) Bool.true 174955501 67108864 165467 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz215) qz215 10) (Ns336p1893 (Ns336p1892 rfl rfl rfl rfl) rfl rfl)) (Ns336p1932 rfl) rfl rfl)) 

theorem RS337to348.d72 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz215) Bool.true 6459837078810469172183 2361183241434822606848 44255133458897593758827 Ns336p1818 := Ns336p1933 

noncomputable def Ns336p1934 := nat_lit 223661806241365519047252246528 

noncomputable abbrev qz869 := (Enclosure.sfrac Bool.false 676845 1000)

noncomputable abbrev qz746 := qz869

noncomputable abbrev qz560 := qz746

noncomputable abbrev qz229 := qz560

noncomputable abbrev qz870 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 676845 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz747 := qz870

noncomputable abbrev qz561 := qz747

noncomputable abbrev qz230 := qz561

noncomputable abbrev qz871 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 676845 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz748 := qz871

noncomputable abbrev qz562 := qz748

noncomputable abbrev qz231 := qz562

noncomputable abbrev qz563 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz630 qz230 qz8))

noncomputable def Ns336p1935 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz229) qz229 10) (@HMul.hMul Real Real Real qz5 qz563 (Zeta.RiemannSiegel.correction qz231)) 111753513 134217728 165879 134217728 299578277958207337557 2361183241434822606848 43304428239081698979 Ns336p211 Ns336p1934 

noncomputable def Ns336p1936 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz229) qz229 Real.sin BSN.quadSignPos 9 10 676845 1000 199 268435456 134217728 4503599627370496 Bool.false 334163218525 2542 618095470 56 84886744 8 

noncomputable def Ns336p1937 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz229) qz229 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 676845 1000 103 154 268435456 134217728 4503599627370496 Bool.false 334163218525 2542 

noncomputable def Ns336p1938 := Ns336p1937 558195838 56 94906264 8 589812974 56 89478488 8 Bool.false 50822545 125278 Bool.true 218128334 Bool.true 113499909 14148475504056880 1 Bool.false 194903329 Bool.false Bool.false 244795790 Bool.true Bool.false 38132677 

noncomputable def Ns336p1939 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz229) qz229 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 676845 1000 20 45 268435456 134217728 4503599627370496 Bool.false 334163218525 2542 

noncomputable def Ns336p1940 := Ns336p1939 480971758 57 109588312 8 522351262 57 101459064 8 Bool.false 68106085 92927 Bool.false 186740416 Bool.true 413037131 14148475504056880 1 Bool.false 206058956 Bool.false Bool.false 268297055 Bool.true Bool.false 50822545 

noncomputable def Ns336p1941 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz229) qz229 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 676845 1000 195 99 268435456 134217728 4503599627370496 Bool.false 334163218525 2542 

noncomputable def Ns336p1942 := Ns336p1941 372130544 56 134217720 8 432030192 56 120047984 16 Bool.false 35025101 54588 Bool.false 65321959 Bool.false 1657822 14148475504056880 1 Bool.false 64679181 Bool.false Bool.false 1657811 Bool.false Bool.false 68106085 

noncomputable def Ns336p1943 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz229) qz229 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 676845 1000 493 319 268435456 134217728 4503599627370496 Bool.false 334163218525 2542 

noncomputable def Ns336p1944 := Ns336p1943 186065264 56 189812528 16 294906480 56 154981288 8 Bool.false 190019864 2608 Bool.false 348762777 Bool.false 48522452 14148475504056880 1 Bool.false 258598719 Bool.true Bool.false 48258644 Bool.false Bool.false 35025101 

noncomputable def Ns336p1945 := nat_lit 344980523072421677190681598734847648295149757704711 

noncomputable def Ns336p1946 := nat_lit 277125066099720721349818410825075686807185653760 

noncomputable def Ns336p1947 := nat_lit 68184861541054981638773773500000000 

noncomputable def Ns336p1948 := nat_lit 276903566176210535160025571757645000000 

noncomputable abbrev qz749 := (@Eq.refl Real qz869)

noncomputable abbrev qz564 := qz749

noncomputable abbrev qz232 := qz564

noncomputable def Ns336p1949 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz229 676845 1000 1832477616100 16000000 1353690 4000 2000 Ns336p1947 Ns336p1948 qz232 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns336p1950 := nat_lit 15524123538258975473580671943068144173281739096711995000000 

noncomputable abbrev qz750 := (Real.log (Enclosure.sfrac Bool.false 1832477616100 16000000))

noncomputable abbrev qz751 := (@Nat.cast Real Real.instNatCast 1353690)

noncomputable abbrev qz752 := (Enclosure.sfrac Bool.false 676845 2000)

noncomputable abbrev qz233 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 676845 4000) qz750) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz751))))) qz752)

noncomputable abbrev qz565 := (@HSub.hSub Real Real Real qz11 qz233 (@HMul.hMul Real Real Real qz5 qz752 (Real.log Real.pi)))

noncomputable def Ns336p1951 := @Enclosure.Real.IsNear.addLit_ft_p qz565 (Enclosure.sfrac Bool.true Ns336p1947 Ns336p1948) 56063296054313733031 45035996273704960 938168286394137741 99123200000000000000000 Ns336p1947 Ns336p1948 0 1 Ns336p1950 

noncomputable def Ns336p1952 := nat_lit 3762344110300676923309686784000 

noncomputable abbrev qz566 := (@HMul.hMul Real Real Real qz5 qz752 (Real.log Real.pi))

noncomputable def Ns336p1953 := @Enclosure.Real.IsNear.subLit_ff_p qz233 qz566 367551733923408312899 225179981368524800 107007096771621 24200000000000000000 5199626305809 13421772800 135369 26843545600 Ns336p1952 56063296054313733031 45035996273704960 

noncomputable abbrev qz234 := (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 676845 4000) qz750) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz751)))))

noncomputable def Ns336p1954 := @Enclosure.Real.IsNear.subLit_ff_p qz234 qz752 443757706168097897027 225179981368524800 107007096771621 24200000000000000000 676845 2000 0 1 735103467846816625798000 367551733923408312899 225179981368524800 107007096771621 24200000000000000000 

noncomputable def Ns336p1955 := nat_lit 999253520070715871727368603692957696 

noncomputable def Ns336p1956 := nat_lit 56329128588831091245187072 

noncomputable def Ns336p1957 := nat_lit 5502725799010229436299826891717230063786219887748604696980675614945916651674974470955422905434302011624785155101285532303706867402435527448919662692030250000000000000000000000000000 

noncomputable def Ns336p1958 := nat_lit 142163239338506451586584625186638637482645419367362717862808143501191566692590323536561838102413856202462142086547302068132375694117311034625267303768150000000000000000000000000000 

noncomputable def Ns336p1959 := nat_lit 4471257514998272139466675503037265179278548531210245297582599006006120534782496752924658364457656350708712519669228257730843796301041604478135350000000000000000000000000000 

noncomputable def Ns336p1960 := BSN.log_dyadic_bound 783901616100 2881053616100 8 7 Ns336p1957 134217728 38720000 Ns336p1958 Ns336p1959 74925152 3664955232200 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 783901616100) (BSN.artanhQ 2881053616100) 0 7 Ns336p1958 Ns336p1957 Ns336p1959 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns336p1961 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 676845 4000) qz750 676845 4000 0 1 3278786816449783 281474976710656 195312621 7562500000000000 443846092555990674927 225179981368524800 26439274192149 6050000000000000000 (Enclosure.Real.IsNear.const Bool.false 676845 4000) (BSN.isNear_log_sfrac 1832477616100 16000000 3278786816449783 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1832477616100) qz362)) Bool.false Ns336p1956 Ns336p98 1000000619520000 38720000000000000000000 3278786816449783 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1832477616100 16000000 16 3664955232200 2097152000000 74925152 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns336p1960 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p1962 := BSN.arctan_dyadic_bound_f 1000 1353690 1 0 16777216 4840000 0 1 1 0 1 1 12393 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1353690) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1353690) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz753 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1353690)))

noncomputable def Ns336p1963 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz753 884279719003555 562949953421312 1 2000000000000000 12393 16777216 1 4840000 14828775211369196683264 883863878927779 562949953421312 50000000121 242000000000000000 qz16 (Ns336p1962 rfl) rfl rfl 

noncomputable def Ns336p1964 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 676845 4000) qz750) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz753)) 443846092555990674927 225179981368524800 26439274192149 6050000000000000000 883863878927779 2251799813685248 50000000121 968000000000000000 Ns336p1955 443757706168097897027 225179981368524800 107007096771621 24200000000000000000 (Ns336p1961 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz753) 1 4 0 1 883863878927779 562949953421312 50000000121 242000000000000000 883863878927779 2251799813685248 50000000121 968000000000000000 qz364 Ns336p1963 rfl) 

noncomputable def Ns336p1965 := @Ns336p1951 Ns336p1945 Ns336p1946 938168286394137741 99123200000000000000000 (@Ns336p1953 938168286394137741 99123200000000000000000 (Ns336p1954 (Ns336p1964 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 676845 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz752 (Real.log Real.pi) 676845 2000 0 1 38410761 33554432 1 67108864 5199626305809 13421772800 135369 26843545600 (Enclosure.Real.IsNear.const Bool.false 676845 2000) RS337to348.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns336p1947 Ns336p1948) 

noncomputable def Ns336p1966 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz229) Bool.false Ns336p1945 Ns336p1946 938168286394137741 99123200000000000000000 41770402315 33554432 319 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz229) (@HAdd.hAdd Real Real Real qz365 qz565 (Enclosure.sfrac Bool.true Ns336p1947 Ns336p1948)) Bool.false Ns336p1945 Ns336p1946 938168286394137741 99123200000000000000000 Ns336p1949 (Ns336p1965 rfl rfl)) 

noncomputable def Ns336p1967 := nat_lit 3792667390430433939292160 

noncomputable def Ns336p1968 := nat_lit 316217784632497405613492056522750835055238550061773174024436877848551170253023263504531456 

noncomputable def Ns336p1969 := nat_lit 20052072892042597411705012245279816272850392000149059967199507548332190919545345701492817920 

noncomputable def Ns336p1970 := nat_lit 71206502761406766245216020044191918221734142679877492156798448731355442221867115544576 

noncomputable def Ns336p1971 := nat_lit 948510940891969403307985737528164121329272181899959767088997036648190799874626056282505216 

noncomputable def Ns336p1972 := nat_lit 902343280141916883526725551037591732278267640006707698523977839674948591379540556567176806400 

noncomputable def Ns336p1973 := BSN.cos_dyadic_bound_f 53897045268 68719476736 3 2 33554432 9689454 Ns336p1968 Ns336p1969 Ns336p1970 Ns336p1971 Ns336p1972 Ns336p1970 23752483 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 53897045268) (BSN.cosEvenQ 68719476736) 0 2 Ns336p1968 Ns336p1969 Ns336p1970 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 53897045268) (BSN.cosOddQ 68719476736) 0 2 Ns336p1971 Ns336p1972 Ns336p1970 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1974 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz229) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 41770402315) qz396) Bool.false 41770402315 33554432 319 33554432 Bool.false 23752483 33554432 1 4840000 (Ns336p1966 rfl) (Enclosure.sfrac_false_div 41770402315 33554432) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 41770402315) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns336p1967) qz413) 226375608064910080 72057594037927936 Bool.false 23752483 33554432 198 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q0 41770402315 33554432 226375608064910080 72057594037927936 198 Ns336p1967 Ns336p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 23752483 33554432 Ns336p1967 Ns336p98 53897045268 68719476736 9689454 9680000 (Ns336p1973 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p1975 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz229) Bool.false Ns336p1945 Ns336p1946 938168286394137741 99123200000000000000000 334163218525 268435456 2542 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz229) (@HAdd.hAdd Real Real Real qz365 qz565 (Enclosure.sfrac Bool.true Ns336p1947 Ns336p1948)) Bool.false Ns336p1945 Ns336p1946 938168286394137741 99123200000000000000000 Ns336p1949 (Ns336p1965 rfl rfl)) 

noncomputable def Ns336p1976 := Ns336p1944 54588 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 493 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 258598719 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 319 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 48258644 268435456) qz232 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz229) qz229 1) Bool.false 23752483 33554432 24648663 2537553920000 190019864 268435456 2608 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz229) qz229 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz229)) Bool.false 23752483 33554432 24648663 2537553920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz229) qz229) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz229)) Bool.false 23752483 33554432 1577514432 162403450880000 23752483 33554432 24648663 2537553920000 (Ns336p1974 rfl rfl) rfl)) rfl) (Ns336p1975 rfl) RS337to348.d7 

noncomputable def Ns336p1977 := nat_lit 20717994276020373879893678288905454463604412171749988669191049006123306580020110543590211003585308980580924321 

noncomputable def Ns336p1978 := nat_lit 3238631417178649223987431419566404162326261525530144369403653489681488602362027817325223268391280393121 

noncomputable def Ns336p1979 := nat_lit 103529674150044867136429201459832836242049718902388203999535134568999482077419062920383641886827415063935794081 

noncomputable def Ns336p1980 := BSN.sin_dyadic_bound_f 348762777 268435456 4 3 268435456 134217728 Ns336p1977 Ns336p158 Ns336p1978 Ns336p1979 Ns336p161 Ns336p1978 258598719 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 348762777) qz371 0 3 Ns336p1977 Ns336p158 Ns336p1978 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 348762777) qz372 0 3 Ns336p1979 Ns336p161 Ns336p1978 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1981 := nat_lit 5543332846300655412476104028416 

noncomputable def Ns336p1982 := BSN.sin_dyadic_bound_f 48522452 268435456 2 1 268435456 134217728 Ns336p1981 Ns336p137 Ns336p1981 Ns336p1981 Ns336p138 Ns336p1981 48258644 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 48522452) qz371 0 1 Ns336p1981 Ns336p137 Ns336p1981 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 48522452) qz372 0 1 Ns336p1981 Ns336p138 Ns336p1981 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1983 := nat_lit 18206933369455198769036596577761 

noncomputable def Ns336p1984 := BSN.sin_dyadic_bound_f 65321959 268435456 2 1 268435456 134217728 Ns336p1983 Ns336p137 Ns336p1983 Ns336p1983 Ns336p138 Ns336p1983 64679181 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 65321959) qz371 0 1 Ns336p1983 Ns336p137 Ns336p1983 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 65321959) qz372 0 1 Ns336p1983 Ns336p138 Ns336p1983 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1985 := BSN.sin_dyadic_bound_f 1657822 268435456 1 0 268435456 134217728 0 1 1 0 1 1 1657811 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1657822) qz371 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1657822) qz372 0 0 rfl) rfl rfl 

noncomputable def Ns336p1986 := Ns336p1942 92927 BSN.abs_quadSignPos (BSN.cos_quad_nat3 195 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 64679181 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 1657811 268435456) qz232 rfl rfl (Ns336p1976 RS337to348.d9 RS337to348.d11 RS337to348.d13 RS337to348.d17 (Ns336p1980 rfl rfl) (Ns336p1982 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns336p1975 rfl) RS337to348.d19 RS337to348.d21 RS337to348.d23 RS337to348.d25 RS337to348.d17 (Ns336p1984 rfl rfl) (Ns336p1985 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns336p1987 := nat_lit 10609199675514428003409727968309859365851524492973151240409832621080576 

noncomputable def Ns336p1988 := nat_lit 1478790239986698777201866889605088464141648710093789426900843626496 

noncomputable def Ns336p1989 := nat_lit 31824641446063310612674780171150367920626290181499266142375696175988736 

noncomputable def Ns336p1990 := BSN.cos_dyadic_bound_f 186740416 268435456 3 2 268435456 134217728 Ns336p1987 Ns336p251 Ns336p1988 Ns336p1989 Ns336p254 Ns336p1988 206058956 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 186740416) qz369 0 2 Ns336p1987 Ns336p251 Ns336p1988 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 186740416) qz370 0 2 Ns336p1989 Ns336p254 Ns336p1988 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1991 := nat_lit 40792376227214006001322343705438330720401599370855552155446337756791525698982263839074332641465253231997826961 

noncomputable def Ns336p1992 := nat_lit 24652964181845203168075949686568372211428853180960720822483079901555663004006047431236006287762666370961 

noncomputable def Ns336p1993 := nat_lit 203728503444733681991538764356027691384477636647522820888573119711056599844954399581133481295975956357261637521 

noncomputable def Ns336p1994 := BSN.sin_dyadic_bound_f 413037131 268435456 4 3 268435456 134217728 Ns336p1991 Ns336p158 Ns336p1992 Ns336p1993 Ns336p161 Ns336p1992 268297055 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 413037131) qz371 0 3 Ns336p1991 Ns336p158 Ns336p1992 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 413037131) qz372 0 3 Ns336p1993 Ns336p161 Ns336p1992 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p1995 := Ns336p1940 125278 BSN.abs_quadSignPos (BSN.cos_quad_nat0 20 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 206058956 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 45 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268297055 268435456) qz232 rfl rfl (Ns336p1986 rfl rfl) (Ns336p1975 rfl) RS337to348.d27 RS337to348.d29 RS337to348.d31 RS337to348.d33 RS337to348.d17 (Ns336p1990 rfl rfl) (Ns336p1994 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p1996 := nat_lit 35551034517201548983754854351944832170714307305261513272028712133443840 

noncomputable def Ns336p1997 := nat_lit 5125032914453538861245941449483834664439717044266334303238172426496 

noncomputable def Ns336p1998 := nat_lit 93101554634618751132630220349889681857652188162375151171203289022710016 

noncomputable def Ns336p1999 := BSN.sin_dyadic_bound_f 218128334 268435456 3 2 268435456 134217728 Ns336p1996 Ns336p127 Ns336p1997 Ns336p1998 Ns336p130 Ns336p1997 194903329 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 218128334) qz371 0 2 Ns336p1996 Ns336p127 Ns336p1997 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 218128334) qz372 0 2 Ns336p1998 Ns336p130 Ns336p1997 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2000 := nat_lit 1447635123004997596290501031156424699490284003185073399179751283461601 

noncomputable def Ns336p2001 := nat_lit 27540010824901441890499778767700066858123278866048967881528151521 

noncomputable def Ns336p2002 := nat_lit 4342850288993342985987722093911738698337135762997488099603490794081761 

noncomputable def Ns336p2003 := BSN.cos_dyadic_bound_f 113499909 268435456 3 2 268435456 134217728 Ns336p2000 Ns336p251 Ns336p2001 Ns336p2002 Ns336p254 Ns336p2001 244795790 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 113499909) qz369 0 2 Ns336p2000 Ns336p251 Ns336p2001 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 113499909) qz370 0 2 Ns336p2002 Ns336p254 Ns336p2001 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2004 := Ns336p1938 153079 BSN.abs_quadSignPos (BSN.cos_quad_nat3 103 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 194903329 268435456) BSN.abs_quadSignNeg qz678 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 244795790 268435456) qz232 rfl rfl (Ns336p1995 rfl) (Ns336p1975 rfl) RS337to348.d35 RS337to348.d37 RS337to348.d39 RS337to348.d41 RS337to348.d17 (Ns336p1999 rfl rfl) (Ns336p2003 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p2005 := nat_lit 99029919754185154472489957763208438847963236244490667841693133535699200 

noncomputable def Ns336p2006 := nat_lit 39746744600397964126558427567341894202532649231869165107710403010816 

noncomputable def Ns336p2007 := nat_lit 259299723674465236438411651925674976773099613493957294270450485274337536 

noncomputable def Ns336p2008 := BSN.sin_dyadic_bound_f 281781642 268435456 3 2 268435456 134217728 Ns336p2005 Ns336p127 Ns336p2006 Ns336p2007 Ns336p130 Ns336p2006 232809529 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 281781642) qz371 0 2 Ns336p2005 Ns336p127 Ns336p2006 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 281781642) qz372 0 2 Ns336p2007 Ns336p130 Ns336p2006 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2009 := Ns336p1936 Bool.false 38132677 153079 Bool.true 281781642 14148475504056880 1 Bool.false 232809529 Bool.false Bool.false 111753513 165879 BSN.abs_quadSignPos qz373 (BSN.sfrac_eq_quadSignPos_mul Bool.false 232809529 268435456) qz232 rfl (Ns336p2004 rfl) (Ns336p1975 rfl) RS337to348.d43 RS337to348.d45 RS337to348.d17 (Ns336p2008 rfl rfl) rfl 

noncomputable def Ns336p2010 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz229) qz229 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz229) qz229 10) 111753513 268435456 165879 268435456 111753513 268435456 165879 268435456 59997210443513856 111753513 134217728 165879 134217728 (Ns336p2009 rfl rfl rfl rfl) 

noncomputable def Ns336p2011 := @Enclosure.Real.IsNear.mulLit_ff qz563 (Zeta.RiemannSiegel.correction qz231) 10415319 33554432 1 33554432 28763235956403 70368744177664 1296690219621 66520453480448000 299578277958207337557 2361183241434822606848 

noncomputable abbrev qz567 := (@HPow.hPow Real Real Real qz630 qz230 qz8)

noncomputable def Ns336p2012 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz567 1 1 0 1 10415319 33554432 1 33554432 10415319 33554432 1 33554432 

noncomputable def Ns336p2013 := @Enclosure.Real.IsNear.sqrt_image qz230 722918245257 6710886400 135369 6710886400 174130362 174130396 16777216 (@Enclosure.Real.IsNear.of_eq qz230 (@HMul.hMul Real Real Real qz5 qz229 qz3) Bool.false 722918245257 6710886400 135369 6710886400 (BSN.t_div_two_pi_mk qz229 676845 1000 qz232) (@Enclosure.Real.IsNear.mulLit_ff qz229 qz3 676845 1000 0 1 5340353 33554432 1 33554432 722918245257 6710886400 135369 6710886400 (Enclosure.Real.IsNear.const Bool.false 676845 1000) RS337to348.d48 rfl)) 

noncomputable abbrev qz872 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 676845 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz754 := qz872

noncomputable abbrev qz568 := qz754

noncomputable abbrev qz235 := qz568

noncomputable def Ns336p2014 := @Enclosure.Real.IsNear.sqrt_image qz235 174130379 16777216 17 16777216 54050186 54050193 16777216 (@Enclosure.Real.IsNear.recentre' qz235 Bool.false 348260758 33554432 34 33554432 174130379 16777216 17 16777216 (Ns336p2013 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns336p2015 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz235) 108100379 33554432 7 33554432 5207659 5207660 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz235) Bool.false 108100379 33554432 7 33554432 108100379 33554432 7 33554432 (Ns336p2014 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns336p2016 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz235)) Bool.false 10415319 33554432 1 33554432 10415319 33554432 1 33554432 (Ns336p2015 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz236 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz562))

noncomputable abbrev qz755 := (@HMul.hMul Real Real Real qz824 qz871 qz871)

noncomputable abbrev qz569 := (@HSub.hSub Real Real Real qz631 (@HSub.hSub Real Real Real qz631 qz755 qz748) qz639)

noncomputable abbrev qz237 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz569))

noncomputable def Ns336p2017 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz231) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz236) qz237) Bool.false 28763235956403 

noncomputable def Ns336p2018 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz236) qz237 11577459 8388608 53 

noncomputable abbrev qz756 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz236))

noncomputable def Ns336p2019 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz236) (@Neg.neg Real Real.instNeg qz756) Bool.true 11577459 8388608 53 4194304 (BSN.inv_eq_neg_inv_neg qz236) 

noncomputable def Ns336p2020 := @Enclosure.Real.IsNear.recentre' qz756 Bool.false 46309836 33554432 424 33554432 11577459 8388608 

noncomputable def Ns336p2021 := @Enclosure.Real.IsNear.recentre' qz236 Bool.true 24312328 33554432 1074154432 162403450880000 3039041 4194304 16783663 2537553920000 

noncomputable abbrev qz238 := (@HMul.hMul Real Real Real qz349 qz346 qz562)

noncomputable def Ns336p2022 := @Enclosure.Real.IsNear.cos_image qz238 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9987467) (@Nat.cast Real Real.instNatCast 4194304)) Bool.false 9987467 4194304 215 33554432 Bool.true 24312328 33554432 1 

noncomputable def Ns336p2023 := nat_lit 458763282008365458069484087 

noncomputable def Ns336p2024 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz231 884279719003555 140737488355328 1 500000000000000 6358219 16777216 17 16777216 5622444110683064468545 2361183241434822606848 Ns336p2023 

noncomputable def Ns336p2025 := @Enclosure.Real.IsNear.subLit_ff_p qz235 qz1 174130379 16777216 17 16777216 10 1 0 1 6358219 6358219 16777216 17 

noncomputable def Ns336p2026 := @Ns336p2025 16777216 (@Enclosure.Real.IsNear.recentre' qz235 Bool.false 348260758 33554432 34 33554432 174130379 16777216 17 16777216 (Ns336p2013 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns336p2027 := @Enclosure.Real.IsNear.recentre' qz238 Bool.false 5622444110683064468545 2361183241434822606848 Ns336p2023 Ns336p457 9987467 4194304 215 33554432 (@Ns336p2024 Ns336p457 RS337to348.d47 (Ns336p2026 rfl rfl) rfl) 

noncomputable def Ns336p2028 := nat_lit 648758605796243679909985771882951790575716955780902762251925811788324294502565808636440545 

noncomputable def Ns336p2029 := nat_lit 92520944681446577772436949999381871243278610594529661632453803694275424202794219876321 

noncomputable def Ns336p2030 := nat_lit 1698979886032106343400235933202969976097245766437592281683829343763439563486582117691830241 

noncomputable def Ns336p2031 := BSN.sin_dyadic_bound_f 55690357691 68719476736 3 2 33554432 9689454 Ns336p2028 Ns336p1224 Ns336p2029 Ns336p2030 Ns336p1227 Ns336p2029 24312328 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 55690357691) qz366 0 2 Ns336p2028 Ns336p1224 Ns336p2029 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 55690357691) qz367 0 2 Ns336p2030 Ns336p1227 Ns336p2029 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2032 := @Ns336p2022 4840000 (Ns336p2027 rfl) (Enclosure.sfrac_false_div 9987467 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9987467) (@Nat.cast Real Real.instNatCast 4194304)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 489857566697319410171904) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 24312328 33554432 0 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q1 9987467 4194304 226375608064910080 72057594037927936 0 489857566697319410171904 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 24312328 33554432 489857566697319410171904 604462909807314587353088 55690357691 68719476736 9689454 9680000 (Ns336p2031 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p2033 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz236) 3039041 4194304 16783663 2537553920000 23154706 23155130 16777216 (@Enclosure.Real.IsNear.neg qz236 Bool.true 3039041 4194304 16783663 2537553920000 (Ns336p2021 (Ns336p2032 rfl rfl) rfl)) 

noncomputable def Ns336p2034 := Ns336p2019 (@Enclosure.Real.IsNear.neg qz756 Bool.false 11577459 8388608 53 4194304 (@Ns336p2020 53 4194304 (Ns336p2033 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p2035 := @Enclosure.Real.IsNear.recentre' qz237 Bool.true 4968834 16777216 

noncomputable abbrev qz239 := (@HMul.hMul Real Real Real qz349 qz346 qz569)

noncomputable def Ns336p2036 := @Enclosure.Real.IsNear.cos_image qz239 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 31398089)) qz368) Bool.true 31398089 16777216 

noncomputable def Ns336p2037 := nat_lit 74136641653888958869068848245 

noncomputable def Ns336p2038 := nat_lit 13530613305544270327856413368348897 

noncomputable def Ns336p2039 := @Enclosure.Real.IsNear.recentre' qz239 Bool.true Ns336p2037 Ns336p471 Ns336p2038 

noncomputable abbrev qz240 := qz569

noncomputable def Ns336p2040 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz240 884279719003555 140737488355328 1 500000000000000 83838450730759 

noncomputable abbrev qz570 := (@HSub.hSub Real Real Real qz631 qz755 qz748)

noncomputable abbrev qz241 := qz570

noncomputable def Ns336p2041 := @Enclosure.Real.IsNear.subLit_tf qz241 qz26 66246264686343 281474976710656 501392407 281474976710656 1 16 

noncomputable abbrev qz571 := qz755

noncomputable abbrev qz242 := qz571

noncomputable def Ns336p2042 := @Enclosure.Real.IsNear.subLit_ff_n qz242 qz231 40426948851961 281474976710656 216179735 281474976710656 6358219 16777216 17 16777216 

noncomputable def Ns336p2043 := @Enclosure.Real.IsNear.mulLit_ff qz231 qz231 6358219 16777216 17 16777216 6358219 16777216 17 16777216 40426948851961 281474976710656 

noncomputable def Ns336p2044 := nat_lit 122648028656655425502230852301223248732138780062982507710631333798129506374452741452862146796001 

noncomputable def Ns336p2045 := nat_lit 917991360507217233464737397907169431523954057562836957822771933606961405200596931287767521 

noncomputable def Ns336p2046 := nat_lit 740464379393481147420444148763216010042443825781971351518816928964122528159843590205504271735265 

noncomputable def Ns336p2047 := BSN.cos_dyadic_bound_t 31398089 16777216 4 3 16777216 4840000 Ns336p2044 Ns336p203 Ns336p2045 Ns336p2046 Ns336p206 Ns336p2045 4968834 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 31398089) (BSN.cosEvenQ 16777216) 0 3 Ns336p2044 Ns336p203 Ns336p2045 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 31398089) (BSN.cosOddQ 16777216) 0 3 Ns336p2046 Ns336p206 Ns336p2045 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2048 := @Ns336p2035 231674304 20300431360000 2484417 8388608 3619911 317194240000 (@Ns336p2036 47 4194304 Bool.true 4968834 16777216 1 4840000 (@Ns336p2039 Ns336p474 31398089 16777216 47 4194304 (@Ns336p2040 281474976710656 501392407 281474976710656 Ns336p2037 Ns336p471 Ns336p2038 Ns336p474 RS337to348.d47 (@Ns336p2041 0 1 1341415211692144 83838450730759 281474976710656 501392407 281474976710656 (@Ns336p2042 1111427891835948761088 66246264686343 281474976710656 501392407 281474976710656 (@Ns336p2043 216179735 281474976710656 (Ns336p2026 rfl rfl) (Ns336p2026 rfl rfl) rfl) (Ns336p2026 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 31398089 16777216) (BSN.cos_neg_of_bound 31398089 16777216 Bool.true 4968834 16777216 1 4840000 (Ns336p2047 rfl rfl)) rfl rfl) 

noncomputable def Ns336p2049 := @Ns336p2011 43304428239081698979 Ns336p211 (Ns336p2012 qz28 (@Enclosure.Real.IsNear.of_eq qz567 (@Inv.inv Real Real.instInv (Real.sqrt qz235)) Bool.false 10415319 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz230 (BSN.t_div_two_pi_nonneg qz229 676845 1000 qz232)) Ns336p2016) rfl) (@Ns336p2017 70368744177664 1296690219621 66520453480448000 (BSN.correction_mk qz231 (BSN.cos_two_pi_p_ne_zero_mk qz229 676845 1000 10 qz232 rfl rfl (@BSN.floor_sqrt_eq_dec qz229 676845 1000 10 qz232 rfl rfl rfl))) (@Ns336p2018 4194304 2484417 8388608 3619911 317194240000 28763235956403 70368744177664 1296690219621 66520453480448000 Ns336p2034 (Ns336p2048 rfl) rfl)) 

noncomputable def Ns336p2050 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz229) (hardyZApproximantRS₀ qz229) Bool.false 1666410313854854695851 2361183241434822606848 8870781470545668732579 Ns336p211 (@Eq.refl Real (hardyZApproximantRS₀ qz229)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz229) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz229) qz229 10) (@HMul.hMul Real Real Real qz5 qz563 (Zeta.RiemannSiegel.correction qz231))) Bool.false 1666410313854854695851 2361183241434822606848 8870781470545668732579 Ns336p211 (BSN.hardyZApproximantRS₀_eq qz229 10 (@BSN.floor_sqrt_eq_dec qz229 676845 1000 10 qz232 rfl rfl rfl)) (@Ns336p1935 1666410313854854695851 2361183241434822606848 8870781470545668732579 Ns336p211 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz229) qz229 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz229) qz229 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz229) qz229 10)) Bool.false 111753513 134217728 165879 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz229) qz229 10) (Ns336p2010 (Ns336p2009 rfl rfl rfl rfl) rfl rfl)) (Ns336p2049 rfl) rfl rfl)) 

theorem RS337to348.d73 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz229) Bool.false 1666410313854854695851 2361183241434822606848 8870781470545668732579 Ns336p211 := Ns336p2050 

noncomputable def Ns336p2051 := nat_lit 142851586106806767714304000 

noncomputable def Ns336p2052 := nat_lit 387999749998109815796666466304 

noncomputable abbrev qz873 := (Enclosure.sfrac Bool.false 677517 1000)

noncomputable abbrev qz757 := qz873

noncomputable abbrev qz572 := qz757

noncomputable abbrev qz243 := qz572

noncomputable abbrev qz874 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 677517 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz758 := qz874

noncomputable abbrev qz573 := qz758

noncomputable abbrev qz244 := qz573

noncomputable abbrev qz875 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 677517 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz759 := qz875

noncomputable abbrev qz574 := qz759

noncomputable abbrev qz245 := qz574

noncomputable abbrev qz575 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz630 qz244 qz8))

noncomputable def Ns336p2053 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz243) qz243 10) (@HMul.hMul Real Real Real qz5 qz575 (Zeta.RiemannSiegel.correction qz245)) 24148127 134217728 83021 67108864 1191550037714472276465 9444732965739290427392 820462303869174800571 Ns336p2051 Ns336p2052 

noncomputable def Ns336p2054 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.sin BSN.quadSignPos 9 10 677517 1000 199 268435456 134217728 4503599627370496 Bool.false 334585333254 2545 618095470 56 84886744 8 

noncomputable def Ns336p2055 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 677517 1000 103 154 268435456 134217728 4503599627370496 Bool.false 334585333254 2545 

noncomputable def Ns336p2056 := Ns336p2055 558195838 56 94906264 8 589812974 56 89478488 8 Bool.true 68426523 125400 Bool.true 171121208 Bool.true 87739498 14148475504056880 1 Bool.false 159764513 Bool.false Bool.false 254223609 Bool.true Bool.true 96682445 

noncomputable def Ns336p2057 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 677517 1000 20 45 268435456 134217728 4503599627370496 Bool.false 334585333254 2545 

noncomputable def Ns336p2058 := Ns336p2057 480971758 57 109588312 8 522351262 57 101459064 8 Bool.true 24590592 93017 Bool.false 285642123 Bool.true 341942450 14148475504056880 1 Bool.false 130269438 Bool.false Bool.false 256686045 Bool.true Bool.true 68426523 

noncomputable def Ns336p2059 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 677517 1000 195 99 268435456 134217728 4503599627370496 Bool.false 334585333254 2545 

noncomputable def Ns336p2060 := Ns336p2059 372130544 56 134217720 8 432030192 56 120047984 16 Bool.true 185652050 54640 Bool.false 237364962 Bool.false 133448262 14148475504056880 1 Bool.false 207619242 Bool.false Bool.false 128019015 Bool.false Bool.true 24590592 

noncomputable def Ns336p2061 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 677517 1000 494 319 268435456 134217728 4503599627370496 Bool.false 334585333254 2545 

noncomputable def Ns336p2062 := Ns336p2061 186065264 56 189812528 16 294906480 56 154981288 8 Bool.true 189928400 2608 Bool.false 224184220 Bool.false 272460026 14148475504056880 1 Bool.false 180137777 Bool.true Bool.false 228029664 Bool.false Bool.true 185652050 

noncomputable def Ns336p2063 := nat_lit 135734014694698691755866026337739606215616276054174816711 

noncomputable def Ns336p2064 := nat_lit 108898443858329766884451842063391519367134818861056000 

noncomputable def Ns336p2065 := nat_lit 68524018042024135442609379531360000 

noncomputable def Ns336p2066 := nat_lit 278557193588815125042420555294746598720 

noncomputable abbrev qz876 := (@Eq.refl Real (Enclosure.sfrac Bool.false 677517 1000))

noncomputable abbrev qz760 := qz876

noncomputable abbrev qz576 := qz760

noncomputable abbrev qz246 := qz576

noncomputable def Ns336p2067 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz243 677517 1000 1836118141156 16000000 1355034 4000 2000 Ns336p2065 Ns336p2066 qz246 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns336p2068 := nat_lit 390913962320732232256894155852690065900974875036023472127680 

noncomputable abbrev qz761 := (Real.log (Enclosure.sfrac Bool.false 1836118141156 16000000))

noncomputable abbrev qz762 := (@Nat.cast Real Real.instNatCast 1355034)

noncomputable abbrev qz763 := (Enclosure.sfrac Bool.false 677517 2000)

noncomputable abbrev qz247 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 677517 4000) qz761) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz762))))) qz763)

noncomputable abbrev qz577 := (@HSub.hSub Real Real Real qz11 qz247 (@HMul.hMul Real Real Real qz5 qz763 (Real.log Real.pi)))

noncomputable def Ns336p2069 := @Enclosure.Real.IsNear.addLit_ft_p qz577 (Enclosure.sfrac Bool.true Ns336p2065 Ns336p2066) 1403352878579596979119 1125899906842624000 4695473278615404513 495616000000000000000000 Ns336p2065 Ns336p2066 0 1 Ns336p2068 

noncomputable def Ns336p2070 := nat_lit 94177417472606686846507810816000 

noncomputable abbrev qz578 := (@HMul.hMul Real Real Real qz5 qz763 (Real.log Real.pi))

noncomputable def Ns336p2071 := @Enclosure.Real.IsNear.subLit_ff_p qz247 qz578 1839962200864857582511 1125899906842624000 535560484183353 121000000000000000000 26023943560437 67108864000 677517 134217728000 Ns336p2070 1403352878579596979119 1125899906842624000 

noncomputable abbrev qz248 := (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 677517 4000) qz761) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz762)))))

noncomputable def Ns336p2072 := @Enclosure.Real.IsNear.subLit_ff_p qz248 qz763 444274072891400924963 225179981368524800 535560484183353 121000000000000000000 677517 2000 0 1 735984880345943033004400 1839962200864857582511 1125899906842624000 535560484183353 121000000000000000000 

noncomputable def Ns336p2073 := nat_lit 1000416274562042892040397132948045824 

noncomputable def Ns336p2074 := nat_lit 56338725975809799885946880 

noncomputable def Ns336p2075 := nat_lit 5600875510382842056047894839017240963477271247714048926294590872791361598688168078892096030436007951181699950946731920866454902045243804406211678692466197193257598722704780191334400 

noncomputable def Ns336p2076 := nat_lit 145724329148385461783750397718213773199080477049191315684428088728574678589409068796945969849929646168260706457600976243566948016788048264420458012417179950082697149868820544880640 

noncomputable def Ns336p2077 := nat_lit 4770908361166988835343229024484057729841229951441172115537142682493951527978907797174805927318498430746418452239248465410289876142871655687551366348802647272455412866088960 

noncomputable def Ns336p2078 := BSN.log_dyadic_bound 787542141156 2884694141156 8 7 Ns336p2075 134217728 38720000 Ns336p2076 Ns336p2077 75191533 3672236282312 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 787542141156) (BSN.artanhQ 2884694141156) 0 7 Ns336p2076 Ns336p2075 Ns336p2077 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns336p2079 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 677517 4000) qz761 677517 4000 0 1 3279345457896695 281474976710656 195312621 7562500000000000 444362459319559021263 225179981368524800 132327621042057 30250000000000000000 (Enclosure.Real.IsNear.const Bool.false 677517 4000) (BSN.isNear_log_sfrac 1836118141156 16000000 3279345457896695 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1836118141156) qz362)) Bool.false Ns336p2074 Ns336p98 1000000619520000 38720000000000000000000 3279345457896695 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1836118141156 16000000 16 3672236282312 2097152000000 75191533 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns336p2078 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p2080 := BSN.arctan_dyadic_bound_f 1000 1355034 1 0 16777216 4840000 0 1 1 0 1 1 12381 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1355034) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1355034) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz764 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1355034)))

noncomputable def Ns336p2081 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz764 884279719003555 562949953421312 1 2000000000000000 12381 16777216 1 4840000 14828781966768637739008 883864281580963 562949953421312 50000000121 242000000000000000 qz16 (Ns336p2080 rfl) rfl rfl 

noncomputable def Ns336p2082 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 677517 4000) qz761) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz764)) 444362459319559021263 225179981368524800 132327621042057 30250000000000000000 883864281580963 2251799813685248 50000000121 968000000000000000 Ns336p2073 444274072891400924963 225179981368524800 535560484183353 121000000000000000000 (Ns336p2079 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz764) 1 4 0 1 883864281580963 562949953421312 50000000121 242000000000000000 883864281580963 2251799813685248 50000000121 968000000000000000 qz364 Ns336p2081 rfl) 

noncomputable def Ns336p2083 := @Ns336p2069 Ns336p2063 Ns336p2064 4695473278615404513 495616000000000000000000 (@Ns336p2071 4695473278615404513 495616000000000000000000 (Ns336p2072 (Ns336p2082 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 677517 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz763 (Real.log Real.pi) 677517 2000 0 1 38410761 33554432 1 67108864 26023943560437 67108864000 677517 134217728000 (Enclosure.Real.IsNear.const Bool.false 677517 2000) RS337to348.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns336p2065 Ns336p2066) 

noncomputable def Ns336p2084 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz243) Bool.false Ns336p2063 Ns336p2064 4695473278615404513 495616000000000000000000 653486979 524288 319 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz243) (@HAdd.hAdd Real Real Real qz365 qz577 (Enclosure.sfrac Bool.true Ns336p2065 Ns336p2066)) Bool.false Ns336p2063 Ns336p2064 4695473278615404513 495616000000000000000000 Ns336p2067 (Ns336p2083 rfl rfl)) 

noncomputable def Ns336p2085 := nat_lit 574096636438028585045640766798570034715080824610997635647258700621360470687744000000000000 

noncomputable def Ns336p2086 := nat_lit 72453280434329910569372177240727144521234810007069719531520256000000000000000000000000 

noncomputable def Ns336p2087 := nat_lit 1503469123455085950502423024756912723162653493812601409054055087879563137515520000000000000 

noncomputable def Ns336p2088 := BSN.sin_dyadic_bound_f 54014114000 68719476736 3 2 33554432 9689454 Ns336p2085 Ns336p1224 Ns336p2086 Ns336p2087 Ns336p1227 Ns336p2086 23741050 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 54014114000) qz366 0 2 Ns336p2085 Ns336p1224 Ns336p2086 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 54014114000) qz367 0 2 Ns336p2087 Ns336p1227 Ns336p2086 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2089 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz243) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 653486979) (@Nat.cast Real Real.instNatCast 524288)) Bool.false 653486979 524288 319 33554432 Bool.true 23741050 33554432 1 4840000 (Ns336p2084 rfl) (Enclosure.sfrac_false_div 653486979 524288) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 653486979) (@Nat.cast Real Real.instNatCast 524288)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 59389146407364846419968) (@Nat.cast Real Real.instNatCast 75557863725914323419136)) 226375608064910080 72057594037927936 Bool.false 23741050 33554432 198 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q1 653486979 524288 226375608064910080 72057594037927936 198 59389146407364846419968 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 23741050 33554432 59389146407364846419968 75557863725914323419136 54014114000 68719476736 9689454 9680000 (Ns336p2088 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p2090 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz243) Bool.false Ns336p2063 Ns336p2064 4695473278615404513 495616000000000000000000 334585333254 268435456 2545 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz243) (@HAdd.hAdd Real Real Real qz365 qz577 (Enclosure.sfrac Bool.true Ns336p2065 Ns336p2066)) Bool.false Ns336p2063 Ns336p2064 4695473278615404513 495616000000000000000000 Ns336p2067 (Ns336p2083 rfl rfl)) 

noncomputable def Ns336p2091 := Ns336p2062 54640 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 494 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 180137777 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 319 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 228029664 268435456) qz246 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 1) Bool.true 11870525 16777216 24648663 2537553920000 189928400 268435456 2608 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz243)) Bool.true 11870525 16777216 24648663 2537553920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz243) qz243) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz243)) Bool.true 23741050 33554432 1577514432 162403450880000 11870525 16777216 24648663 2537553920000 (Ns336p2089 rfl rfl) rfl)) rfl) (Ns336p2090 rfl) RS337to348.d7 

noncomputable def Ns336p2092 := nat_lit 22040157608799134436879898749441447499858918591594392901903757516800000 

noncomputable def Ns336p2093 := nat_lit 6380288544257440616488727613800277508794076545136764530713600000000 

noncomputable def Ns336p2094 := nat_lit 66107712249308888429406718793096741944559167621692905176649845350400000 

noncomputable def Ns336p2095 := BSN.cos_dyadic_bound_f 224184220 268435456 3 2 268435456 134217728 Ns336p2092 Ns336p251 Ns336p2093 Ns336p2094 Ns336p254 Ns336p2093 180137777 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 224184220) qz369 0 2 Ns336p2092 Ns336p251 Ns336p2093 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 224184220) qz370 0 2 Ns336p2094 Ns336p254 Ns336p2093 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2096 := nat_lit 86557533730222651129319181345853895864702774001687744256211501865345280 

noncomputable def Ns336p2097 := nat_lit 30368430675888100771836856475306173226488501947621317748578050744576 

noncomputable def Ns336p2098 := nat_lit 226649134691393600794586310519133517269950093382219371870865759469936896 

noncomputable def Ns336p2099 := BSN.sin_dyadic_bound_f 272460026 268435456 3 2 268435456 134217728 Ns336p2096 Ns336p127 Ns336p2097 Ns336p2098 Ns336p130 Ns336p2097 228029664 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 272460026) qz371 0 2 Ns336p2096 Ns336p127 Ns336p2097 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 272460026) qz372 0 2 Ns336p2098 Ns336p130 Ns336p2097 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2100 := nat_lit 49853487390715339010488315964744658156957302710814962210866503236419840 

noncomputable def Ns336p2101 := nat_lit 10077038016132578964889792306848793334327472666149479539007391498496 

noncomputable def Ns336p2102 := nat_lit 130552342247466435137716720243929682840918310239246373299682448890102016 

noncomputable def Ns336p2103 := BSN.sin_dyadic_bound_f 237364962 268435456 3 2 268435456 134217728 Ns336p2100 Ns336p127 Ns336p2101 Ns336p2102 Ns336p130 Ns336p2101 207619242 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 237364962) qz371 0 2 Ns336p2100 Ns336p127 Ns336p2101 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 237364962) qz372 0 2 Ns336p2102 Ns336p130 Ns336p2101 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2104 := nat_lit 4979683734127984186201667508929984742464434293398400864990196287709440 

noncomputable def Ns336p2105 := nat_lit 100578088156972612176519953799903263561578893775571993073233469696 

noncomputable def Ns336p2106 := nat_lit 13041865986763894912965605300605712577361085354977318006033157423145216 

noncomputable def Ns336p2107 := BSN.sin_dyadic_bound_f 133448262 268435456 3 2 268435456 134217728 Ns336p2104 Ns336p127 Ns336p2105 Ns336p2106 Ns336p130 Ns336p2105 128019015 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 133448262) qz371 0 2 Ns336p2104 Ns336p127 Ns336p2105 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 133448262) qz372 0 2 Ns336p2106 Ns336p130 Ns336p2105 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2108 := Ns336p2060 93017 BSN.abs_quadSignPos (BSN.cos_quad_nat3 195 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 207619242 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 128019015 268435456) qz246 rfl rfl (Ns336p2091 RS337to348.d9 RS337to348.d11 RS337to348.d13 RS337to348.d17 (Ns336p2095 rfl rfl) (Ns336p2099 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns336p2090 rfl) RS337to348.d19 RS337to348.d21 RS337to348.d23 RS337to348.d25 RS337to348.d17 (Ns336p2103 rfl rfl) (Ns336p2107 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns336p2109 := nat_lit 3584801471338004570743761747497093287145041940548448015871878993949012375521952482401042122273322993539194001 

noncomputable def Ns336p2110 := nat_lit 295030575930078249994294071859381170770125037450906648076100232599925105540365980779937718070992280721 

noncomputable def Ns336p2111 := nat_lit 21736737720747965146868680705057109912606490419062370702907646522281716935296431846327459217058202041018588305 

noncomputable def Ns336p2112 := BSN.cos_dyadic_bound_f 285642123 268435456 4 3 268435456 134217728 Ns336p2109 Ns336p121 Ns336p2110 Ns336p2111 Ns336p124 Ns336p2110 130269438 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 285642123) qz369 0 3 Ns336p2109 Ns336p121 Ns336p2110 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 285642123) qz370 0 3 Ns336p2111 Ns336p124 Ns336p2110 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2113 := nat_lit 19142921169737147618565183481829087322593232038502513933759363022043688119453691752958772258762081384000000000 

noncomputable def Ns336p2114 := nat_lit 2555266661663154745106305449820941137975688494697527525976208803948168512568229687744140625000000000000 

noncomputable def Ns336p2115 := nat_lit 95663121714842423471946790012549828346761674551449429845273242356886571825607039325719668550847906920000000000 

noncomputable def Ns336p2116 := BSN.sin_dyadic_bound_f 341942450 268435456 4 3 268435456 134217728 Ns336p2113 Ns336p158 Ns336p2114 Ns336p2115 Ns336p161 Ns336p2114 256686045 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 341942450) qz371 0 3 Ns336p2113 Ns336p158 Ns336p2114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 341942450) qz372 0 3 Ns336p2115 Ns336p161 Ns336p2114 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2117 := Ns336p2058 125400 BSN.abs_quadSignPos (BSN.cos_quad_nat0 20 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 130269438 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 45 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 256686045 268435456) qz246 rfl rfl (Ns336p2108 rfl rfl) (Ns336p2090 rfl) RS337to348.d27 RS337to348.d29 RS337to348.d31 RS337to348.d33 RS337to348.d17 (Ns336p2112 rfl rfl) (Ns336p2116 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p2118 := nat_lit 13464194201129517594700745684211412810632061796703446182158131003392000 

noncomputable def Ns336p2119 := nat_lit 735242662710248893655482252004366622859303999599862704262837436416 

noncomputable def Ns336p2120 := nat_lit 35262175371980539011721748868336169339027913451557292604131060414939136 

noncomputable def Ns336p2121 := BSN.sin_dyadic_bound_f 171121208 268435456 3 2 268435456 134217728 Ns336p2118 Ns336p127 Ns336p2119 Ns336p2120 Ns336p130 Ns336p2119 159764513 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 171121208) qz371 0 2 Ns336p2118 Ns336p127 Ns336p2119 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 171121208) qz372 0 2 Ns336p2120 Ns336p130 Ns336p2119 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2122 := nat_lit 516954508949640066891202298575950148852715831092663022821325589012736 

noncomputable def Ns336p2123 := nat_lit 3512053816516738984069063376070047063769910005403178363722752256 

noncomputable def Ns336p2124 := nat_lit 1550856502741287167195638757601098306464019953457978262107249321533696 

noncomputable def Ns336p2125 := BSN.cos_dyadic_bound_f 87739498 268435456 3 2 268435456 134217728 Ns336p2122 Ns336p251 Ns336p2123 Ns336p2124 Ns336p254 Ns336p2123 254223609 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 87739498) qz369 0 2 Ns336p2122 Ns336p251 Ns336p2123 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 87739498) qz370 0 2 Ns336p2124 Ns336p254 Ns336p2123 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2126 := Ns336p2056 153229 BSN.abs_quadSignPos (BSN.cos_quad_nat3 103 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 159764513 268435456) BSN.abs_quadSignNeg qz678 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 254223609 268435456) qz246 rfl rfl (Ns336p2117 rfl) (Ns336p2090 rfl) RS337to348.d35 RS337to348.d37 RS337to348.d39 RS337to348.d41 RS337to348.d17 (Ns336p2121 rfl rfl) (Ns336p2125 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p2127 := nat_lit 89867214060876400385520174478951474930629714160593170981224025784647680 

noncomputable def Ns336p2128 := nat_lit 32734334161269117803065282886154659391483513869883741118683508965376 

noncomputable def Ns336p2129 := nat_lit 235313514570796136723728827463057231560253516160049921750918389469085696 

noncomputable def Ns336p2130 := BSN.sin_dyadic_bound_f 275027068 268435456 3 2 268435456 134217728 Ns336p2127 Ns336p127 Ns336p2128 Ns336p2129 Ns336p130 Ns336p2128 229373655 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 275027068) qz371 0 2 Ns336p2127 Ns336p127 Ns336p2128 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 275027068) qz372 0 2 Ns336p2129 Ns336p130 Ns336p2128 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2131 := Ns336p2054 Bool.true 96682445 153229 Bool.true 275027068 14148475504056880 1 Bool.false 229373655 Bool.false Bool.true 24148127 166042 BSN.abs_quadSignPos qz373 (BSN.sfrac_eq_quadSignPos_mul Bool.false 229373655 268435456) qz246 rfl (Ns336p2126 rfl) (Ns336p2090 rfl) RS337to348.d43 RS337to348.d45 RS337to348.d17 (Ns336p2130 rfl rfl) rfl 

noncomputable def Ns336p2132 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 10) 24148127 268435456 166042 268435456 24148127 268435456 166042 268435456 12964426965581824 24148127 134217728 83021 67108864 (Ns336p2131 rfl rfl rfl rfl) 

noncomputable def Ns336p2133 := @Enclosure.Real.IsNear.mulLit_ff qz575 (Zeta.RiemannSiegel.correction qz245) 10412735 33554432 1 33554432 114431994832719 281474976710656 78627895679611 4257309022748672000 1191550037714472276465 9444732965739290427392 

noncomputable abbrev qz579 := (@HPow.hPow Real Real Real qz630 qz244 qz8)

noncomputable def Ns336p2134 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz579 1 1 0 1 10412735 33554432 1 33554432 10412735 33554432 1 33554432 

noncomputable def Ns336p2135 := @Enclosure.Real.IsNear.sqrt_image qz244 3618179943501 33554432000 677517 33554432000 174216783 174216816 16777216 (@Enclosure.Real.IsNear.of_eq qz244 (@HMul.hMul Real Real Real qz5 qz243 qz3) Bool.false 3618179943501 33554432000 677517 33554432000 (BSN.t_div_two_pi_mk qz243 677517 1000 qz246) (@Enclosure.Real.IsNear.mulLit_ff qz243 qz3 677517 1000 0 1 5340353 33554432 1 33554432 3618179943501 33554432000 677517 33554432000 (Enclosure.Real.IsNear.const Bool.false 677517 1000) RS337to348.d48 rfl)) 

noncomputable abbrev qz877 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 677517 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz765 := qz877

noncomputable abbrev qz580 := qz765

noncomputable abbrev qz249 := qz580

noncomputable def Ns336p2136 := @Enclosure.Real.IsNear.sqrt_image qz249 348433599 33554432 33 33554432 54063597 54063603 16777216 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 348433599 33554432 33 33554432 348433599 33554432 33 33554432 (Ns336p2135 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns336p2137 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz249) 3378975 1048576 3 16777216 5206367 5206368 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz249) Bool.false 108127200 33554432 6 33554432 3378975 1048576 3 16777216 (Ns336p2136 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns336p2138 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 10412735 33554432 1 33554432 10412735 33554432 1 33554432 (Ns336p2137 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz574))

noncomputable abbrev qz766 := (@HMul.hMul Real Real Real qz824 qz875 qz875)

noncomputable abbrev qz581 := (@HSub.hSub Real Real Real qz631 (@HSub.hSub Real Real Real qz631 qz766 qz759) qz639)

noncomputable abbrev qz251 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz581))

noncomputable def Ns336p2139 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz245) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz250) qz251) Bool.false 114431994832719 

noncomputable def Ns336p2140 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz250) qz251 44949803 33554432 387 

noncomputable abbrev qz767 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz250))

noncomputable def Ns336p2141 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz250) (@Neg.neg Real Real.instNeg qz767) Bool.true 44949803 33554432 387 33554432 (BSN.inv_eq_neg_inv_neg qz250) 

noncomputable def Ns336p2142 := @Enclosure.Real.IsNear.recentre' qz767 Bool.false 44949803 33554432 387 33554432 44949803 33554432 

noncomputable def Ns336p2143 := @Enclosure.Real.IsNear.recentre' qz250 Bool.true 25047939 33554432 65017152 10150215680000 25047939 33554432 1015893 158597120000 

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz349 qz346 qz574)

noncomputable def Ns336p2144 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 632701) (@Nat.cast Real Real.instNatCast 262144)) Bool.false 632701 262144 13 2097152 Bool.true 25047939 33554432 1 

noncomputable def Ns336p2145 := nat_lit 890540488609171563568615079 

noncomputable def Ns336p2146 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz245 884279719003555 140737488355328 1 500000000000000 12889279 33554432 33 33554432 11397728012278422386845 4722366482869645213696 Ns336p2145 

noncomputable def Ns336p2147 := @Enclosure.Real.IsNear.subLit_ff_p qz249 qz1 348433599 33554432 33 33554432 10 1 0 1 12889279 12889279 33554432 33 

noncomputable def Ns336p2148 := @Ns336p2147 33554432 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 348433599 33554432 33 33554432 348433599 33554432 33 33554432 (Ns336p2135 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns336p2149 := @Enclosure.Real.IsNear.recentre' qz252 Bool.false 11397728012278422386845 4722366482869645213696 Ns336p2145 Ns336p304 632701 262144 13 2097152 (@Ns336p2146 Ns336p304 RS337to348.d47 (Ns336p2148 rfl rfl) rfl) 

noncomputable def Ns336p2150 := nat_lit 758790578062278953805535458572569049553106423108719064603822644396258107556878514965589985 

noncomputable def Ns336p2151 := nat_lit 126560053196260021547848807913370982314489219377006397024186266200809619711969843884001 

noncomputable def Ns336p2152 := nat_lit 1987103750076984267551039207715344910096293363691463349319591576606827066121814826115018721 

noncomputable def Ns336p2153 := BSN.sin_dyadic_bound_f 57914469307 68719476736 3 2 33554432 9689454 Ns336p2150 Ns336p1224 Ns336p2151 Ns336p2152 Ns336p1227 Ns336p2151 25047939 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 57914469307) qz366 0 2 Ns336p2150 Ns336p1224 Ns336p2151 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 57914469307) qz367 0 2 Ns336p2152 Ns336p1227 Ns336p2151 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2154 := @Ns336p2144 4840000 (Ns336p2149 rfl) (Enclosure.sfrac_false_div 632701 262144) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 632701) (@Nat.cast Real Real.instNatCast 262144)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 31838816210214298058752) (@Nat.cast Real Real.instNatCast 37778931862957161709568)) 226375608064910080 72057594037927936 Bool.false 25047939 33554432 0 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q1 632701 262144 226375608064910080 72057594037927936 0 31838816210214298058752 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 25047939 33554432 31838816210214298058752 37778931862957161709568 57914469307 68719476736 9689454 9680000 (Ns336p2153 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p2155 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz250) 25047939 33554432 1015893 158597120000 22474708 22475095 16777216 (@Enclosure.Real.IsNear.neg qz250 Bool.true 25047939 33554432 1015893 158597120000 (Ns336p2143 (Ns336p2154 rfl rfl) rfl)) 

noncomputable def Ns336p2156 := Ns336p2141 (@Enclosure.Real.IsNear.neg qz767 Bool.false 44949803 33554432 387 33554432 (@Ns336p2142 387 33554432 (Ns336p2155 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p2157 := @Enclosure.Real.IsNear.recentre' qz251 Bool.true 5091546 16777216 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz349 qz346 qz581)

noncomputable def Ns336p2158 := @Enclosure.Real.IsNear.cos_image qz253 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 31526719)) qz368) Bool.true 31526719 16777216 

noncomputable def Ns336p2159 := nat_lit 297761446554177246104744707805 

noncomputable def Ns336p2160 := nat_lit 10567691857880489122808519568934949 

noncomputable def Ns336p2161 := @Enclosure.Real.IsNear.recentre' qz253 Bool.true Ns336p2159 Ns336p194 Ns336p2160 

noncomputable abbrev qz254 := qz581

noncomputable def Ns336p2162 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz254 884279719003555 140737488355328 1 500000000000000 336727666772351 

noncomputable abbrev qz582 := (@HSub.hSub Real Real Real qz631 qz766 qz759)

noncomputable abbrev qz255 := qz582

noncomputable def Ns336p2163 := @Enclosure.Real.IsNear.subLit_tf qz255 qz26 266358922594687 1125899906842624 1957989759 1125899906842624 1 16 

noncomputable abbrev qz583 := qz766

noncomputable abbrev qz256 := qz583

noncomputable def Ns336p2164 := @Enclosure.Real.IsNear.subLit_ff_n qz256 qz245 166133513139841 1125899906842624 850693503 1125899906842624 12889279 33554432 33 33554432 

noncomputable def Ns336p2165 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz245 12889279 33554432 33 33554432 12889279 33554432 33 33554432 166133513139841 1125899906842624 

noncomputable def Ns336p2166 := nat_lit 124685175613161927090415457771845779666065050340877290694478079016320859013708602608102772599041 

noncomputable def Ns336p2167 := nat_lit 964151564935651072760713845115921201083377590278437299404071764780713935762792663553173761 

noncomputable def Ns336p2168 := nat_lit 752703288812435611141165259611868895969165012806010580511796811906936464461408130582268714969345 

noncomputable def Ns336p2169 := BSN.cos_dyadic_bound_t 31526719 16777216 4 3 16777216 4840000 Ns336p2166 Ns336p203 Ns336p2167 Ns336p2168 Ns336p206 Ns336p2167 5091546 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 31526719) (BSN.cosEvenQ 16777216) 0 3 Ns336p2166 Ns336p203 Ns336p2167 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 31526719) (BSN.cosOddQ 16777216) 0 3 Ns336p2168 Ns336p206 Ns336p2167 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2170 := @Ns336p2157 113417152 10150215680000 2545773 8388608 1772143 158597120000 (@Ns336p2158 23 2097152 Bool.true 5091546 16777216 1 4840000 (@Ns336p2161 Ns336p322 31526719 16777216 23 2097152 (@Ns336p2162 1125899906842624 1957989759 1125899906842624 Ns336p2159 Ns336p194 Ns336p2160 Ns336p322 RS337to348.d47 (@Ns336p2163 0 1 5387642668357616 336727666772351 1125899906842624 1957989759 1125899906842624 (@Ns336p2164 8937522355796688502784 266358922594687 1125899906842624 1957989759 1125899906842624 (@Ns336p2165 850693503 1125899906842624 (Ns336p2148 rfl rfl) (Ns336p2148 rfl rfl) rfl) (Ns336p2148 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 31526719 16777216) (BSN.cos_neg_of_bound 31526719 16777216 Bool.true 5091546 16777216 1 4840000 (Ns336p2169 rfl rfl)) rfl rfl) 

noncomputable def Ns336p2171 := @Ns336p2133 820462303869174800571 Ns336p2051 (Ns336p2134 qz28 (@Enclosure.Real.IsNear.of_eq qz579 (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 10412735 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz244 (BSN.t_div_two_pi_nonneg qz243 677517 1000 qz246)) Ns336p2138) rfl) (@Ns336p2139 281474976710656 78627895679611 4257309022748672000 (BSN.correction_mk qz245 (BSN.cos_two_pi_p_ne_zero_mk qz243 677517 1000 10 qz246 rfl rfl (@BSN.floor_sqrt_eq_dec qz243 677517 1000 10 qz246 rfl rfl rfl))) (@Ns336p2140 33554432 2545773 8388608 1772143 158597120000 114431994832719 281474976710656 78627895679611 4257309022748672000 Ns336p2156 (Ns336p2170 rfl) rfl)) 

noncomputable def Ns336p2172 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz243) (hardyZApproximantRS₀ qz243) Bool.true 2890823408947213111793 9444732965739290427392 177543488492677923856571 Ns336p2051 (@Eq.refl Real (hardyZApproximantRS₀ qz243)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz243) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz243) qz243 10) (@HMul.hMul Real Real Real qz5 qz575 (Zeta.RiemannSiegel.correction qz245))) Bool.true 2890823408947213111793 9444732965739290427392 177543488492677923856571 Ns336p2051 (BSN.hardyZApproximantRS₀_eq qz243 10 (@BSN.floor_sqrt_eq_dec qz243 677517 1000 10 qz246 rfl rfl rfl)) (@Ns336p2053 2890823408947213111793 9444732965739290427392 177543488492677923856571 Ns336p2051 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz243) qz243 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 10)) Bool.true 24148127 134217728 83021 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz243) qz243 10) (Ns336p2132 (Ns336p2131 rfl rfl rfl rfl) rfl rfl)) (Ns336p2171 rfl) rfl rfl)) 

theorem RS337to348.d74 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz243) Bool.true 2890823408947213111793 9444732965739290427392 177543488492677923856571 Ns336p2051 := Ns336p2172 

noncomputable def Ns336p2173 := nat_lit 357128965267016919285760000 

noncomputable def Ns336p2174 := nat_lit 127029123164377901688458051584 

noncomputable abbrev qz878 := (Enclosure.sfrac Bool.false 678523 1000)

noncomputable abbrev qz768 := qz878

noncomputable abbrev qz584 := qz768

noncomputable abbrev qz257 := qz584

noncomputable abbrev qz879 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 678523 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz769 := qz879

noncomputable abbrev qz585 := qz769

noncomputable abbrev qz258 := qz585

noncomputable abbrev qz880 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 678523 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz770 := qz880

noncomputable abbrev qz586 := qz770

noncomputable abbrev qz259 := qz586

noncomputable abbrev qz587 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz630 qz258 qz8))

noncomputable def Ns336p2175 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz257) qz257 10) (@HMul.hMul Real Real Real qz5 qz587 (Zeta.RiemannSiegel.correction qz259)) 27949285 8388608 83143 67108864 590997164224795131447 4722366482869645213696 2039747810300065431591 Ns336p2173 Ns336p2174 

noncomputable def Ns336p2176 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz257) qz257 Real.sin BSN.quadSignPos 9 10 678523 1000 199 268435456 134217728 4503599627370496 Bool.false 335217416815 2547 618095470 56 84886744 8 

noncomputable def Ns336p2177 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz257) qz257 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 678523 1000 103 154 268435456 134217728 4503599627370496 Bool.false 335217416815 2547 

noncomputable def Ns336p2178 := Ns336p2177 558195838 56 94906264 8 589812974 56 89478488 8 Bool.false 429652047 125585 Bool.true 100582660 Bool.true 49007789 14148475504056880 1 Bool.false 98245496 Bool.false Bool.false 263974235 Bool.true Bool.false 376395660 

noncomputable def Ns336p2179 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz257) qz257 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 678523 1000 21 45 268435456 134217728 4503599627370496 Bool.false 335217416815 2547 

noncomputable def Ns336p2180 := Ns336p2179 480971758 57 109588312 8 522351262 57 101459064 8 Bool.false 512621671 93155 Bool.false 12210667 Bool.true 235344259 14148475504056880 1 Bool.false 12206455 Bool.true Bool.false 206332515 Bool.true Bool.false 429652047 

noncomputable def Ns336p2181 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz257) qz257 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 678523 1000 196 99 268435456 134217728 4503599627370496 Bool.false 335217416815 2547 

noncomputable def Ns336p2182 := Ns336p2181 372130544 56 134217720 8 432030192 56 120047984 16 Bool.false 270140925 54723 Bool.false 73427768 Bool.false 330909450 14148475504056880 1 Bool.false 258455212 Bool.false Bool.false 253241742 Bool.false Bool.false 512621671 

noncomputable def Ns336p2183 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz257) qz257 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 678523 1000 495 320 268435456 134217728 4503599627370496 Bool.false 335217416815 2547 

noncomputable def Ns336p2184 := Ns336p2183 186065264 56 189812528 16 294906480 56 154981288 8 Bool.true 238656 2616 Bool.false 247428698 Bool.false 186210240 14148475504056880 1 Bool.false 213850930 Bool.false Bool.false 206398340 Bool.false Bool.false 270140925 

noncomputable def Ns336p2185 := nat_lit 1234858337002004207182785839298530215249201171526846914513 

noncomputable def Ns336p2186 := nat_lit 988850054206644685858144448724544295681121922842624000 

noncomputable def Ns336p2187 := nat_lit 69034264593690484682542541844640000 

noncomputable def Ns336p2188 := nat_lit 281048089109005072105601484714880000320 

noncomputable abbrev qz881 := (@Eq.refl Real (Enclosure.sfrac Bool.false 678523 1000))

noncomputable abbrev qz771 := qz881

noncomputable abbrev qz588 := qz771

noncomputable abbrev qz260 := qz588

noncomputable def Ns336p2189 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz257 678523 1000 1841574846116 16000000 1357046 4000 2000 Ns336p2187 Ns336p2188 qz260 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns336p2190 := nat_lit 395154667840641346298491468575529668879744374888591012644160 

noncomputable abbrev qz772 := (Real.log (Enclosure.sfrac Bool.false 1841574846116 16000000))

noncomputable abbrev qz773 := (@Nat.cast Real Real.instNatCast 1357046)

noncomputable abbrev qz774 := (Enclosure.sfrac Bool.false 678523 2000)

noncomputable abbrev qz261 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 678523 4000) qz772) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz773))))) qz774)

noncomputable abbrev qz589 := (@HSub.hSub Real Real Real qz11 qz261 (@HMul.hMul Real Real Real qz5 qz774 (Real.log Real.pi)))

noncomputable def Ns336p2191 := @Enclosure.Real.IsNear.addLit_ft_p qz589 (Enclosure.sfrac Bool.true Ns336p2187 Ns336p2188) 1406004028773352914513 1125899906842624000 4702407263324607047 495616000000000000000000 Ns336p2187 Ns336p2188 0 1 Ns336p2190 

noncomputable def Ns336p2192 := nat_lit 94355333150403027564056543232000 

noncomputable abbrev qz590 := (@HMul.hMul Real Real Real qz5 qz774 (Real.log Real.pi))

noncomputable def Ns336p2193 := @Enclosure.Real.IsNear.subLit_ff_p qz261 qz590 1843261643246439022161 1125899906842624000 536346422170257 121000000000000000000 26062584786003 67108864000 678523 134217728000 Ns336p2192 1406004028773352914513 1125899906842624000 

noncomputable def Ns336p2194 := nat_lit 3686523286492878044322000 

noncomputable abbrev qz262 := (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 678523 4000) qz772) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz773)))))

noncomputable def Ns336p2195 := @Enclosure.Real.IsNear.subLit_ff_p qz262 qz774 2225236134491727904337 1125899906842624000 536346422170257 121000000000000000000 678523 2000 0 1 Ns336p2194 1843261643246439022161 1125899906842624000 536346422170257 121000000000000000000 

noncomputable def Ns336p2196 := nat_lit 5010786313054154355721126051972120576 

noncomputable def Ns336p2197 := nat_lit 56353075777288091987869696 

noncomputable def Ns336p2198 := nat_lit 5751038205726252154213896448567017707656698644053899482901726311190965399985297783953664511914351733319163299100060453338593037476529878065185046645541289417258866123360226928230400 

noncomputable def Ns336p2199 := nat_lit 151212340335603086216509169500590860905454987112748435314126345049388472774220659240574105878590357226779611129623147394365257944652872322491742913375108336671313302605592254218240 

noncomputable def Ns336p2200 := nat_lit 5255131903981900465194649316587194117050436054461046600602862064423144740597857946712580932447081173516233402341171464538885020180210360341165429187519338469580606915215360 

noncomputable def Ns336p2201 := BSN.log_dyadic_bound 792998846116 2890150846116 8 7 Ns336p2198 134217728 38720000 Ns336p2199 Ns336p2200 75589820 3683149692232 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 792998846116) (BSN.artanhQ 2890150846116) 0 7 Ns336p2199 Ns336p2198 Ns336p2200 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns336p2202 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 678523 4000) qz772 678523 4000 0 1 3280180726275319 281474976710656 195312621 7562500000000000 2225678066934508273837 1125899906842624000 132524105538783 30250000000000000000 (Enclosure.Real.IsNear.const Bool.false 678523 4000) (BSN.isNear_log_sfrac 1841574846116 16000000 3280180726275319 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1841574846116) qz362)) Bool.false Ns336p2197 Ns336p98 1000000619520000 38720000000000000000000 3280180726275319 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1841574846116 16000000 16 3683149692232 2097152000000 75589820 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns336p2201 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p2203 := BSN.arctan_dyadic_bound_f 1000 1357046 1 0 16777216 4840000 0 1 1 0 1 1 12363 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1357046) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1357046) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz775 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1357046)))

noncomputable def Ns336p2204 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz775 884279719003555 562949953421312 1 2000000000000000 12363 16777216 1 4840000 14828792099867799322624 883864885560739 562949953421312 50000000121 242000000000000000 qz16 (Ns336p2203 rfl) rfl rfl 

noncomputable def Ns336p2205 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 678523 4000) qz772) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz775)) 2225678066934508273837 1125899906842624000 132524105538783 30250000000000000000 883864885560739 2251799813685248 50000000121 968000000000000000 Ns336p2196 2225236134491727904337 1125899906842624000 536346422170257 121000000000000000000 (Ns336p2202 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz775) 1 4 0 1 883864885560739 562949953421312 50000000121 242000000000000000 883864885560739 2251799813685248 50000000121 968000000000000000 qz364 Ns336p2204 rfl) 

noncomputable def Ns336p2206 := @Ns336p2191 Ns336p2185 Ns336p2186 4702407263324607047 495616000000000000000000 (@Ns336p2193 4702407263324607047 495616000000000000000000 (Ns336p2195 (Ns336p2205 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 678523 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz774 (Real.log Real.pi) 678523 2000 0 1 38410761 33554432 1 67108864 26062584786003 67108864000 678523 134217728000 (Enclosure.Real.IsNear.const Bool.false 678523 2000) RS337to348.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns336p2187 Ns336p2188) 

noncomputable def Ns336p2207 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz257) Bool.false Ns336p2185 Ns336p2186 4702407263324607047 495616000000000000000000 41902177101 33554432 5 524288 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz257) (@HAdd.hAdd Real Real Real qz365 qz589 (Enclosure.sfrac Bool.true Ns336p2187 Ns336p2188)) Bool.false Ns336p2185 Ns336p2186 4702407263324607047 495616000000000000000000 Ns336p2189 (Ns336p2206 rfl rfl)) 

noncomputable def Ns336p2208 := nat_lit 7591605563930739507986432 

noncomputable def Ns336p2209 := nat_lit 1349422785477274825709377676783818934913386785660223610502310009883922292246500997592107869224804826860067147369699923945743470040665030656 

noncomputable def Ns336p2210 := nat_lit 5312452879021523644167342878668926891519915429617346963252719967526930359331948649748578417931730498127901383505799396607174191825394073600 

noncomputable def Ns336p2211 := nat_lit 2485684582201254858815169261161178264818529515519783632825198958565533311861831059486279107479475155767213357852420983610726653362176 

noncomputable def Ns336p2212 := nat_lit 8166823742896745129192307885917045278728525017697321420619775219818737725176418432362132145477437528204468436978726971472257121715455262720 

noncomputable def Ns336p2213 := nat_lit 483433211990958651619228201958872347128312304095178573655997517044950662699207327127120636031787475329639025899027745091252851456110860697600 

noncomputable def Ns336p2214 := BSN.cos_dyadic_bound_f 107883203724 68719476736 4 3 33554432 9689454 Ns336p2209 Ns336p2210 Ns336p2211 Ns336p2212 Ns336p2213 Ns336p2211 29832 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 107883203724) (BSN.cosEvenQ 68719476736) 0 3 Ns336p2209 Ns336p2210 Ns336p2211 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 107883203724) (BSN.cosOddQ 68719476736) 0 3 Ns336p2212 Ns336p2213 Ns336p2211 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2215 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz257) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 41902177101) qz396) Bool.false 41902177101 33554432 5 524288 Bool.true 29832 33554432 1 4840000 (Ns336p2207 rfl) (Enclosure.sfrac_false_div 41902177101 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 41902177101) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns336p2208) qz413) 226375608064910080 72057594037927936 Bool.false 29832 33554432 198 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q2 41902177101 33554432 226375608064910080 72057594037927936 198 Ns336p2208 Ns336p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 29832 33554432 Ns336p2208 Ns336p98 107883203724 68719476736 9689454 9680000 (Ns336p2214 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p2216 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz257) Bool.false Ns336p2185 Ns336p2186 4702407263324607047 495616000000000000000000 335217416815 268435456 2547 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz257) (@HAdd.hAdd Real Real Real qz365 qz589 (Enclosure.sfrac Bool.true Ns336p2187 Ns336p2188)) Bool.false Ns336p2185 Ns336p2186 4702407263324607047 495616000000000000000000 Ns336p2189 (Ns336p2206 rfl rfl)) 

noncomputable def Ns336p2217 := Ns336p2184 54723 BSN.abs_quadSignPos (BSN.cos_quad_nat3 495 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 213850930 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 320 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 206398340 268435456) qz260 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz257) qz257 1) Bool.true 3729 4194304 386317 39649280000 238656 268435456 2616 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz257) qz257 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz257)) Bool.true 3729 4194304 386317 39649280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz257) qz257) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz257)) Bool.true 29832 33554432 24724288 2537553920000 3729 4194304 386317 39649280000 (Ns336p2215 rfl rfl) rfl)) rfl) (Ns336p2216 rfl) RS337to348.d7 

noncomputable def Ns336p2218 := nat_lit 58863385374509549766877509392846500146061530126162643505638026646462720 

noncomputable def Ns336p2219 := nat_lit 14047549096339982309484474623747637182863938815653532716214429491456 

noncomputable def Ns336p2220 := nat_lit 154143265663273794179987644974730956589007942048533960604654294045368576 

noncomputable def Ns336p2221 := BSN.sin_dyadic_bound_f 247428698 268435456 3 2 268435456 134217728 Ns336p2218 Ns336p127 Ns336p2219 Ns336p2220 Ns336p130 Ns336p2219 213850930 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 247428698) qz371 0 2 Ns336p2218 Ns336p127 Ns336p2219 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 247428698) qz372 0 2 Ns336p2220 Ns336p130 Ns336p2219 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2222 := nat_lit 10489212659061288952963792848306134801363914516235215378026646732800000 

noncomputable def Ns336p2223 := nat_lit 1445534558436785678259413297255357568360527699943041374617600000000 

noncomputable def Ns336p2224 := nat_lit 31464746908066993287534859718323893688955022493305760051330704998400000 

noncomputable def Ns336p2225 := BSN.cos_dyadic_bound_f 186210240 268435456 3 2 268435456 134217728 Ns336p2222 Ns336p251 Ns336p2223 Ns336p2224 Ns336p254 Ns336p2223 206398340 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 186210240) qz369 0 2 Ns336p2222 Ns336p251 Ns336p2223 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 186210240) qz370 0 2 Ns336p2224 Ns336p254 Ns336p2223 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2226 := nat_lit 29069750763258949605361505406976 

noncomputable def Ns336p2227 := BSN.cos_dyadic_bound_f 73427768 268435456 2 1 268435456 134217728 Ns336p2226 Ns336p142 Ns336p2226 Ns336p2226 Ns336p143 Ns336p2226 258455212 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 73427768) qz369 0 1 Ns336p2226 Ns336p142 Ns336p2226 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 73427768) qz370 0 1 Ns336p2226 Ns336p143 Ns336p2226 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2228 := nat_lit 16787512380090129187674485432843861808129311468888928355937217316349595827410285619424680676133229544000000000 

noncomputable def Ns336p2229 := nat_lit 1723891932545755107884802496883213769265107651289563563541153284864500058784564043212890625000000000000 

noncomputable def Ns336p2230 := nat_lit 83897960365860018518571220198750546381315046183518642009683377182190861091967165217057401050703647720000000000 

noncomputable def Ns336p2231 := BSN.sin_dyadic_bound_f 330909450 268435456 4 3 268435456 134217728 Ns336p2228 Ns336p158 Ns336p2229 Ns336p2230 Ns336p161 Ns336p2229 253241742 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 330909450) qz371 0 3 Ns336p2228 Ns336p158 Ns336p2229 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 330909450) qz372 0 3 Ns336p2230 Ns336p161 Ns336p2229 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2232 := Ns336p2182 93155 BSN.abs_quadSignPos (BSN.cos_quad_nat0 196 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 258455212 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 253241742 268435456) qz260 rfl rfl (Ns336p2217 RS337to348.d9 RS337to348.d11 RS337to348.d13 RS337to348.d17 (Ns336p2221 rfl rfl) (Ns336p2225 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns336p2216 rfl) RS337to348.d19 RS337to348.d21 RS337to348.d23 RS337to348.d25 RS337to348.d17 (Ns336p2227 rfl rfl) (Ns336p2231 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns336p2233 := BSN.sin_dyadic_bound_f 12210667 268435456 1 0 268435456 134217728 0 1 1 0 1 1 12206455 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 12210667) qz371 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 12210667) qz372 0 0 rfl) rfl rfl 

noncomputable def Ns336p2234 := nat_lit 48177091569430623794657308649795689643375868644935295206246753091919265 

noncomputable def Ns336p2235 := nat_lit 9410850375466140287454887820765539997964919218053610788495677922721 

noncomputable def Ns336p2236 := nat_lit 126162860352662783806494214740612233429797236581810829217941074619342241 

noncomputable def Ns336p2237 := BSN.sin_dyadic_bound_f 235344259 268435456 3 2 268435456 134217728 Ns336p2234 Ns336p127 Ns336p2235 Ns336p2236 Ns336p130 Ns336p2235 206332515 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 235344259) qz371 0 2 Ns336p2234 Ns336p127 Ns336p2235 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 235344259) qz372 0 2 Ns336p2236 Ns336p130 Ns336p2235 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2238 := Ns336p2180 125585 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 21 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 12206455 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 45 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 206332515 268435456) qz260 rfl rfl (Ns336p2232 rfl rfl) (Ns336p2216 rfl) RS337to348.d27 RS337to348.d29 RS337to348.d31 RS337to348.d33 RS337to348.d17 (Ns336p2233 rfl rfl) (Ns336p2237 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p2239 := nat_lit 102351088799312222824446835360000 

noncomputable def Ns336p2240 := BSN.sin_dyadic_bound_f 100582660 268435456 2 1 268435456 134217728 Ns336p2239 Ns336p137 Ns336p2239 Ns336p2239 Ns336p138 Ns336p2239 98245496 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 100582660) qz371 0 1 Ns336p2239 Ns336p137 Ns336p2239 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 100582660) qz372 0 1 Ns336p2239 Ns336p138 Ns336p2239 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2241 := nat_lit 5768467346327336440242964327441 

noncomputable def Ns336p2242 := BSN.cos_dyadic_bound_f 49007789 268435456 2 1 268435456 134217728 Ns336p2241 Ns336p142 Ns336p2241 Ns336p2241 Ns336p143 Ns336p2241 263974235 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 49007789) qz369 0 1 Ns336p2241 Ns336p142 Ns336p2241 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 49007789) qz370 0 1 Ns336p2241 Ns336p143 Ns336p2241 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2243 := Ns336p2178 153454 BSN.abs_quadSignPos (BSN.cos_quad_nat3 103 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 98245496 268435456) BSN.abs_quadSignNeg qz678 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 263974235 268435456) qz260 rfl rfl (Ns336p2238 rfl) (Ns336p2216 rfl) RS337to348.d35 RS337to348.d37 RS337to348.d39 RS337to348.d41 RS337to348.d17 (Ns336p2240 rfl rfl) (Ns336p2242 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p2244 := nat_lit 77162264391509532152189826126886489050910666052801897358043996900000000 

noncomputable def Ns336p2245 := nat_lit 24135460992521292220144277831560748318073521240114437539062500000000 

noncomputable def Ns336p2246 := nat_lit 202052568374251359258807406263451611064632006341997164943623414500000000 

noncomputable def Ns336p2247 := BSN.sin_dyadic_bound_f 264747550 268435456 3 2 268435456 134217728 Ns336p2244 Ns336p127 Ns336p2245 Ns336p2246 Ns336p130 Ns336p2245 223866809 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 264747550) qz371 0 2 Ns336p2244 Ns336p127 Ns336p2245 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 264747550) qz372 0 2 Ns336p2246 Ns336p130 Ns336p2245 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2248 := Ns336p2176 Bool.false 376395660 153454 Bool.true 264747550 14148475504056880 1 Bool.false 223866809 Bool.false Bool.false 447188560 166286 BSN.abs_quadSignPos qz373 (BSN.sfrac_eq_quadSignPos_mul Bool.false 223866809 268435456) qz260 rfl (Ns336p2243 rfl) (Ns336p2216 rfl) RS337to348.d43 RS337to348.d45 RS337to348.d17 (Ns336p2247 rfl rfl) rfl 

noncomputable def Ns336p2249 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz257) qz257 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz257) qz257 10) 447188560 268435456 166286 268435456 447188560 268435456 166286 268435456 240082530043166720 27949285 8388608 83143 67108864 (Ns336p2248 rfl rfl rfl rfl) 

noncomputable def Ns336p2250 := @Enclosure.Real.IsNear.mulLit_ff qz587 (Zeta.RiemannSiegel.correction qz259) 5204437 16777216 1 16777216 113556406624731 281474976710656 195137314254591 10643272556871680000 590997164224795131447 4722366482869645213696 

noncomputable abbrev qz591 := (@HPow.hPow Real Real Real qz630 qz258 qz8)

noncomputable def Ns336p2251 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz591 1 1 0 1 5204437 16777216 1 16777216 5204437 16777216 1 16777216 

noncomputable def Ns336p2252 := @Enclosure.Real.IsNear.sqrt_image qz258 3623552338619 33554432000 678523 33554432000 174346076 174346110 16777216 (@Enclosure.Real.IsNear.of_eq qz258 (@HMul.hMul Real Real Real qz5 qz257 qz3) Bool.false 3623552338619 33554432000 678523 33554432000 (BSN.t_div_two_pi_mk qz257 678523 1000 qz260) (@Enclosure.Real.IsNear.mulLit_ff qz257 qz3 678523 1000 0 1 5340353 33554432 1 33554432 3623552338619 33554432000 678523 33554432000 (Enclosure.Real.IsNear.const Bool.false 678523 1000) RS337to348.d48 rfl)) 

noncomputable abbrev qz882 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 678523 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz776 := qz882

noncomputable abbrev qz592 := qz776

noncomputable abbrev qz263 := qz592

noncomputable def Ns336p2253 := @Enclosure.Real.IsNear.sqrt_image qz263 174346093 16777216 17 16777216 54083655 54083661 16777216 (@Enclosure.Real.IsNear.recentre' qz263 Bool.false 348692186 33554432 34 33554432 174346093 16777216 17 16777216 (Ns336p2252 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns336p2254 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz263) 27041829 8388608 3 16777216 5204436 5204438 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz263) Bool.false 108167316 33554432 6 33554432 27041829 8388608 3 16777216 (Ns336p2253 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns336p2255 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz263)) Bool.false 10408874 33554432 2 33554432 5204437 16777216 1 16777216 (Ns336p2254 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz264 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz586))

noncomputable abbrev qz777 := (@HMul.hMul Real Real Real qz824 qz880 qz880)

noncomputable abbrev qz593 := (@HSub.hSub Real Real Real qz631 (@HSub.hSub Real Real Real qz631 qz777 qz770) qz639)

noncomputable abbrev qz265 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz593))

noncomputable def Ns336p2256 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz259) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz264) qz265) Bool.false 113556406624731 

noncomputable def Ns336p2257 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz264) qz265 43139139 33554432 367 

noncomputable abbrev qz778 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz264))

noncomputable def Ns336p2258 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz264) (@Neg.neg Real Real.instNeg qz778) Bool.true 43139139 33554432 367 33554432 (BSN.inv_eq_neg_inv_neg qz264) 

noncomputable def Ns336p2259 := @Enclosure.Real.IsNear.recentre' qz778 Bool.false 43139139 33554432 367 33554432 43139139 33554432 

noncomputable def Ns336p2260 := @Enclosure.Real.IsNear.recentre' qz264 Bool.true 26099267 33554432 1074154432 162403450880000 26099267 33554432 16783663 2537553920000 

noncomputable abbrev qz266 := (@HMul.hMul Real Real Real qz349 qz346 qz586)

noncomputable def Ns336p2261 := @Enclosure.Real.IsNear.cos_image qz266 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 41305239) qz368) Bool.false 41305239 16777216 215 33554432 Bool.true 26099267 33554432 1 

noncomputable def Ns336p2262 := nat_lit 18350531280408737088802511 

noncomputable def Ns336p2263 := nat_lit 2882303761517117440000000000000 

noncomputable def Ns336p2264 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz259 884279719003555 140737488355328 1 500000000000000 6573933 16777216 17 16777216 5813195625988197331815 2361183241434822606848 Ns336p2262 

noncomputable def Ns336p2265 := @Enclosure.Real.IsNear.subLit_ff_p qz263 qz1 174346093 16777216 17 16777216 10 1 0 1 6573933 6573933 16777216 17 

noncomputable def Ns336p2266 := @Ns336p2265 16777216 (@Enclosure.Real.IsNear.recentre' qz263 Bool.false 348692186 33554432 34 33554432 174346093 16777216 17 16777216 (Ns336p2252 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns336p2267 := @Enclosure.Real.IsNear.recentre' qz266 Bool.false 5813195625988197331815 2361183241434822606848 Ns336p2262 Ns336p2263 41305239 16777216 215 33554432 (@Ns336p2264 Ns336p2263 RS337to348.d47 (Ns336p2266 rfl rfl) rfl) 

noncomputable def Ns336p2268 := nat_lit 2154759813366838489776128 

noncomputable def Ns336p2269 := nat_lit 948829092672938305981741948460544347518317588681935038194938480303483086395109573811285985 

noncomputable def Ns336p2270 := nat_lit 197875715934152911487277122897838790218538126941457760385756474503332924999666461356001 

noncomputable def Ns336p2271 := nat_lit 2484708205841421220476439987769114885459049384818591311279452414121831258680049423806410721 

noncomputable def Ns336p2272 := BSN.sin_dyadic_bound_f 61241957307 68719476736 3 2 33554432 9689454 Ns336p2269 Ns336p1224 Ns336p2270 Ns336p2271 Ns336p1227 Ns336p2270 26099267 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 61241957307) qz366 0 2 Ns336p2269 Ns336p1224 Ns336p2270 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 61241957307) qz367 0 2 Ns336p2271 Ns336p1227 Ns336p2270 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2273 := @Ns336p2261 4840000 (Ns336p2267 rfl) (Enclosure.sfrac_false_div 41305239 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 41305239) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns336p2268) qz635) 226375608064910080 72057594037927936 Bool.false 26099267 33554432 0 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q1 41305239 16777216 226375608064910080 72057594037927936 0 Ns336p2268 Ns336p110 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 26099267 33554432 Ns336p2268 Ns336p110 61241957307 68719476736 9689454 9680000 (Ns336p2272 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p2274 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz264) 26099267 33554432 16783663 2537553920000 21569386 21569753 16777216 (@Enclosure.Real.IsNear.neg qz264 Bool.true 26099267 33554432 16783663 2537553920000 (Ns336p2260 (Ns336p2273 rfl rfl) rfl)) 

noncomputable def Ns336p2275 := Ns336p2258 (@Enclosure.Real.IsNear.neg qz778 Bool.false 43139139 33554432 367 33554432 (@Ns336p2259 367 33554432 (Ns336p2274 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p2276 := @Enclosure.Real.IsNear.recentre' qz265 Bool.true 5264658 16777216 

noncomputable abbrev qz267 := (@HMul.hMul Real Real Real qz349 qz346 qz593)

noncomputable def Ns336p2277 := @Enclosure.Real.IsNear.cos_image qz267 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 63417435)) qz396) Bool.true 63417435 33554432 

noncomputable def Ns336p2278 := nat_lit 74870093438334174256845247525 

noncomputable def Ns336p2279 := nat_lit 13728536630758137038355168891357821 

noncomputable def Ns336p2280 := @Enclosure.Real.IsNear.recentre' qz267 Bool.true Ns336p2278 Ns336p471 Ns336p2279 

noncomputable abbrev qz268 := qz593

noncomputable def Ns336p2281 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz268 884279719003555 140737488355328 1 500000000000000 84667884866455 

noncomputable abbrev qz594 := (@HSub.hSub Real Real Real qz631 qz777 qz770)

noncomputable abbrev qz269 := qz594

noncomputable def Ns336p2282 := @Enclosure.Real.IsNear.subLit_tf qz269 qz26 67075698822039 281474976710656 508726683 281474976710656 1 16 

noncomputable abbrev qz595 := qz777

noncomputable abbrev qz270 := qz595

noncomputable def Ns336p2283 := @Enclosure.Real.IsNear.subLit_ff_n qz270 qz259 43216595088489 281474976710656 223514011 281474976710656 6573933 16777216 17 16777216 

noncomputable def Ns336p2284 := @Enclosure.Real.IsNear.mulLit_ff qz259 qz259 6573933 16777216 17 16777216 6573933 16777216 17 16777216 43216595088489 281474976710656 

noncomputable def Ns336p2285 := nat_lit 522695847632147011579358520574585039451566303912015530109217073309252020602779615962270501658140625 

noncomputable def Ns336p2286 := nat_lit 4231594747089214461215483147704153707015281457487782536379253330612129989482231969843994140625 

noncomputable def Ns336p2287 := nat_lit 3155065322004180792015315320603532607040069514643906600122073916110147311682260385648573490355740625 

noncomputable def Ns336p2288 := BSN.cos_dyadic_bound_t 63417435 33554432 4 3 16777216 4840000 Ns336p2285 Ns336p328 Ns336p2286 Ns336p2287 Ns336p331 Ns336p2286 5264658 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 63417435) (BSN.cosEvenQ 33554432) 0 3 Ns336p2285 Ns336p328 Ns336p2286 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 63417435) (BSN.cosOddQ 33554432) 0 3 Ns336p2287 Ns336p331 Ns336p2286 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2289 := @Ns336p2276 941217216 81201725440000 2632329 8388608 14706519 1268776960000 (@Ns336p2277 191 16777216 Bool.true 5264658 16777216 1 4840000 (@Ns336p2280 Ns336p474 63417435 33554432 191 16777216 (@Ns336p2281 281474976710656 508726683 281474976710656 Ns336p2278 Ns336p471 Ns336p2279 Ns336p474 RS337to348.d47 (@Ns336p2282 0 1 1354686157863280 84667884866455 281474976710656 508726683 281474976710656 (@Ns336p2283 1125343487488293863424 67075698822039 281474976710656 508726683 281474976710656 (@Ns336p2284 223514011 281474976710656 (Ns336p2266 rfl rfl) (Ns336p2266 rfl rfl) rfl) (Ns336p2266 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 63417435 33554432) (BSN.cos_neg_of_bound 63417435 33554432 Bool.true 5264658 16777216 1 4840000 (Ns336p2288 rfl rfl)) rfl rfl) 

noncomputable def Ns336p2290 := @Ns336p2250 2039747810300065431591 Ns336p2173 (Ns336p2251 qz28 (@Enclosure.Real.IsNear.of_eq qz591 (@Inv.inv Real Real.instInv (Real.sqrt qz263)) Bool.false 5204437 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz258 (BSN.t_div_two_pi_nonneg qz257 678523 1000 qz260)) Ns336p2255) rfl) (@Ns336p2256 281474976710656 195137314254591 10643272556871680000 (BSN.correction_mk qz259 (BSN.cos_two_pi_p_ne_zero_mk qz257 678523 1000 10 qz260 rfl rfl (@BSN.floor_sqrt_eq_dec qz257 678523 1000 10 qz260 rfl rfl rfl))) (@Ns336p2257 33554432 2632329 8388608 14706519 1268776960000 113556406624731 281474976710656 195137314254591 10643272556871680000 Ns336p2275 (Ns336p2289 rfl) rfl)) 

noncomputable def Ns336p2291 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz257) (hardyZApproximantRS₀ qz257) Bool.false 15143051524684179030473 4722366482869645213696 444496552908291110551591 Ns336p2173 (@Eq.refl Real (hardyZApproximantRS₀ qz257)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz257) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz257) qz257 10) (@HMul.hMul Real Real Real qz5 qz587 (Zeta.RiemannSiegel.correction qz259))) Bool.false 15143051524684179030473 4722366482869645213696 444496552908291110551591 Ns336p2173 (BSN.hardyZApproximantRS₀_eq qz257 10 (@BSN.floor_sqrt_eq_dec qz257 678523 1000 10 qz260 rfl rfl rfl)) (@Ns336p2175 15143051524684179030473 4722366482869645213696 444496552908291110551591 Ns336p2173 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz257) qz257 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz257) qz257 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz257) qz257 10)) Bool.false 27949285 8388608 83143 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz257) qz257 10) (Ns336p2249 (Ns336p2248 rfl rfl rfl rfl) rfl rfl)) (Ns336p2290 rfl) rfl rfl)) 

theorem RS337to348.d75 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz257) Bool.false 15143051524684179030473 4722366482869645213696 444496552908291110551591 Ns336p2173 := Ns336p2291 

noncomputable def Ns336p2292 := nat_lit 12986507827891524337664000 

noncomputable def Ns336p2293 := nat_lit 2577539869638967617053100343296 

noncomputable abbrev qz883 := (Enclosure.sfrac Bool.false 681206 1000)

noncomputable abbrev qz779 := qz883

noncomputable abbrev qz596 := qz779

noncomputable abbrev qz271 := qz596

noncomputable abbrev qz884 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 681206 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz780 := qz884

noncomputable abbrev qz597 := qz780

noncomputable abbrev qz272 := qz597

noncomputable abbrev qz885 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 681206 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz781 := qz885

noncomputable abbrev qz598 := qz781

noncomputable abbrev qz273 := qz598

noncomputable abbrev qz599 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz630 qz272 qz8))

noncomputable def Ns336p2294 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz271) qz271 10) (@HMul.hMul Real Real Real qz5 qz599 (Zeta.RiemannSiegel.correction qz273)) 264666945 67108864 166945 134217728 1159775991081594722979 9444732965739290427392 66500530151177623241 Ns336p2292 Ns336p2293 

noncomputable def Ns336p2295 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz271) qz271 Real.sin BSN.quadSignPos 9 10 681206 1000 199 268435456 134217728 4503599627370496 Bool.false 336904159516 2558 618095470 56 84886744 8 

noncomputable def Ns336p2296 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz271) qz271 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 681206 1000 102 153 268435456 134217728 4503599627370496 Bool.false 336904159516 2558 

noncomputable def Ns336p2297 := Ns336p2296 558195838 56 94906264 8 589812974 56 89478488 8 Bool.true 476464590 126082 Bool.true 333136821 Bool.true 366390725 14148475504056880 1 Bool.false 86924946 Bool.true Bool.false 262766245 Bool.true Bool.true 594785950 

noncomputable def Ns336p2298 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz271) qz271 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 681206 1000 21 44 268435456 134217728 4503599627370496 Bool.false 336904159516 2558 

noncomputable def Ns336p2299 := Ns336p2298 480971758 57 109588312 8 522351262 57 101459064 8 Bool.true 385770908 93523 Bool.false 408506142 Bool.true 371727422 14148475504056880 1 Bool.false 268113364 Bool.true Bool.false 49642595 Bool.false Bool.true 476464590 

noncomputable def Ns336p2300 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz271) qz271 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 681206 1000 197 101 268435456 134217728 4503599627370496 Bool.false 336904159516 2558 

noncomputable def Ns336p2301 := Ns336p2300 372130544 56 134217720 8 432030192 56 120047984 16 Bool.true 250908311 54938 Bool.false 340086791 Bool.false 15200289 14148475504056880 1 Bool.false 256136921 Bool.true Bool.false 15192167 Bool.true Bool.true 385770908 

noncomputable def Ns336p2302 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz271) qz271 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 681206 1000 498 322 268435456 134217728 4503599627370496 Bool.false 336904159516 2558 

noncomputable def Ns336p2303 := Ns336p2302 186065264 56 189812528 16 294906480 56 154981288 8 Bool.true 125672 2624 Bool.false 169986010 Bool.false 238403999 14148475504056880 1 Bool.false 216388548 Bool.true Bool.false 169347506 Bool.true Bool.true 250908311 

noncomputable def Ns336p2304 := nat_lit 79425561443787766173588240249473346407768632699060463 

noncomputable def Ns336p2305 := nat_lit 63283982111725533643010172733229633528372926611456 

noncomputable def Ns336p2306 := nat_lit 70409968946202935930211864212480000 

noncomputable def Ns336p2307 := nat_lit 287782232188535697982889235996615905280 

noncomputable def Ns336p2308 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz271 681206 1000 1856167457744 16000000 1362412 4000 2000 Ns336p2306 Ns336p2307 (@Eq.refl Real qz271) rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns336p2309 := nat_lit 1626635498368773451235087160309214134431101597676758282240 

noncomputable abbrev qz782 := (Real.log (Enclosure.sfrac Bool.false 1856167457744 16000000))

noncomputable abbrev qz783 := (@Nat.cast Real Real.instNatCast 1362412)

noncomputable abbrev qz784 := (Enclosure.sfrac Bool.false 681206 2000)

noncomputable abbrev qz274 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 681206 4000) qz782) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz783))))) qz784)

noncomputable abbrev qz600 := (@HSub.hSub Real Real Real qz11 qz274 (@HMul.hMul Real Real Real qz5 qz784 (Real.log Real.pi)))

noncomputable def Ns336p2310 := @Enclosure.Real.IsNear.addLit_ft_p qz600 (Enclosure.sfrac Bool.true Ns336p2306 Ns336p2307) 5652314957378675883 4503599627370496 2360450093379396167 247808000000000000000000 Ns336p2306 Ns336p2307 0 1 Ns336p2309 

noncomputable def Ns336p2311 := nat_lit 23707527234993209770770432000000 

noncomputable abbrev qz601 := (@HMul.hMul Real Real Real qz5 qz784 (Real.log Real.pi))

noncomputable def Ns336p2312 := @Enclosure.Real.IsNear.subLit_ff_p qz274 qz601 926032673896917215103 562949953421312000 538442517218829 121000000000000000000 13082820428883 33554432000 340603 67108864000 Ns336p2311 5652314957378675883 4503599627370496 

noncomputable def Ns336p2313 := nat_lit 1852065347793834430206000 

noncomputable abbrev qz275 := (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 681206 4000) qz782) (@HMul.hMul Real Real Real qz349 qz356 (@HSub.hSub Real Real Real qz355 qz357 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz358 qz783)))))

noncomputable def Ns336p2314 := @Enclosure.Real.IsNear.subLit_ff_p qz275 qz784 1117775116882076346239 562949953421312000 538442517218829 121000000000000000000 681206 2000 0 1 Ns336p2313 926032673896917215103 562949953421312000 538442517218829 121000000000000000000 

noncomputable def Ns336p2315 := nat_lit 2517005799937065822805912505414582272 

noncomputable def Ns336p2316 := nat_lit 56391242775323740410478592 

noncomputable def Ns336p2317 := nat_lit 6171177758378107054221536466229201478607131739995041228435265115964966345299560841404911845623690731438680054280289333081428724648329789435517566052398915637098936772624975816294400 

noncomputable def Ns336p2318 := nat_lit 166814247788089794002365622971721901986977094759252965527261880766203181298906571133961689300713482622223903189770096394043236806716461572151010921809738861199131528423191231856640 

noncomputable def Ns336p2319 := nat_lit 6783469520055230219640878214094924130338348166214650563066675581876355098716002601964781734081333648933378705608220090190996237858560622976977259212387589588131114867752960 

noncomputable def Ns336p2320 := BSN.log_dyadic_bound 807591457744 2904743457744 8 7 Ns336p2317 134217728 38720000 Ns336p2318 Ns336p2319 76649167 3712334915488 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 807591457744) (BSN.artanhQ 2904743457744) 0 7 Ns336p2318 Ns336p2317 Ns336p2319 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns336p2321 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 681206 4000) qz782 681206 4000 0 1 3282402337955063 281474976710656 195312621 7562500000000000 1117996083514508322989 562949953421312000 66524064650463 15125000000000000000 (Enclosure.Real.IsNear.const Bool.false 681206 4000) (BSN.isNear_log_sfrac 1856167457744 16000000 3282402337955063 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1856167457744) qz362)) Bool.false Ns336p2316 Ns336p98 1000000619520000 38720000000000000000000 3282402337955063 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1856167457744 16000000 16 3712334915488 2097152000000 76649167 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns336p2320 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p2322 := BSN.arctan_dyadic_bound_f 1000 1362412 1 0 16777216 4840000 0 1 1 0 1 1 12314 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1362412) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1362412) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz785 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1362412)))

noncomputable def Ns336p2323 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz785 884279719003555 562949953421312 1 2000000000000000 12314 16777216 1 4840000 14828819684415516966912 883866529727907 562949953421312 50000000121 242000000000000000 qz16 (Ns336p2322 rfl) rfl rfl 

noncomputable def Ns336p2324 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 681206 4000) qz782) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz785)) 1117996083514508322989 562949953421312000 66524064650463 15125000000000000000 883866529727907 2251799813685248 50000000121 968000000000000000 Ns336p2315 1117775116882076346239 562949953421312000 538442517218829 121000000000000000000 (Ns336p2321 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz785) 1 4 0 1 883866529727907 562949953421312 50000000121 242000000000000000 883866529727907 2251799813685248 50000000121 968000000000000000 qz364 Ns336p2323 rfl) 

noncomputable def Ns336p2325 := @Ns336p2310 Ns336p2304 Ns336p2305 2360450093379396167 247808000000000000000000 (@Ns336p2312 2360450093379396167 247808000000000000000000 (Ns336p2314 (Ns336p2324 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 681206 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz784 (Real.log Real.pi) 681206 2000 0 1 38410761 33554432 1 67108864 13082820428883 33554432000 340603 67108864000 (Enclosure.Real.IsNear.const Bool.false 681206 2000) RS337to348.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns336p2306 Ns336p2307) 

noncomputable def Ns336p2326 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz271) Bool.false Ns336p2304 Ns336p2305 2360450093379396167 247808000000000000000000 42113019939 33554432 321 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz271) (@HAdd.hAdd Real Real Real qz365 qz600 (Enclosure.sfrac Bool.true Ns336p2306 Ns336p2307)) Bool.false Ns336p2304 Ns336p2305 2360450093379396167 247808000000000000000000 Ns336p2308 (Ns336p2325 rfl rfl)) 

noncomputable def Ns336p2327 := nat_lit 7593641027657243377532928 

noncomputable def Ns336p2328 := nat_lit 1350875825158312787223041777117579021073275941309986607455977102227769067193721518485470440601385634710576067714544563563732265270083594321 

noncomputable def Ns336p2329 := nat_lit 2493693936948041947913079452003522175061518610759842707772491934999324804938561608308318349000456929925416245854024442297399182633041 

noncomputable def Ns336p2330 := nat_lit 8175596596087895213557934851048647821354858898904941451214746318217852809059145456080975666600563725042881522857146530560849805286255110225 

noncomputable def Ns336p2331 := BSN.cos_dyadic_bound_f 107912129403 68719476736 4 3 33554432 9689454 Ns336p2328 Ns336p2210 Ns336p2329 Ns336p2330 Ns336p2213 Ns336p2329 15709 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 107912129403) (BSN.cosEvenQ 68719476736) 0 3 Ns336p2328 Ns336p2210 Ns336p2329 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 107912129403) (BSN.cosOddQ 68719476736) 0 3 Ns336p2330 Ns336p2213 Ns336p2329 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2332 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz271) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 42113019939) qz396) Bool.false 42113019939 33554432 321 33554432 Bool.true 15709 33554432 1 4840000 (Ns336p2326 rfl) (Enclosure.sfrac_false_div 42113019939 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 42113019939) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns336p2327) qz413) 226375608064910080 72057594037927936 Bool.false 15709 33554432 199 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q2 42113019939 33554432 226375608064910080 72057594037927936 199 Ns336p2327 Ns336p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 15709 33554432 Ns336p2327 Ns336p98 107912129403 68719476736 9689454 9680000 (Ns336p2331 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p2333 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz271) Bool.false Ns336p2304 Ns336p2305 2360450093379396167 247808000000000000000000 336904159516 268435456 2558 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz271) (@HAdd.hAdd Real Real Real qz365 qz600 (Enclosure.sfrac Bool.true Ns336p2306 Ns336p2307)) Bool.false Ns336p2304 Ns336p2305 2360450093379396167 247808000000000000000000 Ns336p2308 (Ns336p2325 rfl rfl)) 

noncomputable def Ns336p2334 := Ns336p2303 54938 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 498 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 216388548 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 322 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 169347506 268435456) (@Eq.refl Real qz271) rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz271) qz271 1) Bool.true 15709 33554432 24799913 2537553920000 125672 268435456 2624 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz271) qz271 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz271)) Bool.true 15709 33554432 24799913 2537553920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz271) qz271) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz271)) Bool.true 15709 33554432 1587194432 162403450880000 15709 33554432 24799913 2537553920000 (Ns336p2332 rfl rfl) rfl)) rfl) (Ns336p2333 rfl) RS337to348.d7 

noncomputable def Ns336p2335 := nat_lit 7283885044690751995170101477070885789132894844821803122295274032800000 

noncomputable def Ns336p2336 := nat_lit 697116625313216984714875799151713005166663834374572686880100000000 

noncomputable def Ns336p2337 := nat_lit 21850260900821629551540874679614353941388351206796660221512061898400000 

noncomputable def Ns336p2338 := BSN.cos_dyadic_bound_f 169986010 268435456 3 2 268435456 134217728 Ns336p2335 Ns336p251 Ns336p2336 Ns336p2337 Ns336p254 Ns336p2336 216388548 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 169986010) qz369 0 2 Ns336p2335 Ns336p251 Ns336p2336 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 169986010) qz370 0 2 Ns336p2337 Ns336p254 Ns336p2336 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2339 := nat_lit 28189264284194359946261280872044619258973417286315544972831835322049281 

noncomputable def Ns336p2340 := nat_lit 10435380473432173763592687373191736868160131591212304198296140768001 

noncomputable def Ns336p2341 := nat_lit 84546922091636215491256657241387474303183931595764210310098913684611841 

noncomputable def Ns336p2342 := BSN.cos_dyadic_bound_f 238403999 268435456 3 2 268435456 134217728 Ns336p2339 Ns336p251 Ns336p2340 Ns336p2341 Ns336p254 Ns336p2340 169347506 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 238403999) qz369 0 2 Ns336p2339 Ns336p251 Ns336p2340 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 238403999) qz370 0 2 Ns336p2341 Ns336p254 Ns336p2340 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2343 := nat_lit 18730400091847866297446699151373443401440242721129872632516026195039128118734778949276774878151705344775784481 

noncomputable def Ns336p2344 := nat_lit 2393741067537689216567825685724446445982451680017761706924538597077037641718425440555702784015216642081 

noncomputable def Ns336p2345 := nat_lit 93602709699118997086676490622683104963476370968642039758662276360284112258346573894833893982752446703858321441 

noncomputable def Ns336p2346 := BSN.sin_dyadic_bound_f 340086791 268435456 4 3 268435456 134217728 Ns336p2343 Ns336p158 Ns336p2344 Ns336p2345 Ns336p161 Ns336p2344 256136921 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 340086791) qz371 0 3 Ns336p2343 Ns336p158 Ns336p2344 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 340086791) qz372 0 3 Ns336p2345 Ns336p161 Ns336p2344 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2347 := nat_lit 53383541365829618611170957441 

noncomputable def Ns336p2348 := BSN.sin_dyadic_bound_f 15200289 268435456 2 1 268435456 134217728 Ns336p2347 Ns336p137 Ns336p2347 Ns336p2347 Ns336p138 Ns336p2347 15192167 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 15200289) qz371 0 1 Ns336p2347 Ns336p137 Ns336p2347 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 15200289) qz372 0 1 Ns336p2347 Ns336p138 Ns336p2347 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2349 := Ns336p2301 93523 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 197 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 256136921 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 101 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 15192167 268435456) (@Eq.refl Real qz271) rfl rfl (Ns336p2334 RS337to348.d9 RS337to348.d11 RS337to348.d13 RS337to348.d17 (Ns336p2338 rfl rfl) (Ns336p2342 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns336p2333 rfl) RS337to348.d19 RS337to348.d21 RS337to348.d23 RS337to348.d25 RS337to348.d17 (Ns336p2346 rfl rfl) (Ns336p2348 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns336p2350 := nat_lit 39028537710381172286105662621831610086466178467724525238400341462452714917701949449103053509956044549333979136 

noncomputable def Ns336p2351 := nat_lit 21596485786222122220121106050728055492818508493020656002666607562122652201704484330227853548650046427136 

noncomputable def Ns336p2352 := nat_lit 194929026507010793445303155332128530662414258367496185771687924757784867713931479695665731777457100484647325696 

noncomputable def Ns336p2353 := BSN.sin_dyadic_bound_f 408506142 268435456 4 3 268435456 134217728 Ns336p2350 Ns336p158 Ns336p2351 Ns336p2352 Ns336p161 Ns336p2351 268113364 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 408506142) qz371 0 3 Ns336p2350 Ns336p158 Ns336p2351 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 408506142) qz372 0 3 Ns336p2352 Ns336p161 Ns336p2351 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2354 := nat_lit 10296580998308122566025141164775498098400619298464215937184410373933430605522609149019314972000196448498487296 

noncomputable def Ns336p2355 := nat_lit 6961377697180645350194392156072405779659380104715652975179433969188463600148331799839407301839114735616 

noncomputable def Ns336p2356 := nat_lit 62374933394584199631700946828328270158221041645283541079775146525516885084934931283764193749068422165337477120 

noncomputable def Ns336p2357 := BSN.cos_dyadic_bound_f 371727422 268435456 4 3 268435456 134217728 Ns336p2354 Ns336p121 Ns336p2355 Ns336p2356 Ns336p124 Ns336p2355 49642595 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 371727422) qz369 0 3 Ns336p2354 Ns336p121 Ns336p2355 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 371727422) qz370 0 3 Ns336p2356 Ns336p124 Ns336p2355 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2358 := Ns336p2299 126082 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 21 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268113364 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 49642595 268435456) (@Eq.refl Real qz271) rfl rfl (Ns336p2349 rfl rfl) (Ns336p2333 rfl) RS337to348.d27 RS337to348.d29 RS337to348.d31 RS337to348.d33 RS337to348.d17 (Ns336p2353 rfl rfl) (Ns336p2357 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p2359 := nat_lit 6636639000307231020909009847838429913507922518504268156912626082919018587634717794406792983064139739975851921 

noncomputable def Ns336p2360 := nat_lit 1868407686908525718663199291804748983396530714660669955303125600323126082180893214238128871282405220241 

noncomputable def Ns336p2361 := nat_lit 40224421488970295860118247892784963642815447227321807011942820493289956561039053460158744377684517729645305745 

noncomputable def Ns336p2362 := BSN.cos_dyadic_bound_f 333136821 268435456 4 3 268435456 134217728 Ns336p2359 Ns336p121 Ns336p2360 Ns336p2361 Ns336p124 Ns336p2360 86924946 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 333136821) qz369 0 3 Ns336p2359 Ns336p121 Ns336p2360 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 333136821) qz370 0 3 Ns336p2361 Ns336p124 Ns336p2360 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2363 := nat_lit 25240284619695263957729234750113379277778171933509620123118596852536457745208918625317948848003947806744140625 

noncomputable def Ns336p2364 := nat_lit 5852395318293147396526262113587014062131383767539253680154150832710757456677946873774588108062744140625 

noncomputable def Ns336p2365 := nat_lit 126111962364325108227061158580394225192369510342154511996035433328377096390321170298041958223267306782744140625 

noncomputable def Ns336p2366 := BSN.sin_dyadic_bound_f 366390725 268435456 4 3 268435456 134217728 Ns336p2363 Ns336p158 Ns336p2364 Ns336p2365 Ns336p161 Ns336p2364 262766245 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 366390725) qz371 0 3 Ns336p2363 Ns336p158 Ns336p2364 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 366390725) qz372 0 3 Ns336p2365 Ns336p161 Ns336p2364 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2367 := Ns336p2297 154062 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 102 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 86924946 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 153 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 262766245 268435456) (@Eq.refl Real qz271) rfl rfl (Ns336p2358 rfl) (Ns336p2333 rfl) RS337to348.d35 RS337to348.d37 RS337to348.d39 RS337to348.d41 RS337to348.d17 (Ns336p2362 rfl rfl) (Ns336p2366 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns336p2368 := nat_lit 49010231093374230648514095610543062512406018101601276893311080646830625 

noncomputable def Ns336p2369 := nat_lit 9739087754123392325286929247983843994638431032640903113215625390625 

noncomputable def Ns336p2370 := nat_lit 128344361007235356682343595380258904166024442330140973258393338300590625 

noncomputable def Ns336p2371 := BSN.sin_dyadic_bound_f 236354995 268435456 3 2 268435456 134217728 Ns336p2368 Ns336p127 Ns336p2369 Ns336p2370 Ns336p130 Ns336p2369 206977589 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 236354995) qz371 0 2 Ns336p2368 Ns336p127 Ns336p2369 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 236354995) qz372 0 2 Ns336p2370 Ns336p130 Ns336p2369 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2372 := Ns336p2295 Bool.true 594785950 154062 Bool.true 236354995 14148475504056880 1 Bool.false 206977589 Bool.false Bool.true 529333890 166945 BSN.abs_quadSignPos qz373 (BSN.sfrac_eq_quadSignPos_mul Bool.false 206977589 268435456) (@Eq.refl Real qz271) rfl (Ns336p2367 rfl) (Ns336p2333 rfl) RS337to348.d43 RS337to348.d45 RS337to348.d17 (Ns336p2371 rfl rfl) rfl 

noncomputable def Ns336p2373 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz271) qz271 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz271) qz271 10) 529333890 268435456 166945 268435456 529333890 268435456 166945 268435456 284183968276807680 264666945 67108864 166945 134217728 (Ns336p2372 rfl rfl rfl rfl) 

noncomputable def Ns336p2374 := @Enclosure.Real.IsNear.mulLit_ff qz599 (Zeta.RiemannSiegel.correction qz273) 10398609 33554432 1 33554432 111531839602931 281474976710656 15950971781739 967570232442880000 1159775991081594722979 9444732965739290427392 

noncomputable abbrev qz602 := (@HPow.hPow Real Real Real qz630 qz272 qz8)

noncomputable def Ns336p2375 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz602 1 1 0 1 10398609 33554432 1 33554432 10398609 33554432 1 33554432 

noncomputable def Ns336p2376 := @Enclosure.Real.IsNear.sqrt_image qz272 1818940252859 16777216000 340603 16777216000 174690434 174690467 16777216 (@Enclosure.Real.IsNear.of_eq qz272 (@HMul.hMul Real Real Real qz5 qz271 qz3) Bool.false 1818940252859 16777216000 340603 16777216000 (BSN.t_div_two_pi_mk qz271 681206 1000 (@Eq.refl Real qz271)) (@Enclosure.Real.IsNear.mulLit_ff qz271 qz3 681206 1000 0 1 5340353 33554432 1 33554432 1818940252859 16777216000 340603 16777216000 (Enclosure.Real.IsNear.const Bool.false 681206 1000) RS337to348.d48 rfl)) 

noncomputable abbrev qz886 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 681206 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz786 := qz886

noncomputable abbrev qz603 := qz786

noncomputable abbrev qz276 := qz603

noncomputable def Ns336p2377 := @Enclosure.Real.IsNear.sqrt_image qz276 349380901 33554432 33 33554432 54137040 54137046 16777216 (@Enclosure.Real.IsNear.recentre' qz276 Bool.false 349380901 33554432 33 33554432 349380901 33554432 33 33554432 (Ns336p2376 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns336p2378 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz276) 54137043 16777216 3 16777216 5199304 5199305 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz276) Bool.false 108274086 33554432 6 33554432 54137043 16777216 3 16777216 (Ns336p2377 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns336p2379 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz276)) Bool.false 10398609 33554432 1 33554432 10398609 33554432 1 33554432 (Ns336p2378 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz277 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz598))

noncomputable abbrev qz787 := (@HMul.hMul Real Real Real qz824 qz885 qz885)

noncomputable abbrev qz604 := (@HSub.hSub Real Real Real qz631 (@HSub.hSub Real Real Real qz631 qz787 qz781) qz639)

noncomputable abbrev qz278 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz604))

noncomputable def Ns336p2380 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz273) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz277) qz278) Bool.false 111531839602931 

noncomputable def Ns336p2381 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz277) qz278 39374467 33554432 297 

noncomputable abbrev qz788 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz277))

noncomputable def Ns336p2382 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz277) (@Neg.neg Real Real.instNeg qz788) Bool.true 39374467 33554432 297 33554432 (BSN.inv_eq_neg_inv_neg qz277) 

noncomputable def Ns336p2383 := @Enclosure.Real.IsNear.recentre' qz788 Bool.false 39374467 33554432 297 33554432 39374467 33554432 

noncomputable def Ns336p2384 := @Enclosure.Real.IsNear.recentre' qz277 Bool.true 28594670 33554432 65017152 10150215680000 14297335 16777216 1015893 158597120000 

noncomputable abbrev qz279 := (@HMul.hMul Real Real Real qz349 qz346 qz598)

noncomputable def Ns336p2385 := @Enclosure.Real.IsNear.cos_image qz279 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43468901) qz368) Bool.false 43468901 16777216 13 2097152 Bool.true 28594670 33554432 1 

noncomputable def Ns336p2386 := nat_lit 890540488617308825787485863 

noncomputable def Ns336p2387 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz273 884279719003555 140737488355328 1 500000000000000 13836581 33554432 33 33554432 12235407958649928045455 4722366482869645213696 Ns336p2386 

noncomputable def Ns336p2388 := @Enclosure.Real.IsNear.subLit_ff_p qz276 qz1 349380901 33554432 33 33554432 10 1 0 1 13836581 13836581 33554432 33 

noncomputable def Ns336p2389 := @Ns336p2388 33554432 (@Enclosure.Real.IsNear.recentre' qz276 Bool.false 349380901 33554432 33 33554432 349380901 33554432 33 33554432 (Ns336p2376 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns336p2390 := @Enclosure.Real.IsNear.recentre' qz279 Bool.false 12235407958649928045455 4722366482869645213696 Ns336p2386 Ns336p304 43468901 16777216 13 2097152 (@Ns336p2387 Ns336p304 RS337to348.d47 (Ns336p2389 rfl rfl) rfl) 

noncomputable def Ns336p2391 := nat_lit 2466576369429420957499392 

noncomputable def Ns336p2392 := nat_lit 1629430076129849017081455688365032048199348755128852700726047361464948082473032096235237345 

noncomputable def Ns336p2393 := nat_lit 583388807765108851900502801537967121168514472783440227672659864953084433744215622397921 

noncomputable def Ns336p2394 := nat_lit 4266610427032270582786449798324974846135450097143441027247225449769701888822355331513167841 

noncomputable def Ns336p2395 := BSN.sin_dyadic_bound_f 70104316859 68719476736 3 2 33554432 9689454 Ns336p2392 Ns336p1224 Ns336p2393 Ns336p2394 Ns336p1227 Ns336p2393 28594670 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 70104316859) qz366 0 2 Ns336p2392 Ns336p1224 Ns336p2393 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 70104316859) qz367 0 2 Ns336p2394 Ns336p1227 Ns336p2393 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2396 := @Ns336p2385 4840000 (Ns336p2390 rfl) (Enclosure.sfrac_false_div 43468901 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43468901) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns336p2391) qz635) 226375608064910080 72057594037927936 Bool.false 28594670 33554432 0 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q1 43468901 16777216 226375608064910080 72057594037927936 0 Ns336p2391 Ns336p110 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 28594670 33554432 Ns336p2391 Ns336p110 70104316859 68719476736 9689454 9680000 (Ns336p2395 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns336p2397 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz277) 14297335 16777216 1015893 158597120000 19687085 19687382 16777216 (@Enclosure.Real.IsNear.neg qz277 Bool.true 14297335 16777216 1015893 158597120000 (Ns336p2384 (Ns336p2396 rfl rfl) rfl)) 

noncomputable def Ns336p2398 := Ns336p2382 (@Enclosure.Real.IsNear.neg qz788 Bool.false 39374467 33554432 297 33554432 (@Ns336p2383 297 33554432 (Ns336p2397 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns336p2399 := @Enclosure.Real.IsNear.recentre' qz278 Bool.true 5665186 16777216 

noncomputable abbrev qz280 := (@HMul.hMul Real Real Real qz349 qz346 qz604)

noncomputable def Ns336p2400 := @Enclosure.Real.IsNear.cos_image qz280 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 64264729)) qz396) Bool.true 64264729 33554432 

noncomputable def Ns336p2401 := nat_lit 303481604380931211242970512725 

noncomputable def Ns336p2402 := nat_lit 54525680861129135489940019955199437 

noncomputable def Ns336p2403 := @Enclosure.Real.IsNear.recentre' qz280 Bool.true Ns336p2401 Ns336p194 Ns336p2402 

noncomputable abbrev qz281 := qz604

noncomputable def Ns336p2404 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz281 884279719003555 140737488355328 1 500000000000000 343196386685095 

noncomputable abbrev qz605 := (@HSub.hSub Real Real Real qz631 qz787 qz781)

noncomputable abbrev qz282 := qz605

noncomputable def Ns336p2405 := @Enclosure.Real.IsNear.subLit_tf qz282 qz26 272827642507431 1125899906842624 2020511691 1125899906842624 1 16 

noncomputable abbrev qz606 := qz787

noncomputable abbrev qz283 := qz606

noncomputable def Ns336p2406 := @Enclosure.Real.IsNear.subLit_ff_n qz283 qz273 191450973769561 1125899906842624 913215435 1125899906842624 13836581 33554432 33 33554432 

noncomputable def Ns336p2407 := @Enclosure.Real.IsNear.mulLit_ff qz273 qz273 13836581 33554432 33 33554432 13836581 33554432 33 33554432 191450973769561 1125899906842624 

noncomputable def Ns336p2408 := nat_lit 551421789714682063535738400656059237171610564128301722539732022560181972756464355927457909253858721 

noncomputable def Ns336p2409 := nat_lit 4962176022737276360272908111151173759485403063069415644954161501971312110450821377958862644641 

noncomputable def Ns336p2410 := nat_lit 3327547350863410963305021093943562922209538262329494281277229009269185685284087167925053009812252065 

noncomputable def Ns336p2411 := BSN.cos_dyadic_bound_t 64264729 33554432 4 3 16777216 4840000 Ns336p2408 Ns336p328 Ns336p2409 Ns336p2410 Ns336p331 Ns336p2409 5665186 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 64264729) (BSN.cosEvenQ 33554432) 0 3 Ns336p2408 Ns336p328 Ns336p2409 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 64264729) (BSN.cosOddQ 33554432) 0 3 Ns336p2410 Ns336p331 Ns336p2409 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns336p2412 := @Ns336p2399 1867914432 162403450880000 2832593 8388608 29186163 2537553920000 (@Ns336p2400 379 33554432 Bool.true 5665186 16777216 1 4840000 (@Ns336p2403 Ns336p197 64264729 33554432 379 33554432 (@Ns336p2404 1125899906842624 2020511691 1125899906842624 Ns336p2401 Ns336p194 Ns336p2402 Ns336p197 RS337to348.d47 (@Ns336p2405 0 1 5491142186961520 343196386685095 1125899906842624 2020511691 1125899906842624 (@Ns336p2406 9154576578235902984192 272827642507431 1125899906842624 2020511691 1125899906842624 (@Ns336p2407 913215435 1125899906842624 (Ns336p2389 rfl rfl) (Ns336p2389 rfl rfl) rfl) (Ns336p2389 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 64264729 33554432) (BSN.cos_neg_of_bound 64264729 33554432 Bool.true 5665186 16777216 1 4840000 (Ns336p2411 rfl rfl)) rfl rfl) 

noncomputable def Ns336p2413 := @Ns336p2374 66500530151177623241 Ns336p2292 (Ns336p2375 qz28 (@Enclosure.Real.IsNear.of_eq qz602 (@Inv.inv Real Real.instInv (Real.sqrt qz276)) Bool.false 10398609 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz272 (BSN.t_div_two_pi_nonneg qz271 681206 1000 (@Eq.refl Real qz271))) Ns336p2379) rfl) (@Ns336p2380 281474976710656 15950971781739 967570232442880000 (BSN.correction_mk qz273 (BSN.cos_two_pi_p_ne_zero_mk qz271 681206 1000 10 (@Eq.refl Real qz271) rfl rfl (@BSN.floor_sqrt_eq_dec qz271 681206 1000 10 (@Eq.refl Real qz271) rfl rfl rfl))) (@Ns336p2381 33554432 2832593 8388608 29186163 2537553920000 111531839602931 281474976710656 15950971781739 967570232442880000 Ns336p2398 (Ns336p2412 rfl) rfl)) 

noncomputable def Ns336p2414 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz271) (hardyZApproximantRS₀ qz271) Bool.true 38408337081059330955939 9444732965739290427392 16219601775668837783241 Ns336p2292 (@Eq.refl Real (hardyZApproximantRS₀ qz271)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz271) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz271) qz271 10) (@HMul.hMul Real Real Real qz5 qz599 (Zeta.RiemannSiegel.correction qz273))) Bool.true 38408337081059330955939 9444732965739290427392 16219601775668837783241 Ns336p2292 (BSN.hardyZApproximantRS₀_eq qz271 10 (@BSN.floor_sqrt_eq_dec qz271 681206 1000 10 (@Eq.refl Real qz271) rfl rfl rfl)) (@Ns336p2294 38408337081059330955939 9444732965739290427392 16219601775668837783241 Ns336p2292 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz271) qz271 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz271) qz271 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz271) qz271 10)) Bool.true 264666945 67108864 166945 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz271) qz271 10) (Ns336p2373 (Ns336p2372 rfl rfl rfl rfl) rfl rfl)) (Ns336p2413 rfl) rfl rfl)) 

theorem RS337to348.d76 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz271) Bool.true 38408337081059330955939 9444732965739290427392 16219601775668837783241 Ns336p2292 := Ns336p2414 

noncomputable def RS337to348.d77 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz284 := (RS337to348.d3 qz348 qz385 (@Enclosure.dec_le_dec qz348 qz385 664401 1000 665749 1000 (@Eq.refl Real qz348) qz389 rfl rfl rfl))

noncomputable abbrev qz789 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz284)

noncomputable def Ns336p2415 := @Enclosure.Real.IsNear.of_eq qz789 (hardyZApproximantRS₀ qz4) Bool.true 747709838712106827405 1180591620717411303424 128062946251283975273 103892062623132194701312 

noncomputable abbrev qz285 := (@Enclosure.dec_le_dec qz348 qz385 664401 1000 665749 1000 (@Eq.refl Real qz348) qz389 rfl rfl rfl)

noncomputable def Ns336p2416 := @Enclosure.Real.IsNear.neg_val qz789 747709838712106827405 1180591620717411303424 128062946251283975273 103892062623132194701312 (Ns336p2415 (RS337to348.d4 qz4 qz29 qz285) RS337to348.d49) rfl 

noncomputable abbrev qz790 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz284)

noncomputable def Ns336p2417 := @Enclosure.Real.IsNear.of_eq qz790 (hardyZApproximantRS₀ qz29) Bool.false 227956996110923737789 295147905179352825856 8790033860248251543267 Ns336p211 

noncomputable def Ns336p2418 := @Enclosure.Real.IsNear.pos_val qz790 227956996110923737789 295147905179352825856 8790033860248251543267 Ns336p211 (Ns336p2417 (RS337to348.d50 qz4 qz29 qz285) RS337to348.d51) rfl 

noncomputable def Ns336p2419 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz789 qz4 qz4 664401 1000 664401 1000 

noncomputable def Ns336p2420 := @Enclosure.norm_gt_of_isNear qz789 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 747709838712106827405 1180591620717411303424 128062946251283975273 

noncomputable def Ns336p2421 := @Ns336p2420 103892062623132194701312 62121705 1073741824 1213 5368709120 (Ns336p2415 (RS337to348.d4 qz4 qz29 qz285) RS337to348.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS337to348.d52) rfl rfl rfl rfl 

noncomputable def Ns336p2422 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz790 qz4 qz29 664401 1000 665749 1000 

noncomputable def Ns336p2423 := @Enclosure.norm_gt_of_isNear qz790 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 227956996110923737789 295147905179352825856 8790033860248251543267 

noncomputable def Ns336p2424 := @Ns336p2423 Ns336p211 62121705 1073741824 1213 5368709120 (Ns336p2417 (RS337to348.d50 qz4 qz29 qz285) RS337to348.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS337to348.d52) rfl rfl rfl rfl 

noncomputable def Ns336p2425 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz4 664401 1000 qz10 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz789 qz790 (Ns336p2416 rfl rfl) (Ns336p2418 rfl rfl)) (Ns336p2419 qz10 qz10 rfl rfl rfl rfl (Ns336p2421 rfl)) (Ns336p2422 qz10 qz32 rfl rfl rfl rfl (Ns336p2424 rfl)) 

noncomputable abbrev qz286 := (RS337to348.d3 qz385 qz405 (@Enclosure.dec_le_dec qz385 qz405 665749 1000 667096 1000 qz389 qz409 rfl rfl rfl))

noncomputable abbrev qz791 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz286)

noncomputable def Ns336p2426 := @Enclosure.Real.IsNear.of_eq qz791 (hardyZApproximantRS₀ qz29) Bool.false 227956996110923737789 295147905179352825856 8790033860248251543267 Ns336p211 

noncomputable abbrev qz287 := (@Enclosure.dec_le_dec qz385 qz405 665749 1000 667096 1000 qz389 qz409 rfl rfl rfl)

noncomputable def Ns336p2427 := @Enclosure.Real.IsNear.pos_val qz791 227956996110923737789 295147905179352825856 8790033860248251543267 Ns336p211 (Ns336p2426 (RS337to348.d4 qz29 qz53 qz287) RS337to348.d51) rfl 

noncomputable abbrev qz792 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz286)

noncomputable def Ns336p2428 := @Enclosure.Real.IsNear.of_eq qz792 (hardyZApproximantRS₀ qz53) Bool.true 974139618243823387003 9444732965739290427392 7264727013817793342341 Ns336p369 

noncomputable def Ns336p2429 := @Enclosure.Real.IsNear.neg_val qz792 974139618243823387003 9444732965739290427392 7264727013817793342341 Ns336p369 (Ns336p2428 (RS337to348.d50 qz29 qz53 qz287) RS337to348.d53) rfl 

noncomputable def Ns336p2430 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz791 qz4 qz29 664401 1000 665749 1000 

noncomputable def Ns336p2431 := @Enclosure.norm_gt_of_isNear qz791 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 227956996110923737789 295147905179352825856 8790033860248251543267 

noncomputable def Ns336p2432 := @Ns336p2431 Ns336p211 62121705 1073741824 1213 5368709120 (Ns336p2426 (RS337to348.d4 qz29 qz53 qz287) RS337to348.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS337to348.d52) rfl rfl rfl rfl 

noncomputable def Ns336p2433 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz792 qz4 qz53 664401 1000 667096 1000 

noncomputable def Ns336p2434 := @Enclosure.norm_gt_of_isNear qz792 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 974139618243823387003 9444732965739290427392 7264727013817793342341 

noncomputable def Ns336p2435 := @Ns336p2434 Ns336p369 62121705 1073741824 1213 5368709120 (Ns336p2428 (RS337to348.d50 qz29 qz53 qz287) RS337to348.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS337to348.d52) rfl rfl rfl rfl 

noncomputable def Ns336p2436 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz286 (@BSN.thirtyTwoPi_le_dec qz29 665749 1000 qz32 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz791 qz792 (Ns336p2427 rfl rfl) (Ns336p2429 rfl rfl)) (Ns336p2430 qz10 qz32 rfl rfl rfl rfl (Ns336p2432 rfl)) (Ns336p2433 qz10 qz56 rfl rfl rfl rfl (Ns336p2435 rfl)) 

noncomputable abbrev qz288 := (RS337to348.d3 qz405 qz419 (@Enclosure.dec_le_dec qz405 qz419 667096 1000 668442 1000 qz409 qz423 rfl rfl rfl))

noncomputable abbrev qz793 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz288)

noncomputable def Ns336p2437 := @Enclosure.Real.IsNear.of_eq qz793 (hardyZApproximantRS₀ qz53) Bool.true 974139618243823387003 9444732965739290427392 7264727013817793342341 Ns336p369 

noncomputable abbrev qz289 := (@Enclosure.dec_le_dec qz405 qz419 667096 1000 668442 1000 qz409 qz423 rfl rfl rfl)

noncomputable def Ns336p2438 := @Enclosure.Real.IsNear.neg_val qz793 974139618243823387003 9444732965739290427392 7264727013817793342341 Ns336p369 (Ns336p2437 (RS337to348.d4 qz53 qz67 qz289) RS337to348.d53) rfl 

noncomputable abbrev qz794 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz288)

noncomputable def Ns336p2439 := @Enclosure.Real.IsNear.of_eq qz794 (hardyZApproximantRS₀ qz67) Bool.false 1577918753636171020447 590295810358705651712 17584938131667578835411 Ns336p486 

noncomputable def Ns336p2440 := @Enclosure.Real.IsNear.pos_val qz794 1577918753636171020447 590295810358705651712 17584938131667578835411 Ns336p486 (Ns336p2439 (RS337to348.d50 qz53 qz67 qz289) RS337to348.d54) rfl 

noncomputable def Ns336p2441 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz793 qz4 qz53 664401 1000 667096 1000 

noncomputable def Ns336p2442 := @Enclosure.norm_gt_of_isNear qz793 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 974139618243823387003 9444732965739290427392 7264727013817793342341 

noncomputable def Ns336p2443 := @Ns336p2442 Ns336p369 62121705 1073741824 1213 5368709120 (Ns336p2437 (RS337to348.d4 qz53 qz67 qz289) RS337to348.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS337to348.d52) rfl rfl rfl rfl 

noncomputable def Ns336p2444 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz794 qz4 qz67 664401 1000 668442 1000 

noncomputable def Ns336p2445 := @Enclosure.norm_gt_of_isNear qz794 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1577918753636171020447 590295810358705651712 17584938131667578835411 

noncomputable def Ns336p2446 := @Ns336p2445 Ns336p486 62121705 1073741824 1213 5368709120 (Ns336p2439 (RS337to348.d50 qz53 qz67 qz289) RS337to348.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS337to348.d52) rfl rfl rfl rfl 

noncomputable def Ns336p2447 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz53 667096 1000 qz56 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz793 qz794 (Ns336p2438 rfl rfl) (Ns336p2440 rfl rfl)) (Ns336p2441 qz10 qz56 rfl rfl rfl rfl (Ns336p2443 rfl)) (Ns336p2444 qz10 qz70 rfl rfl rfl rfl (Ns336p2446 rfl)) 

noncomputable abbrev qz290 := (RS337to348.d3 qz419 qz432 (@Enclosure.dec_le_dec qz419 qz432 668442 1000 669788 1000 qz423 qz436 rfl rfl rfl))

noncomputable abbrev qz795 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz290)

noncomputable def Ns336p2448 := @Enclosure.Real.IsNear.of_eq qz795 (hardyZApproximantRS₀ qz67) Bool.false 1577918753636171020447 590295810358705651712 17584938131667578835411 Ns336p486 

noncomputable abbrev qz291 := (@Enclosure.dec_le_dec qz419 qz432 668442 1000 669788 1000 qz423 qz436 rfl rfl rfl)

noncomputable def Ns336p2449 := @Enclosure.Real.IsNear.pos_val qz795 1577918753636171020447 590295810358705651712 17584938131667578835411 Ns336p486 (Ns336p2448 (RS337to348.d4 qz67 qz81 qz291) RS337to348.d54) rfl 

noncomputable abbrev qz796 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz290)

noncomputable def Ns336p2450 := @Enclosure.Real.IsNear.of_eq qz796 (hardyZApproximantRS₀ qz81) Bool.true 3240794453982130537235 1180591620717411303424 10002632257582300977887 Ns336p598 

noncomputable def Ns336p2451 := @Enclosure.Real.IsNear.neg_val qz796 3240794453982130537235 1180591620717411303424 10002632257582300977887 Ns336p598 (Ns336p2450 (RS337to348.d50 qz67 qz81 qz291) RS337to348.d55) rfl 

noncomputable def Ns336p2452 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz795 qz4 qz67 664401 1000 668442 1000 

noncomputable def Ns336p2453 := @Enclosure.norm_gt_of_isNear qz795 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1577918753636171020447 590295810358705651712 17584938131667578835411 

noncomputable def Ns336p2454 := @Ns336p2453 Ns336p486 62121705 1073741824 1213 5368709120 (Ns336p2448 (RS337to348.d4 qz67 qz81 qz291) RS337to348.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS337to348.d52) rfl rfl rfl rfl 

noncomputable def Ns336p2455 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz796 qz4 qz81 664401 1000 669788 1000 

noncomputable def Ns336p2456 := @Enclosure.norm_gt_of_isNear qz796 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 3240794453982130537235 1180591620717411303424 10002632257582300977887 

noncomputable def Ns336p2457 := @Ns336p2456 Ns336p598 62121705 1073741824 1213 5368709120 (Ns336p2450 (RS337to348.d50 qz67 qz81 qz291) RS337to348.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS337to348.d52) rfl rfl rfl rfl 

noncomputable def Ns336p2458 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz290 (@BSN.thirtyTwoPi_le_dec qz67 668442 1000 qz70 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz795 qz796 (Ns336p2449 rfl rfl) (Ns336p2451 rfl rfl)) (Ns336p2452 qz10 qz70 rfl rfl rfl rfl (Ns336p2454 rfl)) (Ns336p2455 qz10 qz84 rfl rfl rfl rfl (Ns336p2457 rfl)) 

noncomputable abbrev qz292 := (RS337to348.d3 qz432 qz445 (@Enclosure.dec_le_dec qz432 qz445 669788 1000 671134 1000 qz436 qz449 rfl rfl rfl))

noncomputable abbrev qz797 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz292)

noncomputable def Ns336p2459 := @Enclosure.Real.IsNear.of_eq qz797 (hardyZApproximantRS₀ qz81) Bool.true 3240794453982130537235 1180591620717411303424 10002632257582300977887 Ns336p598 

noncomputable abbrev qz293 := (@Enclosure.dec_le_dec qz432 qz445 669788 1000 671134 1000 qz436 qz449 rfl rfl rfl)

noncomputable def Ns336p2460 := @Enclosure.Real.IsNear.neg_val qz797 3240794453982130537235 1180591620717411303424 10002632257582300977887 Ns336p598 (Ns336p2459 (RS337to348.d4 qz81 qz95 qz293) RS337to348.d55) rfl 

noncomputable abbrev qz798 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz292)

noncomputable def Ns336p2461 := @Enclosure.Real.IsNear.of_eq qz798 (hardyZApproximantRS₀ qz95) Bool.false 46880110908428902521459 9444732965739290427392 881114268925298211258603 Ns336p723 

noncomputable def Ns336p2462 := @Enclosure.Real.IsNear.pos_val qz798 46880110908428902521459 9444732965739290427392 881114268925298211258603 Ns336p723 (Ns336p2461 (RS337to348.d50 qz81 qz95 qz293) RS337to348.d56) rfl 

noncomputable def Ns336p2463 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz797 qz4 qz81 664401 1000 669788 1000 

noncomputable def Ns336p2464 := @Enclosure.norm_gt_of_isNear qz797 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 3240794453982130537235 1180591620717411303424 10002632257582300977887 

noncomputable def Ns336p2465 := @Ns336p2464 Ns336p598 62121705 1073741824 1213 5368709120 (Ns336p2459 (RS337to348.d4 qz81 qz95 qz293) RS337to348.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS337to348.d52) rfl rfl rfl rfl 

noncomputable def Ns336p2466 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz798 qz4 qz95 664401 1000 671134 1000 

noncomputable def Ns336p2467 := @Enclosure.norm_gt_of_isNear qz798 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 46880110908428902521459 9444732965739290427392 881114268925298211258603 

noncomputable def Ns336p2468 := @Ns336p2467 Ns336p723 62121705 1073741824 1213 5368709120 (Ns336p2461 (RS337to348.d50 qz81 qz95 qz293) RS337to348.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS337to348.d52) rfl rfl rfl rfl 

noncomputable def Ns336p2469 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz81 669788 1000 qz84 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz797 qz798 (Ns336p2460 rfl rfl) (Ns336p2462 rfl rfl)) (Ns336p2463 qz10 qz84 rfl rfl rfl rfl (Ns336p2465 rfl)) (Ns336p2466 qz10 qz98 rfl rfl rfl rfl (Ns336p2468 rfl)) 

noncomputable abbrev qz294 := (RS337to348.d3 qz445 qz485 (@Enclosure.dec_le_dec qz445 qz485 671134 1000 672479 1000 qz449 qz491 rfl rfl rfl))

noncomputable abbrev qz799 := (Zeta.Certificates.ZIntervalRS.fstVal qz294)

noncomputable def Ns336p2470 := @Enclosure.Real.IsNear.of_eq qz799 (hardyZApproximantRS qz95) Bool.false Ns336p865 Ns336p866 Ns336p867 Ns336p868 

noncomputable abbrev qz295 := (@Enclosure.dec_le_dec qz445 qz485 671134 1000 672479 1000 qz449 qz491 rfl rfl rfl)

noncomputable def Ns336p2471 := @Enclosure.Real.IsNear.pos_val qz799 Ns336p865 Ns336p866 Ns336p867 Ns336p868 (Ns336p2470 (RS337to348.d57 qz95 qz138 qz295) RS337to348.d66) rfl 

noncomputable abbrev qz800 := (Zeta.Certificates.ZIntervalRS.sndVal qz294)

noncomputable def Ns336p2472 := @Enclosure.Real.IsNear.of_eq qz800 (hardyZApproximantRS qz138) Bool.true Ns336p1115 Ns336p1116 Ns336p1117 Ns336p1118 

noncomputable def Ns336p2473 := @Enclosure.Real.IsNear.neg_val qz800 Ns336p1115 Ns336p1116 Ns336p1117 Ns336p1118 (Ns336p2472 (RS337to348.d67 qz95 qz138 qz295) RS337to348.d68) rfl 

noncomputable def Ns336p2474 := BSN.norm_gt_hardyZErrorBoundRS_of_le qz799 qz4 qz95 664401 1000 671134 1000 

noncomputable def Ns336p2475 := @Enclosure.norm_gt_of_isNear qz799 (hardyZErrorBoundRS qz4) Bool.false Bool.false Ns336p865 Ns336p866 Ns336p867 

noncomputable def Ns336p2476 := @Ns336p2475 Ns336p868 19791001 1073741824 201 1073741824 (Ns336p2470 (RS337to348.d57 qz95 qz138 qz295) RS337to348.d66) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) (hardyZErrorBoundRS qz4) Bool.false 19791001 1073741824 201 1073741824 (@Eq.refl Real (hardyZErrorBoundRS qz4)) RS337to348.d69) rfl rfl rfl rfl 

noncomputable def Ns336p2477 := BSN.norm_gt_hardyZErrorBoundRS_of_le qz800 qz4 qz138 664401 1000 672479 1000 

noncomputable def Ns336p2478 := @Enclosure.norm_gt_of_isNear qz800 (hardyZErrorBoundRS qz4) Bool.true Bool.false Ns336p1115 Ns336p1116 Ns336p1117 

noncomputable def Ns336p2479 := @Ns336p2478 Ns336p1118 19791001 1073741824 201 1073741824 (Ns336p2472 (RS337to348.d67 qz95 qz138 qz295) RS337to348.d68) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) (hardyZErrorBoundRS qz4) Bool.false 19791001 1073741824 201 1073741824 (@Eq.refl Real (hardyZErrorBoundRS qz4)) RS337to348.d69) rfl rfl rfl rfl 

noncomputable def Ns336p2480 := @Zeta.Certificates.ZIntervalRS.Certificate.mk qz294 (@BSN.thirtyTwoPi_le_dec qz95 671134 1000 qz98 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz799 qz800 (Ns336p2471 rfl rfl) (Ns336p2473 rfl rfl)) (Ns336p2474 qz10 qz98 rfl rfl rfl rfl (Ns336p2476 rfl)) (Ns336p2477 qz10 qz143 rfl rfl rfl rfl (Ns336p2479 rfl)) 

noncomputable abbrev qz296 := (RS337to348.d3 qz485 qz520 (@Enclosure.dec_le_dec qz485 qz520 672479 1000 673823 1000 qz491 qz525 rfl rfl rfl))

noncomputable abbrev qz801 := (Zeta.Certificates.ZIntervalRS.fstVal qz296)

noncomputable def Ns336p2481 := @Enclosure.Real.IsNear.of_eq qz801 (hardyZApproximantRS qz138) Bool.true Ns336p1115 Ns336p1116 Ns336p1117 Ns336p1118 

noncomputable abbrev qz297 := (@Enclosure.dec_le_dec qz485 qz520 672479 1000 673823 1000 qz491 qz525 rfl rfl rfl)

noncomputable def Ns336p2482 := @Enclosure.Real.IsNear.neg_val qz801 Ns336p1115 Ns336p1116 Ns336p1117 Ns336p1118 (Ns336p2481 (RS337to348.d57 qz138 qz175 qz297) RS337to348.d68) rfl 

noncomputable abbrev qz802 := (Zeta.Certificates.ZIntervalRS.sndVal qz296)

noncomputable def Ns336p2483 := @Enclosure.Real.IsNear.of_eq qz802 (hardyZApproximantRS qz175) Bool.false Ns336p1464 Ns336p1465 Ns336p1466 Ns336p1467 

noncomputable def Ns336p2484 := @Enclosure.Real.IsNear.pos_val qz802 Ns336p1464 Ns336p1465 Ns336p1466 Ns336p1467 (Ns336p2483 (RS337to348.d67 qz138 qz175 qz297) RS337to348.d70) rfl 

noncomputable def Ns336p2485 := BSN.norm_gt_hardyZErrorBoundRS_of_le qz801 qz4 qz138 664401 1000 672479 1000 

noncomputable def Ns336p2486 := @Enclosure.norm_gt_of_isNear qz801 (hardyZErrorBoundRS qz4) Bool.true Bool.false Ns336p1115 Ns336p1116 Ns336p1117 

noncomputable def Ns336p2487 := @Ns336p2486 Ns336p1118 19791001 1073741824 201 1073741824 (Ns336p2481 (RS337to348.d57 qz138 qz175 qz297) RS337to348.d68) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) (hardyZErrorBoundRS qz4) Bool.false 19791001 1073741824 201 1073741824 (@Eq.refl Real (hardyZErrorBoundRS qz4)) RS337to348.d69) rfl rfl rfl rfl 

noncomputable def Ns336p2488 := BSN.norm_gt_hardyZErrorBoundRS_of_le qz802 qz4 qz175 664401 1000 673823 1000 

noncomputable def Ns336p2489 := @Enclosure.norm_gt_of_isNear qz802 (hardyZErrorBoundRS qz4) Bool.false Bool.false Ns336p1464 Ns336p1465 Ns336p1466 

noncomputable def Ns336p2490 := @Ns336p2489 Ns336p1467 19791001 1073741824 201 1073741824 (Ns336p2483 (RS337to348.d67 qz138 qz175 qz297) RS337to348.d70) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) (hardyZErrorBoundRS qz4) Bool.false 19791001 1073741824 201 1073741824 (@Eq.refl Real (hardyZErrorBoundRS qz4)) RS337to348.d69) rfl rfl rfl rfl 

noncomputable def Ns336p2491 := @Zeta.Certificates.ZIntervalRS.Certificate.mk qz296 (@BSN.thirtyTwoPi_le_dec qz138 672479 1000 qz143 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz801 qz802 (Ns336p2482 rfl rfl) (Ns336p2484 rfl rfl)) (Ns336p2485 qz10 qz143 rfl rfl rfl rfl (Ns336p2487 rfl)) (Ns336p2488 qz10 qz180 rfl rfl rfl rfl (Ns336p2490 rfl)) 

noncomputable abbrev qz607 := (@Enclosure.dec_le_dec qz720 qz736 673823 1000 675167 1000 (@Eq.refl Real qz720) (@Eq.refl Real qz736) rfl rfl rfl)

noncomputable abbrev qz298 := (RS337to348.d3 qz520 qz548 qz607)

noncomputable abbrev qz803 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz298)

noncomputable def Ns336p2492 := @Enclosure.Real.IsNear.of_eq qz803 (hardyZApproximantRS₀ qz175) Bool.false 27008824244221298769595 18889465931478580854784 Ns336p1811 Ns336p1812 

noncomputable abbrev qz299 := qz607

noncomputable def Ns336p2493 := @Enclosure.Real.IsNear.pos_val qz803 27008824244221298769595 18889465931478580854784 Ns336p1811 Ns336p1812 (Ns336p2492 (RS337to348.d4 qz175 qz215 qz299) RS337to348.d71) rfl 

noncomputable abbrev qz804 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz298)

noncomputable def Ns336p2494 := @Enclosure.Real.IsNear.of_eq qz804 (hardyZApproximantRS₀ qz215) Bool.true 6459837078810469172183 2361183241434822606848 44255133458897593758827 Ns336p1818 

noncomputable def Ns336p2495 := @Enclosure.Real.IsNear.neg_val qz804 6459837078810469172183 2361183241434822606848 44255133458897593758827 Ns336p1818 (Ns336p2494 (RS337to348.d50 qz175 qz215 qz299) RS337to348.d72) rfl 

noncomputable def Ns336p2496 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz803 qz4 qz175 664401 1000 673823 1000 

noncomputable def Ns336p2497 := @Enclosure.norm_gt_of_isNear qz803 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 27008824244221298769595 18889465931478580854784 Ns336p1811 

noncomputable def Ns336p2498 := @Ns336p2497 Ns336p1812 62121705 1073741824 1213 5368709120 (Ns336p2492 (RS337to348.d4 qz175 qz215 qz299) RS337to348.d71) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS337to348.d52) rfl rfl rfl rfl 

noncomputable def Ns336p2499 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz804 qz4 qz215 664401 1000 675167 1000 

noncomputable def Ns336p2500 := @Enclosure.norm_gt_of_isNear qz804 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 6459837078810469172183 2361183241434822606848 44255133458897593758827 

noncomputable def Ns336p2501 := @Ns336p2500 Ns336p1818 62121705 1073741824 1213 5368709120 (Ns336p2494 (RS337to348.d50 qz175 qz215 qz299) RS337to348.d72) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS337to348.d52) rfl rfl rfl rfl 

noncomputable def Ns336p2502 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz298 (@BSN.thirtyTwoPi_le_dec qz175 673823 1000 qz180 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz803 qz804 (Ns336p2493 rfl rfl) (Ns336p2495 rfl rfl)) (Ns336p2496 qz10 qz180 rfl rfl rfl rfl (Ns336p2498 rfl)) (Ns336p2499 qz10 qz218 rfl rfl rfl rfl (Ns336p2501 rfl)) 

noncomputable abbrev qz608 := (@Enclosure.dec_le_dec qz736 qz746 675167 1000 676845 1000 (@Eq.refl Real qz736) qz749 rfl rfl rfl)

noncomputable abbrev qz300 := (RS337to348.d3 qz548 qz560 qz608)

noncomputable abbrev qz805 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz300)

noncomputable def Ns336p2503 := @Enclosure.Real.IsNear.of_eq qz805 (hardyZApproximantRS₀ qz215) Bool.true 6459837078810469172183 2361183241434822606848 44255133458897593758827 Ns336p1818 

noncomputable abbrev qz301 := qz608

noncomputable def Ns336p2504 := @Enclosure.Real.IsNear.neg_val qz805 6459837078810469172183 2361183241434822606848 44255133458897593758827 Ns336p1818 (Ns336p2503 (RS337to348.d4 qz215 qz229 qz301) RS337to348.d72) rfl 

noncomputable abbrev qz806 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz300)

noncomputable def Ns336p2505 := @Enclosure.Real.IsNear.of_eq qz806 (hardyZApproximantRS₀ qz229) Bool.false 1666410313854854695851 2361183241434822606848 8870781470545668732579 Ns336p211 

noncomputable def Ns336p2506 := @Enclosure.Real.IsNear.pos_val qz806 1666410313854854695851 2361183241434822606848 8870781470545668732579 Ns336p211 (Ns336p2505 (RS337to348.d50 qz215 qz229 qz301) RS337to348.d73) rfl 

noncomputable def Ns336p2507 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz805 qz4 qz215 664401 1000 675167 1000 

noncomputable def Ns336p2508 := @Enclosure.norm_gt_of_isNear qz805 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 6459837078810469172183 2361183241434822606848 44255133458897593758827 

noncomputable def Ns336p2509 := @Ns336p2508 Ns336p1818 62121705 1073741824 1213 5368709120 (Ns336p2503 (RS337to348.d4 qz215 qz229 qz301) RS337to348.d72) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS337to348.d52) rfl rfl rfl rfl 

noncomputable def Ns336p2510 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz806 qz4 qz229 664401 1000 676845 1000 

noncomputable def Ns336p2511 := @Enclosure.norm_gt_of_isNear qz806 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1666410313854854695851 2361183241434822606848 8870781470545668732579 

noncomputable def Ns336p2512 := @Ns336p2511 Ns336p211 62121705 1073741824 1213 5368709120 (Ns336p2505 (RS337to348.d50 qz215 qz229 qz301) RS337to348.d73) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS337to348.d52) rfl rfl rfl rfl 

noncomputable def Ns336p2513 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz215 675167 1000 qz218 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz805 qz806 (Ns336p2504 rfl rfl) (Ns336p2506 rfl rfl)) (Ns336p2507 qz10 qz218 rfl rfl rfl rfl (Ns336p2509 rfl)) (Ns336p2510 qz10 qz232 rfl rfl rfl rfl (Ns336p2512 rfl)) 

noncomputable abbrev qz807 := (@Enclosure.dec_le_dec qz869 qz873 676845 1000 677517 1000 (@Eq.refl Real qz869) qz876 rfl rfl rfl)

noncomputable abbrev qz609 := qz807

noncomputable abbrev qz302 := (RS337to348.d3 qz560 qz572 qz609)

noncomputable abbrev qz808 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz302)

noncomputable def Ns336p2514 := @Enclosure.Real.IsNear.of_eq qz808 (hardyZApproximantRS₀ qz229) Bool.false 1666410313854854695851 2361183241434822606848 8870781470545668732579 Ns336p211 

noncomputable abbrev qz303 := qz609

noncomputable def Ns336p2515 := @Enclosure.Real.IsNear.pos_val qz808 1666410313854854695851 2361183241434822606848 8870781470545668732579 Ns336p211 (Ns336p2514 (RS337to348.d4 qz229 qz243 qz303) RS337to348.d73) rfl 

noncomputable abbrev qz809 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz302)

noncomputable def Ns336p2516 := @Enclosure.Real.IsNear.of_eq qz809 (hardyZApproximantRS₀ qz243) Bool.true 2890823408947213111793 9444732965739290427392 177543488492677923856571 Ns336p2051 

noncomputable def Ns336p2517 := @Enclosure.Real.IsNear.neg_val qz809 2890823408947213111793 9444732965739290427392 177543488492677923856571 Ns336p2051 (Ns336p2516 (RS337to348.d50 qz229 qz243 qz303) RS337to348.d74) rfl 

noncomputable def Ns336p2518 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz808 qz4 qz229 664401 1000 676845 1000 

noncomputable def Ns336p2519 := @Enclosure.norm_gt_of_isNear qz808 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1666410313854854695851 2361183241434822606848 8870781470545668732579 

noncomputable def Ns336p2520 := @Ns336p2519 Ns336p211 62121705 1073741824 1213 5368709120 (Ns336p2514 (RS337to348.d4 qz229 qz243 qz303) RS337to348.d73) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS337to348.d52) rfl rfl rfl rfl 

noncomputable def Ns336p2521 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz809 qz4 qz243 664401 1000 677517 1000 

noncomputable def Ns336p2522 := @Enclosure.norm_gt_of_isNear qz809 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2890823408947213111793 9444732965739290427392 177543488492677923856571 

noncomputable def Ns336p2523 := @Ns336p2522 Ns336p2051 62121705 1073741824 1213 5368709120 (Ns336p2516 (RS337to348.d50 qz229 qz243 qz303) RS337to348.d74) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS337to348.d52) rfl rfl rfl rfl 

noncomputable def Ns336p2524 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz302 (@BSN.thirtyTwoPi_le_dec qz229 676845 1000 qz232 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz808 qz809 (Ns336p2515 rfl rfl) (Ns336p2517 rfl rfl)) (Ns336p2518 qz10 qz232 rfl rfl rfl rfl (Ns336p2520 rfl)) (Ns336p2521 qz10 qz246 rfl rfl rfl rfl (Ns336p2523 rfl)) 

noncomputable abbrev qz810 := (@Enclosure.dec_le_dec qz873 qz878 677517 1000 678523 1000 qz876 qz881 rfl rfl rfl)

noncomputable abbrev qz610 := qz810

noncomputable abbrev qz304 := (RS337to348.d3 qz572 qz584 qz610)

noncomputable abbrev qz811 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz304)

noncomputable def Ns336p2525 := @Enclosure.Real.IsNear.of_eq qz811 (hardyZApproximantRS₀ qz243) Bool.true 2890823408947213111793 9444732965739290427392 177543488492677923856571 Ns336p2051 

noncomputable abbrev qz305 := qz610

noncomputable def Ns336p2526 := @Enclosure.Real.IsNear.neg_val qz811 2890823408947213111793 9444732965739290427392 177543488492677923856571 Ns336p2051 (Ns336p2525 (RS337to348.d4 qz243 qz257 qz305) RS337to348.d74) rfl 

noncomputable abbrev qz812 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz304)

noncomputable def Ns336p2527 := @Enclosure.Real.IsNear.of_eq qz812 (hardyZApproximantRS₀ qz257) Bool.false 15143051524684179030473 4722366482869645213696 444496552908291110551591 Ns336p2173 

noncomputable def Ns336p2528 := @Enclosure.Real.IsNear.pos_val qz812 15143051524684179030473 4722366482869645213696 444496552908291110551591 Ns336p2173 (Ns336p2527 (RS337to348.d50 qz243 qz257 qz305) RS337to348.d75) rfl 

noncomputable def Ns336p2529 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz811 qz4 qz243 664401 1000 677517 1000 

noncomputable def Ns336p2530 := @Enclosure.norm_gt_of_isNear qz811 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2890823408947213111793 9444732965739290427392 177543488492677923856571 

noncomputable def Ns336p2531 := @Ns336p2530 Ns336p2051 62121705 1073741824 1213 5368709120 (Ns336p2525 (RS337to348.d4 qz243 qz257 qz305) RS337to348.d74) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS337to348.d52) rfl rfl rfl rfl 

noncomputable def Ns336p2532 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz812 qz4 qz257 664401 1000 678523 1000 

noncomputable def Ns336p2533 := @Enclosure.norm_gt_of_isNear qz812 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 15143051524684179030473 4722366482869645213696 444496552908291110551591 

noncomputable def Ns336p2534 := @Ns336p2533 Ns336p2173 62121705 1073741824 1213 5368709120 (Ns336p2527 (RS337to348.d50 qz243 qz257 qz305) RS337to348.d75) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS337to348.d52) rfl rfl rfl rfl 

noncomputable def Ns336p2535 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz243 677517 1000 qz246 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz811 qz812 (Ns336p2526 rfl rfl) (Ns336p2528 rfl rfl)) (Ns336p2529 qz10 qz246 rfl rfl rfl rfl (Ns336p2531 rfl)) (Ns336p2532 qz10 qz260 rfl rfl rfl rfl (Ns336p2534 rfl)) 

noncomputable abbrev qz887 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 678523 1000) (Enclosure.sfrac Bool.false 681206 1000) 678523 1000 681206 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 678523 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 681206 1000)) rfl rfl rfl)

noncomputable abbrev qz813 := qz887

noncomputable abbrev qz611 := qz813

noncomputable abbrev qz306 := (RS337to348.d3 qz584 qz596 qz611)

noncomputable abbrev qz814 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz306)

noncomputable def Ns336p2536 := @Enclosure.Real.IsNear.of_eq qz814 (hardyZApproximantRS₀ qz257) Bool.false 15143051524684179030473 4722366482869645213696 444496552908291110551591 Ns336p2173 

noncomputable abbrev qz307 := qz611

noncomputable def Ns336p2537 := @Enclosure.Real.IsNear.pos_val qz814 15143051524684179030473 4722366482869645213696 444496552908291110551591 Ns336p2173 (Ns336p2536 (RS337to348.d4 qz257 qz271 qz307) RS337to348.d75) rfl 

noncomputable abbrev qz815 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz306)

noncomputable def Ns336p2538 := @Enclosure.Real.IsNear.of_eq qz815 (hardyZApproximantRS₀ qz271) Bool.true 38408337081059330955939 9444732965739290427392 16219601775668837783241 Ns336p2292 

noncomputable def Ns336p2539 := @Enclosure.Real.IsNear.neg_val qz815 38408337081059330955939 9444732965739290427392 16219601775668837783241 Ns336p2292 (Ns336p2538 (RS337to348.d50 qz257 qz271 qz307) RS337to348.d76) rfl 

noncomputable def Ns336p2540 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz814 qz4 qz257 664401 1000 678523 1000 

noncomputable def Ns336p2541 := @Enclosure.norm_gt_of_isNear qz814 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 15143051524684179030473 4722366482869645213696 444496552908291110551591 

noncomputable def Ns336p2542 := @Ns336p2541 Ns336p2173 62121705 1073741824 1213 5368709120 (Ns336p2536 (RS337to348.d4 qz257 qz271 qz307) RS337to348.d75) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS337to348.d52) rfl rfl rfl rfl 

noncomputable def Ns336p2543 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz815 qz4 qz271 664401 1000 681206 1000 

noncomputable def Ns336p2544 := @Enclosure.norm_gt_of_isNear qz815 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 38408337081059330955939 9444732965739290427392 16219601775668837783241 

noncomputable def Ns336p2545 := @Ns336p2544 Ns336p2292 62121705 1073741824 1213 5368709120 (Ns336p2538 (RS337to348.d50 qz257 qz271 qz307) RS337to348.d76) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 62121705 1073741824 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS337to348.d52) rfl rfl rfl rfl 

noncomputable def Ns336p2546 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz306 (@BSN.thirtyTwoPi_le_dec qz257 678523 1000 qz260 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz814 qz815 (Ns336p2537 rfl rfl) (Ns336p2539 rfl rfl)) (Ns336p2540 qz10 qz260 rfl rfl rfl rfl (Ns336p2542 rfl)) (Ns336p2543 qz10 (@Eq.refl Real qz271) rfl rfl rfl rfl (Ns336p2545 rfl)) 

noncomputable def Ns336p2547 := @List.cons RS337to348.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns336p2535)) (@List.cons RS337to348.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz306 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz306) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz306) Ns336p2546)) (@List.nil RS337to348.d0)) 

noncomputable def Ns336p2548 := @List.cons RS337to348.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns336p2513)) (@List.cons RS337to348.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz302 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz302) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz302) Ns336p2524)) Ns336p2547) 

noncomputable def Ns336p2549 := @List.cons RS337to348.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inl (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns336p2491)) (@List.cons RS337to348.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz298 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz298) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz298) Ns336p2502)) Ns336p2548) 

noncomputable def Ns336p2550 := @List.cons RS337to348.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns336p2469)) (@List.cons RS337to348.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz294 (@Or.inl (Zeta.Certificates.ZIntervalRS.Certificate qz294) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz294) Ns336p2480)) Ns336p2549) 

noncomputable def Ns336p2551 := @List.cons RS337to348.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns336p2447)) (@List.cons RS337to348.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz290 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz290) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz290) Ns336p2458)) Ns336p2550) 

noncomputable def Ns336p2552 := @List.cons RS337to348.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns336p2425)) (@List.cons RS337to348.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz286 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz286) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz286) Ns336p2436)) Ns336p2551) 

noncomputable abbrev qz816 := (RS337to348.d2 qz873 qz878 (@Enclosure.dec_le_dec qz873 qz878 677517 1000 678523 1000 qz876 qz881 rfl rfl rfl))

noncomputable abbrev qz817 := (@List.cons RS337to348.d1 (RS337to348.d2 qz878 qz883 qz887) (@List.nil RS337to348.d1))

noncomputable abbrev qz612 := (@List.cons RS337to348.d1 (RS337to348.d2 qz746 qz757 qz807) (@List.cons RS337to348.d1 qz816 qz817))

noncomputable abbrev qz308 := (@List.cons RS337to348.d1 (RS337to348.d2 qz520 qz548 qz607) (@List.cons RS337to348.d1 (RS337to348.d2 qz548 qz560 qz608) qz612))

noncomputable def Ns336p2553 := @List.cons RS337to348.d1 (RS337to348.d2 qz95 qz138 qz295) (@List.cons RS337to348.d1 (RS337to348.d2 qz138 qz175 qz297) qz308) 

noncomputable def Ns336p2554 := @List.IsChain.cons_cons RS337to348.d1 RS337to348.d77 (RS337to348.d2 qz81 qz95 qz293) (RS337to348.d2 qz95 qz138 qz295) (@List.cons RS337to348.d1 (RS337to348.d2 qz138 qz175 qz297) qz308) 

noncomputable def Ns336p2555 := @List.IsChain.cons_cons RS337to348.d1 RS337to348.d77 (RS337to348.d2 qz95 qz138 qz295) (RS337to348.d2 qz138 qz175 qz297) qz308 (@Enclosure.dec_le_dec qz138 qz138 672479 1000 672479 1000 qz143 qz143 rfl rfl rfl) 

noncomputable abbrev qz309 := qz612

noncomputable abbrev qz613 := (RS337to348.d2 qz746 qz757 qz807)

noncomputable abbrev qz310 := qz613

noncomputable abbrev qz614 := (@List.cons RS337to348.d1 qz816 qz817)

noncomputable abbrev qz311 := qz614

noncomputable abbrev qz615 := qz816

noncomputable abbrev qz312 := qz615

noncomputable abbrev qz616 := qz817

noncomputable abbrev qz313 := qz616

noncomputable abbrev qz818 := (RS337to348.d2 qz878 qz883 qz887)

noncomputable abbrev qz617 := qz818

noncomputable abbrev qz314 := qz617

noncomputable def Ns336p2556 := @List.IsChain.cons_cons RS337to348.d1 RS337to348.d77 (RS337to348.d2 qz175 qz215 qz299) (RS337to348.d2 qz215 qz229 qz301) qz309 (@Enclosure.dec_le_dec qz215 qz215 675167 1000 675167 1000 qz218 qz218 rfl rfl rfl) (@List.IsChain.cons_cons RS337to348.d1 RS337to348.d77 (RS337to348.d2 qz215 qz229 qz301) qz310 qz311 (@Enclosure.dec_le_dec qz229 qz229 676845 1000 676845 1000 qz232 qz232 rfl rfl rfl) (@List.IsChain.cons_cons RS337to348.d1 RS337to348.d77 qz310 qz312 qz313 (@Enclosure.dec_le_dec qz243 qz243 677517 1000 677517 1000 qz246 qz246 rfl rfl rfl) (@List.IsChain.cons_cons RS337to348.d1 RS337to348.d77 qz312 qz314 (@List.nil RS337to348.d1) (@Enclosure.dec_le_dec qz257 qz257 678523 1000 678523 1000 qz260 qz260 rfl rfl rfl) (@List.IsChain.singleton RS337to348.d1 RS337to348.d77 qz314)))) 

noncomputable abbrev qz315 := (@List.cons RS337to348.d1 (RS337to348.d2 qz548 qz560 qz608) qz612)

noncomputable def Ns336p2557 := @List.IsChain.cons_cons RS337to348.d1 RS337to348.d77 (RS337to348.d2 qz138 qz175 qz297) (RS337to348.d2 qz175 qz215 qz299) qz315 (@Enclosure.dec_le_dec qz175 qz175 673823 1000 673823 1000 qz180 qz180 rfl rfl rfl) Ns336p2556 

noncomputable abbrev qz819 := (@List.cons RS337to348.d1 (RS337to348.d2 qz81 qz95 qz293) Ns336p2553)

noncomputable def Ns336p2558 := @List.IsChain.cons_cons RS337to348.d1 RS337to348.d77 (RS337to348.d2 qz4 qz29 qz285) (RS337to348.d2 qz29 qz53 qz287) (@List.cons RS337to348.d1 (RS337to348.d2 qz53 qz67 qz289) (@List.cons RS337to348.d1 (RS337to348.d2 qz67 qz81 qz291) qz819)) (@Enclosure.dec_le_dec qz29 qz29 665749 1000 665749 1000 qz32 qz32 rfl rfl rfl) (@List.IsChain.cons_cons RS337to348.d1 RS337to348.d77 (RS337to348.d2 qz29 qz53 qz287) (RS337to348.d2 qz53 qz67 qz289) (@List.cons RS337to348.d1 (RS337to348.d2 qz67 qz81 qz291) qz819) (@Enclosure.dec_le_dec qz53 qz53 667096 1000 667096 1000 qz56 qz56 rfl rfl rfl) (@List.IsChain.cons_cons RS337to348.d1 RS337to348.d77 (RS337to348.d2 qz53 qz67 qz289) (RS337to348.d2 qz67 qz81 qz291) qz819 (@Enclosure.dec_le_dec qz67 qz67 668442 1000 668442 1000 qz70 qz70 rfl rfl rfl) (@List.IsChain.cons_cons RS337to348.d1 RS337to348.d77 (RS337to348.d2 qz67 qz81 qz291) (RS337to348.d2 qz81 qz95 qz293) Ns336p2553 (@Enclosure.dec_le_dec qz81 qz81 669788 1000 669788 1000 qz84 qz84 rfl rfl rfl) (Ns336p2554 (@Enclosure.dec_le_dec qz95 qz95 671134 1000 671134 1000 qz98 qz98 rfl rfl rfl) (Ns336p2555 Ns336p2557))))) 

noncomputable abbrev qz618 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz619 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns336p2552 Ns336p2558)

noncomputable abbrev qz620 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns336p2552 Ns336p2558))

theorem RS337to348.d78 : Zeta.Certificates.BatchSpec 12 664401 1000 681206 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz618 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz618 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz618 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz618 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz618 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz271)))) qz619 (@And.intro (@Eq Nat (@List.length qz618 qz620) 12) (And (@Eq (Option Real) (@Option.map qz618 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz618 qz620)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz618 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz618 qz620)) (@Option.some Real qz271))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz618 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz618 qz620)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz618 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz618 qz620)) (@Option.some Real qz271)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz271))))

theorem solution : Zeta.Certificates.BatchSpec 12 664401 1000 681206 1000 := RS337to348.d78
#print axioms solution
#check solution
