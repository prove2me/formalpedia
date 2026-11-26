-- Prove2me | solution 1 for RHHeight1000.rs_main_0241_0252
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:07:11.448599+00:00
-- url     : https://prove2.me/submissions/38489b39-209a-41aa-9427-dc00afbbf0c9

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

noncomputable def RS241to252.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS241to252.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS241to252.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS241to252.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS241to252.d2 a b h 

theorem RS241to252.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS241to252.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS241to252.d3 a b h)) 

noncomputable def Ns240p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns240p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns240p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns240p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns240p0 Ns240p1 Ns240p2 Ns240p1 153643044 134217728 1 51840000 153643044 134217728 1 51840000 76821522 67108864 2 67108864 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns240p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns240p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns240p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns240p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns240p8 := nat_lit 167537954069964697925743468333314178468718661948561187618563575975392713740913527107727581163208035826476740967700482432525301063254420572874757592895482956004842597348203117269212172556829666669574421653274845612596416189641484794702002223261246862056663160605878293700340502480877986491439034432953223334258717026053687371824342493299510132312376251152844516906794910572262907940062760396663270105627554083664899640691826599584783763757814813433640133591539937449421955686657622469485188711283992428713614179785896055117030632677201478317872225272595773536303110412989181984739022579128493081560758017763072115692678596043664844667144619713966763611484179303468167142547433165016751768184247559143333542643815355903304572487929375 

noncomputable def Ns240p9 := nat_lit 17907736863639440849562382641391758203535690054199171304015283257442503423240620144819838407313611418261944516207295868563739563278604805791797182761045687776939279949642059267526948014748996956777332184087524644234759874591635243045607722412471722018588244283882362848653445974523544951031470230725674276297342086185092985546835544820091590454230569790847977790484558207349923322458845585052164126500435851662252152223728079705692133047658564669873831757357628115566356048471439549797170528303905720944834637690907185213991407615774042056720704508980680095051114888612186461088301140868302968264130481206655302741383410655080008578156649725227045954510069588220729495895148666460653631514375880874422615237249871322129146554264800 

noncomputable def Ns240p10 := nat_lit 55164646516618494962085419356369025784335016154267579706247610053041231157772817011486486467101704279863254798704146668052276438579475100451766223896220272709675360577301802978530276301158911649961092601279696986330335403118086533522541958716560166657634553390183479955483588238249446822384543398154260439705049143284278540285021213103458182619368483938376641172730818250587232036579805400979202432024046862170503602539341971086573372247299262086029843105216008583038025403798224342134620653974939981235680083776396058604459065501719125356177784467570909658245422960948263734871602033841948787585406240093531041217463298165642337705122589129757920995868559518021463265498464182174549661735402095023640043996665674913376875 

noncomputable def Ns240p11 := BSN.log_dyadic_bound Ns240p6 Ns240p7 15 14 Ns240p8 134217728 51840000 Ns240p9 Ns240p10 153643044 Ns240p4 Ns240p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns240p6) (BSN.artanhQ Ns240p7) 0 14 Ns240p9 Ns240p8 Ns240p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns240p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns240p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns240p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns240p15 := nat_lit 167537954069966963268140139327979112712430526945422964221951926912223381190141639739514890494967825643602350173964944759828460064784215684919760383437959917620844610857567326816719640593037578236900835917107172977527392439886629774248115214831425484905681376157923696414882114961796820014026232307332015059110330001516939277521159573995394989771587717775443426002499543257897301982481613760098955890450106043861450716722534643739571053080256776912576113428445260435254713579381797931690799491102381747484553243404562568585572234105168360737285205910186933811836504830286397217473365026331067977496463917110493303316865058355012304571237619413071097245713770677768486493924969821719264401216877841676972336093778875903304572487929375 

noncomputable def Ns240p16 := nat_lit 17907736863639702486765313263906285882628955290251965205176678923530777959693011244026517850256414903756943142851250712732214241881959351517241344993825585048584379523049477943740273636414656012170312373198803997844271825165684859407921203335666024680974464565759223251918458072775203410604089667122984485578465112081892102496937045858735135721609691262763214794451343726045584198128451069547586972080574568545086657023793200560105564573365716615162566961587407171758966967827997201380802107846920231945878242774600967607639551032178207663699700360114112068650063802902647517702890145150192721997537569966984346993833704449560383184487996362781528900358997452380059737141488304159449328022742959995775545894292303322129146554264800 

noncomputable def Ns240p17 := nat_lit 55164646516619937449385584700664297411818070214438189962773666351465523500358685366424500506990751111492356556545320273548942244833046464529601272738875466881799996765940232256588350019911833156887888425998391295014189841212513610526066550079316346993943774342801096070086869790972589246312728227659319758310961510342377923950694747797317942483020440897997204711883064182772445608288320382376665481938194224815739627075458138172195220395246294556718284728034954178416253903237031389214179719385823921869528509431462690683227358218086518156757026652846493301460983550768858152506145788622699720737745394141184245149692548799188169247529408201840608223422296381897323845616153036586108326210125693898345963996665674913376875 

noncomputable def Ns240p18 := BSN.log_dyadic_bound Ns240p13 Ns240p14 15 14 Ns240p15 134217728 51840000 Ns240p16 Ns240p17 153643044 Ns240p12 Ns240p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns240p13) (BSN.artanhQ Ns240p14) 0 14 Ns240p16 Ns240p15 Ns240p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns240p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 76821522 67108864 2 67108864 38410761 33554432 1 33554432 (Ns240p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns240p0 Ns240p1 153643044 134217728 1 51840000 Bool.false (BSN.logfrac_isNear Ns240p4 Ns240p5 1 Ns240p0 Ns240p1 153643044 134217728 51840000 rfl rfl rfl (Ns240p11 rfl))) (BSN.isNear_log_sfrac Ns240p2 Ns240p1 153643044 134217728 1 51840000 Bool.false (BSN.logfrac_isNear Ns240p12 Ns240p5 1 Ns240p2 Ns240p1 153643044 134217728 51840000 rfl rfl rfl (Ns240p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS241to252.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 33554432 := Ns240p19 

noncomputable def Ns240p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 8388608 3240000 385100712855 135135 5814539 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz807 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz607 := qz807

noncomputable abbrev qz316 := qz607

noncomputable abbrev qz0 := qz316

theorem RS241to252.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 5814539 8388608 1 3240000 := BSN.isNear_log_sfrac 2 1 5814539 8388608 1 3240000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 5814539 8388608 3240000 rfl rfl rfl (Ns240p20 rfl)) 

theorem RS241to252.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 93032624 134217728 42 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 5814539 8388608 1 3240000 93032624 134217728 42 134217728 RS241to252.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz608 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz318 := qz608

noncomputable def Ns240p21 := @Enclosure.Real.IsNear.inv_image qz317 23726567 16777216 1 16777216 5931641 5931642 8388608 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2) qz318)) Bool.false 23726567 16777216 1 16777216 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2) qz318)) Bool.false 23726567 16777216 1 16777216 23726567 16777216 1 16777216 (BSN.sqrt_enclosure 2 1 11863283 11863284 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz319 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS241to252.d8 : Enclosure.Real.IsNear qz319 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz319 Bool.false 11863283 16777216 1 16777216 11863283 16777216 1 16777216 (Ns240p21 rfl rfl) rfl 

theorem RS241to252.d9 : Enclosure.Real.IsNear qz319 Bool.false 94906264 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz319 Bool.false 11863283 16777216 1 16777216 94906264 134217728 8 134217728 RS241to252.d8 rfl 

noncomputable def Ns240p22 := BSN.log_dyadic_bound 1 2 12 11 1326382131865190400 8388608 3240000 130797573554866995 13749310575 9215827 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 1) (BSN.artanhQ 2) 0 11 130797573554866995 1326382131865190400 13749310575 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz320 := (Enclosure.sfrac Bool.false 3 1)

theorem RS241to252.d10 : Enclosure.Real.IsNear (Real.log qz320) Bool.false 9215827 8388608 1 3240000 := BSN.isNear_log_sfrac 3 1 9215827 8388608 1 3240000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 9215827 8388608 3240000 rfl rfl rfl (Ns240p22 rfl)) 

theorem RS241to252.d11 : Enclosure.Real.IsNear (Real.log qz320) Bool.false 147453232 134217728 42 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz320) Bool.false 9215827 8388608 1 3240000 147453232 134217728 42 134217728 RS241to252.d10 rfl 

noncomputable abbrev qz609 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns240p23 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz609) 29058991 16777216 1 16777216 4843164 4843166 8388608 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz609) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz609 qz318)) Bool.false 29058991 16777216 1 16777216 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz609 qz318)) Bool.false 29058991 16777216 1 16777216 29058991 16777216 1 16777216 (BSN.sqrt_enclosure 3 1 14529495 14529496 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz321 := (@Inv.inv Real Real.instInv (Real.sqrt qz609))

theorem RS241to252.d12 : Enclosure.Real.IsNear qz321 Bool.false 4843165 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz321 Bool.false 9686330 16777216 2 16777216 4843165 8388608 1 8388608 (Ns240p23 rfl rfl) rfl 

theorem RS241to252.d13 : Enclosure.Real.IsNear qz321 Bool.false 77490640 134217728 16 134217728 := @Enclosure.Real.IsNear.recentre' qz321 Bool.false 4843165 8388608 1 8388608 77490640 134217728 16 134217728 RS241to252.d12 rfl 

noncomputable def Ns240p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns240p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns240p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns240p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns240p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns240p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns240p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns240p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns240p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns240p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns240p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns240p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns240p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns240p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns240p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns240p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns240p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns240p25 Ns240p26 Ns240p27 Ns240p28 200200021673987500790625 Ns240p29 Ns240p30 Ns240p31 Ns240p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns240p32 Ns240p33 151412625 Ns240p34 Ns240p35 1322214852783825 Ns240p27 Ns240p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns240p32 Ns240p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns240p34 Ns240p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns240p36 Ns240p37 1267389585 Ns240p38 Ns240p39 1927077560082675 Ns240p29 Ns240p30 Ns240p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns240p36 Ns240p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns240p38 Ns240p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 5)

theorem RS241to252.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz322)) Bool.false Ns240p24 Ns240p25 1 Ns240p26 := Ns240p40 rfl rfl rfl 

noncomputable def Ns240p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns240p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns240p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns240p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns240p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns240p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns240p25 Ns240p26 Ns240p42 Ns240p43 9945 Ns240p44 Ns240p45 65835 Ns240p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns240p42 Ns240p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns240p44 Ns240p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS241to252.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns240p41 Ns240p25 1 Ns240p26 := Ns240p46 rfl 

noncomputable def Ns240p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns240p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS241to252.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns240p47 Ns240p25 1 Ns240p48 := BSN.pi_combine Ns240p24 Ns240p41 Ns240p25 Ns240p26 Ns240p48 Ns240p47 rfl rfl rfl rfl RS241to252.d14 RS241to252.d15 

theorem RS241to252.d17 : Enclosure.Real.IsNear Real.pi Bool.false 7074237752028440 2251799813685248 1 2251799813685248 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns240p47 Ns240p25 1 Ns240p48 7074237752028440 2251799813685248 1 2251799813685248 RS241to252.d16 rfl 

noncomputable def Ns240p49 := nat_lit 147443727375074537121690809726715087890625 

noncomputable def Ns240p50 := nat_lit 22889945643899497138335355216896171420000 

noncomputable def Ns240p51 := nat_lit 355592320898650075318906513310625 

noncomputable def Ns240p52 := BSN.log_dyadic_bound 3 5 17 16 Ns240p49 8388608 3240000 Ns240p50 Ns240p51 11629079 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 3) (BSN.artanhQ 5) 0 16 Ns240p50 Ns240p49 Ns240p51 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz610 := (Enclosure.sfrac Bool.false 4 1)

noncomputable abbrev qz323 := qz610

theorem RS241to252.d18 : Enclosure.Real.IsNear (Real.log qz323) Bool.false 11629079 8388608 1 3240000 := BSN.isNear_log_sfrac 4 1 11629079 8388608 1 3240000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 11629079 8388608 3240000 rfl rfl rfl (Ns240p52 rfl)) 

theorem RS241to252.d19 : Enclosure.Real.IsNear (Real.log qz323) Bool.false 186065264 134217728 42 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz323) Bool.false 11629079 8388608 1 3240000 186065264 134217728 42 134217728 RS241to252.d18 rfl 

noncomputable abbrev qz611 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns240p53 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz611) 33554433 16777216 1 16777216 4194303 4194304 8388608 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz611) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz611 qz318)) Bool.false 33554433 16777216 1 16777216 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz611 qz318)) Bool.false 33554433 16777216 1 16777216 33554433 16777216 1 16777216 (BSN.sqrt_enclosure 4 1 16777216 16777217 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz324 := (@Inv.inv Real Real.instInv (Real.sqrt qz611))

theorem RS241to252.d20 : Enclosure.Real.IsNear qz324 Bool.false 8388607 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz324 Bool.false 8388607 16777216 1 16777216 8388607 16777216 1 16777216 (Ns240p53 rfl rfl) rfl 

theorem RS241to252.d21 : Enclosure.Real.IsNear qz324 Bool.false 67108856 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz324 Bool.false 8388607 16777216 1 16777216 67108856 134217728 8 134217728 RS241to252.d20 rfl 

noncomputable def Ns240p54 := nat_lit 159424323765613091421820433543167414255940625 

noncomputable def Ns240p55 := nat_lit 33013339099500162583200499609923570567289500 

noncomputable def Ns240p56 := nat_lit 351657888879851162997374110924800000 

noncomputable def Ns240p57 := nat_lit 2289063575687431840984260 

noncomputable def Ns240p58 := nat_lit 3325435793429257756623375 

noncomputable def Ns240p59 := BSN.log_dyadic_bound 2 3 21 20 Ns240p54 8388608 3240000 Ns240p55 Ns240p56 13500943 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 20 10 9927050056596826020 47940881637414340575 686533194547200 Ns240p57 Ns240p58 512222703392784384000 Ns240p55 Ns240p54 Ns240p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 10 20 Ns240p57 Ns240p58 512222703392784384000 rfl rfl rfl rfl)) rfl rfl 

theorem RS241to252.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 13500943 8388608 1 3240000 := BSN.isNear_log_sfrac 5 1 13500943 8388608 1 3240000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 13500943 8388608 3240000 rfl rfl rfl (Ns240p59 rfl rfl)) 

theorem RS241to252.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 216015088 134217728 42 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 13500943 8388608 1 3240000 216015088 134217728 42 134217728 RS241to252.d22 rfl 

noncomputable def Ns240p60 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz322) 37514995 16777216 1 16777216 3751499 3751500 8388608 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz322) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz318)) Bool.false 37514995 16777216 1 16777216 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz318)) Bool.false 37514995 16777216 1 16777216 37514995 16777216 1 16777216 (BSN.sqrt_enclosure 5 1 18757497 18757498 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz325 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS241to252.d24 : Enclosure.Real.IsNear qz325 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz325 Bool.false 7502999 16777216 1 16777216 7502999 16777216 1 16777216 (Ns240p60 rfl rfl) rfl 

theorem RS241to252.d25 : Enclosure.Real.IsNear qz325 Bool.false 60023992 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz325 Bool.false 7502999 16777216 1 16777216 60023992 134217728 8 134217728 RS241to252.d24 rfl 

noncomputable def Ns240p61 := BSN.log_dyadic_bound 2 10 5 4 94500000000 8388608 3240000 1291130880 26880 3401287 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz326 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz608)

theorem RS241to252.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683410914551 2251799813685248 12500000081 40500000000000000 := BSN.isNear_log_sfrac 6 1 4034683410914551 2251799813685248 12500000081 40500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz326) Bool.false 541526040612241437360128 302231454903657293676544 1000000006480000 3240000000000000000000 4034683410914551 2251799813685248 12500000081 40500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 3401287 8388608 24973259072661432 36028797018963968 3240000 1000000000000000 rfl rfl rfl rfl (Ns240p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS241to252.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 240485871 134217728 42 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683410914551 2251799813685248 12500000081 40500000000000000 240485871 134217728 42 134217728 RS241to252.d26 rfl 

noncomputable abbrev qz327 := (@Nat.cast Real Real.instNatCast 6)

noncomputable def Ns240p62 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz327) 41095619 16777216 1 16777216 3424634 3424635 8388608 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz327) (Real.sqrt qz326) Bool.false 41095619 16777216 1 16777216 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz326) Bool.false 41095619 16777216 1 16777216 41095619 16777216 1 16777216 (BSN.sqrt_enclosure 6 1 20547809 20547810 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz328 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS241to252.d28 : Enclosure.Real.IsNear qz328 Bool.false 6849269 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz328 Bool.false 6849269 16777216 1 16777216 6849269 16777216 1 16777216 (Ns240p62 rfl rfl) rfl 

theorem RS241to252.d29 : Enclosure.Real.IsNear qz328 Bool.false 54794152 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz328 Bool.false 6849269 16777216 1 16777216 54794152 134217728 8 134217728 RS241to252.d28 rfl 

noncomputable def Ns240p63 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 8388608 3240000 11010900719820672 5524329195 4694397 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz329 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz608)

theorem RS241to252.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 12500000081 40500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 12500000081 40500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz329) Bool.false 588115238325433934020608 302231454903657293676544 1000000006480000 3240000000000000000000 4381799983422711 2251799813685248 12500000081 40500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 4694397 8388608 24973259072661432 36028797018963968 3240000 1000000000000000 rfl rfl rfl rfl (Ns240p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS241to252.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 261175631 134217728 42 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 12500000081 40500000000000000 261175631 134217728 42 134217728 RS241to252.d30 rfl 

noncomputable abbrev qz330 := (@Nat.cast Real Real.instNatCast 7)

noncomputable def Ns240p64 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz330) 44388341 16777216 1 16777216 3170595 3170596 8388608 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz330) (Real.sqrt qz329) Bool.false 44388341 16777216 1 16777216 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz329) Bool.false 44388341 16777216 1 16777216 44388341 16777216 1 16777216 (BSN.sqrt_enclosure 7 1 22194170 22194171 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz331 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS241to252.d32 : Enclosure.Real.IsNear qz331 Bool.false 6341191 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz331 Bool.false 6341191 16777216 1 16777216 6341191 16777216 1 16777216 (Ns240p64 rfl rfl) rfl 

theorem RS241to252.d33 : Enclosure.Real.IsNear qz331 Bool.false 50729528 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz331 Bool.false 6341191 16777216 1 16777216 50729528 134217728 8 134217728 RS241to252.d32 rfl 

noncomputable def Ns240p65 := BSN.log_dyadic_bound 0 16 1 0 1 8388608 3240000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz332 := (Enclosure.sfrac Bool.false 8 1)

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz608)

theorem RS241to252.d34 : Enclosure.Real.IsNear (Real.log qz332) Bool.false 9364972152248037 4503599627370496 25000000243 81000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 25000000243 81000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 628472642529000809299968 302231454903657293676544 1000000009720000 3240000000000000000000 9364972152248037 4503599627370496 25000000243 81000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 8388608 24973259072661432 36028797018963968 3240000 1000000000000000 rfl rfl rfl rfl (Ns240p65 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS241to252.d35 : Enclosure.Real.IsNear (Real.log qz332) Bool.false 279097919 134217728 42 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz332) Bool.false 9364972152248037 4503599627370496 25000000243 81000000000000000 279097919 134217728 42 134217728 RS241to252.d34 rfl 

noncomputable abbrev qz334 := (@Nat.cast Real Real.instNatCast 8)

noncomputable def Ns240p66 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz334) 47453133 16777216 1 16777216 2965820 2965821 8388608 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz334) (Real.sqrt qz333) Bool.false 47453133 16777216 1 16777216 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 47453133 16777216 1 16777216 47453133 16777216 1 16777216 (BSN.sqrt_enclosure 8 1 23726566 23726567 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS241to252.d36 : Enclosure.Real.IsNear qz335 Bool.false 5931641 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 5931641 16777216 1 16777216 5931641 16777216 1 16777216 (Ns240p66 rfl rfl) rfl 

theorem RS241to252.d37 : Enclosure.Real.IsNear qz335 Bool.false 47453128 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 5931641 16777216 1 16777216 47453128 134217728 8 134217728 RS241to252.d36 rfl 

noncomputable def Ns240p67 := BSN.log_dyadic_bound 1 17 3 2 1252815 8388608 3240000 1448 3 988035 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz808 := (Enclosure.sfrac Bool.false 9 1)

noncomputable abbrev qz612 := qz808

noncomputable abbrev qz336 := qz612

noncomputable abbrev qz1 := qz336

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz608)

theorem RS241to252.d38 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 9895419403785957 4503599627370496 25000000243 81000000000000000 := BSN.isNear_log_sfrac 9 1 9895419403785957 4503599627370496 25000000243 81000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz337) Bool.false 664070354991632873422848 302231454903657293676544 1000000009720000 3240000000000000000000 9895419403785957 4503599627370496 25000000243 81000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 988035 8388608 24973259072661432 36028797018963968 3240000 1000000000000000 rfl rfl rfl rfl (Ns240p67 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS241to252.d39 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 294906479 134217728 42 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 9895419403785957 4503599627370496 25000000243 81000000000000000 294906479 134217728 42 134217728 RS241to252.d38 rfl 

noncomputable abbrev qz338 := (@Nat.cast Real Real.instNatCast 9)

noncomputable def Ns240p68 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz338) 50331649 16777216 1 16777216 2796202 2796203 8388608 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz338) (Real.sqrt qz337) Bool.false 50331649 16777216 1 16777216 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz337) Bool.false 50331649 16777216 1 16777216 50331649 16777216 1 16777216 (BSN.sqrt_enclosure 9 1 25165824 25165825 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz339 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS241to252.d40 : Enclosure.Real.IsNear qz339 Bool.false 5592405 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz339 Bool.false 5592405 16777216 1 16777216 5592405 16777216 1 16777216 (Ns240p68 rfl rfl) rfl 

theorem RS241to252.d41 : Enclosure.Real.IsNear qz339 Bool.false 44739240 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz339 Bool.false 5592405 16777216 1 16777216 44739240 134217728 8 134217728 RS241to252.d40 rfl 

theorem RS241to252.d42 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz809 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz613 := qz809

noncomputable abbrev qz340 := qz613

noncomputable abbrev qz2 := qz340

noncomputable abbrev qz341 := (Enclosure.Real.IsNear.const Bool.false 2 1)

theorem RS241to252.d43 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 qz341 RS241to252.d42 rfl 

noncomputable abbrev qz342 := (@Inv.inv Real Real.instInv qz613)

noncomputable abbrev qz3 := qz342

theorem RS241to252.d44 : Enclosure.Real.IsNear qz3 Bool.false 2670177 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 2670177 16777216 1 16777216 2670177 16777216 1 16777216 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 1335088 1335089 8388608 RS241to252.d43 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns240p69 := nat_lit 29883725399409473617920000 

noncomputable def Ns240p70 := nat_lit 26792558117491537794897543168 

noncomputable abbrev qz810 := (Enclosure.sfrac Bool.false 531948 1000)

noncomputable abbrev qz614 := qz810

noncomputable abbrev qz343 := qz614

noncomputable abbrev qz4 := qz343

noncomputable abbrev qz811 := (@instHMul Real Real.instMul)

noncomputable abbrev qz615 := qz811

noncomputable abbrev qz344 := qz615

noncomputable abbrev qz5 := qz344

noncomputable abbrev qz345 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 9)

noncomputable abbrev qz6 := qz345

noncomputable abbrev qz812 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 531948 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz616 := qz812

noncomputable abbrev qz346 := qz616

noncomputable abbrev qz7 := qz346

noncomputable abbrev qz347 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz8 := qz347

noncomputable abbrev qz813 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 531948 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz617 := qz813

noncomputable abbrev qz348 := qz617

noncomputable abbrev qz9 := qz348

noncomputable abbrev qz618 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz349 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz618 qz7 qz8))

noncomputable def Ns240p71 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (@HMul.hMul Real Real Real qz5 qz349 (Zeta.RiemannSiegel.correction qz9)) 193829031 67108864 45607 33554432 26994319465836613275 147573952589676412928 737409604623848705381 Ns240p69 Ns240p70 

noncomputable def Ns240p72 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 531948 1000 122 162 134217728 67108864 2251799813685248 Bool.false 122702357199 1764 

noncomputable def Ns240p73 := Ns240p72 279097919 42 47453128 8 294906479 42 44739240 8 Bool.true 104369471 74636 Bool.true 42119492 Bool.true 18302802 7074237752028440 1 Bool.false 127662929 Bool.true Bool.false 132971716 Bool.true Bool.true 193829031 

noncomputable def Ns240p74 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 531948 1000 24 76 134217728 67108864 2251799813685248 Bool.false 122702357199 1764 

noncomputable def Ns240p75 := Ns240p74 240485871 42 54794152 8 261175631 42 50729528 8 Bool.true 124834679 55664 Bool.true 163731768 Bool.true 206515086 7074237752028440 1 Bool.false 46136367 Bool.false Bool.false 4312885 Bool.false Bool.true 104369471 

noncomputable def Ns240p76 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 531948 1000 112 36 134217728 67108864 2251799813685248 Bool.false 122702357199 1764 

noncomputable def Ns240p77 := Ns240p76 186065264 42 67108856 8 216015088 42 60023992 8 Bool.true 172892536 32810 Bool.false 112496161 Bool.false 203729458 7074237752028440 1 Bool.false 89768918 Bool.false Bool.false 7095946 Bool.false Bool.true 124834679 

noncomputable def Ns240p78 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 531948 1000 347 209 134217728 67108864 2251799813685248 Bool.false 122702357199 1764 

noncomputable def Ns240p79 := Ns240p78 93032624 42 94906264 8 147453232 42 77490640 16 Bool.true 134217720 1818 Bool.false 56275123 Bool.false 201704089 7074237752028440 1 Bool.false 54640716 Bool.false Bool.false 133907684 Bool.true Bool.true 172892536 

noncomputable def Ns240p80 := nat_lit 88964986588852083674338198102231186259524595771803 

noncomputable def Ns240p81 := nat_lit 97314172636857003773117221834031743362924544000 

noncomputable def Ns240p82 := nat_lit 20445046908318498710438378864640000 

noncomputable def Ns240p83 := nat_lit 65254237780847626474354788400701112320 

noncomputable abbrev qz10 := (@Eq.refl Real qz343)

noncomputable def Ns240p84 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 531948 1000 1131875698816 16000000 1063896 4000 2000 Ns240p82 Ns240p83 qz10 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns240p85 := nat_lit 8395789479965294624181256537192065152694053628241269227520 

noncomputable abbrev qz814 := (@instHSub Real Real.instSub)

noncomputable abbrev qz619 := qz814

noncomputable abbrev qz350 := qz619

noncomputable abbrev qz11 := qz350

noncomputable abbrev qz620 := (@HMul.hMul Real Real Real qz811 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz351 := (@HMul.hMul Real Real Real qz615 (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real qz619 qz620 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1063896)))))

noncomputable abbrev qz621 := (Real.log (Enclosure.sfrac Bool.false 1131875698816 16000000))

noncomputable abbrev qz622 := (Enclosure.sfrac Bool.false 531948 2000)

noncomputable abbrev qz12 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 531948 4000) qz621) qz351) qz622)

noncomputable abbrev qz352 := (@HSub.hSub Real Real Real qz11 qz12 (@HMul.hMul Real Real Real qz5 qz622 (Real.log Real.pi)))

noncomputable def Ns240p86 := @Enclosure.Real.IsNear.addLit_ft_p qz352 (Enclosure.sfrac Bool.true Ns240p82 Ns240p83) 128662790998288905611 140737488355328000 544713022379833199 41472000000000000000000 Ns240p82 Ns240p83 0 1 Ns240p85 

noncomputable def Ns240p87 := nat_lit 2158603435741148599839358976000 

noncomputable abbrev qz353 := (@HMul.hMul Real Real Real qz5 qz622 (Real.log Real.pi))

noncomputable def Ns240p88 := @Enclosure.Real.IsNear.subLit_ff_p qz12 qz353 171512906894089270667 140737488355328000 421834547361277 81000000000000000000 5108131873107 16777216000 132987 16777216000 Ns240p87 128662790998288905611 140737488355328000 

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 531948 4000) qz621) qz351)

noncomputable def Ns240p89 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz622 208945419621909280139 140737488355328000 421834547361277 81000000000000000000 531948 2000 0 1 343025813788178541334000 171512906894089270667 140737488355328000 421834547361277 81000000000000000000 

noncomputable def Ns240p90 := nat_lit 941006513950002557250077808807378944 

noncomputable def Ns240p91 := nat_lit 26999660836899289875611648 

noncomputable def Ns240p92 := nat_lit 2417851639229258349412352 

noncomputable def Ns240p93 := nat_lit 339060455951402476876284256889580256619924595671040 

noncomputable def Ns240p94 := nat_lit 165093488436184056056857019777223061949160357888 

noncomputable def Ns240p95 := nat_lit 144442494260937176860060170147562888215134208 

noncomputable def Ns240p96 := BSN.log_dyadic_bound 83299698816 2180451698816 3 2 Ns240p93 67108864 25920000 Ns240p94 Ns240p95 5130010 2263751397632 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 83299698816) (BSN.artanhQ 2180451698816) 0 2 Ns240p94 Ns240p93 Ns240p95 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz354 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns240p97 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 531948 4000) qz621 531948 4000 0 1 3143174205545719 281474976710656 195312581 5062500000000000 418001308072908532653 281474976710656000 8658011403149 1687500000000000000 (Enclosure.Real.IsNear.const Bool.false 531948 4000) (BSN.isNear_log_sfrac 1131875698816 16000000 3143174205545719 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1131875698816) qz354)) Bool.false Ns240p91 Ns240p92 1000000414720000 25920000000000000000000 3143174205545719 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1131875698816 16000000 16 2263751397632 2097152000000 5130010 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns240p96 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p98 := BSN.arctan_dyadic_bound_f 1000 1063896 1 0 8388608 3240000 0 1 1 0 1 1 7884 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1063896) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1063896) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz355 := qz620

noncomputable abbrev qz14 := qz355

noncomputable abbrev qz356 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz15 := qz356

noncomputable abbrev qz357 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz16 := (@Enclosure.Real.IsNear.mulLit_ff qz357 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def Ns240p99 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1063896))) 884279719003555 562949953421312 1 2000000000000000 7884 8388608 1 3240000 7413437627638199877632 883750632719779 562949953421312 50000000081 162000000000000000 qz16 (Ns240p98 rfl) rfl rfl 

noncomputable abbrev qz17 := qz351

noncomputable abbrev qz358 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz18 := qz358

noncomputable abbrev qz359 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns240p100 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 531948 4000) qz621) qz17 418001308072908532653 281474976710656000 8658011403149 1687500000000000000 883750632719779 2251799813685248 50000000081 648000000000000000 Ns240p90 208945419621909280139 140737488355328000 421834547361277 81000000000000000000 (Ns240p97 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1063896)))) 1 4 0 1 883750632719779 562949953421312 50000000081 162000000000000000 883750632719779 2251799813685248 50000000081 648000000000000000 qz359 Ns240p99 rfl) 

noncomputable def Ns240p101 := @Ns240p86 Ns240p80 Ns240p81 544713022379833199 41472000000000000000000 (@Ns240p88 544713022379833199 41472000000000000000000 (Ns240p89 (Ns240p100 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 531948 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz622 (Real.log Real.pi) 531948 2000 0 1 38410761 33554432 1 33554432 5108131873107 16777216000 132987 16777216000 (Enclosure.Real.IsNear.const Bool.false 531948 2000) RS241to252.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns240p82 Ns240p83) 

noncomputable abbrev qz360 := (@instHAdd Real Real.instAdd)

noncomputable def Ns240p102 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns240p80 Ns240p81 544713022379833199 41472000000000000000000 15337794649 16777216 111 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz360 qz352 (Enclosure.sfrac Bool.true Ns240p82 Ns240p83)) Bool.false Ns240p80 Ns240p81 544713022379833199 41472000000000000000000 Ns240p84 (Ns240p101 rfl rfl)) 

noncomputable def Ns240p103 := nat_lit 3798773326778170236469248 

noncomputable def Ns240p104 := nat_lit 857880315701638037633288115969430579424582874412137543905840086399430724087819050421798443084646444471099243842018339232807217826369536 

noncomputable def Ns240p105 := nat_lit 16860812360175734222210805034837902731874731588140993779854824115686058269364094835627812361599730584878593258197117225559879026789580800 

noncomputable def Ns240p106 := nat_lit 612580196108991635018611350532762904605346115744660125578960181495778845675071716015304862619695109593482547565237696281794318336 

noncomputable def Ns240p107 := nat_lit 4284066865412495480983827233500334521500119233854881227093721819633636369690823829569466085968902706184872742758678370426170494359965696 

noncomputable def Ns240p108 := nat_lit 590128432606150697777378176219326595615615605584934782294918844049012039427743319246973432655990570470750764036899102894595765937635328000 

noncomputable abbrev qz361 := (BSN.sinEvenQ 34359738368)

noncomputable abbrev qz362 := (BSN.sinOddQ 34359738368)

noncomputable def Ns240p109 := BSN.sin_dyadic_bound_f 53983815842 34359738368 4 3 16777216 6486329 Ns240p104 Ns240p105 Ns240p106 Ns240p107 Ns240p108 Ns240p106 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53983815842) qz361 0 3 Ns240p104 Ns240p105 Ns240p106 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53983815842) qz362 0 3 Ns240p107 Ns240p108 Ns240p106 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz363 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable abbrev qz364 := (@Nat.cast Real Real.instNatCast Ns240p92)

noncomputable def Ns240p110 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15337794649) qz363) Bool.false 15337794649 16777216 111 8388608 Bool.true 16777215 16777216 1 3240000 (Ns240p102 rfl) (Enclosure.sfrac_false_div 15337794649 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15337794649) qz363) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns240p103) qz364) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 145 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 15337794649 16777216 226375608064910080 72057594037927936 145 Ns240p103 Ns240p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns240p103 Ns240p92 53983815842 34359738368 6486329 6480000 (Ns240p109 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns240p111 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns240p80 Ns240p81 544713022379833199 41472000000000000000000 122702357199 134217728 1764 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz360 qz352 (Enclosure.sfrac Bool.true Ns240p82 Ns240p83)) Bool.false Ns240p80 Ns240p81 544713022379833199 41472000000000000000000 Ns240p84 (Ns240p101 rfl rfl)) 

noncomputable def Ns240p112 := Ns240p79 32810 BSN.abs_quadSignPos (BSN.cos_quad_nat3 347 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 54640716 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 209 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133907684 134217728) qz10 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 16777215 16777216 5750447 424673280000 134217720 134217728 1818 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 16777215 16777216 5750447 424673280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 16777215 16777216 368028608 27179089920000 16777215 16777216 5750447 424673280000 (Ns240p110 rfl rfl) rfl)) rfl) (Ns240p111 rfl) RS241to252.d7 

noncomputable def Ns240p113 := nat_lit 10029188906742103074365140586641 

noncomputable def Ns240p114 := nat_lit 38942226439011207213978722469150720 

noncomputable def Ns240p115 := nat_lit 272595585073078450497851057284055040 

noncomputable abbrev qz365 := (BSN.sinEvenQ 134217728)

noncomputable abbrev qz366 := (BSN.sinOddQ 134217728)

noncomputable def Ns240p116 := BSN.sin_dyadic_bound_f 56275123 134217728 2 1 134217728 67108864 Ns240p113 Ns240p114 Ns240p113 Ns240p113 Ns240p115 Ns240p113 54640716 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 56275123) qz365 0 1 Ns240p113 Ns240p114 Ns240p113 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 56275123) qz366 0 1 Ns240p113 Ns240p115 Ns240p113 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p117 := nat_lit 9060852646966334611486146980301145491637696046678355836863316397663270865074470174443700999865497491209121 

noncomputable def Ns240p118 := nat_lit 212813371219357667808056223692308629509040396751503069069405487845990478953701519077062806287447472524492800 

noncomputable def Ns240p119 := nat_lit 4534990997291187277351530872862592351610506055487281797140320876077541035754511478238122118315375521 

noncomputable def Ns240p120 := nat_lit 45257086520611716820881386677470439255540186568695139397520811423115335128634644849192082976174372713266081 

noncomputable def Ns240p121 := nat_lit 7448467992677518373281967829230802032816413886302607417429192074609666763379553167697198220060661538357248000 

noncomputable def Ns240p122 := BSN.sin_dyadic_bound_f 201704089 134217728 4 3 134217728 67108864 Ns240p117 Ns240p118 Ns240p119 Ns240p120 Ns240p121 Ns240p119 133907684 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 201704089) qz365 0 3 Ns240p117 Ns240p118 Ns240p119 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 201704089) qz366 0 3 Ns240p120 Ns240p121 Ns240p119 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p123 := nat_lit 87342814900806916023146159264489608685543413896017264975276894511361 

noncomputable def Ns240p124 := nat_lit 4246191600076225767660054876205591831097850246550140165773818614251520 

noncomputable def Ns240p125 := nat_lit 25650841498341852438021519914169390206112527311456342514527822081 

noncomputable def Ns240p126 := nat_lit 261977143019424064364562434753640487276218016633428882240801627889921 

noncomputable def Ns240p127 := nat_lit 191078622003430159544702469429251632399403261094756307459821837641318400 

noncomputable abbrev qz367 := (BSN.cosEvenQ 134217728)

noncomputable abbrev qz368 := (BSN.cosOddQ 134217728)

noncomputable def Ns240p128 := BSN.cos_dyadic_bound_f 112496161 134217728 3 2 134217728 67108864 Ns240p123 Ns240p124 Ns240p125 Ns240p126 Ns240p127 Ns240p125 89768918 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 112496161) qz367 0 2 Ns240p123 Ns240p124 Ns240p125 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 112496161) qz368 0 2 Ns240p126 Ns240p127 Ns240p125 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p129 := nat_lit 3632376507554160948526388470774439770508604132039986539037400027778857490806072959317945853321922830012416 

noncomputable def Ns240p130 := nat_lit 16370259324565974446773555668639125346849261288577159159185037526614652227207809159774062022111344040345600 

noncomputable def Ns240p131 := nat_lit 5112648758884450387204672860542856144899364092350438259022383519272266946735421664683278120733249536 

noncomputable def Ns240p132 := nat_lit 21990116675500269647691443788365799415120623266707517394811319657048827651957929008505623198727605394739200 

noncomputable def Ns240p133 := nat_lit 1489693598535503674656393565846160406563282777260521483485838414921933352675910633539439644012132307671449600 

noncomputable def Ns240p134 := BSN.cos_dyadic_bound_f 203729458 134217728 4 3 134217728 67108864 Ns240p129 Ns240p130 Ns240p131 Ns240p132 Ns240p133 Ns240p131 7095946 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 203729458) qz367 0 3 Ns240p129 Ns240p130 Ns240p131 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 203729458) qz368 0 3 Ns240p132 Ns240p133 Ns240p131 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p135 := Ns240p77 55664 BSN.abs_quadSignPos (BSN.cos_quad_nat0 112 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 89768918 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 7095946 134217728) qz10 rfl rfl (Ns240p112 RS241to252.d9 RS241to252.d11 RS241to252.d13 RS241to252.d17 (Ns240p116 rfl rfl) (Ns240p122 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns240p111 rfl) RS241to252.d19 RS241to252.d21 RS241to252.d23 RS241to252.d25 RS241to252.d17 (Ns240p128 rfl rfl) (Ns240p134 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns240p136 := nat_lit 1512546762242636707143831766346516375017914142994742761243812516288146905851491588671657007625737502457856 

noncomputable def Ns240p137 := nat_lit 371189273044159273013262175676477189781620816912423999207631239884405043106898849430049767005618176 

noncomputable def Ns240p138 := nat_lit 9168061758644539649293462253345852888094983484605512632443331962622754569923206576101295856270370857287680 

noncomputable def Ns240p139 := BSN.cos_dyadic_bound_f 163731768 134217728 4 3 134217728 67108864 Ns240p136 Ns240p130 Ns240p137 Ns240p138 Ns240p133 Ns240p137 46136367 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 163731768) qz367 0 3 Ns240p136 Ns240p130 Ns240p137 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 163731768) qz368 0 3 Ns240p138 Ns240p133 Ns240p137 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p140 := nat_lit 3835827775878377796332797248324515289607117360227640186065763262368095811196859114596458893013135584792576 

noncomputable def Ns240p141 := nat_lit 6017573315009013305934578540919367209454293097149788884016347421677363859807422694083883793229418496 

noncomputable def Ns240p142 := nat_lit 23219072344260694848274935982941846364134035990525770139307935432337226013742175882244286286173422251806720 

noncomputable def Ns240p143 := BSN.cos_dyadic_bound_f 206515086 134217728 4 3 134217728 67108864 Ns240p140 Ns240p130 Ns240p141 Ns240p142 Ns240p133 Ns240p141 4312885 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 206515086) qz367 0 3 Ns240p140 Ns240p130 Ns240p141 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 206515086) qz368 0 3 Ns240p142 Ns240p133 Ns240p141 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p144 := Ns240p75 74636 BSN.abs_quadSignPos (BSN.cos_quad_nat0 24 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 46136367 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 76 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 4312885 134217728) qz10 rfl rfl (Ns240p135 rfl rfl) (Ns240p111 rfl) RS241to252.d27 RS241to252.d29 RS241to252.d31 RS241to252.d33 RS241to252.d17 (Ns240p139 rfl rfl) (Ns240p143 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p145 := nat_lit 3147259101950665200375855268096 

noncomputable def Ns240p146 := nat_lit 7788445287802241442795744493830144 

noncomputable def Ns240p147 := nat_lit 116826679317033621641936167407452160 

noncomputable def Ns240p148 := BSN.cos_dyadic_bound_f 42119492 134217728 2 1 134217728 67108864 Ns240p145 Ns240p146 Ns240p145 Ns240p145 Ns240p147 Ns240p145 127662929 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 42119492) qz367 0 1 Ns240p145 Ns240p146 Ns240p145 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 42119492) qz368 0 1 Ns240p145 Ns240p147 Ns240p145 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p149 := nat_lit 112220015959644639189509849616 

noncomputable def Ns240p150 := BSN.cos_dyadic_bound_f 18302802 134217728 2 1 134217728 67108864 Ns240p149 Ns240p146 Ns240p149 Ns240p149 Ns240p147 Ns240p149 132971716 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 18302802) qz367 0 1 Ns240p149 Ns240p146 Ns240p149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 18302802) qz368 0 1 Ns240p149 Ns240p147 Ns240p149 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p151 := Ns240p73 91214 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 122 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 127662929 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 162 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132971716 134217728) qz10 rfl rfl (Ns240p144 rfl) (Ns240p111 rfl) RS241to252.d35 RS241to252.d37 RS241to252.d39 RS241to252.d41 RS241to252.d17 (Ns240p148 rfl rfl) (Ns240p150 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p152 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) 193829031 134217728 91214 134217728 193829031 134217728 91214 134217728 52030584322523136 193829031 67108864 45607 33554432 (Ns240p151 rfl) 

noncomputable def Ns240p153 := @Enclosure.Real.IsNear.mulLit_tf qz349 (Zeta.RiemannSiegel.correction qz9) 2765461 8388608 1 8388608 9761236721775 17592186044416 531869867810651 7124835347988480000 26994319465836613275 147573952589676412928 

noncomputable abbrev qz369 := (@HPow.hPow Real Real Real qz618 qz7 qz8)

noncomputable def Ns240p154 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz369 1 1 0 1 2765461 8388608 1 8388608 2765461 8388608 1 8388608 

noncomputable abbrev qz19 := (@Enclosure.Real.IsNear.of_eq qz346 (@HMul.hMul Real Real Real qz344 qz343 qz342) Bool.false 355098828699 4194304000 132987 4194304000 (BSN.t_div_two_pi_mk qz343 531948 1000 (@Eq.refl Real qz343)) (@Enclosure.Real.IsNear.mulLit_ff qz343 qz342 531948 1000 0 1 2670177 16777216 1 16777216 355098828699 4194304000 132987 4194304000 (Enclosure.Real.IsNear.const Bool.false 531948 1000) RS241to252.d44 rfl))

noncomputable def Ns240p155 := @Enclosure.Real.IsNear.sqrt_image qz7 355098828699 4194304000 132987 4194304000 77185280 77185310 8388608 qz19 

noncomputable abbrev qz815 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 531948 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz623 := qz815

noncomputable abbrev qz370 := qz623

noncomputable abbrev qz20 := qz370

noncomputable def Ns240p156 := @Enclosure.Real.IsNear.sqrt_image qz20 77185295 8388608 15 8388608 25445570 25445576 8388608 (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 154370590 16777216 30 16777216 77185295 8388608 15 8388608 (Ns240p155 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz816 := (Real.sqrt (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 531948 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))))

noncomputable abbrev qz624 := qz816

noncomputable abbrev qz371 := qz624

noncomputable abbrev qz21 := qz371

noncomputable def Ns240p157 := @Enclosure.Real.IsNear.inv_image qz21 25445573 8388608 3 8388608 2765460 2765462 8388608 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 50891146 16777216 6 16777216 25445573 8388608 3 8388608 (Ns240p156 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns240p158 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz21) Bool.false 5530922 16777216 2 16777216 2765461 8388608 1 8388608 (Ns240p157 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz22 := (@HMul.hMul Real Real Real qz344 qz340 qz348)

noncomputable abbrev qz625 := (@HMul.hMul Real Real Real qz811 qz813 qz813)

noncomputable abbrev qz626 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz372 := (@HSub.hSub Real Real Real qz619 (@HSub.hSub Real Real Real qz619 qz625 qz617) qz626)

noncomputable abbrev qz23 := (Real.cos (@HMul.hMul Real Real Real qz344 qz340 qz372))

noncomputable def Ns240p159 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz9) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz22)) qz23) Bool.false 9761236721775 

noncomputable def Ns240p160 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz22)) qz23 55588225 16777216 2133 

noncomputable def Ns240p161 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz22)) Bool.false 55588225 16777216 2133 16777216 55588225 16777216 2133 

noncomputable def Ns240p162 := @Enclosure.Real.IsNear.recentre' (Real.cos qz22) Bool.false 2531786 8388608 629137216 54358179840000 1265893 4194304 9830269 849346560000 

noncomputable def Ns240p163 := @Enclosure.Real.IsNear.cos_image qz22 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21209809) qz363) Bool.false 21209809 16777216 189 16777216 Bool.false 2531786 8388608 1 

noncomputable def Ns240p164 := nat_lit 404791131150158971000407721 

noncomputable def Ns240p165 := nat_lit 36028797018963968000000000000000 

noncomputable def Ns240p166 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz9 884279719003555 140737488355328 1 500000000000000 1687823 8388608 15 8388608 1492507648167737210765 1180591620717411303424 Ns240p164 

noncomputable def Ns240p167 := @Enclosure.Real.IsNear.subLit_ff_p qz20 qz1 77185295 8388608 15 8388608 9 1 0 1 1687823 1687823 8388608 15 

noncomputable abbrev qz373 := (Enclosure.Real.IsNear.const Bool.false 9 1)

noncomputable def Ns240p168 := @Ns240p167 8388608 (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 154370590 16777216 30 16777216 77185295 8388608 15 8388608 (Ns240p155 rfl rfl rfl rfl rfl rfl) rfl) qz373 

noncomputable def Ns240p169 := @Enclosure.Real.IsNear.recentre' qz22 Bool.false 1492507648167737210765 1180591620717411303424 Ns240p164 Ns240p165 21209809 16777216 189 16777216 (@Ns240p166 Ns240p165 RS241to252.d43 (Ns240p168 rfl rfl) rfl) 

noncomputable def Ns240p170 := nat_lit 26977126982922309029552640609095105053185312774799874278953601 

noncomputable def Ns240p171 := nat_lit 253092741970790968397859029543733109897246971520789871559966720 

noncomputable def Ns240p172 := nat_lit 40953786393736801567141661964872406061002024404883000136321 

noncomputable def Ns240p173 := nat_lit 80849473375979453485523638503355570347433934275589856836588161 

noncomputable def Ns240p174 := nat_lit 11389173388685593577903656329467989945376113718435544220198502400 

noncomputable abbrev qz627 := (BSN.cosEvenQ 16777216)

noncomputable def Ns240p175 := BSN.cos_dyadic_bound_f 21209809 16777216 3 2 8388608 3240000 Ns240p170 Ns240p171 Ns240p172 Ns240p173 Ns240p174 Ns240p172 2531786 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 21209809) qz627 0 2 Ns240p170 Ns240p171 Ns240p172 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 21209809) (BSN.cosOddQ 16777216) 0 2 Ns240p173 Ns240p174 Ns240p172 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p176 := @Enclosure.Real.IsNear.inv_image (Real.cos qz22) 1265893 4194304 9830269 849346560000 27793046 27795179 8388608 (Ns240p162 (@Ns240p163 3240000 (Ns240p169 rfl) (Enclosure.sfrac_false_div 21209809 16777216) (Ns240p175 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns240p177 := @Enclosure.Real.IsNear.recentre' qz23 Bool.false 1404792 8388608 

noncomputable abbrev qz24 := (@HMul.hMul Real Real Real qz344 qz340 qz372)

noncomputable def Ns240p178 := @Enclosure.Real.IsNear.cos_image qz24 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1470669)) (@Nat.cast Real Real.instNatCast 1048576)) Bool.true 1470669 1048576 

noncomputable def Ns240p179 := nat_lit 13890076194231261540958925245 

noncomputable def Ns240p180 := nat_lit 9903520314283042199192993792 

noncomputable def Ns240p181 := nat_lit 4762071755629116604220735937985973 

noncomputable def Ns240p182 := @Enclosure.Real.IsNear.recentre' qz24 Bool.true Ns240p179 Ns240p180 Ns240p181 

noncomputable def Ns240p183 := nat_lit 302231454903657293676544000000000000000 

noncomputable abbrev qz25 := qz372

noncomputable def Ns240p184 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz25 884279719003555 140737488355328 1 500000000000000 15707785552159 

noncomputable abbrev qz374 := (@HSub.hSub Real Real Real qz619 qz625 qz617)

noncomputable abbrev qz26 := qz374

noncomputable abbrev qz375 := qz626

noncomputable abbrev qz27 := qz375

noncomputable def Ns240p185 := @Enclosure.Real.IsNear.subLit_tf qz26 qz27 11309739041055 70368744177664 176464035 70368744177664 1 16 

noncomputable abbrev qz376 := qz625

noncomputable abbrev qz28 := qz376

noncomputable def Ns240p186 := @Enclosure.Real.IsNear.subLit_ff_n qz28 qz9 2848746479329 70368744177664 50634915 70368744177664 1687823 8388608 15 8388608 

noncomputable def Ns240p187 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz9 1687823 8388608 15 8388608 1687823 8388608 15 8388608 2848746479329 70368744177664 

noncomputable def Ns240p188 := nat_lit 136767927836049338418362607384012048082399056341919667213508021324255379016625841 

noncomputable def Ns240p189 := nat_lit 846322570984149739285326836131859157750990110577656481930582364989086940895641600 

noncomputable def Ns240p190 := nat_lit 102371544848208359546222575271330168325385014681709824379231093607341469361 

noncomputable def Ns240p191 := nat_lit 828453767006601532391262081554148928821369190440724423591798686371799954588937905 

noncomputable def Ns240p192 := nat_lit 77015353959557626274964742087999183355340100062566739855682995214006911621503385600 

noncomputable def Ns240p193 := BSN.cos_dyadic_bound_f 1470669 1048576 4 3 8388608 3240000 Ns240p188 Ns240p189 Ns240p190 Ns240p191 Ns240p192 Ns240p190 1404792 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 1470669) (BSN.cosEvenQ 1048576) 0 3 Ns240p188 Ns240p189 Ns240p190 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 1470669) (BSN.cosOddQ 1048576) 0 3 Ns240p191 Ns240p192 Ns240p190 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz377 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns240p194 := @Ns240p177 875377216 54358179840000 175599 1048576 13677769 849346560000 (@Ns240p178 265 16777216 Bool.false 1404792 8388608 1 3240000 (@Ns240p182 Ns240p183 1470669 1048576 265 16777216 (@Ns240p184 70368744177664 176464035 70368744177664 Ns240p179 Ns240p180 Ns240p181 Ns240p183 RS241to252.d43 (@Ns240p185 0 1 251324568834544 15707785552159 70368744177664 176464035 70368744177664 (@Ns240p186 94872967397706301440 11309739041055 70368744177664 176464035 70368744177664 (@Ns240p187 50634915 70368744177664 (Ns240p168 rfl rfl) (Ns240p168 rfl rfl) rfl) (Ns240p168 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 1470669 1048576) (BSN.cos_neg_of_bound 1470669 1048576 Bool.false 1404792 8388608 1 3240000 (Ns240p193 rfl rfl)) rfl rfl) 

noncomputable abbrev qz29 := (@Enclosure.Real.IsNear.of_eq qz345 (Enclosure.sfrac Bool.true 1 1) Bool.true 1 1 0 1 (BSN.neg_one_pow_odd_mk 9 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1))

noncomputable def Ns240p195 := @Ns240p153 737409604623848705381 Ns240p69 (Ns240p154 qz29 (@Enclosure.Real.IsNear.of_eq qz369 (@Inv.inv Real Real.instInv qz21) Bool.false 2765461 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz7 (BSN.t_div_two_pi_nonneg qz4 531948 1000 qz10)) Ns240p158) rfl) (@Ns240p159 17592186044416 531869867810651 7124835347988480000 (BSN.correction_mk qz9 (BSN.cos_two_pi_p_ne_zero_mk qz4 531948 1000 9 qz10 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 531948 1000 9 qz10 rfl rfl rfl))) (@Ns240p160 16777216 175599 1048576 13677769 849346560000 9761236721775 17592186044416 531869867810651 7124835347988480000 (@Ns240p161 16777216 (Ns240p176 rfl rfl rfl rfl rfl) rfl) (Ns240p194 rfl) rfl)) 

noncomputable def Ns240p196 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 399240227304272916837 147573952589676412928 41355205319087674625381 Ns240p69 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (@HMul.hMul Real Real Real qz5 qz349 (Zeta.RiemannSiegel.correction qz9))) Bool.true 399240227304272916837 147573952589676412928 41355205319087674625381 Ns240p69 (BSN.hardyZApproximantRS₀_eq qz4 9 (@BSN.floor_sqrt_eq_dec qz4 531948 1000 9 qz10 rfl rfl rfl)) (@Ns240p71 399240227304272916837 147573952589676412928 41355205319087674625381 Ns240p69 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (@HAdd.hAdd Real Real Real qz360 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9)) Bool.true 193829031 67108864 45607 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (Ns240p152 (Ns240p151 rfl) rfl rfl)) (Ns240p195 rfl) rfl rfl)) 

theorem RS241to252.d45 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 399240227304272916837 147573952589676412928 41355205319087674625381 Ns240p69 := Ns240p196 

theorem RS241to252.d46 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS241to252.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS241to252.d3 a b h)) 

noncomputable def Ns240p197 := nat_lit 59767450798818947235840000 

noncomputable def Ns240p198 := nat_lit 110964146780434371861549154304 

noncomputable abbrev qz817 := (Enclosure.sfrac Bool.false 533363 1000)

noncomputable abbrev qz628 := qz817

noncomputable abbrev qz378 := qz628

noncomputable abbrev qz30 := qz378

noncomputable abbrev qz818 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 533363 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz629 := qz818

noncomputable abbrev qz379 := qz629

noncomputable abbrev qz31 := qz379

noncomputable abbrev qz819 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 533363 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz630 := qz819

noncomputable abbrev qz380 := qz630

noncomputable abbrev qz32 := qz380

noncomputable abbrev qz381 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz618 qz31 qz8))

noncomputable def Ns240p199 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz30) qz30 9) (@HMul.hMul Real Real Real qz5 qz381 (Zeta.RiemannSiegel.correction qz32)) 82052621 67108864 91453 67108864 210009663849068791875 1180591620717411303424 1899388946167853690903 Ns240p197 Ns240p198 

noncomputable def Ns240p200 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz30) qz30 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 533363 1000 122 162 134217728 67108864 2251799813685248 Bool.false 123123974976 1769 

noncomputable def Ns240p201 := Ns240p200 279097919 42 47453128 8 294906479 42 44739240 8 Bool.false 173689556 74831 Bool.true 15425271 Bool.true 13977693 7074237752028440 1 Bool.false 133332311 Bool.true Bool.false 133490553 Bool.true Bool.false 82052621 

noncomputable def Ns240p202 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz30) qz30 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 533363 1000 24 76 134217728 67108864 2251799813685248 Bool.false 123123974976 1769 

noncomputable def Ns240p203 := Ns240p202 240485871 42 54794152 8 261175631 42 50729528 8 Bool.false 108217364 55808 Bool.true 82401498 Bool.true 154460826 7074237752028440 1 Bool.false 109707576 Bool.false Bool.false 54725433 Bool.false Bool.false 173689556 

noncomputable def Ns240p204 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz30) qz30 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 533363 1000 113 37 134217728 67108864 2251799813685248 Bool.false 123123974976 1769 

noncomputable def Ns240p205 := Ns240p204 186065264 42 67108856 8 216015088 42 60023992 8 Bool.false 180747396 32893 Bool.false 60002876 Bool.false 108857172 7074237752028440 1 Bool.false 58024064 Bool.true Bool.false 97309215 Bool.true Bool.false 108217364 

noncomputable def Ns240p206 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz30) qz30 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 533363 1000 348 210 134217728 67108864 2251799813685248 Bool.false 123123974976 1769 

noncomputable def Ns240p207 := Ns240p206 93032624 42 94906264 8 147453232 42 77490640 16 Bool.false 134217720 1818 Bool.false 135423023 Bool.false 203846828 7074237752028440 1 Bool.false 71501016 Bool.false Bool.false 6978737 Bool.true Bool.false 180747396 

noncomputable def Ns240p208 := nat_lit 213999861377366792244760607389832945867913653930119585481 

noncomputable def Ns240p209 := nat_lit 233281740553503461391672736068524150501068341510144000 

noncomputable def Ns240p210 := nat_lit 20718419807513339576462884660640000 

noncomputable def Ns240p211 := nat_lit 66302658454305703057705368356813593920 

noncomputable abbrev qz33 := (@Eq.refl Real qz378)

noncomputable def Ns240p212 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz30 533363 1000 1137905359076 16000000 1066726 4000 2000 Ns240p210 Ns240p211 qz33 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns240p213 := nat_lit 68479955640757373518323394364746542677732369257638267353920 

noncomputable abbrev qz382 := (@HMul.hMul Real Real Real qz615 (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real qz619 qz620 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1066726)))))

noncomputable abbrev qz631 := (Real.log (Enclosure.sfrac Bool.false 1137905359076 16000000))

noncomputable abbrev qz632 := (Enclosure.sfrac Bool.false 533363 2000)

noncomputable abbrev qz34 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 533363 4000) qz631) qz382) qz632)

noncomputable abbrev qz383 := (@HSub.hSub Real Real Real qz11 qz34 (@HMul.hMul Real Real Real qz5 qz632 (Real.log Real.pi)))

noncomputable def Ns240p214 := @Enclosure.Real.IsNear.addLit_ft_p qz383 (Enclosure.sfrac Bool.true Ns240p210 Ns240p211) 1032839113303717103001 1125899906842624000 2184613862675055751 165888000000000000000000 Ns240p210 Ns240p211 0 1 Ns240p213 

noncomputable def Ns240p215 := nat_lit 69312659588579741759768100864000 

noncomputable abbrev qz384 := (@HMul.hMul Real Real Real qz5 qz632 (Real.log Real.pi))

noncomputable def Ns240p216 := @Enclosure.Real.IsNear.subLit_ff_p qz34 qz384 1376551902742260270489 1125899906842624000 422940016569737 81000000000000000000 20486878719243 67108864000 533363 67108864000 Ns240p215 1032839113303717103001 1125899906842624000 

noncomputable abbrev qz35 := (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 533363 4000) qz631) qz382)

noncomputable def Ns240p217 := @Enclosure.Real.IsNear.subLit_ff_p qz35 qz632 335361715749782300549 225179981368524800 422940016569737 81000000000000000000 533363 2000 0 1 550620761096904108195600 1376551902742260270489 1125899906842624000 422940016569737 81000000000000000000 

noncomputable def Ns240p218 := nat_lit 755167449042524884161054819223601152 

noncomputable def Ns240p219 := nat_lit 27012506868447604459438080 

noncomputable def Ns240p220 := nat_lit 342826492561765111339680831624228697477922443472640 

noncomputable def Ns240p221 := nat_lit 190934638813462451331717600936473246817559185408 

noncomputable def Ns240p222 := nat_lit 191028482945079166897915227514931180264694528 

noncomputable def Ns240p223 := BSN.log_dyadic_bound 89329359076 2186481359076 3 2 Ns240p220 67108864 25920000 Ns240p221 Ns240p222 5486559 2275810718152 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 89329359076) (BSN.artanhQ 2186481359076) 0 2 Ns240p221 Ns240p220 Ns240p222 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns240p224 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 533363 4000) qz631 533363 4000 0 1 3144669680442615 281474976710656 195312581 5062500000000000 335450090953982892849 225179981368524800 104172504139903 20250000000000000000 (Enclosure.Real.IsNear.const Bool.false 533363 4000) (BSN.isNear_log_sfrac 1137905359076 16000000 3144669680442615 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1137905359076) qz354)) Bool.false Ns240p219 Ns240p92 1000000414720000 25920000000000000000000 3144669680442615 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1137905359076 16000000 16 2275810718152 2097152000000 5486559 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns240p223 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p225 := BSN.arctan_dyadic_bound_f 1000 1066726 1 0 8388608 3240000 0 1 1 0 1 1 7863 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1066726) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1066726) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns240p226 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1066726))) 884279719003555 562949953421312 1 2000000000000000 7863 8388608 1 3240000 7413449449587221725184 883752042005923 562949953421312 50000000081 162000000000000000 qz16 (Ns240p225 rfl) rfl rfl 

noncomputable abbrev qz36 := qz382

noncomputable def Ns240p227 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 533363 4000) qz631) qz36 335450090953982892849 225179981368524800 104172504139903 20250000000000000000 883752042005923 2251799813685248 50000000081 648000000000000000 Ns240p218 335361715749782300549 225179981368524800 422940016569737 81000000000000000000 (Ns240p224 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1066726)))) 1 4 0 1 883752042005923 562949953421312 50000000081 162000000000000000 883752042005923 2251799813685248 50000000081 648000000000000000 qz359 Ns240p226 rfl) 

noncomputable def Ns240p228 := @Ns240p214 Ns240p208 Ns240p209 2184613862675055751 165888000000000000000000 (@Ns240p216 2184613862675055751 165888000000000000000000 (Ns240p217 (Ns240p227 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 533363 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz632 (Real.log Real.pi) 533363 2000 0 1 38410761 33554432 1 33554432 20486878719243 67108864000 533363 67108864000 (Enclosure.Real.IsNear.const Bool.false 533363 2000) RS241to252.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns240p210 Ns240p211) 

noncomputable def Ns240p229 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz30) Bool.false Ns240p208 Ns240p209 2184613862675055751 165888000000000000000000 1923812109 2097152 111 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz30) (@HAdd.hAdd Real Real Real qz360 qz383 (Enclosure.sfrac Bool.true Ns240p210 Ns240p211)) Bool.false Ns240p208 Ns240p209 2184613862675055751 165888000000000000000000 Ns240p212 (Ns240p228 rfl rfl)) 

noncomputable def Ns240p230 := nat_lit 857234076335112958652721206207371328494510532561463179931561737433425883138255289799938829551290058076715834943818154422318212262400000 

noncomputable def Ns240p231 := nat_lit 611199646708351700884999744724622160960467005445370694541958288554543740290340374039685705995562503889446945012832881000000000000 

noncomputable def Ns240p232 := nat_lit 4280843688530259360578444161276075536211420704197582691845378330019604762474003635033135926896992813523102493985581536240197877312000000 

noncomputable def Ns240p233 := BSN.sin_dyadic_bound_f 53973666910 34359738368 4 3 16777216 6486329 Ns240p230 Ns240p105 Ns240p231 Ns240p232 Ns240p108 Ns240p231 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53973666910) qz361 0 3 Ns240p230 Ns240p105 Ns240p231 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53973666910) qz362 0 3 Ns240p232 Ns240p108 Ns240p231 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p234 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz30) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1923812109) (@Nat.cast Real Real.instNatCast 2097152)) Bool.false 1923812109 2097152 111 8388608 Bool.false 16777215 16777216 1 3240000 (Ns240p229 rfl) (Enclosure.sfrac_false_div 1923812109 2097152) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1923812109) (@Nat.cast Real Real.instNatCast 2097152)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474757394895773806624768) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 145 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q3 1923812109 2097152 226375608064910080 72057594037927936 145 474757394895773806624768 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 474757394895773806624768 302231454903657293676544 53973666910 34359738368 6486329 6480000 (Ns240p233 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns240p235 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz30) Bool.false Ns240p208 Ns240p209 2184613862675055751 165888000000000000000000 123123974976 134217728 1769 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz30) (@HAdd.hAdd Real Real Real qz360 qz383 (Enclosure.sfrac Bool.true Ns240p210 Ns240p211)) Bool.false Ns240p208 Ns240p209 2184613862675055751 165888000000000000000000 Ns240p212 (Ns240p228 rfl rfl)) 

noncomputable def Ns240p236 := Ns240p207 32893 BSN.abs_quadSignPos (BSN.cos_quad_nat0 348 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 71501016 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 210 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 6978737 134217728) qz33 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 1) Bool.false 16777215 16777216 5750447 424673280000 134217720 134217728 1818 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz30)) Bool.false 16777215 16777216 5750447 424673280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz30) qz30) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz30)) Bool.false 16777215 16777216 368028608 27179089920000 16777215 16777216 5750447 424673280000 (Ns240p234 rfl rfl) rfl)) rfl) (Ns240p235 rfl) RS241to252.d7 

noncomputable def Ns240p237 := nat_lit 183479128128017082677720952682136029357692570561889835385088589650561 

noncomputable def Ns240p238 := nat_lit 113120165896292164281022690167480584443539782562132893267051633281 

noncomputable def Ns240p239 := nat_lit 550211144052258663704600812666073126904190632120545240368731665685121 

noncomputable def Ns240p240 := BSN.cos_dyadic_bound_f 135423023 134217728 3 2 134217728 67108864 Ns240p237 Ns240p124 Ns240p238 Ns240p239 Ns240p127 Ns240p238 71501016 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 135423023) qz367 0 2 Ns240p237 Ns240p124 Ns240p238 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 135423023) qz368 0 2 Ns240p239 Ns240p127 Ns240p238 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p241 := nat_lit 3640780769994827887120860814673903376391175262222602048327481502425081282921119563202191863828313953796096 

noncomputable def Ns240p242 := nat_lit 5148106171509994838715482734234165205269359835874707426498597705838480784324011194785279173371887616 

noncomputable def Ns240p243 := nat_lit 22040888649710261530114346141005470667939361811327048177891934176154693144284555347631575475631684122050560 

noncomputable def Ns240p244 := BSN.cos_dyadic_bound_f 203846828 134217728 4 3 134217728 67108864 Ns240p241 Ns240p130 Ns240p242 Ns240p243 Ns240p133 Ns240p242 6978737 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 203846828) qz367 0 3 Ns240p241 Ns240p130 Ns240p242 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 203846828) qz368 0 3 Ns240p243 Ns240p133 Ns240p242 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p245 := nat_lit 12962485042667430902985900933376 

noncomputable def Ns240p246 := BSN.sin_dyadic_bound_f 60002876 134217728 2 1 134217728 67108864 Ns240p245 Ns240p114 Ns240p245 Ns240p245 Ns240p115 Ns240p245 58024064 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 60002876) qz365 0 1 Ns240p245 Ns240p114 Ns240p245 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 60002876) qz366 0 1 Ns240p245 Ns240p115 Ns240p245 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p247 := nat_lit 137819810146870269395849195340863053086505305153065569975114781491200 

noncomputable def Ns240p248 := nat_lit 38215724400686031908940493885850326479880652218951261491964367528263680 

noncomputable def Ns240p249 := nat_lit 19717705725225645147173350574953112293434501773636046941428187136 

noncomputable def Ns240p250 := nat_lit 360924721718247959277938183325139024473324524302776320144538305888256 

noncomputable def Ns240p251 := nat_lit 700621614012577251663909054573922652131145290680773127352680071351500800 

noncomputable def Ns240p252 := BSN.sin_dyadic_bound_f 108857172 134217728 3 2 134217728 67108864 Ns240p247 Ns240p248 Ns240p249 Ns240p250 Ns240p251 Ns240p249 97309215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 108857172) qz365 0 2 Ns240p247 Ns240p248 Ns240p249 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 108857172) qz366 0 2 Ns240p250 Ns240p251 Ns240p249 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p253 := Ns240p205 55808 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 113 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58024064 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 37 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 97309215 134217728) qz33 rfl rfl (Ns240p236 RS241to252.d9 RS241to252.d11 RS241to252.d13 RS241to252.d17 (Ns240p240 rfl rfl) (Ns240p244 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns240p235 rfl) RS241to252.d19 RS241to252.d21 RS241to252.d23 RS241to252.d25 RS241to252.d17 (Ns240p246 rfl rfl) (Ns240p252 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns240p254 := nat_lit 25137724707171388908107573588122821593137661955737988987887234785536 

noncomputable def Ns240p255 := nat_lit 2125596642660989981736167013853220094567581949830006374052864256 

noncomputable def Ns240p256 := nat_lit 75408922928228844744359248430340758339223850703314306950913598628096 

noncomputable def Ns240p257 := BSN.cos_dyadic_bound_f 82401498 134217728 3 2 134217728 67108864 Ns240p254 Ns240p124 Ns240p255 Ns240p256 Ns240p127 Ns240p255 109707576 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 82401498) qz367 0 2 Ns240p254 Ns240p124 Ns240p255 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 82401498) qz368 0 2 Ns240p256 Ns240p127 Ns240p255 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p258 := nat_lit 1197654240596813910250702379077853870649516316694071265798367187626480981371943698355910153378639028883456 

noncomputable def Ns240p259 := nat_lit 184425188270038462360330537764793988140092807029416396498713610492325544526159132945509286134091776 

noncomputable def Ns240p260 := nat_lit 7260716144645597406915366448273944377866758157132064293801745025899221136376119226554822270441699974778880 

noncomputable def Ns240p261 := BSN.cos_dyadic_bound_f 154460826 134217728 4 3 134217728 67108864 Ns240p258 Ns240p130 Ns240p259 Ns240p260 Ns240p133 Ns240p259 54725433 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 154460826) qz367 0 3 Ns240p258 Ns240p130 Ns240p259 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 154460826) qz368 0 3 Ns240p260 Ns240p133 Ns240p259 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p262 := Ns240p203 74831 BSN.abs_quadSignPos (BSN.cos_quad_nat0 24 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 109707576 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 76 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 54725433 134217728) qz33 rfl rfl (Ns240p253 rfl rfl) (Ns240p235 rfl) RS241to252.d27 RS241to252.d29 RS241to252.d31 RS241to252.d33 RS241to252.d17 (Ns240p257 rfl rfl) (Ns240p261 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p263 := nat_lit 56614960784336468674072280481 

noncomputable def Ns240p264 := BSN.cos_dyadic_bound_f 15425271 134217728 2 1 134217728 67108864 Ns240p263 Ns240p146 Ns240p263 Ns240p263 Ns240p147 Ns240p263 133332311 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 15425271) qz367 0 1 Ns240p263 Ns240p146 Ns240p263 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 15425271) qz368 0 1 Ns240p263 Ns240p147 Ns240p263 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p265 := nat_lit 38171742926891683365401858001 

noncomputable def Ns240p266 := BSN.cos_dyadic_bound_f 13977693 134217728 2 1 134217728 67108864 Ns240p265 Ns240p146 Ns240p265 Ns240p265 Ns240p147 Ns240p265 133490553 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 13977693) qz367 0 1 Ns240p265 Ns240p146 Ns240p265 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 13977693) qz368 0 1 Ns240p265 Ns240p147 Ns240p265 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p267 := Ns240p201 91453 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 122 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133332311 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 162 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133490553 134217728) qz33 rfl rfl (Ns240p262 rfl) (Ns240p235 rfl) RS241to252.d35 RS241to252.d37 RS241to252.d39 RS241to252.d41 RS241to252.d17 (Ns240p264 rfl rfl) (Ns240p266 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p268 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 9) 82052621 134217728 91453 134217728 82052621 134217728 91453 134217728 22025832734130176 82052621 67108864 91453 67108864 (Ns240p267 rfl) 

noncomputable def Ns240p269 := @Enclosure.Real.IsNear.mulLit_tf qz381 (Zeta.RiemannSiegel.correction qz32) 2763625 8388608 1 8388608 75990651354315 140737488355328 342944725415639 3562417673994240000 210009663849068791875 1180591620717411303424 

noncomputable abbrev qz385 := (@HPow.hPow Real Real Real qz618 qz31 qz8)

noncomputable def Ns240p270 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz385 1 1 0 1 2763625 8388608 1 8388608 2763625 8388608 1 8388608 

noncomputable def Ns240p271 := @Enclosure.Real.IsNear.sqrt_image qz31 1424173615251 16777216000 533363 16777216000 77287870 77287899 8388608 (@Enclosure.Real.IsNear.of_eq qz31 (@HMul.hMul Real Real Real qz5 qz30 qz3) Bool.false 1424173615251 16777216000 533363 16777216000 (BSN.t_div_two_pi_mk qz30 533363 1000 qz33) (@Enclosure.Real.IsNear.mulLit_ff qz30 qz3 533363 1000 0 1 2670177 16777216 1 16777216 1424173615251 16777216000 533363 16777216000 (Enclosure.Real.IsNear.const Bool.false 533363 1000) RS241to252.d44 rfl)) 

noncomputable abbrev qz820 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 533363 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz633 := qz820

noncomputable abbrev qz386 := qz633

noncomputable abbrev qz37 := qz386

noncomputable def Ns240p272 := @Enclosure.Real.IsNear.sqrt_image qz37 154575769 16777216 29 16777216 25462475 25462481 8388608 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 154575769 16777216 29 16777216 154575769 16777216 29 16777216 (Ns240p271 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns240p273 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz37) 12731239 4194304 3 8388608 2763624 2763626 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz37) Bool.false 50924956 16777216 6 16777216 12731239 4194304 3 8388608 (Ns240p272 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns240p274 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz37)) Bool.false 5527250 16777216 2 16777216 2763625 8388608 1 8388608 (Ns240p273 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz38 := (@HMul.hMul Real Real Real qz344 qz340 qz380)

noncomputable abbrev qz634 := (@HMul.hMul Real Real Real qz811 qz819 qz819)

noncomputable abbrev qz387 := (@HSub.hSub Real Real Real qz619 (@HSub.hSub Real Real Real qz619 qz634 qz630) qz626)

noncomputable abbrev qz39 := (Real.cos (@HMul.hMul Real Real Real qz344 qz340 qz387))

noncomputable def Ns240p275 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz32) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz38)) qz39) Bool.false 75990651354315 

noncomputable def Ns240p276 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz38)) qz39 73669545 16777216 3629 

noncomputable def Ns240p277 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz38)) Bool.false 73669545 16777216 3629 16777216 73669545 16777216 3629 

noncomputable def Ns240p278 := @Enclosure.Real.IsNear.recentre' (Real.cos qz38) Bool.false 1910389 8388608 609697216 54358179840000 1910389 8388608 9526519 849346560000 

noncomputable def Ns240p279 := @Enclosure.Real.IsNear.cos_image qz38 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 22498987) qz363) Bool.false 22498987 16777216 183 16777216 Bool.false 1910389 8388608 1 

noncomputable def Ns240p280 := nat_lit 782596186893036370735298443 

noncomputable def Ns240p281 := nat_lit 72057594037927936000000000000000 

noncomputable def Ns240p282 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz32 884279719003555 140737488355328 1 500000000000000 3580825 16777216 29 16777216 3166450924800904832875 2361183241434822606848 Ns240p280 

noncomputable def Ns240p283 := @Enclosure.Real.IsNear.subLit_ff_p qz37 qz1 154575769 16777216 29 16777216 9 1 0 1 3580825 3580825 16777216 29 

noncomputable def Ns240p284 := @Ns240p283 16777216 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 154575769 16777216 29 16777216 154575769 16777216 29 16777216 (Ns240p271 rfl rfl rfl rfl rfl rfl) rfl) qz373 

noncomputable def Ns240p285 := @Enclosure.Real.IsNear.recentre' qz38 Bool.false 3166450924800904832875 2361183241434822606848 Ns240p280 Ns240p281 22498987 16777216 183 16777216 (@Ns240p282 Ns240p281 RS241to252.d43 (Ns240p284 rfl rfl) rfl) 

noncomputable def Ns240p286 := nat_lit 34172440796306577009046700350616909507747464944737755484220001 

noncomputable def Ns240p287 := nat_lit 65660429337509020475744490311044703673552839158988395866721 

noncomputable def Ns240p288 := nat_lit 102386001530244712986188612071228639115895289155895289660926561 

noncomputable def Ns240p289 := BSN.cos_dyadic_bound_f 22498987 16777216 3 2 8388608 3240000 Ns240p286 Ns240p171 Ns240p287 Ns240p288 Ns240p174 Ns240p287 1910389 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 22498987) qz627 0 2 Ns240p286 Ns240p171 Ns240p287 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 22498987) (BSN.cosOddQ 16777216) 0 2 Ns240p288 Ns240p174 Ns240p287 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p290 := @Enclosure.Real.IsNear.inv_image (Real.cos qz38) 1910389 8388608 9526519 849346560000 36832958 36836587 8388608 (Ns240p278 (@Ns240p279 3240000 (Ns240p285 rfl) (Enclosure.sfrac_false_div 22498987 16777216) (Ns240p289 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns240p291 := @Enclosure.Real.IsNear.recentre' qz39 Bool.false 1031507 8388608 

noncomputable abbrev qz40 := (@HMul.hMul Real Real Real qz344 qz340 qz387)

noncomputable def Ns240p292 := @Enclosure.Real.IsNear.cos_image qz40 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 24285339)) qz363) Bool.true 24285339 16777216 

noncomputable def Ns240p293 := nat_lit 57342137817998779548900053005 

noncomputable def Ns240p294 := nat_lit 39614081257132168796771975168 

noncomputable def Ns240p295 := nat_lit 18734487945253460392767483413885157 

noncomputable def Ns240p296 := @Enclosure.Real.IsNear.recentre' qz40 Bool.true Ns240p293 Ns240p294 Ns240p295 

noncomputable def Ns240p297 := nat_lit 1208925819614629174706176000000000000000 

noncomputable abbrev qz41 := qz387

noncomputable def Ns240p298 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz41 884279719003555 140737488355328 1 500000000000000 64846152846991 

noncomputable abbrev qz388 := (@HSub.hSub Real Real Real qz619 qz634 qz630)

noncomputable abbrev qz42 := qz388

noncomputable def Ns240p299 := @Enclosure.Real.IsNear.subLit_tf qz42 qz27 47253966802575 281474976710656 694227955 281474976710656 1 16 

noncomputable abbrev qz389 := qz634

noncomputable abbrev qz43 := qz389

noncomputable def Ns240p300 := @Enclosure.Real.IsNear.subLit_ff_n qz43 qz32 12822307680625 281474976710656 207688691 281474976710656 3580825 16777216 29 16777216 

noncomputable def Ns240p301 := @Enclosure.Real.IsNear.mulLit_ff qz32 qz32 3580825 16777216 29 16777216 3580825 16777216 29 16777216 12822307680625 281474976710656 

noncomputable def Ns240p302 := nat_lit 43691348241622845834848488065330334140195882052475349972065178473900196904379392558509028514001 

noncomputable def Ns240p303 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600 

noncomputable def Ns240p304 := nat_lit 42085262680166120054462393825498094614348469994008918374249784287751802529278971856525521 

noncomputable def Ns240p305 := nat_lit 264600049389789353525113868726741407012927633447232704204404555870853471937536550607859671341265 

noncomputable def Ns240p306 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600 

noncomputable def Ns240p307 := BSN.cos_dyadic_bound_f 24285339 16777216 4 3 8388608 3240000 Ns240p302 Ns240p303 Ns240p304 Ns240p305 Ns240p306 Ns240p304 1031507 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 24285339) qz627 0 3 Ns240p302 Ns240p303 Ns240p304 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 24285339) (BSN.cosOddQ 16777216) 0 3 Ns240p305 Ns240p306 Ns240p304 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p308 := @Ns240p291 862417216 54358179840000 1031507 8388608 13475269 849346560000 (@Ns240p292 261 16777216 Bool.false 1031507 8388608 1 3240000 (@Ns240p296 Ns240p297 24285339 16777216 261 16777216 (@Ns240p298 281474976710656 694227955 281474976710656 Ns240p293 Ns240p294 Ns240p295 Ns240p297 RS241to252.d43 (@Ns240p299 0 1 1037538445551856 64846152846991 281474976710656 694227955 281474976710656 (@Ns240p300 792790007903630131200 47253966802575 281474976710656 694227955 281474976710656 (@Ns240p301 207688691 281474976710656 (Ns240p284 rfl rfl) (Ns240p284 rfl rfl) rfl) (Ns240p284 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 24285339 16777216) (BSN.cos_neg_of_bound 24285339 16777216 Bool.false 1031507 8388608 1 3240000 (Ns240p307 rfl rfl)) rfl rfl) 

noncomputable def Ns240p309 := @Ns240p269 1899388946167853690903 Ns240p197 (Ns240p270 qz29 (@Enclosure.Real.IsNear.of_eq qz385 (@Inv.inv Real Real.instInv (Real.sqrt qz37)) Bool.false 2763625 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz31 (BSN.t_div_two_pi_nonneg qz30 533363 1000 qz33)) Ns240p274) rfl) (@Ns240p275 140737488355328 342944725415639 3562417673994240000 (BSN.correction_mk qz32 (BSN.cos_two_pi_p_ne_zero_mk qz30 533363 1000 9 qz33 rfl rfl (@BSN.floor_sqrt_eq_dec qz30 533363 1000 9 qz33 rfl rfl rfl))) (@Ns240p276 16777216 1031507 8388608 13475269 849346560000 75990651354315 140737488355328 342944725415639 3562417673994240000 (@Ns240p277 16777216 (Ns240p290 rfl rfl rfl rfl rfl) rfl) (Ns240p308 rfl) rfl)) 

noncomputable def Ns240p310 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz30) (hardyZApproximantRS₀ qz30) Bool.false 1653494637913024006211 1180591620717411303424 83347834831116661370903 Ns240p197 (@Eq.refl Real (hardyZApproximantRS₀ qz30)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz30) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz30) qz30 9) (@HMul.hMul Real Real Real qz5 qz381 (Zeta.RiemannSiegel.correction qz32))) Bool.false 1653494637913024006211 1180591620717411303424 83347834831116661370903 Ns240p197 (BSN.hardyZApproximantRS₀_eq qz30 9 (@BSN.floor_sqrt_eq_dec qz30 533363 1000 9 qz33 rfl rfl rfl)) (@Ns240p199 1653494637913024006211 1180591620717411303424 83347834831116661370903 Ns240p197 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz30) qz30 9) (@HAdd.hAdd Real Real Real qz360 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 9)) Bool.false 82052621 67108864 91453 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz30) qz30 9) (Ns240p268 (Ns240p267 rfl) rfl rfl)) (Ns240p309 rfl) rfl rfl)) 

theorem RS241to252.d47 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz30) Bool.false 1653494637913024006211 1180591620717411303424 83347834831116661370903 Ns240p197 := Ns240p310 

noncomputable abbrev qz821 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 531948 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))) (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 531948 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz635 := qz821

noncomputable abbrev qz390 := qz635

noncomputable abbrev qz636 := (@HMul.hMul Real Real Real qz811 qz821 qz821)

noncomputable abbrev qz391 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz615 qz636 qz635))

noncomputable abbrev qz44 := (@HAdd.hAdd Real Real Real qz360 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz390)) (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 1 32) qz391))

noncomputable abbrev qz392 := (@HMul.hMul Real Real Real qz615 qz624 qz624)

noncomputable abbrev qz45 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz344 qz392 qz371))

noncomputable def Ns240p311 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz360 qz44 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz45)) Bool.false 

noncomputable def Ns240p312 := @Enclosure.Real.IsNear.addLit_ff qz44 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz45) 13065801 536870912 

noncomputable abbrev qz46 := (@Inv.inv Real Real.instInv qz390)

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 1 32) qz391)

noncomputable def Ns240p313 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz46) qz47 1633225 67108864 25 67108864 

noncomputable def Ns240p314 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz46 25 4 0 1 65329 16777216 1 16777216 1633225 

noncomputable def Ns240p315 := @Enclosure.Real.IsNear.recentre' qz46 Bool.false 65329 16777216 1 16777216 65329 16777216 1 16777216 

noncomputable def Ns240p316 := @Enclosure.Real.IsNear.mulLit_ff qz21 qz7 25445573 8388608 3 8388608 355098828699 4194304000 132987 4194304000 9035693167874899527 35184372088832000 4449227301609 

noncomputable def Ns240p317 := @Enclosure.Real.IsNear.sqrt_image qz7 355098828699 4194304000 132987 4194304000 77185280 77185310 8388608 qz19 

noncomputable def Ns240p318 := @Enclosure.Real.IsNear.sqrt_image qz20 77185295 8388608 15 8388608 25445570 25445576 8388608 (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 154370590 16777216 30 16777216 77185295 8388608 15 8388608 (Ns240p317 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz393 := (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 50891146 16777216 6 16777216 25445573 8388608 3 8388608 (Ns240p318 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns240p319 := @Ns240p316 35184372088832000 qz393 

noncomputable def Ns240p320 := Ns240p319 qz19 

noncomputable abbrev qz48 := qz390

noncomputable def Ns240p321 := @Enclosure.Real.IsNear.inv_image qz48 9035693167874899527 35184372088832000 4449227301609 35184372088832000 32664 32665 8388608 (Ns240p320 rfl) rfl rfl 

noncomputable abbrev qz49 := qz391

noncomputable def Ns240p322 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz49 1 32 0 1 1 

noncomputable def Ns240p323 := @Enclosure.Real.IsNear.recentre' qz49 Bool.false 1 16777216 1 16777216 

noncomputable def Ns240p324 := nat_lit 737707883327065694100491384521199421054410302260400476183 

noncomputable def Ns240p325 := nat_lit 43556142965880123323311949751266331066368000000000 

noncomputable def Ns240p326 := nat_lit 1089755354786624197350628904827644368352223139127273 

noncomputable abbrev qz394 := (@HMul.hMul Real Real Real qz615 qz636 qz635)

noncomputable abbrev qz50 := qz394

noncomputable def Ns240p327 := @Enclosure.Real.IsNear.inv_image qz50 Ns240p324 Ns240p325 Ns240p326 Ns240p325 0 1 

noncomputable def Ns240p328 := nat_lit 81643751023981137245616313200344823729 

noncomputable def Ns240p329 := nat_lit 1237940039285380274899124224000000 

noncomputable def Ns240p330 := nat_lit 80403725258565413917695854866767 

noncomputable abbrev qz395 := qz636

noncomputable abbrev qz51 := qz395

noncomputable def Ns240p331 := @Enclosure.Real.IsNear.mulLit_ff qz51 qz48 Ns240p328 Ns240p329 Ns240p330 Ns240p329 9035693167874899527 35184372088832000 4449227301609 

noncomputable def Ns240p332 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz48 9035693167874899527 35184372088832000 4449227301609 35184372088832000 9035693167874899527 35184372088832000 4449227301609 35184372088832000 Ns240p328 

noncomputable def Ns240p333 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz45 13 10 0 1 601109 16777216 1 

noncomputable def Ns240p334 := @Enclosure.Real.IsNear.recentre' qz45 Bool.false 601109 16777216 1 16777216 601109 16777216 

noncomputable abbrev qz52 := qz392

noncomputable def Ns240p335 := @Enclosure.Real.IsNear.mulLit_ff qz52 qz21 647477185298329 70368744177664 152673447 70368744177664 25445573 8388608 3 8388608 16475427984343157347517 

noncomputable def Ns240p336 := @Enclosure.Real.IsNear.mulLit_ff qz21 qz21 25445573 8388608 3 8388608 25445573 8388608 3 8388608 647477185298329 70368744177664 152673447 

noncomputable def Ns240p337 := @Ns240p336 70368744177664 qz393 

noncomputable def Ns240p338 := Ns240p337 qz393 

noncomputable def Ns240p339 := @Ns240p335 590295810358705651712 5827295354715459 590295810358705651712 (Ns240p338 rfl) qz393 

noncomputable abbrev qz53 := (@HMul.hMul Real Real Real qz344 qz392 qz371)

noncomputable def Ns240p340 := @Enclosure.Real.IsNear.inv_image qz53 16475427984343157347517 590295810358705651712 5827295354715459 590295810358705651712 300554 300555 8388608 (Ns240p339 rfl) 

noncomputable def Ns240p341 := @Ns240p312 201 536870912 7814417 167772160 13 167772160 6387410837438464 190359677 2684354560 1213 2684354560 (@Ns240p313 1 536870912 1 536870912 876831062360064 13065801 536870912 201 536870912 (@Ns240p314 67108864 25 67108864 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns240p315 (Ns240p321 rfl rfl rfl rfl) rfl) rfl) (@Ns240p322 16777216 1 16777216 1 536870912 1 536870912 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns240p323 1 16777216 1 16777216 (@Ns240p327 8388608 (@Ns240p331 35184372088832000 Ns240p324 Ns240p325 Ns240p326 Ns240p325 (@Ns240p332 Ns240p329 Ns240p330 Ns240p329 (Ns240p320 rfl) (Ns240p320 rfl) rfl) (Ns240p320 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns240p333 16777216 7814417 167772160 13 167772160 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns240p334 1 16777216 (Ns240p340 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS241to252.d48 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 := @Ns240p311 190359677 2684354560 1213 2684354560 (BSN.hardyZErrorBoundRS₀_mk qz4 531948 1000 qz10 rfl rfl) (Ns240p341 rfl rfl) 

noncomputable def Ns240p342 := nat_lit 7968993439842526298112000 

noncomputable def Ns240p343 := nat_lit 315346940732256334988659654656 

noncomputable abbrev qz822 := (Enclosure.sfrac Bool.false 534777 1000)

noncomputable abbrev qz637 := qz822

noncomputable abbrev qz396 := qz637

noncomputable abbrev qz54 := qz396

noncomputable abbrev qz823 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 534777 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz638 := qz823

noncomputable abbrev qz397 := qz638

noncomputable abbrev qz55 := qz397

noncomputable abbrev qz824 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 534777 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz639 := qz824

noncomputable abbrev qz398 := qz639

noncomputable abbrev qz56 := qz398

noncomputable abbrev qz399 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz618 qz55 qz8))

noncomputable def Ns240p344 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz54) qz54 9) (@HMul.hMul Real Real Real qz5 qz399 (Zeta.RiemannSiegel.correction qz56)) 139363779 33554432 91695 67108864 408782920407352617273 2361183241434822606848 391894193317324170121 Ns240p342 Ns240p343 

noncomputable def Ns240p345 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz54) qz54 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 534777 1000 121 162 134217728 67108864 2251799813685248 Bool.false 123545546622 1773 

noncomputable def Ns240p346 := Ns240p345 279097919 42 47453128 8 294906479 42 44739240 8 Bool.true 186819093 75030 Bool.true 199326796 Bool.true 9403808 7074237752028440 1 Bool.false 133725195 Bool.true Bool.false 133888429 Bool.true Bool.true 278727558 

noncomputable def Ns240p347 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz54) qz54 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 534777 1000 24 76 134217728 67108864 2251799813685248 Bool.false 123545546622 1773 

noncomputable def Ns240p348 := Ns240p347 240485871 42 54794152 8 261175631 42 50729528 8 Bool.true 278334183 55957 Bool.true 876874 Bool.true 102191523 7074237752028440 1 Bool.false 134214863 Bool.false Bool.false 97157575 Bool.false Bool.true 186819093 

noncomputable def Ns240p349 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz54) qz54 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 534777 1000 114 38 134217728 67108864 2251799813685248 Bool.false 123545546622 1773 

noncomputable def Ns240p350 := Ns240p349 186065264 42 67108856 8 216015088 42 60023992 8 Bool.true 151643785 32982 Bool.false 7649524 Bool.false 14154769 7074237752028440 1 Bool.false 133999800 Bool.true Bool.false 133472029 Bool.true Bool.true 278334183 

noncomputable def Ns240p351 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz54) qz54 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 534777 1000 350 211 134217728 67108864 2251799813685248 Bool.false 123545546622 1773 

noncomputable def Ns240p352 := Ns240p351 93032624 42 94906264 8 147453232 42 77490640 16 Bool.true 134217704 1826 Bool.false 3789110 Bool.false 206090890 7074237752028440 1 Bool.false 134164246 Bool.true Bool.false 134134115 Bool.false Bool.true 151643785 

noncomputable def Ns240p353 := nat_lit 24241219166657318092687961167425340371305101665424994979 

noncomputable def Ns240p354 := nat_lit 26335237889613317495259552432238127453107583451136000 

noncomputable def Ns240p355 := nat_lit 20994512864268287739682798875360000 

noncomputable def Ns240p356 := nat_lit 67364323117124018113297544201186368320 

noncomputable abbrev qz57 := (@Eq.refl Real qz396)

noncomputable def Ns240p357 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz54 534777 1000 1143946758916 16000000 1069554 4000 2000 Ns240p355 Ns240p356 qz57 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns240p358 := nat_lit 69814711199973076106941328162184980269358692796423985539520 

noncomputable abbrev qz400 := (@HMul.hMul Real Real Real qz615 (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real qz619 qz620 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1069554)))))

noncomputable abbrev qz640 := (Real.log (Enclosure.sfrac Bool.false 1143946758916 16000000))

noncomputable abbrev qz641 := (Enclosure.sfrac Bool.false 534777 2000)

noncomputable abbrev qz58 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 534777 4000) qz640) qz400) qz641)

noncomputable abbrev qz401 := (@HSub.hSub Real Real Real qz11 qz58 (@HMul.hMul Real Real Real qz5 qz641 (Real.log Real.pi)))

noncomputable def Ns240p359 := @Enclosure.Real.IsNear.addLit_ft_p qz401 (Enclosure.sfrac Bool.true Ns240p355 Ns240p356) 1036375511653382013411 1125899906842624000 2190371563906287029 165888000000000000000000 Ns240p355 Ns240p356 0 1 Ns240p358 

noncomputable def Ns240p360 := nat_lit 69549983264477228678044975104000 

noncomputable abbrev qz402 := (@HMul.hMul Real Real Real qz5 qz641 (Real.log Real.pi))

noncomputable def Ns240p361 := @Enclosure.Real.IsNear.subLit_ff_p qz58 qz402 1380999518938431406563 1125899906842624000 424044704527873 81000000000000000000 20541191535297 67108864000 534777 67108864000 Ns240p360 1036375511653382013411 1125899906842624000 

noncomputable def Ns240p362 := nat_lit 2761999037876862813126000 

noncomputable abbrev qz59 := (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 534777 4000) qz640) qz400)

noncomputable def Ns240p363 := @Enclosure.Real.IsNear.subLit_ff_p qz59 qz641 1682052206179220373987 1125899906842624000 424044704527873 81000000000000000000 534777 2000 0 1 Ns240p362 1380999518938431406563 1125899906842624000 424044704527873 81000000000000000000 

noncomputable def Ns240p364 := nat_lit 3787644844483228792809615067264843776 

noncomputable def Ns240p365 := nat_lit 27025309845583481381322752 

noncomputable def Ns240p366 := nat_lit 346631239099929422560666099907418852930597966647040 

noncomputable def Ns240p367 := nat_lit 218867590677307059919112655567465916529091545088 

noncomputable def Ns240p368 := nat_lit 248188816994558564158958004732000779689329408 

noncomputable def Ns240p369 := BSN.log_dyadic_bound 95370758916 2192522758916 3 2 Ns240p366 67108864 25920000 Ns240p367 Ns240p368 5841913 2287893517832 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 95370758916) (BSN.artanhQ 2192522758916) 0 2 Ns240p367 Ns240p366 Ns240p368 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns240p370 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 534777 4000) qz640 534777 4000 0 1 3146160143146231 281474976710656 195312581 5062500000000000 1682494082871311975487 1125899906842624000 34816225376479 6750000000000000000 (Enclosure.Real.IsNear.const Bool.false 534777 4000) (BSN.isNear_log_sfrac 1143946758916 16000000 3146160143146231 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1143946758916) qz354)) Bool.false Ns240p365 Ns240p92 1000000414720000 25920000000000000000000 3146160143146231 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1143946758916 16000000 16 2287893517832 2097152000000 5841913 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns240p369 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p371 := BSN.arctan_dyadic_bound_f 1000 1069554 1 0 8388608 3240000 0 1 1 0 1 1 7843 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1069554) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1069554) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns240p372 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1069554))) 884279719003555 562949953421312 1 2000000000000000 7843 8388608 1 3240000 7413460708586290151424 883753384183203 562949953421312 50000000081 162000000000000000 qz16 (Ns240p371 rfl) rfl rfl 

noncomputable abbrev qz60 := qz400

noncomputable def Ns240p373 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 534777 4000) qz640) qz60 1682494082871311975487 1125899906842624000 34816225376479 6750000000000000000 883753384183203 2251799813685248 50000000081 648000000000000000 Ns240p364 1682052206179220373987 1125899906842624000 424044704527873 81000000000000000000 (Ns240p370 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1069554)))) 1 4 0 1 883753384183203 562949953421312 50000000081 162000000000000000 883753384183203 2251799813685248 50000000081 648000000000000000 qz359 Ns240p372 rfl) 

noncomputable def Ns240p374 := @Ns240p359 Ns240p353 Ns240p354 2190371563906287029 165888000000000000000000 (@Ns240p361 2190371563906287029 165888000000000000000000 (Ns240p363 (Ns240p373 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 534777 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz641 (Real.log Real.pi) 534777 2000 0 1 38410761 33554432 1 33554432 20541191535297 67108864000 534777 67108864000 (Enclosure.Real.IsNear.const Bool.false 534777 2000) RS241to252.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns240p355 Ns240p356) 

noncomputable def Ns240p375 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz54) Bool.false Ns240p353 Ns240p354 2190371563906287029 165888000000000000000000 15443193327 16777216 223 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz54) (@HAdd.hAdd Real Real Real qz360 qz401 (Enclosure.sfrac Bool.true Ns240p355 Ns240p356)) Bool.false Ns240p353 Ns240p354 2190371563906287029 165888000000000000000000 Ns240p357 (Ns240p374 rfl rfl)) 

noncomputable def Ns240p376 := nat_lit 3796513735149389132857344 

noncomputable def Ns240p377 := nat_lit 855836899826340642847745179574233220250312259567159426313232925634906145574274533076219334061793783495187463144505776091168463210090496 

noncomputable def Ns240p378 := nat_lit 608221962932934991073480660593468665376831939765759317395525309784087799188413688770088050460885915626180531613668796238061572096 

noncomputable def Ns240p379 := nat_lit 4273875124657694251447986179356228438391798371522071799326483374690977799646559954268627888776717123713292884521833799817054919526649856 

noncomputable def Ns240p380 := BSN.sin_dyadic_bound_f 53951705114 34359738368 4 3 16777216 6486329 Ns240p377 Ns240p105 Ns240p378 Ns240p379 Ns240p108 Ns240p378 16777213 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53951705114) qz361 0 3 Ns240p377 Ns240p105 Ns240p378 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53951705114) qz362 0 3 Ns240p379 Ns240p108 Ns240p378 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p381 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz54) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15443193327) qz363) Bool.false 15443193327 16777216 223 16777216 Bool.true 16777213 16777216 1 3240000 (Ns240p375 rfl) (Enclosure.sfrac_false_div 15443193327 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15443193327) qz363) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns240p376) qz364) 226375608064910080 72057594037927936 Bool.false 16777213 16777216 146 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 15443193327 16777216 226375608064910080 72057594037927936 146 Ns240p376 Ns240p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777213 16777216 Ns240p376 Ns240p92 53951705114 34359738368 6486329 6480000 (Ns240p380 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns240p382 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz54) Bool.false Ns240p353 Ns240p354 2190371563906287029 165888000000000000000000 123545546622 134217728 1773 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz54) (@HAdd.hAdd Real Real Real qz360 qz401 (Enclosure.sfrac Bool.true Ns240p355 Ns240p356)) Bool.false Ns240p353 Ns240p354 2190371563906287029 165888000000000000000000 Ns240p357 (Ns240p374 rfl rfl)) 

noncomputable def Ns240p383 := Ns240p352 32982 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 350 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 134164246 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 211 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 134134115 134217728) qz57 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz54) qz54 1) Bool.true 16777213 16777216 11551519 849346560000 134217704 134217728 1826 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz54) qz54 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz54)) Bool.true 16777213 16777216 11551519 849346560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz54) qz54) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz54)) Bool.true 16777213 16777216 739297216 54358179840000 16777213 16777216 11551519 849346560000 (Ns240p381 rfl rfl) rfl)) rfl) (Ns240p382 rfl) RS241to252.d7 

noncomputable def Ns240p384 := nat_lit 206133630883294957382410000 

noncomputable def Ns240p385 := BSN.cos_dyadic_bound_f 3789110 134217728 2 1 134217728 67108864 Ns240p384 Ns240p146 Ns240p384 Ns240p384 Ns240p147 Ns240p384 134164246 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 3789110) qz367 0 1 Ns240p384 Ns240p146 Ns240p384 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 3789110) qz368 0 1 Ns240p384 Ns240p147 Ns240p384 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p386 := nat_lit 9876684862441184511583952518465932490949027427837693462248976510102414855701344000261561234244790438400000 

noncomputable def Ns240p387 := nat_lit 5870911542235027712724152272681274293226019191324421205929545910183660347802651539915521000000000000 

noncomputable def Ns240p388 := nat_lit 49327384659388444363532622271534348547263472017979823665886462341849557424831628642659993409972208192000000 

noncomputable def Ns240p389 := BSN.sin_dyadic_bound_f 206090890 134217728 4 3 134217728 67108864 Ns240p386 Ns240p118 Ns240p387 Ns240p388 Ns240p121 Ns240p387 134134115 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 206090890) qz365 0 3 Ns240p386 Ns240p118 Ns240p387 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 206090890) qz366 0 3 Ns240p388 Ns240p121 Ns240p387 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p390 := nat_lit 3424030670479463595951083776 

noncomputable def Ns240p391 := BSN.cos_dyadic_bound_f 7649524 134217728 2 1 134217728 67108864 Ns240p390 Ns240p146 Ns240p390 Ns240p390 Ns240p147 Ns240p390 133999800 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 7649524) qz367 0 1 Ns240p390 Ns240p146 Ns240p390 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 7649524) qz368 0 1 Ns240p390 Ns240p147 Ns240p390 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p392 := nat_lit 40143121973186615010738976321 

noncomputable def Ns240p393 := BSN.cos_dyadic_bound_f 14154769 134217728 2 1 134217728 67108864 Ns240p392 Ns240p146 Ns240p392 Ns240p392 Ns240p147 Ns240p392 133472029 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 14154769) qz367 0 1 Ns240p392 Ns240p146 Ns240p392 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 14154769) qz368 0 1 Ns240p392 Ns240p147 Ns240p392 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p394 := Ns240p350 55957 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 114 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133999800 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133472029 134217728) qz57 rfl rfl (Ns240p383 RS241to252.d9 RS241to252.d11 RS241to252.d13 RS241to252.d17 (Ns240p385 rfl rfl) (Ns240p389 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns240p382 rfl) RS241to252.d19 RS241to252.d21 RS241to252.d23 RS241to252.d25 RS241to252.d17 (Ns240p391 rfl rfl) (Ns240p393 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns240p395 := BSN.cos_dyadic_bound_f 876874 134217728 1 0 134217728 67108864 0 1 1 0 1 1 134214863 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 876874) qz367 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 876874) qz368 0 0 rfl) rfl rfl 

noncomputable def Ns240p396 := nat_lit 59469620407232450959515140143283705035752912550168501200941401446561 

noncomputable def Ns240p397 := nat_lit 11893754591212449416768319689064534357887343508174345420294789281 

noncomputable def Ns240p398 := nat_lit 178385073712514927979711883790472986038542962963489154911983614761121 

noncomputable def Ns240p399 := BSN.cos_dyadic_bound_f 102191523 134217728 3 2 134217728 67108864 Ns240p396 Ns240p124 Ns240p397 Ns240p398 Ns240p127 Ns240p397 97157575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 102191523) qz367 0 2 Ns240p396 Ns240p124 Ns240p397 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 102191523) qz368 0 2 Ns240p398 Ns240p127 Ns240p397 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p400 := Ns240p348 75030 BSN.abs_quadSignPos (BSN.cos_quad_nat0 24 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 134214863 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 76 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 97157575 134217728) qz57 rfl rfl (Ns240p394 rfl rfl) (Ns240p382 rfl) RS241to252.d27 RS241to252.d29 RS241to252.d31 RS241to252.d33 RS241to252.d17 (Ns240p395 rfl rfl) (Ns240p399 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p401 := nat_lit 8640504670872267024125986076769356918580125156270549923904144458717680702921430696723899879025624603426816 

noncomputable def Ns240p402 := nat_lit 3933582208927468110161877611523957771468692585289986732823434795014639196695866594555599156534050816 

noncomputable def Ns240p403 := nat_lit 43159616386704608906728438641761944065349265908416783301639741926412350623476239928842648249122736283058176 

noncomputable def Ns240p404 := BSN.sin_dyadic_bound_f 199326796 134217728 4 3 134217728 67108864 Ns240p401 Ns240p118 Ns240p402 Ns240p403 Ns240p121 Ns240p402 133725195 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 199326796) qz365 0 3 Ns240p401 Ns240p118 Ns240p402 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 199326796) qz366 0 3 Ns240p403 Ns240p121 Ns240p402 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p405 := nat_lit 7820148745342513823267946496 

noncomputable def Ns240p406 := BSN.cos_dyadic_bound_f 9403808 134217728 2 1 134217728 67108864 Ns240p405 Ns240p146 Ns240p405 Ns240p405 Ns240p147 Ns240p405 133888429 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 9403808) qz367 0 1 Ns240p405 Ns240p146 Ns240p405 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 9403808) qz368 0 1 Ns240p405 Ns240p147 Ns240p405 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz642 := (BSN.cos_quad_nat1 121 rfl)

noncomputable def Ns240p407 := Ns240p346 91695 BSN.abs_quadSignNeg qz642 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133725195 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 162 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133888429 134217728) qz57 rfl rfl (Ns240p400 rfl) (Ns240p382 rfl) RS241to252.d35 RS241to252.d37 RS241to252.d39 RS241to252.d41 RS241to252.d17 (Ns240p404 rfl rfl) (Ns240p406 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p408 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz54) qz54 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz54) qz54 9) 278727558 134217728 91695 134217728 278727558 134217728 91695 134217728 74820359131496448 139363779 33554432 91695 67108864 (Ns240p407 rfl) 

noncomputable def Ns240p409 := @Enclosure.Real.IsNear.mulLit_tf qz399 (Zeta.RiemannSiegel.correction qz56) 5523593 16777216 1 16777216 74006705491761 140737488355328 212711734797827 1424967069597696000 408782920407352617273 2361183241434822606848 

noncomputable abbrev qz403 := (@HPow.hPow Real Real Real qz618 qz55 qz8)

noncomputable def Ns240p410 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz403 1 1 0 1 5523593 16777216 1 16777216 5523593 16777216 1 16777216 

noncomputable def Ns240p411 := @Enclosure.Real.IsNear.sqrt_image qz55 1427949245529 16777216000 534777 16777216000 77390251 77390281 8388608 (@Enclosure.Real.IsNear.of_eq qz55 (@HMul.hMul Real Real Real qz5 qz54 qz3) Bool.false 1427949245529 16777216000 534777 16777216000 (BSN.t_div_two_pi_mk qz54 534777 1000 qz57) (@Enclosure.Real.IsNear.mulLit_ff qz54 qz3 534777 1000 0 1 2670177 16777216 1 16777216 1427949245529 16777216000 534777 16777216000 (Enclosure.Real.IsNear.const Bool.false 534777 1000) RS241to252.d44 rfl)) 

noncomputable abbrev qz825 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 534777 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz643 := qz825

noncomputable abbrev qz404 := qz643

noncomputable abbrev qz61 := qz404

noncomputable def Ns240p412 := @Enclosure.Real.IsNear.sqrt_image qz61 38695133 4194304 15 8388608 25479334 25479340 8388608 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 154780532 16777216 30 16777216 38695133 4194304 15 8388608 (Ns240p411 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns240p413 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz61) 25479337 8388608 3 8388608 2761796 2761797 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz61) Bool.false 50958674 16777216 6 16777216 25479337 8388608 3 8388608 (Ns240p412 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns240p414 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz61)) Bool.false 5523593 16777216 1 16777216 5523593 16777216 1 16777216 (Ns240p413 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz62 := (@HMul.hMul Real Real Real qz344 qz340 qz398)

noncomputable abbrev qz644 := (@HMul.hMul Real Real Real qz811 qz824 qz824)

noncomputable abbrev qz405 := (@HSub.hSub Real Real Real qz619 (@HSub.hSub Real Real Real qz619 qz644 qz639) qz626)

noncomputable abbrev qz63 := (Real.cos (@HMul.hMul Real Real Real qz344 qz340 qz405))

noncomputable def Ns240p415 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz56) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz62)) qz63) Bool.false 74006705491761 

noncomputable def Ns240p416 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz62)) qz63 110036183 16777216 8397 

noncomputable def Ns240p417 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz62)) Bool.false 110036183 16777216 8397 16777216 110036183 16777216 8397 

noncomputable def Ns240p418 := @Enclosure.Real.IsNear.recentre' (Real.cos qz62) Bool.false 1279011 8388608 316188608 27179089920000 1279011 8388608 4940447 424673280000 

noncomputable abbrev qz406 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable def Ns240p419 := @Enclosure.Real.IsNear.cos_image qz62 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11892775) qz406) Bool.false 11892775 8388608 95 8388608 Bool.false 1279011 8388608 1 

noncomputable def Ns240p420 := nat_lit 404791131151919658483664553 

noncomputable def Ns240p421 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz56 884279719003555 140737488355328 1 500000000000000 946397 4194304 15 8388608 836879673225807441335 590295810358705651712 Ns240p420 

noncomputable def Ns240p422 := @Enclosure.Real.IsNear.subLit_ff_p qz61 qz1 38695133 4194304 15 8388608 9 1 0 1 946397 946397 4194304 15 

noncomputable def Ns240p423 := @Ns240p422 8388608 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 154780532 16777216 30 16777216 38695133 4194304 15 8388608 (Ns240p411 rfl rfl rfl rfl rfl rfl) rfl) qz373 

noncomputable def Ns240p424 := @Enclosure.Real.IsNear.recentre' qz62 Bool.false 836879673225807441335 590295810358705651712 Ns240p420 Ns240p165 11892775 8388608 95 8388608 (@Ns240p421 Ns240p165 RS241to252.d43 (Ns240p423 rfl rfl) rfl) 

noncomputable def Ns240p425 := nat_lit 9813438168451884962706751876420658902626525403826750908497598920998133648275489797275390625 

noncomputable def Ns240p426 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600 

noncomputable def Ns240p427 := nat_lit 8005683753192860640355956460697718351561724229008711099391999277420103549957275390625 

noncomputable def Ns240p428 := nat_lit 59439603719970663507020528629230013859816737473095449835844527418532709324666651653275390625 

noncomputable def Ns240p429 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600 

noncomputable def Ns240p430 := BSN.cos_dyadic_bound_f 11892775 8388608 4 3 8388608 3240000 Ns240p425 Ns240p426 Ns240p427 Ns240p428 Ns240p429 Ns240p427 1279011 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 11892775) (BSN.cosEvenQ 8388608) 0 3 Ns240p425 Ns240p426 Ns240p427 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 11892775) (BSN.cosOddQ 8388608) 0 3 Ns240p428 Ns240p429 Ns240p427 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p431 := @Enclosure.Real.IsNear.inv_image (Real.cos qz62) 1279011 8388608 4940447 424673280000 55013893 55022290 8388608 (Ns240p418 (@Ns240p419 3240000 (Ns240p424 rfl) (Enclosure.sfrac_false_div 11892775 8388608) (Ns240p430 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns240p432 := @Enclosure.Real.IsNear.recentre' qz63 Bool.false 672567 8388608 

noncomputable abbrev qz64 := (@HMul.hMul Real Real Real qz344 qz340 qz405)

noncomputable def Ns240p433 := @Enclosure.Real.IsNear.cos_image qz64 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 25007009)) qz363) Bool.true 25007009 16777216 

noncomputable def Ns240p434 := nat_lit 3690383182078715208144779525 

noncomputable def Ns240p435 := nat_lit 2475880078570760549798248448 

noncomputable def Ns240p436 := nat_lit 985602528303519397004758117395839 

noncomputable def Ns240p437 := @Enclosure.Real.IsNear.recentre' qz64 Bool.true Ns240p434 Ns240p435 Ns240p436 

noncomputable def Ns240p438 := nat_lit 60446290980731458735308800000000000000 

noncomputable abbrev qz65 := qz405

noncomputable def Ns240p439 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz65 884279719003555 140737488355328 1 500000000000000 4173321068855 

noncomputable abbrev qz407 := (@HSub.hSub Real Real Real qz619 qz644 qz639)

noncomputable abbrev qz66 := qz407

noncomputable def Ns240p440 := @Enclosure.Real.IsNear.subLit_tf qz66 qz27 3073809441079 17592186044416 182613165 70368744177664 1 16 

noncomputable abbrev qz408 := qz644

noncomputable abbrev qz67 := qz408

noncomputable def Ns240p441 := @Enclosure.Real.IsNear.subLit_ff_n qz67 qz56 895667281609 17592186044416 56784045 70368744177664 946397 4194304 15 8388608 

noncomputable def Ns240p442 := @Enclosure.Real.IsNear.mulLit_ff qz56 qz56 946397 4194304 15 8388608 946397 4194304 15 8388608 895667281609 17592186044416 

noncomputable def Ns240p443 := nat_lit 49136760988277849835263634787432879912393866311456264201264794166002986174925279444671589004161 

noncomputable def Ns240p444 := nat_lit 59805483374911844577071572751764730294114689020866308940263807114243393271622966970692481 

noncomputable def Ns240p445 := nat_lit 297513878214414002959476587118426513203705372154044981424765394538933164174359030170139865920385 

noncomputable def Ns240p446 := BSN.cos_dyadic_bound_f 25007009 16777216 4 3 8388608 3240000 Ns240p443 Ns240p303 Ns240p444 Ns240p445 Ns240p306 Ns240p444 672567 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 25007009) qz627 0 3 Ns240p443 Ns240p303 Ns240p444 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 25007009) (BSN.cosOddQ 16777216) 0 3 Ns240p445 Ns240p306 Ns240p444 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p447 := @Ns240p432 452268608 27179089920000 672567 8388608 7066697 424673280000 (@Ns240p433 137 8388608 Bool.false 672567 8388608 1 3240000 (@Ns240p437 Ns240p438 25007009 16777216 137 8388608 (@Ns240p439 17592186044416 182613165 70368744177664 Ns240p434 Ns240p435 Ns240p436 Ns240p438 RS241to252.d43 (@Ns240p440 0 1 66773137101680 4173321068855 17592186044416 182613165 70368744177664 (@Ns240p441 12892491233955414016 3073809441079 17592186044416 182613165 70368744177664 (@Ns240p442 56784045 70368744177664 (Ns240p423 rfl rfl) (Ns240p423 rfl rfl) rfl) (Ns240p423 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 25007009 16777216) (BSN.cos_neg_of_bound 25007009 16777216 Bool.false 672567 8388608 1 3240000 (Ns240p446 rfl rfl)) rfl rfl) 

noncomputable def Ns240p448 := @Ns240p409 391894193317324170121 Ns240p342 (Ns240p410 qz29 (@Enclosure.Real.IsNear.of_eq qz403 (@Inv.inv Real Real.instInv (Real.sqrt qz61)) Bool.false 5523593 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz55 (BSN.t_div_two_pi_nonneg qz54 534777 1000 qz57)) Ns240p414) rfl) (@Ns240p415 140737488355328 212711734797827 1424967069597696000 (BSN.correction_mk qz56 (BSN.cos_two_pi_p_ne_zero_mk qz54 534777 1000 9 qz57 rfl rfl (@BSN.floor_sqrt_eq_dec qz54 534777 1000 9 qz57 rfl rfl rfl))) (@Ns240p416 16777216 672567 8388608 7066697 424673280000 74006705491761 140737488355328 212711734797827 1424967069597696000 (@Ns240p417 16777216 (Ns240p431 rfl rfl rfl rfl rfl) rfl) (Ns240p447 rfl) rfl)) 

noncomputable def Ns240p449 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz54) (hardyZApproximantRS₀ qz54) Bool.true 9398071191676149814983 2361183241434822606848 11280423813880718730121 Ns240p342 (@Eq.refl Real (hardyZApproximantRS₀ qz54)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz54) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz54) qz54 9) (@HMul.hMul Real Real Real qz5 qz399 (Zeta.RiemannSiegel.correction qz56))) Bool.true 9398071191676149814983 2361183241434822606848 11280423813880718730121 Ns240p342 (BSN.hardyZApproximantRS₀_eq qz54 9 (@BSN.floor_sqrt_eq_dec qz54 534777 1000 9 qz57 rfl rfl rfl)) (@Ns240p344 9398071191676149814983 2361183241434822606848 11280423813880718730121 Ns240p342 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz54) qz54 9) (@HAdd.hAdd Real Real Real qz360 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz54) qz54 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz54) qz54 9)) Bool.true 139363779 33554432 91695 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz54) qz54 9) (Ns240p408 (Ns240p407 rfl) rfl rfl)) (Ns240p448 rfl) rfl rfl)) 

theorem RS241to252.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz54) Bool.true 9398071191676149814983 2361183241434822606848 11280423813880718730121 Ns240p342 := Ns240p449 

noncomputable def Ns240p450 := nat_lit 171302125464994717917773824 

noncomputable abbrev qz826 := (Enclosure.sfrac Bool.false 536191 1000)

noncomputable abbrev qz645 := qz826

noncomputable abbrev qz409 := qz645

noncomputable abbrev qz68 := qz409

noncomputable abbrev qz827 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 536191 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz646 := qz827

noncomputable abbrev qz410 := qz646

noncomputable abbrev qz69 := qz410

noncomputable abbrev qz828 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 536191 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz647 := qz828

noncomputable abbrev qz411 := qz647

noncomputable abbrev qz70 := qz411

noncomputable abbrev qz412 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz618 qz69 qz8))

noncomputable def Ns240p451 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz68) qz68 9) (@HMul.hMul Real Real Real qz5 qz412 (Zeta.RiemannSiegel.correction qz70)) 17158013 8388608 45967 33554432 1555369872189044415 9223372036854775808 14763913319714427407 149418626997047368089600 Ns240p450 

noncomputable def Ns240p452 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz68) qz68 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 536191 1000 121 162 134217728 67108864 2251799813685248 Bool.false 123967369260 1778 

noncomputable def Ns240p453 := Ns240p452 279097919 42 47453128 8 294906479 42 44739240 8 Bool.false 227473477 75224 Bool.true 172148616 Bool.true 4578931 7074237752028440 1 Bool.false 128682603 Bool.true Bool.false 134139628 Bool.true Bool.false 137264104 

noncomputable def Ns240p454 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz68) qz68 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 536191 1000 23 76 134217728 67108864 2251799813685248 Bool.false 123967369260 1778 

noncomputable def Ns240p455 := Ns240p454 240485871 42 54794152 8 261175631 42 50729528 8 Bool.false 135039868 56101 Bool.true 129929972 Bool.true 49671227 7074237752028440 1 Bool.false 110566406 Bool.false Bool.false 125131000 Bool.false Bool.false 227473477 

noncomputable def Ns240p456 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz68) qz68 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 536191 1000 114 38 134217728 67108864 2251799813685248 Bool.false 123967369260 1778 

noncomputable def Ns240p457 := Ns240p456 186065264 42 67108856 8 216015088 42 60023992 8 Bool.false 190667834 33065 Bool.false 166375879 Bool.false 130532073 7074237752028440 1 Bool.false 43644586 Bool.true Bool.false 75591789 Bool.true Bool.false 135039868 

noncomputable def Ns240p458 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz68) qz68 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 536191 1000 351 212 134217728 67108864 2251799813685248 Bool.false 123967369260 1778 

noncomputable def Ns240p459 := Ns240p458 93032624 42 94906264 8 147453232 42 77490640 16 Bool.false 134217696 1826 Bool.false 83234904 Bool.false 208585944 7074237752028440 1 Bool.false 78001424 Bool.false Bool.false 2242665 Bool.false Bool.false 190667834 

noncomputable def Ns240p460 := nat_lit 222411914240965802196751145534199643215378730406533883653 

noncomputable def Ns240p461 := nat_lit 240802252944967026580662696849120253195363974905856000 

noncomputable def Ns240p462 := nat_lit 21273541474663061550582727336480000 

noncomputable def Ns240p463 := nat_lit 68440116633885005109238675472943286080 

noncomputable abbrev qz71 := (@Eq.refl Real qz409)

noncomputable def Ns240p464 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz68 536191 1000 1150004153924 16000000 1072382 4000 2000 Ns240p462 Ns240p463 qz71 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns240p465 := nat_lit 71171812557109056702960366570943885828921193730090842768960 

noncomputable abbrev qz648 := (Real.log (Enclosure.sfrac Bool.false 1150004153924 16000000))

noncomputable abbrev qz649 := (@Nat.cast Real Real.instNatCast 1072382)

noncomputable abbrev qz650 := (Enclosure.sfrac Bool.false 536191 2000)

noncomputable abbrev qz72 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 536191 4000) qz648) (@HMul.hMul Real Real Real qz344 qz358 (@HSub.hSub Real Real Real qz350 qz355 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz356 qz649))))) qz650)

noncomputable abbrev qz413 := (@HSub.hSub Real Real Real qz11 qz72 (@HMul.hMul Real Real Real qz5 qz650 (Real.log Real.pi)))

noncomputable def Ns240p466 := @Enclosure.Real.IsNear.addLit_ft_p qz413 (Enclosure.sfrac Bool.true Ns240p462 Ns240p463) 1039914015484741729837 1125899906842624000 732043088379172769 55296000000000000000000 Ns240p462 Ns240p463 0 1 Ns240p465 

noncomputable def Ns240p467 := nat_lit 69787448236859426822755975168000 

noncomputable abbrev qz414 := (@HMul.hMul Real Real Real qz5 qz650 (Real.log Real.pi))

noncomputable def Ns240p468 := @Enclosure.Real.IsNear.subLit_ff_p qz72 qz414 1385449240616297348653 1125899906842624000 141716464162003 27000000000000000000 20595504351351 67108864000 536191 67108864000 Ns240p467 1039914015484741729837 1125899906842624000 

noncomputable abbrev qz73 := (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 536191 4000) qz648) (@HMul.hMul Real Real Real qz344 qz358 (@HSub.hSub Real Real Real qz350 qz355 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz356 qz649)))))

noncomputable def Ns240p469 := @Enclosure.Real.IsNear.subLit_ff_p qz73 qz650 337459587818244810249 225179981368524800 141716464162003 27000000000000000000 536191 2000 0 1 554179696246518939461200 1385449240616297348653 1125899906842624000 141716464162003 27000000000000000000 

noncomputable def Ns240p470 := nat_lit 759891436975424249340195303170506752 

noncomputable def Ns240p471 := nat_lit 27038079027707754515005440 

noncomputable def Ns240p472 := nat_lit 350477766514625284124251430093124512786985002192640 

noncomputable def Ns240p473 := nat_lit 248957884082994190873271290732313504983745169408 

noncomputable def Ns240p474 := nat_lit 317508487297498143693808066513680265224438528 

noncomputable def Ns240p475 := BSN.log_dyadic_bound 101428153924 2198580153924 3 2 Ns240p472 67108864 25920000 Ns240p473 Ns240p474 6196329 2300008307848 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 101428153924) (BSN.artanhQ 2198580153924) 0 2 Ns240p473 Ns240p472 Ns240p474 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns240p476 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 536191 4000) qz648 536191 4000 0 1 3147646671592695 281474976710656 195312581 5062500000000000 337547963297591744949 225179981368524800 104724848118971 20250000000000000000 (Enclosure.Real.IsNear.const Bool.false 536191 4000) (BSN.isNear_log_sfrac 1150004153924 16000000 3147646671592695 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1150004153924) qz354)) Bool.false Ns240p471 Ns240p92 1000000414720000 25920000000000000000000 3147646671592695 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1150004153924 16000000 16 2300008307848 2097152000000 6196329 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns240p475 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p477 := BSN.arctan_dyadic_bound_f 1000 1072382 1 0 8388608 3240000 0 1 1 0 1 1 7822 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1072382) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1072382) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz651 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1072382)))

noncomputable def Ns240p478 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz651 884279719003555 562949953421312 1 2000000000000000 7822 8388608 1 3240000 7413472530535311998976 883754793469347 562949953421312 50000000081 162000000000000000 qz16 (Ns240p477 rfl) rfl rfl 

noncomputable def Ns240p479 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 536191 4000) qz648) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz11 qz14 qz651)) 337547963297591744949 225179981368524800 104724848118971 20250000000000000000 883754793469347 2251799813685248 50000000081 648000000000000000 Ns240p470 337459587818244810249 225179981368524800 141716464162003 27000000000000000000 (Ns240p476 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 qz651) 1 4 0 1 883754793469347 562949953421312 50000000081 162000000000000000 883754793469347 2251799813685248 50000000081 648000000000000000 qz359 Ns240p478 rfl) 

noncomputable def Ns240p480 := @Ns240p466 Ns240p460 Ns240p461 732043088379172769 55296000000000000000000 (@Ns240p468 732043088379172769 55296000000000000000000 (Ns240p469 (Ns240p479 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 536191 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz650 (Real.log Real.pi) 536191 2000 0 1 38410761 33554432 1 33554432 20595504351351 67108864000 536191 67108864000 (Enclosure.Real.IsNear.const Bool.false 536191 2000) RS241to252.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns240p462 Ns240p463) 

noncomputable def Ns240p481 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz68) Bool.false Ns240p460 Ns240p461 732043088379172769 55296000000000000000000 15495921157 16777216 223 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz68) (@HAdd.hAdd Real Real Real qz360 qz413 (Enclosure.sfrac Bool.true Ns240p462 Ns240p463)) Bool.false Ns240p460 Ns240p461 732043088379172769 55296000000000000000000 Ns240p464 (Ns240p480 rfl rfl)) 

noncomputable def Ns240p482 := BSN.cos_dyadic_bound_f 21848500 34359738368 1 0 16777216 6486329 0 1 1 0 1 1 16777212 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 21848500) (BSN.cosEvenQ 34359738368) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 21848500) (BSN.cosOddQ 34359738368) 0 0 rfl) rfl rfl 

noncomputable def Ns240p483 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz68) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15495921157) qz363) Bool.false 15495921157 16777216 223 16777216 Bool.false 16777212 16777216 1 3240000 (Ns240p481 rfl) (Enclosure.sfrac_false_div 15495921157 16777216) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15495921157) qz363) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1537451522129357963264) qz364) 226375608064910080 72057594037927936 Bool.false 16777212 16777216 147 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q0 15495921157 16777216 226375608064910080 72057594037927936 147 1537451522129357963264 Ns240p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777212 16777216 1537451522129357963264 Ns240p92 21848500 34359738368 6486329 6480000 (Ns240p482 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns240p484 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz68) Bool.false Ns240p460 Ns240p461 732043088379172769 55296000000000000000000 123967369260 134217728 1778 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz68) (@HAdd.hAdd Real Real Real qz360 qz413 (Enclosure.sfrac Bool.true Ns240p462 Ns240p463)) Bool.false Ns240p460 Ns240p461 732043088379172769 55296000000000000000000 Ns240p464 (Ns240p480 rfl rfl)) 

noncomputable def Ns240p485 := Ns240p459 33065 BSN.abs_quadSignPos (BSN.cos_quad_nat3 351 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 78001424 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 212 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 2242665 134217728) qz71 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz68) qz68 1) Bool.false 4194303 4194304 11551519 849346560000 134217696 134217728 1826 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz68) qz68 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz68)) Bool.false 4194303 4194304 11551519 849346560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz68) qz68) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz68)) Bool.false 16777212 16777216 739297216 54358179840000 4194303 4194304 11551519 849346560000 (Ns240p483 rfl rfl) rfl)) rfl) (Ns240p484 rfl) RS241to252.d7 

noncomputable def Ns240p486 := nat_lit 47104727027153722450272117258837294491657400893885981029424745676800 

noncomputable def Ns240p487 := nat_lit 2303795171824943790337585065336305793544960870815591434431758336 

noncomputable def Ns240p488 := nat_lit 123365793212267270794099760540182369649722691452101010786170968211456 

noncomputable def Ns240p489 := BSN.sin_dyadic_bound_f 83234904 134217728 3 2 134217728 67108864 Ns240p486 Ns240p248 Ns240p487 Ns240p488 Ns240p251 Ns240p487 78001424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 83234904) qz365 0 2 Ns240p486 Ns240p248 Ns240p487 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 83234904) qz366 0 2 Ns240p488 Ns240p251 Ns240p487 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p490 := nat_lit 3992555662566278415664552151984661854766826759409600451695198793037297423061873547136247998841175530274816 

noncomputable def Ns240p491 := nat_lit 6782978973744542756169463272164045123917250373218443277345498646740708716428268458550649435178663936 

noncomputable def Ns240p492 := nat_lit 24165597864523237675993720314643843924563793921448440320879506381601016398197684715718741610274421211136000 

noncomputable def Ns240p493 := BSN.cos_dyadic_bound_f 208585944 134217728 4 3 134217728 67108864 Ns240p490 Ns240p130 Ns240p491 Ns240p492 Ns240p133 Ns240p491 2242665 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 208585944) qz367 0 3 Ns240p490 Ns240p130 Ns240p491 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 208585944) qz368 0 3 Ns240p492 Ns240p133 Ns240p491 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p494 := nat_lit 1612784368707580104670698619500173200687791340937575407939267851287347982874779932437653501925471082220321 

noncomputable def Ns240p495 := nat_lit 449867226725483975812884843376639927802527407675119151423659503054259422698725730436717562374359841 

noncomputable def Ns240p496 := nat_lit 9775068325039103116588090612348170055305977462574708141040373981667112877782318639570070684798399352900385 

noncomputable def Ns240p497 := BSN.cos_dyadic_bound_f 166375879 134217728 4 3 134217728 67108864 Ns240p494 Ns240p130 Ns240p495 Ns240p496 Ns240p133 Ns240p495 43644586 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 166375879) qz367 0 3 Ns240p494 Ns240p130 Ns240p495 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 166375879) qz368 0 3 Ns240p496 Ns240p133 Ns240p495 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p498 := nat_lit 158361262215254664021913866891855027992863498459800198462296317175361 

noncomputable def Ns240p499 := nat_lit 84282591616355367836490383747535360462595648976482969704456726081 

noncomputable def Ns240p500 := nat_lit 474915221462531281330068619908070013257665304081447629447480038073921 

noncomputable def Ns240p501 := BSN.cos_dyadic_bound_f 130532073 134217728 3 2 134217728 67108864 Ns240p498 Ns240p124 Ns240p499 Ns240p500 Ns240p127 Ns240p499 75591789 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 130532073) qz367 0 2 Ns240p498 Ns240p124 Ns240p499 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 130532073) qz368 0 2 Ns240p500 Ns240p127 Ns240p499 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p502 := Ns240p457 56101 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 114 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 43644586 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 75591789 134217728) qz71 rfl rfl (Ns240p485 RS241to252.d9 RS241to252.d11 RS241to252.d13 RS241to252.d17 (Ns240p489 rfl rfl) (Ns240p493 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns240p484 rfl) RS241to252.d19 RS241to252.d21 RS241to252.d23 RS241to252.d25 RS241to252.d17 (Ns240p497 rfl rfl) (Ns240p501 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns240p503 := nat_lit 279759475083400767673073851450944238796027185337035577459535998156800 

noncomputable def Ns240p504 := nat_lit 81222201902658067755572549339685744302413772138704686074088718336 

noncomputable def Ns240p505 := nat_lit 732571884510588183224541541101161134213105386918297180997521946771456 

noncomputable def Ns240p506 := BSN.sin_dyadic_bound_f 129929972 134217728 3 2 134217728 67108864 Ns240p503 Ns240p248 Ns240p504 Ns240p505 Ns240p251 Ns240p504 110566406 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 129929972) qz365 0 2 Ns240p503 Ns240p248 Ns240p504 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 129929972) qz366 0 2 Ns240p505 Ns240p251 Ns240p504 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p507 := nat_lit 3318739890361780119638785571779747120286098473592305099699804142561 

noncomputable def Ns240p508 := nat_lit 37054342038800669360171417712491229598137041589809808792845281 

noncomputable def Ns240p509 := nat_lit 9956145562401262757577636372503816378399099146693735679481826737121 

noncomputable def Ns240p510 := BSN.cos_dyadic_bound_f 49671227 134217728 3 2 134217728 67108864 Ns240p507 Ns240p124 Ns240p508 Ns240p509 Ns240p127 Ns240p508 125131000 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 49671227) qz367 0 2 Ns240p507 Ns240p124 Ns240p508 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 49671227) qz368 0 2 Ns240p509 Ns240p127 Ns240p508 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p511 := Ns240p455 75224 BSN.abs_quadSignPos (BSN.cos_quad_nat3 23 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 110566406 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 76 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 125131000 134217728) qz71 rfl rfl (Ns240p502 rfl rfl) (Ns240p484 rfl) RS241to252.d27 RS241to252.d29 RS241to252.d31 RS241to252.d33 RS241to252.d17 (Ns240p506 rfl rfl) (Ns240p510 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p512 := nat_lit 4803754781747105095000216307958363822670097713341885114114842093898002235643026100005379177324333190086656 

noncomputable def Ns240p513 := nat_lit 677395685504514358334235778574564593248793591763746773687540489740845919005796727869633060306681856 

noncomputable def Ns240p514 := nat_lit 24005495074200980880127639786564266635913695381604903496243784859523237612705043881824081466418326526754816 

noncomputable def Ns240p515 := BSN.sin_dyadic_bound_f 172148616 134217728 4 3 134217728 67108864 Ns240p512 Ns240p118 Ns240p513 Ns240p514 Ns240p121 Ns240p513 128682603 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 172148616) qz365 0 3 Ns240p512 Ns240p118 Ns240p513 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 172148616) qz366 0 3 Ns240p514 Ns240p121 Ns240p513 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p516 := nat_lit 439598697267980425457823121 

noncomputable def Ns240p517 := BSN.cos_dyadic_bound_f 4578931 134217728 2 1 134217728 67108864 Ns240p516 Ns240p146 Ns240p516 Ns240p516 Ns240p147 Ns240p516 134139628 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 4578931) qz367 0 1 Ns240p516 Ns240p146 Ns240p516 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 4578931) qz368 0 1 Ns240p516 Ns240p147 Ns240p516 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p518 := Ns240p453 91934 BSN.abs_quadSignNeg qz642 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 128682603 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 162 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 134139628 134217728) qz71 rfl rfl (Ns240p511 rfl) (Ns240p484 rfl) RS241to252.d35 RS241to252.d37 RS241to252.d39 RS241to252.d41 RS241to252.d17 (Ns240p515 rfl rfl) (Ns240p517 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p519 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz68) qz68 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz68) qz68 9) 137264104 134217728 91934 134217728 137264104 134217728 91934 134217728 36846552349671424 17158013 8388608 45967 33554432 (Ns240p518 rfl) 

noncomputable def Ns240p520 := @Enclosure.Real.IsNear.mulLit_tf qz412 (Zeta.RiemannSiegel.correction qz70) 1379987 4194304 1 8388608 1127090235045 2199023255552 133649615384293 445302209249280000 1555369872189044415 9223372036854775808 

noncomputable abbrev qz415 := (@HPow.hPow Real Real Real qz618 qz69 qz8)

noncomputable def Ns240p521 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz415 1 1 0 1 1379987 4194304 1 8388608 1379987 4194304 1 8388608 

noncomputable def Ns240p522 := @Enclosure.Real.IsNear.sqrt_image qz69 1431724875807 16777216000 536191 16777216000 77492497 77492527 8388608 (@Enclosure.Real.IsNear.of_eq qz69 (@HMul.hMul Real Real Real qz5 qz68 qz3) Bool.false 1431724875807 16777216000 536191 16777216000 (BSN.t_div_two_pi_mk qz68 536191 1000 qz71) (@Enclosure.Real.IsNear.mulLit_ff qz68 qz3 536191 1000 0 1 2670177 16777216 1 16777216 1431724875807 16777216000 536191 16777216000 (Enclosure.Real.IsNear.const Bool.false 536191 1000) RS241to252.d44 rfl)) 

noncomputable abbrev qz829 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 536191 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz652 := qz829

noncomputable abbrev qz416 := qz652

noncomputable abbrev qz74 := qz416

noncomputable def Ns240p523 := @Enclosure.Real.IsNear.sqrt_image qz74 2421641 262144 15 8388608 25496160 25496166 8388608 (@Enclosure.Real.IsNear.recentre' qz74 Bool.false 154985024 16777216 30 16777216 2421641 262144 15 8388608 (Ns240p522 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns240p524 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz74) 25496163 8388608 3 8388608 2759973 2759975 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz74) Bool.false 50992326 16777216 6 16777216 25496163 8388608 3 8388608 (Ns240p523 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns240p525 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz74)) Bool.false 5519948 16777216 2 16777216 1379987 4194304 1 8388608 (Ns240p524 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz75 := (@HMul.hMul Real Real Real qz344 qz340 qz411)

noncomputable abbrev qz653 := (@HMul.hMul Real Real Real qz811 qz828 qz828)

noncomputable abbrev qz417 := (@HSub.hSub Real Real Real qz619 (@HSub.hSub Real Real Real qz619 qz653 qz647) qz626)

noncomputable abbrev qz76 := (Real.cos (@HMul.hMul Real Real Real qz344 qz340 qz417))

noncomputable def Ns240p526 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz70) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz75)) qz76) Bool.false 1127090235045 

noncomputable def Ns240p527 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz75)) qz76 27446493 2097152 8315 

noncomputable def Ns240p528 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz75)) Bool.false 219571944 16777216 33260 16777216 27446493 2097152 8315 

noncomputable def Ns240p529 := @Enclosure.Real.IsNear.recentre' (Real.cos qz75) Bool.false 640963 8388608 629137216 54358179840000 640963 8388608 9830269 849346560000 

noncomputable abbrev qz418 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable def Ns240p530 := @Enclosure.Real.IsNear.cos_image qz75 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6267603) qz418) Bool.false 6267603 4194304 189 16777216 Bool.false 640963 8388608 1 

noncomputable def Ns240p531 := nat_lit 80958226230559588987191637 

noncomputable def Ns240p532 := nat_lit 7205759403792793600000000000000 

noncomputable def Ns240p533 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz70 884279719003555 140737488355328 1 500000000000000 62345 262144 15 8388608 55130419081276636475 36893488147419103232 Ns240p531 

noncomputable def Ns240p534 := @Enclosure.Real.IsNear.subLit_ff_p qz74 qz1 2421641 262144 15 8388608 9 1 0 1 62345 62345 262144 15 

noncomputable def Ns240p535 := @Ns240p534 8388608 (@Enclosure.Real.IsNear.recentre' qz74 Bool.false 154985024 16777216 30 16777216 2421641 262144 15 8388608 (Ns240p522 rfl rfl rfl rfl rfl rfl) rfl) qz373 

noncomputable def Ns240p536 := @Enclosure.Real.IsNear.recentre' qz75 Bool.false 55130419081276636475 36893488147419103232 Ns240p531 Ns240p532 6267603 4194304 189 16777216 (@Ns240p533 Ns240p532 RS241to252.d43 (Ns240p535 rfl rfl) rfl) 

noncomputable def Ns240p537 := nat_lit 2958683258182547313375036043375259753273172844066365003810778227696553372315134960342321 

noncomputable def Ns240p538 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600 

noncomputable def Ns240p539 := nat_lit 3674665036040326180045647758084416792124436535834533082327241562588780949402817841 

noncomputable def Ns240p540 := nat_lit 17913916412472864657036624206785147814993303747991364310756786290501783732146712547169585 

noncomputable def Ns240p541 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600 

noncomputable def Ns240p542 := BSN.cos_dyadic_bound_f 6267603 4194304 4 3 8388608 3240000 Ns240p537 Ns240p538 Ns240p539 Ns240p540 Ns240p541 Ns240p539 640963 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 6267603) (BSN.cosEvenQ 4194304) 0 3 Ns240p537 Ns240p538 Ns240p539 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 6267603) (BSN.cosOddQ 4194304) 0 3 Ns240p540 Ns240p541 Ns240p539 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p543 := @Enclosure.Real.IsNear.inv_image (Real.cos qz75) 640963 8388608 9830269 849346560000 109769342 109802602 8388608 (Ns240p529 (@Ns240p530 3240000 (Ns240p536 rfl) (Enclosure.sfrac_false_div 6267603 4194304) (Ns240p542 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns240p544 := @Enclosure.Real.IsNear.recentre' qz76 Bool.false 328520 8388608 

noncomputable abbrev qz77 := (@HMul.hMul Real Real Real qz344 qz340 qz417)

noncomputable def Ns240p545 := @Enclosure.Real.IsNear.cos_image qz77 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6424095)) qz418) Bool.true 6424095 4194304 

noncomputable def Ns240p546 := nat_lit 14812955075656329123805805 

noncomputable def Ns240p547 := nat_lit 9671406556917033397649408 

noncomputable def Ns240p548 := nat_lit 5010789189509743478001102192246823 

noncomputable def Ns240p549 := @Enclosure.Real.IsNear.recentre' qz77 Bool.true Ns240p546 Ns240p547 Ns240p548 

noncomputable abbrev qz78 := qz417

noncomputable def Ns240p550 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz78 884279719003555 140737488355328 1 500000000000000 16751435951 

noncomputable abbrev qz419 := (@HSub.hSub Real Real Real qz619 qz653 qz647)

noncomputable abbrev qz79 := qz419

noncomputable def Ns240p551 := @Enclosure.Real.IsNear.subLit_tf qz79 qz27 12456468655 68719476736 185680545 70368744177664 1 16 

noncomputable abbrev qz420 := qz653

noncomputable abbrev qz80 := qz420

noncomputable def Ns240p552 := @Enclosure.Real.IsNear.subLit_ff_n qz80 qz70 3886899025 68719476736 59851425 70368744177664 62345 262144 15 8388608 

noncomputable def Ns240p553 := @Enclosure.Real.IsNear.mulLit_ff qz70 qz70 62345 262144 15 8388608 62345 262144 15 8388608 3886899025 68719476736 

noncomputable def Ns240p554 := nat_lit 3266432675327187793772225542858937166932338663752767893240950855726601687979106606890625 

noncomputable def Ns240p555 := nat_lit 4940187771990000923012041409376175324496191368200042036081981960786367324462890625 

noncomputable def Ns240p556 := nat_lit 19773200110103267486907440243127640859430382879084508599001982120644742007317019336490625 

noncomputable def Ns240p557 := BSN.cos_dyadic_bound_f 6424095 4194304 4 3 8388608 3240000 Ns240p554 Ns240p538 Ns240p555 Ns240p556 Ns240p541 Ns240p555 328520 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 6424095) (BSN.cosEvenQ 4194304) 0 3 Ns240p554 Ns240p538 Ns240p555 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 6424095) (BSN.cosOddQ 4194304) 0 3 Ns240p556 Ns240p541 Ns240p555 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p558 := @Ns240p544 115497152 6794772480000 41065 1048576 1804643 106168320000 (@Ns240p545 35 2097152 Bool.false 328520 8388608 1 3240000 (@Ns240p549 Ns240p183 6424095 4194304 35 2097152 (@Ns240p550 68719476736 185680545 70368744177664 Ns240p546 Ns240p547 Ns240p548 Ns240p183 RS241to252.d43 (@Ns240p551 0 1 268022975216 16751435951 68719476736 185680545 70368744177664 (@Ns240p552 3265388519096320 12456468655 68719476736 185680545 70368744177664 (@Ns240p553 59851425 70368744177664 (Ns240p535 rfl rfl) (Ns240p535 rfl rfl) rfl) (Ns240p535 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6424095 4194304) (BSN.cos_neg_of_bound 6424095 4194304 Bool.false 328520 8388608 1 3240000 (Ns240p557 rfl rfl)) rfl rfl) 

noncomputable def Ns240p559 := @Ns240p520 14763913319714427407 149418626997047368089600 (Ns240p521 qz29 (@Enclosure.Real.IsNear.of_eq qz415 (@Inv.inv Real Real.instInv (Real.sqrt qz74)) Bool.false 1379987 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz69 (BSN.t_div_two_pi_nonneg qz68 536191 1000 qz71)) Ns240p525) rfl) (@Ns240p526 2199023255552 133649615384293 445302209249280000 (BSN.correction_mk qz70 (BSN.cos_two_pi_p_ne_zero_mk qz68 536191 1000 9 qz71 rfl rfl (@BSN.floor_sqrt_eq_dec qz68 536191 1000 9 qz71 rfl rfl rfl))) (@Ns240p527 4194304 41065 1048576 1804643 106168320000 1127090235045 2199023255552 133649615384293 445302209249280000 (@Ns240p528 4194304 (Ns240p543 rfl rfl rfl rfl rfl) rfl) (Ns240p558 rfl) rfl)) 

noncomputable def Ns240p560 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz68) (hardyZApproximantRS₀ qz68) Bool.false 20420804675220813503 9223372036854775808 219455979845330965007 149418626997047368089600 (@Eq.refl Real (hardyZApproximantRS₀ qz68)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz68) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz68) qz68 9) (@HMul.hMul Real Real Real qz5 qz412 (Zeta.RiemannSiegel.correction qz70))) Bool.false 20420804675220813503 9223372036854775808 219455979845330965007 149418626997047368089600 (BSN.hardyZApproximantRS₀_eq qz68 9 (@BSN.floor_sqrt_eq_dec qz68 536191 1000 9 qz71 rfl rfl rfl)) (@Ns240p451 20420804675220813503 9223372036854775808 219455979845330965007 149418626997047368089600 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz68) qz68 9) (@HAdd.hAdd Real Real Real qz360 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz68) qz68 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz68) qz68 9)) Bool.false 17158013 8388608 45967 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz68) qz68 9) (Ns240p519 (Ns240p518 rfl) rfl rfl)) (Ns240p559 rfl) rfl rfl)) 

theorem RS241to252.d50 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz68) Bool.false 20420804675220813503 9223372036854775808 219455979845330965007 149418626997047368089600 := Ns240p560 

noncomputable def Ns240p561 := nat_lit 1245155224975394734080000 

noncomputable def Ns240p562 := nat_lit 2164174793627228006766346240 

noncomputable abbrev qz830 := (Enclosure.sfrac Bool.false 537603 1000)

noncomputable abbrev qz654 := qz830

noncomputable abbrev qz421 := qz654

noncomputable abbrev qz81 := qz421

noncomputable abbrev qz831 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 537603 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz655 := qz831

noncomputable abbrev qz422 := qz655

noncomputable abbrev qz82 := qz422

noncomputable abbrev qz832 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 537603 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz656 := qz832

noncomputable abbrev qz423 := qz656

noncomputable abbrev qz83 := qz423

noncomputable abbrev qz424 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz618 qz82 qz8))

noncomputable def Ns240p563 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz81) qz81 9) (@HMul.hMul Real Real Real qz5 qz424 (Zeta.RiemannSiegel.correction qz83)) 64233645 33554432 11521 8388608 6128204668933103575 36893488147419103232 94520689084287489137933 Ns240p561 Ns240p562 

noncomputable def Ns240p564 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz81) qz81 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 537603 1000 121 161 134217728 67108864 2251799813685248 Bool.false 124388844898 1782 

noncomputable def Ns240p565 := Ns240p564 279097919 42 47453128 8 294906479 42 44739240 8 Bool.true 41909380 75415 Bool.true 144759240 Bool.true 210339956 7074237752028440 1 Bool.false 118281910 Bool.true Bool.false 134216838 Bool.true Bool.true 128467290 

noncomputable def Ns240p566 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz81) qz81 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 537603 1000 23 75 134217728 67108864 2251799813685248 Bool.false 124388844898 1782 

noncomputable def Ns240p567 := Ns240p566 240485871 42 54794152 8 261175631 42 50729528 8 Bool.true 111814690 56242 Bool.true 48020384 Bool.true 207804294 7074237752028440 1 Bool.false 47002435 Bool.false Bool.false 134183653 Bool.false Bool.true 41909380 

noncomputable def Ns240p568 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz81) qz81 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 537603 1000 115 39 134217728 67108864 2251799813685248 Bool.false 124388844898 1782 

noncomputable def Ns240p569 := Ns240p568 186065264 42 67108856 8 216015088 42 60023992 8 Bool.true 178281452 33146 Bool.false 114298650 Bool.false 36165692 7074237752028440 1 Bool.false 100975981 Bool.false Bool.false 35729635 Bool.false Bool.true 111814690 

noncomputable def Ns240p570 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz81) qz81 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 537603 1000 352 214 134217728 67108864 2251799813685248 Bool.false 124388844898 1782 

noncomputable def Ns240p571 := Ns240p570 93032624 42 94906264 8 147453232 42 77490640 16 Bool.true 134217688 1826 Bool.false 162519762 Bool.false 200190 7074237752028440 1 Bool.false 47272621 Bool.false Bool.false 134217578 Bool.true Bool.true 178281452 

noncomputable def Ns240p572 := nat_lit 25190835012243249021202435368376991172162923214019360593 

noncomputable def Ns240p573 := nat_lit 27181349296474010911155337086712915184612955652096000 

noncomputable def Ns240p574 := nat_lit 21555128034448265248440013556640000 

noncomputable def Ns240p575 := nat_lit 69528637046763065598156013544558003520 

noncomputable abbrev qz84 := (@Eq.refl Real qz421)

noncomputable def Ns240p576 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz81 537603 1000 1156068942436 16000000 1075206 4000 2000 Ns240p574 Ns240p575 qz84 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns240p577 := nat_lit 72549604835260557181063013860925734575829218856375758507840 

noncomputable abbrev qz657 := (Real.log (Enclosure.sfrac Bool.false 1156068942436 16000000))

noncomputable abbrev qz658 := (@Nat.cast Real Real.instNatCast 1075206)

noncomputable abbrev qz659 := (Enclosure.sfrac Bool.false 537603 2000)

noncomputable abbrev qz85 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 537603 4000) qz657) (@HMul.hMul Real Real Real qz344 qz358 (@HSub.hSub Real Real Real qz350 qz355 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz356 qz658))))) qz659)

noncomputable abbrev qz425 := (@HSub.hSub Real Real Real qz11 qz85 (@HMul.hMul Real Real Real qz5 qz659 (Real.log Real.pi)))

noncomputable def Ns240p578 := @Enclosure.Real.IsNear.addLit_ft_p qz425 (Enclosure.sfrac Bool.true Ns240p574 Ns240p575) 1043449608474020577417 1125899906842624000 2201878822519766231 165888000000000000000000 Ns240p574 Ns240p575 0 1 Ns240p577 

noncomputable def Ns240p579 := nat_lit 14004943573187258892615784857600 

noncomputable abbrev qz426 := (@HMul.hMul Real Real Real qz5 qz659 (Real.log Real.pi))

noncomputable def Ns240p580 := @Enclosure.Real.IsNear.subLit_ff_p qz85 qz426 277978952520162875829 225179981368524800 426252517943497 81000000000000000000 20649740345883 67108864000 537603 67108864000 Ns240p579 1043449608474020577417 1125899906842624000 

noncomputable def Ns240p581 := nat_lit 2779789525201628758290000 

noncomputable abbrev qz86 := (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 537603 4000) qz657) (@HMul.hMul Real Real Real qz344 qz358 (@HSub.hSub Real Real Real qz350 qz355 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz356 qz658)))))

noncomputable def Ns240p582 := @Enclosure.Real.IsNear.subLit_ff_p qz86 qz659 1692538346409971974281 1125899906842624000 426252517943497 81000000000000000000 537603 2000 0 1 Ns240p581 277978952520162875829 225179981368524800 426252517943497 81000000000000000000 

noncomputable def Ns240p583 := nat_lit 3811257533101112629821937084885106688 

noncomputable def Ns240p584 := nat_lit 27050796580565899473321984 

noncomputable def Ns240p585 := nat_lit 354360972342672171439777443461293969736125348458240 

noncomputable def Ns240p586 := nat_lit 281207076235376286717696511282854322479055177728 

noncomputable def Ns240p587 := nat_lit 400535541471556996421829528952294431725691648 

noncomputable def Ns240p588 := BSN.log_dyadic_bound 107492942436 2204644942436 3 2 Ns240p585 67108864 25920000 Ns240p586 Ns240p587 6549312 2312137884872 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 107492942436) (BSN.artanhQ 2204644942436) 0 2 Ns240p586 Ns240p585 Ns240p587 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns240p589 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 537603 4000) qz657 537603 4000 0 1 3149127189601527 281474976710656 195312581 5062500000000000 1692980224511349719781 1125899906842624000 35000209827781 6750000000000000000 (Enclosure.Real.IsNear.const Bool.false 537603 4000) (BSN.isNear_log_sfrac 1156068942436 16000000 3149127189601527 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1156068942436) qz354)) Bool.false Ns240p584 Ns240p92 1000000414720000 25920000000000000000000 3149127189601527 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1156068942436 16000000 16 2312137884872 2097152000000 6549312 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns240p588 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p590 := BSN.arctan_dyadic_bound_f 1000 1075206 1 0 8388608 3240000 0 1 1 0 1 1 7801 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1075206) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1075206) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz660 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1075206)))

noncomputable def Ns240p591 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz660 884279719003555 562949953421312 1 2000000000000000 7801 8388608 1 3240000 7413484352484333846528 883756202755491 562949953421312 50000000081 162000000000000000 qz16 (Ns240p590 rfl) rfl rfl 

noncomputable def Ns240p592 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 537603 4000) qz657) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz11 qz14 qz660)) 1692980224511349719781 1125899906842624000 35000209827781 6750000000000000000 883756202755491 2251799813685248 50000000081 648000000000000000 Ns240p583 1692538346409971974281 1125899906842624000 426252517943497 81000000000000000000 (Ns240p589 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 qz660) 1 4 0 1 883756202755491 562949953421312 50000000081 162000000000000000 883756202755491 2251799813685248 50000000081 648000000000000000 qz359 Ns240p591 rfl) 

noncomputable def Ns240p593 := @Ns240p578 Ns240p572 Ns240p573 2201878822519766231 165888000000000000000000 (@Ns240p580 2201878822519766231 165888000000000000000000 (Ns240p582 (Ns240p592 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 537603 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz659 (Real.log Real.pi) 537603 2000 0 1 38410761 33554432 1 33554432 20649740345883 67108864000 537603 67108864000 (Enclosure.Real.IsNear.const Bool.false 537603 2000) RS241to252.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns240p574 Ns240p575) 

noncomputable def Ns240p594 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz81) Bool.false Ns240p572 Ns240p573 2201878822519766231 165888000000000000000000 3887151403 4194304 223 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz81) (@HAdd.hAdd Real Real Real qz360 qz425 (Enclosure.sfrac Bool.true Ns240p574 Ns240p575)) Bool.false Ns240p572 Ns240p573 2201878822519766231 165888000000000000000000 Ns240p576 (Ns240p593 rfl rfl)) 

noncomputable def Ns240p595 := nat_lit 855567126539827888833336214312178015455348598612001936754695376099069973413962386405848741020037935205376727518996980182567278180438016 

noncomputable def Ns240p596 := nat_lit 607648132043760580054226574425281253195709737901762336206915235954236824315157890364269814219910146238926534285406114060741513216 

noncomputable def Ns240p597 := nat_lit 4272529598957455593651505397422475561294581376950498985713767453493851518875359849685569570368415361065705732681677993025550689608011776 

noncomputable def Ns240p598 := BSN.sin_dyadic_bound_f 53947461522 34359738368 4 3 16777216 6486329 Ns240p595 Ns240p105 Ns240p596 Ns240p597 Ns240p108 Ns240p596 16777211 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53947461522) qz361 0 3 Ns240p595 Ns240p105 Ns240p596 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53947461522) qz362 0 3 Ns240p597 Ns240p108 Ns240p596 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz661 := (@Nat.cast Real Real.instNatCast 604462909807314587353088)

noncomputable def Ns240p599 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz81) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3887151403) qz418) Bool.false 3887151403 4194304 223 16777216 Bool.true 16777211 16777216 1 3240000 (Ns240p594 rfl) (Enclosure.sfrac_false_div 3887151403 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3887151403) qz418) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949053779721189050023936) qz661) 226375608064910080 72057594037927936 Bool.false 16777211 16777216 147 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 3887151403 4194304 226375608064910080 72057594037927936 147 949053779721189050023936 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777211 16777216 949053779721189050023936 604462909807314587353088 53947461522 34359738368 6486329 6480000 (Ns240p598 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns240p600 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz81) Bool.false Ns240p572 Ns240p573 2201878822519766231 165888000000000000000000 124388844898 134217728 1782 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz81) (@HAdd.hAdd Real Real Real qz360 qz425 (Enclosure.sfrac Bool.true Ns240p574 Ns240p575)) Bool.false Ns240p572 Ns240p573 2201878822519766231 165888000000000000000000 Ns240p576 (Ns240p593 rfl rfl)) 

noncomputable def Ns240p601 := Ns240p571 33146 BSN.abs_quadSignPos (BSN.cos_quad_nat0 352 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 47272621 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 214 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 134217578 134217728) qz84 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz81) qz81 1) Bool.true 16777211 16777216 11551519 849346560000 134217688 134217728 1826 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz81) qz81 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz81)) Bool.true 16777211 16777216 11551519 849346560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz81) qz81) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz81)) Bool.true 16777211 16777216 739297216 54358179840000 16777211 16777216 11551519 849346560000 (Ns240p599 rfl rfl) rfl)) rfl) (Ns240p600 rfl) RS241to252.d7 

noncomputable def Ns240p602 := nat_lit 1468199145432263597426003385767507217256356483971716909686563649973622150234291296080082418851896674881536 

noncomputable def Ns240p603 := nat_lit 339526855968391266769914796938187644678568017738306103906782276165959215837073017307712234737504256 

noncomputable def Ns240p604 := nat_lit 8899484449811248216042850899409423232394329921845587132387297631538689611657949880366519638249405523824640 

noncomputable def Ns240p605 := BSN.cos_dyadic_bound_f 162519762 134217728 4 3 134217728 67108864 Ns240p602 Ns240p130 Ns240p603 Ns240p604 Ns240p133 Ns240p603 47272621 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 162519762) qz367 0 3 Ns240p602 Ns240p130 Ns240p603 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 162519762) qz368 0 3 Ns240p604 Ns240p133 Ns240p603 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p606 := BSN.cos_dyadic_bound_f 200190 134217728 1 0 134217728 67108864 0 1 1 0 1 1 134217578 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 200190) qz367 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 200190) qz368 0 0 rfl) rfl rfl 

noncomputable def Ns240p607 := nat_lit 167517910373479889487193575027423984571321735147833639698796900000000 

noncomputable def Ns240p608 := nat_lit 29129216756597255372188130221321580066185542385643789062500000000 

noncomputable def Ns240p609 := nat_lit 438690222722460457862523439527656867509545005937606585457414500000000 

noncomputable def Ns240p610 := BSN.sin_dyadic_bound_f 114298650 134217728 3 2 134217728 67108864 Ns240p607 Ns240p248 Ns240p608 Ns240p609 Ns240p251 Ns240p608 100975981 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 114298650) qz365 0 2 Ns240p607 Ns240p248 Ns240p608 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 114298650) qz366 0 2 Ns240p609 Ns240p251 Ns240p608 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p611 := nat_lit 1710752240651651276130348810496 

noncomputable def Ns240p612 := BSN.sin_dyadic_bound_f 36165692 134217728 2 1 134217728 67108864 Ns240p611 Ns240p114 Ns240p611 Ns240p611 Ns240p115 Ns240p611 35729635 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 36165692) qz365 0 1 Ns240p611 Ns240p114 Ns240p611 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 36165692) qz366 0 1 Ns240p611 Ns240p115 Ns240p611 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p613 := Ns240p569 56242 BSN.abs_quadSignPos (BSN.cos_quad_nat3 115 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 100975981 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 39 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 35729635 134217728) qz84 rfl rfl (Ns240p601 RS241to252.d9 RS241to252.d11 RS241to252.d13 RS241to252.d17 (Ns240p605 rfl rfl) (Ns240p606 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns240p600 rfl) RS241to252.d19 RS241to252.d21 RS241to252.d23 RS241to252.d25 RS241to252.d17 (Ns240p610 rfl rfl) (Ns240p612 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns240p614 := nat_lit 5317438974913427555201959591936 

noncomputable def Ns240p615 := BSN.sin_dyadic_bound_f 48020384 134217728 2 1 134217728 67108864 Ns240p614 Ns240p114 Ns240p614 Ns240p614 Ns240p115 Ns240p614 47002435 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 48020384) qz365 0 1 Ns240p614 Ns240p114 Ns240p614 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 48020384) qz366 0 1 Ns240p614 Ns240p115 Ns240p614 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p616 := nat_lit 10209887053544940188819983587082188359368976967758691007257792898266536993793111215122436176400865297371136 

noncomputable def Ns240p617 := nat_lit 6484167262824947984919672363365075106441034482002960054450667447287866231504880254267650297666932736 

noncomputable def Ns240p618 := nat_lit 50989557259487698327707697732964474648809242844328091168489835813771923588954004559752076521951694171344896 

noncomputable def Ns240p619 := BSN.sin_dyadic_bound_f 207804294 134217728 4 3 134217728 67108864 Ns240p616 Ns240p118 Ns240p617 Ns240p618 Ns240p121 Ns240p617 134183653 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 207804294) qz365 0 3 Ns240p616 Ns240p118 Ns240p617 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 207804294) qz366 0 3 Ns240p618 Ns240p121 Ns240p617 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p620 := Ns240p567 75415 BSN.abs_quadSignPos (BSN.cos_quad_nat3 23 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 47002435 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 75 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 134183653 134217728) qz84 rfl rfl (Ns240p613 rfl rfl) (Ns240p600 rfl) RS241to252.d27 RS241to252.d29 RS241to252.d31 RS241to252.d33 RS241to252.d17 (Ns240p615 rfl rfl) (Ns240p619 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p621 := nat_lit 431122596513037424945393445655425005528489617744025412972513853440000 

noncomputable def Ns240p622 := nat_lit 192828114567467366448777782865063330037188355319628044697600000000 

noncomputable def Ns240p623 := nat_lit 1128818412015322118168446717449093483373603074849549064760406835200000 

noncomputable def Ns240p624 := BSN.sin_dyadic_bound_f 144759240 134217728 3 2 134217728 67108864 Ns240p621 Ns240p248 Ns240p622 Ns240p623 Ns240p251 Ns240p622 118281910 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 144759240) qz365 0 2 Ns240p621 Ns240p248 Ns240p622 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 144759240) qz366 0 2 Ns240p623 Ns240p251 Ns240p622 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p625 := nat_lit 10718424508037272155478165620444725841653741540367921090841160417772625171304336249343644569513320446427136 

noncomputable def Ns240p626 := nat_lit 7500001406244743524131904651729460262284537244021175683080724897477735306020885306625179000542068736 

noncomputable def Ns240p627 := nat_lit 53526142164017620912889487367621328174128391175669652352138955674661148147184231791011762099464110285520896 

noncomputable def Ns240p628 := BSN.sin_dyadic_bound_f 210339956 134217728 4 3 134217728 67108864 Ns240p625 Ns240p118 Ns240p626 Ns240p627 Ns240p121 Ns240p626 134216838 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 210339956) qz365 0 3 Ns240p625 Ns240p118 Ns240p626 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 210339956) qz366 0 3 Ns240p627 Ns240p121 Ns240p626 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz662 := (BSN.cos_quad_nat1 161 rfl)

noncomputable def Ns240p629 := Ns240p565 92168 BSN.abs_quadSignNeg qz642 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 118281910 134217728) BSN.abs_quadSignNeg qz662 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 134216838 134217728) qz84 rfl rfl (Ns240p620 rfl) (Ns240p600 rfl) RS241to252.d35 RS241to252.d37 RS241to252.d39 RS241to252.d41 RS241to252.d17 (Ns240p624 rfl rfl) (Ns240p628 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p630 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz81) qz81 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz81) qz81 9) 128467290 134217728 92168 134217728 128467290 134217728 92168 134217728 34485175572234240 64233645 33554432 11521 8388608 (Ns240p629 rfl) 

noncomputable def Ns240p631 := @Enclosure.Real.IsNear.mulLit_tf qz424 (Zeta.RiemannSiegel.correction qz83) 172385 524288 1 8388608 35549523850295 70368744177664 822466396388120497 3562417673994240000 6128204668933103575 36893488147419103232 

noncomputable abbrev qz427 := (@HPow.hPow Real Real Real qz618 qz82 qz8)

noncomputable def Ns240p632 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz427 1 1 0 1 172385 524288 1 8388608 172385 524288 1 8388608 

noncomputable def Ns240p633 := @Enclosure.Real.IsNear.sqrt_image qz82 1435495165731 16777216000 537603 16777216000 77594464 77594494 8388608 (@Enclosure.Real.IsNear.of_eq qz82 (@HMul.hMul Real Real Real qz5 qz81 qz3) Bool.false 1435495165731 16777216000 537603 16777216000 (BSN.t_div_two_pi_mk qz81 537603 1000 qz84) (@Enclosure.Real.IsNear.mulLit_ff qz81 qz3 537603 1000 0 1 2670177 16777216 1 16777216 1435495165731 16777216000 537603 16777216000 (Enclosure.Real.IsNear.const Bool.false 537603 1000) RS241to252.d44 rfl)) 

noncomputable abbrev qz833 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 537603 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz663 := qz833

noncomputable abbrev qz428 := qz663

noncomputable abbrev qz87 := qz428

noncomputable def Ns240p634 := @Enclosure.Real.IsNear.sqrt_image qz87 77594479 8388608 15 8388608 25512928 25512934 8388608 (@Enclosure.Real.IsNear.recentre' qz87 Bool.false 155188958 16777216 30 16777216 77594479 8388608 15 8388608 (Ns240p633 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns240p635 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz87) 25512931 8388608 3 8388608 2758159 2758161 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz87) Bool.false 51025862 16777216 6 16777216 25512931 8388608 3 8388608 (Ns240p634 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns240p636 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz87)) Bool.false 5516320 16777216 2 16777216 172385 524288 1 8388608 (Ns240p635 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz88 := (@HMul.hMul Real Real Real qz344 qz340 qz423)

noncomputable abbrev qz664 := (@HMul.hMul Real Real Real qz811 qz832 qz832)

noncomputable abbrev qz429 := (@HSub.hSub Real Real Real qz619 (@HSub.hSub Real Real Real qz619 qz664 qz656) qz626)

noncomputable abbrev qz89 := (Real.cos (@HMul.hMul Real Real Real qz344 qz340 qz429))

noncomputable def Ns240p637 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz83) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz88)) qz89) Bool.false 35549523850295 

noncomputable def Ns240p638 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz88)) qz89 78130821649 8388608 8326728127 

noncomputable def Ns240p639 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz88)) Bool.false 156261643298 16777216 16653456254 16777216 78130821649 8388608 8326728127 

noncomputable def Ns240p640 := @Enclosure.Real.IsNear.recentre' (Real.cos qz88) Bool.false 911 8388608 629137216 54358179840000 911 8388608 9830269 849346560000 

noncomputable def Ns240p641 := @Enclosure.Real.IsNear.cos_image qz88 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 26351767) qz363) Bool.false 26351767 16777216 189 16777216 Bool.false 911 8388608 1 

noncomputable def Ns240p642 := nat_lit 404791131153673834796500649 

noncomputable def Ns240p643 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz83 884279719003555 140737488355328 1 500000000000000 2097007 8388608 15 8388608 1854340760708487859885 1180591620717411303424 Ns240p642 

noncomputable def Ns240p644 := @Enclosure.Real.IsNear.subLit_ff_p qz87 qz1 77594479 8388608 15 8388608 9 1 0 1 2097007 2097007 8388608 15 

noncomputable def Ns240p645 := @Ns240p644 8388608 (@Enclosure.Real.IsNear.recentre' qz87 Bool.false 155188958 16777216 30 16777216 77594479 8388608 15 8388608 (Ns240p633 rfl rfl rfl rfl rfl rfl) rfl) qz373 

noncomputable def Ns240p646 := @Enclosure.Real.IsNear.recentre' qz88 Bool.false 1854340760708487859885 1180591620717411303424 Ns240p642 Ns240p165 26351767 16777216 189 16777216 (@Ns240p643 Ns240p165 RS241to252.d43 (Ns240p645 rfl rfl) rfl) 

noncomputable def Ns240p647 := nat_lit 60631065458127430492171796332785564709052578646820485105324025754035177157018682464998172403041 

noncomputable def Ns240p648 := nat_lit 112128729727602246357086841412467865930072131122107310845605040175529769751825809812497761 

noncomputable def Ns240p649 := nat_lit 366942713131826103151046290829499275185977750943898243311511533772561325907459485940815935317345 

noncomputable def Ns240p650 := BSN.cos_dyadic_bound_f 26351767 16777216 4 3 8388608 3240000 Ns240p647 Ns240p303 Ns240p648 Ns240p649 Ns240p306 Ns240p648 911 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 26351767) qz627 0 3 Ns240p647 Ns240p303 Ns240p648 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 26351767) (BSN.cosOddQ 16777216) 0 3 Ns240p649 Ns240p306 Ns240p648 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p651 := @Enclosure.Real.IsNear.inv_image (Real.cos qz88) 911 8388608 9830269 849346560000 69804093522 86457549776 8388608 (Ns240p640 (@Ns240p641 3240000 (Ns240p646 rfl) (Enclosure.sfrac_false_div 26351767 16777216) (Ns240p650 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns240p652 := @Enclosure.Real.IsNear.recentre' qz89 Bool.false 455 8388608 

noncomputable abbrev qz90 := (@HMul.hMul Real Real Real qz344 qz340 qz429)

noncomputable def Ns240p653 := @Enclosure.Real.IsNear.cos_image qz90 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 13176339)) qz406) Bool.true 13176339 8388608 

noncomputable def Ns240p654 := nat_lit 15555875517417893482863300605 

noncomputable def Ns240p655 := nat_lit 5093339864050526617704020803655797 

noncomputable def Ns240p656 := @Enclosure.Real.IsNear.recentre' qz90 Bool.true Ns240p654 Ns240p180 Ns240p655 

noncomputable abbrev qz91 := qz429

noncomputable def Ns240p657 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz91 884279719003555 140737488355328 1 500000000000000 17591577849311 

noncomputable abbrev qz430 := (@HSub.hSub Real Real Real qz619 qz664 qz656)

noncomputable abbrev qz92 := qz430

noncomputable def Ns240p658 := @Enclosure.Real.IsNear.subLit_tf qz92 qz27 13193531338207 70368744177664 188739555 70368744177664 1 16 

noncomputable abbrev qz431 := qz664

noncomputable abbrev qz93 := qz431

noncomputable def Ns240p659 := @Enclosure.Real.IsNear.subLit_ff_n qz93 qz83 4397438358049 70368744177664 62910435 70368744177664 2097007 8388608 15 8388608 

noncomputable def Ns240p660 := @Enclosure.Real.IsNear.mulLit_ff qz83 qz83 2097007 8388608 15 8388608 2097007 8388608 15 8388608 4397438358049 70368744177664 

noncomputable def Ns240p661 := nat_lit 14804560653620909829810548674360886026164165921312239839296380182651337050977817960614666801 

noncomputable def Ns240p662 := nat_lit 27386536876659538887567434854410575335096234613734111286542406500356593568159567913521 

noncomputable def Ns240p663 := nat_lit 89598027082130518814487421957695712026488842865112395061710477590286726116294139921537901105 

noncomputable def Ns240p664 := BSN.cos_dyadic_bound_f 13176339 8388608 4 3 8388608 3240000 Ns240p661 Ns240p426 Ns240p662 Ns240p663 Ns240p429 Ns240p662 455 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 13176339) (BSN.cosEvenQ 8388608) 0 3 Ns240p661 Ns240p426 Ns240p662 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 13176339) (BSN.cosOddQ 8388608) 0 3 Ns240p663 Ns240p429 Ns240p662 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p665 := @Ns240p652 933697216 54358179840000 455 8388608 14589019 849346560000 (@Ns240p653 283 16777216 Bool.false 455 8388608 1 3240000 (@Ns240p656 Ns240p183 13176339 8388608 283 16777216 (@Ns240p657 70368744177664 188739555 70368744177664 Ns240p654 Ns240p180 Ns240p655 Ns240p183 RS241to252.d43 (@Ns240p658 0 1 281465245588976 17591577849311 70368744177664 188739555 70368744177664 (@Ns240p659 110675362531933945856 13193531338207 70368744177664 188739555 70368744177664 (@Ns240p660 62910435 70368744177664 (Ns240p645 rfl rfl) (Ns240p645 rfl rfl) rfl) (Ns240p645 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 13176339 8388608) (BSN.cos_neg_of_bound 13176339 8388608 Bool.false 455 8388608 1 3240000 (Ns240p664 rfl rfl)) rfl rfl) 

noncomputable def Ns240p666 := @Ns240p631 94520689084287489137933 Ns240p561 (Ns240p632 qz29 (@Enclosure.Real.IsNear.of_eq qz427 (@Inv.inv Real Real.instInv (Real.sqrt qz87)) Bool.false 172385 524288 1 8388608 (BSN.rpow_neg_quarter_mk qz82 (BSN.t_div_two_pi_nonneg qz81 537603 1000 qz84)) Ns240p636) rfl) (@Ns240p637 70368744177664 822466396388120497 3562417673994240000 (BSN.correction_mk qz83 (BSN.cos_two_pi_p_ne_zero_mk qz81 537603 1000 9 qz84 rfl rfl (@BSN.floor_sqrt_eq_dec qz81 537603 1000 9 qz84 rfl rfl rfl))) (@Ns240p638 8388608 455 8388608 14589019 849346560000 35549523850295 70368744177664 822466396388120497 3562417673994240000 (@Ns240p639 8388608 (Ns240p651 rfl rfl rfl rfl rfl) rfl) (Ns240p665 rfl) rfl)) 

noncomputable def Ns240p667 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz81) (hardyZApproximantRS₀ qz81) Bool.true 64497434903002619945 36893488147419103232 96230798001874474097933 Ns240p561 (@Eq.refl Real (hardyZApproximantRS₀ qz81)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz81) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz81) qz81 9) (@HMul.hMul Real Real Real qz5 qz424 (Zeta.RiemannSiegel.correction qz83))) Bool.true 64497434903002619945 36893488147419103232 96230798001874474097933 Ns240p561 (BSN.hardyZApproximantRS₀_eq qz81 9 (@BSN.floor_sqrt_eq_dec qz81 537603 1000 9 qz84 rfl rfl rfl)) (@Ns240p563 64497434903002619945 36893488147419103232 96230798001874474097933 Ns240p561 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz81) qz81 9) (@HAdd.hAdd Real Real Real qz360 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz81) qz81 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz81) qz81 9)) Bool.true 64233645 33554432 11521 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz81) qz81 9) (Ns240p630 (Ns240p629 rfl) rfl rfl)) (Ns240p666 rfl) rfl rfl)) 

theorem RS241to252.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz81) Bool.true 64497434903002619945 36893488147419103232 96230798001874474097933 Ns240p561 := Ns240p667 

noncomputable def Ns240p668 := nat_lit 4980620899901578936320000 

noncomputable def Ns240p669 := nat_lit 8671209809763162214367232 

noncomputable abbrev qz834 := (Enclosure.sfrac Bool.false 539015 1000)

noncomputable abbrev qz665 := qz834

noncomputable abbrev qz432 := qz665

noncomputable abbrev qz94 := qz432

noncomputable abbrev qz835 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 539015 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz666 := qz835

noncomputable abbrev qz433 := qz666

noncomputable abbrev qz95 := qz433

noncomputable abbrev qz836 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 539015 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz667 := qz836

noncomputable abbrev qz434 := qz667

noncomputable abbrev qz96 := qz434

noncomputable abbrev qz435 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz618 qz95 qz8))

noncomputable def Ns240p670 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz94) qz94 9) (@HMul.hMul Real Real Real qz5 qz435 (Zeta.RiemannSiegel.correction qz96)) 54785577 33554432 92423 67108864 23119928734418109 144115188075855872 497724305109322726021 Ns240p668 Ns240p669 

noncomputable def Ns240p671 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz94) qz94 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 539015 1000 121 161 134217728 67108864 2251799813685248 Bool.false 124810569118 1787 

noncomputable def Ns240p672 := Ns240p671 279097919 42 47453128 8 294906479 42 44739240 8 Bool.false 190618446 75626 Bool.true 117121281 Bool.true 205023684 7074237752028440 1 Bool.false 102813027 Bool.true Bool.false 134092211 Bool.true Bool.false 109571154 

noncomputable def Ns240p673 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz94) qz94 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 539015 1000 22 75 134217728 67108864 2251799813685248 Bool.false 124810569118 1787 

noncomputable def Ns240p674 := Ns240p673 240485871 42 54794152 8 261175631 42 50729528 8 Bool.false 158022916 56402 Bool.true 176690928 Bool.true 154860065 7074237752028440 1 Bool.false 33770900 Bool.true Bool.false 122716415 Bool.false Bool.false 190618446 

noncomputable def Ns240p675 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz94) qz94 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 539015 1000 116 39 134217728 67108864 2251799813685248 Bool.false 124810569118 1787 

noncomputable def Ns240p676 := Ns240p675 186065264 42 67108856 8 216015088 42 60023992 8 Bool.false 43537548 33245 Bool.false 62470003 Bool.false 152876608 7074237752028440 1 Bool.false 119940339 Bool.false Bool.false 121899708 Bool.false Bool.false 158022916 

noncomputable def Ns240p677 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz94) qz94 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 539015 1000 354 215 134217728 67108864 2251799813685248 Bool.false 124810569118 1787 

noncomputable def Ns240p678 := Ns240p677 93032624 42 94906264 8 147453232 42 77490640 16 Bool.false 134217720 1842 Bool.false 31224489 Bool.false 2891732 7074237752028440 1 Bool.false 130602037 Bool.true Bool.false 2891508 Bool.false Bool.false 43537548 

noncomputable def Ns240p679 := nat_lit 2958012267578452992986599459804693498949096057332129 

noncomputable def Ns240p680 := nat_lit 3180962067197526302121832190345800833966066892800 

noncomputable def Ns240p681 := nat_lit 21839688501763898639514864500000000 

noncomputable def Ns240p682 := nat_lit 70631546549238561952184949140805000000 

noncomputable abbrev qz97 := (@Eq.refl Real qz432)

noncomputable def Ns240p683 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz94 539015 1000 1162149680900 16000000 1078030 4000 2000 Ns240p681 Ns240p682 qz97 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns240p684 := nat_lit 14790061337892264964932997299023467494745480286660645000000 

noncomputable abbrev qz668 := (Real.log (Enclosure.sfrac Bool.false 1162149680900 16000000))

noncomputable abbrev qz669 := (@Nat.cast Real Real.instNatCast 1078030)

noncomputable abbrev qz670 := (Enclosure.sfrac Bool.false 539015 2000)

noncomputable abbrev qz98 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 539015 4000) qz668) (@HMul.hMul Real Real Real qz344 qz358 (@HSub.hSub Real Real Real qz350 qz355 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz356 qz669))))) qz670)

noncomputable abbrev qz436 := (@HSub.hSub Real Real Real qz11 qz98 (@HMul.hMul Real Real Real qz5 qz670 (Real.log Real.pi)))

noncomputable def Ns240p685 := @Enclosure.Real.IsNear.addLit_ft_p qz436 (Enclosure.sfrac Bool.true Ns240p681 Ns240p682) 209397457344962497889 225179981368524800 441525675980402831 33177600000000000000000 Ns240p681 Ns240p682 0 1 Ns240p684 

noncomputable def Ns240p686 := nat_lit 2810485097381777871186637619200 

noncomputable abbrev qz437 := (@HMul.hMul Real Real Real qz5 qz670 (Real.log Real.pi))

noncomputable def Ns240p687 := @Enclosure.Real.IsNear.subLit_ff_p qz98 qz437 278868473969368894817 225179981368524800 85471128680197 16200000000000000000 4140795268083 13421772800 107803 13421772800 Ns240p686 209397457344962497889 225179981368524800 

noncomputable abbrev qz99 := (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 539015 4000) qz668) (@HMul.hMul Real Real Real qz344 qz358 (@HSub.hSub Real Real Real qz350 qz355 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz356 qz669)))))

noncomputable def Ns240p688 := @Enclosure.Real.IsNear.subLit_ff_p qz99 qz670 339556167798046592353 225179981368524800 85471128680197 16200000000000000000 539015 2000 0 1 557736947938737789634000 278868473969368894817 225179981368524800 85471128680197 16200000000000000000 

noncomputable def Ns240p689 := nat_lit 764612515383318123297048461305708544 

noncomputable def Ns240p690 := nat_lit 27063480734729207852040192 

noncomputable def Ns240p691 := nat_lit 358286697609223010432063349217978478213041500000000 

noncomputable def Ns240p692 := nat_lit 315705618465068275517985555712239004288800000000 

noncomputable def Ns240p693 := nat_lit 499151131986871648332052519032346608300000000 

noncomputable def Ns240p694 := BSN.log_dyadic_bound 113573680900 2210725680900 3 2 Ns240p691 67108864 25920000 Ns240p692 Ns240p693 6901368 2324299361800 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 113573680900) (BSN.artanhQ 2210725680900) 0 2 Ns240p692 Ns240p691 Ns240p693 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns240p695 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 539015 4000) qz668 539015 4000 0 1 3150603819490551 281474976710656 195312581 5062500000000000 339644543552539869453 225179981368524800 21055282169543 4050000000000000000 (Enclosure.Real.IsNear.const Bool.false 539015 4000) (BSN.isNear_log_sfrac 1162149680900 16000000 3150603819490551 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1162149680900) qz354)) Bool.false Ns240p690 Ns240p92 1000000414720000 25920000000000000000000 3150603819490551 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1162149680900 16000000 16 2324299361800 2097152000000 6901368 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns240p694 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p696 := BSN.arctan_dyadic_bound_f 1000 1078030 1 0 8388608 3240000 0 1 1 0 1 1 7781 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1078030) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1078030) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz671 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1078030)))

noncomputable def Ns240p697 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz671 884279719003555 562949953421312 1 2000000000000000 7781 8388608 1 3240000 7413495611483402272768 883757544932771 562949953421312 50000000081 162000000000000000 qz16 (Ns240p696 rfl) rfl rfl 

noncomputable def Ns240p698 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 539015 4000) qz668) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz11 qz14 qz671)) 339644543552539869453 225179981368524800 21055282169543 4050000000000000000 883757544932771 2251799813685248 50000000081 648000000000000000 Ns240p689 339556167798046592353 225179981368524800 85471128680197 16200000000000000000 (Ns240p695 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 qz671) 1 4 0 1 883757544932771 562949953421312 50000000081 162000000000000000 883757544932771 2251799813685248 50000000081 648000000000000000 qz359 Ns240p697 rfl) 

noncomputable def Ns240p699 := @Ns240p685 Ns240p679 Ns240p680 441525675980402831 33177600000000000000000 (@Ns240p687 441525675980402831 33177600000000000000000 (Ns240p688 (Ns240p698 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 539015 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz670 (Real.log Real.pi) 539015 2000 0 1 38410761 33554432 1 33554432 4140795268083 13421772800 107803 13421772800 (Enclosure.Real.IsNear.const Bool.false 539015 2000) RS241to252.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns240p681 Ns240p682) 

noncomputable def Ns240p700 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz94) Bool.false Ns240p679 Ns240p680 441525675980402831 33177600000000000000000 15601321139 16777216 225 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz94) (@HAdd.hAdd Real Real Real qz360 qz436 (Enclosure.sfrac Bool.true Ns240p681 Ns240p682)) Bool.false Ns240p679 Ns240p680 441525675980402831 33177600000000000000000 Ns240p683 (Ns240p699 rfl rfl)) 

noncomputable def Ns240p701 := nat_lit 3797418259734937603145728 

noncomputable def Ns240p702 := nat_lit 856654448140297154807497784036953231413844947148432813655699796997012755791635649290507298308843578094611368159582113676621997322691761 

noncomputable def Ns240p703 := nat_lit 609963159891519205363908145814569570702274459286749451744011801892009959679370951318279305937136448946100435736802288194256528561 

noncomputable def Ns240p704 := nat_lit 4277952735735591158230884111069950593504810585314810754875641247607451348266961830789689126443896330960678734276358906175686493683999921 

noncomputable def Ns240p705 := BSN.sin_dyadic_bound_f 53964559181 34359738368 4 3 16777216 6486329 Ns240p702 Ns240p105 Ns240p703 Ns240p704 Ns240p108 Ns240p703 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53964559181) qz361 0 3 Ns240p702 Ns240p105 Ns240p703 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53964559181) qz362 0 3 Ns240p704 Ns240p108 Ns240p703 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p706 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz94) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15601321139) qz363) Bool.false 15601321139 16777216 225 16777216 Bool.false 16777215 16777216 1 3240000 (Ns240p700 rfl) (Enclosure.sfrac_false_div 15601321139 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15601321139) qz363) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns240p701) qz364) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 147 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q3 15601321139 16777216 226375608064910080 72057594037927936 147 Ns240p701 Ns240p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns240p701 Ns240p92 53964559181 34359738368 6486329 6480000 (Ns240p705 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns240p707 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz94) Bool.false Ns240p679 Ns240p680 441525675980402831 33177600000000000000000 124810569118 134217728 1787 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz94) (@HAdd.hAdd Real Real Real qz360 qz436 (Enclosure.sfrac Bool.true Ns240p681 Ns240p682)) Bool.false Ns240p679 Ns240p680 441525675980402831 33177600000000000000000 Ns240p683 (Ns240p699 rfl rfl)) 

noncomputable def Ns240p708 := Ns240p678 33245 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 354 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 130602037 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 215 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 2891508 134217728) qz97 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz94) qz94 1) Bool.false 16777215 16777216 11652769 849346560000 134217720 134217728 1842 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz94) qz94 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz94)) Bool.false 16777215 16777216 11652769 849346560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz94) qz94) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz94)) Bool.false 16777215 16777216 745777216 54358179840000 16777215 16777216 11652769 849346560000 (Ns240p706 rfl rfl) rfl)) rfl) (Ns240p707 rfl) RS241to252.d7 

noncomputable def Ns240p709 := nat_lit 950563991935542851011342276641 

noncomputable def Ns240p710 := BSN.cos_dyadic_bound_f 31224489 134217728 2 1 134217728 67108864 Ns240p709 Ns240p146 Ns240p709 Ns240p709 Ns240p147 Ns240p709 130602037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 31224489) qz367 0 1 Ns240p709 Ns240p146 Ns240p709 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 31224489) qz368 0 1 Ns240p709 Ns240p147 Ns240p709 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p711 := BSN.sin_dyadic_bound_f 2891732 134217728 1 0 134217728 67108864 0 1 1 0 1 1 2891508 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 2891732) qz365 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 2891732) qz366 0 0 rfl) rfl rfl 

noncomputable def Ns240p712 := nat_lit 8303229695986161201961126130680207373281543299564828876995132843041 

noncomputable def Ns240p713 := nat_lit 231938163685203355511506920657379742480161930840433463775126561 

noncomputable def Ns240p714 := nat_lit 24909225211631113199172355378199307360359669574832805764057848276001 

noncomputable def Ns240p715 := BSN.cos_dyadic_bound_f 62470003 134217728 3 2 134217728 67108864 Ns240p712 Ns240p124 Ns240p713 Ns240p714 Ns240p127 Ns240p713 119940339 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 62470003) qz367 0 2 Ns240p712 Ns240p124 Ns240p713 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 62470003) qz368 0 2 Ns240p714 Ns240p127 Ns240p713 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p716 := nat_lit 536323876669951889577851761742316761268791761016861173628410884259840 

noncomputable def Ns240p717 := nat_lit 298351554382618821245348889588330288812075618951680099033406242816 

noncomputable def Ns240p718 := nat_lit 1404174726857064042231405001599115173331616013565857496485498229620736 

noncomputable def Ns240p719 := BSN.sin_dyadic_bound_f 152876608 134217728 3 2 134217728 67108864 Ns240p716 Ns240p248 Ns240p717 Ns240p718 Ns240p251 Ns240p717 121899708 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 152876608) qz365 0 2 Ns240p716 Ns240p248 Ns240p717 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 152876608) qz366 0 2 Ns240p718 Ns240p251 Ns240p717 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p720 := Ns240p676 56402 BSN.abs_quadSignPos (BSN.cos_quad_nat0 116 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 119940339 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 39 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 121899708 134217728) qz97 rfl rfl (Ns240p708 RS241to252.d9 RS241to252.d11 RS241to252.d13 RS241to252.d17 (Ns240p710 rfl rfl) (Ns240p711 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns240p707 rfl) RS241to252.d19 RS241to252.d21 RS241to252.d23 RS241to252.d25 RS241to252.d17 (Ns240p715 rfl rfl) (Ns240p719 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns240p721 := nat_lit 2052285174478025349522832444934251725116581428637533084524456541700449504419504559885714894184370191466496 

noncomputable def Ns240p722 := nat_lit 925914788319035307940780333977340445818451753061436863021067916077695534500140738164769520684630016 

noncomputable def Ns240p723 := nat_lit 12435712850250937649311257697116178060696455459215131050213445893104695949214183470766844384494273020559360 

noncomputable def Ns240p724 := BSN.cos_dyadic_bound_f 176690928 134217728 4 3 134217728 67108864 Ns240p721 Ns240p130 Ns240p722 Ns240p723 Ns240p133 Ns240p722 33770900 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 176690928) qz367 0 3 Ns240p721 Ns240p130 Ns240p722 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 176690928) qz368 0 3 Ns240p723 Ns240p133 Ns240p722 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p725 := nat_lit 564720446365923698308413282210879171733245345914657242757842547130625 

noncomputable def Ns240p726 := nat_lit 330761915031486429991555980027968078012000026102109582782312890625 

noncomputable def Ns240p727 := nat_lit 1478494221191177755635381791346543025270289810686603648850797212090625 

noncomputable def Ns240p728 := BSN.sin_dyadic_bound_f 154860065 134217728 3 2 134217728 67108864 Ns240p725 Ns240p248 Ns240p726 Ns240p727 Ns240p251 Ns240p726 122716415 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 154860065) qz365 0 2 Ns240p725 Ns240p248 Ns240p726 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 154860065) qz366 0 2 Ns240p727 Ns240p251 Ns240p726 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p729 := Ns240p674 75626 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 22 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 33770900 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 75 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 122716415 134217728) qz97 rfl rfl (Ns240p720 rfl rfl) (Ns240p707 rfl) RS241to252.d27 RS241to252.d29 RS241to252.d31 RS241to252.d33 RS241to252.d17 (Ns240p724 rfl rfl) (Ns240p728 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p730 := nat_lit 184691895748376027715850788457740566713663453857095598333609546942465 

noncomputable def Ns240p731 := nat_lit 35406786341001113514216441406553122034493949080517990213680957441 

noncomputable def Ns240p732 := nat_lit 483659544544051785072014762198471826814396055612929537937202853775361 

noncomputable def Ns240p733 := BSN.sin_dyadic_bound_f 117121281 134217728 3 2 134217728 67108864 Ns240p730 Ns240p248 Ns240p731 Ns240p732 Ns240p251 Ns240p731 102813027 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 117121281) qz365 0 2 Ns240p730 Ns240p248 Ns240p731 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 117121281) qz366 0 2 Ns240p732 Ns240p251 Ns240p731 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p734 := nat_lit 9673324578583320413261463216494682290989851422622717626759597573937661549890368096618844491374330229293056 

noncomputable def Ns240p735 := nat_lit 5516306583933779687771279150830206935841778281528416444291147471882795230697765597148863785919840256 

noncomputable def Ns240p736 := nat_lit 48312863593410123191500596712735273418849765360899954857138240717763079043004789208629012185806979219849216 

noncomputable def Ns240p737 := BSN.sin_dyadic_bound_f 205023684 134217728 4 3 134217728 67108864 Ns240p734 Ns240p118 Ns240p735 Ns240p736 Ns240p121 Ns240p735 134092211 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 205023684) qz365 0 3 Ns240p734 Ns240p118 Ns240p735 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 205023684) qz366 0 3 Ns240p736 Ns240p121 Ns240p735 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p738 := Ns240p672 92423 BSN.abs_quadSignNeg qz642 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 102813027 134217728) BSN.abs_quadSignNeg qz662 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 134092211 134217728) qz97 rfl rfl (Ns240p729 rfl) (Ns240p707 rfl) RS241to252.d35 RS241to252.d37 RS241to252.d39 RS241to252.d41 RS241to252.d17 (Ns240p733 rfl rfl) (Ns240p737 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p739 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz94) qz94 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz94) qz94 9) 109571154 134217728 92423 134217728 109571154 134217728 92423 134217728 29412782688436224 54785577 33554432 92423 67108864 (Ns240p738 rfl) 

noncomputable def Ns240p740 := @Enclosure.Real.IsNear.mulLit_tf qz435 (Zeta.RiemannSiegel.correction qz96) 10767 32768 1 8388608 2147295322227 4398046511104 180468329071357 593736278999040000 23119928734418109 144115188075855872 

noncomputable abbrev qz438 := (@HPow.hPow Real Real Real qz618 qz95 qz8)

noncomputable def Ns240p741 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz438 1 1 0 1 10767 32768 1 8388608 10767 32768 1 8388608 

noncomputable def Ns240p742 := @Enclosure.Real.IsNear.sqrt_image qz95 287853091131 3355443200 107803 3355443200 77696297 77696327 8388608 (@Enclosure.Real.IsNear.of_eq qz95 (@HMul.hMul Real Real Real qz5 qz94 qz3) Bool.false 287853091131 3355443200 107803 3355443200 (BSN.t_div_two_pi_mk qz94 539015 1000 qz97) (@Enclosure.Real.IsNear.mulLit_ff qz94 qz3 539015 1000 0 1 2670177 16777216 1 16777216 287853091131 3355443200 107803 3355443200 (Enclosure.Real.IsNear.const Bool.false 539015 1000) RS241to252.d44 rfl)) 

noncomputable abbrev qz837 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 539015 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz672 := qz837

noncomputable abbrev qz439 := qz672

noncomputable abbrev qz100 := qz439

noncomputable def Ns240p743 := @Enclosure.Real.IsNear.sqrt_image qz100 9712039 1048576 15 8388608 25529664 25529670 8388608 (@Enclosure.Real.IsNear.recentre' qz100 Bool.false 155392624 16777216 30 16777216 9712039 1048576 15 8388608 (Ns240p742 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns240p744 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz100) 25529667 8388608 3 8388608 2756351 2756353 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz100) Bool.false 51059334 16777216 6 16777216 25529667 8388608 3 8388608 (Ns240p743 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns240p745 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz100)) Bool.false 5512704 16777216 2 16777216 10767 32768 1 8388608 (Ns240p744 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz101 := (Real.cos (@HMul.hMul Real Real Real qz344 qz340 qz434))

noncomputable abbrev qz673 := (@HMul.hMul Real Real Real qz811 qz836 qz836)

noncomputable abbrev qz440 := (@HSub.hSub Real Real Real qz619 (@HSub.hSub Real Real Real qz619 qz673 qz667) qz626)

noncomputable abbrev qz102 := (Real.cos (@HMul.hMul Real Real Real qz344 qz340 qz440))

noncomputable def Ns240p746 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz96) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz101) qz102) Bool.false 2147295322227 

noncomputable def Ns240p747 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz101) qz102 13780349 1048576 16769 

noncomputable abbrev qz674 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz101))

noncomputable def Ns240p748 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz101) (@Neg.neg Real Real.instNeg qz674) Bool.true 13780349 1048576 16769 8388608 (BSN.inv_eq_neg_inv_neg qz101) 

noncomputable def Ns240p749 := @Enclosure.Real.IsNear.recentre' qz674 Bool.false 220485584 16777216 33538 16777216 13780349 1048576 

noncomputable def Ns240p750 := @Enclosure.Real.IsNear.recentre' qz101 Bool.true 638307 8388608 629137216 54358179840000 638307 8388608 9830269 849346560000 

noncomputable abbrev qz103 := (@HMul.hMul Real Real Real qz344 qz340 qz434)

noncomputable def Ns240p751 := @Enclosure.Real.IsNear.cos_image qz103 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13815719) qz406) Bool.false 13815719 8388608 189 16777216 Bool.true 638307 8388608 1 

noncomputable def Ns240p752 := nat_lit 80958226230909714721161557 

noncomputable def Ns240p753 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz96 884279719003555 140737488355328 1 500000000000000 274855 1048576 15 8388608 243048702166722109525 147573952589676412928 Ns240p752 

noncomputable def Ns240p754 := @Enclosure.Real.IsNear.subLit_ff_p qz100 qz1 9712039 1048576 15 8388608 9 1 0 1 274855 274855 1048576 15 

noncomputable def Ns240p755 := @Ns240p754 8388608 (@Enclosure.Real.IsNear.recentre' qz100 Bool.false 155392624 16777216 30 16777216 9712039 1048576 15 8388608 (Ns240p742 rfl rfl rfl rfl rfl rfl) rfl) qz373 

noncomputable def Ns240p756 := @Enclosure.Real.IsNear.recentre' qz103 Bool.false 243048702166722109525 147573952589676412928 Ns240p752 Ns240p532 13815719 8388608 189 16777216 (@Ns240p753 Ns240p532 RS241to252.d43 (Ns240p755 rfl rfl) rfl) 

noncomputable def Ns240p757 := nat_lit 17907621462975548345126542974260186126761765453530837486584681715338460774005986403072583841 

noncomputable def Ns240p758 := nat_lit 48359510653585327328838590986559018519554795372753475227256729560240306862497690265761 

noncomputable def Ns240p759 := nat_lit 108323517390521287562935241158774463373071752051985744362243696136253484535815556453094631585 

noncomputable def Ns240p760 := BSN.cos_dyadic_bound_t 13815719 8388608 4 3 8388608 3240000 Ns240p757 Ns240p426 Ns240p758 Ns240p759 Ns240p429 Ns240p758 638307 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 13815719) (BSN.cosEvenQ 8388608) 0 3 Ns240p757 Ns240p426 Ns240p758 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 13815719) (BSN.cosOddQ 8388608) 0 3 Ns240p759 Ns240p429 Ns240p758 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p761 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz101) 638307 8388608 9830269 849346560000 110226023 110259561 8388608 (@Enclosure.Real.IsNear.neg qz101 Bool.true 638307 8388608 9830269 849346560000 (Ns240p750 (@Ns240p751 3240000 (Ns240p756 rfl) (Enclosure.sfrac_false_div 13815719 8388608) (Ns240p760 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns240p762 := Ns240p748 (@Enclosure.Real.IsNear.neg qz674 Bool.false 13780349 1048576 16769 8388608 (@Ns240p749 16769 8388608 (Ns240p761 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p763 := @Enclosure.Real.IsNear.recentre' qz102 Bool.true 311646 8388608 

noncomputable abbrev qz104 := (@HMul.hMul Real Real Real qz344 qz340 qz440)

noncomputable def Ns240p764 := @Enclosure.Real.IsNear.cos_image qz104 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 26977023)) qz363) Bool.true 26977023 16777216 

noncomputable def Ns240p765 := nat_lit 248819124467319812227589005 

noncomputable def Ns240p766 := nat_lit 154742504910672534362390528 

noncomputable def Ns240p767 := nat_lit 5175782054567982183013026129393623 

noncomputable def Ns240p768 := @Enclosure.Real.IsNear.recentre' qz104 Bool.true Ns240p765 Ns240p766 Ns240p767 

noncomputable abbrev qz105 := qz440

noncomputable def Ns240p769 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz105 884279719003555 140737488355328 1 500000000000000 281380562191 

noncomputable abbrev qz441 := (@HSub.hSub Real Real Real qz619 qz673 qz667)

noncomputable abbrev qz106 := qz441

noncomputable def Ns240p770 := @Enclosure.Real.IsNear.subLit_tf qz106 qz27 212661085455 1099511627776 191794545 70368744177664 1 16 

noncomputable abbrev qz442 := qz673

noncomputable abbrev qz107 := qz442

noncomputable def Ns240p771 := @Enclosure.Real.IsNear.subLit_ff_n qz107 qz96 75545271025 1099511627776 65965425 70368744177664 274855 1048576 15 8388608 

noncomputable def Ns240p772 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz96 274855 1048576 15 8388608 274855 1048576 15 8388608 75545271025 1099511627776 

noncomputable def Ns240p773 := nat_lit 66617238951248156856611972931276117178534626146248147537563937853634037819069807933392559692801 

noncomputable def Ns240p774 := nat_lit 148569022682900074180267808436057839207619154949907649202010588569023352604813445722168321 

noncomputable def Ns240p775 := nat_lit 403075988029712534629041813067793869487364076931488749911010383384165599533698368900500969380865 

noncomputable def Ns240p776 := BSN.cos_dyadic_bound_t 26977023 16777216 4 3 8388608 3240000 Ns240p773 Ns240p303 Ns240p774 Ns240p775 Ns240p306 Ns240p774 311646 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 26977023) qz627 0 3 Ns240p773 Ns240p303 Ns240p774 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 26977023) (BSN.cosOddQ 16777216) 0 3 Ns240p775 Ns240p306 Ns240p774 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p777 := @Ns240p763 29684288 1698693120000 155823 4194304 463817 26542080000 (@Ns240p764 9 524288 Bool.true 311646 8388608 1 3240000 (@Ns240p768 Ns240p183 26977023 16777216 9 524288 (@Ns240p769 1099511627776 191794545 70368744177664 Ns240p765 Ns240p766 Ns240p767 Ns240p183 RS241to252.d43 (@Ns240p770 0 1 4502088995056 281380562191 1099511627776 191794545 70368744177664 (@Ns240p771 222991310342062080 212661085455 1099511627776 191794545 70368744177664 (@Ns240p772 65965425 70368744177664 (Ns240p755 rfl rfl) (Ns240p755 rfl rfl) rfl) (Ns240p755 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 26977023 16777216) (BSN.cos_neg_of_bound 26977023 16777216 Bool.true 311646 8388608 1 3240000 (Ns240p776 rfl rfl)) rfl rfl) 

noncomputable def Ns240p778 := @Ns240p740 497724305109322726021 Ns240p668 (Ns240p741 qz29 (@Enclosure.Real.IsNear.of_eq qz438 (@Inv.inv Real Real.instInv (Real.sqrt qz100)) Bool.false 10767 32768 1 8388608 (BSN.rpow_neg_quarter_mk qz95 (BSN.t_div_two_pi_nonneg qz94 539015 1000 qz97)) Ns240p745) rfl) (@Ns240p746 4398046511104 180468329071357 593736278999040000 (BSN.correction_mk qz96 (BSN.cos_two_pi_p_ne_zero_mk qz94 539015 1000 9 qz97 rfl rfl (@BSN.floor_sqrt_eq_dec qz94 539015 1000 9 qz97 rfl rfl rfl))) (@Ns240p747 8388608 155823 4194304 463817 26542080000 2147295322227 4398046511104 180468329071357 593736278999040000 Ns240p762 (Ns240p777 rfl) rfl)) 

noncomputable def Ns240p779 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz94) (hardyZApproximantRS₀ qz94) Bool.false 258422190241907901 144115188075855872 7357085319350356966021 Ns240p668 (@Eq.refl Real (hardyZApproximantRS₀ qz94)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz94) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz94) qz94 9) (@HMul.hMul Real Real Real qz5 qz435 (Zeta.RiemannSiegel.correction qz96))) Bool.false 258422190241907901 144115188075855872 7357085319350356966021 Ns240p668 (BSN.hardyZApproximantRS₀_eq qz94 9 (@BSN.floor_sqrt_eq_dec qz94 539015 1000 9 qz97 rfl rfl rfl)) (@Ns240p670 258422190241907901 144115188075855872 7357085319350356966021 Ns240p668 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz94) qz94 9) (@HAdd.hAdd Real Real Real qz360 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz94) qz94 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz94) qz94 9)) Bool.false 54785577 33554432 92423 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz94) qz94 9) (Ns240p739 (Ns240p738 rfl) rfl rfl)) (Ns240p778 rfl) rfl rfl)) 

theorem RS241to252.d52 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz94) Bool.false 258422190241907901 144115188075855872 7357085319350356966021 Ns240p668 := Ns240p779 

noncomputable def Ns240p780 := nat_lit 1237366643122996930737602560 

noncomputable abbrev qz838 := (Enclosure.sfrac Bool.false 540426 1000)

noncomputable abbrev qz675 := qz838

noncomputable abbrev qz443 := qz675

noncomputable abbrev qz108 := qz443

noncomputable abbrev qz444 := qz618

noncomputable abbrev qz839 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 540426 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz676 := qz839

noncomputable abbrev qz445 := qz676

noncomputable abbrev qz109 := (@HMul.hMul Real Real Real qz344 qz345 (@HPow.hPow Real Real Real qz444 qz445 qz347))

noncomputable abbrev qz840 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 540426 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz677 := qz840

noncomputable abbrev qz446 := qz677

noncomputable abbrev qz110 := (Zeta.RiemannSiegel.correction qz446)

noncomputable def Ns240p781 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz108) qz108 9) (@HMul.hMul Real Real Real qz5 qz109 qz110) 4725065 16777216 23165 16777216 92495645883653199045 590295810358705651712 3847825447509110331 73786976294838206464000 Ns240p780 

noncomputable def Ns240p782 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz108) qz108 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 540426 1000 121 161 134217728 67108864 2251799813685248 Bool.false 125232243004 1792 

noncomputable def Ns240p783 := Ns240p782 279097919 42 47453128 8 294906479 42 44739240 8 Bool.false 54959983 75819 Bool.true 89254559 Bool.true 199462840 7074237752028440 1 Bool.false 82820093 Bool.true Bool.false 133736770 Bool.true Bool.true 18900260 

noncomputable def Ns240p784 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz108) qz108 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 540426 1000 22 75 134217728 67108864 2251799813685248 Bool.false 125232243004 1792 

noncomputable def Ns240p785 := Ns240p784 240485871 42 54794152 8 261175631 42 50729528 8 Bool.false 61899811 56545 Bool.true 94342606 Bool.true 101704994 7074237752028440 1 Bool.false 102403575 Bool.true Bool.false 92247441 Bool.false Bool.false 54959983 

noncomputable def Ns240p786 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz108) qz108 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 540426 1000 117 40 134217728 67108864 2251799813685248 Bool.false 125232243004 1792 

noncomputable def Ns240p787 := Ns240p786 186065264 42 67108856 8 216015088 42 60023992 8 Bool.false 12950773 33328 Bool.false 10777087 Bool.false 58924491 7074237752028440 1 Bool.false 10765510 Bool.true Bool.false 121489584 Bool.false Bool.false 61899811 

noncomputable def Ns240p788 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz108) qz108 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 540426 1000 355 216 134217728 67108864 2251799813685248 Bool.false 125232243004 1792 

noncomputable def Ns240p789 := Ns240p788 93032624 42 94906264 8 147453232 42 77490640 16 Bool.true 134217720 1842 Bool.false 110800628 Bool.false 5680394 7074237752028440 1 Bool.false 98637499 Bool.false Bool.false 134097542 Bool.false Bool.false 12950773 

noncomputable def Ns240p790 := nat_lit 40892589210681207649204602238980274043226096055649221 

noncomputable def Ns240p791 := nat_lit 43826655853141558790053322405862510178390874521600 

noncomputable def Ns240p792 := nat_lit 22127041651716951726272368020480000 

noncomputable def Ns240p793 := nat_lit 71748200330743935248479811280551546880 

noncomputable abbrev qz447 := (@Eq.refl Real qz675)

noncomputable abbrev qz111 := qz447

noncomputable def Ns240p794 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz108 540426 1000 1168242045904 16000000 1080852 4000 2000 Ns240p792 Ns240p793 qz111 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns240p795 := nat_lit 7537322043312760193901392284688844111647434024977264414720 

noncomputable abbrev qz678 := (Real.log (Enclosure.sfrac Bool.false 1168242045904 16000000))

noncomputable abbrev qz679 := (@Nat.cast Real Real.instNatCast 1080852)

noncomputable abbrev qz680 := (Enclosure.sfrac Bool.false 540426 2000)

noncomputable abbrev qz112 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 540426 4000) qz678) (@HMul.hMul Real Real Real qz344 qz358 (@HSub.hSub Real Real Real qz350 qz355 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz356 qz679))))) qz680)

noncomputable abbrev qz448 := (@HSub.hSub Real Real Real qz11 qz112 (@HMul.hMul Real Real Real qz5 qz680 (Real.log Real.pi)))

noncomputable def Ns240p796 := @Enclosure.Real.IsNear.addLit_ft_p qz448 (Enclosure.sfrac Bool.true Ns240p792 Ns240p793) 105052454275517873569 112589990684262400 1106686932679885201 82944000000000000000000 Ns240p792 Ns240p793 0 1 Ns240p795 

noncomputable def Ns240p797 := nat_lit 17624877167104868767278039040000 

noncomputable abbrev qz449 := (@HMul.hMul Real Real Real qz5 qz680 (Real.log Real.pi))

noncomputable def Ns240p798 := @Enclosure.Real.IsNear.subLit_ff_p qz112 qz449 699394455223407440933 562949953421312000 428457987608149 81000000000000000000 10379086962093 33554432000 270213 33554432000 Ns240p797 105052454275517873569 112589990684262400 

noncomputable def Ns240p799 := nat_lit 1398788910446814881866000 

noncomputable abbrev qz113 := (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 540426 4000) qz678) (@HMul.hMul Real Real Real qz344 qz358 (@HSub.hSub Real Real Real qz350 qz355 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz356 qz679)))))

noncomputable def Ns240p800 := @Enclosure.Real.IsNear.subLit_ff_p qz113 qz680 851510850987240420389 562949953421312000 428457987608149 81000000000000000000 540426 2000 0 1 Ns240p799 699394455223407440933 562949953421312000 428457987608149 81000000000000000000 

noncomputable def Ns240p801 := nat_lit 1917431975604034951635296110847721472 

noncomputable def Ns240p802 := nat_lit 27076122807257598080843776 

noncomputable def Ns240p803 := nat_lit 362252550290303104116050835801706922952531562659840 

noncomputable def Ns240p804 := nat_lit 352476872596071224015685937343244753912684085248 

noncomputable def Ns240p805 := nat_lit 615183981638473604690905943721219176776531968 

noncomputable def Ns240p806 := BSN.log_dyadic_bound 119666045904 2216818045904 3 2 Ns240p803 67108864 25920000 Ns240p804 Ns240p805 7252256 2336484091808 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 119666045904) (BSN.artanhQ 2216818045904) 0 2 Ns240p804 Ns240p803 Ns240p805 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns240p807 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 540426 4000) qz678 540426 4000 0 1 3152075550432503 281474976710656 195312581 5062500000000000 851731790709017933139 562949953421312000 17591999483251 3375000000000000000 (Enclosure.Real.IsNear.const Bool.false 540426 4000) (BSN.isNear_log_sfrac 1168242045904 16000000 3152075550432503 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1168242045904) qz354)) Bool.false Ns240p802 Ns240p92 1000000414720000 25920000000000000000000 3152075550432503 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1168242045904 16000000 16 2336484091808 2097152000000 7252256 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns240p806 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p808 := BSN.arctan_dyadic_bound_f 1000 1080852 1 0 8388608 3240000 0 1 1 0 1 1 7761 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1080852) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1080852) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz681 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1080852)))

noncomputable def Ns240p809 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz681 884279719003555 562949953421312 1 2000000000000000 7761 8388608 1 3240000 7413506870482470699008 883758887110051 562949953421312 50000000081 162000000000000000 qz16 (Ns240p808 rfl) rfl rfl 

noncomputable def Ns240p810 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 540426 4000) qz678) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz11 qz14 qz681)) 851731790709017933139 562949953421312000 17591999483251 3375000000000000000 883758887110051 2251799813685248 50000000081 648000000000000000 Ns240p801 851510850987240420389 562949953421312000 428457987608149 81000000000000000000 (Ns240p807 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 qz681) 1 4 0 1 883758887110051 562949953421312 50000000081 162000000000000000 883758887110051 2251799813685248 50000000081 648000000000000000 qz359 Ns240p809 rfl) 

noncomputable def Ns240p811 := @Ns240p796 Ns240p790 Ns240p791 1106686932679885201 82944000000000000000000 (@Ns240p798 1106686932679885201 82944000000000000000000 (Ns240p800 (Ns240p810 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 540426 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz680 (Real.log Real.pi) 540426 2000 0 1 38410761 33554432 1 33554432 10379086962093 33554432000 270213 33554432000 (Enclosure.Real.IsNear.const Bool.false 540426 2000) RS241to252.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns240p792 Ns240p793) 

noncomputable def Ns240p812 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz108) Bool.false Ns240p790 Ns240p791 1106686932679885201 82944000000000000000000 15654030375 16777216 225 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz108) (@HAdd.hAdd Real Real Real qz360 qz448 (Enclosure.sfrac Bool.true Ns240p792 Ns240p793)) Bool.false Ns240p790 Ns240p791 1106686932679885201 82944000000000000000000 Ns240p794 (Ns240p811 rfl rfl)) 

noncomputable def Ns240p813 := nat_lit 3797714771936933796904960 

noncomputable def Ns240p814 := nat_lit 856922576527866156726354566031965569432870466150331541202852198314988557123979189591026147770794547912293298906452522186953926591057121 

noncomputable def Ns240p815 := nat_lit 610534935366826120884648224013204323599669203727070722671781836952570526906465577915494882138418959225871759112312135235722218721 

noncomputable def Ns240p816 := nat_lit 4279290053117211753746727554839698934051866034623461284632469801901258525613805812695949874772846651378883759978885602415977970599136481 

noncomputable def Ns240p817 := BSN.sin_dyadic_bound_f 53968772873 34359738368 4 3 16777216 6486329 Ns240p814 Ns240p105 Ns240p815 Ns240p816 Ns240p108 Ns240p815 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53968772873) qz361 0 3 Ns240p814 Ns240p105 Ns240p815 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53968772873) qz362 0 3 Ns240p816 Ns240p108 Ns240p815 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p818 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz108) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15654030375) qz363) Bool.false 15654030375 16777216 225 16777216 Bool.true 16777215 16777216 1 3240000 (Ns240p812 rfl) (Enclosure.sfrac_false_div 15654030375 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15654030375) qz363) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns240p813) qz364) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 148 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 15654030375 16777216 226375608064910080 72057594037927936 148 Ns240p813 Ns240p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns240p813 Ns240p92 53968772873 34359738368 6486329 6480000 (Ns240p817 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns240p819 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz108) Bool.false Ns240p790 Ns240p791 1106686932679885201 82944000000000000000000 125232243004 134217728 1792 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz108) (@HAdd.hAdd Real Real Real qz360 qz448 (Enclosure.sfrac Bool.true Ns240p792 Ns240p793)) Bool.false Ns240p790 Ns240p791 1106686932679885201 82944000000000000000000 Ns240p794 (Ns240p811 rfl rfl)) 

noncomputable def Ns240p820 := Ns240p789 33328 BSN.abs_quadSignPos (BSN.cos_quad_nat3 355 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 98637499 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 216 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 134097542 134217728) qz111 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz108) qz108 1) Bool.true 16777215 16777216 11652769 849346560000 134217720 134217728 1842 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz108) qz108 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz108)) Bool.true 16777215 16777216 11652769 849346560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz108) qz108) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz108)) Bool.true 16777215 16777216 745777216 54358179840000 16777215 16777216 11652769 849346560000 (Ns240p818 rfl rfl) rfl)) rfl) (Ns240p819 rfl) RS241to252.d7 

noncomputable def Ns240p821 := nat_lit 147930219610999135296519308189625051155217287807219671868047374745600 

noncomputable def Ns240p822 := nat_lit 22716309403372149321735263585043620193572322380177933742007975936 

noncomputable def Ns240p823 := nat_lit 387399510670725608963410616736546968116684255735055042999779873325056 

noncomputable def Ns240p824 := BSN.sin_dyadic_bound_f 110800628 134217728 3 2 134217728 67108864 Ns240p821 Ns240p248 Ns240p822 Ns240p823 Ns240p251 Ns240p822 98637499 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 110800628) qz365 0 2 Ns240p821 Ns240p248 Ns240p822 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 110800628) qz366 0 2 Ns240p823 Ns240p251 Ns240p822 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p825 := nat_lit 1041151286491937205494695696 

noncomputable def Ns240p826 := BSN.cos_dyadic_bound_f 5680394 134217728 2 1 134217728 67108864 Ns240p825 Ns240p146 Ns240p825 Ns240p825 Ns240p147 Ns240p825 134097542 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 5680394) qz367 0 1 Ns240p825 Ns240p146 Ns240p825 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 5680394) qz368 0 1 Ns240p825 Ns240p147 Ns240p825 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p827 := nat_lit 13489801376276687379610613761 

noncomputable def Ns240p828 := BSN.sin_dyadic_bound_f 10777087 134217728 2 1 134217728 67108864 Ns240p827 Ns240p114 Ns240p827 Ns240p827 Ns240p115 Ns240p827 10765510 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 10777087) qz365 0 1 Ns240p827 Ns240p114 Ns240p827 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 10777087) qz366 0 1 Ns240p827 Ns240p115 Ns240p827 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p829 := nat_lit 6572669206783596032932686313503540493179826770319827265754838197601 

noncomputable def Ns240p830 := nat_lit 145333829629403630040564536866812051161127940534562267275322721 

noncomputable def Ns240p831 := nat_lit 19717716952691529291537977811436887855437158055078412672729963947361 

noncomputable def Ns240p832 := BSN.cos_dyadic_bound_f 58924491 134217728 3 2 134217728 67108864 Ns240p829 Ns240p124 Ns240p830 Ns240p831 Ns240p127 Ns240p830 121489584 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 58924491) qz367 0 2 Ns240p829 Ns240p124 Ns240p830 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 58924491) qz368 0 2 Ns240p831 Ns240p127 Ns240p830 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p833 := Ns240p787 56545 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 117 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 10765510 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 121489584 134217728) qz111 rfl rfl (Ns240p820 RS241to252.d9 RS241to252.d11 RS241to252.d13 RS241to252.d17 (Ns240p824 rfl rfl) (Ns240p826 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns240p819 rfl) RS241to252.d19 RS241to252.d21 RS241to252.d23 RS241to252.d25 RS241to252.d17 (Ns240p828 rfl rfl) (Ns240p832 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns240p834 := nat_lit 43195985648333782834591592188132283487566337188882645517178357924096 

noncomputable def Ns240p835 := nat_lit 6275711172143301675423255275509429635049046524123641365849948416 

noncomputable def Ns240p836 := nat_lit 129575405522657061900423930053845831603428913473599689268803373875456 

noncomputable def Ns240p837 := BSN.cos_dyadic_bound_f 94342606 134217728 3 2 134217728 67108864 Ns240p834 Ns240p124 Ns240p835 Ns240p836 Ns240p127 Ns240p835 102403575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 94342606) qz367 0 2 Ns240p834 Ns240p124 Ns240p835 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 94342606) qz368 0 2 Ns240p836 Ns240p127 Ns240p835 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p838 := nat_lit 105011722288514882881398146865961637358917062412718968629418672554240 

noncomputable def Ns240p839 := nat_lit 11448226893795819025492732992176304231192288030208232668074639616 

noncomputable def Ns240p840 := nat_lit 275012166007329976220477682128864574304598947376500771176538688225536 

noncomputable def Ns240p841 := BSN.sin_dyadic_bound_f 101704994 134217728 3 2 134217728 67108864 Ns240p838 Ns240p248 Ns240p839 Ns240p840 Ns240p251 Ns240p839 92247441 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 101704994) qz365 0 2 Ns240p838 Ns240p248 Ns240p839 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 101704994) qz366 0 2 Ns240p840 Ns240p251 Ns240p839 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p842 := Ns240p785 75819 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 22 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 102403575 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 75 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 92247441 134217728) qz111 rfl rfl (Ns240p833 rfl rfl) (Ns240p819 rfl) RS241to252.d27 RS241to252.d29 RS241to252.d31 RS241to252.d33 RS241to252.d17 (Ns240p837 rfl rfl) (Ns240p841 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p843 := nat_lit 62283217152649773581654394498191794927857402357799237792034279234305 

noncomputable def Ns240p844 := nat_lit 4027571584299258024529120686041664592783451435880570172104088321 

noncomputable def Ns240p845 := nat_lit 163116190760089112962769414633201109735047737730006578056001610423041 

noncomputable def Ns240p846 := BSN.sin_dyadic_bound_f 89254559 134217728 3 2 134217728 67108864 Ns240p843 Ns240p248 Ns240p844 Ns240p845 Ns240p251 Ns240p844 82820093 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 89254559) qz365 0 2 Ns240p843 Ns240p248 Ns240p844 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 89254559) qz366 0 2 Ns240p845 Ns240p251 Ns240p844 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p847 := nat_lit 8664156057935518048043585196591370237210801836911114581275327620621079280223904989925076290226251366400000 

noncomputable def Ns240p848 := nat_lit 3965920279668162618141454827085222067019439608077196708204322805905697743161750565421056000000000000 

noncomputable def Ns240p849 := nat_lit 43277638440370531769337886007426939345157751465541338723716261791952139997937404695108281558296952832000000 

noncomputable def Ns240p850 := BSN.sin_dyadic_bound_f 199462840 134217728 4 3 134217728 67108864 Ns240p847 Ns240p118 Ns240p848 Ns240p849 Ns240p121 Ns240p848 133736770 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 199462840) qz365 0 3 Ns240p847 Ns240p118 Ns240p848 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 199462840) qz366 0 3 Ns240p849 Ns240p121 Ns240p848 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p851 := Ns240p783 92660 BSN.abs_quadSignNeg qz642 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 82820093 134217728) BSN.abs_quadSignNeg qz662 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133736770 134217728) qz111 rfl rfl (Ns240p842 rfl) (Ns240p819 rfl) RS241to252.d35 RS241to252.d37 RS241to252.d39 RS241to252.d41 RS241to252.d17 (Ns240p846 rfl rfl) (Ns240p850 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p852 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz108) qz108 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz108) qz108 9) 18900260 134217728 92660 134217728 18900260 134217728 92660 134217728 5073499911618560 4725065 16777216 23165 16777216 (Ns240p851 rfl) 

noncomputable def Ns240p853 := @Enclosure.Real.IsNear.mulLit_tf qz109 qz110 2754551 8388608 1 8388608 33579209781795 70368744177664 2790746405431 17592186044416000 92495645883653199045 590295810358705651712 

noncomputable abbrev qz114 := (@HPow.hPow Real Real Real qz444 qz445 qz347)

noncomputable def Ns240p854 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz114 1 1 0 1 2754551 8388608 1 8388608 2754551 8388608 1 8388608 

noncomputable abbrev qz115 := qz445

noncomputable def Ns240p855 := @Enclosure.Real.IsNear.sqrt_image qz115 721516537701 8388608000 270213 8388608000 77797924 77797955 8388608 (@Enclosure.Real.IsNear.of_eq qz115 (@HMul.hMul Real Real Real qz5 qz108 qz3) Bool.false 721516537701 8388608000 270213 8388608000 (BSN.t_div_two_pi_mk qz108 540426 1000 qz111) (@Enclosure.Real.IsNear.mulLit_ff qz108 qz3 540426 1000 0 1 2670177 16777216 1 16777216 721516537701 8388608000 270213 8388608000 (Enclosure.Real.IsNear.const Bool.false 540426 1000) RS241to252.d44 rfl)) 

noncomputable abbrev qz841 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 540426 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz682 := qz841

noncomputable abbrev qz450 := qz682

noncomputable abbrev qz116 := qz450

noncomputable abbrev qz451 := (@Enclosure.Real.IsNear.recentre' qz116 Bool.false 155595879 16777216 31 16777216 155595879 16777216 31 16777216 (Ns240p855 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns240p856 := @Enclosure.Real.IsNear.sqrt_image qz116 155595879 16777216 31 16777216 25546355 25546361 8388608 qz451 rfl 

noncomputable def Ns240p857 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz116) 12773179 4194304 3 8388608 2754550 2754552 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz116) Bool.false 51092716 16777216 6 16777216 12773179 4194304 3 8388608 (Ns240p856 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns240p858 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz116)) Bool.false 5509102 16777216 2 16777216 2754551 8388608 1 8388608 (Ns240p857 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz842 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 540426 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1)))

noncomputable abbrev qz683 := (Real.cos qz842)

noncomputable abbrev qz452 := qz683

noncomputable abbrev qz117 := (@Inv.inv Real Real.instInv qz452)

noncomputable abbrev qz684 := (@HSub.hSub Real Real Real qz814 (@HMul.hMul Real Real Real qz811 qz840 qz840) qz840)

noncomputable abbrev qz453 := (@HMul.hMul Real Real Real qz615 qz613 (@HSub.hSub Real Real Real qz619 qz684 qz626))

noncomputable abbrev qz118 := (Real.cos qz453)

noncomputable def Ns240p859 := @Enclosure.Real.IsNear.of_eq qz110 (@HMul.hMul Real Real Real qz5 qz117 qz118) Bool.false 33579209781795 

noncomputable def Ns240p860 := @Enclosure.Real.IsNear.mulLit_tt qz117 qz118 55297995 8388608 2175 

noncomputable abbrev qz119 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz452))

noncomputable abbrev qz120 := qz452

noncomputable def Ns240p861 := @Enclosure.Real.IsNear.of_eq qz117 (@Neg.neg Real Real.instNeg qz119) Bool.true 55297995 8388608 2175 4194304 (BSN.inv_eq_neg_inv_neg qz120) 

noncomputable def Ns240p862 := @Enclosure.Real.IsNear.recentre' qz119 Bool.false 110595990 16777216 8700 16777216 55297995 8388608 

noncomputable def Ns240p863 := @Enclosure.Real.IsNear.recentre' qz120 Bool.true 1272537 8388608 648577216 54358179840000 1272537 8388608 10134019 849346560000 

noncomputable abbrev qz685 := qz842

noncomputable abbrev qz454 := qz685

noncomputable abbrev qz121 := qz454

noncomputable def Ns240p864 := @Enclosure.Real.IsNear.cos_image qz121 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 28908527) qz363) Bool.false 28908527 16777216 195 16777216 Bool.true 1272537 8388608 1 

noncomputable def Ns240p865 := nat_lit 836568337719887139822281497 

noncomputable abbrev qz122 := qz446

noncomputable def Ns240p866 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz122 884279719003555 140737488355328 1 500000000000000 4600935 16777216 31 16777216 4068513508953621323925 2361183241434822606848 Ns240p865 

noncomputable def Ns240p867 := @Enclosure.Real.IsNear.subLit_ff_p qz116 qz1 155595879 16777216 31 16777216 9 1 0 1 4600935 4600935 16777216 31 

noncomputable def Ns240p868 := @Ns240p867 16777216 qz451 qz373 

noncomputable def Ns240p869 := @Enclosure.Real.IsNear.recentre' qz121 Bool.false 4068513508953621323925 2361183241434822606848 Ns240p865 Ns240p281 28908527 16777216 195 16777216 (@Ns240p866 Ns240p281 RS241to252.d43 (Ns240p868 rfl rfl) rfl) 

noncomputable def Ns240p870 := nat_lit 87955546450281425997320513921555989571879996070098251083535794977571396853732597070637592785601 

noncomputable def Ns240p871 := nat_lit 340652483312332864110844942955221160825594952595780335414375119338330290346149437293245121 

noncomputable def Ns240p872 := nat_lit 531738466611381257350253817517876892873085589941431029276743015543670263753244656051428357878465 

noncomputable def Ns240p873 := BSN.cos_dyadic_bound_t 28908527 16777216 4 3 8388608 3240000 Ns240p870 Ns240p303 Ns240p871 Ns240p872 Ns240p306 Ns240p871 1272537 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 28908527) qz627 0 3 Ns240p870 Ns240p303 Ns240p871 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 28908527) (BSN.cosOddQ 16777216) 0 3 Ns240p872 Ns240p306 Ns240p871 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz123 := (@Neg.neg Real Real.instNeg qz452)

noncomputable def Ns240p874 := @Enclosure.Real.IsNear.inv_image qz123 1272537 8388608 10134019 849346560000 55293645 55302345 8388608 (@Enclosure.Real.IsNear.neg qz120 Bool.true 1272537 8388608 10134019 849346560000 (Ns240p863 (@Ns240p864 3240000 (Ns240p869 rfl) (Enclosure.sfrac_false_div 28908527 16777216) (Ns240p873 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns240p875 := Ns240p861 (@Enclosure.Real.IsNear.neg qz119 Bool.false 55297995 8388608 2175 4194304 (@Ns240p862 2175 4194304 (Ns240p874 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p876 := @Enclosure.Real.IsNear.recentre' qz118 Bool.true 607241 8388608 

noncomputable abbrev qz124 := qz453

noncomputable def Ns240p877 := @Enclosure.Real.IsNear.cos_image qz124 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 27569133)) qz363) Bool.true 27569133 16777216 

noncomputable def Ns240p878 := nat_lit 65095777069329751428194721805 

noncomputable def Ns240p879 := nat_lit 21733306723726064992235738932913701 

noncomputable def Ns240p880 := @Enclosure.Real.IsNear.recentre' qz124 Bool.true Ns240p878 Ns240p294 Ns240p879 

noncomputable abbrev qz455 := (@HSub.hSub Real Real Real qz619 qz684 qz626)

noncomputable abbrev qz125 := qz455

noncomputable def Ns240p881 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz125 884279719003555 140737488355328 1 500000000000000 73614463467151 

noncomputable abbrev qz456 := qz684

noncomputable abbrev qz126 := qz456

noncomputable def Ns240p882 := @Enclosure.Real.IsNear.subLit_tf qz126 qz27 56022277422735 281474976710656 805352627 281474976710656 1 16 

noncomputable abbrev qz686 := (@HMul.hMul Real Real Real qz811 qz840 qz840)

noncomputable abbrev qz457 := qz686

noncomputable abbrev qz127 := qz457

noncomputable def Ns240p883 := @Enclosure.Real.IsNear.subLit_ff_n qz127 qz122 21168602874225 281474976710656 285258931 281474976710656 4600935 16777216 31 16777216 

noncomputable def Ns240p884 := @Enclosure.Real.IsNear.mulLit_ff qz122 qz122 4600935 16777216 31 16777216 4600935 16777216 31 16777216 21168602874225 281474976710656 

noncomputable def Ns240p885 := nat_lit 72687426916919974857915317150723037473815797899086488794306734851160593222510762547557866158641 

noncomputable def Ns240p886 := nat_lit 192786803427520078104063121910812035884829505099094599026659985158594246293079483359181361 

noncomputable def Ns240p887 := nat_lit 439699015277082945575624986043856710490937444592999409486174099445359643127022460809348138154545 

noncomputable def Ns240p888 := BSN.cos_dyadic_bound_t 27569133 16777216 4 3 8388608 3240000 Ns240p885 Ns240p303 Ns240p886 Ns240p887 Ns240p306 Ns240p886 607241 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 27569133) qz627 0 3 Ns240p885 Ns240p303 Ns240p886 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 27569133) (BSN.cosOddQ 16777216) 0 3 Ns240p887 Ns240p306 Ns240p886 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p889 := @Ns240p876 998497216 54358179840000 607241 8388608 15601519 849346560000 (@Ns240p877 303 16777216 Bool.true 607241 8388608 1 3240000 (@Ns240p880 Ns240p297 27569133 16777216 303 16777216 (@Ns240p881 281474976710656 805352627 281474976710656 Ns240p878 Ns240p294 Ns240p879 Ns240p297 RS241to252.d43 (@Ns240p882 0 1 1177831415474416 73614463467151 281474976710656 805352627 281474976710656 (@Ns240p883 939897849133148405760 56022277422735 281474976710656 805352627 281474976710656 (@Ns240p884 285258931 281474976710656 (Ns240p868 rfl rfl) (Ns240p868 rfl rfl) rfl) (Ns240p868 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 27569133 16777216) (BSN.cos_neg_of_bound 27569133 16777216 Bool.true 607241 8388608 1 3240000 (Ns240p888 rfl rfl)) rfl rfl) 

noncomputable abbrev qz128 := (BSN.correction_mk qz446 (BSN.cos_two_pi_p_ne_zero_mk qz443 540426 1000 9 qz447 rfl rfl (@BSN.floor_sqrt_eq_dec qz443 540426 1000 9 qz447 rfl rfl rfl)))

noncomputable def Ns240p890 := @Ns240p853 3847825447509110331 73786976294838206464000 (Ns240p854 qz29 (@Enclosure.Real.IsNear.of_eq qz114 (@Inv.inv Real Real.instInv (Real.sqrt qz116)) Bool.false 2754551 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz115 (BSN.t_div_two_pi_nonneg qz108 540426 1000 qz111)) Ns240p858) rfl) (@Ns240p859 70368744177664 2790746405431 17592186044416000 qz128 (@Ns240p860 4194304 607241 8388608 15601519 849346560000 33579209781795 70368744177664 2790746405431 17592186044416000 Ns240p875 (Ns240p889 rfl) rfl)) 

noncomputable def Ns240p891 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz108) (hardyZApproximantRS₀ qz108) Bool.true 73752799220263775035 590295810358705651712 105728572877233270331 73786976294838206464000 (@Eq.refl Real (hardyZApproximantRS₀ qz108)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz108) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz108) qz108 9) (@HMul.hMul Real Real Real qz5 qz109 qz110)) Bool.true 73752799220263775035 590295810358705651712 105728572877233270331 73786976294838206464000 (BSN.hardyZApproximantRS₀_eq qz108 9 (@BSN.floor_sqrt_eq_dec qz108 540426 1000 9 qz111 rfl rfl rfl)) (@Ns240p781 73752799220263775035 590295810358705651712 105728572877233270331 73786976294838206464000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz108) qz108 9) (@HAdd.hAdd Real Real Real qz360 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz108) qz108 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz108) qz108 9)) Bool.true 4725065 16777216 23165 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz108) qz108 9) (Ns240p852 (Ns240p851 rfl) rfl rfl)) (Ns240p890 rfl) rfl rfl)) 

theorem RS241to252.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz108) Bool.true 73752799220263775035 590295810358705651712 105728572877233270331 73786976294838206464000 := Ns240p891 

theorem RS241to252.d54 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal (RS241to252.d3 a b h)) (hardyZApproximantRS a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal (RS241to252.d3 a b h)) 

theorem RS241to252.d55 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

theorem RS241to252.d56 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 qz341 RS241to252.d55 rfl 

theorem RS241to252.d57 : Enclosure.Real.IsNear qz3 Bool.false 10937044409 68719476736 1 68719476736 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 10937044409 68719476736 1 68719476736 10937044409 68719476736 1 68719476736 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 5468522204 5468522205 34359738368 RS241to252.d56 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz129 := (@HMul.hMul Real Real Real qz344 qz323 Real.pi)

noncomputable abbrev qz687 := (Enclosure.Real.IsNear.const Bool.false 4 1)

theorem RS241to252.d58 : Enclosure.Real.IsNear qz129 Bool.false 884279719003555 70368744177664 1 250000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz323 Real.pi 4 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 70368744177664 1 250000000000000 qz687 RS241to252.d55 rfl 

noncomputable def Ns240p892 := nat_lit 781950621441006189802102638025 

noncomputable def Ns240p893 := nat_lit 79228162514264337593543950336 

noncomputable def Ns240p894 := nat_lit 26986075409044041160201671 

noncomputable def Ns240p895 := nat_lit 4294967296000000000000000000000000000000 

theorem RS241to252.d59 : Enclosure.Real.IsNear RSCompact.c2 Bool.false Ns240p892 Ns240p893 Ns240p894 Ns240p895 := @Enclosure.Real.IsNear.mulLit_ff Real.pi Real.pi 226375608064910080 72057594037927936 1 1000000000000000 226375608064910080 72057594037927936 1 1000000000000000 Ns240p892 Ns240p893 Ns240p894 Ns240p895 RS241to252.d55 RS241to252.d55 rfl 

noncomputable def Ns240p896 := nat_lit 19807040628566084398385987584 

noncomputable def Ns240p897 := nat_lit 1073741824000000000000000000000000000000 

noncomputable abbrev qz688 := (@HMul.hMul Real Real Real qz811 (Enclosure.sfrac Bool.false 4 1) RSCompact.c2)

noncomputable abbrev qz458 := qz688

noncomputable abbrev qz130 := qz458

theorem RS241to252.d60 : Enclosure.Real.IsNear qz130 Bool.false Ns240p892 Ns240p896 Ns240p894 Ns240p897 := @Enclosure.Real.IsNear.mulLit_ff qz323 RSCompact.c2 4 1 0 1 Ns240p892 Ns240p893 Ns240p894 Ns240p895 Ns240p892 Ns240p896 Ns240p894 Ns240p897 qz687 RS241to252.d59 rfl 

noncomputable def Ns240p898 := nat_lit 691463075802508163054686763366652189853178875 

noncomputable def Ns240p899 := nat_lit 2787593149816327892691964784081045188247552 

noncomputable def Ns240p900 := nat_lit 2184744797947834540264818678394244808492865883128339 

noncomputable def Ns240p901 := nat_lit 9223372036854775808000000000000000000000000000000000000000000000 

noncomputable def Ns240p902 := nat_lit 22300745198530623141535718272648361505980416 

noncomputable def Ns240p903 := nat_lit 73786976294838206464000000000000000000000000000000000000000000000 

noncomputable def Ns240p904 := @Enclosure.Real.IsNear.mulLit_ff qz332 (@HMul.hMul Real Real Real qz5 RSCompact.c2 Real.pi) 8 1 0 1 Ns240p898 Ns240p902 Ns240p900 Ns240p903 Ns240p898 Ns240p899 Ns240p900 Ns240p901 (Enclosure.Real.IsNear.const Bool.false 8 1) (@Enclosure.Real.IsNear.mulLit_ff RSCompact.c2 Real.pi Ns240p892 Ns240p893 Ns240p894 Ns240p895 226375608064910080 72057594037927936 1 1000000000000000 Ns240p898 Ns240p902 Ns240p900 Ns240p903 RS241to252.d59 RS241to252.d55 rfl) rfl 

noncomputable abbrev qz459 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 8 1) RSCompact.c10)

theorem RS241to252.d61 : Enclosure.Real.IsNear qz459 Bool.false Ns240p898 Ns240p899 Ns240p900 Ns240p901 := Ns240p904 

noncomputable def Ns240p905 := nat_lit 2345851864323018569406307914075 

noncomputable def Ns240p906 := nat_lit 80958226227132123480605013 

noncomputable def Ns240p907 := nat_lit 134217728000000000000000000000000000000 

noncomputable abbrev qz460 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 96 1) RSCompact.c2)

noncomputable abbrev qz461 := (Enclosure.sfrac Bool.false 96 1)

noncomputable def Ns240p908 := @Enclosure.Real.IsNear.inv_image qz460 Ns240p905 Ns240p435 Ns240p906 Ns240p907 36264264 36264265 34359738368 (@Enclosure.Real.IsNear.mulLit_ff qz461 RSCompact.c2 96 1 0 1 Ns240p892 Ns240p893 Ns240p894 Ns240p895 Ns240p905 Ns240p435 Ns240p906 Ns240p907 (Enclosure.Real.IsNear.const Bool.false 96 1) RS241to252.d59 rfl) rfl rfl 

noncomputable abbrev qz462 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 96 1) RSCompact.c2))

theorem RS241to252.d62 : Enclosure.Real.IsNear qz462 Bool.false 72528529 68719476736 1 68719476736 := @Enclosure.Real.IsNear.recentre' qz462 Bool.false 72528529 68719476736 1 68719476736 72528529 68719476736 1 68719476736 (Ns240p908 rfl rfl rfl rfl) rfl 

noncomputable def Ns240p909 := nat_lit 52200364127639235648072714301658654802174718042865050943921573496925786867434581801470375604798932212710506473604617030121396464258304231826709666849665 

noncomputable def Ns240p910 := nat_lit 418993997810706159361688281193932691483730181893512293053861295116305125939798343025058571817715732115313495568327689089179808837873330310826051531440128 

noncomputable def Ns240p911 := nat_lit 2491845916255725438582080967284095720026169993043336540591150136803325122955084089964500374446389296596539928506459230794036777516397776376283877901007247587811707745427460111804796657589149629843273 

noncomputable def Ns240p912 := nat_lit 1738223543152717296841904372045140579836450832642630487733249448242411557614225375966774341820679503703297378602300667402290030008506706296832000000000000000000000000000000000000000000000000000000000000 

noncomputable abbrev qz689 := (Zeta.RiemannSiegel.correctionLinear qz122)

noncomputable abbrev qz463 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) qz110 (@HMul.hMul Real Real Real qz5 qz689 (@Inv.inv Real Real.instInv qz116)))

noncomputable def Ns240p913 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz108) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz108) qz108 9) (@HMul.hMul Real Real Real qz5 qz109 qz463)) Bool.true Ns240p909 Ns240p910 Ns240p911 Ns240p912 

noncomputable def Ns240p914 := nat_lit 65803354383551435014111979415082524001601281020905044343553006338532270053256744917199657650174657312955954632788736446770442649366146182659418256841855 

noncomputable def Ns240p915 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz108) qz108 9) (@HMul.hMul Real Real Real qz5 qz109 qz463) 4725065 16777216 23165 16777216 Ns240p914 Ns240p910 

noncomputable def Ns240p916 := nat_lit 91808366692514463570332010936053140618991618623734668126688603463379822606472566200943439357990798103888717761941489568433641385405730296283877901007247587811707745427460111804796657589149629843273 

noncomputable def Ns240p917 := nat_lit 875776784248055026542615911545216409885522514344244218537176125617799262244913344752937609122842322302002112577062958511625174702497849891070782650024869232640 

noncomputable def Ns240p918 := nat_lit 23888958448600673944360434573577517352774111287431252622860497532458927082220203916064599148890202908915447429649600405572611525205431368908914105 

noncomputable def Ns240p919 := nat_lit 49947976805055875702105555676690660891977570282639538413746511354005947821116249921924897649015871538557230897942505966327167610868612564900642816 

noncomputable def Ns240p920 := nat_lit 99881136909618216784658766198254274417272447641967330022863751329943228662929081574805525308535796298005750492484204949808567297222604273232547279189529862268076280938584225866591485459865797 

noncomputable def Ns240p921 := @Enclosure.Real.IsNear.mulLit_tf qz109 qz463 2754551 8388608 1 8388608 Ns240p918 Ns240p919 Ns240p920 

noncomputable def Ns240p922 := nat_lit 621637180979031549754823817746093480528515875092493470096558135119346937280020252215900781805758298767792241073477506900652657750310912000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns240p923 := nat_lit 54319776086570408930885793542596220146076036875701476172429986066402006440031242089917574040009122473227068360378454759903444769224538313309625 

noncomputable def Ns240p924 := nat_lit 1267370324870690454862703942921551815624121422998096808692877873465179149611834930021966722271640190521143652743944601258108667275212273232547279189529862268076280938584225866591485459865797 

noncomputable abbrev qz464 := (@HMul.hMul Real Real Real qz5 qz689 (@Inv.inv Real Real.instInv qz116))

noncomputable def Ns240p925 := @Enclosure.Real.IsNear.addLit_ff qz110 qz464 33579209781795 70368744177664 2790746405431 17592186044416000 Ns240p923 Ns240p919 Ns240p924 Ns240p922 

noncomputable def Ns240p926 := nat_lit 1681036005740425896830359799887677730832995169976019941187584964562121363970203302132917573514573515793955447432024792783301880284283001422418694698567435550720 

noncomputable def Ns240p927 := nat_lit 30027300017507010138061911961161263156249312125286814507375008397619036701246061852467380853542303163784377647025452420686553810959091125 

noncomputable def Ns240p928 := nat_lit 2977131414714805823690030317109266572712515013375254774912983855843898524112477893944078543723575564536883288499266264815757728270805630976 

noncomputable def Ns240p929 := nat_lit 700379662244539513469767692207542964662526903402420781765464288219871401880922767455557185065444977348500340394828265775476027459375092467032898591606241594362126881583912330431673173 

noncomputable def Ns240p930 := nat_lit 37052463351430389270473946198588221104652635758667795067820437855681594448090806735509680617198842690455451075641960316935340032000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns240p931 := @Enclosure.Real.IsNear.mulLit_ff qz689 (@Inv.inv Real Real.instInv qz116) Ns240p927 Ns240p928 Ns240p929 Ns240p930 1809013 16777216 1 16777216 Ns240p923 

noncomputable def Ns240p932 := nat_lit 414006742333172235411832383380631684343816102009828635947862783727752657181921638759106514535022531117160498967591806814206225125 

noncomputable def Ns240p933 := nat_lit 43322963970637732180912721627235682866194329302747133987038743447103457934462900359999600095377180907771737671271930809827721216 

noncomputable def Ns240p934 := nat_lit 48282690249186093468494680005389007166732501462172369827236030808479161848559986778445865867386905466373847587813635772008242243709816853666443263871168373115048158621383504283 

noncomputable def Ns240p935 := nat_lit 2695921528460922801639677068930775647797609836464674668082475389796425184474414471734029984305295706905268240053698560000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns240p936 := @Enclosure.Real.IsNear.mulLit_tf (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz122) qz462 Ns240p932 Ns240p933 Ns240p934 Ns240p935 72528529 68719476736 1 68719476736 Ns240p927 

noncomputable abbrev qz843 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 540426 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1)))

noncomputable abbrev qz844 := (Enclosure.sfrac Bool.false 1 1)

noncomputable abbrev qz690 := (@HMul.hMul Real Real Real qz811 qz809 (@HSub.hSub Real Real Real qz814 qz843 qz844))

noncomputable abbrev qz465 := (@HMul.hMul Real Real Real qz615 qz690 qz690)

noncomputable abbrev qz466 := qz690

noncomputable abbrev qz131 := (@HMul.hMul Real Real Real qz344 qz465 qz466)

noncomputable abbrev qz132 := (Real.sin qz453)

noncomputable abbrev qz133 := (@HMul.hMul Real Real Real qz344 qz320 qz466)

noncomputable def Ns240p937 := @HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 qz131 qz132) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz133 qz129) qz118) 

noncomputable abbrev qz691 := (Real.sin qz842)

noncomputable abbrev qz467 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz615 qz613 qz691))

noncomputable abbrev qz134 := (@HMul.hMul Real Real Real qz344 qz320 qz467)

noncomputable abbrev qz468 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz615 qz688 qz683))

noncomputable abbrev qz135 := (@HMul.hMul Real Real Real qz344 qz320 qz468)

noncomputable abbrev qz469 := qz691

noncomputable abbrev qz136 := qz469

noncomputable abbrev qz470 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 8 1) RSCompact.c9)

noncomputable def Ns240p938 := @HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns240p937 (@HMul.hMul Real Real Real qz5 qz134 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz122))) (@HMul.hMul Real Real Real qz5 qz135 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz122))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz470 qz136) qz110) 

noncomputable abbrev qz137 := (BSN.cos_two_pi_p_ne_zero_mk qz443 540426 1000 9 qz447 rfl rfl (@BSN.floor_sqrt_eq_dec qz443 540426 1000 9 qz447 rfl rfl rfl))

noncomputable def Ns240p939 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz122) (@HMul.hMul Real Real Real qz5 qz117 Ns240p938) Bool.true Ns240p932 Ns240p933 Ns240p934 Ns240p935 (BSN.iteratedDeriv_three_correction_mk qz122 qz137) 

noncomputable def Ns240p940 := nat_lit 913910865072730596561169146677577317763814616993623878933690978893166819958782798654825883597872049398745006459300975 

noncomputable def Ns240p941 := nat_lit 630432099142311667396464641602297820881275828327447146687172694467931548343955369782628260078158650252906047844909056 

noncomputable def Ns240p942 := nat_lit 53290962755425289117264620268479448297519839852803979485588790329693214709850408682773296863953434753169825834720790609391226842931188591856919039757190479806156331 

noncomputable def Ns240p943 := @Enclosure.Real.IsNear.mulLit_tf qz117 Ns240p938 453005602795 68719476736 8439 68719476736 Ns240p940 Ns240p941 Ns240p942 

noncomputable def Ns240p944 := nat_lit 19615410772246270801695042383877266895416031449456020113447996771693762162426824737733331743986460110356480000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns240p945 := @Enclosure.Real.IsNear.of_eq qz117 (@Neg.neg Real Real.instNeg qz119) Bool.true 453005602795 68719476736 8439 68719476736 (BSN.inv_eq_neg_inv_neg qz120) 

noncomputable def Ns240p946 := @Enclosure.Real.IsNear.recentre' qz119 Bool.false 453005602795 68719476736 8439 68719476736 453005602795 68719476736 

noncomputable def Ns240p947 := @Enclosure.Real.IsNear.recentre' qz120 Bool.true 5212260570 34359738368 2576946036736 911978924542525440000 2606130285 17179869184 9830269 3478923509760000 

noncomputable def Ns240p948 := @Enclosure.Real.IsNear.cos_image qz121 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3700288247) (@Nat.cast Real Real.instNatCast 2147483648)) Bool.false 3700288247 2147483648 189 68719476736 Bool.true 5212260570 34359738368 1 

noncomputable def Ns240p949 := nat_lit 4166154192588905098063265 

noncomputable def Ns240p950 := nat_lit 404791212076094450571232937 

noncomputable def Ns240p951 := nat_lit 147573952589676412928000000000000000 

noncomputable def Ns240p952 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz122 884279719003555 140737488355328 1 500000000000000 4711353323 17179869184 15 34359738368 Ns240p949 Ns240p92 Ns240p950 

noncomputable def Ns240p953 := @Enclosure.Real.IsNear.subLit_ff_p qz116 qz1 159330175979 17179869184 15 34359738368 9 1 0 1 4711353323 4711353323 17179869184 15 

noncomputable def Ns240p954 := @Enclosure.Real.IsNear.sqrt_image qz115 2955331580889117 34359738368000 270213 34359738368000 318660351943 318660351973 34359738368 (@Enclosure.Real.IsNear.of_eq qz115 (@HMul.hMul Real Real Real qz5 qz108 qz3) Bool.false 2955331580889117 34359738368000 270213 34359738368000 (BSN.t_div_two_pi_mk qz108 540426 1000 qz111) (@Enclosure.Real.IsNear.mulLit_ff qz108 qz3 540426 1000 0 1 10937044409 68719476736 1 68719476736 2955331580889117 34359738368000 270213 34359738368000 (Enclosure.Real.IsNear.const Bool.false 540426 1000) RS241to252.d57 rfl)) 

noncomputable def Ns240p955 := @Ns240p953 34359738368 (@Enclosure.Real.IsNear.recentre' qz116 Bool.false 637320703916 68719476736 30 68719476736 159330175979 17179869184 15 34359738368 (Ns240p954 rfl rfl rfl rfl rfl rfl) rfl) qz373 

noncomputable def Ns240p956 := @Enclosure.Real.IsNear.recentre' qz121 Bool.false Ns240p949 Ns240p92 Ns240p950 Ns240p951 3700288247 2147483648 189 68719476736 (@Ns240p952 Ns240p951 RS241to252.d56 (Ns240p955 rfl rfl) rfl) 

noncomputable def Ns240p957 := nat_lit 1580459767661941070316191354508526136523762723872531043623870725583618670954688891253753816780620415254576961288884855489929036978069091205574312683346840900931201 

noncomputable def Ns240p958 := nat_lit 4280528994397723129507835988463142326332233186641591649370616086334967125456923470802661531755578368730858425306122747239013298128334544361442972611807824314368000 

noncomputable def Ns240p959 := nat_lit 1235289928465790066572236277711300595970757320384475140708377195903550165351765006373663616248376061296367698450177708006581511321902375210016031516462721 

noncomputable def Ns240p960 := nat_lit 16064541544458968200433245566311251095742968248612827877232039718054585281916663895701910702623473316718948052951339245263783663250687985794339524966152435541806721 

noncomputable def Ns240p961 := nat_lit 654920936142851638814698906234860775928831677556163522353704261209249970194909291032807214358603490415821339071836780327569034613635185287300774809606597120098304000 

noncomputable def Ns240p962 := BSN.cos_dyadic_bound_t 3700288247 2147483648 5 4 34359738368 13271040000 Ns240p957 Ns240p958 Ns240p959 Ns240p960 Ns240p961 Ns240p959 5212260570 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 3700288247) (BSN.cosEvenQ 2147483648) 0 4 Ns240p957 Ns240p958 Ns240p959 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 3700288247) (BSN.cosOddQ 2147483648) 0 4 Ns240p960 Ns240p961 Ns240p959 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz471 := (Ns240p947 (@Ns240p948 13271040000 (Ns240p956 rfl) (Enclosure.sfrac_false_div 3700288247 2147483648) (Ns240p962 rfl rfl) rfl rfl) rfl)

noncomputable def Ns240p963 := @Enclosure.Real.IsNear.inv_image qz123 2606130285 17179869184 9830269 3478923509760000 226502797178 226502805617 34359738368 (@Enclosure.Real.IsNear.neg qz120 Bool.true 2606130285 17179869184 9830269 3478923509760000 qz471) 

noncomputable def Ns240p964 := Ns240p945 (@Enclosure.Real.IsNear.neg qz119 Bool.false 453005602795 68719476736 8439 68719476736 (@Ns240p946 8439 68719476736 (Ns240p963 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p965 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns240p937 (@HMul.hMul Real Real Real qz5 qz134 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz122))) (@HMul.hMul Real Real Real qz5 qz135 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz122))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz470 qz136) qz110) 

noncomputable def Ns240p966 := nat_lit 74672606735348194511108400015638839624070099364327768286822859041143882032737241824465585407826586622079251655281060975 

noncomputable def Ns240p967 := nat_lit 53104548190151877663615470034349555547789602200192528328729610178161929847558251290182851948819189020053872007632803578003878246506791770599161621416864694206156331 

noncomputable def Ns240p968 := nat_lit 26459634496926268003348359053823993903283610223982213838666454072694431458125 

noncomputable def Ns240p969 := nat_lit 226156424291633194186662080095093570025917938800079226639565593765455331328 

noncomputable def Ns240p970 := nat_lit 78278345189574666108543331539361423076585084249471552883461335102537699160320681877145844161622468051619651639 

noncomputable def Ns240p971 := nat_lit 8236812897174402498305322881133099871209510814225706087822131200000000000000000000000000000000000000000000000000000 

noncomputable def Ns240p972 := nat_lit 206686813366121996416716680744373833067801979835197265901690815218481132736747657213302176250706020140980849795655672425014826769662339412016693305373052580105228379243750548042902965898444800 

noncomputable def Ns240p973 := nat_lit 64668238282972194410114386788939406274550478025054428427270031505908332311134482031597586465774522897825397772503460975 

noncomputable def Ns240p974 := @Enclosure.Real.IsNear.subLit_ft (@HSub.hSub Real Real Real qz11 Ns240p937 (@HMul.hMul Real Real Real qz5 qz134 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 2 Zeta.RiemannSiegel.correction qz122))) (@HMul.hMul Real Real Real qz5 qz135 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz122)) Ns240p973 Ns240p941 

noncomputable def Ns240p975 := nat_lit 52492494038480816721471633907643990282966762125047028382903084718031449083762899739589748047439409892786606068659835527741508372422923144959723481452429775273676331 

noncomputable def Ns240p976 := nat_lit 4237014847816993403610451152150929892375933952820711290898347016076226341595642763050127637215625 

noncomputable def Ns240p977 := nat_lit 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072 

noncomputable def Ns240p978 := nat_lit 20481186448164713194619863567756681761518616730693003086257369937356558718485442763842629577644895343276918796309566168437771505188926369 

noncomputable def Ns240p979 := nat_lit 656391079427931266262378537002689177999462975154055327932729364295993189642423762944000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns240p980 := nat_lit 19937464990640522013460783066937547240427636257507126481520931258841687873300636028612376260797298969117060943861655985329276799835647191281196820663066768630204469845983572761013000920372023324029940571963601715200 

noncomputable def Ns240p981 := nat_lit 456293753443080877048556625201923135005168051231853905114089835332989093003226002775 

noncomputable def Ns240p982 := nat_lit 30354201441027016733116592294117482916287606860189680019559568902170379456331382784 

noncomputable def Ns240p983 := nat_lit 13750005201179586146776814729199200809323488570369298166592038099054254363432929228943931723791091332173718730627 

noncomputable def Ns240p984 := nat_lit 19411161600348460652160250862654134085018743984229212186394599379435520000000000000000000000000000000000000000000000000 

noncomputable def Ns240p985 := @Enclosure.Real.IsNear.subLit_ft Ns240p937 (@HMul.hMul Real Real Real qz5 qz134 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 2 Zeta.RiemannSiegel.correction qz122)) Ns240p981 Ns240p982 Ns240p983 Ns240p984 

noncomputable def Ns240p986 := nat_lit 55191387792685898306888999516128677331320712302496812093424074677217923193973528408582888612995422038852920399376395375 

noncomputable def Ns240p987 := nat_lit 52478599352233043762094347987284259855573534718940904713314188449013020388779960998500511405909331423937398917205486469184382339390430287522480068611981775273676331 

noncomputable def Ns240p988 := nat_lit 1962952731677673073861237520924405804197134713658752594692360508222895628495759907569397088486252989030705649616300007594482700499179609392005977865961155162813728675276882943596478748797325147530854400 

noncomputable def Ns240p989 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 qz131 qz132) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz133 qz129) qz118) 

noncomputable def Ns240p990 := nat_lit 691300201654186324842772672815703732138891794322313775890086873230929671253591340375 

noncomputable def Ns240p991 := nat_lit 1493779952661368963947605839945359889040608602172291408769298325491299804309902918410717516021329110724572910209 

noncomputable def Ns240p992 := nat_lit 6470387200116153550720083620884711361672914661409737395464866459811840000000000000000000000000000000000000000000000000 

noncomputable def Ns240p993 := nat_lit 22630297786692806884754617785964948741692194574675 

noncomputable def Ns240p994 := nat_lit 2923003274661805836407369665432566039311865085952 

noncomputable def Ns240p995 := nat_lit 14623375465647611636425420751317684423188706134911701174409184595583 

noncomputable def Ns240p996 := nat_lit 30625413022884461711703714668859139031040000000000000000000000000000000000 

noncomputable def Ns240p997 := nat_lit 1333748135521852045404578724369423099792342528561210052758202039699150656866435995370154891837691032422721076647714357393706765516800 

noncomputable def Ns240p998 := nat_lit 40344810600569848114740788610399740245215104528328997177405615692937497375 

noncomputable def Ns240p999 := nat_lit 1766847064778384329583297500742918515827483896875618958121606201292619776 

noncomputable def Ns240p1000 := @Enclosure.Real.IsNear.mulLit_tt qz131 qz132 Ns240p998 Ns240p999 

noncomputable def Ns240p1001 := nat_lit 53215427798128159931213523094586182598869682812030780392041437919727582304473146219436914045465751 

noncomputable def Ns240p1002 := nat_lit 401734511064747568885490523085290650630550748445698208825344000000000000000000000000000000000000000000000 

noncomputable def Ns240p1003 := nat_lit 11763190239253901986153147138641626106985693577025 

noncomputable def Ns240p1004 := nat_lit 1461501637330902918203684832716283019655932542976 

noncomputable def Ns240p1005 := nat_lit 169474233078674188972617443881858744598590168067168386388685501 

noncomputable def Ns240p1006 := nat_lit 5444517870735015415413993718908291383296000000000000000000000000000000 

noncomputable abbrev qz138 := qz465

noncomputable abbrev qz139 := qz466

noncomputable def Ns240p1007 := @Enclosure.Real.IsNear.mulLit_ft qz138 qz139 Ns240p1003 Ns240p1004 Ns240p1005 Ns240p1006 

noncomputable def Ns240p1008 := nat_lit 3429750754683771767411295 

noncomputable def Ns240p1009 := nat_lit 1208925819614629174706176 

noncomputable def Ns240p1010 := nat_lit 404791197769179502760249001 

noncomputable def Ns240p1011 := nat_lit 73786976294838206464000000000000000 

noncomputable def Ns240p1012 := @Enclosure.Real.IsNear.mulLit_tt qz139 qz139 Ns240p1008 Ns240p1009 Ns240p1010 Ns240p1011 Ns240p1008 Ns240p1009 

noncomputable abbrev qz692 := (@HSub.hSub Real Real Real qz814 qz843 qz844)

noncomputable abbrev qz472 := qz692

noncomputable abbrev qz140 := qz472

noncomputable def Ns240p1013 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz140 884279719003555 140737488355328 1 500000000000000 3878581269 8589934592 15 17179869184 

noncomputable abbrev qz693 := qz843

noncomputable abbrev qz473 := qz693

noncomputable abbrev qz141 := qz473

noncomputable abbrev qz694 := qz844

noncomputable abbrev qz474 := qz694

noncomputable abbrev qz142 := qz474

noncomputable def Ns240p1014 := @Enclosure.Real.IsNear.subLit_ff_n qz141 qz142 4711353323 8589934592 15 17179869184 1 1 0 1 3878581269 

noncomputable def Ns240p1015 := @Enclosure.Real.IsNear.mulLit_ff qz0 qz122 2 1 0 1 4711353323 17179869184 15 34359738368 4711353323 8589934592 15 

noncomputable def Ns240p1016 := @Enclosure.Real.IsNear.recentre' qz132 Bool.true 34269597074 34359738368 

noncomputable abbrev qz695 := (@Nat.cast Real Real.instNatCast 68719476736)

noncomputable def Ns240p1017 := @Enclosure.Real.IsNear.sin_image qz124 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 112923125949)) qz695) Bool.true 112923125949 68719476736 

noncomputable def Ns240p1018 := nat_lit 68257841295696787633620093393941045 

noncomputable def Ns240p1019 := nat_lit 41538374868278621028243970633760768 

noncomputable def Ns240p1020 := nat_lit 21536976181007106175684210164558308467 

noncomputable def Ns240p1021 := @Enclosure.Real.IsNear.recentre' qz124 Bool.true Ns240p1018 Ns240p1019 Ns240p1020 

noncomputable def Ns240p1022 := nat_lit 5070602400912917605986812821504000000000000000 

noncomputable def Ns240p1023 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz125 884279719003555 140737488355328 1 500000000000000 77190327708310107719 

noncomputable def Ns240p1024 := @Enclosure.Real.IsNear.subLit_tf qz126 qz27 58743583634600556103 295147905179352825856 798077275125 1180591620717411303424 1 16 

noncomputable def Ns240p1025 := @Enclosure.Real.IsNear.subLit_ff_n qz127 qz122 22196850134143142329 295147905179352825856 282681199605 1180591620717411303424 4711353323 17179869184 15 34359738368 

noncomputable def Ns240p1026 := nat_lit 1009207082241800809943192829952 

noncomputable def Ns240p1027 := @Enclosure.Real.IsNear.mulLit_ff qz122 qz122 4711353323 17179869184 15 34359738368 4711353323 17179869184 15 34359738368 22196850134143142329 295147905179352825856 

noncomputable def Ns240p1028 := nat_lit 4206450051398191022698936679251812525209122520367012566626396660916569018688231962807897382680313411369629428580394738003238791467469097201 

noncomputable def Ns240p1029 := nat_lit 69061887427279807374175457422696049589758900585025510522285359577850094671315332446731519433112496475662717985575392155893264493730122956800 

noncomputable def Ns240p1030 := nat_lit 4299269818100326139151108916172628955474052779234414352375601308097558496034169858979369769220425810390270219893476704782256828303601 

noncomputable def Ns240p1031 := nat_lit 21000958873131085795803849077063207803867894813711356274540256269167656065585073356523700741620665325365526359534121053897551180131709470961 

noncomputable def Ns240p1032 := nat_lit 2417166059954793258096141009794361735641561520475892868279987585224753313496036635635603180158937376648195129495138725456264257280554303488000 

noncomputable def Ns240p1033 := BSN.sin_dyadic_bound_f 112923125949 68719476736 4 3 34359738368 13271040000 Ns240p1028 Ns240p1029 Ns240p1030 Ns240p1031 Ns240p1032 Ns240p1030 34269597074 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 112923125949) (BSN.sinEvenQ 68719476736) 0 3 Ns240p1028 Ns240p1029 Ns240p1030 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 112923125949) (BSN.sinOddQ 68719476736) 0 3 Ns240p1031 Ns240p1032 Ns240p1030 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1034 := @Ns240p1016 985965789184 227994731135631360000 17134798537 17179869184 3761161 869730877440000 (@Ns240p1017 73 17179869184 Bool.true 34269597074 34359738368 1 13271040000 (@Ns240p1021 Ns240p1022 112923125949 68719476736 73 17179869184 (@Ns240p1023 295147905179352825856 798077275125 1180591620717411303424 Ns240p1018 Ns240p1019 Ns240p1020 Ns240p1022 RS241to252.d56 (@Ns240p1024 0 1 1235045243332961723504 77190327708310107719 295147905179352825856 798077275125 1180591620717411303424 (@Ns240p1025 Ns240p1026 58743583634600556103 295147905179352825856 798077275125 1180591620717411303424 (@Ns240p1027 282681199605 1180591620717411303424 (Ns240p955 rfl rfl) (Ns240p955 rfl rfl) rfl) (Ns240p955 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 112923125949 68719476736) (BSN.sin_neg_of_bound 112923125949 68719476736 Bool.false 34269597074 34359738368 1 13271040000 (Ns240p1033 rfl rfl)) rfl rfl) 

noncomputable def Ns240p1035 := nat_lit 9098577100811989188838482325977756461175 

noncomputable def Ns240p1036 := nat_lit 85070591730234615865843651857942052864 

noncomputable def Ns240p1037 := nat_lit 32771182758280510565234011294875489735615694343855901 

noncomputable def Ns240p1038 := @Enclosure.Real.IsNear.mulLit_tt (@HMul.hMul Real Real Real qz5 qz133 qz129) qz118 Ns240p1035 Ns240p1036 Ns240p1037 

noncomputable def Ns240p1039 := nat_lit 158456325028528675187087900672000000000000000000000000000000 

noncomputable def Ns240p1040 := nat_lit 10289252264051315302233885 

noncomputable def Ns240p1041 := nat_lit 1214373593307538508280747003 

noncomputable def Ns240p1042 := @Enclosure.Real.IsNear.mulLit_tf qz133 qz129 Ns240p1040 Ns240p1009 Ns240p1041 Ns240p1011 884279719003555 

noncomputable def Ns240p1043 := @Enclosure.Real.IsNear.mulLit_ft qz320 qz139 3 1 0 1 Ns240p1008 Ns240p1009 Ns240p1010 

noncomputable def Ns240p1044 := @Enclosure.Real.IsNear.recentre' qz118 Bool.true 2487234821 34359738368 

noncomputable def Ns240p1045 := @Enclosure.Real.IsNear.cos_image qz124 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 112923125949)) qz695) Bool.true 112923125949 68719476736 

noncomputable def Ns240p1046 := nat_lit 1578992310180325394129161343908041046118791997836082431796549751127391454668547384479668546123666824148656222973276191616113680464905279885639336737161255563286360124954530560249126966081 

noncomputable def Ns240p1047 := nat_lit 5174842022936451849208033726988381676994660555726632972699833299014846850082204673180855169884728450418683224900597020294179740818790067306040739502139169983341866199585122315055136768000 

noncomputable def Ns240p1048 := nat_lit 699079020686123533201498924057213245191214707165444561762310617452007083439849642868975704098613687247821047573114509223033356065399261669675810279739773425125264781952083284801 

noncomputable def Ns240p1049 := nat_lit 16059286748633732714783606422247889888654529985188318852783833266818805126007691365423817194737071360119960565145100283730648035685319159410655860130345408892683771803506658030583263777601 

noncomputable def Ns240p1050 := nat_lit 791750829509277132928829160229222396580183065026174844823074494749271568062577314996670840992363452914058533409791344105009500345274880297824233143827293007451305528536523714203435925504000 

noncomputable def Ns240p1051 := BSN.cos_dyadic_bound_t 112923125949 68719476736 5 4 34359738368 13271040000 Ns240p1046 Ns240p1047 Ns240p1048 Ns240p1049 Ns240p1050 Ns240p1048 2487234821 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 112923125949) (BSN.cosEvenQ 68719476736) 0 4 Ns240p1046 Ns240p1047 Ns240p1048 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 112923125949) (BSN.cosOddQ 68719476736) 0 4 Ns240p1049 Ns240p1050 Ns240p1048 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1052 := @Ns240p1044 985965789184 227994731135631360000 2487234821 34359738368 3761161 869730877440000 (@Ns240p1045 73 17179869184 Bool.true 2487234821 34359738368 1 13271040000 (@Ns240p1021 Ns240p1022 112923125949 68719476736 73 17179869184 (@Ns240p1023 295147905179352825856 798077275125 1180591620717411303424 Ns240p1018 Ns240p1019 Ns240p1020 Ns240p1022 RS241to252.d56 (@Ns240p1024 0 1 1235045243332961723504 77190327708310107719 295147905179352825856 798077275125 1180591620717411303424 (@Ns240p1025 Ns240p1026 58743583634600556103 295147905179352825856 798077275125 1180591620717411303424 (@Ns240p1027 282681199605 1180591620717411303424 (Ns240p955 rfl rfl) (Ns240p955 rfl rfl) rfl) (Ns240p955 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 112923125949 68719476736) (BSN.cos_neg_of_bound 112923125949 68719476736 Bool.true 2487234821 34359738368 1 13271040000 (Ns240p1051 rfl rfl)) rfl rfl) 

noncomputable abbrev qz475 := (@Ns240p1013 Ns240p1008 Ns240p1009 Ns240p1010 Ns240p1011 RS241to252.d56 (@Ns240p1014 3878581269 8589934592 15 17179869184 (@Ns240p1015 17179869184 (Enclosure.Real.IsNear.const Bool.false 2 1) (Ns240p955 rfl rfl) rfl) (Enclosure.Real.IsNear.const Bool.false 1 1) rfl rfl) rfl)

noncomputable abbrev qz476 := (Enclosure.Real.IsNear.const Bool.false 3 1)

noncomputable def Ns240p1053 := @Ns240p989 Ns240p990 Ns240p982 Ns240p991 Ns240p992 Ns240p993 Ns240p994 Ns240p995 Ns240p996 Ns240p997 Ns240p981 Ns240p982 Ns240p983 Ns240p984 (@Ns240p1000 Ns240p1001 Ns240p1002 17134798537 17179869184 3761161 869730877440000 Ns240p990 Ns240p982 Ns240p991 Ns240p992 (@Ns240p1007 Ns240p1008 Ns240p1009 Ns240p1010 Ns240p1011 Ns240p998 Ns240p999 Ns240p1001 Ns240p1002 (@Ns240p1012 Ns240p1010 Ns240p1011 Ns240p1003 Ns240p1004 Ns240p1005 Ns240p1006 qz475 qz475 rfl) qz475 rfl) (Ns240p1034 rfl) rfl) (@Ns240p1038 Ns240p1039 2487234821 34359738368 3761161 869730877440000 Ns240p993 Ns240p994 Ns240p995 Ns240p996 (@Ns240p1042 70368744177664 1 250000000000000 Ns240p1035 Ns240p1036 Ns240p1037 Ns240p1039 (@Ns240p1043 Ns240p1011 Ns240p1040 Ns240p1009 Ns240p1041 Ns240p1011 qz476 qz475 rfl) RS241to252.d58 rfl) (Ns240p1052 rfl) rfl) rfl rfl 

noncomputable def Ns240p1054 := nat_lit 90095977955826410862168105 

noncomputable def Ns240p1055 := nat_lit 4835703278458516698824704 

noncomputable def Ns240p1056 := nat_lit 265280410063071498661007347342123 

noncomputable def Ns240p1057 := nat_lit 4980620899901578936320000000000000000000 

noncomputable def Ns240p1058 := nat_lit 612584368857685839528446849088114308811385944237642555749193793472456680582691914543558607575 

noncomputable def Ns240p1059 := @Enclosure.Real.IsNear.mulLit_tf qz134 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz122) Ns240p1054 Ns240p1055 Ns240p1056 Ns240p1057 Ns240p1058 

noncomputable def Ns240p1060 := nat_lit 130370302485407109521180524058200202307293977194619920040712988758680403184853549195737432064 

noncomputable def Ns240p1061 := nat_lit 2261894533995119319618393310078469415526005100878498038809613749114152693555683501676360651724098686677325262623664931966463 

noncomputable def Ns240p1062 := nat_lit 15753385906270350390297084888064540271987111403697327870385504743103836551418170310656000000000000000000000000000000000000000000 

noncomputable def Ns240p1063 := nat_lit 30031992651942136954056035 

noncomputable abbrev qz143 := qz467

noncomputable def Ns240p1064 := @Enclosure.Real.IsNear.mulLit_ft qz320 qz143 3 1 0 1 Ns240p1063 Ns240p1055 Ns240p1056 

noncomputable def Ns240p1065 := nat_lit 14941862699704736808960000000000000000000 

noncomputable def Ns240p1066 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz136 884279719003555 140737488355328 1 500000000000000 33962095937 34359738368 9830269 3478923509760000 Ns240p1063 

noncomputable def Ns240p1067 := @Enclosure.Real.IsNear.recentre' qz136 Bool.false 33962095937 34359738368 2576946036736 911978924542525440000 33962095937 34359738368 9830269 3478923509760000 

noncomputable def Ns240p1068 := @Enclosure.Real.IsNear.sin_image qz121 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3700288247) (@Nat.cast Real Real.instNatCast 2147483648)) Bool.false 3700288247 2147483648 189 68719476736 Bool.false 33962095937 34359738368 1 

noncomputable def Ns240p1069 := nat_lit 5361084637501509244002554179783164104603457328403524266325860510071808633811222345398446911212162650518516687360599230619675689244428558296421742884183942736973441 

noncomputable def Ns240p1070 := nat_lit 72768992904761293201633211803873419547647964172907058039300473467694441132767699003645246039844832268424593230204086703063226068181687254144530534400733013344256000 

noncomputable def Ns240p1071 := nat_lit 43576057014314817217674668380386498979998450066034407402019025821412189124737394027915252964917523179128707298692457688622902020799564487254920793758465325655461505 

noncomputable def Ns240p1072 := nat_lit 4147832595571393712493093072820784914215933957855702308240126987658583144567758843207779024271155439300201814121632942074603885886356173486238240460841781760622592000 

noncomputable def Ns240p1073 := BSN.sin_dyadic_bound_f 3700288247 2147483648 5 4 34359738368 13271040000 Ns240p1069 Ns240p1070 Ns240p959 Ns240p1071 Ns240p1072 Ns240p959 33962095937 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.sinEvenP 3700288247) (BSN.sinEvenQ 2147483648) 0 4 Ns240p1069 Ns240p1070 Ns240p959 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.sinOddP 3700288247) (BSN.sinOddQ 2147483648) 0 4 Ns240p1071 Ns240p1072 Ns240p959 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz477 := (@HMul.hMul Real Real Real qz615 qz613 qz691)

noncomputable abbrev qz144 := qz477

noncomputable abbrev qz478 := (@Enclosure.Real.IsNear.neg qz144 Bool.false Ns240p1063 Ns240p1055 Ns240p1056 Ns240p1065 (@Ns240p1066 Ns240p1055 Ns240p1056 Ns240p1065 RS241to252.d56 (Ns240p1067 (@Ns240p1068 13271040000 (Ns240p956 rfl) (Enclosure.sfrac_false_div 3700288247 2147483648) (Ns240p1073 rfl rfl) rfl rfl) rfl) rfl))

noncomputable def Ns240p1074 := @Ns240p1064 Ns240p1065 Ns240p1054 Ns240p1055 Ns240p1056 Ns240p1057 qz476 qz478 rfl 

noncomputable abbrev qz145 := (@HMul.hMul Real Real Real qz344 qz465 (Real.cos qz453))

noncomputable def Ns240p1075 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz145) (@HMul.hMul Real Real Real qz5 qz129 qz132) 

noncomputable abbrev qz146 := (@HMul.hMul Real Real Real qz344 qz316 qz467)

noncomputable abbrev qz147 := (@HMul.hMul Real Real Real qz344 qz468 (Zeta.RiemannSiegel.correction qz446))

noncomputable def Ns240p1076 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz122) (@HMul.hMul Real Real Real qz5 qz117 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns240p1075 (@HMul.hMul Real Real Real qz5 qz146 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c8 1 Zeta.RiemannSiegel.correction qz122))) qz147)) 

noncomputable def Ns240p1077 := @Enclosure.Real.IsNear.mulLit_tt qz117 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns240p1075 (@HMul.hMul Real Real Real qz5 qz146 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 1 Zeta.RiemannSiegel.correction qz122))) qz147) 453005602795 

noncomputable def Ns240p1078 := nat_lit 1352266649856206089241172360030510798378890377444879159972319418015635805007686085 

noncomputable def Ns240p1079 := nat_lit 1897137590064188545819787018382342682267975428761855001222473056385648716020711424 

noncomputable def Ns240p1080 := nat_lit 2495019407925299051233279368700055189482152713546664713326855492401951198245805359534056558211873797744308881341 

noncomputable def Ns240p1081 := nat_lit 114620968133897625304941065318886396358627181352475075039441469875628802048000000000000000000000000000000000000000000 

noncomputable def Ns240p1082 := nat_lit 4069308810632011118958175161586352856976654714422214141438390876411432715194553915 

noncomputable def Ns240p1083 := @Enclosure.Real.IsNear.subLit_ff_n (@HSub.hSub Real Real Real qz11 Ns240p1075 (@HMul.hMul Real Real Real qz5 qz146 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz122))) qz147 Ns240p1082 Ns240p1079 

noncomputable def Ns240p1084 := nat_lit 2463247196759625304897273412192014914021548479094865201201664369899092974308764588420927119950392943324115601341 

noncomputable def Ns240p1085 := nat_lit 2296126520529462579261928114673471142401033367922068589051875 

noncomputable def Ns240p1086 := nat_lit 803469022129495137770981046170581301261101496891396417650688 

noncomputable def Ns240p1087 := nat_lit 1063194455879372747531802600539890521816995127935668474786211211345826278578625814609 

noncomputable def Ns240p1088 := nat_lit 3835564897011221618533750474980613156785029365786214400000000000000000000000000000000000000 

noncomputable def Ns240p1089 := nat_lit 1086504362818294303279281872481391167195880913530164038269543268860115347329065916082353880716318733563219056700299297322403224318598688276480 

noncomputable def Ns240p1090 := nat_lit 658645396312551560446272433876468699579664603508238508846405 

noncomputable def Ns240p1091 := nat_lit 50216813883093446110686315385661331328818843555712276103168 

noncomputable def Ns240p1092 := nat_lit 865638461872592877734259455555979109611358552914013722305717965335866108378947 

noncomputable def Ns240p1093 := nat_lit 9470530609904250909959877716001513967370442878484480000000000000000000000000000000000 

noncomputable def Ns240p1094 := @Enclosure.Real.IsNear.subLit_ff_p Ns240p1075 (@HMul.hMul Real Real Real qz5 qz146 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz122)) Ns240p1090 Ns240p1091 Ns240p1092 Ns240p1093 

noncomputable def Ns240p1095 := nat_lit 20813610738510290492036940164574558881441515400145288214816430303744393386136349125 

noncomputable def Ns240p1096 := nat_lit 2452770453413269364934246788685497479635147520183691476471587938625815450096845028834162775992340721576915601341 

noncomputable def Ns240p1097 := nat_lit 204347723176340055044244372276982683380652410486988858296779947171460736007644703186970052492836618318037205444930499750660374270552278302720 

noncomputable def Ns240p1098 := @Enclosure.Real.IsNear.subLit_ft (@Neg.neg Real Real.instNeg qz145) (@HMul.hMul Real Real Real qz5 qz129 qz132) 

noncomputable def Ns240p1099 := nat_lit 29257816369119626080081167401965967093357488413612625587525 

noncomputable def Ns240p1100 := nat_lit 38997497883471609811067316748673606635567238469448428002602746370651789819883 

noncomputable def Ns240p1101 := nat_lit 1052281178878250101106653079555723774152271430942720000000000000000000000000000000000 

noncomputable def Ns240p1102 := nat_lit 15151954835480885311799035 

noncomputable def Ns240p1103 := nat_lit 101498981822887194219527919730687 

noncomputable def Ns240p1104 := nat_lit 1867732837463092101120000000000000000000 

noncomputable def Ns240p1105 := nat_lit 796253425572553651551843690437149175629381443666160075400154277764986435242588897280 

noncomputable def Ns240p1106 := @Enclosure.Real.IsNear.neg qz145 Bool.true Ns240p1099 

noncomputable def Ns240p1107 := @Enclosure.Real.IsNear.mulLit_ft qz138 qz118 Ns240p1003 Ns240p1004 Ns240p1005 

noncomputable def Ns240p1108 := @Enclosure.Real.IsNear.mulLit_ft qz129 qz132 884279719003555 70368744177664 1 

noncomputable def Ns240p1109 := nat_lit 7470931349852368404480000000000000000000 

noncomputable def Ns240p1110 := nat_lit 693047943229444566028771548413945376474563361410559649975 

noncomputable def Ns240p1111 := @Enclosure.Real.IsNear.mulLit_tt qz146 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz122) Ns240p1063 Ns240p92 Ns240p1056 Ns240p1109 Ns240p1110 

noncomputable def Ns240p1112 := nat_lit 784637716923335095479473677900958302012794430558004314112 

noncomputable def Ns240p1113 := nat_lit 105572463880740639744231924650562449914900052545529269880082898779851443 

noncomputable def Ns240p1114 := nat_lit 61369038352179545896540007599689810508560469852579430400000000000000000000000 

noncomputable def Ns240p1115 := @Enclosure.Real.IsNear.mulLit_ft qz0 qz143 2 1 0 1 Ns240p1063 Ns240p1055 Ns240p1056 

noncomputable def Ns240p1116 := @Ns240p1115 Ns240p1065 Ns240p1063 Ns240p92 Ns240p1056 Ns240p1109 qz341 qz478 rfl 

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz344 qz466 (Real.sin qz453))

noncomputable def Ns240p1117 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz148) (@HMul.hMul Real Real Real qz5 qz143 qz110) 

noncomputable def Ns240p1118 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz122) (@HMul.hMul Real Real Real qz5 qz117 Ns240p1117) Bool.true Ns240p1110 Ns240p1112 Ns240p1113 Ns240p1114 (BSN.deriv_correction_mk qz122 qz137) 

noncomputable def Ns240p1119 := nat_lit 1529888237481847779071620761219652359409320805 

noncomputable def Ns240p1120 := nat_lit 11417981541647679048466287755595961091061972992 

noncomputable def Ns240p1121 := nat_lit 115409910865886836575207017904415833959780769248478954350951 

noncomputable def Ns240p1122 := @Enclosure.Real.IsNear.mulLit_tf qz117 Ns240p1117 453005602795 68719476736 8439 68719476736 Ns240p1119 Ns240p1120 Ns240p1121 

noncomputable def Ns240p1123 := nat_lit 446518521873655451756640159871966247072563200000000000000000000000 

noncomputable def Ns240p1124 := @Enclosure.Real.IsNear.subLit_tt_p (@Neg.neg Real Real.instNeg qz148) (@HMul.hMul Real Real Real qz5 qz143 qz110) 

noncomputable def Ns240p1125 := nat_lit 58768088213630138377880961843275415 

noncomputable def Ns240p1126 := nat_lit 20769187434139310514121985316880384 

noncomputable def Ns240p1127 := nat_lit 47436659753908603465542484032677420750189 

noncomputable def Ns240p1128 := nat_lit 2673950484856421393782108323840000000000000000000 

noncomputable def Ns240p1129 := nat_lit 33837986404007864518009633036149800832475284325 

noncomputable def Ns240p1130 := nat_lit 107488542345453621056169970331294991185725484381438411630951 

noncomputable def Ns240p1131 := nat_lit 31774535557545530213107888281149739599612267283091119198453737764529514867589120 

noncomputable def Ns240p1132 := @Enclosure.Real.IsNear.neg qz148 Bool.false Ns240p1125 

noncomputable def Ns240p1133 := @Enclosure.Real.IsNear.mulLit_tt qz139 qz132 Ns240p1008 Ns240p1009 Ns240p1010 

noncomputable def Ns240p1134 := @Enclosure.Real.IsNear.mulLit_tf qz143 qz110 Ns240p1063 Ns240p1055 Ns240p1056 Ns240p1065 1126731309379818924695 2361183241434822606848 

noncomputable def Ns240p1135 := nat_lit 119534901597637894471680000 

noncomputable def Ns240p1136 := @Enclosure.Real.IsNear.of_eq qz110 (@HMul.hMul Real Real Real qz5 qz117 qz118) Bool.false 1126731309379818924695 

noncomputable def Ns240p1137 := @Enclosure.Real.IsNear.mulLit_tt qz117 qz118 453005602795 68719476736 8439 

noncomputable abbrev qz479 := (@Ns240p1136 2361183241434822606848 4470261417388927223 Ns240p1135 qz128 (@Ns240p1137 68719476736 2487234821 34359738368 3761161 869730877440000 1126731309379818924695 2361183241434822606848 4470261417388927223 Ns240p1135 Ns240p964 (Ns240p1052 rfl) rfl))

noncomputable def Ns240p1138 := @Ns240p1134 4470261417388927223 Ns240p1135 Ns240p1129 Ns240p1120 Ns240p1130 Ns240p1123 qz478 qz479 

noncomputable def Ns240p1139 := @Ns240p1111 Ns240p1112 Ns240p1113 Ns240p1114 Ns240p1095 Ns240p1079 Ns240p1096 Ns240p1081 Ns240p1116 (Ns240p1118 (@Ns240p1122 Ns240p1123 Ns240p1110 Ns240p1112 Ns240p1113 Ns240p1114 Ns240p964 (@Ns240p1124 Ns240p1125 Ns240p1126 Ns240p1127 Ns240p1128 Ns240p1129 Ns240p1120 Ns240p1130 Ns240p1123 Ns240p1131 Ns240p1119 Ns240p1120 Ns240p1121 Ns240p1123 (@Ns240p1132 Ns240p1126 Ns240p1127 Ns240p1128 (@Ns240p1133 Ns240p1011 17134798537 17179869184 3761161 869730877440000 Ns240p1125 Ns240p1126 Ns240p1127 Ns240p1128 qz475 (Ns240p1034 rfl) rfl)) (Ns240p1138 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns240p1140 := @Ns240p1094 Ns240p1095 Ns240p1079 Ns240p1096 Ns240p1081 Ns240p1097 Ns240p1082 Ns240p1079 Ns240p1084 Ns240p1081 (@Ns240p1098 Ns240p1099 Ns240p1091 Ns240p1100 Ns240p1101 Ns240p1102 Ns240p1009 Ns240p1103 Ns240p1104 Ns240p1105 Ns240p1090 Ns240p1091 Ns240p1092 Ns240p1093 (@Ns240p1106 Ns240p1091 Ns240p1100 Ns240p1101 (@Ns240p1107 Ns240p1006 2487234821 34359738368 3761161 869730877440000 Ns240p1099 Ns240p1091 Ns240p1100 Ns240p1101 (@Ns240p1012 Ns240p1010 Ns240p1011 Ns240p1003 Ns240p1004 Ns240p1005 Ns240p1006 qz475 qz475 rfl) (Ns240p1052 rfl) rfl)) (@Ns240p1108 250000000000000 17134798537 17179869184 3761161 869730877440000 Ns240p1102 Ns240p1009 Ns240p1103 Ns240p1104 RS241to252.d58 (Ns240p1034 rfl) rfl) rfl rfl) Ns240p1139 

noncomputable def Ns240p1141 := nat_lit 2037865195911976572115717841635345087125 

noncomputable def Ns240p1142 := nat_lit 340282366920938463463374607431768211456 

noncomputable def Ns240p1143 := nat_lit 7158876598062628871092693329397393709968204444194077336941 

noncomputable def Ns240p1144 := nat_lit 64174811636554113450770599772160000000000000000000000000000000000 

noncomputable abbrev qz149 := qz468

noncomputable def Ns240p1145 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz110 Ns240p1141 Ns240p1142 Ns240p1143 Ns240p1144 1126731309379818924695 2361183241434822606848 

noncomputable def Ns240p1146 := @Enclosure.Real.IsNear.mulLit_ft qz130 qz120 Ns240p892 Ns240p896 Ns240p894 Ns240p897 2606130285 17179869184 9830269 3478923509760000 Ns240p1141 

noncomputable abbrev qz480 := (@HMul.hMul Real Real Real qz615 qz688 qz683)

noncomputable abbrev qz150 := qz480

noncomputable def Ns240p1147 := @Ns240p1145 4470261417388927223 Ns240p1135 Ns240p1085 Ns240p1086 Ns240p1087 Ns240p1088 (@Enclosure.Real.IsNear.neg qz150 Bool.true Ns240p1141 Ns240p1142 Ns240p1143 Ns240p1144 (@Ns240p1146 Ns240p1142 Ns240p1143 Ns240p1144 RS241to252.d60 qz471 rfl)) qz479 

noncomputable def Ns240p1148 := nat_lit 6113595587735929716347153524906035261375 

noncomputable def Ns240p1149 := nat_lit 21391603878851371150256866590720000000000000000000000000000000000 

noncomputable def Ns240p1150 := @Enclosure.Real.IsNear.mulLit_ft qz135 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz122) Ns240p1148 Ns240p1142 Ns240p1143 Ns240p1149 Ns240p1110 

noncomputable def Ns240p1151 := @Enclosure.Real.IsNear.mulLit_ff qz320 qz149 3 1 0 1 Ns240p1141 Ns240p1142 Ns240p1143 

noncomputable def Ns240p1152 := @Ns240p1151 Ns240p1144 Ns240p1148 Ns240p1142 Ns240p1143 Ns240p1149 qz476 (@Enclosure.Real.IsNear.neg qz150 Bool.true Ns240p1141 Ns240p1142 Ns240p1143 Ns240p1144 (@Ns240p1146 Ns240p1142 Ns240p1143 Ns240p1144 RS241to252.d60 qz471 rfl)) rfl 

noncomputable def Ns240p1153 := @Ns240p1150 Ns240p1112 Ns240p1113 Ns240p1114 Ns240p976 Ns240p977 Ns240p978 Ns240p979 Ns240p1152 (Ns240p1118 (@Ns240p1122 Ns240p1123 Ns240p1110 Ns240p1112 Ns240p1113 Ns240p1114 Ns240p964 (@Ns240p1124 Ns240p1125 Ns240p1126 Ns240p1127 Ns240p1128 Ns240p1129 Ns240p1120 Ns240p1130 Ns240p1123 Ns240p1131 Ns240p1119 Ns240p1120 Ns240p1121 Ns240p1123 (@Ns240p1132 Ns240p1126 Ns240p1127 Ns240p1128 (@Ns240p1133 Ns240p1011 17134798537 17179869184 3761161 869730877440000 Ns240p1125 Ns240p1126 Ns240p1127 Ns240p1128 qz475 (Ns240p1034 rfl) rfl)) (Ns240p1138 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns240p1154 := @Ns240p974 Ns240p975 Ns240p944 Ns240p976 Ns240p977 Ns240p978 Ns240p979 Ns240p980 Ns240p966 Ns240p941 Ns240p967 Ns240p944 (@Ns240p985 Ns240p986 Ns240p941 Ns240p987 Ns240p944 Ns240p988 Ns240p973 Ns240p941 Ns240p975 Ns240p944 Ns240p1053 (@Ns240p1059 Ns240p1060 Ns240p1061 Ns240p1062 Ns240p986 Ns240p941 Ns240p987 Ns240p944 Ns240p1074 (@Ns240p1076 Bool.false Ns240p1058 Ns240p1060 Ns240p1061 Ns240p1062 (BSN.iteratedDeriv_two_correction_mk qz122 qz137) (@Ns240p1077 68719476736 8439 68719476736 Ns240p1078 Ns240p1079 Ns240p1080 Ns240p1081 Ns240p1058 Ns240p1060 Ns240p1061 Ns240p1062 Ns240p964 (@Ns240p1083 Ns240p1084 Ns240p1081 Ns240p1085 Ns240p1086 Ns240p1087 Ns240p1088 Ns240p1089 Ns240p1078 Ns240p1079 Ns240p1080 Ns240p1081 (Ns240p1140 rfl rfl) (Ns240p1147 rfl) rfl rfl) rfl)) rfl) rfl rfl) Ns240p1153 

noncomputable def Ns240p1155 := nat_lit 23483535317297885498888910834942258778304798897171730875 

noncomputable def Ns240p1156 := nat_lit 95780971304118053647396689196894323976171195136475136 

noncomputable def Ns240p1157 := nat_lit 193190041649412884047779403533332029031251978963052391260500535031535343028528629947 

noncomputable def Ns240p1158 := nat_lit 275628717205960155405333432019732251279360000000000000000000000000000000000000000000000000 

noncomputable def Ns240p1159 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz332 RSCompact.c11) qz136) qz110 Ns240p1155 Ns240p1156 Ns240p1157 Ns240p1158 1126731309379818924695 2361183241434822606848 4470261417388927223 

noncomputable def Ns240p1160 := @Enclosure.Real.IsNear.mulLit_ff qz459 qz136 Ns240p898 Ns240p899 Ns240p900 Ns240p901 33962095937 34359738368 9830269 3478923509760000 Ns240p1155 

noncomputable abbrev qz481 := (Ns240p1067 (@Ns240p1068 13271040000 (Ns240p956 rfl) (Enclosure.sfrac_false_div 3700288247 2147483648) (Ns240p1073 rfl rfl) rfl rfl) rfl)

noncomputable def Ns240p1161 := Ns240p939 (@Ns240p943 Ns240p944 Ns240p932 Ns240p933 Ns240p934 Ns240p935 Ns240p964 (@Ns240p965 Ns240p966 Ns240p941 Ns240p967 Ns240p944 Ns240p968 Ns240p969 Ns240p970 Ns240p971 Ns240p972 Ns240p940 Ns240p941 Ns240p942 Ns240p944 (Ns240p1154 rfl rfl) (@Ns240p1159 Ns240p1135 Ns240p968 Ns240p969 Ns240p970 Ns240p971 (@Ns240p1160 Ns240p1156 Ns240p1157 Ns240p1158 RS241to252.d61 qz481 rfl) qz479 rfl) rfl rfl) rfl) 

noncomputable def Ns240p1162 := @Enclosure.Real.IsNear.of_eq qz689 (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz122) qz462)) Bool.false Ns240p927 Ns240p928 Ns240p929 Ns240p930 (BSN.correctionLinear_mk qz122) (@Enclosure.Real.IsNear.neg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz122) qz462) Bool.true Ns240p927 Ns240p928 Ns240p929 Ns240p930 (@Ns240p936 Ns240p928 Ns240p929 Ns240p930 Ns240p1161 RS241to252.d62 rfl)) 

noncomputable def Ns240p1163 := @Enclosure.Real.IsNear.inv_image qz116 155595879 16777216 31 16777216 904506 904507 8388608 qz451 rfl 

noncomputable def Ns240p1164 := @Ns240p931 Ns240p919 Ns240p924 Ns240p922 Ns240p1162 (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz116) Bool.false 1809013 16777216 1 16777216 1809013 16777216 1 16777216 (Ns240p1163 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns240p1165 := @Ns240p921 Ns240p922 Ns240p914 Ns240p910 Ns240p916 Ns240p912 (Ns240p854 qz29 (@Enclosure.Real.IsNear.of_eq qz114 (@Inv.inv Real Real.instInv (Real.sqrt qz116)) Bool.false 2754551 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz115 (BSN.t_div_two_pi_nonneg qz108 540426 1000 qz111)) Ns240p858) rfl) (@Ns240p925 Ns240p926 Ns240p918 Ns240p919 Ns240p920 Ns240p922 (@Ns240p859 70368744177664 2790746405431 17592186044416000 qz128 (@Ns240p860 4194304 607241 8388608 15601519 849346560000 33579209781795 70368744177664 2790746405431 17592186044416000 Ns240p875 (Ns240p889 rfl) rfl)) (Ns240p1164 rfl) rfl rfl) 

noncomputable def Ns240p1166 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz108) (hardyZApproximantRS qz108) Bool.true Ns240p909 Ns240p910 Ns240p911 Ns240p912 (@Eq.refl Real (hardyZApproximantRS qz108)) (Ns240p913 (BSN.hardyZApproximantRS_eq qz108 9 (@BSN.floor_sqrt_eq_dec qz108 540426 1000 9 qz111 rfl rfl rfl)) (@Ns240p915 Ns240p916 Ns240p912 Ns240p917 Ns240p909 Ns240p910 Ns240p911 Ns240p912 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz108) qz108 9) (@HAdd.hAdd Real Real Real qz360 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz108) qz108 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz108) qz108 9)) Bool.true 4725065 16777216 23165 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz108) qz108 9) (Ns240p852 (Ns240p851 rfl) rfl rfl)) (Ns240p1165 rfl) rfl rfl)) 

theorem RS241to252.d63 : Enclosure.Real.IsNear (hardyZApproximantRS qz108) Bool.true Ns240p909 Ns240p910 Ns240p911 Ns240p912 := Ns240p1166 

theorem RS241to252.d64 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal (RS241to252.d3 a b h)) (hardyZApproximantRS b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal (RS241to252.d3 a b h)) 

noncomputable def Ns240p1167 := nat_lit 5151135545648419081562208939154128014766263479517851672533725220416472966059831727607087054736554107668695587212702920442086651854756514240342066971 

noncomputable def Ns240p1168 := nat_lit 102293456496754433437912178025862473506770063938845774671352855253004181137646079840102190385184504910965208878986252219038039267058918532916516487168 

noncomputable def Ns240p1169 := nat_lit 11891316023838235105323121862541843392961531703730923803932621590672820240233189095535000766323483410987256057357957204947840197550933887796604024363936496464499350471488197779041304755684731843 

noncomputable def Ns240p1170 := nat_lit 8382636685728767828134183892964605419735970450629969558898772416292494008556256635642237373749418902890130105142267879061969666321888051200000000000000000000000000000000000000000000000000000000000 

noncomputable abbrev qz845 := (Enclosure.sfrac Bool.false 541836 1000)

noncomputable abbrev qz696 := qz845

noncomputable abbrev qz482 := qz696

noncomputable abbrev qz151 := qz482

noncomputable abbrev qz846 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 541836 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz697 := qz846

noncomputable abbrev qz483 := qz697

noncomputable abbrev qz152 := qz483

noncomputable abbrev qz847 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 541836 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz698 := qz847

noncomputable abbrev qz484 := qz698

noncomputable abbrev qz153 := (Zeta.RiemannSiegel.correction qz484)

noncomputable abbrev qz154 := qz484

noncomputable abbrev qz848 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 541836 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz699 := qz848

noncomputable abbrev qz485 := qz699

noncomputable abbrev qz155 := qz485

noncomputable abbrev qz486 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz618 qz152 qz8))

noncomputable abbrev qz700 := (Zeta.RiemannSiegel.correctionLinear qz154)

noncomputable abbrev qz487 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) qz153 (@HMul.hMul Real Real Real qz5 qz700 (@Inv.inv Real Real.instInv qz155)))

noncomputable def Ns240p1171 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz151) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz151) qz151 9) (@HMul.hMul Real Real Real qz5 qz486 qz487)) Bool.false Ns240p1167 Ns240p1168 Ns240p1169 Ns240p1170 

noncomputable def Ns240p1172 := nat_lit 15706733794941056559552205546445999499305908863941580848290509854773332591221574392458039388642141484576923629944691882275285571111088736535169009435 

noncomputable def Ns240p1173 := @Enclosure.Real.IsNear.subLit_tt_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz151) qz151 9) (@HMul.hMul Real Real Real qz5 qz486 qz487) 3462461 33554432 46453 33554432 Ns240p1172 Ns240p1168 

noncomputable def Ns240p1174 := nat_lit 286332754797696677483924811616206637644230092333836947581583520529501343359482829385454479180796677504322602421996143647035674629769087796604024363936496464499350471488197779041304755684731843 

noncomputable def Ns240p1175 := nat_lit 172843427389242773979781593618639325990769583817565146732119150615149553819492931635434525296237982720089924609828709680175406497768101333634589542917865472 

noncomputable def Ns240p1176 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 541836 1000 121 161 134217728 67108864 2251799813685248 Bool.false 125653864910 1797 

noncomputable def Ns240p1177 := Ns240p1176 279097919 42 47453128 8 294906479 42 44739240 8 Bool.false 58331713 76021 Bool.true 61160719 Bool.true 193659070 7074237752028440 1 Bool.false 59065947 Bool.true Bool.false 133121021 Bool.true Bool.true 6924922 

noncomputable def Ns240p1178 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 541836 1000 22 75 134217728 67108864 2251799813685248 Bool.false 125653864910 1797 

noncomputable def Ns240p1179 := Ns240p1178 240485871 42 54794152 8 261175631 42 50729528 8 Bool.false 95035423 56696 Bool.true 11805778 Bool.true 48340728 7074237752028440 1 Bool.false 133698845 Bool.true Bool.false 47302360 Bool.false Bool.false 58331713 

noncomputable def Ns240p1180 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 541836 1000 117 40 134217728 67108864 2251799813685248 Bool.false 125653864910 1797 

noncomputable def Ns240p1181 := Ns240p1180 186065264 42 67108856 8 216015088 42 60023992 8 Bool.false 143653450 33418 Bool.false 170046971 Bool.false 175965123 7074237752028440 1 Bool.false 128069529 Bool.true Bool.false 34472858 Bool.false Bool.false 95035423 

noncomputable def Ns240p1182 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 541836 1000 356 217 134217728 67108864 2251799813685248 Bool.false 125653864910 1797 

noncomputable def Ns240p1183 := Ns240p1182 93032624 42 94906264 8 147453232 42 77490640 16 Bool.false 134217712 1850 Bool.false 190417820 Bool.false 8564529 7074237752028440 1 Bool.false 20332313 Bool.false Bool.false 8558717 Bool.true Bool.false 143653450 

noncomputable def Ns240p1184 := nat_lit 20349984082427614315146764552318204294789533667987 

noncomputable def Ns240p1185 := nat_lit 21736924927243909049957714557306575793632051200 

noncomputable def Ns240p1186 := nat_lit 22417204662748763209451236884480000 

noncomputable def Ns240p1187 := nat_lit 72878719994871013406522360077410631680 

noncomputable abbrev qz488 := (@Eq.refl Real qz696)

noncomputable abbrev qz156 := qz488

noncomputable def Ns240p1188 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz151 541836 1000 1174346003584 16000000 1083672 4000 2000 Ns240p1186 Ns240p1187 qz156 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns240p1189 := nat_lit 1920465441829405629730740040849045204795190704989882286080 

noncomputable abbrev qz701 := (Real.log (Enclosure.sfrac Bool.false 1174346003584 16000000))

noncomputable abbrev qz702 := (@Nat.cast Real Real.instNatCast 1083672)

noncomputable abbrev qz703 := (Enclosure.sfrac Bool.false 541836 2000)

noncomputable abbrev qz157 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 541836 4000) qz701) (@HMul.hMul Real Real Real qz344 qz358 (@HSub.hSub Real Real Real qz350 qz355 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz356 qz702))))) qz703)

noncomputable abbrev qz489 := (@HSub.hSub Real Real Real qz11 qz157 (@HMul.hMul Real Real Real qz5 qz703 (Real.log Real.pi)))

noncomputable def Ns240p1190 := @Enclosure.Real.IsNear.addLit_ft_p qz489 (Enclosure.sfrac Bool.true Ns240p1186 Ns240p1187) 26351534068556340331 28147497671065600 554778819723258743 41472000000000000000000 Ns240p1186 Ns240p1187 0 1 Ns240p1189 

noncomputable def Ns240p1191 := nat_lit 2210526894997642649513492480000 

noncomputable abbrev qz490 := (@HMul.hMul Real Real Real qz5 qz703 (Real.log Real.pi))

noncomputable def Ns240p1192 := @Enclosure.Real.IsNear.subLit_ff_p qz157 qz490 175404296322232487447 140737488355328000 429559550564989 81000000000000000000 5203083274299 16777216000 135459 16777216000 Ns240p1191 26351534068556340331 28147497671065600 

noncomputable abbrev qz158 := (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 541836 4000) qz701) (@HMul.hMul Real Real Real qz344 qz358 (@HSub.hSub Real Real Real qz350 qz355 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz356 qz702)))))

noncomputable def Ns240p1193 := @Enclosure.Real.IsNear.subLit_ff_p qz158 qz703 213532615192481238551 140737488355328000 429559550564989 81000000000000000000 541836 2000 0 1 350808592644464974894000 175404296322232487447 140737488355328000 429559550564989 81000000000000000000 

noncomputable def Ns240p1194 := nat_lit 961665406212306018941135149435191296 

noncomputable def Ns240p1195 := nat_lit 27088722978295055254552576 

noncomputable def Ns240p1196 := nat_lit 366258875740016711294055284100464366468757234647040 

noncomputable def Ns240p1197 := nat_lit 391566874708823860368091051735289586060349145088 

noncomputable def Ns240p1198 := nat_lit 750636274540996813088537527043680691350929408 

noncomputable def Ns240p1199 := BSN.log_dyadic_bound 125770003584 2222922003584 3 2 Ns240p1196 67108864 25920000 Ns240p1197 Ns240p1198 7601981 2348692007168 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 125770003584) (BSN.artanhQ 2222922003584) 0 2 Ns240p1197 Ns240p1196 Ns240p1198 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns240p1200 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 541836 4000) qz701 541836 4000 0 1 3153542403398903 281474976710656 195312581 5062500000000000 427175700422012001477 281474976710656000 979883218877 187500000000000000 (Enclosure.Real.IsNear.const Bool.false 541836 4000) (BSN.isNear_log_sfrac 1174346003584 16000000 3153542403398903 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1174346003584) qz354)) Bool.false Ns240p1195 Ns240p92 1000000414720000 25920000000000000000000 3153542403398903 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1174346003584 16000000 16 2348692007168 2097152000000 7601981 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns240p1199 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p1201 := BSN.arctan_dyadic_bound_f 1000 1083672 1 0 8388608 3240000 0 1 1 0 1 1 7740 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1083672) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1083672) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz704 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1083672)))

noncomputable def Ns240p1202 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz704 884279719003555 562949953421312 1 2000000000000000 7740 8388608 1 3240000 7413518692431492546560 883760296396195 562949953421312 50000000081 162000000000000000 qz16 (Ns240p1201 rfl) rfl rfl 

noncomputable def Ns240p1203 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 541836 4000) qz701) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz11 qz14 qz704)) 427175700422012001477 281474976710656000 979883218877 187500000000000000 883760296396195 2251799813685248 50000000081 648000000000000000 Ns240p1194 213532615192481238551 140737488355328000 429559550564989 81000000000000000000 (Ns240p1200 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 qz704) 1 4 0 1 883760296396195 562949953421312 50000000081 162000000000000000 883760296396195 2251799813685248 50000000081 648000000000000000 qz359 Ns240p1202 rfl) 

noncomputable def Ns240p1204 := @Ns240p1190 Ns240p1184 Ns240p1185 554778819723258743 41472000000000000000000 (@Ns240p1192 554778819723258743 41472000000000000000000 (Ns240p1193 (Ns240p1203 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 541836 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz703 (Real.log Real.pi) 541836 2000 0 1 38410761 33554432 1 33554432 5203083274299 16777216000 135459 16777216000 (Enclosure.Real.IsNear.const Bool.false 541836 2000) RS241to252.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns240p1186 Ns240p1187) 

noncomputable def Ns240p1205 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz151) Bool.false Ns240p1184 Ns240p1185 554778819723258743 41472000000000000000000 15706733113 16777216 113 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz151) (@HAdd.hAdd Real Real Real qz360 qz489 (Enclosure.sfrac Bool.true Ns240p1186 Ns240p1187)) Bool.false Ns240p1184 Ns240p1185 554778819723258743 41472000000000000000000 Ns240p1188 (Ns240p1204 rfl rfl)) 

noncomputable def Ns240p1206 := nat_lit 3797074823646813079207936 

noncomputable def Ns240p1207 := nat_lit 856343966634494617622475343962069303626723595991481885409103359126061695773911559084662376763700537812544473010638172178767127812867921 

noncomputable def Ns240p1208 := nat_lit 609301512962886445504484843511480368176581143764591463105906824504605734818398415683461380387156216920037005671610144903279773521 

noncomputable def Ns240p1209 := nat_lit 4276404176611247092751562858817180633560429733826227110661348752243612072399636982296187822753940222728647062891620906488938848476563281 

noncomputable def Ns240p1210 := BSN.sin_dyadic_bound_f 53959678661 34359738368 4 3 16777216 6486329 Ns240p1207 Ns240p105 Ns240p1208 Ns240p1209 Ns240p108 Ns240p1208 16777214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53959678661) qz361 0 3 Ns240p1207 Ns240p105 Ns240p1208 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53959678661) qz362 0 3 Ns240p1209 Ns240p108 Ns240p1208 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1211 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz151) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15706733113) qz363) Bool.false 15706733113 16777216 113 8388608 Bool.false 16777214 16777216 1 3240000 (Ns240p1205 rfl) (Enclosure.sfrac_false_div 15706733113 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15706733113) qz363) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns240p1206) qz364) 226375608064910080 72057594037927936 Bool.false 16777214 16777216 148 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q3 15706733113 16777216 226375608064910080 72057594037927936 148 Ns240p1206 Ns240p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777214 16777216 Ns240p1206 Ns240p92 53959678661 34359738368 6486329 6480000 (Ns240p1210 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns240p1212 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz151) Bool.false Ns240p1184 Ns240p1185 554778819723258743 41472000000000000000000 125653864910 134217728 1797 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz151) (@HAdd.hAdd Real Real Real qz360 qz489 (Enclosure.sfrac Bool.true Ns240p1186 Ns240p1187)) Bool.false Ns240p1184 Ns240p1185 554778819723258743 41472000000000000000000 Ns240p1188 (Ns240p1204 rfl rfl)) 

noncomputable def Ns240p1213 := Ns240p1183 33418 BSN.abs_quadSignPos (BSN.cos_quad_nat0 356 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 20332313 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 217 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 8558717 134217728) qz156 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 1) Bool.false 8388607 8388608 5851697 424673280000 134217712 134217728 1850 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz151)) Bool.false 8388607 8388608 5851697 424673280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz151) qz151) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz151)) Bool.false 16777214 16777216 374508608 27179089920000 8388607 8388608 5851697 424673280000 (Ns240p1211 rfl rfl) rfl)) rfl) (Ns240p1212 rfl) RS241to252.d7 

noncomputable def Ns240p1214 := nat_lit 2770011193218603538429804147378364535390256040226075031184502381778403224113931029782684692308557824000000 

noncomputable def Ns240p1215 := nat_lit 2272432887403414249812504488348880804624377912683971619191312349551721384586391794814976000000000000 

noncomputable def Ns240p1216 := nat_lit 16777772016761008214101936924115490586833145018772583239612358819274639005009859429376568577283168665600000 

noncomputable def Ns240p1217 := BSN.cos_dyadic_bound_f 190417820 134217728 4 3 134217728 67108864 Ns240p1214 Ns240p130 Ns240p1215 Ns240p1216 Ns240p133 Ns240p1215 20332313 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 190417820) qz367 0 3 Ns240p1214 Ns240p130 Ns240p1215 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 190417820) qz368 0 3 Ns240p1216 Ns240p133 Ns240p1215 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1218 := nat_lit 5380392232041704820140569281 

noncomputable def Ns240p1219 := BSN.sin_dyadic_bound_f 8564529 134217728 2 1 134217728 67108864 Ns240p1218 Ns240p114 Ns240p1218 Ns240p1218 Ns240p115 Ns240p1218 8558717 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 8564529) qz365 0 1 Ns240p1218 Ns240p114 Ns240p1218 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 8564529) qz366 0 1 Ns240p1218 Ns240p115 Ns240p1218 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1220 := nat_lit 821233758969349116162278677764867571637313618980419851470278785107425 

noncomputable def Ns240p1221 := nat_lit 699119157464147313268717779104675367747850571639819685945006228961 

noncomputable def Ns240p1222 := nat_lit 2149718413902877160965437660598959879883277244023206569597295379482081 

noncomputable def Ns240p1223 := BSN.sin_dyadic_bound_f 170046971 134217728 3 2 134217728 67108864 Ns240p1220 Ns240p248 Ns240p1221 Ns240p1222 Ns240p251 Ns240p1221 128069529 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 170046971) qz365 0 2 Ns240p1220 Ns240p248 Ns240p1221 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 170046971) qz366 0 2 Ns240p1222 Ns240p251 Ns240p1221 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1224 := nat_lit 2018712294002668897787580971495414067458716099572361955145317724430944903842969584759353751695386661378801 

noncomputable def Ns240p1225 := nat_lit 881290663183225091796355068287038729044299527908041668810589033767819944240769290455627185883732721 

noncomputable def Ns240p1226 := nat_lit 12232517431108335398180427103570882846792009077435161851747583332251142943650685872855407819502146153634545 

noncomputable def Ns240p1227 := BSN.cos_dyadic_bound_f 175965123 134217728 4 3 134217728 67108864 Ns240p1224 Ns240p130 Ns240p1225 Ns240p1226 Ns240p133 Ns240p1225 34472858 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 175965123) qz367 0 3 Ns240p1224 Ns240p130 Ns240p1225 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 175965123) qz368 0 3 Ns240p1226 Ns240p133 Ns240p1225 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1228 := Ns240p1181 56696 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 117 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 128069529 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 34472858 134217728) qz156 rfl rfl (Ns240p1213 RS241to252.d9 RS241to252.d11 RS241to252.d13 RS241to252.d17 (Ns240p1217 rfl rfl) (Ns240p1219 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns240p1212 rfl) RS241to252.d19 RS241to252.d21 RS241to252.d23 RS241to252.d25 RS241to252.d17 (Ns240p1223 rfl rfl) (Ns240p1227 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns240p1229 := nat_lit 19425779256091667606122160656 

noncomputable def Ns240p1230 := BSN.cos_dyadic_bound_f 11805778 134217728 2 1 134217728 67108864 Ns240p1229 Ns240p146 Ns240p1229 Ns240p1229 Ns240p147 Ns240p1229 133698845 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 11805778) qz367 0 1 Ns240p1229 Ns240p146 Ns240p1229 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 11805778) qz368 0 1 Ns240p1229 Ns240p147 Ns240p1229 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1231 := nat_lit 5460755677487823131513425760256 

noncomputable def Ns240p1232 := BSN.sin_dyadic_bound_f 48340728 134217728 2 1 134217728 67108864 Ns240p1231 Ns240p114 Ns240p1231 Ns240p1231 Ns240p115 Ns240p1231 47302360 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 48340728) qz365 0 1 Ns240p1231 Ns240p114 Ns240p1231 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 48340728) qz366 0 1 Ns240p1231 Ns240p115 Ns240p1231 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1233 := Ns240p1179 76021 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 22 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133698845 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 75 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 47302360 134217728) qz156 rfl rfl (Ns240p1228 rfl rfl) (Ns240p1212 rfl) RS241to252.d27 RS241to252.d29 RS241to252.d31 RS241to252.d33 RS241to252.d17 (Ns240p1230 rfl rfl) (Ns240p1232 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p1234 := nat_lit 13992339344889092991251618435521 

noncomputable def Ns240p1235 := BSN.sin_dyadic_bound_f 61160719 134217728 2 1 134217728 67108864 Ns240p1234 Ns240p114 Ns240p1234 Ns240p1234 Ns240p115 Ns240p1234 59065947 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 61160719) qz365 0 1 Ns240p1234 Ns240p114 Ns240p1234 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 61160719) qz366 0 1 Ns240p1234 Ns240p115 Ns240p1234 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1236 := nat_lit 7697535083606287339659458149289652711478145352835684511985602099719367426606012361358442478633522342400000 

noncomputable def Ns240p1237 := nat_lit 2782621287051604801922012134489191911594820101198980488836184089394872240257477067991601000000000000 

noncomputable def Ns240p1238 := nat_lit 38453612039947756563956989491315315998606551002763181467767149553457752096733385031848931952676187712000000 

noncomputable def Ns240p1239 := BSN.sin_dyadic_bound_f 193659070 134217728 4 3 134217728 67108864 Ns240p1236 Ns240p118 Ns240p1237 Ns240p1238 Ns240p121 Ns240p1237 133121021 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 193659070) qz365 0 3 Ns240p1236 Ns240p118 Ns240p1237 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 193659070) qz366 0 3 Ns240p1238 Ns240p121 Ns240p1237 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1240 := Ns240p1177 92906 BSN.abs_quadSignNeg qz642 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 59065947 134217728) BSN.abs_quadSignNeg qz662 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133121021 134217728) qz156 rfl rfl (Ns240p1233 rfl) (Ns240p1212 rfl) RS241to252.d35 RS241to252.d37 RS241to252.d39 RS241to252.d41 RS241to252.d17 (Ns240p1235 rfl rfl) (Ns240p1239 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p1241 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 9) 6924922 134217728 92906 134217728 6924922 134217728 92906 134217728 1858894594834432 3462461 33554432 46453 33554432 (Ns240p1240 rfl) 

noncomputable def Ns240p1242 := nat_lit 5705819218674607515139260583642508038052726362676248157135014044019625630312292146549092196892839246100154728493903342094956282414716858965455 

noncomputable def Ns240p1243 := nat_lit 12194330274671844653834364178879555881830461494785043558043581873536608354764709453594945715091765512343073949692994620685343654997219864477696 

noncomputable def Ns240p1244 := nat_lit 5607728589753989836134409531641291225141197871359190383168377134831636040337472690803914950831866487680382689936250613152580002753525707886435156779577482352926231768132519578514006619659 

noncomputable def Ns240p1245 := @Enclosure.Real.IsNear.mulLit_tf qz486 qz487 2752757 8388608 1 8388608 Ns240p1242 Ns240p1243 Ns240p1244 

noncomputable def Ns240p1246 := nat_lit 53961560848874266471772900846015059073655891935112280390326227006887754972223980227074720642860963434704187593183811362903876540825600000000000000000000000000000000000000000000000000000000000 

noncomputable abbrev qz491 := (@HPow.hPow Real Real Real qz618 qz152 qz8)

noncomputable def Ns240p1247 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz491 1 1 0 1 2752757 8388608 1 8388608 2752757 8388608 1 8388608 

noncomputable def Ns240p1248 := @Enclosure.Real.IsNear.sqrt_image qz152 361699506243 4194304000 135459 4194304000 77899348 77899378 8388608 (@Enclosure.Real.IsNear.of_eq qz152 (@HMul.hMul Real Real Real qz5 qz151 qz3) Bool.false 361699506243 4194304000 135459 4194304000 (BSN.t_div_two_pi_mk qz151 541836 1000 qz156) (@Enclosure.Real.IsNear.mulLit_ff qz151 qz3 541836 1000 0 1 2670177 16777216 1 16777216 361699506243 4194304000 135459 4194304000 (Enclosure.Real.IsNear.const Bool.false 541836 1000) RS241to252.d44 rfl)) 

noncomputable abbrev qz492 := (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 155798726 16777216 30 16777216 77899363 8388608 15 8388608 (Ns240p1248 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns240p1249 := @Enclosure.Real.IsNear.sqrt_image qz155 77899363 8388608 15 8388608 25563002 25563008 8388608 qz492 rfl 

noncomputable def Ns240p1250 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz155) 25563005 8388608 3 8388608 2752756 2752758 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz155) Bool.false 51126010 16777216 6 16777216 25563005 8388608 3 8388608 (Ns240p1249 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns240p1251 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz155)) Bool.false 5505514 16777216 2 16777216 2752757 8388608 1 8388608 (Ns240p1250 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns240p1252 := nat_lit 12888790188718510619391700130727145053520756924757091718533661014979789565239609529564568187751458006072578099365013040246840759800392359375 

noncomputable def Ns240p1253 := nat_lit 23529109103901746912188566535242210574946556480092626850563508409742707827577579261906307200336123229031383689046131213709060975605707886435156779577482352926231768132519578514006619659 

noncomputable abbrev qz493 := (@HMul.hMul Real Real Real qz5 qz700 (@Inv.inv Real Real.instInv qz155))

noncomputable def Ns240p1254 := @Enclosure.Real.IsNear.addLit_ff qz153 qz493 8212922643555 17592186044416 368655958279093 3562417673994240000 Ns240p1252 Ns240p1243 Ns240p1253 Ns240p1246 

noncomputable def Ns240p1255 := nat_lit 100377833230728035299979055482332956994984276997453909487104632322314225517996773524381656040011929102686044567228719880941311424597806359988115942439649280 

noncomputable abbrev qz849 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 541836 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1)))

noncomputable abbrev qz705 := (Real.cos qz849)

noncomputable abbrev qz494 := qz705

noncomputable abbrev qz159 := (@Inv.inv Real Real.instInv qz494)

noncomputable abbrev qz706 := (@HSub.hSub Real Real Real qz814 (@HMul.hMul Real Real Real qz811 qz847 qz847) qz847)

noncomputable abbrev qz495 := (@HMul.hMul Real Real Real qz615 qz613 (@HSub.hSub Real Real Real qz619 qz706 qz626))

noncomputable abbrev qz160 := (Real.cos qz495)

noncomputable def Ns240p1256 := @Enclosure.Real.IsNear.of_eq qz153 (@HMul.hMul Real Real Real qz5 qz159 qz160) Bool.false 8212922643555 

noncomputable def Ns240p1257 := @Enclosure.Real.IsNear.mulLit_tt qz159 qz160 74144595 16777216 3793 

noncomputable abbrev qz161 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz494))

noncomputable abbrev qz162 := qz494

noncomputable def Ns240p1258 := @Enclosure.Real.IsNear.of_eq qz159 (@Neg.neg Real Real.instNeg qz161) Bool.true 74144595 16777216 3793 16777216 (BSN.inv_eq_neg_inv_neg qz162) 

noncomputable def Ns240p1259 := @Enclosure.Real.IsNear.recentre' qz161 Bool.false 74144595 16777216 3793 16777216 74144595 16777216 

noncomputable def Ns240p1260 := @Enclosure.Real.IsNear.recentre' qz162 Bool.true 1898149 8388608 629137216 54358179840000 1898149 8388608 9830269 849346560000 

noncomputable abbrev qz707 := qz849

noncomputable abbrev qz496 := qz707

noncomputable abbrev qz163 := qz496

noncomputable def Ns240p1261 := @Enclosure.Real.IsNear.cos_image qz163 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7545763) qz418) Bool.false 7545763 4194304 189 16777216 Bool.true 1898149 8388608 1 

noncomputable def Ns240p1262 := nat_lit 404791131156292768414647977 

noncomputable def Ns240p1263 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz154 884279719003555 140737488355328 1 500000000000000 2401891 8388608 15 8388608 2123943498557167722505 1180591620717411303424 Ns240p1262 

noncomputable def Ns240p1264 := @Enclosure.Real.IsNear.subLit_ff_p qz155 qz1 77899363 8388608 15 8388608 9 1 0 1 2401891 2401891 8388608 15 

noncomputable def Ns240p1265 := @Ns240p1264 8388608 qz492 qz373 

noncomputable def Ns240p1266 := @Enclosure.Real.IsNear.recentre' qz163 Bool.false 2123943498557167722505 1180591620717411303424 Ns240p1262 Ns240p165 7545763 4194304 189 16777216 (@Ns240p1263 Ns240p165 RS241to252.d43 (Ns240p1265 rfl rfl) rfl) 

noncomputable def Ns240p1267 := nat_lit 6236193225347217157244582647593879637459069935730626944043277772054491654208738768603761 

noncomputable def Ns240p1268 := nat_lit 34075161844369116744772203221531917259778895423760902129667523155603037825186810481 

noncomputable def Ns240p1269 := nat_lit 37676439671050756890822804573534416795750640440034759952143341240795123737578086129879665 

noncomputable def Ns240p1270 := BSN.cos_dyadic_bound_t 7545763 4194304 4 3 8388608 3240000 Ns240p1267 Ns240p538 Ns240p1268 Ns240p1269 Ns240p541 Ns240p1268 1898149 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 7545763) (BSN.cosEvenQ 4194304) 0 3 Ns240p1267 Ns240p538 Ns240p1268 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 7545763) (BSN.cosOddQ 4194304) 0 3 Ns240p1269 Ns240p541 Ns240p1268 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz164 := (@Neg.neg Real Real.instNeg qz494)

noncomputable def Ns240p1271 := @Enclosure.Real.IsNear.inv_image qz164 1898149 8388608 9830269 849346560000 37070401 37074194 8388608 (@Enclosure.Real.IsNear.neg qz162 Bool.true 1898149 8388608 9830269 849346560000 (Ns240p1260 (@Ns240p1261 3240000 (Ns240p1266 rfl) (Enclosure.sfrac_false_div 7545763 4194304) (Ns240p1270 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns240p1272 := Ns240p1258 (@Enclosure.Real.IsNear.neg qz161 Bool.false 74144595 16777216 3793 16777216 (@Ns240p1259 3793 16777216 (Ns240p1271 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p1273 := @Enclosure.Real.IsNear.recentre' qz160 Bool.true 886152 8388608 

noncomputable abbrev qz165 := qz495

noncomputable def Ns240p1274 := @Enclosure.Real.IsNear.cos_image qz165 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 28129205)) qz363) Bool.true 28129205 16777216 

noncomputable def Ns240p1275 := nat_lit 16604551982855282031294940805 

noncomputable def Ns240p1276 := nat_lit 5340168542511043052624476706895517 

noncomputable def Ns240p1277 := @Enclosure.Real.IsNear.recentre' qz165 Bool.true Ns240p1275 Ns240p180 Ns240p1276 

noncomputable abbrev qz497 := (@HSub.hSub Real Real Real qz619 qz706 qz626)

noncomputable abbrev qz166 := qz497

noncomputable def Ns240p1278 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz166 884279719003555 140737488355328 1 500000000000000 18777488192951 

noncomputable abbrev qz498 := qz706

noncomputable abbrev qz167 := qz498

noncomputable def Ns240p1279 := @Enclosure.Real.IsNear.subLit_tf qz167 qz27 14379441681847 70368744177664 197886075 70368744177664 1 16 

noncomputable abbrev qz708 := (@HMul.hMul Real Real Real qz811 qz847 qz847)

noncomputable abbrev qz499 := qz708

noncomputable abbrev qz168 := qz499

noncomputable def Ns240p1280 := @Enclosure.Real.IsNear.subLit_ff_n qz168 qz154 5769080375881 70368744177664 72056955 70368744177664 2401891 8388608 15 8388608 

noncomputable def Ns240p1281 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz154 2401891 8388608 15 8388608 2401891 8388608 15 8388608 5769080375881 70368744177664 

noncomputable def Ns240p1282 := nat_lit 78805056134338190940385464585475005135438816604131251160326594700113427863285556901194913140625 

noncomputable def Ns240p1283 := nat_lit 245408441496050151411821911828002494653934520116591965467470229779005365680410078369140625 

noncomputable def Ns240p1284 := nat_lit 476590606664791974678598514621448905262394867206448796760164840175355406892386686000940602740625 

noncomputable def Ns240p1285 := BSN.cos_dyadic_bound_t 28129205 16777216 4 3 8388608 3240000 Ns240p1282 Ns240p303 Ns240p1283 Ns240p1284 Ns240p306 Ns240p1283 886152 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 28129205) qz627 0 3 Ns240p1282 Ns240p303 Ns240p1283 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 28129205) (BSN.cosOddQ 16777216) 0 3 Ns240p1284 Ns240p306 Ns240p1283 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1286 := @Ns240p1273 979057216 54358179840000 110769 1048576 15297769 849346560000 (@Ns240p1274 297 16777216 Bool.true 886152 8388608 1 3240000 (@Ns240p1277 Ns240p183 28129205 16777216 297 16777216 (@Ns240p1278 70368744177664 197886075 70368744177664 Ns240p1275 Ns240p180 Ns240p1276 Ns240p183 RS241to252.d43 (@Ns240p1279 0 1 300439811087216 18777488192951 70368744177664 197886075 70368744177664 (@Ns240p1280 120623499527875198976 14379441681847 70368744177664 197886075 70368744177664 (@Ns240p1281 72056955 70368744177664 (Ns240p1265 rfl rfl) (Ns240p1265 rfl rfl) rfl) (Ns240p1265 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 28129205 16777216) (BSN.cos_neg_of_bound 28129205 16777216 Bool.true 886152 8388608 1 3240000 (Ns240p1285 rfl rfl)) rfl rfl) 

noncomputable def Ns240p1287 := nat_lit 14268101864014673080784188408350827941448527529567955549455028029632381519069585421883464593466453535835313711134053086136768286859375 

noncomputable def Ns240p1288 := nat_lit 1453677448591213781098647615776009068707282721374636120562980398361278576226795846652382101427527131121525043212532355867069203257229312 

noncomputable def Ns240p1289 := nat_lit 2337946679612968938281571523879756179020643670503308748750968858618393968872519815628414320887178016403501498705329268493140641428351940297531389901870632419319223797137212032116207 

noncomputable def Ns240p1290 := nat_lit 578944739866099832351155409352940954760197433729184297934694341495024913251418855242338759643731917038366423056905629952114688000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns240p1291 := @Enclosure.Real.IsNear.mulLit_ff qz700 (@Inv.inv Real Real.instInv qz155) Ns240p1287 Ns240p1288 Ns240p1289 Ns240p1290 903329 8388608 1 8388608 Ns240p1252 

noncomputable def Ns240p1292 := nat_lit 196723993451110432431136007299290847901362063052015787462820706451007458307469401756148461158869684725514200227803504551109375 

noncomputable def Ns240p1293 := nat_lit 21153791001287955166461289857048673274508949854856999017108761448780985319561963066406054734070889115122918784800747465736192 

noncomputable def Ns240p1294 := nat_lit 322337752038791992961101641478118295690215944142347179144036176778231824493813943655318602311547330828011628704706087869376265205176519081043056558451903754167935600146804019 

noncomputable def Ns240p1295 := nat_lit 84247547764403837551239908404086738993675307389521083377577355931138287014825452241688437009540490840789632501678080000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns240p1296 := @Enclosure.Real.IsNear.mulLit_tf (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz154) qz462 Ns240p1292 Ns240p1293 Ns240p1294 Ns240p1295 72528529 68719476736 1 68719476736 Ns240p1287 

noncomputable abbrev qz850 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 541836 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1)))

noncomputable abbrev qz709 := (@HMul.hMul Real Real Real qz811 qz809 (@HSub.hSub Real Real Real qz814 qz850 qz844))

noncomputable abbrev qz500 := (@HMul.hMul Real Real Real qz615 qz709 qz709)

noncomputable abbrev qz501 := qz709

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz344 qz500 qz501)

noncomputable abbrev qz170 := (Real.sin qz495)

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz344 qz320 qz501)

noncomputable def Ns240p1297 := @HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 qz169 qz170) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz171 qz129) qz160) 

noncomputable abbrev qz710 := (Real.sin qz849)

noncomputable abbrev qz502 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz615 qz613 qz710))

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz344 qz320 qz502)

noncomputable abbrev qz503 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz615 qz688 qz705))

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz344 qz320 qz503)

noncomputable abbrev qz504 := qz710

noncomputable abbrev qz174 := qz504

noncomputable def Ns240p1298 := @HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns240p1297 (@HMul.hMul Real Real Real qz5 qz172 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz154))) (@HMul.hMul Real Real Real qz5 qz173 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz154))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz470 qz174) qz153) 

noncomputable abbrev qz711 := (BSN.cos_two_pi_p_ne_zero_mk qz151 541836 1000 9 qz156 rfl rfl (@BSN.floor_sqrt_eq_dec qz151 541836 1000 9 qz156 rfl rfl rfl))

noncomputable abbrev qz505 := qz711

noncomputable def Ns240p1299 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz154) (@HMul.hMul Real Real Real qz5 qz159 Ns240p1298) Bool.true Ns240p1292 Ns240p1293 Ns240p1294 Ns240p1295 (BSN.iteratedDeriv_three_correction_mk qz154 qz505) 

noncomputable def Ns240p1300 := nat_lit 1295521994810041820103123323723352349009801788444418145581361085301692261134284849448201730923710504969907120684375 

noncomputable def Ns240p1301 := nat_lit 615656346818663737691860001564743965704370926101022604186692084441339402679643915803347910232576806887603562348544 

noncomputable def Ns240p1302 := nat_lit 4245368902749467450342452644219568979210838637717484113529146987604289755815078714092289513991996306257191119509598430779633340990024168344138952681961385318333939 

noncomputable def Ns240p1303 := @Enclosure.Real.IsNear.mulLit_tf qz159 Ns240p1298 151849211545 34359738368 1897 34359738368 Ns240p1300 Ns240p1301 Ns240p1302 

noncomputable def Ns240p1304 := nat_lit 4903852693061567700423760595969316723854007862364005028361999192923440540606706184433332935996615027589120000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns240p1305 := @Enclosure.Real.IsNear.of_eq qz159 (@Neg.neg Real Real.instNeg qz161) Bool.true 151849211545 34359738368 1897 34359738368 (BSN.inv_eq_neg_inv_neg qz162) 

noncomputable def Ns240p1306 := @Enclosure.Real.IsNear.recentre' qz161 Bool.false 303698423090 68719476736 3794 68719476736 151849211545 34359738368 

noncomputable def Ns240p1307 := @Enclosure.Real.IsNear.recentre' qz162 Bool.true 7774762929 34359738368 2576946036736 911978924542525440000 7774762929 34359738368 9830269 3478923509760000 

noncomputable def Ns240p1308 := @Enclosure.Real.IsNear.cos_image qz163 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 123629671977) qz695) Bool.false 123629671977 68719476736 189 68719476736 Bool.true 7774762929 34359738368 1 

noncomputable def Ns240p1309 := nat_lit 404791215644611476341999273 

noncomputable def Ns240p1310 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz154 884279719003555 140737488355328 1 500000000000000 76860443 268435456 15 34359738368 67966130938528755874865 37778931862957161709568 Ns240p1309 

noncomputable def Ns240p1311 := @Enclosure.Real.IsNear.subLit_ff_p qz155 qz1 2492779547 268435456 15 34359738368 9 1 0 1 76860443 76860443 268435456 15 

noncomputable def Ns240p1312 := @Enclosure.Real.IsNear.sqrt_image qz152 1481521098598731 17179869184000 135459 17179869184000 319075782001 319075782031 34359738368 (@Enclosure.Real.IsNear.of_eq qz152 (@HMul.hMul Real Real Real qz5 qz151 qz3) Bool.false 1481521098598731 17179869184000 135459 17179869184000 (BSN.t_div_two_pi_mk qz151 541836 1000 qz156) (@Enclosure.Real.IsNear.mulLit_ff qz151 qz3 541836 1000 0 1 10937044409 68719476736 1 68719476736 1481521098598731 17179869184000 135459 17179869184000 (Enclosure.Real.IsNear.const Bool.false 541836 1000) RS241to252.d57 rfl)) 

noncomputable def Ns240p1313 := @Ns240p1311 34359738368 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 638151564032 68719476736 30 68719476736 2492779547 268435456 15 34359738368 (Ns240p1312 rfl rfl rfl rfl rfl rfl) rfl) qz373 

noncomputable def Ns240p1314 := @Enclosure.Real.IsNear.recentre' qz163 Bool.false 67966130938528755874865 37778931862957161709568 Ns240p1309 Ns240p951 123629671977 68719476736 189 68719476736 (@Ns240p1310 Ns240p951 RS241to252.d56 (Ns240p1313 rfl rfl) rfl) 

noncomputable def Ns240p1315 := nat_lit 2272789944249969618628163171217086441795306654573515639480299683681514370880955468941143507732574936864303250742664063393487412848504413816444229870317390361828379970202520044063888371841 

noncomputable def Ns240p1316 := nat_lit 2978265914392503966322491384990242727176266458827333579894615020321060766236728491127029580793805876747362551020600043046909782883517181536882854834865653561672181615378104184961 

noncomputable def Ns240p1317 := nat_lit 23086581837770345358617659652991800140999217565013276837286901425412353200543839109535236780474880977475296461864439409767635759346093318960526257700693507030042607689376017166208558559361 

noncomputable def Ns240p1318 := BSN.cos_dyadic_bound_t 123629671977 68719476736 5 4 34359738368 13271040000 Ns240p1315 Ns240p1047 Ns240p1316 Ns240p1317 Ns240p1050 Ns240p1316 7774762929 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 123629671977) (BSN.cosEvenQ 68719476736) 0 4 Ns240p1315 Ns240p1047 Ns240p1316 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 123629671977) (BSN.cosOddQ 68719476736) 0 4 Ns240p1317 Ns240p1050 Ns240p1316 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz506 := (Ns240p1307 (@Ns240p1308 13271040000 (Ns240p1314 rfl) (Enclosure.sfrac_false_div 123629671977 68719476736) (Ns240p1318 rfl rfl) rfl rfl) rfl)

noncomputable def Ns240p1319 := @Enclosure.Real.IsNear.inv_image qz164 7774762929 34359738368 9830269 3478923509760000 151849209648 151849213442 34359738368 (@Enclosure.Real.IsNear.neg qz162 Bool.true 7774762929 34359738368 9830269 3478923509760000 qz506) 

noncomputable def Ns240p1320 := Ns240p1305 (@Enclosure.Real.IsNear.neg qz161 Bool.false 151849211545 34359738368 1897 34359738368 (@Ns240p1306 1897 34359738368 (Ns240p1319 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p1321 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns240p1297 (@HMul.hMul Real Real Real qz5 qz172 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz154))) (@HMul.hMul Real Real Real qz5 qz173 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz154))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz470 qz174) qz153) 

noncomputable def Ns240p1322 := nat_lit 70740865151328959071970252940812265456562371667058942032938886156422924350856647895775892908728626518947275123244375 

noncomputable def Ns240p1323 := nat_lit 4213752212927494798857682864536343423476890378510056212372015985665702961056882425424521702384520449490084420727900890955098024591269725729744073147109698918333939 

noncomputable def Ns240p1324 := nat_lit 398596721540054643856909327815622588615159127708192680418546563991801058125 

noncomputable def Ns240p1325 := nat_lit 3533694129556768659166595001485837031654967793751237916243212402585239552 

noncomputable def Ns240p1326 := nat_lit 53105338759472689127223929893311652254023312224964385184052921778984339627899387570459607771916831982904771539 

noncomputable def Ns240p1327 := nat_lit 4577978467771919293914100496167225302787724277402916310180160359988555262030784182842261898067572335728292156132694340623106124560736159300808465771121750268646299407332944409683558400000 

noncomputable def Ns240p1328 := nat_lit 57093706716460944533923233090590815718978791435489895713194278738351161477654839309196319539339042364550606400044375 

noncomputable def Ns240p1329 := @Enclosure.Real.IsNear.subLit_ft (@HSub.hSub Real Real Real qz11 Ns240p1297 (@HMul.hMul Real Real Real qz5 qz172 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 2 Zeta.RiemannSiegel.correction qz154))) (@HMul.hMul Real Real Real qz5 qz173 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz154)) Ns240p1328 Ns240p1301 

noncomputable def Ns240p1330 := nat_lit 4106138248170455370746055210870695784878950403423973692398411334959255594139340021275986226381911217445100887774922174715280290890497847262358399681161298401213939 

noncomputable def Ns240p1331 := nat_lit 92476742645861111420054914856194481424515631758723524490262099401962538966917173873180759009375 

noncomputable def Ns240p1332 := nat_lit 4171849679533027504677776769862406473833407270227837441302815640277772901915313574263597826048 

noncomputable def Ns240p1333 := nat_lit 3601089332696316583300276576257331620065702596596430526023572768702463670524822807931207156327634925213731758641050577515466966366997261 

noncomputable def Ns240p1334 := nat_lit 164097769856982816565594634250672294499865743788513831983182341073998297410605940736000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns240p1335 := nat_lit 295120255611460831158163210045266733938527746949275730464270154437365194115231239228356357575609778036793833631907248225478035527242154690573578596026278012486864103403989357169456920279397960666818522644480000 

noncomputable def Ns240p1336 := nat_lit 990859569000176153502771354814035212898101692354785952761627481973850703699125 

noncomputable def Ns240p1337 := nat_lit 115792089237316195423570985008687907853269984665640564039457584007913129639936 

noncomputable def Ns240p1338 := nat_lit 139105081114493375636661478429365394884024396690277615687848040203858393274622334697585783906840422740662472957 

noncomputable def Ns240p1339 := nat_lit 207052390403716913623042675868310763573533269165111596654875726713978880000000000000000000000000000000000000000000000 

noncomputable def Ns240p1340 := @Enclosure.Real.IsNear.subLit_ft Ns240p1297 (@HMul.hMul Real Real Real qz5 qz172 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 2 Zeta.RiemannSiegel.correction qz154)) Ns240p1336 Ns240p1337 Ns240p1338 Ns240p1339 

noncomputable def Ns240p1341 := nat_lit 51825393600435305707146575879423512875751722209365041871438162774177419575643372756828756291718465926797275081260375 

noncomputable def Ns240p1342 := nat_lit 4102843667386762035084807715069099082119961921580233492284108027013932813117155938136794486754654058840835815033223237355545319096629989240365509313161298401213939 

noncomputable def Ns240p1343 := nat_lit 6610999583001604715075795339778649748690157959653159093397661363082673579520562266231077772542225022344173053325065373556419252532375193348961745795425885796227932001811920362833602318172160000 

noncomputable def Ns240p1344 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 qz169 qz170) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz171 qz129) qz160) 

noncomputable def Ns240p1345 := nat_lit 2229039717460567697887938454353772826405068605825768465385062215035733477203125 

noncomputable def Ns240p1346 := nat_lit 14038094385246399972069491447700193293558005433944503286481803899925143419807716365737854762859127580220824319 

noncomputable def Ns240p1347 := nat_lit 69017463467905637874347558622770254524511089721703865551625242237992960000000000000000000000000000000000000000000000 

noncomputable def Ns240p1348 := nat_lit 30523497273160976887319494657427192465521937625 

noncomputable def Ns240p1349 := nat_lit 2854495385411919762116571938898990272765493248 

noncomputable def Ns240p1350 := nat_lit 956403108448138538706925522873931273860876229022042913475657314663 

noncomputable def Ns240p1351 := nat_lit 2041694201525630780780247644590609268736000000000000000000000000000000000 

noncomputable def Ns240p1352 := nat_lit 2828404067302246532314193977270766462023509678516784507890309659263716141385510682427069439967740702102342216153728811008000 

noncomputable def Ns240p1353 := nat_lit 130477236953309666788999966930596344646639946159722945922892702859375 

noncomputable def Ns240p1354 := nat_lit 6739986666787659948666753771754907668409286105635143120275902562304 

noncomputable def Ns240p1355 := @Enclosure.Real.IsNear.mulLit_tt qz169 qz170 Ns240p1353 Ns240p1354 

noncomputable def Ns240p1356 := nat_lit 381345713575332595138013561471962225988374832076526317561465515685093541206306702989999815651437 

noncomputable def Ns240p1357 := nat_lit 3213876088517980551083924184682325205044405987565585670602752000000000000000000000000000000000000000000 

noncomputable def Ns240p1358 := nat_lit 2572506619036323729925483493195931128955830625 

noncomputable def Ns240p1359 := nat_lit 356811923176489970264571492362373784095686656 

noncomputable def Ns240p1360 := nat_lit 6415925743574087751349871911621288205940564040093508473420089 

noncomputable def Ns240p1361 := nat_lit 217780714829400616616559748756331655331840000000000000000000000000000 

noncomputable abbrev qz175 := qz500

noncomputable abbrev qz176 := qz501

noncomputable def Ns240p1362 := @Enclosure.Real.IsNear.mulLit_ft qz175 qz176 Ns240p1358 Ns240p1359 Ns240p1360 Ns240p1361 

noncomputable def Ns240p1363 := nat_lit 80958238840132495397896533 

noncomputable def Ns240p1364 := nat_lit 14757395258967641292800000000000000 

noncomputable def Ns240p1365 := @Enclosure.Real.IsNear.mulLit_tt qz176 qz176 50719883862606820148175 18889465931478580854784 Ns240p1363 Ns240p1364 50719883862606820148175 18889465931478580854784 

noncomputable abbrev qz712 := (@HSub.hSub Real Real Real qz814 qz850 qz844)

noncomputable abbrev qz507 := qz712

noncomputable abbrev qz177 := qz507

noncomputable def Ns240p1366 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz177 884279719003555 140737488355328 1 500000000000000 57357285 134217728 15 17179869184 

noncomputable abbrev qz713 := qz850

noncomputable abbrev qz508 := qz713

noncomputable abbrev qz178 := qz508

noncomputable def Ns240p1367 := @Enclosure.Real.IsNear.subLit_ff_n qz178 qz142 76860443 134217728 15 17179869184 1 1 0 1 57357285 

noncomputable def Ns240p1368 := @Enclosure.Real.IsNear.mulLit_ff qz0 qz154 2 1 0 1 76860443 268435456 15 34359738368 76860443 134217728 15 

noncomputable def Ns240p1369 := @Enclosure.Real.IsNear.recentre' qz170 Bool.true 34167488054 34359738368 

noncomputable def Ns240p1370 := @Enclosure.Real.IsNear.sin_image qz165 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 115217177101)) qz695) Bool.true 115217177101 68719476736 

noncomputable def Ns240p1371 := nat_lit 17003054231104045816047014861525 

noncomputable def Ns240p1372 := nat_lit 10141204801825835211973625643008 

noncomputable def Ns240p1373 := nat_lit 4374660208211783272716495203209825019 

noncomputable def Ns240p1374 := @Enclosure.Real.IsNear.recentre' qz165 Bool.true Ns240p1371 Ns240p1372 Ns240p1373 

noncomputable def Ns240p1375 := nat_lit 1014120480182583521197362564300800000000000000 

noncomputable def Ns240p1376 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz166 884279719003555 140737488355328 1 500000000000000 19228139994281255 

noncomputable def Ns240p1377 := @Enclosure.Real.IsNear.subLit_tf qz167 qz27 14724540366910759 72057594037927936 810540176865 1180591620717411303424 1 16 

noncomputable def Ns240p1378 := @Enclosure.Real.IsNear.subLit_ff_n qz168 qz154 5907527698156249 72057594037927936 295144101345 1180591620717411303424 76860443 268435456 15 34359738368 

noncomputable def Ns240p1379 := nat_lit 3952588707782096903471104 

noncomputable def Ns240p1380 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz154 76860443 268435456 15 34359738368 76860443 268435456 15 34359738368 5907527698156249 72057594037927936 

noncomputable def Ns240p1381 := nat_lit 4559746201152729982156990875763649237701357074306486543887419993443085215039847321496301014619030968124351390572642297917577044923334330801 

noncomputable def Ns240p1382 := nat_lit 5472764573531947921356428047436920402277074630153932699142459869139060478392891167455605513008103159396345659297702136043376977185201 

noncomputable def Ns240p1383 := nat_lit 22761975747936436941993577103847485512135441858332775970515817316027005984387871140816114207563609749945807273752937928929352308749592496561 

noncomputable def Ns240p1384 := BSN.sin_dyadic_bound_f 115217177101 68719476736 4 3 34359738368 13271040000 Ns240p1381 Ns240p1029 Ns240p1382 Ns240p1383 Ns240p1032 Ns240p1382 34167488054 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 115217177101) (BSN.sinEvenQ 68719476736) 0 3 Ns240p1381 Ns240p1029 Ns240p1382 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 115217177101) (BSN.sinOddQ 68719476736) 0 3 Ns240p1383 Ns240p1032 Ns240p1382 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1385 := @Ns240p1369 2011744698368 455989462271262720000 17083744027 17179869184 7674197 1739461754880000 (@Ns240p1370 149 34359738368 Bool.true 34167488054 34359738368 1 13271040000 (@Ns240p1374 Ns240p1375 115217177101 68719476736 149 34359738368 (@Ns240p1376 72057594037927936 810540176865 1180591620717411303424 Ns240p1371 Ns240p1372 Ns240p1373 Ns240p1375 RS241to252.d56 (@Ns240p1377 0 1 307650239908500080 19228139994281255 72057594037927936 810540176865 1180591620717411303424 (@Ns240p1378 Ns240p1379 14724540366910759 72057594037927936 810540176865 1180591620717411303424 (@Ns240p1380 295144101345 1180591620717411303424 (Ns240p1313 rfl rfl) (Ns240p1313 rfl rfl) rfl) (Ns240p1313 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 115217177101 68719476736) (BSN.sin_neg_of_bound 115217177101 68719476736 Bool.false 34167488054 34359738368 1 13271040000 (Ns240p1384 rfl rfl)) rfl rfl) 

noncomputable def Ns240p1386 := nat_lit 134551693949756708145729883825355286375 

noncomputable def Ns240p1387 := nat_lit 1329227995784915872903807060280344576 

noncomputable def Ns240p1388 := nat_lit 6554236436095778645957852273740307229566411695474233 

noncomputable def Ns240p1389 := @Enclosure.Real.IsNear.mulLit_tt (@HMul.hMul Real Real Real qz5 qz171 qz129) qz160 Ns240p1386 Ns240p1387 Ns240p1388 

noncomputable def Ns240p1390 := nat_lit 31691265005705735037417580134400000000000000000000000000000 

noncomputable def Ns240p1391 := nat_lit 242874716520397486193689599 

noncomputable def Ns240p1392 := @Enclosure.Real.IsNear.mulLit_tf qz171 qz129 152159651587820460444525 18889465931478580854784 Ns240p1391 Ns240p1364 884279719003555 

noncomputable def Ns240p1393 := @Enclosure.Real.IsNear.mulLit_ft qz320 qz176 3 1 0 1 50719883862606820148175 18889465931478580854784 Ns240p1363 

noncomputable def Ns240p1394 := @Enclosure.Real.IsNear.recentre' qz160 Bool.true 3629652976 34359738368 

noncomputable def Ns240p1395 := @Enclosure.Real.IsNear.cos_image qz165 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 115217177101)) qz695) Bool.true 115217177101 68719476736 

noncomputable def Ns240p1396 := nat_lit 1711885677076469695285867891505338800737557758198495732663942684920095754561408334416359093186674625914411881215845882885352217962096031429896598549256391641172688119455821690568715682881 

noncomputable def Ns240p1397 := nat_lit 964441052187160452702744801503751902842528252452564921539991520674177124918435647382143612022279885443488657065338938082652077654200444571393578832424550467716224494523364033601 

noncomputable def Ns240p1398 := nat_lit 17406689980529296434942771362890482075714198566609956130467540831042623974984126397175492171704698730398780337511650566067366788116731336252898781060480967201517574651266315343246163854401 

noncomputable def Ns240p1399 := BSN.cos_dyadic_bound_t 115217177101 68719476736 5 4 34359738368 13271040000 Ns240p1396 Ns240p1047 Ns240p1397 Ns240p1398 Ns240p1050 Ns240p1397 3629652976 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 115217177101) (BSN.cosEvenQ 68719476736) 0 4 Ns240p1396 Ns240p1047 Ns240p1397 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 115217177101) (BSN.cosOddQ 68719476736) 0 4 Ns240p1398 Ns240p1050 Ns240p1397 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1400 := @Ns240p1394 2011744698368 455989462271262720000 226853311 2147483648 7674197 1739461754880000 (@Ns240p1395 149 34359738368 Bool.true 3629652976 34359738368 1 13271040000 (@Ns240p1374 Ns240p1375 115217177101 68719476736 149 34359738368 (@Ns240p1376 72057594037927936 810540176865 1180591620717411303424 Ns240p1371 Ns240p1372 Ns240p1373 Ns240p1375 RS241to252.d56 (@Ns240p1377 0 1 307650239908500080 19228139994281255 72057594037927936 810540176865 1180591620717411303424 (@Ns240p1378 Ns240p1379 14724540366910759 72057594037927936 810540176865 1180591620717411303424 (@Ns240p1380 295144101345 1180591620717411303424 (Ns240p1313 rfl rfl) (Ns240p1313 rfl rfl) rfl) (Ns240p1313 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 115217177101 68719476736) (BSN.cos_neg_of_bound 115217177101 68719476736 Bool.true 3629652976 34359738368 1 13271040000 (Ns240p1399 rfl rfl)) rfl rfl) 

noncomputable abbrev qz509 := (Enclosure.Real.IsNear.const Bool.false 1 1)

noncomputable abbrev qz179 := (@Ns240p1366 50719883862606820148175 18889465931478580854784 Ns240p1363 Ns240p1364 RS241to252.d56 (@Ns240p1367 57357285 134217728 15 17179869184 (@Ns240p1368 17179869184 qz341 (Ns240p1313 rfl rfl) rfl) qz509 rfl rfl) rfl)

noncomputable def Ns240p1401 := @Ns240p1344 Ns240p1345 Ns240p1337 Ns240p1346 Ns240p1347 Ns240p1348 Ns240p1349 Ns240p1350 Ns240p1351 Ns240p1352 Ns240p1336 Ns240p1337 Ns240p1338 Ns240p1339 (@Ns240p1355 Ns240p1356 Ns240p1357 17083744027 17179869184 7674197 1739461754880000 Ns240p1345 Ns240p1337 Ns240p1346 Ns240p1347 (@Ns240p1362 50719883862606820148175 18889465931478580854784 Ns240p1363 Ns240p1364 Ns240p1353 Ns240p1354 Ns240p1356 Ns240p1357 (@Ns240p1365 Ns240p1363 Ns240p1364 Ns240p1358 Ns240p1359 Ns240p1360 Ns240p1361 qz179 qz179 rfl) qz179 rfl) (Ns240p1385 rfl) rfl) (@Ns240p1389 Ns240p1390 226853311 2147483648 7674197 1739461754880000 Ns240p1348 Ns240p1349 Ns240p1350 Ns240p1351 (@Ns240p1392 70368744177664 1 250000000000000 Ns240p1386 Ns240p1387 Ns240p1388 Ns240p1390 (@Ns240p1393 Ns240p1364 152159651587820460444525 18889465931478580854784 Ns240p1391 Ns240p1364 qz476 qz179 rfl) RS241to252.d58 rfl) (Ns240p1400 rfl) rfl) rfl rfl 

noncomputable def Ns240p1402 := nat_lit 44393356689112817739032505 

noncomputable def Ns240p1403 := nat_lit 265280409633830311207720865422123 

noncomputable def Ns240p1404 := nat_lit 1167413267786194386319215356260421396279359772678944414930878571459926913158598383486514575 

noncomputable def Ns240p1405 := @Enclosure.Real.IsNear.mulLit_tf qz172 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz154) Ns240p1402 Ns240p92 Ns240p1403 Ns240p1057 Ns240p1404 

noncomputable def Ns240p1406 := nat_lit 254629497041810760783555711051172270131433549208242031329517556169297662470417088272924672 

noncomputable def Ns240p1407 := nat_lit 44852470527000606981875817954897342226825615874080817938448085207722522302611345710085916482119011088574337152939645803093 

noncomputable def Ns240p1408 := nat_lit 984586619141896899393567805504033766999194462731082991899094046443989784463635644416000000000000000000000000000000000000000000 

noncomputable def Ns240p1409 := nat_lit 14797785563037605913010835 

noncomputable abbrev qz180 := qz502

noncomputable def Ns240p1410 := @Enclosure.Real.IsNear.mulLit_ft qz320 qz180 3 1 0 1 Ns240p1409 Ns240p92 Ns240p1403 

noncomputable def Ns240p1411 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz174 884279719003555 140737488355328 1 500000000000000 16734281297 17179869184 9830269 3478923509760000 Ns240p1409 

noncomputable def Ns240p1412 := @Enclosure.Real.IsNear.recentre' qz174 Bool.false 33468562594 34359738368 2576946036736 911978924542525440000 16734281297 17179869184 9830269 3478923509760000 

noncomputable def Ns240p1413 := @Enclosure.Real.IsNear.sin_image qz163 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 123629671977) qz695) Bool.false 123629671977 68719476736 189 68719476736 Bool.false 33468562594 34359738368 1 

noncomputable def Ns240p1414 := nat_lit 7706177647295532232009149455248021102034446554078624127584041863539933105067140688717594590991147921441959346643269016453670960154781890591689298264530699932549930585719312692454497841281 

noncomputable def Ns240p1415 := nat_lit 87972314389919681436536573358802488508909229447352760535897166083252396451397479444074537888040383657117614823310149345001055593919431144202692571536365889716811725392947079355937325056000 

noncomputable def Ns240p1416 := nat_lit 62616286036821667119039167763376217504561519622694815523721733140621655958237750100878594147997745714371761100299213336469663524042855083817795330649721168462272302502606621914335350747265 

noncomputable def Ns240p1417 := nat_lit 5014421920225421841882584681451741845007826078499107350546138466745386597729656328312248659618301868455704044928678512665060168853407575219553476577572855713858268347397983523288427528192000 

noncomputable def Ns240p1418 := BSN.sin_dyadic_bound_f 123629671977 68719476736 5 4 34359738368 13271040000 Ns240p1414 Ns240p1415 Ns240p1316 Ns240p1416 Ns240p1417 Ns240p1316 33468562594 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.sinEvenP 123629671977) (BSN.sinEvenQ 68719476736) 0 4 Ns240p1414 Ns240p1415 Ns240p1316 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.sinOddP 123629671977) (BSN.sinOddQ 68719476736) 0 4 Ns240p1416 Ns240p1417 Ns240p1316 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz510 := (@HMul.hMul Real Real Real qz615 qz613 qz710)

noncomputable abbrev qz181 := qz510

noncomputable abbrev qz511 := (@Enclosure.Real.IsNear.neg qz181 Bool.false Ns240p1409 Ns240p92 Ns240p1403 Ns240p1065 (@Ns240p1411 Ns240p92 Ns240p1403 Ns240p1065 RS241to252.d56 (Ns240p1412 (@Ns240p1413 13271040000 (Ns240p1314 rfl) (Enclosure.sfrac_false_div 123629671977 68719476736) (Ns240p1418 rfl rfl) rfl rfl) rfl) rfl))

noncomputable def Ns240p1419 := @Ns240p1410 Ns240p1065 Ns240p1402 Ns240p92 Ns240p1403 Ns240p1057 qz476 qz511 rfl 

noncomputable abbrev qz182 := (@HMul.hMul Real Real Real qz344 qz500 (Real.cos qz495))

noncomputable def Ns240p1420 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz182) (@HMul.hMul Real Real Real qz5 qz129 qz170) 

noncomputable abbrev qz183 := (@HMul.hMul Real Real Real qz344 qz316 qz502)

noncomputable abbrev qz184 := (@HMul.hMul Real Real Real qz344 qz503 (Zeta.RiemannSiegel.correction qz484))

noncomputable def Ns240p1421 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz154) (@HMul.hMul Real Real Real qz5 qz159 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns240p1420 (@HMul.hMul Real Real Real qz5 qz183 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c8 1 Zeta.RiemannSiegel.correction qz154))) qz184)) 

noncomputable def Ns240p1422 := @Enclosure.Real.IsNear.mulLit_tt qz159 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns240p1420 (@HMul.hMul Real Real Real qz5 qz183 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 1 Zeta.RiemannSiegel.correction qz154))) qz184) 151849211545 

noncomputable def Ns240p1423 := nat_lit 7687977144617806690497132118384759942938825041226488608244676885193549084216935 

noncomputable def Ns240p1424 := nat_lit 7410693711188236507108543040556026102609279018600996098525285376506440296955904 

noncomputable def Ns240p1425 := nat_lit 590007370934160858157247349782794040538785378008319064031368843640194169994455156091444638169847919925459465333 

noncomputable def Ns240p1426 := nat_lit 57310484066948812652470532659443198179313590676237537519720734937814401024000000000000000000000000000000000000000000 

noncomputable def Ns240p1427 := nat_lit 23217386455932728575289202938314986045000145231439884143558967774246377949639065 

noncomputable def Ns240p1428 := @Enclosure.Real.IsNear.subLit_ff_n (@HSub.hSub Real Real Real qz11 Ns240p1420 (@HMul.hMul Real Real Real qz5 qz183 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz154))) qz184 Ns240p1427 Ns240p1424 

noncomputable def Ns240p1429 := nat_lit 574055037447018055247199423671385153871938721594211806444246047595298940620312378085244887967248792656738825333 

noncomputable def Ns240p1430 := nat_lit 209422889732320761210049768685839311567105721196424235611375 

noncomputable def Ns240p1431 := nat_lit 533813414289305235494298903796048714828956601236693032083357104963725828183311771067 

noncomputable def Ns240p1432 := nat_lit 1917782448505610809266875237490306578392514682893107200000000000000000000000000000000000000 

noncomputable def Ns240p1433 := nat_lit 386065717408748585307576486805111814418434900213554247468891803021611601177575073808368803154858960304622019267291814705761698514552750080 

noncomputable def Ns240p1434 := nat_lit 10158658991537029354108952740801385300416613729029417055 

noncomputable def Ns240p1435 := nat_lit 766247770432944429179173513575154591809369561091801088 

noncomputable def Ns240p1436 := nat_lit 34230524825913474239609939954723997900135651001986829485368366039882416733533 

noncomputable def Ns240p1437 := nat_lit 378821224396170036398395108640060558694817715139379200000000000000000000000000000000 

noncomputable def Ns240p1438 := @Enclosure.Real.IsNear.subLit_ff_p Ns240p1420 (@HMul.hMul Real Real Real qz5 qz183 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz154)) Ns240p1434 Ns240p1435 Ns240p1436 Ns240p1437 

noncomputable def Ns240p1439 := nat_lit 75031134724302675207375478835629028442133863964660086307367880929171543556214375 

noncomputable def Ns240p1440 := nat_lit 568876425950880765855405623272733076360536042939180320185869462376470634471735388603559192192649378896738825333 

noncomputable def Ns240p1441 := nat_lit 17790270607138494667026698399343546191008810182861793578819504711631639160535474748843856331427685096969019488469621023336540374302720 

noncomputable def Ns240p1442 := @Enclosure.Real.IsNear.subLit_ft (@Neg.neg Real Real.instNeg qz182) (@HMul.hMul Real Real Real qz5 qz129 qz170) 

noncomputable def Ns240p1443 := nat_lit 583581644097805667401465713707342948331598150036449375 

noncomputable def Ns240p1444 := nat_lit 163314163951582073903675310813193758570870620980751918423899211356573046093 

noncomputable def Ns240p1445 := nat_lit 4676805239458889338251791464692105662898984137523200000000000000000000000000000000 

noncomputable def Ns240p1446 := nat_lit 15106808367724221123015985 

noncomputable def Ns240p1447 := nat_lit 207096473804119269062990371924499 

noncomputable def Ns240p1448 := nat_lit 3735465674926184202240000000000000000000 

noncomputable def Ns240p1449 := nat_lit 12281065147529425472833085221743001810891751149512496306365856087927240188231680 

noncomputable def Ns240p1450 := @Enclosure.Real.IsNear.neg qz182 Bool.true Ns240p1443 

noncomputable def Ns240p1451 := @Enclosure.Real.IsNear.mulLit_ft qz175 qz160 Ns240p1358 Ns240p1359 Ns240p1360 

noncomputable def Ns240p1452 := @Enclosure.Real.IsNear.mulLit_ft qz129 qz170 884279719003555 70368744177664 1 

noncomputable def Ns240p1453 := nat_lit 5070429923766290021129074864709044205428738672403916125 

noncomputable def Ns240p1454 := @Enclosure.Real.IsNear.mulLit_tt qz183 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz154) Ns240p1409 Ns240p1009 Ns240p1403 Ns240p1109 Ns240p1453 

noncomputable def Ns240p1455 := nat_lit 6129982163463555433433388108601236734474956488734408704 

noncomputable def Ns240p1456 := nat_lit 6202391407411266649258264325788864803768712238836854120594800688722771 

noncomputable def Ns240p1457 := nat_lit 7671129794022443237067500949961226313570058731572428800000000000000000000000 

noncomputable def Ns240p1458 := @Enclosure.Real.IsNear.mulLit_ft qz0 qz180 2 1 0 1 Ns240p1409 Ns240p92 Ns240p1403 

noncomputable def Ns240p1459 := @Ns240p1458 Ns240p1065 Ns240p1409 Ns240p1009 Ns240p1403 Ns240p1109 qz341 qz511 rfl 

noncomputable abbrev qz185 := (@HMul.hMul Real Real Real qz344 qz501 (Real.sin qz495))

noncomputable def Ns240p1460 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz185) (@HMul.hMul Real Real Real qz5 qz180 qz153) 

noncomputable def Ns240p1461 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz154) (@HMul.hMul Real Real Real qz5 qz159 Ns240p1460) Bool.true Ns240p1453 Ns240p1455 Ns240p1456 Ns240p1457 (BSN.deriv_correction_mk qz154 qz505) 

noncomputable def Ns240p1462 := nat_lit 33391216669331768449842397004913893413319525 

noncomputable def Ns240p1463 := nat_lit 178405961588244985132285746181186892047843328 

noncomputable def Ns240p1464 := nat_lit 80647412537458916183790692806818988931779296094328987930051 

noncomputable def Ns240p1465 := @Enclosure.Real.IsNear.mulLit_tf qz159 Ns240p1460 151849211545 34359738368 1897 34359738368 Ns240p1462 Ns240p1463 Ns240p1464 

noncomputable def Ns240p1466 := @Enclosure.Real.IsNear.subLit_tt_p (@Neg.neg Real Real.instNeg qz185) (@HMul.hMul Real Real Real qz5 qz180 qz153) 

noncomputable def Ns240p1467 := nat_lit 866485512987942952355847911200725 

noncomputable def Ns240p1468 := nat_lit 324518553658426726783156020576256 

noncomputable def Ns240p1469 := nat_lit 49347242295236932017185238754047157438639 

noncomputable def Ns240p1470 := nat_lit 2852213850513516153367582212096000000000000000000 

noncomputable def Ns240p1471 := nat_lit 509746665084179540953145172423413217123988325 

noncomputable def Ns240p1472 := nat_lit 72922024876136390828910666371915790145535138417036239130051 

noncomputable def Ns240p1473 := nat_lit 10836069338426694469169181031259428047766932757152930174368344750076356198400 

noncomputable def Ns240p1474 := @Enclosure.Real.IsNear.neg qz185 Bool.false Ns240p1467 

noncomputable def Ns240p1475 := @Enclosure.Real.IsNear.mulLit_tt qz176 qz170 50719883862606820148175 18889465931478580854784 Ns240p1363 

noncomputable def Ns240p1476 := @Enclosure.Real.IsNear.mulLit_tf qz180 qz153 Ns240p1409 Ns240p92 Ns240p1403 Ns240p1065 34447496411722675495 73786976294838206464 

noncomputable def Ns240p1477 := @Enclosure.Real.IsNear.of_eq qz153 (@HMul.hMul Real Real Real qz5 qz159 qz160) Bool.false 34447496411722675495 

noncomputable def Ns240p1478 := @Enclosure.Real.IsNear.mulLit_tt qz159 qz160 151849211545 34359738368 1897 

noncomputable abbrev qz512 := (@Ns240p1477 73786976294838206464 756948385166113037 Ns240p69 (BSN.correction_mk qz154 qz711) (@Ns240p1478 34359738368 226853311 2147483648 7674197 1739461754880000 34447496411722675495 73786976294838206464 756948385166113037 Ns240p69 Ns240p1320 (Ns240p1400 rfl) rfl))

noncomputable def Ns240p1479 := @Ns240p1476 756948385166113037 Ns240p69 Ns240p1471 Ns240p1463 Ns240p1472 Ns240p1123 qz511 qz512 

noncomputable def Ns240p1480 := @Ns240p1454 Ns240p1455 Ns240p1456 Ns240p1457 Ns240p1439 Ns240p1424 Ns240p1440 Ns240p1426 Ns240p1459 (Ns240p1461 (@Ns240p1465 Ns240p1123 Ns240p1453 Ns240p1455 Ns240p1456 Ns240p1457 Ns240p1320 (@Ns240p1466 Ns240p1467 Ns240p1468 Ns240p1469 Ns240p1470 Ns240p1471 Ns240p1463 Ns240p1472 Ns240p1123 Ns240p1473 Ns240p1462 Ns240p1463 Ns240p1464 Ns240p1123 (@Ns240p1474 Ns240p1468 Ns240p1469 Ns240p1470 (@Ns240p1475 Ns240p1364 17083744027 17179869184 7674197 1739461754880000 Ns240p1467 Ns240p1468 Ns240p1469 Ns240p1470 qz179 (Ns240p1385 rfl) rfl)) (Ns240p1479 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns240p1481 := @Ns240p1438 Ns240p1439 Ns240p1424 Ns240p1440 Ns240p1426 Ns240p1441 Ns240p1427 Ns240p1424 Ns240p1429 Ns240p1426 (@Ns240p1442 Ns240p1443 Ns240p1435 Ns240p1444 Ns240p1445 Ns240p1446 Ns240p1009 Ns240p1447 Ns240p1448 Ns240p1449 Ns240p1434 Ns240p1435 Ns240p1436 Ns240p1437 (@Ns240p1450 Ns240p1435 Ns240p1444 Ns240p1445 (@Ns240p1451 Ns240p1361 226853311 2147483648 7674197 1739461754880000 Ns240p1443 Ns240p1435 Ns240p1444 Ns240p1445 (@Ns240p1365 Ns240p1363 Ns240p1364 Ns240p1358 Ns240p1359 Ns240p1360 Ns240p1361 qz179 qz179 rfl) (Ns240p1400 rfl) rfl)) (@Ns240p1452 250000000000000 17083744027 17179869184 7674197 1739461754880000 Ns240p1446 Ns240p1009 Ns240p1447 Ns240p1448 RS241to252.d58 (Ns240p1385 rfl) rfl) rfl rfl) Ns240p1480 

noncomputable def Ns240p1482 := nat_lit 6079480703888047484932925436369875775225 

noncomputable def Ns240p1483 := nat_lit 680564733841876926926749214863536422912 

noncomputable def Ns240p1484 := nat_lit 7158876718349682706862854975956733012916542661260245656941 

noncomputable abbrev qz186 := qz503

noncomputable def Ns240p1485 := @Enclosure.Real.IsNear.mulLit_ff qz186 qz153 Ns240p1482 Ns240p1483 Ns240p1484 Ns240p1144 34447496411722675495 73786976294838206464 

noncomputable def Ns240p1486 := @Enclosure.Real.IsNear.mulLit_ft qz130 qz162 Ns240p892 Ns240p896 Ns240p894 Ns240p897 7774762929 34359738368 9830269 3478923509760000 Ns240p1482 

noncomputable abbrev qz513 := (@HMul.hMul Real Real Real qz615 qz688 qz705)

noncomputable abbrev qz187 := qz513

noncomputable def Ns240p1487 := @Ns240p1485 756948385166113037 Ns240p69 Ns240p1430 Ns240p1091 Ns240p1431 Ns240p1432 (@Enclosure.Real.IsNear.neg qz187 Bool.true Ns240p1482 Ns240p1483 Ns240p1484 Ns240p1144 (@Ns240p1486 Ns240p1483 Ns240p1484 Ns240p1144 RS241to252.d60 qz506 rfl)) qz512 

noncomputable def Ns240p1488 := nat_lit 18238442111664142454798776309109627325675 

noncomputable def Ns240p1489 := @Enclosure.Real.IsNear.mulLit_ft qz173 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz154) Ns240p1488 Ns240p1483 Ns240p1484 Ns240p1149 Ns240p1453 

noncomputable def Ns240p1490 := @Enclosure.Real.IsNear.mulLit_ff qz320 qz186 3 1 0 1 Ns240p1482 Ns240p1483 Ns240p1484 

noncomputable def Ns240p1491 := @Ns240p1490 Ns240p1144 Ns240p1488 Ns240p1483 Ns240p1484 Ns240p1149 qz476 (@Enclosure.Real.IsNear.neg qz187 Bool.true Ns240p1482 Ns240p1483 Ns240p1484 Ns240p1144 (@Ns240p1486 Ns240p1483 Ns240p1484 Ns240p1144 RS241to252.d60 qz506 rfl)) rfl 

noncomputable def Ns240p1492 := @Ns240p1489 Ns240p1455 Ns240p1456 Ns240p1457 Ns240p1331 Ns240p1332 Ns240p1333 Ns240p1334 Ns240p1491 (Ns240p1461 (@Ns240p1465 Ns240p1123 Ns240p1453 Ns240p1455 Ns240p1456 Ns240p1457 Ns240p1320 (@Ns240p1466 Ns240p1467 Ns240p1468 Ns240p1469 Ns240p1470 Ns240p1471 Ns240p1463 Ns240p1472 Ns240p1123 Ns240p1473 Ns240p1462 Ns240p1463 Ns240p1464 Ns240p1123 (@Ns240p1474 Ns240p1468 Ns240p1469 Ns240p1470 (@Ns240p1475 Ns240p1364 17083744027 17179869184 7674197 1739461754880000 Ns240p1467 Ns240p1468 Ns240p1469 Ns240p1470 qz179 (Ns240p1385 rfl) rfl)) (Ns240p1479 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns240p1493 := @Ns240p1329 Ns240p1330 Ns240p1304 Ns240p1331 Ns240p1332 Ns240p1333 Ns240p1334 Ns240p1335 Ns240p1322 Ns240p1301 Ns240p1323 Ns240p1304 (@Ns240p1340 Ns240p1341 Ns240p1301 Ns240p1342 Ns240p1304 Ns240p1343 Ns240p1328 Ns240p1301 Ns240p1330 Ns240p1304 Ns240p1401 (@Ns240p1405 Ns240p1406 Ns240p1407 Ns240p1408 Ns240p1341 Ns240p1301 Ns240p1342 Ns240p1304 Ns240p1419 (@Ns240p1421 Bool.false Ns240p1404 Ns240p1406 Ns240p1407 Ns240p1408 (BSN.iteratedDeriv_two_correction_mk qz154 qz505) (@Ns240p1422 34359738368 1897 34359738368 Ns240p1423 Ns240p1424 Ns240p1425 Ns240p1426 Ns240p1404 Ns240p1406 Ns240p1407 Ns240p1408 Ns240p1320 (@Ns240p1428 Ns240p1429 Ns240p1426 Ns240p1430 Ns240p1091 Ns240p1431 Ns240p1432 Ns240p1433 Ns240p1423 Ns240p1424 Ns240p1425 Ns240p1426 (Ns240p1481 rfl rfl) (Ns240p1487 rfl) rfl rfl) rfl)) rfl) rfl rfl) Ns240p1492 

noncomputable def Ns240p1494 := nat_lit 11571137616968005618695871092400032494164144423908000875 

noncomputable def Ns240p1495 := nat_lit 47890485652059026823698344598447161988085597568237568 

noncomputable def Ns240p1496 := nat_lit 193190040711630432694260458035666810738634839520955814537733715751503673865397749947 

noncomputable def Ns240p1497 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz332 RSCompact.c11) qz174) qz153 Ns240p1494 Ns240p1495 Ns240p1496 Ns240p1158 34447496411722675495 73786976294838206464 756948385166113037 

noncomputable def Ns240p1498 := @Enclosure.Real.IsNear.mulLit_ff qz459 qz174 Ns240p898 Ns240p899 Ns240p900 Ns240p901 16734281297 17179869184 9830269 3478923509760000 Ns240p1494 

noncomputable abbrev qz514 := (Ns240p1412 (@Ns240p1413 13271040000 (Ns240p1314 rfl) (Enclosure.sfrac_false_div 123629671977 68719476736) (Ns240p1418 rfl rfl) rfl rfl) rfl)

noncomputable def Ns240p1499 := Ns240p1299 (@Ns240p1303 Ns240p1304 Ns240p1292 Ns240p1293 Ns240p1294 Ns240p1295 Ns240p1320 (@Ns240p1321 Ns240p1322 Ns240p1301 Ns240p1323 Ns240p1304 Ns240p1324 Ns240p1325 Ns240p1326 Ns240p971 Ns240p1327 Ns240p1300 Ns240p1301 Ns240p1302 Ns240p1304 (Ns240p1493 rfl rfl) (@Ns240p1497 Ns240p69 Ns240p1324 Ns240p1325 Ns240p1326 Ns240p971 (@Ns240p1498 Ns240p1495 Ns240p1496 Ns240p1158 RS241to252.d61 qz514 rfl) qz512 rfl) rfl rfl) rfl) 

noncomputable def Ns240p1500 := @Enclosure.Real.IsNear.of_eq qz700 (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz154) qz462)) Bool.false Ns240p1287 Ns240p1288 Ns240p1289 Ns240p1290 (BSN.correctionLinear_mk qz154) (@Enclosure.Real.IsNear.neg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz154) qz462) Bool.true Ns240p1287 Ns240p1288 Ns240p1289 Ns240p1290 (@Ns240p1296 Ns240p1288 Ns240p1289 Ns240p1290 Ns240p1499 RS241to252.d62 rfl)) 

noncomputable def Ns240p1501 := @Enclosure.Real.IsNear.inv_image qz155 77899363 8388608 15 8388608 903328 903330 8388608 qz492 rfl 

noncomputable def Ns240p1502 := @Ns240p1291 Ns240p1243 Ns240p1253 Ns240p1246 Ns240p1500 (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz155) Bool.false 1806658 16777216 2 16777216 903329 8388608 1 8388608 (Ns240p1501 rfl rfl rfl rfl rfl) rfl) 

noncomputable abbrev qz515 := (BSN.correction_mk qz154 qz711)

noncomputable def Ns240p1503 := @Ns240p1245 Ns240p1246 Ns240p1172 Ns240p1168 Ns240p1174 Ns240p1170 (Ns240p1247 qz29 (@Enclosure.Real.IsNear.of_eq qz491 (@Inv.inv Real Real.instInv (Real.sqrt qz155)) Bool.false 2752757 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz152 (BSN.t_div_two_pi_nonneg qz151 541836 1000 qz156)) Ns240p1251) rfl) (@Ns240p1254 Ns240p1255 Ns240p1242 Ns240p1243 Ns240p1244 Ns240p1246 (@Ns240p1256 17592186044416 368655958279093 3562417673994240000 qz515 (@Ns240p1257 16777216 110769 1048576 15297769 849346560000 8212922643555 17592186044416 368655958279093 3562417673994240000 Ns240p1272 (Ns240p1286 rfl) rfl)) (Ns240p1502 rfl) rfl rfl) 

noncomputable abbrev qz714 := (@BSN.floor_sqrt_eq_dec qz151 541836 1000 9 qz156 rfl rfl rfl)

noncomputable abbrev qz516 := qz714

noncomputable def Ns240p1504 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz151) (hardyZApproximantRS qz151) Bool.false Ns240p1167 Ns240p1168 Ns240p1169 Ns240p1170 (@Eq.refl Real (hardyZApproximantRS qz151)) (Ns240p1171 (BSN.hardyZApproximantRS_eq qz151 9 qz516) (@Ns240p1173 Ns240p1174 Ns240p1170 Ns240p1175 Ns240p1167 Ns240p1168 Ns240p1169 Ns240p1170 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz151) qz151 9) (@HAdd.hAdd Real Real Real qz360 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 9)) Bool.true 3462461 33554432 46453 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz151) qz151 9) (Ns240p1241 (Ns240p1240 rfl) rfl rfl)) (Ns240p1503 rfl) rfl rfl)) 

theorem RS241to252.d65 : Enclosure.Real.IsNear (hardyZApproximantRS qz151) Bool.false Ns240p1167 Ns240p1168 Ns240p1169 Ns240p1170 := Ns240p1504 

noncomputable def Ns240p1505 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) qz44 Bool.false 13065801 536870912 

theorem RS241to252.d66 : Enclosure.Real.IsNear (hardyZErrorBoundRS qz4) Bool.false 13065801 536870912 201 536870912 := @Ns240p1505 201 536870912 (BSN.hardyZErrorBoundRS_mk qz4 531948 1000 qz10 rfl rfl) (@Ns240p313 1 536870912 1 536870912 876831062360064 13065801 536870912 201 536870912 (@Ns240p314 67108864 25 67108864 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns240p315 (Ns240p321 rfl rfl rfl rfl) rfl) rfl) (@Ns240p322 16777216 1 16777216 1 536870912 1 536870912 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns240p323 1 16777216 1 16777216 (@Ns240p327 8388608 (@Ns240p331 35184372088832000 Ns240p324 Ns240p325 Ns240p326 Ns240p325 (@Ns240p332 Ns240p329 Ns240p330 Ns240p329 (Ns240p320 rfl) (Ns240p320 rfl) rfl) (Ns240p320 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) 

theorem RS241to252.d67 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

theorem RS241to252.d68 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 qz341 RS241to252.d67 rfl 

theorem RS241to252.d69 : Enclosure.Real.IsNear qz3 Bool.false 683565275 4294967296 1 4294967296 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 683565275 4294967296 1 4294967296 683565275 4294967296 1 4294967296 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 341782637 341782638 2147483648 RS241to252.d68 rfl rfl rfl rfl rfl rfl) rfl 

theorem RS241to252.d70 : Enclosure.Real.IsNear qz129 Bool.false 884279719003555 70368744177664 1 250000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz323 Real.pi 4 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 70368744177664 1 250000000000000 qz687 RS241to252.d67 rfl 

theorem RS241to252.d71 : Enclosure.Real.IsNear RSCompact.c2 Bool.false Ns240p892 Ns240p893 Ns240p894 Ns240p895 := @Enclosure.Real.IsNear.mulLit_ff Real.pi Real.pi 226375608064910080 72057594037927936 1 1000000000000000 226375608064910080 72057594037927936 1 1000000000000000 Ns240p892 Ns240p893 Ns240p894 Ns240p895 RS241to252.d67 RS241to252.d67 rfl 

theorem RS241to252.d72 : Enclosure.Real.IsNear qz130 Bool.false Ns240p892 Ns240p896 Ns240p894 Ns240p897 := @Enclosure.Real.IsNear.mulLit_ff qz323 RSCompact.c2 4 1 0 1 Ns240p892 Ns240p893 Ns240p894 Ns240p895 Ns240p892 Ns240p896 Ns240p894 Ns240p897 qz687 RS241to252.d71 rfl 

noncomputable def Ns240p1506 := @Enclosure.Real.IsNear.mulLit_ff qz332 (@HMul.hMul Real Real Real qz5 RSCompact.c2 Real.pi) 8 1 0 1 Ns240p898 Ns240p902 Ns240p900 Ns240p903 Ns240p898 Ns240p899 Ns240p900 Ns240p901 (Enclosure.Real.IsNear.const Bool.false 8 1) (@Enclosure.Real.IsNear.mulLit_ff RSCompact.c2 Real.pi Ns240p892 Ns240p893 Ns240p894 Ns240p895 226375608064910080 72057594037927936 1 1000000000000000 Ns240p898 Ns240p902 Ns240p900 Ns240p903 RS241to252.d71 RS241to252.d67 rfl) rfl 

theorem RS241to252.d73 : Enclosure.Real.IsNear qz459 Bool.false Ns240p898 Ns240p899 Ns240p900 Ns240p901 := Ns240p1506 

noncomputable def Ns240p1507 := @Enclosure.Real.IsNear.inv_image qz460 Ns240p905 Ns240p435 Ns240p906 Ns240p907 2266516 2266517 2147483648 (@Enclosure.Real.IsNear.mulLit_ff qz461 RSCompact.c2 96 1 0 1 Ns240p892 Ns240p893 Ns240p894 Ns240p895 Ns240p905 Ns240p435 Ns240p906 Ns240p907 (Enclosure.Real.IsNear.const Bool.false 96 1) RS241to252.d71 rfl) rfl rfl 

theorem RS241to252.d74 : Enclosure.Real.IsNear qz462 Bool.false 4533033 4294967296 1 4294967296 := @Enclosure.Real.IsNear.recentre' qz462 Bool.false 4533033 4294967296 1 4294967296 4533033 4294967296 1 4294967296 (Ns240p1507 rfl rfl rfl rfl) rfl 

noncomputable def Ns240p1508 := nat_lit 20811921831088204570839604336656539999447420645610406289403287079957008500648098483361609328430533729193926030961737514739174104610310149907 

noncomputable def Ns240p1509 := nat_lit 2158212337634767333856699377688004537254573296430807322622588706050375531883912411069634587640429436044678414746591817129138512460099443696337058812674703089734181460259670317729692349 

noncomputable def Ns240p1510 := nat_lit 1524792730511538653105923711876058481672947973607728192091376043443687014324724557016859284658388588084586464018187667363594240000000000000000000000000000000000000000000000000000000000000 

noncomputable abbrev qz851 := (Enclosure.sfrac Bool.false 543245 1000)

noncomputable abbrev qz715 := qz851

noncomputable abbrev qz517 := qz715

noncomputable abbrev qz188 := qz517

noncomputable abbrev qz852 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 543245 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz716 := qz852

noncomputable abbrev qz518 := qz716

noncomputable abbrev qz189 := (@HMul.hMul Real Real Real qz344 qz345 (@HPow.hPow Real Real Real qz444 qz518 qz347))

noncomputable abbrev qz853 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 543245 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz717 := qz853

noncomputable abbrev qz519 := qz717

noncomputable abbrev qz190 := (Zeta.RiemannSiegel.correction qz519)

noncomputable abbrev qz191 := qz519

noncomputable abbrev qz854 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 543245 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz718 := qz854

noncomputable abbrev qz520 := qz718

noncomputable abbrev qz192 := qz520

noncomputable abbrev qz719 := (Zeta.RiemannSiegel.correctionLinear qz191)

noncomputable abbrev qz521 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) qz190 (@HMul.hMul Real Real Real qz5 qz719 (@Inv.inv Real Real.instInv qz192)))

noncomputable def Ns240p1511 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz188) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (@HMul.hMul Real Real Real qz5 qz189 qz521)) Bool.true Ns240p1508 Ns240p928 Ns240p1509 Ns240p1510 

noncomputable def Ns240p1512 := nat_lit 447372437165358722314714120802071644344689962571732886360001843954781390722095979713550898963216909005938828794244948817463500628956850413 

noncomputable def Ns240p1513 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (@HMul.hMul Real Real Real qz5 qz189 qz521) 479215355 67108864 23285 16777216 Ns240p1512 Ns240p928 

noncomputable def Ns240p1514 := nat_lit 41961421513691135185153774947119413897122717892869267056773068248117271124128945795207147279014391167769408230641862466738512460099443696337058812674703089734181460259670317729692349 

noncomputable def Ns240p1515 := nat_lit 1396664431741129292548653373242493957533477027257060952660309833801792009316837152978520503242776021479888011637871032080329230458615076847928475648 

noncomputable def Ns240p1516 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 543245 1000 121 161 134217728 67108864 2251799813685248 Bool.false 126075433488 1801 

noncomputable def Ns240p1517 := Ns240p1516 279097919 42 47453128 8 294906479 42 44739240 8 Bool.true 423648109 76211 Bool.true 32841109 Bool.true 187613720 7074237752028440 1 Bool.false 32514384 Bool.true Bool.false 132215035 Bool.true Bool.true 479215355 

noncomputable def Ns240p1518 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 543245 1000 21 74 134217728 67108864 2251799813685248 Bool.false 126075433488 1801 

noncomputable def Ns240p1519 := Ns240p1518 240485871 42 54794152 8 261175631 42 50729528 8 Bool.true 374349788 56837 Bool.true 139910506 Bool.true 205597328 7074237752028440 1 Bool.false 115913648 Bool.true Bool.false 5230061 Bool.true Bool.true 423648109 

noncomputable def Ns240p1520 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 543245 1000 118 41 134217728 67108864 2251799813685248 Bool.false 126075433488 1801 

noncomputable def Ns240p1521 := Ns240p1520 186065264 42 67108856 8 216015088 42 60023992 8 Bool.true 297231137 33499 Bool.false 118620878 Bool.false 82339727 7074237752028440 1 Bool.false 85123844 Bool.true Bool.false 77271207 Bool.true Bool.true 374349788 

noncomputable def Ns240p1522 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 543245 1000 358 218 134217728 67108864 2251799813685248 Bool.false 126075433488 1801 

noncomputable def Ns240p1523 := Ns240p1522 93032624 42 94906264 8 147453232 42 77490640 16 Bool.true 134217656 1850 Bool.false 59246003 Bool.false 11542789 7074237752028440 1 Bool.false 121352575 Bool.true Bool.false 133721691 Bool.true Bool.true 297231137 

noncomputable def Ns240p1524 := nat_lit 3131470897117856805729331643679672396300196742184667 

noncomputable def Ns240p1525 := nat_lit 3333709807528147055305620522063973311529038643200 

noncomputable def Ns240p1526 := nat_lit 22710194740651054655789373500000000 

noncomputable def Ns240p1527 := nat_lit 74023227714728957578174573452045000000 

noncomputable abbrev qz522 := (@Eq.refl Real qz715)

noncomputable abbrev qz193 := qz522

noncomputable def Ns240p1528 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz188 543245 1000 1180461520100 16000000 1086490 4000 2000 Ns240p1526 Ns240p1527 qz193 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns240p1529 := nat_lit 15657354485589284028646658218398361981500983710923335000000 

noncomputable abbrev qz720 := (Real.log (Enclosure.sfrac Bool.false 1180461520100 16000000))

noncomputable abbrev qz721 := (@Nat.cast Real Real.instNatCast 1086490)

noncomputable abbrev qz722 := (Enclosure.sfrac Bool.false 543245 2000)

noncomputable abbrev qz194 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 543245 4000) qz720) (@HMul.hMul Real Real Real qz344 qz358 (@HSub.hSub Real Real Real qz350 qz355 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz356 qz721))))) qz722)

noncomputable abbrev qz523 := (@HSub.hSub Real Real Real qz11 qz194 (@HMul.hMul Real Real Real qz5 qz722 (Real.log Real.pi)))

noncomputable def Ns240p1530 := @Enclosure.Real.IsNear.addLit_ft_p qz523 (Enclosure.sfrac Bool.true Ns240p1526 Ns240p1527) 211519547077991712163 225179981368524800 444970524100361573 33177600000000000000000 Ns240p1526 Ns240p1527 0 1 Ns240p1529 

noncomputable def Ns240p1531 := nat_lit 2838967303639708640934782566400 

noncomputable abbrev qz524 := (@HMul.hMul Real Real Real qz5 qz722 (Real.log Real.pi))

noncomputable def Ns240p1532 := @Enclosure.Real.IsNear.subLit_ff_p qz194 qz524 281535747788780193187 225179981368524800 86132066454301 16200000000000000000 4173290771889 13421772800 108649 13421772800 Ns240p1531 211519547077991712163 225179981368524800 

noncomputable abbrev qz195 := (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 543245 4000) qz720) (@HMul.hMul Real Real Real qz344 qz358 (@HSub.hSub Real Real Real qz350 qz355 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz356 qz721)))))

noncomputable def Ns240p1533 := @Enclosure.Real.IsNear.subLit_ff_p qz195 qz722 13707987891122092827 9007199254740992 86132066454301 16200000000000000000 543245 2000 0 1 22522859823102415454960 281535747788780193187 225179981368524800 86132066454301 16200000000000000000 

noncomputable def Ns240p1534 := nat_lit 30867644579228364274422873216516096 

noncomputable def Ns240p1535 := nat_lit 27101281464014361486950400 

noncomputable def Ns240p1536 := nat_lit 370306021516473818758014373651217165611201500000000 

noncomputable def Ns240p1537 := nat_lit 433022285927727695785647749417251248640800000000 

noncomputable def Ns240p1538 := nat_lit 907631834694707037994024082612898240300000000 

noncomputable def Ns240p1539 := BSN.log_dyadic_bound 131885520100 2229037520100 3 2 Ns240p1536 67108864 25920000 Ns240p1537 Ns240p1538 7950549 2360923040200 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 131885520100) (BSN.artanhQ 2229037520100) 0 2 Ns240p1537 Ns240p1536 Ns240p1538 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns240p1540 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 543245 4000) qz720 543245 4000 0 1 3155004403555575 281474976710656 195312581 5062500000000000 13711522937676386727 9007199254740992 21220516613069 4050000000000000000 (Enclosure.Real.IsNear.const Bool.false 543245 4000) (BSN.isNear_log_sfrac 1180461520100 16000000 3155004403555575 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1180461520100) qz354)) Bool.false Ns240p1535 Ns240p92 1000000414720000 25920000000000000000000 3155004403555575 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1180461520100 16000000 16 2360923040200 2097152000000 7950549 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns240p1539 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p1541 := BSN.arctan_dyadic_bound_f 1000 1086490 1 0 8388608 3240000 0 1 1 0 1 1 7720 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1086490) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1086490) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz723 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1086490)))

noncomputable def Ns240p1542 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz723 884279719003555 562949953421312 1 2000000000000000 7720 8388608 1 3240000 7413529951430560972800 883761638573475 562949953421312 50000000081 162000000000000000 qz16 (Ns240p1541 rfl) rfl rfl 

noncomputable def Ns240p1543 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 543245 4000) qz720) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz11 qz14 qz723)) 13711522937676386727 9007199254740992 21220516613069 4050000000000000000 883761638573475 2251799813685248 50000000081 648000000000000000 Ns240p1534 13707987891122092827 9007199254740992 86132066454301 16200000000000000000 (Ns240p1540 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 qz723) 1 4 0 1 883761638573475 562949953421312 50000000081 162000000000000000 883761638573475 2251799813685248 50000000081 648000000000000000 qz359 Ns240p1542 rfl) 

noncomputable def Ns240p1544 := @Ns240p1530 Ns240p1524 Ns240p1525 444970524100361573 33177600000000000000000 (@Ns240p1532 444970524100361573 33177600000000000000000 (Ns240p1533 (Ns240p1543 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 543245 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz722 (Real.log Real.pi) 543245 2000 0 1 38410761 33554432 1 33554432 4173290771889 13421772800 108649 13421772800 (Enclosure.Real.IsNear.const Bool.false 543245 2000) RS241to252.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns240p1526 Ns240p1527) 

noncomputable def Ns240p1545 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz188) Bool.false Ns240p1524 Ns240p1525 444970524100361573 33177600000000000000000 7879714593 8388608 113 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz188) (@HAdd.hAdd Real Real Real qz360 qz523 (Enclosure.sfrac Bool.true Ns240p1526 Ns240p1527)) Bool.false Ns240p1524 Ns240p1525 444970524100361573 33177600000000000000000 Ns240p1528 (Ns240p1544 rfl rfl)) 

noncomputable def Ns240p1546 := nat_lit 1897737173814083391062016 

noncomputable def Ns240p1547 := nat_lit 854898181653193366502553118345444424462761837716713958176250907311105062131869011509149748204925309031789100243157141308236016990563841 

noncomputable def Ns240p1548 := nat_lit 606226783184743385850325879527849001168987413775787931228379498984904703523540215420361075648290947673900503199057323951156375041 

noncomputable def Ns240p1549 := nat_lit 4269193153870853071830781866857415761831512659913123311327072279026777819828111996521700327847938474491360613954206105746758784082521601 

noncomputable def Ns240p1550 := BSN.sin_dyadic_bound_f 53936934529 34359738368 4 3 16777216 6486329 Ns240p1547 Ns240p105 Ns240p1548 Ns240p1549 Ns240p108 Ns240p1548 16777207 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53936934529) qz361 0 3 Ns240p1547 Ns240p105 Ns240p1548 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53936934529) qz362 0 3 Ns240p1549 Ns240p108 Ns240p1548 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1551 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz188) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7879714593) qz406) Bool.false 7879714593 8388608 113 8388608 Bool.true 16777207 16777216 1 3240000 (Ns240p1545 rfl) (Enclosure.sfrac_false_div 7879714593 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7879714593) qz406) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns240p1546) (@Nat.cast Real Real.instNatCast Ns240p1009)) 226375608064910080 72057594037927936 Bool.false 16777207 16777216 149 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 7879714593 8388608 226375608064910080 72057594037927936 149 Ns240p1546 Ns240p1009 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777207 16777216 Ns240p1546 Ns240p1009 53936934529 34359738368 6486329 6480000 (Ns240p1550 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns240p1552 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz188) Bool.false Ns240p1524 Ns240p1525 444970524100361573 33177600000000000000000 126075433488 134217728 1801 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz188) (@HAdd.hAdd Real Real Real qz360 qz523 (Enclosure.sfrac Bool.true Ns240p1526 Ns240p1527)) Bool.false Ns240p1524 Ns240p1525 444970524100361573 33177600000000000000000 Ns240p1528 (Ns240p1544 rfl rfl)) 

noncomputable def Ns240p1553 := Ns240p1523 33499 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 358 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 121352575 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 218 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133721691 134217728) qz193 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 1) Bool.true 16777207 16777216 5851697 424673280000 134217656 134217728 1850 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz188)) Bool.true 16777207 16777216 5851697 424673280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz188) qz188) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz188)) Bool.true 16777207 16777216 374508608 27179089920000 16777207 16777216 5851697 424673280000 (Ns240p1551 rfl rfl) rfl)) rfl) (Ns240p1552 rfl) RS241to252.d7 

noncomputable def Ns240p1554 := nat_lit 6717301672507595779567245806595474328020075422063332741160662379041 

noncomputable def Ns240p1555 := nat_lit 151800237066666008978144835359544342264882158762728913160022561 

noncomputable def Ns240p1556 := nat_lit 20151601417048654006683781130115703895375696501872472765655667092001 

noncomputable def Ns240p1557 := BSN.cos_dyadic_bound_f 59246003 134217728 3 2 134217728 67108864 Ns240p1554 Ns240p124 Ns240p1555 Ns240p1556 Ns240p127 Ns240p1555 121352575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 59246003) qz367 0 2 Ns240p1554 Ns240p124 Ns240p1555 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 59246003) qz368 0 2 Ns240p1556 Ns240p127 Ns240p1555 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1558 := nat_lit 17751825806575176387373987441 

noncomputable def Ns240p1559 := BSN.cos_dyadic_bound_f 11542789 134217728 2 1 134217728 67108864 Ns240p1558 Ns240p146 Ns240p1558 Ns240p1558 Ns240p147 Ns240p1558 133721691 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 11542789) qz367 0 1 Ns240p1558 Ns240p146 Ns240p1558 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 11542789) qz368 0 1 Ns240p1558 Ns240p147 Ns240p1558 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1560 := nat_lit 107981918516839624430942597084154837824296249463470797400357365596416 

noncomputable def Ns240p1561 := nat_lit 39200271408260845322975220539167378437798701435975785864149319936 

noncomputable def Ns240p1562 := nat_lit 323867355007702351602181840811386178716013150987540440629343798149376 

noncomputable def Ns240p1563 := BSN.cos_dyadic_bound_f 118620878 134217728 3 2 134217728 67108864 Ns240p1560 Ns240p124 Ns240p1561 Ns240p1562 Ns240p127 Ns240p1561 85123844 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 118620878) qz367 0 2 Ns240p1560 Ns240p124 Ns240p1561 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 118620878) qz368 0 2 Ns240p1562 Ns240p127 Ns240p1561 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1564 := nat_lit 45110677679624708610278513007726918872557917546325276321286254272385 

noncomputable def Ns240p1565 := nat_lit 2112882674658660382075755517815499166872909604822623339942289281 

noncomputable def Ns240p1566 := nat_lit 118143592112781932338682268558922610048524370767682201356056473673601 

noncomputable def Ns240p1567 := BSN.sin_dyadic_bound_f 82339727 134217728 3 2 134217728 67108864 Ns240p1564 Ns240p248 Ns240p1565 Ns240p1566 Ns240p251 Ns240p1565 77271207 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 82339727) qz365 0 2 Ns240p1564 Ns240p248 Ns240p1565 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 82339727) qz366 0 2 Ns240p1566 Ns240p251 Ns240p1565 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1568 := Ns240p1521 56837 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 118 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 85123844 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 77271207 134217728) qz193 rfl rfl (Ns240p1553 RS241to252.d9 RS241to252.d11 RS241to252.d13 RS241to252.d17 (Ns240p1557 rfl rfl) (Ns240p1559 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns240p1552 rfl) RS241to252.d19 RS241to252.d21 RS241to252.d23 RS241to252.d25 RS241to252.d17 (Ns240p1563 rfl rfl) (Ns240p1567 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns240p1569 := nat_lit 376176940939514551935105415440463044943599120151990916186862423466240 

noncomputable def Ns240p1570 := nat_lit 146825881903398394658371880667866649132565998362287373134159503616 

noncomputable def Ns240p1571 := nat_lit 984987603413742133857733962156321905039402112591199172361470088929536 

noncomputable def Ns240p1572 := BSN.sin_dyadic_bound_f 139910506 134217728 3 2 134217728 67108864 Ns240p1569 Ns240p248 Ns240p1570 Ns240p1571 Ns240p251 Ns240p1570 115913648 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 139910506) qz365 0 2 Ns240p1569 Ns240p248 Ns240p1570 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 139910506) qz366 0 2 Ns240p1571 Ns240p251 Ns240p1570 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1573 := nat_lit 3767873466651953989517884615380790780098024446580073064372779988879190818164680787575019167567257163268096 

noncomputable def Ns240p1574 := nat_lit 5704395042488472017742126552258446927778180449140251467516357300662562546823416213959295067662319616 

noncomputable def Ns240p1575 := nat_lit 22808623498367609888436394598670590502245436756997132534924703476913295891547999395272389487740251076034560 

noncomputable def Ns240p1576 := BSN.cos_dyadic_bound_f 205597328 134217728 4 3 134217728 67108864 Ns240p1573 Ns240p130 Ns240p1574 Ns240p1575 Ns240p133 Ns240p1574 5230061 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 205597328) qz367 0 3 Ns240p1573 Ns240p130 Ns240p1574 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 205597328) qz368 0 3 Ns240p1575 Ns240p133 Ns240p1574 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1577 := Ns240p1519 76211 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 21 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 115913648 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 74 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 5230061 134217728) qz193 rfl rfl (Ns240p1568 rfl rfl) (Ns240p1552 rfl) RS241to252.d27 RS241to252.d29 RS241to252.d31 RS241to252.d33 RS241to252.d17 (Ns240p1572 rfl rfl) (Ns240p1576 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p1578 := nat_lit 1163245167312353815973696714161 

noncomputable def Ns240p1579 := BSN.sin_dyadic_bound_f 32841109 134217728 2 1 134217728 67108864 Ns240p1578 Ns240p114 Ns240p1578 Ns240p1578 Ns240p115 Ns240p1578 32514384 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 32841109) qz365 0 1 Ns240p1578 Ns240p114 Ns240p1578 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 32841109) qz366 0 1 Ns240p1578 Ns240p115 Ns240p1578 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1580 := nat_lit 6779295936619580143167743718297255843085768156476405941920647414120734214518256105523356613397079654400000 

noncomputable def Ns240p1581 := nat_lit 1901845076528305454143680471452675258900734227978045156098901138556345441991488297762816000000000000 

noncomputable def Ns240p1582 := nat_lit 33870050433653750693091472632563884849550754555331073219628997875321572659010946686778938964702134272000000 

noncomputable def Ns240p1583 := BSN.sin_dyadic_bound_f 187613720 134217728 4 3 134217728 67108864 Ns240p1580 Ns240p118 Ns240p1581 Ns240p1582 Ns240p121 Ns240p1581 132215035 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 187613720) qz365 0 3 Ns240p1580 Ns240p118 Ns240p1581 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 187613720) qz366 0 3 Ns240p1582 Ns240p121 Ns240p1581 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1584 := Ns240p1517 93140 BSN.abs_quadSignNeg qz642 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 32514384 134217728) BSN.abs_quadSignNeg qz662 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132215035 134217728) qz193 rfl rfl (Ns240p1577 rfl) (Ns240p1552 rfl) RS241to252.d35 RS241to252.d37 RS241to252.d39 RS241to252.d41 RS241to252.d17 (Ns240p1579 rfl rfl) (Ns240p1583 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p1585 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) 479215355 134217728 93140 134217728 479215355 134217728 93140 134217728 128638392341626880 479215355 67108864 23285 16777216 (Ns240p1584 rfl) 

noncomputable def Ns240p1586 := nat_lit 81311747466095823694713214991231575246752003078864874479752117290022083247002463260429528227077845619562047065616470408800003603993 

noncomputable def Ns240p1587 := nat_lit 177450860423732151013018507785157357019931972824052260810910693159335763699560039874558361990664932998233037501529828597054346100736 

noncomputable def Ns240p1588 := nat_lit 15238174522172058923048629722924928272298974731143912451777124596609114358418789345630677006883825582888676990739653838360092101705207991249014977561465263747933303892181332169 

noncomputable def Ns240p1589 := @Enclosure.Real.IsNear.mulLit_tf qz189 qz521 5501941 16777216 1 16777216 Ns240p1586 Ns240p1587 Ns240p1588 

noncomputable def Ns240p1590 := nat_lit 181769458116476375234833206161982832154386994076696418773099904470883251944151467921359453756617139349530513765595873280000000000000000000000000000000000000000000000000000000000000 

noncomputable abbrev qz196 := (@HPow.hPow Real Real Real qz444 qz518 qz347)

noncomputable def Ns240p1591 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz196 1 1 0 1 5501941 16777216 1 16777216 5501941 16777216 1 16777216 

noncomputable abbrev qz197 := qz518

noncomputable def Ns240p1592 := @Enclosure.Real.IsNear.sqrt_image qz197 290112060873 3355443200 108649 3355443200 78000567 78000598 8388608 (@Enclosure.Real.IsNear.of_eq qz197 (@HMul.hMul Real Real Real qz5 qz188 qz3) Bool.false 290112060873 3355443200 108649 3355443200 (BSN.t_div_two_pi_mk qz188 543245 1000 qz193) (@Enclosure.Real.IsNear.mulLit_ff qz188 qz3 543245 1000 0 1 2670177 16777216 1 16777216 290112060873 3355443200 108649 3355443200 (Enclosure.Real.IsNear.const Bool.false 543245 1000) RS241to252.d44 rfl)) 

noncomputable abbrev qz525 := (@Enclosure.Real.IsNear.recentre' qz192 Bool.false 156001165 16777216 31 16777216 156001165 16777216 31 16777216 (Ns240p1592 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns240p1593 := @Enclosure.Real.IsNear.sqrt_image qz192 156001165 16777216 31 16777216 25579604 25579610 8388608 qz525 rfl 

noncomputable def Ns240p1594 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz192) 25579607 8388608 3 8388608 2750970 2750971 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz192) Bool.false 51159214 16777216 6 16777216 25579607 8388608 3 8388608 (Ns240p1593 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns240p1595 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz192)) Bool.false 5501941 16777216 1 16777216 5501941 16777216 1 16777216 (Ns240p1594 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns240p1596 := nat_lit 181035916619146733444163787205843635911599763485015392320418786831212114943022583099785076260506311674304068725316107869310860825 

noncomputable def Ns240p1597 := nat_lit 430727165323394666275221285394845580550034117834801785069010526325760212771568862266992002449996892238781237280482510360092101705207991249014977561465263747933303892181332169 

noncomputable abbrev qz526 := (@HMul.hMul Real Real Real qz5 qz719 (@Inv.inv Real Real.instInv qz192))

noncomputable def Ns240p1598 := @Enclosure.Real.IsNear.addLit_ff qz190 qz526 64345320978939 140737488355328 580408972083473 7124835347988480000 Ns240p1596 Ns240p1587 Ns240p1597 Ns240p1590 

noncomputable def Ns240p1599 := nat_lit 11443611112161031997717713600064931182915190241565604075722517969220435793138977005076032869105932978820082892460376276492214799035009270183624704 

noncomputable abbrev qz855 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 543245 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1)))

noncomputable abbrev qz724 := (Real.cos qz855)

noncomputable abbrev qz527 := qz724

noncomputable abbrev qz198 := (@Inv.inv Real Real.instInv qz527)

noncomputable abbrev qz725 := (@HSub.hSub Real Real Real qz814 (@HMul.hMul Real Real Real qz811 qz853 qz853) qz853)

noncomputable abbrev qz528 := (@HMul.hMul Real Real Real qz615 qz613 (@HSub.hSub Real Real Real qz619 qz725 qz626))

noncomputable abbrev qz199 := (Real.cos qz528)

noncomputable def Ns240p1600 := @Enclosure.Real.IsNear.of_eq qz190 (@HMul.hMul Real Real Real qz5 qz198 qz199) Bool.false 64345320978939 

noncomputable def Ns240p1601 := @Enclosure.Real.IsNear.mulLit_tt qz198 qz199 56035239 16777216 2245 

noncomputable abbrev qz200 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz527))

noncomputable abbrev qz201 := qz527

noncomputable def Ns240p1602 := @Enclosure.Real.IsNear.of_eq qz198 (@Neg.neg Real Real.instNeg qz200) Bool.true 56035239 16777216 2245 16777216 (BSN.inv_eq_neg_inv_neg qz201) 

noncomputable def Ns240p1603 := @Enclosure.Real.IsNear.recentre' qz200 Bool.false 56035239 16777216 2245 16777216 56035239 16777216 

noncomputable def Ns240p1604 := @Enclosure.Real.IsNear.recentre' qz201 Bool.true 2511589 8388608 162954304 13589544960000 2511589 8388608 2546161 212336640000 

noncomputable abbrev qz726 := qz855

noncomputable abbrev qz529 := qz726

noncomputable abbrev qz202 := qz529

noncomputable def Ns240p1605 := @Enclosure.Real.IsNear.cos_image qz202 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15727507) qz406) Bool.false 15727507 8388608 49 4194304 Bool.true 2511589 8388608 1 

noncomputable def Ns240p1606 := nat_lit 836568337723368520053334809 

noncomputable def Ns240p1607 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz191 884279719003555 140737488355328 1 500000000000000 5006221 16777216 31 16777216 4426899699149696115655 2361183241434822606848 Ns240p1606 

noncomputable def Ns240p1608 := @Enclosure.Real.IsNear.subLit_ff_p qz192 qz1 156001165 16777216 31 16777216 9 1 0 1 5006221 5006221 16777216 31 

noncomputable def Ns240p1609 := @Ns240p1608 16777216 qz525 qz373 

noncomputable def Ns240p1610 := @Enclosure.Real.IsNear.recentre' qz202 Bool.false 4426899699149696115655 2361183241434822606848 Ns240p1606 Ns240p281 15727507 8388608 49 4194304 (@Ns240p1607 Ns240p281 RS241to252.d43 (Ns240p1609 rfl rfl) rfl) 

noncomputable def Ns240p1611 := nat_lit 30162701050392073561786310018093657483588195331635239483420160948878235196413691713864620081 

noncomputable def Ns240p1612 := nat_lit 229043855643314676056146047818013082723864346634627720333442810753173019784799760177201 

noncomputable def Ns240p1613 := nat_lit 182095228315632633219390761459128220557298981560180473985569500978135897846050771956852873265 

noncomputable def Ns240p1614 := BSN.cos_dyadic_bound_t 15727507 8388608 4 3 8388608 3240000 Ns240p1611 Ns240p426 Ns240p1612 Ns240p1613 Ns240p429 Ns240p1612 2511589 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 15727507) (BSN.cosEvenQ 8388608) 0 3 Ns240p1611 Ns240p426 Ns240p1612 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 15727507) (BSN.cosOddQ 8388608) 0 3 Ns240p1613 Ns240p429 Ns240p1612 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz203 := (@Neg.neg Real Real.instNeg qz527)

noncomputable def Ns240p1615 := @Enclosure.Real.IsNear.inv_image qz203 2511589 8388608 2546161 212336640000 28016497 28018742 8388608 (@Enclosure.Real.IsNear.neg qz201 Bool.true 2511589 8388608 2546161 212336640000 (Ns240p1604 (@Ns240p1605 3240000 (Ns240p1610 rfl) (Enclosure.sfrac_false_div 15727507 8388608) (Ns240p1614 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns240p1616 := Ns240p1602 (@Enclosure.Real.IsNear.neg qz200 Bool.false 56035239 16777216 2245 16777216 (@Ns240p1603 2245 16777216 (Ns240p1615 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p1617 := @Enclosure.Real.IsNear.recentre' qz199 Bool.true 1148301 8388608 

noncomputable abbrev qz204 := qz528

noncomputable def Ns240p1618 := @Enclosure.Real.IsNear.cos_image qz204 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 28657423)) qz363) Bool.true 28657423 16777216 

noncomputable def Ns240p1619 := nat_lit 67665427556207019449386325605 

noncomputable def Ns240p1620 := nat_lit 4482281118872255169553701772129053 

noncomputable def Ns240p1621 := @Enclosure.Real.IsNear.recentre' qz204 Bool.true Ns240p1619 Ns240p294 Ns240p1620 

noncomputable def Ns240p1622 := nat_lit 241785163922925834941235200000000000000 

noncomputable abbrev qz530 := (@HSub.hSub Real Real Real qz619 qz725 qz626)

noncomputable abbrev qz205 := qz530

noncomputable def Ns240p1623 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz205 884279719003555 140737488355328 1 500000000000000 76520388404311 

noncomputable abbrev qz531 := qz725

noncomputable abbrev qz206 := qz531

noncomputable def Ns240p1624 := @Enclosure.Real.IsNear.subLit_tf qz206 qz27 58928202359895 281474976710656 830480359 281474976710656 1 16 

noncomputable abbrev qz727 := (@HMul.hMul Real Real Real qz811 qz853 qz853)

noncomputable abbrev qz532 := qz727

noncomputable abbrev qz207 := qz532

noncomputable def Ns240p1625 := @Enclosure.Real.IsNear.subLit_ff_n qz207 qz191 25062248700841 281474976710656 310386663 281474976710656 5006221 16777216 31 16777216 

noncomputable def Ns240p1626 := @Enclosure.Real.IsNear.mulLit_ff qz191 qz191 5006221 16777216 31 16777216 5006221 16777216 31 16777216 25062248700841 281474976710656 

noncomputable def Ns240p1627 := nat_lit 84923924081414554978117848809128390587970516939191239284771851675098046455506190875576791854401 

noncomputable def Ns240p1628 := nat_lit 306793115721128431484613879542168390913828217502808063494393870708197338795141203281177921 

noncomputable def Ns240p1629 := nat_lit 513471967485881079644409158258900226964736083648861651194424014563166061275681671153341318688065 

noncomputable def Ns240p1630 := BSN.cos_dyadic_bound_t 28657423 16777216 4 3 8388608 3240000 Ns240p1627 Ns240p303 Ns240p1628 Ns240p1629 Ns240p306 Ns240p1628 1148301 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 28657423) qz627 0 3 Ns240p1627 Ns240p303 Ns240p1628 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 28657423) (BSN.cosOddQ 16777216) 0 3 Ns240p1629 Ns240p306 Ns240p1628 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1631 := @Ns240p1617 128457152 6794772480000 1148301 8388608 2007143 106168320000 (@Ns240p1618 39 2097152 Bool.true 1148301 8388608 1 3240000 (@Ns240p1621 Ns240p1622 28657423 16777216 39 2097152 (@Ns240p1623 281474976710656 830480359 281474976710656 Ns240p1619 Ns240p294 Ns240p1620 Ns240p1622 RS241to252.d43 (@Ns240p1624 0 1 1224326214468976 76520388404311 281474976710656 830480359 281474976710656 (@Ns240p1625 988651179483668152320 58928202359895 281474976710656 830480359 281474976710656 (@Ns240p1626 310386663 281474976710656 (Ns240p1609 rfl rfl) (Ns240p1609 rfl rfl) rfl) (Ns240p1609 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 28657423 16777216) (BSN.cos_neg_of_bound 28657423 16777216 Bool.true 1148301 8388608 1 3240000 (Ns240p1630 rfl rfl)) rfl rfl) 

noncomputable def Ns240p1632 := nat_lit 100335095196424751938363126134902112832751170935982499888001021347854898203927247157109146949839806992636016436902082881025 

noncomputable def Ns240p1633 := nat_lit 10576895500643977583230644928524336637254474927428499508554380724390492659780981533203027367035444557561459392400373732868096 

noncomputable def Ns240p1634 := nat_lit 1431982642887541588907278310555402671429707500703291059901358249534300082612493800490954475028420599198070383796887258358751190295169776417147096423945322298671206357051 

noncomputable def Ns240p1635 := nat_lit 65005823892286911690771534262412607248206255701790959396278824020940036276871490927228732260447909599374716436480000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns240p1636 := @Enclosure.Real.IsNear.mulLit_ff qz719 (@Inv.inv Real Real.instInv qz192) Ns240p1632 Ns240p1633 Ns240p1634 Ns240p1635 1804313 16777216 1 16777216 Ns240p1596 

noncomputable def Ns240p1637 := nat_lit 22134207978725227003280833414383286605844513140756420676399448525491629600739118192413147433482131498410890994374425 

noncomputable def Ns240p1638 := nat_lit 2462625387274654950767440006258975862817483704404090416746768337765357610718575663213391640930307227550414249394176 

noncomputable def Ns240p1639 := nat_lit 631738745209604300921310901295964681220249007658371210976636818015210600391575651217202680064654341724891831920906166122169924897902446138047703231747357510672503 

noncomputable def Ns240p1640 := nat_lit 30270695636182516669282472814625411875642023841753117459024686376070620621029050521193413185164290293760000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns240p1641 := @Enclosure.Real.IsNear.mulLit_tf (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz191) qz462 Ns240p1637 Ns240p1638 Ns240p1639 Ns240p1640 4533033 4294967296 1 4294967296 Ns240p1632 

noncomputable abbrev qz856 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 543245 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1)))

noncomputable abbrev qz728 := (@HMul.hMul Real Real Real qz811 qz809 (@HSub.hSub Real Real Real qz814 qz856 qz844))

noncomputable abbrev qz533 := (@HMul.hMul Real Real Real qz615 qz728 qz728)

noncomputable abbrev qz534 := qz728

noncomputable abbrev qz208 := (@HMul.hMul Real Real Real qz344 qz533 qz534)

noncomputable abbrev qz209 := (Real.sin qz528)

noncomputable abbrev qz210 := (@HMul.hMul Real Real Real qz344 qz320 qz534)

noncomputable def Ns240p1642 := @HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 qz208 qz209) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz210 qz129) qz199) 

noncomputable abbrev qz729 := (Real.sin qz855)

noncomputable abbrev qz535 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz615 qz613 qz729))

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz344 qz320 qz535)

noncomputable abbrev qz536 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz615 qz688 qz724))

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz344 qz320 qz536)

noncomputable abbrev qz537 := qz729

noncomputable abbrev qz213 := qz537

noncomputable def Ns240p1643 := @HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns240p1642 (@HMul.hMul Real Real Real qz5 qz211 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz191))) (@HMul.hMul Real Real Real qz5 qz212 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz191))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz470 qz213) qz190) 

noncomputable abbrev qz214 := (BSN.cos_two_pi_p_ne_zero_mk qz517 543245 1000 9 qz522 rfl rfl (@BSN.floor_sqrt_eq_dec qz517 543245 1000 9 qz522 rfl rfl rfl))

noncomputable def Ns240p1644 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz191) (@HMul.hMul Real Real Real qz5 qz198 Ns240p1643) Bool.true Ns240p1637 Ns240p1638 Ns240p1639 Ns240p1640 (BSN.iteratedDeriv_three_correction_mk qz191 qz214) 

noncomputable def Ns240p1645 := nat_lit 12343848461088723686398359158686019842249649326241823154273467258353410902030317847889587521141928840197475 

noncomputable def Ns240p1646 := nat_lit 4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220251373109248 

noncomputable def Ns240p1647 := nat_lit 264214657645519104328564890886094979896110588570619663765592625479487300579270486238372946283962902862847937666624364328258378357861141088139619921883789 

noncomputable def Ns240p1648 := @Enclosure.Real.IsNear.mulLit_tf qz198 Ns240p1643 1793136723 536870912 1089 2147483648 Ns240p1645 Ns240p1646 Ns240p1647 

noncomputable def Ns240p1649 := nat_lit 42287673292936547662991759573983138253412242757742922928684418615052412200294039940266050191360000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns240p1650 := @Enclosure.Real.IsNear.of_eq qz198 (@Neg.neg Real Real.instNeg qz200) Bool.true 1793136723 536870912 1089 2147483648 (BSN.inv_eq_neg_inv_neg qz201) 

noncomputable def Ns240p1651 := @Enclosure.Real.IsNear.recentre' qz200 Bool.false 14345093784 4294967296 2178 4294967296 1793136723 536870912 

noncomputable def Ns240p1652 := @Enclosure.Real.IsNear.recentre' qz201 Bool.true 642963523 2147483648 80944283648 1781208836997120000 642963523 2147483648 4940447 108716359680000 

noncomputable abbrev qz730 := (@Nat.cast Real Real.instNatCast 1073741824)

noncomputable def Ns240p1653 := @Enclosure.Real.IsNear.cos_image qz202 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2013119299) qz730) Bool.false 2013119299 1073741824 95 2147483648 Bool.true 642963523 2147483648 1 

noncomputable def Ns240p1654 := nat_lit 80958227328010895181496661 

noncomputable def Ns240p1655 := nat_lit 1844674407370955161600000000000000 

noncomputable def Ns240p1656 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz191 884279719003555 140737488355328 1 500000000000000 640795775 2147483648 15 2147483648 566642707855665253980125 302231454903657293676544 Ns240p1654 

noncomputable def Ns240p1657 := @Enclosure.Real.IsNear.subLit_ff_p qz192 qz1 19968148607 2147483648 15 2147483648 9 1 0 1 640795775 640795775 2147483648 15 

noncomputable def Ns240p1658 := @Enclosure.Real.IsNear.sqrt_image qz197 2970747342539 34359738368 108649 858993459200 19968148592 19968148622 2147483648 (@Enclosure.Real.IsNear.of_eq qz197 (@HMul.hMul Real Real Real qz5 qz188 qz3) Bool.false 2970747342539 34359738368 108649 858993459200 (BSN.t_div_two_pi_mk qz188 543245 1000 qz193) (@Enclosure.Real.IsNear.mulLit_ff qz188 qz3 543245 1000 0 1 683565275 4294967296 1 4294967296 2970747342539 34359738368 108649 858993459200 (Enclosure.Real.IsNear.const Bool.false 543245 1000) RS241to252.d69 rfl)) 

noncomputable def Ns240p1659 := @Ns240p1657 2147483648 (@Enclosure.Real.IsNear.recentre' qz192 Bool.false 39936297214 4294967296 30 4294967296 19968148607 2147483648 15 2147483648 (Ns240p1658 rfl rfl rfl rfl rfl rfl) rfl) qz373 

noncomputable def Ns240p1660 := @Enclosure.Real.IsNear.recentre' qz202 Bool.false 566642707855665253980125 302231454903657293676544 Ns240p1654 Ns240p1655 2013119299 1073741824 95 2147483648 (@Ns240p1656 Ns240p1655 RS241to252.d68 (Ns240p1659 rfl rfl) rfl) 

noncomputable def Ns240p1661 := nat_lit 33874320138715838950004614099594309520595868696732970881725635228506900137495567336463821421501022652942487752751704199066418083650363667485775234032958313281 

noncomputable def Ns240p1662 := nat_lit 65315689001430101463437438788805272313419085489526239767007691747054552085219169171183189876641515636152014546297038989853108186772682866843307077206540288000 

noncomputable def Ns240p1663 := nat_lit 72763268038450273896142465456745611017374337741693912829340524733185679195520986371391465564410967888319950445747320215981956995820531926041768891201 

noncomputable def Ns240p1664 := nat_lit 343834117299819530538485073964433518145828186195049179748541036775509296234890121991828124670851429697695784748260126122529227965889315270393251147492661793601 

noncomputable def Ns240p1665 := nat_lit 9993300417218805523905928134687206663953120079897514684352176837299346469038532883191028051126151892331258225583446965447525552576220478627025982812600664064000 

noncomputable def Ns240p1666 := BSN.cos_dyadic_bound_t 2013119299 1073741824 5 4 2147483648 829440000 Ns240p1661 Ns240p1662 Ns240p1663 Ns240p1664 Ns240p1665 Ns240p1663 642963523 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 2013119299) (BSN.cosEvenQ 1073741824) 0 4 Ns240p1661 Ns240p1662 Ns240p1663 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 2013119299) (BSN.cosOddQ 1073741824) 0 4 Ns240p1664 Ns240p1665 Ns240p1663 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz538 := (Ns240p1652 (@Ns240p1653 829440000 (Ns240p1660 rfl) (Enclosure.sfrac_false_div 2013119299 1073741824) (Ns240p1666 rfl rfl) rfl rfl) rfl)

noncomputable def Ns240p1667 := @Enclosure.Real.IsNear.inv_image qz203 642963523 2147483648 4940447 108716359680000 7172545803 7172547981 2147483648 (@Enclosure.Real.IsNear.neg qz201 Bool.true 642963523 2147483648 4940447 108716359680000 qz538) 

noncomputable def Ns240p1668 := Ns240p1650 (@Enclosure.Real.IsNear.neg qz200 Bool.false 1793136723 536870912 1089 2147483648 (@Ns240p1651 1089 2147483648 (Ns240p1667 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p1669 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns240p1642 (@HMul.hMul Real Real Real qz5 qz211 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz191))) (@HMul.hMul Real Real Real qz5 qz212 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz191))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz470 qz213) qz190) 

noncomputable def Ns240p1670 := nat_lit 508686154545999909561528835014753485309062911748929907696304603661520558275028130122236522640827477347333475 

noncomputable def Ns240p1671 := nat_lit 260911235657877529076691480569041175592240482775643475753103269280835348479750690488357779577759031535394301460880124378473546679853184136503242321883789 

noncomputable def Ns240p1672 := nat_lit 746812898402457340439082439814264567769121763122761524618676308535887625 

noncomputable def Ns240p1673 := nat_lit 6901746346790563787434755862277025452451108972170386555162524223799296 

noncomputable def Ns240p1674 := nat_lit 6545431404265546448868932761618654363736460824322417794030138279076628218090579335820405056397056776161073 

noncomputable def Ns240p1675 := nat_lit 83789193696842473330742623709443154614354561505388448972800000000000000000000000000000000000000000000000000000 

noncomputable def Ns240p1676 := nat_lit 85194111021655421475322509245890120544287932642273379239716863561294701333698059058105450031446554516344802596045277119127547098764330355451210481592937089721669945191405977600 

noncomputable def Ns240p1677 := nat_lit 383035410660487270460626888682690386394558462018590673549458858900740620505610079263666915040031986371589475 

noncomputable def Ns240p1678 := @Enclosure.Real.IsNear.subLit_ft (@HSub.hSub Real Real Real qz11 Ns240p1642 (@HMul.hMul Real Real Real qz5 qz211 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 2 Zeta.RiemannSiegel.correction qz191))) (@HMul.hMul Real Real Real qz5 qz212 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz191)) Ns240p1677 Ns240p1646 

noncomputable def Ns240p1679 := nat_lit 249306317794497779328548746668192982701824238227102469071229704958456757670252708176328692364303315249830850460811718502451682153696281580036157665243789 

noncomputable def Ns240p1680 := nat_lit 217969295192148025503041987187389896323167718054819645250804156720557283893575322671359875 

noncomputable def Ns240p1681 := nat_lit 7957171782556586274486115970349133441607298412757563479047423630290551952200534008528896 

noncomputable def Ns240p1682 := nat_lit 596483657907776617088757045655662110992844926704838693728971487905964970492650986565179624565565658170098729255923152787151820837 

noncomputable def Ns240p1683 := nat_lit 2173553173502058672449252794195179071689522846387675497044223428752664690688000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns240p1684 := nat_lit 4047703115130649232978975953646216298502891227422632991920128554917445919810190850582376870869377769279161046264172470706823912380404166212375486247564918568284365361796059503826279313413085593600 

noncomputable def Ns240p1685 := nat_lit 22481878601331726055530941425950869562763209277660613899465260552829610523512025 

noncomputable def Ns240p1686 := nat_lit 107919172345504075961665581931329250149699929584404111643926498707168030078068887635306903492916367477396883059 

noncomputable def Ns240p1687 := nat_lit 10662869531441415153164200302971631272288128409305597514498986475520000000000000000000000000000000000000000000000000 

noncomputable def Ns240p1688 := @Enclosure.Real.IsNear.subLit_ft Ns240p1642 (@HMul.hMul Real Real Real qz5 qz211 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 2 Zeta.RiemannSiegel.correction qz191)) Ns240p1685 Ns240p1424 Ns240p1686 Ns240p1687 

noncomputable def Ns240p1689 := nat_lit 369119801821016396910317850586363742437315137656135925490463466581201193440810324872915487688547069755192675 

noncomputable def Ns240p1690 := nat_lit 248878323183034698691985997424712220355544482699373673510438759027330968656502092599321468333658510625721672624532669690601146601356805624324157665243789 

noncomputable def Ns240p1691 := nat_lit 2838558108944076619199740271901498790338215893115248404514299266536330227112203728394964765407128061013722769050776906711541159278528603906448084943882891252832712874940075610032465510400 

noncomputable def Ns240p1692 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 qz208 qz209) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz210 qz129) qz199) 

noncomputable def Ns240p1693 := nat_lit 119369301610603332222700687154541407952624596811029041232911986705678056428817625 

noncomputable def Ns240p1694 := nat_lit 30252682649398579202886265479982669236336069251557455839572469308344328436078270640117715818804367477396883059 

noncomputable def Ns240p1695 := nat_lit 298557422732910495753148734327675558170035420725 

noncomputable def Ns240p1696 := nat_lit 22835963083295358096932575511191922182123945984 

noncomputable def Ns240p1697 := nat_lit 2614103780992348512270204072674045212832819761887219373699303400737 

noncomputable def Ns240p1698 := nat_lit 358891558861927285684027906275693035520000000000000000000000000000000000 

noncomputable def Ns240p1699 := nat_lit 513395349783139175719932317468596315541827385971294526389146887633813384508587690177984841913310488147939215201912003074457600 

noncomputable def Ns240p1700 := nat_lit 56113884741000878508597492662181193454215136498584319651291560188714875 

noncomputable def Ns240p1701 := nat_lit 3450873173395281893717377931138512726225554486085193277581262111899648 

noncomputable def Ns240p1702 := @Enclosure.Real.IsNear.mulLit_tt qz208 qz209 Ns240p1700 Ns240p1701 

noncomputable def Ns240p1703 := nat_lit 165767460015029398576126784262480046796462019669338879266185457174274874151442559020609098782697 

noncomputable def Ns240p1704 := nat_lit 98079714615416886934934209737619787751599303819750539264000000000000000000000000000000000000000000000 

noncomputable def Ns240p1705 := nat_lit 146570608381816219430753498597688246021755598025 

noncomputable def Ns240p1706 := nat_lit 9458766534205519712997031279935829241251165080770689292867919 

noncomputable def Ns240p1707 := nat_lit 21267647932558653966460912964485513216000000000000000000000000000000 

noncomputable abbrev qz215 := qz533

noncomputable abbrev qz216 := qz534

noncomputable def Ns240p1708 := @Enclosure.Real.IsNear.mulLit_ft qz215 qz216 Ns240p1705 Ns240p1696 Ns240p1706 Ns240p1707 

noncomputable def Ns240p1709 := nat_lit 404791134854638924602361513 

noncomputable def Ns240p1710 := nat_lit 4611686018427387904000000000000000 

noncomputable def Ns240p1711 := @Enclosure.Real.IsNear.mulLit_tt qz216 qz216 382845410553419354204195 151115727451828646838272 Ns240p1709 Ns240p1710 382845410553419354204195 151115727451828646838272 

noncomputable abbrev qz731 := (@HSub.hSub Real Real Real qz814 qz856 qz844)

noncomputable abbrev qz539 := qz731

noncomputable abbrev qz217 := qz539

noncomputable def Ns240p1712 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz217 884279719003555 140737488355328 1 500000000000000 432946049 1073741824 15 1073741824 

noncomputable abbrev qz732 := qz856

noncomputable abbrev qz540 := qz732

noncomputable abbrev qz218 := qz540

noncomputable def Ns240p1713 := @Enclosure.Real.IsNear.subLit_ff_n qz218 qz142 640795775 1073741824 15 1073741824 1 1 0 1 432946049 

noncomputable def Ns240p1714 := @Enclosure.Real.IsNear.mulLit_ff qz0 qz191 2 1 0 1 640795775 2147483648 15 2147483648 640795775 1073741824 15 

noncomputable def Ns240p1715 := @Enclosure.Real.IsNear.recentre' qz209 Bool.true 2127268539 2147483648 

noncomputable def Ns240p1716 := @Enclosure.Real.IsNear.sin_image qz204 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1834074439)) qz730) Bool.true 1834074439 1073741824 

noncomputable def Ns240p1717 := nat_lit 1108629972281737293859858591774045 

noncomputable def Ns240p1718 := nat_lit 649037107316853453566312041152512 

noncomputable def Ns240p1719 := nat_lit 1388059244988810040760956711216875413 

noncomputable def Ns240p1720 := @Enclosure.Real.IsNear.recentre' qz204 Bool.true Ns240p1717 Ns240p1718 Ns240p1719 

noncomputable def Ns240p1721 := nat_lit 19807040628566084398385987584000000000000000 

noncomputable def Ns240p1722 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz205 884279719003555 140737488355328 1 500000000000000 1253709599413848319 

noncomputable def Ns240p1723 := @Enclosure.Real.IsNear.subLit_tf qz206 qz27 965479223262136575 4611686018427387904 51436128195 4611686018427387904 1 16 

noncomputable def Ns240p1724 := @Enclosure.Real.IsNear.subLit_ff_n qz207 qz191 410619225257850625 4611686018427387904 19223873475 4611686018427387904 640795775 2147483648 15 2147483648 

noncomputable def Ns240p1725 := nat_lit 2073350844439179512355225600 

noncomputable def Ns240p1726 := @Enclosure.Real.IsNear.mulLit_ff qz191 qz191 640795775 2147483648 15 2147483648 640795775 2147483648 15 2147483648 410619225257850625 4611686018427387904 

noncomputable def Ns240p1727 := nat_lit 1040368781865151294754986226332228118213002973899981013774330243435691846545927146397756694102089502625136031099666721 

noncomputable def Ns240p1728 := nat_lit 14624423512618381205798935777403614887678544646249125127947611591383273469336389161304077707881121116968882159799500800 

noncomputable def Ns240p1729 := nat_lit 1448783526565491850459412426300211888588205393784640281380727017429879177049600359863783427656964163561751724321 

noncomputable def Ns240p1730 := nat_lit 5192811213571836855347484068675687713855492385856600009887627111615907679790932753552426497377279222903317656677794081 

noncomputable def Ns240p1731 := nat_lit 511854822941643342202962752209126521068749062618719379478166405698414571426773620645642719775839239093910875592982528000 

noncomputable def Ns240p1732 := BSN.sin_dyadic_bound_f 1834074439 1073741824 4 3 2147483648 829440000 Ns240p1727 Ns240p1728 Ns240p1729 Ns240p1730 Ns240p1731 Ns240p1729 2127268539 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 1834074439) (BSN.sinEvenQ 1073741824) 0 3 Ns240p1727 Ns240p1728 Ns240p1729 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 1834074439) (BSN.sinOddQ 1073741824) 0 3 Ns240p1730 Ns240p1731 Ns240p1729 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1733 := @Ns240p1715 127392923648 1781208836997120000 2127268539 2147483648 7775447 108716359680000 (@Ns240p1716 151 2147483648 Bool.true 2127268539 2147483648 1 829440000 (@Ns240p1720 Ns240p1721 1834074439 1073741824 151 2147483648 (@Ns240p1722 4611686018427387904 51436128195 4611686018427387904 Ns240p1717 Ns240p1718 Ns240p1719 Ns240p1721 RS241to252.d68 (@Ns240p1723 0 1 20059353590621573104 1253709599413848319 4611686018427387904 51436128195 4611686018427387904 (@Ns240p1724 Ns240p1725 965479223262136575 4611686018427387904 51436128195 4611686018427387904 (@Ns240p1726 19223873475 4611686018427387904 (Ns240p1659 rfl rfl) (Ns240p1659 rfl rfl) rfl) (Ns240p1659 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 1834074439 1073741824) (BSN.sin_neg_of_bound 1834074439 1073741824 Bool.false 2127268539 2147483648 1 829440000 (Ns240p1732 rfl rfl)) rfl rfl) 

noncomputable def Ns240p1734 := nat_lit 1015627296197934949378093287076202739675 

noncomputable def Ns240p1735 := nat_lit 10633823966279326983230456482242756608 

noncomputable def Ns240p1736 := nat_lit 32771172571381292360053774775338900137263581898301213 

noncomputable def Ns240p1737 := @Enclosure.Real.IsNear.mulLit_tt (@HMul.hMul Real Real Real qz5 qz210 qz129) qz199 Ns240p1734 Ns240p1735 Ns240p1736 

noncomputable def Ns240p1738 := nat_lit 9903520314283042199192993792000000000000000000000000000000 

noncomputable def Ns240p1739 := nat_lit 1214373404563916773807084539 

noncomputable def Ns240p1740 := @Enclosure.Real.IsNear.mulLit_tf qz210 qz129 1148536231660258062612585 151115727451828646838272 Ns240p1739 Ns240p1710 884279719003555 

noncomputable def Ns240p1741 := @Enclosure.Real.IsNear.mulLit_ft qz320 qz216 3 1 0 1 382845410553419354204195 151115727451828646838272 Ns240p1709 

noncomputable def Ns240p1742 := @Enclosure.Real.IsNear.recentre' qz199 Bool.true 293963567 2147483648 

noncomputable def Ns240p1743 := @Enclosure.Real.IsNear.cos_image qz204 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1834074439)) qz730) Bool.true 1834074439 1073741824 

noncomputable def Ns240p1744 := nat_lit 401041336229562745715775957808668849578666966767013570729412250177858722874460503847178488095981165802300400821748001 

noncomputable def Ns240p1745 := nat_lit 1124955654816798554292225829031047299052195742019163471380585507029482574564337627792621362144701624382221704599961600 

noncomputable def Ns240p1746 := nat_lit 2424799455982903371233584965163130263469894523166202402139088762873159299460442577175898942817331806635218792623784225 

noncomputable def Ns240p1747 := nat_lit 102370964588328668440592550441825304213749812523743875895633281139682914285354724129128543955167847818782175118596505600 

noncomputable def Ns240p1748 := BSN.cos_dyadic_bound_t 1834074439 1073741824 4 3 2147483648 829440000 Ns240p1744 Ns240p1745 Ns240p1729 Ns240p1746 Ns240p1747 Ns240p1729 293963567 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 1834074439) (BSN.cosEvenQ 1073741824) 0 3 Ns240p1744 Ns240p1745 Ns240p1729 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 1834074439) (BSN.cosOddQ 1073741824) 0 3 Ns240p1746 Ns240p1747 Ns240p1729 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1749 := @Ns240p1742 127392923648 1781208836997120000 293963567 2147483648 7775447 108716359680000 (@Ns240p1743 151 2147483648 Bool.true 293963567 2147483648 1 829440000 (@Ns240p1720 Ns240p1721 1834074439 1073741824 151 2147483648 (@Ns240p1722 4611686018427387904 51436128195 4611686018427387904 Ns240p1717 Ns240p1718 Ns240p1719 Ns240p1721 RS241to252.d68 (@Ns240p1723 0 1 20059353590621573104 1253709599413848319 4611686018427387904 51436128195 4611686018427387904 (@Ns240p1724 Ns240p1725 965479223262136575 4611686018427387904 51436128195 4611686018427387904 (@Ns240p1726 19223873475 4611686018427387904 (Ns240p1659 rfl rfl) (Ns240p1659 rfl rfl) rfl) (Ns240p1659 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 1834074439 1073741824) (BSN.cos_neg_of_bound 1834074439 1073741824 Bool.true 293963567 2147483648 1 829440000 (Ns240p1748 rfl rfl)) rfl rfl) 

noncomputable abbrev qz219 := (@Ns240p1712 382845410553419354204195 151115727451828646838272 Ns240p1709 Ns240p1710 RS241to252.d68 (@Ns240p1713 432946049 1073741824 15 1073741824 (@Ns240p1714 1073741824 qz341 (Ns240p1659 rfl rfl) rfl) qz509 rfl rfl) rfl)

noncomputable def Ns240p1750 := @Ns240p1692 Ns240p1693 Ns240p1424 Ns240p1694 Ns240p1687 Ns240p1695 Ns240p1696 Ns240p1697 Ns240p1698 Ns240p1699 Ns240p1685 Ns240p1424 Ns240p1686 Ns240p1687 (@Ns240p1702 Ns240p1703 Ns240p1704 2127268539 2147483648 7775447 108716359680000 Ns240p1693 Ns240p1424 Ns240p1694 Ns240p1687 (@Ns240p1708 382845410553419354204195 151115727451828646838272 Ns240p1709 Ns240p1710 Ns240p1700 Ns240p1701 Ns240p1703 Ns240p1704 (@Ns240p1711 Ns240p1709 Ns240p1710 Ns240p1705 Ns240p1696 Ns240p1706 Ns240p1707 qz219 qz219 rfl) qz219 rfl) (Ns240p1733 rfl) rfl) (@Ns240p1737 Ns240p1738 293963567 2147483648 7775447 108716359680000 Ns240p1695 Ns240p1696 Ns240p1697 Ns240p1698 (@Ns240p1740 70368744177664 1 250000000000000 Ns240p1734 Ns240p1735 Ns240p1736 Ns240p1738 (@Ns240p1741 Ns240p1710 1148536231660258062612585 151115727451828646838272 Ns240p1739 Ns240p1710 qz476 qz219 rfl) RS241to252.d70 rfl) (Ns240p1749 rfl) rfl) rfl rfl 

noncomputable def Ns240p1751 := nat_lit 5435591643752975947311615 

noncomputable def Ns240p1752 := nat_lit 133323276187412287503414365828249 

noncomputable def Ns240p1753 := nat_lit 155644403121924341760000000000000000000 

noncomputable def Ns240p1754 := nat_lit 67907934593511802470366906115873042882381250656931572481671579877759346146763558045 

noncomputable def Ns240p1755 := @Enclosure.Real.IsNear.mulLit_tf qz211 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz191) Ns240p1751 302231454903657293676544 Ns240p1752 Ns240p1753 Ns240p1754 

noncomputable def Ns240p1756 := nat_lit 15177100720513508366558296147058741458143803430094840009779784451085189728165691392 

noncomputable def Ns240p1757 := nat_lit 177702469321832715446948648777997543936512262644861482607033347992754609329796120366995657103411145397412215330797 

noncomputable def Ns240p1758 := nat_lit 543388293375514668112313198548794767922380711596918874261055857188166172672000000000000000000000000000000000000000000 

noncomputable def Ns240p1759 := nat_lit 1811863881250991982437205 

noncomputable abbrev qz220 := qz535

noncomputable def Ns240p1760 := @Enclosure.Real.IsNear.mulLit_ft qz320 qz220 3 1 0 1 Ns240p1759 302231454903657293676544 Ns240p1752 

noncomputable def Ns240p1761 := nat_lit 466933209365773025280000000000000000000 

noncomputable def Ns240p1762 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz213 884279719003555 140737488355328 1 500000000000000 2048971431 2147483648 4940447 108716359680000 Ns240p1759 

noncomputable def Ns240p1763 := @Enclosure.Real.IsNear.recentre' qz213 Bool.false 2048971431 2147483648 80944283648 1781208836997120000 2048971431 2147483648 4940447 108716359680000 

noncomputable def Ns240p1764 := @Enclosure.Real.IsNear.sin_image qz202 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2013119299) qz730) Bool.false 2013119299 1073741824 95 2147483648 Bool.false 2048971431 2147483648 1 

noncomputable def Ns240p1765 := nat_lit 1511987694616358753853189645187950903367250737544265469334672808969898970985836434852679329595592310554501675158108401 

noncomputable def Ns240p1766 := nat_lit 4430310319813608240601652726045150427255878747638327367139203729178936180298146582282363584030219134190946908401 

noncomputable def Ns240p1767 := nat_lit 7540903003624689933246942124631775391448329479036654205878010674077949029734187535164369859340942803481933722314373361 

noncomputable def Ns240p1768 := BSN.sin_dyadic_bound_f 2013119299 1073741824 4 3 2147483648 829440000 Ns240p1765 Ns240p1728 Ns240p1766 Ns240p1767 Ns240p1731 Ns240p1766 2048971431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 2013119299) (BSN.sinEvenQ 1073741824) 0 3 Ns240p1765 Ns240p1728 Ns240p1766 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 2013119299) (BSN.sinOddQ 1073741824) 0 3 Ns240p1767 Ns240p1731 Ns240p1766 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz541 := (@HMul.hMul Real Real Real qz615 qz613 qz729)

noncomputable abbrev qz221 := qz541

noncomputable abbrev qz542 := (@Enclosure.Real.IsNear.neg qz221 Bool.false Ns240p1759 302231454903657293676544 Ns240p1752 Ns240p1761 (@Ns240p1762 302231454903657293676544 Ns240p1752 Ns240p1761 RS241to252.d68 (Ns240p1763 (@Ns240p1764 829440000 (Ns240p1660 rfl) (Enclosure.sfrac_false_div 2013119299 1073741824) (Ns240p1768 rfl rfl) rfl rfl) rfl) rfl))

noncomputable def Ns240p1769 := @Ns240p1760 Ns240p1761 Ns240p1751 302231454903657293676544 Ns240p1752 Ns240p1753 qz476 qz542 rfl 

noncomputable abbrev qz222 := (@HMul.hMul Real Real Real qz344 qz533 (Real.cos qz528))

noncomputable def Ns240p1770 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz222) (@HMul.hMul Real Real Real qz5 qz129 qz209) 

noncomputable abbrev qz223 := (@HMul.hMul Real Real Real qz344 qz316 qz535)

noncomputable abbrev qz224 := (@HMul.hMul Real Real Real qz344 qz536 (Zeta.RiemannSiegel.correction qz519))

noncomputable def Ns240p1771 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz191) (@HMul.hMul Real Real Real qz5 qz198 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns240p1770 (@HMul.hMul Real Real Real qz5 qz223 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c8 1 Zeta.RiemannSiegel.correction qz191))) qz224)) 

noncomputable def Ns240p1772 := @Enclosure.Real.IsNear.mulLit_tt qz198 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns240p1770 (@HMul.hMul Real Real Real qz5 qz223 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 1 Zeta.RiemannSiegel.correction qz191))) qz224) 1793136723 

noncomputable def Ns240p1773 := nat_lit 37871029979185698976043393494135161316631654672175029947045248193134766415 

noncomputable def Ns240p1774 := nat_lit 28269553036454149273332760011886696253239742350009903329945699220681916416 

noncomputable def Ns240p1775 := nat_lit 74171685670113657813241877090590651204345096030263071939266931815535365445290438038033098898048264502861 

noncomputable def Ns240p1776 := nat_lit 759104676603592934243818556725226484130668516639041073053687611392000000000000000000000000000000000000000000 

noncomputable def Ns240p1777 := nat_lit 114900462594495282995922653349793973838664442037569357177140358135388395185 

noncomputable def Ns240p1778 := @Enclosure.Real.IsNear.subLit_ff_n (@HSub.hSub Real Real Real qz11 Ns240p1770 (@HMul.hMul Real Real Real qz5 qz223 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz191))) qz224 Ns240p1777 Ns240p1774 

noncomputable def Ns240p1779 := nat_lit 70782852469494737066400144228906769602286751082906786321087355585008331035701320723810763244356217142861 

noncomputable def Ns240p1780 := nat_lit 265016294627580844357691512096097145789908190570666862575 

noncomputable def Ns240p1781 := nat_lit 49039857307708443467467104868809893875799651909875269632 

noncomputable def Ns240p1782 := nat_lit 2721615050594103083728757610958039153895203231950176250125082804316410032533367 

noncomputable def Ns240p1783 := nat_lit 609646621864830910131732698278524582669739622400000000000000000000000000000000000000 

noncomputable def Ns240p1784 := nat_lit 1857189906275215341635229025301970077886532949872962962480567294419834537325126464163915090980716693317422498656377568161463009280 

noncomputable def Ns240p1785 := nat_lit 653538408360498992971252152955438013599361056681534648295 

noncomputable def Ns240p1786 := nat_lit 121488591096816100862557661006656048712608883510539158288945418156558536659 

noncomputable def Ns240p1787 := nat_lit 85634861562357592863497158166969708182964797440000000000000000000000000000000000 

noncomputable def Ns240p1788 := @Enclosure.Real.IsNear.subLit_ff_p Ns240p1770 (@HMul.hMul Real Real Real qz5 qz223 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz191)) Ns240p1785 Ns240p1781 Ns240p1786 Ns240p1787 

noncomputable def Ns240p1789 := nat_lit 261838779948179956994239042992341657947457970070692297082727807883133757775 

noncomputable def Ns240p1790 := nat_lit 69705924732670872352169715268665123571344202171334772873427525329686714918254182764276712624145017142861 

noncomputable def Ns240p1791 := nat_lit 5634702290223740163938649001989897463971824291844339155499145284881040265005496836584531734666090542561230202618641264995645521920 

noncomputable def Ns240p1792 := @Enclosure.Real.IsNear.subLit_ft (@Neg.neg Real Real.instNeg qz222) (@HMul.hMul Real Real Real qz5 qz129 qz209) 

noncomputable def Ns240p1793 := nat_lit 43086418857278793802319007945505934754528835197647155175 

noncomputable def Ns240p1794 := nat_lit 1202148176231981101690834902679444481683222848307330095211318290227080489793 

noncomputable def Ns240p1795 := nat_lit 2312141262183655007314423270508182120940049530880000000000000000000000000000000000 

noncomputable def Ns240p1796 := nat_lit 1881100425912022980656145 

noncomputable def Ns240p1797 := nat_lit 209828800006100862589745609033249 

noncomputable def Ns240p1798 := nat_lit 233466604682886512640000000000000000000 

noncomputable def Ns240p1799 := nat_lit 98759931997107058111980947725912803058941273599708143094298880512759471265546240 

noncomputable def Ns240p1800 := @Enclosure.Real.IsNear.neg qz222 Bool.true Ns240p1793 

noncomputable def Ns240p1801 := @Enclosure.Real.IsNear.mulLit_ft qz215 qz199 Ns240p1705 Ns240p1696 Ns240p1706 

noncomputable def Ns240p1802 := @Enclosure.Real.IsNear.mulLit_ft qz129 qz209 884279719003555 70368744177664 1 

noncomputable def Ns240p1803 := nat_lit 144513493898556405226841343389936054707011487310355 

noncomputable def Ns240p1804 := @Enclosure.Real.IsNear.mulLit_tt qz223 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz191) Ns240p1759 151115727451828646838272 Ns240p1752 Ns240p1798 Ns240p1803 

noncomputable def Ns240p1805 := nat_lit 187072209578355573530071658587684226515959365500928 

noncomputable def Ns240p1806 := nat_lit 49564140107763342291042978261367187576672997854833630404851358403 

noncomputable def Ns240p1807 := nat_lit 6502897299891529708071815448304262215143889305600000000000000000000000 

noncomputable def Ns240p1808 := @Enclosure.Real.IsNear.mulLit_ft qz0 qz220 2 1 0 1 Ns240p1759 302231454903657293676544 Ns240p1752 

noncomputable def Ns240p1809 := @Ns240p1808 Ns240p1761 Ns240p1759 151115727451828646838272 Ns240p1752 Ns240p1798 qz341 qz542 rfl 

noncomputable abbrev qz225 := (@HMul.hMul Real Real Real qz344 qz534 (Real.sin qz528))

noncomputable def Ns240p1810 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz225) (@HMul.hMul Real Real Real qz5 qz220 qz190) 

noncomputable def Ns240p1811 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz191) (@HMul.hMul Real Real Real qz5 qz198 Ns240p1810) Bool.true Ns240p1803 Ns240p1805 Ns240p1806 Ns240p1807 (BSN.deriv_correction_mk qz191 qz214) 

noncomputable def Ns240p1812 := nat_lit 80592568344023817768212281150150787864385 

noncomputable def Ns240p1813 := nat_lit 348449143727040986586495598010130648530944 

noncomputable def Ns240p1814 := nat_lit 10205876984584849678918541211020423072159140770665533057 

noncomputable def Ns240p1815 := @Enclosure.Real.IsNear.mulLit_tf qz198 Ns240p1810 1793136723 536870912 1089 2147483648 Ns240p1812 Ns240p1813 Ns240p1814 

noncomputable def Ns240p1816 := nat_lit 4542221291846267209438478188801739980800000000000000000000000 

noncomputable def Ns240p1817 := @Enclosure.Real.IsNear.subLit_tt_p (@Neg.neg Real Real.instNeg qz225) (@HMul.hMul Real Real Real qz5 qz220 qz190) 

noncomputable def Ns240p1818 := nat_lit 814414997170827571072281405321105 

noncomputable def Ns240p1819 := nat_lit 134437712131872192484046246686338107103811 

noncomputable def Ns240p1820 := nat_lit 501365715910579011334145310720000000000000000000 

noncomputable def Ns240p1821 := nat_lit 955064012899183053520853353140917376259905 

noncomputable def Ns240p1822 := nat_lit 8987912095694439939761394176311594589326784122770493057 

noncomputable def Ns240p1823 := nat_lit 26153783714620516517479337987146383532457679847284597263707348759279042560 

noncomputable def Ns240p1824 := @Enclosure.Real.IsNear.neg qz225 Bool.false Ns240p1818 

noncomputable def Ns240p1825 := @Enclosure.Real.IsNear.mulLit_tt qz216 qz209 382845410553419354204195 151115727451828646838272 Ns240p1709 

noncomputable def Ns240p1826 := @Enclosure.Real.IsNear.mulLit_tf qz220 qz190 Ns240p1759 302231454903657293676544 Ns240p1752 Ns240p1761 527116867211770941 1152921504606846976 

noncomputable def Ns240p1827 := @Enclosure.Real.IsNear.of_eq qz190 (@HMul.hMul Real Real Real qz5 qz198 qz199) Bool.false 527116867211770941 

noncomputable def Ns240p1828 := @Enclosure.Real.IsNear.mulLit_tt qz198 qz199 1793136723 536870912 1089 

noncomputable abbrev qz226 := (BSN.correction_mk qz519 (BSN.cos_two_pi_p_ne_zero_mk qz517 543245 1000 9 qz522 rfl rfl (@BSN.floor_sqrt_eq_dec qz517 543245 1000 9 qz522 rfl rfl rfl)))

noncomputable abbrev qz543 := (@Ns240p1827 1152921504606846976 11996026976193647 38911100780481085440000 qz226 (@Ns240p1828 2147483648 293963567 2147483648 7775447 108716359680000 527116867211770941 1152921504606846976 11996026976193647 38911100780481085440000 Ns240p1668 (Ns240p1749 rfl) rfl))

noncomputable def Ns240p1829 := @Ns240p1826 11996026976193647 38911100780481085440000 Ns240p1821 Ns240p1813 Ns240p1822 Ns240p1816 qz542 qz543 

noncomputable def Ns240p1830 := @Ns240p1804 Ns240p1805 Ns240p1806 Ns240p1807 Ns240p1789 Ns240p1774 Ns240p1790 Ns240p1776 Ns240p1809 (Ns240p1811 (@Ns240p1815 Ns240p1816 Ns240p1803 Ns240p1805 Ns240p1806 Ns240p1807 Ns240p1668 (@Ns240p1817 Ns240p1818 Ns240p1468 Ns240p1819 Ns240p1820 Ns240p1821 Ns240p1813 Ns240p1822 Ns240p1816 Ns240p1823 Ns240p1812 Ns240p1813 Ns240p1814 Ns240p1816 (@Ns240p1824 Ns240p1468 Ns240p1819 Ns240p1820 (@Ns240p1825 Ns240p1710 2127268539 2147483648 7775447 108716359680000 Ns240p1818 Ns240p1468 Ns240p1819 Ns240p1820 qz219 (Ns240p1733 rfl) rfl)) (Ns240p1829 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns240p1831 := @Ns240p1788 Ns240p1789 Ns240p1774 Ns240p1790 Ns240p1776 Ns240p1791 Ns240p1777 Ns240p1774 Ns240p1779 Ns240p1776 (@Ns240p1792 Ns240p1793 Ns240p1781 Ns240p1794 Ns240p1795 Ns240p1796 151115727451828646838272 Ns240p1797 Ns240p1798 Ns240p1799 Ns240p1785 Ns240p1781 Ns240p1786 Ns240p1787 (@Ns240p1800 Ns240p1781 Ns240p1794 Ns240p1795 (@Ns240p1801 Ns240p1707 293963567 2147483648 7775447 108716359680000 Ns240p1793 Ns240p1781 Ns240p1794 Ns240p1795 (@Ns240p1711 Ns240p1709 Ns240p1710 Ns240p1705 Ns240p1696 Ns240p1706 Ns240p1707 qz219 qz219 rfl) (Ns240p1749 rfl) rfl)) (@Ns240p1802 250000000000000 2127268539 2147483648 7775447 108716359680000 Ns240p1796 151115727451828646838272 Ns240p1797 Ns240p1798 RS241to252.d70 (Ns240p1733 rfl) rfl) rfl rfl) Ns240p1830 

noncomputable def Ns240p1832 := nat_lit 502765726373748676459966584952147762075 

noncomputable def Ns240p1833 := nat_lit 42535295865117307932921825928971026432 

noncomputable def Ns240p1834 := nat_lit 3597871976019750728371899791092980967435567480097882828783 

noncomputable def Ns240p1835 := nat_lit 2005462863642316045336581242880000000000000000000000000000000000 

noncomputable abbrev qz227 := qz536

noncomputable def Ns240p1836 := @Enclosure.Real.IsNear.mulLit_ff qz227 qz190 Ns240p1832 Ns240p1833 Ns240p1834 Ns240p1835 527116867211770941 1152921504606846976 

noncomputable def Ns240p1837 := @Enclosure.Real.IsNear.mulLit_ft qz130 qz201 Ns240p892 Ns240p896 Ns240p894 Ns240p897 642963523 2147483648 4940447 108716359680000 Ns240p1832 

noncomputable abbrev qz544 := (@HMul.hMul Real Real Real qz615 qz688 qz724)

noncomputable abbrev qz228 := qz544

noncomputable def Ns240p1838 := @Ns240p1836 11996026976193647 38911100780481085440000 Ns240p1780 Ns240p1781 Ns240p1782 Ns240p1783 (@Enclosure.Real.IsNear.neg qz228 Bool.true Ns240p1832 Ns240p1833 Ns240p1834 Ns240p1835 (@Ns240p1837 Ns240p1833 Ns240p1834 Ns240p1835 RS241to252.d72 qz538 rfl)) qz543 

noncomputable def Ns240p1839 := nat_lit 1508297179121246029379899754856443286225 

noncomputable def Ns240p1840 := nat_lit 668487621214105348445527080960000000000000000000000000000000000 

noncomputable def Ns240p1841 := @Enclosure.Real.IsNear.mulLit_ft qz212 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz191) Ns240p1839 Ns240p1833 Ns240p1834 Ns240p1840 Ns240p1803 

noncomputable def Ns240p1842 := @Enclosure.Real.IsNear.mulLit_ff qz320 qz227 3 1 0 1 Ns240p1832 Ns240p1833 Ns240p1834 

noncomputable def Ns240p1843 := @Ns240p1842 Ns240p1835 Ns240p1839 Ns240p1833 Ns240p1834 Ns240p1840 qz476 (@Enclosure.Real.IsNear.neg qz228 Bool.true Ns240p1832 Ns240p1833 Ns240p1834 Ns240p1835 (@Ns240p1837 Ns240p1833 Ns240p1834 Ns240p1835 RS241to252.d72 qz538 rfl)) rfl 

noncomputable def Ns240p1844 := @Ns240p1841 Ns240p1805 Ns240p1806 Ns240p1807 Ns240p1680 Ns240p1681 Ns240p1682 Ns240p1683 Ns240p1843 (Ns240p1811 (@Ns240p1815 Ns240p1816 Ns240p1803 Ns240p1805 Ns240p1806 Ns240p1807 Ns240p1668 (@Ns240p1817 Ns240p1818 Ns240p1468 Ns240p1819 Ns240p1820 Ns240p1821 Ns240p1813 Ns240p1822 Ns240p1816 Ns240p1823 Ns240p1812 Ns240p1813 Ns240p1814 Ns240p1816 (@Ns240p1824 Ns240p1468 Ns240p1819 Ns240p1820 (@Ns240p1825 Ns240p1710 2127268539 2147483648 7775447 108716359680000 Ns240p1818 Ns240p1468 Ns240p1819 Ns240p1820 qz219 (Ns240p1733 rfl) rfl)) (Ns240p1829 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns240p1845 := @Ns240p1678 Ns240p1679 Ns240p1649 Ns240p1680 Ns240p1681 Ns240p1682 Ns240p1683 Ns240p1684 Ns240p1670 Ns240p1646 Ns240p1671 Ns240p1649 (@Ns240p1688 Ns240p1689 Ns240p1646 Ns240p1690 Ns240p1649 Ns240p1691 Ns240p1677 Ns240p1646 Ns240p1679 Ns240p1649 Ns240p1750 (@Ns240p1755 Ns240p1756 Ns240p1757 Ns240p1758 Ns240p1689 Ns240p1646 Ns240p1690 Ns240p1649 Ns240p1769 (@Ns240p1771 Bool.false Ns240p1754 Ns240p1756 Ns240p1757 Ns240p1758 (BSN.iteratedDeriv_two_correction_mk qz191 qz214) (@Ns240p1772 536870912 1089 2147483648 Ns240p1773 Ns240p1774 Ns240p1775 Ns240p1776 Ns240p1754 Ns240p1756 Ns240p1757 Ns240p1758 Ns240p1668 (@Ns240p1778 Ns240p1779 Ns240p1776 Ns240p1780 Ns240p1781 Ns240p1782 Ns240p1783 Ns240p1784 Ns240p1773 Ns240p1774 Ns240p1775 Ns240p1776 (Ns240p1831 rfl rfl) (Ns240p1838 rfl) rfl rfl) rfl)) rfl) rfl rfl) Ns240p1844 

noncomputable def Ns240p1846 := nat_lit 1416788087910726624243342868792127715122751599407720125 

noncomputable def Ns240p1847 := nat_lit 97092445996381362174475269251066550869155699175054321145152627837373913278316617161 

noncomputable def Ns240p1848 := nat_lit 8613397412686254856416669750616632852480000000000000000000000000000000000000000000000000 

noncomputable def Ns240p1849 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz332 RSCompact.c11) qz213) qz190 Ns240p1846 Ns240p25 Ns240p1847 Ns240p1848 527116867211770941 1152921504606846976 11996026976193647 

noncomputable def Ns240p1850 := @Enclosure.Real.IsNear.mulLit_ff qz459 qz213 Ns240p898 Ns240p899 Ns240p900 Ns240p901 2048971431 2147483648 4940447 108716359680000 Ns240p1846 

noncomputable abbrev qz545 := (Ns240p1763 (@Ns240p1764 829440000 (Ns240p1660 rfl) (Enclosure.sfrac_false_div 2013119299 1073741824) (Ns240p1768 rfl rfl) rfl rfl) rfl)

noncomputable def Ns240p1851 := Ns240p1644 (@Ns240p1648 Ns240p1649 Ns240p1637 Ns240p1638 Ns240p1639 Ns240p1640 Ns240p1668 (@Ns240p1669 Ns240p1670 Ns240p1646 Ns240p1671 Ns240p1649 Ns240p1672 Ns240p1673 Ns240p1674 Ns240p1675 Ns240p1676 Ns240p1645 Ns240p1646 Ns240p1647 Ns240p1649 (Ns240p1845 rfl rfl) (@Ns240p1849 38911100780481085440000 Ns240p1672 Ns240p1673 Ns240p1674 Ns240p1675 (@Ns240p1850 Ns240p25 Ns240p1847 Ns240p1848 RS241to252.d73 qz545 rfl) qz543 rfl) rfl rfl) rfl) 

noncomputable def Ns240p1852 := @Enclosure.Real.IsNear.of_eq qz719 (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz191) qz462)) Bool.false Ns240p1632 Ns240p1633 Ns240p1634 Ns240p1635 (BSN.correctionLinear_mk qz191) (@Enclosure.Real.IsNear.neg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz191) qz462) Bool.true Ns240p1632 Ns240p1633 Ns240p1634 Ns240p1635 (@Ns240p1641 Ns240p1633 Ns240p1634 Ns240p1635 Ns240p1851 RS241to252.d74 rfl)) 

noncomputable def Ns240p1853 := @Enclosure.Real.IsNear.inv_image qz192 156001165 16777216 31 16777216 902156 902157 8388608 qz525 rfl 

noncomputable def Ns240p1854 := @Ns240p1636 Ns240p1587 Ns240p1597 Ns240p1590 Ns240p1852 (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz192) Bool.false 1804313 16777216 1 16777216 1804313 16777216 1 16777216 (Ns240p1853 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns240p1855 := @Ns240p1589 Ns240p1590 Ns240p1512 Ns240p928 Ns240p1514 Ns240p1510 (Ns240p1591 qz29 (@Enclosure.Real.IsNear.of_eq qz196 (@Inv.inv Real Real.instInv (Real.sqrt qz192)) Bool.false 5501941 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz197 (BSN.t_div_two_pi_nonneg qz188 543245 1000 qz193)) Ns240p1595) rfl) (@Ns240p1598 Ns240p1599 Ns240p1586 Ns240p1587 Ns240p1588 Ns240p1590 (@Ns240p1600 140737488355328 580408972083473 7124835347988480000 qz226 (@Ns240p1601 16777216 1148301 8388608 2007143 106168320000 64345320978939 140737488355328 580408972083473 7124835347988480000 Ns240p1616 (Ns240p1631 rfl) rfl)) (Ns240p1854 rfl) rfl rfl) 

noncomputable def Ns240p1856 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz188) (hardyZApproximantRS qz188) Bool.true Ns240p1508 Ns240p928 Ns240p1509 Ns240p1510 (@Eq.refl Real (hardyZApproximantRS qz188)) (Ns240p1511 (BSN.hardyZApproximantRS_eq qz188 9 (@BSN.floor_sqrt_eq_dec qz188 543245 1000 9 qz193 rfl rfl rfl)) (@Ns240p1513 Ns240p1514 Ns240p1510 Ns240p1515 Ns240p1508 Ns240p928 Ns240p1509 Ns240p1510 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (@HAdd.hAdd Real Real Real qz360 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 9)) Bool.true 479215355 67108864 23285 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (Ns240p1585 (Ns240p1584 rfl) rfl rfl)) (Ns240p1855 rfl) rfl rfl)) 

theorem RS241to252.d75 : Enclosure.Real.IsNear (hardyZApproximantRS qz188) Bool.true Ns240p1508 Ns240p928 Ns240p1509 Ns240p1510 := Ns240p1856 

noncomputable def Ns240p1857 := nat_lit 1107757106081426479896019861504 

noncomputable def Ns240p1858 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (@HMul.hMul Real Real Real qz5 qz189 qz190) 479215355 67108864 23285 16777216 354024159652184620599 2361183241434822606848 3196633982557446391441 Ns240p1135 Ns240p1857 

noncomputable def Ns240p1859 := @Enclosure.Real.IsNear.mulLit_tf qz189 qz190 5501941 16777216 1 16777216 64345320978939 140737488355328 580408972083473 7124835347988480000 354024159652184620599 2361183241434822606848 

noncomputable def Ns240p1860 := @Ns240p1859 3196633982557446391441 Ns240p1135 (Ns240p1591 qz29 (@Enclosure.Real.IsNear.of_eq qz196 (@Inv.inv Real Real.instInv (Real.sqrt qz192)) Bool.false 5501941 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz197 (BSN.t_div_two_pi_nonneg qz188 543245 1000 qz193)) Ns240p1595) rfl) (@Ns240p1600 140737488355328 580408972083473 7124835347988480000 qz226 (@Ns240p1601 16777216 1148301 8388608 2007143 106168320000 64345320978939 140737488355328 580408972083473 7124835347988480000 Ns240p1616 (Ns240p1631 rfl) rfl)) 

noncomputable def Ns240p1861 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz188) (hardyZApproximantRS₀ qz188) Bool.true 16506867201349533794761 2361183241434822606848 169098425060469203191441 Ns240p1135 (@Eq.refl Real (hardyZApproximantRS₀ qz188)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz188) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (@HMul.hMul Real Real Real qz5 qz189 qz190)) Bool.true 16506867201349533794761 2361183241434822606848 169098425060469203191441 Ns240p1135 (BSN.hardyZApproximantRS₀_eq qz188 9 (@BSN.floor_sqrt_eq_dec qz188 543245 1000 9 qz193 rfl rfl rfl)) (@Ns240p1858 16506867201349533794761 2361183241434822606848 169098425060469203191441 Ns240p1135 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (@HAdd.hAdd Real Real Real qz360 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 9)) Bool.true 479215355 67108864 23285 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (Ns240p1585 (Ns240p1584 rfl) rfl rfl)) (Ns240p1860 rfl) rfl rfl)) 

theorem RS241to252.d76 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz188) Bool.true 16506867201349533794761 2361183241434822606848 169098425060469203191441 Ns240p1135 := Ns240p1861 

noncomputable def Ns240p1862 := nat_lit 23906980319527578894336000 

noncomputable def Ns240p1863 := nat_lit 69322959123678321610386833408 

noncomputable abbrev qz857 := (Enclosure.sfrac Bool.false 544654 1000)

noncomputable abbrev qz733 := qz857

noncomputable abbrev qz546 := qz733

noncomputable abbrev qz229 := qz546

noncomputable abbrev qz858 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 544654 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz734 := qz858

noncomputable abbrev qz547 := qz734

noncomputable abbrev qz230 := qz547

noncomputable abbrev qz859 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 544654 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz735 := qz859

noncomputable abbrev qz548 := qz735

noncomputable abbrev qz231 := qz548

noncomputable abbrev qz549 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz618 qz230 qz8))

noncomputable def Ns240p1864 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz229) qz229 9) (@HMul.hMul Real Real Real qz5 qz549 (Zeta.RiemannSiegel.correction qz231)) 26894965 16777216 93387 67108864 346840529841316808343 2361183241434822606848 504173830855704809381 Ns240p1862 Ns240p1863 

noncomputable def Ns240p1865 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz229) qz229 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 544654 1000 121 161 134217728 67108864 2251799813685248 Bool.false 126497247559 1806 

noncomputable def Ns240p1866 := Ns240p1865 279097919 42 47453128 8 294906479 42 44739240 8 Bool.false 152753915 76414 Bool.true 4276005 Bool.true 181322878 7074237752028440 1 Bool.false 4275281 Bool.true Bool.false 130987551 Bool.true Bool.false 107579860 

noncomputable def Ns240p1867 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz229) qz229 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 544654 1000 21 74 134217728 67108864 2251799813685248 Bool.false 126497247559 1806 

noncomputable def Ns240p1868 := Ns240p1867 240485871 42 54794152 8 261175631 42 50729528 8 Bool.false 196914303 56989 Bool.true 56941027 Bool.true 151779721 7074237752028440 1 Bool.false 55248265 Bool.true Bool.false 57162468 Bool.true Bool.false 152753915 

noncomputable def Ns240p1869 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz229) qz229 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 544654 1000 119 41 134217728 67108864 2251799813685248 Bool.false 126497247559 1806 

noncomputable def Ns240p1870 := Ns240p1869 186065264 42 67108856 8 216015088 42 60023992 8 Bool.false 224416326 33590 Bool.false 67440278 Bool.false 199788539 7074237752028440 1 Bool.false 64638053 Bool.false Bool.false 133763925 Bool.true Bool.false 196914303 

noncomputable def Ns240p1871 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz229) qz229 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 544654 1000 359 219 134217728 67108864 2251799813685248 Bool.false 126497247559 1806 

noncomputable def Ns240p1872 := Ns240p1871 93032624 42 94906264 8 147453232 42 77490640 16 Bool.false 134217720 1858 Bool.false 139148393 Bool.false 14766542 7074237752028440 1 Bool.false 115527573 Bool.false Bool.false 14736770 Bool.false Bool.false 224416326 

noncomputable def Ns240p1873 := nat_lit 1947730203109965855301593418066969598265669130188682127 

noncomputable def Ns240p1874 := nat_lit 2066605619190669640176711862531405213038293286912000 

noncomputable def Ns240p1875 := nat_lit 23006240317743859198484921451520000 

noncomputable def Ns240p1876 := nat_lit 75182674452323031443546346509953044480 

noncomputable abbrev qz736 := (@Eq.refl Real qz857)

noncomputable abbrev qz550 := qz736

noncomputable abbrev qz232 := qz550

noncomputable def Ns240p1877 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz229 544654 1000 1186592918864 16000000 1089308 4000 2000 Ns240p1875 Ns240p1876 qz232 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns240p1878 := nat_lit 39889514559692100716576633202011537372480903786264209960960 

noncomputable abbrev qz737 := (Real.log (Enclosure.sfrac Bool.false 1186592918864 16000000))

noncomputable abbrev qz738 := (@Nat.cast Real Real.instNatCast 1089308)

noncomputable abbrev qz739 := (Enclosure.sfrac Bool.false 544654 2000)

noncomputable abbrev qz233 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 544654 4000) qz737) (@HMul.hMul Real Real Real qz344 qz358 (@HSub.hSub Real Real Real qz350 qz355 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz356 qz738))))) qz739)

noncomputable abbrev qz551 := (@HSub.hSub Real Real Real qz11 qz233 (@HMul.hMul Real Real Real qz5 qz739 (Real.log Real.pi)))

noncomputable def Ns240p1879 := @Enclosure.Real.IsNear.addLit_ft_p qz551 (Enclosure.sfrac Bool.true Ns240p1875 Ns240p1876) 530568083692605187027 562949953421312000 123921664561698931 9216000000000000000000 Ns240p1875 Ns240p1876 0 1 Ns240p1878 

noncomputable def Ns240p1880 := nat_lit 17802910685633829650944753664000 

noncomputable abbrev qz552 := (@HMul.hMul Real Real Real qz5 qz739 (Real.log Real.pi))

noncomputable def Ns240p1881 := @Enclosure.Real.IsNear.subLit_ff_p qz233 qz552 706062583328744448979 562949953421312000 47973457108669 9000000000000000000 10460287310847 33554432000 272327 33554432000 Ns240p1880 530568083692605187027 562949953421312000 

noncomputable def Ns240p1882 := nat_lit 1412125166657488897958000 

noncomputable abbrev qz234 := (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 544654 4000) qz737) (@HMul.hMul Real Real Real qz344 qz358 (@HSub.hSub Real Real Real qz350 qz355 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz356 qz738)))))

noncomputable def Ns240p1883 := @Enclosure.Real.IsNear.subLit_ff_p qz234 qz739 859369055294110082003 562949953421312000 47973457108669 9000000000000000000 544654 2000 0 1 Ns240p1882 706062583328744448979 562949953421312000 47973457108669 9000000000000000000 

noncomputable def Ns240p1884 := nat_lit 1935127078598144669057948410911391744 

noncomputable def Ns240p1885 := nat_lit 27113807451758756613849088 

noncomputable def Ns240p1886 := nat_lit 374397256772789337170820140738239399557249447690240 

noncomputable def Ns240p1887 := nat_lit 476922433656614371504394050208980878953902768128 

noncomputable def Ns240p1888 := nat_lit 1088555474044533112570641034267341497633538048 

noncomputable def Ns240p1889 := BSN.log_dyadic_bound 138016918864 2235168918864 3 2 Ns240p1886 67108864 25920000 Ns240p1887 Ns240p1888 8298215 2373185837728 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 138016918864) (BSN.artanhQ 2235168918864) 0 2 Ns240p1887 Ns240p1886 Ns240p1888 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns240p1890 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 544654 4000) qz737 544654 4000 0 1 3156462620450039 281474976710656 195312581 5062500000000000 859589996039297770753 562949953421312000 53188889245987 10125000000000000000 (Enclosure.Real.IsNear.const Bool.false 544654 4000) (BSN.isNear_log_sfrac 1186592918864 16000000 3156462620450039 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1186592918864) qz354)) Bool.false Ns240p1885 Ns240p92 1000000414720000 25920000000000000000000 3156462620450039 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1186592918864 16000000 16 2373185837728 2097152000000 8298215 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns240p1889 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p1891 := BSN.arctan_dyadic_bound_f 1000 1089308 1 0 8388608 3240000 0 1 1 0 1 1 7700 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1089308) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1089308) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz740 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1089308)))

noncomputable def Ns240p1892 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz740 884279719003555 562949953421312 1 2000000000000000 7700 8388608 1 3240000 7413541210429629399040 883762980750755 562949953421312 50000000081 162000000000000000 qz16 (Ns240p1891 rfl) rfl rfl 

noncomputable def Ns240p1893 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 544654 4000) qz737) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz11 qz14 qz740)) 859589996039297770753 562949953421312000 53188889245987 10125000000000000000 883762980750755 2251799813685248 50000000081 648000000000000000 Ns240p1884 859369055294110082003 562949953421312000 47973457108669 9000000000000000000 (Ns240p1890 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 qz740) 1 4 0 1 883762980750755 562949953421312 50000000081 162000000000000000 883762980750755 2251799813685248 50000000081 648000000000000000 qz359 Ns240p1892 rfl) 

noncomputable def Ns240p1894 := @Ns240p1879 Ns240p1873 Ns240p1874 123921664561698931 9216000000000000000000 (@Ns240p1881 123921664561698931 9216000000000000000000 (Ns240p1883 (Ns240p1893 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 544654 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz739 (Real.log Real.pi) 544654 2000 0 1 38410761 33554432 1 33554432 10460287310847 33554432000 272327 33554432000 (Enclosure.Real.IsNear.const Bool.false 544654 2000) RS241to252.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns240p1875 Ns240p1876) 

noncomputable def Ns240p1895 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz229) Bool.false Ns240p1873 Ns240p1874 123921664561698931 9216000000000000000000 1976519493 2097152 227 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz229) (@HAdd.hAdd Real Real Real qz360 qz551 (Enclosure.sfrac Bool.true Ns240p1875 Ns240p1876)) Bool.false Ns240p1873 Ns240p1874 123921664561698931 9216000000000000000000 Ns240p1877 (Ns240p1894 rfl rfl)) 

noncomputable def Ns240p1896 := nat_lit 857448391167346287757038341892095699163826389985671615762517259239891124608037304732697761492873767257931219945622803197631142339617521 

noncomputable def Ns240p1897 := nat_lit 611657253921798497043454198389406629857877610704382254257308151896149953428421297129633255901302792542899441413302164463173051121 

noncomputable def Ns240p1898 := nat_lit 4281912603670842661426584193199555087752968347964912648580525592887437121745255075002268680209197334272473120270442931506465243555504881 

noncomputable def Ns240p1899 := BSN.sin_dyadic_bound_f 53977033277 34359738368 4 3 16777216 6486329 Ns240p1896 Ns240p105 Ns240p1897 Ns240p1898 Ns240p108 Ns240p1897 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53977033277) qz361 0 3 Ns240p1896 Ns240p105 Ns240p1897 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53977033277) qz362 0 3 Ns240p1898 Ns240p108 Ns240p1897 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1900 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz229) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1976519493) (@Nat.cast Real Real.instNatCast 2097152)) Bool.false 1976519493 2097152 227 16777216 Bool.false 16777215 16777216 1 3240000 (Ns240p1895 rfl) (Enclosure.sfrac_false_div 1976519493 2097152) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1976519493) (@Nat.cast Real Real.instNatCast 2097152)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474787005769453515309056) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 149 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q3 1976519493 2097152 226375608064910080 72057594037927936 149 474787005769453515309056 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 474787005769453515309056 302231454903657293676544 53977033277 34359738368 6486329 6480000 (Ns240p1899 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns240p1901 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz229) Bool.false Ns240p1873 Ns240p1874 123921664561698931 9216000000000000000000 126497247559 134217728 1806 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz229) (@HAdd.hAdd Real Real Real qz360 qz551 (Enclosure.sfrac Bool.true Ns240p1875 Ns240p1876)) Bool.false Ns240p1873 Ns240p1874 123921664561698931 9216000000000000000000 Ns240p1877 (Ns240p1894 rfl rfl)) 

noncomputable def Ns240p1902 := Ns240p1872 33590 BSN.abs_quadSignPos (BSN.cos_quad_nat3 359 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 115527573 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 219 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 14736770 134217728) qz232 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz229) qz229 1) Bool.false 16777215 16777216 11754019 849346560000 134217720 134217728 1858 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz229) qz229 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz229)) Bool.false 16777215 16777216 11754019 849346560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz229) qz229) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz229)) Bool.false 16777215 16777216 752257216 54358179840000 16777215 16777216 11754019 849346560000 (Ns240p1900 rfl rfl) rfl)) rfl) (Ns240p1901 rfl) RS241to252.d7 

noncomputable def Ns240p1903 := nat_lit 368044200368755141772162386160750122904784931055918372766658240647745 

noncomputable def Ns240p1904 := nat_lit 140548288318137342182065160603762978894173483773418081767831835201 

noncomputable def Ns240p1905 := nat_lit 963697732308510291801654334446701372308608062363200680351718902534721 

noncomputable def Ns240p1906 := BSN.sin_dyadic_bound_f 139148393 134217728 3 2 134217728 67108864 Ns240p1903 Ns240p248 Ns240p1904 Ns240p1905 Ns240p251 Ns240p1904 115527573 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 139148393) qz365 0 2 Ns240p1903 Ns240p248 Ns240p1904 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 139148393) qz366 0 2 Ns240p1905 Ns240p251 Ns240p1904 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1907 := nat_lit 47546135086910496759078919696 

noncomputable def Ns240p1908 := BSN.sin_dyadic_bound_f 14766542 134217728 2 1 134217728 67108864 Ns240p1907 Ns240p114 Ns240p1907 Ns240p1907 Ns240p115 Ns240p1907 14736770 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 14766542) qz365 0 1 Ns240p1907 Ns240p114 Ns240p1907 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 14766542) qz366 0 1 Ns240p1907 Ns240p115 Ns240p1907 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1909 := nat_lit 20300553558506913509392024021837831837356882775665323322079282028800 

noncomputable def Ns240p1910 := nat_lit 427912344062218562657887907643224344188937674987490224825262336 

noncomputable def Ns240p1911 := nat_lit 53167423652294387027877664429153375306044101370506819430796021555456 

noncomputable def Ns240p1912 := BSN.sin_dyadic_bound_f 67440278 134217728 3 2 134217728 67108864 Ns240p1909 Ns240p248 Ns240p1910 Ns240p1911 Ns240p251 Ns240p1910 64638053 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 67440278) qz365 0 2 Ns240p1909 Ns240p248 Ns240p1910 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 67440278) qz366 0 2 Ns240p1911 Ns240p251 Ns240p1910 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1913 := nat_lit 8720976950588797191022718907772565501936800171183132578160793399814649957406605058791899516960203260848721 

noncomputable def Ns240p1914 := nat_lit 4044332489041755320704556467927071176035349975187544959683342124449901007958468104355212297054743121 

noncomputable def Ns240p1915 := nat_lit 43561176003143341124448346246608785675525164268885006886155492333622001955720548579944211803487179513817681 

noncomputable def Ns240p1916 := BSN.sin_dyadic_bound_f 199788539 134217728 4 3 134217728 67108864 Ns240p1913 Ns240p118 Ns240p1914 Ns240p1915 Ns240p121 Ns240p1914 133763925 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 199788539) qz365 0 3 Ns240p1913 Ns240p118 Ns240p1914 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 199788539) qz366 0 3 Ns240p1915 Ns240p121 Ns240p1914 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1917 := Ns240p1870 56989 BSN.abs_quadSignPos (BSN.cos_quad_nat3 119 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 64638053 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133763925 134217728) qz232 rfl rfl (Ns240p1902 RS241to252.d9 RS241to252.d11 RS241to252.d13 RS241to252.d17 (Ns240p1906 rfl rfl) (Ns240p1908 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns240p1901 rfl) RS241to252.d19 RS241to252.d21 RS241to252.d23 RS241to252.d25 RS241to252.d17 (Ns240p1912 rfl rfl) (Ns240p1916 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns240p1918 := nat_lit 10512383202614268014252973343441 

noncomputable def Ns240p1919 := BSN.sin_dyadic_bound_f 56941027 134217728 2 1 134217728 67108864 Ns240p1918 Ns240p114 Ns240p1918 Ns240p1918 Ns240p115 Ns240p1918 55248265 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 56941027) qz365 0 1 Ns240p1918 Ns240p114 Ns240p1918 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 56941027) qz366 0 1 Ns240p1918 Ns240p115 Ns240p1918 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1920 := nat_lit 1116560848965524107885729752017715330876225586943615874326557226545856122497326564508871929721812823415521 

noncomputable def Ns240p1921 := nat_lit 149473774731940516289630186524632985381212299922562839053714831620337402796360969668397808385891041 

noncomputable def Ns240p1922 := nat_lit 6769410105442677401282815706937441959113774846844355430040286144107873782512977836498094312634187356674785 

noncomputable def Ns240p1923 := BSN.cos_dyadic_bound_f 151779721 134217728 4 3 134217728 67108864 Ns240p1920 Ns240p130 Ns240p1921 Ns240p1922 Ns240p133 Ns240p1921 57162468 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 151779721) qz367 0 3 Ns240p1920 Ns240p130 Ns240p1921 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 151779721) qz368 0 3 Ns240p1922 Ns240p133 Ns240p1921 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1924 := Ns240p1868 76414 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 21 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 55248265 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 74 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 57162468 134217728) qz232 rfl rfl (Ns240p1917 rfl rfl) (Ns240p1901 rfl) RS241to252.d27 RS241to252.d29 RS241to252.d31 RS241to252.d33 RS241to252.d17 (Ns240p1919 rfl rfl) (Ns240p1923 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p1925 := BSN.sin_dyadic_bound_f 4276005 134217728 1 0 134217728 67108864 0 1 1 0 1 1 4275281 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 4276005) qz365 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 4276005) qz366 0 0 rfl) rfl rfl 

noncomputable def Ns240p1926 := nat_lit 5913801707539280883227477622884114224511493454754372138109836437302856996576852118029193596877234079010816 

noncomputable def Ns240p1927 := nat_lit 1263081121356693781841249328964427942927065489094885948112168152188426899930556628425506585150754816 

noncomputable def Ns240p1928 := nat_lit 29548891086359840109169827324257162693592778049550393582715042117545620917093948444791279289246558668722176 

noncomputable def Ns240p1929 := BSN.sin_dyadic_bound_f 181322878 134217728 4 3 134217728 67108864 Ns240p1926 Ns240p118 Ns240p1927 Ns240p1928 Ns240p121 Ns240p1927 130987551 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 181322878) qz365 0 3 Ns240p1926 Ns240p118 Ns240p1927 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 181322878) qz366 0 3 Ns240p1928 Ns240p121 Ns240p1927 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1930 := Ns240p1866 93387 BSN.abs_quadSignNeg qz642 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 4275281 134217728) BSN.abs_quadSignNeg qz662 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 130987551 134217728) qz232 rfl rfl (Ns240p1924 rfl) (Ns240p1901 rfl) RS241to252.d35 RS241to252.d37 RS241to252.d39 RS241to252.d41 RS241to252.d17 (Ns240p1925 rfl rfl) (Ns240p1929 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p1931 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz229) qz229 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz229) qz229 9) 107579860 134217728 93387 134217728 107579860 134217728 93387 134217728 28878248775516160 26894965 16777216 93387 67108864 (Ns240p1930 rfl) 

noncomputable def Ns240p1932 := @Enclosure.Real.IsNear.mulLit_tf qz549 (Zeta.RiemannSiegel.correction qz231) 5498379 16777216 1 16777216 63080506062117 140737488355328 457894089469831 7124835347988480000 346840529841316808343 2361183241434822606848 

noncomputable abbrev qz553 := (@HPow.hPow Real Real Real qz618 qz230 qz8)

noncomputable def Ns240p1933 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz553 1 1 0 1 5498379 16777216 1 16777216 5498379 16777216 1 16777216 

noncomputable def Ns240p1934 := @Enclosure.Real.IsNear.sqrt_image qz230 727161291879 8388608000 272327 8388608000 78101656 78101686 8388608 (@Enclosure.Real.IsNear.of_eq qz230 (@HMul.hMul Real Real Real qz5 qz229 qz3) Bool.false 727161291879 8388608000 272327 8388608000 (BSN.t_div_two_pi_mk qz229 544654 1000 qz232) (@Enclosure.Real.IsNear.mulLit_ff qz229 qz3 544654 1000 0 1 2670177 16777216 1 16777216 727161291879 8388608000 272327 8388608000 (Enclosure.Real.IsNear.const Bool.false 544654 1000) RS241to252.d44 rfl)) 

noncomputable abbrev qz860 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 544654 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz741 := qz860

noncomputable abbrev qz554 := qz741

noncomputable abbrev qz235 := qz554

noncomputable def Ns240p1935 := @Enclosure.Real.IsNear.sqrt_image qz235 78101671 8388608 15 8388608 25596175 25596180 8388608 (@Enclosure.Real.IsNear.recentre' qz235 Bool.false 156203342 16777216 30 16777216 78101671 8388608 15 8388608 (Ns240p1934 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns240p1936 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz235) 51192355 16777216 5 16777216 2749189 2749190 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz235) Bool.false 51192355 16777216 5 16777216 51192355 16777216 5 16777216 (Ns240p1935 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns240p1937 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz235)) Bool.false 5498379 16777216 1 16777216 5498379 16777216 1 16777216 (Ns240p1936 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz236 := (Real.cos (@HMul.hMul Real Real Real qz344 qz340 qz548))

noncomputable abbrev qz742 := (@HMul.hMul Real Real Real qz811 qz859 qz859)

noncomputable abbrev qz555 := (@HSub.hSub Real Real Real qz619 (@HSub.hSub Real Real Real qz619 qz742 qz735) qz626)

noncomputable abbrev qz237 := (Real.cos (@HMul.hMul Real Real Real qz344 qz340 qz555))

noncomputable def Ns240p1938 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz231) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz236) qz237) Bool.false 63080506062117 

noncomputable def Ns240p1939 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz236) qz237 45255627 16777216 1421 

noncomputable abbrev qz743 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz236))

noncomputable def Ns240p1940 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz236) (@Neg.neg Real Real.instNeg qz743) Bool.true 45255627 16777216 1421 16777216 (BSN.inv_eq_neg_inv_neg qz236) 

noncomputable def Ns240p1941 := @Enclosure.Real.IsNear.recentre' qz743 Bool.false 45255627 16777216 1421 16777216 45255627 16777216 

noncomputable def Ns240p1942 := @Enclosure.Real.IsNear.recentre' qz236 Bool.true 3109834 8388608 316188608 27179089920000 1554917 4194304 4940447 424673280000 

noncomputable abbrev qz238 := (@HMul.hMul Real Real Real qz344 qz340 qz548)

noncomputable def Ns240p1943 := @Enclosure.Real.IsNear.cos_image qz238 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 32725329) qz363) Bool.false 32725329 16777216 95 8388608 Bool.true 3109834 8388608 1 

noncomputable def Ns240p1944 := nat_lit 404791131158030580902086313 

noncomputable def Ns240p1945 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz231 884279719003555 140737488355328 1 500000000000000 2604199 8388608 15 8388608 2302840359949338927445 1180591620717411303424 Ns240p1944 

noncomputable def Ns240p1946 := @Enclosure.Real.IsNear.subLit_ff_p qz235 qz1 78101671 8388608 15 8388608 9 1 0 1 2604199 2604199 8388608 15 

noncomputable def Ns240p1947 := @Ns240p1946 8388608 (@Enclosure.Real.IsNear.recentre' qz235 Bool.false 156203342 16777216 30 16777216 78101671 8388608 15 8388608 (Ns240p1934 rfl rfl rfl rfl rfl rfl) rfl) qz373 

noncomputable def Ns240p1948 := @Enclosure.Real.IsNear.recentre' qz238 Bool.false 2302840359949338927445 1180591620717411303424 Ns240p1944 Ns240p165 32725329 16777216 95 8388608 (@Ns240p1945 Ns240p165 RS241to252.d43 (Ns240p1947 rfl rfl) rfl) 

noncomputable def Ns240p1949 := nat_lit 144927801587814026172753559383359014527267116221183424908947444494957351534476974346600501584321 

noncomputable def Ns240p1950 := nat_lit 1508718641460966569143014361580686664565678294283797849329665770450139460398321007508693441 

noncomputable def Ns240p1951 := nat_lit 874213448323288028044641820179283615316528033372290172177366666271442217729210641241916818170305 

noncomputable def Ns240p1952 := BSN.cos_dyadic_bound_t 32725329 16777216 4 3 8388608 3240000 Ns240p1949 Ns240p303 Ns240p1950 Ns240p1951 Ns240p306 Ns240p1950 3109834 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32725329) qz627 0 3 Ns240p1949 Ns240p303 Ns240p1950 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32725329) (BSN.cosOddQ 16777216) 0 3 Ns240p1951 Ns240p306 Ns240p1950 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1953 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz236) 1554917 4194304 4940447 424673280000 22627103 22628524 8388608 (@Enclosure.Real.IsNear.neg qz236 Bool.true 1554917 4194304 4940447 424673280000 (Ns240p1942 (@Ns240p1943 3240000 (Ns240p1948 rfl) (Enclosure.sfrac_false_div 32725329 16777216) (Ns240p1952 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns240p1954 := Ns240p1940 (@Enclosure.Real.IsNear.neg qz743 Bool.false 45255627 16777216 1421 16777216 (@Ns240p1941 1421 16777216 (Ns240p1953 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p1955 := @Enclosure.Real.IsNear.recentre' qz237 Bool.true 1393871 8388608 

noncomputable abbrev qz239 := (@HMul.hMul Real Real Real qz344 qz340 qz555)

noncomputable def Ns240p1956 := @Enclosure.Real.IsNear.cos_image qz239 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 29154321)) qz363) Bool.true 29154321 16777216 

noncomputable def Ns240p1957 := nat_lit 17209673836657806191086179725 

noncomputable def Ns240p1958 := nat_lit 1100790702166501543416438270716129 

noncomputable def Ns240p1959 := @Enclosure.Real.IsNear.recentre' qz239 Bool.true Ns240p1957 Ns240p180 Ns240p1958 

noncomputable abbrev qz240 := qz555

noncomputable def Ns240p1960 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz240 884279719003555 140737488355328 1 500000000000000 19461798644495 

noncomputable abbrev qz556 := (@HSub.hSub Real Real Real qz619 qz742 qz735)

noncomputable abbrev qz241 := qz556

noncomputable def Ns240p1961 := @Enclosure.Real.IsNear.subLit_tf qz241 qz27 15063752133391 70368744177664 203955315 70368744177664 1 16 

noncomputable abbrev qz557 := qz742

noncomputable abbrev qz242 := qz557

noncomputable def Ns240p1962 := @Enclosure.Real.IsNear.subLit_ff_n qz242 qz231 6781852431601 70368744177664 78126195 70368744177664 2604199 8388608 15 8388608 

noncomputable def Ns240p1963 := @Enclosure.Real.IsNear.mulLit_ff qz231 qz231 2604199 8388608 15 8388608 2604199 8388608 15 8388608 6781852431601 70368744177664 

noncomputable def Ns240p1964 := nat_lit 91001656595812410994251321105932851054693904471349777659312800276015136772973053692871607997121 

noncomputable def Ns240p1965 := nat_lit 377081455383671671078493991446579995124675830673555048604766425940305043144392184984130241 

noncomputable def Ns240p1966 := nat_lit 550087895436200102624665548615886857086197943643489524353139860171732269791539258934738961715905 

noncomputable def Ns240p1967 := BSN.cos_dyadic_bound_t 29154321 16777216 4 3 8388608 3240000 Ns240p1964 Ns240p303 Ns240p1965 Ns240p1966 Ns240p306 Ns240p1965 1393871 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 29154321) qz627 0 3 Ns240p1964 Ns240p303 Ns240p1965 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 29154321) (BSN.cosOddQ 16777216) 0 3 Ns240p1966 Ns240p306 Ns240p1965 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p1968 := @Ns240p1955 1011457216 54358179840000 1393871 8388608 15804019 849346560000 (@Ns240p1956 307 16777216 Bool.true 1393871 8388608 1 3240000 (@Ns240p1959 Ns240p438 29154321 16777216 307 16777216 (@Ns240p1960 70368744177664 203955315 70368744177664 Ns240p1957 Ns240p180 Ns240p1958 Ns240p438 RS241to252.d43 (@Ns240p1961 0 1 311388778311920 19461798644495 70368744177664 203955315 70368744177664 (@Ns240p1962 126363911656180809728 15063752133391 70368744177664 203955315 70368744177664 (@Ns240p1963 78126195 70368744177664 (Ns240p1947 rfl rfl) (Ns240p1947 rfl rfl) rfl) (Ns240p1947 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 29154321 16777216) (BSN.cos_neg_of_bound 29154321 16777216 Bool.true 1393871 8388608 1 3240000 (Ns240p1967 rfl rfl)) rfl rfl) 

noncomputable def Ns240p1969 := @Ns240p1932 504173830855704809381 Ns240p1862 (Ns240p1933 qz29 (@Enclosure.Real.IsNear.of_eq qz553 (@Inv.inv Real Real.instInv (Real.sqrt qz235)) Bool.false 5498379 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz230 (BSN.t_div_two_pi_nonneg qz229 544654 1000 qz232)) Ns240p1937) rfl) (@Ns240p1938 140737488355328 457894089469831 7124835347988480000 (BSN.correction_mk qz231 (BSN.cos_two_pi_p_ne_zero_mk qz229 544654 1000 9 qz232 rfl rfl (@BSN.floor_sqrt_eq_dec qz229 544654 1000 9 qz232 rfl rfl rfl))) (@Ns240p1939 16777216 1393871 8388608 15804019 849346560000 63080506062117 140737488355328 457894089469831 7124835347988480000 Ns240p1954 (Ns240p1968 rfl) rfl)) 

noncomputable def Ns240p1970 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz229) (hardyZApproximantRS₀ qz229) Bool.false 4131970353345770931863 2361183241434822606848 33772523762985713897381 Ns240p1862 (@Eq.refl Real (hardyZApproximantRS₀ qz229)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz229) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz229) qz229 9) (@HMul.hMul Real Real Real qz5 qz549 (Zeta.RiemannSiegel.correction qz231))) Bool.false 4131970353345770931863 2361183241434822606848 33772523762985713897381 Ns240p1862 (BSN.hardyZApproximantRS₀_eq qz229 9 (@BSN.floor_sqrt_eq_dec qz229 544654 1000 9 qz232 rfl rfl rfl)) (@Ns240p1864 4131970353345770931863 2361183241434822606848 33772523762985713897381 Ns240p1862 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz229) qz229 9) (@HAdd.hAdd Real Real Real qz360 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz229) qz229 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz229) qz229 9)) Bool.false 26894965 16777216 93387 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz229) qz229 9) (Ns240p1931 (Ns240p1930 rfl) rfl rfl)) (Ns240p1969 rfl) rfl rfl)) 

theorem RS241to252.d77 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz229) Bool.false 4131970353345770931863 2361183241434822606848 33772523762985713897381 Ns240p1862 := Ns240p1970 

noncomputable def Ns240p1971 := nat_lit 14941862699704736808960000 

noncomputable def Ns240p1972 := nat_lit 26801739902680745317914116096 

noncomputable abbrev qz861 := (Enclosure.sfrac Bool.false 546062 1000)

noncomputable abbrev qz744 := qz861

noncomputable abbrev qz558 := qz744

noncomputable abbrev qz243 := qz558

noncomputable abbrev qz862 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 546062 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz745 := qz862

noncomputable abbrev qz559 := qz745

noncomputable abbrev qz244 := qz559

noncomputable abbrev qz863 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 546062 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz746 := qz863

noncomputable abbrev qz560 := qz746

noncomputable abbrev qz245 := qz560

noncomputable abbrev qz561 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz618 qz244 qz8))

noncomputable def Ns240p1973 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz243) qz243 9) (@HMul.hMul Real Real Real qz5 qz561 (Zeta.RiemannSiegel.correction qz245)) 100476041 67108864 23405 16777216 42521255004167878125 295147905179352825856 267817688996566922243 Ns240p1971 Ns240p1972 

noncomputable def Ns240p1974 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 546062 1000 120 161 134217728 67108864 2251799813685248 Bool.false 126919006624 1810 

noncomputable def Ns240p1975 := Ns240p1974 279097919 42 47453128 8 294906479 42 44739240 8 Bool.true 65958353 76604 Bool.true 186315524 Bool.true 174792136 7074237752028440 1 Bool.false 24377138 Bool.false Bool.false 129408928 Bool.true Bool.true 100476041 

noncomputable def Ns240p1976 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 546062 1000 20 74 134217728 67108864 2251799813685248 Bool.false 126919006624 1810 

noncomputable def Ns240p1977 := Ns240p1976 240485871 42 54794152 8 261175631 42 50729528 8 Bool.true 38733735 57130 Bool.true 184614783 Bool.true 97755945 7074237752028440 1 Bool.false 26047590 Bool.false Bool.false 100164186 Bool.true Bool.true 65958353 

noncomputable def Ns240p1978 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 546062 1000 120 42 134217728 67108864 2251799813685248 Bool.false 126919006624 1810 

noncomputable def Ns240p1979 := Ns240p1978 186065264 42 67108856 8 216015088 42 60023992 8 Bool.true 63266331 33671 Bool.false 16390737 Bool.false 106569646 7074237752028440 1 Bool.false 133218148 Bool.false Bool.false 94085847 Bool.true Bool.true 38733735 

noncomputable def Ns240p1980 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 546062 1000 361 220 134217728 67108864 2251799813685248 Bool.false 126919006624 1810 

noncomputable def Ns240p1981 := Ns240p1980 93032624 42 94906264 8 147453232 42 77490640 16 Bool.true 134217672 1858 Bool.false 8260095 Bool.false 18082742 7074237752028440 1 Bool.false 8254881 Bool.true Bool.false 133001453 Bool.false Bool.true 63266331 

noncomputable def Ns240p1982 := nat_lit 1984732261200940393052937978548484570183246265203973711 

noncomputable def Ns240p1983 := nat_lit 2098868103932217864615510292522315417384541749248000 

noncomputable def Ns240p1984 := nat_lit 23305151837069964226720550159360000 

noncomputable def Ns240p1985 := nat_lit 76356376809861753449350009487618641920 

noncomputable abbrev qz864 := (@Eq.refl Real (Enclosure.sfrac Bool.false 546062 1000))

noncomputable abbrev qz747 := qz864

noncomputable abbrev qz562 := qz747

noncomputable abbrev qz246 := qz562

noncomputable def Ns240p1986 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz243 546062 1000 1192735831376 16000000 1092124 4000 2000 Ns240p1984 Ns240p1985 qz246 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns240p1987 := nat_lit 40647316709395259249724169800672963997352883511377381601280 

noncomputable abbrev qz748 := (Real.log (Enclosure.sfrac Bool.false 1192735831376 16000000))

noncomputable abbrev qz749 := (@Nat.cast Real Real.instNatCast 1092124)

noncomputable abbrev qz750 := (Enclosure.sfrac Bool.false 546062 2000)

noncomputable abbrev qz247 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 546062 4000) qz748) (@HMul.hMul Real Real Real qz344 qz358 (@HSub.hSub Real Real Real qz350 qz355 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz356 qz749))))) qz750)

noncomputable abbrev qz563 := (@HSub.hSub Real Real Real qz11 qz247 (@HMul.hMul Real Real Real qz5 qz750 (Real.log Real.pi)))

noncomputable def Ns240p1988 := @Enclosure.Real.IsNear.addLit_ft_p qz563 (Enclosure.sfrac Bool.true Ns240p1984 Ns240p1985) 532337068981770013459 562949953421312000 1118161615897430987 82944000000000000000000 Ns240p1984 Ns240p1985 0 1 Ns240p1987 

noncomputable def Ns240p1989 := nat_lit 3572453596445622231249820057600 

noncomputable abbrev qz564 := (@HMul.hMul Real Real Real qz5 qz750 (Real.log Real.pi))

noncomputable def Ns240p1990 := @Enclosure.Real.IsNear.subLit_ff_p qz247 qz564 141657048852852064823 112589990684262400 432861114434213 81000000000000000000 10487328486591 33554432000 273031 33554432000 Ns240p1989 532337068981770013459 562949953421312000 

noncomputable def Ns240p1991 := nat_lit 1416570488528520648230000 

noncomputable abbrev qz248 := (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 546062 4000) qz748) (@HMul.hMul Real Real Real qz344 qz358 (@HSub.hSub Real Real Real qz350 qz355 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz356 qz749)))))

noncomputable def Ns240p1992 := @Enclosure.Real.IsNear.subLit_ff_p qz248 qz750 861988032996834560787 562949953421312000 432861114434213 81000000000000000000 546062 2000 0 1 Ns240p1991 141657048852852064823 112589990684262400 432861114434213 81000000000000000000 

noncomputable def Ns240p1993 := nat_lit 1941024492101185469207118621941170176 

noncomputable def Ns240p1994 := nat_lit 27126292222559362045968384 

noncomputable def Ns240p1995 := nat_lit 378530077578148503172763113567237169482836974960640 

noncomputable def Ns240p1996 := nat_lit 523286787288714292381672187719507726938375979008 

noncomputable def Ns240p1997 := nat_lit 1295681677253769343367298829191192617570992128 

noncomputable def Ns240p1998 := BSN.log_dyadic_bound 144159831376 2241311831376 3 2 Ns240p1995 67108864 25920000 Ns240p1996 Ns240p1997 8644737 2385471662752 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 144159831376) (BSN.artanhQ 2241311831376) 0 2 Ns240p1996 Ns240p1995 Ns240p1997 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns240p1999 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 546062 4000) qz748 546062 4000 0 1 3157916039060727 281474976710656 195312581 5062500000000000 862208974060789353537 562949953421312000 53326389303011 10125000000000000000 (Enclosure.Real.IsNear.const Bool.false 546062 4000) (BSN.isNear_log_sfrac 1192735831376 16000000 3157916039060727 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1192735831376) qz354)) Bool.false Ns240p1994 Ns240p92 1000000414720000 25920000000000000000000 3157916039060727 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1192735831376 16000000 16 2385471662752 2097152000000 8644737 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns240p1998 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p2000 := BSN.arctan_dyadic_bound_f 1000 1092124 1 0 8388608 3240000 0 1 1 0 1 1 7681 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1092124) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1092124) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz751 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1092124)))

noncomputable def Ns240p2001 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz751 884279719003555 562949953421312 1 2000000000000000 7681 8388608 1 3240000 7413551906478744403968 883764255819171 562949953421312 50000000081 162000000000000000 qz16 (Ns240p2000 rfl) rfl rfl 

noncomputable def Ns240p2002 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 546062 4000) qz748) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz11 qz14 qz751)) 862208974060789353537 562949953421312000 53326389303011 10125000000000000000 883764255819171 2251799813685248 50000000081 648000000000000000 Ns240p1993 861988032996834560787 562949953421312000 432861114434213 81000000000000000000 (Ns240p1999 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 qz751) 1 4 0 1 883764255819171 562949953421312 50000000081 162000000000000000 883764255819171 2251799813685248 50000000081 648000000000000000 qz359 Ns240p2001 rfl) 

noncomputable def Ns240p2003 := @Ns240p1988 Ns240p1982 Ns240p1983 1118161615897430987 82944000000000000000000 (@Ns240p1990 1118161615897430987 82944000000000000000000 (Ns240p1992 (Ns240p2002 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 546062 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz750 (Real.log Real.pi) 546062 2000 0 1 38410761 33554432 1 33554432 10487328486591 33554432000 273031 33554432000 (Enclosure.Real.IsNear.const Bool.false 546062 2000) RS241to252.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns240p1984 Ns240p1985) 

noncomputable def Ns240p2004 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz243) Bool.false Ns240p1982 Ns240p1983 1118161615897430987 82944000000000000000000 3966218957 4194304 227 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz243) (@HAdd.hAdd Real Real Real qz360 qz563 (Enclosure.sfrac Bool.true Ns240p1984 Ns240p1985)) Bool.false Ns240p1982 Ns240p1983 1118161615897430987 82944000000000000000000 Ns240p1986 (Ns240p2003 rfl rfl)) 

noncomputable def Ns240p2005 := BSN.cos_dyadic_bound_f 30903254 34359738368 1 0 16777216 6486329 0 1 1 0 1 1 16777209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 30903254) (BSN.cosEvenQ 34359738368) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 30903254) (BSN.cosOddQ 34359738368) 0 0 rfl) rfl rfl 

noncomputable def Ns240p2006 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz243) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3966218957) qz418) Bool.false 3966218957 4194304 227 16777216 Bool.true 16777209 16777216 1 3240000 (Ns240p2004 rfl) (Enclosure.sfrac_false_div 3966218957 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3966218957) qz418) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 543655810979399204864) qz661) 226375608064910080 72057594037927936 Bool.false 16777209 16777216 150 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q2 3966218957 4194304 226375608064910080 72057594037927936 150 543655810979399204864 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777209 16777216 543655810979399204864 604462909807314587353088 30903254 34359738368 6486329 6480000 (Ns240p2005 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns240p2007 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz243) Bool.false Ns240p1982 Ns240p1983 1118161615897430987 82944000000000000000000 126919006624 134217728 1810 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz243) (@HAdd.hAdd Real Real Real qz360 qz563 (Enclosure.sfrac Bool.true Ns240p1984 Ns240p1985)) Bool.false Ns240p1982 Ns240p1983 1118161615897430987 82944000000000000000000 Ns240p1986 (Ns240p2003 rfl rfl)) 

noncomputable def Ns240p2008 := Ns240p1981 33671 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 361 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 8254881 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 220 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133001453 134217728) qz246 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 1) Bool.true 16777209 16777216 11754019 849346560000 134217672 134217728 1858 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz243)) Bool.true 16777209 16777216 11754019 849346560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz243) qz243) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz243)) Bool.true 16777209 16777216 752257216 54358179840000 16777209 16777216 11754019 849346560000 (Ns240p2006 rfl rfl) rfl)) rfl) (Ns240p2007 rfl) RS241to252.d7 

noncomputable def Ns240p2009 := nat_lit 4655219558245432867751450625 

noncomputable def Ns240p2010 := BSN.sin_dyadic_bound_f 8260095 134217728 2 1 134217728 67108864 Ns240p2009 Ns240p114 Ns240p2009 Ns240p2009 Ns240p115 Ns240p2009 8254881 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 8260095) qz365 0 1 Ns240p2009 Ns240p114 Ns240p2009 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 8260095) qz366 0 1 Ns240p2009 Ns240p115 Ns240p2009 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2011 := nat_lit 106919555296585329374336782096 

noncomputable def Ns240p2012 := BSN.cos_dyadic_bound_f 18082742 134217728 2 1 134217728 67108864 Ns240p2011 Ns240p146 Ns240p2011 Ns240p2011 Ns240p147 Ns240p2011 133001453 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 18082742) qz367 0 1 Ns240p2011 Ns240p146 Ns240p2011 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 18082742) qz368 0 1 Ns240p2011 Ns240p147 Ns240p2011 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2013 := nat_lit 72176185716502831732087242561 

noncomputable def Ns240p2014 := BSN.cos_dyadic_bound_f 16390737 134217728 2 1 134217728 67108864 Ns240p2013 Ns240p146 Ns240p2013 Ns240p2013 Ns240p147 Ns240p2013 133218148 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 16390737) qz367 0 1 Ns240p2013 Ns240p146 Ns240p2013 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 16390737) qz368 0 1 Ns240p2013 Ns240p147 Ns240p2013 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2015 := nat_lit 70337291533948846605323180287082373156366306611277087596385010729216 

noncomputable def Ns240p2016 := nat_lit 16636738304505978726135392182049599654244644745311388385564180736 

noncomputable def Ns240p2017 := nat_lit 210978601125237527858517270076883020269790430544340640012383903826176 

noncomputable def Ns240p2018 := BSN.cos_dyadic_bound_f 106569646 134217728 3 2 134217728 67108864 Ns240p2015 Ns240p124 Ns240p2016 Ns240p2017 Ns240p127 Ns240p2016 94085847 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 106569646) qz367 0 2 Ns240p2015 Ns240p124 Ns240p2016 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 106569646) qz368 0 2 Ns240p2017 Ns240p127 Ns240p2016 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2019 := Ns240p1979 57130 BSN.abs_quadSignPos (BSN.cos_quad_nat0 120 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133218148 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 42 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 94085847 134217728) qz246 rfl rfl (Ns240p2008 RS241to252.d9 RS241to252.d11 RS241to252.d13 RS241to252.d17 (Ns240p2010 rfl rfl) (Ns240p2012 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns240p2007 rfl) RS241to252.d19 RS241to252.d21 RS241to252.d23 RS241to252.d25 RS241to252.d17 (Ns240p2014 rfl rfl) (Ns240p2018 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns240p2020 := nat_lit 2446782222024831906133451897325819129247648475652900507940795712708419165400007735215056322051461603427841 

noncomputable def Ns240p2021 := nat_lit 1567464413555093568129050131466447139932112930326841388308896664868956151156745019195024848571368961 

noncomputable def Ns240p2022 := nat_lit 14822764161323464022503849625605464876670119003125462088341585611232849031348625240768738125134810606503425 

noncomputable def Ns240p2023 := BSN.cos_dyadic_bound_f 184614783 134217728 4 3 134217728 67108864 Ns240p2020 Ns240p130 Ns240p2021 Ns240p2022 Ns240p133 Ns240p2021 26047590 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 184614783) qz367 0 3 Ns240p2020 Ns240p130 Ns240p2021 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 184614783) qz368 0 3 Ns240p2022 Ns240p133 Ns240p2021 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2024 := nat_lit 49795978030104347936823603873769326080382727311141598184536298690625 

noncomputable def Ns240p2025 := nat_lit 8339603960835680008300588929470911017145985632926220561437890625 

noncomputable def Ns240p2026 := nat_lit 149371254882391372450454210443449036419113889962158942112486020290625 

noncomputable def Ns240p2027 := BSN.cos_dyadic_bound_f 97755945 134217728 3 2 134217728 67108864 Ns240p2024 Ns240p124 Ns240p2025 Ns240p2026 Ns240p127 Ns240p2025 100164186 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 97755945) qz367 0 2 Ns240p2024 Ns240p124 Ns240p2025 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 97755945) qz368 0 2 Ns240p2026 Ns240p127 Ns240p2025 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2028 := Ns240p1977 76604 BSN.abs_quadSignPos (BSN.cos_quad_nat0 20 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 26047590 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 74 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 100164186 134217728) qz246 rfl rfl (Ns240p2019 rfl rfl) (Ns240p2007 rfl) RS241to252.d27 RS241to252.d29 RS241to252.d31 RS241to252.d33 RS241to252.d17 (Ns240p2023 rfl rfl) (Ns240p2027 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p2029 := nat_lit 2538400282863975920261227335873732159216497184852607674960397961694792483584503252359080399836317541728256 

noncomputable def Ns240p2030 := nat_lit 1749800382663855340024783138812889457440071199510979186811329339685491703133710634446081576272920576 

noncomputable def Ns240p2031 := nat_lit 15376977913348328510284976158740207201935939820228209480303044623876084727630402187831137633206746459668480 

noncomputable def Ns240p2032 := BSN.cos_dyadic_bound_f 186315524 134217728 4 3 134217728 67108864 Ns240p2029 Ns240p130 Ns240p2030 Ns240p2031 Ns240p133 Ns240p2030 24377138 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 186315524) qz367 0 3 Ns240p2029 Ns240p130 Ns240p2030 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 186315524) qz368 0 3 Ns240p2031 Ns240p133 Ns240p2030 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2033 := nat_lit 5105974722725962316772980934018532597404280831066858181403303111511298962940282078384059884562073251741696 

noncomputable def Ns240p2034 := nat_lit 813322290242047920154032949052823345827571345865985755216007213751264953131449244591735975073284096 

noncomputable def Ns240p2035 := nat_lit 25514872884751779596859720106896306621923923099638156995143989077146916854101578936858722533277252930502656 

noncomputable def Ns240p2036 := BSN.sin_dyadic_bound_f 174792136 134217728 4 3 134217728 67108864 Ns240p2033 Ns240p118 Ns240p2034 Ns240p2035 Ns240p121 Ns240p2034 129408928 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 174792136) qz365 0 3 Ns240p2033 Ns240p118 Ns240p2034 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 174792136) qz366 0 3 Ns240p2035 Ns240p121 Ns240p2034 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2037 := Ns240p1975 93620 BSN.abs_quadSignPos (BSN.cos_quad_nat0 120 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 24377138 134217728) BSN.abs_quadSignNeg qz662 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 129408928 134217728) qz246 rfl rfl (Ns240p2028 rfl) (Ns240p2007 rfl) RS241to252.d35 RS241to252.d37 RS241to252.d39 RS241to252.d41 RS241to252.d17 (Ns240p2032 rfl rfl) (Ns240p2036 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p2038 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 9) 100476041 134217728 93620 134217728 100476041 134217728 93620 134217728 26971331882909696 100476041 67108864 23405 16777216 (Ns240p2037 rfl) 

noncomputable def Ns240p2039 := @Enclosure.Real.IsNear.mulLit_tf qz561 (Zeta.RiemannSiegel.correction qz245) 5494831 16777216 1 16777216 7738409971875 17592186044416 24334313768987 445302209249280000 42521255004167878125 295147905179352825856 

noncomputable abbrev qz565 := (@HPow.hPow Real Real Real qz618 qz244 qz8)

noncomputable def Ns240p2040 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz565 1 1 0 1 5494831 16777216 1 16777216 5494831 16777216 1 16777216 

noncomputable def Ns240p2041 := @Enclosure.Real.IsNear.sqrt_image qz244 729041096487 8388608000 273031 8388608000 78202542 78202572 8388608 (@Enclosure.Real.IsNear.of_eq qz244 (@HMul.hMul Real Real Real qz5 qz243 qz3) Bool.false 729041096487 8388608000 273031 8388608000 (BSN.t_div_two_pi_mk qz243 546062 1000 qz246) (@Enclosure.Real.IsNear.mulLit_ff qz243 qz3 546062 1000 0 1 2670177 16777216 1 16777216 729041096487 8388608000 273031 8388608000 (Enclosure.Real.IsNear.const Bool.false 546062 1000) RS241to252.d44 rfl)) 

noncomputable abbrev qz865 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 546062 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz752 := qz865

noncomputable abbrev qz566 := qz752

noncomputable abbrev qz249 := qz566

noncomputable def Ns240p2042 := @Enclosure.Real.IsNear.sqrt_image qz249 78202557 8388608 15 8388608 25612701 25612707 8388608 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 156405114 16777216 30 16777216 78202557 8388608 15 8388608 (Ns240p2041 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns240p2043 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz249) 800397 262144 3 8388608 2747415 2747416 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz249) Bool.false 51225408 16777216 6 16777216 800397 262144 3 8388608 (Ns240p2042 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns240p2044 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 5494831 16777216 1 16777216 5494831 16777216 1 16777216 (Ns240p2043 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz344 qz340 qz560))

noncomputable abbrev qz753 := (@HMul.hMul Real Real Real qz811 qz863 qz863)

noncomputable abbrev qz567 := (@HSub.hSub Real Real Real qz619 (@HSub.hSub Real Real Real qz619 qz753 qz746) qz626)

noncomputable abbrev qz251 := (Real.cos (@HMul.hMul Real Real Real qz344 qz340 qz567))

noncomputable def Ns240p2045 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz245) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz250) qz251) Bool.false 7738409971875 

noncomputable def Ns240p2046 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz250) qz251 38149375 16777216 1011 

noncomputable abbrev qz754 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz250))

noncomputable def Ns240p2047 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz250) (@Neg.neg Real Real.instNeg qz754) Bool.true 38149375 16777216 1011 16777216 (BSN.inv_eq_neg_inv_neg qz250) 

noncomputable def Ns240p2048 := @Enclosure.Real.IsNear.recentre' qz754 Bool.false 38149375 16777216 1011 16777216 38149375 16777216 

noncomputable def Ns240p2049 := @Enclosure.Real.IsNear.recentre' qz250 Bool.true 7378233 16777216 316188608 27179089920000 7378233 16777216 4940447 424673280000 

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz344 qz340 qz560)

noncomputable def Ns240p2050 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8498275) qz418) Bool.false 8498275 4194304 95 8388608 Bool.true 7378233 16777216 1 

noncomputable def Ns240p2051 := nat_lit 16191645246355887401733393 

noncomputable def Ns240p2052 := nat_lit 1441151880758558720000000000000 

noncomputable def Ns240p2053 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz245 884279719003555 140737488355328 1 500000000000000 2705085 8388608 15 8388608 2392051803680731577175 1180591620717411303424 Ns240p2051 

noncomputable def Ns240p2054 := @Enclosure.Real.IsNear.subLit_ff_p qz249 qz1 78202557 8388608 15 8388608 9 1 0 1 2705085 2705085 8388608 15 

noncomputable def Ns240p2055 := @Ns240p2054 8388608 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 156405114 16777216 30 16777216 78202557 8388608 15 8388608 (Ns240p2041 rfl rfl rfl rfl rfl rfl) rfl) qz373 

noncomputable def Ns240p2056 := @Enclosure.Real.IsNear.recentre' qz252 Bool.false 2392051803680731577175 1180591620717411303424 Ns240p2051 Ns240p2052 8498275 4194304 95 8388608 (@Ns240p2053 Ns240p2052 RS241to252.d43 (Ns240p2055 rfl rfl) rfl) 

noncomputable def Ns240p2057 := nat_lit 59921405395080932117985656692257065082321 

noncomputable def Ns240p2058 := nat_lit 167255588988979673561517887044862711294853120 

noncomputable def Ns240p2059 := nat_lit 1170789122922857714930625209314038979063971840 

noncomputable def Ns240p2060 := BSN.sin_dyadic_bound_f 15645717981 34359738368 2 1 16777216 6486329 Ns240p2057 Ns240p2058 Ns240p2057 Ns240p2057 Ns240p2059 Ns240p2057 7378233 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 15645717981) qz361 0 1 Ns240p2057 Ns240p2058 Ns240p2057 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 15645717981) qz362 0 1 Ns240p2057 Ns240p2059 Ns240p2057 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2061 := @Ns240p2050 3240000 (Ns240p2056 rfl) (Enclosure.sfrac_false_div 8498275 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8498275) qz418) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 275242381536259452436480) qz661) 226375608064910080 72057594037927936 Bool.false 7378233 16777216 0 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 8498275 4194304 226375608064910080 72057594037927936 0 275242381536259452436480 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 7378233 16777216 275242381536259452436480 604462909807314587353088 15645717981 34359738368 6486329 6480000 (Ns240p2060 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns240p2062 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz250) 7378233 16777216 4940447 424673280000 19074182 19075193 8388608 (@Enclosure.Real.IsNear.neg qz250 Bool.true 7378233 16777216 4940447 424673280000 (Ns240p2049 (Ns240p2061 rfl rfl) rfl)) 

noncomputable def Ns240p2063 := Ns240p2047 (@Enclosure.Real.IsNear.neg qz754 Bool.false 38149375 16777216 1011 16777216 (@Ns240p2048 1011 16777216 (Ns240p2062 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p2064 := @Enclosure.Real.IsNear.recentre' qz251 Bool.true 1622760 8388608 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz344 qz340 qz567)

noncomputable def Ns240p2065 := @Enclosure.Real.IsNear.cos_image qz253 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 29619699)) qz363) Bool.true 29619699 16777216 

noncomputable def Ns240p2066 := nat_lit 17484384776414533130823362245 

noncomputable def Ns240p2067 := nat_lit 5585629026946680799106542578689393 

noncomputable def Ns240p2068 := @Enclosure.Real.IsNear.recentre' qz253 Bool.true Ns240p2066 Ns240p180 Ns240p2067 

noncomputable abbrev qz254 := qz567

noncomputable def Ns240p2069 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz254 884279719003555 140737488355328 1 500000000000000 19772459325559 

noncomputable abbrev qz568 := (@HSub.hSub Real Real Real qz619 qz753 qz746)

noncomputable abbrev qz255 := qz568

noncomputable def Ns240p2070 := @Enclosure.Real.IsNear.subLit_tf qz255 qz27 15374412814455 70368744177664 206981895 70368744177664 1 16 

noncomputable abbrev qz569 := qz753

noncomputable abbrev qz256 := qz569

noncomputable def Ns240p2071 := @Enclosure.Real.IsNear.subLit_ff_n qz256 qz245 7317484857225 70368744177664 81152775 70368744177664 2705085 8388608 15 8388608 

noncomputable def Ns240p2072 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz245 2705085 8388608 15 8388608 2705085 8388608 15 8388608 7317484857225 70368744177664 

noncomputable def Ns240p2073 := nat_lit 96987033027151963999273173861924241387014874322095635772661952894215071509385645183463668533681 

noncomputable def Ns240p2074 := nat_lit 456002989727812338253947029221134236444788109737567758418286639369985596315214704538503601 

noncomputable def Ns240p2075 := nat_lit 586130412251384092719723034412655328893259314007554905814897124757408927237156398826236696021425 

noncomputable def Ns240p2076 := BSN.cos_dyadic_bound_t 29619699 16777216 4 3 8388608 3240000 Ns240p2073 Ns240p303 Ns240p2074 Ns240p2075 Ns240p306 Ns240p2074 1622760 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 29619699) qz627 0 3 Ns240p2073 Ns240p303 Ns240p2074 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 29619699) (BSN.cosOddQ 16777216) 0 3 Ns240p2075 Ns240p306 Ns240p2074 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2077 := @Ns240p2064 128457152 6794772480000 202845 1048576 2007143 106168320000 (@Ns240p2065 39 2097152 Bool.true 1622760 8388608 1 3240000 (@Ns240p2068 Ns240p183 29619699 16777216 39 2097152 (@Ns240p2069 70368744177664 206981895 70368744177664 Ns240p2066 Ns240p180 Ns240p2067 Ns240p183 RS241to252.d43 (@Ns240p2070 0 1 316359349208944 19772459325559 70368744177664 206981895 70368744177664 (@Ns240p2071 128969922330639728640 15374412814455 70368744177664 206981895 70368744177664 (@Ns240p2072 81152775 70368744177664 (Ns240p2055 rfl rfl) (Ns240p2055 rfl rfl) rfl) (Ns240p2055 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 29619699 16777216) (BSN.cos_neg_of_bound 29619699 16777216 Bool.true 1622760 8388608 1 3240000 (Ns240p2076 rfl rfl)) rfl rfl) 

noncomputable def Ns240p2078 := @Ns240p2039 267817688996566922243 Ns240p1971 (Ns240p2040 qz29 (@Enclosure.Real.IsNear.of_eq qz565 (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 5494831 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz244 (BSN.t_div_two_pi_nonneg qz243 546062 1000 qz246)) Ns240p2044) rfl) (@Ns240p2045 17592186044416 24334313768987 445302209249280000 (BSN.correction_mk qz245 (BSN.cos_two_pi_p_ne_zero_mk qz243 546062 1000 9 qz246 rfl rfl (@BSN.floor_sqrt_eq_dec qz243 546062 1000 9 qz246 rfl rfl rfl))) (@Ns240p2046 16777216 202845 1048576 2007143 106168320000 7738409971875 17592186044416 24334313768987 445302209249280000 Ns240p2063 (Ns240p2077 rfl) rfl)) 

noncomputable def Ns240p2079 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz243) (hardyZApproximantRS₀ qz243) Bool.true 399377046565424581139 295147905179352825856 21112414103955363722243 Ns240p1971 (@Eq.refl Real (hardyZApproximantRS₀ qz243)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz243) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz243) qz243 9) (@HMul.hMul Real Real Real qz5 qz561 (Zeta.RiemannSiegel.correction qz245))) Bool.true 399377046565424581139 295147905179352825856 21112414103955363722243 Ns240p1971 (BSN.hardyZApproximantRS₀_eq qz243 9 (@BSN.floor_sqrt_eq_dec qz243 546062 1000 9 qz246 rfl rfl rfl)) (@Ns240p1973 399377046565424581139 295147905179352825856 21112414103955363722243 Ns240p1971 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz243) qz243 9) (@HAdd.hAdd Real Real Real qz360 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 9)) Bool.true 100476041 67108864 23405 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz243) qz243 9) (Ns240p2038 (Ns240p2037 rfl) rfl rfl)) (Ns240p2078 rfl) rfl rfl)) 

theorem RS241to252.d78 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz243) Bool.true 399377046565424581139 295147905179352825856 21112414103955363722243 Ns240p1971 := Ns240p2079 

noncomputable def Ns240p2080 := nat_lit 9961241799803157872640000 

noncomputable def Ns240p2081 := nat_lit 6952708755665800658675564544 

noncomputable abbrev qz866 := (Enclosure.sfrac Bool.false 547468 1000)

noncomputable abbrev qz755 := qz866

noncomputable abbrev qz570 := qz755

noncomputable abbrev qz257 := qz570

noncomputable abbrev qz867 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 547468 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz756 := qz867

noncomputable abbrev qz571 := qz756

noncomputable abbrev qz258 := qz571

noncomputable abbrev qz868 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 547468 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz757 := qz868

noncomputable abbrev qz572 := qz757

noncomputable abbrev qz259 := qz572

noncomputable abbrev qz573 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz618 qz258 qz8))

noncomputable def Ns240p2082 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz257) qz257 9) (@HMul.hMul Real Real Real qz5 qz573 (Zeta.RiemannSiegel.correction qz259)) 18810249 33554432 93865 67108864 41750167829209099575 295147905179352825856 161298012683021337767 Ns240p2080 Ns240p2081 

noncomputable def Ns240p2083 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz257) qz257 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 547468 1000 120 161 134217728 67108864 2251799813685248 Bool.false 127340409895 1815 

noncomputable def Ns240p2084 := Ns240p2083 279097919 42 47453128 8 294906479 42 44739240 8 Bool.false 61684362 76805 Bool.true 157323928 Bool.true 168027374 7074237752028440 1 Bool.false 52098882 Bool.false Bool.false 127450803 Bool.true Bool.false 37620498 

noncomputable def Ns240p2085 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz257) qz257 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 547468 1000 20 74 134217728 67108864 2251799813685248 Bool.false 127340409895 1815 

noncomputable def Ns240p2086 := Ns240p2085 240485871 42 54794152 8 261175631 42 50729528 8 Bool.false 69859940 57280 Bool.true 101334646 Bool.true 43565611 7074237752028440 1 Bool.false 97746772 Bool.false Bool.false 127209126 Bool.true Bool.false 61684362 

noncomputable def Ns240p2087 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz257) qz257 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 547468 1000 120 43 134217728 67108864 2251799813685248 Bool.false 127340409895 1815 

noncomputable def Ns240p2088 := Ns240p2087 186065264 42 67108856 8 216015088 42 60023992 8 Bool.false 46735669 33761 Bool.false 176186247 Bool.false 13426990 7074237752028440 1 Bool.false 34259105 Bool.false Bool.false 13404605 Bool.false Bool.false 69859940 

noncomputable def Ns240p2089 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz257) qz257 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 547468 1000 362 221 134217728 67108864 2251799813685248 Bool.false 127340409895 1815 

noncomputable def Ns240p2090 := Ns240p2089 93032624 42 94906264 8 147453232 42 77490640 16 Bool.false 134217656 1866 Bool.false 88030782 Bool.false 21338054 7074237752028440 1 Bool.false 106369065 Bool.true Bool.false 21248281 Bool.true Bool.false 46735669 

noncomputable def Ns240p2091 := nat_lit 987443497110513112595497399102617731454738416163223 

noncomputable def Ns240p2092 := nat_lit 1040772703803357398674871316337935693838811136000 

noncomputable def Ns240p2093 := nat_lit 23606731030743950466091285872640000 

noncomputable def Ns240p2094 := nat_lit 77543609127652451297258683766270853120 

noncomputable abbrev qz869 := (@Eq.refl Real (Enclosure.sfrac Bool.false 547468 1000))

noncomputable abbrev qz758 := qz869

noncomputable abbrev qz574 := qz758

noncomputable abbrev qz260 := qz574

noncomputable def Ns240p2095 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz257 547468 1000 1198885844096 16000000 1094936 4000 2000 Ns240p2093 Ns240p2094 qz260 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns240p2096 := nat_lit 10354095524261533975529362807614264903778837894667677204480 

noncomputable abbrev qz759 := (Real.log (Enclosure.sfrac Bool.false 1198885844096 16000000))

noncomputable abbrev qz760 := (@Nat.cast Real Real.instNatCast 1094936)

noncomputable abbrev qz761 := (Enclosure.sfrac Bool.false 547468 2000)

noncomputable abbrev qz261 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 547468 4000) qz759) (@HMul.hMul Real Real Real qz344 qz358 (@HSub.hSub Real Real Real qz350 qz355 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz356 qz760))))) qz761)

noncomputable abbrev qz575 := (@HSub.hSub Real Real Real qz11 qz261 (@HMul.hMul Real Real Real qz5 qz761 (Real.log Real.pi)))

noncomputable def Ns240p2097 := @Enclosure.Real.IsNear.addLit_ft_p qz575 (Enclosure.sfrac Bool.true Ns240p2093 Ns240p2094) 133526140491715163479 140737488355328000 186837363135846653 13824000000000000000000 Ns240p2093 Ns240p2094 0 1 Ns240p2096 

noncomputable def Ns240p2098 := nat_lit 89607876027034060326499778560 

noncomputable abbrev qz576 := (@HMul.hMul Real Real Real qz5 qz761 (Real.log Real.pi))

noncomputable def Ns240p2099 := @Enclosure.Real.IsNear.subLit_ff_p qz261 qz576 7105057684700679919 5629499534213120 144653184129919 27000000000000000000 5257165625787 16777216000 136867 16777216000 Ns240p2098 133526140491715163479 140737488355328000 

noncomputable abbrev qz262 := (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 547468 4000) qz759) (@HMul.hMul Real Real Real qz344 qz358 (@HSub.hSub Real Real Real qz350 qz355 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz356 qz760)))))

noncomputable def Ns240p2100 := @Enclosure.Real.IsNear.subLit_ff_p qz262 qz761 216151077754974352727 140737488355328000 144653184129919 27000000000000000000 547468 2000 0 1 355252884235033995950000 7105057684700679919 5629499534213120 144653184129919 27000000000000000000 

noncomputable def Ns240p2101 := nat_lit 973457913233033602039790610616942592 

noncomputable def Ns240p2102 := nat_lit 27138727201562487269883904 

noncomputable def Ns240p2103 := nat_lit 13531416530553707514780246044044308268508953496665182653977873469252126638080 

noncomputable def Ns240p2104 := nat_lit 20229255098877775110736401832307001515919822314835245024680246137550012416 

noncomputable def Ns240p2105 := nat_lit 172987931291360068177390820397101352726542259288784570769638623805440 

noncomputable def Ns240p2106 := BSN.log_dyadic_bound 150309844096 2247461844096 4 3 Ns240p2103 67108864 25920000 Ns240p2104 Ns240p2105 8989877 2397771688192 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 150309844096) (BSN.artanhQ 2247461844096) 0 3 Ns240p2104 Ns240p2103 Ns240p2105 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns240p2107 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 547468 4000) qz759 547468 4000 0 1 3159363661143287 281474976710656 195312581 5062500000000000 432412626209698261829 281474976710656000 26731847023727 5062500000000000000 (Enclosure.Real.IsNear.const Bool.false 547468 4000) (BSN.isNear_log_sfrac 1198885844096 16000000 3159363661143287 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1198885844096) qz354)) Bool.false Ns240p2102 Ns240p92 1000000414720000 25920000000000000000000 3159363661143287 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1198885844096 16000000 16 2397771688192 2097152000000 8989877 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns240p2106 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p2108 := BSN.arctan_dyadic_bound_f 1000 1094936 1 0 8388608 3240000 0 1 1 0 1 1 7661 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1094936) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1094936) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz762 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1094936)))

noncomputable def Ns240p2109 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz762 884279719003555 562949953421312 1 2000000000000000 7661 8388608 1 3240000 7413563165477812830208 883765597996451 562949953421312 50000000081 162000000000000000 qz16 (Ns240p2108 rfl) rfl rfl 

noncomputable def Ns240p2110 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 547468 4000) qz759) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz11 qz14 qz762)) 432412626209698261829 281474976710656000 26731847023727 5062500000000000000 883765597996451 2251799813685248 50000000081 648000000000000000 Ns240p2101 216151077754974352727 140737488355328000 144653184129919 27000000000000000000 (Ns240p2107 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 qz762) 1 4 0 1 883765597996451 562949953421312 50000000081 162000000000000000 883765597996451 2251799813685248 50000000081 648000000000000000 qz359 Ns240p2109 rfl) 

noncomputable def Ns240p2111 := @Ns240p2097 Ns240p2091 Ns240p2092 186837363135846653 13824000000000000000000 (@Ns240p2099 186837363135846653 13824000000000000000000 (Ns240p2100 (Ns240p2110 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 547468 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz761 (Real.log Real.pi) 547468 2000 0 1 38410761 33554432 1 33554432 5257165625787 16777216000 136867 16777216000 (Enclosure.Real.IsNear.const Bool.false 547468 2000) RS241to252.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns240p2093 Ns240p2094) 

noncomputable def Ns240p2112 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz257) Bool.false Ns240p2091 Ns240p2092 186837363135846653 13824000000000000000000 3979387809 4194304 57 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz257) (@HAdd.hAdd Real Real Real qz360 qz575 (Enclosure.sfrac Bool.true Ns240p2093 Ns240p2094)) Bool.false Ns240p2091 Ns240p2092 186837363135846653 13824000000000000000000 Ns240p2095 (Ns240p2111 rfl rfl)) 

noncomputable def Ns240p2113 := nat_lit 854965108722126524524412111210190978038032456583118977174206708705932802546543898693379027947416506771428041719490370992373130854400000 

noncomputable def Ns240p2114 := nat_lit 606368887606029551792497224372656513391205172934797213007665538166287488610978272574431755198406264562984495320272896000000000000 

noncomputable def Ns240p2115 := nat_lit 4269526961167618722145638728367529441556934568367107376965580747338054728096550142279943572628567397634564989831811539325973430272000000 

noncomputable def Ns240p2116 := BSN.sin_dyadic_bound_f 53937988020 34359738368 4 3 16777216 6486329 Ns240p2113 Ns240p105 Ns240p2114 Ns240p2115 Ns240p108 Ns240p2114 16777207 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53937988020) qz361 0 3 Ns240p2113 Ns240p105 Ns240p2114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53937988020) qz362 0 3 Ns240p2115 Ns240p108 Ns240p2114 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2117 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz257) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3979387809) qz418) Bool.false 3979387809 4194304 57 4194304 Bool.false 16777207 16777216 1 3240000 (Ns240p2112 rfl) (Enclosure.sfrac_false_div 3979387809 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3979387809) qz418) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 948887120125005542719488) qz661) 226375608064910080 72057594037927936 Bool.false 16777207 16777216 150 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q3 3979387809 4194304 226375608064910080 72057594037927936 150 948887120125005542719488 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777207 16777216 948887120125005542719488 604462909807314587353088 53937988020 34359738368 6486329 6480000 (Ns240p2116 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns240p2118 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz257) Bool.false Ns240p2091 Ns240p2092 186837363135846653 13824000000000000000000 127340409895 134217728 1815 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz257) (@HAdd.hAdd Real Real Real qz360 qz575 (Enclosure.sfrac Bool.true Ns240p2093 Ns240p2094)) Bool.false Ns240p2091 Ns240p2092 186837363135846653 13824000000000000000000 Ns240p2095 (Ns240p2111 rfl rfl)) 

noncomputable def Ns240p2119 := Ns240p2090 33761 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 362 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 106369065 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 221 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 21248281 134217728) qz260 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz257) qz257 1) Bool.false 16777207 16777216 2951161 212336640000 134217656 134217728 1866 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz257) qz257 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz257)) Bool.false 16777207 16777216 2951161 212336640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz257) qz257) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz257)) Bool.false 16777207 16777216 188874304 13589544960000 16777207 16777216 2951161 212336640000 (Ns240p2117 rfl rfl) rfl)) rfl) (Ns240p2118 rfl) RS241to252.d7 

noncomputable def Ns240p2120 := nat_lit 32744237990428680752651751625911528152866087881384474384191322521856 

noncomputable def Ns240p2121 := nat_lit 3606421459495066740524573125458587013034287000602481205490155776 

noncomputable def Ns240p2122 := nat_lit 98225501128367052124474205731483667284572195070152218190162987254016 

noncomputable def Ns240p2123 := BSN.cos_dyadic_bound_f 88030782 134217728 3 2 134217728 67108864 Ns240p2120 Ns240p124 Ns240p2121 Ns240p2122 Ns240p127 Ns240p2121 106369065 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 88030782) qz367 0 2 Ns240p2120 Ns240p124 Ns240p2121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 88030782) qz368 0 2 Ns240p2122 Ns240p127 Ns240p2121 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2124 := nat_lit 207309516827862735420899831056 

noncomputable def Ns240p2125 := BSN.sin_dyadic_bound_f 21338054 134217728 2 1 134217728 67108864 Ns240p2124 Ns240p114 Ns240p2124 Ns240p2124 Ns240p115 Ns240p2124 21248281 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 21338054) qz365 0 1 Ns240p2124 Ns240p114 Ns240p2124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 21338054) qz366 0 1 Ns240p2124 Ns240p115 Ns240p2124 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2126 := nat_lit 2028896523579437799115599496889451880371472459690130683942291109065983315080140425437695808984519299173921 

noncomputable def Ns240p2127 := nat_lit 894672431923438073846132296542653749626242159057881788117810851683848111716900829306998641697361441 

noncomputable def Ns240p2128 := nat_lit 12294156966385110242543578094073684016279900858879746370002290606581478051858590713954059032747236533079585 

noncomputable def Ns240p2129 := BSN.cos_dyadic_bound_f 176186247 134217728 4 3 134217728 67108864 Ns240p2126 Ns240p130 Ns240p2127 Ns240p2128 Ns240p133 Ns240p2127 34259105 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 176186247) qz367 0 3 Ns240p2126 Ns240p130 Ns240p2127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 176186247) qz368 0 3 Ns240p2128 Ns240p133 Ns240p2127 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2130 := nat_lit 32502342455980992223692010000 

noncomputable def Ns240p2131 := BSN.sin_dyadic_bound_f 13426990 134217728 2 1 134217728 67108864 Ns240p2130 Ns240p114 Ns240p2130 Ns240p2130 Ns240p115 Ns240p2130 13404605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 13426990) qz365 0 1 Ns240p2130 Ns240p114 Ns240p2130 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 13426990) qz366 0 1 Ns240p2130 Ns240p115 Ns240p2130 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2132 := Ns240p2088 57280 BSN.abs_quadSignPos (BSN.cos_quad_nat0 120 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 34259105 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 43 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 13404605 134217728) qz260 rfl rfl (Ns240p2119 RS241to252.d9 RS241to252.d11 RS241to252.d13 RS241to252.d17 (Ns240p2123 rfl rfl) (Ns240p2125 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns240p2118 rfl) RS241to252.d19 RS241to252.d21 RS241to252.d23 RS241to252.d25 RS241to252.d17 (Ns240p2129 rfl rfl) (Ns240p2131 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns240p2133 := nat_lit 57499573284883461195256440470101624940103326095732674942194321449216 

noncomputable def Ns240p2134 := nat_lit 11118946419678776796359158766415728289515173479959616926702100736 

noncomputable def Ns240p2135 := nat_lit 172476481961811026032176603092772043363730947940238105592729560146176 

noncomputable def Ns240p2136 := BSN.cos_dyadic_bound_f 101334646 134217728 3 2 134217728 67108864 Ns240p2133 Ns240p124 Ns240p2134 Ns240p2135 Ns240p127 Ns240p2134 97746772 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 101334646) qz367 0 2 Ns240p2133 Ns240p124 Ns240p2134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 101334646) qz368 0 2 Ns240p2135 Ns240p127 Ns240p2134 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2137 := nat_lit 3602261506414522725911286629041 

noncomputable def Ns240p2138 := BSN.cos_dyadic_bound_f 43565611 134217728 2 1 134217728 67108864 Ns240p2137 Ns240p146 Ns240p2137 Ns240p2137 Ns240p147 Ns240p2137 127209126 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 43565611) qz367 0 1 Ns240p2137 Ns240p146 Ns240p2137 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 43565611) qz368 0 1 Ns240p2137 Ns240p147 Ns240p2137 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2139 := Ns240p2086 76805 BSN.abs_quadSignPos (BSN.cos_quad_nat0 20 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 97746772 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 74 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 127209126 134217728) qz260 rfl rfl (Ns240p2132 rfl rfl) (Ns240p2118 rfl) RS241to252.d27 RS241to252.d29 RS241to252.d31 RS241to252.d33 RS241to252.d17 (Ns240p2136 rfl rfl) (Ns240p2138 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p2140 := nat_lit 1289055772711444439201588993193828201309312434799849080838631103187330022629607300022812204862973197418496 

noncomputable def Ns240p2141 := nat_lit 229899154431288640465269029627170163156445761558816567580378587808798761925587301479605867449942016 

noncomputable def Ns240p2142 := nat_lit 7814418943647778234824187894202572481594597312505104555848254129078529664413897194608822725803970511503360 

noncomputable def Ns240p2143 := BSN.cos_dyadic_bound_f 157323928 134217728 4 3 134217728 67108864 Ns240p2140 Ns240p130 Ns240p2141 Ns240p2142 Ns240p133 Ns240p2141 52098882 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 157323928) qz367 0 3 Ns240p2140 Ns240p130 Ns240p2141 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 157323928) qz368 0 3 Ns240p2142 Ns240p133 Ns240p2141 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2144 := nat_lit 782878017951869220282267876035760678986798071002481905356052755595520 

noncomputable def Ns240p2145 := nat_lit 635389920159566408878085262715774118566714627822960606260261765376 

noncomputable def Ns240p2146 := nat_lit 2049366082384161040839184680144500048773458362275739244474764412272896 

noncomputable def Ns240p2147 := BSN.sin_dyadic_bound_f 168027374 134217728 3 2 134217728 67108864 Ns240p2144 Ns240p248 Ns240p2145 Ns240p2146 Ns240p251 Ns240p2145 127450803 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 168027374) qz365 0 2 Ns240p2144 Ns240p248 Ns240p2145 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 168027374) qz366 0 2 Ns240p2146 Ns240p251 Ns240p2145 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2148 := Ns240p2084 93865 BSN.abs_quadSignPos (BSN.cos_quad_nat0 120 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 52098882 134217728) BSN.abs_quadSignNeg qz662 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 127450803 134217728) qz260 rfl rfl (Ns240p2139 rfl) (Ns240p2118 rfl) RS241to252.d35 RS241to252.d37 RS241to252.d39 RS241to252.d41 RS241to252.d17 (Ns240p2143 rfl rfl) (Ns240p2147 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p2149 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz257) qz257 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz257) qz257 9) 37620498 134217728 93865 134217728 37620498 134217728 93865 134217728 10098675535577088 18810249 33554432 93865 67108864 (Ns240p2148 rfl) 

noncomputable def Ns240p2150 := @Enclosure.Real.IsNear.mulLit_tf qz573 (Zeta.RiemannSiegel.correction qz259) 1372825 4194304 1 8388608 30411864461391 70368744177664 87839721328513 1781208836997120000 41750167829209099575 295147905179352825856 

noncomputable abbrev qz577 := (@HPow.hPow Real Real Real qz618 qz258 qz8)

noncomputable def Ns240p2151 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz577 1 1 0 1 1372825 4194304 1 8388608 1372825 4194304 1 8388608 

noncomputable def Ns240p2152 := @Enclosure.Real.IsNear.sqrt_image qz258 365459115459 4194304000 136867 4194304000 78303155 78303186 8388608 (@Enclosure.Real.IsNear.of_eq qz258 (@HMul.hMul Real Real Real qz5 qz257 qz3) Bool.false 365459115459 4194304000 136867 4194304000 (BSN.t_div_two_pi_mk qz257 547468 1000 qz260) (@Enclosure.Real.IsNear.mulLit_ff qz257 qz3 547468 1000 0 1 2670177 16777216 1 16777216 365459115459 4194304000 136867 4194304000 (Enclosure.Real.IsNear.const Bool.false 547468 1000) RS241to252.d44 rfl)) 

noncomputable abbrev qz870 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 547468 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz763 := qz870

noncomputable abbrev qz578 := qz763

noncomputable abbrev qz263 := qz578

noncomputable def Ns240p2153 := @Enclosure.Real.IsNear.sqrt_image qz263 156606341 16777216 31 16777216 25629172 25629178 8388608 (@Enclosure.Real.IsNear.recentre' qz263 Bool.false 156606341 16777216 31 16777216 156606341 16777216 31 16777216 (Ns240p2152 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns240p2154 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz263) 25629175 8388608 3 8388608 2745649 2745651 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz263) Bool.false 51258350 16777216 6 16777216 25629175 8388608 3 8388608 (Ns240p2153 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns240p2155 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz263)) Bool.false 5491300 16777216 2 16777216 1372825 4194304 1 8388608 (Ns240p2154 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz264 := (Real.cos (@HMul.hMul Real Real Real qz344 qz340 qz572))

noncomputable abbrev qz764 := (@HMul.hMul Real Real Real qz811 qz868 qz868)

noncomputable abbrev qz579 := (@HSub.hSub Real Real Real qz619 (@HSub.hSub Real Real Real qz619 qz764 qz757) qz626)

noncomputable abbrev qz265 := (Real.cos (@HMul.hMul Real Real Real qz344 qz340 qz579))

noncomputable def Ns240p2156 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz259) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz264) qz265) Bool.false 30411864461391 

noncomputable def Ns240p2157 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz264) qz265 16573467 8388608 391 

noncomputable abbrev qz765 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz264))

noncomputable def Ns240p2158 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz264) (@Neg.neg Real Real.instNeg qz765) Bool.true 16573467 8388608 391 8388608 (BSN.inv_eq_neg_inv_neg qz264) 

noncomputable def Ns240p2159 := @Enclosure.Real.IsNear.recentre' qz765 Bool.false 33146934 16777216 782 16777216 16573467 8388608 

noncomputable def Ns240p2160 := @Enclosure.Real.IsNear.recentre' qz264 Bool.true 8491735 16777216 648577216 54358179840000 8491735 16777216 10134019 849346560000 

noncomputable abbrev qz266 := (@HMul.hMul Real Real Real qz344 qz340 qz572)

noncomputable def Ns240p2161 := @Enclosure.Real.IsNear.cos_image qz266 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 35257447) qz363) Bool.false 35257447 16777216 195 16777216 Bool.true 8491735 16777216 1 

noncomputable def Ns240p2162 := nat_lit 836568337728566942309983001 

noncomputable def Ns240p2163 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz259 884279719003555 140737488355328 1 500000000000000 5611397 16777216 31 16777216 4962044562377391516335 2361183241434822606848 Ns240p2162 

noncomputable def Ns240p2164 := @Enclosure.Real.IsNear.subLit_ff_p qz263 qz1 156606341 16777216 31 16777216 9 1 0 1 5611397 5611397 16777216 31 

noncomputable def Ns240p2165 := @Ns240p2164 16777216 (@Enclosure.Real.IsNear.recentre' qz263 Bool.false 156606341 16777216 31 16777216 156606341 16777216 31 16777216 (Ns240p2152 rfl rfl rfl rfl rfl rfl) rfl) qz373 

noncomputable def Ns240p2166 := @Enclosure.Real.IsNear.recentre' qz266 Bool.false 4962044562377391516335 2361183241434822606848 Ns240p2162 Ns240p281 35257447 16777216 195 16777216 (@Ns240p2163 Ns240p281 RS241to252.d43 (Ns240p2165 rfl rfl) rfl) 

noncomputable def Ns240p2167 := nat_lit 1283181131843181953941504 

noncomputable def Ns240p2168 := nat_lit 110568815692639492852595861013472409681361 

noncomputable def Ns240p2169 := BSN.sin_dyadic_bound_f 18235100637 34359738368 2 1 16777216 6486329 Ns240p2168 Ns240p2058 Ns240p2168 Ns240p2168 Ns240p2059 Ns240p2168 8491735 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 18235100637) qz361 0 1 Ns240p2168 Ns240p2058 Ns240p2168 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 18235100637) qz362 0 1 Ns240p2168 Ns240p2059 Ns240p2168 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2170 := @Ns240p2161 3240000 (Ns240p2166 rfl) (Enclosure.sfrac_false_div 35257447 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 35257447) qz363) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns240p2167) qz364) 226375608064910080 72057594037927936 Bool.false 8491735 16777216 0 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 35257447 16777216 226375608064910080 72057594037927936 0 Ns240p2167 Ns240p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8491735 16777216 Ns240p2167 Ns240p92 18235100637 34359738368 6486329 6480000 (Ns240p2169 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns240p2171 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz264) 8491735 16777216 10134019 849346560000 16573076 16573858 8388608 (@Enclosure.Real.IsNear.neg qz264 Bool.true 8491735 16777216 10134019 849346560000 (Ns240p2160 (Ns240p2170 rfl rfl) rfl)) 

noncomputable def Ns240p2172 := Ns240p2158 (@Enclosure.Real.IsNear.neg qz765 Bool.false 16573467 8388608 391 8388608 (@Ns240p2159 391 8388608 (Ns240p2171 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p2173 := @Enclosure.Real.IsNear.recentre' qz265 Bool.true 1834973 8388608 

noncomputable abbrev qz267 := (@HMul.hMul Real Real Real qz344 qz340 qz579)

noncomputable def Ns240p2174 := @Enclosure.Real.IsNear.cos_image qz267 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15026725)) qz406) Bool.true 15026725 8388608 

noncomputable def Ns240p2175 := nat_lit 70961704785454605584024052245 

noncomputable def Ns240p2176 := nat_lit 4684789551008280334550221861345997 

noncomputable def Ns240p2177 := @Enclosure.Real.IsNear.recentre' qz267 Bool.true Ns240p2175 Ns240p294 Ns240p2176 

noncomputable abbrev qz268 := qz579

noncomputable def Ns240p2178 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz268 884279719003555 140737488355328 1 500000000000000 80248029283559 

noncomputable abbrev qz580 := (@HSub.hSub Real Real Real qz619 qz764 qz757)

noncomputable abbrev qz269 := qz580

noncomputable def Ns240p2179 := @Enclosure.Real.IsNear.subLit_tf qz269 qz27 62655843239143 281474976710656 868001271 281474976710656 1 16 

noncomputable abbrev qz581 := qz764

noncomputable abbrev qz270 := qz581

noncomputable def Ns240p2180 := @Enclosure.Real.IsNear.subLit_ff_n qz270 qz259 31487776291609 281474976710656 347907575 281474976710656 5611397 16777216 31 16777216 

noncomputable def Ns240p2181 := @Enclosure.Real.IsNear.mulLit_ff qz259 qz259 5611397 16777216 31 16777216 5611397 16777216 31 16777216 31487776291609 281474976710656 

noncomputable def Ns240p2182 := nat_lit 25104884740658551984933055952783112694937597627377329461258479125170910944352656258994140625 

noncomputable def Ns240p2183 := nat_lit 132547659338577663193329111943210733125723926853857205846376039352450430393218994140625 

noncomputable def Ns240p2184 := nat_lit 151683781723294095310505232128481992953887644860848537187227199832660047869078788994994140625 

noncomputable def Ns240p2185 := BSN.cos_dyadic_bound_t 15026725 8388608 4 3 8388608 3240000 Ns240p2182 Ns240p426 Ns240p2183 Ns240p2184 Ns240p429 Ns240p2183 1834973 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 15026725) (BSN.cosEvenQ 8388608) 0 3 Ns240p2182 Ns240p426 Ns240p2183 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 15026725) (BSN.cosOddQ 8388608) 0 3 Ns240p2184 Ns240p429 Ns240p2183 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2186 := @Ns240p2173 1076257216 54358179840000 1834973 8388608 16816519 849346560000 (@Ns240p2174 327 16777216 Bool.true 1834973 8388608 1 3240000 (@Ns240p2177 Ns240p1622 15026725 8388608 327 16777216 (@Ns240p2178 281474976710656 868001271 281474976710656 Ns240p2175 Ns240p294 Ns240p2176 Ns240p1622 RS241to252.d43 (@Ns240p2179 0 1 1283968468536944 80248029283559 281474976710656 868001271 281474976710656 (@Ns240p2180 1051190615685241765888 62655843239143 281474976710656 868001271 281474976710656 (@Ns240p2181 347907575 281474976710656 (Ns240p2165 rfl rfl) (Ns240p2165 rfl rfl) rfl) (Ns240p2165 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 15026725 8388608) (BSN.cos_neg_of_bound 15026725 8388608 Bool.true 1834973 8388608 1 3240000 (Ns240p2185 rfl rfl)) rfl rfl) 

noncomputable def Ns240p2187 := @Ns240p2150 161298012683021337767 Ns240p2080 (Ns240p2151 qz29 (@Enclosure.Real.IsNear.of_eq qz577 (@Inv.inv Real Real.instInv (Real.sqrt qz263)) Bool.false 1372825 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz258 (BSN.t_div_two_pi_nonneg qz257 547468 1000 qz260)) Ns240p2155) rfl) (@Ns240p2156 70368744177664 87839721328513 1781208836997120000 (BSN.correction_mk qz259 (BSN.cos_two_pi_p_ne_zero_mk qz257 547468 1000 9 qz260 rfl rfl (@BSN.floor_sqrt_eq_dec qz257 547468 1000 9 qz260 rfl rfl rfl))) (@Ns240p2157 8388608 1834973 8388608 16816519 849346560000 30411864461391 70368744177664 87839721328513 1781208836997120000 Ns240p2172 (Ns240p2186 rfl) rfl)) 

noncomputable def Ns240p2188 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz257) (hardyZApproximantRS₀ qz257) Bool.false 207206867804104109367 295147905179352825856 14094061969744243737767 Ns240p2080 (@Eq.refl Real (hardyZApproximantRS₀ qz257)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz257) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz257) qz257 9) (@HMul.hMul Real Real Real qz5 qz573 (Zeta.RiemannSiegel.correction qz259))) Bool.false 207206867804104109367 295147905179352825856 14094061969744243737767 Ns240p2080 (BSN.hardyZApproximantRS₀_eq qz257 9 (@BSN.floor_sqrt_eq_dec qz257 547468 1000 9 qz260 rfl rfl rfl)) (@Ns240p2082 207206867804104109367 295147905179352825856 14094061969744243737767 Ns240p2080 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz257) qz257 9) (@HAdd.hAdd Real Real Real qz360 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz257) qz257 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz257) qz257 9)) Bool.false 18810249 33554432 93865 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz257) qz257 9) (Ns240p2149 (Ns240p2148 rfl) rfl rfl)) (Ns240p2187 rfl) rfl rfl)) 

theorem RS241to252.d79 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz257) Bool.false 207206867804104109367 295147905179352825856 14094061969744243737767 Ns240p2080 := Ns240p2188 

noncomputable def Ns240p2189 := nat_lit 18535391291991780304869130240 

noncomputable abbrev qz871 := (Enclosure.sfrac Bool.false 548874 1000)

noncomputable abbrev qz766 := qz871

noncomputable abbrev qz582 := qz766

noncomputable abbrev qz271 := qz582

noncomputable abbrev qz872 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 548874 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz767 := qz872

noncomputable abbrev qz583 := qz767

noncomputable abbrev qz272 := qz583

noncomputable abbrev qz873 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 548874 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz768 := qz873

noncomputable abbrev qz584 := qz768

noncomputable abbrev qz273 := qz584

noncomputable abbrev qz585 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz618 qz272 qz8))

noncomputable def Ns240p2190 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz271) qz271 9) (@HMul.hMul Real Real Real qz5 qz585 (Zeta.RiemannSiegel.correction qz273)) 33732965 16777216 94099 67108864 82077778487507992365 590295810358705651712 433011210172049578897 Ns240p69 Ns240p2189 

noncomputable def Ns240p2191 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz271) qz271 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 548874 1000 120 161 134217728 67108864 2251799813685248 Bool.false 127762055282 1819 

noncomputable def Ns240p2192 := Ns240p2191 279097919 42 47453128 8 294906479 42 44739240 8 Bool.true 120672718 76995 Bool.true 128090215 Bool.true 161020497 7074237752028440 1 Bool.false 77596921 Bool.false Bool.false 125081386 Bool.true Bool.true 134931860 

noncomputable def Ns240p2193 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz271) qz271 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 548874 1000 20 73 134217728 67108864 2251799813685248 Bool.false 127762055282 1819 

noncomputable def Ns240p2194 := Ns240p2193 240485871 42 54794152 8 261175631 42 50729528 8 Bool.true 124421695 57421 Bool.true 17812394 Bool.true 199961875 7074237752028440 1 Bool.false 133037496 Bool.false Bool.false 133778055 Bool.true Bool.true 120672718 

noncomputable def Ns240p2195 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz271) qz271 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 548874 1000 121 43 134217728 67108864 2251799813685248 Bool.false 127762055282 1819 

noncomputable def Ns240p2196 := Ns240p2195 186065264 42 67108856 8 216015088 42 60023992 8 Bool.true 120260536 33842 Bool.false 125395159 Bool.false 131355163 7074237752028440 1 Bool.false 107932989 Bool.true Bool.false 111368104 Bool.false Bool.true 124421695 

noncomputable def Ns240p2197 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz271) qz271 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 548874 1000 363 222 134217728 67108864 2251799813685248 Bool.false 127762055282 1819 

noncomputable def Ns240p2198 := Ns240p2197 93032624 42 94906264 8 147453232 42 77490640 16 Bool.true 134217648 1866 Bool.false 168043586 Bool.false 24835483 7074237752028440 1 Bool.false 127455885 Bool.false Bool.false 131926513 Bool.true Bool.true 120260536 

noncomputable def Ns240p2199 := nat_lit 45787702277186514743580927052678575110152631552796229 

noncomputable def Ns240p2200 := nat_lit 48101303289276098636956409809811099844368505241600 

noncomputable def Ns240p2201 := nat_lit 23911424232963014699627688299520000 

noncomputable def Ns240p2202 := nat_lit 78746184881944807372312004788600442880 

noncomputable def Ns240p2203 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz271 548874 1000 1205051671504 16000000 1097748 4000 2000 Ns240p2201 Ns240p2202 (@Eq.refl Real qz271) rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns240p2204 := nat_lit 8439589283731018397536836474349714964303333047811400929280 

noncomputable abbrev qz769 := (Real.log (Enclosure.sfrac Bool.false 1205051671504 16000000))

noncomputable abbrev qz770 := (@Nat.cast Real Real.instNatCast 1097748)

noncomputable abbrev qz771 := (Enclosure.sfrac Bool.false 548874 2000)

noncomputable abbrev qz274 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 548874 4000) qz769) (@HMul.hMul Real Real Real qz344 qz358 (@HSub.hSub Real Real Real qz350 qz355 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz356 qz770))))) qz771)

noncomputable abbrev qz586 := (@HSub.hSub Real Real Real qz11 qz274 (@HMul.hMul Real Real Real qz5 qz771 (Real.log Real.pi)))

noncomputable def Ns240p2205 := @Enclosure.Real.IsNear.addLit_ft_p qz586 (Enclosure.sfrac Bool.true Ns240p2201 Ns240p2202) 107174614091724821281 112589990684262400 1123886741732728849 82944000000000000000000 Ns240p2201 Ns240p2202 0 1 Ns240p2204 

noncomputable def Ns240p2206 := nat_lit 17980916503335111391927336960000 

noncomputable abbrev qz587 := (@HMul.hMul Real Real Real qz5 qz771 (Real.log Real.pi))

noncomputable def Ns240p2207 := @Enclosure.Real.IsNear.subLit_ff_p qz274 qz587 712727308182548471717 562949953421312000 435057990345301 81000000000000000000 10541334016557 33554432000 274437 33554432000 Ns240p2206 107174614091724821281 112589990684262400 

noncomputable def Ns240p2208 := nat_lit 1425454616365096943434000 

noncomputable abbrev qz275 := (@HSub.hSub Real Real Real qz350 (@HMul.hMul Real Real Real qz344 (Enclosure.sfrac Bool.false 548874 4000) qz769) (@HMul.hMul Real Real Real qz344 qz358 (@HSub.hSub Real Real Real qz350 qz355 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz356 qz770)))))

noncomputable def Ns240p2209 := @Enclosure.Real.IsNear.subLit_ff_p qz275 qz771 867221604549633073061 562949953421312000 435057990345301 81000000000000000000 548874 2000 0 1 Ns240p2208 712727308182548471717 562949953421312000 435057990345301 81000000000000000000 

noncomputable def Ns240p2210 := nat_lit 1952809447548685573211802101641904128 

noncomputable def Ns240p2211 := nat_lit 27151130259051453691723776 

noncomputable def Ns240p2212 := nat_lit 13755687418178569511816673806614745867096718904749511881169592310902638510080 

noncomputable def Ns240p2213 := nat_lit 22169151745926196259469608393878508788096150934283169911346859983100706816 

noncomputable def Ns240p2214 := nat_lit 220177128214567092901161187574106825689726141239950990480143485501440 

noncomputable def Ns240p2215 := BSN.log_dyadic_bound 156475671504 2253627671504 4 3 Ns240p2212 67108864 25920000 Ns240p2213 Ns240p2214 9334131 2410103343008 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 156475671504) (BSN.artanhQ 2253627671504) 0 3 Ns240p2213 Ns240p2212 Ns240p2214 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns240p2216 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 548874 4000) qz769 548874 4000 0 1 3160807567072503 281474976710656 195312581 5062500000000000 867442546284676505811 562949953421312000 5955666532433 1125000000000000000 (Enclosure.Real.IsNear.const Bool.false 548874 4000) (BSN.isNear_log_sfrac 1205051671504 16000000 3160807567072503 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1205051671504) qz354)) Bool.false Ns240p2211 Ns240p92 1000000414720000 25920000000000000000000 3160807567072503 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1205051671504 16000000 16 2410103343008 2097152000000 9334131 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns240p2215 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p2217 := BSN.arctan_dyadic_bound_f 1000 1097748 1 0 8388608 3240000 0 1 1 0 1 1 7641 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1097748) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1097748) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz772 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1097748)))

noncomputable def Ns240p2218 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz772 884279719003555 562949953421312 1 2000000000000000 7641 8388608 1 3240000 7413574424476881256448 883766940173731 562949953421312 50000000081 162000000000000000 qz16 (Ns240p2217 rfl) rfl rfl 

noncomputable def Ns240p2219 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 548874 4000) qz769) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz11 qz14 qz772)) 867442546284676505811 562949953421312000 5955666532433 1125000000000000000 883766940173731 2251799813685248 50000000081 648000000000000000 Ns240p2210 867221604549633073061 562949953421312000 435057990345301 81000000000000000000 (Ns240p2216 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 qz772) 1 4 0 1 883766940173731 562949953421312 50000000081 162000000000000000 883766940173731 2251799813685248 50000000081 648000000000000000 qz359 Ns240p2218 rfl) 

noncomputable def Ns240p2220 := @Ns240p2205 Ns240p2199 Ns240p2200 1123886741732728849 82944000000000000000000 (@Ns240p2207 1123886741732728849 82944000000000000000000 (Ns240p2209 (Ns240p2219 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 548874 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz771 (Real.log Real.pi) 548874 2000 0 1 38410761 33554432 1 33554432 10541334016557 33554432000 274437 33554432000 (Enclosure.Real.IsNear.const Bool.false 548874 2000) RS241to252.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns240p2201 Ns240p2202) 

noncomputable def Ns240p2221 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz271) Bool.false Ns240p2199 Ns240p2200 1123886741732728849 82944000000000000000000 7985128455 8388608 57 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz271) (@HAdd.hAdd Real Real Real qz360 qz586 (Enclosure.sfrac Bool.true Ns240p2201 Ns240p2202)) Bool.false Ns240p2199 Ns240p2200 1123886741732728849 82944000000000000000000 Ns240p2203 (Ns240p2220 rfl rfl)) 

noncomputable def Ns240p2222 := nat_lit 1897665827201046083010560 

noncomputable def Ns240p2223 := nat_lit 854769369398734312921280684588850349925409102529696185035750737431467029415560652346223068683388200429519321493640391779688739499933696 

noncomputable def Ns240p2224 := nat_lit 605953342000942837785379445736040135471537552969865835721431678148449498220425768387372448669423901743986506061968975727790391296 

noncomputable def Ns240p2225 := nat_lit 4268550686132728575591869008600187210756255828917807709267711870013340427391674528409171239889235871334348366362560515218503999795757056 

noncomputable def Ns240p2226 := BSN.sin_dyadic_bound_f 53934906736 34359738368 4 3 16777216 6486329 Ns240p2223 Ns240p105 Ns240p2224 Ns240p2225 Ns240p108 Ns240p2224 16777206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53934906736) qz361 0 3 Ns240p2223 Ns240p105 Ns240p2224 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53934906736) qz362 0 3 Ns240p2225 Ns240p108 Ns240p2224 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2227 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz271) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7985128455) qz406) Bool.false 7985128455 8388608 57 4194304 Bool.true 16777206 16777216 1 3240000 (Ns240p2221 rfl) (Enclosure.sfrac_false_div 7985128455 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7985128455) qz406) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns240p2222) (@Nat.cast Real Real.instNatCast Ns240p1009)) 226375608064910080 72057594037927936 Bool.false 16777206 16777216 151 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 7985128455 8388608 226375608064910080 72057594037927936 151 Ns240p2222 Ns240p1009 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777206 16777216 Ns240p2222 Ns240p1009 53934906736 34359738368 6486329 6480000 (Ns240p2226 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns240p2228 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz271) Bool.false Ns240p2199 Ns240p2200 1123886741732728849 82944000000000000000000 127762055282 134217728 1819 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz271) (@HAdd.hAdd Real Real Real qz360 qz586 (Enclosure.sfrac Bool.true Ns240p2201 Ns240p2202)) Bool.false Ns240p2199 Ns240p2200 1123886741732728849 82944000000000000000000 Ns240p2203 (Ns240p2220 rfl rfl)) 

noncomputable def Ns240p2229 := Ns240p2198 33842 BSN.abs_quadSignPos (BSN.cos_quad_nat3 363 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 127455885 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 222 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 131926513 134217728) (@Eq.refl Real qz271) rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz271) qz271 1) Bool.true 8388603 8388608 2951161 212336640000 134217648 134217728 1866 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz271) qz271 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz271)) Bool.true 8388603 8388608 2951161 212336640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz271) qz271) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz271)) Bool.true 16777206 16777216 188874304 13589544960000 8388603 8388608 2951161 212336640000 (Ns240p2227 rfl rfl) rfl)) rfl) (Ns240p2228 rfl) RS241to252.d7 

noncomputable def Ns240p2230 := nat_lit 783180448717097377320088424508374891070144733242839640168447573295360 

noncomputable def Ns240p2231 := nat_lit 635880526916682820984591885316259273716794045237969214986533273856 

noncomputable def Ns240p2232 := nat_lit 2050157368644056596985304153517136485407218539562766155045479733330176 

noncomputable def Ns240p2233 := BSN.sin_dyadic_bound_f 168043586 134217728 3 2 134217728 67108864 Ns240p2230 Ns240p248 Ns240p2231 Ns240p2232 Ns240p251 Ns240p2231 127455885 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 168043586) qz365 0 2 Ns240p2230 Ns240p248 Ns240p2231 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 168043586) qz366 0 2 Ns240p2232 Ns240p251 Ns240p2231 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2234 := nat_lit 380443739865759585303406337521 

noncomputable def Ns240p2235 := BSN.cos_dyadic_bound_f 24835483 134217728 2 1 134217728 67108864 Ns240p2234 Ns240p146 Ns240p2234 Ns240p2234 Ns240p147 Ns240p2234 131926513 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 24835483) qz367 0 1 Ns240p2234 Ns240p146 Ns240p2234 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 24835483) qz368 0 1 Ns240p2234 Ns240p147 Ns240p2234 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2236 := nat_lit 242691074192397457224076573355025786178340360787775517981638630307905 

noncomputable def Ns240p2237 := nat_lit 61128841288909300473074056351450362181940893238444209086808979521 

noncomputable def Ns240p2238 := nat_lit 635520509522763677671815572219546139404501612045597446946722531506241 

noncomputable def Ns240p2239 := BSN.sin_dyadic_bound_f 125395159 134217728 3 2 134217728 67108864 Ns240p2236 Ns240p248 Ns240p2237 Ns240p2238 Ns240p251 Ns240p2237 107932989 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 125395159) qz365 0 2 Ns240p2236 Ns240p248 Ns240p2237 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 125395159) qz366 0 2 Ns240p2238 Ns240p251 Ns240p2237 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2240 := nat_lit 292241332617698189969757708182438077273801121509610969645877485332705 

noncomputable def Ns240p2241 := nat_lit 88629271886933151176678774672727643406979592952189122153960401121 

noncomputable def Ns240p2242 := nat_lit 765250471368059272437936517699772452865867827469915661922382239983841 

noncomputable def Ns240p2243 := BSN.sin_dyadic_bound_f 131355163 134217728 3 2 134217728 67108864 Ns240p2240 Ns240p248 Ns240p2241 Ns240p2242 Ns240p251 Ns240p2241 111368104 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 131355163) qz365 0 2 Ns240p2240 Ns240p248 Ns240p2241 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 131355163) qz366 0 2 Ns240p2242 Ns240p251 Ns240p2241 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2244 := Ns240p2196 57421 BSN.abs_quadSignNeg qz642 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 107932989 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 43 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 111368104 134217728) (@Eq.refl Real qz271) rfl rfl (Ns240p2229 RS241to252.d9 RS241to252.d11 RS241to252.d13 RS241to252.d17 (Ns240p2233 rfl rfl) (Ns240p2235 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns240p2228 rfl) RS241to252.d19 RS241to252.d21 RS241to252.d23 RS241to252.d25 RS241to252.d17 (Ns240p2239 rfl rfl) (Ns240p2243 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns240p2245 := nat_lit 100667474101834347171486247696 

noncomputable def Ns240p2246 := BSN.cos_dyadic_bound_f 17812394 134217728 2 1 134217728 67108864 Ns240p2245 Ns240p146 Ns240p2245 Ns240p2245 Ns240p147 Ns240p2245 133037496 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 17812394) qz367 0 1 Ns240p2245 Ns240p146 Ns240p2245 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 17812394) qz368 0 1 Ns240p2245 Ns240p147 Ns240p2245 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2247 := nat_lit 8751330864773774179709953254530546358236200698283109435394281513254324101302329867665844907907867431640625 

noncomputable def Ns240p2248 := nat_lit 4086640217200698906790613262587266903584120237877795998128959518854941279641934670507907867431640625 

noncomputable def Ns240p2249 := nat_lit 43712641221891307466703181906717023710283802488181850271407776334864663422746530770590542507907867431640625 

noncomputable def Ns240p2250 := BSN.sin_dyadic_bound_f 199961875 134217728 4 3 134217728 67108864 Ns240p2247 Ns240p118 Ns240p2248 Ns240p2249 Ns240p121 Ns240p2248 133778055 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 199961875) qz365 0 3 Ns240p2247 Ns240p118 Ns240p2248 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 199961875) qz366 0 3 Ns240p2249 Ns240p121 Ns240p2248 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2251 := Ns240p2194 76995 BSN.abs_quadSignPos (BSN.cos_quad_nat0 20 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133037496 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 73 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133778055 134217728) (@Eq.refl Real qz271) rfl rfl (Ns240p2244 rfl rfl) (Ns240p2228 rfl) RS241to252.d27 RS241to252.d29 RS241to252.d31 RS241to252.d33 RS241to252.d17 (Ns240p2246 rfl rfl) (Ns240p2250 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p2252 := nat_lit 146834130483055506045783924428791692794214103280934718677085896690625 

noncomputable def Ns240p2253 := nat_lit 72464889940699533473360228336003782365125020192701031752187890625 

noncomputable def Ns240p2254 := nat_lit 440357461669285119070405052829703070817912059802418753967753314290625 

noncomputable def Ns240p2255 := BSN.cos_dyadic_bound_f 128090215 134217728 3 2 134217728 67108864 Ns240p2252 Ns240p124 Ns240p2253 Ns240p2254 Ns240p127 Ns240p2253 77596921 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 128090215) qz367 0 2 Ns240p2252 Ns240p124 Ns240p2253 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 128090215) qz368 0 2 Ns240p2254 Ns240p127 Ns240p2253 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2256 := nat_lit 660151125865587859758487335805054396692772065115527341588491659972225 

noncomputable def Ns240p2257 := nat_lit 451907243198655238916192091012851479012288921344127221126928338561 

noncomputable def Ns240p2258 := nat_lit 1728235575063741809933031092294454993705525988477538260088034558807681 

noncomputable def Ns240p2259 := BSN.sin_dyadic_bound_f 161020497 134217728 3 2 134217728 67108864 Ns240p2256 Ns240p248 Ns240p2257 Ns240p2258 Ns240p251 Ns240p2257 125081386 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 161020497) qz365 0 2 Ns240p2256 Ns240p248 Ns240p2257 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 161020497) qz366 0 2 Ns240p2258 Ns240p251 Ns240p2257 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2260 := Ns240p2192 94099 BSN.abs_quadSignPos (BSN.cos_quad_nat0 120 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 77596921 134217728) BSN.abs_quadSignNeg qz662 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 125081386 134217728) (@Eq.refl Real qz271) rfl rfl (Ns240p2251 rfl) (Ns240p2228 rfl) RS241to252.d35 RS241to252.d37 RS241to252.d39 RS241to252.d41 RS241to252.d17 (Ns240p2255 rfl rfl) (Ns240p2259 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns240p2261 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz271) qz271 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz271) qz271 9) 134931860 134217728 94099 134217728 134931860 134217728 94099 134217728 36220495368028160 33732965 16777216 94099 67108864 (Ns240p2260 rfl) 

noncomputable def Ns240p2262 := @Enclosure.Real.IsNear.mulLit_tf qz585 (Zeta.RiemannSiegel.correction qz273) 1371945 4194304 1 8388608 59825851974757 140737488355328 314514584066159 7124835347988480000 82077778487507992365 590295810358705651712 

noncomputable abbrev qz588 := (@HPow.hPow Real Real Real qz618 qz272 qz8)

noncomputable def Ns240p2263 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz588 1 1 0 1 1371945 4194304 1 8388608 1371945 4194304 1 8388608 

noncomputable def Ns240p2264 := @Enclosure.Real.IsNear.sqrt_image qz272 732795365349 8388608000 274437 8388608000 78403639 78403670 8388608 (@Enclosure.Real.IsNear.of_eq qz272 (@HMul.hMul Real Real Real qz5 qz271 qz3) Bool.false 732795365349 8388608000 274437 8388608000 (BSN.t_div_two_pi_mk qz271 548874 1000 (@Eq.refl Real qz271)) (@Enclosure.Real.IsNear.mulLit_ff qz271 qz3 548874 1000 0 1 2670177 16777216 1 16777216 732795365349 8388608000 274437 8388608000 (Enclosure.Real.IsNear.const Bool.false 548874 1000) RS241to252.d44 rfl)) 

noncomputable abbrev qz874 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 548874 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz773 := qz874

noncomputable abbrev qz589 := qz773

noncomputable abbrev qz276 := qz589

noncomputable def Ns240p2265 := @Enclosure.Real.IsNear.sqrt_image qz276 156807309 16777216 31 16777216 25645611 25645617 8388608 (@Enclosure.Real.IsNear.recentre' qz276 Bool.false 156807309 16777216 31 16777216 156807309 16777216 31 16777216 (Ns240p2264 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns240p2266 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz276) 12822807 4194304 3 8388608 2743889 2743891 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz276) Bool.false 51291228 16777216 6 16777216 12822807 4194304 3 8388608 (Ns240p2265 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns240p2267 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz276)) Bool.false 5487780 16777216 2 16777216 1371945 4194304 1 8388608 (Ns240p2266 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz277 := (Real.cos (@HMul.hMul Real Real Real qz344 qz340 qz584))

noncomputable abbrev qz774 := (@HMul.hMul Real Real Real qz811 qz873 qz873)

noncomputable abbrev qz590 := (@HSub.hSub Real Real Real qz619 (@HSub.hSub Real Real Real qz619 qz774 qz768) qz626)

noncomputable abbrev qz278 := (Real.cos (@HMul.hMul Real Real Real qz344 qz340 qz590))

noncomputable def Ns240p2268 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz273) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz277) qz278) Bool.false 59825851974757 

noncomputable def Ns240p2269 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz277) qz278 29456251 16777216 621 

noncomputable abbrev qz775 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz277))

noncomputable def Ns240p2270 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz277) (@Neg.neg Real Real.instNeg qz775) Bool.true 29456251 16777216 621 16777216 (BSN.inv_eq_neg_inv_neg qz277) 

noncomputable def Ns240p2271 := @Enclosure.Real.IsNear.recentre' qz775 Bool.false 29456251 16777216 621 16777216 29456251 16777216 

noncomputable def Ns240p2272 := @Enclosure.Real.IsNear.recentre' qz277 Bool.true 9555696 16777216 162954304 13589544960000 597231 1048576 2546161 212336640000 

noncomputable abbrev qz279 := (@HMul.hMul Real Real Real qz344 qz340 qz584)

noncomputable def Ns240p2273 := @Enclosure.Real.IsNear.cos_image qz279 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18260083) qz406) Bool.false 18260083 8388608 49 4194304 Bool.true 9555696 16777216 1 

noncomputable def Ns240p2274 := nat_lit 836568337730293244285068057 

noncomputable def Ns240p2275 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz273 884279719003555 140737488355328 1 500000000000000 5812365 16777216 31 16777216 5139756488946097957575 2361183241434822606848 Ns240p2274 

noncomputable def Ns240p2276 := @Enclosure.Real.IsNear.subLit_ff_p qz276 qz1 156807309 16777216 31 16777216 9 1 0 1 5812365 5812365 16777216 31 

noncomputable def Ns240p2277 := @Ns240p2276 16777216 (@Enclosure.Real.IsNear.recentre' qz276 Bool.false 156807309 16777216 31 16777216 156807309 16777216 31 16777216 (Ns240p2264 rfl rfl rfl rfl rfl rfl) rfl) qz373 

noncomputable def Ns240p2278 := @Enclosure.Real.IsNear.recentre' qz279 Bool.false 5139756488946097957575 2361183241434822606848 Ns240p2274 Ns240p281 18260083 8388608 49 4194304 (@Ns240p2275 Ns240p281 RS241to252.d43 (Ns240p2277 rfl rfl) rfl) 

noncomputable def Ns240p2279 := nat_lit 187939808794350110923808059064654952488401 

noncomputable def Ns240p2280 := BSN.sin_dyadic_bound_f 20821149149 34359738368 2 1 16777216 6486329 Ns240p2279 Ns240p2058 Ns240p2279 Ns240p2279 Ns240p2059 Ns240p2279 9555696 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 20821149149) qz361 0 1 Ns240p2279 Ns240p2058 Ns240p2279 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 20821149149) qz362 0 1 Ns240p2279 Ns240p2059 Ns240p2279 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2281 := @Ns240p2273 3240000 (Ns240p2278 rfl) (Enclosure.sfrac_false_div 18260083 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18260083) qz406) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 732579059007569302388736) (@Nat.cast Real Real.instNatCast Ns240p1009)) 226375608064910080 72057594037927936 Bool.false 9555696 16777216 0 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 18260083 8388608 226375608064910080 72057594037927936 0 732579059007569302388736 Ns240p1009 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 9555696 16777216 732579059007569302388736 Ns240p1009 20821149149 34359738368 6486329 6480000 (Ns240p2280 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns240p2282 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz277) 597231 1048576 2546161 212336640000 14727815 14728436 8388608 (@Enclosure.Real.IsNear.neg qz277 Bool.true 597231 1048576 2546161 212336640000 (Ns240p2272 (Ns240p2281 rfl rfl) rfl)) 

noncomputable def Ns240p2283 := Ns240p2270 (@Enclosure.Real.IsNear.neg qz775 Bool.false 29456251 16777216 621 16777216 (@Ns240p2271 621 16777216 (Ns240p2282 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns240p2284 := @Enclosure.Real.IsNear.recentre' qz278 Bool.true 2031007 8388608 

noncomputable abbrev qz280 := (@HMul.hMul Real Real Real qz344 qz340 qz590)

noncomputable def Ns240p2285 := @Enclosure.Real.IsNear.cos_image qz280 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7614093)) qz418) Bool.true 7614093 4194304 

noncomputable def Ns240p2286 := nat_lit 71913077409591553356706095205 

noncomputable def Ns240p2287 := nat_lit 23760194686424538702040968911636881 

noncomputable def Ns240p2288 := @Enclosure.Real.IsNear.recentre' qz280 Bool.true Ns240p2286 Ns240p294 Ns240p2287 

noncomputable abbrev qz281 := qz590

noncomputable def Ns240p2289 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz281 884279719003555 140737488355328 1 500000000000000 81323902227031 

noncomputable abbrev qz591 := (@HSub.hSub Real Real Real qz619 qz774 qz768)

noncomputable abbrev qz282 := qz591

noncomputable def Ns240p2290 := @Enclosure.Real.IsNear.subLit_tf qz282 qz27 63731716182615 281474976710656 880461287 281474976710656 1 16 

noncomputable abbrev qz592 := qz774

noncomputable abbrev qz283 := qz592

noncomputable def Ns240p2291 := @Enclosure.Real.IsNear.subLit_ff_n qz283 qz273 33783586893225 281474976710656 360367591 281474976710656 5812365 16777216 31 16777216 

noncomputable def Ns240p2292 := @Enclosure.Real.IsNear.mulLit_ff qz273 qz273 5812365 16777216 31 16777216 5812365 16777216 31 16777216 33783586893225 281474976710656 

noncomputable def Ns240p2293 := nat_lit 6466638848700626044203585817228022310825805090492438334296946808520312464295858650511281 

noncomputable def Ns240p2294 := nat_lit 37968035313777335990748198491416487808185660279155175791375189232117431203978311601 

noncomputable def Ns240p2295 := nat_lit 39062768904876552678337969986609114114760972763416424150378094094446684242755955597277105 

noncomputable def Ns240p2296 := BSN.cos_dyadic_bound_t 7614093 4194304 4 3 8388608 3240000 Ns240p2293 Ns240p538 Ns240p2294 Ns240p2295 Ns240p541 Ns240p2294 2031007 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 7614093) (BSN.cosEvenQ 4194304) 0 3 Ns240p2293 Ns240p538 Ns240p2294 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 7614093) (BSN.cosOddQ 4194304) 0 3 Ns240p2295 Ns240p541 Ns240p2294 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns240p2297 := @Ns240p2284 1089217216 54358179840000 2031007 8388608 17019019 849346560000 (@Ns240p2285 331 16777216 Bool.true 2031007 8388608 1 3240000 (@Ns240p2288 Ns240p297 7614093 4194304 331 16777216 (@Ns240p2289 281474976710656 880461287 281474976710656 Ns240p2286 Ns240p294 Ns240p2287 Ns240p297 RS241to252.d43 (@Ns240p2290 0 1 1301182435632496 81323902227031 281474976710656 880461287 281474976710656 (@Ns240p2291 1069240768446427299840 63731716182615 281474976710656 880461287 281474976710656 (@Ns240p2292 360367591 281474976710656 (Ns240p2277 rfl rfl) (Ns240p2277 rfl rfl) rfl) (Ns240p2277 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7614093 4194304) (BSN.cos_neg_of_bound 7614093 4194304 Bool.true 2031007 8388608 1 3240000 (Ns240p2296 rfl rfl)) rfl rfl) 

noncomputable def Ns240p2298 := @Ns240p2262 433011210172049578897 Ns240p69 (Ns240p2263 qz29 (@Enclosure.Real.IsNear.of_eq qz588 (@Inv.inv Real Real.instInv (Real.sqrt qz276)) Bool.false 1371945 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz272 (BSN.t_div_two_pi_nonneg qz271 548874 1000 (@Eq.refl Real qz271))) Ns240p2267) rfl) (@Ns240p2268 140737488355328 314514584066159 7124835347988480000 (BSN.correction_mk qz273 (BSN.cos_two_pi_p_ne_zero_mk qz271 548874 1000 9 (@Eq.refl Real qz271) rfl rfl (@BSN.floor_sqrt_eq_dec qz271 548874 1000 9 (@Eq.refl Real qz271) rfl rfl rfl))) (@Ns240p2269 16777216 2031007 8388608 17019019 849346560000 59825851974757 140737488355328 314514584066159 7124835347988480000 Ns240p2283 (Ns240p2297 rfl) rfl)) 

noncomputable def Ns240p2299 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz271) (hardyZApproximantRS₀ qz271) Bool.true 1104795413732038754515 590295810358705651712 42335503798320048298897 Ns240p69 (@Eq.refl Real (hardyZApproximantRS₀ qz271)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz271) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz271) qz271 9) (@HMul.hMul Real Real Real qz5 qz585 (Zeta.RiemannSiegel.correction qz273))) Bool.true 1104795413732038754515 590295810358705651712 42335503798320048298897 Ns240p69 (BSN.hardyZApproximantRS₀_eq qz271 9 (@BSN.floor_sqrt_eq_dec qz271 548874 1000 9 (@Eq.refl Real qz271) rfl rfl rfl)) (@Ns240p2190 1104795413732038754515 590295810358705651712 42335503798320048298897 Ns240p69 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz271) qz271 9) (@HAdd.hAdd Real Real Real qz360 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz271) qz271 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz271) qz271 9)) Bool.true 33732965 16777216 94099 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz271) qz271 9) (Ns240p2261 (Ns240p2260 rfl) rfl rfl)) (Ns240p2298 rfl) rfl rfl)) 

theorem RS241to252.d80 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz271) Bool.true 1104795413732038754515 590295810358705651712 42335503798320048298897 Ns240p69 := Ns240p2299 

noncomputable def RS241to252.d81 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz284 := (RS241to252.d3 qz343 qz378 (@Enclosure.dec_le_dec qz343 qz378 531948 1000 533363 1000 (@Eq.refl Real qz343) (@Eq.refl Real qz378) rfl rfl rfl))

noncomputable abbrev qz776 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz284)

noncomputable def Ns240p2300 := @Enclosure.Real.IsNear.of_eq qz776 (hardyZApproximantRS₀ qz4) Bool.true 399240227304272916837 147573952589676412928 41355205319087674625381 Ns240p69 

noncomputable abbrev qz285 := (@Enclosure.dec_le_dec qz343 qz378 531948 1000 533363 1000 (@Eq.refl Real qz343) (@Eq.refl Real qz378) rfl rfl rfl)

noncomputable def Ns240p2301 := @Enclosure.Real.IsNear.neg_val qz776 399240227304272916837 147573952589676412928 41355205319087674625381 Ns240p69 (Ns240p2300 (RS241to252.d4 qz4 qz30 qz285) RS241to252.d45) rfl 

noncomputable abbrev qz777 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz284)

noncomputable def Ns240p2302 := @Enclosure.Real.IsNear.of_eq qz777 (hardyZApproximantRS₀ qz30) Bool.false 1653494637913024006211 1180591620717411303424 83347834831116661370903 Ns240p197 

noncomputable def Ns240p2303 := @Enclosure.Real.IsNear.pos_val qz777 1653494637913024006211 1180591620717411303424 83347834831116661370903 Ns240p197 (Ns240p2302 (RS241to252.d46 qz4 qz30 qz285) RS241to252.d47) rfl 

noncomputable def Ns240p2304 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz776 qz4 qz4 531948 1000 531948 1000 

noncomputable def Ns240p2305 := @Enclosure.norm_gt_of_isNear qz776 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 399240227304272916837 147573952589676412928 41355205319087674625381 

noncomputable def Ns240p2306 := @Ns240p2305 Ns240p69 190359677 2684354560 1213 2684354560 (Ns240p2300 (RS241to252.d4 qz4 qz30 qz285) RS241to252.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS241to252.d48) rfl rfl rfl rfl 

noncomputable def Ns240p2307 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz777 qz4 qz30 531948 1000 533363 1000 

noncomputable def Ns240p2308 := @Enclosure.norm_gt_of_isNear qz777 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1653494637913024006211 1180591620717411303424 83347834831116661370903 

noncomputable def Ns240p2309 := @Ns240p2308 Ns240p197 190359677 2684354560 1213 2684354560 (Ns240p2302 (RS241to252.d46 qz4 qz30 qz285) RS241to252.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS241to252.d48) rfl rfl rfl rfl 

noncomputable def Ns240p2310 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz4 531948 1000 qz10 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz776 qz777 (Ns240p2301 rfl rfl) (Ns240p2303 rfl rfl)) (Ns240p2304 qz10 qz10 rfl rfl rfl rfl (Ns240p2306 rfl)) (Ns240p2307 qz10 qz33 rfl rfl rfl rfl (Ns240p2309 rfl)) 

noncomputable abbrev qz286 := (RS241to252.d3 qz378 qz396 (@Enclosure.dec_le_dec qz378 qz396 533363 1000 534777 1000 (@Eq.refl Real qz378) (@Eq.refl Real qz396) rfl rfl rfl))

noncomputable abbrev qz778 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz286)

noncomputable def Ns240p2311 := @Enclosure.Real.IsNear.of_eq qz778 (hardyZApproximantRS₀ qz30) Bool.false 1653494637913024006211 1180591620717411303424 83347834831116661370903 Ns240p197 

noncomputable abbrev qz287 := (@Enclosure.dec_le_dec qz378 qz396 533363 1000 534777 1000 (@Eq.refl Real qz378) (@Eq.refl Real qz396) rfl rfl rfl)

noncomputable def Ns240p2312 := @Enclosure.Real.IsNear.pos_val qz778 1653494637913024006211 1180591620717411303424 83347834831116661370903 Ns240p197 (Ns240p2311 (RS241to252.d4 qz30 qz54 qz287) RS241to252.d47) rfl 

noncomputable abbrev qz779 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz286)

noncomputable def Ns240p2313 := @Enclosure.Real.IsNear.of_eq qz779 (hardyZApproximantRS₀ qz54) Bool.true 9398071191676149814983 2361183241434822606848 11280423813880718730121 Ns240p342 

noncomputable def Ns240p2314 := @Enclosure.Real.IsNear.neg_val qz779 9398071191676149814983 2361183241434822606848 11280423813880718730121 Ns240p342 (Ns240p2313 (RS241to252.d46 qz30 qz54 qz287) RS241to252.d49) rfl 

noncomputable def Ns240p2315 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz778 qz4 qz30 531948 1000 533363 1000 

noncomputable def Ns240p2316 := @Enclosure.norm_gt_of_isNear qz778 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1653494637913024006211 1180591620717411303424 83347834831116661370903 

noncomputable def Ns240p2317 := @Ns240p2316 Ns240p197 190359677 2684354560 1213 2684354560 (Ns240p2311 (RS241to252.d4 qz30 qz54 qz287) RS241to252.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS241to252.d48) rfl rfl rfl rfl 

noncomputable def Ns240p2318 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz779 qz4 qz54 531948 1000 534777 1000 

noncomputable def Ns240p2319 := @Enclosure.norm_gt_of_isNear qz779 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 9398071191676149814983 2361183241434822606848 11280423813880718730121 

noncomputable def Ns240p2320 := @Ns240p2319 Ns240p342 190359677 2684354560 1213 2684354560 (Ns240p2313 (RS241to252.d46 qz30 qz54 qz287) RS241to252.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS241to252.d48) rfl rfl rfl rfl 

noncomputable def Ns240p2321 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz286 (@BSN.thirtyTwoPi_le_dec qz30 533363 1000 qz33 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz778 qz779 (Ns240p2312 rfl rfl) (Ns240p2314 rfl rfl)) (Ns240p2315 qz10 qz33 rfl rfl rfl rfl (Ns240p2317 rfl)) (Ns240p2318 qz10 qz57 rfl rfl rfl rfl (Ns240p2320 rfl)) 

noncomputable abbrev qz288 := (RS241to252.d3 qz396 qz409 (@Enclosure.dec_le_dec qz396 qz409 534777 1000 536191 1000 (@Eq.refl Real qz396) (@Eq.refl Real qz409) rfl rfl rfl))

noncomputable abbrev qz780 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz288)

noncomputable def Ns240p2322 := @Enclosure.Real.IsNear.of_eq qz780 (hardyZApproximantRS₀ qz54) Bool.true 9398071191676149814983 2361183241434822606848 11280423813880718730121 Ns240p342 

noncomputable abbrev qz289 := (@Enclosure.dec_le_dec qz396 qz409 534777 1000 536191 1000 (@Eq.refl Real qz396) (@Eq.refl Real qz409) rfl rfl rfl)

noncomputable def Ns240p2323 := @Enclosure.Real.IsNear.neg_val qz780 9398071191676149814983 2361183241434822606848 11280423813880718730121 Ns240p342 (Ns240p2322 (RS241to252.d4 qz54 qz68 qz289) RS241to252.d49) rfl 

noncomputable abbrev qz781 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz288)

noncomputable def Ns240p2324 := @Enclosure.Real.IsNear.of_eq qz781 (hardyZApproximantRS₀ qz68) Bool.false 20420804675220813503 9223372036854775808 219455979845330965007 149418626997047368089600 

noncomputable def Ns240p2325 := @Enclosure.Real.IsNear.pos_val qz781 20420804675220813503 9223372036854775808 219455979845330965007 149418626997047368089600 (Ns240p2324 (RS241to252.d46 qz54 qz68 qz289) RS241to252.d50) rfl 

noncomputable def Ns240p2326 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz780 qz4 qz54 531948 1000 534777 1000 

noncomputable def Ns240p2327 := @Enclosure.norm_gt_of_isNear qz780 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 9398071191676149814983 2361183241434822606848 11280423813880718730121 

noncomputable def Ns240p2328 := @Ns240p2327 Ns240p342 190359677 2684354560 1213 2684354560 (Ns240p2322 (RS241to252.d4 qz54 qz68 qz289) RS241to252.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS241to252.d48) rfl rfl rfl rfl 

noncomputable def Ns240p2329 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz781 qz4 qz68 531948 1000 536191 1000 

noncomputable def Ns240p2330 := @Enclosure.norm_gt_of_isNear qz781 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 20420804675220813503 9223372036854775808 219455979845330965007 

noncomputable def Ns240p2331 := @Ns240p2330 149418626997047368089600 190359677 2684354560 1213 2684354560 (Ns240p2324 (RS241to252.d46 qz54 qz68 qz289) RS241to252.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS241to252.d48) rfl rfl rfl rfl 

noncomputable def Ns240p2332 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz54 534777 1000 qz57 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz780 qz781 (Ns240p2323 rfl rfl) (Ns240p2325 rfl rfl)) (Ns240p2326 qz10 qz57 rfl rfl rfl rfl (Ns240p2328 rfl)) (Ns240p2329 qz10 qz71 rfl rfl rfl rfl (Ns240p2331 rfl)) 

noncomputable abbrev qz290 := (RS241to252.d3 qz409 qz421 (@Enclosure.dec_le_dec qz409 qz421 536191 1000 537603 1000 (@Eq.refl Real qz409) (@Eq.refl Real qz421) rfl rfl rfl))

noncomputable abbrev qz782 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz290)

noncomputable def Ns240p2333 := @Enclosure.Real.IsNear.of_eq qz782 (hardyZApproximantRS₀ qz68) Bool.false 20420804675220813503 9223372036854775808 219455979845330965007 149418626997047368089600 

noncomputable abbrev qz291 := (@Enclosure.dec_le_dec qz409 qz421 536191 1000 537603 1000 (@Eq.refl Real qz409) (@Eq.refl Real qz421) rfl rfl rfl)

noncomputable def Ns240p2334 := @Enclosure.Real.IsNear.pos_val qz782 20420804675220813503 9223372036854775808 219455979845330965007 149418626997047368089600 (Ns240p2333 (RS241to252.d4 qz68 qz81 qz291) RS241to252.d50) rfl 

noncomputable abbrev qz783 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz290)

noncomputable def Ns240p2335 := @Enclosure.Real.IsNear.of_eq qz783 (hardyZApproximantRS₀ qz81) Bool.true 64497434903002619945 36893488147419103232 96230798001874474097933 Ns240p561 

noncomputable def Ns240p2336 := @Enclosure.Real.IsNear.neg_val qz783 64497434903002619945 36893488147419103232 96230798001874474097933 Ns240p561 (Ns240p2335 (RS241to252.d46 qz68 qz81 qz291) RS241to252.d51) rfl 

noncomputable def Ns240p2337 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz782 qz4 qz68 531948 1000 536191 1000 

noncomputable def Ns240p2338 := @Enclosure.norm_gt_of_isNear qz782 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 20420804675220813503 9223372036854775808 219455979845330965007 

noncomputable def Ns240p2339 := @Ns240p2338 149418626997047368089600 190359677 2684354560 1213 2684354560 (Ns240p2333 (RS241to252.d4 qz68 qz81 qz291) RS241to252.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS241to252.d48) rfl rfl rfl rfl 

noncomputable def Ns240p2340 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz783 qz4 qz81 531948 1000 537603 1000 

noncomputable def Ns240p2341 := @Enclosure.norm_gt_of_isNear qz783 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 64497434903002619945 36893488147419103232 96230798001874474097933 

noncomputable def Ns240p2342 := @Ns240p2341 Ns240p561 190359677 2684354560 1213 2684354560 (Ns240p2335 (RS241to252.d46 qz68 qz81 qz291) RS241to252.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS241to252.d48) rfl rfl rfl rfl 

noncomputable def Ns240p2343 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz290 (@BSN.thirtyTwoPi_le_dec qz68 536191 1000 qz71 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz782 qz783 (Ns240p2334 rfl rfl) (Ns240p2336 rfl rfl)) (Ns240p2337 qz10 qz71 rfl rfl rfl rfl (Ns240p2339 rfl)) (Ns240p2340 qz10 qz84 rfl rfl rfl rfl (Ns240p2342 rfl)) 

noncomputable abbrev qz292 := (RS241to252.d3 qz421 qz432 (@Enclosure.dec_le_dec qz421 qz432 537603 1000 539015 1000 (@Eq.refl Real qz421) (@Eq.refl Real qz432) rfl rfl rfl))

noncomputable abbrev qz784 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz292)

noncomputable def Ns240p2344 := @Enclosure.Real.IsNear.of_eq qz784 (hardyZApproximantRS₀ qz81) Bool.true 64497434903002619945 36893488147419103232 96230798001874474097933 Ns240p561 

noncomputable abbrev qz293 := (@Enclosure.dec_le_dec qz421 qz432 537603 1000 539015 1000 (@Eq.refl Real qz421) (@Eq.refl Real qz432) rfl rfl rfl)

noncomputable def Ns240p2345 := @Enclosure.Real.IsNear.neg_val qz784 64497434903002619945 36893488147419103232 96230798001874474097933 Ns240p561 (Ns240p2344 (RS241to252.d4 qz81 qz94 qz293) RS241to252.d51) rfl 

noncomputable abbrev qz785 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz292)

noncomputable def Ns240p2346 := @Enclosure.Real.IsNear.of_eq qz785 (hardyZApproximantRS₀ qz94) Bool.false 258422190241907901 144115188075855872 7357085319350356966021 Ns240p668 

noncomputable def Ns240p2347 := @Enclosure.Real.IsNear.pos_val qz785 258422190241907901 144115188075855872 7357085319350356966021 Ns240p668 (Ns240p2346 (RS241to252.d46 qz81 qz94 qz293) RS241to252.d52) rfl 

noncomputable def Ns240p2348 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz784 qz4 qz81 531948 1000 537603 1000 

noncomputable def Ns240p2349 := @Enclosure.norm_gt_of_isNear qz784 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 64497434903002619945 36893488147419103232 96230798001874474097933 

noncomputable def Ns240p2350 := @Ns240p2349 Ns240p561 190359677 2684354560 1213 2684354560 (Ns240p2344 (RS241to252.d4 qz81 qz94 qz293) RS241to252.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS241to252.d48) rfl rfl rfl rfl 

noncomputable def Ns240p2351 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz785 qz4 qz94 531948 1000 539015 1000 

noncomputable def Ns240p2352 := @Enclosure.norm_gt_of_isNear qz785 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 258422190241907901 144115188075855872 7357085319350356966021 

noncomputable def Ns240p2353 := @Ns240p2352 Ns240p668 190359677 2684354560 1213 2684354560 (Ns240p2346 (RS241to252.d46 qz81 qz94 qz293) RS241to252.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS241to252.d48) rfl rfl rfl rfl 

noncomputable def Ns240p2354 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz81 537603 1000 qz84 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz784 qz785 (Ns240p2345 rfl rfl) (Ns240p2347 rfl rfl)) (Ns240p2348 qz10 qz84 rfl rfl rfl rfl (Ns240p2350 rfl)) (Ns240p2351 qz10 qz97 rfl rfl rfl rfl (Ns240p2353 rfl)) 

noncomputable abbrev qz294 := (RS241to252.d3 qz432 qz443 (@Enclosure.dec_le_dec qz432 qz443 539015 1000 540426 1000 (@Eq.refl Real qz432) qz447 rfl rfl rfl))

noncomputable abbrev qz786 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz294)

noncomputable def Ns240p2355 := @Enclosure.Real.IsNear.of_eq qz786 (hardyZApproximantRS₀ qz94) Bool.false 258422190241907901 144115188075855872 7357085319350356966021 Ns240p668 

noncomputable abbrev qz295 := (@Enclosure.dec_le_dec qz432 qz443 539015 1000 540426 1000 (@Eq.refl Real qz432) qz447 rfl rfl rfl)

noncomputable def Ns240p2356 := @Enclosure.Real.IsNear.pos_val qz786 258422190241907901 144115188075855872 7357085319350356966021 Ns240p668 (Ns240p2355 (RS241to252.d4 qz94 qz108 qz295) RS241to252.d52) rfl 

noncomputable abbrev qz787 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz294)

noncomputable def Ns240p2357 := @Enclosure.Real.IsNear.of_eq qz787 (hardyZApproximantRS₀ qz108) Bool.true 73752799220263775035 590295810358705651712 105728572877233270331 73786976294838206464000 

noncomputable def Ns240p2358 := @Enclosure.Real.IsNear.neg_val qz787 73752799220263775035 590295810358705651712 105728572877233270331 73786976294838206464000 (Ns240p2357 (RS241to252.d46 qz94 qz108 qz295) RS241to252.d53) rfl 

noncomputable def Ns240p2359 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz786 qz4 qz94 531948 1000 539015 1000 

noncomputable def Ns240p2360 := @Enclosure.norm_gt_of_isNear qz786 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 258422190241907901 144115188075855872 7357085319350356966021 

noncomputable def Ns240p2361 := @Ns240p2360 Ns240p668 190359677 2684354560 1213 2684354560 (Ns240p2355 (RS241to252.d4 qz94 qz108 qz295) RS241to252.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS241to252.d48) rfl rfl rfl rfl 

noncomputable def Ns240p2362 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz787 qz4 qz108 531948 1000 540426 1000 

noncomputable def Ns240p2363 := @Enclosure.norm_gt_of_isNear qz787 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 73752799220263775035 590295810358705651712 105728572877233270331 

noncomputable def Ns240p2364 := @Ns240p2363 73786976294838206464000 190359677 2684354560 1213 2684354560 (Ns240p2357 (RS241to252.d46 qz94 qz108 qz295) RS241to252.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS241to252.d48) rfl rfl rfl rfl 

noncomputable def Ns240p2365 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz294 (@BSN.thirtyTwoPi_le_dec qz94 539015 1000 qz97 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz786 qz787 (Ns240p2356 rfl rfl) (Ns240p2358 rfl rfl)) (Ns240p2359 qz10 qz97 rfl rfl rfl rfl (Ns240p2361 rfl)) (Ns240p2362 qz10 qz111 rfl rfl rfl rfl (Ns240p2364 rfl)) 

noncomputable abbrev qz296 := (RS241to252.d3 qz443 qz482 (@Enclosure.dec_le_dec qz443 qz482 540426 1000 541836 1000 qz447 qz488 rfl rfl rfl))

noncomputable abbrev qz788 := (Zeta.Certificates.ZIntervalRS.fstVal qz296)

noncomputable def Ns240p2366 := @Enclosure.Real.IsNear.of_eq qz788 (hardyZApproximantRS qz108) Bool.true Ns240p909 Ns240p910 Ns240p911 Ns240p912 

noncomputable abbrev qz297 := (@Enclosure.dec_le_dec qz443 qz482 540426 1000 541836 1000 qz447 qz488 rfl rfl rfl)

noncomputable def Ns240p2367 := @Enclosure.Real.IsNear.neg_val qz788 Ns240p909 Ns240p910 Ns240p911 Ns240p912 (Ns240p2366 (RS241to252.d54 qz108 qz151 qz297) RS241to252.d63) rfl 

noncomputable abbrev qz789 := (Zeta.Certificates.ZIntervalRS.sndVal qz296)

noncomputable def Ns240p2368 := @Enclosure.Real.IsNear.of_eq qz789 (hardyZApproximantRS qz151) Bool.false Ns240p1167 Ns240p1168 Ns240p1169 Ns240p1170 

noncomputable def Ns240p2369 := @Enclosure.Real.IsNear.pos_val qz789 Ns240p1167 Ns240p1168 Ns240p1169 Ns240p1170 (Ns240p2368 (RS241to252.d64 qz108 qz151 qz297) RS241to252.d65) rfl 

noncomputable def Ns240p2370 := BSN.norm_gt_hardyZErrorBoundRS_of_le qz788 qz4 qz108 531948 1000 540426 1000 

noncomputable def Ns240p2371 := @Enclosure.norm_gt_of_isNear qz788 (hardyZErrorBoundRS qz4) Bool.true Bool.false Ns240p909 Ns240p910 Ns240p911 

noncomputable def Ns240p2372 := @Ns240p2371 Ns240p912 13065801 536870912 201 536870912 (Ns240p2366 (RS241to252.d54 qz108 qz151 qz297) RS241to252.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) (hardyZErrorBoundRS qz4) Bool.false 13065801 536870912 201 536870912 (@Eq.refl Real (hardyZErrorBoundRS qz4)) RS241to252.d66) rfl rfl rfl rfl 

noncomputable def Ns240p2373 := BSN.norm_gt_hardyZErrorBoundRS_of_le qz789 qz4 qz151 531948 1000 541836 1000 

noncomputable def Ns240p2374 := @Enclosure.norm_gt_of_isNear qz789 (hardyZErrorBoundRS qz4) Bool.false Bool.false Ns240p1167 Ns240p1168 Ns240p1169 

noncomputable def Ns240p2375 := @Ns240p2374 Ns240p1170 13065801 536870912 201 536870912 (Ns240p2368 (RS241to252.d64 qz108 qz151 qz297) RS241to252.d65) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) (hardyZErrorBoundRS qz4) Bool.false 13065801 536870912 201 536870912 (@Eq.refl Real (hardyZErrorBoundRS qz4)) RS241to252.d66) rfl rfl rfl rfl 

noncomputable def Ns240p2376 := @Zeta.Certificates.ZIntervalRS.Certificate.mk qz296 (@BSN.thirtyTwoPi_le_dec qz108 540426 1000 qz111 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz788 qz789 (Ns240p2367 rfl rfl) (Ns240p2369 rfl rfl)) (Ns240p2370 qz10 qz111 rfl rfl rfl rfl (Ns240p2372 rfl)) (Ns240p2373 qz10 qz156 rfl rfl rfl rfl (Ns240p2375 rfl)) 

noncomputable abbrev qz593 := (@Enclosure.dec_le_dec qz696 qz715 541836 1000 543245 1000 (@Eq.refl Real qz696) (@Eq.refl Real qz715) rfl rfl rfl)

noncomputable abbrev qz298 := (RS241to252.d3 qz482 qz517 qz593)

noncomputable abbrev qz790 := (Zeta.Certificates.ZIntervalRS.fstVal qz298)

noncomputable def Ns240p2377 := @Enclosure.Real.IsNear.of_eq qz790 (hardyZApproximantRS qz151) Bool.false Ns240p1167 Ns240p1168 Ns240p1169 Ns240p1170 

noncomputable abbrev qz299 := qz593

noncomputable def Ns240p2378 := @Enclosure.Real.IsNear.pos_val qz790 Ns240p1167 Ns240p1168 Ns240p1169 Ns240p1170 (Ns240p2377 (RS241to252.d54 qz151 qz188 qz299) RS241to252.d65) rfl 

noncomputable abbrev qz791 := (Zeta.Certificates.ZIntervalRS.sndVal qz298)

noncomputable def Ns240p2379 := @Enclosure.Real.IsNear.of_eq qz791 (hardyZApproximantRS qz188) Bool.true Ns240p1508 Ns240p928 Ns240p1509 Ns240p1510 

noncomputable def Ns240p2380 := @Enclosure.Real.IsNear.neg_val qz791 Ns240p1508 Ns240p928 Ns240p1509 Ns240p1510 (Ns240p2379 (RS241to252.d64 qz151 qz188 qz299) RS241to252.d75) rfl 

noncomputable def Ns240p2381 := BSN.norm_gt_hardyZErrorBoundRS_of_le qz790 qz4 qz151 531948 1000 541836 1000 

noncomputable def Ns240p2382 := @Enclosure.norm_gt_of_isNear qz790 (hardyZErrorBoundRS qz4) Bool.false Bool.false Ns240p1167 Ns240p1168 Ns240p1169 

noncomputable def Ns240p2383 := @Ns240p2382 Ns240p1170 13065801 536870912 201 536870912 (Ns240p2377 (RS241to252.d54 qz151 qz188 qz299) RS241to252.d65) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) (hardyZErrorBoundRS qz4) Bool.false 13065801 536870912 201 536870912 (@Eq.refl Real (hardyZErrorBoundRS qz4)) RS241to252.d66) rfl rfl rfl rfl 

noncomputable def Ns240p2384 := BSN.norm_gt_hardyZErrorBoundRS_of_le qz791 qz4 qz188 531948 1000 543245 1000 

noncomputable def Ns240p2385 := @Enclosure.norm_gt_of_isNear qz791 (hardyZErrorBoundRS qz4) Bool.true Bool.false Ns240p1508 Ns240p928 Ns240p1509 

noncomputable def Ns240p2386 := @Ns240p2385 Ns240p1510 13065801 536870912 201 536870912 (Ns240p2379 (RS241to252.d64 qz151 qz188 qz299) RS241to252.d75) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) (hardyZErrorBoundRS qz4) Bool.false 13065801 536870912 201 536870912 (@Eq.refl Real (hardyZErrorBoundRS qz4)) RS241to252.d66) rfl rfl rfl rfl 

noncomputable def Ns240p2387 := @Zeta.Certificates.ZIntervalRS.Certificate.mk qz298 (@BSN.thirtyTwoPi_le_dec qz151 541836 1000 qz156 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz790 qz791 (Ns240p2378 rfl rfl) (Ns240p2380 rfl rfl)) (Ns240p2381 qz10 qz156 rfl rfl rfl rfl (Ns240p2383 rfl)) (Ns240p2384 qz10 qz193 rfl rfl rfl rfl (Ns240p2386 rfl)) 

noncomputable abbrev qz594 := (@Enclosure.dec_le_dec qz715 qz733 543245 1000 544654 1000 (@Eq.refl Real qz715) qz736 rfl rfl rfl)

noncomputable abbrev qz300 := (RS241to252.d3 qz517 qz546 qz594)

noncomputable abbrev qz792 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz300)

noncomputable def Ns240p2388 := @Enclosure.Real.IsNear.of_eq qz792 (hardyZApproximantRS₀ qz188) Bool.true 16506867201349533794761 2361183241434822606848 169098425060469203191441 Ns240p1135 

noncomputable abbrev qz301 := qz594

noncomputable def Ns240p2389 := @Enclosure.Real.IsNear.neg_val qz792 16506867201349533794761 2361183241434822606848 169098425060469203191441 Ns240p1135 (Ns240p2388 (RS241to252.d4 qz188 qz229 qz301) RS241to252.d76) rfl 

noncomputable abbrev qz793 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz300)

noncomputable def Ns240p2390 := @Enclosure.Real.IsNear.of_eq qz793 (hardyZApproximantRS₀ qz229) Bool.false 4131970353345770931863 2361183241434822606848 33772523762985713897381 Ns240p1862 

noncomputable def Ns240p2391 := @Enclosure.Real.IsNear.pos_val qz793 4131970353345770931863 2361183241434822606848 33772523762985713897381 Ns240p1862 (Ns240p2390 (RS241to252.d46 qz188 qz229 qz301) RS241to252.d77) rfl 

noncomputable def Ns240p2392 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz792 qz4 qz188 531948 1000 543245 1000 

noncomputable def Ns240p2393 := @Enclosure.norm_gt_of_isNear qz792 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 16506867201349533794761 2361183241434822606848 169098425060469203191441 

noncomputable def Ns240p2394 := @Ns240p2393 Ns240p1135 190359677 2684354560 1213 2684354560 (Ns240p2388 (RS241to252.d4 qz188 qz229 qz301) RS241to252.d76) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS241to252.d48) rfl rfl rfl rfl 

noncomputable def Ns240p2395 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz793 qz4 qz229 531948 1000 544654 1000 

noncomputable def Ns240p2396 := @Enclosure.norm_gt_of_isNear qz793 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 4131970353345770931863 2361183241434822606848 33772523762985713897381 

noncomputable def Ns240p2397 := @Ns240p2396 Ns240p1862 190359677 2684354560 1213 2684354560 (Ns240p2390 (RS241to252.d46 qz188 qz229 qz301) RS241to252.d77) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS241to252.d48) rfl rfl rfl rfl 

noncomputable def Ns240p2398 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz188 543245 1000 qz193 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz792 qz793 (Ns240p2389 rfl rfl) (Ns240p2391 rfl rfl)) (Ns240p2392 qz10 qz193 rfl rfl rfl rfl (Ns240p2394 rfl)) (Ns240p2395 qz10 qz232 rfl rfl rfl rfl (Ns240p2397 rfl)) 

noncomputable abbrev qz794 := (@Enclosure.dec_le_dec qz857 qz861 544654 1000 546062 1000 (@Eq.refl Real qz857) qz864 rfl rfl rfl)

noncomputable abbrev qz595 := qz794

noncomputable abbrev qz302 := (RS241to252.d3 qz546 qz558 qz595)

noncomputable abbrev qz795 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz302)

noncomputable def Ns240p2399 := @Enclosure.Real.IsNear.of_eq qz795 (hardyZApproximantRS₀ qz229) Bool.false 4131970353345770931863 2361183241434822606848 33772523762985713897381 Ns240p1862 

noncomputable abbrev qz303 := qz595

noncomputable def Ns240p2400 := @Enclosure.Real.IsNear.pos_val qz795 4131970353345770931863 2361183241434822606848 33772523762985713897381 Ns240p1862 (Ns240p2399 (RS241to252.d4 qz229 qz243 qz303) RS241to252.d77) rfl 

noncomputable abbrev qz796 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz302)

noncomputable def Ns240p2401 := @Enclosure.Real.IsNear.of_eq qz796 (hardyZApproximantRS₀ qz243) Bool.true 399377046565424581139 295147905179352825856 21112414103955363722243 Ns240p1971 

noncomputable def Ns240p2402 := @Enclosure.Real.IsNear.neg_val qz796 399377046565424581139 295147905179352825856 21112414103955363722243 Ns240p1971 (Ns240p2401 (RS241to252.d46 qz229 qz243 qz303) RS241to252.d78) rfl 

noncomputable def Ns240p2403 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz795 qz4 qz229 531948 1000 544654 1000 

noncomputable def Ns240p2404 := @Enclosure.norm_gt_of_isNear qz795 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 4131970353345770931863 2361183241434822606848 33772523762985713897381 

noncomputable def Ns240p2405 := @Ns240p2404 Ns240p1862 190359677 2684354560 1213 2684354560 (Ns240p2399 (RS241to252.d4 qz229 qz243 qz303) RS241to252.d77) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS241to252.d48) rfl rfl rfl rfl 

noncomputable def Ns240p2406 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz796 qz4 qz243 531948 1000 546062 1000 

noncomputable def Ns240p2407 := @Enclosure.norm_gt_of_isNear qz796 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 399377046565424581139 295147905179352825856 21112414103955363722243 

noncomputable def Ns240p2408 := @Ns240p2407 Ns240p1971 190359677 2684354560 1213 2684354560 (Ns240p2401 (RS241to252.d46 qz229 qz243 qz303) RS241to252.d78) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS241to252.d48) rfl rfl rfl rfl 

noncomputable def Ns240p2409 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz302 (@BSN.thirtyTwoPi_le_dec qz229 544654 1000 qz232 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz795 qz796 (Ns240p2400 rfl rfl) (Ns240p2402 rfl rfl)) (Ns240p2403 qz10 qz232 rfl rfl rfl rfl (Ns240p2405 rfl)) (Ns240p2406 qz10 qz246 rfl rfl rfl rfl (Ns240p2408 rfl)) 

noncomputable abbrev qz797 := (@Enclosure.dec_le_dec qz861 qz866 546062 1000 547468 1000 qz864 qz869 rfl rfl rfl)

noncomputable abbrev qz596 := qz797

noncomputable abbrev qz304 := (RS241to252.d3 qz558 qz570 qz596)

noncomputable abbrev qz798 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz304)

noncomputable def Ns240p2410 := @Enclosure.Real.IsNear.of_eq qz798 (hardyZApproximantRS₀ qz243) Bool.true 399377046565424581139 295147905179352825856 21112414103955363722243 Ns240p1971 

noncomputable abbrev qz305 := qz596

noncomputable def Ns240p2411 := @Enclosure.Real.IsNear.neg_val qz798 399377046565424581139 295147905179352825856 21112414103955363722243 Ns240p1971 (Ns240p2410 (RS241to252.d4 qz243 qz257 qz305) RS241to252.d78) rfl 

noncomputable abbrev qz799 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz304)

noncomputable def Ns240p2412 := @Enclosure.Real.IsNear.of_eq qz799 (hardyZApproximantRS₀ qz257) Bool.false 207206867804104109367 295147905179352825856 14094061969744243737767 Ns240p2080 

noncomputable def Ns240p2413 := @Enclosure.Real.IsNear.pos_val qz799 207206867804104109367 295147905179352825856 14094061969744243737767 Ns240p2080 (Ns240p2412 (RS241to252.d46 qz243 qz257 qz305) RS241to252.d79) rfl 

noncomputable def Ns240p2414 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz798 qz4 qz243 531948 1000 546062 1000 

noncomputable def Ns240p2415 := @Enclosure.norm_gt_of_isNear qz798 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 399377046565424581139 295147905179352825856 21112414103955363722243 

noncomputable def Ns240p2416 := @Ns240p2415 Ns240p1971 190359677 2684354560 1213 2684354560 (Ns240p2410 (RS241to252.d4 qz243 qz257 qz305) RS241to252.d78) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS241to252.d48) rfl rfl rfl rfl 

noncomputable def Ns240p2417 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz799 qz4 qz257 531948 1000 547468 1000 

noncomputable def Ns240p2418 := @Enclosure.norm_gt_of_isNear qz799 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 207206867804104109367 295147905179352825856 14094061969744243737767 

noncomputable def Ns240p2419 := @Ns240p2418 Ns240p2080 190359677 2684354560 1213 2684354560 (Ns240p2412 (RS241to252.d46 qz243 qz257 qz305) RS241to252.d79) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS241to252.d48) rfl rfl rfl rfl 

noncomputable def Ns240p2420 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz243 546062 1000 qz246 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz798 qz799 (Ns240p2411 rfl rfl) (Ns240p2413 rfl rfl)) (Ns240p2414 qz10 qz246 rfl rfl rfl rfl (Ns240p2416 rfl)) (Ns240p2417 qz10 qz260 rfl rfl rfl rfl (Ns240p2419 rfl)) 

noncomputable abbrev qz875 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 547468 1000) (Enclosure.sfrac Bool.false 548874 1000) 547468 1000 548874 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 547468 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 548874 1000)) rfl rfl rfl)

noncomputable abbrev qz800 := qz875

noncomputable abbrev qz597 := qz800

noncomputable abbrev qz306 := (RS241to252.d3 qz570 qz582 qz597)

noncomputable abbrev qz801 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz306)

noncomputable def Ns240p2421 := @Enclosure.Real.IsNear.of_eq qz801 (hardyZApproximantRS₀ qz257) Bool.false 207206867804104109367 295147905179352825856 14094061969744243737767 Ns240p2080 

noncomputable abbrev qz307 := qz597

noncomputable def Ns240p2422 := @Enclosure.Real.IsNear.pos_val qz801 207206867804104109367 295147905179352825856 14094061969744243737767 Ns240p2080 (Ns240p2421 (RS241to252.d4 qz257 qz271 qz307) RS241to252.d79) rfl 

noncomputable abbrev qz802 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz306)

noncomputable def Ns240p2423 := @Enclosure.Real.IsNear.of_eq qz802 (hardyZApproximantRS₀ qz271) Bool.true 1104795413732038754515 590295810358705651712 42335503798320048298897 Ns240p69 

noncomputable def Ns240p2424 := @Enclosure.Real.IsNear.neg_val qz802 1104795413732038754515 590295810358705651712 42335503798320048298897 Ns240p69 (Ns240p2423 (RS241to252.d46 qz257 qz271 qz307) RS241to252.d80) rfl 

noncomputable def Ns240p2425 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz801 qz4 qz257 531948 1000 547468 1000 

noncomputable def Ns240p2426 := @Enclosure.norm_gt_of_isNear qz801 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 207206867804104109367 295147905179352825856 14094061969744243737767 

noncomputable def Ns240p2427 := @Ns240p2426 Ns240p2080 190359677 2684354560 1213 2684354560 (Ns240p2421 (RS241to252.d4 qz257 qz271 qz307) RS241to252.d79) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS241to252.d48) rfl rfl rfl rfl 

noncomputable def Ns240p2428 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz802 qz4 qz271 531948 1000 548874 1000 

noncomputable def Ns240p2429 := @Enclosure.norm_gt_of_isNear qz802 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1104795413732038754515 590295810358705651712 42335503798320048298897 

noncomputable def Ns240p2430 := @Ns240p2429 Ns240p69 190359677 2684354560 1213 2684354560 (Ns240p2423 (RS241to252.d46 qz257 qz271 qz307) RS241to252.d80) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 190359677 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS241to252.d48) rfl rfl rfl rfl 

noncomputable def Ns240p2431 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz306 (@BSN.thirtyTwoPi_le_dec qz257 547468 1000 qz260 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz801 qz802 (Ns240p2422 rfl rfl) (Ns240p2424 rfl rfl)) (Ns240p2425 qz10 qz260 rfl rfl rfl rfl (Ns240p2427 rfl)) (Ns240p2428 qz10 (@Eq.refl Real qz271) rfl rfl rfl rfl (Ns240p2430 rfl)) 

noncomputable def Ns240p2432 := @List.cons RS241to252.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns240p2420)) (@List.cons RS241to252.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz306 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz306) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz306) Ns240p2431)) (@List.nil RS241to252.d0)) 

noncomputable def Ns240p2433 := @List.cons RS241to252.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns240p2398)) (@List.cons RS241to252.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz302 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz302) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz302) Ns240p2409)) Ns240p2432) 

noncomputable def Ns240p2434 := @List.cons RS241to252.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inl (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns240p2376)) (@List.cons RS241to252.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz298 (@Or.inl (Zeta.Certificates.ZIntervalRS.Certificate qz298) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz298) Ns240p2387)) Ns240p2433) 

noncomputable def Ns240p2435 := @List.cons RS241to252.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns240p2354)) (@List.cons RS241to252.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz294 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz294) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz294) Ns240p2365)) Ns240p2434) 

noncomputable def Ns240p2436 := @List.cons RS241to252.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns240p2332)) (@List.cons RS241to252.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz290 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz290) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz290) Ns240p2343)) Ns240p2435) 

noncomputable def Ns240p2437 := @List.cons RS241to252.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns240p2310)) (@List.cons RS241to252.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz286 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz286) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz286) Ns240p2321)) Ns240p2436) 

noncomputable abbrev qz803 := (RS241to252.d2 qz861 qz866 (@Enclosure.dec_le_dec qz861 qz866 546062 1000 547468 1000 qz864 qz869 rfl rfl rfl))

noncomputable abbrev qz804 := (@List.cons RS241to252.d1 (RS241to252.d2 qz866 qz871 qz875) (@List.nil RS241to252.d1))

noncomputable abbrev qz598 := (@List.cons RS241to252.d1 (RS241to252.d2 qz733 qz744 qz794) (@List.cons RS241to252.d1 qz803 qz804))

noncomputable abbrev qz308 := (@List.cons RS241to252.d1 (RS241to252.d2 qz482 qz517 qz593) (@List.cons RS241to252.d1 (RS241to252.d2 qz517 qz546 qz594) qz598))

noncomputable def Ns240p2438 := @List.cons RS241to252.d1 (RS241to252.d2 qz94 qz108 qz295) (@List.cons RS241to252.d1 (RS241to252.d2 qz108 qz151 qz297) qz308) 

noncomputable def Ns240p2439 := @List.IsChain.cons_cons RS241to252.d1 RS241to252.d81 (RS241to252.d2 qz81 qz94 qz293) (RS241to252.d2 qz94 qz108 qz295) (@List.cons RS241to252.d1 (RS241to252.d2 qz108 qz151 qz297) qz308) 

noncomputable def Ns240p2440 := @List.IsChain.cons_cons RS241to252.d1 RS241to252.d81 (RS241to252.d2 qz94 qz108 qz295) (RS241to252.d2 qz108 qz151 qz297) qz308 (@Enclosure.dec_le_dec qz108 qz108 540426 1000 540426 1000 qz111 qz111 rfl rfl rfl) 

noncomputable abbrev qz309 := qz598

noncomputable abbrev qz599 := (RS241to252.d2 qz733 qz744 qz794)

noncomputable abbrev qz310 := qz599

noncomputable abbrev qz600 := (@List.cons RS241to252.d1 qz803 qz804)

noncomputable abbrev qz311 := qz600

noncomputable abbrev qz601 := qz803

noncomputable abbrev qz312 := qz601

noncomputable abbrev qz602 := qz804

noncomputable abbrev qz313 := qz602

noncomputable abbrev qz805 := (RS241to252.d2 qz866 qz871 qz875)

noncomputable abbrev qz603 := qz805

noncomputable abbrev qz314 := qz603

noncomputable def Ns240p2441 := @List.IsChain.cons_cons RS241to252.d1 RS241to252.d81 (RS241to252.d2 qz151 qz188 qz299) (RS241to252.d2 qz188 qz229 qz301) qz309 (@Enclosure.dec_le_dec qz188 qz188 543245 1000 543245 1000 qz193 qz193 rfl rfl rfl) (@List.IsChain.cons_cons RS241to252.d1 RS241to252.d81 (RS241to252.d2 qz188 qz229 qz301) qz310 qz311 (@Enclosure.dec_le_dec qz229 qz229 544654 1000 544654 1000 qz232 qz232 rfl rfl rfl) (@List.IsChain.cons_cons RS241to252.d1 RS241to252.d81 qz310 qz312 qz313 (@Enclosure.dec_le_dec qz243 qz243 546062 1000 546062 1000 qz246 qz246 rfl rfl rfl) (@List.IsChain.cons_cons RS241to252.d1 RS241to252.d81 qz312 qz314 (@List.nil RS241to252.d1) (@Enclosure.dec_le_dec qz257 qz257 547468 1000 547468 1000 qz260 qz260 rfl rfl rfl) (@List.IsChain.singleton RS241to252.d1 RS241to252.d81 qz314)))) 

noncomputable abbrev qz315 := (@List.cons RS241to252.d1 (RS241to252.d2 qz517 qz546 qz594) qz598)

noncomputable def Ns240p2442 := @List.IsChain.cons_cons RS241to252.d1 RS241to252.d81 (RS241to252.d2 qz108 qz151 qz297) (RS241to252.d2 qz151 qz188 qz299) qz315 (@Enclosure.dec_le_dec qz151 qz151 541836 1000 541836 1000 qz156 qz156 rfl rfl rfl) Ns240p2441 

noncomputable abbrev qz806 := (@List.cons RS241to252.d1 (RS241to252.d2 qz81 qz94 qz293) Ns240p2438)

noncomputable def Ns240p2443 := @List.IsChain.cons_cons RS241to252.d1 RS241to252.d81 (RS241to252.d2 qz4 qz30 qz285) (RS241to252.d2 qz30 qz54 qz287) (@List.cons RS241to252.d1 (RS241to252.d2 qz54 qz68 qz289) (@List.cons RS241to252.d1 (RS241to252.d2 qz68 qz81 qz291) qz806)) (@Enclosure.dec_le_dec qz30 qz30 533363 1000 533363 1000 qz33 qz33 rfl rfl rfl) (@List.IsChain.cons_cons RS241to252.d1 RS241to252.d81 (RS241to252.d2 qz30 qz54 qz287) (RS241to252.d2 qz54 qz68 qz289) (@List.cons RS241to252.d1 (RS241to252.d2 qz68 qz81 qz291) qz806) (@Enclosure.dec_le_dec qz54 qz54 534777 1000 534777 1000 qz57 qz57 rfl rfl rfl) (@List.IsChain.cons_cons RS241to252.d1 RS241to252.d81 (RS241to252.d2 qz54 qz68 qz289) (RS241to252.d2 qz68 qz81 qz291) qz806 (@Enclosure.dec_le_dec qz68 qz68 536191 1000 536191 1000 qz71 qz71 rfl rfl rfl) (@List.IsChain.cons_cons RS241to252.d1 RS241to252.d81 (RS241to252.d2 qz68 qz81 qz291) (RS241to252.d2 qz81 qz94 qz293) Ns240p2438 (@Enclosure.dec_le_dec qz81 qz81 537603 1000 537603 1000 qz84 qz84 rfl rfl rfl) (Ns240p2439 (@Enclosure.dec_le_dec qz94 qz94 539015 1000 539015 1000 qz97 qz97 rfl rfl rfl) (Ns240p2440 Ns240p2442))))) 

noncomputable abbrev qz604 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz605 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns240p2437 Ns240p2443)

noncomputable abbrev qz606 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns240p2437 Ns240p2443))

theorem RS241to252.d82 : Zeta.Certificates.BatchSpec 12 531948 1000 548874 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz604 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz604 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz604 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz604 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz604 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz271)))) qz605 (@And.intro (@Eq Nat (@List.length qz604 qz606) 12) (And (@Eq (Option Real) (@Option.map qz604 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz604 qz606)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz604 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz604 qz606)) (@Option.some Real qz271))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz604 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz604 qz606)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz604 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz604 qz606)) (@Option.some Real qz271)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz271))))

theorem solution : Zeta.Certificates.BatchSpec 12 531948 1000 548874 1000 := RS241to252.d82
#print axioms solution
#check solution
