-- Prove2me | solution 1 for RHHeight1000.rs_main_0277_0288
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:12:09.650879+00:00
-- url     : https://prove2.me/submissions/a79c6fde-07b7-4d9c-a8ce-4edc3f25a3a3

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

noncomputable def RS277to288.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS277to288.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS277to288.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS277to288.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS277to288.d2 a b h 

theorem RS277to288.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS277to288.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS277to288.d3 a b h)) 

noncomputable def Ns276p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns276p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns276p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns276p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns276p0 Ns276p1 Ns276p2 Ns276p1 153643044 134217728 1 57760000 153643044 134217728 1 57760000 76821522 67108864 2 67108864 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns276p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns276p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns276p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns276p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns276p8 := nat_lit 167537954069964697925743468333314178468718661948561187618563575975392713740913527107727581163208035826476740967700482432525301063254420572874757592895482956004842597348203117269212172556829666669574421653274845612596416189641484794702002223261246862056663160605878293700340502480877986491439034432953223334258717026053687371824342493299510132312376251152844516906794910572262907940062760396663270105627554083664899640691826599584783763757814813433640133591539937449421955686657622469485188711283992428713614179785896055117030632677201478317872225272595773536303110412989181984739022579128493081560758017763072115692678596043664844667144619713966763611484179303468167142547433165016751768184247559143333542643815355903304572487929375 

noncomputable def Ns276p9 := nat_lit 17907736863639440849562382641391758203535690054199171304015283257442503423240620144819838407313611418261944516207295868563739563278604805791797182761045687776939279949642059267526948014748996956777332184087524644234759874591635243045607722412471722018588244283882362848653445974523544951031470230725674276297342086185092985546835544820091590454230569790847977790484558207349923322458845585052164126500435851662252152223728079705692133047658564669873831757357628115566356048471439549797170528303905720944834637690907185213991407615774042056720704508980680095051114888612186461088301140868302968264130481206655302741383410655080008578156649725227045954510069588220729495895148666460653631514375880874422615237249871322129146554264800 

noncomputable def Ns276p10 := nat_lit 55164646516618494962085419356369025784335016154267579706247610053041231157772817011486486467101704279863254798704146668052276438579475100451766223896220272709675360577301802978530276301158911649961092601279696986330335403118086533522541958716560166657634553390183479955483588238249446822384543398154260439705049143284278540285021213103458182619368483938376641172730818250587232036579805400979202432024046862170503602539341971086573372247299262086029843105216008583038025403798224342134620653974939981235680083776396058604459065501719125356177784467570909658245422960948263734871602033841948787585406240093531041217463298165642337705122589129757920995868559518021463265498464182174549661735402095023640043996665674913376875 

noncomputable def Ns276p11 := BSN.log_dyadic_bound Ns276p6 Ns276p7 15 14 Ns276p8 134217728 57760000 Ns276p9 Ns276p10 153643044 Ns276p4 Ns276p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns276p6) (BSN.artanhQ Ns276p7) 0 14 Ns276p9 Ns276p8 Ns276p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns276p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns276p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns276p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns276p15 := nat_lit 167537954069966963268140139327979112712430526945422964221951926912223381190141639739514890494967825643602350173964944759828460064784215684919760383437959917620844610857567326816719640593037578236900835917107172977527392439886629774248115214831425484905681376157923696414882114961796820014026232307332015059110330001516939277521159573995394989771587717775443426002499543257897301982481613760098955890450106043861450716722534643739571053080256776912576113428445260435254713579381797931690799491102381747484553243404562568585572234105168360737285205910186933811836504830286397217473365026331067977496463917110493303316865058355012304571237619413071097245713770677768486493924969821719264401216877841676972336093778875903304572487929375 

noncomputable def Ns276p16 := nat_lit 17907736863639702486765313263906285882628955290251965205176678923530777959693011244026517850256414903756943142851250712732214241881959351517241344993825585048584379523049477943740273636414656012170312373198803997844271825165684859407921203335666024680974464565759223251918458072775203410604089667122984485578465112081892102496937045858735135721609691262763214794451343726045584198128451069547586972080574568545086657023793200560105564573365716615162566961587407171758966967827997201380802107846920231945878242774600967607639551032178207663699700360114112068650063802902647517702890145150192721997537569966984346993833704449560383184487996362781528900358997452380059737141488304159449328022742959995775545894292303322129146554264800 

noncomputable def Ns276p17 := nat_lit 55164646516619937449385584700664297411818070214438189962773666351465523500358685366424500506990751111492356556545320273548942244833046464529601272738875466881799996765940232256588350019911833156887888425998391295014189841212513610526066550079316346993943774342801096070086869790972589246312728227659319758310961510342377923950694747797317942483020440897997204711883064182772445608288320382376665481938194224815739627075458138172195220395246294556718284728034954178416253903237031389214179719385823921869528509431462690683227358218086518156757026652846493301460983550768858152506145788622699720737745394141184245149692548799188169247529408201840608223422296381897323845616153036586108326210125693898345963996665674913376875 

noncomputable def Ns276p18 := BSN.log_dyadic_bound Ns276p13 Ns276p14 15 14 Ns276p15 134217728 57760000 Ns276p16 Ns276p17 153643044 Ns276p12 Ns276p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns276p13) (BSN.artanhQ Ns276p14) 0 14 Ns276p16 Ns276p15 Ns276p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns276p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 76821522 67108864 2 67108864 38410761 33554432 1 33554432 (Ns276p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns276p0 Ns276p1 153643044 134217728 1 57760000 Bool.false (BSN.logfrac_isNear Ns276p4 Ns276p5 1 Ns276p0 Ns276p1 153643044 134217728 57760000 rfl rfl rfl (Ns276p11 rfl))) (BSN.isNear_log_sfrac Ns276p2 Ns276p1 153643044 134217728 1 57760000 Bool.false (BSN.logfrac_isNear Ns276p12 Ns276p5 1 Ns276p2 Ns276p1 153643044 134217728 57760000 rfl rfl rfl (Ns276p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS277to288.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 33554432 := Ns276p19 

noncomputable def Ns276p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 8388608 3610000 385100712855 135135 5814539 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz579 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz316 := qz579

noncomputable abbrev qz0 := qz316

theorem RS277to288.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 5814539 8388608 1 3610000 := BSN.isNear_log_sfrac 2 1 5814539 8388608 1 3610000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 5814539 8388608 3610000 rfl rfl rfl (Ns276p20 rfl)) 

theorem RS277to288.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 93032624 134217728 38 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 5814539 8388608 1 3610000 93032624 134217728 38 134217728 RS277to288.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz580 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz319 := qz580

noncomputable def Ns276p21 := @Enclosure.Real.IsNear.inv_image qz317 23726567 16777216 1 16777216 5931641 5931642 8388608 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 23726567 16777216 1 16777216 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 23726567 16777216 1 16777216 23726567 16777216 1 16777216 (BSN.sqrt_enclosure 2 1 11863283 11863284 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS277to288.d8 : Enclosure.Real.IsNear qz320 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 11863283 16777216 1 16777216 (Ns276p21 rfl rfl) rfl 

theorem RS277to288.d9 : Enclosure.Real.IsNear qz320 Bool.false 94906264 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 94906264 134217728 8 134217728 RS277to288.d8 rfl 

noncomputable def Ns276p22 := BSN.log_dyadic_bound 1 2 12 11 1326382131865190400 8388608 3610000 130797573554866995 13749310575 9215827 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 1) (BSN.artanhQ 2) 0 11 130797573554866995 1326382131865190400 13749310575 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS277to288.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 9215827 8388608 1 3610000 := BSN.isNear_log_sfrac 3 1 9215827 8388608 1 3610000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 9215827 8388608 3610000 rfl rfl rfl (Ns276p22 rfl)) 

theorem RS277to288.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 147453232 134217728 38 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 9215827 8388608 1 3610000 147453232 134217728 38 134217728 RS277to288.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns276p23 := @Enclosure.Real.IsNear.inv_image qz321 29058991 16777216 1 16777216 4843164 4843166 8388608 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 29058991 16777216 1 16777216 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 29058991 16777216 1 16777216 29058991 16777216 1 16777216 (BSN.sqrt_enclosure 3 1 14529495 14529496 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS277to288.d12 : Enclosure.Real.IsNear qz323 Bool.false 4843165 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 9686330 16777216 2 16777216 4843165 8388608 1 8388608 (Ns276p23 rfl rfl) rfl 

theorem RS277to288.d13 : Enclosure.Real.IsNear qz323 Bool.false 77490640 134217728 16 134217728 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 4843165 8388608 1 8388608 77490640 134217728 16 134217728 RS277to288.d12 rfl 

noncomputable def Ns276p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns276p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns276p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns276p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns276p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns276p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns276p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns276p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns276p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns276p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns276p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns276p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns276p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns276p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns276p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns276p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns276p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns276p25 Ns276p26 Ns276p27 Ns276p28 200200021673987500790625 Ns276p29 Ns276p30 Ns276p31 Ns276p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns276p32 Ns276p33 151412625 Ns276p34 Ns276p35 1322214852783825 Ns276p27 Ns276p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns276p32 Ns276p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns276p34 Ns276p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns276p36 Ns276p37 1267389585 Ns276p38 Ns276p39 1927077560082675 Ns276p29 Ns276p30 Ns276p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns276p36 Ns276p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns276p38 Ns276p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS277to288.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns276p24 Ns276p25 1 Ns276p26 := Ns276p40 rfl rfl rfl 

noncomputable def Ns276p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns276p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns276p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns276p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns276p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns276p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns276p25 Ns276p26 Ns276p42 Ns276p43 9945 Ns276p44 Ns276p45 65835 Ns276p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns276p42 Ns276p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns276p44 Ns276p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS277to288.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns276p41 Ns276p25 1 Ns276p26 := Ns276p46 rfl 

noncomputable def Ns276p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns276p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS277to288.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns276p47 Ns276p25 1 Ns276p48 := BSN.pi_combine Ns276p24 Ns276p41 Ns276p25 Ns276p26 Ns276p48 Ns276p47 rfl rfl rfl rfl RS277to288.d14 RS277to288.d15 

theorem RS277to288.d17 : Enclosure.Real.IsNear Real.pi Bool.false 7074237752028440 2251799813685248 1 2251799813685248 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns276p47 Ns276p25 1 Ns276p48 7074237752028440 2251799813685248 1 2251799813685248 RS277to288.d16 rfl 

noncomputable def Ns276p49 := nat_lit 147443727375074537121690809726715087890625 

noncomputable def Ns276p50 := nat_lit 22889945643899497138335355216896171420000 

noncomputable def Ns276p51 := nat_lit 355592320898650075318906513310625 

noncomputable def Ns276p52 := BSN.log_dyadic_bound 3 5 17 16 Ns276p49 8388608 3610000 Ns276p50 Ns276p51 11629079 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 3) (BSN.artanhQ 5) 0 16 Ns276p50 Ns276p49 Ns276p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS277to288.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 11629079 8388608 1 3610000 := BSN.isNear_log_sfrac 4 1 11629079 8388608 1 3610000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 11629079 8388608 3610000 rfl rfl rfl (Ns276p52 rfl)) 

theorem RS277to288.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 186065264 134217728 38 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 11629079 8388608 1 3610000 186065264 134217728 38 134217728 RS277to288.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns276p53 := @Enclosure.Real.IsNear.inv_image qz325 33554433 16777216 1 16777216 4194303 4194304 8388608 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 33554433 16777216 1 16777216 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 33554433 16777216 1 16777216 33554433 16777216 1 16777216 (BSN.sqrt_enclosure 4 1 16777216 16777217 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS277to288.d20 : Enclosure.Real.IsNear qz327 Bool.false 8388607 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 8388607 16777216 1 16777216 8388607 16777216 1 16777216 (Ns276p53 rfl rfl) rfl 

theorem RS277to288.d21 : Enclosure.Real.IsNear qz327 Bool.false 67108856 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 8388607 16777216 1 16777216 67108856 134217728 8 134217728 RS277to288.d20 rfl 

noncomputable def Ns276p54 := nat_lit 159424323765613091421820433543167414255940625 

noncomputable def Ns276p55 := nat_lit 33013339099500162583200499609923570567289500 

noncomputable def Ns276p56 := nat_lit 351657888879851162997374110924800000 

noncomputable def Ns276p57 := nat_lit 2289063575687431840984260 

noncomputable def Ns276p58 := nat_lit 3325435793429257756623375 

noncomputable def Ns276p59 := BSN.log_dyadic_bound 2 3 21 20 Ns276p54 8388608 3610000 Ns276p55 Ns276p56 13500943 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 20 10 9927050056596826020 47940881637414340575 686533194547200 Ns276p57 Ns276p58 512222703392784384000 Ns276p55 Ns276p54 Ns276p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 10 20 Ns276p57 Ns276p58 512222703392784384000 rfl rfl rfl rfl)) rfl rfl 

theorem RS277to288.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 13500943 8388608 1 3610000 := BSN.isNear_log_sfrac 5 1 13500943 8388608 1 3610000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 13500943 8388608 3610000 rfl rfl rfl (Ns276p59 rfl rfl)) 

theorem RS277to288.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 216015088 134217728 38 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 13500943 8388608 1 3610000 216015088 134217728 38 134217728 RS277to288.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns276p60 := @Enclosure.Real.IsNear.inv_image qz328 37514995 16777216 1 16777216 3751499 3751500 8388608 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 37514995 16777216 1 16777216 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 37514995 16777216 1 16777216 37514995 16777216 1 16777216 (BSN.sqrt_enclosure 5 1 18757497 18757498 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS277to288.d24 : Enclosure.Real.IsNear qz329 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 7502999 16777216 1 16777216 (Ns276p60 rfl rfl) rfl 

theorem RS277to288.d25 : Enclosure.Real.IsNear qz329 Bool.false 60023992 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 60023992 134217728 8 134217728 RS277to288.d24 rfl 

noncomputable def Ns276p61 := BSN.log_dyadic_bound 2 10 5 4 94500000000 8388608 3610000 1291130880 26880 3401287 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz580)

theorem RS277to288.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683410914551 2251799813685248 50000000361 180500000000000000 := BSN.isNear_log_sfrac 6 1 4034683410914551 2251799813685248 50000000361 180500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 541526040612241437360128 302231454903657293676544 1000000007220000 3610000000000000000000 4034683410914551 2251799813685248 50000000361 180500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 3401287 8388608 24973259072661432 36028797018963968 3610000 1000000000000000 rfl rfl rfl rfl (Ns276p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS277to288.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 240485871 134217728 38 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683410914551 2251799813685248 50000000361 180500000000000000 240485871 134217728 38 134217728 RS277to288.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns276p62 := @Enclosure.Real.IsNear.inv_image qz331 41095619 16777216 1 16777216 3424634 3424635 8388608 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 41095619 16777216 1 16777216 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 41095619 16777216 1 16777216 41095619 16777216 1 16777216 (BSN.sqrt_enclosure 6 1 20547809 20547810 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS277to288.d28 : Enclosure.Real.IsNear qz332 Bool.false 6849269 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 6849269 16777216 1 16777216 6849269 16777216 1 16777216 (Ns276p62 rfl rfl) rfl 

theorem RS277to288.d29 : Enclosure.Real.IsNear qz332 Bool.false 54794152 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 6849269 16777216 1 16777216 54794152 134217728 8 134217728 RS277to288.d28 rfl 

noncomputable def Ns276p63 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 8388608 3610000 11010900719820672 5524329195 4694397 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz580)

theorem RS277to288.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 50000000361 180500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 50000000361 180500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 588115238325433934020608 302231454903657293676544 1000000007220000 3610000000000000000000 4381799983422711 2251799813685248 50000000361 180500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 4694397 8388608 24973259072661432 36028797018963968 3610000 1000000000000000 rfl rfl rfl rfl (Ns276p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS277to288.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 261175631 134217728 38 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 50000000361 180500000000000000 261175631 134217728 38 134217728 RS277to288.d30 rfl 

noncomputable abbrev qz334 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns276p64 := @Enclosure.Real.IsNear.inv_image qz334 44388341 16777216 1 16777216 3170595 3170596 8388608 (@Enclosure.Real.IsNear.of_eq qz334 (Real.sqrt qz333) Bool.false 44388341 16777216 1 16777216 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 44388341 16777216 1 16777216 44388341 16777216 1 16777216 (BSN.sqrt_enclosure 7 1 22194170 22194171 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS277to288.d32 : Enclosure.Real.IsNear qz335 Bool.false 6341191 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 6341191 16777216 1 16777216 6341191 16777216 1 16777216 (Ns276p64 rfl rfl) rfl 

theorem RS277to288.d33 : Enclosure.Real.IsNear qz335 Bool.false 50729528 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 6341191 16777216 1 16777216 50729528 134217728 8 134217728 RS277to288.d32 rfl 

noncomputable def Ns276p65 := BSN.log_dyadic_bound 0 16 1 0 1 8388608 3610000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz580)

theorem RS277to288.d34 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 100000001083 361000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 100000001083 361000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false 628472642529000809299968 302231454903657293676544 1000000010830000 3610000000000000000000 9364972152248037 4503599627370496 100000001083 361000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 8388608 24973259072661432 36028797018963968 3610000 1000000000000000 rfl rfl rfl rfl (Ns276p65 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS277to288.d35 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 279097919 134217728 38 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 100000001083 361000000000000000 279097919 134217728 38 134217728 RS277to288.d34 rfl 

noncomputable abbrev qz337 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns276p66 := @Enclosure.Real.IsNear.inv_image qz337 47453133 16777216 1 16777216 2965820 2965821 8388608 (@Enclosure.Real.IsNear.of_eq qz337 (Real.sqrt qz336) Bool.false 47453133 16777216 1 16777216 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 47453133 16777216 1 16777216 47453133 16777216 1 16777216 (BSN.sqrt_enclosure 8 1 23726566 23726567 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz338 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS277to288.d36 : Enclosure.Real.IsNear qz338 Bool.false 5931641 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 5931641 16777216 1 16777216 5931641 16777216 1 16777216 (Ns276p66 rfl rfl) rfl 

theorem RS277to288.d37 : Enclosure.Real.IsNear qz338 Bool.false 47453128 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 5931641 16777216 1 16777216 47453128 134217728 8 134217728 RS277to288.d36 rfl 

noncomputable def Ns276p67 := BSN.log_dyadic_bound 1 17 3 2 1252815 8388608 3610000 1448 3 988035 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz731 := (Enclosure.sfrac Bool.false 9 1)

noncomputable abbrev qz581 := qz731

noncomputable abbrev qz339 := qz581

noncomputable abbrev qz1 := qz339

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz580)

theorem RS277to288.d38 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 9895419403785957 4503599627370496 100000001083 361000000000000000 := BSN.isNear_log_sfrac 9 1 9895419403785957 4503599627370496 100000001083 361000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz340) Bool.false 664070354991632873422848 302231454903657293676544 1000000010830000 3610000000000000000000 9895419403785957 4503599627370496 100000001083 361000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 988035 8388608 24973259072661432 36028797018963968 3610000 1000000000000000 rfl rfl rfl rfl (Ns276p67 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS277to288.d39 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 294906479 134217728 38 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 9895419403785957 4503599627370496 100000001083 361000000000000000 294906479 134217728 38 134217728 RS277to288.d38 rfl 

noncomputable abbrev qz341 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns276p68 := @Enclosure.Real.IsNear.inv_image qz341 50331649 16777216 1 16777216 2796202 2796203 8388608 (@Enclosure.Real.IsNear.of_eq qz341 (Real.sqrt qz340) Bool.false 50331649 16777216 1 16777216 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz340) Bool.false 50331649 16777216 1 16777216 50331649 16777216 1 16777216 (BSN.sqrt_enclosure 9 1 25165824 25165825 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz342 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS277to288.d40 : Enclosure.Real.IsNear qz342 Bool.false 5592405 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz342 Bool.false 5592405 16777216 1 16777216 5592405 16777216 1 16777216 (Ns276p68 rfl rfl) rfl 

theorem RS277to288.d41 : Enclosure.Real.IsNear qz342 Bool.false 44739240 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz342 Bool.false 5592405 16777216 1 16777216 44739240 134217728 8 134217728 RS277to288.d40 rfl 

theorem RS277to288.d42 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz732 := (@instHMul Real Real.instMul)

noncomputable abbrev qz582 := (@HMul.hMul Real Real Real qz732 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz343 := qz582

noncomputable abbrev qz2 := qz343

theorem RS277to288.d43 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS277to288.d42 rfl 

noncomputable abbrev qz344 := (@Inv.inv Real Real.instInv qz582)

noncomputable abbrev qz3 := qz344

theorem RS277to288.d44 : Enclosure.Real.IsNear qz3 Bool.false 2670177 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 2670177 16777216 1 16777216 2670177 16777216 1 16777216 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 1335088 1335089 8388608 RS277to288.d43 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns276p69 := nat_lit 66592746106091481333760000 

noncomputable def Ns276p70 := nat_lit 32962666426305052977362108416 

noncomputable abbrev qz733 := (Enclosure.sfrac Bool.false 582385 1000)

noncomputable abbrev qz583 := qz733

noncomputable abbrev qz345 := qz583

noncomputable abbrev qz4 := qz345

noncomputable abbrev qz584 := qz732

noncomputable abbrev qz346 := qz584

noncomputable abbrev qz5 := qz346

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 9)

noncomputable abbrev qz7 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz734 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 582385 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz585 := qz734

noncomputable abbrev qz347 := qz585

noncomputable abbrev qz8 := qz347

noncomputable abbrev qz9 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz735 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 582385 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz586 := qz735

noncomputable abbrev qz348 := qz586

noncomputable abbrev qz10 := qz348

noncomputable abbrev qz587 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz8 qz9))

noncomputable def Ns276p71 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (@HMul.hMul Real Real Real qz5 qz587 (Zeta.RiemannSiegel.correction qz10)) 120585961 67108864 45415 33554432 39160659266771150925 295147905179352825856 973257165932343606701 Ns276p69 Ns276p70 

noncomputable def Ns276p72 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 582385 1000 116 160 134217728 67108864 2251799813685248 Bool.false 137881848819 1851 

noncomputable def Ns276p73 := Ns276p72 279097919 38 47453128 8 294906479 38 44739240 8 Bool.true 146882775 74338 Bool.true 204461898 Bool.true 134666692 7074237752028440 1 Bool.false 6364428 Bool.false Bool.false 72139952 Bool.false Bool.true 120585961 

noncomputable def Ns276p74 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 582385 1000 10 67 134217728 67108864 2251799813685248 Bool.false 137881848819 1851 

noncomputable def Ns276p75 := Ns276p74 240485871 38 54794152 8 261175631 38 50729528 8 Bool.true 132098804 55463 Bool.true 65228022 Bool.true 97397194 7074237752028440 1 Bool.false 118677266 Bool.true Bool.false 89071384 Bool.false Bool.true 146882775 

noncomputable def Ns276p76 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 582385 1000 140 57 134217728 67108864 2251799813685248 Bool.false 137881848819 1851 

noncomputable def Ns276p77 := Ns276p76 186065264 38 67108856 8 216015088 38 60023992 8 Bool.true 172958768 32727 Bool.false 4210065 Bool.false 60665088 7074237752028440 1 Bool.false 134151703 Bool.false Bool.false 58620488 Bool.true Bool.true 132098804 

noncomputable def Ns276p78 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 582385 1000 397 246 134217728 67108864 2251799813685248 Bool.false 137881848819 1851 

noncomputable def Ns276p79 := Ns276p78 93032624 38 94906264 8 147453232 38 77490640 16 Bool.true 134217664 1894 Bool.false 2044579 Bool.false 143434623 7074237752028440 1 Bool.false 2044499 Bool.true Bool.false 64597571 Bool.true Bool.true 172958768 

noncomputable def Ns276p80 := nat_lit 5198900694646549423709969895377168101340296701367583 

noncomputable def Ns276p81 := nat_lit 5060743276284416580260991138798330270045752524800 

noncomputable def Ns276p82 := nat_lit 32158290331431324396823235500000000 

noncomputable def Ns276p83 := nat_lit 112371074140958184367744346650005000000 

noncomputable abbrev qz349 := (@Eq.refl Real qz583)

noncomputable abbrev qz11 := qz349

noncomputable def Ns276p84 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 582385 1000 1356690152900 16000000 1164770 4000 2000 Ns276p82 Ns276p83 qz11 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns276p85 := nat_lit 25994503473232747118549849476885840506701483506837915000000 

noncomputable abbrev qz736 := (@instHSub Real Real.instSub)

noncomputable abbrev qz588 := qz736

noncomputable abbrev qz350 := qz588

noncomputable abbrev qz589 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz737 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz738 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz590 := (@HSub.hSub Real Real Real qz736 qz737 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz738 (@Nat.cast Real Real.instNatCast 1164770))))

noncomputable abbrev qz351 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 582385 4000) (Real.log (Enclosure.sfrac Bool.false 1356690152900 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz590))

noncomputable abbrev qz591 := (Enclosure.sfrac Bool.false 582385 2000)

noncomputable abbrev qz12 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz351 qz591) (@HMul.hMul Real Real Real qz346 qz591 (Real.log Real.pi)))

noncomputable def Ns276p86 := @Enclosure.Real.IsNear.addLit_ft_p qz12 (Enclosure.sfrac Bool.true Ns276p82 Ns276p83) 231327420453670057583 225179981368524800 2038902281440203649 147865600000000000000000 Ns276p82 Ns276p83 0 1 Ns276p85 

noncomputable def Ns276p87 := nat_lit 620964815947846487808388628480 

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz350 qz351 qz591)

noncomputable def Ns276p88 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (@HMul.hMul Real Real Real qz5 qz591 (Real.log Real.pi)) 61277637005515573987 45035996273704960 368990793201813 72200000000000000000 4473970208997 13421772800 116477 13421772800 Ns276p87 231327420453670057583 225179981368524800 

noncomputable abbrev qz14 := qz351

noncomputable def Ns276p89 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz591 371958906752232027759 225179981368524800 368990793201813 72200000000000000000 582385 2000 0 1 612776370055155739870000 61277637005515573987 45035996273704960 368990793201813 72200000000000000000 

noncomputable def Ns276p90 := nat_lit 837576996923244614374480501624799232 

noncomputable def Ns276p91 := nat_lit 27437707489880747293016064 

noncomputable def Ns276p92 := nat_lit 2417851639229258349412352 

noncomputable def Ns276p93 := nat_lit 1058612280314728643891296789872470552074434760514605017021218112796528672195542057081450000000000000000 

noncomputable def Ns276p94 := nat_lit 5848143033461165718638880780337522737603453891103527547718910567910722659260883949840000000000000000 

noncomputable def Ns276p95 := nat_lit 8528692968384720922449750360606236870831320556714040091135047212786115361009050000000000000000 

noncomputable def Ns276p96 := BSN.log_dyadic_bound 308114152900 2405266152900 5 4 Ns276p93 67108864 28880000 Ns276p94 Ns276p95 17288247 2713380305800 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 308114152900) (BSN.artanhQ 2405266152900) 0 4 Ns276p94 Ns276p93 Ns276p95 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz352 := (Real.log (Enclosure.sfrac Bool.false 1356690152900 16000000))

noncomputable abbrev qz353 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns276p97 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 582385 4000) qz352 582385 4000 0 1 3194169547627767 281474976710656 781250361 22562500000000000 372047286399039416859 225179981368524800 90997698298197 18050000000000000000 (Enclosure.Real.IsNear.const Bool.false 582385 4000) (BSN.isNear_log_sfrac 1356690152900 16000000 3194169547627767 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1356690152900) qz353)) Bool.false Ns276p91 Ns276p92 1000000462080000 28880000000000000000000 3194169547627767 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1356690152900 16000000 16 2713380305800 2097152000000 17288247 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns276p96 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p98 := BSN.arctan_dyadic_bound_f 1000 1164770 1 0 8388608 3610000 0 1 1 0 1 1 7201 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1164770) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1164770) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz592 := qz737

noncomputable abbrev qz354 := qz592

noncomputable abbrev qz15 := qz354

noncomputable abbrev qz593 := qz738

noncomputable abbrev qz355 := qz593

noncomputable abbrev qz16 := qz355

noncomputable abbrev qz739 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz594 := qz739

noncomputable abbrev qz356 := qz594

noncomputable abbrev qz17 := (@Enclosure.Real.IsNear.mulLit_ff qz356 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz357 := (@Nat.cast Real Real.instNatCast 1164770)

noncomputable def Ns276p99 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 qz357)) 884279719003555 562949953421312 1 2000000000000000 7201 8388608 1 3610000 7413822122456386633728 883796468073891 562949953421312 200000000361 722000000000000000 qz17 (Ns276p98 rfl) rfl rfl 

noncomputable abbrev qz358 := (@HMul.hMul Real Real Real qz584 qz589 qz590)

noncomputable abbrev qz18 := qz358

noncomputable abbrev qz359 := qz589

noncomputable abbrev qz19 := qz359

noncomputable abbrev qz360 := qz590

noncomputable abbrev qz20 := qz360

noncomputable abbrev qz361 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns276p100 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 582385 4000) qz352) qz18 372047286399039416859 225179981368524800 90997698298197 18050000000000000000 883796468073891 2251799813685248 200000000361 2888000000000000000 Ns276p90 371958906752232027759 225179981368524800 368990793201813 72200000000000000000 (Ns276p97 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz20 1 4 0 1 883796468073891 562949953421312 200000000361 722000000000000000 883796468073891 2251799813685248 200000000361 2888000000000000000 qz361 Ns276p99 rfl) 

noncomputable def Ns276p101 := @Ns276p86 Ns276p80 Ns276p81 2038902281440203649 147865600000000000000000 (@Ns276p88 2038902281440203649 147865600000000000000000 (Ns276p89 (Ns276p100 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 582385 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz591 (Real.log Real.pi) 582385 2000 0 1 38410761 33554432 1 33554432 4473970208997 13421772800 116477 13421772800 (Enclosure.Real.IsNear.const Bool.false 582385 2000) RS277to288.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns276p82 Ns276p83) 

noncomputable abbrev qz362 := (@instHAdd Real Real.instAdd)

noncomputable def Ns276p102 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns276p80 Ns276p81 2038902281440203649 147865600000000000000000 8617615551 8388608 29 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz362 qz12 (Enclosure.sfrac Bool.true Ns276p82 Ns276p83)) Bool.false Ns276p80 Ns276p81 2038902281440203649 147865600000000000000000 Ns276p84 (Ns276p101 rfl rfl)) 

noncomputable def Ns276p103 := nat_lit 1897803255520831893143552 

noncomputable def Ns276p104 := nat_lit 1208925819614629174706176 

noncomputable def Ns276p105 := nat_lit 855017501426565709941598481885047178924205370223833912687956641655418443545715280620648257943194757037153306822294116068642007973625856 

noncomputable def Ns276p106 := nat_lit 16860812360175734222210805034837902731874731588140993779854824115686058269364094835627812361599730584878593258197117225559879026789580800 

noncomputable def Ns276p107 := nat_lit 606480147071681496129518932072769532258936134534940627213786848432206939957923761325490397317175836343770826277982870445286752256 

noncomputable def Ns276p108 := nat_lit 4269788276421767767619292625846363294580591786259014013099694780693341232973211316109345228437016461662038525829664777375801421296828416 

noncomputable def Ns276p109 := nat_lit 590128432606150697777378176219326595615615605584934782294918844049012039427743319246973432655990570470750764036899102894595765937635328000 

noncomputable abbrev qz363 := (BSN.sinEvenQ 34359738368)

noncomputable abbrev qz364 := (BSN.sinOddQ 34359738368)

noncomputable def Ns276p110 := BSN.sin_dyadic_bound_f 53938812684 34359738368 4 3 16777216 7227051 Ns276p105 Ns276p106 Ns276p107 Ns276p108 Ns276p109 Ns276p107 16777208 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53938812684) qz363 0 3 Ns276p105 Ns276p106 Ns276p107 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53938812684) qz364 0 3 Ns276p108 Ns276p109 Ns276p107 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz365 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable abbrev qz366 := (@Nat.cast Real Real.instNatCast Ns276p104)

noncomputable def Ns276p111 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8617615551) qz365) Bool.false 8617615551 8388608 29 2097152 Bool.true 16777208 16777216 1 3610000 (Ns276p102 rfl) (Enclosure.sfrac_false_div 8617615551 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8617615551) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns276p103) qz366) 226375608064910080 72057594037927936 Bool.false 16777208 16777216 163 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q1 8617615551 8388608 226375608064910080 72057594037927936 163 Ns276p103 Ns276p104 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777208 16777216 Ns276p103 Ns276p104 53938812684 34359738368 7227051 7220000 (Ns276p110 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p112 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns276p80 Ns276p81 2038902281440203649 147865600000000000000000 137881848819 134217728 1851 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz362 qz12 (Enclosure.sfrac Bool.true Ns276p82 Ns276p83)) Bool.false Ns276p80 Ns276p81 2038902281440203649 147865600000000000000000 Ns276p84 (Ns276p101 rfl rfl)) 

noncomputable def Ns276p113 := Ns276p79 32727 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 397 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 2044499 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 246 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 64597571 134217728) qz11 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 2097151 2097152 6674197 473169920000 134217664 134217728 1894 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 2097151 2097152 6674197 473169920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 16777208 16777216 106787152 7570718720000 2097151 2097152 6674197 473169920000 (Ns276p111 rfl rfl) rfl)) rfl) (Ns276p112 rfl) RS277to288.d7 

noncomputable abbrev qz367 := (BSN.sinEvenQ 134217728)

noncomputable abbrev qz368 := (BSN.sinOddQ 134217728)

noncomputable def Ns276p114 := BSN.sin_dyadic_bound_f 2044579 134217728 1 0 134217728 67108864 0 1 1 0 1 1 2044499 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 2044579) qz367 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 2044579) qz368 0 0 rfl) rfl rfl 

noncomputable def Ns276p115 := nat_lit 890344025922067462356122373587540624193941090397190018568317663354627611691035225742516235590846844556801 

noncomputable def Ns276p116 := nat_lit 16370259324565974446773555668639125346849261288577159159185037526614652227207809159774062022111344040345600 

noncomputable def Ns276p117 := nat_lit 75831204635734708216032526878041621453501509016121558846826631326652632488902776689122106787550721 

noncomputable def Ns276p118 := nat_lit 5398626551673601198444430331108445208933791534764194074507264944341667008404432677408748783907951749420545 

noncomputable def Ns276p119 := nat_lit 1489693598535503674656393565846160406563282777260521483485838414921933352675910633539439644012132307671449600 

noncomputable abbrev qz369 := (BSN.cosEvenQ 134217728)

noncomputable abbrev qz370 := (BSN.cosOddQ 134217728)

noncomputable def Ns276p120 := BSN.cos_dyadic_bound_f 143434623 134217728 4 3 134217728 67108864 Ns276p115 Ns276p116 Ns276p117 Ns276p118 Ns276p119 Ns276p117 64597571 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 143434623) qz369 0 3 Ns276p115 Ns276p116 Ns276p117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 143434623) qz370 0 3 Ns276p118 Ns276p119 Ns276p117 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p121 := nat_lit 314163122059170559702850625 

noncomputable def Ns276p122 := nat_lit 7788445287802241442795744493830144 

noncomputable def Ns276p123 := nat_lit 116826679317033621641936167407452160 

noncomputable def Ns276p124 := BSN.cos_dyadic_bound_f 4210065 134217728 2 1 134217728 67108864 Ns276p121 Ns276p122 Ns276p121 Ns276p121 Ns276p123 Ns276p121 134151703 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 4210065) qz369 0 1 Ns276p121 Ns276p122 Ns276p121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 4210065) qz370 0 1 Ns276p121 Ns276p123 Ns276p121 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p125 := nat_lit 13544261423030841593108455489536 

noncomputable def Ns276p126 := nat_lit 38942226439011207213978722469150720 

noncomputable def Ns276p127 := nat_lit 272595585073078450497851057284055040 

noncomputable def Ns276p128 := BSN.sin_dyadic_bound_f 60665088 134217728 2 1 134217728 67108864 Ns276p125 Ns276p126 Ns276p125 Ns276p125 Ns276p127 Ns276p125 58620488 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 60665088) qz367 0 1 Ns276p125 Ns276p126 Ns276p125 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 60665088) qz368 0 1 Ns276p125 Ns276p127 Ns276p125 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p129 := Ns276p77 55463 BSN.abs_quadSignPos (BSN.cos_quad_nat0 140 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 134151703 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58620488 134217728) qz11 rfl rfl (Ns276p113 RS277to288.d9 RS277to288.d11 RS277to288.d13 RS277to288.d17 (Ns276p114 rfl rfl) (Ns276p120 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns276p112 rfl) RS277to288.d19 RS277to288.d21 RS277to288.d23 RS277to288.d25 RS277to288.d17 (Ns276p124 rfl rfl) (Ns276p128 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns276p130 := nat_lit 9869611765781596714775557448312211851748869178034985516217144566016 

noncomputable def Ns276p131 := nat_lit 4246191600076225767660054876205591831097850246550140165773818614251520 

noncomputable def Ns276p132 := nat_lit 327697910390329521060956029574540767371493854683947556431585536 

noncomputable def Ns276p133 := nat_lit 29608179901524009485284550432877486473711864546395588653538570526976 

noncomputable def Ns276p134 := nat_lit 191078622003430159544702469429251632399403261094756307459821837641318400 

noncomputable def Ns276p135 := BSN.cos_dyadic_bound_f 65228022 134217728 3 2 134217728 67108864 Ns276p130 Ns276p131 Ns276p132 Ns276p133 Ns276p134 Ns276p132 118677266 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 65228022) qz369 0 2 Ns276p130 Ns276p131 Ns276p132 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 65228022) qz370 0 2 Ns276p133 Ns276p134 Ns276p132 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p136 := nat_lit 88317531407126162422725921935999874963979043416941784082480984285440 

noncomputable def Ns276p137 := nat_lit 38215724400686031908940493885850326479880652218951261491964367528263680 

noncomputable def Ns276p138 := nat_lit 8097884175685742262267086274816338440783651358794171394258166016 

noncomputable def Ns276p139 := nat_lit 231294709491903124667286125026030922262469559227885672509954731335936 

noncomputable def Ns276p140 := nat_lit 700621614012577251663909054573922652131145290680773127352680071351500800 

noncomputable def Ns276p141 := BSN.sin_dyadic_bound_f 97397194 134217728 3 2 134217728 67108864 Ns276p136 Ns276p137 Ns276p138 Ns276p139 Ns276p140 Ns276p138 89071384 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 97397194) qz367 0 2 Ns276p136 Ns276p137 Ns276p138 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 97397194) qz368 0 2 Ns276p139 Ns276p140 Ns276p138 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p142 := Ns276p75 74338 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 10 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 118677266 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 67 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 89071384 134217728) qz11 rfl rfl (Ns276p129 rfl rfl) (Ns276p112 rfl) RS277to288.d27 RS277to288.d29 RS277to288.d31 RS277to288.d33 RS277to288.d17 (Ns276p135 rfl rfl) (Ns276p141 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p143 := nat_lit 3685062746746496897420448877897062686055566003448983823146100918389411430129625455374355397258888544587776 

noncomputable def Ns276p144 := nat_lit 5337632339121623924732025667463878737620374144403639772857726447638342620931797011186154889394589696 

noncomputable def Ns276p145 := nat_lit 22308397593263420118626547935175787713764862677000239792287196487231975678493757182956324631392086635909120 

noncomputable def Ns276p146 := BSN.cos_dyadic_bound_f 204461898 134217728 4 3 134217728 67108864 Ns276p143 Ns276p116 Ns276p144 Ns276p145 Ns276p119 Ns276p144 6364428 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 204461898) qz369 0 3 Ns276p143 Ns276p116 Ns276p144 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 204461898) qz370 0 3 Ns276p145 Ns276p119 Ns276p144 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p147 := nat_lit 179412000072565601673505055391105975775227270800513438107877674909696 

noncomputable def Ns276p148 := nat_lit 108163700442882302725089540644434566630965216691557104346443350016 

noncomputable def Ns276p149 := nat_lit 538019672816811040415064987092029058192419881968157200114940138029056 

noncomputable def Ns276p150 := BSN.cos_dyadic_bound_f 134666692 134217728 3 2 134217728 67108864 Ns276p147 Ns276p131 Ns276p148 Ns276p149 Ns276p134 Ns276p148 72139952 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 134666692) qz369 0 2 Ns276p147 Ns276p131 Ns276p148 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 134666692) qz370 0 2 Ns276p149 Ns276p134 Ns276p148 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz371 := (BSN.cos_quad_nat0 160 rfl)

noncomputable def Ns276p151 := Ns276p73 90830 BSN.abs_quadSignPos (BSN.cos_quad_nat0 116 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 6364428 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 72139952 134217728) qz11 rfl rfl (Ns276p142 rfl) (Ns276p112 rfl) RS277to288.d35 RS277to288.d37 RS277to288.d39 RS277to288.d41 RS277to288.d17 (Ns276p146 rfl rfl) (Ns276p150 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p152 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) 120585961 134217728 90830 134217728 120585961 134217728 90830 134217728 32369547428233216 120585961 67108864 45415 33554432 (Ns276p151 rfl) 

noncomputable def Ns276p153 := @Enclosure.Real.IsNear.mulLit_tf qz587 (Zeta.RiemannSiegel.correction qz10) 2703537 8388608 1 8388608 14484972562525 35184372088832 89696260418563 1984618488135680000 39160659266771150925 295147905179352825856 

noncomputable abbrev qz595 := (@HPow.hPow Real Real Real qz7 qz8 qz9)

noncomputable def Ns276p154 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz595 1 1 0 1 2703537 8388608 1 8388608 2703537 8388608 1 8388608 

noncomputable abbrev qz21 := (@Enclosure.Real.IsNear.of_eq qz347 (@HMul.hMul Real Real Real qz346 qz345 qz344) Bool.false 311014206429 3355443200 116477 3355443200 (BSN.t_div_two_pi_mk qz345 582385 1000 qz349) (@Enclosure.Real.IsNear.mulLit_ff qz345 qz344 582385 1000 0 1 2670177 16777216 1 16777216 311014206429 3355443200 116477 3355443200 (Enclosure.Real.IsNear.const Bool.false 582385 1000) RS277to288.d44 rfl))

noncomputable def Ns276p155 := @Enclosure.Real.IsNear.sqrt_image qz8 311014206429 3355443200 116477 3355443200 80761613 80761644 8388608 qz21 

noncomputable abbrev qz740 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 582385 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz596 := qz740

noncomputable abbrev qz372 := qz596

noncomputable abbrev qz22 := qz372

noncomputable def Ns276p156 := @Enclosure.Real.IsNear.sqrt_image qz22 161523257 16777216 31 16777216 26028398 26028404 8388608 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 161523257 16777216 31 16777216 161523257 16777216 31 16777216 (Ns276p155 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz597 := (Real.sqrt qz740)

noncomputable abbrev qz373 := qz597

noncomputable abbrev qz23 := qz373

noncomputable def Ns276p157 := @Enclosure.Real.IsNear.inv_image qz23 26028401 8388608 3 8388608 2703536 2703538 8388608 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 52056802 16777216 6 16777216 26028401 8388608 3 8388608 (Ns276p156 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns276p158 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz23) Bool.false 5407074 16777216 2 16777216 2703537 8388608 1 8388608 (Ns276p157 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz374 := (@HMul.hMul Real Real Real qz584 qz582 qz586)

noncomputable abbrev qz24 := (Real.cos qz374)

noncomputable abbrev qz598 := (@HMul.hMul Real Real Real qz732 qz735 qz735)

noncomputable abbrev qz599 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz375 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz598 qz586) qz599)

noncomputable abbrev qz25 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz375))

noncomputable def Ns276p159 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz10) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz24) qz25) Bool.false 14484972562525 

noncomputable def Ns276p160 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz24) qz25 6028475 4194304 13 

noncomputable abbrev qz26 := (@Neg.neg Real Real.instNeg (Real.cos qz374))

noncomputable def Ns276p161 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz24) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz26)) Bool.true 6028475 4194304 13 524288 (BSN.inv_eq_neg_inv_neg qz24) 

noncomputable def Ns276p162 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz26) Bool.false 24113900 16777216 416 16777216 6028475 4194304 

noncomputable def Ns276p163 := @Enclosure.Real.IsNear.recentre' qz24 Bool.true 11672727 16777216 181084304 15141437440000 11672727 16777216 11317769 946339840000 

noncomputable abbrev qz27 := qz374

noncomputable abbrev qz376 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable def Ns276p164 := @Enclosure.Real.IsNear.cos_image qz27 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 66151341) qz376) Bool.false 66151341 16777216 49 4194304 Bool.true 11672727 16777216 1 

noncomputable def Ns276p165 := nat_lit 836568337770802929144341273 

noncomputable def Ns276p166 := nat_lit 72057594037927936000000000000000 

noncomputable def Ns276p167 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz10 884279719003555 140737488355328 1 500000000000000 10528313 16777216 31 16777216 9309973661221475152715 2361183241434822606848 Ns276p165 

noncomputable def Ns276p168 := @Enclosure.Real.IsNear.subLit_ff_p qz22 qz1 161523257 16777216 31 16777216 9 1 0 1 10528313 10528313 16777216 31 

noncomputable abbrev qz377 := (Enclosure.Real.IsNear.const Bool.false 9 1)

noncomputable def Ns276p169 := @Ns276p168 16777216 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 161523257 16777216 31 16777216 161523257 16777216 31 16777216 (Ns276p155 rfl rfl rfl rfl rfl rfl) rfl) qz377 

noncomputable def Ns276p170 := @Enclosure.Real.IsNear.recentre' qz27 Bool.false 9309973661221475152715 2361183241434822606848 Ns276p165 Ns276p166 66151341 16777216 49 4194304 (@Ns276p167 Ns276p166 RS277to288.d43 (Ns276p169 rfl rfl) rfl) 

noncomputable def Ns276p171 := nat_lit 1937508002412398790049792 

noncomputable def Ns276p172 := nat_lit 1346077523430083200331437302090377800798764315173762603808843295582809171528239681892321 

noncomputable def Ns276p173 := nat_lit 78328409734541396139472704083124282315821843750582265496873076360672620779474006646456320 

noncomputable def Ns276p174 := nat_lit 330300807173824339238986610174183095219505041296253225575855411878747604120082051041 

noncomputable def Ns276p175 := nat_lit 4037571968675901952315833933050785036205853935438695304975378175924670019376478881574881 

noncomputable def Ns276p176 := nat_lit 3524778438054362826276271683740592704211982968776201947359288436230267935076330299090534400 

noncomputable abbrev qz378 := (BSN.cosEvenQ 34359738368)

noncomputable abbrev qz379 := (BSN.cosOddQ 34359738368)

noncomputable def Ns276p177 := BSN.cos_dyadic_bound_f 27533644731 34359738368 3 2 16777216 7227051 Ns276p172 Ns276p173 Ns276p174 Ns276p175 Ns276p176 Ns276p174 11672727 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 27533644731) qz378 0 2 Ns276p172 Ns276p173 Ns276p174 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 27533644731) qz379 0 2 Ns276p175 Ns276p176 Ns276p174 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz380 := (@Nat.cast Real Real.instNatCast Ns276p92)

noncomputable def Ns276p178 := @Ns276p164 3610000 (Ns276p170 rfl) (Enclosure.sfrac_false_div 66151341 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 66151341) qz376) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns276p171) qz380) 226375608064910080 72057594037927936 Bool.false 11672727 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 66151341 16777216 226375608064910080 72057594037927936 0 Ns276p171 Ns276p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 11672727 16777216 Ns276p171 Ns276p92 27533644731 34359738368 7227051 7220000 (Ns276p177 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p179 := @Enclosure.Real.IsNear.inv_image qz26 11672727 16777216 11317769 946339840000 12056742 12057158 8388608 (@Enclosure.Real.IsNear.neg qz24 Bool.true 11672727 16777216 11317769 946339840000 (Ns276p163 (Ns276p178 rfl rfl) rfl)) 

noncomputable def Ns276p180 := Ns276p161 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz26) Bool.false 6028475 4194304 13 524288 (@Ns276p162 13 524288 (Ns276p179 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p181 := @Enclosure.Real.IsNear.recentre' qz25 Bool.true 2402759 8388608 

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz346 qz343 qz375)

noncomputable def Ns276p182 := @Enclosure.Real.IsNear.cos_image qz28 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 31227367)) qz376) Bool.true 31227367 16777216 

noncomputable def Ns276p183 := nat_lit 73733535673542301966718120525 

noncomputable def Ns276p184 := nat_lit 39614081257132168796771975168 

noncomputable def Ns276p185 := nat_lit 31650620244336310499575283457117481 

noncomputable def Ns276p186 := @Enclosure.Real.IsNear.recentre' qz28 Bool.true Ns276p183 Ns276p184 Ns276p185 

noncomputable def Ns276p187 := nat_lit 1208925819614629174706176000000000000000 

noncomputable abbrev qz29 := qz375

noncomputable def Ns276p188 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz29 884279719003555 140737488355328 1 500000000000000 83382592735055 

noncomputable abbrev qz381 := (@HSub.hSub Real Real Real qz588 qz598 qz586)

noncomputable abbrev qz30 := qz381

noncomputable abbrev qz382 := qz599

noncomputable abbrev qz31 := qz382

noncomputable def Ns276p189 := @Enclosure.Real.IsNear.subLit_tf qz30 qz31 65790406690639 281474976710656 1172850063 281474976710656 1 16 

noncomputable abbrev qz383 := qz598

noncomputable abbrev qz32 := qz383

noncomputable def Ns276p190 := @Enclosure.Real.IsNear.subLit_ff_n qz32 qz10 110845374625969 281474976710656 652756367 281474976710656 10528313 16777216 31 16777216 

noncomputable def Ns276p191 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz10 10528313 16777216 31 16777216 10528313 16777216 31 16777216 110845374625969 281474976710656 

noncomputable def Ns276p192 := nat_lit 119983387847153564487548708694346731814784744259392999886343056187010888697122902208858540852641 

noncomputable def Ns276p193 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600 

noncomputable def Ns276p194 := nat_lit 859853390435699407649224649653757525773509085028282150906435604489358772097468431552595361 

noncomputable def Ns276p195 := nat_lit 724452649247928250268883478078663796632936549460321481537643643284352595154641858794804835632545 

noncomputable def Ns276p196 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600 

noncomputable abbrev qz600 := (BSN.cosEvenQ 16777216)

noncomputable def Ns276p197 := BSN.cos_dyadic_bound_t 31227367 16777216 4 3 8388608 3610000 Ns276p192 Ns276p193 Ns276p194 Ns276p195 Ns276p196 Ns276p194 2402759 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 31227367) qz600 0 3 Ns276p192 Ns276p193 Ns276p194 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 31227367) (BSN.cosOddQ 16777216) 0 3 Ns276p195 Ns276p196 Ns276p194 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz384 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns276p198 := @Ns276p181 200647152 7570718720000 2402759 8388608 12540447 473169920000 (@Ns276p182 55 2097152 Bool.true 2402759 8388608 1 3610000 (@Ns276p186 Ns276p187 31227367 16777216 55 2097152 (@Ns276p188 281474976710656 1172850063 281474976710656 Ns276p183 Ns276p184 Ns276p185 Ns276p187 RS277to288.d43 (@Ns276p189 0 1 1334121483760880 83382592735055 281474976710656 1172850063 281474976710656 (@Ns276p190 1103779863776695681024 65790406690639 281474976710656 1172850063 281474976710656 (@Ns276p191 652756367 281474976710656 (Ns276p169 rfl rfl) (Ns276p169 rfl rfl) rfl) (Ns276p169 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 31227367 16777216) (BSN.cos_neg_of_bound 31227367 16777216 Bool.true 2402759 8388608 1 3610000 (Ns276p197 rfl rfl)) rfl rfl) 

noncomputable abbrev qz33 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 9) (Enclosure.sfrac Bool.true 1 1) Bool.true 1 1 0 1 (BSN.neg_one_pow_odd_mk 9 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1))

noncomputable def Ns276p199 := @Ns276p153 973257165932343606701 Ns276p69 (Ns276p154 qz33 (@Enclosure.Real.IsNear.of_eq qz595 (@Inv.inv Real Real.instInv qz23) Bool.false 2703537 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz8 (BSN.t_div_two_pi_nonneg qz4 582385 1000 qz11)) Ns276p158) rfl) (@Ns276p159 35184372088832 89696260418563 1984618488135680000 (BSN.correction_mk qz10 (BSN.cos_two_pi_p_ne_zero_mk qz4 582385 1000 9 qz11 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 582385 1000 9 qz11 rfl rfl rfl))) (@Ns276p160 524288 2402759 8388608 12540447 473169920000 14484972562525 35184372088832 89696260418563 1984618488135680000 Ns276p180 (Ns276p198 rfl) rfl)) 

noncomputable abbrev qz34 := qz350

noncomputable def Ns276p200 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 491182005797401860019 295147905179352825856 91104705804614250806701 Ns276p69 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (@HMul.hMul Real Real Real qz5 qz587 (Zeta.RiemannSiegel.correction qz10))) Bool.true 491182005797401860019 295147905179352825856 91104705804614250806701 Ns276p69 (BSN.hardyZApproximantRS₀_eq qz4 9 (@BSN.floor_sqrt_eq_dec qz4 582385 1000 9 qz11 rfl rfl rfl)) (@Ns276p71 491182005797401860019 295147905179352825856 91104705804614250806701 Ns276p69 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9)) Bool.true 120585961 67108864 45415 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (Ns276p152 (Ns276p151 rfl) rfl rfl)) (Ns276p199 rfl) rfl rfl)) 

theorem RS277to288.d45 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 491182005797401860019 295147905179352825856 91104705804614250806701 Ns276p69 := Ns276p200 

theorem RS277to288.d46 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS277to288.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS277to288.d3 a b h)) 

noncomputable def Ns276p201 := nat_lit 2130967875394927402680320 

noncomputable def Ns276p202 := nat_lit 14787124785571223704648548352 

noncomputable abbrev qz741 := (Enclosure.sfrac Bool.false 583772 1000)

noncomputable abbrev qz601 := qz741

noncomputable abbrev qz385 := qz601

noncomputable abbrev qz35 := qz385

noncomputable abbrev qz742 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 583772 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz602 := qz742

noncomputable abbrev qz386 := qz602

noncomputable abbrev qz36 := qz386

noncomputable abbrev qz743 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 583772 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz603 := qz743

noncomputable abbrev qz387 := qz603

noncomputable abbrev qz37 := qz387

noncomputable abbrev qz604 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz36 qz9))

noncomputable def Ns276p203 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) (@HMul.hMul Real Real Real qz5 qz604 (Zeta.RiemannSiegel.correction qz37)) 22795571 16777216 22761 16777216 79333468051958891925 590295810358705651712 34065048826325466297 Ns276p201 Ns276p202 

noncomputable def Ns276p204 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 583772 1000 116 160 134217728 67108864 2251799813685248 Bool.false 138303542616 1856 

noncomputable def Ns276p205 := Ns276p204 279097919 38 47453128 8 294906479 38 44739240 8 Bool.false 49434539 74512 Bool.true 169876915 Bool.true 122008181 7074237752028440 1 Bool.false 40319349 Bool.false Bool.false 82478118 Bool.false Bool.false 91182284 

noncomputable def Ns276p206 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 583772 1000 9 67 134217728 67108864 2251799813685248 Bool.false 138303542616 1856 

noncomputable def Ns276p207 := Ns276p206 240485871 38 54794152 8 261175631 38 50729528 8 Bool.false 89277416 55592 Bool.true 187916842 Bool.true 37953997 7074237752028440 1 Bool.false 132266866 Bool.true Bool.false 37450189 Bool.false Bool.false 49434539 

noncomputable def Ns276p208 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 583772 1000 140 57 134217728 67108864 2251799813685248 Bool.false 138303542616 1856 

noncomputable def Ns276p209 := Ns276p208 186065264 38 67108856 8 216015088 38 60023992 8 Bool.false 126859478 32801 Bool.false 167831341 Bool.false 182745958 7074237752028440 1 Bool.false 42265685 Bool.false Bool.false 131290513 Bool.true Bool.false 89277416 

noncomputable def Ns276p210 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 583772 1000 398 247 134217728 67108864 2251799813685248 Bool.false 138303542616 1856 

noncomputable def Ns276p211 := Ns276p210 93032624 38 94906264 8 147453232 38 77490640 16 Bool.false 134217688 1894 Bool.false 83873413 Bool.false 149782074 7074237752028440 1 Bool.false 108853038 Bool.true Bool.false 120572408 Bool.false Bool.false 126859478 

noncomputable def Ns276p212 := nat_lit 1576472183935255378792107455337975106409669280818009 

noncomputable def Ns276p213 := nat_lit 1529899457235026429142407014807678905017696256000 

noncomputable def Ns276p214 := nat_lit 32543057075571691144892121743360000 

noncomputable def Ns276p215 := nat_lit 113986392113195838715315387756204523520 

noncomputable abbrev qz605 := (@Eq.refl Real qz741)

noncomputable abbrev qz388 := qz605

noncomputable abbrev qz38 := qz388

noncomputable def Ns276p216 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz35 583772 1000 1363159991936 16000000 1167544 4000 2000 Ns276p214 Ns276p215 qz38 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns276p217 := nat_lit 16530508967420943440723128670884725851786253758030246051840 

noncomputable abbrev qz606 := (@HSub.hSub Real Real Real qz736 qz737 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz738 (@Nat.cast Real Real.instNatCast 1167544))))

noncomputable abbrev qz389 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 583772 4000) (Real.log (Enclosure.sfrac Bool.false 1363159991936 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz606))

noncomputable abbrev qz607 := (Enclosure.sfrac Bool.false 583772 2000)

noncomputable abbrev qz39 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz389 qz607) (@HMul.hMul Real Real Real qz346 qz607 (Real.log Real.pi)))

noncomputable def Ns276p218 := @Enclosure.Real.IsNear.addLit_ft_p qz39 (Enclosure.sfrac Bool.true Ns276p214 Ns276p215) 145021815683342215117 140737488355328000 2554667144073261091 184832000000000000000000 Ns276p214 Ns276p215 0 1 Ns276p217 

noncomputable def Ns276p219 := nat_lit 2433062326431619944936374272000 

noncomputable abbrev qz40 := (@HSub.hSub Real Real Real qz350 qz389 qz607)

noncomputable def Ns276p220 := @Enclosure.Real.IsNear.subLit_ff_p qz40 (@HMul.hMul Real Real Real qz5 qz607 (Real.log Real.pi)) 192046520836333053901 140737488355328000 1849288343011893 361000000000000000000 5605781692623 16777216000 145943 16777216000 Ns276p219 145021815683342215117 140737488355328000 

noncomputable abbrev qz41 := qz389

noncomputable def Ns276p221 := @Enclosure.Real.IsNear.subLit_ff_p qz41 qz607 233125823362416322509 140737488355328000 1849288343011893 361000000000000000000 583772 2000 0 1 384093041672666107802000 192046520836333053901 140737488355328000 1849288343011893 361000000000000000000 

noncomputable def Ns276p222 := nat_lit 1049905371225418220922725901967294464 

noncomputable def Ns276p223 := nat_lit 27449210439933788938043392 

noncomputable def Ns276p224 := nat_lit 1081608087780303044496348574349935463777273712076141698837065848450131129205455575941827135983761489920 

noncomputable def Ns276p225 := nat_lit 6197656013955204879841173765548943990265819083892509454749472338768083018532940543250213889128792064 

noncomputable def Ns276p226 := nat_lit 10071223924438390090144524451152418617331268982180618408996193081081072669754012392334693498880 

noncomputable def Ns276p227 := BSN.log_dyadic_bound 314583991936 2411735991936 5 4 Ns276p224 67108864 28880000 Ns276p225 Ns276p226 17607518 2726319983872 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 314583991936) (BSN.artanhQ 2411735991936) 0 4 Ns276p225 Ns276p224 Ns276p226 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz390 := (Real.log (Enclosure.sfrac Bool.false 1363159991936 16000000))

noncomputable def Ns276p228 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 583772 4000) qz390 583772 4000 0 1 3195508667260151 281474976710656 781250361 22562500000000000 466362121425948217393 281474976710656000 114018021435423 22562500000000000000 (Enclosure.Real.IsNear.const Bool.false 583772 4000) (BSN.isNear_log_sfrac 1363159991936 16000000 3195508667260151 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1363159991936) qz353)) Bool.false Ns276p223 Ns276p92 1000000462080000 28880000000000000000000 3195508667260151 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1363159991936 16000000 16 2726319983872 2097152000000 17607518 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns276p227 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p229 := BSN.arctan_dyadic_bound_f 1000 1167544 1 0 8388608 3610000 0 1 1 0 1 1 7184 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1167544) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1167544) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz391 := (@Nat.cast Real Real.instNatCast 1167544)

noncomputable def Ns276p230 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 qz391)) 884279719003555 562949953421312 1 2000000000000000 7184 8388608 1 3610000 7413831692605594796032 883797608924579 562949953421312 200000000361 722000000000000000 qz17 (Ns276p229 rfl) rfl rfl 

noncomputable abbrev qz392 := (@HMul.hMul Real Real Real qz584 qz589 qz606)

noncomputable abbrev qz42 := qz392

noncomputable abbrev qz393 := qz606

noncomputable abbrev qz43 := qz393

noncomputable def Ns276p231 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 583772 4000) qz390) qz42 466362121425948217393 281474976710656000 114018021435423 22562500000000000000 883797608924579 2251799813685248 200000000361 2888000000000000000 Ns276p222 233125823362416322509 140737488355328000 1849288343011893 361000000000000000000 (Ns276p228 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz43 1 4 0 1 883797608924579 562949953421312 200000000361 722000000000000000 883797608924579 2251799813685248 200000000361 2888000000000000000 qz361 Ns276p230 rfl) 

noncomputable def Ns276p232 := @Ns276p218 Ns276p212 Ns276p213 2554667144073261091 184832000000000000000000 (@Ns276p220 2554667144073261091 184832000000000000000000 (Ns276p221 (Ns276p231 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 583772 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz607 (Real.log Real.pi) 583772 2000 0 1 38410761 33554432 1 33554432 5605781692623 16777216000 145943 16777216000 (Enclosure.Real.IsNear.const Bool.false 583772 2000) RS277to288.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns276p214 Ns276p215) 

noncomputable def Ns276p233 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns276p212 Ns276p213 2554667144073261091 184832000000000000000000 17287942827 16777216 29 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz362 qz39 (Enclosure.sfrac Bool.true Ns276p214 Ns276p215)) Bool.false Ns276p212 Ns276p213 2554667144073261091 184832000000000000000000 Ns276p216 (Ns276p232 rfl rfl)) 

noncomputable def Ns276p234 := nat_lit 3796261725946780785311744 

noncomputable def Ns276p235 := nat_lit 855609227659728428460047254497156289417738956492591913731680051612167446076382881420944469655515885909025848610598746884110873731792896 

noncomputable def Ns276p236 := nat_lit 607737661001583072413877427189590656770200231122327310733761986998988682085606808510359488472130274016781526669847538699648106496 

noncomputable def Ns276p237 := nat_lit 4272739583267535368994522257619877712087771235314143240346131590518607285260235517357539478884491981646407041068686825201929190172000256 

noncomputable def Ns276p238 := BSN.sin_dyadic_bound_f 53948123848 34359738368 4 3 16777216 7227051 Ns276p235 Ns276p106 Ns276p236 Ns276p237 Ns276p109 Ns276p236 16777211 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53948123848) qz363 0 3 Ns276p235 Ns276p106 Ns276p236 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53948123848) qz364 0 3 Ns276p237 Ns276p109 Ns276p236 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p239 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz35) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17287942827) qz376) Bool.false 17287942827 16777216 29 2097152 Bool.false 16777211 16777216 1 3610000 (Ns276p233 rfl) (Enclosure.sfrac_false_div 17287942827 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17287942827) qz376) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns276p234) qz380) 226375608064910080 72057594037927936 Bool.false 16777211 16777216 163 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q3 17287942827 16777216 226375608064910080 72057594037927936 163 Ns276p234 Ns276p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777211 16777216 Ns276p234 Ns276p92 53948123848 34359738368 7227051 7220000 (Ns276p238 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p240 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns276p212 Ns276p213 2554667144073261091 184832000000000000000000 138303542616 134217728 1856 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz362 qz39 (Enclosure.sfrac Bool.true Ns276p214 Ns276p215)) Bool.false Ns276p212 Ns276p213 2554667144073261091 184832000000000000000000 Ns276p216 (Ns276p232 rfl rfl)) 

noncomputable def Ns276p241 := Ns276p211 32801 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 398 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 108853038 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 247 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 120572408 134217728) qz38 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) Bool.false 16777211 16777216 6674197 473169920000 134217688 134217728 1894 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 16777211 16777216 6674197 473169920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz35) qz35) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 16777211 16777216 106787152 7570718720000 16777211 16777216 6674197 473169920000 (Ns276p239 rfl rfl) rfl)) rfl) (Ns276p240 rfl) RS277to288.d7 

noncomputable def Ns276p242 := nat_lit 26982705687310482004520487792340073325364451917273776413648509164001 

noncomputable def Ns276p243 := nat_lit 2449032375785130248880480029905134386757138510432153507742833121 

noncomputable def Ns276p244 := nat_lit 80943218997179875753063702416960409707319841474800464933930041825761 

noncomputable def Ns276p245 := BSN.cos_dyadic_bound_f 83873413 134217728 3 2 134217728 67108864 Ns276p242 Ns276p131 Ns276p243 Ns276p244 Ns276p134 Ns276p243 108853038 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 83873413) qz369 0 2 Ns276p242 Ns276p131 Ns276p243 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 83873413) qz370 0 2 Ns276p244 Ns276p134 Ns276p243 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p246 := nat_lit 494177949526399931742560325377552214335013214407582234076412445630720 

noncomputable def Ns276p247 := nat_lit 253325389452595692062828921421125231082641542604627419297658347776 

noncomputable def Ns276p248 := nat_lit 1293865436224314666300508652973193025265186522855641216283169720279296 

noncomputable def Ns276p249 := BSN.sin_dyadic_bound_f 149782074 134217728 3 2 134217728 67108864 Ns276p246 Ns276p137 Ns276p247 Ns276p248 Ns276p140 Ns276p247 120572408 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 149782074) qz367 0 2 Ns276p246 Ns276p137 Ns276p247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 149782074) qz368 0 2 Ns276p248 Ns276p140 Ns276p247 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p250 := nat_lit 1670047141618458469971463980248182855723066192649208115534578847695216980109135048508174792039916058438961 

noncomputable def Ns276p251 := nat_lit 499432472290229546634904822552792759221422042275492159123497080888036417559002640111217418353765681 

noncomputable def Ns276p252 := nat_lit 10121801590603802635990541120754281489740026188841560716202660856050075370185407034515241311552730882370865 

noncomputable def Ns276p253 := BSN.cos_dyadic_bound_f 167831341 134217728 4 3 134217728 67108864 Ns276p250 Ns276p116 Ns276p251 Ns276p252 Ns276p119 Ns276p251 42265685 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 167831341) qz369 0 3 Ns276p250 Ns276p116 Ns276p251 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 167831341) qz370 0 3 Ns276p252 Ns276p119 Ns276p251 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p254 := nat_lit 6101865747747336108303863944323601339142100797532108344903250431254194427022449176519554235391934615719936 

noncomputable def Ns276p255 := nat_lit 212813371219357667808056223692308629509040396751503069069405487845990478953701519077062806287447472524492800 

noncomputable def Ns276p256 := nat_lit 1387309497370370958299949578411983670867943885451329313887703671108701154229428931974793265932865536 

noncomputable def Ns276p257 := nat_lit 30487912764571068815626622573401883631315576994802573616504902662075677691906454015887341870483487226269696 

noncomputable def Ns276p258 := nat_lit 7448467992677518373281967829230802032816413886302607417429192074609666763379553167697198220060661538357248000 

noncomputable def Ns276p259 := BSN.sin_dyadic_bound_f 182745958 134217728 4 3 134217728 67108864 Ns276p254 Ns276p255 Ns276p256 Ns276p257 Ns276p258 Ns276p256 131290513 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 182745958) qz367 0 3 Ns276p254 Ns276p255 Ns276p256 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 182745958) qz368 0 3 Ns276p257 Ns276p258 Ns276p256 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p260 := Ns276p209 55592 BSN.abs_quadSignPos (BSN.cos_quad_nat0 140 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 42265685 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 131290513 134217728) qz38 rfl rfl (Ns276p241 RS277to288.d9 RS277to288.d11 RS277to288.d13 RS277to288.d17 (Ns276p245 rfl rfl) (Ns276p249 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns276p240 rfl) RS277to288.d19 RS277to288.d21 RS277to288.d23 RS277to288.d25 RS277to288.d17 (Ns276p253 rfl rfl) (Ns276p259 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns276p261 := nat_lit 6823270433233550027989280800706265275208444453839715915378720090504898382809049647545511920991141420404736 

noncomputable def Ns276p262 := nat_lit 1939047574205917857647909980301158677583649741738882390909234025831964902063844680881975671289614336 

noncomputable def Ns276p263 := nat_lit 34089579321082756074018037444507350888660798653731926550536839370500357954297837122689028961425100179050496 

noncomputable def Ns276p264 := BSN.sin_dyadic_bound_f 187916842 134217728 4 3 134217728 67108864 Ns276p261 Ns276p255 Ns276p262 Ns276p263 Ns276p258 Ns276p262 132266866 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 187916842) qz367 0 3 Ns276p261 Ns276p255 Ns276p262 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 187916842) qz368 0 3 Ns276p263 Ns276p258 Ns276p262 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p265 := nat_lit 2075057214157853723358164968081 

noncomputable def Ns276p266 := BSN.sin_dyadic_bound_f 37953997 134217728 2 1 134217728 67108864 Ns276p265 Ns276p126 Ns276p265 Ns276p265 Ns276p127 Ns276p265 37450189 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 37953997) qz367 0 1 Ns276p265 Ns276p126 Ns276p265 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 37953997) qz368 0 1 Ns276p265 Ns276p127 Ns276p265 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p267 := Ns276p207 74512 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 9 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132266866 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 67 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 37450189 134217728) qz38 rfl rfl (Ns276p260 rfl rfl) (Ns276p240 rfl) RS277to288.d27 RS277to288.d29 RS277to288.d31 RS277to288.d33 RS277to288.d17 (Ns276p264 rfl rfl) (Ns276p266 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p268 := nat_lit 1753094313112764721735771794684884156415869465729101106559893420174281900837507852470625155180509825640625 

noncomputable def Ns276p269 := nat_lit 577580318843868336254500355327710598918756247354207795386024287857225715313494109945784023681640625 

noncomputable def Ns276p270 := nat_lit 10624621821681224282072778393318433937358494025440603629857520811271064135652119736158764589420336155240625 

noncomputable def Ns276p271 := BSN.cos_dyadic_bound_f 169876915 134217728 4 3 134217728 67108864 Ns276p268 Ns276p116 Ns276p269 Ns276p270 Ns276p119 Ns276p269 40319349 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 169876915) qz369 0 3 Ns276p268 Ns276p116 Ns276p269 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 169876915) qz370 0 3 Ns276p270 Ns276p119 Ns276p269 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p272 := nat_lit 120859587014163848483701525603514631048345956989169842255221768724321 

noncomputable def Ns276p273 := nat_lit 49103406145138727637561099590170291848347180215157983557017804641 

noncomputable def Ns276p274 := nat_lit 362480554230201267995829454611363552561341176607079210798551270563681 

noncomputable def Ns276p275 := BSN.cos_dyadic_bound_f 122008181 134217728 3 2 134217728 67108864 Ns276p272 Ns276p131 Ns276p273 Ns276p274 Ns276p134 Ns276p273 82478118 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 122008181) qz369 0 2 Ns276p272 Ns276p131 Ns276p273 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 122008181) qz370 0 2 Ns276p274 Ns276p134 Ns276p273 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p276 := Ns276p205 91044 BSN.abs_quadSignPos (BSN.cos_quad_nat0 116 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 40319349 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 82478118 134217728) qz38 rfl rfl (Ns276p267 rfl) (Ns276p240 rfl) RS277to288.d35 RS277to288.d37 RS277to288.d39 RS277to288.d41 RS277to288.d17 (Ns276p271 rfl rfl) (Ns276p275 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p277 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) 91182284 134217728 91044 134217728 91182284 134217728 91044 134217728 24476557984661504 22795571 16777216 22761 16777216 (Ns276p276 rfl) 

noncomputable def Ns276p278 := @Enclosure.Real.IsNear.mulLit_tf qz604 (Zeta.RiemannSiegel.correction qz37) 1350965 4194304 1 8388608 58723555422945 140737488355328 3142109551353 63507791620341760 79333468051958891925 590295810358705651712 

noncomputable abbrev qz608 := (@HPow.hPow Real Real Real qz7 qz36 qz9)

noncomputable def Ns276p279 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz608 1 1 0 1 1350965 4194304 1 8388608 1350965 4194304 1 8388608 

noncomputable def Ns276p280 := @Enclosure.Real.IsNear.sqrt_image qz36 389693641911 4194304000 145943 4194304000 80857726 80857757 8388608 (@Enclosure.Real.IsNear.of_eq qz36 (@HMul.hMul Real Real Real qz5 qz35 qz3) Bool.false 389693641911 4194304000 145943 4194304000 (BSN.t_div_two_pi_mk qz35 583772 1000 qz38) (@Enclosure.Real.IsNear.mulLit_ff qz35 qz3 583772 1000 0 1 2670177 16777216 1 16777216 389693641911 4194304000 145943 4194304000 (Enclosure.Real.IsNear.const Bool.false 583772 1000) RS277to288.d44 rfl)) 

noncomputable abbrev qz744 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 583772 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz609 := qz744

noncomputable abbrev qz394 := qz609

noncomputable abbrev qz44 := qz394

noncomputable def Ns276p281 := @Enclosure.Real.IsNear.sqrt_image qz44 161715483 16777216 31 16777216 26043881 26043887 8388608 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 161715483 16777216 31 16777216 161715483 16777216 31 16777216 (Ns276p280 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns276p282 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz44) 6510971 2097152 3 8388608 2701929 2701931 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz44) Bool.false 52087768 16777216 6 16777216 6510971 2097152 3 8388608 (Ns276p281 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns276p283 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 5403860 16777216 2 16777216 1350965 4194304 1 8388608 (Ns276p282 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz395 := (@HMul.hMul Real Real Real qz584 qz582 qz603)

noncomputable abbrev qz45 := (Real.cos qz395)

noncomputable abbrev qz610 := (@HMul.hMul Real Real Real qz732 qz743 qz743)

noncomputable abbrev qz396 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz610 qz603) qz599)

noncomputable abbrev qz46 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz396))

noncomputable def Ns276p284 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz37) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz45) qz46) Bool.false 58723555422945 

noncomputable def Ns276p285 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz45) qz46 26121265 16777216 485 

noncomputable abbrev qz47 := (@Neg.neg Real Real.instNeg (Real.cos qz395))

noncomputable def Ns276p286 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz45) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz47)) Bool.true 26121265 16777216 485 16777216 (BSN.inv_eq_neg_inv_neg qz45) 

noncomputable def Ns276p287 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz47) Bool.false 26121265 16777216 485 16777216 26121265 16777216 

noncomputable def Ns276p288 := @Enclosure.Real.IsNear.recentre' qz45 Bool.true 10775702 16777216 720727216 60565749760000 5387851 8388608 45045451 3785359360000 

noncomputable abbrev qz48 := qz395

noncomputable def Ns276p289 := @Enclosure.Real.IsNear.cos_image qz48 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 67359133) qz376) Bool.false 67359133 16777216 195 16777216 Bool.true 10775702 16777216 1 

noncomputable def Ns276p290 := nat_lit 167313667554490827582244613 

noncomputable def Ns276p291 := nat_lit 14411518807585587200000000000000 

noncomputable def Ns276p292 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz37 884279719003555 140737488355328 1 500000000000000 10720539 16777216 31 16777216 9479955214486652516145 2361183241434822606848 Ns276p290 

noncomputable def Ns276p293 := @Enclosure.Real.IsNear.subLit_ff_p qz44 qz1 161715483 16777216 31 16777216 9 1 0 1 10720539 10720539 16777216 31 

noncomputable def Ns276p294 := @Ns276p293 16777216 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 161715483 16777216 31 16777216 161715483 16777216 31 16777216 (Ns276p280 rfl rfl rfl rfl rfl rfl) rfl) qz377 

noncomputable def Ns276p295 := @Enclosure.Real.IsNear.recentre' qz48 Bool.false 9479955214486652516145 2361183241434822606848 Ns276p290 Ns276p291 67359133 16777216 195 16777216 (@Ns276p292 Ns276p291 RS277to288.d43 (Ns276p294 rfl rfl) rfl) 

noncomputable def Ns276p296 := nat_lit 2111569173648912905404416 

noncomputable def Ns276p297 := nat_lit 1899157902418481440248803210544489058332526691850679076999519875428300817455451451420641 

noncomputable def Ns276p298 := nat_lit 657361252089437519767803970297949965385496781427062506745919446962563208575608942561 

noncomputable def Ns276p299 := nat_lit 5696158984751265445706874023692871275066809081989183105985067787390977325949203136376801 

noncomputable def Ns276p300 := BSN.cos_dyadic_bound_f 30007202747 34359738368 3 2 16777216 7227051 Ns276p297 Ns276p173 Ns276p298 Ns276p299 Ns276p176 Ns276p298 10775702 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 30007202747) qz378 0 2 Ns276p297 Ns276p173 Ns276p298 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 30007202747) qz379 0 2 Ns276p299 Ns276p176 Ns276p298 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p301 := @Ns276p289 3610000 (Ns276p295 rfl) (Enclosure.sfrac_false_div 67359133 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 67359133) qz376) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns276p296) qz380) 226375608064910080 72057594037927936 Bool.false 10775702 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 67359133 16777216 226375608064910080 72057594037927936 0 Ns276p296 Ns276p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 10775702 16777216 Ns276p296 Ns276p92 30007202747 34359738368 7227051 7220000 (Ns276p300 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p302 := @Enclosure.Real.IsNear.inv_image qz47 5387851 8388608 45045451 3785359360000 13060390 13060875 8388608 (@Enclosure.Real.IsNear.neg qz45 Bool.true 5387851 8388608 45045451 3785359360000 (Ns276p288 (Ns276p301 rfl rfl) rfl)) 

noncomputable def Ns276p303 := Ns276p286 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz47) Bool.false 26121265 16777216 485 16777216 (@Ns276p287 485 16777216 (Ns276p302 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p304 := @Enclosure.Real.IsNear.recentre' qz46 Bool.true 2248113 8388608 

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz346 qz343 qz396)

noncomputable def Ns276p305 := @Enclosure.Real.IsNear.cos_image qz49 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 30905453)) qz376) Bool.true 30905453 16777216 

noncomputable def Ns276p306 := nat_lit 72973440040625817322019449045 

noncomputable def Ns276p307 := nat_lit 31972240614886818737273028438999373 

noncomputable def Ns276p308 := @Enclosure.Real.IsNear.recentre' qz49 Bool.true Ns276p306 Ns276p184 Ns276p307 

noncomputable abbrev qz50 := qz396

noncomputable def Ns276p309 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz50 884279719003555 140737488355328 1 500000000000000 82523028033319 

noncomputable abbrev qz397 := (@HSub.hSub Real Real Real qz588 qz610 qz603)

noncomputable abbrev qz51 := qz397

noncomputable def Ns276p310 := @Enclosure.Real.IsNear.subLit_tf qz51 qz31 64930841988903 281474976710656 1184768075 281474976710656 1 16 

noncomputable abbrev qz398 := qz610

noncomputable abbrev qz52 := qz398

noncomputable def Ns276p311 := @Enclosure.Real.IsNear.subLit_ff_n qz52 qz37 114929956450521 281474976710656 664674379 281474976710656 10720539 16777216 31 16777216 

noncomputable def Ns276p312 := @Enclosure.Real.IsNear.mulLit_ff qz37 qz37 10720539 16777216 31 16777216 10720539 16777216 31 16777216 114929956450521 281474976710656 

noncomputable def Ns276p313 := nat_lit 115078650649548391596132697930042932889942729600814363400996172167476200230979789321951772547121 

noncomputable def Ns276p314 := nat_lit 759313924766504975572941360601672859670615071589596843439168048320794064755984591612680241 

noncomputable def Ns276p315 := nat_lit 694971597365359536051743910904971678180558496074371281709060515093097954742347091725116227065905 

noncomputable def Ns276p316 := BSN.cos_dyadic_bound_t 30905453 16777216 4 3 8388608 3610000 Ns276p313 Ns276p193 Ns276p314 Ns276p315 Ns276p196 Ns276p314 2248113 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 30905453) qz600 0 3 Ns276p313 Ns276p193 Ns276p314 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 30905453) (BSN.cosOddQ 16777216) 0 3 Ns276p315 Ns276p196 Ns276p314 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p317 := @Ns276p304 1623227216 60565749760000 2248113 8388608 101451701 3785359360000 (@Ns276p305 445 16777216 Bool.true 2248113 8388608 1 3610000 (@Ns276p308 Ns276p187 30905453 16777216 445 16777216 (@Ns276p309 281474976710656 1184768075 281474976710656 Ns276p306 Ns276p184 Ns276p307 Ns276p187 RS277to288.d43 (@Ns276p310 0 1 1320368448533104 82523028033319 281474976710656 1184768075 281474976710656 (@Ns276p311 1089358761109695234048 64930841988903 281474976710656 1184768075 281474976710656 (@Ns276p312 664674379 281474976710656 (Ns276p294 rfl rfl) (Ns276p294 rfl rfl) rfl) (Ns276p294 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 30905453 16777216) (BSN.cos_neg_of_bound 30905453 16777216 Bool.true 2248113 8388608 1 3610000 (Ns276p316 rfl rfl)) rfl rfl) 

noncomputable def Ns276p318 := @Ns276p278 34065048826325466297 Ns276p201 (Ns276p279 qz33 (@Enclosure.Real.IsNear.of_eq qz608 (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 1350965 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz36 (BSN.t_div_two_pi_nonneg qz35 583772 1000 qz38)) Ns276p283) rfl) (@Ns276p284 140737488355328 3142109551353 63507791620341760 (BSN.correction_mk qz37 (BSN.cos_two_pi_p_ne_zero_mk qz35 583772 1000 9 qz38 rfl rfl (@BSN.floor_sqrt_eq_dec qz35 583772 1000 9 qz38 rfl rfl rfl))) (@Ns276p285 16777216 2248113 8388608 101451701 3785359360000 58723555422945 140737488355328 3142109551353 63507791620341760 Ns276p303 (Ns276p317 rfl) rfl)) 

noncomputable def Ns276p319 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (hardyZApproximantRS₀ qz35) Bool.false 881381320093347054997 590295810358705651712 2925066738967523065017 Ns276p201 (@Eq.refl Real (hardyZApproximantRS₀ qz35)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) (@HMul.hMul Real Real Real qz5 qz604 (Zeta.RiemannSiegel.correction qz37))) Bool.false 881381320093347054997 590295810358705651712 2925066738967523065017 Ns276p201 (BSN.hardyZApproximantRS₀_eq qz35 9 (@BSN.floor_sqrt_eq_dec qz35 583772 1000 9 qz38 rfl rfl rfl)) (@Ns276p203 881381320093347054997 590295810358705651712 2925066738967523065017 Ns276p201 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 9)) Bool.false 22795571 16777216 22761 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) (Ns276p277 (Ns276p276 rfl) rfl rfl)) (Ns276p318 rfl) rfl rfl)) 

theorem RS277to288.d47 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz35) Bool.false 881381320093347054997 590295810358705651712 2925066738967523065017 Ns276p201 := Ns276p319 

noncomputable abbrev qz611 := (@HMul.hMul Real Real Real qz732 (Real.sqrt qz740) qz734)

noncomputable abbrev qz399 := qz611

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv qz399)

noncomputable abbrev qz400 := (@HMul.hMul Real Real Real qz584 (@HMul.hMul Real Real Real qz584 qz611 qz611) qz611)

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz346 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz400))

noncomputable abbrev qz401 := (@HMul.hMul Real Real Real qz584 qz597 qz597)

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz346 qz401 qz373))

noncomputable abbrev qz612 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz53)

noncomputable def Ns276p320 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz362 (@HAdd.hAdd Real Real Real qz362 qz612 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55)) Bool.false 

noncomputable def Ns276p321 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz362 qz612 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55) 11667001 536870912 

noncomputable def Ns276p322 := @Enclosure.Real.IsNear.addLit_ff qz612 qz54 1458375 67108864 25 67108864 

noncomputable def Ns276p323 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz53 25 4 0 1 58335 16777216 1 16777216 1458375 

noncomputable def Ns276p324 := @Enclosure.Real.IsNear.recentre' qz53 Bool.false 58335 16777216 1 16777216 58335 16777216 1 16777216 

noncomputable def Ns276p325 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz8 26028401 8388608 3 8388608 311014206429 3355443200 116477 3355443200 8095202481630790029 28147497671065600 792950606399 

noncomputable def Ns276p326 := @Enclosure.Real.IsNear.sqrt_image qz8 311014206429 3355443200 116477 3355443200 80761613 80761644 8388608 qz21 

noncomputable def Ns276p327 := @Enclosure.Real.IsNear.sqrt_image qz22 161523257 16777216 31 16777216 26028398 26028404 8388608 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 161523257 16777216 31 16777216 161523257 16777216 31 16777216 (Ns276p326 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz402 := (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 52056802 16777216 6 16777216 26028401 8388608 3 8388608 (Ns276p327 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns276p328 := @Ns276p325 5629499534213120 qz402 

noncomputable def Ns276p329 := Ns276p328 qz21 

noncomputable abbrev qz56 := qz399

noncomputable def Ns276p330 := @Enclosure.Real.IsNear.inv_image qz56 8095202481630790029 28147497671065600 792950606399 5629499534213120 29167 29168 8388608 (Ns276p329 rfl) rfl rfl 

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv qz400)

noncomputable def Ns276p331 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz57 1 32 0 1 1 

noncomputable def Ns276p332 := @Enclosure.Real.IsNear.recentre' qz57 Bool.false 1 16777216 1 16777216 

noncomputable def Ns276p333 := nat_lit 530497263642202663703804827812482825575413114251183194389 

noncomputable def Ns276p334 := nat_lit 22300745198530623141535718272648361505980416000000 

noncomputable def Ns276p335 := nat_lit 155891715078139205488113524360646857014588261847087 

noncomputable def Ns276p336 := nat_lit 4460149039706124628307143654529672301196083200000 

noncomputable abbrev qz58 := qz400

noncomputable def Ns276p337 := @Enclosure.Real.IsNear.inv_image qz58 Ns276p333 Ns276p334 Ns276p335 Ns276p336 0 1 

noncomputable def Ns276p338 := nat_lit 65532303218601301376899619958685820841 

noncomputable def Ns276p339 := nat_lit 792281625142643375935439503360000 

noncomputable def Ns276p340 := nat_lit 12838194577316970166559084327147 

noncomputable def Ns276p341 := nat_lit 158456325028528675187087900672000 

noncomputable abbrev qz403 := (@HMul.hMul Real Real Real qz584 qz611 qz611)

noncomputable abbrev qz59 := qz403

noncomputable def Ns276p342 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz56 Ns276p338 Ns276p339 Ns276p340 Ns276p341 8095202481630790029 28147497671065600 792950606399 

noncomputable def Ns276p343 := @Enclosure.Real.IsNear.mulLit_ff qz56 qz56 8095202481630790029 28147497671065600 792950606399 5629499534213120 8095202481630790029 28147497671065600 792950606399 5629499534213120 Ns276p338 

noncomputable def Ns276p344 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz55 13 10 0 1 280813 8388608 1 

noncomputable def Ns276p345 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 561626 16777216 2 16777216 280813 8388608 

noncomputable abbrev qz60 := qz401

noncomputable def Ns276p346 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz23 677477658616801 70368744177664 156170415 70368744177664 26028401 8388608 3 8388608 17633660167019201765201 

noncomputable def Ns276p347 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz23 26028401 8388608 3 8388608 26028401 8388608 3 8388608 677477658616801 70368744177664 156170415 

noncomputable def Ns276p348 := @Ns276p347 70368744177664 qz402 

noncomputable def Ns276p349 := Ns276p348 qz402 

noncomputable def Ns276p350 := @Ns276p346 590295810358705651712 6097299630318063 590295810358705651712 (Ns276p349 rfl) qz402 

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz346 qz401 qz373)

noncomputable def Ns276p351 := @Enclosure.Real.IsNear.inv_image qz61 17633660167019201765201 590295810358705651712 6097299630318063 590295810358705651712 280812 280814 8388608 (Ns276p350 rfl) 

noncomputable def Ns276p352 := @Ns276p321 201 536870912 3650569 83886080 13 83886080 2938583287595008 175153213 2684354560 1421 2684354560 (@Ns276p322 1 536870912 1 536870912 782959183396864 11667001 536870912 201 536870912 (@Ns276p323 67108864 25 67108864 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns276p324 (Ns276p330 rfl rfl rfl rfl) rfl) rfl) (@Ns276p331 16777216 1 16777216 1 536870912 1 536870912 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns276p332 1 16777216 1 16777216 (@Ns276p337 8388608 (@Ns276p342 5629499534213120 Ns276p333 Ns276p334 Ns276p335 Ns276p336 (@Ns276p343 Ns276p339 Ns276p340 Ns276p341 (Ns276p329 rfl) (Ns276p329 rfl) rfl) (Ns276p329 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns276p344 8388608 3650569 83886080 13 83886080 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns276p345 1 8388608 (Ns276p351 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS277to288.d48 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 := @Ns276p320 175153213 2684354560 1421 2684354560 (BSN.hardyZErrorBoundRS₀_mk qz4 582385 1000 qz11 rfl rfl) (Ns276p352 rfl rfl) 

noncomputable def Ns276p353 := nat_lit 27233387497173138272375799808 

noncomputable abbrev qz745 := (Enclosure.sfrac Bool.false 585158 1000)

noncomputable abbrev qz613 := qz745

noncomputable abbrev qz404 := qz613

noncomputable abbrev qz62 := qz404

noncomputable abbrev qz746 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 585158 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz614 := qz746

noncomputable abbrev qz405 := qz614

noncomputable abbrev qz63 := qz405

noncomputable abbrev qz747 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 585158 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz615 := qz747

noncomputable abbrev qz406 := qz615

noncomputable abbrev qz64 := qz406

noncomputable abbrev qz616 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz63 qz9))

noncomputable def Ns276p354 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (@HMul.hMul Real Real Real qz5 qz616 (Zeta.RiemannSiegel.correction qz64)) 101415445 67108864 11409 8388608 40220747104417284933 295147905179352825856 37647783437221584269 Ns276p201 Ns276p353 

noncomputable def Ns276p355 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 585158 1000 116 160 134217728 67108864 2251799813685248 Bool.false 138725153303 1861 

noncomputable def Ns276p356 := Ns276p355 279097919 38 47453128 8 294906479 38 44739240 8 Bool.true 157538376 74701 Bool.true 135095943 Bool.true 109137874 7074237752028440 1 Bool.false 71777608 Bool.false Bool.false 92237159 Bool.false Bool.true 101415445 

noncomputable def Ns276p357 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 585158 1000 9 66 134217728 67108864 2251799813685248 Bool.false 138725153303 1861 

noncomputable def Ns276p358 := Ns276p357 240485871 38 54794152 8 261175631 38 50729528 8 Bool.true 112347524 55736 Bool.true 99619572 Bool.true 189161448 7074237752028440 1 Bool.false 90721565 Bool.true Bool.false 21573277 Bool.true Bool.true 157538376 

noncomputable def Ns276p359 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 585158 1000 141 58 134217728 67108864 2251799813685248 Bool.false 138725153303 1861 

noncomputable def Ns276p360 := Ns276p359 186065264 38 67108856 8 216015088 38 60023992 8 Bool.true 13943451 32891 Bool.false 120726858 Bool.false 94131019 7074237752028440 1 Bool.false 105093392 Bool.true Bool.false 102540226 Bool.true Bool.true 112347524 

noncomputable def Ns276p361 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 585158 1000 399 248 134217728 67108864 2251799813685248 Bool.false 138725153303 1861 

noncomputable def Ns276p362 := Ns276p361 93032624 38 94906264 8 147453232 38 77490640 16 Bool.true 134217648 1910 Bool.false 165712169 Bool.false 156193867 7074237752028440 1 Bool.false 126706021 Bool.false Bool.false 53138475 Bool.false Bool.true 13943451 

noncomputable def Ns276p363 := nat_lit 3284864698801325201722212127624359827534480895316014619 

noncomputable def Ns276p364 := nat_lit 3178133641673045987850963204415874246436578131968000 

noncomputable def Ns276p365 := nat_lit 32931216569067317406394018288640000 

noncomputable def Ns276p366 := nat_lit 115619828345117493439864600237920030720 

noncomputable abbrev qz617 := (@Eq.refl Real qz745)

noncomputable abbrev qz407 := qz617

noncomputable abbrev qz65 := qz407

noncomputable def Ns276p367 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz62 585158 1000 1369640539856 16000000 1170316 4000 2000 Ns276p365 Ns276p366 qz65 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns276p368 := nat_lit 67274029031451140131270904373746889267906168736071979397120 

noncomputable abbrev qz618 := (@HSub.hSub Real Real Real qz736 qz737 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz738 (@Nat.cast Real Real.instNatCast 1170316))))

noncomputable abbrev qz408 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 585158 4000) (Real.log (Enclosure.sfrac Bool.false 1369640539856 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz618))

noncomputable abbrev qz619 := (Enclosure.sfrac Bool.false 585158 2000)

noncomputable abbrev qz66 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz408 qz619) (@HMul.hMul Real Real Real qz346 qz619 (Real.log Real.pi)))

noncomputable def Ns276p369 := @Enclosure.Real.IsNear.addLit_ft_p qz66 (Enclosure.sfrac Bool.true Ns276p365 Ns276p366) 581855625743271462871 562949953421312000 5121404164268205023 369664000000000000000000 Ns276p365 Ns276p366 0 1 Ns276p368 

noncomputable def Ns276p370 := nat_lit 780953401112802070337819770880 

noncomputable abbrev qz67 := (@HSub.hSub Real Real Real qz350 qz408 qz619)

noncomputable def Ns276p371 := @Enclosure.Real.IsNear.subLit_ff_p qz67 (@HMul.hMul Real Real Real qz5 qz619 (Real.log Real.pi)) 30816041332784465263 22517998136852480 1853619595013277 361000000000000000000 11238182042619 33554432000 292579 33554432000 Ns276p370 581855625743271462871 562949953421312000 

noncomputable def Ns276p372 := nat_lit 1540802066639223263150000 

noncomputable abbrev qz68 := qz408

noncomputable def Ns276p373 := @Enclosure.Real.IsNear.subLit_ff_p qz68 qz619 935108367741665675223 562949953421312000 1853619595013277 361000000000000000000 585158 2000 0 1 Ns276p372 30816041332784465263 22517998136852480 1853619595013277 361000000000000000000 

noncomputable def Ns276p374 := nat_lit 2105676848256199138553911053914210304 

noncomputable def Ns276p375 := nat_lit 27460677829564172865634304 

noncomputable def Ns276p376 := nat_lit 1105078951032554531558253081309153892298079912268843804827350134711759375605608100389182337511975813120 

noncomputable def Ns276p377 := nat_lit 6562867040149957834607906101810812390429828221976111282865400155349569775704868380397450902061973504 

noncomputable def Ns276p378 := nat_lit 11855722833951897238616632117326196200326245758136497777631151577477151877817196990554628423680 

noncomputable def Ns276p379 := BSN.log_dyadic_bound 321064539856 2418216539856 5 4 Ns276p376 67108864 28880000 Ns276p377 Ns276p378 17925802 2739281079712 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 321064539856) (BSN.artanhQ 2418216539856) 0 4 Ns276p377 Ns276p376 Ns276p378 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz409 := (Real.log (Enclosure.sfrac Bool.false 1369640539856 16000000))

noncomputable def Ns276p380 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 585158 4000) qz409 585158 4000 0 1 3196843647114487 281474976710656 781250361 22562500000000000 935329317429109491973 562949953421312000 228577449371019 45125000000000000000 (Enclosure.Real.IsNear.const Bool.false 585158 4000) (BSN.isNear_log_sfrac 1369640539856 16000000 3196843647114487 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1369640539856) qz353)) Bool.false Ns276p375 Ns276p92 1000000462080000 28880000000000000000000 3196843647114487 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1369640539856 16000000 16 2739281079712 2097152000000 17925802 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns276p379 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p381 := BSN.arctan_dyadic_bound_f 1000 1170316 1 0 8388608 3610000 0 1 1 0 1 1 7167 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1170316) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1170316) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz410 := (@Nat.cast Real Real.instNatCast 1170316)

noncomputable def Ns276p382 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 qz410)) 884279719003555 562949953421312 1 2000000000000000 7167 8388608 1 3610000 7413841262754802958336 883798749775267 562949953421312 200000000361 722000000000000000 qz17 (Ns276p381 rfl) rfl rfl 

noncomputable abbrev qz411 := (@HMul.hMul Real Real Real qz584 qz589 qz618)

noncomputable abbrev qz69 := qz411

noncomputable abbrev qz412 := qz618

noncomputable abbrev qz70 := qz412

noncomputable def Ns276p383 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 585158 4000) qz409) qz69 935329317429109491973 562949953421312000 228577449371019 45125000000000000000 883798749775267 2251799813685248 200000000361 2888000000000000000 Ns276p374 935108367741665675223 562949953421312000 1853619595013277 361000000000000000000 (Ns276p380 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz70 1 4 0 1 883798749775267 562949953421312 200000000361 722000000000000000 883798749775267 2251799813685248 200000000361 2888000000000000000 qz361 Ns276p382 rfl) 

noncomputable def Ns276p384 := @Ns276p369 Ns276p363 Ns276p364 5121404164268205023 369664000000000000000000 (@Ns276p371 5121404164268205023 369664000000000000000000 (Ns276p373 (Ns276p383 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 585158 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz619 (Real.log Real.pi) 585158 2000 0 1 38410761 33554432 1 33554432 11238182042619 33554432000 292579 33554432000 (Enclosure.Real.IsNear.const Bool.false 585158 2000) RS277to288.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns276p365 Ns276p366) 

noncomputable def Ns276p385 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns276p363 Ns276p364 5121404164268205023 369664000000000000000000 8670322081 8388608 117 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz362 qz66 (Enclosure.sfrac Bool.true Ns276p365 Ns276p366)) Bool.false Ns276p363 Ns276p364 5121404164268205023 369664000000000000000000 Ns276p367 (Ns276p384 rfl rfl)) 

noncomputable def Ns276p386 := nat_lit 1897709792023894820913152 

noncomputable def Ns276p387 := nat_lit 854848743685531504067901267894376969896202339613352282239555132024975023376186449528682936634212396343733793375985082062000436581236736 

noncomputable def Ns276p388 := nat_lit 606121827125442165253040649275065662733775777865909179213231642425745435481716196621294288670386789929746635131147828708335681536 

noncomputable def Ns276p389 := nat_lit 4268946575657029746003787586940774576085776836656266513052710835388599342925545083621740052205576837657224239163553697430874309206736896 

noncomputable def Ns276p390 := BSN.sin_dyadic_bound_f 53936156292 34359738368 4 3 16777216 7227051 Ns276p387 Ns276p106 Ns276p388 Ns276p389 Ns276p109 Ns276p388 16777206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53936156292) qz363 0 3 Ns276p387 Ns276p106 Ns276p388 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53936156292) qz364 0 3 Ns276p389 Ns276p109 Ns276p388 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p391 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz62) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8670322081) qz365) Bool.false 8670322081 8388608 117 8388608 Bool.true 16777206 16777216 1 3610000 (Ns276p385 rfl) (Enclosure.sfrac_false_div 8670322081 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8670322081) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns276p386) qz366) 226375608064910080 72057594037927936 Bool.false 16777206 16777216 164 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q1 8670322081 8388608 226375608064910080 72057594037927936 164 Ns276p386 Ns276p104 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777206 16777216 Ns276p386 Ns276p104 53936156292 34359738368 7227051 7220000 (Ns276p390 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p392 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns276p363 Ns276p364 5121404164268205023 369664000000000000000000 138725153303 134217728 1861 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz362 qz66 (Enclosure.sfrac Bool.true Ns276p365 Ns276p366)) Bool.false Ns276p363 Ns276p364 5121404164268205023 369664000000000000000000 Ns276p367 (Ns276p384 rfl rfl)) 

noncomputable def Ns276p393 := Ns276p362 32891 BSN.abs_quadSignPos (BSN.cos_quad_nat3 399 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 126706021 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 248 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 53138475 134217728) qz65 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) Bool.true 8388603 8388608 26922413 1892679680000 134217648 134217728 1910 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 8388603 8388608 26922413 1892679680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz62) qz62) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 16777206 16777216 430758608 30282874880000 8388603 8388608 26922413 1892679680000 (Ns276p391 rfl rfl) rfl)) rfl) (Ns276p392 rfl) RS277to288.d7 

noncomputable def Ns276p394 := nat_lit 740580915738547738689150828882045304014641949271841912854717468313665 

noncomputable def Ns276p395 := nat_lit 568637130436148766642482885505848570831870539501503151751605323841 

noncomputable def Ns276p396 := nat_lit 1938696033485014122373211960495490136637953505314678766659519341725761 

noncomputable def Ns276p397 := BSN.sin_dyadic_bound_f 165712169 134217728 3 2 134217728 67108864 Ns276p394 Ns276p137 Ns276p395 Ns276p396 Ns276p140 Ns276p395 126706021 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 165712169) qz367 0 2 Ns276p394 Ns276p137 Ns276p395 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 165712169) qz368 0 2 Ns276p396 Ns276p140 Ns276p395 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p398 := nat_lit 1252375700101790788817076014452175467662728684706647664652955605974587333592563622959871017729829030756241 

noncomputable def Ns276p399 := nat_lit 210847145615181146082588739037464407620839287451220596277272041667828295915284438161495933892329361 

noncomputable def Ns276p400 := nat_lit 7592221189149996141345057148765671404436357171564022775215310256808229727662072667100076227910088113422225 

noncomputable def Ns276p401 := BSN.cos_dyadic_bound_f 156193867 134217728 4 3 134217728 67108864 Ns276p398 Ns276p116 Ns276p399 Ns276p400 Ns276p119 Ns276p399 53138475 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 156193867) qz369 0 3 Ns276p398 Ns276p116 Ns276p399 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 156193867) qz370 0 3 Ns276p400 Ns276p119 Ns276p399 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p402 := nat_lit 208511931463417309377773285338992196911831116603254473061486663491840 

noncomputable def Ns276p403 := nat_lit 45126451440331971014231104991625257729623678064396591286583746816 

noncomputable def Ns276p404 := nat_lit 546029615768522891845859373146421693875614486101181263537048697364736 

noncomputable def Ns276p405 := BSN.sin_dyadic_bound_f 120726858 134217728 3 2 134217728 67108864 Ns276p402 Ns276p137 Ns276p403 Ns276p404 Ns276p140 Ns276p403 105093392 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 120726858) qz367 0 2 Ns276p402 Ns276p137 Ns276p403 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 120726858) qz368 0 2 Ns276p404 Ns276p140 Ns276p403 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p406 := nat_lit 42809720321433967493894418227023279834169473275448894143893605050721 

noncomputable def Ns276p407 := nat_lit 6163992204202990407225055519353527254915255803478972537842035041 

noncomputable def Ns276p408 := nat_lit 128416832979893496500868804570031132447998589314739724486605131082081 

noncomputable def Ns276p409 := BSN.cos_dyadic_bound_f 94131019 134217728 3 2 134217728 67108864 Ns276p406 Ns276p131 Ns276p407 Ns276p408 Ns276p134 Ns276p407 102540226 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 94131019) qz369 0 2 Ns276p406 Ns276p131 Ns276p407 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 94131019) qz370 0 2 Ns276p408 Ns276p134 Ns276p407 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p410 := Ns276p360 55736 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 141 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 105093392 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 58 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 102540226 134217728) qz65 rfl rfl (Ns276p393 RS277to288.d9 RS277to288.d11 RS277to288.d13 RS277to288.d17 (Ns276p397 rfl rfl) (Ns276p401 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns276p392 rfl) RS277to288.d19 RS277to288.d21 RS277to288.d23 RS277to288.d25 RS277to288.d17 (Ns276p405 rfl rfl) (Ns276p409 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns276p411 := nat_lit 96659287140091551196679260227165427337683572282223531577004957696000 

noncomputable def Ns276p412 := nat_lit 9699679226875631736012383853640491669285189601247091687371636736 

noncomputable def Ns276p413 := nat_lit 253139571600539121158968328163955939374087656146469135029423906553856 

noncomputable def Ns276p414 := BSN.sin_dyadic_bound_f 99619572 134217728 3 2 134217728 67108864 Ns276p411 Ns276p137 Ns276p412 Ns276p413 Ns276p140 Ns276p412 90721565 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 99619572) qz367 0 2 Ns276p411 Ns276p137 Ns276p412 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 99619572) qz368 0 2 Ns276p413 Ns276p140 Ns276p412 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p415 := nat_lit 2697455985404473878929508145228826873099682714544447815693678822907596112937399829309015572672656730750976 

noncomputable def Ns276p416 := nat_lit 2098899082553739290546584678458948254765446647796162725782173046207004275308421770648565459919568896 

noncomputable def Ns276p417 := nat_lit 16338994792112835953131922006892882554401915017346571854832352361865839095095726991532488575112984416747520 

noncomputable def Ns276p418 := BSN.cos_dyadic_bound_f 189161448 134217728 4 3 134217728 67108864 Ns276p415 Ns276p116 Ns276p416 Ns276p417 Ns276p119 Ns276p416 21573277 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 189161448) qz369 0 3 Ns276p415 Ns276p116 Ns276p416 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 189161448) qz370 0 3 Ns276p417 Ns276p119 Ns276p416 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p419 := Ns276p358 74701 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 9 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 90721565 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 21573277 134217728) qz65 rfl rfl (Ns276p410 rfl rfl) (Ns276p392 rfl) RS277to288.d27 RS277to288.d29 RS277to288.d31 RS277to288.d33 RS277to288.d17 (Ns276p414 rfl rfl) (Ns276p418 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p420 := nat_lit 181711871853148125395777803343214292121902407263256814524569740518081 

noncomputable def Ns276p421 := nat_lit 110952848674621153756840498814750530513471910539631422143896888001 

noncomputable def Ns276p422 := nat_lit 544913709862095133879819729032013375304680277968691180729421427778241 

noncomputable def Ns276p423 := BSN.cos_dyadic_bound_f 135095943 134217728 3 2 134217728 67108864 Ns276p420 Ns276p131 Ns276p421 Ns276p422 Ns276p134 Ns276p421 71777608 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 135095943) qz369 0 2 Ns276p420 Ns276p131 Ns276p421 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 135095943) qz370 0 2 Ns276p422 Ns276p134 Ns276p421 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p424 := nat_lit 77368427871747578447016795611596032659593853882983783106543000371456 

noncomputable def Ns276p425 := nat_lit 20128152582450590464203527261411607005717396840789213061141381376 

noncomputable def Ns276p426 := nat_lit 232065027310077834160121979780265274764770126855269770893506718351616 

noncomputable def Ns276p427 := BSN.cos_dyadic_bound_f 109137874 134217728 3 2 134217728 67108864 Ns276p424 Ns276p131 Ns276p425 Ns276p426 Ns276p134 Ns276p425 92237159 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 109137874) qz369 0 2 Ns276p424 Ns276p131 Ns276p425 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 109137874) qz370 0 2 Ns276p426 Ns276p134 Ns276p425 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p428 := Ns276p356 91272 BSN.abs_quadSignPos (BSN.cos_quad_nat0 116 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 71777608 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 92237159 134217728) qz65 rfl rfl (Ns276p419 rfl) (Ns276p392 rfl) RS277to288.d35 RS277to288.d37 RS277to288.d39 RS277to288.d41 RS277to288.d17 (Ns276p423 rfl rfl) (Ns276p427 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p429 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) 101415445 134217728 91272 134217728 101415445 134217728 91272 134217728 27223501224017920 101415445 67108864 11409 8388608 (Ns276p428 rfl) 

noncomputable def Ns276p430 := @Enclosure.Real.IsNear.mulLit_tf qz616 (Zeta.RiemannSiegel.correction qz64) 5400657 16777216 1 16777216 7447380402869 17592186044416 13922012225441 254031166481367040 40220747104417284933 295147905179352825856 

noncomputable abbrev qz620 := (@HPow.hPow Real Real Real qz7 qz63 qz9)

noncomputable def Ns276p431 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz620 1 1 0 1 5400657 16777216 1 16777216 5400657 16777216 1 16777216 

noncomputable def Ns276p432 := @Enclosure.Real.IsNear.sqrt_image qz63 781237716483 8388608000 292579 8388608000 80953656 80953687 8388608 (@Enclosure.Real.IsNear.of_eq qz63 (@HMul.hMul Real Real Real qz5 qz62 qz3) Bool.false 781237716483 8388608000 292579 8388608000 (BSN.t_div_two_pi_mk qz62 585158 1000 qz65) (@Enclosure.Real.IsNear.mulLit_ff qz62 qz3 585158 1000 0 1 2670177 16777216 1 16777216 781237716483 8388608000 292579 8388608000 (Enclosure.Real.IsNear.const Bool.false 585158 1000) RS277to288.d44 rfl)) 

noncomputable abbrev qz748 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 585158 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz621 := qz748

noncomputable abbrev qz413 := qz621

noncomputable abbrev qz71 := qz413

noncomputable def Ns276p433 := @Enclosure.Real.IsNear.sqrt_image qz71 161907343 16777216 31 16777216 26059326 26059332 8388608 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 161907343 16777216 31 16777216 161907343 16777216 31 16777216 (Ns276p432 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns276p434 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz71) 26059329 8388608 3 8388608 2700328 2700329 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz71) Bool.false 52118658 16777216 6 16777216 26059329 8388608 3 8388608 (Ns276p433 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns276p435 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 5400657 16777216 1 16777216 5400657 16777216 1 16777216 (Ns276p434 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz414 := (@HMul.hMul Real Real Real qz584 qz582 qz615)

noncomputable abbrev qz72 := (Real.cos qz414)

noncomputable abbrev qz622 := (@HMul.hMul Real Real Real qz732 qz747 qz747)

noncomputable abbrev qz415 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz622 qz615) qz599)

noncomputable abbrev qz73 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz415))

noncomputable def Ns276p436 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz64) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz72) qz73) Bool.false 7447380402869 

noncomputable def Ns276p437 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz72) qz73 14324833 8388608 73 

noncomputable abbrev qz74 := (@Neg.neg Real Real.instNeg (Real.cos qz414))

noncomputable def Ns276p438 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz72) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz74)) Bool.true 14324833 8388608 73 2097152 (BSN.inv_eq_neg_inv_neg qz72) 

noncomputable def Ns276p439 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz74) Bool.false 28649666 16777216 584 16777216 14324833 8388608 

noncomputable def Ns276p440 := @Enclosure.Real.IsNear.recentre' qz72 Bool.true 9824721 16777216 720727216 60565749760000 9824721 16777216 45045451 3785359360000 

noncomputable abbrev qz75 := qz414

noncomputable def Ns276p441 := @Enclosure.Real.IsNear.cos_image qz75 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 68564625) qz376) Bool.false 68564625 16777216 195 16777216 Bool.true 9824721 16777216 1 

noncomputable def Ns276p442 := nat_lit 167313667554820440552408837 

noncomputable def Ns276p443 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz64 884279719003555 140737488355328 1 500000000000000 10912399 16777216 31 16777216 9649613121374674578445 2361183241434822606848 Ns276p442 

noncomputable def Ns276p444 := @Enclosure.Real.IsNear.subLit_ff_p qz71 qz1 161907343 16777216 31 16777216 9 1 0 1 10912399 10912399 16777216 31 

noncomputable def Ns276p445 := @Ns276p444 16777216 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 161907343 16777216 31 16777216 161907343 16777216 31 16777216 (Ns276p432 rfl rfl rfl rfl rfl rfl) rfl) qz377 

noncomputable def Ns276p446 := @Enclosure.Real.IsNear.recentre' qz75 Bool.false 9649613121374674578445 2361183241434822606848 Ns276p442 Ns276p291 68564625 16777216 195 16777216 (@Ns276p443 Ns276p291 RS277to288.d43 (Ns276p445 rfl rfl) rfl) 

noncomputable def Ns276p447 := nat_lit 2285298879952852552253440 

noncomputable def Ns276p448 := nat_lit 2605960115392680864771983931477153681528864806894494355190621793448405988013427433336801 

noncomputable def Ns276p449 := nat_lit 1237387287211162365664956956034712481236024354808685743291069309273360456275259748321 

noncomputable def Ns276p450 := nat_lit 7815405571603620269584621880519391619624122371973865694085283241726671243127731780513761 

noncomputable def Ns276p451 := BSN.cos_dyadic_bound_f 32476050363 34359738368 3 2 16777216 7227051 Ns276p448 Ns276p173 Ns276p449 Ns276p450 Ns276p176 Ns276p449 9824721 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 32476050363) qz378 0 2 Ns276p448 Ns276p173 Ns276p449 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 32476050363) qz379 0 2 Ns276p450 Ns276p176 Ns276p449 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p452 := @Ns276p441 3610000 (Ns276p446 rfl) (Enclosure.sfrac_false_div 68564625 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 68564625) qz376) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns276p447) qz380) 226375608064910080 72057594037927936 Bool.false 9824721 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 68564625 16777216 226375608064910080 72057594037927936 0 Ns276p447 Ns276p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 9824721 16777216 Ns276p447 Ns276p92 32476050363 34359738368 7227051 7220000 (Ns276p451 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p453 := @Enclosure.Real.IsNear.inv_image qz74 9824721 16777216 45045451 3785359360000 14324541 14325125 8388608 (@Enclosure.Real.IsNear.neg qz72 Bool.true 9824721 16777216 45045451 3785359360000 (Ns276p440 (Ns276p452 rfl rfl) rfl)) 

noncomputable def Ns276p454 := Ns276p438 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz74) Bool.false 14324833 8388608 73 2097152 (@Ns276p439 73 2097152 (Ns276p453 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p455 := @Enclosure.Real.IsNear.recentre' qz73 Bool.true 2079572 8388608 

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz346 qz343 qz415)

noncomputable def Ns276p456 := @Enclosure.Real.IsNear.cos_image qz76 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7639139)) (@Nat.cast Real Real.instNatCast 4194304)) Bool.true 7639139 4194304 

noncomputable def Ns276p457 := nat_lit 72149628409675697057623968445 

noncomputable def Ns276p458 := nat_lit 32293248617413526007303250125085173 

noncomputable def Ns276p459 := @Enclosure.Real.IsNear.recentre' qz76 Bool.true Ns276p457 Ns276p184 Ns276p458 

noncomputable abbrev qz77 := qz415

noncomputable def Ns276p460 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz77 884279719003555 140737488355328 1 500000000000000 81591409210399 

noncomputable abbrev qz416 := (@HSub.hSub Real Real Real qz588 qz622 qz615)

noncomputable abbrev qz78 := qz416

noncomputable def Ns276p461 := @Enclosure.Real.IsNear.subLit_tf qz78 qz31 63999223165983 281474976710656 1196663395 281474976710656 1 16 

noncomputable abbrev qz417 := qz622

noncomputable abbrev qz79 := qz417

noncomputable def Ns276p462 := @Enclosure.Real.IsNear.subLit_ff_n qz79 qz64 119080451935201 281474976710656 676569699 281474976710656 10912399 16777216 31 16777216 

noncomputable def Ns276p463 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz64 10912399 16777216 31 16777216 10912399 16777216 31 16777216 119080451935201 281474976710656 

noncomputable def Ns276p464 := nat_lit 6552703209811136270477398885202422567695260978289722433023315522644615158645038296518001 

noncomputable def Ns276p465 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600 

noncomputable def Ns276p466 := nat_lit 39494166164647239607098964931877232241563988952466231815976669262358890880919063921 

noncomputable def Ns276p467 := nat_lit 39580413242676117645240755833415297833432392766086173800531878098139636896556819033804145 

noncomputable def Ns276p468 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600 

noncomputable def Ns276p469 := BSN.cos_dyadic_bound_t 7639139 4194304 4 3 8388608 3610000 Ns276p464 Ns276p465 Ns276p466 Ns276p467 Ns276p468 Ns276p466 2079572 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 7639139) (BSN.cosEvenQ 4194304) 0 3 Ns276p464 Ns276p465 Ns276p466 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 7639139) (BSN.cosOddQ 4194304) 0 3 Ns276p467 Ns276p468 Ns276p466 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p470 := @Ns276p455 1637667216 60565749760000 519893 2097152 102354201 3785359360000 (@Ns276p456 449 16777216 Bool.true 2079572 8388608 1 3610000 (@Ns276p459 Ns276p187 7639139 4194304 449 16777216 (@Ns276p460 281474976710656 1196663395 281474976710656 Ns276p457 Ns276p184 Ns276p458 Ns276p187 RS277to288.d43 (@Ns276p461 0 1 1305462547366384 81591409210399 281474976710656 1196663395 281474976710656 (@Ns276p462 1073728790887900643328 63999223165983 281474976710656 1196663395 281474976710656 (@Ns276p463 676569699 281474976710656 (Ns276p445 rfl rfl) (Ns276p445 rfl rfl) rfl) (Ns276p445 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7639139 4194304) (BSN.cos_neg_of_bound 7639139 4194304 Bool.true 2079572 8388608 1 3610000 (Ns276p469 rfl rfl)) rfl rfl) 

noncomputable def Ns276p471 := @Ns276p430 37647783437221584269 Ns276p201 (Ns276p431 qz33 (@Enclosure.Real.IsNear.of_eq qz620 (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 5400657 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz63 (BSN.t_div_two_pi_nonneg qz62 585158 1000 qz65)) Ns276p435) rfl) (@Ns276p436 17592186044416 13922012225441 254031166481367040 (BSN.correction_mk qz64 (BSN.cos_two_pi_p_ne_zero_mk qz62 585158 1000 9 qz65 rfl rfl (@BSN.floor_sqrt_eq_dec qz62 585158 1000 9 qz65 rfl rfl rfl))) (@Ns276p437 2097152 519893 2097152 102354201 3785359360000 7447380402869 17592186044416 13922012225441 254031166481367040 Ns276p454 (Ns276p470 rfl) rfl)) 

noncomputable def Ns276p472 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (hardyZApproximantRS₀ qz62) Bool.true 405809096949892316347 295147905179352825856 2935889361823138143629 Ns276p201 (@Eq.refl Real (hardyZApproximantRS₀ qz62)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (@HMul.hMul Real Real Real qz5 qz616 (Zeta.RiemannSiegel.correction qz64))) Bool.true 405809096949892316347 295147905179352825856 2935889361823138143629 Ns276p201 (BSN.hardyZApproximantRS₀_eq qz62 9 (@BSN.floor_sqrt_eq_dec qz62 585158 1000 9 qz65 rfl rfl rfl)) (@Ns276p354 405809096949892316347 295147905179352825856 2935889361823138143629 Ns276p201 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 9)) Bool.true 101415445 67108864 11409 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (Ns276p429 (Ns276p428 rfl) rfl rfl)) (Ns276p471 rfl) rfl rfl)) 

theorem RS277to288.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz62) Bool.true 405809096949892316347 295147905179352825856 2935889361823138143629 Ns276p201 := Ns276p472 

noncomputable def Ns276p473 := nat_lit 133185492212182962667520000 

noncomputable def Ns276p474 := nat_lit 1890727874214058278785122304 

noncomputable abbrev qz749 := (Enclosure.sfrac Bool.false 586544 1000)

noncomputable abbrev qz623 := qz749

noncomputable abbrev qz418 := qz623

noncomputable abbrev qz80 := qz418

noncomputable abbrev qz750 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 586544 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz624 := qz750

noncomputable abbrev qz419 := qz624

noncomputable abbrev qz81 := qz419

noncomputable abbrev qz751 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 586544 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz625 := qz751

noncomputable abbrev qz420 := qz625

noncomputable abbrev qz82 := qz420

noncomputable abbrev qz626 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz81 qz9))

noncomputable def Ns276p475 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) (@HMul.hMul Real Real Real qz5 qz626 (Zeta.RiemannSiegel.correction qz82)) 8170949 33554432 91483 67108864 20411867912870478101 147573952589676412928 2733885356278847937343 Ns276p473 Ns276p474 

noncomputable def Ns276p476 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 586544 1000 116 160 134217728 67108864 2251799813685248 Bool.false 139146984297 1865 

noncomputable def Ns276p477 := Ns276p476 279097919 38 47453128 8 294906479 38 44739240 8 Bool.true 52280214 74873 Bool.true 100094665 Bool.true 96047260 7074237752028440 1 Bool.false 98592335 Bool.false Bool.false 101293392 Bool.false Bool.false 16341898 

noncomputable def Ns276p478 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 586544 1000 9 66 134217728 67108864 2251799813685248 Bool.false 139146984297 1865 

noncomputable def Ns276p479 := Ns276p478 240485871 38 54794152 8 261175631 38 50729528 8 Bool.true 18804581 55863 Bool.true 11101995 Bool.true 129319879 7074237752028440 1 Bool.false 11089339 Bool.true Bool.false 76590351 Bool.true Bool.true 52280214 

noncomputable def Ns276p480 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 586544 1000 142 59 134217728 67108864 2251799813685248 Bool.false 139146984297 1865 

noncomputable def Ns276p481 := Ns276p480 186065264 38 67108856 8 216015088 38 60023992 8 Bool.false 35836762 32964 Bool.false 73842682 Bool.false 5736387 7074237752028440 1 Bool.false 114411916 Bool.true Bool.false 5734640 Bool.false Bool.true 18804581 

noncomputable def Ns276p482 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 586544 1000 401 249 134217728 67108864 2251799813685248 Bool.false 139146984297 1865 

noncomputable def Ns276p483 := Ns276p482 93032624 38 94906264 8 147453232 38 77490640 16 Bool.false 134217720 1910 Bool.false 36942518 Bool.false 162825967 7074237752028440 1 Bool.false 36477828 Bool.true Bool.false 125724787 Bool.true Bool.false 35836762 

noncomputable def Ns276p484 := nat_lit 26109033472365035304377081805127533653197801642581197 

noncomputable def Ns276p485 := nat_lit 25184125769004966336737871790381103574253830144000 

noncomputable def Ns276p486 := nat_lit 33323071097877578211286225387520000 

noncomputable def Ns276p487 := nat_lit 117272724253148615065672769166441185280 

noncomputable abbrev qz627 := (@Eq.refl Real qz749)

noncomputable abbrev qz421 := qz627

noncomputable abbrev qz83 := qz421

noncomputable def Ns276p488 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz80 586544 1000 1376136455744 16000000 1173088 4000 2000 Ns276p486 Ns276p487 qz83 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns276p489 := nat_lit 34221632352898299074153128663616760909919422568964026531840 

noncomputable abbrev qz628 := (@HSub.hSub Real Real Real qz736 qz737 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz738 (@Nat.cast Real Real.instNatCast 1173088))))

noncomputable abbrev qz422 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 586544 4000) (Real.log (Enclosure.sfrac Bool.false 1376136455744 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz628))

noncomputable abbrev qz629 := (Enclosure.sfrac Bool.false 586544 2000)

noncomputable abbrev qz84 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz422 qz629) (@HMul.hMul Real Real Real qz346 qz629 (Real.log Real.pi)))

noncomputable def Ns276p490 := @Enclosure.Real.IsNear.addLit_ft_p qz84 (Enclosure.sfrac Bool.true Ns276p486 Ns276p487) 291812456395547195453 281474976710656000 641684255048735983 46208000000000000000000 Ns276p486 Ns276p487 0 1 Ns276p489 

noncomputable def Ns276p491 := nat_lit 1223950153109669184077299712000 

noncomputable abbrev qz85 := (@HSub.hSub Real Real Real qz350 qz422 qz629)

noncomputable def Ns276p492 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (@HMul.hMul Real Real Real qz5 qz629 (Real.log Real.pi)) 386308453665905686589 281474976710656000 1857950847014661 361000000000000000000 1408100087499 4194304000 36659 4194304000 Ns276p491 291812456395547195453 281474976710656000 

noncomputable abbrev qz86 := qz422

noncomputable def Ns276p493 := @Enclosure.Real.IsNear.subLit_ff_p qz86 qz629 468857183035793193021 281474976710656000 1857950847014661 361000000000000000000 586544 2000 0 1 772616907331811373178000 386308453665905686589 281474976710656000 1857950847014661 361000000000000000000 

noncomputable def Ns276p494 := nat_lit 263943129351247332828067979751063552 

noncomputable def Ns276p495 := nat_lit 27472118089510401513357312 

noncomputable def Ns276p496 := nat_lit 1129051510248302906159087248834645753459825346149683132117982835073528633214678563556682246403517317120 

noncomputable def Ns276p497 := nat_lit 6944593121879247709130360758113828117188282063072225050849103232734334503822904812901874913513570304 

noncomputable def Ns276p498 := nat_lit 13916211884398136750548989706857657587020570207304207686665102815623292274000165829055537479680 

noncomputable def Ns276p499 := BSN.log_dyadic_bound 327560455744 2424712455744 5 4 Ns276p496 67108864 28880000 Ns276p497 Ns276p498 18243333 2752272911488 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 327560455744) (BSN.artanhQ 2424712455744) 0 4 Ns276p497 Ns276p496 Ns276p498 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz423 := (Real.log (Enclosure.sfrac Bool.false 1376136455744 16000000))

noncomputable def Ns276p500 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 586544 4000) qz423 586544 4000 0 1 3198175468657911 281474976710656 781250361 22562500000000000 117241914505530359349 70368744177664000 28639856983899 5640625000000000000 (Enclosure.Real.IsNear.const Bool.false 586544 4000) (BSN.isNear_log_sfrac 1376136455744 16000000 3198175468657911 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1376136455744) qz353)) Bool.false Ns276p495 Ns276p92 1000000462080000 28880000000000000000000 3198175468657911 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1376136455744 16000000 16 2752272911488 2097152000000 18243333 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns276p499 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p501 := BSN.arctan_dyadic_bound_f 1000 1173088 1 0 8388608 3610000 0 1 1 0 1 1 7150 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1173088) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1173088) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns276p502 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1173088))) 884279719003555 562949953421312 1 2000000000000000 7150 8388608 1 3610000 7413850832904011120640 883799890625955 562949953421312 200000000361 722000000000000000 qz17 (Ns276p501 rfl) rfl rfl 

noncomputable abbrev qz424 := (@HMul.hMul Real Real Real qz584 qz589 qz628)

noncomputable abbrev qz87 := qz424

noncomputable abbrev qz425 := qz628

noncomputable abbrev qz88 := qz425

noncomputable def Ns276p503 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 586544 4000) qz423) qz87 117241914505530359349 70368744177664000 28639856983899 5640625000000000000 883799890625955 2251799813685248 200000000361 2888000000000000000 Ns276p494 468857183035793193021 281474976710656000 1857950847014661 361000000000000000000 (Ns276p500 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz88 1 4 0 1 883799890625955 562949953421312 200000000361 722000000000000000 883799890625955 2251799813685248 200000000361 2888000000000000000 qz361 Ns276p502 rfl) 

noncomputable def Ns276p504 := @Ns276p490 Ns276p484 Ns276p485 641684255048735983 46208000000000000000000 (@Ns276p492 641684255048735983 46208000000000000000000 (Ns276p493 (Ns276p503 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 586544 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz629 (Real.log Real.pi) 586544 2000 0 1 38410761 33554432 1 33554432 1408100087499 4194304000 36659 4194304000 (Enclosure.Real.IsNear.const Bool.false 586544 2000) RS277to288.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns276p486 Ns276p487) 

noncomputable def Ns276p505 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns276p484 Ns276p485 641684255048735983 46208000000000000000000 17393373037 16777216 117 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz362 qz84 (Enclosure.sfrac Bool.true Ns276p486 Ns276p487)) Bool.false Ns276p484 Ns276p485 641684255048735983 46208000000000000000000 Ns276p488 (Ns276p504 rfl rfl)) 

noncomputable def Ns276p506 := nat_lit 3798546374428407569055744 

noncomputable def Ns276p507 := nat_lit 857674910248803598132274674712486660676799961147021338009740186737550071465890291227210385024669755190977964766991787407271670623290625 

noncomputable def Ns276p508 := nat_lit 612141167501618400072792053045591380997125368226672679154515024713565033611276263589747518747254442676212551231127271230712890625 

noncomputable def Ns276p509 := nat_lit 4283042387919792754876115663608201475721497084773178059574023672828464417725795312273014271199253089196355203291331885603235286264890625 

noncomputable def Ns276p510 := BSN.sin_dyadic_bound_f 53980590655 34359738368 4 3 16777216 7227051 Ns276p507 Ns276p106 Ns276p508 Ns276p509 Ns276p109 Ns276p508 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53980590655) qz363 0 3 Ns276p507 Ns276p106 Ns276p508 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53980590655) qz364 0 3 Ns276p509 Ns276p109 Ns276p508 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p511 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz80) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17393373037) qz376) Bool.false 17393373037 16777216 117 8388608 Bool.false 16777215 16777216 1 3610000 (Ns276p505 rfl) (Enclosure.sfrac_false_div 17393373037 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17393373037) qz376) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns276p506) qz380) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 164 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q3 17393373037 16777216 226375608064910080 72057594037927936 164 Ns276p506 Ns276p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns276p506 Ns276p92 53980590655 34359738368 7227051 7220000 (Ns276p510 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p512 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns276p484 Ns276p485 641684255048735983 46208000000000000000000 139146984297 134217728 1865 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz362 qz84 (Enclosure.sfrac Bool.true Ns276p486 Ns276p487)) Bool.false Ns276p484 Ns276p485 641684255048735983 46208000000000000000000 Ns276p488 (Ns276p504 rfl rfl)) 

noncomputable def Ns276p513 := Ns276p483 32964 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 401 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 36477828 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 249 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 125724787 134217728) qz83 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) Bool.false 16777215 16777216 26922413 1892679680000 134217720 134217728 1910 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 16777215 16777216 26922413 1892679680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz80) qz80) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 16777215 16777216 430758608 30282874880000 16777215 16777216 26922413 1892679680000 (Ns276p511 rfl rfl) rfl)) rfl) (Ns276p512 rfl) RS277to288.d7 

noncomputable def Ns276p514 := nat_lit 1862541569454326722756644744976 

noncomputable def Ns276p515 := BSN.sin_dyadic_bound_f 36942518 134217728 2 1 134217728 67108864 Ns276p514 Ns276p126 Ns276p514 Ns276p514 Ns276p127 Ns276p514 36477828 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 36942518) qz367 0 1 Ns276p514 Ns276p126 Ns276p514 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 36942518) qz368 0 1 Ns276p514 Ns276p127 Ns276p514 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p516 := nat_lit 690282623649221375558226537537941486631674838416509279804690156020865 

noncomputable def Ns276p517 := nat_lit 494070960465756505951375987065993494765751849342705603685456602241 

noncomputable def Ns276p518 := nat_lit 1807083137526254282595243465763168475520003835715731352320602526508161 

noncomputable def Ns276p519 := BSN.sin_dyadic_bound_f 162825967 134217728 3 2 134217728 67108864 Ns276p516 Ns276p137 Ns276p517 Ns276p518 Ns276p140 Ns276p517 125724787 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 162825967) qz367 0 2 Ns276p516 Ns276p137 Ns276p517 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 162825967) qz368 0 2 Ns276p518 Ns276p140 Ns276p517 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p520 := nat_lit 16210721536968769312373854432865797901261468954319544663578343219456 

noncomputable def Ns276p521 := nat_lit 884015127073903743553381422668744356642251813656370073055109376 

noncomputable def Ns276p522 := nat_lit 48630396580652160129634456535752056215071122359331321250588919439616 

noncomputable def Ns276p523 := BSN.cos_dyadic_bound_f 73842682 134217728 3 2 134217728 67108864 Ns276p520 Ns276p131 Ns276p521 Ns276p522 Ns276p134 Ns276p521 114411916 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 73842682) qz369 0 2 Ns276p520 Ns276p131 Ns276p521 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 73842682) qz370 0 2 Ns276p522 Ns276p134 Ns276p521 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p524 := BSN.sin_dyadic_bound_f 5736387 134217728 1 0 134217728 67108864 0 1 1 0 1 1 5734640 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 5736387) qz367 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 5736387) qz368 0 0 rfl) rfl rfl 

noncomputable def Ns276p525 := Ns276p481 55863 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 142 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 114411916 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 59 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 5734640 134217728) qz83 rfl rfl (Ns276p513 RS277to288.d9 RS277to288.d11 RS277to288.d13 RS277to288.d17 (Ns276p515 rfl rfl) (Ns276p519 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns276p512 rfl) RS277to288.d19 RS277to288.d21 RS277to288.d23 RS277to288.d25 RS277to288.d17 (Ns276p523 rfl rfl) (Ns276p524 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns276p526 := nat_lit 15191620738005839995049000625 

noncomputable def Ns276p527 := BSN.sin_dyadic_bound_f 11101995 134217728 2 1 134217728 67108864 Ns276p526 Ns276p126 Ns276p526 Ns276p526 Ns276p127 Ns276p526 11089339 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 11101995) qz367 0 1 Ns276p526 Ns276p126 Ns276p526 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 11101995) qz368 0 1 Ns276p526 Ns276p127 Ns276p526 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p528 := nat_lit 152557198587215920408730948989116119318898844030382103519655561832641 

noncomputable def Ns276p529 := nat_lit 78220811404402449582616693729864796349468102436910153583254612161 

noncomputable def Ns276p530 := nat_lit 457515154138838956327027613579888628363997595886272490251800176273601 

noncomputable def Ns276p531 := BSN.cos_dyadic_bound_f 129319879 134217728 3 2 134217728 67108864 Ns276p528 Ns276p131 Ns276p529 Ns276p530 Ns276p134 Ns276p529 76590351 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 129319879) qz369 0 2 Ns276p528 Ns276p131 Ns276p529 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 129319879) qz370 0 2 Ns276p530 Ns276p134 Ns276p529 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p532 := Ns276p479 74873 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 9 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 11089339 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 76590351 134217728) qz83 rfl rfl (Ns276p525 rfl rfl) (Ns276p512 rfl) RS277to288.d27 RS277to288.d29 RS277to288.d31 RS277to288.d33 RS277to288.d17 (Ns276p527 rfl rfl) (Ns276p531 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p533 := nat_lit 54735928414150488341712104215450791304804608990280829724157662690625 

noncomputable def Ns276p534 := nat_lit 10075983396573500625573616132792384755379554709065718929937890625 

noncomputable def Ns276p535 := nat_lit 164187633275658318023885165414086789144903067861424357734613112290625 

noncomputable def Ns276p536 := BSN.cos_dyadic_bound_f 100094665 134217728 3 2 134217728 67108864 Ns276p533 Ns276p131 Ns276p534 Ns276p535 Ns276p134 Ns276p534 98592335 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 100094665) qz369 0 2 Ns276p533 Ns276p131 Ns276p534 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 100094665) qz370 0 2 Ns276p535 Ns276p134 Ns276p534 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p537 := nat_lit 46404117693755151673011094096485567114694161752552707388911820800000 

noncomputable def Ns276p538 := nat_lit 7242355516591135298333700833962792829378157671598600217600000000 

noncomputable def Ns276p539 := nat_lit 139197868370232272748436614887788775758423728942314924966300262400000 

noncomputable def Ns276p540 := BSN.cos_dyadic_bound_f 96047260 134217728 3 2 134217728 67108864 Ns276p537 Ns276p131 Ns276p538 Ns276p539 Ns276p134 Ns276p538 101293392 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 96047260) qz369 0 2 Ns276p537 Ns276p131 Ns276p538 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 96047260) qz370 0 2 Ns276p539 Ns276p134 Ns276p538 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p541 := Ns276p477 91483 BSN.abs_quadSignPos (BSN.cos_quad_nat0 116 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 98592335 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 101293392 134217728) qz83 rfl rfl (Ns276p532 rfl) (Ns276p512 rfl) RS277to288.d35 RS277to288.d37 RS277to288.d39 RS277to288.d41 RS277to288.d17 (Ns276p536 rfl rfl) (Ns276p540 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p542 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) 16341898 134217728 91483 134217728 16341898 134217728 91483 134217728 4386744841535488 8170949 33554432 91483 67108864 (Ns276p541 rfl) 

noncomputable def Ns276p543 := @Enclosure.Real.IsNear.mulLit_tf qz626 (Zeta.RiemannSiegel.correction qz82) 674683 2097152 1 8388608 30254012496047 70368744177664 126312018209537 1984618488135680000 20411867912870478101 147573952589676412928 

noncomputable abbrev qz630 := (@HPow.hPow Real Real Real qz7 qz81 qz9)

noncomputable def Ns276p544 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz630 1 1 0 1 674683 2097152 1 8388608 674683 2097152 1 8388608 

noncomputable def Ns276p545 := @Enclosure.Real.IsNear.sqrt_image qz81 97886018643 1048576000 36659 1048576000 81049472 81049504 8388608 (@Enclosure.Real.IsNear.of_eq qz81 (@HMul.hMul Real Real Real qz5 qz80 qz3) Bool.false 97886018643 1048576000 36659 1048576000 (BSN.t_div_two_pi_mk qz80 586544 1000 qz83) (@Enclosure.Real.IsNear.mulLit_ff qz80 qz3 586544 1000 0 1 2670177 16777216 1 16777216 97886018643 1048576000 36659 1048576000 (Enclosure.Real.IsNear.const Bool.false 586544 1000) RS277to288.d44 rfl)) 

noncomputable abbrev qz752 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 586544 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz631 := qz752

noncomputable abbrev qz426 := qz631

noncomputable abbrev qz89 := qz426

noncomputable def Ns276p546 := @Enclosure.Real.IsNear.sqrt_image qz89 5065593 524288 1 524288 26074743 26074749 8388608 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 162098976 16777216 32 16777216 5065593 524288 1 524288 (Ns276p545 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns276p547 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz89) 13037373 4194304 3 8388608 2698731 2698733 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz89) Bool.false 52149492 16777216 6 16777216 13037373 4194304 3 8388608 (Ns276p546 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns276p548 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 5397464 16777216 2 16777216 674683 2097152 1 8388608 (Ns276p547 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz427 := (@HMul.hMul Real Real Real qz584 qz582 qz625)

noncomputable abbrev qz90 := (Real.cos qz427)

noncomputable abbrev qz632 := (@HMul.hMul Real Real Real qz732 qz751 qz751)

noncomputable abbrev qz428 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz632 qz625) qz599)

noncomputable abbrev qz91 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz428))

noncomputable def Ns276p549 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz82) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz90) qz91) Bool.false 30254012496047 

noncomputable def Ns276p550 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz90) qz91 15948943 8388608 187 

noncomputable abbrev qz92 := (@Neg.neg Real Real.instNeg (Real.cos qz427))

noncomputable def Ns276p551 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz90) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz92)) Bool.true 15948943 8388608 187 4194304 (BSN.inv_eq_neg_inv_neg qz90) 

noncomputable def Ns276p552 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz92) Bool.false 31897886 16777216 748 16777216 15948943 8388608 

noncomputable def Ns276p553 := @Enclosure.Real.IsNear.recentre' qz90 Bool.true 8824252 16777216 372998608 30282874880000 2206063 4194304 23312413 1892679680000 

noncomputable abbrev qz93 := qz427

noncomputable def Ns276p554 := @Enclosure.Real.IsNear.cos_image qz93 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 34884345) qz365) Bool.false 34884345 8388608 101 8388608 Bool.true 8824252 16777216 1 

noncomputable def Ns276p555 := nat_lit 26986075412024761348527559 

noncomputable def Ns276p556 := nat_lit 2251799813685248000000000000000 

noncomputable def Ns276p557 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz82 884279719003555 140737488355328 1 500000000000000 347001 524288 1 524288 306845946773952588555 73786976294838206464 Ns276p555 

noncomputable def Ns276p558 := @Enclosure.Real.IsNear.subLit_ff_p qz89 qz1 5065593 524288 1 524288 9 1 0 1 347001 347001 524288 1 

noncomputable def Ns276p559 := @Ns276p558 524288 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 162098976 16777216 32 16777216 5065593 524288 1 524288 (Ns276p545 rfl rfl rfl rfl rfl rfl) rfl) qz377 

noncomputable def Ns276p560 := @Enclosure.Real.IsNear.recentre' qz93 Bool.false 306845946773952588555 73786976294838206464 Ns276p555 Ns276p556 34884345 8388608 101 8388608 (@Ns276p557 Ns276p556 RS277to288.d43 (Ns276p559 rfl rfl) rfl) 

noncomputable def Ns276p561 := nat_lit 1229411466941703976386560 

noncomputable def Ns276p562 := nat_lit 3492809394267244342308145561231085985778483370198392627713411840748239217300069339082721 

noncomputable def Ns276p563 := nat_lit 2222182060545510126053237231909991988115680245239797112701638011503269787729810665441 

noncomputable def Ns276p564 := nat_lit 10473983818680642006672330209229437973359218750104698288914832246221711112324748395917281 

noncomputable def Ns276p565 := BSN.cos_dyadic_bound_f 34941975483 34359738368 3 2 16777216 7227051 Ns276p562 Ns276p173 Ns276p563 Ns276p564 Ns276p176 Ns276p563 8824252 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 34941975483) qz378 0 2 Ns276p562 Ns276p173 Ns276p563 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 34941975483) qz379 0 2 Ns276p564 Ns276p176 Ns276p563 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p566 := @Ns276p554 3610000 (Ns276p560 rfl) (Enclosure.sfrac_false_div 34884345 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 34884345) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns276p561) qz366) 226375608064910080 72057594037927936 Bool.false 8824252 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 34884345 8388608 226375608064910080 72057594037927936 0 Ns276p561 Ns276p104 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 8824252 16777216 Ns276p561 Ns276p104 34941975483 34359738368 7227051 7220000 (Ns276p565 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p567 := @Enclosure.Real.IsNear.inv_image qz92 2206063 4194304 23312413 1892679680000 15948569 15949317 8388608 (@Enclosure.Real.IsNear.neg qz90 Bool.true 2206063 4194304 23312413 1892679680000 (Ns276p553 (Ns276p566 rfl rfl) rfl)) 

noncomputable def Ns276p568 := Ns276p551 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz92) Bool.false 15948943 8388608 187 4194304 (@Ns276p552 187 4194304 (Ns276p567 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p569 := @Enclosure.Real.IsNear.recentre' qz91 Bool.true 1896929 8388608 

noncomputable abbrev qz94 := (@HMul.hMul Real Real Real qz346 qz343 qz428)

noncomputable def Ns276p570 := @Enclosure.Real.IsNear.cos_image qz94 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7545137)) (@Nat.cast Real Real.instNatCast 4194304)) Bool.true 7545137 4194304 

noncomputable def Ns276p571 := nat_lit 69591607260259086298099405 

noncomputable def Ns276p572 := nat_lit 38685626227668133590597632 

noncomputable def Ns276p573 := nat_lit 32876892796835695312798797088229 

noncomputable def Ns276p574 := @Enclosure.Real.IsNear.recentre' qz94 Bool.true Ns276p571 Ns276p572 Ns276p573 

noncomputable def Ns276p575 := nat_lit 1180591620717411303424000000000000000 

noncomputable abbrev qz95 := qz428

noncomputable def Ns276p576 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz95 884279719003555 140737488355328 1 500000000000000 78698635471 

noncomputable abbrev qz429 := (@HSub.hSub Real Real Real qz588 qz632 qz625)

noncomputable abbrev qz96 := qz429

noncomputable def Ns276p577 := @Enclosure.Real.IsNear.subLit_tf qz96 qz31 61518766287 274877906944 1218291 274877906944 1 16 

noncomputable abbrev qz430 := qz632

noncomputable abbrev qz97 := qz430

noncomputable def Ns276p578 := @Enclosure.Real.IsNear.subLit_ff_n qz97 qz82 120409694001 274877906944 694003 274877906944 347001 524288 1 524288 

noncomputable def Ns276p579 := @Enclosure.Real.IsNear.mulLit_ff qz82 qz82 347001 524288 1 524288 347001 524288 1 524288 120409694001 274877906944 

noncomputable def Ns276p580 := nat_lit 6234111212492918348965158112018751110885205620423205429809248257978999929664537993732161 

noncomputable def Ns276p581 := nat_lit 34041254623558103366906394297135159896648818786131734769490125466536530390361890881 

noncomputable def Ns276p582 := nat_lit 37663912664034008089508640486068580491618573105651579998999602005413711188199031288422465 

noncomputable def Ns276p583 := BSN.cos_dyadic_bound_t 7545137 4194304 4 3 8388608 3610000 Ns276p580 Ns276p465 Ns276p581 Ns276p582 Ns276p468 Ns276p581 1896929 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 7545137) (BSN.cosEvenQ 4194304) 0 3 Ns276p580 Ns276p465 Ns276p581 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 7545137) (BSN.cosOddQ 4194304) 0 3 Ns276p582 Ns276p468 Ns276p581 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p584 := @Ns276p569 426564304 15141437440000 1896929 8388608 26660269 946339840000 (@Ns276p570 117 4194304 Bool.true 1896929 8388608 1 3610000 (@Ns276p574 Ns276p575 7545137 4194304 117 4194304 (@Ns276p576 274877906944 1218291 274877906944 Ns276p571 Ns276p572 Ns276p573 Ns276p575 RS277to288.d43 (@Ns276p577 0 1 1259178167536 78698635471 274877906944 1218291 274877906944 (@Ns276p578 32253550939078656 61518766287 274877906944 1218291 274877906944 (@Ns276p579 694003 274877906944 (Ns276p559 rfl rfl) (Ns276p559 rfl rfl) rfl) (Ns276p559 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7545137 4194304) (BSN.cos_neg_of_bound 7545137 4194304 Bool.true 1896929 8388608 1 3610000 (Ns276p583 rfl rfl)) rfl rfl) 

noncomputable def Ns276p585 := @Ns276p543 2733885356278847937343 Ns276p473 (Ns276p544 qz33 (@Enclosure.Real.IsNear.of_eq qz630 (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 674683 2097152 1 8388608 (BSN.rpow_neg_quarter_mk qz81 (BSN.t_div_two_pi_nonneg qz80 586544 1000 qz83)) Ns276p548) rfl) (@Ns276p549 70368744177664 126312018209537 1984618488135680000 (BSN.correction_mk qz82 (BSN.cos_two_pi_p_ne_zero_mk qz80 586544 1000 9 qz83 rfl rfl (@BSN.floor_sqrt_eq_dec qz80 586544 1000 9 qz83 rfl rfl rfl))) (@Ns276p550 4194304 1896929 8388608 26660269 946339840000 30254012496047 70368744177664 126312018209537 1984618488135680000 Ns276p568 (Ns276p584 rfl) rfl)) 

noncomputable def Ns276p586 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (hardyZApproximantRS₀ qz80) Bool.false 56348081654729195797 147573952589676412928 184292738506395261377343 Ns276p473 (@Eq.refl Real (hardyZApproximantRS₀ qz80)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) (@HMul.hMul Real Real Real qz5 qz626 (Zeta.RiemannSiegel.correction qz82))) Bool.false 56348081654729195797 147573952589676412928 184292738506395261377343 Ns276p473 (BSN.hardyZApproximantRS₀_eq qz80 9 (@BSN.floor_sqrt_eq_dec qz80 586544 1000 9 qz83 rfl rfl rfl)) (@Ns276p475 56348081654729195797 147573952589676412928 184292738506395261377343 Ns276p473 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 9)) Bool.false 8170949 33554432 91483 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) (Ns276p542 (Ns276p541 rfl) rfl rfl)) (Ns276p585 rfl) rfl rfl)) 

theorem RS277to288.d50 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz80) Bool.false 56348081654729195797 147573952589676412928 184292738506395261377343 Ns276p473 := Ns276p586 

noncomputable def Ns276p587 := nat_lit 24036104043875687644476211200 

noncomputable abbrev qz753 := (Enclosure.sfrac Bool.false 587929 1000)

noncomputable abbrev qz633 := qz753

noncomputable abbrev qz431 := qz633

noncomputable abbrev qz98 := qz431

noncomputable abbrev qz754 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 587929 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz634 := qz754

noncomputable abbrev qz432 := qz634

noncomputable abbrev qz99 := qz432

noncomputable abbrev qz755 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 587929 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz635 := qz755

noncomputable abbrev qz433 := qz635

noncomputable abbrev qz100 := qz433

noncomputable abbrev qz636 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz99 qz9))

noncomputable def Ns276p588 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) (@HMul.hMul Real Real Real qz5 qz636 (Zeta.RiemannSiegel.correction qz100)) 45434025 33554432 91705 67108864 82952098886877414675 590295810358705651712 3036563194890421906957 Ns276p473 Ns276p587 

noncomputable def Ns276p589 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 587929 1000 116 160 134217728 67108864 2251799813685248 Bool.false 139568730415 1870 

noncomputable def Ns276p590 := Ns276p589 279097919 38 47453128 8 294906479 38 44739240 8 Bool.true 169383772 75055 Bool.true 64899165 Bool.true 82746615 7074237752028440 1 Bool.false 118830513 Bool.false Bool.false 109508394 Bool.false Bool.true 90868050 

noncomputable def Ns276p591 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 587929 1000 8 66 134217728 67108864 2251799813685248 Bool.false 139568730415 1870 

noncomputable def Ns276p592 := Ns276p591 240485871 38 54794152 8 261175631 38 50729528 8 Bool.true 155202263 56000 Bool.true 133257523 Bool.true 69302010 7074237752028440 1 Bool.false 73324269 Bool.false Bool.false 116720009 Bool.true Bool.true 169383772 

noncomputable def Ns276p593 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 587929 1000 143 59 134217728 67108864 2251799813685248 Bool.false 139568730415 1870 

noncomputable def Ns276p594 := Ns276p593 186065264 38 67108856 8 216015088 38 60023992 8 Bool.true 217670973 33046 Bool.false 27059695 Bool.false 128301608 7074237752028440 1 Bool.false 26876752 Bool.false Bool.false 109635166 Bool.false Bool.true 155202263 

noncomputable def Ns276p595 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 587929 1000 402 250 134217728 67108864 2251799813685248 Bool.false 139568730415 1870 

noncomputable def Ns276p596 := Ns276p595 93032624 38 94906264 8 147453232 38 77490640 16 Bool.true 134217672 1918 Bool.false 119009737 Bool.false 169520645 7074237752028440 1 Bool.false 84822840 Bool.true Bool.false 40659021 Bool.true Bool.true 217670973 

noncomputable def Ns276p597 := nat_lit 87036370290780729532540128360990483285670522656049064927 

noncomputable def Ns276p598 := nat_lit 83699434959333288902511630435158649594552597558067200 

noncomputable def Ns276p599 := nat_lit 33718360224124426109626053111520000 

noncomputable def Ns276p600 := nat_lit 118944050995158489886466143211633052480 

noncomputable abbrev qz637 := (@Eq.refl Real qz753)

noncomputable abbrev qz434 := qz637

noncomputable abbrev qz101 := qz434

noncomputable def Ns276p601 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz98 587929 1000 1382643036164 16000000 1175858 4000 2000 Ns276p599 Ns276p600 qz101 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns276p602 := nat_lit 27851638493049833450412841075516954651414567249935700776640 

noncomputable abbrev qz638 := (@HSub.hSub Real Real Real qz736 qz737 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz738 (@Nat.cast Real Real.instNatCast 1175858))))

noncomputable abbrev qz435 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 587929 4000) (Real.log (Enclosure.sfrac Bool.false 1382643036164 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz638))

noncomputable abbrev qz639 := (Enclosure.sfrac Bool.false 587929 2000)

noncomputable abbrev qz102 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz435 qz639) (@HMul.hMul Real Real Real qz346 qz639 (Real.log Real.pi)))

noncomputable def Ns276p603 := @Enclosure.Real.IsNear.addLit_ft_p qz102 (Enclosure.sfrac Bool.true Ns276p599 Ns276p600) 234157537537402661543 225179981368524800 10291070416174480973 739328000000000000000000 Ns276p599 Ns276p600 0 1 Ns276p602 

noncomputable def Ns276p604 := nat_lit 78570231705862250633636085760000 

noncomputable abbrev qz103 := (@HSub.hSub Real Real Real qz350 qz435 qz639)

noncomputable def Ns276p605 := @Enclosure.Real.IsNear.subLit_ff_p qz103 (@HMul.hMul Real Real Real qz5 qz639 (Real.log Real.pi)) 1549664206271566878019 1125899906842624000 1862278974014601 361000000000000000000 22582800303969 67108864000 587929 67108864000 Ns276p604 234157537537402661543 225179981368524800 

noncomputable def Ns276p606 := nat_lit 3099328412543133756038000 

noncomputable abbrev qz104 := qz435

noncomputable def Ns276p607 := @Enclosure.Real.IsNear.subLit_ff_p qz104 qz639 1880638809436605420867 1125899906842624000 1862278974014601 361000000000000000000 587929 2000 0 1 Ns276p606 1549664206271566878019 1125899906842624000 1862278974014601 361000000000000000000 

noncomputable def Ns276p608 := nat_lit 4234822120698594704951911889309270016 

noncomputable def Ns276p609 := nat_lit 27483523113293145614319616 

noncomputable def Ns276p610 := nat_lit 1153518353694200939364933603749078748816436183649909216322835409092624266236933142937072407331428433920 

noncomputable def Ns276p611 := nat_lit 7343128292490833844433701162336414943273772363237772669810731303150060258953678828653518774208036864 

noncomputable def Ns276p612 := nat_lit 16287644864213183934439312218094269607902446299159321100648979889164778873351084775795438714880 

noncomputable def Ns276p613 := BSN.log_dyadic_bound 334067036164 2431219036164 5 4 Ns276p610 67108864 28880000 Ns276p611 Ns276p612 18559886 2765286072328 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 334067036164) (BSN.artanhQ 2431219036164) 0 4 Ns276p611 Ns276p610 Ns276p612 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz436 := (Real.log (Enclosure.sfrac Bool.false 1382643036164 16000000))

noncomputable def Ns276p614 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 587929 4000) qz436 587929 4000 0 1 3199503188172023 281474976710656 781250361 22562500000000000 1881080709918789310367 1125899906842624000 459319743492369 90250000000000000000 (Enclosure.Real.IsNear.const Bool.false 587929 4000) (BSN.isNear_log_sfrac 1382643036164 16000000 3199503188172023 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1382643036164) qz353)) Bool.false Ns276p609 Ns276p92 1000000462080000 28880000000000000000000 3199503188172023 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1382643036164 16000000 16 2765286072328 2097152000000 18559886 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns276p613 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p615 := BSN.arctan_dyadic_bound_f 1000 1175858 1 0 8388608 3610000 0 1 1 0 1 1 7134 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1175858) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1175858) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns276p616 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1175858))) 884279719003555 562949953421312 1 2000000000000000 7134 8388608 1 3610000 7413859840103265861632 883800964367779 562949953421312 200000000361 722000000000000000 qz17 (Ns276p615 rfl) rfl rfl 

noncomputable abbrev qz437 := (@HMul.hMul Real Real Real qz584 qz589 qz638)

noncomputable abbrev qz105 := qz437

noncomputable abbrev qz438 := qz638

noncomputable abbrev qz106 := qz438

noncomputable def Ns276p617 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 587929 4000) qz436) qz105 1881080709918789310367 1125899906842624000 459319743492369 90250000000000000000 883800964367779 2251799813685248 200000000361 2888000000000000000 Ns276p608 1880638809436605420867 1125899906842624000 1862278974014601 361000000000000000000 (Ns276p614 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz106 1 4 0 1 883800964367779 562949953421312 200000000361 722000000000000000 883800964367779 2251799813685248 200000000361 2888000000000000000 qz361 Ns276p616 rfl) 

noncomputable def Ns276p618 := @Ns276p603 Ns276p597 Ns276p598 10291070416174480973 739328000000000000000000 (@Ns276p605 10291070416174480973 739328000000000000000000 (Ns276p607 (Ns276p617 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 587929 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz639 (Real.log Real.pi) 587929 2000 0 1 38410761 33554432 1 33554432 22582800303969 67108864000 587929 67108864000 (Enclosure.Real.IsNear.const Bool.false 587929 2000) RS277to288.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns276p599 Ns276p600) 

noncomputable def Ns276p619 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns276p597 Ns276p598 10291070416174480973 739328000000000000000000 17446091301 16777216 235 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz362 qz102 (Enclosure.sfrac Bool.true Ns276p599 Ns276p600)) Bool.false Ns276p597 Ns276p598 10291070416174480973 739328000000000000000000 Ns276p601 (Ns276p618 rfl rfl)) 

noncomputable def Ns276p620 := BSN.cos_dyadic_bound_f 31142873 34359738368 1 0 16777216 7227051 0 1 1 0 1 1 16777209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 31142873) qz378 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 31142873) qz379 0 0 rfl) rfl rfl 

noncomputable def Ns276p621 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz98) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17446091301) qz376) Bool.false 17446091301 16777216 235 16777216 Bool.true 16777209 16777216 1 3610000 (Ns276p619 rfl) (Enclosure.sfrac_false_div 17446091301 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17446091301) qz376) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2191484912014156890112) qz380) 226375608064910080 72057594037927936 Bool.false 16777209 16777216 165 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 17446091301 16777216 226375608064910080 72057594037927936 165 2191484912014156890112 Ns276p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777209 16777216 2191484912014156890112 Ns276p92 31142873 34359738368 7227051 7220000 (Ns276p620 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p622 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns276p597 Ns276p598 10291070416174480973 739328000000000000000000 139568730415 134217728 1870 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz362 qz102 (Enclosure.sfrac Bool.true Ns276p599 Ns276p600)) Bool.false Ns276p597 Ns276p598 10291070416174480973 739328000000000000000000 Ns276p601 (Ns276p618 rfl rfl)) 

noncomputable def Ns276p623 := Ns276p596 33046 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 402 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 84822840 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 250 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 40659021 134217728) qz101 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) Bool.true 16777209 16777216 54070451 3785359360000 134217672 134217728 1918 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 16777209 16777216 54070451 3785359360000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz98) qz98) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 16777209 16777216 865127216 60565749760000 16777209 16777216 54070451 3785359360000 (Ns276p621 rfl rfl) rfl)) rfl) (Ns276p622 rfl) RS277to288.d7 

noncomputable def Ns276p624 := nat_lit 109405350464889951170053017571187875768132947035247467960850183009601 

noncomputable def Ns276p625 := nat_lit 40240184526836680338884677027148620306242881586448925045415654721 

noncomputable def Ns276p626 := nat_lit 328135571025616180149481283359509330063786355342569506032459717719361 

noncomputable def Ns276p627 := BSN.cos_dyadic_bound_f 119009737 134217728 3 2 134217728 67108864 Ns276p624 Ns276p131 Ns276p625 Ns276p626 Ns276p134 Ns276p625 84822840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 119009737) qz369 0 2 Ns276p624 Ns276p131 Ns276p625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 119009737) qz370 0 2 Ns276p626 Ns276p134 Ns276p625 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p628 := nat_lit 1738411802153186915473474615224961749911863343346247688333199242622884767177688557089260323655172628140625 

noncomputable def Ns276p629 := nat_lit 563211032667853093302480085032057838123650566490668627654517953940358816983011722932352500244140625 

noncomputable def Ns276p630 := nat_lit 10535728104934399940634588114638470913009227754008451496906402475346232923053391343640795862113606573740625 

noncomputable def Ns276p631 := BSN.cos_dyadic_bound_f 169520645 134217728 4 3 134217728 67108864 Ns276p628 Ns276p116 Ns276p629 Ns276p630 Ns276p119 Ns276p629 40659021 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 169520645) qz369 0 3 Ns276p628 Ns276p116 Ns276p629 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 169520645) qz370 0 3 Ns276p630 Ns276p119 Ns276p629 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p632 := nat_lit 536156516445243174295723650625 

noncomputable def Ns276p633 := BSN.sin_dyadic_bound_f 27059695 134217728 2 1 134217728 67108864 Ns276p632 Ns276p126 Ns276p632 Ns276p632 Ns276p127 Ns276p632 26876752 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 27059695) qz367 0 1 Ns276p632 Ns276p126 Ns276p632 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 27059695) qz368 0 1 Ns276p632 Ns276p127 Ns276p632 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p634 := nat_lit 265992639791069767529515074835639111792177659392583535480832618659840 

noncomputable def Ns276p635 := nat_lit 73427170868130874946139495235761821985458589400015473208843042816 

noncomputable def Ns276p636 := nat_lit 696528507842824798303579065386768345077250746407261615493175874420736 

noncomputable def Ns276p637 := BSN.sin_dyadic_bound_f 128301608 134217728 3 2 134217728 67108864 Ns276p634 Ns276p137 Ns276p635 Ns276p636 Ns276p140 Ns276p635 109635166 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 128301608) qz367 0 2 Ns276p634 Ns276p137 Ns276p635 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 128301608) qz368 0 2 Ns276p636 Ns276p140 Ns276p635 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p638 := Ns276p594 56000 BSN.abs_quadSignPos (BSN.cos_quad_nat3 143 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 26876752 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 59 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 109635166 134217728) qz101 rfl rfl (Ns276p623 RS277to288.d9 RS277to288.d11 RS277to288.d13 RS277to288.d17 (Ns276p627 rfl rfl) (Ns276p631 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns276p622 rfl) RS277to288.d19 RS277to288.d21 RS277to288.d23 RS277to288.d25 RS277to288.d17 (Ns276p633 rfl rfl) (Ns276p637 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns276p639 := nat_lit 172015220358187275905716461269198462598864218725153966147438188502561 

noncomputable def Ns276p640 := nat_lit 99433766480178946364609564019547867903058312896142869704514805281 

noncomputable def Ns276p641 := nat_lit 515846793541601469824420164679556292060786539549669612702905535897121 

noncomputable def Ns276p642 := BSN.cos_dyadic_bound_f 133257523 134217728 3 2 134217728 67108864 Ns276p639 Ns276p131 Ns276p640 Ns276p641 Ns276p134 Ns276p640 73324269 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 133257523) qz369 0 2 Ns276p639 Ns276p131 Ns276p640 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 133257523) qz370 0 2 Ns276p641 Ns276p134 Ns276p640 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p643 := nat_lit 12576231150601675879004159224377189045642114903749474976289840800000 

noncomputable def Ns276p644 := nat_lit 532067395668523990507483568082157250244171321692056160100000000 

noncomputable def Ns276p645 := nat_lit 37727629317013690589031462705995402822425856368605040816549322400000 

noncomputable def Ns276p646 := BSN.cos_dyadic_bound_f 69302010 134217728 3 2 134217728 67108864 Ns276p643 Ns276p131 Ns276p644 Ns276p645 Ns276p134 Ns276p644 116720009 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 69302010) qz369 0 2 Ns276p643 Ns276p131 Ns276p644 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 69302010) qz370 0 2 Ns276p645 Ns276p134 Ns276p644 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p647 := Ns276p592 75055 BSN.abs_quadSignPos (BSN.cos_quad_nat0 8 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 73324269 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 116720009 134217728) qz101 rfl rfl (Ns276p638 rfl rfl) (Ns276p622 rfl) RS277to288.d27 RS277to288.d29 RS277to288.d31 RS277to288.d33 RS277to288.d17 (Ns276p642 rfl rfl) (Ns276p646 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p648 := nat_lit 9672068896363828963626919313365023058305727239490825360149760190625 

noncomputable def Ns276p649 := nat_lit 314711688627734175067891723938356291644815142940605005875390625 

noncomputable def Ns276p650 := nat_lit 29015577265714231422530622156647192462333892088186594870437529790625 

noncomputable def Ns276p651 := BSN.cos_dyadic_bound_f 64899165 134217728 3 2 134217728 67108864 Ns276p648 Ns276p131 Ns276p649 Ns276p650 Ns276p134 Ns276p649 118830513 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 64899165) qz369 0 2 Ns276p648 Ns276p131 Ns276p649 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 64899165) qz370 0 2 Ns276p650 Ns276p134 Ns276p649 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p652 := nat_lit 25561545226611842103767508055549860931486163561464745659894118690625 

noncomputable def Ns276p653 := nat_lit 2197869455241662722412646346933927128107638846966361078937890625 

noncomputable def Ns276p654 := nat_lit 76680239940925042985857698873955714940202275406700304257524480290625 

noncomputable def Ns276p655 := BSN.cos_dyadic_bound_f 82746615 134217728 3 2 134217728 67108864 Ns276p652 Ns276p131 Ns276p653 Ns276p654 Ns276p134 Ns276p653 109508394 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 82746615) qz369 0 2 Ns276p652 Ns276p131 Ns276p653 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 82746615) qz370 0 2 Ns276p654 Ns276p134 Ns276p653 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p656 := Ns276p590 91705 BSN.abs_quadSignPos (BSN.cos_quad_nat0 116 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 118830513 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 109508394 134217728) qz101 rfl rfl (Ns276p647 rfl) (Ns276p622 rfl) RS277to288.d35 RS277to288.d37 RS277to288.d39 RS277to288.d41 RS277to288.d17 (Ns276p651 rfl rfl) (Ns276p655 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p657 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) 90868050 134217728 91705 134217728 90868050 134217728 91705 134217728 24392206437580800 45434025 33554432 91705 67108864 (Ns276p656 rfl) 

noncomputable def Ns276p658 := @Enclosure.Real.IsNear.mulLit_tf qz636 (Zeta.RiemannSiegel.correction qz100) 2697141 8388608 1 8388608 30755566315175 70368744177664 1123271956107821 15876947905085440000 82952098886877414675 590295810358705651712 

noncomputable abbrev qz640 := (@HPow.hPow Real Real Real qz7 qz99 qz9)

noncomputable def Ns276p659 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz640 1 1 0 1 2697141 8388608 1 8388608 2697141 8388608 1 8388608 

noncomputable def Ns276p660 := @Enclosure.Real.IsNear.sqrt_image qz99 1569874493433 16777216000 587929 16777216000 81145107 81145138 8388608 (@Enclosure.Real.IsNear.of_eq qz99 (@HMul.hMul Real Real Real qz5 qz98 qz3) Bool.false 1569874493433 16777216000 587929 16777216000 (BSN.t_div_two_pi_mk qz98 587929 1000 qz101) (@Enclosure.Real.IsNear.mulLit_ff qz98 qz3 587929 1000 0 1 2670177 16777216 1 16777216 1569874493433 16777216000 587929 16777216000 (Enclosure.Real.IsNear.const Bool.false 587929 1000) RS277to288.d44 rfl)) 

noncomputable abbrev qz756 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 587929 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz641 := qz756

noncomputable abbrev qz439 := qz641

noncomputable abbrev qz107 := qz439

noncomputable def Ns276p661 := @Enclosure.Real.IsNear.sqrt_image qz107 162290245 16777216 31 16777216 26090122 26090128 8388608 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 162290245 16777216 31 16777216 162290245 16777216 31 16777216 (Ns276p660 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns276p662 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz107) 26090125 8388608 3 8388608 2697140 2697142 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz107) Bool.false 52180250 16777216 6 16777216 26090125 8388608 3 8388608 (Ns276p661 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns276p663 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 5394282 16777216 2 16777216 2697141 8388608 1 8388608 (Ns276p662 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz440 := (@HMul.hMul Real Real Real qz584 qz582 qz635)

noncomputable abbrev qz108 := (Real.cos qz440)

noncomputable abbrev qz642 := (@HMul.hMul Real Real Real qz732 qz755 qz755)

noncomputable abbrev qz441 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz642 qz635) qz599)

noncomputable abbrev qz109 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz441))

noncomputable def Ns276p664 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz100) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz108) qz109) Bool.false 30755566315175 

noncomputable def Ns276p665 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz108) qz109 18088775 8388608 467 

noncomputable abbrev qz110 := (@Neg.neg Real Real.instNeg (Real.cos qz440))

noncomputable def Ns276p666 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz108) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz110)) Bool.true 18088775 8388608 467 8388608 (BSN.inv_eq_neg_inv_neg qz108) 

noncomputable def Ns276p667 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz110) Bool.false 36177550 16777216 934 16777216 18088775 8388608 

noncomputable def Ns276p668 := @Enclosure.Real.IsNear.recentre' qz108 Bool.true 7780377 16777216 181084304 15141437440000 7780377 16777216 11317769 946339840000 

noncomputable abbrev qz111 := qz440

noncomputable def Ns276p669 := @Enclosure.Real.IsNear.cos_image qz111 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 70970469) qz376) Bool.false 70970469 16777216 49 4194304 Bool.true 7780377 16777216 1 

noncomputable def Ns276p670 := nat_lit 836568337777391305897190169 

noncomputable def Ns276p671 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz100 884279719003555 140737488355328 1 500000000000000 11295301 16777216 31 16777216 9988205594340573795055 2361183241434822606848 Ns276p670 

noncomputable def Ns276p672 := @Enclosure.Real.IsNear.subLit_ff_p qz107 qz1 162290245 16777216 31 16777216 9 1 0 1 11295301 11295301 16777216 31 

noncomputable def Ns276p673 := @Ns276p672 16777216 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 162290245 16777216 31 16777216 162290245 16777216 31 16777216 (Ns276p660 rfl rfl rfl rfl rfl rfl) rfl) qz377 

noncomputable def Ns276p674 := @Enclosure.Real.IsNear.recentre' qz111 Bool.false 9988205594340573795055 2361183241434822606848 Ns276p670 Ns276p166 70970469 16777216 49 4194304 (@Ns276p671 Ns276p166 RS277to288.d43 (Ns276p673 rfl rfl) rfl) 

noncomputable def Ns276p675 := nat_lit 2632017540494021946769408 

noncomputable def Ns276p676 := nat_lit 4586775053511424977682287047787334726412066163922981439207076240216351401397535400390625 

noncomputable def Ns276p677 := nat_lit 3830644321573367928395902958161172012148649882054749865711296919345915317535400390625 

noncomputable def Ns276p678 := nat_lit 13752663871891128197190069337445681835211901192004834817889806126810362373557535400390625 

noncomputable def Ns276p679 := BSN.cos_dyadic_bound_f 37403218875 34359738368 3 2 16777216 7227051 Ns276p676 Ns276p173 Ns276p677 Ns276p678 Ns276p176 Ns276p677 7780377 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 37403218875) qz378 0 2 Ns276p676 Ns276p173 Ns276p677 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 37403218875) qz379 0 2 Ns276p678 Ns276p176 Ns276p677 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p680 := @Ns276p669 3610000 (Ns276p674 rfl) (Enclosure.sfrac_false_div 70970469 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 70970469) qz376) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns276p675) qz380) 226375608064910080 72057594037927936 Bool.false 7780377 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 70970469 16777216 226375608064910080 72057594037927936 0 Ns276p675 Ns276p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 7780377 16777216 Ns276p675 Ns276p92 37403218875 34359738368 7227051 7220000 (Ns276p679 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p681 := @Enclosure.Real.IsNear.inv_image qz110 7780377 16777216 11317769 946339840000 18088308 18089242 8388608 (@Enclosure.Real.IsNear.neg qz108 Bool.true 7780377 16777216 11317769 946339840000 (Ns276p668 (Ns276p680 rfl rfl) rfl)) 

noncomputable def Ns276p682 := Ns276p666 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz110) Bool.false 18088775 8388608 467 8388608 (@Ns276p667 467 8388608 (Ns276p681 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p683 := @Enclosure.Real.IsNear.recentre' qz109 Bool.true 1700257 8388608 

noncomputable abbrev qz112 := (@HMul.hMul Real Real Real qz346 qz343 qz441)

noncomputable def Ns276p684 := @Enclosure.Real.IsNear.cos_image qz112 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 29777827)) qz376) Bool.true 29777827 16777216 

noncomputable def Ns276p685 := nat_lit 70310907402713948816210829205 

noncomputable def Ns276p686 := nat_lit 1317355839866585565484469868201897 

noncomputable def Ns276p687 := @Enclosure.Real.IsNear.recentre' qz112 Bool.true Ns276p685 Ns276p184 Ns276p686 

noncomputable def Ns276p688 := nat_lit 48357032784585166988247040000000000000 

noncomputable abbrev qz113 := qz441

noncomputable def Ns276p689 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz113 884279719003555 140737488355328 1 500000000000000 79512066025831 

noncomputable abbrev qz442 := (@HSub.hSub Real Real Real qz588 qz642 qz635)

noncomputable abbrev qz114 := qz442

noncomputable def Ns276p690 := @Enclosure.Real.IsNear.subLit_tf qz114 qz31 61919879981415 281474976710656 1220403319 281474976710656 1 16 

noncomputable abbrev qz443 := qz642

noncomputable abbrev qz115 := qz443

noncomputable def Ns276p691 := @Enclosure.Real.IsNear.subLit_ff_n qz115 qz100 127583824680601 281474976710656 700309623 281474976710656 11295301 16777216 31 16777216 

noncomputable def Ns276p692 := @Enclosure.Real.IsNear.mulLit_ff qz100 qz100 11295301 16777216 31 16777216 11295301 16777216 31 16777216 127583824680601 281474976710656 

noncomputable def Ns276p693 := nat_lit 99087062942431711557412425372090504348535396002840832882717923875986244854730445457364634188401 

noncomputable def Ns276p694 := nat_lit 486089264569934738343535021442377428489846269311402913983494390248018607908105036799031921 

noncomputable def Ns276p695 := nat_lit 598772301824562051126178049915567849075767211949815784146085851131074682362840639530620034366065 

noncomputable def Ns276p696 := BSN.cos_dyadic_bound_t 29777827 16777216 4 3 8388608 3610000 Ns276p693 Ns276p193 Ns276p694 Ns276p695 Ns276p196 Ns276p694 1700257 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 29777827) qz600 0 3 Ns276p693 Ns276p193 Ns276p694 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 29777827) (BSN.cosOddQ 16777216) 0 3 Ns276p695 Ns276p196 Ns276p694 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p697 := @Ns276p683 835078608 30282874880000 1700257 8388608 52192413 1892679680000 (@Ns276p684 229 8388608 Bool.true 1700257 8388608 1 3610000 (@Ns276p687 Ns276p688 29777827 16777216 229 8388608 (@Ns276p689 281474976710656 1220403319 281474976710656 Ns276p685 Ns276p184 Ns276p686 Ns276p688 RS277to288.d43 (@Ns276p690 0 1 1272193056413296 79512066025831 281474976710656 1220403319 281474976710656 (@Ns276p691 1038843201142275440640 61919879981415 281474976710656 1220403319 281474976710656 (@Ns276p692 700309623 281474976710656 (Ns276p673 rfl rfl) (Ns276p673 rfl rfl) rfl) (Ns276p673 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 29777827 16777216) (BSN.cos_neg_of_bound 29777827 16777216 Bool.true 1700257 8388608 1 3610000 (Ns276p696 rfl rfl)) rfl rfl) 

noncomputable def Ns276p698 := @Ns276p658 3036563194890421906957 Ns276p473 (Ns276p659 qz33 (@Enclosure.Real.IsNear.of_eq qz640 (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 2697141 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz99 (BSN.t_div_two_pi_nonneg qz98 587929 1000 qz101)) Ns276p663) rfl) (@Ns276p664 70368744177664 1123271956107821 15876947905085440000 (BSN.correction_mk qz100 (BSN.cos_two_pi_p_ne_zero_mk qz98 587929 1000 9 qz101 rfl rfl (@BSN.floor_sqrt_eq_dec qz98 587929 1000 9 qz101 rfl rfl rfl))) (@Ns276p665 8388608 1700257 8388608 52192413 1892679680000 30755566315175 70368744177664 1123271956107821 15876947905085440000 Ns276p682 (Ns276p697 rfl) rfl)) 

noncomputable def Ns276p699 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (hardyZApproximantRS₀ qz98) Bool.true 716331721659770239725 590295810358705651712 185036001649372956306957 Ns276p473 (@Eq.refl Real (hardyZApproximantRS₀ qz98)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) (@HMul.hMul Real Real Real qz5 qz636 (Zeta.RiemannSiegel.correction qz100))) Bool.true 716331721659770239725 590295810358705651712 185036001649372956306957 Ns276p473 (BSN.hardyZApproximantRS₀_eq qz98 9 (@BSN.floor_sqrt_eq_dec qz98 587929 1000 9 qz101 rfl rfl rfl)) (@Ns276p588 716331721659770239725 590295810358705651712 185036001649372956306957 Ns276p473 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 9)) Bool.true 45434025 33554432 91705 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) (Ns276p657 (Ns276p656 rfl) rfl rfl)) (Ns276p698 rfl) rfl rfl)) 

theorem RS277to288.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz98) Bool.true 716331721659770239725 590295810358705651712 185036001649372956306957 Ns276p473 := Ns276p699 

noncomputable def Ns276p700 := nat_lit 16648186526522870333440000 

noncomputable def Ns276p701 := nat_lit 2414608417451952301324369920 

noncomputable abbrev qz757 := (Enclosure.sfrac Bool.false 589313 1000)

noncomputable abbrev qz643 := qz757

noncomputable abbrev qz444 := qz643

noncomputable abbrev qz116 := qz444

noncomputable abbrev qz758 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 589313 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz644 := qz758

noncomputable abbrev qz445 := qz644

noncomputable abbrev qz117 := qz445

noncomputable abbrev qz759 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 589313 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz645 := qz759

noncomputable abbrev qz446 := qz645

noncomputable abbrev qz118 := qz446

noncomputable abbrev qz646 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz117 qz9))

noncomputable def Ns276p702 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) (@HMul.hMul Real Real Real qz5 qz646 (Zeta.RiemannSiegel.correction qz118)) 32124655 4194304 45961 33554432 10544600602888259375 73786976294838206464 458979283998572945347 Ns276p700 Ns276p701 

noncomputable def Ns276p703 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 589313 1000 116 160 134217728 67108864 2251799813685248 Bool.false 139990390615 1874 

noncomputable def Ns276p704 := Ns276p703 279097919 38 47453128 8 294906479 38 44739240 8 Bool.false 428766387 75233 Bool.true 29510485 Bool.true 69236982 7074237752028440 1 Bool.false 130986537 Bool.false Bool.false 116752100 Bool.false Bool.false 513994480 

noncomputable def Ns276p705 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 589313 1000 8 66 134217728 67108864 2251799813685248 Bool.false 139990390615 1874 

noncomputable def Ns276p706 := Ns276p705 240485871 38 54794152 8 261175631 38 50729528 8 Bool.false 427559818 56133 Bool.true 44429768 Bool.true 9108883 7074237752028440 1 Bool.false 126930895 Bool.false Bool.false 133908752 Bool.true Bool.false 428766387 

noncomputable def Ns276p707 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 589313 1000 143 60 134217728 67108864 2251799813685248 Bool.false 139990390615 1874 

noncomputable def Ns276p708 := Ns276p707 186065264 38 67108856 8 216015088 38 60023992 8 Bool.false 303811002 33126 Bool.false 191205570 Bool.false 40168212 7074237752028440 1 Bool.false 132785792 Bool.false Bool.false 128251756 Bool.false Bool.false 427559818 

noncomputable def Ns276p709 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 589313 1000 403 251 134217728 67108864 2251799813685248 Bool.false 139990390615 1874 

noncomputable def Ns276p710 := Ns276p709 93032624 38 94906264 8 147453232 38 77490640 16 Bool.false 134217664 1926 Bool.false 201084072 Bool.false 176276857 7074237752028440 1 Bool.false 133864137 Bool.false Bool.false 129794868 Bool.false Bool.false 303811002 

noncomputable def Ns276p711 := nat_lit 88539629020446866085804864139343320267606059515440755943 

noncomputable def Ns276p712 := nat_lit 84888596944402660744298120203158047061332867206348800 

noncomputable def Ns276p713 := nat_lit 34117102255837988939033003740640000 

noncomputable def Ns276p714 := nat_lit 120633951815424695644620271939342681920 

noncomputable abbrev qz647 := (@Eq.refl Real qz757)

noncomputable abbrev qz447 := qz647

noncomputable abbrev qz119 := qz447

noncomputable def Ns276p715 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz116 589313 1000 1389160247876 16000000 1178626 4000 2000 Ns276p713 Ns276p714 qz119 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns276p716 := nat_lit 28332681286542997147457556524589862485633939044941041901760 

noncomputable abbrev qz648 := (@HSub.hSub Real Real Real qz736 qz737 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz738 (@Nat.cast Real Real.instNatCast 1178626))))

noncomputable abbrev qz448 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 589313 4000) (Real.log (Enclosure.sfrac Bool.false 1389160247876 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz648))

noncomputable abbrev qz649 := (Enclosure.sfrac Bool.false 589313 2000)

noncomputable abbrev qz120 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz448 qz649) (@HMul.hMul Real Real Real qz346 qz649 (Real.log Real.pi)))

noncomputable def Ns276p717 := @Enclosure.Real.IsNear.addLit_ft_p qz120 (Enclosure.sfrac Bool.true Ns276p713 Ns276p714) 234864965813121334303 225179981368524800 10315175334720525781 739328000000000000000000 Ns276p713 Ns276p714 0 1 Ns276p716 

noncomputable def Ns276p718 := nat_lit 78807605245587045196192808960000 

noncomputable abbrev qz121 := (@HSub.hSub Real Real Real qz350 qz448 qz649)

noncomputable def Ns276p719 := @Enclosure.Real.IsNear.subLit_ff_p qz121 (@HMul.hMul Real Real Real qz5 qz649 (Real.log Real.pi)) 1554093232727645826203 1125899906842624000 1866603976013097 361000000000000000000 22635960797193 67108864000 589313 67108864000 Ns276p718 234864965813121334303 225179981368524800 

noncomputable def Ns276p720 := nat_lit 3108186465455291652406000 

noncomputable abbrev qz122 := qz448

noncomputable def Ns276p721 := @Enclosure.Real.IsNear.subLit_ff_p qz122 qz649 1885846958628219464859 1125899906842624000 1866603976013097 361000000000000000000 589313 2000 0 1 Ns276p720 1554093232727645826203 1125899906842624000 1866603976013097 361000000000000000000 

noncomputable def Ns276p722 := nat_lit 4246549830077916184198526403222700032 

noncomputable def Ns276p723 := nat_lit 27494893081056390263341056 

noncomputable def Ns276p724 := nat_lit 1178488989709441708836148633490805163594155741504326995922540386282755636914680921666319543334452920320 

noncomputable def Ns276p725 := nat_lit 7759039617780123437832664350234095004354354167273927387379254444185978996841068400208254218541727744 

noncomputable def Ns276p726 := nat_lit 19010159547009747450157357804032991084003549424555847960715768805515487167918300448558370324480 

noncomputable def Ns276p727 := BSN.log_dyadic_bound 340584247876 2437736247876 5 4 Ns276p724 67108864 28880000 Ns276p725 Ns276p726 18875466 2778320495752 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 340584247876) (BSN.artanhQ 2437736247876) 0 4 Ns276p725 Ns276p724 Ns276p726 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz449 := (Real.log (Enclosure.sfrac Bool.false 1389160247876 16000000))

noncomputable def Ns276p728 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 589313 4000) qz449 589313 4000 0 1 3200826826628343 281474976710656 781250361 22562500000000000 1886288859680828698359 1125899906842624000 460400993991993 90250000000000000000 (Enclosure.Real.IsNear.const Bool.false 589313 4000) (BSN.isNear_log_sfrac 1389160247876 16000000 3200826826628343 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1389160247876) qz353)) Bool.false Ns276p723 Ns276p92 1000000462080000 28880000000000000000000 3200826826628343 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1389160247876 16000000 16 2778320495752 2097152000000 18875466 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns276p727 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p729 := BSN.arctan_dyadic_bound_f 1000 1178626 1 0 8388608 3610000 0 1 1 0 1 1 7117 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1178626) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1178626) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns276p730 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1178626))) 884279719003555 562949953421312 1 2000000000000000 7117 8388608 1 3610000 7413869410252474023936 883802105218467 562949953421312 200000000361 722000000000000000 qz17 (Ns276p729 rfl) rfl rfl 

noncomputable abbrev qz450 := (@HMul.hMul Real Real Real qz584 qz589 qz648)

noncomputable abbrev qz123 := qz450

noncomputable abbrev qz451 := qz648

noncomputable abbrev qz124 := qz451

noncomputable def Ns276p731 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 589313 4000) qz449) qz123 1886288859680828698359 1125899906842624000 460400993991993 90250000000000000000 883802105218467 2251799813685248 200000000361 2888000000000000000 Ns276p722 1885846958628219464859 1125899906842624000 1866603976013097 361000000000000000000 (Ns276p728 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz124 1 4 0 1 883802105218467 562949953421312 200000000361 722000000000000000 883802105218467 2251799813685248 200000000361 2888000000000000000 qz361 Ns276p730 rfl) 

noncomputable def Ns276p732 := @Ns276p717 Ns276p711 Ns276p712 10315175334720525781 739328000000000000000000 (@Ns276p719 10315175334720525781 739328000000000000000000 (Ns276p721 (Ns276p731 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 589313 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz649 (Real.log Real.pi) 589313 2000 0 1 38410761 33554432 1 33554432 22635960797193 67108864000 589313 67108864000 (Enclosure.Real.IsNear.const Bool.false 589313 2000) RS277to288.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns276p713 Ns276p714) 

noncomputable def Ns276p733 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns276p711 Ns276p712 10315175334720525781 739328000000000000000000 8749399413 8388608 59 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz362 qz120 (Enclosure.sfrac Bool.true Ns276p713 Ns276p714)) Bool.false Ns276p711 Ns276p712 10315175334720525781 739328000000000000000000 Ns276p715 (Ns276p732 rfl rfl)) 

noncomputable def Ns276p734 := BSN.cos_dyadic_bound_f 31852437 34359738368 1 0 16777216 7227051 0 1 1 0 1 1 16777208 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 31852437) qz378 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 31852437) qz379 0 0 rfl) rfl rfl 

noncomputable def Ns276p735 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz116) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8749399413) qz365) Bool.false 8749399413 8388608 59 4194304 Bool.false 16777208 16777216 1 3610000 (Ns276p733 rfl) (Enclosure.sfrac_false_div 8749399413 8388608) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8749399413) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1120708013606280626176) qz366) 226375608064910080 72057594037927936 Bool.false 16777208 16777216 166 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q0 8749399413 8388608 226375608064910080 72057594037927936 166 1120708013606280626176 Ns276p104 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777208 16777216 1120708013606280626176 Ns276p104 31852437 34359738368 7227051 7220000 (Ns276p734 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p736 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns276p711 Ns276p712 10315175334720525781 739328000000000000000000 139990390615 134217728 1874 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz362 qz120 (Enclosure.sfrac Bool.true Ns276p713 Ns276p714)) Bool.false Ns276p711 Ns276p712 10315175334720525781 739328000000000000000000 Ns276p715 (Ns276p732 rfl rfl)) 

noncomputable def Ns276p737 := Ns276p710 33126 BSN.abs_quadSignPos (BSN.cos_quad_nat3 403 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133864137 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 251 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 129794868 134217728) qz119 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) Bool.false 2097151 2097152 13574019 946339840000 134217664 134217728 1926 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 2097151 2097152 13574019 946339840000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz116) qz116) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 16777208 16777216 217184304 15141437440000 2097151 2097152 13574019 946339840000 (Ns276p735 rfl rfl) rfl)) rfl) (Ns276p736 rfl) RS277to288.d7 

noncomputable def Ns276p738 := nat_lit 8949772320969990870952469400965388325690410932869982138647906198929143423753802395085078766419174035030016 

noncomputable def Ns276p739 := nat_lit 4370509358616136019324995014914460463996453089281440033423986897948595179462394060822760645267030016 

noncomputable def Ns276p740 := nat_lit 44702832832047601049409867964359162178199302962567400007311334691360128380139755240650392451989578633445376 

noncomputable def Ns276p741 := BSN.sin_dyadic_bound_f 201084072 134217728 4 3 134217728 67108864 Ns276p738 Ns276p255 Ns276p739 Ns276p740 Ns276p258 Ns276p739 133864137 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 201084072) qz367 0 3 Ns276p738 Ns276p255 Ns276p739 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 201084072) qz368 0 3 Ns276p740 Ns276p258 Ns276p739 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p742 := nat_lit 5281855342252039594758135869559565020295774893236032651831362783386323981221374513803271905257642946452001 

noncomputable def Ns276p743 := nat_lit 900209479147482459153306842638137763232145730163805674850716830905806830431558882218071884774496801 

noncomputable def Ns276p744 := nat_lit 26393225682455239790836259980847974196030186167696657349605983897390889754242732647435003993074791834966561 

noncomputable def Ns276p745 := BSN.sin_dyadic_bound_f 176276857 134217728 4 3 134217728 67108864 Ns276p742 Ns276p255 Ns276p743 Ns276p744 Ns276p258 Ns276p743 129794868 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 176276857) qz367 0 3 Ns276p742 Ns276p255 Ns276p743 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 176276857) qz368 0 3 Ns276p744 Ns276p258 Ns276p743 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p746 := nat_lit 7314279389052168725571554785812749683765547494915521702612195684334889904740084581375250694732829862400000 

noncomputable def Ns276p747 := nat_lit 2387846880465480537691040583704143639624997389172679917821964329939376843702304257246001000000000000 

noncomputable def Ns276p748 := nat_lit 36540637235038707302601813403811730775755500762182154006549638550998240003340628789070167678062325312000000 

noncomputable def Ns276p749 := BSN.sin_dyadic_bound_f 191205570 134217728 4 3 134217728 67108864 Ns276p746 Ns276p255 Ns276p747 Ns276p748 Ns276p258 Ns276p747 132785792 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 191205570) qz367 0 3 Ns276p746 Ns276p255 Ns276p747 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 191205570) qz368 0 3 Ns276p748 Ns276p258 Ns276p747 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p750 := nat_lit 2603334668996105145998137979136 

noncomputable def Ns276p751 := BSN.cos_dyadic_bound_f 40168212 134217728 2 1 134217728 67108864 Ns276p750 Ns276p122 Ns276p750 Ns276p750 Ns276p123 Ns276p750 128251756 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 40168212) qz369 0 1 Ns276p750 Ns276p122 Ns276p750 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 40168212) qz370 0 1 Ns276p750 Ns276p123 Ns276p750 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p752 := Ns276p708 56133 BSN.abs_quadSignPos (BSN.cos_quad_nat3 143 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 132785792 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 128251756 134217728) qz119 rfl rfl (Ns276p737 RS277to288.d9 RS277to288.d11 RS277to288.d13 RS277to288.d17 (Ns276p741 rfl rfl) (Ns276p745 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns276p736 rfl) RS277to288.d19 RS277to288.d21 RS277to288.d23 RS277to288.d25 RS277to288.d17 (Ns276p749 rfl rfl) (Ns276p751 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns276p753 := nat_lit 3896692915357894382089000062976 

noncomputable def Ns276p754 := BSN.cos_dyadic_bound_f 44429768 134217728 2 1 134217728 67108864 Ns276p753 Ns276p122 Ns276p753 Ns276p753 Ns276p123 Ns276p753 126930895 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 44429768) qz369 0 1 Ns276p753 Ns276p122 Ns276p753 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 44429768) qz370 0 1 Ns276p753 Ns276p123 Ns276p753 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p755 := nat_lit 6884311216366689813870120721 

noncomputable def Ns276p756 := BSN.cos_dyadic_bound_f 9108883 134217728 2 1 134217728 67108864 Ns276p755 Ns276p122 Ns276p755 Ns276p755 Ns276p123 Ns276p755 133908752 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 9108883) qz369 0 1 Ns276p755 Ns276p122 Ns276p755 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 9108883) qz370 0 1 Ns276p755 Ns276p123 Ns276p755 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p757 := Ns276p706 75233 BSN.abs_quadSignPos (BSN.cos_quad_nat0 8 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 126930895 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133908752 134217728) qz119 rfl rfl (Ns276p752 rfl rfl) (Ns276p736 rfl) RS277to288.d27 RS277to288.d29 RS277to288.d31 RS277to288.d33 RS277to288.d17 (Ns276p754 rfl rfl) (Ns276p756 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p758 := nat_lit 758412336070304581680445800625 

noncomputable def Ns276p759 := BSN.cos_dyadic_bound_f 29510485 134217728 2 1 134217728 67108864 Ns276p758 Ns276p122 Ns276p758 Ns276p758 Ns276p123 Ns276p758 130986537 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 29510485) qz369 0 1 Ns276p758 Ns276p122 Ns276p758 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 29510485) qz370 0 1 Ns276p758 Ns276p123 Ns276p758 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p760 := nat_lit 12529093052095791026374015547324762306548998358284992623231128166656 

noncomputable def Ns276p761 := nat_lit 528086459187701070966481480600102180707240834000269068143288576 

noncomputable def Ns276p762 := nat_lit 37586222983368997676980113679013086715285580593186977331557097922816 

noncomputable def Ns276p763 := BSN.cos_dyadic_bound_f 69236982 134217728 3 2 134217728 67108864 Ns276p760 Ns276p131 Ns276p761 Ns276p762 Ns276p134 Ns276p761 116752100 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 69236982) qz369 0 2 Ns276p760 Ns276p131 Ns276p761 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 69236982) qz370 0 2 Ns276p762 Ns276p134 Ns276p761 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p764 := Ns276p704 91922 BSN.abs_quadSignPos (BSN.cos_quad_nat0 116 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 130986537 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 116752100 134217728) qz119 rfl rfl (Ns276p757 rfl) (Ns276p736 rfl) RS277to288.d35 RS277to288.d37 RS277to288.d39 RS277to288.d41 RS277to288.d17 (Ns276p759 rfl rfl) (Ns276p763 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p765 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) 513994480 134217728 91922 134217728 513994480 134217728 91922 134217728 137974342620282880 32124655 4194304 45961 33554432 (Ns276p764 rfl) 

noncomputable def Ns276p766 := @Enclosure.Real.IsNear.mulLit_tf qz646 (Zeta.RiemannSiegel.correction qz118) 673889 2097152 1 8388608 15647384959375 35184372088832 679780355141009 7938473952542720000 10544600602888259375 73786976294838206464 

noncomputable abbrev qz650 := (@HPow.hPow Real Real Real qz7 qz117 qz9)

noncomputable def Ns276p767 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz650 1 1 0 1 673889 2097152 1 8388608 673889 2097152 1 8388608 

noncomputable def Ns276p768 := @Enclosure.Real.IsNear.sqrt_image qz117 1573570018401 16777216000 589313 16777216000 81240559 81240591 8388608 (@Enclosure.Real.IsNear.of_eq qz117 (@HMul.hMul Real Real Real qz5 qz116 qz3) Bool.false 1573570018401 16777216000 589313 16777216000 (BSN.t_div_two_pi_mk qz116 589313 1000 qz119) (@Enclosure.Real.IsNear.mulLit_ff qz116 qz3 589313 1000 0 1 2670177 16777216 1 16777216 1573570018401 16777216000 589313 16777216000 (Enclosure.Real.IsNear.const Bool.false 589313 1000) RS277to288.d44 rfl)) 

noncomputable abbrev qz760 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 589313 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz651 := qz760

noncomputable abbrev qz452 := qz651

noncomputable abbrev qz125 := qz452

noncomputable def Ns276p769 := @Enclosure.Real.IsNear.sqrt_image qz125 81240575 8388608 1 524288 26105463 26105469 8388608 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 162481150 16777216 32 16777216 81240575 8388608 1 524288 (Ns276p768 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns276p770 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz125) 13052733 4194304 3 8388608 2695555 2695557 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz125) Bool.false 52210932 16777216 6 16777216 13052733 4194304 3 8388608 (Ns276p769 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns276p771 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 5391112 16777216 2 16777216 673889 2097152 1 8388608 (Ns276p770 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz453 := (@HMul.hMul Real Real Real qz584 qz582 qz645)

noncomputable abbrev qz126 := (Real.cos qz453)

noncomputable abbrev qz652 := (@HMul.hMul Real Real Real qz732 qz759 qz759)

noncomputable abbrev qz454 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz652 qz645) qz599)

noncomputable abbrev qz127 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz454))

noncomputable def Ns276p772 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz118) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz126) qz127) Bool.false 15647384959375 

noncomputable def Ns276p773 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz126) qz127 42019375 16777216 1297 

noncomputable abbrev qz128 := (@Neg.neg Real Real.instNeg (Real.cos qz453))

noncomputable def Ns276p774 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz126) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz128)) Bool.true 42019375 16777216 1297 16777216 (BSN.inv_eq_neg_inv_neg qz126) 

noncomputable def Ns276p775 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz128) Bool.false 42019375 16777216 1297 16777216 42019375 16777216 

noncomputable def Ns276p776 := @Enclosure.Real.IsNear.recentre' qz126 Bool.true 6698695 16777216 372998608 30282874880000 6698695 16777216 23312413 1892679680000 

noncomputable abbrev qz129 := qz453

noncomputable def Ns276p777 := @Enclosure.Real.IsNear.cos_image qz129 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9021245) (@Nat.cast Real Real.instNatCast 2097152)) Bool.false 9021245 2097152 101 8388608 Bool.true 6698695 16777216 1 

noncomputable def Ns276p778 := nat_lit 26986075412127350400488903 

noncomputable def Ns276p779 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz118 884279719003555 140737488355328 1 500000000000000 5743103 8388608 1 524288 5078509507048473731165 1180591620717411303424 Ns276p778 

noncomputable def Ns276p780 := @Enclosure.Real.IsNear.subLit_ff_p qz125 qz1 81240575 8388608 1 524288 9 1 0 1 5743103 5743103 8388608 1 

noncomputable def Ns276p781 := @Ns276p780 524288 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 162481150 16777216 32 16777216 81240575 8388608 1 524288 (Ns276p768 rfl rfl rfl rfl rfl rfl) rfl) qz377 

noncomputable def Ns276p782 := @Enclosure.Real.IsNear.recentre' qz129 Bool.false 5078509507048473731165 1180591620717411303424 Ns276p778 Ns276p556 9021245 2097152 101 8388608 (@Ns276p779 Ns276p556 RS277to288.d43 (Ns276p781 rfl rfl) rfl) 

noncomputable def Ns276p783 := nat_lit 5917197148148294670886636232735688322018342407003755843653595423763321397498727201779681 

noncomputable def Ns276p784 := nat_lit 6372045507300957078260328989846688816782028404929490980634461578471253706103233196001 

noncomputable def Ns276p785 := nat_lit 17738847353430282098503388040227371588421463164201408548999517348133021685083975138947041 

noncomputable def Ns276p786 := BSN.cos_dyadic_bound_f 39859776443 34359738368 3 2 16777216 7227051 Ns276p783 Ns276p173 Ns276p784 Ns276p785 Ns276p176 Ns276p784 6698695 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 39859776443) qz378 0 2 Ns276p783 Ns276p173 Ns276p784 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 39859776443) qz379 0 2 Ns276p785 Ns276p176 Ns276p784 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p787 := @Ns276p777 3610000 (Ns276p782 rfl) (Enclosure.sfrac_false_div 9021245 2097152) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9021245) (@Nat.cast Real Real.instNatCast 2097152)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 350610301444289797816320) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 6698695 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 9021245 2097152 226375608064910080 72057594037927936 0 350610301444289797816320 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 6698695 16777216 350610301444289797816320 302231454903657293676544 39859776443 34359738368 7227051 7220000 (Ns276p786 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p788 := @Enclosure.Real.IsNear.inv_image qz128 6698695 16777216 23312413 1892679680000 21009039 21010336 8388608 (@Enclosure.Real.IsNear.neg qz126 Bool.true 6698695 16777216 23312413 1892679680000 (Ns276p776 (Ns276p787 rfl rfl) rfl)) 

noncomputable def Ns276p789 := Ns276p774 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz128) Bool.false 42019375 16777216 1297 16777216 (@Ns276p775 1297 16777216 (Ns276p788 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p790 := @Enclosure.Real.IsNear.recentre' qz127 Bool.true 1489540 8388608 

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz346 qz343 qz454)

noncomputable def Ns276p791 := @Enclosure.Real.IsNear.cos_image qz130 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 29348549)) qz376) Bool.true 29348549 16777216 

noncomputable def Ns276p792 := nat_lit 17324325626447883053288638045 

noncomputable def Ns276p793 := nat_lit 9903520314283042199192993792 

noncomputable def Ns276p794 := nat_lit 268171830566224473912279640147569 

noncomputable def Ns276p795 := @Enclosure.Real.IsNear.recentre' qz130 Bool.true Ns276p792 Ns276p793 Ns276p794 

noncomputable def Ns276p796 := nat_lit 9444732965739290427392000000000000000 

noncomputable abbrev qz131 := qz454

noncomputable def Ns276p797 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz131 884279719003555 140737488355328 1 500000000000000 19591454213119 

noncomputable abbrev qz455 := (@HSub.hSub Real Real Real qz588 qz652 qz645)

noncomputable abbrev qz132 := qz455

noncomputable def Ns276p798 := @Enclosure.Real.IsNear.subLit_tf qz132 qz31 15193407702015 70368744177664 9937415 2199023255552 1 16 

noncomputable abbrev qz456 := qz652

noncomputable abbrev qz133 := qz456

noncomputable def Ns276p799 := @Enclosure.Real.IsNear.subLit_ff_n qz133 qz118 32983232068609 70368744177664 5743111 2199023255552 5743103 8388608 1 524288 

noncomputable def Ns276p800 := @Enclosure.Real.IsNear.mulLit_ff qz118 qz118 5743103 8388608 1 524288 5743103 8388608 1 524288 32983232068609 70368744177664 

noncomputable def Ns276p801 := nat_lit 93464633969914133214117290198626533205944977009005327978863119190650450200791576157168911558481 

noncomputable def Ns276p802 := nat_lit 408356632505668676485579471333913276710696870140738398768827043249823536194533438487832401 

noncomputable def Ns276p803 := nat_lit 564921401912209861052589965224818003295747260647076425855201204489467682601426115768943422515025 

noncomputable def Ns276p804 := BSN.cos_dyadic_bound_t 29348549 16777216 4 3 8388608 3610000 Ns276p801 Ns276p193 Ns276p802 Ns276p803 Ns276p196 Ns276p802 1489540 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 29348549) qz600 0 3 Ns276p801 Ns276p193 Ns276p802 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 29348549) (BSN.cosOddQ 16777216) 0 3 Ns276p803 Ns276p196 Ns276p802 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p805 := @Ns276p790 1738747216 60565749760000 372385 2097152 108671701 3785359360000 (@Ns276p791 477 16777216 Bool.true 1489540 8388608 1 3610000 (@Ns276p795 Ns276p796 29348549 16777216 477 16777216 (@Ns276p797 70368744177664 9937415 2199023255552 Ns276p792 Ns276p793 Ns276p794 Ns276p796 RS277to288.d43 (@Ns276p798 0 1 313463267409904 19591454213119 70368744177664 9937415 2199023255552 (@Ns276p799 127451541396384645120 15193407702015 70368744177664 9937415 2199023255552 (@Ns276p800 5743111 2199023255552 (Ns276p781 rfl rfl) (Ns276p781 rfl rfl) rfl) (Ns276p781 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 29348549 16777216) (BSN.cos_neg_of_bound 29348549 16777216 Bool.true 1489540 8388608 1 3610000 (Ns276p804 rfl rfl)) rfl rfl) 

noncomputable def Ns276p806 := @Ns276p766 458979283998572945347 Ns276p700 (Ns276p767 qz33 (@Enclosure.Real.IsNear.of_eq qz650 (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 673889 2097152 1 8388608 (BSN.rpow_neg_quarter_mk qz117 (BSN.t_div_two_pi_nonneg qz116 589313 1000 qz119)) Ns276p771) rfl) (@Ns276p772 35184372088832 679780355141009 7938473952542720000 (BSN.correction_mk qz118 (BSN.cos_two_pi_p_ne_zero_mk qz116 589313 1000 9 qz119 rfl rfl (@BSN.floor_sqrt_eq_dec qz116 589313 1000 9 qz119 rfl rfl rfl))) (@Ns276p773 16777216 372385 2097152 108671701 3785359360000 15647384959375 35184372088832 679780355141009 7938473952542720000 Ns276p789 (Ns276p805 rfl) rfl)) 

noncomputable def Ns276p807 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (hardyZApproximantRS₀ qz116) Bool.false 575687507975566935855 73786976294838206464 23262741867299570065347 Ns276p700 (@Eq.refl Real (hardyZApproximantRS₀ qz116)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) (@HMul.hMul Real Real Real qz5 qz646 (Zeta.RiemannSiegel.correction qz118))) Bool.false 575687507975566935855 73786976294838206464 23262741867299570065347 Ns276p700 (BSN.hardyZApproximantRS₀_eq qz116 9 (@BSN.floor_sqrt_eq_dec qz116 589313 1000 9 qz119 rfl rfl rfl)) (@Ns276p702 575687507975566935855 73786976294838206464 23262741867299570065347 Ns276p700 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 9)) Bool.false 32124655 4194304 45961 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) (Ns276p765 (Ns276p764 rfl) rfl rfl)) (Ns276p806 rfl) rfl rfl)) 

theorem RS277to288.d52 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz116) Bool.false 575687507975566935855 73786976294838206464 23262741867299570065347 Ns276p700 := Ns276p807 

noncomputable def Ns276p808 := nat_lit 3378671994580865270195159040 

noncomputable abbrev qz761 := (Enclosure.sfrac Bool.false 590696 1000)

noncomputable abbrev qz653 := qz761

noncomputable abbrev qz457 := qz653

noncomputable abbrev qz134 := qz457

noncomputable abbrev qz762 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 590696 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz654 := qz762

noncomputable abbrev qz458 := qz654

noncomputable abbrev qz135 := qz458

noncomputable abbrev qz763 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 590696 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz655 := qz763

noncomputable abbrev qz459 := qz655

noncomputable abbrev qz136 := qz459

noncomputable abbrev qz656 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz135 qz9))

noncomputable def Ns276p809 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) (@HMul.hMul Real Real Real qz5 qz656 (Zeta.RiemannSiegel.correction qz136)) 10604445 33554432 23033 16777216 85863097313000532525 590295810358705651712 4451589798897815613627 Ns276p473 Ns276p808 

noncomputable def Ns276p810 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 590696 1000 115 160 134217728 67108864 2251799813685248 Bool.false 140411964181 1878 

noncomputable def Ns276p811 := Ns276p810 279097919 38 47453128 8 294906479 38 44739240 8 Bool.true 109579422 75404 Bool.true 204758055 Bool.true 55519077 7074237752028440 1 Bool.false 134080463 Bool.false Bool.false 122897811 Bool.false Bool.true 21208890 

noncomputable def Ns276p812 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 590696 1000 7 65 134217728 67108864 2251799813685248 Bool.false 140411964181 1878 

noncomputable def Ns276p813 := Ns276p812 240485871 38 54794152 8 261175631 38 50729528 8 Bool.true 114307782 56260 Bool.true 166276876 Bool.true 159569929 7074237752028440 1 Bool.false 126891168 Bool.false Bool.false 124548056 Bool.true Bool.true 109579422 

noncomputable def Ns276p814 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 590696 1000 144 60 134217728 67108864 2251799813685248 Bool.false 140411964181 1878 

noncomputable def Ns276p815 := Ns276p814 186065264 38 67108856 8 216015088 38 60023992 8 Bool.true 167027618 33199 Bool.false 144622162 Bool.false 162992911 7074237752028440 1 Bool.false 63554105 Bool.false Bool.false 46829498 Bool.false Bool.true 114307782 

noncomputable def Ns276p816 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 590696 1000 405 252 134217728 67108864 2251799813685248 Bool.false 140411964181 1878 

noncomputable def Ns276p817 := Ns276p816 93032624 38 94906264 8 147453232 38 77490640 16 Bool.true 134217720 1926 Bool.false 72336090 Bool.false 183093889 7074237752028440 1 Bool.false 68884775 Bool.true Bool.false 27537865 Bool.false Bool.true 167027618 

noncomputable def Ns276p818 := nat_lit 27485377002594020660436393813516750215048483318573987 

noncomputable def Ns276p819 := nat_lit 26272866959920321646185097786833177380026056704000 

noncomputable def Ns276p820 := nat_lit 34519315516836338501722541588480000 

noncomputable def Ns276p821 := nat_lit 122342570498214669740689442431708692480 

noncomputable abbrev qz657 := (@Eq.refl Real qz761)

noncomputable abbrev qz460 := qz657

noncomputable abbrev qz137 := qz460

noncomputable def Ns276p822 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz134 590696 1000 1395688057664 16000000 1181392 4000 2000 Ns276p820 Ns276p821 qz137 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns276p823 := nat_lit 36025633344840034760047190099252674841868348055321296240640 

noncomputable abbrev qz658 := (@HSub.hSub Real Real Real qz736 qz737 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz738 (@Nat.cast Real Real.instNatCast 1181392))))

noncomputable abbrev qz461 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 590696 4000) (Real.log (Enclosure.sfrac Bool.false 1395688057664 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz658))

noncomputable abbrev qz659 := (Enclosure.sfrac Bool.false 590696 2000)

noncomputable abbrev qz138 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz461 qz659) (@HMul.hMul Real Real Real qz346 qz659 (Real.log Real.pi)))

noncomputable def Ns276p824 := @Enclosure.Real.IsNear.addLit_ft_p qz138 (Enclosure.sfrac Bool.true Ns276p820 Ns276p821) 294465310925351889343 281474976710656000 1292407854552238769 92416000000000000000000 Ns276p820 Ns276p821 0 1 Ns276p823 

noncomputable def Ns276p825 := nat_lit 2470154062950894261757804544000 

noncomputable abbrev qz139 := (@HSub.hSub Real Real Real qz350 qz461 qz659)

noncomputable def Ns276p826 := @Enclosure.Real.IsNear.subLit_ff_p qz139 (@HMul.hMul Real Real Real qz5 qz659 (Real.log Real.pi)) 389630222003824568767 281474976710656000 1870925853010149 361000000000000000000 2836135359957 8388608000 73837 8388608000 Ns276p825 294465310925351889343 281474976710656000 

noncomputable abbrev qz140 := qz461

noncomputable def Ns276p827 := @Enclosure.Real.IsNear.subLit_ff_p qz140 qz659 94552658685072679411 56294995342131200 1870925853010149 361000000000000000000 590696 2000 0 1 155852088801529827506800 389630222003824568767 281474976710656000 1870925853010149 361000000000000000000 

noncomputable def Ns276p828 := nat_lit 106456829605245752823863716782014464 

noncomputable def Ns276p829 := nat_lit 27506228208972917574205440 

noncomputable def Ns276p830 := nat_lit 1203973093669814950193343453772286547575649374869790555330141446109348772926452837916222915587520593920 

noncomputable def Ns276p831 := nat_lit 8192909878401352145286745536145385966361586600595284333891175888432138473233024376710296187766308864 

noncomputable def Ns276p832 := nat_lit 22128241348686305039240621433706629007141692611733591195880356708463364285210537229139448954880 

noncomputable def Ns276p833 := BSN.log_dyadic_bound 347112057664 2444264057664 5 4 Ns276p830 67108864 28880000 Ns276p831 Ns276p832 19190079 2791376115328 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 347112057664) (BSN.artanhQ 2444264057664) 0 4 Ns276p831 Ns276p830 Ns276p832 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz462 := (Real.log (Enclosure.sfrac Bool.false 1395688057664 16000000))

noncomputable def Ns276p834 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 590696 4000) qz462 590696 4000 0 1 3202146409192695 281474976710656 781250361 22562500000000000 47287376883112204143 28147497671065600 57685182905157 11281250000000000000 (Enclosure.Real.IsNear.const Bool.false 590696 4000) (BSN.isNear_log_sfrac 1395688057664 16000000 3202146409192695 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1395688057664) qz353)) Bool.false Ns276p829 Ns276p92 1000000462080000 28880000000000000000000 3202146409192695 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1395688057664 16000000 16 2791376115328 2097152000000 19190079 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns276p833 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p835 := BSN.arctan_dyadic_bound_f 1000 1181392 1 0 8388608 3610000 0 1 1 0 1 1 7100 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1181392) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1181392) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns276p836 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1181392))) 884279719003555 562949953421312 1 2000000000000000 7100 8388608 1 3610000 7413878980401682186240 883803246069155 562949953421312 200000000361 722000000000000000 qz17 (Ns276p835 rfl) rfl rfl 

noncomputable abbrev qz463 := (@HMul.hMul Real Real Real qz584 qz589 qz658)

noncomputable abbrev qz141 := qz463

noncomputable abbrev qz464 := qz658

noncomputable abbrev qz142 := qz464

noncomputable def Ns276p837 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 590696 4000) qz462) qz141 47287376883112204143 28147497671065600 57685182905157 11281250000000000000 883803246069155 2251799813685248 200000000361 2888000000000000000 Ns276p828 94552658685072679411 56294995342131200 1870925853010149 361000000000000000000 (Ns276p834 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz142 1 4 0 1 883803246069155 562949953421312 200000000361 722000000000000000 883803246069155 2251799813685248 200000000361 2888000000000000000 qz361 Ns276p836 rfl) 

noncomputable def Ns276p838 := @Ns276p824 Ns276p818 Ns276p819 1292407854552238769 92416000000000000000000 (@Ns276p826 1292407854552238769 92416000000000000000000 (Ns276p827 (Ns276p837 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 590696 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz659 (Real.log Real.pi) 590696 2000 0 1 38410761 33554432 1 33554432 2836135359957 8388608000 73837 8388608000 (Enclosure.Real.IsNear.const Bool.false 590696 2000) RS277to288.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns276p820 Ns276p821) 

noncomputable def Ns276p839 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns276p818 Ns276p819 1292407854552238769 92416000000000000000000 8775747761 8388608 59 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz362 qz138 (Enclosure.sfrac Bool.true Ns276p820 Ns276p821)) Bool.false Ns276p818 Ns276p819 1292407854552238769 92416000000000000000000 Ns276p822 (Ns276p838 rfl rfl)) 

noncomputable def Ns276p840 := nat_lit 1899341598703537977556992 

noncomputable def Ns276p841 := nat_lit 857798738827074956163279965056375206795412322417259118244049147083597552190257992840040349448088625071908503034009152994501223608985521 

noncomputable def Ns276p842 := nat_lit 612405810616209836995420796662829121957762884972722539835345783771422981260946099008638599169620848640293328942415450554436659121 

noncomputable def Ns276p843 := nat_lit 4283659993755350567132736055963683437744677004494411881019626112778316685824125018835154480982561545171285120558667646196246023976232881 

noncomputable def Ns276p844 := BSN.sin_dyadic_bound_f 53982535027 34359738368 4 3 16777216 7227051 Ns276p841 Ns276p106 Ns276p842 Ns276p843 Ns276p109 Ns276p842 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53982535027) qz363 0 3 Ns276p841 Ns276p106 Ns276p842 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53982535027) qz364 0 3 Ns276p843 Ns276p109 Ns276p842 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p845 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz134) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8775747761) qz365) Bool.false 8775747761 8388608 59 4194304 Bool.true 16777215 16777216 1 3610000 (Ns276p839 rfl) (Enclosure.sfrac_false_div 8775747761 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8775747761) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns276p840) qz366) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 166 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q1 8775747761 8388608 226375608064910080 72057594037927936 166 Ns276p840 Ns276p104 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns276p840 Ns276p104 53982535027 34359738368 7227051 7220000 (Ns276p844 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p846 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns276p818 Ns276p819 1292407854552238769 92416000000000000000000 140411964181 134217728 1878 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz362 qz138 (Enclosure.sfrac Bool.true Ns276p820 Ns276p821)) Bool.false Ns276p818 Ns276p819 1292407854552238769 92416000000000000000000 Ns276p822 (Ns276p838 rfl rfl)) 

noncomputable def Ns276p847 := Ns276p817 33199 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 405 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 68884775 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 252 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 27537865 134217728) qz137 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) Bool.true 16777215 16777216 13574019 946339840000 134217720 134217728 1926 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 16777215 16777216 13574019 946339840000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz134) qz134) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 16777215 16777216 217184304 15141437440000 16777215 16777216 13574019 946339840000 (Ns276p845 rfl rfl) rfl)) rfl) (Ns276p846 rfl) RS277to288.d7 

noncomputable def Ns276p848 := nat_lit 26869126944496193628526959784170994626188056856967453865086471840000 

noncomputable def Ns276p849 := nat_lit 749618403737327640110554596582975712367864478438159392100000000 

noncomputable def Ns276p850 := nat_lit 70370309281979218115677096632053375393624886654330622150496407200000 

noncomputable def Ns276p851 := BSN.sin_dyadic_bound_f 72336090 134217728 3 2 134217728 67108864 Ns276p848 Ns276p137 Ns276p849 Ns276p850 Ns276p140 Ns276p849 68884775 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 72336090) qz367 0 2 Ns276p848 Ns276p137 Ns276p849 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 72336090) qz368 0 2 Ns276p850 Ns276p140 Ns276p849 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p852 := nat_lit 2366980852116824568120338315551880752942376836281408390500712315919337572612777430085443647171730803392001 

noncomputable def Ns276p853 := nat_lit 1419339184379466562002537779100683136362230151377164097082291656359987560031128380739212083839761921 

noncomputable def Ns276p854 := nat_lit 14339983927770022804690192110515338434992769675041679170443379020243604693425355890333858533111898658962945 

noncomputable def Ns276p855 := BSN.cos_dyadic_bound_f 183093889 134217728 4 3 134217728 67108864 Ns276p852 Ns276p116 Ns276p853 Ns276p854 Ns276p119 Ns276p853 27537865 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 183093889) qz369 0 3 Ns276p852 Ns276p116 Ns276p853 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 183093889) qz370 0 3 Ns276p854 Ns276p119 Ns276p853 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p856 := nat_lit 920221893883164568999763991246555448744618424889845799553314911618043402114415022735774407590094647463936 

noncomputable def Ns276p857 := nat_lit 83717874917044981391155837496051140967398686516765270891474147215033661558016372684501777429958656 

noncomputable def Ns276p858 := nat_lit 5579695100944607527579391996899328156998997409849463979112989788142615286933003382071093577081297859645440 

noncomputable def Ns276p859 := BSN.cos_dyadic_bound_f 144622162 134217728 4 3 134217728 67108864 Ns276p856 Ns276p116 Ns276p857 Ns276p858 Ns276p119 Ns276p857 63554105 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 144622162) qz369 0 3 Ns276p856 Ns276p116 Ns276p857 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 144622162) qz370 0 3 Ns276p858 Ns276p119 Ns276p857 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p860 := nat_lit 1485393827774759014693047196258500857131894333858970610391114193960446118081355322989314949398897060961601 

noncomputable def Ns276p861 := nat_lit 351580350009570948216495154038431622601310522428381159947309596967680512568224297242150547891379521 

noncomputable def Ns276p862 := nat_lit 9003620238920607566642834416246802208693659250171848918822040380177283499474918108693170700237174166478145 

noncomputable def Ns276p863 := BSN.cos_dyadic_bound_f 162992911 134217728 4 3 134217728 67108864 Ns276p860 Ns276p116 Ns276p861 Ns276p862 Ns276p119 Ns276p861 46829498 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 162992911) qz369 0 3 Ns276p860 Ns276p116 Ns276p861 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 162992911) qz370 0 3 Ns276p862 Ns276p119 Ns276p861 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p864 := Ns276p815 56260 BSN.abs_quadSignPos (BSN.cos_quad_nat0 144 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 63554105 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 46829498 134217728) qz137 rfl rfl (Ns276p847 RS277to288.d9 RS277to288.d11 RS277to288.d13 RS277to288.d17 (Ns276p851 rfl rfl) (Ns276p855 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns276p846 rfl) RS277to288.d19 RS277to288.d21 RS277to288.d23 RS277to288.d25 RS277to288.d17 (Ns276p859 rfl rfl) (Ns276p863 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns276p865 := nat_lit 750735414714813762899218216757503688896160782091769924464678466027520 

noncomputable def Ns276p866 := nat_lit 584325516058682381832955644341063075153710595763308735351582949376 

noncomputable def Ns276p867 := nat_lit 1965265749608036274213080068083576511653981754990066349931207705296896 

noncomputable def Ns276p868 := BSN.sin_dyadic_bound_f 166276876 134217728 3 2 134217728 67108864 Ns276p865 Ns276p137 Ns276p866 Ns276p867 Ns276p140 Ns276p866 126891168 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 166276876) qz367 0 2 Ns276p865 Ns276p137 Ns276p866 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 166276876) qz368 0 2 Ns276p867 Ns276p140 Ns276p866 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p869 := nat_lit 636667022454675787828953101144752855503527760819264333941363539285825 

noncomputable def Ns276p870 := nat_lit 420347447356531821207591830431838505699485235582951535359116285761 

noncomputable def Ns276p871 := nat_lit 1666780686752240297555779163844129740166678302240462762598704033666881 

noncomputable def Ns276p872 := BSN.sin_dyadic_bound_f 159569929 134217728 3 2 134217728 67108864 Ns276p869 Ns276p137 Ns276p870 Ns276p871 Ns276p140 Ns276p870 124548056 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 159569929) qz367 0 2 Ns276p869 Ns276p137 Ns276p870 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 159569929) qz368 0 2 Ns276p871 Ns276p140 Ns276p870 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p873 := Ns276p813 75404 BSN.abs_quadSignPos (BSN.cos_quad_nat3 7 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 126891168 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 65 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 124548056 134217728) qz137 rfl rfl (Ns276p864 rfl rfl) (Ns276p846 rfl) RS277to288.d27 RS277to288.d29 RS277to288.d31 RS277to288.d33 RS277to288.d17 (Ns276p868 rfl rfl) (Ns276p872 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p874 := nat_lit 9623201306932713892926758098002754717428090422862969932548002013968888808583146255117693281423429697790625 

noncomputable def Ns276p875 := nat_lit 5431151861205647859229346717940098517724180977572294154258972234416476431784765826390250957275390625 

noncomputable def Ns276p876 := nat_lit 48062802032988362056458646013829227804378264979734362345209059429714002131215474202857490972064295387390625 

noncomputable def Ns276p877 := BSN.sin_dyadic_bound_f 204758055 134217728 4 3 134217728 67108864 Ns276p874 Ns276p255 Ns276p875 Ns276p876 Ns276p258 Ns276p875 134080463 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 204758055) qz367 0 3 Ns276p874 Ns276p255 Ns276p875 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 204758055) qz368 0 3 Ns276p876 Ns276p258 Ns276p875 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p878 := nat_lit 5179947181262161982467532952985597118505019817910646549900932596961 

noncomputable def Ns276p879 := nat_lit 90268847812456095632593266691467060050589162446816651197203681 

noncomputable def Ns276p880 := nat_lit 15539661006090861035211333672423408421394958275407046016400403383521 

noncomputable def Ns276p881 := BSN.cos_dyadic_bound_f 55519077 134217728 3 2 134217728 67108864 Ns276p878 Ns276p131 Ns276p879 Ns276p880 Ns276p134 Ns276p879 122897811 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 55519077) qz369 0 2 Ns276p878 Ns276p131 Ns276p879 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 55519077) qz370 0 2 Ns276p880 Ns276p134 Ns276p879 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p882 := Ns276p811 92132 BSN.abs_quadSignPos (BSN.cos_quad_nat3 115 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 134080463 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 122897811 134217728) qz137 rfl rfl (Ns276p873 rfl) (Ns276p846 rfl) RS277to288.d35 RS277to288.d37 RS277to288.d39 RS277to288.d41 RS277to288.d17 (Ns276p877 rfl rfl) (Ns276p881 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p883 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) 21208890 134217728 92132 134217728 21208890 134217728 92132 134217728 5693218058403840 10604445 33554432 23033 16777216 (Ns276p882 rfl) 

noncomputable def Ns276p884 := @Enclosure.Real.IsNear.mulLit_tf qz656 (Zeta.RiemannSiegel.correction qz136) 2693977 8388608 1 8388608 31872245870325 70368744177664 1649753124718659 15876947905085440000 85863097313000532525 590295810358705651712 

noncomputable abbrev qz660 := (@HPow.hPow Real Real Real qz7 qz135 qz9)

noncomputable def Ns276p885 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz660 1 1 0 1 2693977 8388608 1 8388608 2693977 8388608 1 8388608 

noncomputable def Ns276p886 := @Enclosure.Real.IsNear.sqrt_image qz135 197157859149 2097152000 73837 2097152000 81335831 81335863 8388608 (@Enclosure.Real.IsNear.of_eq qz135 (@HMul.hMul Real Real Real qz5 qz134 qz3) Bool.false 197157859149 2097152000 73837 2097152000 (BSN.t_div_two_pi_mk qz134 590696 1000 qz137) (@Enclosure.Real.IsNear.mulLit_ff qz134 qz3 590696 1000 0 1 2670177 16777216 1 16777216 197157859149 2097152000 73837 2097152000 (Enclosure.Real.IsNear.const Bool.false 590696 1000) RS277to288.d44 rfl)) 

noncomputable abbrev qz764 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 590696 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz661 := qz764

noncomputable abbrev qz465 := qz661

noncomputable abbrev qz143 := qz465

noncomputable def Ns276p887 := @Enclosure.Real.IsNear.sqrt_image qz143 81335847 8388608 1 524288 26120765 26120771 8388608 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 162671694 16777216 32 16777216 81335847 8388608 1 524288 (Ns276p886 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns276p888 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz143) 408137 131072 3 8388608 2693976 2693978 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz143) Bool.false 52241536 16777216 6 16777216 408137 131072 3 8388608 (Ns276p887 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns276p889 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 5387954 16777216 2 16777216 2693977 8388608 1 8388608 (Ns276p888 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz466 := (@HMul.hMul Real Real Real qz584 qz582 qz655)

noncomputable abbrev qz144 := (Real.cos qz466)

noncomputable abbrev qz662 := (@HMul.hMul Real Real Real qz732 qz763 qz763)

noncomputable abbrev qz467 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz662 qz655) qz599)

noncomputable abbrev qz145 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz467))

noncomputable def Ns276p890 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz136) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz144) qz145) Bool.false 31872245870325 

noncomputable def Ns276p891 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz144) qz145 25199535 8388608 933 

noncomputable abbrev qz146 := (@Neg.neg Real Real.instNeg (Real.cos qz466))

noncomputable def Ns276p892 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz144) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz146)) Bool.true 25199535 8388608 933 8388608 (BSN.inv_eq_neg_inv_neg qz144) 

noncomputable def Ns276p893 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz146) Bool.false 50399070 16777216 1866 16777216 25199535 8388608 

noncomputable def Ns276p894 := @Enclosure.Real.IsNear.recentre' qz144 Bool.true 5584924 16777216 372998608 30282874880000 1396231 4194304 23312413 1892679680000 

noncomputable abbrev qz147 := qz466

noncomputable def Ns276p895 := @Enclosure.Real.IsNear.cos_image qz147 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4585449) (@Nat.cast Real Real.instNatCast 1048576)) Bool.false 4585449 1048576 101 8388608 Bool.true 5584924 16777216 1 

noncomputable def Ns276p896 := nat_lit 26986075412178499166016967 

noncomputable def Ns276p897 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz136 884279719003555 140737488355328 1 500000000000000 5838375 8388608 1 524288 5162756604437380423125 1180591620717411303424 Ns276p896 

noncomputable def Ns276p898 := @Enclosure.Real.IsNear.subLit_ff_p qz143 qz1 81335847 8388608 1 524288 9 1 0 1 5838375 5838375 8388608 1 

noncomputable def Ns276p899 := @Ns276p898 524288 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 162671694 16777216 32 16777216 81335847 8388608 1 524288 (Ns276p886 rfl rfl rfl rfl rfl rfl) rfl) qz377 

noncomputable def Ns276p900 := @Enclosure.Real.IsNear.recentre' qz147 Bool.false 5162756604437380423125 1180591620717411303424 Ns276p896 Ns276p556 4585449 1048576 101 8388608 (@Ns276p897 Ns276p556 RS277to288.d43 (Ns276p899 rfl rfl) rfl) 

noncomputable def Ns276p901 := nat_lit 7515264294379862861318244695865526065791005240033532224976600352018547864278661237190625 

noncomputable def Ns276p902 := nat_lit 10272663805758898827056669407346144916989005319989074993432409760091822211673000390625 

noncomputable def Ns276p903 := nat_lit 22525247555528070786300620748781885907539037709460618524942936236535459948412637710790625 

noncomputable def Ns276p904 := BSN.cos_dyadic_bound_f 42311691195 34359738368 3 2 16777216 7227051 Ns276p901 Ns276p173 Ns276p902 Ns276p903 Ns276p176 Ns276p902 5584924 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 42311691195) qz378 0 2 Ns276p901 Ns276p173 Ns276p902 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 42311691195) qz379 0 2 Ns276p903 Ns276p176 Ns276p902 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p905 := @Ns276p895 3610000 (Ns276p900 rfl) (Enclosure.sfrac_false_div 4585449 1048576) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4585449) (@Nat.cast Real Real.instNatCast 1048576)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 186088785842702928314368) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false 5584924 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 4585449 1048576 226375608064910080 72057594037927936 0 186088785842702928314368 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 5584924 16777216 186088785842702928314368 151115727451828646838272 42311691195 34359738368 7227051 7220000 (Ns276p904 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p906 := @Enclosure.Real.IsNear.inv_image qz146 1396231 4194304 23312413 1892679680000 25198602 25200468 8388608 (@Enclosure.Real.IsNear.neg qz144 Bool.true 1396231 4194304 23312413 1892679680000 (Ns276p894 (Ns276p905 rfl rfl) rfl)) 

noncomputable def Ns276p907 := Ns276p892 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz146) Bool.false 25199535 8388608 933 8388608 (@Ns276p893 933 8388608 (Ns276p906 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p908 := @Enclosure.Real.IsNear.recentre' qz145 Bool.true 1264795 8388608 

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz346 qz343 qz467)

noncomputable def Ns276p909 := @Enclosure.Real.IsNear.cos_image qz148 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 14446431)) qz365) Bool.true 14446431 8388608 

noncomputable def Ns276p910 := nat_lit 17055335596607764543730312845 

noncomputable def Ns276p911 := nat_lit 270742847942513262531388703119753 

noncomputable def Ns276p912 := @Enclosure.Real.IsNear.recentre' qz148 Bool.true Ns276p910 Ns276p793 Ns276p911 

noncomputable abbrev qz149 := qz467

noncomputable def Ns276p913 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz149 884279719003555 140737488355328 1 500000000000000 19287263102479 

noncomputable abbrev qz468 := (@HSub.hSub Real Real Real qz588 qz662 qz655)

noncomputable abbrev qz150 := qz468

noncomputable def Ns276p914 := @Enclosure.Real.IsNear.subLit_tf qz150 qz31 14889216591375 70368744177664 10032687 2199023255552 1 16 

noncomputable abbrev qz469 := qz662

noncomputable abbrev qz151 := qz469

noncomputable def Ns276p915 := @Enclosure.Real.IsNear.subLit_ff_n qz151 qz136 34086622640625 70368744177664 5838383 2199023255552 5838375 8388608 1 524288 

noncomputable def Ns276p916 := @Enclosure.Real.IsNear.mulLit_ff qz136 qz136 5838375 8388608 1 524288 5838375 8388608 1 524288 34086622640625 70368744177664 

noncomputable def Ns276p917 := nat_lit 21426772890817777807844656362840962500799372073264541201102452486608466671482614354340384641 

noncomputable def Ns276p918 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600 

noncomputable def Ns276p919 := nat_lit 82627918290921651240780281804710149693303065975795200538384138604701947958654378610561 

noncomputable def Ns276p920 := nat_lit 129537313976709066654147011875672496502485227243175691471384984853459909065332329991688589185 

noncomputable def Ns276p921 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600 

noncomputable def Ns276p922 := BSN.cos_dyadic_bound_t 14446431 8388608 4 3 8388608 3610000 Ns276p917 Ns276p918 Ns276p919 Ns276p920 Ns276p921 Ns276p919 1264795 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 14446431) (BSN.cosEvenQ 8388608) 0 3 Ns276p917 Ns276p918 Ns276p919 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 14446431) (BSN.cosOddQ 8388608) 0 3 Ns276p920 Ns276p921 Ns276p919 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p923 := @Ns276p908 878398608 30282874880000 1264795 8388608 54899913 1892679680000 (@Ns276p909 241 8388608 Bool.true 1264795 8388608 1 3610000 (@Ns276p912 Ns276p796 14446431 8388608 241 8388608 (@Ns276p913 70368744177664 10032687 2199023255552 Ns276p910 Ns276p793 Ns276p911 Ns276p796 RS277to288.d43 (@Ns276p914 0 1 308596209639664 19287263102479 70368744177664 10032687 2199023255552 (@Ns276p915 124899801412141056000 14889216591375 70368744177664 10032687 2199023255552 (@Ns276p916 5838383 2199023255552 (Ns276p899 rfl rfl) (Ns276p899 rfl rfl) rfl) (Ns276p899 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 14446431 8388608) (BSN.cos_neg_of_bound 14446431 8388608 Bool.true 1264795 8388608 1 3610000 (Ns276p922 rfl rfl)) rfl rfl) 

noncomputable def Ns276p924 := @Ns276p884 4451589798897815613627 Ns276p473 (Ns276p885 qz33 (@Enclosure.Real.IsNear.of_eq qz660 (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 2693977 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz135 (BSN.t_div_two_pi_nonneg qz134 590696 1000 qz137)) Ns276p889) rfl) (@Ns276p890 70368744177664 1649753124718659 15876947905085440000 (BSN.correction_mk qz136 (BSN.cos_two_pi_p_ne_zero_mk qz134 590696 1000 9 qz137 rfl rfl (@BSN.floor_sqrt_eq_dec qz134 590696 1000 9 qz137 rfl rfl rfl))) (@Ns276p891 8388608 1264795 8388608 54899913 1892679680000 31872245870325 70368744177664 1649753124718659 15876947905085440000 Ns276p907 (Ns276p923 rfl) rfl)) 

noncomputable def Ns276p925 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (hardyZApproximantRS₀ qz134) Bool.true 100692272024776496595 590295810358705651712 187298460347814285373627 Ns276p473 (@Eq.refl Real (hardyZApproximantRS₀ qz134)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) (@HMul.hMul Real Real Real qz5 qz656 (Zeta.RiemannSiegel.correction qz136))) Bool.true 100692272024776496595 590295810358705651712 187298460347814285373627 Ns276p473 (BSN.hardyZApproximantRS₀_eq qz134 9 (@BSN.floor_sqrt_eq_dec qz134 590696 1000 9 qz137 rfl rfl rfl)) (@Ns276p809 100692272024776496595 590295810358705651712 187298460347814285373627 Ns276p473 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 9)) Bool.true 10604445 33554432 23033 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) (Ns276p883 (Ns276p882 rfl) rfl rfl)) (Ns276p924 rfl) rfl rfl)) 

theorem RS277to288.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz134) Bool.true 100692272024776496595 590295810358705651712 187298460347814285373627 Ns276p473 := Ns276p925 

noncomputable def Ns276p926 := nat_lit 266370984424365925335040000 

noncomputable def Ns276p927 := nat_lit 42078413024909519566349008896 

noncomputable abbrev qz765 := (Enclosure.sfrac Bool.false 592078 1000)

noncomputable abbrev qz663 := qz765

noncomputable abbrev qz470 := qz663

noncomputable abbrev qz152 := qz470

noncomputable abbrev qz766 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 592078 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz664 := qz766

noncomputable abbrev qz471 := qz664

noncomputable abbrev qz153 := qz471

noncomputable abbrev qz767 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 592078 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz665 := qz767

noncomputable abbrev qz472 := qz665

noncomputable abbrev qz154 := qz472

noncomputable abbrev qz666 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz153 qz9))

noncomputable def Ns276p928 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (@HMul.hMul Real Real Real qz5 qz666 (Zeta.RiemannSiegel.correction qz154)) 25697319 67108864 92341 67108864 174945198574769384385 1180591620717411303424 10929786668907739520823 Ns276p926 Ns276p927 

noncomputable def Ns276p929 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 592078 1000 115 160 134217728 67108864 2251799813685248 Bool.false 140833450117 1882 

noncomputable def Ns276p930 := Ns276p929 279097919 38 47453128 8 294906479 38 44739240 8 Bool.true 62076451 75574 Bool.true 168985443 Bool.true 41593895 7074237752028440 1 Bool.false 127747925 Bool.false Bool.false 127824196 Bool.false Bool.false 25697319 

noncomputable def Ns276p931 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 592078 1000 7 65 134217728 67108864 2251799813685248 Bool.false 140833450117 1882 

noncomputable def Ns276p932 := Ns276p931 240485871 38 54794152 8 261175631 38 50729528 8 Bool.true 57739574 56386 Bool.true 77142414 Bool.true 99028715 7074237752028440 1 Bool.false 72964759 Bool.false Bool.false 90285245 Bool.true Bool.true 62076451 

noncomputable def Ns276p933 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 592078 1000 145 61 134217728 67108864 2251799813685248 Bool.false 140833450117 1882 

noncomputable def Ns276p934 := Ns276p933 186065264 38 67108856 8 216015088 38 60023992 8 Bool.false 18939212 33272 Bool.false 98137189 Bool.false 75117282 7074237752028440 1 Bool.false 89623587 Bool.true Bool.false 71256774 Bool.true Bool.true 57739574 

noncomputable def Ns276p935 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 592078 1000 406 253 134217728 67108864 2251799813685248 Bool.false 140833450117 1882 

noncomputable def Ns276p936 := Ns276p935 93032624 38 94906264 8 147453232 38 77490640 16 Bool.false 134217664 1926 Bool.false 154422226 Bool.false 189970745 7074237752028440 1 Bool.false 54760676 Bool.true Bool.false 132600281 Bool.true Bool.false 18939212 

noncomputable def Ns276p937 := nat_lit 3578514102297416468445311816817489342334856547997261871 

noncomputable def Ns276p938 := nat_lit 3410411603389969318626081968178739881298926501888000 

noncomputable def Ns276p939 := nat_lit 34925018346326323296391616496640000 

noncomputable def Ns276p940 := nat_lit 124070051365923766520648567827401707520 

noncomputable abbrev qz667 := (@Eq.refl Real qz765)

noncomputable abbrev qz473 := qz667

noncomputable abbrev qz155 := qz473

noncomputable def Ns276p941 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz152 592078 1000 1402226432336 16000000 1184156 4000 2000 Ns276p939 Ns276p940 qz155 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns276p942 := nat_lit 73287968815051089273759986008422181731017862102983923118080 

noncomputable abbrev qz668 := (@HSub.hSub Real Real Real qz736 qz737 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz738 (@Nat.cast Real Real.instNatCast 1184156))))

noncomputable abbrev qz474 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 592078 4000) (Real.log (Enclosure.sfrac Bool.false 1402226432336 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz668))

noncomputable abbrev qz669 := (Enclosure.sfrac Bool.false 592078 2000)

noncomputable abbrev qz156 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz474 qz669) (@HMul.hMul Real Real Real qz346 qz669 (Real.log Real.pi)))

noncomputable def Ns276p943 := @Enclosure.Real.IsNear.addLit_ft_p qz156 (Enclosure.sfrac Bool.true Ns276p939 Ns276p940) 590698461629051273779 562949953421312000 5181666460633317043 369664000000000000000000 Ns276p939 Ns276p940 0 1 Ns276p942 

noncomputable def Ns276p944 := nat_lit 19820551363236610190530838528000 

noncomputable abbrev qz157 := (@HSub.hSub Real Real Real qz350 qz474 qz669)

noncomputable def Ns276p945 := @Enclosure.Real.IsNear.subLit_ff_p qz157 (@HMul.hMul Real Real Real qz5 qz669 (Real.log Real.pi)) 781473581899105403443 562949953421312000 1875244605005757 361000000000000000000 11371083275679 33554432000 296039 33554432000 Ns276p944 590698461629051273779 562949953421312000 

noncomputable def Ns276p946 := nat_lit 1562947163798210806886000 

noncomputable abbrev qz158 := qz474

noncomputable def Ns276p947 := @Enclosure.Real.IsNear.subLit_ff_p qz158 qz669 948128723159997186611 562949953421312000 1875244605005757 361000000000000000000 592078 2000 0 1 Ns276p946 781473581899105403443 562949953421312000 1875244605005757 361000000000000000000 

noncomputable def Ns276p948 := nat_lit 2134996082161313745179117655873814528 

noncomputable def Ns276p949 := nat_lit 27517528677186712641732608 

noncomputable def Ns276p950 := nat_lit 1229980510589366335754530919263600822737803524336546575294886025757782302462323230896471945647142993920 

noncomputable def Ns276p951 := nat_lit 8645337935587635316294204939535679934172447039342640030312682247785428285311535445217804319524388864 

noncomputable def Ns276p952 := nat_lit 25691108649804449333354710886154099529157905806766542591079023312738316781746375971264402554880 

noncomputable def Ns276p953 := BSN.log_dyadic_bound 353650432336 2450802432336 5 4 Ns276p950 67108864 28880000 Ns276p951 Ns276p952 19503730 2804452864672 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 353650432336) (BSN.artanhQ 2450802432336) 0 4 Ns276p951 Ns276p950 Ns276p952 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz475 := (Real.log (Enclosure.sfrac Bool.false 1402226432336 16000000))

noncomputable def Ns276p954 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 592078 4000) qz475 592078 4000 0 1 3203461956836599 281474976710656 781250361 22562500000000000 948349674239949931361 562949953421312000 12172661874741 2375000000000000000 (Enclosure.Real.IsNear.const Bool.false 592078 4000) (BSN.isNear_log_sfrac 1402226432336 16000000 3203461956836599 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1402226432336) qz353)) Bool.false Ns276p949 Ns276p92 1000000462080000 28880000000000000000000 3203461956836599 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1402226432336 16000000 16 2804452864672 2097152000000 19503730 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns276p953 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p955 := BSN.arctan_dyadic_bound_f 1000 1184156 1 0 8388608 3610000 0 1 1 0 1 1 7084 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1184156) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1184156) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns276p956 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1184156))) 884279719003555 562949953421312 1 2000000000000000 7084 8388608 1 3610000 7413887987600936927232 883804319810979 562949953421312 200000000361 722000000000000000 qz17 (Ns276p955 rfl) rfl rfl 

noncomputable abbrev qz476 := (@HMul.hMul Real Real Real qz584 qz589 qz668)

noncomputable abbrev qz159 := qz476

noncomputable abbrev qz477 := qz668

noncomputable abbrev qz160 := qz477

noncomputable def Ns276p957 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 592078 4000) qz475) qz159 948349674239949931361 562949953421312000 12172661874741 2375000000000000000 883804319810979 2251799813685248 200000000361 2888000000000000000 Ns276p948 948128723159997186611 562949953421312000 1875244605005757 361000000000000000000 (Ns276p954 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz160 1 4 0 1 883804319810979 562949953421312 200000000361 722000000000000000 883804319810979 2251799813685248 200000000361 2888000000000000000 qz361 Ns276p956 rfl) 

noncomputable def Ns276p958 := @Ns276p943 Ns276p937 Ns276p938 5181666460633317043 369664000000000000000000 (@Ns276p945 5181666460633317043 369664000000000000000000 (Ns276p947 (Ns276p957 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 592078 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz669 (Real.log Real.pi) 592078 2000 0 1 38410761 33554432 1 33554432 11371083275679 33554432000 296039 33554432000 (Enclosure.Real.IsNear.const Bool.false 592078 2000) RS277to288.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns276p939 Ns276p940) 

noncomputable def Ns276p959 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns276p937 Ns276p938 5181666460633317043 369664000000000000000000 1100261329 1048576 59 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz362 qz156 (Enclosure.sfrac Bool.true Ns276p939 Ns276p940)) Bool.false Ns276p937 Ns276p938 5181666460633317043 369664000000000000000000 Ns276p941 (Ns276p958 rfl rfl)) 

noncomputable def Ns276p960 := nat_lit 855006085948613370158833813324324129491907709119505580246059714820963006791525143222971060944670718879987873977526330222910105692939201 

noncomputable def Ns276p961 := nat_lit 606455904371885582497337809796083847516782811541826098335417032234613352337403871568945271791006570724045372482702495680015115201 

noncomputable def Ns276p962 := nat_lit 4269731340281939059879711539389469806505269486716759806788410875140296251495267898490586291095518208686840153478094838882988517951284161 

noncomputable def Ns276p963 := BSN.sin_dyadic_bound_f 53938633007 34359738368 4 3 16777216 7227051 Ns276p960 Ns276p106 Ns276p961 Ns276p962 Ns276p109 Ns276p961 16777208 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53938633007) qz363 0 3 Ns276p960 Ns276p106 Ns276p961 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53938633007) qz364 0 3 Ns276p962 Ns276p109 Ns276p961 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p964 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz152) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1100261329) (@Nat.cast Real Real.instNatCast 1048576)) Bool.false 1100261329 1048576 59 4194304 Bool.false 16777208 16777216 1 3610000 (Ns276p959 rfl) (Enclosure.sfrac_false_div 1100261329 1048576) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1100261329) (@Nat.cast Real Real.instNatCast 1048576)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 237224616711276124438528) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false 16777208 16777216 166 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q3 1100261329 1048576 226375608064910080 72057594037927936 166 237224616711276124438528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777208 16777216 237224616711276124438528 151115727451828646838272 53938633007 34359738368 7227051 7220000 (Ns276p963 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p965 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns276p937 Ns276p938 5181666460633317043 369664000000000000000000 140833450117 134217728 1882 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz362 qz156 (Enclosure.sfrac Bool.true Ns276p939 Ns276p940)) Bool.false Ns276p937 Ns276p938 5181666460633317043 369664000000000000000000 Ns276p941 (Ns276p958 rfl rfl)) 

noncomputable def Ns276p966 := Ns276p936 33272 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 406 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 54760676 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 253 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132600281 134217728) qz155 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) Bool.false 2097151 2097152 13574019 946339840000 134217664 134217728 1926 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 2097151 2097152 13574019 946339840000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz152) qz152) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 16777208 16777216 217184304 15141437440000 2097151 2097152 13574019 946339840000 (Ns276p964 rfl rfl) rfl)) rfl) (Ns276p965 rfl) RS277to288.d7 

noncomputable def Ns276p967 := nat_lit 1196456259402142346289532922973238242050018318405881170554352962914412006878608174524612901796258533216256 

noncomputable def Ns276p968 := nat_lit 183872890104733519158084037907977373868587487056420260895383301008593642233039847715166522535448576 

noncomputable def Ns276p969 := nat_lit 7253458486015522631080520646988766410246833960115070425703304213024784345588367474243424468636903348244480 

noncomputable def Ns276p970 := BSN.cos_dyadic_bound_f 154422226 134217728 4 3 134217728 67108864 Ns276p967 Ns276p116 Ns276p968 Ns276p969 Ns276p119 Ns276p968 54760676 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 154422226) qz369 0 3 Ns276p967 Ns276p116 Ns276p968 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 154422226) qz370 0 3 Ns276p969 Ns276p119 Ns276p968 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p971 := nat_lit 7126908303505945922521530562331763705485941000762477226673768211037957837258136450379503878094090851790625 

noncomputable def Ns276p972 := nat_lit 2209228873480964135309491751056347531510857784806071036879143367532023903262370664222169238525390625 

noncomputable def Ns276p973 := nat_lit 35605335773099845475031491296367192893666529201802350772070347504853945953018432265638370821131996157390625 

noncomputable def Ns276p974 := BSN.sin_dyadic_bound_f 189970745 134217728 4 3 134217728 67108864 Ns276p971 Ns276p255 Ns276p972 Ns276p973 Ns276p258 Ns276p972 132600281 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 189970745) qz367 0 3 Ns276p971 Ns276p255 Ns276p972 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 189970745) qz368 0 3 Ns276p973 Ns276p258 Ns276p972 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p975 := nat_lit 91032573702404316970524598288503950227889675626994111116340874972385 

noncomputable def Ns276p976 := nat_lit 8603376178016679119699668614408849872438248665256108023542189281 

noncomputable def Ns276p977 := nat_lit 238404716135342136489942053196896541030393774239526543034568937573601 

noncomputable def Ns276p978 := BSN.sin_dyadic_bound_f 98137189 134217728 3 2 134217728 67108864 Ns276p975 Ns276p137 Ns276p976 Ns276p977 Ns276p140 Ns276p976 89623587 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 98137189) qz367 0 2 Ns276p975 Ns276p137 Ns276p976 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 98137189) qz368 0 2 Ns276p977 Ns276p140 Ns276p976 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p979 := nat_lit 31246031756416106041965278279210543056576034144809044680897875902720 

noncomputable def Ns276p980 := nat_lit 1013722117935984979908476349276507185982418764681419529912811776 

noncomputable def Ns276p981 := nat_lit 81833203811946476610417781769557355565112308367928489961207911383296 

noncomputable def Ns276p982 := BSN.sin_dyadic_bound_f 75117282 134217728 3 2 134217728 67108864 Ns276p979 Ns276p137 Ns276p980 Ns276p981 Ns276p140 Ns276p980 71256774 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 75117282) qz367 0 2 Ns276p979 Ns276p137 Ns276p980 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 75117282) qz368 0 2 Ns276p981 Ns276p140 Ns276p980 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p983 := Ns276p934 56386 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 145 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 89623587 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 71256774 134217728) qz155 rfl rfl (Ns276p966 RS277to288.d9 RS277to288.d11 RS277to288.d13 RS277to288.d17 (Ns276p970 rfl rfl) (Ns276p974 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns276p965 rfl) RS277to288.d19 RS277to288.d21 RS277to288.d23 RS277to288.d25 RS277to288.d17 (Ns276p978 rfl rfl) (Ns276p982 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns276p984 := nat_lit 34754407642736613338384767040153893957192258000086553642375370031360 

noncomputable def Ns276p985 := nat_lit 1254139366287550935790379404332945186313938509197765893001625856 

noncomputable def Ns276p986 := nat_lit 91021418076764759851397395919462707024249500766449891728108728402176 

noncomputable def Ns276p987 := BSN.sin_dyadic_bound_f 77142414 134217728 3 2 134217728 67108864 Ns276p984 Ns276p137 Ns276p985 Ns276p986 Ns276p140 Ns276p985 72964759 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 77142414) qz367 0 2 Ns276p984 Ns276p137 Ns276p985 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 77142414) qz368 0 2 Ns276p986 Ns276p140 Ns276p985 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p988 := nat_lit 94386189135557532848301295844459059335288021374885596917584830230625 

noncomputable def Ns276p989 := nat_lit 9248880098426272173457402898761648110264105399798412436250390625 

noncomputable def Ns276p990 := nat_lit 247186949549157991114413034273651922257385342668338794497349197590625 

noncomputable def Ns276p991 := BSN.sin_dyadic_bound_f 99028715 134217728 3 2 134217728 67108864 Ns276p988 Ns276p137 Ns276p989 Ns276p990 Ns276p140 Ns276p989 90285245 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 99028715) qz367 0 2 Ns276p988 Ns276p137 Ns276p989 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 99028715) qz368 0 2 Ns276p990 Ns276p140 Ns276p989 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p992 := Ns276p932 75574 BSN.abs_quadSignPos (BSN.cos_quad_nat3 7 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 72964759 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 65 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 90285245 134217728) qz155 rfl rfl (Ns276p983 rfl rfl) (Ns276p965 rfl) RS277to288.d27 RS277to288.d29 RS277to288.d31 RS277to288.d33 RS277to288.d17 (Ns276p987 rfl rfl) (Ns276p991 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p993 := nat_lit 800901717107262084952957705544068874871711509485272999741613221098145 

noncomputable def Ns276p994 := nat_lit 664958216291270303993173399976450049530629539382435185510294500001 

noncomputable def Ns276p995 := nat_lit 2096523136264071975336995519491647086488575791302429151880065578447521 

noncomputable def Ns276p996 := BSN.sin_dyadic_bound_f 168985443 134217728 3 2 134217728 67108864 Ns276p993 Ns276p137 Ns276p994 Ns276p995 Ns276p140 Ns276p994 127747925 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 168985443) qz367 0 2 Ns276p993 Ns276p137 Ns276p994 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 168985443) qz368 0 2 Ns276p995 Ns276p140 Ns276p994 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p997 := nat_lit 2993080273112288942420504550625 

noncomputable def Ns276p998 := BSN.cos_dyadic_bound_f 41593895 134217728 2 1 134217728 67108864 Ns276p997 Ns276p122 Ns276p997 Ns276p997 Ns276p123 Ns276p997 127824196 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 41593895) qz369 0 1 Ns276p997 Ns276p122 Ns276p997 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 41593895) qz370 0 1 Ns276p997 Ns276p123 Ns276p997 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p999 := Ns276p930 92341 BSN.abs_quadSignPos (BSN.cos_quad_nat3 115 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 127747925 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 127824196 134217728) qz155 rfl rfl (Ns276p992 rfl) (Ns276p965 rfl) RS277to288.d35 RS277to288.d37 RS277to288.d39 RS277to288.d41 RS277to288.d17 (Ns276p996 rfl rfl) (Ns276p998 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p1000 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) 25697319 134217728 92341 134217728 25697319 134217728 92341 134217728 6898071543742464 25697319 67108864 92341 67108864 (Ns276p999 rfl) 

noncomputable def Ns276p1001 := @Enclosure.Real.IsNear.mulLit_tf qz666 (Zeta.RiemannSiegel.correction qz154) 5384807 16777216 1 16777216 32488666460055 70368744177664 2028383632905331 15876947905085440000 174945198574769384385 1180591620717411303424 

noncomputable abbrev qz670 := (@HPow.hPow Real Real Real qz7 qz153 qz9)

noncomputable def Ns276p1002 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz670 1 1 0 1 5384807 16777216 1 16777216 5384807 16777216 1 16777216 

noncomputable def Ns276p1003 := @Enclosure.Real.IsNear.sqrt_image qz153 790476528903 8388608000 296039 8388608000 81430923 81430954 8388608 (@Enclosure.Real.IsNear.of_eq qz153 (@HMul.hMul Real Real Real qz5 qz152 qz3) Bool.false 790476528903 8388608000 296039 8388608000 (BSN.t_div_two_pi_mk qz152 592078 1000 qz155) (@Enclosure.Real.IsNear.mulLit_ff qz152 qz3 592078 1000 0 1 2670177 16777216 1 16777216 790476528903 8388608000 296039 8388608000 (Enclosure.Real.IsNear.const Bool.false 592078 1000) RS277to288.d44 rfl)) 

noncomputable abbrev qz768 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 592078 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz671 := qz768

noncomputable abbrev qz478 := qz671

noncomputable abbrev qz161 := qz478

noncomputable def Ns276p1004 := @Enclosure.Real.IsNear.sqrt_image qz161 162861877 16777216 31 16777216 26136030 26136036 8388608 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 162861877 16777216 31 16777216 162861877 16777216 31 16777216 (Ns276p1003 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns276p1005 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz161) 26136033 8388608 3 8388608 2692403 2692404 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz161) Bool.false 52272066 16777216 6 16777216 26136033 8388608 3 8388608 (Ns276p1004 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns276p1006 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 5384807 16777216 1 16777216 5384807 16777216 1 16777216 (Ns276p1005 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz479 := (@HMul.hMul Real Real Real qz584 qz582 qz665)

noncomputable abbrev qz162 := (Real.cos qz479)

noncomputable abbrev qz672 := (@HMul.hMul Real Real Real qz732 qz767 qz767)

noncomputable abbrev qz480 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz672 qz665) qz599)

noncomputable abbrev qz163 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz480))

noncomputable def Ns276p1007 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz154) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz162) qz163) Bool.false 32488666460055 

noncomputable def Ns276p1008 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz162) qz163 63325179 16777216 2845 

noncomputable abbrev qz164 := (@Neg.neg Real Real.instNeg (Real.cos qz479))

noncomputable def Ns276p1009 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz162) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz164)) Bool.true 63325179 16777216 2845 16777216 (BSN.inv_eq_neg_inv_neg qz162) 

noncomputable def Ns276p1010 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz164) Bool.false 63325179 16777216 2845 16777216 63325179 16777216 

noncomputable def Ns276p1011 := @Enclosure.Real.IsNear.recentre' qz162 Bool.true 4444914 16777216 720727216 60565749760000 2222457 8388608 45045451 3785359360000 

noncomputable abbrev qz165 := qz479

noncomputable def Ns276p1012 := @Enclosure.Real.IsNear.cos_image qz165 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 74562139) qz376) Bool.false 74562139 16777216 195 16777216 Bool.true 4444914 16777216 1 

noncomputable def Ns276p1013 := nat_lit 836568337782301587387884313 

noncomputable def Ns276p1014 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz154 884279719003555 140737488355328 1 500000000000000 11866933 16777216 31 16777216 10493688178674013946815 2361183241434822606848 Ns276p1013 

noncomputable def Ns276p1015 := @Enclosure.Real.IsNear.subLit_ff_p qz161 qz1 162861877 16777216 31 16777216 9 1 0 1 11866933 11866933 16777216 31 

noncomputable def Ns276p1016 := @Ns276p1015 16777216 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 162861877 16777216 31 16777216 162861877 16777216 31 16777216 (Ns276p1003 rfl rfl rfl rfl rfl rfl) rfl) qz377 

noncomputable def Ns276p1017 := @Enclosure.Real.IsNear.recentre' qz165 Bool.false 10493688178674013946815 2361183241434822606848 Ns276p1013 Ns276p166 74562139 16777216 195 16777216 (@Ns276p1014 Ns276p166 RS277to288.d43 (Ns276p1016 rfl rfl) rfl) 

noncomputable def Ns276p1018 := nat_lit 3149631738050431206555648 

noncomputable def Ns276p1019 := nat_lit 155879262641081587450065885743997795263707682538137333578147523198788166361289648157246345939341406844145246020611877385846021168140625 

noncomputable def Ns276p1020 := nat_lit 1296985566167364170939292694987530979374979352933922598450371085822004482258776525817524027815363891144507173707470555812298386676121600 

noncomputable def Ns276p1021 := nat_lit 64648690196527808427788283575134833022614466183453429405319849624428555361908610776851247940451739658194544930996273437744140625 

noncomputable def Ns276p1022 := nat_lit 944588464736399321421486290832605053188394911263644350775716054904149644327621844412337488529135659792798597302889001926480623049740625 

noncomputable def Ns276p1023 := nat_lit 118025686521230139555475635243865319123123121116986956458983768809802407885548663849394686531198114094150152807379820578919153187527065600 

noncomputable def Ns276p1024 := BSN.cos_dyadic_bound_f 44758959035 34359738368 4 3 16777216 7227051 Ns276p1019 Ns276p1020 Ns276p1021 Ns276p1022 Ns276p1023 Ns276p1021 4444914 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 44758959035) qz378 0 3 Ns276p1019 Ns276p1020 Ns276p1021 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 44758959035) qz379 0 3 Ns276p1022 Ns276p1023 Ns276p1021 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1025 := @Ns276p1012 3610000 (Ns276p1017 rfl) (Enclosure.sfrac_false_div 74562139 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 74562139) qz376) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns276p1018) qz380) 226375608064910080 72057594037927936 Bool.false 4444914 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 74562139 16777216 226375608064910080 72057594037927936 0 Ns276p1018 Ns276p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 4444914 16777216 Ns276p1018 Ns276p92 44758959035 34359738368 7227051 7220000 (Ns276p1024 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p1026 := @Enclosure.Real.IsNear.inv_image qz164 2222457 8388608 45045451 3785359360000 31661167 31664012 8388608 (@Enclosure.Real.IsNear.neg qz162 Bool.true 2222457 8388608 45045451 3785359360000 (Ns276p1011 (Ns276p1025 rfl rfl) rfl)) 

noncomputable def Ns276p1027 := Ns276p1009 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz164) Bool.false 63325179 16777216 2845 16777216 (@Ns276p1010 2845 16777216 (Ns276p1026 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p1028 := @Enclosure.Real.IsNear.recentre' qz163 Bool.true 1026090 8388608 

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz346 qz343 qz480)

noncomputable def Ns276p1029 := @Enclosure.Real.IsNear.cos_image qz166 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 28410921)) qz376) Bool.true 28410921 16777216 

noncomputable def Ns276p1030 := nat_lit 67083392003058415445300497525 

noncomputable def Ns276p1031 := nat_lit 33890314460643092180489604873649761 

noncomputable def Ns276p1032 := @Enclosure.Real.IsNear.recentre' qz166 Bool.true Ns276p1030 Ns276p184 Ns276p1031 

noncomputable abbrev qz167 := qz480

noncomputable def Ns276p1033 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz167 884279719003555 140737488355328 1 500000000000000 75862185416455 

noncomputable abbrev qz481 := (@HSub.hSub Real Real Real qz588 qz672 qz665)

noncomputable abbrev qz168 := qz481

noncomputable def Ns276p1034 := @Enclosure.Real.IsNear.subLit_tf qz168 qz31 58269999372039 281474976710656 1255844503 281474976710656 1 16 

noncomputable abbrev qz482 := qz672

noncomputable abbrev qz169 := qz482

noncomputable def Ns276p1035 := @Enclosure.Real.IsNear.subLit_ff_n qz169 qz154 140824098826489 281474976710656 735750807 281474976710656 11866933 16777216 31 16777216 

noncomputable def Ns276p1036 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz154 11866933 16777216 31 16777216 11866933 16777216 31 16777216 140824098826489 281474976710656 

noncomputable def Ns276p1037 := nat_lit 82025387016091376783096502071480756316028588842032818081178452960270625136159696172869104244321 

noncomputable def Ns276p1038 := nat_lit 276581896540979926971646633568867244402985672693748295523104470605094769822140673564153441 

noncomputable def Ns276p1039 := nat_lit 496003294608939931968561159332808523831468402046743529031153438689661434000861248803388072990305 

noncomputable def Ns276p1040 := BSN.cos_dyadic_bound_t 28410921 16777216 4 3 8388608 3610000 Ns276p1037 Ns276p193 Ns276p1038 Ns276p1039 Ns276p196 Ns276p1038 1026090 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 28410921) qz600 0 3 Ns276p1037 Ns276p193 Ns276p1038 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 28410921) (BSN.cosOddQ 16777216) 0 3 Ns276p1039 Ns276p196 Ns276p1038 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1041 := @Ns276p1028 1717087216 60565749760000 513045 4194304 107317951 3785359360000 (@Ns276p1029 471 16777216 Bool.true 1026090 8388608 1 3610000 (@Ns276p1032 Ns276p187 28410921 16777216 471 16777216 (@Ns276p1033 281474976710656 1255844503 281474976710656 Ns276p1030 Ns276p184 Ns276p1031 Ns276p187 RS277to288.d43 (@Ns276p1034 0 1 1213794966663280 75862185416455 281474976710656 1255844503 281474976710656 (@Ns276p1035 977608365784562663424 58269999372039 281474976710656 1255844503 281474976710656 (@Ns276p1036 735750807 281474976710656 (Ns276p1016 rfl rfl) (Ns276p1016 rfl rfl) rfl) (Ns276p1016 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 28410921 16777216) (BSN.cos_neg_of_bound 28410921 16777216 Bool.true 1026090 8388608 1 3610000 (Ns276p1040 rfl rfl)) rfl rfl) 

noncomputable def Ns276p1042 := @Ns276p1001 10929786668907739520823 Ns276p926 (Ns276p1002 qz33 (@Enclosure.Real.IsNear.of_eq qz670 (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 5384807 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz153 (BSN.t_div_two_pi_nonneg qz152 592078 1000 qz155)) Ns276p1006) rfl) (@Ns276p1007 70368744177664 2028383632905331 15876947905085440000 (BSN.correction_mk qz154 (BSN.cos_two_pi_p_ne_zero_mk qz152 592078 1000 9 qz155 rfl rfl (@BSN.floor_sqrt_eq_dec qz152 592078 1000 9 qz155 rfl rfl rfl))) (@Ns276p1008 16777216 513045 4194304 107317951 3785359360000 32488666460055 70368744177664 2028383632905331 15876947905085440000 Ns276p1027 (Ns276p1041 rfl) rfl)) 

noncomputable def Ns276p1043 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (hardyZApproximantRS₀ qz152) Bool.false 627017215265475505089 1180591620717411303424 377453098294781393280823 Ns276p926 (@Eq.refl Real (hardyZApproximantRS₀ qz152)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (@HMul.hMul Real Real Real qz5 qz666 (Zeta.RiemannSiegel.correction qz154))) Bool.false 627017215265475505089 1180591620717411303424 377453098294781393280823 Ns276p926 (BSN.hardyZApproximantRS₀_eq qz152 9 (@BSN.floor_sqrt_eq_dec qz152 592078 1000 9 qz155 rfl rfl rfl)) (@Ns276p928 627017215265475505089 1180591620717411303424 377453098294781393280823 Ns276p926 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 9)) Bool.false 25697319 67108864 92341 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (Ns276p1000 (Ns276p999 rfl) rfl rfl)) (Ns276p1042 rfl) rfl rfl)) 

theorem RS277to288.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz152) Bool.false 627017215265475505089 1180591620717411303424 377453098294781393280823 Ns276p926 := Ns276p1043 

noncomputable def Ns276p1044 := nat_lit 2663709844243659253350400 

noncomputable def Ns276p1045 := nat_lit 56982976532048023620356669440 

noncomputable abbrev qz769 := (Enclosure.sfrac Bool.false 593460 1000)

noncomputable abbrev qz673 := qz769

noncomputable abbrev qz483 := qz673

noncomputable abbrev qz170 := qz483

noncomputable abbrev qz770 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 593460 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz674 := qz770

noncomputable abbrev qz484 := qz674

noncomputable abbrev qz171 := qz484

noncomputable abbrev qz771 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 593460 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz675 := qz771

noncomputable abbrev qz485 := qz675

noncomputable abbrev qz172 := qz485

noncomputable abbrev qz676 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz171 qz9))

noncomputable def Ns276p1046 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) (@HMul.hMul Real Real Real qz5 qz676 (Zeta.RiemannSiegel.correction qz172)) 106672465 67108864 92563 67108864 89188406438941396135 590295810358705651712 154383604266590384599 Ns276p1044 Ns276p1045 

noncomputable def Ns276p1047 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 593460 1000 115 160 134217728 67108864 2251799813685248 Bool.false 141255152308 1887 

noncomputable def Ns276p1048 := Ns276p1047 279097919 38 47453128 8 294906479 38 44739240 8 Bool.true 190174632 75757 Bool.true 132996576 Bool.true 27452458 7074237752028440 1 Bool.false 112275867 Bool.false Bool.false 131419983 Bool.false Bool.true 106672465 

noncomputable def Ns276p1049 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 593460 1000 6 65 134217728 67108864 2251799813685248 Bool.false 141255152308 1887 

noncomputable def Ns276p1050 := Ns276p1049 240485871 38 54794152 8 261175631 38 50729528 8 Bool.true 170927536 56523 Bool.true 198620410 Bool.true 38271246 7074237752028440 1 Bool.false 12191476 Bool.true Bool.false 37754733 Bool.true Bool.true 190174632 

noncomputable def Ns276p1051 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 593460 1000 146 61 134217728 67108864 2251799813685248 Bool.false 141255152308 1887 

noncomputable def Ns276p1052 := Ns276p1051 186065264 38 67108856 8 216015088 38 60023992 8 Bool.true 49005655 33354 Bool.false 51868471 Bool.false 198286621 7074237752028440 1 Bool.false 124319548 Bool.true Bool.false 133632150 Bool.true Bool.true 170927536 

noncomputable def Ns276p1053 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 593460 1000 408 254 134217728 67108864 2251799813685248 Bool.false 141255152308 1887 

noncomputable def Ns276p1054 := Ns276p1053 93032624 38 94906264 8 147453232 38 77490640 16 Bool.true 134217696 1934 Bool.false 25895902 Bool.false 197063855 7074237752028440 1 Bool.false 131727296 Bool.false Bool.false 13740742 Bool.true Bool.true 49005655 

noncomputable def Ns276p1055 := nat_lit 1263816113804361536657773367311678008884534777 

noncomputable def Ns276p1056 := nat_lit 1200851966331738974226405220620983232102400 

noncomputable def Ns276p1057 := nat_lit 35334526796599089162958848000000000 

noncomputable def Ns276p1058 := nat_lit 125817811314315194823286111764480000000 

noncomputable abbrev qz677 := (@Eq.refl Real qz769)

noncomputable abbrev qz486 := qz677

noncomputable abbrev qz173 := qz486

noncomputable def Ns276p1059 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz170 593460 1000 1408780086400 16000000 1186920 4000 2000 Ns276p1057 Ns276p1058 qz173 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns276p1060 := nat_lit 1863572688771359347494086296503107924780779600773120000000 

noncomputable abbrev qz678 := (@HSub.hSub Real Real Real qz736 qz737 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz738 (@Nat.cast Real Real.instNatCast 1186920))))

noncomputable abbrev qz487 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 593460 4000) (Real.log (Enclosure.sfrac Bool.false 1408780086400 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz678))

noncomputable abbrev qz679 := (Enclosure.sfrac Bool.false 593460 2000)

noncomputable abbrev qz174 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz487 qz679) (@HMul.hMul Real Real Real qz346 qz679 (Real.log Real.pi)))

noncomputable def Ns276p1061 := @Enclosure.Real.IsNear.addLit_ft_p qz174 (Enclosure.sfrac Bool.true Ns276p1057 Ns276p1058) 14811680211199021369 14073748835532800 519370150305767901 36966400000000000000000 Ns276p1057 Ns276p1058 0 1 Ns276p1060 

noncomputable def Ns276p1062 := nat_lit 49699751645242320099265740800 

noncomputable abbrev qz175 := (@HSub.hSub Real Real Real qz350 qz487 qz679)

noncomputable def Ns276p1063 := @Enclosure.Real.IsNear.subLit_ff_p qz175 (@HMul.hMul Real Real Real qz5 qz679 (Real.log Real.pi)) 19592190670778093881 14073748835532800 375912671400273 72200000000000000000 1139762511153 3355443200 29673 3355443200 Ns276p1062 14811680211199021369 14073748835532800 

noncomputable abbrev qz176 := qz487

noncomputable def Ns276p1064 := @Enclosure.Real.IsNear.subLit_ff_p qz176 qz679 950731766509829665 562949953421312 375912671400273 72200000000000000000 593460 2000 0 1 1567375253662247510480 19592190670778093881 14073748835532800 375912671400273 72200000000000000000 

noncomputable def Ns276p1065 := nat_lit 8563430458765924575384721613127680 

noncomputable def Ns276p1066 := nat_lit 27528802772321089827635200 

noncomputable def Ns276p1067 := nat_lit 1256540678979654304140673696319465374540283956505274661395686578218635994751544013619200000000000000000 

noncomputable def Ns276p1068 := nat_lit 9117287821321301690816503966481183005098181892160910747725524618879754492032204144640000000000000000 

noncomputable def Ns276p1069 := nat_lit 29756262593127998985158376597171958331241543256050357135053515808623934885068800000000000000000 

noncomputable def Ns276p1070 := BSN.log_dyadic_bound 360204086400 2457356086400 5 4 Ns276p1067 67108864 28880000 Ns276p1068 Ns276p1069 19816649 2817560172800 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 360204086400) (BSN.artanhQ 2457356086400) 0 4 Ns276p1068 Ns276p1067 Ns276p1069 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz488 := (Real.log (Enclosure.sfrac Bool.false 1408780086400 16000000))

noncomputable def Ns276p1071 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 593460 4000) qz488 593460 4000 0 1 3204774434249975 281474976710656 781250361 22562500000000000 3803810871499980327 2251799813685248 23182041961953 4512500000000000000 (Enclosure.Real.IsNear.const Bool.false 593460 4000) (BSN.isNear_log_sfrac 1408780086400 16000000 3204774434249975 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1408780086400) qz353)) Bool.false Ns276p1066 Ns276p92 1000000462080000 28880000000000000000000 3204774434249975 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1408780086400 16000000 16 2817560172800 2097152000000 19816649 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns276p1070 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p1072 := BSN.arctan_dyadic_bound_f 1000 1186920 1 0 8388608 3610000 0 1 1 0 1 1 7067 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1186920) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1186920) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns276p1073 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1186920))) 884279719003555 562949953421312 1 2000000000000000 7067 8388608 1 3610000 7413897557750145089536 883805460661667 562949953421312 200000000361 722000000000000000 qz17 (Ns276p1072 rfl) rfl rfl 

noncomputable abbrev qz489 := (@HMul.hMul Real Real Real qz584 qz589 qz678)

noncomputable abbrev qz177 := qz489

noncomputable abbrev qz490 := qz678

noncomputable abbrev qz178 := qz490

noncomputable def Ns276p1074 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 593460 4000) qz488) qz177 3803810871499980327 2251799813685248 23182041961953 4512500000000000000 883805460661667 2251799813685248 200000000361 2888000000000000000 Ns276p1065 950731766509829665 562949953421312 375912671400273 72200000000000000000 (Ns276p1071 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz178 1 4 0 1 883805460661667 562949953421312 200000000361 722000000000000000 883805460661667 2251799813685248 200000000361 2888000000000000000 qz361 Ns276p1073 rfl) 

noncomputable def Ns276p1075 := @Ns276p1061 Ns276p1055 Ns276p1056 519370150305767901 36966400000000000000000 (@Ns276p1063 519370150305767901 36966400000000000000000 (Ns276p1064 (Ns276p1074 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 593460 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz679 (Real.log Real.pi) 593460 2000 0 1 38410761 33554432 1 33554432 1139762511153 3355443200 29673 3355443200 (Enclosure.Real.IsNear.const Bool.false 593460 2000) RS277to288.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns276p1057 Ns276p1058) 

noncomputable def Ns276p1076 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns276p1055 Ns276p1056 519370150305767901 36966400000000000000000 8828447019 8388608 237 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz362 qz174 (Enclosure.sfrac Bool.true Ns276p1057 Ns276p1058)) Bool.false Ns276p1055 Ns276p1056 519370150305767901 36966400000000000000000 Ns276p1059 (Ns276p1075 rfl rfl)) 

noncomputable def Ns276p1077 := nat_lit 1898200129558913281425408 

noncomputable def Ns276p1078 := nat_lit 855734376782750714162984329051556062855652738417423066079888888246206066622724165253175301032862178060112259804878963448410837561480721 

noncomputable def Ns276p1079 := nat_lit 608003845183551007409896319067344176325406559367413880331788385495530074765187446594546674957725227237644620433740219259603490321 

noncomputable def Ns276p1080 := nat_lit 4273363779155304287629538236779664992538824492616870357899780185833835166665513262134964084436546327998995607411876410382013195940632081 

noncomputable def Ns276p1081 := BSN.sin_dyadic_bound_f 53950092523 34359738368 4 3 16777216 7227051 Ns276p1078 Ns276p106 Ns276p1079 Ns276p1080 Ns276p109 Ns276p1079 16777212 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53950092523) qz363 0 3 Ns276p1078 Ns276p106 Ns276p1079 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53950092523) qz364 0 3 Ns276p1080 Ns276p109 Ns276p1079 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1082 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz170) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8828447019) qz365) Bool.false 8828447019 8388608 237 16777216 Bool.true 16777212 16777216 1 3610000 (Ns276p1076 rfl) (Enclosure.sfrac_false_div 8828447019 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8828447019) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns276p1077) qz366) 226375608064910080 72057594037927936 Bool.false 16777212 16777216 167 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q1 8828447019 8388608 226375608064910080 72057594037927936 167 Ns276p1077 Ns276p104 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777212 16777216 Ns276p1077 Ns276p104 53950092523 34359738368 7227051 7220000 (Ns276p1081 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p1083 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns276p1055 Ns276p1056 519370150305767901 36966400000000000000000 141255152308 134217728 1887 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz362 qz174 (Enclosure.sfrac Bool.true Ns276p1057 Ns276p1058)) Bool.false Ns276p1055 Ns276p1056 519370150305767901 36966400000000000000000 Ns276p1059 (Ns276p1075 rfl rfl)) 

noncomputable def Ns276p1084 := Ns276p1054 33354 BSN.abs_quadSignPos (BSN.cos_quad_nat0 408 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131727296 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 254 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 13740742 134217728) qz173 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) Bool.true 4194303 4194304 54521701 3785359360000 134217696 134217728 1934 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 4194303 4194304 54521701 3785359360000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz170) qz170) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 16777212 16777216 872347216 60565749760000 4194303 4194304 54521701 3785359360000 (Ns276p1082 rfl rfl) rfl)) rfl) (Ns276p1083 rfl) RS277to288.d7 

noncomputable def Ns276p1085 := nat_lit 449701329421007505864844108816 

noncomputable def Ns276p1086 := BSN.cos_dyadic_bound_f 25895902 134217728 2 1 134217728 67108864 Ns276p1085 Ns276p122 Ns276p1085 Ns276p1085 Ns276p123 Ns276p1085 131727296 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 25895902) qz369 0 1 Ns276p1085 Ns276p122 Ns276p1085 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 25895902) qz370 0 1 Ns276p1085 Ns276p123 Ns276p1085 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1087 := nat_lit 3178577655149401977995591441894885614636622905399381880094807633483879839135716245515350515134000371890625 

noncomputable def Ns276p1088 := nat_lit 3429917637277076479885941323377058296018574463932397962058087476950286420481999743950286777587890625 

noncomputable def Ns276p1089 := nat_lit 19247891124153580317512423794141667762486082921492991207403640922779213947071234919707278142128129677490625 

noncomputable def Ns276p1090 := BSN.cos_dyadic_bound_f 197063855 134217728 4 3 134217728 67108864 Ns276p1087 Ns276p116 Ns276p1088 Ns276p1089 Ns276p119 Ns276p1088 13740742 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 197063855) qz369 0 3 Ns276p1087 Ns276p116 Ns276p1088 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 197063855) qz370 0 3 Ns276p1089 Ns276p119 Ns276p1088 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1091 := nat_lit 3946102506252827170277915661376907285805908631575785238846137093441 

noncomputable def Ns276p1092 := nat_lit 52387487109058279987539904971869031076602494965525565322480961 

noncomputable def Ns276p1093 := nat_lit 11838202743784263394273771904320778119355572689737424665407766318401 

noncomputable def Ns276p1094 := BSN.cos_dyadic_bound_f 51868471 134217728 3 2 134217728 67108864 Ns276p1091 Ns276p131 Ns276p1092 Ns276p1093 Ns276p134 Ns276p1092 124319548 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 51868471) qz369 0 2 Ns276p1091 Ns276p131 Ns276p1092 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 51868471) qz370 0 2 Ns276p1093 Ns276p134 Ns276p1092 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1095 := nat_lit 8461270125004292188656370545605495102527015775688982242281431298538859526200891024295885889831510078633841 

noncomputable def Ns276p1096 := nat_lit 3694204596357193370689686332155448619645485361652845742472422992560424208267681517159735148016809841 

noncomputable def Ns276p1097 := nat_lit 42265202852203129616535413293701969978228672514640127218410321087902708259396148827340838395472519083833201 

noncomputable def Ns276p1098 := BSN.sin_dyadic_bound_f 198286621 134217728 4 3 134217728 67108864 Ns276p1095 Ns276p255 Ns276p1096 Ns276p1097 Ns276p258 Ns276p1096 133632150 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 198286621) qz367 0 3 Ns276p1095 Ns276p255 Ns276p1096 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 198286621) qz368 0 3 Ns276p1097 Ns276p258 Ns276p1096 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1099 := Ns276p1052 56523 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 146 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 124319548 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133632150 134217728) qz173 rfl rfl (Ns276p1084 RS277to288.d9 RS277to288.d11 RS277to288.d13 RS277to288.d17 (Ns276p1086 rfl rfl) (Ns276p1090 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns276p1083 rfl) RS277to288.d19 RS277to288.d21 RS277to288.d23 RS277to288.d25 RS277to288.d17 (Ns276p1094 rfl rfl) (Ns276p1098 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns276p1100 := nat_lit 3280490285020738961742457025537212247168767816459845736443107474332166049814164576463519704246643264000000 

noncomputable def Ns276p1101 := nat_lit 3769523789719302223309535089564673474977991574390289211417253930309262727746685291890081000000000000 

noncomputable def Ns276p1102 := nat_lit 19863855541773493967825457373719222806483400253043507079990939959201523972277504114929311342820951001600000 

noncomputable def Ns276p1103 := BSN.cos_dyadic_bound_f 198620410 134217728 4 3 134217728 67108864 Ns276p1100 Ns276p116 Ns276p1101 Ns276p1102 Ns276p119 Ns276p1101 12191476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 198620410) qz369 0 3 Ns276p1100 Ns276p116 Ns276p1101 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 198620410) qz370 0 3 Ns276p1102 Ns276p119 Ns276p1101 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1104 := nat_lit 2145311729425420062128708810256 

noncomputable def Ns276p1105 := BSN.sin_dyadic_bound_f 38271246 134217728 2 1 134217728 67108864 Ns276p1104 Ns276p126 Ns276p1104 Ns276p1104 Ns276p127 Ns276p1104 37754733 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 38271246) qz367 0 1 Ns276p1104 Ns276p126 Ns276p1104 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 38271246) qz368 0 1 Ns276p1104 Ns276p127 Ns276p1104 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1106 := Ns276p1050 75757 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 6 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 12191476 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 65 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 37754733 134217728) qz173 rfl rfl (Ns276p1099 rfl rfl) (Ns276p1083 rfl) RS277to288.d27 RS277to288.d29 RS277to288.d31 RS277to288.d33 RS277to288.d17 (Ns276p1103 rfl rfl) (Ns276p1105 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p1107 := nat_lit 307129545727062896911829064341290785416149700255845817699919011512320 

noncomputable def Ns276p1108 := nat_lit 97886698622587754802426765579097921673001333655199776514009726976 

noncomputable def Ns276p1109 := nat_lit 804228422249299587927967429940062088978635784225106818147336633450496 

noncomputable def Ns276p1110 := BSN.sin_dyadic_bound_f 132996576 134217728 3 2 134217728 67108864 Ns276p1107 Ns276p137 Ns276p1108 Ns276p1109 Ns276p140 Ns276p1108 112275867 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 132996576) qz367 0 2 Ns276p1107 Ns276p137 Ns276p1108 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 132996576) qz368 0 2 Ns276p1109 Ns276p140 Ns276p1108 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1111 := nat_lit 567969406406907308982049831696 

noncomputable def Ns276p1112 := BSN.cos_dyadic_bound_f 27452458 134217728 2 1 134217728 67108864 Ns276p1111 Ns276p122 Ns276p1111 Ns276p1111 Ns276p123 Ns276p1111 131419983 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 27452458) qz369 0 1 Ns276p1111 Ns276p122 Ns276p1111 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 27452458) qz370 0 1 Ns276p1111 Ns276p123 Ns276p1111 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1113 := Ns276p1048 92563 BSN.abs_quadSignPos (BSN.cos_quad_nat3 115 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 112275867 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 131419983 134217728) qz173 rfl rfl (Ns276p1106 rfl) (Ns276p1083 rfl) RS277to288.d35 RS277to288.d37 RS277to288.d39 RS277to288.d41 RS277to288.d17 (Ns276p1110 rfl rfl) (Ns276p1112 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p1114 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) 106672465 134217728 92563 134217728 106672465 134217728 92563 134217728 28634671784919040 106672465 67108864 92563 67108864 (Ns276p1113 rfl) 

noncomputable def Ns276p1115 := @Enclosure.Real.IsNear.mulLit_tf qz676 (Zeta.RiemannSiegel.correction qz172) 5381669 16777216 1 16777216 16572629501915 35184372088832 573460729758469 3175389581017088000 89188406438941396135 590295810358705651712 

noncomputable abbrev qz680 := (@HPow.hPow Real Real Real qz7 qz171 qz9)

noncomputable def Ns276p1116 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz680 1 1 0 1 5381669 16777216 1 16777216 5381669 16777216 1 16777216 

noncomputable def Ns276p1117 := @Enclosure.Real.IsNear.sqrt_image qz171 79232162121 838860800 29673 838860800 81525903 81525935 8388608 (@Enclosure.Real.IsNear.of_eq qz171 (@HMul.hMul Real Real Real qz5 qz170 qz3) Bool.false 79232162121 838860800 29673 838860800 (BSN.t_div_two_pi_mk qz170 593460 1000 qz173) (@Enclosure.Real.IsNear.mulLit_ff qz170 qz3 593460 1000 0 1 2670177 16777216 1 16777216 79232162121 838860800 29673 838860800 (Enclosure.Real.IsNear.const Bool.false 593460 1000) RS277to288.d44 rfl)) 

noncomputable abbrev qz772 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 593460 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz681 := qz772

noncomputable abbrev qz491 := qz681

noncomputable abbrev qz179 := qz491

noncomputable def Ns276p1118 := @Enclosure.Real.IsNear.sqrt_image qz179 81525919 8388608 1 524288 26151268 26151274 8388608 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 163051838 16777216 32 16777216 81525919 8388608 1 524288 (Ns276p1117 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns276p1119 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz179) 26151271 8388608 3 8388608 2690834 2690835 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz179) Bool.false 52302542 16777216 6 16777216 26151271 8388608 3 8388608 (Ns276p1118 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns276p1120 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 5381669 16777216 1 16777216 5381669 16777216 1 16777216 (Ns276p1119 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz492 := (@HMul.hMul Real Real Real qz584 qz582 qz675)

noncomputable abbrev qz180 := (Real.cos qz492)

noncomputable abbrev qz682 := (@HMul.hMul Real Real Real qz732 qz771 qz771)

noncomputable abbrev qz493 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz682 qz675) qz599)

noncomputable abbrev qz181 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz493))

noncomputable def Ns276p1121 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz172) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz180) qz181) Bool.false 16572629501915 

noncomputable def Ns276p1122 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz180) qz181 85717985 16777216 5395 

noncomputable abbrev qz182 := (@Neg.neg Real Real.instNeg (Real.cos qz492))

noncomputable def Ns276p1123 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz180) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz182)) Bool.true 85717985 16777216 5395 16777216 (BSN.inv_eq_neg_inv_neg qz180) 

noncomputable def Ns276p1124 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz182) Bool.false 85717985 16777216 5395 16777216 85717985 16777216 

noncomputable def Ns276p1125 := @Enclosure.Real.IsNear.recentre' qz180 Bool.true 3283733 16777216 372998608 30282874880000 3283733 16777216 23312413 1892679680000 

noncomputable abbrev qz183 := qz492

noncomputable def Ns276p1126 := @Enclosure.Real.IsNear.cos_image qz183 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 75755699) qz376) Bool.false 75755699 16777216 101 8388608 Bool.true 3283733 16777216 1 

noncomputable def Ns276p1127 := nat_lit 26986075412280543294002631 

noncomputable def Ns276p1128 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz172 884279719003555 140737488355328 1 500000000000000 6028447 8388608 1 524288 5330833419187824129085 1180591620717411303424 Ns276p1127 

noncomputable def Ns276p1129 := @Enclosure.Real.IsNear.subLit_ff_p qz179 qz1 81525919 8388608 1 524288 9 1 0 1 6028447 6028447 8388608 1 

noncomputable def Ns276p1130 := @Ns276p1129 524288 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 163051838 16777216 32 16777216 81525919 8388608 1 524288 (Ns276p1117 rfl rfl rfl rfl rfl rfl) rfl) qz377 

noncomputable def Ns276p1131 := @Enclosure.Real.IsNear.recentre' qz183 Bool.false 5330833419187824129085 1180591620717411303424 Ns276p1127 Ns276p556 75755699 16777216 101 8388608 (@Ns276p1128 Ns276p556 RS277to288.d43 (Ns276p1130 rfl rfl) rfl) 

noncomputable def Ns276p1132 := nat_lit 3321641861930249741139968 

noncomputable def Ns276p1133 := nat_lit 192901956516086838678363406189255755474040222703358629885305814057661125969449976258466816483336047469758005724355944226803353648140625 

noncomputable def Ns276p1134 := nat_lit 122370308700160389169917444467379894697949549452619252836791095132001594201759100463725588355842672781992100330772833437744140625 

noncomputable def Ns276p1135 := nat_lit 1168620585273522419115755185795044295877488081931592826384626228470525498380156167308914554877746237543409804372051345317344354761740625 

noncomputable def Ns276p1136 := BSN.cos_dyadic_bound_f 47203369915 34359738368 4 3 16777216 7227051 Ns276p1133 Ns276p1020 Ns276p1134 Ns276p1135 Ns276p1023 Ns276p1134 3283733 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 47203369915) qz378 0 3 Ns276p1133 Ns276p1020 Ns276p1134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 47203369915) qz379 0 3 Ns276p1135 Ns276p1023 Ns276p1134 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1137 := @Ns276p1126 3610000 (Ns276p1131 rfl) (Enclosure.sfrac_false_div 75755699 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 75755699) qz376) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns276p1132) qz380) 226375608064910080 72057594037927936 Bool.false 3283733 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 75755699 16777216 226375608064910080 72057594037927936 0 Ns276p1132 Ns276p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 3283733 16777216 Ns276p1132 Ns276p92 47203369915 34359738368 7227051 7220000 (Ns276p1136 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p1138 := @Enclosure.Real.IsNear.inv_image qz182 3283733 16777216 23312413 1892679680000 42856295 42861690 8388608 (@Enclosure.Real.IsNear.neg qz180 Bool.true 3283733 16777216 23312413 1892679680000 (Ns276p1125 (Ns276p1137 rfl rfl) rfl)) 

noncomputable def Ns276p1139 := Ns276p1123 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz182) Bool.false 85717985 16777216 5395 16777216 (@Ns276p1124 5395 16777216 (Ns276p1138 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p1140 := @Enclosure.Real.IsNear.recentre' qz181 Bool.true 773356 8388608 

noncomputable abbrev qz184 := (@HMul.hMul Real Real Real qz346 qz343 qz493)

noncomputable def Ns276p1141 := @Enclosure.Real.IsNear.cos_image qz184 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 27902499)) qz376) Bool.true 27902499 16777216 

noncomputable def Ns276p1142 := nat_lit 16470728466467364739448357405 

noncomputable def Ns276p1143 := nat_lit 275872145267483616681854814853329 

noncomputable def Ns276p1144 := @Enclosure.Real.IsNear.recentre' qz184 Bool.true Ns276p1142 Ns276p793 Ns276p1143 

noncomputable abbrev qz185 := qz493

noncomputable def Ns276p1145 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz185 884279719003555 140737488355328 1 500000000000000 18626152011071 

noncomputable abbrev qz494 := (@HSub.hSub Real Real Real qz588 qz682 qz675)

noncomputable abbrev qz186 := qz494

noncomputable def Ns276p1146 := @Enclosure.Real.IsNear.subLit_tf qz186 qz31 14228105499967 70368744177664 10222759 2199023255552 1 16 

noncomputable abbrev qz495 := qz682

noncomputable abbrev qz187 := qz495

noncomputable def Ns276p1147 := @Enclosure.Real.IsNear.subLit_ff_n qz187 qz172 36342173231809 70368744177664 6028455 2199023255552 6028447 8388608 1 524288 

noncomputable def Ns276p1148 := @Enclosure.Real.IsNear.mulLit_ff qz172 qz172 6028447 8388608 1 524288 6028447 8388608 1 524288 36342173231809 70368744177664 

noncomputable def Ns276p1149 := nat_lit 76283710088262504622383823304211123787430939609367212180278738519395968852140083126931077588081 

noncomputable def Ns276p1150 := nat_lit 222698460553665065770495546636156872253078831572717690810592549703522742374129267077670001 

noncomputable def Ns276p1151 := nat_lit 461388092946175795141361673133328908004706684236280402152917543875693917031963927429136136922225 

noncomputable def Ns276p1152 := BSN.cos_dyadic_bound_t 27902499 16777216 4 3 8388608 3610000 Ns276p1149 Ns276p193 Ns276p1150 Ns276p1151 Ns276p196 Ns276p1150 773356 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 27902499) qz600 0 3 Ns276p1149 Ns276p193 Ns276p1150 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 27902499) (BSN.cosOddQ 16777216) 0 3 Ns276p1151 Ns276p196 Ns276p1150 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1153 := @Ns276p1140 1789287216 60565749760000 193339 2097152 111830451 3785359360000 (@Ns276p1141 491 16777216 Bool.true 773356 8388608 1 3610000 (@Ns276p1144 Ns276p796 27902499 16777216 491 16777216 (@Ns276p1145 70368744177664 10222759 2199023255552 Ns276p1142 Ns276p793 Ns276p1143 Ns276p796 RS277to288.d43 (@Ns276p1146 0 1 298018432177136 18626152011071 70368744177664 10222759 2199023255552 (@Ns276p1147 119353999621867175936 14228105499967 70368744177664 10222759 2199023255552 (@Ns276p1148 6028455 2199023255552 (Ns276p1130 rfl rfl) (Ns276p1130 rfl rfl) rfl) (Ns276p1130 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 27902499 16777216) (BSN.cos_neg_of_bound 27902499 16777216 Bool.true 773356 8388608 1 3610000 (Ns276p1152 rfl rfl)) rfl rfl) 

noncomputable def Ns276p1154 := @Ns276p1115 154383604266590384599 Ns276p1044 (Ns276p1116 qz33 (@Enclosure.Real.IsNear.of_eq qz680 (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 5381669 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz171 (BSN.t_div_two_pi_nonneg qz170 593460 1000 qz173)) Ns276p1120) rfl) (@Ns276p1121 35184372088832 573460729758469 3175389581017088000 (BSN.correction_mk qz172 (BSN.cos_two_pi_p_ne_zero_mk qz170 593460 1000 9 qz173 rfl rfl (@BSN.floor_sqrt_eq_dec qz170 593460 1000 9 qz173 rfl rfl rfl))) (@Ns276p1122 16777216 193339 2097152 111830451 3785359360000 16572629501915 35184372088832 573460729758469 3175389581017088000 Ns276p1139 (Ns276p1153 rfl) rfl)) 

noncomputable def Ns276p1155 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (hardyZApproximantRS₀ qz170) Bool.true 849112518609285706585 590295810358705651712 3828428426612649341399 Ns276p1044 (@Eq.refl Real (hardyZApproximantRS₀ qz170)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) (@HMul.hMul Real Real Real qz5 qz676 (Zeta.RiemannSiegel.correction qz172))) Bool.true 849112518609285706585 590295810358705651712 3828428426612649341399 Ns276p1044 (BSN.hardyZApproximantRS₀_eq qz170 9 (@BSN.floor_sqrt_eq_dec qz170 593460 1000 9 qz173 rfl rfl rfl)) (@Ns276p1046 849112518609285706585 590295810358705651712 3828428426612649341399 Ns276p1044 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 9)) Bool.true 106672465 67108864 92563 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) (Ns276p1114 (Ns276p1113 rfl) rfl rfl)) (Ns276p1154 rfl) rfl rfl)) 

theorem RS277to288.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz170) Bool.true 849112518609285706585 590295810358705651712 3828428426612649341399 Ns276p1044 := Ns276p1155 

noncomputable def Ns276p1156 := nat_lit 95819553501887980947795607552 

noncomputable abbrev qz773 := (Enclosure.sfrac Bool.false 594841 1000)

noncomputable abbrev qz683 := qz773

noncomputable abbrev qz496 := qz683

noncomputable abbrev qz188 := qz496

noncomputable abbrev qz774 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 594841 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz684 := qz774

noncomputable abbrev qz497 := qz684

noncomputable abbrev qz189 := qz497

noncomputable abbrev qz775 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 594841 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz685 := qz775

noncomputable abbrev qz498 := qz685

noncomputable abbrev qz190 := qz498

noncomputable abbrev qz686 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz189 qz9))

noncomputable def Ns276p1157 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (@HMul.hMul Real Real Real qz5 qz686 (Zeta.RiemannSiegel.correction qz190)) 75988945 33554432 92771 67108864 182021908990494992421 1180591620717411303424 23530445971374723108963 Ns276p926 Ns276p1156 

noncomputable def Ns276p1158 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 594841 1000 115 160 134217728 67108864 2251799813685248 Bool.false 141676765251 1891 

noncomputable def Ns276p1159 := Ns276p1158 279097919 38 47453128 8 294906479 38 44739240 8 Bool.false 76113782 75926 Bool.true 96817859 Bool.true 13105362 7074237752028440 1 Bool.false 88637180 Bool.false Bool.false 133578415 Bool.false Bool.false 151977890 

noncomputable def Ns276p1160 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 594841 1000 6 64 134217728 67108864 2251799813685248 Bool.false 141676765251 1891 

noncomputable def Ns276p1161 := Ns276p1160 240485871 38 54794152 8 261175631 38 50729528 8 Bool.false 105251844 56648 Bool.true 109118455 Bool.true 188170564 7074237752028440 1 Bool.false 92251265 Bool.true Bool.false 22550681 Bool.false Bool.false 76113782 

noncomputable def Ns276p1162 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 594841 1000 147 62 134217728 67108864 2251799813685248 Bool.false 141676765251 1891 

noncomputable def Ns276p1163 := Ns276p1162 186065264 38 67108856 8 216015088 38 60023992 8 Bool.false 143126101 33426 Bool.false 5696570 Bool.false 110754013 7074237752028440 1 Bool.false 5694859 Bool.false Bool.false 91056459 Bool.true Bool.false 105251844 

noncomputable def Ns276p1164 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 594841 1000 409 255 134217728 67108864 2251799813685248 Bool.false 141676765251 1891 

noncomputable def Ns276p1165 := Ns276p1164 93032624 38 94906264 8 147453232 38 77490640 16 Bool.false 134217664 1934 Bool.false 108202077 Bool.false 204215170 7074237752028440 1 Bool.false 96856869 Bool.true Bool.false 134054820 Bool.false Bool.false 143126101 

noncomputable def Ns276p1166 := nat_lit 473846124666652910632638362451307153891630198990704588379 

noncomputable def Ns276p1167 := nat_lit 448898943744508092017362622069698586343648585056256000 

noncomputable def Ns276p1168 := nat_lit 35747567097723052030955569696480000 

noncomputable def Ns276p1169 := nat_lit 127584753427216836603680184813839158080 

noncomputable abbrev qz687 := (@Eq.refl Real qz773)

noncomputable abbrev qz499 := qz687

noncomputable abbrev qz191 := qz499

noncomputable def Ns276p1170 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz188 594841 1000 1415344261124 16000000 1189682 4000 2000 Ns276p1168 Ns276p1169 qz191 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns276p1171 := nat_lit 151630759893328931402444275984418289245321663677025468281280 

noncomputable abbrev qz688 := (@HSub.hSub Real Real Real qz736 qz737 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz738 (@Nat.cast Real Real.instNatCast 1189682))))

noncomputable abbrev qz500 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 594841 4000) (Real.log (Enclosure.sfrac Bool.false 1415344261124 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz688))

noncomputable abbrev qz689 := (Enclosure.sfrac Bool.false 594841 2000)

noncomputable abbrev qz192 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz500 qz689) (@HMul.hMul Real Real Real qz346 qz689 (Real.log Real.pi)))

noncomputable def Ns276p1172 := @Enclosure.Real.IsNear.addLit_ft_p qz192 (Enclosure.sfrac Bool.true Ns276p1168 Ns276p1169) 1188471161861923316291 1125899906842624000 10411455674115421517 739328000000000000000000 Ns276p1168 Ns276p1169 0 1 Ns276p1171 

noncomputable def Ns276p1173 := nat_lit 79756949569313798611401703424000 

noncomputable abbrev qz193 := (@HSub.hSub Real Real Real qz350 qz500 qz689)

noncomputable def Ns276p1174 := @Enclosure.Real.IsNear.subLit_ff_p qz193 (@HMul.hMul Real Real Real qz5 qz689 (Real.log Real.pi)) 1571801950428832637507 1125899906842624000 1883878983995529 361000000000000000000 22848295484001 67108864000 594841 67108864000 Ns276p1173 1188471161861923316291 1125899906842624000 

noncomputable def Ns276p1175 := nat_lit 3143603900857665275014000 

noncomputable abbrev qz194 := qz500

noncomputable def Ns276p1176 := @Enclosure.Real.IsNear.subLit_ff_p qz194 qz689 1906667663671919288899 1125899906842624000 1883878983995529 361000000000000000000 594841 2000 0 1 Ns276p1175 1571801950428832637507 1125899906842624000 1883878983995529 361000000000000000000 

noncomputable def Ns276p1177 := nat_lit 4293433889816114951289716524766461952 

noncomputable def Ns276p1178 := nat_lit 27540042532011907940876288 

noncomputable def Ns276p1179 := nat_lit 1283645193787433287227283057872305300119137965936344795591975485911318548908420871376469499040349880320 

noncomputable def Ns276p1180 := nat_lit 9609072663321894148658443120054900465435960662437604043837257722120975649062469313669254788160159744 

noncomputable def Ns276p1181 := nat_lit 34381377207501315110309344149473138988319952746259890879158783205834959744475876658976607764480 

noncomputable def Ns276p1182 := BSN.log_dyadic_bound 366768261124 2463920261124 5 4 Ns276p1179 67108864 28880000 Ns276p1180 Ns276p1181 20128615 2830688522248 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 366768261124) (BSN.artanhQ 2463920261124) 0 4 Ns276p1180 Ns276p1179 Ns276p1181 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz501 := (Real.log (Enclosure.sfrac Bool.false 1415344261124 16000000))

noncomputable def Ns276p1183 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 594841 4000) qz501 594841 4000 0 1 3206082914491639 281474976710656 781250361 22562500000000000 1907109566939121034399 1125899906842624000 464719745987601 90250000000000000000 (Enclosure.Real.IsNear.const Bool.false 594841 4000) (BSN.isNear_log_sfrac 1415344261124 16000000 3206082914491639 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1415344261124) qz353)) Bool.false Ns276p1178 Ns276p92 1000000462080000 28880000000000000000000 3206082914491639 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1415344261124 16000000 16 2830688522248 2097152000000 20128615 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns276p1182 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p1184 := BSN.arctan_dyadic_bound_f 1000 1189682 1 0 8388608 3610000 0 1 1 0 1 1 7051 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1189682) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1189682) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns276p1185 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1189682))) 884279719003555 562949953421312 1 2000000000000000 7051 8388608 1 3610000 7413906564949399830528 883806534403491 562949953421312 200000000361 722000000000000000 qz17 (Ns276p1184 rfl) rfl rfl 

noncomputable abbrev qz502 := (@HMul.hMul Real Real Real qz584 qz589 qz688)

noncomputable abbrev qz195 := qz502

noncomputable abbrev qz503 := qz688

noncomputable abbrev qz196 := qz503

noncomputable def Ns276p1186 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 594841 4000) qz501) qz195 1907109566939121034399 1125899906842624000 464719745987601 90250000000000000000 883806534403491 2251799813685248 200000000361 2888000000000000000 Ns276p1177 1906667663671919288899 1125899906842624000 1883878983995529 361000000000000000000 (Ns276p1183 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz196 1 4 0 1 883806534403491 562949953421312 200000000361 722000000000000000 883806534403491 2251799813685248 200000000361 2888000000000000000 qz361 Ns276p1185 rfl) 

noncomputable def Ns276p1187 := @Ns276p1172 Ns276p1166 Ns276p1167 10411455674115421517 739328000000000000000000 (@Ns276p1174 10411455674115421517 739328000000000000000000 (Ns276p1176 (Ns276p1186 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 594841 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz689 (Real.log Real.pi) 594841 2000 0 1 38410761 33554432 1 33554432 22848295484001 67108864000 594841 67108864000 (Enclosure.Real.IsNear.const Bool.false 594841 2000) RS277to288.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns276p1168 Ns276p1169) 

noncomputable def Ns276p1188 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz188) Bool.false Ns276p1166 Ns276p1167 10411455674115421517 739328000000000000000000 2213699457 2097152 237 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz188) (@HAdd.hAdd Real Real Real qz362 qz192 (Enclosure.sfrac Bool.true Ns276p1168 Ns276p1169)) Bool.false Ns276p1166 Ns276p1167 10411455674115421517 739328000000000000000000 Ns276p1170 (Ns276p1187 rfl rfl)) 

noncomputable def Ns276p1189 := nat_lit 855010631299827558613199948950283402065977086034363101666517891921167633244501977390114723160609229263329946365179869656121064000000000 

noncomputable def Ns276p1190 := nat_lit 606465557117355499754074705518428036773312469167297218481502154724031439713630952135277262312887968911883222900390625000000000000 

noncomputable def Ns276p1191 := nat_lit 4269754010796125832879784166210434246062145730740690299456502121573617436362952843282495595879453280300106265441809180318105320000000000 

noncomputable def Ns276p1192 := BSN.sin_dyadic_bound_f 53938704550 34359738368 4 3 16777216 7227051 Ns276p1189 Ns276p106 Ns276p1190 Ns276p1191 Ns276p109 Ns276p1190 16777208 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53938704550) qz363 0 3 Ns276p1189 Ns276p106 Ns276p1190 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53938704550) qz364 0 3 Ns276p1191 Ns276p109 Ns276p1190 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1193 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz188) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2213699457) (@Nat.cast Real Real.instNatCast 2097152)) Bool.false 2213699457 2097152 237 16777216 Bool.false 16777208 16777216 1 3610000 (Ns276p1188 rfl) (Enclosure.sfrac_false_div 2213699457 2097152) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2213699457) (@Nat.cast Real Real.instNatCast 2097152)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474449862727132610822144) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 16777208 16777216 167 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q3 2213699457 2097152 226375608064910080 72057594037927936 167 474449862727132610822144 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777208 16777216 474449862727132610822144 302231454903657293676544 53938704550 34359738368 7227051 7220000 (Ns276p1192 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p1194 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz188) Bool.false Ns276p1166 Ns276p1167 10411455674115421517 739328000000000000000000 141676765251 134217728 1891 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz188) (@HAdd.hAdd Real Real Real qz362 qz192 (Enclosure.sfrac Bool.true Ns276p1168 Ns276p1169)) Bool.false Ns276p1166 Ns276p1167 10411455674115421517 739328000000000000000000 Ns276p1170 (Ns276p1187 rfl rfl)) 

noncomputable def Ns276p1195 := Ns276p1165 33426 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 409 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 96856869 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 255 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 134054820 134217728) qz191 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 1) Bool.false 2097151 2097152 54521701 3785359360000 134217664 134217728 1934 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz188)) Bool.false 2097151 2097152 54521701 3785359360000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz188) qz188) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz188)) Bool.false 16777208 16777216 872347216 60565749760000 2097151 2097152 54521701 3785359360000 (Ns276p1193 rfl rfl) rfl)) rfl) (Ns276p1194 rfl) RS277to288.d7 

noncomputable def Ns276p1196 := nat_lit 134531617623703169099810626879772714263576432977692969129999656167585 

noncomputable def Ns276p1197 := nat_lit 18788182887365724894386252970656166735719456014800806220085995681 

noncomputable def Ns276p1198 := nat_lit 352314293861214469802055968846976046420366159631838574987547531684001 

noncomputable def Ns276p1199 := BSN.sin_dyadic_bound_f 108202077 134217728 3 2 134217728 67108864 Ns276p1196 Ns276p137 Ns276p1197 Ns276p1198 Ns276p140 Ns276p1197 96856869 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 108202077) qz367 0 2 Ns276p1196 Ns276p137 Ns276p1197 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 108202077) qz368 0 2 Ns276p1198 Ns276p140 Ns276p1197 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1200 := nat_lit 9521368680809316714806245591751153760316317925302744742228823487192419387411171411562863064783647910400000 

noncomputable def Ns276p1201 := nat_lit 5260851015896772641604160140508282293945386499051264581972634430017922596716071281443761000000000000 

noncomputable def Ns276p1202 := nat_lit 47554757219611886516530671089890480693849425042919849248154153914484037762190882990785430711097855552000000 

noncomputable def Ns276p1203 := BSN.sin_dyadic_bound_f 204215170 134217728 4 3 134217728 67108864 Ns276p1200 Ns276p255 Ns276p1201 Ns276p1202 Ns276p258 Ns276p1201 134054820 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 204215170) qz367 0 3 Ns276p1200 Ns276p255 Ns276p1201 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 204215170) qz368 0 3 Ns276p1202 Ns276p258 Ns276p1201 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1204 := BSN.sin_dyadic_bound_f 5696570 134217728 1 0 134217728 67108864 0 1 1 0 1 1 5694859 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 5696570) qz367 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 5696570) qz368 0 0 rfl) rfl rfl 

noncomputable def Ns276p1205 := nat_lit 82055281803824034707042604126586136516216734178632050875694186429601 

noncomputable def Ns276p1206 := nat_lit 22639965949656344333806883559145638871365829351782021139262274721 

noncomputable def Ns276p1207 := nat_lit 246120565479572791432460198612640118270907470877192588584804034739361 

noncomputable def Ns276p1208 := BSN.cos_dyadic_bound_f 110754013 134217728 3 2 134217728 67108864 Ns276p1205 Ns276p131 Ns276p1206 Ns276p1207 Ns276p134 Ns276p1206 91056459 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 110754013) qz369 0 2 Ns276p1205 Ns276p131 Ns276p1206 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 110754013) qz370 0 2 Ns276p1207 Ns276p134 Ns276p1206 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1209 := Ns276p1163 56648 BSN.abs_quadSignPos (BSN.cos_quad_nat3 147 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 5694859 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 62 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 91056459 134217728) qz191 rfl rfl (Ns276p1195 RS277to288.d9 RS277to288.d11 RS277to288.d13 RS277to288.d17 (Ns276p1199 rfl rfl) (Ns276p1203 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns276p1194 rfl) RS277to288.d19 RS277to288.d21 RS277to288.d23 RS277to288.d25 RS277to288.d17 (Ns276p1204 rfl rfl) (Ns276p1208 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns276p1210 := nat_lit 77313363319366619849677972433926690325544147169058781480778374690625 

noncomputable def Ns276p1211 := nat_lit 20099519056750742881999040487216301059603449153296482282937890625 

noncomputable def Ns276p1212 := nat_lit 231899890919986358063269919220805638374513234608869751477769248290625 

noncomputable def Ns276p1213 := BSN.cos_dyadic_bound_f 109118455 134217728 3 2 134217728 67108864 Ns276p1210 Ns276p131 Ns276p1211 Ns276p1212 Ns276p134 Ns276p1211 92251265 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 109118455) qz369 0 2 Ns276p1210 Ns276p131 Ns276p1211 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 109118455) qz370 0 2 Ns276p1212 Ns276p134 Ns276p1211 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1214 := nat_lit 2641249490272058989656602627707108277117516396374292849626552373475845814612940598622539607976167683915776 

noncomputable def Ns276p1215 := nat_lit 1970698742057896525153549268252993408593726660670256087167039296255098997856331076965700379078557696 

noncomputable def Ns276p1216 := nat_lit 15999061101048160990325600954017185398522425085769003769639335226360638686680024272501114102055164832645120 

noncomputable def Ns276p1217 := BSN.cos_dyadic_bound_f 188170564 134217728 4 3 134217728 67108864 Ns276p1214 Ns276p116 Ns276p1215 Ns276p1216 Ns276p119 Ns276p1215 22550681 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 188170564) qz369 0 3 Ns276p1214 Ns276p116 Ns276p1215 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 188170564) qz370 0 3 Ns276p1216 Ns276p119 Ns276p1215 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1218 := Ns276p1161 75926 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 6 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 92251265 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 22550681 134217728) qz191 rfl rfl (Ns276p1209 rfl rfl) (Ns276p1194 rfl) RS277to288.d27 RS277to288.d29 RS277to288.d31 RS277to288.d33 RS277to288.d17 (Ns276p1213 rfl rfl) (Ns276p1217 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p1219 := nat_lit 86234708624269341618636601642609897953373439593364472245765880499105 

noncomputable def Ns276p1220 := nat_lit 7720471008410359349489551888163741300344050284303042047841749921 

noncomputable def Ns276p1221 := nat_lit 225840308491453706514625259313302229534825118091684746194642705140641 

noncomputable def Ns276p1222 := BSN.sin_dyadic_bound_f 96817859 134217728 3 2 134217728 67108864 Ns276p1219 Ns276p137 Ns276p1220 Ns276p1221 Ns276p140 Ns276p1220 88637180 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 96817859) qz367 0 2 Ns276p1219 Ns276p137 Ns276p1220 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 96817859) qz368 0 2 Ns276p1221 Ns276p140 Ns276p1220 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1223 := nat_lit 29498238767646937993958289936 

noncomputable def Ns276p1224 := BSN.cos_dyadic_bound_f 13105362 134217728 2 1 134217728 67108864 Ns276p1223 Ns276p122 Ns276p1223 Ns276p1223 Ns276p123 Ns276p1223 133578415 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 13105362) qz369 0 1 Ns276p1223 Ns276p122 Ns276p1223 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 13105362) qz370 0 1 Ns276p1223 Ns276p123 Ns276p1223 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1225 := Ns276p1159 92771 BSN.abs_quadSignPos (BSN.cos_quad_nat3 115 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 88637180 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 133578415 134217728) qz191 rfl rfl (Ns276p1218 rfl) (Ns276p1194 rfl) RS277to288.d35 RS277to288.d37 RS277to288.d39 RS277to288.d41 RS277to288.d17 (Ns276p1222 rfl rfl) (Ns276p1224 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p1226 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) 151977890 134217728 92771 134217728 151977890 134217728 92771 134217728 40796254204067840 75988945 33554432 92771 67108864 (Ns276p1225 rfl) 

noncomputable def Ns276p1227 := @Enclosure.Real.IsNear.mulLit_tf qz686 (Zeta.RiemannSiegel.correction qz190) 5378543 16777216 1 16777216 33842233666347 70368744177664 4373453171974377 15876947905085440000 182021908990494992421 1180591620717411303424 

noncomputable abbrev qz690 := (@HPow.hPow Real Real Real qz7 qz189 qz9)

noncomputable def Ns276p1228 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz690 1 1 0 1 5378543 16777216 1 16777216 5378543 16777216 1 16777216 

noncomputable def Ns276p1229 := @Enclosure.Real.IsNear.sqrt_image qz189 1588330756857 16777216000 594841 16777216000 81620705 81620736 8388608 (@Enclosure.Real.IsNear.of_eq qz189 (@HMul.hMul Real Real Real qz5 qz188 qz3) Bool.false 1588330756857 16777216000 594841 16777216000 (BSN.t_div_two_pi_mk qz188 594841 1000 qz191) (@Enclosure.Real.IsNear.mulLit_ff qz188 qz3 594841 1000 0 1 2670177 16777216 1 16777216 1588330756857 16777216000 594841 16777216000 (Enclosure.Real.IsNear.const Bool.false 594841 1000) RS277to288.d44 rfl)) 

noncomputable abbrev qz776 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 594841 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz691 := qz776

noncomputable abbrev qz504 := qz691

noncomputable abbrev qz197 := qz504

noncomputable def Ns276p1230 := @Enclosure.Real.IsNear.sqrt_image qz197 163241441 16777216 31 16777216 26166468 26166474 8388608 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 163241441 16777216 31 16777216 163241441 16777216 31 16777216 (Ns276p1229 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns276p1231 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz197) 26166471 8388608 3 8388608 2689271 2689272 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz197) Bool.false 52332942 16777216 6 16777216 26166471 8388608 3 8388608 (Ns276p1230 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns276p1232 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz197)) Bool.false 5378543 16777216 1 16777216 5378543 16777216 1 16777216 (Ns276p1231 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz505 := (@HMul.hMul Real Real Real qz584 qz582 qz685)

noncomputable abbrev qz198 := (Real.cos qz505)

noncomputable abbrev qz692 := (@HMul.hMul Real Real Real qz732 qz775 qz775)

noncomputable abbrev qz506 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz692 qz685) qz599)

noncomputable abbrev qz199 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz506))

noncomputable def Ns276p1233 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz190) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz198) qz199) Bool.false 33842233666347 

noncomputable def Ns276p1234 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz198) qz199 133516263 16777216 12645 

noncomputable abbrev qz200 := (@Neg.neg Real Real.instNeg (Real.cos qz505))

noncomputable def Ns276p1235 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz198) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz200)) Bool.true 133516263 16777216 12645 16777216 (BSN.inv_eq_neg_inv_neg qz198) 

noncomputable def Ns276p1236 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz200) Bool.false 133516263 16777216 12645 16777216 133516263 16777216 

noncomputable def Ns276p1237 := @Enclosure.Real.IsNear.recentre' qz198 Bool.true 2108170 16777216 720727216 60565749760000 1054085 8388608 45045451 3785359360000 

noncomputable abbrev qz201 := qz505

noncomputable def Ns276p1238 := @Enclosure.Real.IsNear.cos_image qz201 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 38473505) qz365) Bool.false 38473505 8388608 195 16777216 Bool.true 2108170 16777216 1 

noncomputable def Ns276p1239 := nat_lit 836568337785562017321362201 

noncomputable def Ns276p1240 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz190 884279719003555 140737488355328 1 500000000000000 12246497 16777216 31 16777216 10829328925937879296835 2361183241434822606848 Ns276p1239 

noncomputable def Ns276p1241 := @Enclosure.Real.IsNear.subLit_ff_p qz197 qz1 163241441 16777216 31 16777216 9 1 0 1 12246497 12246497 16777216 31 

noncomputable def Ns276p1242 := @Ns276p1241 16777216 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 163241441 16777216 31 16777216 163241441 16777216 31 16777216 (Ns276p1229 rfl rfl rfl rfl rfl rfl) rfl) qz377 

noncomputable def Ns276p1243 := @Enclosure.Real.IsNear.recentre' qz201 Bool.false 10829328925937879296835 2361183241434822606848 Ns276p1239 Ns276p166 38473505 8388608 195 16777216 (@Ns276p1240 Ns276p166 RS277to288.d43 (Ns276p1242 rfl rfl) rfl) 

noncomputable def Ns276p1244 := nat_lit 1746663935376042837934080 

noncomputable def Ns276p1245 := nat_lit 236095717768022616531900451205685896737177526134074174019164179834950326274628640914024134777344494030117407425275395042359331892588881 

noncomputable def Ns276p1246 := nat_lit 224034333314918680238710328433116590714325089027083230014556980084576130528475248085410161502214336413573620755171779892032139601 

noncomputable def Ns276p1247 := nat_lit 1429842578080710411556752729855952376147707972231256119431397978552285489232608235506556888851204128579303856406544421387616847615848785 

noncomputable def Ns276p1248 := BSN.cos_dyadic_bound_f 49643174843 34359738368 4 3 16777216 7227051 Ns276p1245 Ns276p1020 Ns276p1246 Ns276p1247 Ns276p1023 Ns276p1246 2108170 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 49643174843) qz378 0 3 Ns276p1245 Ns276p1020 Ns276p1246 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 49643174843) qz379 0 3 Ns276p1247 Ns276p1023 Ns276p1246 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1249 := @Ns276p1238 3610000 (Ns276p1243 rfl) (Enclosure.sfrac_false_div 38473505 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 38473505) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns276p1244) qz366) 226375608064910080 72057594037927936 Bool.false 2108170 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 38473505 8388608 226375608064910080 72057594037927936 0 Ns276p1244 Ns276p104 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 2108170 16777216 Ns276p1244 Ns276p104 49643174843 34359738368 7227051 7220000 (Ns276p1248 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p1250 := @Enclosure.Real.IsNear.inv_image qz200 1054085 8388608 45045451 3785359360000 66751809 66764454 8388608 (@Enclosure.Real.IsNear.neg qz198 Bool.true 1054085 8388608 45045451 3785359360000 (Ns276p1237 (Ns276p1249 rfl rfl) rfl)) 

noncomputable def Ns276p1251 := Ns276p1235 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz200) Bool.false 133516263 16777216 12645 16777216 (@Ns276p1236 12645 16777216 (Ns276p1250 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p1252 := @Enclosure.Real.IsNear.recentre' qz199 Bool.true 506938 8388608 

noncomputable abbrev qz202 := (@HMul.hMul Real Real Real qz346 qz343 qz506)

noncomputable def Ns276p1253 := @Enclosure.Real.IsNear.cos_image qz202 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 27368083)) qz376) Bool.true 27368083 16777216 

noncomputable def Ns276p1254 := nat_lit 64621059654010784770368873245 

noncomputable def Ns276p1255 := nat_lit 6905075381933158680210528411603557 

noncomputable def Ns276p1256 := @Enclosure.Real.IsNear.recentre' qz202 Bool.true Ns276p1254 Ns276p184 Ns276p1255 

noncomputable def Ns276p1257 := nat_lit 241785163922925834941235200000000000000 

noncomputable abbrev qz203 := qz506

noncomputable def Ns276p1258 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz203 884279719003555 140737488355328 1 500000000000000 73077622685759 

noncomputable abbrev qz507 := (@HSub.hSub Real Real Real qz588 qz692 qz685)

noncomputable abbrev qz204 := qz507

noncomputable def Ns276p1259 := @Enclosure.Real.IsNear.subLit_tf qz204 qz31 55485436641343 281474976710656 1279377471 281474976710656 1 16 

noncomputable abbrev qz508 := qz692

noncomputable abbrev qz205 := qz508

noncomputable def Ns276p1260 := @Enclosure.Real.IsNear.subLit_ff_n qz205 qz190 149976688771009 281474976710656 759283775 281474976710656 12246497 16777216 31 16777216 

noncomputable def Ns276p1261 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz190 12246497 16777216 31 16777216 12246497 16777216 31 16777216 149976688771009 281474976710656 

noncomputable def Ns276p1262 := nat_lit 70581381745712800182779278419339522647425585982810726331875263839166359836410898199396281275441 

noncomputable def Ns276p1263 := nat_lit 176576351635656605280554148237736611926169329030789085518082669627778764491656139403482161 

noncomputable def Ns276p1264 := nat_lit 426994674766688537646345590740002472219408367053780025843607607216293290100308270302028849796145 

noncomputable def Ns276p1265 := BSN.cos_dyadic_bound_t 27368083 16777216 4 3 8388608 3610000 Ns276p1262 Ns276p193 Ns276p1263 Ns276p1264 Ns276p196 Ns276p1263 506938 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 27368083) qz600 0 3 Ns276p1262 Ns276p193 Ns276p1263 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 27368083) (BSN.cosOddQ 16777216) 0 3 Ns276p1264 Ns276p196 Ns276p1263 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1266 := @Ns276p1252 54674288 1892679680000 253469 4194304 3417143 118292480000 (@Ns276p1253 15 524288 Bool.true 506938 8388608 1 3610000 (@Ns276p1256 Ns276p1257 27368083 16777216 15 524288 (@Ns276p1258 281474976710656 1279377471 281474976710656 Ns276p1254 Ns276p184 Ns276p1255 Ns276p1257 RS277to288.d43 (@Ns276p1259 0 1 1169241962972144 73077622685759 281474976710656 1279377471 281474976710656 (@Ns276p1260 930891155386126041088 55485436641343 281474976710656 1279377471 281474976710656 (@Ns276p1261 759283775 281474976710656 (Ns276p1242 rfl rfl) (Ns276p1242 rfl rfl) rfl) (Ns276p1242 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 27368083 16777216) (BSN.cos_neg_of_bound 27368083 16777216 Bool.true 506938 8388608 1 3610000 (Ns276p1265 rfl rfl)) rfl rfl) 

noncomputable def Ns276p1267 := @Ns276p1227 23530445971374723108963 Ns276p926 (Ns276p1228 qz33 (@Enclosure.Real.IsNear.of_eq qz690 (@Inv.inv Real Real.instInv (Real.sqrt qz197)) Bool.false 5378543 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz189 (BSN.t_div_two_pi_nonneg qz188 594841 1000 qz191)) Ns276p1232) rfl) (@Ns276p1233 70368744177664 4373453171974377 15876947905085440000 (BSN.correction_mk qz190 (BSN.cos_two_pi_p_ne_zero_mk qz188 594841 1000 9 qz191 rfl rfl (@BSN.floor_sqrt_eq_dec qz188 594841 1000 9 qz191 rfl rfl rfl))) (@Ns276p1234 16777216 253469 4194304 3417143 118292480000 33842233666347 70368744177664 4373453171974377 15876947905085440000 Ns276p1251 (Ns276p1266 rfl) rfl)) 

noncomputable def Ns276p1268 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz188) (hardyZApproximantRS₀ qz188) Bool.false 2855645224508284954661 1180591620717411303424 391760529497045061668963 Ns276p926 (@Eq.refl Real (hardyZApproximantRS₀ qz188)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz188) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (@HMul.hMul Real Real Real qz5 qz686 (Zeta.RiemannSiegel.correction qz190))) Bool.false 2855645224508284954661 1180591620717411303424 391760529497045061668963 Ns276p926 (BSN.hardyZApproximantRS₀_eq qz188 9 (@BSN.floor_sqrt_eq_dec qz188 594841 1000 9 qz191 rfl rfl rfl)) (@Ns276p1157 2855645224508284954661 1180591620717411303424 391760529497045061668963 Ns276p926 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 9)) Bool.false 75988945 33554432 92771 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (Ns276p1226 (Ns276p1225 rfl) rfl rfl)) (Ns276p1267 rfl) rfl rfl)) 

theorem RS277to288.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz188) Bool.false 2855645224508284954661 1180591620717411303424 391760529497045061668963 Ns276p926 := Ns276p1268 

noncomputable def Ns276p1269 := nat_lit 13318549221218296266752000 

noncomputable def Ns276p1270 := nat_lit 6756068873730340861681598464 

noncomputable abbrev qz777 := (Enclosure.sfrac Bool.false 596222 1000)

noncomputable abbrev qz693 := qz777

noncomputable abbrev qz509 := qz693

noncomputable abbrev qz206 := qz509

noncomputable abbrev qz778 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 596222 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz694 := qz778

noncomputable abbrev qz510 := qz694

noncomputable abbrev qz207 := qz510

noncomputable abbrev qz779 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 596222 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz695 := qz779

noncomputable abbrev qz511 := qz695

noncomputable abbrev qz208 := qz511

noncomputable abbrev qz696 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz207 qz9))

noncomputable def Ns276p1271 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) (@HMul.hMul Real Real Real qz5 qz696 (Zeta.RiemannSiegel.correction qz208)) 33456935 67108864 1453 1048576 46471884924790709839 295147905179352825856 2802830772490155436809 Ns276p1269 Ns276p1270 

noncomputable def Ns276p1272 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 596222 1000 115 159 134217728 67108864 2251799813685248 Bool.false 142098593181 1896 

noncomputable def Ns276p1273 := Ns276p1272 279097919 38 47453128 8 294906479 38 44739240 8 Bool.true 98842347 76108 Bool.true 60424155 Bool.true 209371994 7074237752028440 1 Bool.false 58403655 Bool.false Bool.false 134209822 Bool.false Bool.true 33456935 

noncomputable def Ns276p1274 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 596222 1000 6 64 134217728 67108864 2251799813685248 Bool.false 142098593181 1896 

noncomputable def Ns276p1275 := Ns276p1274 240485871 38 54794152 8 261175631 38 50729528 8 Bool.true 74275767 56785 Bool.true 19401513 Bool.true 127026180 7074237752028440 1 Bool.false 132817899 Bool.true Bool.false 78462658 Bool.false Bool.true 98842347 

noncomputable def Ns276p1276 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 596222 1000 147 63 134217728 67108864 2251799813685248 Bool.false 142098593181 1896 

noncomputable def Ns276p1277 := Ns276p1276 186065264 38 67108856 8 216015088 38 60023992 8 Bool.true 148815932 33508 Bool.false 170568370 Bool.false 23436393 7074237752028440 1 Bool.false 128224562 Bool.false Bool.false 23317477 Bool.false Bool.true 74275767 

noncomputable def Ns276p1278 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 596222 1000 410 257 134217728 67108864 2251799813685248 Bool.false 142098593181 1896 

noncomputable def Ns276p1279 := Ns276p1278 93032624 38 94906264 8 147453232 38 77490640 16 Bool.true 134217720 1942 Bool.false 190723239 Bool.false 752759 7074237752028440 1 Bool.false 20030367 Bool.true Bool.false 752755 Bool.true Bool.true 148815932 

noncomputable def Ns276p1280 := nat_lit 3764966504647083178414714488570664938757812063690269191 

noncomputable def Ns276p1281 := nat_lit 3556159416750652498658825687142279487025565401088000 

noncomputable def Ns276p1282 := nat_lit 36164460963759472932101067023360000 

noncomputable def Ns276p1283 := nat_lit 129372325927785004702266658101226475520 

noncomputable abbrev qz780 := (@Eq.refl Real (Enclosure.sfrac Bool.false 596222 1000))

noncomputable abbrev qz697 := qz780

noncomputable abbrev qz512 := qz697

noncomputable abbrev qz209 := qz512

noncomputable def Ns276p1284 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz206 596222 1000 1421923693136 16000000 1192444 4000 2000 Ns276p1282 Ns276p1283 qz209 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns276p1285 := nat_lit 77106514015172263493933352725927217945759991064376713031680 

noncomputable abbrev qz698 := (@HSub.hSub Real Real Real qz736 qz737 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz738 (@Nat.cast Real Real.instNatCast 1192444))))

noncomputable abbrev qz513 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 596222 4000) (Real.log (Enclosure.sfrac Bool.false 1421923693136 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz698))

noncomputable abbrev qz699 := (Enclosure.sfrac Bool.false 596222 2000)

noncomputable abbrev qz210 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz513 qz699) (@HMul.hMul Real Real Real qz346 qz699 (Real.log Real.pi)))

noncomputable def Ns276p1286 := @Enclosure.Real.IsNear.addLit_ft_p qz210 (Enclosure.sfrac Bool.true Ns276p1282 Ns276p1283) 596004855141851328859 562949953421312000 5217754171057742507 369664000000000000000000 Ns276p1282 Ns276p1283 0 1 Ns276p1285 

noncomputable def Ns276p1287 := nat_lit 3999720876705420153661790617600 

noncomputable abbrev qz211 := (@HSub.hSub Real Real Real qz350 qz513 qz699)

noncomputable def Ns276p1288 := @Enclosure.Real.IsNear.subLit_ff_p qz211 (@HMul.hMul Real Real Real qz5 qz699 (Real.log Real.pi)) 157623045065119549919 112589990684262400 1888194610989693 361000000000000000000 11450670372471 33554432000 298111 33554432000 Ns276p1287 596004855141851328859 562949953421312000 

noncomputable def Ns276p1289 := nat_lit 1576230450651195499190000 

noncomputable abbrev qz212 := qz513

noncomputable def Ns276p1290 := @Enclosure.Real.IsNear.subLit_ff_p qz212 qz699 955936798889978491227 562949953421312000 1888194610989693 361000000000000000000 596222 2000 0 1 Ns276p1289 157623045065119549919 112589990684262400 1888194610989693 361000000000000000000 

noncomputable def Ns276p1291 := nat_lit 2152578305635325953684740721707319296 

noncomputable def Ns276p1292 := nat_lit 27551256206853684324204544 

noncomputable def Ns276p1293 := nat_lit 1311324703437257242735413585516147669520952853295521512256756182218998167217931642996379204125112401920 

noncomputable def Ns276p1294 := nat_lit 10121722264675282190435371481567996010229263324404704992382964851071579769781935214010345700630462464 

noncomputable def Ns276p1295 := nat_lit 39636662330767650097260628852207783431724684310577258963586212513800532862233388263429510266880 

noncomputable def Ns276p1296 := BSN.log_dyadic_bound 373347693136 2470499693136 5 4 Ns276p1293 67108864 28880000 Ns276p1294 Ns276p1295 20439857 2843847386272 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 373347693136) (BSN.artanhQ 2470499693136) 0 4 Ns276p1294 Ns276p1293 Ns276p1295 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz514 := (Real.log (Enclosure.sfrac Bool.false 1421923693136 16000000))

noncomputable def Ns276p1297 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 596222 4000) qz514 596222 4000 0 1 3207388358057207 281474976710656 781250361 22562500000000000 956157750808792035977 562949953421312000 232899326368071 45125000000000000000 (Enclosure.Real.IsNear.const Bool.false 596222 4000) (BSN.isNear_log_sfrac 1421923693136 16000000 3207388358057207 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1421923693136) qz353)) Bool.false Ns276p1292 Ns276p92 1000000462080000 28880000000000000000000 3207388358057207 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1421923693136 16000000 16 2843847386272 2097152000000 20439857 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns276p1296 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p1298 := BSN.arctan_dyadic_bound_f 1000 1192444 1 0 8388608 3610000 0 1 1 0 1 1 7034 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1192444) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1192444) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns276p1299 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1192444))) 884279719003555 562949953421312 1 2000000000000000 7034 8388608 1 3610000 7413916135098607992832 883807675254179 562949953421312 200000000361 722000000000000000 qz17 (Ns276p1298 rfl) rfl rfl 

noncomputable abbrev qz515 := (@HMul.hMul Real Real Real qz584 qz589 qz698)

noncomputable abbrev qz213 := qz515

noncomputable abbrev qz516 := qz698

noncomputable abbrev qz214 := qz516

noncomputable def Ns276p1300 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 596222 4000) qz514) qz213 956157750808792035977 562949953421312000 232899326368071 45125000000000000000 883807675254179 2251799813685248 200000000361 2888000000000000000 Ns276p1291 955936798889978491227 562949953421312000 1888194610989693 361000000000000000000 (Ns276p1297 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz214 1 4 0 1 883807675254179 562949953421312 200000000361 722000000000000000 883807675254179 2251799813685248 200000000361 2888000000000000000 qz361 Ns276p1299 rfl) 

noncomputable def Ns276p1301 := @Ns276p1286 Ns276p1280 Ns276p1281 5217754171057742507 369664000000000000000000 (@Ns276p1288 5217754171057742507 369664000000000000000000 (Ns276p1290 (Ns276p1300 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 596222 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz699 (Real.log Real.pi) 596222 2000 0 1 38410761 33554432 1 33554432 11450670372471 33554432000 298111 33554432000 (Enclosure.Real.IsNear.const Bool.false 596222 2000) RS277to288.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns276p1282 Ns276p1283) 

noncomputable def Ns276p1302 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns276p1280 Ns276p1281 5217754171057742507 369664000000000000000000 17762324147 16777216 119 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz362 qz210 (Enclosure.sfrac Bool.true Ns276p1282 Ns276p1283)) Bool.false Ns276p1280 Ns276p1281 5217754171057742507 369664000000000000000000 Ns276p1284 (Ns276p1301 rfl rfl)) 

noncomputable def Ns276p1303 := nat_lit 3798670351965457685151744 

noncomputable def Ns276p1304 := nat_lit 857787112759438317378804097060064114850629827885129120885085464518017363906485277314092612482813835728483574093327304228437242398642176 

noncomputable def Ns276p1305 := nat_lit 612380960459135184933087024407968110143956652014408651293817395497205053480665083971292282618375403988813539028913069108742066176 

noncomputable def Ns276p1306 := nat_lit 4283602007738272419128586430925990328677033968326269967984815741737990581861130206408269691643308052250475514942886378263049464390619136 

noncomputable def Ns276p1307 := BSN.sin_dyadic_bound_f 53982352482 34359738368 4 3 16777216 7227051 Ns276p1304 Ns276p106 Ns276p1305 Ns276p1306 Ns276p109 Ns276p1305 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53982352482) qz363 0 3 Ns276p1304 Ns276p106 Ns276p1305 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53982352482) qz364 0 3 Ns276p1306 Ns276p109 Ns276p1305 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1308 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz206) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17762324147) qz376) Bool.false 17762324147 16777216 119 8388608 Bool.true 16777215 16777216 1 3610000 (Ns276p1302 rfl) (Enclosure.sfrac_false_div 17762324147 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17762324147) qz376) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns276p1303) qz380) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 168 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q1 17762324147 16777216 226375608064910080 72057594037927936 168 Ns276p1303 Ns276p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns276p1303 Ns276p92 53982352482 34359738368 7227051 7220000 (Ns276p1307 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p1309 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns276p1280 Ns276p1281 5217754171057742507 369664000000000000000000 142098593181 134217728 1896 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz362 qz210 (Enclosure.sfrac Bool.true Ns276p1282 Ns276p1283)) Bool.false Ns276p1280 Ns276p1281 5217754171057742507 369664000000000000000000 Ns276p1284 (Ns276p1301 rfl rfl)) 

noncomputable def Ns276p1310 := Ns276p1279 33508 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 410 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 20030367 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 257 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 752755 134217728) qz209 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) Bool.true 16777215 16777216 27373663 1892679680000 134217720 134217728 1942 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.true 16777215 16777216 27373663 1892679680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz206) qz206) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.true 16777215 16777216 437978608 30282874880000 16777215 16777216 27373663 1892679680000 (Ns276p1308 rfl rfl) rfl)) rfl) (Ns276p1309 rfl) RS277to288.d7 

noncomputable def Ns276p1311 := nat_lit 2787868898235479790650796911483167807292275054166166173819608738163605974553858496262353305489157004528801 

noncomputable def Ns276p1312 := nat_lit 2316558988617702256226059687432919586832277552289694449537759341615347223807694666944343736898882721 

noncomputable def Ns276p1313 := nat_lit 16885760766232471022490885356868374255374884372902739580455662492101006091479240186878972069917588535184545 

noncomputable def Ns276p1314 := BSN.cos_dyadic_bound_f 190723239 134217728 4 3 134217728 67108864 Ns276p1311 Ns276p116 Ns276p1312 Ns276p1313 Ns276p119 Ns276p1312 20030367 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 190723239) qz369 0 3 Ns276p1311 Ns276p116 Ns276p1312 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 190723239) qz370 0 3 Ns276p1313 Ns276p119 Ns276p1312 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1315 := BSN.sin_dyadic_bound_f 752759 134217728 1 0 134217728 67108864 0 1 1 0 1 1 752755 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 752759) qz367 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 752759) qz368 0 0 rfl) rfl rfl 

noncomputable def Ns276p1316 := nat_lit 831361186211011531418171920901957416056453500171680772832240775840000 

noncomputable def Ns276p1317 := nat_lit 716453475673716101227861503732667309960198515238330116912100000000 

noncomputable def Ns276p1318 := nat_lit 2176214563020606089550367064689559390217442655234492346752296727200000 

noncomputable def Ns276p1319 := BSN.sin_dyadic_bound_f 170568370 134217728 3 2 134217728 67108864 Ns276p1316 Ns276p137 Ns276p1317 Ns276p1318 Ns276p140 Ns276p1317 128224562 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 170568370) qz367 0 2 Ns276p1316 Ns276p137 Ns276p1317 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 170568370) qz368 0 2 Ns276p1318 Ns276p140 Ns276p1317 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1320 := nat_lit 301691509470957173458631501601 

noncomputable def Ns276p1321 := BSN.sin_dyadic_bound_f 23436393 134217728 2 1 134217728 67108864 Ns276p1320 Ns276p126 Ns276p1320 Ns276p1320 Ns276p127 Ns276p1320 23317477 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 23436393) qz367 0 1 Ns276p1320 Ns276p126 Ns276p1320 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 23436393) qz368 0 1 Ns276p1320 Ns276p127 Ns276p1320 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1322 := Ns276p1277 56785 BSN.abs_quadSignPos (BSN.cos_quad_nat3 147 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 128224562 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 23317477 134217728) qz209 rfl rfl (Ns276p1310 RS277to288.d9 RS277to288.d11 RS277to288.d13 RS277to288.d17 (Ns276p1314 rfl rfl) (Ns276p1315 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns276p1309 rfl) RS277to288.d19 RS277to288.d21 RS277to288.d23 RS277to288.d25 RS277to288.d17 (Ns276p1319 rfl rfl) (Ns276p1321 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns276p1323 := nat_lit 141691042745546642865581910561 

noncomputable def Ns276p1324 := BSN.cos_dyadic_bound_f 19401513 134217728 2 1 134217728 67108864 Ns276p1323 Ns276p122 Ns276p1323 Ns276p1323 Ns276p123 Ns276p1323 132817899 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 19401513) qz369 0 1 Ns276p1323 Ns276p122 Ns276p1323 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 19401513) qz370 0 1 Ns276p1323 Ns276p123 Ns276p1323 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1325 := nat_lit 142013331462058719265466788174114678876496571383854412279689420800000 

noncomputable def Ns276p1326 := nat_lit 67786920317322176502199595964799192882503396849849454617600000000 

noncomputable def Ns276p1327 := nat_lit 425904420545541513443395965330414438243724707357863537929833062400000 

noncomputable def Ns276p1328 := BSN.cos_dyadic_bound_f 127026180 134217728 3 2 134217728 67108864 Ns276p1325 Ns276p131 Ns276p1326 Ns276p1327 Ns276p134 Ns276p1326 78462658 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 127026180) qz369 0 2 Ns276p1325 Ns276p131 Ns276p1326 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 127026180) qz370 0 2 Ns276p1327 Ns276p134 Ns276p1326 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1329 := Ns276p1275 76108 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 6 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132817899 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 78462658 134217728) qz209 rfl rfl (Ns276p1322 rfl rfl) (Ns276p1309 rfl) RS277to288.d27 RS277to288.d29 RS277to288.d31 RS277to288.d33 RS277to288.d17 (Ns276p1324 rfl rfl) (Ns276p1328 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p1330 := nat_lit 13330374267665732457636669200625 

noncomputable def Ns276p1331 := BSN.sin_dyadic_bound_f 60424155 134217728 2 1 134217728 67108864 Ns276p1330 Ns276p126 Ns276p1330 Ns276p1330 Ns276p127 Ns276p1330 58403655 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 60424155) qz367 0 1 Ns276p1330 Ns276p126 Ns276p1330 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 60424155) qz368 0 1 Ns276p1330 Ns276p127 Ns276p1330 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1332 := nat_lit 10522098895716586068415570807807394385682023493120725077017257326556895205147568149839992724762515742068736 

noncomputable def Ns276p1333 := nat_lit 7096154621321964769765193072275770596725588123757355311681341771954478128344423542319619008214798336 

noncomputable def Ns276p1334 := nat_lit 52546904941885935980465327727995681293538594991589802330101059650995010347357366351209755532049933157994496 

noncomputable def Ns276p1335 := BSN.sin_dyadic_bound_f 209371994 134217728 4 3 134217728 67108864 Ns276p1332 Ns276p255 Ns276p1333 Ns276p1334 Ns276p258 Ns276p1333 134209822 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 209371994) qz367 0 3 Ns276p1332 Ns276p255 Ns276p1333 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 209371994) qz368 0 3 Ns276p1334 Ns276p258 Ns276p1333 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1336 := Ns276p1273 92992 BSN.abs_quadSignPos (BSN.cos_quad_nat3 115 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 58403655 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 159 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 134209822 134217728) qz209 rfl rfl (Ns276p1329 rfl) (Ns276p1309 rfl) RS277to288.d35 RS277to288.d37 RS277to288.d39 RS277to288.d41 RS277to288.d17 (Ns276p1331 rfl rfl) (Ns276p1335 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p1337 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) 33456935 134217728 92992 134217728 33456935 134217728 92992 134217728 8981027603087360 33456935 67108864 1453 1048576 (Ns276p1336 rfl) 

noncomputable def Ns276p1338 := @Enclosure.Real.IsNear.mulLit_tf qz696 (Zeta.RiemannSiegel.correction qz208) 2687713 8388608 1 8388608 17290493785903 35184372088832 1042540441043231 1587694790508544000 46471884924790709839 295147905179352825856 

noncomputable abbrev qz700 := (@HPow.hPow Real Real Real qz7 qz207 qz9)

noncomputable def Ns276p1339 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz700 1 1 0 1 2687713 8388608 1 8388608 2687713 8388608 1 8388608 

noncomputable def Ns276p1340 := @Enclosure.Real.IsNear.sqrt_image qz207 796009135647 8388608000 298111 8388608000 81715396 81715428 8388608 (@Enclosure.Real.IsNear.of_eq qz207 (@HMul.hMul Real Real Real qz5 qz206 qz3) Bool.false 796009135647 8388608000 298111 8388608000 (BSN.t_div_two_pi_mk qz206 596222 1000 qz209) (@Enclosure.Real.IsNear.mulLit_ff qz206 qz3 596222 1000 0 1 2670177 16777216 1 16777216 796009135647 8388608000 298111 8388608000 (Enclosure.Real.IsNear.const Bool.false 596222 1000) RS277to288.d44 rfl)) 

noncomputable abbrev qz781 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 596222 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz701 := qz781

noncomputable abbrev qz517 := qz701

noncomputable abbrev qz215 := qz517

noncomputable def Ns276p1341 := @Enclosure.Real.IsNear.sqrt_image qz215 20428853 2097152 1 524288 26181642 26181649 8388608 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 163430824 16777216 32 16777216 20428853 2097152 1 524288 (Ns276p1340 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns276p1342 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz215) 52363291 16777216 7 16777216 2687712 2687714 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz215) Bool.false 52363291 16777216 7 16777216 52363291 16777216 7 16777216 (Ns276p1341 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns276p1343 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 5375426 16777216 2 16777216 2687713 8388608 1 8388608 (Ns276p1342 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz216 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz511))

noncomputable abbrev qz702 := (@HMul.hMul Real Real Real qz732 qz779 qz779)

noncomputable abbrev qz518 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz702 qz695) qz599)

noncomputable abbrev qz217 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz518))

noncomputable def Ns276p1344 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz208) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz216) qz217) Bool.false 17290493785903 

noncomputable def Ns276p1345 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz216) qz217 152418383 8388608 533 

noncomputable abbrev qz703 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz216))

noncomputable def Ns276p1346 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz216) (@Neg.neg Real Real.instNeg qz703) Bool.true 152418383 8388608 533 131072 (BSN.inv_eq_neg_inv_neg qz216) 

noncomputable def Ns276p1347 := @Enclosure.Real.IsNear.recentre' qz703 Bool.false 304836766 16777216 68224 16777216 152418383 8388608 

noncomputable def Ns276p1348 := @Enclosure.Real.IsNear.recentre' qz216 Bool.true 923363 16777216 372998608 30282874880000 923363 16777216 23312413 1892679680000 

noncomputable abbrev qz218 := (@HMul.hMul Real Real Real qz346 qz343 qz511)

noncomputable def Ns276p1349 := @Enclosure.Real.IsNear.cos_image qz218 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39068469) qz365) Bool.false 39068469 8388608 101 8388608 Bool.true 923363 16777216 1 

noncomputable def Ns276p1350 := nat_lit 26986075412382276573730247 

noncomputable def Ns276p1351 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz208 884279719003555 140737488355328 1 500000000000000 1554485 2097152 1 524288 1374599558995241194175 295147905179352825856 Ns276p1350 

noncomputable def Ns276p1352 := @Enclosure.Real.IsNear.subLit_ff_p qz215 qz1 20428853 2097152 1 524288 9 1 0 1 1554485 1554485 2097152 1 

noncomputable def Ns276p1353 := @Ns276p1352 524288 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 163430824 16777216 32 16777216 20428853 2097152 1 524288 (Ns276p1340 rfl rfl rfl rfl rfl rfl) rfl) qz377 

noncomputable def Ns276p1354 := @Enclosure.Real.IsNear.recentre' qz218 Bool.false 1374599558995241194175 295147905179352825856 Ns276p1350 Ns276p556 39068469 8388608 101 8388608 (@Ns276p1351 Ns276p556 RS277to288.d43 (Ns276p1353 rfl rfl) rfl) 

noncomputable def Ns276p1355 := nat_lit 1832407284134406350962688 

noncomputable def Ns276p1356 := nat_lit 286138478524865460307539416889200185418588401407402586580801386027197460890595478404862601003596644574365525406184141443311098520039761 

noncomputable def Ns276p1357 := nat_lit 398168093261919711316958547727691836129483225640009524428224493055013139785417964660025562820617217561487164599114197625982316881 

noncomputable def Ns276p1358 := nat_lit 1732280216940993188162957921198620070844611309067164638081001901864719827866910820977697680507640210478840143080520933540489468367761745 

noncomputable def Ns276p1359 := BSN.cos_dyadic_bound_f 52080147387 34359738368 4 3 16777216 7227051 Ns276p1356 Ns276p1020 Ns276p1357 Ns276p1358 Ns276p1023 Ns276p1357 923363 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 52080147387) qz378 0 3 Ns276p1356 Ns276p1020 Ns276p1357 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 52080147387) qz379 0 3 Ns276p1358 Ns276p1023 Ns276p1357 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1360 := @Ns276p1349 3610000 (Ns276p1354 rfl) (Enclosure.sfrac_false_div 39068469 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39068469) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns276p1355) qz366) 226375608064910080 72057594037927936 Bool.false 923363 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 39068469 8388608 226375608064910080 72057594037927936 0 Ns276p1355 Ns276p104 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 923363 16777216 Ns276p1355 Ns276p104 52080147387 34359738368 7227051 7220000 (Ns276p1359 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p1361 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz216) 923363 16777216 23312413 1892679680000 152384271 152452495 8388608 (@Enclosure.Real.IsNear.neg qz216 Bool.true 923363 16777216 23312413 1892679680000 (Ns276p1348 (Ns276p1360 rfl rfl) rfl)) 

noncomputable def Ns276p1362 := Ns276p1346 (@Enclosure.Real.IsNear.neg qz703 Bool.false 152418383 8388608 533 131072 (@Ns276p1347 533 131072 (Ns276p1361 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p1363 := @Enclosure.Real.IsNear.recentre' qz217 Bool.true 226882 8388608 

noncomputable abbrev qz219 := (@HMul.hMul Real Real Real qz346 qz343 qz518)

noncomputable def Ns276p1364 := @Enclosure.Real.IsNear.cos_image qz219 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 26807407)) qz376) Bool.true 26807407 16777216 

noncomputable def Ns276p1365 := nat_lit 989018777193996212814550645 

noncomputable def Ns276p1366 := nat_lit 618970019642690137449562112 

noncomputable def Ns276p1367 := nat_lit 70246454413693341933055996638657 

noncomputable def Ns276p1368 := @Enclosure.Real.IsNear.recentre' qz219 Bool.true Ns276p1365 Ns276p1366 Ns276p1367 

noncomputable def Ns276p1369 := nat_lit 2361183241434822606848000000000000000 

noncomputable abbrev qz220 := qz518

noncomputable def Ns276p1370 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz220 884279719003555 140737488355328 1 500000000000000 1118445618439 

noncomputable abbrev qz519 := (@HSub.hSub Real Real Real qz588 qz702 qz695)

noncomputable abbrev qz221 := qz519

noncomputable def Ns276p1371 := @Enclosure.Real.IsNear.subLit_tf qz221 qz31 843567711495 4398046511104 2603063 549755813888 1 16 

noncomputable abbrev qz520 := qz702

noncomputable abbrev qz222 := qz520

noncomputable def Ns276p1372 := @Enclosure.Real.IsNear.subLit_ff_n qz222 qz208 2416423615225 4398046511104 1554487 549755813888 1554485 2097152 1 524288 

noncomputable def Ns276p1373 := @Enclosure.Real.IsNear.mulLit_ff qz208 qz208 1554485 2097152 1 524288 1554485 2097152 1 524288 2416423615225 4398046511104 

noncomputable def Ns276p1374 := nat_lit 64951149210095144366813902142019637572153215301128655667145445431284314699414816902197136575681 

noncomputable def Ns276p1375 := nat_lit 137739244374991256173571451308112783806609601505155509930778329837710414668049333650705601 

noncomputable def Ns276p1376 := nat_lit 393020976388450358165084072876508578692670191719194796996404318131495787373570138173698533215425 

noncomputable def Ns276p1377 := BSN.cos_dyadic_bound_t 26807407 16777216 4 3 8388608 3610000 Ns276p1374 Ns276p193 Ns276p1375 Ns276p1376 Ns276p196 Ns276p1375 226882 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 26807407) qz600 0 3 Ns276p1374 Ns276p193 Ns276p1375 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 26807407) (BSN.cosOddQ 16777216) 0 3 Ns276p1376 Ns276p196 Ns276p1375 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1378 := @Ns276p1363 455444304 15141437440000 113441 4194304 28465269 946339840000 (@Ns276p1364 125 4194304 Bool.true 226882 8388608 1 3610000 (@Ns276p1368 Ns276p1369 26807407 16777216 125 4194304 (@Ns276p1370 4398046511104 2603063 549755813888 Ns276p1365 Ns276p1366 Ns276p1367 Ns276p1369 RS277to288.d43 (@Ns276p1371 0 1 17895129895024 1118445618439 4398046511104 2603063 549755813888 (@Ns276p1372 1769089713297162240 843567711495 4398046511104 2603063 549755813888 (@Ns276p1373 1554487 549755813888 (Ns276p1353 rfl rfl) (Ns276p1353 rfl rfl) rfl) (Ns276p1353 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 26807407 16777216) (BSN.cos_neg_of_bound 26807407 16777216 Bool.true 226882 8388608 1 3610000 (Ns276p1377 rfl rfl)) rfl rfl) 

noncomputable def Ns276p1379 := @Ns276p1338 2802830772490155436809 Ns276p1269 (Ns276p1339 qz33 (@Enclosure.Real.IsNear.of_eq qz700 (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 2687713 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz207 (BSN.t_div_two_pi_nonneg qz206 596222 1000 qz209)) Ns276p1343) rfl) (@Ns276p1344 35184372088832 1042540441043231 1587694790508544000 (BSN.correction_mk qz208 (BSN.cos_two_pi_p_ne_zero_mk qz206 596222 1000 9 qz209 rfl rfl (@BSN.floor_sqrt_eq_dec qz206 596222 1000 9 qz209 rfl rfl rfl))) (@Ns276p1345 131072 113441 4194304 28465269 946339840000 17290493785903 35184372088832 1042540441043231 1587694790508544000 Ns276p1362 (Ns276p1378 rfl) rfl)) 

noncomputable def Ns276p1380 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (hardyZApproximantRS₀ qz206) Bool.true 100673271324192596401 295147905179352825856 21258195017361470892809 Ns276p1269 (@Eq.refl Real (hardyZApproximantRS₀ qz206)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) (@HMul.hMul Real Real Real qz5 qz696 (Zeta.RiemannSiegel.correction qz208))) Bool.true 100673271324192596401 295147905179352825856 21258195017361470892809 Ns276p1269 (BSN.hardyZApproximantRS₀_eq qz206 9 (@BSN.floor_sqrt_eq_dec qz206 596222 1000 9 qz209 rfl rfl rfl)) (@Ns276p1271 100673271324192596401 295147905179352825856 21258195017361470892809 Ns276p1269 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 9)) Bool.true 33456935 67108864 1453 1048576 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) (Ns276p1337 (Ns276p1336 rfl) rfl rfl)) (Ns276p1379 rfl) rfl rfl)) 

theorem RS277to288.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz206) Bool.true 100673271324192596401 295147905179352825856 21258195017361470892809 Ns276p1269 := Ns276p1380 

noncomputable def Ns276p1381 := nat_lit 33296373053045740666880000 

noncomputable def Ns276p1382 := nat_lit 682979091687191595821563904 

noncomputable abbrev qz782 := (Enclosure.sfrac Bool.false 597602 1000)

noncomputable abbrev qz704 := qz782

noncomputable abbrev qz521 := qz704

noncomputable abbrev qz223 := qz521

noncomputable abbrev qz783 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 597602 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz705 := qz783

noncomputable abbrev qz522 := qz705

noncomputable abbrev qz224 := qz522

noncomputable abbrev qz784 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 597602 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz706 := qz784

noncomputable abbrev qz523 := qz706

noncomputable abbrev qz225 := qz523

noncomputable abbrev qz707 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz224 qz9))

noncomputable def Ns276p1383 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (@HMul.hMul Real Real Real qz5 qz707 (Zeta.RiemannSiegel.correction qz225)) 142698141 33554432 93201 67108864 742079913077104045 4611686018427387904 24808251747973565881201 Ns276p1381 Ns276p1382 

noncomputable def Ns276p1384 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 597602 1000 115 159 134217728 67108864 2251799813685248 Bool.false 142520330296 1900 

noncomputable def Ns276p1385 := Ns276p1384 279097919 38 47453128 8 294906479 38 44739240 8 Bool.false 232598239 76278 Bool.true 23842168 Bool.true 194605820 7074237752028440 1 Bool.false 23716974 Bool.false Bool.false 133238490 Bool.false Bool.false 285396282 

noncomputable def Ns276p1386 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 597602 1000 5 64 134217728 67108864 2251799813685248 Bool.false 142520330296 1900 

noncomputable def Ns276p1387 := Ns276p1386 240485871 38 54794152 8 261175631 38 50729528 8 Bool.false 235242615 56910 Bool.true 140363614 Bool.true 65711436 7074237752028440 1 Bool.false 116141415 Bool.true Bool.false 118450704 Bool.false Bool.false 232598239 

noncomputable def Ns276p1388 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 597602 1000 148 63 134217728 67108864 2251799813685248 Bool.false 142520330296 1900 

noncomputable def Ns276p1389 := Ns276p1388 186065264 38 67108856 8 216015088 38 60023992 8 Bool.false 141697904 33580 Bool.false 124706707 Bool.false 147072686 7074237752028440 1 Bool.false 80332700 Bool.false Bool.false 119357656 Bool.false Bool.false 235242615 

noncomputable def Ns276p1390 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 597602 1000 412 258 134217728 67108864 2251799813685248 Bool.false 142520330296 1900 

noncomputable def Ns276p1391 := Ns276p1390 93032624 38 94906264 8 147453232 38 77490640 16 Bool.false 134217672 1942 Bool.false 62417905 Bool.false 8175699 7074237752028440 1 Bool.false 119963712 Bool.false Bool.false 133968798 Bool.true Bool.false 141697904 

noncomputable def Ns276p1392 := nat_lit 3828885910945245310232722786956684237629865664134413149 

noncomputable def Ns276p1393 := nat_lit 3605832000721344979790928652817807964048570974208000 

noncomputable def Ns276p1394 := nat_lit 36584929198064068525398563855360000 

noncomputable def Ns276p1395 := nat_lit 131179404005573632449920429383121080320 

noncomputable abbrev qz785 := (@Eq.refl Real (Enclosure.sfrac Bool.false 597602 1000))

noncomputable abbrev qz708 := qz785

noncomputable abbrev qz524 := qz708

noncomputable abbrev qz226 := qz524

noncomputable def Ns276p1396 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz223 597602 1000 1428513601616 16000000 1195204 4000 2000 Ns276p1394 Ns276p1395 qz226 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns276p1397 := nat_lit 78415583456158623953566162676872893186659648801472781291520 

noncomputable abbrev qz709 := (@HSub.hSub Real Real Real qz736 qz737 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz738 (@Nat.cast Real Real.instNatCast 1195204))))

noncomputable abbrev qz525 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 597602 4000) (Real.log (Enclosure.sfrac Bool.false 1428513601616 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz709))

noncomputable abbrev qz710 := (Enclosure.sfrac Bool.false 597602 2000)

noncomputable abbrev qz227 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz525 qz710) (@HMul.hMul Real Real Real qz346 qz710 (Real.log Real.pi)))

noncomputable def Ns276p1398 := @Enclosure.Real.IsNear.addLit_ft_p qz227 (Enclosure.sfrac Bool.true Ns276p1394 Ns276p1395) 597773748448430523161 562949953421312000 5229771796633444037 369664000000000000000000 Ns276p1394 Ns276p1395 0 1 Ns276p1397 

noncomputable def Ns276p1399 := nat_lit 20057958593697967496130199552000 

noncomputable abbrev qz228 := (@HSub.hSub Real Real Real qz350 qz525 qz710)

noncomputable def Ns276p1400 := @Enclosure.Real.IsNear.subLit_ff_p qz228 (@HMul.hMul Real Real Real qz5 qz710 (Real.log Real.pi)) 790328772319651693337 562949953421312000 1892507112982413 361000000000000000000 11477173797561 33554432000 298801 33554432000 Ns276p1399 597773748448430523161 562949953421312000 

noncomputable def Ns276p1401 := nat_lit 1580657544639303386674000 

noncomputable abbrev qz229 := qz525

noncomputable def Ns276p1402 := @Enclosure.Real.IsNear.subLit_ff_p qz229 qz710 958538781351893140249 562949953421312000 1892507112982413 361000000000000000000 597602 2000 0 1 Ns276p1401 790328772319651693337 562949953421312000 1892507112982413 361000000000000000000 

noncomputable def Ns276p1403 := nat_lit 2158437449258277643252503044006346752 

noncomputable def Ns276p1404 := nat_lit 27562435870511074805547008 

noncomputable def Ns276p1405 := nat_lit 1339570387065315002850944079862719823320229047150689046815716173037870473985950729368874178887517470720 

noncomputable def Ns276p1406 := nat_lit 10655557974690222911784456811492908902169037837291655882795466401880084296804596530655230067080167424 

noncomputable def Ns276p1407 := nat_lit 45591881390616488665945271920908102476507315385701700717607779380054502805114338201718310830080 

noncomputable def Ns276p1408 := BSN.log_dyadic_bound 379937601616 2477089601616 5 4 Ns276p1405 67108864 28880000 Ns276p1406 Ns276p1407 20750155 2857027203232 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 379937601616) (BSN.artanhQ 2477089601616) 0 4 Ns276p1406 Ns276p1405 Ns276p1407 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz526 := (Real.log (Enclosure.sfrac Bool.false 1428513601616 16000000))

noncomputable def Ns276p1409 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 597602 4000) qz526 597602 4000 0 1 3208689842199799 281474976710656 781250361 22562500000000000 958759733539142140999 562949953421312000 233438389117161 45125000000000000000 (Enclosure.Real.IsNear.const Bool.false 597602 4000) (BSN.isNear_log_sfrac 1428513601616 16000000 3208689842199799 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1428513601616) qz353)) Bool.false Ns276p1404 Ns276p92 1000000462080000 28880000000000000000000 3208689842199799 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1428513601616 16000000 16 2857027203232 2097152000000 20750155 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns276p1408 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p1410 := BSN.arctan_dyadic_bound_f 1000 1195204 1 0 8388608 3610000 0 1 1 0 1 1 7018 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1195204) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1195204) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns276p1411 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1195204))) 884279719003555 562949953421312 1 2000000000000000 7018 8388608 1 3610000 7413925142297862733824 883808748996003 562949953421312 200000000361 722000000000000000 qz17 (Ns276p1410 rfl) rfl rfl 

noncomputable abbrev qz527 := (@HMul.hMul Real Real Real qz584 qz589 qz709)

noncomputable abbrev qz230 := qz527

noncomputable abbrev qz528 := qz709

noncomputable abbrev qz231 := qz528

noncomputable def Ns276p1412 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 597602 4000) qz526) qz230 958759733539142140999 562949953421312000 233438389117161 45125000000000000000 883808748996003 2251799813685248 200000000361 2888000000000000000 Ns276p1403 958538781351893140249 562949953421312000 1892507112982413 361000000000000000000 (Ns276p1409 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz231 1 4 0 1 883808748996003 562949953421312 200000000361 722000000000000000 883808748996003 2251799813685248 200000000361 2888000000000000000 qz361 Ns276p1411 rfl) 

noncomputable def Ns276p1413 := @Ns276p1398 Ns276p1392 Ns276p1393 5229771796633444037 369664000000000000000000 (@Ns276p1400 5229771796633444037 369664000000000000000000 (Ns276p1402 (Ns276p1412 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 597602 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz710 (Real.log Real.pi) 597602 2000 0 1 38410761 33554432 1 33554432 11477173797561 33554432000 298801 33554432000 (Enclosure.Real.IsNear.const Bool.false 597602 2000) RS277to288.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns276p1394 Ns276p1395) 

noncomputable def Ns276p1414 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns276p1392 Ns276p1393 5229771796633444037 369664000000000000000000 17815041287 16777216 119 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz362 qz227 (Enclosure.sfrac Bool.true Ns276p1394 Ns276p1395)) Bool.false Ns276p1392 Ns276p1393 5229771796633444037 369664000000000000000000 Ns276p1396 (Ns276p1413 rfl rfl)) 

noncomputable def Ns276p1415 := BSN.cos_dyadic_bound_f 30602748 34359738368 1 0 16777216 7227051 0 1 1 0 1 1 16777209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 30602748) qz378 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 30602748) qz379 0 0 rfl) rfl rfl 

noncomputable def Ns276p1416 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz223) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17815041287) qz376) Bool.false 17815041287 16777216 119 8388608 Bool.false 16777209 16777216 1 3610000 (Ns276p1414 rfl) (Enclosure.sfrac_false_div 17815041287 16777216) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17815041287) qz376) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2153476977667010985984) qz380) 226375608064910080 72057594037927936 Bool.false 16777209 16777216 169 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q0 17815041287 16777216 226375608064910080 72057594037927936 169 2153476977667010985984 Ns276p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777209 16777216 2153476977667010985984 Ns276p92 30602748 34359738368 7227051 7220000 (Ns276p1415 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p1417 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns276p1392 Ns276p1393 5229771796633444037 369664000000000000000000 142520330296 134217728 1900 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz362 qz227 (Enclosure.sfrac Bool.true Ns276p1394 Ns276p1395)) Bool.false Ns276p1392 Ns276p1393 5229771796633444037 369664000000000000000000 Ns276p1396 (Ns276p1413 rfl rfl)) 

noncomputable def Ns276p1418 := Ns276p1391 33580 BSN.abs_quadSignPos (BSN.cos_quad_nat0 412 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 119963712 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 258 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133968798 134217728) qz226 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) Bool.false 16777209 16777216 27373663 1892679680000 134217672 134217728 1942 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 16777209 16777216 27373663 1892679680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz223) qz223) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 16777209 16777216 437978608 30282874880000 16777209 16777216 27373663 1892679680000 (Ns276p1416 rfl rfl) rfl)) rfl) (Ns276p1417 rfl) RS277to288.d7 

noncomputable def Ns276p1419 := nat_lit 8275565035836626976181055770899955441121610990594867072217167690625 

noncomputable def Ns276p1420 := nat_lit 230395240399900072365627716196050091089311478973787890562890625 

noncomputable def Ns276p1421 := nat_lit 24826234317029081128398436057267474223182654348826653640870377290625 

noncomputable def Ns276p1422 := BSN.cos_dyadic_bound_f 62417905 134217728 3 2 134217728 67108864 Ns276p1419 Ns276p131 Ns276p1420 Ns276p1421 Ns276p134 Ns276p1420 119963712 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 62417905) qz369 0 2 Ns276p1419 Ns276p131 Ns276p1420 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 62417905) qz370 0 2 Ns276p1421 Ns276p134 Ns276p1420 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1423 := nat_lit 4467860201467667072118237201 

noncomputable def Ns276p1424 := BSN.cos_dyadic_bound_f 8175699 134217728 2 1 134217728 67108864 Ns276p1423 Ns276p122 Ns276p1423 Ns276p1423 Ns276p123 Ns276p1423 133968798 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 8175699) qz369 0 1 Ns276p1423 Ns276p122 Ns276p1423 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 8175699) qz370 0 1 Ns276p1423 Ns276p123 Ns276p1423 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1425 := nat_lit 131916973142926143592065569961460218968376747580218504757628418043681 

noncomputable def Ns276p1426 := nat_lit 58494965790985540536366014241380210422450024962147695439081549601 

noncomputable def Ns276p1427 := nat_lit 395633929497196459695123977855897896484285342690731218882007091031841 

noncomputable def Ns276p1428 := BSN.cos_dyadic_bound_f 124706707 134217728 3 2 134217728 67108864 Ns276p1425 Ns276p131 Ns276p1426 Ns276p1427 Ns276p134 Ns276p1426 80332700 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 124706707) qz369 0 2 Ns276p1425 Ns276p131 Ns276p1426 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 124706707) qz370 0 2 Ns276p1427 Ns276p134 Ns276p1426 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1429 := nat_lit 459363435249682645165148593856339266739024897139202408408805043093760 

noncomputable def Ns276p1430 := nat_lit 218905257563919862583767492652693743183341288074728654793838182656 

noncomputable def Ns276p1431 := nat_lit 1202740293332160581369301169873736575398958844707694842296251755806976 

noncomputable def Ns276p1432 := BSN.sin_dyadic_bound_f 147072686 134217728 3 2 134217728 67108864 Ns276p1429 Ns276p137 Ns276p1430 Ns276p1431 Ns276p140 Ns276p1430 119357656 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 147072686) qz367 0 2 Ns276p1429 Ns276p137 Ns276p1430 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 147072686) qz368 0 2 Ns276p1431 Ns276p140 Ns276p1430 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1433 := Ns276p1389 56910 BSN.abs_quadSignPos (BSN.cos_quad_nat0 148 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 80332700 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 119357656 134217728) qz226 rfl rfl (Ns276p1418 RS277to288.d9 RS277to288.d11 RS277to288.d13 RS277to288.d17 (Ns276p1422 rfl rfl) (Ns276p1424 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns276p1417 rfl) RS277to288.d19 RS277to288.d21 RS277to288.d23 RS277to288.d25 RS277to288.d17 (Ns276p1428 rfl rfl) (Ns276p1432 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns276p1434 := nat_lit 381075681123401452056383158662007772888055031662208950784500179042560 

noncomputable def Ns276p1435 := nat_lit 150673311454933202865411121847204899287187078741265956393979904256 

noncomputable def Ns276p1436 := nat_lit 997811408057029149247792845155601073441298208606870916696672120504576 

noncomputable def Ns276p1437 := BSN.sin_dyadic_bound_f 140363614 134217728 3 2 134217728 67108864 Ns276p1434 Ns276p137 Ns276p1435 Ns276p1436 Ns276p140 Ns276p1435 116141415 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 140363614) qz367 0 2 Ns276p1434 Ns276p137 Ns276p1435 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 140363614) qz368 0 2 Ns276p1436 Ns276p140 Ns276p1435 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1438 := nat_lit 10165470809625655414187399246532676243423782919620380261084718759936 

noncomputable def Ns276p1439 := nat_lit 347638337124805012381113025116761870914897377427234125900742656 

noncomputable def Ns276p1440 := nat_lit 30495717152202716632537435513547795206529518964106286315002354794496 

noncomputable def Ns276p1441 := BSN.cos_dyadic_bound_f 65711436 134217728 3 2 134217728 67108864 Ns276p1438 Ns276p131 Ns276p1439 Ns276p1440 Ns276p134 Ns276p1439 118450704 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 65711436) qz369 0 2 Ns276p1438 Ns276p131 Ns276p1439 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 65711436) qz370 0 2 Ns276p1440 Ns276p134 Ns276p1439 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1442 := Ns276p1387 76278 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 5 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 116141415 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 118450704 134217728) qz226 rfl rfl (Ns276p1433 rfl rfl) (Ns276p1417 rfl) RS277to288.d27 RS277to288.d29 RS277to288.d31 RS277to288.d33 RS277to288.d17 (Ns276p1437 rfl rfl) (Ns276p1441 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p1443 := nat_lit 323134237110591413144373170176 

noncomputable def Ns276p1444 := BSN.sin_dyadic_bound_f 23842168 134217728 2 1 134217728 67108864 Ns276p1443 Ns276p126 Ns276p1443 Ns276p1443 Ns276p127 Ns276p1443 23716974 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 23842168) qz367 0 1 Ns276p1443 Ns276p126 Ns276p1443 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 23842168) qz368 0 1 Ns276p1443 Ns276p127 Ns276p1443 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1445 := nat_lit 7849389087618792273292128627701805753727107855531150389471157802517387287086935171672096751756142182400000 

noncomputable def Ns276p1446 := nat_lit 2950325227389725577737865821253974510425221330926749099826671680352912723676192948555776000000000000 

noncomputable def Ns276p1447 := nat_lit 39211526595104518284828002993298239689969250342686326461002908460672492228072108781043598866952486912000000 

noncomputable def Ns276p1448 := BSN.sin_dyadic_bound_f 194605820 134217728 4 3 134217728 67108864 Ns276p1445 Ns276p255 Ns276p1446 Ns276p1447 Ns276p258 Ns276p1446 133238490 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 194605820) qz367 0 3 Ns276p1445 Ns276p255 Ns276p1446 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 194605820) qz368 0 3 Ns276p1447 Ns276p258 Ns276p1446 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1449 := Ns276p1385 93201 BSN.abs_quadSignPos (BSN.cos_quad_nat3 115 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 23716974 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 159 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133238490 134217728) qz226 rfl rfl (Ns276p1442 rfl) (Ns276p1417 rfl) RS277to288.d35 RS277to288.d37 RS277to288.d39 RS277to288.d41 RS277to288.d17 (Ns276p1444 rfl rfl) (Ns276p1448 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p1450 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) 285396282 134217728 93201 134217728 285396282 134217728 93201 134217728 76610481099374592 142698141 33554432 93201 67108864 (Ns276p1449 rfl) 

noncomputable def Ns276p1451 := @Enclosure.Real.IsNear.mulLit_tf qz707 (Zeta.RiemannSiegel.correction qz225) 167885 524288 1 8388608 4420168050017 8796093022208 9234836313661391 3969236976271360000 742079913077104045 4611686018427387904 

noncomputable abbrev qz711 := (@HPow.hPow Real Real Real qz7 qz224 qz9)

noncomputable def Ns276p1452 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz711 1 1 0 1 167885 524288 1 8388608 167885 524288 1 8388608 

noncomputable def Ns276p1453 := @Enclosure.Real.IsNear.sqrt_image qz224 797851557777 8388608000 298801 8388608000 81809910 81809942 8388608 (@Enclosure.Real.IsNear.of_eq qz224 (@HMul.hMul Real Real Real qz5 qz223 qz3) Bool.false 797851557777 8388608000 298801 8388608000 (BSN.t_div_two_pi_mk qz223 597602 1000 qz226) (@Enclosure.Real.IsNear.mulLit_ff qz223 qz3 597602 1000 0 1 2670177 16777216 1 16777216 797851557777 8388608000 298801 8388608000 (Enclosure.Real.IsNear.const Bool.false 597602 1000) RS277to288.d44 rfl)) 

noncomputable abbrev qz786 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 597602 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz712 := qz786

noncomputable abbrev qz529 := qz712

noncomputable abbrev qz232 := qz529

noncomputable def Ns276p1454 := @Enclosure.Real.IsNear.sqrt_image qz232 40904963 4194304 1 524288 26196779 26196785 8388608 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 163619852 16777216 32 16777216 40904963 4194304 1 524288 (Ns276p1453 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns276p1455 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz232) 13098391 4194304 3 8388608 2686159 2686161 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz232) Bool.false 52393564 16777216 6 16777216 13098391 4194304 3 8388608 (Ns276p1454 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns276p1456 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 5372320 16777216 2 16777216 167885 524288 1 8388608 (Ns276p1455 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz233 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz523))

noncomputable abbrev qz713 := (@HMul.hMul Real Real Real qz732 qz784 qz784)

noncomputable abbrev qz530 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz713 qz706) qz599)

noncomputable abbrev qz234 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz530))

noncomputable def Ns276p1457 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz225) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz233) qz234) Bool.false 4420168050017 

noncomputable def Ns276p1458 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz233) qz234 533385791 8388608 417737 

noncomputable def Ns276p1459 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz233) Bool.false 1066771582 16777216 835474 16777216 533385791 8388608 417737 

noncomputable def Ns276p1460 := @Enclosure.Real.IsNear.recentre' qz233 Bool.false 263857 16777216 372998608 30282874880000 263857 16777216 23312413 1892679680000 

noncomputable abbrev qz235 := (@HMul.hMul Real Real Real qz346 qz343 qz523)

noncomputable def Ns276p1461 := @Enclosure.Real.IsNear.cos_image qz235 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 19831159) (@Nat.cast Real Real.instNatCast 4194304)) Bool.false 19831159 4194304 101 8388608 Bool.false 263857 16777216 1 

noncomputable def Ns276p1462 := nat_lit 5397215082486603678221403 

noncomputable def Ns276p1463 := nat_lit 450359962737049600000000000000 

noncomputable def Ns276p1464 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz225 884279719003555 140737488355328 1 500000000000000 3156227 4194304 1 524288 2790987524671433386985 590295810358705651712 Ns276p1462 

noncomputable def Ns276p1465 := @Enclosure.Real.IsNear.subLit_ff_p qz232 qz1 40904963 4194304 1 524288 9 1 0 1 3156227 3156227 4194304 1 

noncomputable def Ns276p1466 := @Ns276p1465 524288 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 163619852 16777216 32 16777216 40904963 4194304 1 524288 (Ns276p1453 rfl rfl rfl rfl rfl rfl) rfl) qz377 

noncomputable def Ns276p1467 := @Enclosure.Real.IsNear.recentre' qz235 Bool.false 2790987524671433386985 590295810358705651712 Ns276p1462 Ns276p1463 19831159 4194304 101 8388608 (@Ns276p1464 Ns276p1463 RS277to288.d43 (Ns276p1466 rfl rfl) rfl) 

noncomputable def Ns276p1468 := BSN.sin_dyadic_bound_f 540402073 34359738368 1 0 16777216 7227051 0 1 1 0 1 1 263857 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 540402073) qz363 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 540402073) qz364 0 0 rfl) rfl rfl 

noncomputable def Ns276p1469 := @Ns276p1461 3610000 (Ns276p1467 rfl) (Enclosure.sfrac_false_div 19831159 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 19831159) (@Nat.cast Real Real.instNatCast 4194304)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9506853819948034162688) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 263857 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q3 19831159 4194304 226375608064910080 72057594037927936 0 9506853819948034162688 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 263857 16777216 9506853819948034162688 604462909807314587353088 540402073 34359738368 7227051 7220000 (Ns276p1468 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p1470 := @Enclosure.Real.IsNear.inv_image qz233 263857 16777216 23312413 1892679680000 532968054 533803528 8388608 (Ns276p1460 (Ns276p1469 rfl rfl) rfl) rfl 

noncomputable def Ns276p1471 := @Enclosure.Real.IsNear.recentre' qz234 Bool.false 66296 8388608 

noncomputable abbrev qz236 := (@HMul.hMul Real Real Real qz346 qz343 qz530)

noncomputable def Ns276p1472 := @Enclosure.Real.IsNear.cos_image qz236 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 13110497)) qz365) Bool.true 13110497 8388608 

noncomputable def Ns276p1473 := nat_lit 3869535789899250194841971525 

noncomputable def Ns276p1474 := nat_lit 2475880078570760549798248448 

noncomputable def Ns276p1475 := nat_lit 141768189792939337884980499543921 

noncomputable def Ns276p1476 := @Enclosure.Real.IsNear.recentre' qz236 Bool.true Ns276p1473 Ns276p1474 Ns276p1475 

noncomputable def Ns276p1477 := nat_lit 4722366482869645213696000000000000000 

noncomputable abbrev qz237 := qz530

noncomputable def Ns276p1478 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz237 884279719003555 140737488355328 1 500000000000000 4375918283255 

noncomputable abbrev qz531 := (@HSub.hSub Real Real Real qz588 qz713 qz706)

noncomputable abbrev qz238 := qz531

noncomputable def Ns276p1479 := @Enclosure.Real.IsNear.subLit_tf qz238 qz31 3276406655479 17592186044416 5253383 1099511627776 1 16 

noncomputable abbrev qz532 := qz713

noncomputable abbrev qz239 := qz532

noncomputable def Ns276p1480 := @Enclosure.Real.IsNear.subLit_ff_n qz239 qz225 9961768875529 17592186044416 3156231 1099511627776 3156227 4194304 1 524288 

noncomputable def Ns276p1481 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz225 3156227 4194304 1 524288 3156227 4194304 1 524288 9961768875529 17592186044416 

noncomputable def Ns276p1482 := nat_lit 14509818110159218505752389067000190511083263899927621127690090517203423201122852616954389121 

noncomputable def Ns276p1483 := nat_lit 25788724684341947238819949751250650284471448108804693057291981262214091561818620109441 

noncomputable def Ns276p1484 := nat_lit 87818422321050688368082060940724804048860869446260893139675543607669049603766586234448585345 

noncomputable def Ns276p1485 := BSN.cos_dyadic_bound_f 13110497 8388608 4 3 8388608 3610000 Ns276p1482 Ns276p918 Ns276p1483 Ns276p1484 Ns276p921 Ns276p1483 66296 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 13110497) (BSN.cosEvenQ 8388608) 0 3 Ns276p1482 Ns276p918 Ns276p1483 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 13110497) (BSN.cosOddQ 8388608) 0 3 Ns276p1484 Ns276p921 Ns276p1483 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1486 := @Ns276p1471 1839827216 60565749760000 8287 1048576 114989201 3785359360000 (@Ns276p1472 505 16777216 Bool.false 66296 8388608 1 3610000 (@Ns276p1476 Ns276p1477 13110497 8388608 505 16777216 (@Ns276p1478 17592186044416 5253383 1099511627776 Ns276p1473 Ns276p1474 Ns276p1475 Ns276p1477 RS277to288.d43 (@Ns276p1479 0 1 70014692532080 4375918283255 17592186044416 5253383 1099511627776 (@Ns276p1480 13742245540702191616 3276406655479 17592186044416 5253383 1099511627776 (@Ns276p1481 3156231 1099511627776 (Ns276p1466 rfl rfl) (Ns276p1466 rfl rfl) rfl) (Ns276p1466 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 13110497 8388608) (BSN.cos_neg_of_bound 13110497 8388608 Bool.false 66296 8388608 1 3610000 (Ns276p1485 rfl rfl)) rfl rfl) 

noncomputable def Ns276p1487 := @Ns276p1451 24808251747973565881201 Ns276p1381 (Ns276p1452 qz33 (@Enclosure.Real.IsNear.of_eq qz711 (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 167885 524288 1 8388608 (BSN.rpow_neg_quarter_mk qz224 (BSN.t_div_two_pi_nonneg qz223 597602 1000 qz226)) Ns276p1456) rfl) (@Ns276p1457 8796093022208 9234836313661391 3969236976271360000 (BSN.correction_mk qz225 (BSN.cos_two_pi_p_ne_zero_mk qz223 597602 1000 9 qz226 rfl rfl (@BSN.floor_sqrt_eq_dec qz223 597602 1000 9 qz226 rfl rfl rfl))) (@Ns276p1458 8388608 8287 1048576 114989201 3785359360000 4420168050017 8796093022208 9234836313661391 3969236976271360000 (@Ns276p1459 8388608 (Ns276p1470 rfl rfl rfl rfl rfl) rfl) (Ns276p1486 rfl) rfl)) 

noncomputable def Ns276p1488 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (hardyZApproximantRS₀ qz223) Bool.false 20354363074516999597 4611686018427387904 71050358676156943801201 Ns276p1381 (@Eq.refl Real (hardyZApproximantRS₀ qz223)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (@HMul.hMul Real Real Real qz5 qz707 (Zeta.RiemannSiegel.correction qz225))) Bool.false 20354363074516999597 4611686018427387904 71050358676156943801201 Ns276p1381 (BSN.hardyZApproximantRS₀_eq qz223 9 (@BSN.floor_sqrt_eq_dec qz223 597602 1000 9 qz226 rfl rfl rfl)) (@Ns276p1383 20354363074516999597 4611686018427387904 71050358676156943801201 Ns276p1381 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 9)) Bool.false 142698141 33554432 93201 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (Ns276p1450 (Ns276p1449 rfl) rfl rfl)) (Ns276p1487 rfl) rfl rfl)) 

theorem RS277to288.d58 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz223) Bool.false 20354363074516999597 4611686018427387904 71050358676156943801201 Ns276p1381 := Ns276p1488 

noncomputable def Ns276p1489 := nat_lit 106548393769746370134016000 

noncomputable def Ns276p1490 := nat_lit 65736633048595521577460695040 

noncomputable abbrev qz787 := (Enclosure.sfrac Bool.false 598981 1000)

noncomputable abbrev qz714 := qz787

noncomputable abbrev qz533 := qz714

noncomputable abbrev qz240 := qz533

noncomputable abbrev qz788 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 598981 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz715 := qz788

noncomputable abbrev qz534 := qz715

noncomputable abbrev qz241 := qz534

noncomputable abbrev qz789 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 598981 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz716 := qz789

noncomputable abbrev qz535 := qz716

noncomputable abbrev qz242 := qz535

noncomputable abbrev qz717 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz241 qz9))

noncomputable def Ns276p1491 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (@HMul.hMul Real Real Real qz5 qz717 (Zeta.RiemannSiegel.correction qz242)) 30601505 16777216 93419 67108864 388570292001271820075 2361183241434822606848 14608040820134555291033 Ns276p1489 Ns276p1490 

noncomputable def Ns276p1492 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 598981 1000 114 159 134217728 67108864 2251799813685248 Bool.false 142941975371 1904 

noncomputable def Ns276p1493 := Ns276p1492 279097919 38 47453128 8 294906479 38 44739240 8 Bool.true 161379252 76457 Bool.true 197901838 Bool.true 179636779 7074237752028440 1 Bool.false 12906900 Bool.true Bool.false 130609539 Bool.false Bool.true 122406020 

noncomputable def Ns276p1494 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 598981 1000 5 64 134217728 67108864 2251799813685248 Bool.false 142941975371 1904 

noncomputable def Ns276p1495 := Ns276p1494 240485871 38 54794152 8 261175631 38 50729528 8 Bool.true 192007602 57045 Bool.true 50348555 Bool.true 4227556 7074237752028440 1 Bool.false 49175998 Bool.true Bool.false 134151154 Bool.false Bool.true 161379252 

noncomputable def Ns276p1496 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 598981 1000 149 64 134217728 67108864 2251799813685248 Bool.false 142941975371 1904 

noncomputable def Ns276p1497 := Ns276p1496 186065264 38 67108856 8 216015088 38 60023992 8 Bool.true 208899316 33661 Bool.false 78939069 Bool.false 60004241 7074237752028440 1 Bool.false 74466154 Bool.true Bool.false 121026705 Bool.false Bool.true 192007602 

noncomputable def Ns276p1498 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 598981 1000 413 259 134217728 67108864 2251799813685248 Bool.false 142941975371 1904 

noncomputable def Ns276p1499 := Ns276p1498 93032624 38 94906264 8 147453232 38 77490640 16 Bool.true 134217680 1950 Bool.false 144942277 Bool.false 15654053 7074237752028440 1 Bool.false 118368306 Bool.true Bool.false 15618586 Bool.false Bool.true 208899316 

noncomputable def Ns276p1500 := nat_lit 498392360121514751131582051868556467052665414039011527607 

noncomputable def Ns276p1501 := nat_lit 467973735875208525792264034257081008134654783389696000 

noncomputable def Ns276p1502 := nat_lit 37008990315856602839347945072480000 

noncomputable def Ns276p1503 := nat_lit 133006135421058083293321497608610857280 

noncomputable abbrev qz790 := (@Eq.refl Real (Enclosure.sfrac Bool.false 598981 1000))

noncomputable abbrev qz718 := qz790

noncomputable abbrev qz536 := qz718

noncomputable abbrev qz243 := qz536

noncomputable def Ns276p1504 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz240 598981 1000 1435113953444 16000000 1197962 4000 2000 Ns276p1502 Ns276p1503 qz243 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns276p1505 := nat_lit 159485555238884720362106256597938069456852932492483688834240 

noncomputable abbrev qz719 := (@HSub.hSub Real Real Real qz736 qz737 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz738 (@Nat.cast Real Real.instNatCast 1197962))))

noncomputable abbrev qz537 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 598981 4000) (Real.log (Enclosure.sfrac Bool.false 1435113953444 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz719))

noncomputable abbrev qz720 := (Enclosure.sfrac Bool.false 598981 2000)

noncomputable abbrev qz244 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz537 qz720) (@HMul.hMul Real Real Real qz346 qz720 (Real.log Real.pi)))

noncomputable def Ns276p1506 := @Enclosure.Real.IsNear.addLit_ft_p qz244 (Enclosure.sfrac Bool.true Ns276p1502 Ns276p1503) 1199084511420614118583 1125899906842624000 10483561427569630697 739328000000000000000000 Ns276p1502 Ns276p1503 0 1 Ns276p1505 

noncomputable def Ns276p1507 := nat_lit 80469199401432439680466419712000 

noncomputable abbrev qz245 := (@HSub.hSub Real Real Real qz350 qz537 qz720)

noncomputable def Ns276p1508 := @Enclosure.Real.IsNear.subLit_ff_p qz245 (@HMul.hMul Real Real Real qz5 qz720 (Real.log Real.pi)) 1585083222112371936439 1125899906842624000 1896816489973689 361000000000000000000 23007316034541 67108864000 598981 67108864000 Ns276p1507 1199084511420614118583 1125899906842624000 

noncomputable def Ns276p1509 := nat_lit 3170166444224743872878000 

noncomputable abbrev qz246 := qz537

noncomputable def Ns276p1510 := @Enclosure.Real.IsNear.subLit_ff_p qz246 qz720 1922279548162622819511 1125899906842624000 1896816489973689 361000000000000000000 598981 2000 0 1 Ns276p1509 1585083222112371936439 1125899906842624000 1896816489973689 361000000000000000000 

noncomputable def Ns276p1511 := nat_lit 4328588728403556774383743513267273728 

noncomputable def Ns276p1512 := nat_lit 27573581667099267460759552 

noncomputable def Ns276p1513 := nat_lit 1368393029418793946487327141761867729647174769407827968482629495816049187945092745476161489229482885120 

noncomputable def Ns276p1514 := nat_lit 11211267992876665279757176782011128699916771064172135077821707170680762595720574198133186261854715904 

noncomputable def Ns276p1515 := nat_lit 52327072994498809016253240868854460315812322370834999059787856556200393329939588043435311431680 

noncomputable def Ns276p1516 := BSN.log_dyadic_bound 386537953444 2483689953444 5 4 Ns276p1513 67108864 28880000 Ns276p1514 Ns276p1515 21059513 2870227906888 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 386537953444) (BSN.artanhQ 2483689953444) 0 4 Ns276p1514 Ns276p1513 Ns276p1515 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz538 := (Real.log (Enclosure.sfrac Bool.false 1435113953444 16000000))

noncomputable def Ns276p1517 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 598981 4000) qz538 598981 4000 0 1 3209987383696631 281474976710656 781250361 22562500000000000 1922721453073991733011 1125899906842624000 467954122482141 90250000000000000000 (Enclosure.Real.IsNear.const Bool.false 598981 4000) (BSN.isNear_log_sfrac 1435113953444 16000000 3209987383696631 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1435113953444) qz353)) Bool.false Ns276p1512 Ns276p92 1000000462080000 28880000000000000000000 3209987383696631 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1435113953444 16000000 16 2870227906888 2097152000000 21059513 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns276p1516 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns276p1518 := BSN.arctan_dyadic_bound_f 1000 1197962 1 0 8388608 3610000 0 1 1 0 1 1 7002 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1197962) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1197962) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns276p1519 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1197962))) 884279719003555 562949953421312 1 2000000000000000 7002 8388608 1 3610000 7413934149497117474816 883809822737827 562949953421312 200000000361 722000000000000000 qz17 (Ns276p1518 rfl) rfl rfl 

noncomputable abbrev qz539 := (@HMul.hMul Real Real Real qz584 qz589 qz719)

noncomputable abbrev qz247 := qz539

noncomputable abbrev qz540 := qz719

noncomputable abbrev qz248 := qz540

noncomputable def Ns276p1520 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 598981 4000) qz538) qz247 1922721453073991733011 1125899906842624000 467954122482141 90250000000000000000 883809822737827 2251799813685248 200000000361 2888000000000000000 Ns276p1511 1922279548162622819511 1125899906842624000 1896816489973689 361000000000000000000 (Ns276p1517 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz248 1 4 0 1 883809822737827 562949953421312 200000000361 722000000000000000 883809822737827 2251799813685248 200000000361 2888000000000000000 qz361 Ns276p1519 rfl) 

noncomputable def Ns276p1521 := @Ns276p1506 Ns276p1500 Ns276p1501 10483561427569630697 739328000000000000000000 (@Ns276p1508 10483561427569630697 739328000000000000000000 (Ns276p1510 (Ns276p1520 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 598981 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz720 (Real.log Real.pi) 598981 2000 0 1 38410761 33554432 1 33554432 23007316034541 67108864000 598981 67108864000 (Enclosure.Real.IsNear.const Bool.false 598981 2000) RS277to288.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns276p1502 Ns276p1503) 

noncomputable def Ns276p1522 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns276p1500 Ns276p1501 10483561427569630697 739328000000000000000000 17867746921 16777216 239 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz362 qz244 (Enclosure.sfrac Bool.true Ns276p1502 Ns276p1503)) Bool.false Ns276p1500 Ns276p1501 10483561427569630697 739328000000000000000000 Ns276p1504 (Ns276p1521 rfl rfl)) 

noncomputable def Ns276p1523 := BSN.cos_dyadic_bound_f 27439544 34359738368 1 0 16777216 7227051 0 1 1 0 1 1 16777210 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 27439544) qz378 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 27439544) qz379 0 0 rfl) rfl rfl 

noncomputable def Ns276p1524 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz240) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17867746921) qz376) Bool.false 17867746921 16777216 239 16777216 Bool.true 16777210 16777216 1 3610000 (Ns276p1522 rfl) (Enclosure.sfrac_false_div 17867746921 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17867746921) qz376) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1930886272213971894272) qz380) 226375608064910080 72057594037927936 Bool.false 16777210 16777216 169 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 17867746921 16777216 226375608064910080 72057594037927936 169 1930886272213971894272 Ns276p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777210 16777216 1930886272213971894272 Ns276p92 27439544 34359738368 7227051 7220000 (Ns276p1523 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p1525 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns276p1500 Ns276p1501 10483561427569630697 739328000000000000000000 142941975371 134217728 1904 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz362 qz244 (Enclosure.sfrac Bool.true Ns276p1502 Ns276p1503)) Bool.false Ns276p1500 Ns276p1501 10483561427569630697 739328000000000000000000 Ns276p1504 (Ns276p1521 rfl rfl)) 

noncomputable def Ns276p1526 := Ns276p1499 33661 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 413 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 118368306 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 259 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 15618586 134217728) qz243 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) Bool.true 8388605 8388608 54972951 3785359360000 134217680 134217728 1950 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 8388605 8388608 54972951 3785359360000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz240) qz240) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 16777210 16777216 879567216 60565749760000 8388605 8388608 54972951 3785359360000 (Ns276p1524 rfl rfl) rfl)) rfl) (Ns276p1525 rfl) RS277to288.d7 

noncomputable def Ns276p1527 := nat_lit 433308204005698841330200620919968476702182242682731675114363294933985 

noncomputable def Ns276p1528 := nat_lit 194787299830822948832204959947538531849456791380146219696968000481 

noncomputable def Ns276p1529 := nat_lit 1134539450100913728233368532474288090882721038887777007610489729016801 

noncomputable def Ns276p1530 := BSN.sin_dyadic_bound_f 144942277 134217728 3 2 134217728 67108864 Ns276p1527 Ns276p137 Ns276p1528 Ns276p1529 Ns276p140 Ns276p1528 118368306 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 144942277) qz367 0 2 Ns276p1527 Ns276p137 Ns276p1528 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 144942277) qz368 0 2 Ns276p1529 Ns276p140 Ns276p1528 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1531 := nat_lit 60049196348059307495554122481 

noncomputable def Ns276p1532 := BSN.sin_dyadic_bound_f 15654053 134217728 2 1 134217728 67108864 Ns276p1531 Ns276p126 Ns276p1531 Ns276p1531 Ns276p127 Ns276p1531 15618586 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 15654053) qz367 0 1 Ns276p1531 Ns276p126 Ns276p1531 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 15654053) qz368 0 1 Ns276p1531 Ns276p127 Ns276p1531 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1533 := nat_lit 38107152915162367324246949057234686355707827327142921184753871196065 

noncomputable def Ns276p1534 := nat_lit 1507773133468476746511150011393963187549958128360646482586996641 

noncomputable def Ns276p1535 := nat_lit 99802006954637727363057181859405731181693038305547447770526426566561 

noncomputable def Ns276p1536 := BSN.sin_dyadic_bound_f 78939069 134217728 3 2 134217728 67108864 Ns276p1533 Ns276p137 Ns276p1534 Ns276p1535 Ns276p140 Ns276p1534 74466154 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 78939069) qz367 0 2 Ns276p1533 Ns276p137 Ns276p1534 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 78939069) qz368 0 2 Ns276p1535 Ns276p140 Ns276p1534 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1537 := nat_lit 7067843536081012885869410084767398860654794875538379504744519145601 

noncomputable def Ns276p1538 := nat_lit 168056600185842570798161823763645307139457319117084084650350721 

noncomputable def Ns276p1539 := nat_lit 21203194495042666972466633930654669291350105711976904346064256735361 

noncomputable def Ns276p1540 := BSN.cos_dyadic_bound_f 60004241 134217728 3 2 134217728 67108864 Ns276p1537 Ns276p131 Ns276p1538 Ns276p1539 Ns276p134 Ns276p1538 121026705 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 60004241) qz369 0 2 Ns276p1537 Ns276p131 Ns276p1538 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 60004241) qz370 0 2 Ns276p1539 Ns276p134 Ns276p1538 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1541 := Ns276p1497 57045 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 149 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 74466154 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 121026705 134217728) qz243 rfl rfl (Ns276p1526 RS277to288.d9 RS277to288.d11 RS277to288.d13 RS277to288.d17 (Ns276p1530 rfl rfl) (Ns276p1532 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns276p1525 rfl) RS277to288.d19 RS277to288.d21 RS277to288.d23 RS277to288.d25 RS277to288.d17 (Ns276p1536 rfl rfl) (Ns276p1540 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns276p1542 := nat_lit 6426108342810719789435273400625 

noncomputable def Ns276p1543 := BSN.sin_dyadic_bound_f 50348555 134217728 2 1 134217728 67108864 Ns276p1542 Ns276p126 Ns276p1542 Ns276p1542 Ns276p127 Ns276p1542 49175998 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 50348555) qz367 0 1 Ns276p1542 Ns276p126 Ns276p1542 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 50348555) qz368 0 1 Ns276p1542 Ns276p127 Ns276p1542 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1544 := nat_lit 319416595633990497776394496 

noncomputable def Ns276p1545 := BSN.cos_dyadic_bound_f 4227556 134217728 2 1 134217728 67108864 Ns276p1544 Ns276p122 Ns276p1544 Ns276p1544 Ns276p123 Ns276p1544 134151154 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 4227556) qz369 0 1 Ns276p1544 Ns276p122 Ns276p1544 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 4227556) qz370 0 1 Ns276p1544 Ns276p123 Ns276p1544 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1546 := Ns276p1495 76457 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 5 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 49175998 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 134151154 134217728) qz243 rfl rfl (Ns276p1541 rfl rfl) (Ns276p1525 rfl) RS277to288.d27 RS277to288.d29 RS277to288.d31 RS277to288.d33 RS277to288.d17 (Ns276p1543 rfl rfl) (Ns276p1545 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p1547 := nat_lit 3233141880893241731551204324763046384213940935880349951569295544068720184751375879872045702385061507239936 

noncomputable def Ns276p1548 := nat_lit 3609091830412808585393604322092495024405447678293584336936154057800712844875967279228690767427014656 

noncomputable def Ns276p1549 := nat_lit 19577688684197514972585301050223905940914032459132118072214643436743064807408436431496071244472262194237440 

noncomputable def Ns276p1550 := BSN.cos_dyadic_bound_f 197901838 134217728 4 3 134217728 67108864 Ns276p1547 Ns276p116 Ns276p1548 Ns276p1549 Ns276p119 Ns276p1548 12906900 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 197901838) qz369 0 3 Ns276p1547 Ns276p116 Ns276p1548 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 197901838) qz370 0 3 Ns276p1549 Ns276p119 Ns276p1548 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1551 := nat_lit 5696654050136311031453755351042402930284807926494188935963329928682258666186020243840659853932443307361041 

noncomputable def Ns276p1552 := nat_lit 1129127829272032346255117093925369605621122581260785134769441198138906213561188830630477480955233041 

noncomputable def Ns276p1553 := nat_lit 28464601717167958941395170629863244349336100071597067633311298952197840770862130016987296970159792803824401 

noncomputable def Ns276p1554 := BSN.sin_dyadic_bound_f 179636779 134217728 4 3 134217728 67108864 Ns276p1551 Ns276p255 Ns276p1552 Ns276p1553 Ns276p258 Ns276p1552 130609539 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 179636779) qz367 0 3 Ns276p1551 Ns276p255 Ns276p1552 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 179636779) qz368 0 3 Ns276p1553 Ns276p258 Ns276p1552 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1555 := Ns276p1493 93419 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 114 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 12906900 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 159 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 130609539 134217728) qz243 rfl rfl (Ns276p1546 rfl) (Ns276p1525 rfl) RS277to288.d35 RS277to288.d37 RS277to288.d39 RS277to288.d41 RS277to288.d17 (Ns276p1550 rfl rfl) (Ns276p1554 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns276p1556 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) 122406020 134217728 93419 134217728 122406020 134217728 93419 134217728 32858115795845120 30601505 16777216 93419 67108864 (Ns276p1555 rfl) 

noncomputable def Ns276p1557 := @Enclosure.Real.IsNear.mulLit_tf qz717 (Zeta.RiemannSiegel.correction qz242) 5369225 16777216 1 16777216 72369902919187 140737488355328 2720089474398233 6350779162034176000 388570292001271820075 2361183241434822606848 

noncomputable abbrev qz721 := (@HPow.hPow Real Real Real qz7 qz241 qz9)

noncomputable def Ns276p1558 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz721 1 1 0 1 5369225 16777216 1 16777216 5369225 16777216 1 16777216 

noncomputable def Ns276p1559 := @Enclosure.Real.IsNear.sqrt_image qz241 1599385289637 16777216000 598981 16777216000 81904246 81904278 8388608 (@Enclosure.Real.IsNear.of_eq qz241 (@HMul.hMul Real Real Real qz5 qz240 qz3) Bool.false 1599385289637 16777216000 598981 16777216000 (BSN.t_div_two_pi_mk qz240 598981 1000 qz243) (@Enclosure.Real.IsNear.mulLit_ff qz240 qz3 598981 1000 0 1 2670177 16777216 1 16777216 1599385289637 16777216000 598981 16777216000 (Enclosure.Real.IsNear.const Bool.false 598981 1000) RS277to288.d44 rfl)) 

noncomputable abbrev qz791 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 598981 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz722 := qz791

noncomputable abbrev qz541 := qz722

noncomputable abbrev qz249 := qz541

noncomputable def Ns276p1560 := @Enclosure.Real.IsNear.sqrt_image qz249 40952131 4194304 1 524288 26211879 26211885 8388608 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 163808524 16777216 32 16777216 40952131 4194304 1 524288 (Ns276p1559 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns276p1561 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz249) 13105941 4194304 3 8388608 2684612 2684613 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz249) Bool.false 52423764 16777216 6 16777216 13105941 4194304 3 8388608 (Ns276p1560 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns276p1562 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 5369225 16777216 1 16777216 5369225 16777216 1 16777216 (Ns276p1561 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz535))

noncomputable abbrev qz723 := (@HMul.hMul Real Real Real qz732 qz789 qz789)

noncomputable abbrev qz542 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz723 qz716) qz599)

noncomputable abbrev qz251 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz542))

noncomputable def Ns276p1563 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz242) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz250) qz251) Bool.false 72369902919187 

noncomputable def Ns276p1564 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz250) qz251 194452319 16777216 27761 

noncomputable def Ns276p1565 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz250) Bool.false 194452319 16777216 27761 16777216 194452319 16777216 27761 

noncomputable def Ns276p1566 := @Enclosure.Real.IsNear.recentre' qz250 Bool.false 1447527 16777216 372998608 30282874880000 1447527 16777216 23312413 1892679680000 

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz346 qz343 qz535)

noncomputable def Ns276p1567 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 80510097) qz376) Bool.false 80510097 16777216 101 8388608 Bool.false 1447527 16777216 1 

noncomputable def Ns276p1568 := nat_lit 26986075412483664645461447 

noncomputable def Ns276p1569 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz242 884279719003555 140737488355328 1 500000000000000 3203395 4194304 1 524288 2832697230457393069225 590295810358705651712 Ns276p1568 

noncomputable def Ns276p1570 := @Enclosure.Real.IsNear.subLit_ff_p qz249 qz1 40952131 4194304 1 524288 9 1 0 1 3203395 3203395 4194304 1 

noncomputable def Ns276p1571 := @Ns276p1570 524288 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 163808524 16777216 32 16777216 40952131 4194304 1 524288 (Ns276p1559 rfl rfl rfl rfl rfl rfl) rfl) qz377 

noncomputable def Ns276p1572 := @Enclosure.Real.IsNear.recentre' qz252 Bool.false 2832697230457393069225 590295810358705651712 Ns276p1568 Ns276p556 80510097 16777216 101 8388608 (@Ns276p1569 Ns276p556 RS277to288.d43 (Ns276p1571 rfl rfl) rfl) 

noncomputable def Ns276p1573 := nat_lit 77622562803464754695461421366583544801 

noncomputable def Ns276p1574 := nat_lit 167255588988979673561517887044862711294853120 

noncomputable def Ns276p1575 := nat_lit 1170789122922857714930625209314038979063971840 

noncomputable def Ns276p1576 := BSN.sin_dyadic_bound_f 2968226201 34359738368 2 1 16777216 7227051 Ns276p1573 Ns276p1574 Ns276p1573 Ns276p1573 Ns276p1575 Ns276p1573 1447527 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 2968226201) qz363 0 1 Ns276p1573 Ns276p1574 Ns276p1573 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 2968226201) qz364 0 1 Ns276p1573 Ns276p1575 Ns276p1573 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1577 := @Ns276p1567 3610000 (Ns276p1572 rfl) (Enclosure.sfrac_false_div 80510097 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 80510097) qz376) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 208870350251384314527744) qz380) 226375608064910080 72057594037927936 Bool.false 1447527 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q3 80510097 16777216 226375608064910080 72057594037927936 0 208870350251384314527744 Ns276p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1447527 16777216 208870350251384314527744 Ns276p92 2968226201 34359738368 7227051 7220000 (Ns276p1576 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns276p1578 := @Enclosure.Real.IsNear.inv_image qz250 1447527 16777216 23312413 1892679680000 97212279 97240040 8388608 (Ns276p1566 (Ns276p1577 rfl rfl) rfl) rfl 

noncomputable def Ns276p1579 := @Enclosure.Real.IsNear.recentre' qz251 Bool.false 372173 8388608 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz346 qz343 qz542)

noncomputable def Ns276p1580 := @Enclosure.Real.IsNear.cos_image qz253 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 25608997)) qz376) Bool.true 25608997 16777216 

noncomputable def Ns276p1581 := nat_lit 3779221013186207547613419205 

noncomputable def Ns276p1582 := nat_lit 143041068997778294797916794384689 

noncomputable def Ns276p1583 := @Enclosure.Real.IsNear.recentre' qz253 Bool.true Ns276p1581 Ns276p1474 Ns276p1582 

noncomputable abbrev qz254 := qz542

noncomputable def Ns276p1584 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz254 884279719003555 140737488355328 1 500000000000000 4273784563831 

noncomputable abbrev qz543 := (@HSub.hSub Real Real Real qz588 qz723 qz716)

noncomputable abbrev qz255 := qz543

noncomputable def Ns276p1585 := @Enclosure.Real.IsNear.subLit_tf qz255 qz31 3174272936055 17592186044416 5300551 1099511627776 1 16 

noncomputable abbrev qz544 := qz723

noncomputable abbrev qz256 := qz544

noncomputable def Ns276p1586 := @Enclosure.Real.IsNear.subLit_ff_n qz256 qz242 10261739526025 17592186044416 3203399 1099511627776 3203395 4194304 1 524288 

noncomputable def Ns276p1587 := @Enclosure.Real.IsNear.mulLit_ff qz242 qz242 3203395 4194304 1 524288 3203395 4194304 1 524288 10261739526025 17592186044416 

noncomputable def Ns276p1588 := nat_lit 54057616473243610592530430463909462879393186009442743080538373713095769296499361408022516986321 

noncomputable def Ns276p1589 := nat_lit 79562941528436316622448692940963959636806501402399266879531440422709943564908364464255441 

noncomputable def Ns276p1590 := nat_lit 327244937739901227599476514647770683946518593798528234076405718404588360419590411245595625124305 

noncomputable def Ns276p1591 := BSN.cos_dyadic_bound_f 25608997 16777216 4 3 8388608 3610000 Ns276p1588 Ns276p193 Ns276p1589 Ns276p1590 Ns276p196 Ns276p1589 372173 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 25608997) qz600 0 3 Ns276p1588 Ns276p193 Ns276p1589 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 25608997) (BSN.cosOddQ 16777216) 0 3 Ns276p1590 Ns276p196 Ns276p1589 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns276p1592 := @Ns276p1579 1854267216 60565749760000 372173 8388608 115891701 3785359360000 (@Ns276p1580 509 16777216 Bool.false 372173 8388608 1 3610000 (@Ns276p1583 Ns276p1477 25608997 16777216 509 16777216 (@Ns276p1584 17592186044416 5300551 1099511627776 Ns276p1581 Ns276p1474 Ns276p1582 Ns276p1477 RS277to288.d43 (@Ns276p1585 0 1 68380553021296 4273784563831 17592186044416 5300551 1099511627776 (@Ns276p1586 13313865672787230720 3174272936055 17592186044416 5300551 1099511627776 (@Ns276p1587 3203399 1099511627776 (Ns276p1571 rfl rfl) (Ns276p1571 rfl rfl) rfl) (Ns276p1571 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 25608997 16777216) (BSN.cos_neg_of_bound 25608997 16777216 Bool.false 372173 8388608 1 3610000 (Ns276p1591 rfl rfl)) rfl rfl) 

noncomputable def Ns276p1593 := @Ns276p1557 14608040820134555291033 Ns276p1489 (Ns276p1558 qz33 (@Enclosure.Real.IsNear.of_eq qz721 (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 5369225 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz241 (BSN.t_div_two_pi_nonneg qz240 598981 1000 qz243)) Ns276p1562) rfl) (@Ns276p1563 140737488355328 2720089474398233 6350779162034176000 (BSN.correction_mk qz242 (BSN.cos_two_pi_p_ne_zero_mk qz240 598981 1000 9 qz243 rfl rfl (@BSN.floor_sqrt_eq_dec qz240 598981 1000 9 qz243 rfl rfl rfl))) (@Ns276p1564 16777216 372173 8388608 115891701 3785359360000 72369902919187 140737488355328 2720089474398233 6350779162034176000 (@Ns276p1565 16777216 (Ns276p1578 rfl rfl rfl rfl rfl) rfl) (Ns276p1592 rfl) rfl)) 

noncomputable def Ns276p1594 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (hardyZApproximantRS₀ qz240) Bool.true 3918208661591739748565 2361183241434822606848 162928900454652227227033 Ns276p1489 (@Eq.refl Real (hardyZApproximantRS₀ qz240)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (@HMul.hMul Real Real Real qz5 qz717 (Zeta.RiemannSiegel.correction qz242))) Bool.true 3918208661591739748565 2361183241434822606848 162928900454652227227033 Ns276p1489 (BSN.hardyZApproximantRS₀_eq qz240 9 (@BSN.floor_sqrt_eq_dec qz240 598981 1000 9 qz243 rfl rfl rfl)) (@Ns276p1491 3918208661591739748565 2361183241434822606848 162928900454652227227033 Ns276p1489 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 9)) Bool.true 30601505 16777216 93419 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (Ns276p1556 (Ns276p1555 rfl) rfl rfl)) (Ns276p1593 rfl) rfl rfl)) 

theorem RS277to288.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz240) Bool.true 3918208661591739748565 2361183241434822606848 162928900454652227227033 Ns276p1489 := Ns276p1594 

noncomputable def RS277to288.d60 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz545 := (RS277to288.d3 qz583 qz601 (@Enclosure.dec_le_dec qz583 qz601 582385 1000 583772 1000 (@Eq.refl Real qz583) qz605 rfl rfl rfl))

noncomputable abbrev qz257 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz545)

noncomputable def Ns276p1595 := @Enclosure.Real.IsNear.of_eq qz257 (hardyZApproximantRS₀ qz4) Bool.true 491182005797401860019 295147905179352825856 91104705804614250806701 Ns276p69 

noncomputable abbrev qz546 := (@Enclosure.dec_le_dec qz583 qz601 582385 1000 583772 1000 (@Eq.refl Real qz583) qz605 rfl rfl rfl)

noncomputable abbrev qz258 := qz546

noncomputable def Ns276p1596 := @Enclosure.Real.IsNear.neg_val qz257 491182005797401860019 295147905179352825856 91104705804614250806701 Ns276p69 (Ns276p1595 (RS277to288.d4 qz4 qz35 qz258) RS277to288.d45) rfl 

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz545)

noncomputable def Ns276p1597 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantRS₀ qz35) Bool.false 881381320093347054997 590295810358705651712 2925066738967523065017 Ns276p201 

noncomputable def Ns276p1598 := @Enclosure.Real.IsNear.pos_val qz259 881381320093347054997 590295810358705651712 2925066738967523065017 Ns276p201 (Ns276p1597 (RS277to288.d46 qz4 qz35 qz258) RS277to288.d47) rfl 

noncomputable def Ns276p1599 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz257 qz4 qz4 582385 1000 582385 1000 

noncomputable def Ns276p1600 := @Enclosure.norm_gt_of_isNear qz257 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 491182005797401860019 295147905179352825856 91104705804614250806701 

noncomputable def Ns276p1601 := @Ns276p1600 Ns276p69 175153213 2684354560 1421 2684354560 (Ns276p1595 (RS277to288.d4 qz4 qz35 qz258) RS277to288.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable def Ns276p1602 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz259 qz4 qz35 582385 1000 583772 1000 

noncomputable def Ns276p1603 := @Enclosure.norm_gt_of_isNear qz259 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 881381320093347054997 590295810358705651712 2925066738967523065017 

noncomputable def Ns276p1604 := @Ns276p1603 Ns276p201 175153213 2684354560 1421 2684354560 (Ns276p1597 (RS277to288.d46 qz4 qz35 qz258) RS277to288.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable abbrev qz260 := qz545

noncomputable def Ns276p1605 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz260 (@BSN.thirtyTwoPi_le_dec qz4 582385 1000 qz11 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz257 qz259 (Ns276p1596 rfl rfl) (Ns276p1598 rfl rfl)) (Ns276p1599 qz11 qz11 rfl rfl rfl rfl (Ns276p1601 rfl)) (Ns276p1602 qz11 qz38 rfl rfl rfl rfl (Ns276p1604 rfl)) 

noncomputable abbrev qz547 := (RS277to288.d3 qz601 qz613 (@Enclosure.dec_le_dec qz601 qz613 583772 1000 585158 1000 qz605 qz617 rfl rfl rfl))

noncomputable abbrev qz261 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz547)

noncomputable def Ns276p1606 := @Enclosure.Real.IsNear.of_eq qz261 (hardyZApproximantRS₀ qz35) Bool.false 881381320093347054997 590295810358705651712 2925066738967523065017 Ns276p201 

noncomputable abbrev qz548 := (@Enclosure.dec_le_dec qz601 qz613 583772 1000 585158 1000 qz605 qz617 rfl rfl rfl)

noncomputable abbrev qz262 := qz548

noncomputable def Ns276p1607 := @Enclosure.Real.IsNear.pos_val qz261 881381320093347054997 590295810358705651712 2925066738967523065017 Ns276p201 (Ns276p1606 (RS277to288.d4 qz35 qz62 qz262) RS277to288.d47) rfl 

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz547)

noncomputable def Ns276p1608 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantRS₀ qz62) Bool.true 405809096949892316347 295147905179352825856 2935889361823138143629 Ns276p201 

noncomputable def Ns276p1609 := @Enclosure.Real.IsNear.neg_val qz263 405809096949892316347 295147905179352825856 2935889361823138143629 Ns276p201 (Ns276p1608 (RS277to288.d46 qz35 qz62 qz262) RS277to288.d49) rfl 

noncomputable def Ns276p1610 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz261 qz4 qz35 582385 1000 583772 1000 

noncomputable def Ns276p1611 := @Enclosure.norm_gt_of_isNear qz261 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 881381320093347054997 590295810358705651712 2925066738967523065017 

noncomputable def Ns276p1612 := @Ns276p1611 Ns276p201 175153213 2684354560 1421 2684354560 (Ns276p1606 (RS277to288.d4 qz35 qz62 qz262) RS277to288.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable def Ns276p1613 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz263 qz4 qz62 582385 1000 585158 1000 

noncomputable def Ns276p1614 := @Enclosure.norm_gt_of_isNear qz263 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 405809096949892316347 295147905179352825856 2935889361823138143629 

noncomputable def Ns276p1615 := @Ns276p1614 Ns276p201 175153213 2684354560 1421 2684354560 (Ns276p1608 (RS277to288.d46 qz35 qz62 qz262) RS277to288.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable abbrev qz264 := qz547

noncomputable def Ns276p1616 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz264 (@BSN.thirtyTwoPi_le_dec qz35 583772 1000 qz38 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz261 qz263 (Ns276p1607 rfl rfl) (Ns276p1609 rfl rfl)) (Ns276p1610 qz11 qz38 rfl rfl rfl rfl (Ns276p1612 rfl)) (Ns276p1613 qz11 qz65 rfl rfl rfl rfl (Ns276p1615 rfl)) 

noncomputable abbrev qz549 := (RS277to288.d3 qz613 qz623 (@Enclosure.dec_le_dec qz613 qz623 585158 1000 586544 1000 qz617 qz627 rfl rfl rfl))

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz549)

noncomputable def Ns276p1617 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantRS₀ qz62) Bool.true 405809096949892316347 295147905179352825856 2935889361823138143629 Ns276p201 

noncomputable abbrev qz550 := (@Enclosure.dec_le_dec qz613 qz623 585158 1000 586544 1000 qz617 qz627 rfl rfl rfl)

noncomputable abbrev qz266 := qz550

noncomputable def Ns276p1618 := @Enclosure.Real.IsNear.neg_val qz265 405809096949892316347 295147905179352825856 2935889361823138143629 Ns276p201 (Ns276p1617 (RS277to288.d4 qz62 qz80 qz266) RS277to288.d49) rfl 

noncomputable abbrev qz267 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz549)

noncomputable def Ns276p1619 := @Enclosure.Real.IsNear.of_eq qz267 (hardyZApproximantRS₀ qz80) Bool.false 56348081654729195797 147573952589676412928 184292738506395261377343 Ns276p473 

noncomputable def Ns276p1620 := @Enclosure.Real.IsNear.pos_val qz267 56348081654729195797 147573952589676412928 184292738506395261377343 Ns276p473 (Ns276p1619 (RS277to288.d46 qz62 qz80 qz266) RS277to288.d50) rfl 

noncomputable def Ns276p1621 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz265 qz4 qz62 582385 1000 585158 1000 

noncomputable def Ns276p1622 := @Enclosure.norm_gt_of_isNear qz265 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 405809096949892316347 295147905179352825856 2935889361823138143629 

noncomputable def Ns276p1623 := @Ns276p1622 Ns276p201 175153213 2684354560 1421 2684354560 (Ns276p1617 (RS277to288.d4 qz62 qz80 qz266) RS277to288.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable def Ns276p1624 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz267 qz4 qz80 582385 1000 586544 1000 

noncomputable def Ns276p1625 := @Enclosure.norm_gt_of_isNear qz267 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 56348081654729195797 147573952589676412928 184292738506395261377343 

noncomputable def Ns276p1626 := @Ns276p1625 Ns276p473 175153213 2684354560 1421 2684354560 (Ns276p1619 (RS277to288.d46 qz62 qz80 qz266) RS277to288.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable abbrev qz268 := qz549

noncomputable def Ns276p1627 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz62 585158 1000 qz65 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz265 qz267 (Ns276p1618 rfl rfl) (Ns276p1620 rfl rfl)) (Ns276p1621 qz11 qz65 rfl rfl rfl rfl (Ns276p1623 rfl)) (Ns276p1624 qz11 qz83 rfl rfl rfl rfl (Ns276p1626 rfl)) 

noncomputable abbrev qz551 := (RS277to288.d3 qz623 qz633 (@Enclosure.dec_le_dec qz623 qz633 586544 1000 587929 1000 qz627 qz637 rfl rfl rfl))

noncomputable abbrev qz269 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz551)

noncomputable def Ns276p1628 := @Enclosure.Real.IsNear.of_eq qz269 (hardyZApproximantRS₀ qz80) Bool.false 56348081654729195797 147573952589676412928 184292738506395261377343 Ns276p473 

noncomputable abbrev qz552 := (@Enclosure.dec_le_dec qz623 qz633 586544 1000 587929 1000 qz627 qz637 rfl rfl rfl)

noncomputable abbrev qz270 := qz552

noncomputable def Ns276p1629 := @Enclosure.Real.IsNear.pos_val qz269 56348081654729195797 147573952589676412928 184292738506395261377343 Ns276p473 (Ns276p1628 (RS277to288.d4 qz80 qz98 qz270) RS277to288.d50) rfl 

noncomputable abbrev qz271 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz551)

noncomputable def Ns276p1630 := @Enclosure.Real.IsNear.of_eq qz271 (hardyZApproximantRS₀ qz98) Bool.true 716331721659770239725 590295810358705651712 185036001649372956306957 Ns276p473 

noncomputable def Ns276p1631 := @Enclosure.Real.IsNear.neg_val qz271 716331721659770239725 590295810358705651712 185036001649372956306957 Ns276p473 (Ns276p1630 (RS277to288.d46 qz80 qz98 qz270) RS277to288.d51) rfl 

noncomputable def Ns276p1632 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz269 qz4 qz80 582385 1000 586544 1000 

noncomputable def Ns276p1633 := @Enclosure.norm_gt_of_isNear qz269 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 56348081654729195797 147573952589676412928 184292738506395261377343 

noncomputable def Ns276p1634 := @Ns276p1633 Ns276p473 175153213 2684354560 1421 2684354560 (Ns276p1628 (RS277to288.d4 qz80 qz98 qz270) RS277to288.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable def Ns276p1635 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz271 qz4 qz98 582385 1000 587929 1000 

noncomputable def Ns276p1636 := @Enclosure.norm_gt_of_isNear qz271 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 716331721659770239725 590295810358705651712 185036001649372956306957 

noncomputable def Ns276p1637 := @Ns276p1636 Ns276p473 175153213 2684354560 1421 2684354560 (Ns276p1630 (RS277to288.d46 qz80 qz98 qz270) RS277to288.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable abbrev qz272 := qz551

noncomputable def Ns276p1638 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz80 586544 1000 qz83 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz269 qz271 (Ns276p1629 rfl rfl) (Ns276p1631 rfl rfl)) (Ns276p1632 qz11 qz83 rfl rfl rfl rfl (Ns276p1634 rfl)) (Ns276p1635 qz11 qz101 rfl rfl rfl rfl (Ns276p1637 rfl)) 

noncomputable abbrev qz553 := (RS277to288.d3 qz633 qz643 (@Enclosure.dec_le_dec qz633 qz643 587929 1000 589313 1000 qz637 qz647 rfl rfl rfl))

noncomputable abbrev qz273 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz553)

noncomputable def Ns276p1639 := @Enclosure.Real.IsNear.of_eq qz273 (hardyZApproximantRS₀ qz98) Bool.true 716331721659770239725 590295810358705651712 185036001649372956306957 Ns276p473 

noncomputable abbrev qz554 := (@Enclosure.dec_le_dec qz633 qz643 587929 1000 589313 1000 qz637 qz647 rfl rfl rfl)

noncomputable abbrev qz274 := qz554

noncomputable def Ns276p1640 := @Enclosure.Real.IsNear.neg_val qz273 716331721659770239725 590295810358705651712 185036001649372956306957 Ns276p473 (Ns276p1639 (RS277to288.d4 qz98 qz116 qz274) RS277to288.d51) rfl 

noncomputable abbrev qz275 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz553)

noncomputable def Ns276p1641 := @Enclosure.Real.IsNear.of_eq qz275 (hardyZApproximantRS₀ qz116) Bool.false 575687507975566935855 73786976294838206464 23262741867299570065347 Ns276p700 

noncomputable def Ns276p1642 := @Enclosure.Real.IsNear.pos_val qz275 575687507975566935855 73786976294838206464 23262741867299570065347 Ns276p700 (Ns276p1641 (RS277to288.d46 qz98 qz116 qz274) RS277to288.d52) rfl 

noncomputable def Ns276p1643 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz273 qz4 qz98 582385 1000 587929 1000 

noncomputable def Ns276p1644 := @Enclosure.norm_gt_of_isNear qz273 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 716331721659770239725 590295810358705651712 185036001649372956306957 

noncomputable def Ns276p1645 := @Ns276p1644 Ns276p473 175153213 2684354560 1421 2684354560 (Ns276p1639 (RS277to288.d4 qz98 qz116 qz274) RS277to288.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable def Ns276p1646 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz275 qz4 qz116 582385 1000 589313 1000 

noncomputable def Ns276p1647 := @Enclosure.norm_gt_of_isNear qz275 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 575687507975566935855 73786976294838206464 23262741867299570065347 

noncomputable def Ns276p1648 := @Ns276p1647 Ns276p700 175153213 2684354560 1421 2684354560 (Ns276p1641 (RS277to288.d46 qz98 qz116 qz274) RS277to288.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable abbrev qz276 := qz553

noncomputable def Ns276p1649 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz98 587929 1000 qz101 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz273 qz275 (Ns276p1640 rfl rfl) (Ns276p1642 rfl rfl)) (Ns276p1643 qz11 qz101 rfl rfl rfl rfl (Ns276p1645 rfl)) (Ns276p1646 qz11 qz119 rfl rfl rfl rfl (Ns276p1648 rfl)) 

noncomputable abbrev qz555 := (RS277to288.d3 qz643 qz653 (@Enclosure.dec_le_dec qz643 qz653 589313 1000 590696 1000 qz647 qz657 rfl rfl rfl))

noncomputable abbrev qz277 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz555)

noncomputable def Ns276p1650 := @Enclosure.Real.IsNear.of_eq qz277 (hardyZApproximantRS₀ qz116) Bool.false 575687507975566935855 73786976294838206464 23262741867299570065347 Ns276p700 

noncomputable abbrev qz556 := (@Enclosure.dec_le_dec qz643 qz653 589313 1000 590696 1000 qz647 qz657 rfl rfl rfl)

noncomputable abbrev qz278 := qz556

noncomputable def Ns276p1651 := @Enclosure.Real.IsNear.pos_val qz277 575687507975566935855 73786976294838206464 23262741867299570065347 Ns276p700 (Ns276p1650 (RS277to288.d4 qz116 qz134 qz278) RS277to288.d52) rfl 

noncomputable abbrev qz279 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz555)

noncomputable def Ns276p1652 := @Enclosure.Real.IsNear.of_eq qz279 (hardyZApproximantRS₀ qz134) Bool.true 100692272024776496595 590295810358705651712 187298460347814285373627 Ns276p473 

noncomputable def Ns276p1653 := @Enclosure.Real.IsNear.neg_val qz279 100692272024776496595 590295810358705651712 187298460347814285373627 Ns276p473 (Ns276p1652 (RS277to288.d46 qz116 qz134 qz278) RS277to288.d53) rfl 

noncomputable def Ns276p1654 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz277 qz4 qz116 582385 1000 589313 1000 

noncomputable def Ns276p1655 := @Enclosure.norm_gt_of_isNear qz277 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 575687507975566935855 73786976294838206464 23262741867299570065347 

noncomputable def Ns276p1656 := @Ns276p1655 Ns276p700 175153213 2684354560 1421 2684354560 (Ns276p1650 (RS277to288.d4 qz116 qz134 qz278) RS277to288.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable def Ns276p1657 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz279 qz4 qz134 582385 1000 590696 1000 

noncomputable def Ns276p1658 := @Enclosure.norm_gt_of_isNear qz279 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 100692272024776496595 590295810358705651712 187298460347814285373627 

noncomputable def Ns276p1659 := @Ns276p1658 Ns276p473 175153213 2684354560 1421 2684354560 (Ns276p1652 (RS277to288.d46 qz116 qz134 qz278) RS277to288.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable abbrev qz280 := qz555

noncomputable def Ns276p1660 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz116 589313 1000 qz119 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz277 qz279 (Ns276p1651 rfl rfl) (Ns276p1653 rfl rfl)) (Ns276p1654 qz11 qz119 rfl rfl rfl rfl (Ns276p1656 rfl)) (Ns276p1657 qz11 qz137 rfl rfl rfl rfl (Ns276p1659 rfl)) 

noncomputable abbrev qz557 := (RS277to288.d3 qz653 qz663 (@Enclosure.dec_le_dec qz653 qz663 590696 1000 592078 1000 qz657 qz667 rfl rfl rfl))

noncomputable abbrev qz281 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz557)

noncomputable def Ns276p1661 := @Enclosure.Real.IsNear.of_eq qz281 (hardyZApproximantRS₀ qz134) Bool.true 100692272024776496595 590295810358705651712 187298460347814285373627 Ns276p473 

noncomputable abbrev qz558 := (@Enclosure.dec_le_dec qz653 qz663 590696 1000 592078 1000 qz657 qz667 rfl rfl rfl)

noncomputable abbrev qz282 := qz558

noncomputable def Ns276p1662 := @Enclosure.Real.IsNear.neg_val qz281 100692272024776496595 590295810358705651712 187298460347814285373627 Ns276p473 (Ns276p1661 (RS277to288.d4 qz134 qz152 qz282) RS277to288.d53) rfl 

noncomputable abbrev qz283 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz557)

noncomputable def Ns276p1663 := @Enclosure.Real.IsNear.of_eq qz283 (hardyZApproximantRS₀ qz152) Bool.false 627017215265475505089 1180591620717411303424 377453098294781393280823 Ns276p926 

noncomputable def Ns276p1664 := @Enclosure.Real.IsNear.pos_val qz283 627017215265475505089 1180591620717411303424 377453098294781393280823 Ns276p926 (Ns276p1663 (RS277to288.d46 qz134 qz152 qz282) RS277to288.d54) rfl 

noncomputable def Ns276p1665 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz281 qz4 qz134 582385 1000 590696 1000 

noncomputable def Ns276p1666 := @Enclosure.norm_gt_of_isNear qz281 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 100692272024776496595 590295810358705651712 187298460347814285373627 

noncomputable def Ns276p1667 := @Ns276p1666 Ns276p473 175153213 2684354560 1421 2684354560 (Ns276p1661 (RS277to288.d4 qz134 qz152 qz282) RS277to288.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable def Ns276p1668 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz283 qz4 qz152 582385 1000 592078 1000 

noncomputable def Ns276p1669 := @Enclosure.norm_gt_of_isNear qz283 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 627017215265475505089 1180591620717411303424 377453098294781393280823 

noncomputable def Ns276p1670 := @Ns276p1669 Ns276p926 175153213 2684354560 1421 2684354560 (Ns276p1663 (RS277to288.d46 qz134 qz152 qz282) RS277to288.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable abbrev qz284 := qz557

noncomputable def Ns276p1671 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz134 590696 1000 qz137 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz281 qz283 (Ns276p1662 rfl rfl) (Ns276p1664 rfl rfl)) (Ns276p1665 qz11 qz137 rfl rfl rfl rfl (Ns276p1667 rfl)) (Ns276p1668 qz11 qz155 rfl rfl rfl rfl (Ns276p1670 rfl)) 

noncomputable abbrev qz559 := (RS277to288.d3 qz663 qz673 (@Enclosure.dec_le_dec qz663 qz673 592078 1000 593460 1000 qz667 qz677 rfl rfl rfl))

noncomputable abbrev qz285 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz559)

noncomputable def Ns276p1672 := @Enclosure.Real.IsNear.of_eq qz285 (hardyZApproximantRS₀ qz152) Bool.false 627017215265475505089 1180591620717411303424 377453098294781393280823 Ns276p926 

noncomputable abbrev qz560 := (@Enclosure.dec_le_dec qz663 qz673 592078 1000 593460 1000 qz667 qz677 rfl rfl rfl)

noncomputable abbrev qz286 := qz560

noncomputable def Ns276p1673 := @Enclosure.Real.IsNear.pos_val qz285 627017215265475505089 1180591620717411303424 377453098294781393280823 Ns276p926 (Ns276p1672 (RS277to288.d4 qz152 qz170 qz286) RS277to288.d54) rfl 

noncomputable abbrev qz287 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz559)

noncomputable def Ns276p1674 := @Enclosure.Real.IsNear.of_eq qz287 (hardyZApproximantRS₀ qz170) Bool.true 849112518609285706585 590295810358705651712 3828428426612649341399 Ns276p1044 

noncomputable def Ns276p1675 := @Enclosure.Real.IsNear.neg_val qz287 849112518609285706585 590295810358705651712 3828428426612649341399 Ns276p1044 (Ns276p1674 (RS277to288.d46 qz152 qz170 qz286) RS277to288.d55) rfl 

noncomputable def Ns276p1676 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz285 qz4 qz152 582385 1000 592078 1000 

noncomputable def Ns276p1677 := @Enclosure.norm_gt_of_isNear qz285 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 627017215265475505089 1180591620717411303424 377453098294781393280823 

noncomputable def Ns276p1678 := @Ns276p1677 Ns276p926 175153213 2684354560 1421 2684354560 (Ns276p1672 (RS277to288.d4 qz152 qz170 qz286) RS277to288.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable def Ns276p1679 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz287 qz4 qz170 582385 1000 593460 1000 

noncomputable def Ns276p1680 := @Enclosure.norm_gt_of_isNear qz287 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 849112518609285706585 590295810358705651712 3828428426612649341399 

noncomputable def Ns276p1681 := @Ns276p1680 Ns276p1044 175153213 2684354560 1421 2684354560 (Ns276p1674 (RS277to288.d46 qz152 qz170 qz286) RS277to288.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable abbrev qz288 := qz559

noncomputable def Ns276p1682 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz152 592078 1000 qz155 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz285 qz287 (Ns276p1673 rfl rfl) (Ns276p1675 rfl rfl)) (Ns276p1676 qz11 qz155 rfl rfl rfl rfl (Ns276p1678 rfl)) (Ns276p1679 qz11 qz173 rfl rfl rfl rfl (Ns276p1681 rfl)) 

noncomputable abbrev qz724 := (@Enclosure.dec_le_dec qz769 qz773 593460 1000 594841 1000 (@Eq.refl Real qz769) (@Eq.refl Real qz773) rfl rfl rfl)

noncomputable abbrev qz561 := (RS277to288.d3 qz673 qz683 qz724)

noncomputable abbrev qz289 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz561)

noncomputable def Ns276p1683 := @Enclosure.Real.IsNear.of_eq qz289 (hardyZApproximantRS₀ qz170) Bool.true 849112518609285706585 590295810358705651712 3828428426612649341399 Ns276p1044 

noncomputable abbrev qz562 := qz724

noncomputable abbrev qz290 := qz562

noncomputable def Ns276p1684 := @Enclosure.Real.IsNear.neg_val qz289 849112518609285706585 590295810358705651712 3828428426612649341399 Ns276p1044 (Ns276p1683 (RS277to288.d4 qz170 qz188 qz290) RS277to288.d55) rfl 

noncomputable abbrev qz291 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz561)

noncomputable def Ns276p1685 := @Enclosure.Real.IsNear.of_eq qz291 (hardyZApproximantRS₀ qz188) Bool.false 2855645224508284954661 1180591620717411303424 391760529497045061668963 Ns276p926 

noncomputable def Ns276p1686 := @Enclosure.Real.IsNear.pos_val qz291 2855645224508284954661 1180591620717411303424 391760529497045061668963 Ns276p926 (Ns276p1685 (RS277to288.d46 qz170 qz188 qz290) RS277to288.d56) rfl 

noncomputable def Ns276p1687 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz289 qz4 qz170 582385 1000 593460 1000 

noncomputable def Ns276p1688 := @Enclosure.norm_gt_of_isNear qz289 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 849112518609285706585 590295810358705651712 3828428426612649341399 

noncomputable def Ns276p1689 := @Ns276p1688 Ns276p1044 175153213 2684354560 1421 2684354560 (Ns276p1683 (RS277to288.d4 qz170 qz188 qz290) RS277to288.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable def Ns276p1690 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz291 qz4 qz188 582385 1000 594841 1000 

noncomputable def Ns276p1691 := @Enclosure.norm_gt_of_isNear qz291 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2855645224508284954661 1180591620717411303424 391760529497045061668963 

noncomputable def Ns276p1692 := @Ns276p1691 Ns276p926 175153213 2684354560 1421 2684354560 (Ns276p1685 (RS277to288.d46 qz170 qz188 qz290) RS277to288.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable abbrev qz292 := qz561

noncomputable def Ns276p1693 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz170 593460 1000 qz173 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz289 qz291 (Ns276p1684 rfl rfl) (Ns276p1686 rfl rfl)) (Ns276p1687 qz11 qz173 rfl rfl rfl rfl (Ns276p1689 rfl)) (Ns276p1690 qz11 qz191 rfl rfl rfl rfl (Ns276p1692 rfl)) 

noncomputable abbrev qz725 := (@Enclosure.dec_le_dec qz773 qz777 594841 1000 596222 1000 (@Eq.refl Real qz773) qz780 rfl rfl rfl)

noncomputable abbrev qz563 := (RS277to288.d3 qz683 qz693 qz725)

noncomputable abbrev qz293 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz563)

noncomputable def Ns276p1694 := @Enclosure.Real.IsNear.of_eq qz293 (hardyZApproximantRS₀ qz188) Bool.false 2855645224508284954661 1180591620717411303424 391760529497045061668963 Ns276p926 

noncomputable abbrev qz564 := qz725

noncomputable abbrev qz294 := qz564

noncomputable def Ns276p1695 := @Enclosure.Real.IsNear.pos_val qz293 2855645224508284954661 1180591620717411303424 391760529497045061668963 Ns276p926 (Ns276p1694 (RS277to288.d4 qz188 qz206 qz294) RS277to288.d56) rfl 

noncomputable abbrev qz295 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz563)

noncomputable def Ns276p1696 := @Enclosure.Real.IsNear.of_eq qz295 (hardyZApproximantRS₀ qz206) Bool.true 100673271324192596401 295147905179352825856 21258195017361470892809 Ns276p1269 

noncomputable def Ns276p1697 := @Enclosure.Real.IsNear.neg_val qz295 100673271324192596401 295147905179352825856 21258195017361470892809 Ns276p1269 (Ns276p1696 (RS277to288.d46 qz188 qz206 qz294) RS277to288.d57) rfl 

noncomputable def Ns276p1698 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz293 qz4 qz188 582385 1000 594841 1000 

noncomputable def Ns276p1699 := @Enclosure.norm_gt_of_isNear qz293 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2855645224508284954661 1180591620717411303424 391760529497045061668963 

noncomputable def Ns276p1700 := @Ns276p1699 Ns276p926 175153213 2684354560 1421 2684354560 (Ns276p1694 (RS277to288.d4 qz188 qz206 qz294) RS277to288.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable def Ns276p1701 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz295 qz4 qz206 582385 1000 596222 1000 

noncomputable def Ns276p1702 := @Enclosure.norm_gt_of_isNear qz295 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 100673271324192596401 295147905179352825856 21258195017361470892809 

noncomputable def Ns276p1703 := @Ns276p1702 Ns276p1269 175153213 2684354560 1421 2684354560 (Ns276p1696 (RS277to288.d46 qz188 qz206 qz294) RS277to288.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable abbrev qz296 := qz563

noncomputable def Ns276p1704 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz188 594841 1000 qz191 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz293 qz295 (Ns276p1695 rfl rfl) (Ns276p1697 rfl rfl)) (Ns276p1698 qz11 qz191 rfl rfl rfl rfl (Ns276p1700 rfl)) (Ns276p1701 qz11 qz209 rfl rfl rfl rfl (Ns276p1703 rfl)) 

noncomputable abbrev qz726 := (@Enclosure.dec_le_dec qz777 qz782 596222 1000 597602 1000 qz780 qz785 rfl rfl rfl)

noncomputable abbrev qz565 := (RS277to288.d3 qz693 qz704 qz726)

noncomputable abbrev qz297 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz565)

noncomputable def Ns276p1705 := @Enclosure.Real.IsNear.of_eq qz297 (hardyZApproximantRS₀ qz206) Bool.true 100673271324192596401 295147905179352825856 21258195017361470892809 Ns276p1269 

noncomputable abbrev qz566 := qz726

noncomputable abbrev qz298 := qz566

noncomputable def Ns276p1706 := @Enclosure.Real.IsNear.neg_val qz297 100673271324192596401 295147905179352825856 21258195017361470892809 Ns276p1269 (Ns276p1705 (RS277to288.d4 qz206 qz223 qz298) RS277to288.d57) rfl 

noncomputable abbrev qz299 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz565)

noncomputable def Ns276p1707 := @Enclosure.Real.IsNear.of_eq qz299 (hardyZApproximantRS₀ qz223) Bool.false 20354363074516999597 4611686018427387904 71050358676156943801201 Ns276p1381 

noncomputable def Ns276p1708 := @Enclosure.Real.IsNear.pos_val qz299 20354363074516999597 4611686018427387904 71050358676156943801201 Ns276p1381 (Ns276p1707 (RS277to288.d46 qz206 qz223 qz298) RS277to288.d58) rfl 

noncomputable def Ns276p1709 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz297 qz4 qz206 582385 1000 596222 1000 

noncomputable def Ns276p1710 := @Enclosure.norm_gt_of_isNear qz297 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 100673271324192596401 295147905179352825856 21258195017361470892809 

noncomputable def Ns276p1711 := @Ns276p1710 Ns276p1269 175153213 2684354560 1421 2684354560 (Ns276p1705 (RS277to288.d4 qz206 qz223 qz298) RS277to288.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable def Ns276p1712 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz299 qz4 qz223 582385 1000 597602 1000 

noncomputable def Ns276p1713 := @Enclosure.norm_gt_of_isNear qz299 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 20354363074516999597 4611686018427387904 71050358676156943801201 

noncomputable def Ns276p1714 := @Ns276p1713 Ns276p1381 175153213 2684354560 1421 2684354560 (Ns276p1707 (RS277to288.d46 qz206 qz223 qz298) RS277to288.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable abbrev qz300 := qz565

noncomputable def Ns276p1715 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz206 596222 1000 qz209 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz297 qz299 (Ns276p1706 rfl rfl) (Ns276p1708 rfl rfl)) (Ns276p1709 qz11 qz209 rfl rfl rfl rfl (Ns276p1711 rfl)) (Ns276p1712 qz11 qz226 rfl rfl rfl rfl (Ns276p1714 rfl)) 

noncomputable abbrev qz792 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 597602 1000) (Enclosure.sfrac Bool.false 598981 1000) 597602 1000 598981 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 597602 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 598981 1000)) rfl rfl rfl)

noncomputable abbrev qz727 := qz792

noncomputable abbrev qz567 := (RS277to288.d3 qz704 qz714 qz727)

noncomputable abbrev qz301 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz567)

noncomputable def Ns276p1716 := @Enclosure.Real.IsNear.of_eq qz301 (hardyZApproximantRS₀ qz223) Bool.false 20354363074516999597 4611686018427387904 71050358676156943801201 Ns276p1381 

noncomputable abbrev qz568 := qz727

noncomputable abbrev qz302 := qz568

noncomputable def Ns276p1717 := @Enclosure.Real.IsNear.pos_val qz301 20354363074516999597 4611686018427387904 71050358676156943801201 Ns276p1381 (Ns276p1716 (RS277to288.d4 qz223 qz240 qz302) RS277to288.d58) rfl 

noncomputable abbrev qz303 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz567)

noncomputable def Ns276p1718 := @Enclosure.Real.IsNear.of_eq qz303 (hardyZApproximantRS₀ qz240) Bool.true 3918208661591739748565 2361183241434822606848 162928900454652227227033 Ns276p1489 

noncomputable def Ns276p1719 := @Enclosure.Real.IsNear.neg_val qz303 3918208661591739748565 2361183241434822606848 162928900454652227227033 Ns276p1489 (Ns276p1718 (RS277to288.d46 qz223 qz240 qz302) RS277to288.d59) rfl 

noncomputable def Ns276p1720 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz301 qz4 qz223 582385 1000 597602 1000 

noncomputable def Ns276p1721 := @Enclosure.norm_gt_of_isNear qz301 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 20354363074516999597 4611686018427387904 71050358676156943801201 

noncomputable def Ns276p1722 := @Ns276p1721 Ns276p1381 175153213 2684354560 1421 2684354560 (Ns276p1716 (RS277to288.d4 qz223 qz240 qz302) RS277to288.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable def Ns276p1723 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz303 qz4 qz240 582385 1000 598981 1000 

noncomputable def Ns276p1724 := @Enclosure.norm_gt_of_isNear qz303 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 3918208661591739748565 2361183241434822606848 162928900454652227227033 

noncomputable def Ns276p1725 := @Ns276p1724 Ns276p1489 175153213 2684354560 1421 2684354560 (Ns276p1718 (RS277to288.d46 qz223 qz240 qz302) RS277to288.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 175153213 2684354560 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS277to288.d48) rfl rfl rfl rfl 

noncomputable abbrev qz304 := qz567

noncomputable def Ns276p1726 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz223 597602 1000 qz226 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz301 qz303 (Ns276p1717 rfl rfl) (Ns276p1719 rfl rfl)) (Ns276p1720 qz11 qz226 rfl rfl rfl rfl (Ns276p1722 rfl)) (Ns276p1723 qz11 qz243 rfl rfl rfl rfl (Ns276p1725 rfl)) 

noncomputable def Ns276p1727 := @List.cons RS277to288.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns276p1715)) (@List.cons RS277to288.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns276p1726)) (@List.nil RS277to288.d0)) 

noncomputable def Ns276p1728 := @List.cons RS277to288.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns276p1693)) (@List.cons RS277to288.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns276p1704)) Ns276p1727) 

noncomputable def Ns276p1729 := @List.cons RS277to288.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns276p1671)) (@List.cons RS277to288.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns276p1682)) Ns276p1728) 

noncomputable def Ns276p1730 := @List.cons RS277to288.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns276p1649)) (@List.cons RS277to288.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns276p1660)) Ns276p1729) 

noncomputable def Ns276p1731 := @List.cons RS277to288.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns276p1627)) (@List.cons RS277to288.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns276p1638)) Ns276p1730) 

noncomputable def Ns276p1732 := @List.cons RS277to288.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz260 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz260) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz260) Ns276p1605)) (@List.cons RS277to288.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz264 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz264) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz264) Ns276p1616)) Ns276p1731) 

noncomputable abbrev qz569 := (RS277to288.d2 qz673 qz683 qz724)

noncomputable abbrev qz728 := (RS277to288.d2 qz777 qz782 (@Enclosure.dec_le_dec qz777 qz782 596222 1000 597602 1000 qz780 qz785 rfl rfl rfl))

noncomputable abbrev qz729 := (@List.cons RS277to288.d1 (RS277to288.d2 qz782 qz787 qz792) (@List.nil RS277to288.d1))

noncomputable abbrev qz570 := (@List.cons RS277to288.d1 (RS277to288.d2 qz683 qz693 qz725) (@List.cons RS277to288.d1 qz728 qz729))

noncomputable abbrev qz305 := (@List.cons RS277to288.d1 (RS277to288.d2 qz470 qz483 qz560) (@List.cons RS277to288.d1 qz569 qz570))

noncomputable def Ns276p1733 := @List.cons RS277to288.d1 (RS277to288.d2 qz116 qz134 qz278) (@List.cons RS277to288.d1 (RS277to288.d2 qz134 qz152 qz282) qz305) 

noncomputable abbrev qz306 := (RS277to288.d2 qz431 qz444 qz554)

noncomputable def Ns276p1734 := @List.IsChain.cons_cons RS277to288.d1 RS277to288.d60 qz306 (RS277to288.d2 qz116 qz134 qz278) (@List.cons RS277to288.d1 (RS277to288.d2 qz134 qz152 qz282) qz305) 

noncomputable def Ns276p1735 := @List.IsChain.cons_cons RS277to288.d1 RS277to288.d60 (RS277to288.d2 qz116 qz134 qz278) (RS277to288.d2 qz134 qz152 qz282) qz305 (@Enclosure.dec_le_dec qz134 qz134 590696 1000 590696 1000 qz137 qz137 rfl rfl rfl) 

noncomputable abbrev qz307 := (RS277to288.d2 qz470 qz483 qz560)

noncomputable abbrev qz308 := qz569

noncomputable abbrev qz309 := qz570

noncomputable abbrev qz571 := (RS277to288.d2 qz683 qz693 qz725)

noncomputable abbrev qz310 := qz571

noncomputable abbrev qz572 := (@List.cons RS277to288.d1 qz728 qz729)

noncomputable abbrev qz311 := qz572

noncomputable abbrev qz573 := qz728

noncomputable abbrev qz312 := qz573

noncomputable abbrev qz574 := qz729

noncomputable abbrev qz313 := qz574

noncomputable abbrev qz730 := (RS277to288.d2 qz782 qz787 qz792)

noncomputable abbrev qz575 := qz730

noncomputable abbrev qz314 := qz575

noncomputable def Ns276p1736 := @List.IsChain.cons_cons RS277to288.d1 RS277to288.d60 qz307 qz308 qz309 (@Enclosure.dec_le_dec qz170 qz170 593460 1000 593460 1000 qz173 qz173 rfl rfl rfl) (@List.IsChain.cons_cons RS277to288.d1 RS277to288.d60 qz308 qz310 qz311 (@Enclosure.dec_le_dec qz188 qz188 594841 1000 594841 1000 qz191 qz191 rfl rfl rfl) (@List.IsChain.cons_cons RS277to288.d1 RS277to288.d60 qz310 qz312 qz313 (@Enclosure.dec_le_dec qz206 qz206 596222 1000 596222 1000 qz209 qz209 rfl rfl rfl) (@List.IsChain.cons_cons RS277to288.d1 RS277to288.d60 qz312 qz314 (@List.nil RS277to288.d1) (@Enclosure.dec_le_dec qz223 qz223 597602 1000 597602 1000 qz226 qz226 rfl rfl rfl) (@List.IsChain.singleton RS277to288.d1 RS277to288.d60 qz314)))) 

noncomputable abbrev qz315 := (@List.cons RS277to288.d1 qz569 qz570)

noncomputable def Ns276p1737 := @List.IsChain.cons_cons RS277to288.d1 RS277to288.d60 (RS277to288.d2 qz134 qz152 qz282) qz307 qz315 (@Enclosure.dec_le_dec qz152 qz152 592078 1000 592078 1000 qz155 qz155 rfl rfl rfl) Ns276p1736 

noncomputable def Ns276p1738 := @List.IsChain.cons_cons RS277to288.d1 RS277to288.d60 (RS277to288.d2 qz4 qz35 qz258) (RS277to288.d2 qz35 qz62 qz262) (@List.cons RS277to288.d1 (RS277to288.d2 qz62 qz80 qz266) (@List.cons RS277to288.d1 (RS277to288.d2 qz80 qz98 qz270) (@List.cons RS277to288.d1 qz306 Ns276p1733))) (@Enclosure.dec_le_dec qz35 qz35 583772 1000 583772 1000 qz38 qz38 rfl rfl rfl) (@List.IsChain.cons_cons RS277to288.d1 RS277to288.d60 (RS277to288.d2 qz35 qz62 qz262) (RS277to288.d2 qz62 qz80 qz266) (@List.cons RS277to288.d1 (RS277to288.d2 qz80 qz98 qz270) (@List.cons RS277to288.d1 qz306 Ns276p1733)) (@Enclosure.dec_le_dec qz62 qz62 585158 1000 585158 1000 qz65 qz65 rfl rfl rfl) (@List.IsChain.cons_cons RS277to288.d1 RS277to288.d60 (RS277to288.d2 qz62 qz80 qz266) (RS277to288.d2 qz80 qz98 qz270) (@List.cons RS277to288.d1 qz306 Ns276p1733) (@Enclosure.dec_le_dec qz80 qz80 586544 1000 586544 1000 qz83 qz83 rfl rfl rfl) (@List.IsChain.cons_cons RS277to288.d1 RS277to288.d60 (RS277to288.d2 qz80 qz98 qz270) qz306 Ns276p1733 (@Enclosure.dec_le_dec qz98 qz98 587929 1000 587929 1000 qz101 qz101 rfl rfl rfl) (Ns276p1734 (@Enclosure.dec_le_dec qz116 qz116 589313 1000 589313 1000 qz119 qz119 rfl rfl rfl) (Ns276p1735 Ns276p1737))))) 

noncomputable abbrev qz576 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz577 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns276p1732 Ns276p1738)

noncomputable abbrev qz578 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns276p1732 Ns276p1738))

theorem RS277to288.d61 : Zeta.Certificates.BatchSpec 12 582385 1000 598981 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz576 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz576 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz576 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz240)))) qz577 (@And.intro (@Eq Nat (@List.length qz576 qz578) 12) (And (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz576 qz578)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz576 qz578)) (@Option.some Real qz240))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz576 qz578)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz576 qz578)) (@Option.some Real qz240)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz240))))

theorem solution : Zeta.Certificates.BatchSpec 12 582385 1000 598981 1000 := RS277to288.d61
#print axioms solution
#check solution
