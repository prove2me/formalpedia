-- Prove2me | solution 1 for RHHeight1000.rs_main_0223_0240
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T07:52:14.81973+00:00
-- url     : https://prove2.me/submissions/6f3c7dd1-d041-42fb-8de0-f9a6ab0380e1

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

noncomputable def RS223to240.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS223to240.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS223to240.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS223to240.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS223to240.d2 a b h 

theorem RS223to240.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS223to240.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS223to240.d3 a b h)) 

noncomputable def Ns222p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns222p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns222p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns222p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns222p0 Ns222p1 Ns222p2 Ns222p1 153643044 134217728 1 46240000 153643044 134217728 1 46240000 76821522 67108864 2 67108864 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns222p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns222p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns222p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns222p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns222p8 := nat_lit 167537954069964697925743468333314178468718661948561187618563575975392713740913527107727581163208035826476740967700482432525301063254420572874757592895482956004842597348203117269212172556829666669574421653274845612596416189641484794702002223261246862056663160605878293700340502480877986491439034432953223334258717026053687371824342493299510132312376251152844516906794910572262907940062760396663270105627554083664899640691826599584783763757814813433640133591539937449421955686657622469485188711283992428713614179785896055117030632677201478317872225272595773536303110412989181984739022579128493081560758017763072115692678596043664844667144619713966763611484179303468167142547433165016751768184247559143333542643815355903304572487929375 

noncomputable def Ns222p9 := nat_lit 17907736863639440849562382641391758203535690054199171304015283257442503423240620144819838407313611418261944516207295868563739563278604805791797182761045687776939279949642059267526948014748996956777332184087524644234759874591635243045607722412471722018588244283882362848653445974523544951031470230725674276297342086185092985546835544820091590454230569790847977790484558207349923322458845585052164126500435851662252152223728079705692133047658564669873831757357628115566356048471439549797170528303905720944834637690907185213991407615774042056720704508980680095051114888612186461088301140868302968264130481206655302741383410655080008578156649725227045954510069588220729495895148666460653631514375880874422615237249871322129146554264800 

noncomputable def Ns222p10 := nat_lit 55164646516618494962085419356369025784335016154267579706247610053041231157772817011486486467101704279863254798704146668052276438579475100451766223896220272709675360577301802978530276301158911649961092601279696986330335403118086533522541958716560166657634553390183479955483588238249446822384543398154260439705049143284278540285021213103458182619368483938376641172730818250587232036579805400979202432024046862170503602539341971086573372247299262086029843105216008583038025403798224342134620653974939981235680083776396058604459065501719125356177784467570909658245422960948263734871602033841948787585406240093531041217463298165642337705122589129757920995868559518021463265498464182174549661735402095023640043996665674913376875 

noncomputable def Ns222p11 := BSN.log_dyadic_bound Ns222p6 Ns222p7 15 14 Ns222p8 134217728 46240000 Ns222p9 Ns222p10 153643044 Ns222p4 Ns222p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns222p6) (BSN.artanhQ Ns222p7) 0 14 Ns222p9 Ns222p8 Ns222p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns222p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns222p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns222p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns222p15 := nat_lit 167537954069966963268140139327979112712430526945422964221951926912223381190141639739514890494967825643602350173964944759828460064784215684919760383437959917620844610857567326816719640593037578236900835917107172977527392439886629774248115214831425484905681376157923696414882114961796820014026232307332015059110330001516939277521159573995394989771587717775443426002499543257897301982481613760098955890450106043861450716722534643739571053080256776912576113428445260435254713579381797931690799491102381747484553243404562568585572234105168360737285205910186933811836504830286397217473365026331067977496463917110493303316865058355012304571237619413071097245713770677768486493924969821719264401216877841676972336093778875903304572487929375 

noncomputable def Ns222p16 := nat_lit 17907736863639702486765313263906285882628955290251965205176678923530777959693011244026517850256414903756943142851250712732214241881959351517241344993825585048584379523049477943740273636414656012170312373198803997844271825165684859407921203335666024680974464565759223251918458072775203410604089667122984485578465112081892102496937045858735135721609691262763214794451343726045584198128451069547586972080574568545086657023793200560105564573365716615162566961587407171758966967827997201380802107846920231945878242774600967607639551032178207663699700360114112068650063802902647517702890145150192721997537569966984346993833704449560383184487996362781528900358997452380059737141488304159449328022742959995775545894292303322129146554264800 

noncomputable def Ns222p17 := nat_lit 55164646516619937449385584700664297411818070214438189962773666351465523500358685366424500506990751111492356556545320273548942244833046464529601272738875466881799996765940232256588350019911833156887888425998391295014189841212513610526066550079316346993943774342801096070086869790972589246312728227659319758310961510342377923950694747797317942483020440897997204711883064182772445608288320382376665481938194224815739627075458138172195220395246294556718284728034954178416253903237031389214179719385823921869528509431462690683227358218086518156757026652846493301460983550768858152506145788622699720737745394141184245149692548799188169247529408201840608223422296381897323845616153036586108326210125693898345963996665674913376875 

noncomputable def Ns222p18 := BSN.log_dyadic_bound Ns222p13 Ns222p14 15 14 Ns222p15 134217728 46240000 Ns222p16 Ns222p17 153643044 Ns222p12 Ns222p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns222p13) (BSN.artanhQ Ns222p14) 0 14 Ns222p16 Ns222p15 Ns222p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns222p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 76821522 67108864 2 67108864 38410761 33554432 1 33554432 (Ns222p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns222p0 Ns222p1 153643044 134217728 1 46240000 Bool.false (BSN.logfrac_isNear Ns222p4 Ns222p5 1 Ns222p0 Ns222p1 153643044 134217728 46240000 rfl rfl rfl (Ns222p11 rfl))) (BSN.isNear_log_sfrac Ns222p2 Ns222p1 153643044 134217728 1 46240000 Bool.false (BSN.logfrac_isNear Ns222p12 Ns222p5 1 Ns222p2 Ns222p1 153643044 134217728 46240000 rfl rfl rfl (Ns222p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS223to240.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 33554432 := Ns222p19 

noncomputable def Ns222p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 8388608 2890000 385100712855 135135 5814539 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz317 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz0 := qz317

theorem RS223to240.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 5814539 8388608 1 2890000 := BSN.isNear_log_sfrac 2 1 5814539 8388608 1 2890000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 5814539 8388608 2890000 rfl rfl rfl (Ns222p20 rfl)) 

theorem RS223to240.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 93032624 134217728 47 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 5814539 8388608 1 2890000 93032624 134217728 47 134217728 RS223to240.d6 rfl 

noncomputable abbrev qz318 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz319 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz628 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz320 := qz628

noncomputable def Ns222p21 := @Enclosure.Real.IsNear.inv_image qz318 23726567 16777216 1 16777216 5931641 5931642 8388608 (@Enclosure.Real.IsNear.of_eq qz318 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz320)) Bool.false 23726567 16777216 1 16777216 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz320)) Bool.false 23726567 16777216 1 16777216 23726567 16777216 1 16777216 (BSN.sqrt_enclosure 2 1 11863283 11863284 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz321 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS223to240.d8 : Enclosure.Real.IsNear qz321 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz321 Bool.false 11863283 16777216 1 16777216 11863283 16777216 1 16777216 (Ns222p21 rfl rfl) rfl 

theorem RS223to240.d9 : Enclosure.Real.IsNear qz321 Bool.false 94906264 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz321 Bool.false 11863283 16777216 1 16777216 94906264 134217728 8 134217728 RS223to240.d8 rfl 

noncomputable def Ns222p22 := BSN.log_dyadic_bound 1 2 12 11 1326382131865190400 8388608 2890000 130797573554866995 13749310575 9215827 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 1) (BSN.artanhQ 2) 0 11 130797573554866995 1326382131865190400 13749310575 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS223to240.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 9215827 8388608 1 2890000 := BSN.isNear_log_sfrac 3 1 9215827 8388608 1 2890000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 9215827 8388608 2890000 rfl rfl rfl (Ns222p22 rfl)) 

theorem RS223to240.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 147453232 134217728 47 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 9215827 8388608 1 2890000 147453232 134217728 47 134217728 RS223to240.d10 rfl 

noncomputable abbrev qz322 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz323 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns222p23 := @Enclosure.Real.IsNear.inv_image qz322 29058991 16777216 1 16777216 4843164 4843166 8388608 (@Enclosure.Real.IsNear.of_eq qz322 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz323 qz320)) Bool.false 29058991 16777216 1 16777216 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz323 qz320)) Bool.false 29058991 16777216 1 16777216 29058991 16777216 1 16777216 (BSN.sqrt_enclosure 3 1 14529495 14529496 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz324 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS223to240.d12 : Enclosure.Real.IsNear qz324 Bool.false 4843165 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz324 Bool.false 9686330 16777216 2 16777216 4843165 8388608 1 8388608 (Ns222p23 rfl rfl) rfl 

theorem RS223to240.d13 : Enclosure.Real.IsNear qz324 Bool.false 77490640 134217728 16 134217728 := @Enclosure.Real.IsNear.recentre' qz324 Bool.false 4843165 8388608 1 8388608 77490640 134217728 16 134217728 RS223to240.d12 rfl 

noncomputable def Ns222p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns222p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns222p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns222p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns222p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns222p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns222p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns222p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns222p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns222p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns222p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns222p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns222p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns222p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns222p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns222p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns222p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns222p25 Ns222p26 Ns222p27 Ns222p28 200200021673987500790625 Ns222p29 Ns222p30 Ns222p31 Ns222p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns222p32 Ns222p33 151412625 Ns222p34 Ns222p35 1322214852783825 Ns222p27 Ns222p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns222p32 Ns222p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns222p34 Ns222p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns222p36 Ns222p37 1267389585 Ns222p38 Ns222p39 1927077560082675 Ns222p29 Ns222p30 Ns222p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns222p36 Ns222p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns222p38 Ns222p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz325 := (@Nat.cast Real Real.instNatCast 5)

theorem RS223to240.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz320 qz325)) Bool.false Ns222p24 Ns222p25 1 Ns222p26 := Ns222p40 rfl rfl rfl 

noncomputable def Ns222p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns222p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns222p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns222p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns222p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns222p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns222p25 Ns222p26 Ns222p42 Ns222p43 9945 Ns222p44 Ns222p45 65835 Ns222p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns222p42 Ns222p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns222p44 Ns222p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS223to240.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz320 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns222p41 Ns222p25 1 Ns222p26 := Ns222p46 rfl 

noncomputable def Ns222p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns222p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS223to240.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns222p47 Ns222p25 1 Ns222p48 := BSN.pi_combine Ns222p24 Ns222p41 Ns222p25 Ns222p26 Ns222p48 Ns222p47 rfl rfl rfl rfl RS223to240.d14 RS223to240.d15 

theorem RS223to240.d17 : Enclosure.Real.IsNear Real.pi Bool.false 7074237752028440 2251799813685248 1 2251799813685248 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns222p47 Ns222p25 1 Ns222p48 7074237752028440 2251799813685248 1 2251799813685248 RS223to240.d16 rfl 

noncomputable def Ns222p49 := nat_lit 147443727375074537121690809726715087890625 

noncomputable def Ns222p50 := nat_lit 22889945643899497138335355216896171420000 

noncomputable def Ns222p51 := nat_lit 355592320898650075318906513310625 

noncomputable def Ns222p52 := BSN.log_dyadic_bound 3 5 17 16 Ns222p49 8388608 2890000 Ns222p50 Ns222p51 11629079 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 3) (BSN.artanhQ 5) 0 16 Ns222p50 Ns222p49 Ns222p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS223to240.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 11629079 8388608 1 2890000 := BSN.isNear_log_sfrac 4 1 11629079 8388608 1 2890000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 11629079 8388608 2890000 rfl rfl rfl (Ns222p52 rfl)) 

theorem RS223to240.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 186065264 134217728 47 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 11629079 8388608 1 2890000 186065264 134217728 47 134217728 RS223to240.d18 rfl 

noncomputable abbrev qz326 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz327 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns222p53 := @Enclosure.Real.IsNear.inv_image qz326 33554433 16777216 1 16777216 4194303 4194304 8388608 (@Enclosure.Real.IsNear.of_eq qz326 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz327 qz320)) Bool.false 33554433 16777216 1 16777216 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz327 qz320)) Bool.false 33554433 16777216 1 16777216 33554433 16777216 1 16777216 (BSN.sqrt_enclosure 4 1 16777216 16777217 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz328 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS223to240.d20 : Enclosure.Real.IsNear qz328 Bool.false 8388607 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz328 Bool.false 8388607 16777216 1 16777216 8388607 16777216 1 16777216 (Ns222p53 rfl rfl) rfl 

theorem RS223to240.d21 : Enclosure.Real.IsNear qz328 Bool.false 67108856 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz328 Bool.false 8388607 16777216 1 16777216 67108856 134217728 8 134217728 RS223to240.d20 rfl 

noncomputable def Ns222p54 := nat_lit 159424323765613091421820433543167414255940625 

noncomputable def Ns222p55 := nat_lit 33013339099500162583200499609923570567289500 

noncomputable def Ns222p56 := nat_lit 351657888879851162997374110924800000 

noncomputable def Ns222p57 := nat_lit 2289063575687431840984260 

noncomputable def Ns222p58 := nat_lit 3325435793429257756623375 

noncomputable def Ns222p59 := BSN.log_dyadic_bound 2 3 21 20 Ns222p54 8388608 2890000 Ns222p55 Ns222p56 13500943 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 20 10 9927050056596826020 47940881637414340575 686533194547200 Ns222p57 Ns222p58 512222703392784384000 Ns222p55 Ns222p54 Ns222p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 10 20 Ns222p57 Ns222p58 512222703392784384000 rfl rfl rfl rfl)) rfl rfl 

theorem RS223to240.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 13500943 8388608 1 2890000 := BSN.isNear_log_sfrac 5 1 13500943 8388608 1 2890000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 13500943 8388608 2890000 rfl rfl rfl (Ns222p59 rfl rfl)) 

theorem RS223to240.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 216015088 134217728 47 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 13500943 8388608 1 2890000 216015088 134217728 47 134217728 RS223to240.d22 rfl 

noncomputable abbrev qz329 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns222p60 := @Enclosure.Real.IsNear.inv_image qz329 37514995 16777216 1 16777216 3751499 3751500 8388608 (@Enclosure.Real.IsNear.of_eq qz329 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz325 qz320)) Bool.false 37514995 16777216 1 16777216 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz325 qz320)) Bool.false 37514995 16777216 1 16777216 37514995 16777216 1 16777216 (BSN.sqrt_enclosure 5 1 18757497 18757498 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz330 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS223to240.d24 : Enclosure.Real.IsNear qz330 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz330 Bool.false 7502999 16777216 1 16777216 7502999 16777216 1 16777216 (Ns222p60 rfl rfl) rfl 

theorem RS223to240.d25 : Enclosure.Real.IsNear qz330 Bool.false 60023992 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz330 Bool.false 7502999 16777216 1 16777216 60023992 134217728 8 134217728 RS223to240.d24 rfl 

noncomputable def Ns222p61 := BSN.log_dyadic_bound 2 10 5 4 94500000000 8388608 2890000 1291130880 26880 3401287 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz331 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz628)

theorem RS223to240.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683410914551 2251799813685248 50000000289 144500000000000000 := BSN.isNear_log_sfrac 6 1 4034683410914551 2251799813685248 50000000289 144500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz331) Bool.false 541526040612241437360128 302231454903657293676544 1000000005780000 2890000000000000000000 4034683410914551 2251799813685248 50000000289 144500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 3401287 8388608 24973259072661432 36028797018963968 2890000 1000000000000000 rfl rfl rfl rfl (Ns222p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS223to240.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 240485871 134217728 47 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683410914551 2251799813685248 50000000289 144500000000000000 240485871 134217728 47 134217728 RS223to240.d26 rfl 

noncomputable abbrev qz332 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns222p62 := @Enclosure.Real.IsNear.inv_image qz332 41095619 16777216 1 16777216 3424634 3424635 8388608 (@Enclosure.Real.IsNear.of_eq qz332 (Real.sqrt qz331) Bool.false 41095619 16777216 1 16777216 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz331) Bool.false 41095619 16777216 1 16777216 41095619 16777216 1 16777216 (BSN.sqrt_enclosure 6 1 20547809 20547810 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz333 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS223to240.d28 : Enclosure.Real.IsNear qz333 Bool.false 6849269 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz333 Bool.false 6849269 16777216 1 16777216 6849269 16777216 1 16777216 (Ns222p62 rfl rfl) rfl 

theorem RS223to240.d29 : Enclosure.Real.IsNear qz333 Bool.false 54794152 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz333 Bool.false 6849269 16777216 1 16777216 54794152 134217728 8 134217728 RS223to240.d28 rfl 

noncomputable def Ns222p63 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 8388608 2890000 11010900719820672 5524329195 4694397 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz334 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz628)

theorem RS223to240.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 50000000289 144500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 50000000289 144500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz334) Bool.false 588115238325433934020608 302231454903657293676544 1000000005780000 2890000000000000000000 4381799983422711 2251799813685248 50000000289 144500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 4694397 8388608 24973259072661432 36028797018963968 2890000 1000000000000000 rfl rfl rfl rfl (Ns222p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS223to240.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 261175631 134217728 47 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 50000000289 144500000000000000 261175631 134217728 47 134217728 RS223to240.d30 rfl 

noncomputable abbrev qz335 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns222p64 := @Enclosure.Real.IsNear.inv_image qz335 44388341 16777216 1 16777216 3170595 3170596 8388608 (@Enclosure.Real.IsNear.of_eq qz335 (Real.sqrt qz334) Bool.false 44388341 16777216 1 16777216 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz334) Bool.false 44388341 16777216 1 16777216 44388341 16777216 1 16777216 (BSN.sqrt_enclosure 7 1 22194170 22194171 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz336 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS223to240.d32 : Enclosure.Real.IsNear qz336 Bool.false 6341191 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz336 Bool.false 6341191 16777216 1 16777216 6341191 16777216 1 16777216 (Ns222p64 rfl rfl) rfl 

theorem RS223to240.d33 : Enclosure.Real.IsNear qz336 Bool.false 50729528 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz336 Bool.false 6341191 16777216 1 16777216 50729528 134217728 8 134217728 RS223to240.d32 rfl 

noncomputable def Ns222p65 := BSN.log_dyadic_bound 0 16 1 0 1 8388608 2890000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz847 := (Enclosure.sfrac Bool.false 8 1)

noncomputable abbrev qz629 := qz847

noncomputable abbrev qz337 := qz629

noncomputable abbrev qz338 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz628)

theorem RS223to240.d34 : Enclosure.Real.IsNear (Real.log qz337) Bool.false 9364972152248037 4503599627370496 100000000867 289000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 100000000867 289000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz338) Bool.false 628472642529000809299968 302231454903657293676544 1000000008670000 2890000000000000000000 9364972152248037 4503599627370496 100000000867 289000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 8388608 24973259072661432 36028797018963968 2890000 1000000000000000 rfl rfl rfl rfl (Ns222p65 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS223to240.d35 : Enclosure.Real.IsNear (Real.log qz337) Bool.false 279097919 134217728 47 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz337) Bool.false 9364972152248037 4503599627370496 100000000867 289000000000000000 279097919 134217728 47 134217728 RS223to240.d34 rfl 

noncomputable abbrev qz339 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns222p66 := @Enclosure.Real.IsNear.inv_image qz339 47453133 16777216 1 16777216 2965820 2965821 8388608 (@Enclosure.Real.IsNear.of_eq qz339 (Real.sqrt qz338) Bool.false 47453133 16777216 1 16777216 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz338) Bool.false 47453133 16777216 1 16777216 47453133 16777216 1 16777216 (BSN.sqrt_enclosure 8 1 23726566 23726567 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz340 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS223to240.d36 : Enclosure.Real.IsNear qz340 Bool.false 5931641 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz340 Bool.false 5931641 16777216 1 16777216 5931641 16777216 1 16777216 (Ns222p66 rfl rfl) rfl 

theorem RS223to240.d37 : Enclosure.Real.IsNear qz340 Bool.false 47453128 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz340 Bool.false 5931641 16777216 1 16777216 47453128 134217728 8 134217728 RS223to240.d36 rfl 

theorem RS223to240.d38 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz848 := (@instHMul Real Real.instMul)

noncomputable abbrev qz630 := qz848

noncomputable abbrev qz341 := (@HMul.hMul Real Real Real qz630 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz1 := qz341

theorem RS223to240.d39 : Enclosure.Real.IsNear qz1 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS223to240.d38 rfl 

noncomputable abbrev qz2 := (@Inv.inv Real Real.instInv qz341)

theorem RS223to240.d40 : Enclosure.Real.IsNear qz2 Bool.false 2670177 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz2 Bool.false 2670177 16777216 1 16777216 2670177 16777216 1 16777216 (@Enclosure.Real.IsNear.inv_image qz1 884279719003555 140737488355328 1 500000000000000 1335088 1335089 8388608 RS223to240.d39 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns222p67 := nat_lit 162802011267774066108399616 

noncomputable abbrev qz849 := (Enclosure.sfrac Bool.false 506327 1000)

noncomputable abbrev qz631 := qz849

noncomputable abbrev qz342 := qz631

noncomputable abbrev qz3 := qz342

noncomputable abbrev qz343 := qz630

noncomputable abbrev qz4 := qz343

noncomputable abbrev qz5 := (@Neg.neg Real Real.instNeg (1 : Real))

noncomputable abbrev qz6 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz850 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 506327 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz632 := qz850

noncomputable abbrev qz344 := qz632

noncomputable abbrev qz7 := qz344

noncomputable abbrev qz8 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz851 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 506327 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz633 := qz851

noncomputable abbrev qz345 := qz633

noncomputable abbrev qz9 := qz345

noncomputable abbrev qz346 := (@HMul.hMul Real Real Real qz4 (@HPow.hPow Real Nat Real RSCompact.c1 qz5 8) (@HPow.hPow Real Real Real qz6 qz7 qz8))

noncomputable def Ns222p68 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz3) qz3 8) (@HMul.hMul Real Real Real qz4 qz346 (Zeta.RiemannSiegel.correction qz9)) 3955891 16777216 22015 16777216 5354207897620386735 18446744073709551616 11231755199890820919 783986623132655943680000 Ns222p67 

noncomputable def Ns222p69 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz3) qz3 Real.cos BSN.quadSignPos 7 8 506327 1000 124 134217728 67108864 2251799813685248 Bool.false 115112615660 1760 279097919 47 47453128 8 

noncomputable def Ns222p70 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz3) qz3 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 506327 1000 31 81 134217728 67108864 2251799813685248 Bool.false 115112615660 1760 

noncomputable def Ns222p71 := Ns222p70 240485871 47 54794152 8 261175631 47 50729528 8 Bool.true 81774304 58901 Bool.true 116183807 Bool.true 50532212 7074237752028440 1 Bool.false 102207897 Bool.false Bool.false 49346838 Bool.true Bool.true 58699460 

noncomputable def Ns222p72 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz3) qz3 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 506327 1000 99 27 134217728 67108864 2251799813685248 Bool.false 115112615660 1760 

noncomputable def Ns222p73 := Ns222p72 186065264 47 67108856 8 216015088 47 60023992 8 Bool.true 117152098 34672 Bool.false 30706035 Bool.false 45968916 7074237752028440 1 Bool.false 30438879 Bool.false Bool.false 45075457 Bool.false Bool.true 81774304 

noncomputable def Ns222p74 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz3) qz3 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 506327 1000 322 191 134217728 67108864 2251799813685248 Bool.false 115112615660 1760 

noncomputable def Ns222p75 := Ns222p74 93032624 47 94906264 8 147453232 47 77490640 16 Bool.true 134217656 1815 Bool.false 120840297 Bool.false 184778661 7074237752028440 1 Bool.false 83396338 Bool.true Bool.false 131697652 Bool.false Bool.true 117152098 

noncomputable def Ns222p76 := nat_lit 468590092547059238353402804476883947583886440147736959051 

noncomputable def Ns222p77 := nat_lit 546361467195406468190818231331377231000071597509836800 

noncomputable def Ns222p78 := nat_lit 15973413876940310386767603395360000 

noncomputable def Ns222p79 := nat_lit 48526646451865793014130388567950656320 

noncomputable abbrev qz10 := (@Eq.refl Real qz342)

noncomputable def Ns222p80 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz3 506327 1000 1025469123716 16000000 1012654 4000 2000 Ns222p78 Ns222p79 qz10 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns222p81 := nat_lit 149948829615058956273088897432602863226843660847275826896320 

noncomputable abbrev qz852 := (@instHSub Real Real.instSub)

noncomputable abbrev qz634 := qz852

noncomputable abbrev qz347 := qz634

noncomputable abbrev qz11 := qz347

noncomputable abbrev qz348 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz349 := (@HMul.hMul Real Real Real qz630 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz350 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz351 := (Enclosure.sfrac Bool.false 506327 2000)

noncomputable abbrev qz635 := (Real.log (Enclosure.sfrac Bool.false 1025469123716 16000000))

noncomputable abbrev qz12 := (@HSub.hSub Real Real Real qz347 (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 506327 4000) qz635) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1012654)))))) qz351)

noncomputable abbrev qz352 := (@HSub.hSub Real Real Real qz11 qz12 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 506327 2000) (Real.log Real.pi)))

noncomputable def Ns222p82 := @Enclosure.Real.IsNear.addLit_ft_p qz352 (Enclosure.sfrac Bool.true Ns222p78 Ns222p79) 3090031933570431663251 3602879701896396800 1551457089218736783 118374400000000000000000 Ns222p78 Ns222p79 0 1 Ns222p81 

noncomputable def Ns222p83 := nat_lit 1036842663928175664552025784320000 

noncomputable abbrev qz353 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 506327 2000) (Real.log Real.pi))

noncomputable def Ns222p84 := @Enclosure.Real.IsNear.subLit_ff_p qz12 qz353 20670801235806418251487 18014398509481984000 1285817939014409 231200000000000000000 19448405384847 67108864000 506327 67108864000 Ns222p83 3090031933570431663251 3602879701896396800 

noncomputable def Ns222p85 := nat_lit 41341602471612836502974000 

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 506327 4000) qz635) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1012654))))))

noncomputable def Ns222p86 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz351 25231389412861660507871 18014398509481984000 1285817939014409 231200000000000000000 506327 2000 0 1 Ns222p85 20670801235806418251487 18014398509481984000 1285817939014409 231200000000000000000 

noncomputable def Ns222p87 := nat_lit 56816037978901826058878029967820587008 

noncomputable def Ns222p88 := nat_lit 26760956082080582075416576 

noncomputable def Ns222p89 := nat_lit 2417851639229258349412352 

noncomputable def Ns222p90 := nat_lit 934437123224526035470456511437275721540562306640045518933464085781430783583536066179541706163999952369210403196313049031533167782023322796140792358171861074760229393751500390400 

noncomputable def Ns222p91 := nat_lit 34785886561709561739035172156240954326474538538383075380206422909661269828281697690519553795946902059539165542067817078328540533921882511776479414893692216787194304430069514240 

noncomputable def Ns222p92 := nat_lit 8524986962802621414405516128462984507929464183035375023039988400371960456945116658743476068774902784610145989216564184622298278406065138081480803635156647225953993359360 

noncomputable def Ns222p93 := BSN.log_dyadic_bound 501181123716 1549757123716 8 7 Ns222p90 67108864 23120000 Ns222p91 Ns222p92 45020942 2050938247432 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 501181123716) (BSN.artanhQ 1549757123716) 0 7 Ns222p91 Ns222p90 Ns222p92 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz354 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns222p94 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 506327 4000) qz635 506327 4000 0 1 49846165035070073 4503599627370496 2500000867 57800000000000000 25238459203711924851871 18014398509481984000 1265817938985509 231200000000000000000 (Enclosure.Real.IsNear.const Bool.false 506327 4000) (BSN.isNear_log_sfrac 1025469123716 16000000 49846165035070073 4503599627370496 2500000867 57800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1025469123716) qz354)) Bool.false Ns222p88 Ns222p89 1000000346800000 23120000000000000000000 49846165035070073 4503599627370496 2500000867 57800000000000000 (BSN.log_rat_reduce_isNear 1025469123716 16000000 15 2050938247432 1048576000000 45020942 67108864 24973259072661432 36028797018963968 23120000 1000000000000000 rfl rfl rfl rfl (Ns222p93 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns222p95 := BSN.arctan_dyadic_bound_f 1000 1012654 1 0 8388608 2890000 0 1 1 0 1 1 8283 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1012654) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1012654) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz14 := qz349

noncomputable abbrev qz15 := qz350

noncomputable abbrev qz355 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz16 := (@Enclosure.Real.IsNear.mulLit_ff qz355 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz356 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1012654)))

noncomputable def Ns222p96 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz356 884279719003555 562949953421312 1 2000000000000000 8283 8388608 1 2890000 7413213010606784774144 883723856283043 562949953421312 200000000289 578000000000000000 qz16 (Ns222p95 rfl) rfl rfl 

noncomputable abbrev qz17 := qz348

noncomputable abbrev qz357 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns222p97 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 506327 4000) qz635) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz356)) 25238459203711924851871 18014398509481984000 1265817938985509 231200000000000000000 883723856283043 2251799813685248 200000000289 2312000000000000000 Ns222p87 25231389412861660507871 18014398509481984000 1285817939014409 231200000000000000000 (Ns222p94 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz356) 1 4 0 1 883723856283043 562949953421312 200000000289 578000000000000000 883723856283043 2251799813685248 200000000289 2312000000000000000 qz357 Ns222p96 rfl) 

noncomputable def Ns222p98 := @Ns222p82 Ns222p76 Ns222p77 1551457089218736783 118374400000000000000000 (@Ns222p84 1551457089218736783 118374400000000000000000 (Ns222p86 (Ns222p97 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 506327 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz351 (Real.log Real.pi) 506327 2000 0 1 38410761 33554432 1 33554432 19448405384847 67108864000 506327 67108864000 (Enclosure.Real.IsNear.const Bool.false 506327 2000) RS223to240.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns222p78 Ns222p79) 

noncomputable abbrev qz358 := (@instHAdd Real Real.instAdd)

noncomputable def Ns222p99 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz3) Bool.false Ns222p76 Ns222p77 1551457089218736783 118374400000000000000000 14389076957 16777216 221 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz3) (@HAdd.hAdd Real Real Real qz358 qz352 (Enclosure.sfrac Bool.true Ns222p78 Ns222p79)) Bool.false Ns222p76 Ns222p77 1551457089218736783 118374400000000000000000 Ns222p80 (Ns222p98 rfl rfl)) 

noncomputable def Ns222p100 := BSN.cos_dyadic_bound_f 35261259 34359738368 1 0 16777216 5785645 0 1 1 0 1 1 16777207 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 35261259) (BSN.cosEvenQ 34359738368) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 35261259) (BSN.cosOddQ 34359738368) 0 0 rfl) rfl rfl 

noncomputable abbrev qz359 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable abbrev qz360 := (@Nat.cast Real Real.instNatCast Ns222p89)

noncomputable def Ns222p101 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz3) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 14389076957) qz359) Bool.false 14389076957 16777216 221 16777216 Bool.true 16777207 16777216 1 2890000 (Ns222p99 rfl) (Enclosure.sfrac_false_div 14389076957 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 14389076957) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2481290578111573786624) qz360) 226375608064910080 72057594037927936 Bool.false 16777207 16777216 136 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q2 14389076957 16777216 226375608064910080 72057594037927936 136 2481290578111573786624 Ns222p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777207 16777216 2481290578111573786624 Ns222p89 35261259 34359738368 5785645 5780000 (Ns222p100 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p102 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz3) Bool.false Ns222p76 Ns222p77 1551457089218736783 118374400000000000000000 115112615660 134217728 1760 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz3) (@HAdd.hAdd Real Real Real qz358 qz352 (Enclosure.sfrac Bool.true Ns222p78 Ns222p79)) Bool.false Ns222p76 Ns222p77 1551457089218736783 118374400000000000000000 Ns222p80 (Ns222p98 rfl rfl)) 

noncomputable def Ns222p103 := Ns222p75 34672 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 322 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 83396338 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 191 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131697652 134217728) qz10 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz3) qz3 1) Bool.true 16777207 16777216 40966701 3030384640000 134217656 134217728 1815 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz3) qz3 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz3)) Bool.true 16777207 16777216 40966701 3030384640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz3) qz3) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz3)) Bool.true 16777207 16777216 655467216 48486154240000 16777207 16777216 40966701 3030384640000 (Ns222p101 rfl rfl) rfl)) rfl) (Ns222p102 rfl) RS223to240.d7 

noncomputable def Ns222p104 := nat_lit 116296266578577902522692031647419201318806644354572556239059988722241 

noncomputable def Ns222p105 := nat_lit 4246191600076225767660054876205591831097850246550140165773818614251520 

noncomputable def Ns222p106 := nat_lit 45466787737064897270424166660882415404276499508771679731647197761 

noncomputable def Ns222p107 := nat_lit 348797866160259577773535246608935839125611380064700125357716671771201 

noncomputable def Ns222p108 := nat_lit 191078622003430159544702469429251632399403261094756307459821837641318400 

noncomputable abbrev qz361 := (BSN.cosEvenQ 134217728)

noncomputable abbrev qz362 := (BSN.cosOddQ 134217728)

noncomputable def Ns222p109 := BSN.cos_dyadic_bound_f 120840297 134217728 3 2 134217728 67108864 Ns222p104 Ns222p105 Ns222p106 Ns222p107 Ns222p108 Ns222p106 83396338 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 120840297) qz361 0 2 Ns222p104 Ns222p105 Ns222p106 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 120840297) qz362 0 2 Ns222p107 Ns222p108 Ns222p106 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p110 := nat_lit 6378243626245924074403572932338245926352270146066255799748474449273856005879734084059188004696785247367121 

noncomputable def Ns222p111 := nat_lit 212813371219357667808056223692308629509040396751503069069405487845990478953701519077062806287447472524492800 

noncomputable def Ns222p112 := nat_lit 1584242967644667279822000797848674086614608600877383924943581042819989234478428785516220915892973521 

noncomputable def Ns222p113 := nat_lit 31867820321175871498842802267740301110986913772255265981509222223193556726045126084092724944126913067184081 

noncomputable def Ns222p114 := nat_lit 7448467992677518373281967829230802032816413886302607417429192074609666763379553167697198220060661538357248000 

noncomputable abbrev qz363 := (BSN.sinEvenQ 134217728)

noncomputable abbrev qz364 := (BSN.sinOddQ 134217728)

noncomputable def Ns222p115 := BSN.sin_dyadic_bound_f 184778661 134217728 4 3 134217728 67108864 Ns222p110 Ns222p111 Ns222p112 Ns222p113 Ns222p114 Ns222p112 131697652 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 184778661) qz363 0 3 Ns222p110 Ns222p111 Ns222p112 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 184778661) qz364 0 3 Ns222p113 Ns222p114 Ns222p112 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p116 := nat_lit 888986083540855125010680500625 

noncomputable def Ns222p117 := nat_lit 38942226439011207213978722469150720 

noncomputable def Ns222p118 := nat_lit 272595585073078450497851057284055040 

noncomputable def Ns222p119 := BSN.sin_dyadic_bound_f 30706035 134217728 2 1 134217728 67108864 Ns222p116 Ns222p117 Ns222p116 Ns222p116 Ns222p118 Ns222p116 30438879 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 30706035) qz363 0 1 Ns222p116 Ns222p117 Ns222p116 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 30706035) qz364 0 1 Ns222p116 Ns222p118 Ns222p116 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p120 := nat_lit 4465365892645060048204905083136 

noncomputable def Ns222p121 := BSN.sin_dyadic_bound_f 45968916 134217728 2 1 134217728 67108864 Ns222p120 Ns222p117 Ns222p120 Ns222p120 Ns222p118 Ns222p120 45075457 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 45968916) qz363 0 1 Ns222p120 Ns222p117 Ns222p120 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 45968916) qz364 0 1 Ns222p120 Ns222p118 Ns222p120 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p122 := Ns222p73 58901 BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 30438879 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 27 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 45075457 134217728) qz10 rfl rfl (Ns222p103 RS223to240.d9 RS223to240.d11 RS223to240.d13 RS223to240.d17 (Ns222p109 rfl rfl) (Ns222p115 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns222p102 rfl) RS223to240.d19 RS223to240.d21 RS223to240.d23 RS223to240.d25 RS223to240.d17 (Ns222p119 rfl rfl) (Ns222p121 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns222p123 := nat_lit 178848112774294296635092812126935902241241006481210465839756046854145 

noncomputable def Ns222p124 := nat_lit 38215724400686031908940493885850326479880652218951261491964367528263680 

noncomputable def Ns222p125 := nat_lit 33202044198037531293533812846338126366611635776896050360611072001 

noncomputable def Ns222p126 := nat_lit 468357968242069192326958310349747577474847169564293388355920085739521 

noncomputable def Ns222p127 := nat_lit 700621614012577251663909054573922652131145290680773127352680071351500800 

noncomputable def Ns222p128 := BSN.sin_dyadic_bound_f 116183807 134217728 3 2 134217728 67108864 Ns222p123 Ns222p124 Ns222p125 Ns222p126 Ns222p127 Ns222p125 102207897 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 116183807) qz363 0 2 Ns222p123 Ns222p124 Ns222p125 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 116183807) qz364 0 2 Ns222p126 Ns222p127 Ns222p125 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p129 := nat_lit 6520384974193104063351412347136 

noncomputable def Ns222p130 := BSN.sin_dyadic_bound_f 50532212 134217728 2 1 134217728 67108864 Ns222p129 Ns222p117 Ns222p129 Ns222p129 Ns222p118 Ns222p129 49346838 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 50532212) qz363 0 1 Ns222p129 Ns222p117 Ns222p129 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 50532212) qz364 0 1 Ns222p129 Ns222p118 Ns222p129 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p131 := Ns222p71 79014 BSN.abs_quadSignPos (BSN.cos_quad_nat3 31 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 102207897 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 81 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 49346838 134217728) qz10 rfl rfl (Ns222p122 rfl rfl) (Ns222p102 rfl) RS223to240.d27 RS223to240.d29 RS223to240.d31 RS223to240.d33 RS223to240.d17 (Ns222p128 rfl rfl) (Ns222p130 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p132 := nat_lit 6803804382585228381779060266206609176306502345565930044912238206241 

noncomputable def Ns222p133 := nat_lit 155734964679670501520709834812208882131913508104990467772521761 

noncomputable def Ns222p134 := nat_lit 20411101677826325804334139378950203111155243209681580153801169575201 

noncomputable def Ns222p135 := BSN.cos_dyadic_bound_f 59435821 134217728 3 2 134217728 67108864 Ns222p132 Ns222p105 Ns222p133 Ns222p134 Ns222p108 Ns222p133 121271360 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 59435821) qz361 0 2 Ns222p132 Ns222p105 Ns222p133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 59435821) qz362 0 2 Ns222p134 Ns222p108 Ns222p133 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p136 := Ns222p69 Bool.true 58699460 79014 Bool.true 59435821 7074237752028440 1 Bool.false 121271360 Bool.false Bool.true 15823564 88060 BSN.abs_quadSignPos (BSN.cos_quad_nat0 124 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 121271360 134217728) qz10 rfl (Ns222p131 rfl) (Ns222p102 rfl) RS223to240.d35 RS223to240.d37 RS223to240.d17 (Ns222p135 rfl rfl) rfl 

noncomputable def Ns222p137 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz3) qz3 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz3) qz3 8) 15823564 134217728 88060 134217728 15823564 134217728 88060 134217728 4247605617885184 3955891 16777216 22015 16777216 (Ns222p136 rfl rfl rfl rfl) 

noncomputable def Ns222p138 := @Enclosure.Real.IsNear.mulLit_ff qz346 (Zeta.RiemannSiegel.correction qz9) 5599601 16777216 1 16777216 956176680735 1099511627776 3997111827219 93458488360960000 5354207897620386735 18446744073709551616 

noncomputable abbrev qz365 := (@HPow.hPow Real Nat Real RSCompact.c1 qz5 8)

noncomputable def Ns222p139 := @Enclosure.Real.IsNear.mulLit_ff qz365 (@HPow.hPow Real Real Real qz6 qz7 qz8) 1 1 0 1 5599601 16777216 1 16777216 5599601 16777216 1 16777216 

noncomputable abbrev qz366 := (@Enclosure.Real.IsNear.of_eq qz7 (@HMul.hMul Real Real Real qz4 qz3 qz2) Bool.false 1351982709879 16777216000 506327 16777216000 (BSN.t_div_two_pi_mk qz3 506327 1000 qz10) (@Enclosure.Real.IsNear.mulLit_ff qz3 qz2 506327 1000 0 1 2670177 16777216 1 16777216 1351982709879 16777216000 506327 16777216000 (Enclosure.Real.IsNear.const Bool.false 506327 1000) RS223to240.d40 rfl))

noncomputable def Ns222p140 := @Enclosure.Real.IsNear.sqrt_image qz7 1351982709879 16777216000 506327 16777216000 75303548 75303577 8388608 qz366 

noncomputable abbrev qz853 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 506327 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz636 := qz853

noncomputable abbrev qz367 := qz636

noncomputable abbrev qz18 := qz367

noncomputable def Ns222p141 := @Enclosure.Real.IsNear.sqrt_image qz18 150607125 16777216 29 16777216 25133482 25133488 8388608 (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 150607125 16777216 29 16777216 150607125 16777216 29 16777216 (Ns222p140 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz637 := (Real.sqrt qz853)

noncomputable abbrev qz368 := qz637

noncomputable abbrev qz19 := qz368

noncomputable def Ns222p142 := @Enclosure.Real.IsNear.inv_image qz19 25133485 8388608 3 8388608 2799800 2799801 8388608 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 50266970 16777216 6 16777216 25133485 8388608 3 8388608 (Ns222p141 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns222p143 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz19) Bool.false 5599601 16777216 1 16777216 5599601 16777216 1 16777216 (Ns222p142 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz20 := (@HMul.hMul Real Real Real qz343 qz341 qz345)

noncomputable abbrev qz638 := (@HMul.hMul Real Real Real qz848 qz851 qz851)

noncomputable abbrev qz639 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz369 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz638 qz633) qz639)

noncomputable abbrev qz21 := (Real.cos (@HMul.hMul Real Real Real qz343 qz341 qz369))

noncomputable def Ns222p144 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz9) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz20)) qz21) Bool.false 956176680735 

noncomputable def Ns222p145 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz20)) qz21 8477871 8388608 97 

noncomputable def Ns222p146 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz20)) Bool.false 16955742 16777216 194 16777216 8477871 8388608 97 

noncomputable def Ns222p147 := @Enclosure.Real.IsNear.recentre' (Real.cos qz20) Bool.false 16600569 16777216 545647216 48486154240000 16600569 16777216 34102951 3030384640000 

noncomputable abbrev qz370 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable def Ns222p148 := @Enclosure.Real.IsNear.cos_image qz20 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51488809) qz370) Bool.false 51488809 8388608 183 16777216 Bool.false 16600569 16777216 1 

noncomputable def Ns222p149 := nat_lit 782596187003061166432221067 

noncomputable def Ns222p150 := nat_lit 72057594037927936000000000000000 

noncomputable def Ns222p151 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz9 884279719003555 140737488355328 1 500000000000000 16389397 16777216 29 16777216 14492811373797707306335 2361183241434822606848 Ns222p149 

noncomputable def Ns222p152 := @Enclosure.Real.IsNear.subLit_ff_p qz18 qz337 150607125 16777216 29 16777216 8 1 0 1 16389397 16389397 16777216 29 

noncomputable def Ns222p153 := @Ns222p152 16777216 (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 150607125 16777216 29 16777216 150607125 16777216 29 16777216 (Ns222p140 rfl rfl rfl rfl rfl rfl) rfl) (Enclosure.Real.IsNear.const Bool.false 8 1) 

noncomputable def Ns222p154 := @Enclosure.Real.IsNear.recentre' qz20 Bool.false 14492811373797707306335 2361183241434822606848 Ns222p149 Ns222p150 51488809 8388608 183 16777216 (@Ns222p151 Ns222p150 RS223to240.d39 (Ns222p153 rfl rfl) rfl) 

noncomputable def Ns222p155 := nat_lit 1723390682382312855830528 

noncomputable def Ns222p156 := nat_lit 1208925819614629174706176 

noncomputable def Ns222p157 := nat_lit 24294593280143905188661122197276824999554780116713253167332017728329837423290130959489985 

noncomputable def Ns222p158 := nat_lit 704955687610872565255254336748118540842396593755240389471857687246053587015266059818106880 

noncomputable def Ns222p159 := nat_lit 33133818239083508736131824502530726067426527880903317351900100126309860960547374685121 

noncomputable def Ns222p160 := nat_lit 63575051456561235527587297086530444299486685927203724353014112935897453476585647239650241 

noncomputable def Ns222p161 := nat_lit 12924187606199330363012996173715506582110604218846073806984057599510982428613211096665292800 

noncomputable abbrev qz371 := (BSN.sinEvenQ 34359738368)

noncomputable abbrev qz372 := (BSN.sinOddQ 34359738368)

noncomputable def Ns222p162 := BSN.sin_dyadic_bound_f 48981709209 34359738368 3 2 16777216 5785645 Ns222p157 Ns222p158 Ns222p159 Ns222p160 Ns222p161 Ns222p159 16600569 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 48981709209) qz371 0 2 Ns222p157 Ns222p158 Ns222p159 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 48981709209) qz372 0 2 Ns222p160 Ns222p161 Ns222p159 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz640 := (@Nat.cast Real Real.instNatCast Ns222p156)

noncomputable def Ns222p163 := @Ns222p148 2890000 (Ns222p154 rfl) (Enclosure.sfrac_false_div 51488809 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51488809) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns222p155) qz640) 226375608064910080 72057594037927936 Bool.false 16600569 16777216 0 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q3 51488809 8388608 226375608064910080 72057594037927936 0 Ns222p155 Ns222p156 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16600569 16777216 Ns222p155 Ns222p156 48981709209 34359738368 5785645 5780000 (Ns222p162 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p164 := @Enclosure.Real.IsNear.inv_image (Real.cos qz20) 16600569 16777216 34102951 3030384640000 8477774 8477968 8388608 (Ns222p147 (Ns222p163 rfl rfl) rfl) rfl 

noncomputable def Ns222p165 := @Enclosure.Real.IsNear.recentre' qz21 Bool.false 7218240 8388608 

noncomputable abbrev qz22 := (@HMul.hMul Real Real Real qz343 qz341 qz369)

noncomputable abbrev qz373 := (@Nat.cast Real Real.instNatCast 2097152)

noncomputable def Ns222p166 := @Enclosure.Real.IsNear.cos_image qz22 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1121101)) qz373) Bool.true 1121101 2097152 

noncomputable def Ns222p167 := nat_lit 21177000946189295270327432245 

noncomputable def Ns222p168 := nat_lit 39614081257132168796771975168 

noncomputable def Ns222p169 := nat_lit 7756473431520803357643819096210921 

noncomputable def Ns222p170 := @Enclosure.Real.IsNear.recentre' qz22 Bool.true Ns222p167 Ns222p168 Ns222p169 

noncomputable def Ns222p171 := nat_lit 241785163922925834941235200000000000000 

noncomputable abbrev qz23 := qz369

noncomputable def Ns222p172 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz23 884279719003555 140737488355328 1 500000000000000 23948305599559 

noncomputable abbrev qz374 := (@HSub.hSub Real Real Real qz634 qz638 qz633)

noncomputable abbrev qz24 := qz374

noncomputable abbrev qz375 := qz639

noncomputable abbrev qz25 := qz375

noncomputable def Ns222p173 := @Enclosure.Real.IsNear.subLit_tf qz24 qz25 6356119555143 281474976710656 1437125131 281474976710656 1 16 

noncomputable abbrev qz376 := qz638

noncomputable abbrev qz26 := qz376

noncomputable def Ns222p174 := @Enclosure.Real.IsNear.subLit_ff_n qz26 qz9 268612334023609 281474976710656 950585867 281474976710656 16389397 16777216 29 16777216 

noncomputable def Ns222p175 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz9 16389397 16777216 29 16777216 16389397 16777216 29 16777216 268612334023609 281474976710656 

noncomputable def Ns222p176 := nat_lit 51336823042271359365223222202765327594816507091931681 

noncomputable def Ns222p177 := nat_lit 15085502980398593449464978548510856026246963233994833920 

noncomputable def Ns222p178 := nat_lit 2495501984765014970869947528733883684707370848801 

noncomputable def Ns222p179 := nat_lit 154005478122844548065727926713238515017080106534097441 

noncomputable def Ns222p180 := nat_lit 678847634117936705225924034682988521181113345529767526400 

noncomputable def Ns222p181 := BSN.cos_dyadic_bound_f 1121101 2097152 3 2 8388608 2890000 Ns222p176 Ns222p177 Ns222p178 Ns222p179 Ns222p180 Ns222p178 7218240 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1121101) (BSN.cosEvenQ 2097152) 0 2 Ns222p176 Ns222p177 Ns222p178 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1121101) (BSN.cosOddQ 2097152) 0 2 Ns222p179 Ns222p180 Ns222p178 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz377 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns222p182 := @Ns222p165 1574487216 48486154240000 112785 131072 98405451 3030384640000 (@Ns222p166 539 16777216 Bool.false 7218240 8388608 1 2890000 (@Ns222p170 Ns222p171 1121101 2097152 539 16777216 (@Ns222p172 281474976710656 1437125131 281474976710656 Ns222p167 Ns222p168 Ns222p169 Ns222p171 RS223to240.d39 (@Ns222p173 0 1 383172889592944 23948305599559 281474976710656 1437125131 281474976710656 (@Ns222p174 106637990698458021888 6356119555143 281474976710656 1437125131 281474976710656 (@Ns222p175 950585867 281474976710656 (Ns222p153 rfl rfl) (Ns222p153 rfl rfl) rfl) (Ns222p153 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 1121101 2097152) (BSN.cos_neg_of_bound 1121101 2097152 Bool.false 7218240 8388608 1 2890000 (Ns222p181 rfl rfl)) rfl rfl) 

noncomputable def Ns222p183 := @Ns222p138 11231755199890820919 783986623132655943680000 (Ns222p139 (@Enclosure.Real.IsNear.of_eq qz365 (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 8 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1)) (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Real Real qz6 qz7 qz8) (@Inv.inv Real Real.instInv qz19) Bool.false 5599601 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz7 (BSN.t_div_two_pi_nonneg qz3 506327 1000 qz10)) Ns222p143) rfl) (@Ns222p144 1099511627776 3997111827219 93458488360960000 (BSN.correction_mk qz9 (BSN.cos_two_pi_p_ne_zero_mk qz3 506327 1000 8 qz10 rfl rfl (@BSN.floor_sqrt_eq_dec qz3 506327 1000 8 qz10 rfl rfl rfl))) (@Ns222p145 8388608 112785 131072 98405451 3030384640000 956176680735 1099511627776 3997111827219 93458488360960000 (@Ns222p146 8388608 (Ns222p164 rfl rfl rfl rfl rfl) rfl) (Ns222p182 rfl) rfl)) 

noncomputable def Ns222p184 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz3) (hardyZApproximantRS₀ qz3) Bool.true 9703756050334815151 18446744073709551616 1039976065833158020919 783986623132655943680000 (@Eq.refl Real (hardyZApproximantRS₀ qz3)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz3) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz3) qz3 8) (@HMul.hMul Real Real Real qz4 qz346 (Zeta.RiemannSiegel.correction qz9))) Bool.true 9703756050334815151 18446744073709551616 1039976065833158020919 783986623132655943680000 (BSN.hardyZApproximantRS₀_eq qz3 8 (@BSN.floor_sqrt_eq_dec qz3 506327 1000 8 qz10 rfl rfl rfl)) (@Ns222p68 9703756050334815151 18446744073709551616 1039976065833158020919 783986623132655943680000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz3) qz3 8) (@HAdd.hAdd Real Real Real qz358 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz3) qz3 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz3) qz3 8)) Bool.true 3955891 16777216 22015 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz3) qz3 8) (Ns222p137 (Ns222p136 rfl rfl rfl rfl) rfl rfl)) (Ns222p183 rfl) rfl rfl)) 

theorem RS223to240.d41 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz3) Bool.true 9703756050334815151 18446744073709551616 1039976065833158020919 783986623132655943680000 := Ns222p184 

theorem RS223to240.d42 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS223to240.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS223to240.d3 a b h)) 

noncomputable def Ns222p185 := nat_lit 21324436149208241668096000 

noncomputable def Ns222p186 := nat_lit 239286324216272651947517935616 

noncomputable abbrev qz854 := (Enclosure.sfrac Bool.false 507758 1000)

noncomputable abbrev qz641 := qz854

noncomputable abbrev qz378 := qz641

noncomputable abbrev qz27 := qz378

noncomputable abbrev qz855 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 507758 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz642 := qz855

noncomputable abbrev qz379 := qz642

noncomputable abbrev qz28 := qz379

noncomputable abbrev qz856 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 507758 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz643 := qz856

noncomputable abbrev qz380 := qz643

noncomputable abbrev qz29 := qz380

noncomputable abbrev qz381 := (@HMul.hMul Real Real Real qz4 (@HPow.hPow Real Nat Real RSCompact.c1 qz5 8) (@HPow.hPow Real Real Real qz6 qz28 qz8))

noncomputable def Ns222p187 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz27) qz27 8) (@HMul.hMul Real Real Real qz4 qz381 (Zeta.RiemannSiegel.correction qz29)) 425489787 67108864 11039 8388608 177003657821497461127 590295810358705651712 318434302159234812457 Ns222p185 Ns222p186 

noncomputable def Ns222p188 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz27) qz27 Real.cos BSN.quadSignPos 7 8 507758 1000 124 134217728 67108864 2251799813685248 Bool.false 115534268293 1765 279097919 47 47453128 8 

noncomputable def Ns222p189 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz27) qz27 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 507758 1000 31 81 134217728 67108864 2251799813685248 Bool.false 115534268293 1765 

noncomputable def Ns222p190 := Ns222p189 240485871 47 54794152 8 261175631 47 50729528 8 Bool.false 365267844 59070 Bool.true 38666456 Bool.true 2621907 7074237752028440 1 Bool.false 38133820 Bool.false Bool.false 2621740 Bool.true Bool.false 379844984 

noncomputable def Ns222p191 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz27) qz27 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 507758 1000 99 27 134217728 67108864 2251799813685248 Bool.false 115534268293 1765 

noncomputable def Ns222p192 := Ns222p191 186065264 47 67108856 8 216015088 47 60023992 8 Bool.false 243774701 34773 Bool.false 186099275 Bool.false 158503958 7074237752028440 1 Bool.false 131945982 Bool.false Bool.false 124146854 Bool.false Bool.false 365267844 

noncomputable def Ns222p193 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz27) qz27 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 507758 1000 323 192 134217728 67108864 2251799813685248 Bool.false 115534268293 1765 

noncomputable def Ns222p194 := Ns222p193 93032624 47 94906264 8 147453232 47 77490640 16 Bool.false 134217656 1823 Bool.false 198534530 Bool.false 184597005 7074237752028440 1 Bool.false 133655055 Bool.false Bool.false 26065030 Bool.false Bool.false 243774701 

noncomputable def Ns222p195 := nat_lit 3737017641052268030316584917332058153933225018206784559 

noncomputable def Ns222p196 := nat_lit 4341344128339687868186135112816690625841408350617600 

noncomputable def Ns222p197 := nat_lit 16200416408034398960558649328640000 

noncomputable def Ns222p198 := nat_lit 49355368541224468892620906363125534720 

noncomputable abbrev qz382 := (@Eq.refl Real qz641)

noncomputable abbrev qz30 := qz382

noncomputable def Ns222p199 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz27 507758 1000 1031273746256 16000000 1015516 4000 2000 Ns222p197 Ns222p198 qz30 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns222p200 := nat_lit 76534121288750449260883659106960550992552448372874947768320 

noncomputable abbrev qz383 := (Enclosure.sfrac Bool.false 507758 2000)

noncomputable abbrev qz644 := (Real.log (Enclosure.sfrac Bool.false 1031273746256 16000000))

noncomputable abbrev qz31 := (@HSub.hSub Real Real Real qz347 (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 507758 4000) qz644) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1015516)))))) qz383)

noncomputable abbrev qz384 := (@HSub.hSub Real Real Real qz11 qz31 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 507758 2000) (Real.log Real.pi)))

noncomputable def Ns222p201 := @Enclosure.Real.IsNear.addLit_ft_p qz384 (Enclosure.sfrac Bool.true Ns222p197 Ns222p198) 1550675290954425826131 1801439850948198400 777906466836161391 59187200000000000000000 Ns222p197 Ns222p198 0 1 Ns222p200 

noncomputable def Ns222p202 := nat_lit 260160143022052482409782312960000 

noncomputable abbrev qz385 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 507758 2000) (Real.log Real.pi))

noncomputable def Ns222p203 := @Enclosure.Real.IsNear.subLit_ff_p qz31 qz385 10371074623407535810719 9007199254740992000 644697720127543 115600000000000000000 9751685591919 33554432000 253879 33554432000 Ns222p202 1550675290954425826131 1801439850948198400 

noncomputable def Ns222p204 := nat_lit 20742149246815071621438000 

noncomputable abbrev qz32 := (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 507758 4000) qz644) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1015516))))))

noncomputable def Ns222p205 := @Enclosure.Real.IsNear.subLit_ff_p qz32 qz383 12657813363001924118687 9007199254740992000 644697720127543 115600000000000000000 507758 2000 0 1 Ns222p204 10371074623407535810719 9007199254740992000 644697720127543 115600000000000000000 

noncomputable def Ns222p206 := nat_lit 28502861772470375140469918904013029376 

noncomputable def Ns222p207 := nat_lit 26774603610247380531675136 

noncomputable def Ns222p208 := nat_lit 984647243882903923414840127062365296171701332245003188908915643523957518191046201154471175653120478864916181772258554950487490061965224342269692738096075034192853007035950694400 

noncomputable def Ns222p209 := nat_lit 37269786720607917156403396849916884343523526326786443422423474333581876974507018258725775552424284228532834548712340547427976280498059725135493354606044119123312632459312496640 

noncomputable def Ns222p210 := nat_lit 10016323400635389798338969807097456628214331483539248689079768442932861439680964890929783193275458766598271019272393665567115130765242762657904566040830174653664156712960 

noncomputable def Ns222p211 := BSN.log_dyadic_bound 506985746256 1555561746256 8 7 Ns222p208 67108864 23120000 Ns222p209 Ns222p210 45399737 2062547492512 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 506985746256) (BSN.artanhQ 1555561746256) 0 7 Ns222p209 Ns222p208 Ns222p210 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns222p212 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 507758 4000) qz644 507758 4000 0 1 49871585537208953 4503599627370496 2500000867 57800000000000000 12661348264601071778687 9007199254740992000 634697720113093 115600000000000000000 (Enclosure.Real.IsNear.const Bool.false 507758 4000) (BSN.isNear_log_sfrac 1031273746256 16000000 49871585537208953 4503599627370496 2500000867 57800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1031273746256) qz354)) Bool.false Ns222p207 Ns222p89 1000000346800000 23120000000000000000000 49871585537208953 4503599627370496 2500000867 57800000000000000 (BSN.log_rat_reduce_isNear 1031273746256 16000000 15 2062547492512 1048576000000 45399737 67108864 24973259072661432 36028797018963968 23120000 1000000000000000 rfl rfl rfl rfl (Ns222p211 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns222p213 := BSN.arctan_dyadic_bound_f 1000 1015516 1 0 8388608 2890000 0 1 1 0 1 1 8260 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1015516) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1015516) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz386 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1015516)))

noncomputable def Ns222p214 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz386 884279719003555 562949953421312 1 2000000000000000 8260 8388608 1 2890000 7413225958455713464320 883725399786915 562949953421312 200000000289 578000000000000000 qz16 (Ns222p213 rfl) rfl rfl 

noncomputable def Ns222p215 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 507758 4000) qz644) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz386)) 12661348264601071778687 9007199254740992000 634697720113093 115600000000000000000 883725399786915 2251799813685248 200000000289 2312000000000000000 Ns222p206 12657813363001924118687 9007199254740992000 644697720127543 115600000000000000000 (Ns222p212 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz386) 1 4 0 1 883725399786915 562949953421312 200000000289 578000000000000000 883725399786915 2251799813685248 200000000289 2312000000000000000 qz357 Ns222p214 rfl) 

noncomputable def Ns222p216 := @Ns222p201 Ns222p195 Ns222p196 777906466836161391 59187200000000000000000 (@Ns222p203 777906466836161391 59187200000000000000000 (Ns222p205 (Ns222p215 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 507758 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz383 (Real.log Real.pi) 507758 2000 0 1 38410761 33554432 1 33554432 9751685591919 33554432000 253879 33554432000 (Enclosure.Real.IsNear.const Bool.false 507758 2000) RS223to240.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns222p197 Ns222p198) 

noncomputable def Ns222p217 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz27) Bool.false Ns222p195 Ns222p196 777906466836161391 59187200000000000000000 902611471 1048576 111 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz27) (@HAdd.hAdd Real Real Real qz358 qz384 (Enclosure.sfrac Bool.true Ns222p197 Ns222p198)) Bool.false Ns222p195 Ns222p196 777906466836161391 59187200000000000000000 Ns222p199 (Ns222p216 rfl rfl)) 

noncomputable def Ns222p218 := BSN.cos_dyadic_bound_f 34033415 34359738368 1 0 16777216 5785645 0 1 1 0 1 1 16777207 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 34033415) (BSN.cosEvenQ 34359738368) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 34033415) (BSN.cosOddQ 34359738368) 0 0 rfl) rfl rfl 

noncomputable abbrev qz645 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable def Ns222p219 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz27) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 902611471) qz645) Bool.false 902611471 1048576 111 8388608 Bool.false 16777207 16777216 1 2890000 (Ns222p217 rfl) (Enclosure.sfrac_false_div 902611471 1048576) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 902611471) qz645) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 149680545336888655872) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false 16777207 16777216 137 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q0 902611471 1048576 226375608064910080 72057594037927936 137 149680545336888655872 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777207 16777216 149680545336888655872 151115727451828646838272 34033415 34359738368 5785645 5780000 (Ns222p218 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p220 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz27) Bool.false Ns222p195 Ns222p196 777906466836161391 59187200000000000000000 115534268293 134217728 1765 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz27) (@HAdd.hAdd Real Real Real qz358 qz384 (Enclosure.sfrac Bool.true Ns222p197 Ns222p198)) Bool.false Ns222p195 Ns222p196 777906466836161391 59187200000000000000000 Ns222p199 (Ns222p216 rfl rfl)) 

noncomputable def Ns222p221 := Ns222p194 34773 BSN.abs_quadSignPos (BSN.cos_quad_nat3 323 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133655055 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 192 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 26065030 134217728) qz30 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz27) qz27 1) Bool.false 16777207 16777216 20573663 1515192320000 134217656 134217728 1823 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz27) qz27 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz27)) Bool.false 16777207 16777216 20573663 1515192320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz27) qz27) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz27)) Bool.false 16777207 16777216 329178608 24243077120000 16777207 16777216 20573663 1515192320000 (Ns222p219 rfl rfl) rfl)) rfl) (Ns222p220 rfl) RS223to240.d7 

noncomputable def Ns222p222 := nat_lit 8503731605170594604271681197114135607726456208550265183080283457542486772923285917158799667450672294400000 

noncomputable def Ns222p223 := nat_lit 3750011719085165429593145875115383491088703609669676365867768002935386932766033773752241000000000000 

noncomputable def Ns222p224 := nat_lit 42477096810854281796097711400212171590639944755048438590295605547769566199099861556605849255113297472000000 

noncomputable def Ns222p225 := BSN.sin_dyadic_bound_f 198534530 134217728 4 3 134217728 67108864 Ns222p222 Ns222p111 Ns222p223 Ns222p224 Ns222p114 Ns222p223 133655055 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 198534530) qz363 0 3 Ns222p222 Ns222p111 Ns222p223 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 198534530) qz364 0 3 Ns222p224 Ns222p114 Ns222p223 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p226 := nat_lit 2445837875047826278180103411480261239550190747496032587177513102049073744386940733968425830087164645640625 

noncomputable def Ns222p227 := nat_lit 16370259324565974446773555668639125346849261288577159159185037526614652227207809159774062022111344040345600 

noncomputable def Ns222p228 := nat_lit 1565654051836462889508512023785542339257775259556366496543629281228481093871131629707713086181640625 

noncomputable def Ns222p229 := nat_lit 14817051335588537489582197840690273756781665508751837021619200577945825005695301513058248552116264063240625 

noncomputable def Ns222p230 := nat_lit 1489693598535503674656393565846160406563282777260521483485838414921933352675910633539439644012132307671449600 

noncomputable def Ns222p231 := BSN.cos_dyadic_bound_f 184597005 134217728 4 3 134217728 67108864 Ns222p226 Ns222p227 Ns222p228 Ns222p229 Ns222p230 Ns222p228 26065030 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 184597005) qz361 0 3 Ns222p226 Ns222p227 Ns222p228 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 184597005) qz362 0 3 Ns222p229 Ns222p230 Ns222p228 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p232 := nat_lit 6562774197300283165245638641309140722896011727919922422696062197931600142733917033778819355281802369140625 

noncomputable def Ns222p233 := nat_lit 1725584275879360165494667479394108041321232200074117148062723296461001763051066222250461578369140625 

noncomputable def Ns222p234 := nat_lit 32789101241579790790862310147566039219343570660409547919096234174887399150920226092373105374562698369140625 

noncomputable def Ns222p235 := BSN.sin_dyadic_bound_f 186099275 134217728 4 3 134217728 67108864 Ns222p232 Ns222p111 Ns222p233 Ns222p234 Ns222p114 Ns222p233 131945982 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 186099275) qz363 0 3 Ns222p232 Ns222p111 Ns222p233 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 186099275) qz364 0 3 Ns222p234 Ns222p114 Ns222p233 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p236 := nat_lit 619813467246279067999005528150406144213777513686285682743571395600640 

noncomputable def Ns222p237 := nat_lit 398401432766079230963861201036775278198490257313538403574836060416 

noncomputable def Ns222p238 := nat_lit 1622675954753871526004406322258908932014238789714145345008327730094336 

noncomputable def Ns222p239 := BSN.sin_dyadic_bound_f 158503958 134217728 3 2 134217728 67108864 Ns222p236 Ns222p124 Ns222p237 Ns222p238 Ns222p127 Ns222p237 124146854 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 158503958) qz363 0 2 Ns222p236 Ns222p124 Ns222p237 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 158503958) qz364 0 2 Ns222p238 Ns222p127 Ns222p237 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p240 := Ns222p192 59070 BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131945982 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 27 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 124146854 134217728) qz30 rfl rfl (Ns222p221 RS223to240.d9 RS223to240.d11 RS223to240.d13 RS223to240.d17 (Ns222p225 rfl rfl) (Ns222p231 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns222p220 rfl) RS223to240.d19 RS223to240.d21 RS223to240.d23 RS223to240.d25 RS223to240.d17 (Ns222p235 rfl rfl) (Ns222p239 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns222p241 := nat_lit 2235308519594565172023091204096 

noncomputable def Ns222p242 := BSN.sin_dyadic_bound_f 38666456 134217728 2 1 134217728 67108864 Ns222p241 Ns222p117 Ns222p241 Ns222p241 Ns222p118 Ns222p241 38133820 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 38666456) qz363 0 1 Ns222p241 Ns222p117 Ns222p241 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 38666456) qz364 0 1 Ns222p241 Ns222p118 Ns222p241 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p243 := BSN.sin_dyadic_bound_f 2621907 134217728 1 0 134217728 67108864 0 1 1 0 1 1 2621740 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 2621907) qz363 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 2621907) qz364 0 0 rfl) rfl rfl 

noncomputable def Ns222p244 := Ns222p190 79240 BSN.abs_quadSignPos (BSN.cos_quad_nat3 31 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 38133820 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 81 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 2621740 134217728) qz30 rfl rfl (Ns222p240 rfl rfl) (Ns222p220 rfl) RS223to240.d27 RS223to240.d29 RS223to240.d31 RS223to240.d33 RS223to240.d17 (Ns222p242 rfl rfl) (Ns222p243 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p245 := nat_lit 1909317711477454344027843210000 

noncomputable def Ns222p246 := nat_lit 7788445287802241442795744493830144 

noncomputable def Ns222p247 := nat_lit 116826679317033621641936167407452160 

noncomputable def Ns222p248 := BSN.cos_dyadic_bound_f 37172310 134217728 2 1 134217728 67108864 Ns222p245 Ns222p246 Ns222p245 Ns222p245 Ns222p247 Ns222p245 129103013 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 37172310) qz361 0 1 Ns222p245 Ns222p246 Ns222p245 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 37172310) qz362 0 1 Ns222p245 Ns222p247 Ns222p245 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p249 := Ns222p188 Bool.false 379844984 79240 Bool.true 37172310 7074237752028440 1 Bool.false 129103013 Bool.false Bool.false 425489787 88312 BSN.abs_quadSignPos (BSN.cos_quad_nat0 124 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 129103013 134217728) qz30 rfl (Ns222p244 rfl) (Ns222p220 rfl) RS223to240.d35 RS223to240.d37 RS223to240.d17 (Ns222p248 rfl rfl) rfl 

noncomputable def Ns222p250 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz27) qz27 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz27) qz27 8) 425489787 134217728 88312 134217728 425489787 134217728 88312 134217728 114216544996687872 425489787 67108864 11039 8388608 (Ns222p249 rfl rfl rfl rfl) 

noncomputable def Ns222p251 := @Enclosure.Real.IsNear.mulLit_ff qz381 (Zeta.RiemannSiegel.correction qz29) 1398913 4194304 1 8388608 126529425219079 140737488355328 225996006483757 5084141766836224000 177003657821497461127 590295810358705651712 

noncomputable def Ns222p252 := @Enclosure.Real.IsNear.mulLit_ff qz365 (@HPow.hPow Real Real Real qz6 qz28 qz8) 1 1 0 1 1398913 4194304 1 8388608 1398913 4194304 1 8388608 

noncomputable def Ns222p253 := @Enclosure.Real.IsNear.sqrt_image qz28 677901866583 8388608000 253879 8388608000 75409885 75409915 8388608 (@Enclosure.Real.IsNear.of_eq qz28 (@HMul.hMul Real Real Real qz4 qz27 qz2) Bool.false 677901866583 8388608000 253879 8388608000 (BSN.t_div_two_pi_mk qz27 507758 1000 qz30) (@Enclosure.Real.IsNear.mulLit_ff qz27 qz2 507758 1000 0 1 2670177 16777216 1 16777216 677901866583 8388608000 253879 8388608000 (Enclosure.Real.IsNear.const Bool.false 507758 1000) RS223to240.d40 rfl)) 

noncomputable abbrev qz857 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 507758 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz646 := qz857

noncomputable abbrev qz387 := qz646

noncomputable abbrev qz33 := qz387

noncomputable def Ns222p254 := @Enclosure.Real.IsNear.sqrt_image qz33 18852475 2097152 15 8388608 25151221 25151227 8388608 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 150819800 16777216 30 16777216 18852475 2097152 15 8388608 (Ns222p253 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns222p255 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz33) 3143903 1048576 3 8388608 2797825 2797827 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz33) Bool.false 50302448 16777216 6 16777216 3143903 1048576 3 8388608 (Ns222p254 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns222p256 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz33)) Bool.false 5595652 16777216 2 16777216 1398913 4194304 1 8388608 (Ns222p255 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz343 qz341 qz380)

noncomputable abbrev qz647 := (@HMul.hMul Real Real Real qz848 qz856 qz856)

noncomputable abbrev qz388 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz647 qz643) qz639)

noncomputable abbrev qz35 := (Real.cos (@HMul.hMul Real Real Real qz343 qz341 qz388))

noncomputable def Ns222p257 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz29) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz34)) qz35) Bool.false 126529425219079 

noncomputable def Ns222p258 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz34)) qz35 16813373 16777216 197 

noncomputable def Ns222p259 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz34)) Bool.false 16813373 16777216 197 16777216 16813373 16777216 197 

noncomputable def Ns222p260 := @Enclosure.Real.IsNear.recentre' (Real.cos qz34) Bool.false 16741137 16777216 282938608 24243077120000 16741137 16777216 17683663 1515192320000 

noncomputable def Ns222p261 := @Enclosure.Real.IsNear.cos_image qz34 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 52156947) qz370) Bool.false 52156947 8388608 95 8388608 Bool.false 16741137 16777216 1 

noncomputable def Ns222p262 := nat_lit 404791131206966038113371817 

noncomputable def Ns222p263 := nat_lit 36028797018963968000000000000000 

noncomputable def Ns222p264 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz29 884279719003555 140737488355328 1 500000000000000 2075259 2097152 15 8388608 1835109445379598545745 295147905179352825856 Ns222p262 

noncomputable def Ns222p265 := @Enclosure.Real.IsNear.subLit_ff_p qz33 qz337 18852475 2097152 15 8388608 8 1 0 1 2075259 2075259 2097152 15 

noncomputable def Ns222p266 := @Ns222p265 8388608 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 150819800 16777216 30 16777216 18852475 2097152 15 8388608 (Ns222p253 rfl rfl rfl rfl rfl rfl) rfl) (Enclosure.Real.IsNear.const Bool.false 8 1) 

noncomputable def Ns222p267 := @Enclosure.Real.IsNear.recentre' qz34 Bool.false 1835109445379598545745 295147905179352825856 Ns222p262 Ns222p263 52156947 8388608 95 8388608 (@Ns222p264 Ns222p263 RS223to240.d39 (Ns222p266 rfl rfl) rfl) 

noncomputable def Ns222p268 := nat_lit 1819679515912939046436864 

noncomputable def Ns222p269 := nat_lit 30206343535681740241062261777475974028801145422828658467230876213767199626380047300287425 

noncomputable def Ns222p270 := nat_lit 51187133675500322870352080279189752963107424359329780325754869352067245587733402737601 

noncomputable def Ns222p271 := nat_lit 79028977710358509632420591763413624761110349801302809674601072676153604433377126943939521 

noncomputable def Ns222p272 := BSN.sin_dyadic_bound_f 51718402457 34359738368 3 2 16777216 5785645 Ns222p269 Ns222p158 Ns222p270 Ns222p271 Ns222p161 Ns222p270 16741137 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 51718402457) qz371 0 2 Ns222p269 Ns222p158 Ns222p270 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 51718402457) qz372 0 2 Ns222p271 Ns222p161 Ns222p270 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p273 := @Ns222p261 2890000 (Ns222p267 rfl) (Enclosure.sfrac_false_div 52156947 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 52156947) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns222p268) qz640) 226375608064910080 72057594037927936 Bool.false 16741137 16777216 0 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q3 52156947 8388608 226375608064910080 72057594037927936 0 Ns222p268 Ns222p156 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16741137 16777216 Ns222p268 Ns222p156 51718402457 34359738368 5785645 5780000 (Ns222p272 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p274 := @Enclosure.Real.IsNear.inv_image (Real.cos qz34) 16741137 16777216 17683663 1515192320000 8406588 8406785 8388608 (Ns222p260 (Ns222p273 rfl rfl) rfl) rfl 

noncomputable def Ns222p275 := @Enclosure.Real.IsNear.recentre' qz35 Bool.false 7525523 8388608 

noncomputable abbrev qz36 := (@HMul.hMul Real Real Real qz343 qz341 qz388)

noncomputable def Ns222p276 := @Enclosure.Real.IsNear.cos_image qz36 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7677371)) qz359) Bool.true 7677371 16777216 

noncomputable def Ns222p277 := nat_lit 283245009400421210657181205 

noncomputable def Ns222p278 := nat_lit 618970019642690137449562112 

noncomputable def Ns222p279 := nat_lit 10116011696960323007567577923227007 

noncomputable def Ns222p280 := @Enclosure.Real.IsNear.recentre' qz36 Bool.true Ns222p277 Ns222p278 Ns222p279 

noncomputable def Ns222p281 := nat_lit 302231454903657293676544000000000000000 

noncomputable abbrev qz37 := qz388

noncomputable def Ns222p282 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz37 884279719003555 140737488355328 1 500000000000000 320311552231 

noncomputable abbrev qz389 := (@HSub.hSub Real Real Real qz634 qz647 qz643)

noncomputable abbrev qz38 := qz389

noncomputable def Ns222p283 := @Enclosure.Real.IsNear.subLit_tf qz38 qz25 45433645287 4398046511104 374860425 70368744177664 1 16 

noncomputable abbrev qz390 := qz647

noncomputable abbrev qz39 := qz390

noncomputable def Ns222p284 := @Enclosure.Real.IsNear.subLit_ff_n qz39 qz29 4306699917081 4398046511104 249031305 70368744177664 2075259 2097152 15 8388608 

noncomputable def Ns222p285 := @Enclosure.Real.IsNear.mulLit_ff qz29 qz29 2075259 2097152 15 8388608 2075259 2097152 15 8388608 4306699917081 4398046511104 

noncomputable def Ns222p286 := nat_lit 3474162366699576448495232881 

noncomputable def Ns222p287 := nat_lit 1901475900342344102245054808064 

noncomputable def Ns222p288 := nat_lit 28522138505135161533675822120960 

noncomputable abbrev qz391 := (BSN.cosEvenQ 16777216)

noncomputable def Ns222p289 := BSN.cos_dyadic_bound_f 7677371 16777216 2 1 8388608 2890000 Ns222p286 Ns222p287 Ns222p286 Ns222p286 Ns222p288 Ns222p286 7525523 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 7677371) qz391 0 1 Ns222p286 Ns222p287 Ns222p286 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 7677371) (BSN.cosOddQ 16777216) 0 1 Ns222p286 Ns222p288 Ns222p286 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p290 := @Ns222p275 820478608 24243077120000 7525523 8388608 51279913 1515192320000 (@Ns222p276 281 8388608 Bool.false 7525523 8388608 1 2890000 (@Ns222p280 Ns222p281 7677371 16777216 281 8388608 (@Ns222p282 4398046511104 374860425 70368744177664 Ns222p277 Ns222p278 Ns222p279 Ns222p281 RS223to240.d39 (@Ns222p283 0 1 5124984835696 320311552231 4398046511104 374860425 70368744177664 (@Ns222p284 95281260080922624 45433645287 4398046511104 374860425 70368744177664 (@Ns222p285 249031305 70368744177664 (Ns222p266 rfl rfl) (Ns222p266 rfl rfl) rfl) (Ns222p266 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7677371 16777216) (BSN.cos_neg_of_bound 7677371 16777216 Bool.false 7525523 8388608 1 2890000 (Ns222p289 rfl rfl)) rfl rfl) 

noncomputable def Ns222p291 := @Ns222p251 318434302159234812457 Ns222p185 (Ns222p252 (@Enclosure.Real.IsNear.of_eq qz365 (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 8 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1)) (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Real Real qz6 qz28 qz8) (@Inv.inv Real Real.instInv (Real.sqrt qz33)) Bool.false 1398913 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz28 (BSN.t_div_two_pi_nonneg qz27 507758 1000 qz30)) Ns222p256) rfl) (@Ns222p257 140737488355328 225996006483757 5084141766836224000 (BSN.correction_mk qz29 (BSN.cos_two_pi_p_ne_zero_mk qz27 507758 1000 8 qz30 rfl rfl (@BSN.floor_sqrt_eq_dec qz27 507758 1000 8 qz30 rfl rfl rfl))) (@Ns222p258 16777216 7525523 8388608 51279913 1515192320000 126529425219079 140737488355328 225996006483757 5084141766836224000 (@Ns222p259 16777216 (Ns222p274 rfl rfl rfl rfl rfl) rfl) (Ns222p290 rfl) rfl)) 

noncomputable def Ns222p292 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz27) (hardyZApproximantRS₀ qz27) Bool.false 3565644088629970728569 590295810358705651712 28380354784211773180457 Ns222p185 (@Eq.refl Real (hardyZApproximantRS₀ qz27)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz27) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz27) qz27 8) (@HMul.hMul Real Real Real qz4 qz381 (Zeta.RiemannSiegel.correction qz29))) Bool.false 3565644088629970728569 590295810358705651712 28380354784211773180457 Ns222p185 (BSN.hardyZApproximantRS₀_eq qz27 8 (@BSN.floor_sqrt_eq_dec qz27 507758 1000 8 qz30 rfl rfl rfl)) (@Ns222p187 3565644088629970728569 590295810358705651712 28380354784211773180457 Ns222p185 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz27) qz27 8) (@HAdd.hAdd Real Real Real qz358 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz27) qz27 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz27) qz27 8)) Bool.false 425489787 67108864 11039 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz27) qz27 8) (Ns222p250 (Ns222p249 rfl rfl rfl rfl) rfl rfl)) (Ns222p291 rfl) rfl rfl)) 

theorem RS223to240.d43 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz27) Bool.false 3565644088629970728569 590295810358705651712 28380354784211773180457 Ns222p185 := Ns222p292 

noncomputable abbrev qz648 := (@HMul.hMul Real Real Real qz848 (Real.sqrt qz853) qz850)

noncomputable abbrev qz392 := qz648

noncomputable abbrev qz40 := qz392

noncomputable abbrev qz393 := (@HMul.hMul Real Real Real qz630 (@HMul.hMul Real Real Real qz630 qz648 qz648) qz648)

noncomputable abbrev qz41 := (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz393))

noncomputable abbrev qz42 := (@HMul.hMul Real Real Real qz343 (@HMul.hMul Real Real Real qz343 qz368 qz368) qz368)

noncomputable abbrev qz649 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz40))

noncomputable def Ns222p293 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (@HAdd.hAdd Real Real Real qz358 (@HAdd.hAdd Real Real Real qz358 qz649 qz41) (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz42))) Bool.false 

noncomputable def Ns222p294 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz358 qz649 qz41) (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz42)) 13897401 536870912 

noncomputable def Ns222p295 := @Enclosure.Real.IsNear.addLit_ff qz649 qz41 1737175 67108864 25 67108864 

noncomputable def Ns222p296 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz40) 25 4 0 1 69487 16777216 1 16777216 1737175 

noncomputable def Ns222p297 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz40) Bool.false 69487 16777216 1 16777216 69487 16777216 1 16777216 

noncomputable def Ns222p298 := @Enclosure.Real.IsNear.mulLit_ff qz19 qz7 25133485 8388608 3 8388608 1351982709879 16777216000 506327 16777216000 6796007431800639663 28147497671065600 16781711708213 

noncomputable def Ns222p299 := @Enclosure.Real.IsNear.sqrt_image qz7 1351982709879 16777216000 506327 16777216000 75303548 75303577 8388608 qz366 

noncomputable def Ns222p300 := @Enclosure.Real.IsNear.sqrt_image qz18 150607125 16777216 29 16777216 25133482 25133488 8388608 (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 150607125 16777216 29 16777216 150607125 16777216 29 16777216 (Ns222p299 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz394 := (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 50266970 16777216 6 16777216 25133485 8388608 3 8388608 (Ns222p300 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns222p301 := @Ns222p298 140737488355328000 qz394 

noncomputable def Ns222p302 := Ns222p301 qz366 

noncomputable def Ns222p303 := @Enclosure.Real.IsNear.inv_image qz40 6796007431800639663 28147497671065600 16781711708213 140737488355328000 34743 34744 8388608 (Ns222p302 rfl) rfl rfl 

noncomputable abbrev qz43 := (@Inv.inv Real Real.instInv qz393)

noncomputable def Ns222p304 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz43 1 32 0 1 1 

noncomputable def Ns222p305 := @Enclosure.Real.IsNear.recentre' qz43 Bool.false 1 16777216 1 16777216 

noncomputable def Ns222p306 := nat_lit 313878476063997659598856928999623251742422052395014207247 

noncomputable def Ns222p307 := nat_lit 22300745198530623141535718272648361505980416000000 

noncomputable def Ns222p308 := nat_lit 58130682805283314930876423519234212806277548658204077 

noncomputable def Ns222p309 := nat_lit 2787593149816327892691964784081045188247552000000000 

noncomputable abbrev qz44 := qz393

noncomputable def Ns222p310 := @Enclosure.Real.IsNear.inv_image qz44 Ns222p306 Ns222p307 Ns222p308 Ns222p309 0 1 

noncomputable def Ns222p311 := nat_lit 46185717013089525960243695375968753569 

noncomputable def Ns222p312 := nat_lit 792281625142643375935439503360000 

noncomputable def Ns222p313 := nat_lit 1140486656499361414947584558175559 

noncomputable def Ns222p314 := nat_lit 19807040628566084398385987584000000 

noncomputable abbrev qz395 := (@HMul.hMul Real Real Real qz630 qz648 qz648)

noncomputable abbrev qz45 := qz395

noncomputable def Ns222p315 := @Enclosure.Real.IsNear.mulLit_ff qz45 qz40 Ns222p311 Ns222p312 Ns222p313 Ns222p314 6796007431800639663 28147497671065600 16781711708213 

noncomputable def Ns222p316 := @Enclosure.Real.IsNear.mulLit_ff qz40 qz40 6796007431800639663 28147497671065600 16781711708213 140737488355328000 6796007431800639663 28147497671065600 16781711708213 140737488355328000 Ns222p311 

noncomputable def Ns222p317 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz42) 13 10 0 1 155945 4194304 1 

noncomputable def Ns222p318 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz42) Bool.false 623780 16777216 2 16777216 155945 4194304 

noncomputable def Ns222p319 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz4 qz19 qz19) qz19 631692068245225 70368744177664 150800919 70368744177664 25133485 8388608 3 8388608 15876623121860338859125 

noncomputable def Ns222p320 := @Enclosure.Real.IsNear.mulLit_ff qz19 qz19 25133485 8388608 3 8388608 25133485 8388608 3 8388608 631692068245225 70368744177664 150800919 

noncomputable def Ns222p321 := @Ns222p320 70368744177664 qz394 

noncomputable def Ns222p322 := Ns222p321 qz394 

noncomputable def Ns222p323 := @Ns222p319 590295810358705651712 5685229292811147 590295810358705651712 (Ns222p322 rfl) qz394 

noncomputable def Ns222p324 := @Enclosure.Real.IsNear.inv_image qz42 15876623121860338859125 590295810358705651712 5685229292811147 590295810358705651712 311889 311891 8388608 (Ns222p323 rfl) 

noncomputable def Ns222p325 := @Ns222p294 201 536870912 405457 8388608 13 83886080 334257918574592 39846649 536870912 1421 2684354560 (@Ns222p295 1 536870912 1 536870912 932638793662464 13897401 536870912 201 536870912 (@Ns222p296 67108864 25 67108864 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns222p297 (Ns222p303 rfl rfl rfl rfl) rfl) rfl) (@Ns222p304 16777216 1 16777216 1 536870912 1 536870912 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns222p305 1 16777216 1 16777216 (@Ns222p310 8388608 (@Ns222p315 140737488355328000 Ns222p306 Ns222p307 Ns222p308 Ns222p309 (@Ns222p316 Ns222p312 Ns222p313 Ns222p314 (Ns222p302 rfl) (Ns222p302 rfl) rfl) (Ns222p302 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns222p317 8388608 405457 8388608 13 83886080 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns222p318 1 8388608 (Ns222p324 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS223to240.d44 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 := @Ns222p293 39846649 536870912 1421 2684354560 (BSN.hardyZErrorBoundRS₀_mk qz3 506327 1000 qz10 rfl rfl) (Ns222p325 rfl rfl) 

noncomputable def Ns222p326 := BSN.log_dyadic_bound 1 17 3 2 1252815 8388608 2890000 1448 3 988035 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz858 := (Enclosure.sfrac Bool.false 9 1)

noncomputable abbrev qz650 := qz858

noncomputable abbrev qz396 := qz650

noncomputable abbrev qz46 := qz396

noncomputable abbrev qz397 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz628)

theorem RS223to240.d45 : Enclosure.Real.IsNear (Real.log qz46) Bool.false 9895419403785957 4503599627370496 100000000867 289000000000000000 := BSN.isNear_log_sfrac 9 1 9895419403785957 4503599627370496 100000000867 289000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz397) Bool.false 664070354991632873422848 302231454903657293676544 1000000008670000 2890000000000000000000 9895419403785957 4503599627370496 100000000867 289000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 988035 8388608 24973259072661432 36028797018963968 2890000 1000000000000000 rfl rfl rfl rfl (Ns222p326 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS223to240.d46 : Enclosure.Real.IsNear (Real.log qz46) Bool.false 294906479 134217728 47 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz46) Bool.false 9895419403785957 4503599627370496 100000000867 289000000000000000 294906479 134217728 47 134217728 RS223to240.d45 rfl 

noncomputable abbrev qz398 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns222p327 := @Enclosure.Real.IsNear.inv_image qz398 50331649 16777216 1 16777216 2796202 2796203 8388608 (@Enclosure.Real.IsNear.of_eq qz398 (Real.sqrt qz397) Bool.false 50331649 16777216 1 16777216 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz397) Bool.false 50331649 16777216 1 16777216 50331649 16777216 1 16777216 (BSN.sqrt_enclosure 9 1 25165824 25165825 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz399 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS223to240.d47 : Enclosure.Real.IsNear qz399 Bool.false 5592405 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz399 Bool.false 5592405 16777216 1 16777216 5592405 16777216 1 16777216 (Ns222p327 rfl rfl) rfl 

theorem RS223to240.d48 : Enclosure.Real.IsNear qz399 Bool.false 44739240 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz399 Bool.false 5592405 16777216 1 16777216 44739240 134217728 8 134217728 RS223to240.d47 rfl 

noncomputable def Ns222p328 := nat_lit 5017514388048998039552000 

noncomputable def Ns222p329 := nat_lit 159910185799698276030301077504 

noncomputable abbrev qz859 := (Enclosure.sfrac Bool.false 509188 1000)

noncomputable abbrev qz651 := qz859

noncomputable abbrev qz400 := qz651

noncomputable abbrev qz47 := qz400

noncomputable abbrev qz48 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 9)

noncomputable abbrev qz860 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 509188 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz652 := qz860

noncomputable abbrev qz401 := qz652

noncomputable abbrev qz49 := qz401

noncomputable abbrev qz861 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 509188 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz653 := qz861

noncomputable abbrev qz402 := qz653

noncomputable abbrev qz50 := qz402

noncomputable abbrev qz654 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz49 qz8))

noncomputable def Ns222p330 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz47) qz47 9) (@HMul.hMul Real Real Real qz4 qz654 (Zeta.RiemannSiegel.correction qz50)) 77997443 33554432 97131 67108864 722887202700064732505 2361183241434822606848 37929506354600654019 Ns222p328 Ns222p329 

noncomputable def Ns222p331 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz47) qz47 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 509188 1000 124 162 134217728 67108864 2251799813685248 Bool.false 115955896794 1770 

noncomputable def Ns222p332 := Ns222p331 279097919 47 47453128 8 294906479 47 44739240 8 Bool.true 161829833 79457 Bool.true 14653833 Bool.true 52691745 7074237752028440 1 Bool.false 133418572 Bool.false Bool.false 124006917 Bool.true Bool.true 155994886 

noncomputable def Ns222p333 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz47) qz47 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 509188 1000 30 80 134217728 67108864 2251799813685248 Bool.false 115955896794 1770 

noncomputable def Ns222p334 := Ns222p333 240485871 47 54794152 8 261175631 47 50729528 8 Bool.true 162983901 59230 Bool.true 171761464 Bool.true 165303272 7074237752028440 1 Bool.false 38517927 Bool.true Bool.false 44657495 Bool.false Bool.true 161829833 

noncomputable def Ns222p335 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz47) qz47 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 509188 1000 100 28 134217728 67108864 2251799813685248 Bool.false 115955896794 1770 

noncomputable def Ns222p336 := Ns222p335 186065264 47 67108856 8 216015088 47 60023992 8 Bool.true 254705985 34865 Bool.false 130825735 Bool.false 60402169 7074237752028440 1 Bool.false 75348950 Bool.false Bool.false 120854141 Bool.false Bool.true 162983901 

noncomputable def Ns222p337 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz47) qz47 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 509188 1000 325 193 134217728 67108864 2251799813685248 Bool.false 115955896794 1770 

noncomputable def Ns222p338 := Ns222p337 93032624 47 94906264 8 147453232 47 77490640 16 Bool.true 134217680 1823 Bool.false 65468951 Bool.false 184538670 7074237752028440 1 Bool.false 62903480 Bool.true Bool.false 131651154 Bool.true Bool.true 254705985 

noncomputable def Ns222p339 := nat_lit 18625396296372140268636170445204413806338456837933581 

noncomputable def Ns222p340 := nat_lit 21558699842806449966346366464530632038345080832000 

noncomputable def Ns222p341 := nat_lit 16429831097285957076620803440640000 

noncomputable def Ns222p342 := nat_lit 50195259607412037361288365126891601920 

noncomputable abbrev qz403 := (@Eq.refl Real qz651)

noncomputable abbrev qz51 := qz403

noncomputable def Ns222p343 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz47 509188 1000 1037090677376 16000000 1018376 4000 2000 Ns222p341 Ns222p342 qz51 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns222p344 := nat_lit 195301435468647133543254410607506634113951537172930426306560 

noncomputable abbrev qz404 := (Enclosure.sfrac Bool.false 509188 2000)

noncomputable abbrev qz655 := (Real.log (Enclosure.sfrac Bool.false 1037090677376 16000000))

noncomputable abbrev qz52 := (@HSub.hSub Real Real Real qz347 (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 509188 4000) qz655) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1018376)))))) qz404)

noncomputable abbrev qz405 := (@HSub.hSub Real Real Real qz11 qz52 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 509188 2000) (Real.log Real.pi)))

noncomputable def Ns222p345 := @Enclosure.Real.IsNear.addLit_ft_p qz405 (Enclosure.sfrac Bool.true Ns222p341 Ns222p342) 3890835728105076305993 4503599627370496000 390041433552362313 29593600000000000000000 Ns222p341 Ns222p342 0 1 Ns222p344 

noncomputable def Ns222p346 := nat_lit 13055478286187227176425331097600 

noncomputable abbrev qz406 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 509188 2000) (Real.log Real.pi))

noncomputable def Ns222p347 := @Enclosure.Real.IsNear.subLit_ff_p qz52 qz406 1040674185409876383349 900719925474099200 80810652593431 14450000000000000000 4889574643017 16777216000 127297 16777216000 Ns222p346 3890835728105076305993 4503599627370496000 

noncomputable def Ns222p348 := nat_lit 10406741854098763833490000 

noncomputable abbrev qz53 := (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 509188 4000) qz655) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1018376))))))

noncomputable def Ns222p349 := @Enclosure.Real.IsNear.subLit_ff_p qz53 qz404 6349960370580145975369 4503599627370496000 80810652593431 14450000000000000000 509188 2000 0 1 Ns222p348 1040674185409876383349 900719925474099200 80810652593431 14450000000000000000 

noncomputable def Ns222p350 := nat_lit 14298839579381081052867920675326656512 

noncomputable def Ns222p351 := nat_lit 26788203256142940784820224 

noncomputable def Ns222p352 := nat_lit 42997176134508216924427107077118693787228842315268106597209778256277345835660214293412856508413486103051028204066209682392613352527116568416638674730485151445763301990385830002851860355672124695563468800 

noncomputable def Ns222p353 := nat_lit 1654449374231993890419559774410969676556448707471278698657731376574841354976619196603657431375594490078507023105257445425119424414145834161764087845135889485158575161615682340445768021184214436864327680 

noncomputable def Ns222p354 := nat_lit 46351484618345116649450809997364525556017994162134160036712807220139672242327514879068217719567224109906916276204659560726351724030795703721981756595661972497526417088770984359961228954986086400 

noncomputable def Ns222p355 := BSN.log_dyadic_bound 512802677376 1561378677376 9 8 Ns222p352 67108864 23120000 Ns222p353 Ns222p354 45777203 2074181354752 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 512802677376) (BSN.artanhQ 1561378677376) 0 8 Ns222p353 Ns222p352 Ns222p354 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns222p356 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 509188 4000) qz655 509188 4000 0 1 49896916851667577 4503599627370496 2500000867 57800000000000000 6351727824466727549369 4503599627370496000 318242610366499 57800000000000000000 (Enclosure.Real.IsNear.const Bool.false 509188 4000) (BSN.isNear_log_sfrac 1037090677376 16000000 49896916851667577 4503599627370496 2500000867 57800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1037090677376) qz354)) Bool.false Ns222p351 Ns222p89 1000000346800000 23120000000000000000000 49896916851667577 4503599627370496 2500000867 57800000000000000 (BSN.log_rat_reduce_isNear 1037090677376 16000000 15 2074181354752 1048576000000 45777203 67108864 24973259072661432 36028797018963968 23120000 1000000000000000 rfl rfl rfl rfl (Ns222p355 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns222p357 := BSN.arctan_dyadic_bound_f 1000 1018376 1 0 8388608 2890000 0 1 1 0 1 1 8237 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1018376) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1018376) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz407 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1018376)))

noncomputable def Ns222p358 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz407 884279719003555 562949953421312 1 2000000000000000 8237 8388608 1 2890000 7413238906304642154496 883726943290787 562949953421312 200000000289 578000000000000000 qz16 (Ns222p357 rfl) rfl rfl 

noncomputable def Ns222p359 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 509188 4000) qz655) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz407)) 6351727824466727549369 4503599627370496000 318242610366499 57800000000000000000 883726943290787 2251799813685248 200000000289 2312000000000000000 Ns222p350 6349960370580145975369 4503599627370496000 80810652593431 14450000000000000000 (Ns222p356 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz407) 1 4 0 1 883726943290787 562949953421312 200000000289 578000000000000000 883726943290787 2251799813685248 200000000289 2312000000000000000 qz357 Ns222p358 rfl) 

noncomputable def Ns222p360 := @Ns222p345 Ns222p339 Ns222p340 390041433552362313 29593600000000000000000 (@Ns222p347 390041433552362313 29593600000000000000000 (Ns222p349 (Ns222p359 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 509188 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz404 (Real.log Real.pi) 509188 2000 0 1 38410761 33554432 1 33554432 4889574643017 16777216000 127297 16777216000 (Enclosure.Real.IsNear.const Bool.false 509188 2000) RS223to240.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns222p341 Ns222p342) 

noncomputable def Ns222p361 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz47) Bool.false Ns222p339 Ns222p340 390041433552362313 29593600000000000000000 14494487099 16777216 111 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz47) (@HAdd.hAdd Real Real Real qz358 qz405 (Enclosure.sfrac Bool.true Ns222p341 Ns222p342)) Bool.false Ns222p339 Ns222p340 390041433552362313 29593600000000000000000 Ns222p343 (Ns222p360 rfl rfl)) 

noncomputable def Ns222p362 := BSN.cos_dyadic_bound_f 26628803 34359738368 1 0 16777216 5785645 0 1 1 0 1 1 16777210 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 26628803) (BSN.cosEvenQ 34359738368) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 26628803) (BSN.cosOddQ 34359738368) 0 0 rfl) rfl rfl 

noncomputable def Ns222p363 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz47) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 14494487099) qz359) Bool.false 14494487099 16777216 111 8388608 Bool.true 16777210 16777216 1 2890000 (Ns222p361 rfl) (Enclosure.sfrac_false_div 14494487099 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 14494487099) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1873835465432081891328) qz360) 226375608064910080 72057594037927936 Bool.false 16777210 16777216 137 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q2 14494487099 16777216 226375608064910080 72057594037927936 137 1873835465432081891328 Ns222p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777210 16777216 1873835465432081891328 Ns222p89 26628803 34359738368 5785645 5780000 (Ns222p362 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p364 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz47) Bool.false Ns222p339 Ns222p340 390041433552362313 29593600000000000000000 115955896794 134217728 1770 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz47) (@HAdd.hAdd Real Real Real qz358 qz405 (Enclosure.sfrac Bool.true Ns222p341 Ns222p342)) Bool.false Ns222p339 Ns222p340 390041433552362313 29593600000000000000000 Ns222p343 (Ns222p360 rfl rfl)) 

noncomputable def Ns222p365 := Ns222p338 34865 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 325 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 62903480 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 193 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 131651154 134217728) qz51 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz47) qz47 1) Bool.true 8388605 8388608 20573663 1515192320000 134217680 134217728 1823 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz47) qz47 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz47)) Bool.true 8388605 8388608 20573663 1515192320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz47) qz47) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz47)) Bool.true 16777210 16777216 329178608 24243077120000 8388605 8388608 20573663 1515192320000 (Ns222p363 rfl rfl) rfl)) rfl) (Ns222p364 rfl) RS223to240.d7 

noncomputable def Ns222p366 := nat_lit 18028972574000003416960556361884567454495598438719819607626452794945 

noncomputable def Ns222p367 := nat_lit 337507212961623591603457614856665877331598703806493782629121601 

noncomputable def Ns222p368 := nat_lit 47218191253559975844319813444987908731306125703507650363373595885121 

noncomputable def Ns222p369 := BSN.sin_dyadic_bound_f 65468951 134217728 3 2 134217728 67108864 Ns222p366 Ns222p124 Ns222p367 Ns222p368 Ns222p127 Ns222p367 62903480 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 65468951) qz363 0 2 Ns222p366 Ns222p124 Ns222p367 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 65468951) qz364 0 2 Ns222p368 Ns222p127 Ns222p367 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p370 := nat_lit 6345132757008422474123890792744571771472357183475597821169663506430755804181964557688603510942977190400000 

noncomputable def Ns222p371 := nat_lit 1559727161263352015974297063250992416926898170779624876737656125265125438501516927289361000000000000 

noncomputable def Ns222p372 := nat_lit 31702508018313597744923960637311153027088605118167935331509527022854524238951134620592113555756901952000000 

noncomputable def Ns222p373 := BSN.sin_dyadic_bound_f 184538670 134217728 4 3 134217728 67108864 Ns222p370 Ns222p111 Ns222p371 Ns222p372 Ns222p114 Ns222p371 131651154 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 184538670) qz363 0 3 Ns222p370 Ns222p111 Ns222p371 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 184538670) qz364 0 3 Ns222p372 Ns222p114 Ns222p371 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p374 := nat_lit 159791927106027618158506189169253758760430225823280063942287700690625 

noncomputable def Ns222p375 := nat_lit 85811494715795358247221308810470361995207172225592296215687890625 

noncomputable def Ns222p376 := nat_lit 479204158328651263759024124890140335557300263125389007234431726290625 

noncomputable def Ns222p377 := BSN.cos_dyadic_bound_f 130825735 134217728 3 2 134217728 67108864 Ns222p374 Ns222p105 Ns222p375 Ns222p376 Ns222p108 Ns222p375 75348950 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 130825735) qz361 0 2 Ns222p374 Ns222p105 Ns222p375 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 130825735) qz362 0 2 Ns222p376 Ns222p108 Ns222p375 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p378 := nat_lit 7257207708137120039821659296800055255560794707254503783225204131521 

noncomputable def Ns222p379 := nat_lit 177182274691089278421801226980214776400497946409880295488603841 

noncomputable def Ns222p380 := nat_lit 21771268759861977940908134287946205337129583125870691589084635186881 

noncomputable def Ns222p381 := BSN.cos_dyadic_bound_f 60402169 134217728 3 2 134217728 67108864 Ns222p378 Ns222p105 Ns222p379 Ns222p380 Ns222p108 Ns222p379 120854141 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 60402169) qz361 0 2 Ns222p378 Ns222p105 Ns222p379 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 60402169) qz362 0 2 Ns222p380 Ns222p108 Ns222p379 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p382 := Ns222p336 59230 BSN.abs_quadSignPos (BSN.cos_quad_nat0 100 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 75348950 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 120854141 134217728) qz51 rfl rfl (Ns222p365 RS223to240.d9 RS223to240.d11 RS223to240.d13 RS223to240.d17 (Ns222p369 rfl rfl) (Ns222p373 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns222p364 rfl) RS223to240.d19 RS223to240.d21 RS223to240.d23 RS223to240.d25 RS223to240.d17 (Ns222p377 rfl rfl) (Ns222p381 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns222p383 := nat_lit 1832317161617366855025081335129464842605869983953070430478062526899353883254420082767862270667639253630976 

noncomputable def Ns222p384 := nat_lit 659339049312008355526946066258716338028935905718041946323948489550466028419546418372314048176848896 

noncomputable def Ns222p385 := nat_lit 11104242180654637548456368174317294432197438246992744315411976582259517631563981921615342491997121827307520 

noncomputable def Ns222p386 := BSN.cos_dyadic_bound_f 171761464 134217728 4 3 134217728 67108864 Ns222p383 Ns222p227 Ns222p384 Ns222p385 Ns222p230 Ns222p384 38517927 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 171761464) qz361 0 3 Ns222p383 Ns222p227 Ns222p384 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 171761464) qz362 0 3 Ns222p385 Ns222p230 Ns222p384 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p387 := nat_lit 1571538702308191972428320082074604850755122974932392758699186475359559818111947983127198253707059261341696 

noncomputable def Ns222p388 := nat_lit 416272192619663716014122115525306992881395167452829264195157881026482250885872298401535428149641216 

noncomputable def Ns222p389 := nat_lit 9525306416263556873379441061632830606042356069858953266137266724305078713391258249652785590878319945973760 

noncomputable def Ns222p390 := BSN.cos_dyadic_bound_f 165303272 134217728 4 3 134217728 67108864 Ns222p387 Ns222p227 Ns222p388 Ns222p389 Ns222p230 Ns222p388 44657495 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 165303272) qz361 0 3 Ns222p387 Ns222p227 Ns222p388 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 165303272) qz362 0 3 Ns222p389 Ns222p230 Ns222p388 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p391 := Ns222p334 79457 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 38517927 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 80 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 44657495 134217728) qz51 rfl rfl (Ns222p382 rfl rfl) (Ns222p364 rfl) RS223to240.d27 RS223to240.d29 RS223to240.d31 RS223to240.d33 RS223to240.d17 (Ns222p386 rfl rfl) (Ns222p390 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p392 := nat_lit 46111043604100398284070588321 

noncomputable def Ns222p393 := BSN.cos_dyadic_bound_f 14653833 134217728 2 1 134217728 67108864 Ns222p392 Ns222p246 Ns222p392 Ns222p392 Ns222p247 Ns222p392 133418572 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 14653833) qz361 0 1 Ns222p392 Ns222p246 Ns222p392 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 14653833) qz362 0 1 Ns222p392 Ns222p247 Ns222p392 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p394 := nat_lit 4202669899830036470888364373196691195084820160278750434789461690625 

noncomputable def Ns222p395 := nat_lit 59421095080844389112554031755068869966429739158278290312890625 

noncomputable def Ns222p396 := nat_lit 12607890857299947723886868011526563447514527621357934747787759290625 

noncomputable def Ns222p397 := BSN.cos_dyadic_bound_f 52691745 134217728 3 2 134217728 67108864 Ns222p394 Ns222p105 Ns222p395 Ns222p396 Ns222p108 Ns222p395 124006917 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 52691745) qz361 0 2 Ns222p394 Ns222p105 Ns222p395 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 52691745) qz362 0 2 Ns222p396 Ns222p108 Ns222p395 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz408 := (BSN.cos_quad_nat2 162 rfl)

noncomputable def Ns222p398 := Ns222p332 97131 BSN.abs_quadSignPos (BSN.cos_quad_nat0 124 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133418572 134217728) BSN.abs_quadSignNeg qz408 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 124006917 134217728) qz51 rfl rfl (Ns222p391 rfl) (Ns222p364 rfl) RS223to240.d35 RS223to240.d37 RS223to240.d46 RS223to240.d48 RS223to240.d17 (Ns222p393 rfl rfl) (Ns222p397 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p399 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz47) qz47 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz47) qz47 9) 155994886 134217728 97131 134217728 155994886 134217728 97131 134217728 41874558357078016 77997443 33554432 97131 67108864 (Ns222p398 rfl) 

noncomputable def Ns222p400 := @Enclosure.Real.IsNear.mulLit_tf qz654 (Zeta.RiemannSiegel.correction qz50) 5591719 16777216 1 16777216 129278170576895 140737488355328 16835066062913 747667906887680000 722887202700064732505 2361183241434822606848 

noncomputable abbrev qz656 := (@HPow.hPow Real Real Real qz6 qz49 qz8)

noncomputable def Ns222p401 := @Enclosure.Real.IsNear.mulLit_tf qz48 qz656 1 1 0 1 5591719 16777216 1 16777216 5591719 16777216 1 16777216 

noncomputable def Ns222p402 := @Enclosure.Real.IsNear.sqrt_image qz49 339905521569 4194304000 127297 4194304000 75515999 75516029 8388608 (@Enclosure.Real.IsNear.of_eq qz49 (@HMul.hMul Real Real Real qz4 qz47 qz2) Bool.false 339905521569 4194304000 127297 4194304000 (BSN.t_div_two_pi_mk qz47 509188 1000 qz51) (@Enclosure.Real.IsNear.mulLit_ff qz47 qz2 509188 1000 0 1 2670177 16777216 1 16777216 339905521569 4194304000 127297 4194304000 (Enclosure.Real.IsNear.const Bool.false 509188 1000) RS223to240.d40 rfl)) 

noncomputable abbrev qz862 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 509188 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz657 := qz862

noncomputable abbrev qz409 := qz657

noncomputable abbrev qz54 := qz409

noncomputable def Ns222p403 := @Enclosure.Real.IsNear.sqrt_image qz54 37758007 4194304 15 8388608 25168911 25168917 8388608 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 151032028 16777216 30 16777216 37758007 4194304 15 8388608 (Ns222p402 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns222p404 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz54) 12584457 4194304 3 8388608 2795859 2795860 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz54) Bool.false 50337828 16777216 6 16777216 12584457 4194304 3 8388608 (Ns222p403 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns222p405 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz54)) Bool.false 5591719 16777216 1 16777216 5591719 16777216 1 16777216 (Ns222p404 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz55 := (@HMul.hMul Real Real Real qz343 qz341 qz402)

noncomputable abbrev qz658 := (@HMul.hMul Real Real Real qz848 qz861 qz861)

noncomputable abbrev qz410 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz658 qz653) qz639)

noncomputable abbrev qz56 := (Real.cos (@HMul.hMul Real Real Real qz343 qz341 qz410))

noncomputable def Ns222p406 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz50) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz55)) qz56) Bool.false 129278170576895 

noncomputable def Ns222p407 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz55)) qz56 16778837 16777216 197 

noncomputable def Ns222p408 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz55)) Bool.false 16778837 16777216 197 16777216 16778837 16777216 197 

noncomputable def Ns222p409 := @Enclosure.Real.IsNear.recentre' (Real.cos qz55) Bool.false 8387798 8388608 282938608 24243077120000 4193899 4194304 17683663 1515192320000 

noncomputable def Ns222p410 := @Enclosure.Real.IsNear.cos_image qz55 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 233005) qz359) Bool.false 233005 16777216 95 8388608 Bool.false 8387798 8388608 1 

noncomputable def Ns222p411 := nat_lit 404791131135819956394739369 

noncomputable def Ns222p412 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz50 884279719003555 140737488355328 1 500000000000000 9271 4194304 15 8388608 8198157274881958405 590295810358705651712 Ns222p411 

noncomputable def Ns222p413 := @Enclosure.Real.IsNear.subLit_ff_p qz54 qz46 37758007 4194304 15 8388608 9 1 0 1 9271 9271 4194304 15 

noncomputable abbrev qz411 := (Enclosure.Real.IsNear.const Bool.false 9 1)

noncomputable def Ns222p414 := @Ns222p413 8388608 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 151032028 16777216 30 16777216 37758007 4194304 15 8388608 (Ns222p402 rfl rfl rfl rfl rfl rfl) rfl) qz411 

noncomputable def Ns222p415 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 8198157274881958405 590295810358705651712 Ns222p411 Ns222p263 233005 16777216 95 8388608 (@Ns222p412 Ns222p263 RS223to240.d39 (Ns222p414 rfl rfl) rfl) 

noncomputable def Ns222p416 := BSN.cos_dyadic_bound_f 233005 16777216 1 0 8388608 2890000 0 1 1 0 1 1 8387798 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 233005) qz391 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 233005) (BSN.cosOddQ 16777216) 0 0 rfl) rfl rfl 

noncomputable def Ns222p417 := @Enclosure.Real.IsNear.inv_image (Real.cos qz55) 4193899 4194304 17683663 1515192320000 8389320 8389517 8388608 (Ns222p409 (@Ns222p410 2890000 (Ns222p415 rfl) (Enclosure.sfrac_false_div 233005 16777216) (Ns222p416 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns222p418 := @Enclosure.Real.IsNear.recentre' qz56 Bool.false 7704835 8388608 

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz343 qz341 qz410)

noncomputable def Ns222p419 := @Enclosure.Real.IsNear.cos_image qz57 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6820887)) qz359) Bool.true 6820887 16777216 

noncomputable def Ns222p420 := nat_lit 1006585391985473705810296045 

noncomputable def Ns222p421 := nat_lit 2475880078570760549798248448 

noncomputable def Ns222p422 := nat_lit 3410651467186766227001613580430627 

noncomputable def Ns222p423 := @Enclosure.Real.IsNear.recentre' qz57 Bool.true Ns222p420 Ns222p421 Ns222p422 

noncomputable abbrev qz58 := qz410

noncomputable def Ns222p424 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz58 884279719003555 140737488355328 1 500000000000000 1138311068719 

noncomputable abbrev qz412 := (@HSub.hSub Real Real Real qz634 qz658 qz653)

noncomputable abbrev qz59 := qz412

noncomputable def Ns222p425 := @Enclosure.Real.IsNear.subLit_tf qz59 qz25 38799440943 17592186044416 126385605 70368744177664 1 16 

noncomputable abbrev qz413 := qz658

noncomputable abbrev qz60 := qz413

noncomputable def Ns222p426 := @Enclosure.Real.IsNear.subLit_ff_n qz60 qz50 85951441 17592186044416 556485 70368744177664 9271 4194304 15 8388608 

noncomputable def Ns222p427 := @Enclosure.Real.IsNear.mulLit_ff qz50 qz50 9271 4194304 15 8388608 9271 4194304 15 8388608 85951441 17592186044416 

noncomputable def Ns222p428 := nat_lit 2164529050633388965335299361 

noncomputable def Ns222p429 := BSN.cos_dyadic_bound_f 6820887 16777216 2 1 8388608 2890000 Ns222p428 Ns222p287 Ns222p428 Ns222p428 Ns222p288 Ns222p428 7704835 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 6820887) qz391 0 1 Ns222p428 Ns222p287 Ns222p428 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 6820887) (BSN.cosOddQ 16777216) 0 1 Ns222p428 Ns222p288 Ns222p428 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p430 := @Ns222p418 568767216 48486154240000 7704835 8388608 35547951 3030384640000 (@Ns222p419 191 16777216 Bool.false 7704835 8388608 1 2890000 (@Ns222p423 Ns222p281 6820887 16777216 191 16777216 (@Ns222p424 17592186044416 126385605 70368744177664 Ns222p420 Ns222p421 Ns222p422 Ns222p281 RS223to240.d39 (@Ns222p425 0 1 18212977099504 1138311068719 17592186044416 126385605 70368744177664 (@Ns222p426 162736650344988672 38799440943 17592186044416 126385605 70368744177664 (@Ns222p427 556485 70368744177664 (Ns222p414 rfl rfl) (Ns222p414 rfl rfl) rfl) (Ns222p414 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6820887 16777216) (BSN.cos_neg_of_bound 6820887 16777216 Bool.false 7704835 8388608 1 2890000 (Ns222p429 rfl rfl)) rfl rfl) 

noncomputable abbrev qz61 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 9) (Enclosure.sfrac Bool.true 1 1) Bool.true 1 1 0 1 (BSN.neg_one_pow_odd_mk 9 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1))

noncomputable def Ns222p431 := @Ns222p400 37929506354600654019 Ns222p328 (Ns222p401 qz61 (@Enclosure.Real.IsNear.of_eq qz656 (@Inv.inv Real Real.instInv (Real.sqrt qz54)) Bool.false 5591719 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz49 (BSN.t_div_two_pi_nonneg qz47 509188 1000 qz51)) Ns222p405) rfl) (@Ns222p406 140737488355328 16835066062913 747667906887680000 (BSN.correction_mk qz50 (BSN.cos_two_pi_p_ne_zero_mk qz47 509188 1000 9 qz51 rfl rfl (@BSN.floor_sqrt_eq_dec qz47 509188 1000 9 qz51 rfl rfl rfl))) (@Ns222p407 16777216 7704835 8388608 35547951 3030384640000 129278170576895 140737488355328 16835066062913 747667906887680000 (@Ns222p408 16777216 (Ns222p417 rfl rfl rfl rfl rfl) rfl) (Ns222p430 rfl) rfl)) 

noncomputable def Ns222p432 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz47) (hardyZApproximantRS₀ qz47) Bool.true 4765694910278864980647 2361183241434822606848 7300102652745325262019 Ns222p328 (@Eq.refl Real (hardyZApproximantRS₀ qz47)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz47) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz47) qz47 9) (@HMul.hMul Real Real Real qz4 qz654 (Zeta.RiemannSiegel.correction qz50))) Bool.true 4765694910278864980647 2361183241434822606848 7300102652745325262019 Ns222p328 (BSN.hardyZApproximantRS₀_eq qz47 9 (@BSN.floor_sqrt_eq_dec qz47 509188 1000 9 qz51 rfl rfl rfl)) (@Ns222p330 4765694910278864980647 2361183241434822606848 7300102652745325262019 Ns222p328 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz47) qz47 9) (@HAdd.hAdd Real Real Real qz358 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz47) qz47 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz47) qz47 9)) Bool.true 77997443 33554432 97131 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz47) qz47 9) (Ns222p399 (Ns222p398 rfl) rfl rfl)) (Ns222p431 rfl) rfl rfl)) 

theorem RS223to240.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz47) Bool.true 4765694910278864980647 2361183241434822606848 7300102652745325262019 Ns222p328 := Ns222p432 

noncomputable def Ns222p433 := nat_lit 213244361492082416680960000 

noncomputable def Ns222p434 := nat_lit 10430924751464827534549450752 

noncomputable abbrev qz863 := (Enclosure.sfrac Bool.false 510617 1000)

noncomputable abbrev qz659 := qz863

noncomputable abbrev qz414 := qz659

noncomputable abbrev qz62 := qz414

noncomputable abbrev qz864 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 510617 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz660 := qz864

noncomputable abbrev qz415 := qz660

noncomputable abbrev qz63 := qz415

noncomputable abbrev qz865 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 510617 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz661 := qz865

noncomputable abbrev qz416 := qz661

noncomputable abbrev qz64 := qz416

noncomputable abbrev qz662 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz63 qz8))

noncomputable def Ns222p435 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (@HMul.hMul Real Real Real qz4 qz662 (Zeta.RiemannSiegel.correction qz64)) 6352239 8388608 97407 67108864 349464966687021192777 1180591620717411303424 1573852303284613415717 Ns222p433 Ns222p434 

noncomputable def Ns222p436 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 510617 1000 123 162 134217728 67108864 2251799813685248 Bool.false 116377499789 1775 

noncomputable def Ns222p437 := Ns222p436 279097919 47 47453128 8 294906479 47 44739240 8 Bool.false 44810324 79684 Bool.true 202710478 Bool.true 52510108 7074237752028440 1 Bool.false 133972284 Bool.false Bool.false 124076293 Bool.true Bool.false 50817912 

noncomputable def Ns222p438 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 510617 1000 30 80 134217728 67108864 2251799813685248 Bool.false 116377499789 1775 

noncomputable def Ns222p439 := Ns222p438 240485871 47 54794152 8 261175631 47 50729528 8 Bool.false 54087751 59400 Bool.true 93812779 Bool.true 116920254 7074237752028440 1 Bool.false 102745277 Bool.true Bool.false 86431815 Bool.false Bool.false 44810324 

noncomputable def Ns222p440 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 510617 1000 101 28 134217728 67108864 2251799813685248 Bool.false 116377499789 1775 

noncomputable def Ns222p441 := Ns222p440 186065264 47 67108856 8 216015088 47 60023992 8 Bool.false 73411009 34966 Bool.false 75712753 Bool.false 173319603 7074237752028440 1 Bool.false 71760692 Bool.true Bool.false 37022767 Bool.false Bool.false 54087751 

noncomputable def Ns222p442 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 510617 1000 326 194 134217728 67108864 2251799813685248 Bool.false 116377499789 1775 

noncomputable def Ns222p443 := Ns222p442 93032624 47 94906264 8 147453232 47 77490640 16 Bool.false 134217712 1831 Bool.false 143299612 Bool.false 184602283 7074237752028440 1 Bool.false 64715884 Bool.true Bool.false 26059853 Bool.true Bool.false 73411009 

noncomputable def Ns222p444 := nat_lit 2491691568217325143334205429293627105439662749164669031193 

noncomputable def Ns222p445 := nat_lit 2873658411358283880402743731296837924003852545163264000 

noncomputable def Ns222p446 := nat_lit 16661674304393439882138671771360000 

noncomputable def Ns222p447 := nat_lit 51046427731163459647283242249515174720 

noncomputable abbrev qz417 := (@Eq.refl Real qz659)

noncomputable abbrev qz65 := qz417

noncomputable def Ns222p448 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz62 510617 1000 1042919882756 16000000 1021234 4000 2000 Ns222p446 Ns222p447 qz65 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns222p449 := nat_lit 797341301829544045866945737373960673740692079732694089981760 

noncomputable abbrev qz418 := (Enclosure.sfrac Bool.false 510617 2000)

noncomputable abbrev qz663 := (Real.log (Enclosure.sfrac Bool.false 1042919882756 16000000))

noncomputable abbrev qz66 := (@HSub.hSub Real Real Real qz347 (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 510617 4000) qz663) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1021234)))))) qz418)

noncomputable abbrev qz419 := (@HSub.hSub Real Real Real qz11 qz66 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 510617 2000) (Real.log Real.pi)))

noncomputable def Ns222p450 := @Enclosure.Real.IsNear.addLit_ft_p qz419 (Enclosure.sfrac Bool.true Ns222p446 Ns222p447) 15619929492006622002833 18014398509481984000 1564515490830116193 118374400000000000000000 Ns222p446 Ns222p447 0 1 Ns222p449 

noncomputable def Ns222p451 := nat_lit 209647144793732296617505482342400 

noncomputable abbrev qz420 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 510617 2000) (Real.log Real.pi))

noncomputable def Ns222p452 := @Enclosure.Real.IsNear.subLit_ff_p qz66 qz420 4176960887096021837341 3602879701896396800 1296542942733839 231200000000000000000 19613187549537 67108864000 510617 67108864000 Ns222p451 15619929492006622002833 18014398509481984000 

noncomputable def Ns222p453 := nat_lit 41769608870960218373410000 

noncomputable abbrev qz67 := (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 510617 4000) qz663) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1021234))))))

noncomputable def Ns222p454 := @Enclosure.Real.IsNear.subLit_ff_p qz67 qz418 25484033497338190298769 18014398509481984000 1296542942733839 231200000000000000000 510617 2000 0 1 Ns222p453 4176960887096021837341 3602879701896396800 1296542942733839 231200000000000000000 

noncomputable def Ns222p455 := nat_lit 57384941881254755898510448556047859712 

noncomputable def Ns222p456 := nat_lit 26801755307997638986563584 

noncomputable def Ns222p457 := nat_lit 45638750416091477657928749523326152190002737208401305345638823477828704579549725984664374223564839670615007482707541044236343811251556570455051232765497051519334823824944630818443878992591198788308172800 

noncomputable def Ns222p458 := nat_lit 1784844642219910970388431332252383715142267788026651587537733179458679307666788095228555679792214888744973526964197259477862922506258616870609728867262608104732599545659701883406605954088821720172462080 

noncomputable def Ns222p459 := nat_lit 55540078249386218172653974439392189381405817789661706666739763595493546925453639996298529492536665092583915624452494810073643374929866260742123018962606713655927918572685621868664668362794598400 

noncomputable def Ns222p460 := BSN.log_dyadic_bound 518631882756 1567207882756 9 8 Ns222p457 67108864 23120000 Ns222p458 Ns222p459 46153348 2085839765512 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 518631882756) (BSN.artanhQ 1567207882756) 0 8 Ns222p458 Ns222p457 Ns222p459 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns222p461 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 510617 4000) qz663 510617 4000 0 1 49922159515316857 4503599627370496 2500000867 57800000000000000 25491103325232547570769 18014398509481984000 1276542942704939 231200000000000000000 (Enclosure.Real.IsNear.const Bool.false 510617 4000) (BSN.isNear_log_sfrac 1042919882756 16000000 49922159515316857 4503599627370496 2500000867 57800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1042919882756) qz354)) Bool.false Ns222p456 Ns222p89 1000000346800000 23120000000000000000000 49922159515316857 4503599627370496 2500000867 57800000000000000 (BSN.log_rat_reduce_isNear 1042919882756 16000000 15 2085839765512 1048576000000 46153348 67108864 24973259072661432 36028797018963968 23120000 1000000000000000 rfl rfl rfl rfl (Ns222p460 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns222p462 := BSN.arctan_dyadic_bound_f 1000 1021234 1 0 8388608 2890000 0 1 1 0 1 1 8214 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1021234) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1021234) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz421 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1021234)))

noncomputable def Ns222p463 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz421 884279719003555 562949953421312 1 2000000000000000 8214 8388608 1 2890000 7413251854153570844672 883728486794659 562949953421312 200000000289 578000000000000000 qz16 (Ns222p462 rfl) rfl rfl 

noncomputable def Ns222p464 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 510617 4000) qz663) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz421)) 25491103325232547570769 18014398509481984000 1276542942704939 231200000000000000000 883728486794659 2251799813685248 200000000289 2312000000000000000 Ns222p455 25484033497338190298769 18014398509481984000 1296542942733839 231200000000000000000 (Ns222p461 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz421) 1 4 0 1 883728486794659 562949953421312 200000000289 578000000000000000 883728486794659 2251799813685248 200000000289 2312000000000000000 qz357 Ns222p463 rfl) 

noncomputable def Ns222p465 := @Ns222p450 Ns222p444 Ns222p445 1564515490830116193 118374400000000000000000 (@Ns222p452 1564515490830116193 118374400000000000000000 (Ns222p454 (Ns222p464 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 510617 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz418 (Real.log Real.pi) 510617 2000 0 1 38410761 33554432 1 33554432 19613187549537 67108864000 510617 67108864000 (Enclosure.Real.IsNear.const Bool.false 510617 2000) RS223to240.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns222p446 Ns222p447) 

noncomputable def Ns222p466 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns222p444 Ns222p445 1564515490830116193 118374400000000000000000 14547187473 16777216 223 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz358 qz419 (Enclosure.sfrac Bool.true Ns222p446 Ns222p447)) Bool.false Ns222p444 Ns222p445 1564515490830116193 118374400000000000000000 Ns222p448 (Ns222p465 rfl rfl)) 

noncomputable def Ns222p467 := BSN.cos_dyadic_bound_f 12693119 34359738368 1 0 16777216 5785645 0 1 1 0 1 1 16777214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 12693119) (BSN.cosEvenQ 34359738368) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 12693119) (BSN.cosOddQ 34359738368) 0 0 rfl) rfl rfl 

noncomputable def Ns222p468 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz62) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 14547187473) qz359) Bool.false 14547187473 16777216 223 16777216 Bool.false 16777214 16777216 1 2890000 (Ns222p466 rfl) (Enclosure.sfrac_false_div 14547187473 16777216) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 14547187473) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 893198870700040912896) qz360) 226375608064910080 72057594037927936 Bool.false 16777214 16777216 138 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q0 14547187473 16777216 226375608064910080 72057594037927936 138 893198870700040912896 Ns222p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777214 16777216 893198870700040912896 Ns222p89 12693119 34359738368 5785645 5780000 (Ns222p467 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p469 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns222p444 Ns222p445 1564515490830116193 118374400000000000000000 116377499789 134217728 1775 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz358 qz419 (Enclosure.sfrac Bool.true Ns222p446 Ns222p447)) Bool.false Ns222p444 Ns222p445 1564515490830116193 118374400000000000000000 Ns222p448 (Ns222p465 rfl rfl)) 

noncomputable def Ns222p470 := Ns222p443 34966 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 326 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 64715884 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 194 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 26059853 134217728) qz65 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) Bool.false 8388607 8388608 41327951 3030384640000 134217712 134217728 1831 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.false 8388607 8388608 41327951 3030384640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz62) qz62) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.false 16777214 16777216 661247216 48486154240000 8388607 8388608 41327951 3030384640000 (Ns222p468 rfl rfl) rfl)) rfl) (Ns222p469 rfl) RS223to240.d7 

noncomputable def Ns222p471 := nat_lit 886993944567750443709398837978594914158548989936313161742473266009569276268459525874292675657716398555136 

noncomputable def Ns222p472 := nat_lit 74979091512105141933694392357269772718299701480223890969889748297093096700075988285044315291385856 

noncomputable def Ns222p473 := nat_lit 5378323695395592024020326378653966365169238967144386594899846500669358355263199296281421764360727785635840 

noncomputable def Ns222p474 := BSN.cos_dyadic_bound_f 143299612 134217728 4 3 134217728 67108864 Ns222p471 Ns222p227 Ns222p472 Ns222p473 Ns222p230 Ns222p472 64715884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 143299612) qz361 0 3 Ns222p471 Ns222p227 Ns222p472 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 143299612) qz362 0 3 Ns222p473 Ns222p230 Ns222p472 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p475 := nat_lit 2446118207719946470389155743925515702906235921219375656850836234963463589815390481780493598690681984877841 

noncomputable def Ns222p476 := nat_lit 1566191318735141704224733134134975926533333320056890007706789363032411748898275558291173935448818961 

noncomputable def Ns222p477 := nat_lit 14818747208351277516202516594470277612536876242831360066663743429131728714450367056377893117510636479153425 

noncomputable def Ns222p478 := BSN.cos_dyadic_bound_f 184602283 134217728 4 3 134217728 67108864 Ns222p475 Ns222p227 Ns222p476 Ns222p477 Ns222p230 Ns222p476 26059853 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 184602283) qz361 0 3 Ns222p475 Ns222p227 Ns222p476 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 184602283) qz362 0 3 Ns222p477 Ns222p230 Ns222p476 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p479 := nat_lit 32248685166225614932317563051793081801083709344844547121040605668225 

noncomputable def Ns222p480 := nat_lit 1079822327692849453578176855385274663143650444180597256908530561 

noncomputable def Ns222p481 := nat_lit 84459093818250822114097348087406495224812244278635616730976115319681 

noncomputable def Ns222p482 := BSN.sin_dyadic_bound_f 75712753 134217728 3 2 134217728 67108864 Ns222p479 Ns222p124 Ns222p480 Ns222p481 Ns222p127 Ns222p480 71760692 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 75712753) qz363 0 2 Ns222p479 Ns222p124 Ns222p480 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 75712753) qz364 0 2 Ns222p481 Ns222p127 Ns222p480 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p483 := nat_lit 1899826459492086522847543740986259467282454183381035535836237110672692933705438337031167920466140433926321 

noncomputable def Ns222p484 := nat_lit 734805210118759081102472568551168887058475318715841666858725262849678151412980596917735455580145841 

noncomputable def Ns222p485 := nat_lit 11512913271230233122468338192647391349075100084041045472983769573840525182337064903863221769645177554782385 

noncomputable def Ns222p486 := BSN.cos_dyadic_bound_f 173319603 134217728 4 3 134217728 67108864 Ns222p483 Ns222p227 Ns222p484 Ns222p485 Ns222p230 Ns222p484 37022767 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 173319603) qz361 0 3 Ns222p483 Ns222p227 Ns222p484 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 173319603) qz362 0 3 Ns222p485 Ns222p230 Ns222p484 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p487 := Ns222p441 59400 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 101 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 71760692 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 37022767 134217728) qz65 rfl rfl (Ns222p470 RS223to240.d9 RS223to240.d11 RS223to240.d13 RS223to240.d17 (Ns222p474 rfl rfl) (Ns222p478 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns222p469 rfl) RS223to240.d19 RS223to240.d21 RS223to240.d23 RS223to240.d25 RS223to240.d17 (Ns222p482 rfl rfl) (Ns222p486 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns222p488 := nat_lit 42233639988767548295920479371555885233580863908933357001439494393441 

noncomputable def Ns222p489 := nat_lit 5999236867218489894143965079488632341316963970796883373527780961 

noncomputable def Ns222p490 := nat_lit 126688921492568207907973150184508678436059957798858477237571427618401 

noncomputable def Ns222p491 := BSN.cos_dyadic_bound_f 93812779 134217728 3 2 134217728 67108864 Ns222p488 Ns222p105 Ns222p489 Ns222p490 Ns222p108 Ns222p489 102745277 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 93812779) qz361 0 2 Ns222p488 Ns222p105 Ns222p489 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 93812779) qz362 0 2 Ns222p490 Ns222p108 Ns222p489 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p492 := nat_lit 101919352102267544807927287197199972401452722842424316636649801974016 

noncomputable def Ns222p493 := nat_lit 34923519255972610497795253173083802407231988955813873634319073536 

noncomputable def Ns222p494 := nat_lit 305688209268290689202786271085253749599543704549361322162680767774976 

noncomputable def Ns222p495 := BSN.cos_dyadic_bound_f 116920254 134217728 3 2 134217728 67108864 Ns222p492 Ns222p105 Ns222p493 Ns222p494 Ns222p108 Ns222p493 86431815 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 116920254) qz361 0 2 Ns222p492 Ns222p105 Ns222p493 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 116920254) qz362 0 2 Ns222p494 Ns222p108 Ns222p493 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p496 := Ns222p439 79684 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 102745277 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 80 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 86431815 134217728) qz65 rfl rfl (Ns222p487 rfl rfl) (Ns222p469 rfl) RS223to240.d27 RS223to240.d29 RS223to240.d31 RS223to240.d33 RS223to240.d17 (Ns222p491 rfl rfl) (Ns222p495 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p497 := nat_lit 9243357747405251263853171227066526157598527286053407273367432237743947682550286552179140794335100283785216 

noncomputable def Ns222p498 := nat_lit 4814091857456225706780278177071025231608030349344038056945201031353160151866312958736172880112521216 

noncomputable def Ns222p499 := nat_lit 46167695348409256768723861018083417044478524220146091634754544470982966781661152899323949554742304960024576 

noncomputable def Ns222p500 := BSN.sin_dyadic_bound_f 202710478 134217728 4 3 134217728 67108864 Ns222p497 Ns222p111 Ns222p498 Ns222p499 Ns222p114 Ns222p498 133972284 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 202710478) qz363 0 3 Ns222p497 Ns222p111 Ns222p498 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 202710478) qz364 0 3 Ns222p499 Ns222p114 Ns222p498 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p501 := nat_lit 4145018906094850567448313604364722332272929562054584708566047850496 

noncomputable def Ns222p502 := nat_lit 57802056767696703025687648859205799601633728193258035378978816 

noncomputable def Ns222p503 := nat_lit 12434941114171016308938889437796448585219585418707367609627385593856 

noncomputable def Ns222p504 := BSN.cos_dyadic_bound_f 52510108 134217728 3 2 134217728 67108864 Ns222p501 Ns222p105 Ns222p502 Ns222p503 Ns222p108 Ns222p502 124076293 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 52510108) qz361 0 2 Ns222p501 Ns222p105 Ns222p502 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 52510108) qz362 0 2 Ns222p503 Ns222p108 Ns222p502 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz664 := (BSN.cos_quad_nat3 123 rfl)

noncomputable def Ns222p505 := Ns222p437 97407 BSN.abs_quadSignPos qz664 (BSN.sfrac_eq_quadSignPos_mul Bool.false 133972284 134217728) BSN.abs_quadSignNeg qz408 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 124076293 134217728) qz65 rfl rfl (Ns222p496 rfl) (Ns222p469 rfl) RS223to240.d35 RS223to240.d37 RS223to240.d46 RS223to240.d48 RS223to240.d17 (Ns222p500 rfl rfl) (Ns222p504 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p506 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) 50817912 134217728 97407 134217728 50817912 134217728 97407 134217728 13641329380687872 6352239 8388608 97407 67108864 (Ns222p505 rfl) 

noncomputable def Ns222p507 := @Enclosure.Real.IsNear.mulLit_tf qz662 (Zeta.RiemannSiegel.correction qz64) 2793901 8388608 1 8388608 125081370702477 140737488355328 138807613930399 6355177208545280000 349464966687021192777 1180591620717411303424 

noncomputable abbrev qz665 := (@HPow.hPow Real Real Real qz6 qz63 qz8)

noncomputable def Ns222p508 := @Enclosure.Real.IsNear.mulLit_tf qz48 qz665 1 1 0 1 2793901 8388608 1 8388608 2793901 8388608 1 8388608 

noncomputable def Ns222p509 := @Enclosure.Real.IsNear.sqrt_image qz63 1363437769209 16777216000 510617 16777216000 75621890 75621919 8388608 (@Enclosure.Real.IsNear.of_eq qz63 (@HMul.hMul Real Real Real qz4 qz62 qz2) Bool.false 1363437769209 16777216000 510617 16777216000 (BSN.t_div_two_pi_mk qz62 510617 1000 qz65) (@Enclosure.Real.IsNear.mulLit_ff qz62 qz2 510617 1000 0 1 2670177 16777216 1 16777216 1363437769209 16777216000 510617 16777216000 (Enclosure.Real.IsNear.const Bool.false 510617 1000) RS223to240.d40 rfl)) 

noncomputable abbrev qz866 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 510617 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz666 := qz866

noncomputable abbrev qz422 := qz666

noncomputable abbrev qz68 := qz422

noncomputable def Ns222p510 := @Enclosure.Real.IsNear.sqrt_image qz68 151243809 16777216 29 16777216 25186551 25186557 8388608 (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 151243809 16777216 29 16777216 151243809 16777216 29 16777216 (Ns222p509 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns222p511 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz68) 12593277 4194304 3 8388608 2793900 2793902 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz68) Bool.false 50373108 16777216 6 16777216 12593277 4194304 3 8388608 (Ns222p510 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns222p512 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz68)) Bool.false 5587802 16777216 2 16777216 2793901 8388608 1 8388608 (Ns222p511 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz69 := (@HMul.hMul Real Real Real qz343 qz341 qz416)

noncomputable abbrev qz667 := (@HMul.hMul Real Real Real qz848 qz865 qz865)

noncomputable abbrev qz423 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz667 qz661) qz639)

noncomputable abbrev qz70 := (Real.cos (@HMul.hMul Real Real Real qz343 qz341 qz423))

noncomputable def Ns222p513 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz64) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz69)) qz70) Bool.false 125081370702477 

noncomputable def Ns222p514 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz69)) qz70 16850349 16777216 193 

noncomputable def Ns222p515 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz69)) Bool.false 16850349 16777216 193 16777216 16850349 16777216 193 

noncomputable def Ns222p516 := @Enclosure.Real.IsNear.recentre' (Real.cos qz69) Bool.false 8352200 8388608 68567152 6060769280000 1044025 1048576 4285447 378798080000 

noncomputable def Ns222p517 := @Enclosure.Real.IsNear.cos_image qz69 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 97729) qz645) Bool.false 97729 1048576 23 2097152 Bool.false 8352200 8388608 1 

noncomputable def Ns222p518 := nat_lit 782596186864415052272138123 

noncomputable def Ns222p519 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz64 884279719003555 140737488355328 1 500000000000000 248865 16777216 29 16777216 220066272269819715075 2361183241434822606848 Ns222p518 

noncomputable def Ns222p520 := @Enclosure.Real.IsNear.subLit_ff_p qz68 qz46 151243809 16777216 29 16777216 9 1 0 1 248865 248865 16777216 29 

noncomputable def Ns222p521 := @Ns222p520 16777216 (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 151243809 16777216 29 16777216 151243809 16777216 29 16777216 (Ns222p509 rfl rfl rfl rfl rfl rfl) rfl) qz411 

noncomputable def Ns222p522 := @Enclosure.Real.IsNear.recentre' qz69 Bool.false 220066272269819715075 2361183241434822606848 Ns222p518 Ns222p150 97729 1048576 23 2097152 (@Ns222p519 Ns222p150 RS223to240.d39 (Ns222p521 rfl rfl) rfl) 

noncomputable def Ns222p523 := nat_lit 29014219670751100192948224 

noncomputable def Ns222p524 := nat_lit 435213295061266502894223360 

noncomputable def Ns222p525 := BSN.cos_dyadic_bound_f 97729 1048576 2 1 8388608 2890000 91220788039793268481 Ns222p523 91220788039793268481 91220788039793268481 Ns222p524 91220788039793268481 8352200 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 97729) (BSN.cosEvenQ 1048576) 0 1 91220788039793268481 Ns222p523 91220788039793268481 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 97729) (BSN.cosOddQ 1048576) 0 1 91220788039793268481 Ns222p524 91220788039793268481 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p526 := @Enclosure.Real.IsNear.inv_image (Real.cos qz69) 1044025 1048576 4285447 378798080000 8425078 8425271 8388608 (Ns222p516 (@Ns222p517 2890000 (Ns222p522 rfl) (Enclosure.sfrac_false_div 97729 1048576) (Ns222p525 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns222p527 := @Enclosure.Real.IsNear.recentre' qz70 Bool.false 7423073 8388608 

noncomputable abbrev qz71 := (@HMul.hMul Real Real Real qz343 qz341 qz423)

noncomputable def Ns222p528 := @Enclosure.Real.IsNear.cos_image qz71 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8128867)) qz359) Bool.true 8128867 16777216 

noncomputable def Ns222p529 := nat_lit 19193745923351589177971490205 

noncomputable def Ns222p530 := nat_lit 13519329563327618061512757233968277 

noncomputable def Ns222p531 := @Enclosure.Real.IsNear.recentre' qz71 Bool.true Ns222p529 Ns222p168 Ns222p530 

noncomputable def Ns222p532 := nat_lit 1208925819614629174706176000000000000000 

noncomputable abbrev qz72 := qz423

noncomputable def Ns222p533 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz72 884279719003555 140737488355328 1 500000000000000 21705514116031 

noncomputable abbrev qz424 := (@HSub.hSub Real Real Real qz634 qz667 qz661)

noncomputable abbrev qz73 := qz424

noncomputable def Ns222p534 := @Enclosure.Real.IsNear.subLit_tf qz73 qz25 4113328071615 281474976710656 500974275 281474976710656 1 16 

noncomputable abbrev qz425 := qz667

noncomputable abbrev qz74 := qz425

noncomputable def Ns222p535 := @Enclosure.Real.IsNear.subLit_ff_n qz74 qz64 61933788225 281474976710656 14435011 281474976710656 248865 16777216 29 16777216 

noncomputable def Ns222p536 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz64 248865 16777216 29 16777216 248865 16777216 29 16777216 61933788225 281474976710656 

noncomputable def Ns222p537 := nat_lit 4366365347793880705862208721 

noncomputable def Ns222p538 := BSN.cos_dyadic_bound_f 8128867 16777216 2 1 8388608 2890000 Ns222p537 Ns222p287 Ns222p537 Ns222p537 Ns222p288 Ns222p537 7423073 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 8128867) qz391 0 1 Ns222p537 Ns222p287 Ns222p537 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 8128867) (BSN.cosOddQ 16777216) 0 1 Ns222p537 Ns222p288 Ns222p537 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p539 := @Ns222p527 562987216 48486154240000 7423073 8388608 35186701 3030384640000 (@Ns222p528 189 16777216 Bool.false 7423073 8388608 1 2890000 (@Ns222p531 Ns222p532 8128867 16777216 189 16777216 (@Ns222p533 281474976710656 500974275 281474976710656 Ns222p529 Ns222p168 Ns222p530 Ns222p532 RS223to240.d39 (@Ns222p534 0 1 347288225856496 21705514116031 281474976710656 500974275 281474976710656 (@Ns222p535 69010193536348323840 4113328071615 281474976710656 500974275 281474976710656 (@Ns222p536 14435011 281474976710656 (Ns222p521 rfl rfl) (Ns222p521 rfl rfl) rfl) (Ns222p521 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8128867 16777216) (BSN.cos_neg_of_bound 8128867 16777216 Bool.false 7423073 8388608 1 2890000 (Ns222p538 rfl rfl)) rfl rfl) 

noncomputable def Ns222p540 := @Ns222p507 1573852303284613415717 Ns222p433 (Ns222p508 qz61 (@Enclosure.Real.IsNear.of_eq qz665 (@Inv.inv Real Real.instInv (Real.sqrt qz68)) Bool.false 2793901 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz63 (BSN.t_div_two_pi_nonneg qz62 510617 1000 qz65)) Ns222p512) rfl) (@Ns222p513 140737488355328 138807613930399 6355177208545280000 (BSN.correction_mk qz64 (BSN.cos_two_pi_p_ne_zero_mk qz62 510617 1000 9 qz65 rfl rfl (@BSN.floor_sqrt_eq_dec qz62 510617 1000 9 qz65 rfl rfl rfl))) (@Ns222p514 16777216 7423073 8388608 35186701 3030384640000 125081370702477 140737488355328 138807613930399 6355177208545280000 (@Ns222p515 16777216 (Ns222p526 rfl rfl rfl rfl rfl) rfl) (Ns222p539 rfl) rfl)) 

noncomputable def Ns222p541 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (hardyZApproximantRS₀ qz62) Bool.false 1243463128979781572169 1180591620717411303424 311093225479669657895717 Ns222p433 (@Eq.refl Real (hardyZApproximantRS₀ qz62)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (@HMul.hMul Real Real Real qz4 qz662 (Zeta.RiemannSiegel.correction qz64))) Bool.false 1243463128979781572169 1180591620717411303424 311093225479669657895717 Ns222p433 (BSN.hardyZApproximantRS₀_eq qz62 9 (@BSN.floor_sqrt_eq_dec qz62 510617 1000 9 qz65 rfl rfl rfl)) (@Ns222p435 1243463128979781572169 1180591620717411303424 311093225479669657895717 Ns222p433 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (@HAdd.hAdd Real Real Real qz358 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 9)) Bool.false 6352239 8388608 97407 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (Ns222p506 (Ns222p505 rfl) rfl rfl)) (Ns222p540 rfl) rfl rfl)) 

theorem RS223to240.d50 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz62) Bool.false 1243463128979781572169 1180591620717411303424 311093225479669657895717 Ns222p433 := Ns222p541 

noncomputable def Ns222p542 := nat_lit 53311090373020604170240000 

noncomputable def Ns222p543 := nat_lit 7093109788811472981633007616 

noncomputable abbrev qz867 := (Enclosure.sfrac Bool.false 512045 1000)

noncomputable abbrev qz668 := qz867

noncomputable abbrev qz426 := qz668

noncomputable abbrev qz75 := qz426

noncomputable abbrev qz868 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 512045 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz669 := qz868

noncomputable abbrev qz427 := qz669

noncomputable abbrev qz76 := qz427

noncomputable abbrev qz869 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 512045 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz670 := qz869

noncomputable abbrev qz428 := qz670

noncomputable abbrev qz77 := qz428

noncomputable abbrev qz671 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz76 qz8))

noncomputable def Ns222p544 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz75) qz75 9) (@HMul.hMul Real Real Real qz4 qz671 (Zeta.RiemannSiegel.correction qz77)) 33634729 33554432 48837 33554432 84463060403280130369 295147905179352825856 394471831513789746703 Ns222p542 Ns222p543 

noncomputable def Ns222p545 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz75) qz75 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 512045 1000 123 162 134217728 67108864 2251799813685248 Bool.false 116799075641 1780 

noncomputable def Ns222p546 := Ns222p545 279097919 47 47453128 8 294906479 47 44739240 8 Bool.true 72035287 79901 Bool.true 179686454 Bool.true 52060708 7074237752028440 1 Bool.false 130620971 Bool.false Bool.false 124246966 Bool.true Bool.true 67269458 

noncomputable def Ns222p547 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz75) qz75 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 512045 1000 30 80 134217728 67108864 2251799813685248 Bool.false 116799075641 1780 

noncomputable def Ns222p548 := Ns222p547 240485871 47 54794152 8 261175631 47 50729528 8 Bool.true 61914405 59561 Bool.true 15650751 Bool.true 68303203 7074237752028440 1 Bool.false 133306266 Bool.true Bool.false 117209885 Bool.false Bool.true 72035287 

noncomputable def Ns222p549 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz75) qz75 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 512045 1000 102 29 134217728 67108864 2251799813685248 Bool.false 116799075641 1780 

noncomputable def Ns222p550 := Ns222p549 186065264 47 67108856 8 216015088 47 60023992 8 Bool.false 36442065 35059 Bool.false 20758694 Bool.false 75597196 7074237752028440 1 Bool.false 132615610 Bool.true Bool.false 71663012 Bool.true Bool.true 61914405 

noncomputable def Ns222p551 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz75) qz75 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 512045 1000 328 195 134217728 67108864 2251799813685248 Bool.false 116799075641 1780 

noncomputable def Ns222p552 := Ns222p551 93032624 47 94906264 8 147453232 47 77490640 16 Bool.true 134217720 1831 Bool.false 10367449 Bool.false 184786205 7074237752028440 1 Bool.false 133817517 Bool.false Bool.false 131699107 Bool.false Bool.false 36442065 

noncomputable def Ns222p553 := nat_lit 2034378726074797535987232267700464659083655202579067 

noncomputable def Ns222p554 := nat_lit 2337772700726360108667245113525875717975520051200 

noncomputable def Ns222p555 := nat_lit 16895962423777261523838573500000000 

noncomputable def Ns222p556 := nat_lit 51908981573730808204808376016845000000 

noncomputable abbrev qz429 := (@Eq.refl Real qz668)

noncomputable abbrev qz78 := qz429

noncomputable def Ns222p557 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz75 512045 1000 1048761328100 16000000 1024090 4000 2000 Ns222p555 Ns222p556 qz78 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns222p558 := nat_lit 10171893630373987679936161338502323295418276012895335000000 

noncomputable abbrev qz430 := (Enclosure.sfrac Bool.false 512045 2000)

noncomputable abbrev qz672 := (Real.log (Enclosure.sfrac Bool.false 1048761328100 16000000))

noncomputable abbrev qz79 := (@HSub.hSub Real Real Real qz347 (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 512045 4000) qz672) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1024090)))))) qz430)

noncomputable abbrev qz431 := (@HSub.hSub Real Real Real qz11 qz79 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 512045 2000) (Real.log Real.pi)))

noncomputable def Ns222p559 := @Enclosure.Real.IsNear.addLit_ft_p qz431 (Enclosure.sfrac Bool.true Ns222p555 Ns222p556) 195956405358453571843 225179981368524800 1568862218687578517 118374400000000000000000 Ns222p555 Ns222p556 0 1 Ns222p558 

noncomputable def Ns222p560 := nat_lit 2630082351425866400625223270400 

noncomputable abbrev qz432 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 512045 2000) (Real.log Real.pi))

noncomputable def Ns222p561 := @Enclosure.Real.IsNear.subLit_ff_p qz79 qz432 261951390112948666627 225179981368524800 325028243392029 57800000000000000000 3933607623249 13421772800 102409 13421772800 Ns222p560 195956405358453571843 225179981368524800 

noncomputable abbrev qz80 := (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 512045 4000) qz672) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1024090))))))

noncomputable def Ns222p562 := @Enclosure.Real.IsNear.subLit_ff_p qz80 qz430 63920506378574361447 45035996273704960 325028243392029 57800000000000000000 512045 2000 0 1 104780556045179466650800 261951390112948666627 225179981368524800 325028243392029 57800000000000000000 

noncomputable def Ns222p563 := nat_lit 143936184353940453467854333443833856 

noncomputable def Ns222p564 := nat_lit 26815260013407882423828480 

noncomputable def Ns222p565 := BSN.log_dyadic_bound 185328100 2097337328100 1 0 1 67108864 23120000 0 1 11859 2097522656200 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 185328100) (BSN.artanhQ 2097337328100) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns222p566 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 512045 4000) qz672 512045 4000 0 1 3121707124333815 281474976710656 781250289 18062500000000000 63938180979180332067 45035996273704960 80007060846201 14450000000000000000 (Enclosure.Real.IsNear.const Bool.false 512045 4000) (BSN.isNear_log_sfrac 1048761328100 16000000 3121707124333815 281474976710656 781250289 18062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1048761328100) qz354)) Bool.false Ns222p564 Ns222p89 1000000369920000 23120000000000000000000 3121707124333815 281474976710656 781250289 18062500000000000 (BSN.log_rat_reduce_isNear 1048761328100 16000000 16 2097522656200 2097152000000 11859 67108864 24973259072661432 36028797018963968 23120000 1000000000000000 rfl rfl rfl rfl (Ns222p565 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns222p567 := BSN.arctan_dyadic_bound_f 1000 1024090 1 0 8388608 2890000 0 1 1 0 1 1 8191 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1024090) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1024090) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz433 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1024090)))

noncomputable def Ns222p568 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz433 884279719003555 562949953421312 1 2000000000000000 8191 8388608 1 2890000 7413264802002499534848 883730030298531 562949953421312 200000000289 578000000000000000 qz16 (Ns222p567 rfl) rfl rfl 

noncomputable def Ns222p569 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 512045 4000) qz672) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz433)) 63938180979180332067 45035996273704960 80007060846201 14450000000000000000 883730030298531 2251799813685248 200000000289 2312000000000000000 Ns222p563 63920506378574361447 45035996273704960 325028243392029 57800000000000000000 (Ns222p566 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz433) 1 4 0 1 883730030298531 562949953421312 200000000289 578000000000000000 883730030298531 2251799813685248 200000000289 2312000000000000000 qz357 Ns222p568 rfl) 

noncomputable def Ns222p570 := @Ns222p559 Ns222p553 Ns222p554 1568862218687578517 118374400000000000000000 (@Ns222p561 1568862218687578517 118374400000000000000000 (Ns222p562 (Ns222p569 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 512045 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz430 (Real.log Real.pi) 512045 2000 0 1 38410761 33554432 1 33554432 3933607623249 13421772800 102409 13421772800 (Enclosure.Real.IsNear.const Bool.false 512045 2000) RS223to240.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns222p555 Ns222p556) 

noncomputable def Ns222p571 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz75) Bool.false Ns222p553 Ns222p554 1568862218687578517 118374400000000000000000 14599884455 16777216 223 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz75) (@HAdd.hAdd Real Real Real qz358 qz431 (Enclosure.sfrac Bool.true Ns222p555 Ns222p556)) Bool.false Ns222p553 Ns222p554 1568862218687578517 118374400000000000000000 Ns222p557 (Ns222p570 rfl rfl)) 

noncomputable def Ns222p572 := nat_lit 3797376197194353129553920 

noncomputable def Ns222p573 := nat_lit 856616417219388399266846597266209913019283404410994706396369682291454189341960474638632060153971503226915047869306466386260103425223281 

noncomputable def Ns222p574 := nat_lit 16860812360175734222210805034837902731874731588140993779854824115686058269364094835627812361599730584878593258197117225559879026789580800 

noncomputable def Ns222p575 := nat_lit 609882088993127410606726471277368487949420305685193116484235471102061309115059097077541650459691375677144474757965580933059373681 

noncomputable def Ns222p576 := nat_lit 4277763052597221950574685411979972045020140185558437726093047203152389620244240786668643276259844944809920363195456640325677004317321841 

noncomputable def Ns222p577 := nat_lit 590128432606150697777378176219326595615615605584934782294918844049012039427743319246973432655990570470750764036899102894595765937635328000 

noncomputable def Ns222p578 := BSN.sin_dyadic_bound_f 53963961437 34359738368 4 3 16777216 5785645 Ns222p573 Ns222p574 Ns222p575 Ns222p576 Ns222p577 Ns222p575 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53963961437) qz371 0 3 Ns222p573 Ns222p574 Ns222p575 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53963961437) qz372 0 3 Ns222p576 Ns222p577 Ns222p575 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p579 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz75) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 14599884455) qz359) Bool.false 14599884455 16777216 223 16777216 Bool.true 16777215 16777216 1 2890000 (Ns222p571 rfl) (Enclosure.sfrac_false_div 14599884455 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 14599884455) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns222p572) qz360) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 138 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q1 14599884455 16777216 226375608064910080 72057594037927936 138 Ns222p572 Ns222p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns222p572 Ns222p89 53963961437 34359738368 5785645 5780000 (Ns222p578 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p580 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz75) Bool.false Ns222p553 Ns222p554 1568862218687578517 118374400000000000000000 116799075641 134217728 1780 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz75) (@HAdd.hAdd Real Real Real qz358 qz431 (Enclosure.sfrac Bool.true Ns222p555 Ns222p556)) Bool.false Ns222p553 Ns222p554 1568862218687578517 118374400000000000000000 Ns222p557 (Ns222p570 rfl rfl)) 

noncomputable def Ns222p581 := Ns222p552 35059 BSN.abs_quadSignPos (BSN.cos_quad_nat0 328 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133817517 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 195 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131699107 134217728) qz78 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz75) qz75 1) Bool.true 16777215 16777216 41327951 3030384640000 134217720 134217728 1831 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz75) qz75 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz75)) Bool.true 16777215 16777216 41327951 3030384640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz75) qz75) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz75)) Bool.true 16777215 16777216 661247216 48486154240000 16777215 16777216 41327951 3030384640000 (Ns222p579 rfl rfl) rfl)) rfl) (Ns222p580 rfl) RS223to240.d7 

noncomputable def Ns222p582 := nat_lit 11552809991073653286807295201 

noncomputable def Ns222p583 := BSN.cos_dyadic_bound_f 10367449 134217728 2 1 134217728 67108864 Ns222p582 Ns222p246 Ns222p582 Ns222p582 Ns222p247 Ns222p582 133817517 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 10367449) qz361 0 1 Ns222p582 Ns222p246 Ns222p582 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 10367449) qz362 0 1 Ns222p582 Ns222p247 Ns222p582 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p584 := nat_lit 6379286550681625332247246376751565902415415414803809742515675997354964424140553052352346707739223307040625 

noncomputable def Ns222p585 := nat_lit 1585019304888016357702142735854198032569409784289722436868820715160932925032535579171955195556640625 

noncomputable def Ns222p586 := nat_lit 31873027299085700119922944548563570311341771254894894408506880638179397929309281751448007384286150308640625 

noncomputable def Ns222p587 := BSN.sin_dyadic_bound_f 184786205 134217728 4 3 134217728 67108864 Ns222p584 Ns222p111 Ns222p585 Ns222p586 Ns222p114 Ns222p585 131699107 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 184786205) qz363 0 3 Ns222p584 Ns222p111 Ns222p585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 184786205) qz364 0 3 Ns222p586 Ns222p114 Ns222p585 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p588 := nat_lit 185694956487965860797241524496 

noncomputable def Ns222p589 := BSN.cos_dyadic_bound_f 20758694 134217728 2 1 134217728 67108864 Ns222p588 Ns222p246 Ns222p588 Ns222p588 Ns222p247 Ns222p588 132615610 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 20758694) qz361 0 1 Ns222p588 Ns222p246 Ns222p588 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 20758694) qz362 0 1 Ns222p588 Ns222p247 Ns222p588 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p590 := nat_lit 32052249979143704528004483203898532975268406404079181232040170291200 

noncomputable def Ns222p591 := nat_lit 1066707866775530436891345373591863857446769785964933318285787136 

noncomputable def Ns222p592 := nat_lit 83944641942163494333590108117700818584219483907220579049018459488256 

noncomputable def Ns222p593 := BSN.sin_dyadic_bound_f 75597196 134217728 3 2 134217728 67108864 Ns222p590 Ns222p124 Ns222p591 Ns222p592 Ns222p127 Ns222p591 71663012 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 75597196) qz363 0 2 Ns222p590 Ns222p124 Ns222p591 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 75597196) qz364 0 2 Ns222p592 Ns222p127 Ns222p591 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p594 := Ns222p550 59561 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 102 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132615610 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 29 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 71663012 134217728) qz78 rfl rfl (Ns222p581 RS223to240.d9 RS223to240.d11 RS223to240.d13 RS223to240.d17 (Ns222p583 rfl rfl) (Ns222p587 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns222p580 rfl) RS223to240.d19 RS223to240.d21 RS223to240.d23 RS223to240.d25 RS223to240.d17 (Ns222p589 rfl rfl) (Ns222p593 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns222p595 := nat_lit 59998546278619225006509728001 

noncomputable def Ns222p596 := BSN.cos_dyadic_bound_f 15650751 134217728 2 1 134217728 67108864 Ns222p595 Ns222p246 Ns222p595 Ns222p595 Ns222p247 Ns222p595 133306266 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 15650751) qz361 0 1 Ns222p595 Ns222p246 Ns222p595 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 15650751) qz362 0 1 Ns222p595 Ns222p247 Ns222p595 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p597 := nat_lit 11866712774959102558772184989843828604781718643276142146030925038241 

noncomputable def Ns222p598 := nat_lit 473727459448192142583862982641286200405726861562029924435673761 

noncomputable def Ns222p599 := nat_lit 35599190869958411292031387243566203241944344476105302378243903767201 

noncomputable def Ns222p600 := BSN.cos_dyadic_bound_f 68303203 134217728 3 2 134217728 67108864 Ns222p597 Ns222p105 Ns222p598 Ns222p599 Ns222p108 Ns222p598 117209885 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 68303203) qz361 0 2 Ns222p597 Ns222p105 Ns222p598 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 68303203) qz362 0 2 Ns222p599 Ns222p108 Ns222p598 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p601 := Ns222p548 79901 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133306266 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 80 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 117209885 134217728) qz78 rfl rfl (Ns222p594 rfl rfl) (Ns222p580 rfl) RS223to240.d27 RS223to240.d29 RS223to240.d31 RS223to240.d33 RS223to240.d17 (Ns222p596 rfl rfl) (Ns222p600 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p602 := nat_lit 5702964544387074727990893029515864403045469887428161705900769198779235551383489503596880108703603336482816 

noncomputable def Ns222p603 := nat_lit 1132880388936032000211376463185903629744334081176459821017390201951286491917512678976474108241186816 

noncomputable def Ns222p604 := nat_lit 28496112844107851909193350363268047702942482107492732525190106209928821122797505993522312600236941862834176 

noncomputable def Ns222p605 := BSN.sin_dyadic_bound_f 179686454 134217728 4 3 134217728 67108864 Ns222p602 Ns222p111 Ns222p603 Ns222p604 Ns222p114 Ns222p603 130620971 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 179686454) qz363 0 3 Ns222p602 Ns222p111 Ns222p603 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 179686454) qz364 0 3 Ns222p604 Ns222p114 Ns222p603 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p606 := nat_lit 4004930141471634144249366769290918547065974953527376170282186244096 

noncomputable def Ns222p607 := nat_lit 53961070904280484081097987777557564948764382277771743073468416 

noncomputable def Ns222p608 := nat_lit 12014682502273093871779938111897200526068027331817572967360411795456 

noncomputable def Ns222p609 := BSN.cos_dyadic_bound_f 52060708 134217728 3 2 134217728 67108864 Ns222p606 Ns222p105 Ns222p607 Ns222p608 Ns222p108 Ns222p607 124246966 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 52060708) qz361 0 2 Ns222p606 Ns222p105 Ns222p607 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 52060708) qz362 0 2 Ns222p608 Ns222p108 Ns222p607 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p610 := Ns222p546 97674 BSN.abs_quadSignPos qz664 (BSN.sfrac_eq_quadSignPos_mul Bool.false 130620971 134217728) BSN.abs_quadSignNeg qz408 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 124246966 134217728) qz78 rfl rfl (Ns222p601 rfl) (Ns222p580 rfl) RS223to240.d35 RS223to240.d37 RS223to240.d46 RS223to240.d48 RS223to240.d17 (Ns222p605 rfl rfl) (Ns222p609 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p611 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz75) qz75 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz75) qz75 9) 67269458 134217728 97674 134217728 67269458 134217728 97674 134217728 18057507633102848 33634729 33554432 48837 33554432 (Ns222p610 rfl) 

noncomputable def Ns222p612 := @Enclosure.Real.IsNear.mulLit_tf qz671 (Zeta.RiemannSiegel.correction qz77) 2791951 8388608 1 8388608 30252343398319 35184372088832 139331729910639 6355177208545280000 84463060403280130369 295147905179352825856 

noncomputable abbrev qz673 := (@HPow.hPow Real Real Real qz6 qz76 qz8)

noncomputable def Ns222p613 := @Enclosure.Real.IsNear.mulLit_tf qz48 qz673 1 1 0 1 2791951 8388608 1 8388608 2791951 8388608 1 8388608 

noncomputable def Ns222p614 := @Enclosure.Real.IsNear.sqrt_image qz76 273450156393 3355443200 102409 3355443200 75727559 75727588 8388608 (@Enclosure.Real.IsNear.of_eq qz76 (@HMul.hMul Real Real Real qz4 qz75 qz2) Bool.false 273450156393 3355443200 102409 3355443200 (BSN.t_div_two_pi_mk qz75 512045 1000 qz78) (@Enclosure.Real.IsNear.mulLit_ff qz75 qz2 512045 1000 0 1 2670177 16777216 1 16777216 273450156393 3355443200 102409 3355443200 (Enclosure.Real.IsNear.const Bool.false 512045 1000) RS223to240.d40 rfl)) 

noncomputable abbrev qz870 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 512045 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz674 := qz870

noncomputable abbrev qz434 := qz674

noncomputable abbrev qz81 := qz434

noncomputable def Ns222p615 := @Enclosure.Real.IsNear.sqrt_image qz81 151455147 16777216 29 16777216 25204142 25204148 8388608 (@Enclosure.Real.IsNear.recentre' qz81 Bool.false 151455147 16777216 29 16777216 151455147 16777216 29 16777216 (Ns222p614 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns222p616 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz81) 25204145 8388608 3 8388608 2791950 2791952 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz81) Bool.false 50408290 16777216 6 16777216 25204145 8388608 3 8388608 (Ns222p615 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns222p617 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz81)) Bool.false 5583902 16777216 2 16777216 2791951 8388608 1 8388608 (Ns222p616 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz82 := (@HMul.hMul Real Real Real qz343 qz341 qz428)

noncomputable abbrev qz675 := (@HMul.hMul Real Real Real qz848 qz869 qz869)

noncomputable abbrev qz435 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz675 qz670) qz639)

noncomputable abbrev qz83 := (Real.cos (@HMul.hMul Real Real Real qz343 qz341 qz435))

noncomputable def Ns222p618 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz77) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz82)) qz83) Bool.false 30252343398319 

noncomputable def Ns222p619 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz82)) qz83 4257379 4194304 49 

noncomputable def Ns222p620 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz82)) Bool.false 17029516 16777216 196 16777216 4257379 4194304 49 

noncomputable def Ns222p621 := @Enclosure.Real.IsNear.recentre' (Real.cos qz82) Bool.false 8264327 8388608 545647216 48486154240000 8264327 8388608 34102951 3030384640000 

noncomputable abbrev qz676 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable def Ns222p622 := @Enclosure.Real.IsNear.cos_image qz82 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 722885) qz676) Bool.false 722885 4194304 183 16777216 Bool.false 8264327 8388608 1 

noncomputable def Ns222p623 := nat_lit 782596186866230431868942219 

noncomputable def Ns222p624 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz77 884279719003555 140737488355328 1 500000000000000 460203 16777216 29 16777216 406948179524593021665 2361183241434822606848 Ns222p623 

noncomputable def Ns222p625 := @Enclosure.Real.IsNear.subLit_ff_p qz81 qz46 151455147 16777216 29 16777216 9 1 0 1 460203 460203 16777216 29 

noncomputable def Ns222p626 := @Ns222p625 16777216 (@Enclosure.Real.IsNear.recentre' qz81 Bool.false 151455147 16777216 29 16777216 151455147 16777216 29 16777216 (Ns222p614 rfl rfl rfl rfl rfl rfl) rfl) qz411 

noncomputable def Ns222p627 := @Enclosure.Real.IsNear.recentre' qz82 Bool.false 406948179524593021665 2361183241434822606848 Ns222p623 Ns222p150 722885 4194304 183 16777216 (@Ns222p624 Ns222p150 RS223to240.d39 (Ns222p626 rfl rfl) rfl) 

noncomputable def Ns222p628 := nat_lit 7427640235712281649394745344 

noncomputable def Ns222p629 := nat_lit 111414603535684224740921180160 

noncomputable def Ns222p630 := BSN.cos_dyadic_bound_f 722885 4194304 2 1 8388608 2890000 273071799704327954400625 Ns222p628 273071799704327954400625 273071799704327954400625 Ns222p629 273071799704327954400625 8264327 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 722885) (BSN.cosEvenQ 4194304) 0 1 273071799704327954400625 Ns222p628 273071799704327954400625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 722885) (BSN.cosOddQ 4194304) 0 1 273071799704327954400625 Ns222p629 273071799704327954400625 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p631 := @Enclosure.Real.IsNear.inv_image (Real.cos qz82) 8264327 8388608 34102951 3030384640000 8514660 8514856 8388608 (Ns222p621 (@Ns222p622 2890000 (Ns222p627 rfl) (Enclosure.sfrac_false_div 722885 4194304) (Ns222p630 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns222p632 := @Enclosure.Real.IsNear.recentre' qz83 Bool.false 7105861 8388608 

noncomputable abbrev qz84 := (@HMul.hMul Real Real Real qz343 qz341 qz435)

noncomputable def Ns222p633 := @Enclosure.Real.IsNear.cos_image qz84 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 4700311)) qz370) Bool.true 4700311 8388608 

noncomputable def Ns222p634 := nat_lit 22196592067643560374708985525 

noncomputable def Ns222p635 := nat_lit 13850114189234987777297846726077553 

noncomputable def Ns222p636 := @Enclosure.Real.IsNear.recentre' qz84 Bool.true Ns222p634 Ns222p168 Ns222p635 

noncomputable abbrev qz85 := qz435

noncomputable def Ns222p637 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz85 884279719003555 140737488355328 1 500000000000000 25101324378055 

noncomputable abbrev qz436 := (@HSub.hSub Real Real Real qz634 qz675 qz670)

noncomputable abbrev qz86 := qz436

noncomputable def Ns222p638 := @Enclosure.Real.IsNear.subLit_tf qz86 qz25 7509138333639 281474976710656 513231879 281474976710656 1 16 

noncomputable abbrev qz437 := qz675

noncomputable abbrev qz87 := qz437

noncomputable def Ns222p639 := @Enclosure.Real.IsNear.subLit_ff_n qz87 qz77 211786801209 281474976710656 26692615 281474976710656 460203 16777216 29 16777216 

noncomputable def Ns222p640 := @Enclosure.Real.IsNear.mulLit_ff qz77 qz77 460203 16777216 29 16777216 460203 16777216 29 16777216 211786801209 281474976710656 

noncomputable def Ns222p641 := nat_lit 4060698459747556733445036131376645757024747901508058589761 

noncomputable def Ns222p642 := nat_lit 988643523323402220304136834155207460536120982503085435781120 

noncomputable def Ns222p643 := nat_lit 238238943645986417817016995896511301332325105618889281 

noncomputable def Ns222p644 := nat_lit 12181618901355378227499474360138144248471579054312937990721 

noncomputable def Ns222p645 := nat_lit 44488958549553099913686157536984335724125444212638844610150400 

noncomputable def Ns222p646 := BSN.cos_dyadic_bound_f 4700311 8388608 3 2 8388608 2890000 Ns222p641 Ns222p642 Ns222p643 Ns222p644 Ns222p645 Ns222p643 7105861 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 4700311) (BSN.cosEvenQ 8388608) 0 2 Ns222p641 Ns222p642 Ns222p643 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 4700311) (BSN.cosOddQ 8388608) 0 2 Ns222p644 Ns222p645 Ns222p643 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p647 := @Ns222p632 574547216 48486154240000 7105861 8388608 35909201 3030384640000 (@Ns222p633 193 16777216 Bool.false 7105861 8388608 1 2890000 (@Ns222p636 Ns222p532 4700311 8388608 193 16777216 (@Ns222p637 281474976710656 513231879 281474976710656 Ns222p634 Ns222p168 Ns222p635 Ns222p532 RS223to240.d39 (@Ns222p638 0 1 401621190048880 25101324378055 281474976710656 513231879 281474976710656 (@Ns222p639 125982435797341569024 7509138333639 281474976710656 513231879 281474976710656 (@Ns222p640 26692615 281474976710656 (Ns222p626 rfl rfl) (Ns222p626 rfl rfl) rfl) (Ns222p626 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 4700311 8388608) (BSN.cos_neg_of_bound 4700311 8388608 Bool.false 7105861 8388608 1 2890000 (Ns222p646 rfl rfl)) rfl rfl) 

noncomputable def Ns222p648 := @Ns222p612 394471831513789746703 Ns222p542 (Ns222p613 qz61 (@Enclosure.Real.IsNear.of_eq qz673 (@Inv.inv Real Real.instInv (Real.sqrt qz81)) Bool.false 2791951 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz76 (BSN.t_div_two_pi_nonneg qz75 512045 1000 qz78)) Ns222p617) rfl) (@Ns222p618 35184372088832 139331729910639 6355177208545280000 (BSN.correction_mk qz77 (BSN.cos_two_pi_p_ne_zero_mk qz75 512045 1000 9 qz78 rfl rfl (@BSN.floor_sqrt_eq_dec qz75 512045 1000 9 qz78 rfl rfl rfl))) (@Ns222p619 4194304 7105861 8388608 35909201 3030384640000 30252343398319 35184372088832 139331729910639 6355177208545280000 (@Ns222p620 4194304 (Ns222p631 rfl rfl rfl rfl rfl) rfl) (Ns222p647 rfl) rfl)) 

noncomputable def Ns222p649 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz75) (hardyZApproximantRS₀ qz75) Bool.true 211391144657476931263 295147905179352825856 77986419164945249586703 Ns222p542 (@Eq.refl Real (hardyZApproximantRS₀ qz75)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz75) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz75) qz75 9) (@HMul.hMul Real Real Real qz4 qz671 (Zeta.RiemannSiegel.correction qz77))) Bool.true 211391144657476931263 295147905179352825856 77986419164945249586703 Ns222p542 (BSN.hardyZApproximantRS₀_eq qz75 9 (@BSN.floor_sqrt_eq_dec qz75 512045 1000 9 qz78 rfl rfl rfl)) (@Ns222p544 211391144657476931263 295147905179352825856 77986419164945249586703 Ns222p542 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz75) qz75 9) (@HAdd.hAdd Real Real Real qz358 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz75) qz75 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz75) qz75 9)) Bool.true 33634729 33554432 48837 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz75) qz75 9) (Ns222p611 (Ns222p610 rfl) rfl rfl)) (Ns222p648 rfl) rfl rfl)) 

theorem RS223to240.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz75) Bool.true 211391144657476931263 295147905179352825856 77986419164945249586703 Ns222p542 := Ns222p649 

noncomputable def Ns222p650 := nat_lit 4264887229841648333619200 

noncomputable def Ns222p651 := nat_lit 21738098611155268748600934400 

noncomputable abbrev qz871 := (Enclosure.sfrac Bool.false 513472 1000)

noncomputable abbrev qz677 := qz871

noncomputable abbrev qz438 := qz677

noncomputable abbrev qz88 := qz438

noncomputable abbrev qz872 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 513472 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz678 := qz872

noncomputable abbrev qz439 := qz678

noncomputable abbrev qz89 := qz439

noncomputable abbrev qz873 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 513472 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz679 := qz873

noncomputable abbrev qz440 := qz679

noncomputable abbrev qz90 := qz440

noncomputable abbrev qz680 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz89 qz8))

noncomputable def Ns222p652 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz88) qz88 9) (@HMul.hMul Real Real Real qz4 qz680 (Zeta.RiemannSiegel.correction qz90)) 18259667 67108864 24487 16777216 163309181966038837989 590295810358705651712 31761864210090961287 Ns222p650 Ns222p651 

noncomputable def Ns222p653 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz88) qz88 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 513472 1000 123 162 134217728 67108864 2251799813685248 Bool.false 117220623350 1785 

noncomputable def Ns222p654 := Ns222p653 279097919 47 47453128 8 294906479 47 44739240 8 Bool.false 16158969 80126 Bool.true 156411476 Bool.true 51344545 7074237752028440 1 Bool.false 123336553 Bool.false Bool.false 124516069 Bool.true Bool.false 18259667 

noncomputable def Ns222p655 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz88) qz88 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 513472 1000 29 80 134217728 67108864 2251799813685248 Bool.false 117220623350 1785 

noncomputable def Ns222p656 := Ns222p655 240485871 47 54794152 8 261175631 47 50729528 8 Bool.false 14880217 59729 Bool.true 148105094 Bool.true 19453120 7074237752028440 1 Bool.false 119826298 Bool.true Bool.false 132810455 Bool.false Bool.false 16158969 

noncomputable def Ns222p657 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz88) qz88 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 513472 1000 102 29 134217728 67108864 2251799813685248 Bool.false 117220623350 1785 

noncomputable def Ns222p658 := Ns222p657 186065264 47 67108856 8 216015088 47 60023992 8 Bool.false 90941121 35159 Bool.false 176791271 Bool.false 188891374 7074237752028440 1 Bool.false 33673776 Bool.true Bool.false 132428931 Bool.true Bool.false 14880217 

noncomputable def Ns222p659 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz88) qz88 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 513472 1000 329 196 134217728 67108864 2251799813685248 Bool.false 117220623350 1785 

noncomputable def Ns222p660 := Ns222p659 93032624 47 94906264 8 147453232 47 77490640 16 Bool.false 134217648 1839 Bool.false 88328889 Bool.false 185089438 7074237752028440 1 Bool.false 82089703 Bool.true Bool.false 25581798 Bool.false Bool.false 90941121 

noncomputable def Ns222p661 := nat_lit 9899615556861596346800401793157011859348345184105753 

noncomputable def Ns222p662 := nat_lit 11335069462499074831189959553080491900399517696000 

noncomputable def Ns222p663 := nat_lit 17132711884226481865418785423360000 

noncomputable def Ns222p664 := nat_lit 52783030376299632858438228969837035520 

noncomputable abbrev qz441 := (@Eq.refl Real qz677)

noncomputable abbrev qz91 := qz441

noncomputable def Ns222p665 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz88 513472 1000 1054614979136 16000000 1026944 4000 2000 Ns222p663 Ns222p664 qz91 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns222p666 := nat_lit 12975624102689631563678222638326758584285062999711092572160 

noncomputable abbrev qz442 := (Enclosure.sfrac Bool.false 513472 2000)

noncomputable abbrev qz681 := (Real.log (Enclosure.sfrac Bool.false 1054614979136 16000000))

noncomputable abbrev qz92 := (@HSub.hSub Real Real Real qz347 (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 513472 4000) qz681) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1026944)))))) qz442)

noncomputable abbrev qz443 := (@HSub.hSub Real Real Real qz11 qz92 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 513472 2000) (Real.log Real.pi)))

noncomputable def Ns222p667 := @Enclosure.Real.IsNear.addLit_ft_p qz443 (Enclosure.sfrac Bool.true Ns222p663 Ns222p664) 245829556064017895033 281474976710656000 122906709962309099 9248000000000000000000 Ns222p663 Ns222p664 0 1 Ns222p666 

noncomputable def Ns222p668 := nat_lit 257770972579383628302123008000 

noncomputable abbrev qz444 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 513472 2000) (Real.log Real.pi))

noncomputable def Ns222p669 := @Enclosure.Real.IsNear.subLit_ff_p qz92 qz444 328553185852073889401 281474976710656000 1629600593609757 289000000000000000000 308169535503 1048576000 8023 1048576000 Ns222p668 245829556064017895033 281474976710656000 

noncomputable abbrev qz93 := (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 513472 4000) qz681) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1026944))))))

noncomputable def Ns222p670 := @Enclosure.Real.IsNear.subLit_ff_p qz93 qz442 400817945472860868217 281474976710656000 1629600593609757 289000000000000000000 513472 2000 0 1 657106371704147778802000 328553185852073889401 281474976710656000 1629600593609757 289000000000000000000 

noncomputable def Ns222p671 := nat_lit 56410110933593249695340325477810176 

noncomputable def Ns222p672 := nat_lit 26828717705843187958939648 

noncomputable def Ns222p673 := nat_lit 13270236884157139161919488 

noncomputable def Ns222p674 := BSN.log_dyadic_bound 6038979136 2103190979136 2 1 Ns222p673 67108864 23120000 36469269005043306496 36469269005043306496 385385 2109229958272 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 6038979136) (BSN.artanhQ 2103190979136) 0 1 36469269005043306496 Ns222p673 36469269005043306496 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns222p675 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 513472 4000) qz681 513472 4000 0 1 3123273805929719 281474976710656 781250289 18062500000000000 25058025744974135537 17592186044416000 6267971068647 1128906250000000000 (Enclosure.Real.IsNear.const Bool.false 513472 4000) (BSN.isNear_log_sfrac 1054614979136 16000000 3123273805929719 281474976710656 781250289 18062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1054614979136) qz354)) Bool.false Ns222p672 Ns222p89 1000000369920000 23120000000000000000000 3123273805929719 281474976710656 781250289 18062500000000000 (BSN.log_rat_reduce_isNear 1054614979136 16000000 16 2109229958272 2097152000000 385385 67108864 24973259072661432 36028797018963968 23120000 1000000000000000 rfl rfl rfl rfl (Ns222p674 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns222p676 := BSN.arctan_dyadic_bound_f 1000 1026944 1 0 8388608 2890000 0 1 1 0 1 1 8168 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1026944) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1026944) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz445 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1026944)))

noncomputable def Ns222p677 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz445 884279719003555 562949953421312 1 2000000000000000 8168 8388608 1 2890000 7413277749851428225024 883731573802403 562949953421312 200000000289 578000000000000000 qz16 (Ns222p676 rfl) rfl rfl 

noncomputable def Ns222p678 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 513472 4000) qz681) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz445)) 25058025744974135537 17592186044416000 6267971068647 1128906250000000000 883731573802403 2251799813685248 200000000289 2312000000000000000 Ns222p671 400817945472860868217 281474976710656000 1629600593609757 289000000000000000000 (Ns222p675 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz445) 1 4 0 1 883731573802403 562949953421312 200000000289 578000000000000000 883731573802403 2251799813685248 200000000289 2312000000000000000 qz357 Ns222p677 rfl) 

noncomputable def Ns222p679 := @Ns222p667 Ns222p661 Ns222p662 122906709962309099 9248000000000000000000 (@Ns222p669 122906709962309099 9248000000000000000000 (Ns222p670 (Ns222p678 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 513472 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz442 (Real.log Real.pi) 513472 2000 0 1 38410761 33554432 1 33554432 308169535503 1048576000 8023 1048576000 (Enclosure.Real.IsNear.const Bool.false 513472 2000) RS223to240.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns222p663 Ns222p664) 

noncomputable def Ns222p680 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz88) Bool.false Ns222p661 Ns222p662 122906709962309099 9248000000000000000000 7326288959 8388608 7 524288 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz88) (@HAdd.hAdd Real Real Real qz358 qz443 (Enclosure.sfrac Bool.true Ns222p663 Ns222p664)) Bool.false Ns222p661 Ns222p662 122906709962309099 9248000000000000000000 Ns222p665 (Ns222p679 rfl rfl)) 

noncomputable def Ns222p681 := nat_lit 1897699790267414424322048 

noncomputable def Ns222p682 := nat_lit 854830685991956842889466685489745612022643315527340324082356116464385724726192289143387506201248660527515120962758564436777588775390625 

noncomputable def Ns222p683 := nat_lit 606083493929124745328753754855373431599766793817111718613084140535970793561241091940981786360737978478755617675840854644775390625 

noncomputable def Ns222p684 := nat_lit 4268856510582115019388515334942440868071157740154523212534358894347025533988228782848957234810730081264330947736678816420469364775390625 

noncomputable def Ns222p685 := BSN.sin_dyadic_bound_f 53935872025 34359738368 4 3 16777216 5785645 Ns222p682 Ns222p574 Ns222p683 Ns222p684 Ns222p577 Ns222p683 16777206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53935872025) qz371 0 3 Ns222p682 Ns222p574 Ns222p683 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53935872025) qz372 0 3 Ns222p684 Ns222p577 Ns222p683 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p686 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz88) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7326288959) qz370) Bool.false 7326288959 8388608 7 524288 Bool.false 16777206 16777216 1 2890000 (Ns222p680 rfl) (Enclosure.sfrac_false_div 7326288959 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7326288959) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns222p681) qz640) 226375608064910080 72057594037927936 Bool.false 16777206 16777216 138 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q3 7326288959 8388608 226375608064910080 72057594037927936 138 Ns222p681 Ns222p156 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777206 16777216 Ns222p681 Ns222p156 53935872025 34359738368 5785645 5780000 (Ns222p685 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p687 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz88) Bool.false Ns222p661 Ns222p662 122906709962309099 9248000000000000000000 117220623350 134217728 1785 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz88) (@HAdd.hAdd Real Real Real qz358 qz443 (Enclosure.sfrac Bool.true Ns222p663 Ns222p664)) Bool.false Ns222p661 Ns222p662 122906709962309099 9248000000000000000000 Ns222p665 (Ns222p679 rfl rfl)) 

noncomputable def Ns222p688 := Ns222p660 35159 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 329 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 82089703 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 196 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 25581798 134217728) qz91 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz88) qz88 1) Bool.false 8388603 8388608 1297143 94699520000 134217648 134217728 1839 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz88) qz88 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz88)) Bool.false 8388603 8388608 1297143 94699520000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz88) qz88) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz88)) Bool.false 16777206 16777216 20754288 1515192320000 8388603 8388608 1297143 94699520000 (Ns222p686 rfl rfl) rfl)) rfl) (Ns222p687 rfl) RS223to240.d7 

noncomputable def Ns222p689 := nat_lit 59739189750278623226767455792724765613739403019779989268818996411585 

noncomputable def Ns222p690 := nat_lit 3705289479622900087615264533196650840872980558224757760000703681 

noncomputable def Ns222p691 := nat_lit 156453783639191290422344340457415877267956070702329512762914513272001 

noncomputable def Ns222p692 := BSN.sin_dyadic_bound_f 88328889 134217728 3 2 134217728 67108864 Ns222p689 Ns222p124 Ns222p690 Ns222p691 Ns222p127 Ns222p690 82089703 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 88328889) qz363 0 2 Ns222p689 Ns222p124 Ns222p690 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 88328889) qz364 0 2 Ns222p691 Ns222p127 Ns222p690 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p693 := nat_lit 2472096986751443899896014209787109186020395412059589442367387472688698303944278938533364266799645742862336 

noncomputable def Ns222p694 := nat_lit 1616514635561967402171681639484329975228030743184410882066879770397172293782165878286872001240109056 

noncomputable def Ns222p695 := nat_lit 14975903476671800357224652761572974408674625110929673582808265972706299648190497467345644849151923454218240 

noncomputable def Ns222p696 := BSN.cos_dyadic_bound_f 185089438 134217728 4 3 134217728 67108864 Ns222p693 Ns222p227 Ns222p694 Ns222p695 Ns222p230 Ns222p694 25581798 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 185089438) qz361 0 3 Ns222p693 Ns222p227 Ns222p694 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 185089438) qz362 0 3 Ns222p695 Ns222p230 Ns222p694 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p697 := nat_lit 2056959478467725531505075325238536063925563840965635169427050394461377842851470729809082450972714003913121 

noncomputable def Ns222p698 := nat_lit 932244472554172478323347673350753014615681144393107467606687812052688424239318681281363974111156641 

noncomputable def Ns222p699 := nat_lit 12464002832094870564711468569134336918637638283974090536273904836368405003799781772627690212486656947181985 

noncomputable def Ns222p700 := BSN.cos_dyadic_bound_f 176791271 134217728 4 3 134217728 67108864 Ns222p697 Ns222p227 Ns222p698 Ns222p699 Ns222p230 Ns222p698 33673776 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 176791271) qz361 0 3 Ns222p697 Ns222p227 Ns222p698 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 176791271) qz362 0 3 Ns222p699 Ns222p230 Ns222p698 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p701 := nat_lit 6966101419640121011106376429552230388400243276324071920240990307852729965613278874679167830814301908504576 

noncomputable def Ns222p702 := nat_lit 2063219853611656772791080122592402401694882183336907344728465422777385441524672168583854613674725376 

noncomputable def Ns222p703 := nat_lit 34802602966193764869522188300274622276964839317311797457602654130501903545236546203897732277303751828443136 

noncomputable def Ns222p704 := BSN.sin_dyadic_bound_f 188891374 134217728 4 3 134217728 67108864 Ns222p701 Ns222p111 Ns222p702 Ns222p703 Ns222p114 Ns222p702 132428931 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 188891374) qz363 0 3 Ns222p701 Ns222p111 Ns222p702 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 188891374) qz364 0 3 Ns222p703 Ns222p114 Ns222p702 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p705 := Ns222p658 59729 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 102 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 33673776 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 29 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132428931 134217728) qz91 rfl rfl (Ns222p688 RS223to240.d9 RS223to240.d11 RS223to240.d13 RS223to240.d17 (Ns222p692 rfl rfl) (Ns222p696 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns222p687 rfl) RS223to240.d19 RS223to240.d21 RS223to240.d23 RS223to240.d25 RS223to240.d17 (Ns222p700 rfl rfl) (Ns222p704 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns222p706 := nat_lit 472404671749320058991528383409831527449736429373861439981501878083840 

noncomputable def Ns222p707 := nat_lit 231504783406517530540588270022560293185544118533186071437343170816 

noncomputable def Ns222p708 := nat_lit 1236875513503656268975984813636188902846056910263440517740653982228736 

noncomputable def Ns222p709 := BSN.sin_dyadic_bound_f 148105094 134217728 3 2 134217728 67108864 Ns222p706 Ns222p124 Ns222p707 Ns222p708 Ns222p127 Ns222p707 119826298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 148105094) qz363 0 2 Ns222p706 Ns222p124 Ns222p707 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 148105094) qz364 0 2 Ns222p708 Ns222p127 Ns222p707 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p710 := nat_lit 143204631239540120076943360000 

noncomputable def Ns222p711 := BSN.cos_dyadic_bound_f 19453120 134217728 2 1 134217728 67108864 Ns222p710 Ns222p246 Ns222p710 Ns222p710 Ns222p247 Ns222p710 132810455 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 19453120) qz361 0 1 Ns222p710 Ns222p246 Ns222p710 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 19453120) qz362 0 1 Ns222p710 Ns222p247 Ns222p710 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p712 := Ns222p656 80126 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 29 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 119826298 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 80 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 132810455 134217728) qz91 rfl rfl (Ns222p705 rfl rfl) (Ns222p687 rfl) RS223to240.d27 RS223to240.d29 RS223to240.d31 RS223to240.d33 RS223to240.d17 (Ns222p709 rfl rfl) (Ns222p711 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p713 := nat_lit 587706600080642154644016255927490885181081996062827192161496553553920 

noncomputable def Ns222p714 := nat_lit 358219245345688327151234169123440420298472335083940333534723506176 

noncomputable def Ns222p715 := nat_lit 1538651597623503100109416767345800081460445796383935314168672849821696 

noncomputable def Ns222p716 := BSN.sin_dyadic_bound_f 156411476 134217728 3 2 134217728 67108864 Ns222p713 Ns222p124 Ns222p714 Ns222p715 Ns222p127 Ns222p714 123336553 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 156411476) qz363 0 2 Ns222p713 Ns222p124 Ns222p714 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 156411476) qz364 0 2 Ns222p715 Ns222p127 Ns222p714 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p717 := nat_lit 3789060922146919793620538463053181229800061738435035795629829690625 

noncomputable def Ns222p718 := nat_lit 48300817016963012014835898821149842104524749970129312312890625 

noncomputable def Ns222p719 := nat_lit 11367086164806725454837585717361901389715976165805167128264863290625 

noncomputable def Ns222p720 := BSN.cos_dyadic_bound_f 51344545 134217728 3 2 134217728 67108864 Ns222p717 Ns222p105 Ns222p718 Ns222p719 Ns222p108 Ns222p718 124516069 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 51344545) qz361 0 2 Ns222p717 Ns222p105 Ns222p718 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 51344545) qz362 0 2 Ns222p719 Ns222p108 Ns222p718 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p721 := Ns222p654 97948 BSN.abs_quadSignPos qz664 (BSN.sfrac_eq_quadSignPos_mul Bool.false 123336553 134217728) BSN.abs_quadSignNeg qz408 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 124516069 134217728) qz91 rfl rfl (Ns222p712 rfl) (Ns222p687 rfl) RS223to240.d35 RS223to240.d37 RS223to240.d46 RS223to240.d48 RS223to240.d17 (Ns222p716 rfl rfl) (Ns222p720 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p722 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz88) qz88 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz88) qz88 9) 18259667 134217728 97948 134217728 18259667 134217728 97948 134217728 4901542037553152 18259667 67108864 24487 16777216 (Ns222p721 rfl) 

noncomputable def Ns222p723 := @Enclosure.Real.IsNear.mulLit_tf qz680 (Zeta.RiemannSiegel.correction qz90) 5580019 16777216 1 16777216 29266778834631 35184372088832 14135438463039 635517720854528000 163309181966038837989 590295810358705651712 

noncomputable abbrev qz682 := (@HPow.hPow Real Real Real qz6 qz89 qz8)

noncomputable def Ns222p724 := @Enclosure.Real.IsNear.mulLit_tf qz48 qz682 1 1 0 1 5580019 16777216 1 16777216 5580019 16777216 1 16777216 

noncomputable def Ns222p725 := @Enclosure.Real.IsNear.sqrt_image qz89 21422830071 262144000 8023 262144000 75833007 75833036 8388608 (@Enclosure.Real.IsNear.of_eq qz89 (@HMul.hMul Real Real Real qz4 qz88 qz2) Bool.false 21422830071 262144000 8023 262144000 (BSN.t_div_two_pi_mk qz88 513472 1000 qz91) (@Enclosure.Real.IsNear.mulLit_ff qz88 qz2 513472 1000 0 1 2670177 16777216 1 16777216 21422830071 262144000 8023 262144000 (Enclosure.Real.IsNear.const Bool.false 513472 1000) RS223to240.d40 rfl)) 

noncomputable abbrev qz874 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 513472 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz683 := qz874

noncomputable abbrev qz446 := qz683

noncomputable abbrev qz94 := qz446

noncomputable def Ns222p726 := @Enclosure.Real.IsNear.sqrt_image qz94 151666043 16777216 29 16777216 25221684 25221690 8388608 (@Enclosure.Real.IsNear.recentre' qz94 Bool.false 151666043 16777216 29 16777216 151666043 16777216 29 16777216 (Ns222p725 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns222p727 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz94) 25221687 8388608 3 8388608 2790009 2790010 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz94) Bool.false 50443374 16777216 6 16777216 25221687 8388608 3 8388608 (Ns222p726 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns222p728 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz94)) Bool.false 5580019 16777216 1 16777216 5580019 16777216 1 16777216 (Ns222p727 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz95 := (@HMul.hMul Real Real Real qz343 qz341 qz440)

noncomputable abbrev qz684 := (@HMul.hMul Real Real Real qz848 qz873 qz873)

noncomputable abbrev qz447 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz684 qz679) qz639)

noncomputable abbrev qz96 := (Real.cos (@HMul.hMul Real Real Real qz343 qz341 qz447))

noncomputable def Ns222p729 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz90) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz95)) qz96) Bool.false 29266778834631 

noncomputable def Ns222p730 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz95)) qz96 8660709 8388608 101 

noncomputable def Ns222p731 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz95)) Bool.false 17321418 16777216 202 16777216 8660709 8388608 101 

noncomputable def Ns222p732 := @Enclosure.Real.IsNear.recentre' (Real.cos qz95) Bool.false 8125056 8388608 545647216 48486154240000 63477 65536 34102951 3030384640000 

noncomputable def Ns222p733 := @Enclosure.Real.IsNear.cos_image qz95 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4216639) qz359) Bool.false 4216639 16777216 183 16777216 Bool.false 8125056 8388608 1 

noncomputable def Ns222p734 := nat_lit 782596186868042014714656651 

noncomputable def Ns222p735 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz90 884279719003555 140737488355328 1 500000000000000 671099 16777216 29 16777216 593439235143566756945 2361183241434822606848 Ns222p734 

noncomputable def Ns222p736 := @Enclosure.Real.IsNear.subLit_ff_p qz94 qz46 151666043 16777216 29 16777216 9 1 0 1 671099 671099 16777216 29 

noncomputable def Ns222p737 := @Ns222p736 16777216 (@Enclosure.Real.IsNear.recentre' qz94 Bool.false 151666043 16777216 29 16777216 151666043 16777216 29 16777216 (Ns222p725 rfl rfl rfl rfl rfl rfl) rfl) qz411 

noncomputable def Ns222p738 := @Enclosure.Real.IsNear.recentre' qz95 Bool.false 593439235143566756945 2361183241434822606848 Ns222p734 Ns222p150 4216639 16777216 183 16777216 (@Ns222p735 Ns222p150 RS223to240.d39 (Ns222p737 rfl rfl) rfl) 

noncomputable def Ns222p739 := nat_lit 316129980868751124476855041 

noncomputable def Ns222p740 := BSN.cos_dyadic_bound_f 4216639 16777216 2 1 8388608 2890000 Ns222p739 Ns222p287 Ns222p739 Ns222p739 Ns222p288 Ns222p739 8125056 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 4216639) qz391 0 1 Ns222p739 Ns222p287 Ns222p739 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 4216639) (BSN.cosOddQ 16777216) 0 1 Ns222p739 Ns222p288 Ns222p739 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p741 := @Enclosure.Real.IsNear.inv_image (Real.cos qz95) 63477 65536 34102951 3030384640000 8660608 8660810 8388608 (Ns222p732 (@Ns222p733 2890000 (Ns222p738 rfl) (Enclosure.sfrac_false_div 4216639 16777216) (Ns222p740 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns222p742 := @Enclosure.Real.IsNear.recentre' qz96 Bool.false 6758518 8388608 

noncomputable abbrev qz97 := (@HMul.hMul Real Real Real qz343 qz341 qz447)

noncomputable def Ns222p743 := @Enclosure.Real.IsNear.cos_image qz97 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 664773)) qz645) Bool.true 664773 1048576 

noncomputable def Ns222p744 := nat_lit 25114415085627240205158631445 

noncomputable def Ns222p745 := nat_lit 14180207000112345321303942236645457 

noncomputable def Ns222p746 := @Enclosure.Real.IsNear.recentre' qz97 Bool.true Ns222p744 Ns222p168 Ns222p745 

noncomputable abbrev qz98 := qz447

noncomputable def Ns222p747 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz98 884279719003555 140737488355328 1 500000000000000 28400985056999 

noncomputable abbrev qz448 := (@HSub.hSub Real Real Real qz634 qz684 qz679)

noncomputable abbrev qz99 := qz448

noncomputable def Ns222p748 := @Enclosure.Real.IsNear.subLit_tf qz99 qz25 10808799012583 281474976710656 525463847 281474976710656 1 16 

noncomputable abbrev qz449 := qz684

noncomputable abbrev qz100 := qz449

noncomputable def Ns222p749 := @Enclosure.Real.IsNear.subLit_ff_n qz100 qz90 450373867801 281474976710656 38924583 281474976710656 671099 16777216 29 16777216 

noncomputable def Ns222p750 := @Enclosure.Real.IsNear.mulLit_ff qz90 qz90 671099 16777216 29 16777216 671099 16777216 29 16777216 450373867801 281474976710656 

noncomputable def Ns222p751 := nat_lit 396683541680575614419653657684910149736630334088161 

noncomputable def Ns222p752 := nat_lit 58927746017182005661972572455120531352527200132792320 

noncomputable def Ns222p753 := nat_lit 38140552230666756969503874451634375174266381281 

noncomputable def Ns222p754 := nat_lit 1189974343937265509745021965305827180459542469501921 

noncomputable def Ns222p755 := nat_lit 2651748570773190254788765760480423910863724005975654400 

noncomputable def Ns222p756 := BSN.cos_dyadic_bound_f 664773 1048576 3 2 8388608 2890000 Ns222p751 Ns222p752 Ns222p753 Ns222p754 Ns222p755 Ns222p753 6758518 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 664773) (BSN.cosEvenQ 1048576) 0 2 Ns222p751 Ns222p752 Ns222p753 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 664773) (BSN.cosOddQ 1048576) 0 2 Ns222p754 Ns222p755 Ns222p753 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p757 := @Ns222p742 294498608 24243077120000 3379259 4194304 18406163 1515192320000 (@Ns222p743 99 8388608 Bool.false 6758518 8388608 1 2890000 (@Ns222p746 Ns222p532 664773 1048576 99 8388608 (@Ns222p747 281474976710656 525463847 281474976710656 Ns222p744 Ns222p168 Ns222p745 Ns222p532 RS223to240.d39 (@Ns222p748 0 1 454415760911984 28400985056999 281474976710656 525463847 281474976710656 (@Ns222p749 181341555734691708928 10808799012583 281474976710656 525463847 281474976710656 (@Ns222p750 38924583 281474976710656 (Ns222p737 rfl rfl) (Ns222p737 rfl rfl) rfl) (Ns222p737 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 664773 1048576) (BSN.cos_neg_of_bound 664773 1048576 Bool.false 6758518 8388608 1 2890000 (Ns222p756 rfl rfl)) rfl rfl) 

noncomputable def Ns222p758 := @Ns222p723 31761864210090961287 Ns222p650 (Ns222p724 qz61 (@Enclosure.Real.IsNear.of_eq qz682 (@Inv.inv Real Real.instInv (Real.sqrt qz94)) Bool.false 5580019 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz89 (BSN.t_div_two_pi_nonneg qz88 513472 1000 qz91)) Ns222p728) rfl) (@Ns222p729 35184372088832 14135438463039 635517720854528000 (BSN.correction_mk qz90 (BSN.cos_two_pi_p_ne_zero_mk qz88 513472 1000 9 qz91 rfl rfl (@BSN.floor_sqrt_eq_dec qz88 513472 1000 9 qz91 rfl rfl rfl))) (@Ns222p730 8388608 3379259 4194304 18406163 1515192320000 29266778834631 35184372088832 14135438463039 635517720854528000 (@Ns222p731 8388608 (Ns222p741 rfl rfl rfl rfl rfl) rfl) (Ns222p757 rfl) rfl)) 

noncomputable def Ns222p759 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz88) (hardyZApproximantRS₀ qz88) Bool.false 323922911452580522725 590295810358705651712 6256530836436021815687 Ns222p650 (@Eq.refl Real (hardyZApproximantRS₀ qz88)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz88) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz88) qz88 9) (@HMul.hMul Real Real Real qz4 qz680 (Zeta.RiemannSiegel.correction qz90))) Bool.false 323922911452580522725 590295810358705651712 6256530836436021815687 Ns222p650 (BSN.hardyZApproximantRS₀_eq qz88 9 (@BSN.floor_sqrt_eq_dec qz88 513472 1000 9 qz91 rfl rfl rfl)) (@Ns222p652 323922911452580522725 590295810358705651712 6256530836436021815687 Ns222p650 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz88) qz88 9) (@HAdd.hAdd Real Real Real qz358 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz88) qz88 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz88) qz88 9)) Bool.false 18259667 67108864 24487 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz88) qz88 9) (Ns222p722 (Ns222p721 rfl) rfl rfl)) (Ns222p758 rfl) rfl rfl)) 

theorem RS223to240.d52 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz88) Bool.false 323922911452580522725 590295810358705651712 6256530836436021815687 Ns222p650 := Ns222p759 

noncomputable def Ns222p760 := nat_lit 8529774459683296667238400 

noncomputable def Ns222p761 := nat_lit 14481653353413491490899886080 

noncomputable abbrev qz875 := (Enclosure.sfrac Bool.false 514899 1000)

noncomputable abbrev qz685 := qz875

noncomputable abbrev qz450 := qz685

noncomputable abbrev qz101 := qz450

noncomputable abbrev qz876 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 514899 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz686 := qz876

noncomputable abbrev qz451 := qz686

noncomputable abbrev qz102 := qz451

noncomputable abbrev qz877 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 514899 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz687 := qz877

noncomputable abbrev qz452 := qz687

noncomputable abbrev qz103 := qz452

noncomputable abbrev qz688 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz102 qz8))

noncomputable def Ns222p762 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz101) qz101 9) (@HMul.hMul Real Real Real qz4 qz688 (Zeta.RiemannSiegel.correction qz103)) 13388261 4194304 98217 67108864 315765237608961649821 1180591620717411303424 66822709490529208961 Ns222p760 Ns222p761 

noncomputable def Ns222p763 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz101) qz101 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 514899 1000 123 162 134217728 67108864 2251799813685248 Bool.false 117642437362 1790 

noncomputable def Ns222p764 := Ns222p763 279097919 47 47453128 8 294906479 47 44739240 8 Bool.true 212256697 80345 Bool.true 132870194 Bool.true 50362079 7074237752028440 1 Bool.false 112206568 Bool.false Bool.false 124879469 Bool.true Bool.true 214212176 

noncomputable def Ns222p765 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz101) qz101 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 514899 1000 29 79 134217728 67108864 2251799813685248 Bool.false 117642437362 1790 

noncomputable def Ns222p766 := Ns222p765 240485871 47 54794152 8 261175631 47 50729528 8 Bool.true 234642767 59891 Bool.true 69464420 Bool.true 181165447 7074237752028440 1 Bool.false 66404585 Bool.true Bool.false 130953130 Bool.false Bool.true 212256697 

noncomputable def Ns222p767 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz101) qz101 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 514899 1000 103 30 134217728 67108864 2251799813685248 Bool.false 117642437362 1790 

noncomputable def Ns222p768 := Ns222p767 186065264 47 67108856 8 216015088 47 60023992 8 Bool.true 241090272 35252 Bool.false 122261437 Bool.false 91623141 7074237752028440 1 Bool.false 106041031 Bool.false Bool.false 104140403 Bool.true Bool.true 234642767 

noncomputable def Ns222p769 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz101) qz101 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 514899 1000 330 197 134217728 67108864 2251799813685248 Bool.false 117642437362 1790 

noncomputable def Ns222p770 := Ns222p769 93032624 47 94906264 8 147453232 47 77490640 16 Bool.true 134217720 1839 Bool.false 166556633 Bool.false 185658974 7074237752028440 1 Bool.false 43473616 Bool.true Bool.false 131864605 Bool.true Bool.true 241090272 

noncomputable def Ns222p771 := nat_lit 18390241520219492203439928359113408418710512796693979809 

noncomputable def Ns222p772 := nat_lit 20981343888759019182967208846286475571260265857024000 

noncomputable def Ns222p773 := nat_lit 17372107842052966726999283759520000 

noncomputable def Ns222p774 := nat_lit 53669309351912253489076897385694530880 

noncomputable abbrev qz453 := (@Eq.refl Real qz685)

noncomputable abbrev qz104 := qz453

noncomputable def Ns222p775 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz101 514899 1000 1060484920804 16000000 1029798 4000 2000 Ns222p773 Ns222p774 qz104 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns222p776 := nat_lit 52963895578232137545906993674246616245886276854478661849920 

noncomputable abbrev qz454 := (Enclosure.sfrac Bool.false 514899 2000)

noncomputable abbrev qz689 := (Real.log (Enclosure.sfrac Bool.false 1060484920804 16000000))

noncomputable abbrev qz105 := (@HSub.hSub Real Real Real qz347 (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 514899 4000) qz689) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1029798)))))) qz454)

noncomputable abbrev qz455 := (@HSub.hSub Real Real Real qz11 qz105 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 514899 2000) (Real.log Real.pi)))

noncomputable def Ns222p777 := @Enclosure.Real.IsNear.addLit_ft_p qz455 (Enclosure.sfrac Bool.true Ns222p773 Ns222p774) 986856655639069044409 1125899906842624000 7887747781737672087 591872000000000000000000 Ns222p773 Ns222p774 0 1 Ns222p776 

noncomputable def Ns222p778 := nat_lit 66226829090777117587853541376000 

noncomputable abbrev qz456 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 514899 2000) (Real.log Real.pi))

noncomputable def Ns222p779 := @Enclosure.Real.IsNear.subLit_ff_p qz105 qz456 1318670770171041525433 1125899906842624000 1634059970259369 289000000000000000000 19777662428139 67108864000 514899 67108864000 Ns222p778 986856655639069044409 1125899906842624000 

noncomputable def Ns222p780 := nat_lit 2637341540342083050866000 

noncomputable abbrev qz106 := (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 514899 4000) qz689) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1029798))))))

noncomputable def Ns222p781 := @Enclosure.Real.IsNear.subLit_ff_p qz106 qz454 1608533138237721652921 1125899906842624000 1634059970259369 289000000000000000000 514899 2000 0 1 Ns222p780 1318670770171041525433 1125899906842624000 1634059970259369 289000000000000000000 

noncomputable def Ns222p782 := nat_lit 3622094620990248883504680990993809408 

noncomputable def Ns222p783 := nat_lit 26842138072444781847379968 

noncomputable def Ns222p784 := nat_lit 13344413902987849080019248 

noncomputable def Ns222p785 := BSN.log_dyadic_bound 11908920804 2109060920804 2 1 Ns222p784 67108864 23120000 141822394715944006416 141822394715944006416 757875 2120969841608 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 11908920804) (BSN.artanhQ 2109060920804) 0 1 141822394715944006416 Ns222p784 141822394715944006416 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns222p786 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 514899 4000) qz689 514899 4000 0 1 3124836142226679 281474976710656 781250289 18062500000000000 1608975004796374790421 1125899906842624000 402264992555811 72250000000000000000 (Enclosure.Real.IsNear.const Bool.false 514899 4000) (BSN.isNear_log_sfrac 1060484920804 16000000 3124836142226679 281474976710656 781250289 18062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1060484920804) qz354)) Bool.false Ns222p783 Ns222p89 1000000369920000 23120000000000000000000 3124836142226679 281474976710656 781250289 18062500000000000 (BSN.log_rat_reduce_isNear 1060484920804 16000000 16 2120969841608 2097152000000 757875 67108864 24973259072661432 36028797018963968 23120000 1000000000000000 rfl rfl rfl rfl (Ns222p785 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns222p787 := BSN.arctan_dyadic_bound_f 1000 1029798 1 0 8388608 2890000 0 1 1 0 1 1 8145 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1029798) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1029798) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz457 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1029798)))

noncomputable def Ns222p788 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz457 884279719003555 562949953421312 1 2000000000000000 8145 8388608 1 2890000 7413290697700356915200 883733117306275 562949953421312 200000000289 578000000000000000 qz16 (Ns222p787 rfl) rfl rfl 

noncomputable def Ns222p789 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 514899 4000) qz689) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz457)) 1608975004796374790421 1125899906842624000 402264992555811 72250000000000000000 883733117306275 2251799813685248 200000000289 2312000000000000000 Ns222p782 1608533138237721652921 1125899906842624000 1634059970259369 289000000000000000000 (Ns222p786 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz457) 1 4 0 1 883733117306275 562949953421312 200000000289 578000000000000000 883733117306275 2251799813685248 200000000289 2312000000000000000 qz357 Ns222p788 rfl) 

noncomputable def Ns222p790 := @Ns222p777 Ns222p771 Ns222p772 7887747781737672087 591872000000000000000000 (@Ns222p779 7887747781737672087 591872000000000000000000 (Ns222p781 (Ns222p789 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 514899 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz454 (Real.log Real.pi) 514899 2000 0 1 38410761 33554432 1 33554432 19777662428139 67108864000 514899 67108864000 (Enclosure.Real.IsNear.const Bool.false 514899 2000) RS223to240.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns222p773 Ns222p774) 

noncomputable def Ns222p791 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz101) Bool.false Ns222p771 Ns222p772 7887747781737672087 591872000000000000000000 7352652335 8388608 7 524288 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz101) (@HAdd.hAdd Real Real Real qz358 qz455 (Enclosure.sfrac Bool.true Ns222p773 Ns222p774)) Bool.false Ns222p771 Ns222p772 7887747781737672087 591872000000000000000000 Ns222p775 (Ns222p790 rfl rfl)) 

noncomputable def Ns222p792 := nat_lit 1899110207185580866928640 

noncomputable def Ns222p793 := nat_lit 857379961661786169145056973481245119978486862967973125939989012687898777751037443635769049308610584365434376692012746277264362104160256 

noncomputable def Ns222p794 := nat_lit 611511117781309480650888401183487713062362910577655740128280343234892086944759922800756561571769570712803263544339980357159878656 

noncomputable def Ns222p795 := nat_lit 4281571305225022091543035500468773145737228549966841202892158910524423053605891624169412452594539597609548860725352475626673152842530816 

noncomputable def Ns222p796 := BSN.sin_dyadic_bound_f 53975958484 34359738368 4 3 16777216 5785645 Ns222p793 Ns222p574 Ns222p794 Ns222p795 Ns222p577 Ns222p794 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53975958484) qz371 0 3 Ns222p793 Ns222p574 Ns222p794 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53975958484) qz372 0 3 Ns222p795 Ns222p577 Ns222p794 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p797 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz101) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7352652335) qz370) Bool.false 7352652335 8388608 7 524288 Bool.true 16777215 16777216 1 2890000 (Ns222p791 rfl) (Enclosure.sfrac_false_div 7352652335 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7352652335) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns222p792) qz640) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 139 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q1 7352652335 8388608 226375608064910080 72057594037927936 139 Ns222p792 Ns222p156 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns222p792 Ns222p156 53975958484 34359738368 5785645 5780000 (Ns222p796 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p798 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz101) Bool.false Ns222p771 Ns222p772 7887747781737672087 591872000000000000000000 117642437362 134217728 1790 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz101) (@HAdd.hAdd Real Real Real qz358 qz455 (Enclosure.sfrac Bool.true Ns222p773 Ns222p774)) Bool.false Ns222p771 Ns222p772 7887747781737672087 591872000000000000000000 Ns222p775 (Ns222p790 rfl rfl)) 

noncomputable def Ns222p799 := Ns222p770 35252 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 330 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 43473616 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 197 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 131864605 134217728) qz104 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz101) qz101 1) Bool.true 16777215 16777216 1297143 94699520000 134217720 134217728 1839 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz101) qz101 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz101)) Bool.true 16777215 16777216 1297143 94699520000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz101) qz101) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz101)) Bool.true 16777215 16777216 20754288 1515192320000 16777215 16777216 1297143 94699520000 (Ns222p797 rfl rfl) rfl)) rfl) (Ns222p798 rfl) RS223to240.d7 

noncomputable def Ns222p800 := nat_lit 1619814339321550711033776565379872410645190487468426927863981599977086185392002464038318079099752284398241 

noncomputable def Ns222p801 := nat_lit 455767333086105040278267966883728831972548273512766546968692511191547955322530144969060710870131361 

noncomputable def Ns222p802 := nat_lit 9817636914742091797458324827065459745674708791052756157523233253946984519278853514297418640880264344216225 

noncomputable def Ns222p803 := BSN.cos_dyadic_bound_f 166556633 134217728 4 3 134217728 67108864 Ns222p800 Ns222p227 Ns222p801 Ns222p802 Ns222p230 Ns222p801 43473616 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 166556633) qz361 0 3 Ns222p800 Ns222p227 Ns222p801 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 166556633) qz362 0 3 Ns222p802 Ns222p230 Ns222p801 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p804 := nat_lit 6500810697810092670526813134948075686235594907008296743404123120334236022518072371915049861506320693989376 

noncomputable def Ns222p805 := nat_lit 1677225100417614801759989785852304494301138503306943003463248581694862891461503408780353049905074176 

noncomputable def Ns222p806 := nat_lit 32479748775216862542474886365298981200804801621320199209531806134503770035934477589143637232277045047463936 

noncomputable def Ns222p807 := BSN.sin_dyadic_bound_f 185658974 134217728 4 3 134217728 67108864 Ns222p804 Ns222p111 Ns222p805 Ns222p806 Ns222p114 Ns222p805 131864605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 185658974) qz363 0 3 Ns222p804 Ns222p111 Ns222p805 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 185658974) qz364 0 3 Ns222p806 Ns222p114 Ns222p805 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p808 := nat_lit 219319968074352676847181874264211786530564848153241134318006535679905 

noncomputable def Ns222p809 := nat_lit 49924757922137828990596760197064536309906711334059845730577903521 

noncomputable def Ns222p810 := nat_lit 574328609634287835257586799746902288806977610487757350130262848270241 

noncomputable def Ns222p811 := BSN.sin_dyadic_bound_f 122261437 134217728 3 2 134217728 67108864 Ns222p808 Ns222p124 Ns222p809 Ns222p810 Ns222p127 Ns222p809 106041031 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 122261437) qz363 0 2 Ns222p808 Ns222p124 Ns222p809 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 122261437) qz364 0 2 Ns222p810 Ns222p127 Ns222p809 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p812 := nat_lit 38426041898819941356065734282803897561886197196647676513552836120801 

noncomputable def Ns222p813 := nat_lit 4966396720942974211904869516262750929204704723359089592111517921 

noncomputable def Ns222p814 := nat_lit 115268192903017938119773393109379167183800182180496311361474285326561 

noncomputable def Ns222p815 := BSN.cos_dyadic_bound_f 91623141 134217728 3 2 134217728 67108864 Ns222p812 Ns222p105 Ns222p813 Ns222p814 Ns222p108 Ns222p813 104140403 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 91623141) qz361 0 2 Ns222p812 Ns222p105 Ns222p813 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 91623141) qz362 0 2 Ns222p814 Ns222p108 Ns222p813 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p816 := Ns222p768 59891 BSN.abs_quadSignPos (BSN.cos_quad_nat3 103 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 106041031 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 104140403 134217728) qz104 rfl rfl (Ns222p799 RS223to240.d9 RS223to240.d11 RS223to240.d13 RS223to240.d17 (Ns222p803 rfl rfl) (Ns222p807 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns222p798 rfl) RS223to240.d19 RS223to240.d21 RS223to240.d23 RS223to240.d25 RS223to240.d17 (Ns222p811 rfl rfl) (Ns222p815 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns222p817 := nat_lit 22849740808432150262145375974338546649292089170588575827737354240000 

noncomputable def Ns222p818 := nat_lit 542124845069015944187393501181971191662764285767397401600000000 

noncomputable def Ns222p819 := nat_lit 59843681534239805613137776533789518032883255733174075191138099200000 

noncomputable def Ns222p820 := BSN.sin_dyadic_bound_f 69464420 134217728 3 2 134217728 67108864 Ns222p817 Ns222p124 Ns222p818 Ns222p819 Ns222p127 Ns222p818 66404585 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 69464420) qz363 0 2 Ns222p817 Ns222p124 Ns222p818 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 69464420) qz364 0 2 Ns222p819 Ns222p127 Ns222p818 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p821 := nat_lit 5893267645289331855317589108937407370299771059563055708877988574588433874001410027951560036683665349252641 

noncomputable def Ns222p822 := nat_lit 1249983956107920937867027186062616239558891871827967747177509052399133195754382441010723879099012641 

noncomputable def Ns222p823 := nat_lit 29446360102142359348671129561828652832653892180383150060901265088029835874928446908872445263195767135508001 

noncomputable def Ns222p824 := BSN.sin_dyadic_bound_f 181165447 134217728 4 3 134217728 67108864 Ns222p821 Ns222p111 Ns222p822 Ns222p823 Ns222p114 Ns222p822 130953130 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 181165447) qz363 0 3 Ns222p821 Ns222p111 Ns222p822 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 181165447) qz364 0 3 Ns222p823 Ns222p114 Ns222p822 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p825 := Ns222p766 80345 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 29 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66404585 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 79 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 130953130 134217728) qz104 rfl rfl (Ns222p816 rfl rfl) (Ns222p798 rfl) RS223to240.d27 RS223to240.d29 RS223to240.d31 RS223to240.d33 RS223to240.d17 (Ns222p820 rfl rfl) (Ns222p824 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p826 := nat_lit 305963420663327268548147066232971985970312663492049047807103696093440 

noncomputable def Ns222p827 := nat_lit 97145022421213705805939730383841489754690695899380536778653942016 

noncomputable def Ns222p828 := nat_lit 801175485986698976388127937713352791319787476590577080530487097671936 

noncomputable def Ns222p829 := BSN.sin_dyadic_bound_f 132870194 134217728 3 2 134217728 67108864 Ns222p826 Ns222p124 Ns222p827 Ns222p828 Ns222p127 Ns222p827 112206568 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 132870194) qz363 0 2 Ns222p826 Ns222p124 Ns222p827 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 132870194) qz364 0 2 Ns222p828 Ns222p127 Ns222p827 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p830 := nat_lit 3507264647523380796954215432043566293175851864064341467681309047041 

noncomputable def Ns222p831 := nat_lit 41383688796607085678764738112375185154138782163105058198370561 

noncomputable def Ns222p832 := nat_lit 10521711175192549176691288766654474129157247314628698192927530400001 

noncomputable def Ns222p833 := BSN.cos_dyadic_bound_f 50362079 134217728 3 2 134217728 67108864 Ns222p830 Ns222p105 Ns222p831 Ns222p832 Ns222p108 Ns222p831 124879469 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 50362079) qz361 0 2 Ns222p830 Ns222p105 Ns222p831 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 50362079) qz362 0 2 Ns222p832 Ns222p108 Ns222p831 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p834 := Ns222p764 98217 BSN.abs_quadSignPos qz664 (BSN.sfrac_eq_quadSignPos_mul Bool.false 112206568 134217728) BSN.abs_quadSignNeg qz408 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 124879469 134217728) qz104 rfl rfl (Ns222p825 rfl) (Ns222p798 rfl) RS223to240.d35 RS223to240.d37 RS223to240.d46 RS223to240.d48 RS223to240.d17 (Ns222p829 rfl rfl) (Ns222p833 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p835 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz101) qz101 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz101) qz101 9) 214212176 134217728 98217 134217728 214212176 134217728 98217 134217728 57502143145312256 13388261 4194304 98217 67108864 (Ns222p834 rfl) 

noncomputable def Ns222p836 := @Enclosure.Real.IsNear.mulLit_tf qz688 (Zeta.RiemannSiegel.correction qz103) 5576149 16777216 1 16777216 56627833583529 70368744177664 18609830873701 794397151068160000 315765237608961649821 1180591620717411303424 

noncomputable abbrev qz690 := (@HPow.hPow Real Real Real qz6 qz102 qz8)

noncomputable def Ns222p837 := @Enclosure.Real.IsNear.mulLit_tf qz48 qz690 1 1 0 1 5576149 16777216 1 16777216 5576149 16777216 1 16777216 

noncomputable def Ns222p838 := @Enclosure.Real.IsNear.sqrt_image qz102 1374871467123 16777216000 514899 16777216000 75938308 75938338 8388608 (@Enclosure.Real.IsNear.of_eq qz102 (@HMul.hMul Real Real Real qz4 qz101 qz2) Bool.false 1374871467123 16777216000 514899 16777216000 (BSN.t_div_two_pi_mk qz101 514899 1000 qz104) (@Enclosure.Real.IsNear.mulLit_ff qz101 qz2 514899 1000 0 1 2670177 16777216 1 16777216 1374871467123 16777216000 514899 16777216000 (Enclosure.Real.IsNear.const Bool.false 514899 1000) RS223to240.d40 rfl)) 

noncomputable abbrev qz878 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 514899 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz691 := qz878

noncomputable abbrev qz458 := qz691

noncomputable abbrev qz107 := qz458

noncomputable def Ns222p839 := @Enclosure.Real.IsNear.sqrt_image qz107 75938323 8388608 15 8388608 25239189 25239195 8388608 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 151876646 16777216 30 16777216 75938323 8388608 15 8388608 (Ns222p838 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns222p840 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz107) 3154899 1048576 3 8388608 2788074 2788075 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz107) Bool.false 50478384 16777216 6 16777216 3154899 1048576 3 8388608 (Ns222p839 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns222p841 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 5576149 16777216 1 16777216 5576149 16777216 1 16777216 (Ns222p840 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz108 := (@HMul.hMul Real Real Real qz343 qz341 qz452)

noncomputable abbrev qz692 := (@HMul.hMul Real Real Real qz848 qz877 qz877)

noncomputable abbrev qz459 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz692 qz687) qz639)

noncomputable abbrev qz109 := (Real.cos (@HMul.hMul Real Real Real qz343 qz341 qz459))

noncomputable def Ns222p842 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz103) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz108)) qz109) Bool.false 56627833583529 

noncomputable def Ns222p843 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz108)) qz109 8867673 8388608 109 

noncomputable def Ns222p844 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz108)) Bool.false 17735346 16777216 218 16777216 8867673 8388608 109 

noncomputable def Ns222p845 := @Enclosure.Real.IsNear.recentre' (Real.cos qz108) Bool.false 7935424 8388608 562987216 48486154240000 123991 131072 35186701 3030384640000 

noncomputable def Ns222p846 := @Enclosure.Real.IsNear.cos_image qz108 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5539897) qz359) Bool.false 5539897 16777216 189 16777216 Bool.false 7935424 8388608 1 

noncomputable def Ns222p847 := nat_lit 404791131139447563082352297 

noncomputable def Ns222p848 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz103 884279719003555 140737488355328 1 500000000000000 440851 8388608 15 8388608 389835598402436225305 1180591620717411303424 Ns222p847 

noncomputable def Ns222p849 := @Enclosure.Real.IsNear.subLit_ff_p qz107 qz46 75938323 8388608 15 8388608 9 1 0 1 440851 440851 8388608 15 

noncomputable def Ns222p850 := @Ns222p849 8388608 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 151876646 16777216 30 16777216 75938323 8388608 15 8388608 (Ns222p838 rfl rfl rfl rfl rfl rfl) rfl) qz411 

noncomputable def Ns222p851 := @Enclosure.Real.IsNear.recentre' qz108 Bool.false 389835598402436225305 1180591620717411303424 Ns222p847 Ns222p263 5539897 16777216 189 16777216 (@Ns222p848 Ns222p263 RS223to240.d39 (Ns222p850 rfl rfl) rfl) 

noncomputable def Ns222p852 := nat_lit 941904259550450891682230881 

noncomputable def Ns222p853 := BSN.cos_dyadic_bound_f 5539897 16777216 2 1 8388608 2890000 Ns222p852 Ns222p287 Ns222p852 Ns222p852 Ns222p288 Ns222p852 7935424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 5539897) qz391 0 1 Ns222p852 Ns222p287 Ns222p852 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 5539897) (BSN.cosOddQ 16777216) 0 1 Ns222p852 Ns222p288 Ns222p852 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p854 := @Enclosure.Real.IsNear.inv_image (Real.cos qz108) 123991 131072 35186701 3030384640000 8867564 8867782 8388608 (Ns222p845 (@Ns222p846 2890000 (Ns222p851 rfl) (Enclosure.sfrac_false_div 5539897 16777216) (Ns222p853 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns222p855 := @Enclosure.Real.IsNear.recentre' qz109 Bool.false 6385873 8388608 

noncomputable abbrev qz110 := (@HMul.hMul Real Real Real qz343 qz341 qz459)

noncomputable def Ns222p856 := @Enclosure.Real.IsNear.cos_image qz110 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 11837153)) qz359) Bool.true 11837153 16777216 

noncomputable def Ns222p857 := nat_lit 6987421939055761881844365605 

noncomputable def Ns222p858 := nat_lit 9903520314283042199192993792 

noncomputable def Ns222p859 := nat_lit 3752545342813069754126942861866237 

noncomputable def Ns222p860 := @Enclosure.Real.IsNear.recentre' qz110 Bool.true Ns222p857 Ns222p858 Ns222p859 

noncomputable abbrev qz111 := qz459

noncomputable def Ns222p861 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz111 884279719003555 140737488355328 1 500000000000000 7901823132311 

noncomputable abbrev qz460 := (@HSub.hSub Real Real Real qz634 qz692 qz687)

noncomputable abbrev qz112 := qz460

noncomputable def Ns222p862 := @Enclosure.Real.IsNear.subLit_tf qz112 qz25 3503776621207 70368744177664 139054875 70368744177664 1 16 

noncomputable abbrev qz461 := qz692

noncomputable abbrev qz113 := qz461

noncomputable def Ns222p863 := @Enclosure.Real.IsNear.subLit_ff_n qz113 qz103 194349604201 70368744177664 13225755 70368744177664 440851 8388608 15 8388608 

noncomputable def Ns222p864 := @Enclosure.Real.IsNear.mulLit_ff qz103 qz103 440851 8388608 15 8388608 440851 8388608 15 8388608 194349604201 70368744177664 

noncomputable def Ns222p865 := nat_lit 2613617110765860618990878235614496238305732532675019843331841 

noncomputable def Ns222p866 := nat_lit 253092741970790968397859029543733109897246971520789871559966720 

noncomputable def Ns222p867 := nat_lit 385458909708450746104203269390018914452362845034287752961 

noncomputable def Ns222p868 := nat_lit 7840080414478164955480426300304708677088292872334990954489601 

noncomputable def Ns222p869 := nat_lit 11389173388685593577903656329467989945376113718435544220198502400 

noncomputable def Ns222p870 := BSN.cos_dyadic_bound_f 11837153 16777216 3 2 8388608 2890000 Ns222p865 Ns222p866 Ns222p867 Ns222p868 Ns222p869 Ns222p867 6385873 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 11837153) qz391 0 2 Ns222p865 Ns222p866 Ns222p867 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 11837153) (BSN.cosOddQ 16777216) 0 2 Ns222p868 Ns222p869 Ns222p867 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p871 := @Ns222p855 620787216 48486154240000 6385873 8388608 38799201 3030384640000 (@Ns222p856 209 16777216 Bool.false 6385873 8388608 1 2890000 (@Ns222p860 Ns222p281 11837153 16777216 209 16777216 (@Ns222p861 70368744177664 139054875 70368744177664 Ns222p857 Ns222p858 Ns222p859 Ns222p281 RS223to240.d39 (@Ns222p862 0 1 126429170116976 7901823132311 70368744177664 139054875 70368744177664 (@Ns222p863 29391808594870009856 3503776621207 70368744177664 139054875 70368744177664 (@Ns222p864 13225755 70368744177664 (Ns222p850 rfl rfl) (Ns222p850 rfl rfl) rfl) (Ns222p850 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 11837153 16777216) (BSN.cos_neg_of_bound 11837153 16777216 Bool.false 6385873 8388608 1 2890000 (Ns222p870 rfl rfl)) rfl rfl) 

noncomputable def Ns222p872 := @Ns222p836 66822709490529208961 Ns222p760 (Ns222p837 qz61 (@Enclosure.Real.IsNear.of_eq qz690 (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 5576149 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz102 (BSN.t_div_two_pi_nonneg qz101 514899 1000 qz104)) Ns222p841) rfl) (@Ns222p842 70368744177664 18609830873701 794397151068160000 (BSN.correction_mk qz103 (BSN.cos_two_pi_p_ne_zero_mk qz101 514899 1000 9 qz104 rfl rfl (@BSN.floor_sqrt_eq_dec qz101 514899 1000 9 qz104 rfl rfl rfl))) (@Ns222p843 8388608 6385873 8388608 38799201 3030384640000 56627833583529 70368744177664 18609830873701 794397151068160000 (@Ns222p844 8388608 (Ns222p854 rfl rfl rfl rfl rfl) rfl) (Ns222p871 rfl) rfl)) 

noncomputable def Ns222p873 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz101) (hardyZApproximantRS₀ qz101) Bool.true 3452695215562222359395 1180591620717411303424 12550551507324364524161 Ns222p760 (@Eq.refl Real (hardyZApproximantRS₀ qz101)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz101) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz101) qz101 9) (@HMul.hMul Real Real Real qz4 qz688 (Zeta.RiemannSiegel.correction qz103))) Bool.true 3452695215562222359395 1180591620717411303424 12550551507324364524161 Ns222p760 (BSN.hardyZApproximantRS₀_eq qz101 9 (@BSN.floor_sqrt_eq_dec qz101 514899 1000 9 qz104 rfl rfl rfl)) (@Ns222p762 3452695215562222359395 1180591620717411303424 12550551507324364524161 Ns222p760 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz101) qz101 9) (@HAdd.hAdd Real Real Real qz358 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz101) qz101 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz101) qz101 9)) Bool.true 13388261 4194304 98217 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz101) qz101 9) (Ns222p835 (Ns222p834 rfl) rfl rfl)) (Ns222p872 rfl) rfl rfl)) 

theorem RS223to240.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz101) Bool.true 3452695215562222359395 1180591620717411303424 12550551507324364524161 Ns222p760 := Ns222p873 

noncomputable def Ns222p874 := nat_lit 106622180746041208340480000 

noncomputable def Ns222p875 := nat_lit 191465435101471145504188399616 

noncomputable abbrev qz879 := (Enclosure.sfrac Bool.false 516325 1000)

noncomputable abbrev qz693 := qz879

noncomputable abbrev qz462 := qz693

noncomputable abbrev qz114 := qz462

noncomputable abbrev qz880 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 516325 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz694 := qz880

noncomputable abbrev qz463 := qz694

noncomputable abbrev qz115 := qz463

noncomputable abbrev qz881 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 516325 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz695 := qz881

noncomputable abbrev qz464 := qz695

noncomputable abbrev qz116 := qz464

noncomputable abbrev qz696 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz115 qz8))

noncomputable def Ns222p876 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 9) (@HMul.hMul Real Real Real qz4 qz696 (Zeta.RiemannSiegel.correction qz116)) 307000363 67108864 49245 33554432 152653560697575661815 590295810358705651712 866911267712230222401 Ns222p874 Ns222p875 

noncomputable def Ns222p877 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 516325 1000 123 162 134217728 67108864 2251799813685248 Bool.false 118064220609 1795 

noncomputable def Ns222p878 := Ns222p877 279097919 47 47453128 8 294906479 47 44739240 8 Bool.false 314318987 80569 Bool.true 109080580 Bool.true 49115471 7074237752028440 1 Bool.false 97462950 Bool.false Bool.false 125330937 Bool.true Bool.false 307000363 

noncomputable def Ns222p879 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 516325 1000 28 79 134217728 67108864 2251799813685248 Bool.false 118064220609 1795 

noncomputable def Ns222p880 := Ns222p879 240485871 47 54794152 8 261175631 47 50729528 8 Bool.false 268299598 60059 Bool.true 201442739 Bool.true 131818650 7074237752028440 1 Bool.false 9378326 Bool.false Bool.false 111626123 Bool.false Bool.false 314318987 

noncomputable def Ns222p881 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 516325 1000 104 30 134217728 67108864 2251799813685248 Bool.false 118064220609 1795 

noncomputable def Ns222p882 := Ns222p881 186065264 47 67108856 8 216015088 47 60023992 8 Bool.false 212034573 35352 Bool.false 67886904 Bool.false 205368873 7074237752028440 1 Bool.false 117412148 Bool.false Bool.false 5458335 Bool.true Bool.false 268299598 

noncomputable def Ns222p883 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 516325 1000 332 198 134217728 67108864 2251799813685248 Bool.false 118064220609 1795 

noncomputable def Ns222p884 := Ns222p883 93032624 47 94906264 8 147453232 47 77490640 16 Bool.false 134217648 1847 Bool.false 34017929 Bool.false 186345198 7074237752028440 1 Bool.false 129929777 Bool.false Bool.false 24347957 Bool.true Bool.false 212034573 

noncomputable def Ns222p885 := nat_lit 27670104389056751402699964529348147882587577279 

noncomputable def Ns222p886 := nat_lit 31455918867224944754728955075597934589378560 

noncomputable def Ns222p887 := nat_lit 17614001851985267789935937500000000 

noncomputable def Ns222p888 := nat_lit 54567320917396884482357668828125000000 

noncomputable abbrev qz465 := (@Eq.refl Real qz693)

noncomputable abbrev qz117 := qz465

noncomputable def Ns222p889 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz114 516325 1000 1066367022500 16000000 1032650 4000 2000 Ns222p887 Ns222p888 qz117 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns222p890 := nat_lit 2161726905395058703335934728855324053327154474921875000000 

noncomputable abbrev qz466 := (Enclosure.sfrac Bool.false 516325 2000)

noncomputable abbrev qz697 := (Real.log (Enclosure.sfrac Bool.false 1066367022500 16000000))

noncomputable abbrev qz118 := (@HSub.hSub Real Real Real qz347 (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 516325 4000) qz697) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1032650)))))) qz466)

noncomputable abbrev qz467 := (@HSub.hSub Real Real Real qz11 qz118 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 516325 2000) (Real.log Real.pi)))

noncomputable def Ns222p891 := @Enclosure.Real.IsNear.addLit_ft_p qz467 (Enclosure.sfrac Bool.true Ns222p887 Ns222p888) 39615793158171873839 45035996273704960 316378036252204649 23674880000000000000000 Ns222p887 Ns222p888 0 1 Ns222p890 

noncomputable def Ns222p892 := nat_lit 106342835012155470803464355840 

noncomputable abbrev qz468 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 516325 2000) (Real.log Real.pi))

noncomputable def Ns222p893 := @Enclosure.Real.IsNear.subLit_ff_p qz118 qz468 52925115777615352367 45035996273704960 65540648876313 11560000000000000000 793297446933 2684354560 20653 2684354560 Ns222p892 39615793158171873839 45035996273704960 

noncomputable abbrev qz119 := (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 516325 4000) qz697) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1032650))))))

noncomputable def Ns222p894 := @Enclosure.Real.IsNear.subLit_ff_p qz119 qz466 64551721165625709103 45035996273704960 65540648876313 11560000000000000000 516325 2000 0 1 105850231555230704734000 52925115777615352367 45035996273704960 65540648876313 11560000000000000000 

noncomputable def Ns222p895 := nat_lit 145357553693818051611430483650412544 

noncomputable def Ns222p896 := nat_lit 26855511889840627234373632 

noncomputable def Ns222p897 := nat_lit 13418951965264306518750000 

noncomputable def Ns222p898 := BSN.log_dyadic_bound 17791022500 2114943022500 2 1 Ns222p897 67108864 23120000 316520481595506250000 316520481595506250000 1129073 2132734045000 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 17791022500) (BSN.artanhQ 2114943022500) 0 1 316520481595506250000 Ns222p897 316520481595506250000 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns222p899 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 516325 4000) qz697 516325 4000 0 1 3126393059482871 281474976710656 781250289 18062500000000000 64569395857499734763 45035996273704960 16135162218717 2890000000000000000 (Enclosure.Real.IsNear.const Bool.false 516325 4000) (BSN.isNear_log_sfrac 1066367022500 16000000 3126393059482871 281474976710656 781250289 18062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1066367022500) qz354)) Bool.false Ns222p896 Ns222p89 1000000369920000 23120000000000000000000 3126393059482871 281474976710656 781250289 18062500000000000 (BSN.log_rat_reduce_isNear 1066367022500 16000000 16 2132734045000 2097152000000 1129073 67108864 24973259072661432 36028797018963968 23120000 1000000000000000 rfl rfl rfl rfl (Ns222p898 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns222p900 := BSN.arctan_dyadic_bound_f 1000 1032650 1 0 8388608 2890000 0 1 1 0 1 1 8123 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1032650) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1032650) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz469 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1032650)))

noncomputable def Ns222p901 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz469 884279719003555 562949953421312 1 2000000000000000 8123 8388608 1 2890000 7413303082599332184064 883734593701283 562949953421312 200000000289 578000000000000000 qz16 (Ns222p900 rfl) rfl rfl 

noncomputable def Ns222p902 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 516325 4000) qz697) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz469)) 64569395857499734763 45035996273704960 16135162218717 2890000000000000000 883734593701283 2251799813685248 200000000289 2312000000000000000 Ns222p895 64551721165625709103 45035996273704960 65540648876313 11560000000000000000 (Ns222p899 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz469) 1 4 0 1 883734593701283 562949953421312 200000000289 578000000000000000 883734593701283 2251799813685248 200000000289 2312000000000000000 qz357 Ns222p901 rfl) 

noncomputable def Ns222p903 := @Ns222p891 Ns222p885 Ns222p886 316378036252204649 23674880000000000000000 (@Ns222p893 316378036252204649 23674880000000000000000 (Ns222p894 (Ns222p902 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 516325 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz466 (Real.log Real.pi) 516325 2000 0 1 38410761 33554432 1 33554432 793297446933 2684354560 20653 2684354560 (Enclosure.Real.IsNear.const Bool.false 516325 2000) RS223to240.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns222p887 Ns222p888) 

noncomputable def Ns222p904 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz114) Bool.false Ns222p885 Ns222p886 316378036252204649 23674880000000000000000 1844753447 2097152 225 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz114) (@HAdd.hAdd Real Real Real qz358 qz467 (Enclosure.sfrac Bool.true Ns222p887 Ns222p888)) Bool.false Ns222p885 Ns222p886 316378036252204649 23674880000000000000000 Ns222p889 (Ns222p903 rfl rfl)) 

noncomputable def Ns222p905 := BSN.cos_dyadic_bound_f 36017518 34359738368 1 0 16777216 5785645 0 1 1 0 1 1 16777206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 36017518) (BSN.cosEvenQ 34359738368) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 36017518) (BSN.cosOddQ 34359738368) 0 0 rfl) rfl rfl 

noncomputable abbrev qz698 := (@Nat.cast Real Real.instNatCast 302231454903657293676544)

noncomputable def Ns222p906 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz114) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1844753447) qz373) Bool.false 1844753447 2097152 225 16777216 Bool.false 16777206 16777216 1 2890000 (Ns222p904 rfl) (Enclosure.sfrac_false_div 1844753447 2097152) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1844753447) qz373) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 316813444727055581184) qz698) 226375608064910080 72057594037927936 Bool.false 16777206 16777216 140 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q0 1844753447 2097152 226375608064910080 72057594037927936 140 316813444727055581184 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777206 16777216 316813444727055581184 302231454903657293676544 36017518 34359738368 5785645 5780000 (Ns222p905 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p907 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz114) Bool.false Ns222p885 Ns222p886 316378036252204649 23674880000000000000000 118064220609 134217728 1795 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz114) (@HAdd.hAdd Real Real Real qz358 qz467 (Enclosure.sfrac Bool.true Ns222p887 Ns222p888)) Bool.false Ns222p885 Ns222p886 316378036252204649 23674880000000000000000 Ns222p889 (Ns222p903 rfl rfl)) 

noncomputable def Ns222p908 := Ns222p884 35352 BSN.abs_quadSignPos (BSN.cos_quad_nat0 332 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 129929777 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 198 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 24347957 134217728) qz117 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 1) Bool.false 8388603 8388608 41689201 3030384640000 134217648 134217728 1847 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz114)) Bool.false 8388603 8388608 41689201 3030384640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz114) qz114) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz114)) Bool.false 16777206 16777216 667027216 48486154240000 8388603 8388608 41689201 3030384640000 (Ns222p906 rfl rfl) rfl)) rfl) (Ns222p907 rfl) RS223to240.d7 

noncomputable def Ns222p909 := nat_lit 1339156956018455045914063819681 

noncomputable def Ns222p910 := BSN.cos_dyadic_bound_f 34017929 134217728 2 1 134217728 67108864 Ns222p909 Ns222p246 Ns222p909 Ns222p909 Ns222p247 Ns222p909 129929777 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 34017929) qz361 0 1 Ns222p909 Ns222p246 Ns222p909 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 34017929) qz362 0 1 Ns222p909 Ns222p247 Ns222p909 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p911 := nat_lit 2540021379289769572281151299814564218430895509866617069589256114735937169151174088563783136181861930110976 

noncomputable def Ns222p912 := nat_lit 1753147548792153800818453409088684650860507182248771070334990602611038847127798641128472379755728896 

noncomputable def Ns222p913 := nat_lit 15386783683387372759446989157021020327843647248162046370392477189934584534398762246666946748825050201067520 

noncomputable def Ns222p914 := BSN.cos_dyadic_bound_f 186345198 134217728 4 3 134217728 67108864 Ns222p911 Ns222p227 Ns222p912 Ns222p913 Ns222p230 Ns222p912 24347957 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 186345198) qz361 0 3 Ns222p911 Ns222p227 Ns222p912 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 186345198) qz362 0 3 Ns222p913 Ns222p230 Ns222p912 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p915 := nat_lit 11580031595559317575972133348610201294581206959636355766285884194816 

noncomputable def Ns222p916 := nat_lit 451115785345004751695498707121990972024270037378361271135502336 

noncomputable def Ns222p917 := nat_lit 34739192555107262718413009048416359901799572338834310576315381579776 

noncomputable def Ns222p918 := BSN.cos_dyadic_bound_f 67886904 134217728 3 2 134217728 67108864 Ns222p915 Ns222p105 Ns222p916 Ns222p917 Ns222p108 Ns222p916 117412148 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 67886904) qz361 0 2 Ns222p915 Ns222p105 Ns222p916 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 67886904) qz362 0 2 Ns222p917 Ns222p108 Ns222p916 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p919 := nat_lit 3751099840418087853479441215569875808197082927351043452400619619797425446878349756719461955238938047368801 

noncomputable def Ns222p920 := nat_lit 5628795079113244780338030894773005890773388715705540586423402696225586329989603184642567425960922721 

noncomputable def Ns222p921 := nat_lit 22707304679845113499235087643396452927234435751806799571958169141691597720895509057655907299182603636264545 

noncomputable def Ns222p922 := BSN.cos_dyadic_bound_f 205368873 134217728 4 3 134217728 67108864 Ns222p919 Ns222p227 Ns222p920 Ns222p921 Ns222p230 Ns222p920 5458335 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 205368873) qz361 0 3 Ns222p919 Ns222p227 Ns222p920 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 205368873) qz362 0 3 Ns222p921 Ns222p230 Ns222p920 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p923 := Ns222p882 60059 BSN.abs_quadSignPos (BSN.cos_quad_nat0 104 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 117412148 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 5458335 134217728) qz117 rfl rfl (Ns222p908 RS223to240.d9 RS223to240.d11 RS223to240.d13 RS223to240.d17 (Ns222p910 rfl rfl) (Ns222p914 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns222p907 rfl) RS223to240.d19 RS223to240.d21 RS223to240.d23 RS223to240.d25 RS223to240.d17 (Ns222p918 rfl rfl) (Ns222p922 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns222p924 := nat_lit 3471535105729595748732118709876961067537378436805694864902456044081619685251934185942244101636826139674801 

noncomputable def Ns222p925 := nat_lit 4464978936349478725140559192167106342098790705118924990515497500181468291787488541750187305190508721 

noncomputable def Ns222p926 := nat_lit 21018344385411133559058956932585920984543872680787263888677651674621975104573653654082079153312579724986545 

noncomputable def Ns222p927 := BSN.cos_dyadic_bound_f 201442739 134217728 4 3 134217728 67108864 Ns222p924 Ns222p227 Ns222p925 Ns222p926 Ns222p230 Ns222p925 9378326 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 201442739) qz361 0 3 Ns222p924 Ns222p227 Ns222p925 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 201442739) qz362 0 3 Ns222p926 Ns222p230 Ns222p925 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p928 := nat_lit 296389187318631255014243689946036542490158214071965976071276900000000 

noncomputable def Ns222p929 := nat_lit 91162216617397324612148096429662128906748078857143789062500000000 

noncomputable def Ns222p930 := nat_lit 776109799388558453178409043416828634503612968536999323575814500000000 

noncomputable def Ns222p931 := BSN.sin_dyadic_bound_f 131818650 134217728 3 2 134217728 67108864 Ns222p928 Ns222p124 Ns222p929 Ns222p930 Ns222p127 Ns222p929 111626123 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 131818650) qz363 0 2 Ns222p928 Ns222p124 Ns222p929 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 131818650) qz364 0 2 Ns222p930 Ns222p127 Ns222p929 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p932 := Ns222p880 80569 BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 9378326 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 79 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 111626123 134217728) qz117 rfl rfl (Ns222p923 rfl rfl) (Ns222p907 rfl) RS223to240.d27 RS223to240.d29 RS223to240.d31 RS223to240.d33 RS223to240.d17 (Ns222p927 rfl rfl) (Ns222p931 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p933 := nat_lit 138954854101924847841854037544769098573219859896384152586992394240000 

noncomputable def Ns222p934 := nat_lit 20043774491935918863280208026637517923471429477598744601600000000 

noncomputable def Ns222p935 := nat_lit 363896927965387657621934311328066416472271155509470954046101299200000 

noncomputable def Ns222p936 := BSN.sin_dyadic_bound_f 109080580 134217728 3 2 134217728 67108864 Ns222p933 Ns222p124 Ns222p934 Ns222p935 Ns222p127 Ns222p934 97462950 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 109080580) qz363 0 2 Ns222p933 Ns222p124 Ns222p934 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 109080580) qz364 0 2 Ns222p935 Ns222p127 Ns222p934 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p937 := nat_lit 3172683146310356290122268327321504104048005961358413617589243949441 

noncomputable def Ns222p938 := nat_lit 33864643266558489683627159900649719719821166343349458575896961 

noncomputable def Ns222p939 := nat_lit 9517981709644535753387437727644711012704578241742554153850580054401 

noncomputable def Ns222p940 := BSN.cos_dyadic_bound_f 49115471 134217728 3 2 134217728 67108864 Ns222p937 Ns222p105 Ns222p938 Ns222p939 Ns222p108 Ns222p938 125330937 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 49115471) qz361 0 2 Ns222p937 Ns222p105 Ns222p938 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 49115471) qz362 0 2 Ns222p939 Ns222p108 Ns222p938 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p941 := Ns222p878 98490 BSN.abs_quadSignPos qz664 (BSN.sfrac_eq_quadSignPos_mul Bool.false 97462950 134217728) BSN.abs_quadSignNeg qz408 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 125330937 134217728) qz117 rfl rfl (Ns222p932 rfl) (Ns222p907 rfl) RS223to240.d35 RS223to240.d37 RS223to240.d46 RS223to240.d48 RS223to240.d17 (Ns222p936 rfl rfl) (Ns222p940 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p942 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 9) 307000363 134217728 98490 134217728 307000363 134217728 98490 134217728 82409782434070528 307000363 67108864 49245 33554432 (Ns222p941 rfl) 

noncomputable def Ns222p943 := @Enclosure.Real.IsNear.mulLit_tf qz696 (Zeta.RiemannSiegel.correction qz116) 2786147 8388608 1 8388608 54790203351645 70368744177664 307598443166637 12710354417090560000 152653560697575661815 590295810358705651712 

noncomputable abbrev qz699 := (@HPow.hPow Real Real Real qz6 qz115 qz8)

noncomputable def Ns222p944 := @Enclosure.Real.IsNear.mulLit_tf qz48 qz699 1 1 0 1 2786147 8388608 1 8388608 2786147 8388608 1 8388608 

noncomputable def Ns222p945 := @Enclosure.Real.IsNear.sqrt_image qz115 55147165581 671088640 20653 671088640 76043390 76043420 8388608 (@Enclosure.Real.IsNear.of_eq qz115 (@HMul.hMul Real Real Real qz4 qz114 qz2) Bool.false 55147165581 671088640 20653 671088640 (BSN.t_div_two_pi_mk qz114 516325 1000 qz117) (@Enclosure.Real.IsNear.mulLit_ff qz114 qz2 516325 1000 0 1 2670177 16777216 1 16777216 55147165581 671088640 20653 671088640 (Enclosure.Real.IsNear.const Bool.false 516325 1000) RS223to240.d40 rfl)) 

noncomputable abbrev qz882 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 516325 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz700 := qz882

noncomputable abbrev qz470 := qz700

noncomputable abbrev qz120 := qz470

noncomputable def Ns222p946 := @Enclosure.Real.IsNear.sqrt_image qz120 76043405 8388608 15 8388608 25256646 25256652 8388608 (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 152086810 16777216 30 16777216 76043405 8388608 15 8388608 (Ns222p945 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns222p947 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz120) 25256649 8388608 3 8388608 2786146 2786148 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz120) Bool.false 50513298 16777216 6 16777216 25256649 8388608 3 8388608 (Ns222p946 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns222p948 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz120)) Bool.false 5572294 16777216 2 16777216 2786147 8388608 1 8388608 (Ns222p947 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz121 := (@HMul.hMul Real Real Real qz343 qz341 qz464)

noncomputable abbrev qz701 := (@HMul.hMul Real Real Real qz848 qz881 qz881)

noncomputable abbrev qz471 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz701 qz695) qz639)

noncomputable abbrev qz122 := (Real.cos (@HMul.hMul Real Real Real qz343 qz341 qz471))

noncomputable def Ns222p949 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz116) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz121)) qz122) Bool.false 54790203351645 

noncomputable def Ns222p950 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz121)) qz122 18284715 16777216 233 

noncomputable def Ns222p951 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz121)) Bool.false 18284715 16777216 233 16777216 18284715 16777216 233 

noncomputable def Ns222p952 := @Enclosure.Real.IsNear.recentre' (Real.cos qz121) Bool.false 7697002 8388608 562987216 48486154240000 3848501 4194304 35186701 3030384640000 

noncomputable def Ns222p953 := @Enclosure.Real.IsNear.cos_image qz121 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1715099) qz676) Bool.false 1715099 4194304 189 16777216 Bool.false 7697002 8388608 1 

noncomputable def Ns222p954 := nat_lit 404791131140350210589148841 

noncomputable def Ns222p955 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz116 884279719003555 140737488355328 1 500000000000000 545933 8388608 15 8388608 482757479834767791815 1180591620717411303424 Ns222p954 

noncomputable def Ns222p956 := @Enclosure.Real.IsNear.subLit_ff_p qz120 qz46 76043405 8388608 15 8388608 9 1 0 1 545933 545933 8388608 15 

noncomputable def Ns222p957 := @Ns222p956 8388608 (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 152086810 16777216 30 16777216 76043405 8388608 15 8388608 (Ns222p945 rfl rfl rfl rfl rfl rfl) rfl) qz411 

noncomputable def Ns222p958 := @Enclosure.Real.IsNear.recentre' qz121 Bool.false 482757479834767791815 1180591620717411303424 Ns222p954 Ns222p263 1715099 4194304 189 16777216 (@Ns222p955 Ns222p263 RS223to240.d39 (Ns222p957 rfl rfl) rfl) 

noncomputable def Ns222p959 := nat_lit 8652802177139833697199601 

noncomputable def Ns222p960 := BSN.cos_dyadic_bound_f 1715099 4194304 2 1 8388608 2890000 Ns222p959 Ns222p628 Ns222p959 Ns222p959 Ns222p629 Ns222p959 7697002 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1715099) (BSN.cosEvenQ 4194304) 0 1 Ns222p959 Ns222p628 Ns222p959 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1715099) (BSN.cosOddQ 4194304) 0 1 Ns222p959 Ns222p629 Ns222p959 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p961 := @Enclosure.Real.IsNear.inv_image (Real.cos qz121) 3848501 4194304 35186701 3030384640000 9142241 9142474 8388608 (Ns222p952 (@Ns222p953 2890000 (Ns222p958 rfl) (Enclosure.sfrac_false_div 1715099 4194304) (Ns222p960 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns222p962 := @Enclosure.Real.IsNear.recentre' qz122 Bool.false 5993006 8388608 

noncomputable abbrev qz123 := (@HMul.hMul Real Real Real qz343 qz341 qz471)

noncomputable def Ns222p963 := @Enclosure.Real.IsNear.cos_image qz123 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 13002317)) qz359) Bool.true 13002317 16777216 

noncomputable def Ns222p964 := nat_lit 7675213351166748046795679845 

noncomputable def Ns222p965 := nat_lit 3837617866103745983641891646071313 

noncomputable def Ns222p966 := @Enclosure.Real.IsNear.recentre' qz123 Bool.true Ns222p964 Ns222p858 Ns222p965 

noncomputable abbrev qz124 := qz471

noncomputable def Ns222p967 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz124 884279719003555 140737488355328 1 500000000000000 8679621601879 

noncomputable abbrev qz472 := (@HSub.hSub Real Real Real qz634 qz701 qz695)

noncomputable abbrev qz125 := qz472

noncomputable def Ns222p968 := @Enclosure.Real.IsNear.subLit_tf qz125 qz25 4281575090775 70368744177664 142207335 70368744177664 1 16 

noncomputable abbrev qz473 := qz701

noncomputable abbrev qz126 := qz473

noncomputable def Ns222p969 := @Enclosure.Real.IsNear.subLit_ff_n qz126 qz116 298042840489 70368744177664 16378215 70368744177664 545933 8388608 15 8388608 

noncomputable def Ns222p970 := @Enclosure.Real.IsNear.mulLit_ff qz116 qz116 545933 8388608 15 8388608 545933 8388608 15 8388608 298042840489 70368744177664 

noncomputable def Ns222p971 := nat_lit 3805091564991141547689182272850994165498480887576994128562721 

noncomputable def Ns222p972 := nat_lit 816894553324590609537909235061794919528606841663183620641 

noncomputable def Ns222p973 := nat_lit 11413640905866775461848471000082858906656385449047656018446881 

noncomputable def Ns222p974 := BSN.cos_dyadic_bound_f 13002317 16777216 3 2 8388608 2890000 Ns222p971 Ns222p866 Ns222p972 Ns222p973 Ns222p869 Ns222p972 5993006 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 13002317) qz391 0 2 Ns222p971 Ns222p866 Ns222p972 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 13002317) (BSN.cosOddQ 16777216) 0 2 Ns222p973 Ns222p869 Ns222p972 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p975 := @Ns222p962 317618608 24243077120000 2996503 4194304 19851163 1515192320000 (@Ns222p963 107 8388608 Bool.false 5993006 8388608 1 2890000 (@Ns222p966 Ns222p281 13002317 16777216 107 8388608 (@Ns222p967 70368744177664 142207335 70368744177664 Ns222p964 Ns222p858 Ns222p965 Ns222p281 RS223to240.d39 (@Ns222p968 0 1 138873945630064 8679621601879 70368744177664 142207335 70368744177664 (@Ns222p969 35916455059075891200 4281575090775 70368744177664 142207335 70368744177664 (@Ns222p970 16378215 70368744177664 (Ns222p957 rfl rfl) (Ns222p957 rfl rfl) rfl) (Ns222p957 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 13002317 16777216) (BSN.cos_neg_of_bound 13002317 16777216 Bool.false 5993006 8388608 1 2890000 (Ns222p974 rfl rfl)) rfl rfl) 

noncomputable def Ns222p976 := @Ns222p943 866911267712230222401 Ns222p874 (Ns222p944 qz61 (@Enclosure.Real.IsNear.of_eq qz699 (@Inv.inv Real Real.instInv (Real.sqrt qz120)) Bool.false 2786147 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz115 (BSN.t_div_two_pi_nonneg qz114 516325 1000 qz117)) Ns222p948) rfl) (@Ns222p949 70368744177664 307598443166637 12710354417090560000 (BSN.correction_mk qz116 (BSN.cos_two_pi_p_ne_zero_mk qz114 516325 1000 9 qz117 rfl rfl (@BSN.floor_sqrt_eq_dec qz114 516325 1000 9 qz117 rfl rfl rfl))) (@Ns222p950 16777216 2996503 4194304 19851163 1515192320000 54790203351645 70368744177664 307598443166637 12710354417090560000 (@Ns222p951 16777216 (Ns222p961 rfl rfl rfl rfl rfl) rfl) (Ns222p975 rfl) rfl)) 

noncomputable def Ns222p977 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz114) (hardyZApproximantRS₀ qz114) Bool.false 2853057311497198723319 590295810358705651712 157347262085118387022401 Ns222p874 (@Eq.refl Real (hardyZApproximantRS₀ qz114)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz114) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 9) (@HMul.hMul Real Real Real qz4 qz696 (Zeta.RiemannSiegel.correction qz116))) Bool.false 2853057311497198723319 590295810358705651712 157347262085118387022401 Ns222p874 (BSN.hardyZApproximantRS₀_eq qz114 9 (@BSN.floor_sqrt_eq_dec qz114 516325 1000 9 qz117 rfl rfl rfl)) (@Ns222p876 2853057311497198723319 590295810358705651712 157347262085118387022401 Ns222p874 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 9) (@HAdd.hAdd Real Real Real qz358 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 9)) Bool.false 307000363 67108864 49245 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz114) qz114 9) (Ns222p942 (Ns222p941 rfl) rfl rfl)) (Ns222p976 rfl) rfl rfl)) 

theorem RS223to240.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz114) Bool.false 2853057311497198723319 590295810358705651712 157347262085118387022401 Ns222p874 := Ns222p977 

noncomputable def Ns222p978 := nat_lit 10662218074604120834048000 

noncomputable def Ns222p979 := nat_lit 481248665837937191127351296 

noncomputable abbrev qz883 := (Enclosure.sfrac Bool.false 517749 1000)

noncomputable abbrev qz702 := qz883

noncomputable abbrev qz474 := qz702

noncomputable abbrev qz127 := qz474

noncomputable abbrev qz884 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 517749 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz703 := qz884

noncomputable abbrev qz475 := qz703

noncomputable abbrev qz128 := qz475

noncomputable abbrev qz885 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 517749 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz704 := qz885

noncomputable abbrev qz476 := qz704

noncomputable abbrev qz129 := qz476

noncomputable abbrev qz705 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz128 qz8))

noncomputable def Ns222p980 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz127) qz127 9) (@HMul.hMul Real Real Real qz4 qz705 (Zeta.RiemannSiegel.correction qz129)) 42871823 67108864 98761 67108864 4613353029138410973 18446744073709551616 89016288401259377649 Ns222p978 Ns222p979 

noncomputable def Ns222p981 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz127) qz127 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 517749 1000 123 162 134217728 67108864 2251799813685248 Bool.false 118485676358 1799 

noncomputable def Ns222p982 := Ns222p981 279097919 47 47453128 8 294906479 47 44739240 8 Bool.true 29017803 80791 Bool.true 85060267 Bool.true 47606548 7074237752028440 1 Bool.false 79479631 Bool.false Bool.false 125862938 Bool.true Bool.true 42871823 

noncomputable def Ns222p983 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz127) qz127 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 517749 1000 28 79 134217728 67108864 2251799813685248 Bool.false 118485676358 1799 

noncomputable def Ns222p984 := Ns222p983 240485871 47 54794152 8 261175631 47 50729528 8 Bool.true 91736843 60225 Bool.true 122438870 Bool.true 82277000 7074237752028440 1 Bool.false 82137919 Bool.false Bool.false 77219909 Bool.false Bool.true 29017803 

noncomputable def Ns222p985 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz127) qz127 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 517749 1000 105 31 134217728 67108864 2251799813685248 Bool.false 118485676358 1799 

noncomputable def Ns222p986 := Ns222p985 186065264 47 67108856 8 216015088 47 60023992 8 Bool.true 128343838 35451 Bool.false 13557003 Bool.false 108390422 7074237752028440 1 Bool.false 13533962 Bool.true Bool.false 96987159 Bool.false Bool.true 91736843 

noncomputable def Ns222p987 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz127) qz127 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 517749 1000 333 199 134217728 67108864 2251799813685248 Bool.false 118485676358 1799 

noncomputable def Ns222p988 := Ns222p987 93032624 47 94906264 8 147453232 47 77490640 16 Bool.true 134217712 1855 Bool.false 112166508 Bool.false 186998830 7074237752028440 1 Bool.false 99558672 Bool.true Bool.false 132107823 Bool.false Bool.true 128343838 

noncomputable def Ns222p989 := nat_lit 19145758647598265314672200542666997296895948794425609839 

noncomputable def Ns222p990 := nat_lit 21687855490207803789273327417733647512880623386624000 

noncomputable def Ns222p991 := nat_lit 17858238025711613181676638599520000 

noncomputable def Ns222p992 := nat_lit 55476533422015061803296005893913282880 

noncomputable abbrev qz706 := (@Eq.refl Real qz883)

noncomputable abbrev qz477 := qz706

noncomputable abbrev qz130 := qz477

noncomputable def Ns222p993 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz127 517749 1000 1072257108004 16000000 1035498 4000 2000 Ns222p991 Ns222p992 qz130 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns222p994 := nat_lit 55139784905083004106255937562880952215060332527945756336320 

noncomputable abbrev qz478 := (Enclosure.sfrac Bool.false 517749 2000)

noncomputable abbrev qz707 := (Real.log (Enclosure.sfrac Bool.false 1072257108004 16000000))

noncomputable abbrev qz131 := (@HSub.hSub Real Real Real qz347 (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 517749 4000) qz707) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1035498)))))) qz478)

noncomputable abbrev qz479 := (@HSub.hSub Real Real Real qz11 qz131 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 517749 2000) (Real.log Real.pi)))

noncomputable def Ns222p995 := @Enclosure.Real.IsNear.addLit_ft_p qz479 (Enclosure.sfrac Bool.true Ns222p991 Ns222p992) 993930255018243400839 1125899906842624000 7931123591707669137 591872000000000000000000 Ns222p991 Ns222p992 0 1 Ns222p994 

noncomputable def Ns222p996 := nat_lit 66701530309504613905801936896000 

noncomputable abbrev qz480 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 517749 2000) (Real.log Real.pi))

noncomputable def Ns222p997 := @Enclosure.Real.IsNear.subLit_ff_p qz131 qz480 1327580982607176803463 1125899906842624000 1642966223553969 289000000000000000000 19887133096989 67108864000 517749 67108864000 Ns222p996 993930255018243400839 1125899906842624000 

noncomputable def Ns222p998 := nat_lit 2655161965214353606926000 

noncomputable abbrev qz132 := (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 517749 4000) qz707) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1035498))))))

noncomputable def Ns222p999 := @Enclosure.Real.IsNear.subLit_ff_p qz132 qz478 1619047758041107670151 1125899906842624000 1642966223553969 289000000000000000000 517749 2000 0 1 Ns222p998 1327580982607176803463 1125899906842624000 1642966223553969 289000000000000000000 

noncomputable def Ns222p1000 := nat_lit 3645771439904484736061040430518632448 

noncomputable def Ns222p1001 := nat_lit 26868830186860266397892608 

noncomputable def Ns222p1002 := nat_lit 13493799216017718986592048 

noncomputable def Ns222p1003 := BSN.log_dyadic_bound 23681108004 2120833108004 2 1 Ns222p1002 67108864 23120000 560794876297112864016 560794876297112864016 1498730 2144514216008 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 23681108004) (BSN.artanhQ 2120833108004) 0 1 560794876297112864016 Ns222p1002 560794876297112864016 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns222p1004 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 517749 4000) qz707 517749 4000 0 1 3127943513316599 281474976710656 781250289 18062500000000000 1619489626076155815651 1125899906842624000 404491555879461 72250000000000000000 (Enclosure.Real.IsNear.const Bool.false 517749 4000) (BSN.isNear_log_sfrac 1072257108004 16000000 3127943513316599 281474976710656 781250289 18062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1072257108004) qz354)) Bool.false Ns222p1001 Ns222p89 1000000369920000 23120000000000000000000 3127943513316599 281474976710656 781250289 18062500000000000 (BSN.log_rat_reduce_isNear 1072257108004 16000000 16 2144514216008 2097152000000 1498730 67108864 24973259072661432 36028797018963968 23120000 1000000000000000 rfl rfl rfl rfl (Ns222p1003 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns222p1005 := BSN.arctan_dyadic_bound_f 1000 1035498 1 0 8388608 2890000 0 1 1 0 1 1 8101 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1035498) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1035498) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz481 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1035498)))

noncomputable def Ns222p1006 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz481 884279719003555 562949953421312 1 2000000000000000 8101 8388608 1 2890000 7413315467498307452928 883736070096291 562949953421312 200000000289 578000000000000000 qz16 (Ns222p1005 rfl) rfl rfl 

noncomputable def Ns222p1007 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 517749 4000) qz707) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz481)) 1619489626076155815651 1125899906842624000 404491555879461 72250000000000000000 883736070096291 2251799813685248 200000000289 2312000000000000000 Ns222p1000 1619047758041107670151 1125899906842624000 1642966223553969 289000000000000000000 (Ns222p1004 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz481) 1 4 0 1 883736070096291 562949953421312 200000000289 578000000000000000 883736070096291 2251799813685248 200000000289 2312000000000000000 qz357 Ns222p1006 rfl) 

noncomputable def Ns222p1008 := @Ns222p995 Ns222p989 Ns222p990 7931123591707669137 591872000000000000000000 (@Ns222p997 7931123591707669137 591872000000000000000000 (Ns222p999 (Ns222p1007 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 517749 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz478 (Real.log Real.pi) 517749 2000 0 1 38410761 33554432 1 33554432 19887133096989 67108864000 517749 67108864000 (Enclosure.Real.IsNear.const Bool.false 517749 2000) RS223to240.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns222p991 Ns222p992) 

noncomputable def Ns222p1009 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz127) Bool.false Ns222p989 Ns222p990 7931123591707669137 591872000000000000000000 1851338693 2097152 113 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz127) (@HAdd.hAdd Real Real Real qz358 qz479 (Enclosure.sfrac Bool.true Ns222p991 Ns222p992)) Bool.false Ns222p989 Ns222p990 7931123591707669137 591872000000000000000000 Ns222p993 (Ns222p1008 rfl rfl)) 

noncomputable def Ns222p1010 := nat_lit 856144160451641262462584102148413101478246324004019424740722227806027132812630505248924451230011446997982121684510192929714523022032896 

noncomputable def Ns222p1011 := nat_lit 608875971641277360403921800293745109194164688875239171042515336915728362481208294567800950941741581591287012110294042482621546496 

noncomputable def Ns222p1012 := nat_lit 4275407621552038105547281867375017754916835599947570378247462622569107614457365709040486695418933789568327943926245555263471558387040256 

noncomputable def Ns222p1013 := BSN.sin_dyadic_bound_f 53956537164 34359738368 4 3 16777216 5785645 Ns222p1010 Ns222p574 Ns222p1011 Ns222p1012 Ns222p577 Ns222p1011 16777214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53956537164) qz371 0 3 Ns222p1010 Ns222p574 Ns222p1011 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53956537164) qz372 0 3 Ns222p1012 Ns222p577 Ns222p1011 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1014 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz127) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1851338693) qz373) Bool.false 1851338693 2097152 113 8388608 Bool.true 16777214 16777216 1 2890000 (Ns222p1009 rfl) (Enclosure.sfrac_false_div 1851338693 2097152) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1851338693) qz373) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474606720055962329153536) qz698) 226375608064910080 72057594037927936 Bool.false 16777214 16777216 140 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q1 1851338693 2097152 226375608064910080 72057594037927936 140 474606720055962329153536 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777214 16777216 474606720055962329153536 302231454903657293676544 53956537164 34359738368 5785645 5780000 (Ns222p1013 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p1015 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz127) Bool.false Ns222p989 Ns222p990 7931123591707669137 591872000000000000000000 118485676358 134217728 1799 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz127) (@HAdd.hAdd Real Real Real qz358 qz479 (Enclosure.sfrac Bool.true Ns222p991 Ns222p992)) Bool.false Ns222p989 Ns222p990 7931123591707669137 591872000000000000000000 Ns222p993 (Ns222p1008 rfl rfl)) 

noncomputable def Ns222p1016 := Ns222p988 35451 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 333 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 99558672 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 199 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 132107823 134217728) qz130 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 1) Bool.true 8388607 8388608 20934913 1515192320000 134217712 134217728 1855 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz127)) Bool.true 8388607 8388608 20934913 1515192320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz127) qz127) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz127)) Bool.true 16777214 16777216 334958608 24243077120000 8388607 8388608 20934913 1515192320000 (Ns222p1014 rfl rfl) rfl)) rfl) (Ns222p1015 rfl) RS223to240.d7 

noncomputable def Ns222p1017 := nat_lit 155361770619540740767208203682969499312726844795132758080349488087040 

noncomputable def Ns222p1018 := nat_lit 25055645513050631483435526424843644511001983986438996427727241216 

noncomputable def Ns222p1019 := nat_lit 406859309148918905748857828317375132299362018870322036597175196123136 

noncomputable def Ns222p1020 := BSN.sin_dyadic_bound_f 112166508 134217728 3 2 134217728 67108864 Ns222p1017 Ns222p124 Ns222p1018 Ns222p1019 Ns222p127 Ns222p1018 99558672 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 112166508) qz363 0 2 Ns222p1017 Ns222p124 Ns222p1018 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 112166508) qz364 0 2 Ns222p1019 Ns222p127 Ns222p1018 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1021 := nat_lit 6690747243149831975006570558985284879516671840088975016593706529969242729447987023325308394949889190400000 

noncomputable def Ns222p1022 := nat_lit 1828380881419948031109166691850733671806674020098224021127613979907741807886646937529361000000000000 

noncomputable def Ns222p1023 := nat_lit 33427992125117368261419658581659043860221991999369890260914961367297719081766547296486159872751461952000000 

noncomputable def Ns222p1024 := BSN.sin_dyadic_bound_f 186998830 134217728 4 3 134217728 67108864 Ns222p1021 Ns222p111 Ns222p1022 Ns222p1023 Ns222p114 Ns222p1022 132107823 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 186998830) qz363 0 3 Ns222p1021 Ns222p111 Ns222p1022 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 186998830) qz364 0 3 Ns222p1023 Ns222p114 Ns222p1022 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1025 := nat_lit 33779620692546162098910156081 

noncomputable def Ns222p1026 := BSN.sin_dyadic_bound_f 13557003 134217728 2 1 134217728 67108864 Ns222p1025 Ns222p117 Ns222p1025 Ns222p1025 Ns222p118 Ns222p1025 13533962 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 13557003) qz363 0 1 Ns222p1025 Ns222p117 Ns222p1025 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 13557003) qz364 0 1 Ns222p1025 Ns222p118 Ns222p1025 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1027 := nat_lit 135470903323299987714052256451491376709839930126384878515937814995200 

noncomputable def Ns222p1028 := nat_lit 19051415865034591970293270926722614621784465086658699615465595136 

noncomputable def Ns222p1029 := nat_lit 354773901649623245149804006362881769054478832625629615361412094976256 

noncomputable def Ns222p1030 := BSN.sin_dyadic_bound_f 108390422 134217728 3 2 134217728 67108864 Ns222p1027 Ns222p124 Ns222p1028 Ns222p1029 Ns222p127 Ns222p1028 96987159 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 108390422) qz363 0 2 Ns222p1027 Ns222p124 Ns222p1028 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 108390422) qz364 0 2 Ns222p1029 Ns222p127 Ns222p1028 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1031 := Ns222p986 60225 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 105 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 13533962 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 31 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 96987159 134217728) qz130 rfl rfl (Ns222p1016 RS223to240.d9 RS223to240.d11 RS223to240.d13 RS223to240.d17 (Ns222p1020 rfl rfl) (Ns222p1024 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns222p1015 rfl) RS223to240.d19 RS223to240.d21 RS223to240.d23 RS223to240.d25 RS223to240.d17 (Ns222p1026 rfl rfl) (Ns222p1030 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns222p1032 := nat_lit 122575889181086011013848120619211397076891176349750238106269488800000 

noncomputable def Ns222p1033 := nat_lit 50507340658166478803061764692298301360194930021988628032100000000 

noncomputable def Ns222p1034 := nat_lit 367626652861941700083938238328249594627953139189206737062744266400000 

noncomputable def Ns222p1035 := BSN.cos_dyadic_bound_f 122438870 134217728 3 2 134217728 67108864 Ns222p1032 Ns222p105 Ns222p1033 Ns222p1034 Ns222p108 Ns222p1033 82137919 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 122438870) qz361 0 2 Ns222p1032 Ns222p105 Ns222p1033 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 122438870) qz362 0 2 Ns222p1034 Ns222p108 Ns222p1033 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1036 := nat_lit 44973365705255654336153966590816623087039039978524053504000000000000 

noncomputable def Ns222p1037 := nat_lit 2100040081817420812149805902400635360481000000000000000000000000 

noncomputable def Ns222p1038 := nat_lit 117783986306013295056231193766392030865947183086610616320000000000000 

noncomputable def Ns222p1039 := BSN.sin_dyadic_bound_f 82277000 134217728 3 2 134217728 67108864 Ns222p1036 Ns222p124 Ns222p1037 Ns222p1038 Ns222p127 Ns222p1037 77219909 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 82277000) qz363 0 2 Ns222p1036 Ns222p124 Ns222p1037 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 82277000) qz364 0 2 Ns222p1038 Ns222p127 Ns222p1037 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1040 := Ns222p984 80791 BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 82137919 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 79 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 77219909 134217728) qz130 rfl rfl (Ns222p1031 rfl rfl) (Ns222p1015 rfl) RS223to240.d27 RS223to240.d29 RS223to240.d31 RS223to240.d33 RS223to240.d17 (Ns222p1035 rfl rfl) (Ns222p1039 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p1041 := nat_lit 51374954631692767185513036204562187533312291011996623580512244730465 

noncomputable def Ns222p1042 := nat_lit 2740399836105078013597396930818770226305170314970737747574393441 

noncomputable def Ns222p1043 := nat_lit 134549015768984505835750222845489165530689601422338347230702663371361 

noncomputable def Ns222p1044 := BSN.sin_dyadic_bound_f 85060267 134217728 3 2 134217728 67108864 Ns222p1041 Ns222p124 Ns222p1042 Ns222p1043 Ns222p127 Ns222p1042 79479631 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 85060267) qz363 0 2 Ns222p1041 Ns222p124 Ns222p1042 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 85060267) qz364 0 2 Ns222p1043 Ns222p127 Ns222p1042 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1045 := nat_lit 2800397433762983604553634107923571379697655932150549055285021966336 

noncomputable def Ns222p1046 := nat_lit 26383568273367082911169375345591957087246449571368630768173056 

noncomputable def Ns222p1047 := nat_lit 8401139534152404079495079985020022955178793303552504428593529552896 

noncomputable def Ns222p1048 := BSN.cos_dyadic_bound_f 47606548 134217728 3 2 134217728 67108864 Ns222p1045 Ns222p105 Ns222p1046 Ns222p1047 Ns222p108 Ns222p1046 125862938 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 47606548) qz361 0 2 Ns222p1045 Ns222p105 Ns222p1046 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 47606548) qz362 0 2 Ns222p1047 Ns222p108 Ns222p1046 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1049 := Ns222p982 98761 BSN.abs_quadSignPos qz664 (BSN.sfrac_eq_quadSignPos_mul Bool.false 79479631 134217728) BSN.abs_quadSignNeg qz408 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 125862938 134217728) qz130 rfl rfl (Ns222p1040 rfl) (Ns222p1015 rfl) RS223to240.d35 RS223to240.d37 RS223to240.d46 RS223to240.d48 RS223to240.d17 (Ns222p1044 rfl rfl) (Ns222p1048 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p1050 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 9) 42871823 134217728 98761 134217728 42871823 134217728 98761 134217728 11508317356556288 42871823 67108864 98761 67108864 (Ns222p1049 rfl) 

noncomputable def Ns222p1051 := @Enclosure.Real.IsNear.mulLit_tf qz705 (Zeta.RiemannSiegel.correction qz129) 5568459 16777216 1 16777216 828479302647 1099511627776 317996097177063 12710354417090560000 4613353029138410973 18446744073709551616 

noncomputable abbrev qz708 := (@HPow.hPow Real Real Real qz6 qz128 qz8)

noncomputable def Ns222p1052 := @Enclosure.Real.IsNear.mulLit_tf qz48 qz708 1 1 0 1 5568459 16777216 1 16777216 5568459 16777216 1 16777216 

noncomputable def Ns222p1053 := @Enclosure.Real.IsNear.sqrt_image qz128 1382481471573 16777216000 517749 16777216000 76148180 76148210 8388608 (@Enclosure.Real.IsNear.of_eq qz128 (@HMul.hMul Real Real Real qz4 qz127 qz2) Bool.false 1382481471573 16777216000 517749 16777216000 (BSN.t_div_two_pi_mk qz127 517749 1000 qz130) (@Enclosure.Real.IsNear.mulLit_ff qz127 qz2 517749 1000 0 1 2670177 16777216 1 16777216 1382481471573 16777216000 517749 16777216000 (Enclosure.Real.IsNear.const Bool.false 517749 1000) RS223to240.d40 rfl)) 

noncomputable abbrev qz886 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 517749 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz709 := qz886

noncomputable abbrev qz482 := qz709

noncomputable abbrev qz133 := qz482

noncomputable def Ns222p1054 := @Enclosure.Real.IsNear.sqrt_image qz133 76148195 8388608 15 8388608 25274042 25274048 8388608 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 152296390 16777216 30 16777216 76148195 8388608 15 8388608 (Ns222p1053 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns222p1055 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz133) 25274045 8388608 3 8388608 2784229 2784230 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz133) Bool.false 50548090 16777216 6 16777216 25274045 8388608 3 8388608 (Ns222p1054 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns222p1056 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz133)) Bool.false 5568459 16777216 1 16777216 5568459 16777216 1 16777216 (Ns222p1055 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz134 := (@HMul.hMul Real Real Real qz343 qz341 qz476)

noncomputable abbrev qz710 := (@HMul.hMul Real Real Real qz848 qz885 qz885)

noncomputable abbrev qz483 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz710 qz704) qz639)

noncomputable abbrev qz135 := (Real.cos (@HMul.hMul Real Real Real qz343 qz341 qz483))

noncomputable def Ns222p1057 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz129) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz134)) qz135) Bool.false 828479302647 

noncomputable def Ns222p1058 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz134)) qz135 296693 262144 125 

noncomputable def Ns222p1059 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz134)) Bool.false 18988352 16777216 250 16777216 296693 262144 125 

noncomputable def Ns222p1060 := @Enclosure.Real.IsNear.recentre' (Real.cos qz134) Bool.false 7411780 8388608 562987216 48486154240000 1852945 2097152 35186701 3030384640000 

noncomputable def Ns222p1061 := @Enclosure.Real.IsNear.cos_image qz134 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4088613) qz370) Bool.false 4088613 8388608 189 16777216 Bool.false 7411780 8388608 1 

noncomputable def Ns222p1062 := nat_lit 404791131141250349835044521 

noncomputable def Ns222p1063 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz129 884279719003555 140737488355328 1 500000000000000 650723 8388608 15 8388608 575421151589150320265 1180591620717411303424 Ns222p1062 

noncomputable def Ns222p1064 := @Enclosure.Real.IsNear.subLit_ff_p qz133 qz46 76148195 8388608 15 8388608 9 1 0 1 650723 650723 8388608 15 

noncomputable def Ns222p1065 := @Ns222p1064 8388608 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 152296390 16777216 30 16777216 76148195 8388608 15 8388608 (Ns222p1053 rfl rfl rfl rfl rfl rfl) rfl) qz411 

noncomputable def Ns222p1066 := @Enclosure.Real.IsNear.recentre' qz134 Bool.false 575421151589150320265 1180591620717411303424 Ns222p1062 Ns222p263 4088613 8388608 189 16777216 (@Ns222p1063 Ns222p263 RS223to240.d39 (Ns222p1065 rfl rfl) rfl) 

noncomputable def Ns222p1067 := nat_lit 279449939982260096302085361 

noncomputable def Ns222p1068 := nat_lit 118842243771396506390315925504 

noncomputable def Ns222p1069 := nat_lit 1782633656570947595854738882560 

noncomputable def Ns222p1070 := BSN.cos_dyadic_bound_f 4088613 8388608 2 1 8388608 2890000 Ns222p1067 Ns222p1068 Ns222p1067 Ns222p1067 Ns222p1069 Ns222p1067 7411780 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 4088613) (BSN.cosEvenQ 8388608) 0 1 Ns222p1067 Ns222p1068 Ns222p1067 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 4088613) (BSN.cosOddQ 8388608) 0 1 Ns222p1067 Ns222p1069 Ns222p1067 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1071 := @Enclosure.Real.IsNear.inv_image (Real.cos qz134) 1852945 2097152 35186701 3030384640000 9494051 9494301 8388608 (Ns222p1060 (@Ns222p1061 2890000 (Ns222p1066 rfl) (Enclosure.sfrac_false_div 4088613 8388608) (Ns222p1070 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns222p1072 := @Enclosure.Real.IsNear.recentre' qz135 Bool.false 5584758 8388608 

noncomputable abbrev qz136 := (@HMul.hMul Real Real Real qz343 qz341 qz483)

noncomputable def Ns222p1073 := @Enclosure.Real.IsNear.cos_image qz136 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7065649)) qz370) Bool.true 7065649 8388608 

noncomputable def Ns222p1074 := nat_lit 8341646030568022981046714245 

noncomputable def Ns222p1075 := nat_lit 3922453991373631507589104255196573 

noncomputable def Ns222p1076 := @Enclosure.Real.IsNear.recentre' qz136 Bool.true Ns222p1074 Ns222p858 Ns222p1075 

noncomputable abbrev qz137 := qz483

noncomputable def Ns222p1077 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz137 884279719003555 140737488355328 1 500000000000000 9433266251959 

noncomputable abbrev qz484 := (@HSub.hSub Real Real Real qz634 qz710 qz704)

noncomputable abbrev qz138 := qz484

noncomputable def Ns222p1078 := @Enclosure.Real.IsNear.subLit_tf qz138 qz25 5035219740855 70368744177664 145351035 70368744177664 1 16 

noncomputable abbrev qz485 := qz710

noncomputable abbrev qz139 := qz485

noncomputable def Ns222p1079 := @Enclosure.Real.IsNear.subLit_ff_n qz139 qz129 423440422729 70368744177664 19521915 70368744177664 650723 8388608 15 8388608 

noncomputable def Ns222p1080 := @Enclosure.Real.IsNear.mulLit_ff qz129 qz129 650723 8388608 15 8388608 650723 8388608 15 8388608 423440422729 70368744177664 

noncomputable def Ns222p1081 := nat_lit 20739926550774971332840772526136352208728176453668504862081 

noncomputable def Ns222p1082 := nat_lit 6211785828801184396931110184828150677208623789279804801 

noncomputable def Ns222p1083 := nat_lit 62207356080667311629728455358039400324830112113426954976641 

noncomputable def Ns222p1084 := BSN.cos_dyadic_bound_f 7065649 8388608 3 2 8388608 2890000 Ns222p1081 Ns222p642 Ns222p1082 Ns222p1083 Ns222p645 Ns222p1082 5584758 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 7065649) (BSN.cosEvenQ 8388608) 0 2 Ns222p1081 Ns222p642 Ns222p1082 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 7065649) (BSN.cosOddQ 8388608) 0 2 Ns222p1083 Ns222p645 Ns222p1082 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1085 := @Ns222p1072 323398608 24243077120000 2792379 4194304 20212413 1515192320000 (@Ns222p1073 109 8388608 Bool.false 5584758 8388608 1 2890000 (@Ns222p1076 Ns222p281 7065649 8388608 109 8388608 (@Ns222p1077 70368744177664 145351035 70368744177664 Ns222p1074 Ns222p858 Ns222p1075 Ns222p281 RS223to240.d39 (@Ns222p1078 0 1 150932260031344 9433266251959 70368744177664 145351035 70368744177664 (@Ns222p1079 42238484599894179840 5035219740855 70368744177664 145351035 70368744177664 (@Ns222p1080 19521915 70368744177664 (Ns222p1065 rfl rfl) (Ns222p1065 rfl rfl) rfl) (Ns222p1065 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7065649 8388608) (BSN.cos_neg_of_bound 7065649 8388608 Bool.false 5584758 8388608 1 2890000 (Ns222p1084 rfl rfl)) rfl rfl) 

noncomputable def Ns222p1086 := @Ns222p1051 89016288401259377649 Ns222p978 (Ns222p1052 qz61 (@Enclosure.Real.IsNear.of_eq qz708 (@Inv.inv Real Real.instInv (Real.sqrt qz133)) Bool.false 5568459 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz128 (BSN.t_div_two_pi_nonneg qz127 517749 1000 qz130)) Ns222p1056) rfl) (@Ns222p1057 1099511627776 317996097177063 12710354417090560000 (BSN.correction_mk qz129 (BSN.cos_two_pi_p_ne_zero_mk qz127 517749 1000 9 qz130 rfl rfl (@BSN.floor_sqrt_eq_dec qz127 517749 1000 9 qz130 rfl rfl rfl))) (@Ns222p1058 8388608 2792379 4194304 20212413 1515192320000 828479302647 1099511627776 317996097177063 12710354417090560000 (@Ns222p1059 8388608 (Ns222p1071 rfl rfl rfl rfl rfl) rfl) (Ns222p1085 rfl) rfl)) 

noncomputable def Ns222p1087 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz127) (hardyZApproximantRS₀ qz127) Bool.true 7171163943975227939 18446744073709551616 15780107695729769329649 Ns222p978 (@Eq.refl Real (hardyZApproximantRS₀ qz127)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz127) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz127) qz127 9) (@HMul.hMul Real Real Real qz4 qz705 (Zeta.RiemannSiegel.correction qz129))) Bool.true 7171163943975227939 18446744073709551616 15780107695729769329649 Ns222p978 (BSN.hardyZApproximantRS₀_eq qz127 9 (@BSN.floor_sqrt_eq_dec qz127 517749 1000 9 qz130 rfl rfl rfl)) (@Ns222p980 7171163943975227939 18446744073709551616 15780107695729769329649 Ns222p978 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz127) qz127 9) (@HAdd.hAdd Real Real Real qz358 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 9)) Bool.true 42871823 67108864 98761 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz127) qz127 9) (Ns222p1050 (Ns222p1049 rfl) rfl rfl)) (Ns222p1086 rfl) rfl rfl)) 

theorem RS223to240.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz127) Bool.true 7171163943975227939 18446744073709551616 15780107695729769329649 Ns222p978 := Ns222p1087 

noncomputable def Ns222p1088 := nat_lit 55433736069256465351595524096 

noncomputable abbrev qz887 := (Enclosure.sfrac Bool.false 519173 1000)

noncomputable abbrev qz711 := qz887

noncomputable abbrev qz486 := qz711

noncomputable abbrev qz140 := qz486

noncomputable abbrev qz888 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 519173 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz712 := qz888

noncomputable abbrev qz487 := qz712

noncomputable abbrev qz141 := qz487

noncomputable abbrev qz889 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 519173 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz713 := qz889

noncomputable abbrev qz488 := qz713

noncomputable abbrev qz142 := qz488

noncomputable abbrev qz714 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz141 qz8))

noncomputable def Ns222p1089 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz140) qz140 9) (@HMul.hMul Real Real Real qz4 qz714 (Zeta.RiemannSiegel.correction qz142)) 85791323 33554432 99031 67108864 142797158277809707035 590295810358705651712 903700101987837971649 Ns222p874 Ns222p1088 

noncomputable def Ns222p1090 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz140) qz140 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 519173 1000 123 162 134217728 67108864 2251799813685248 Bool.false 118907394753 1805 

noncomputable def Ns222p1091 := Ns222p1090 279097919 47 47453128 8 294906479 47 44739240 8 Bool.false 192977233 81011 Bool.true 60777309 Bool.true 45834979 7074237752028440 1 Bool.false 58721419 Bool.false Bool.false 126467232 Bool.true Bool.false 171582646 

noncomputable def Ns222p1092 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz140) qz140 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 519173 1000 28 79 134217728 67108864 2251799813685248 Bool.false 118907394753 1805 

noncomputable def Ns222p1093 := Ns222p1092 240485871 47 54794152 8 261175631 47 50729528 8 Bool.false 128839215 60388 Bool.true 43172355 Bool.true 32472703 7074237752028440 1 Bool.false 127333997 Bool.false Bool.false 32156829 Bool.false Bool.false 192977233 

noncomputable def Ns222p1094 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz140) qz140 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 519173 1000 105 32 134217728 67108864 2251799813685248 Bool.false 118907394753 1805 

noncomputable def Ns222p1095 := Ns222p1094 186065264 47 67108856 8 216015088 47 60023992 8 Bool.false 133117391 35545 Bool.false 170318462 Bool.false 11674618 7074237752028440 1 Bool.false 128150496 Bool.true Bool.false 133710303 Bool.false Bool.false 128839215 

noncomputable def Ns222p1096 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz140) qz140 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 519173 1000 334 200 134217728 67108864 2251799813685248 Bool.false 118907394753 1805 

noncomputable def Ns222p1097 := Ns222p1096 93032624 47 94906264 8 147453232 47 77490640 16 Bool.false 134217720 1855 Bool.false 190577732 Bool.false 187915109 7074237752028440 1 Bool.false 20174233 Bool.true Bool.false 22802463 Bool.false Bool.false 133117391 

noncomputable def Ns222p1098 := nat_lit 7031938513639060052632053527944969891536690720515619983 

noncomputable def Ns222p1099 := nat_lit 7937360100191872664436348566940211166125543611432960 

noncomputable def Ns222p1100 := nat_lit 18105175985571030235361305804640000 

noncomputable def Ns222p1101 := nat_lit 56398335603033961152422282956850176320 

noncomputable abbrev qz715 := (@Eq.refl Real qz887)

noncomputable abbrev qz489 := qz715

noncomputable abbrev qz143 := qz489

noncomputable def Ns222p1102 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz140 519173 1000 1078163415716 16000000 1038346 4000 2000 Ns222p1100 Ns222p1101 qz143 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns222p1103 := nat_lit 2250220324364499216842257128942390365291741030564998394560 

noncomputable abbrev qz490 := (Enclosure.sfrac Bool.false 519173 2000)

noncomputable abbrev qz716 := (Real.log (Enclosure.sfrac Bool.false 1078163415716 16000000))

noncomputable abbrev qz144 := (@HSub.hSub Real Real Real qz347 (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 519173 4000) qz716) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1038346)))))) qz490)

noncomputable abbrev qz491 := (@HSub.hSub Real Real Real qz11 qz144 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 519173 2000) (Real.log Real.pi)))

noncomputable def Ns222p1104 := @Enclosure.Real.IsNear.addLit_ft_p qz491 (Enclosure.sfrac Bool.true Ns222p1100 Ns222p1101) 39898715373226125583 45035996273704960 7952796277110222049 591872000000000000000000 Ns222p1100 Ns222p1101 0 1 Ns222p1103 

noncomputable def Ns222p1105 := nat_lit 66938936593913532574911692800000 

noncomputable abbrev qz492 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 519173 2000) (Real.log Real.pi))

noncomputable def Ns222p1106 := @Enclosure.Real.IsNear.subLit_ff_p qz144 qz492 1332036274022432981623 1125899906842624000 1647416225200113 289000000000000000000 19941830020653 67108864000 519173 67108864000 Ns222p1105 39898715373226125583 45035996273704960 

noncomputable def Ns222p1107 := nat_lit 2664072548044865963246000 

noncomputable abbrev qz145 := (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 519173 4000) qz716) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1038346))))))

noncomputable def Ns222p1108 := @Enclosure.Real.IsNear.subLit_ff_p qz145 qz490 1624304690190035796599 1125899906842624000 1647416225200113 289000000000000000000 519173 2000 0 1 Ns222p1107 1332036274022432981623 1125899906842624000 1647416225200113 289000000000000000000 

noncomputable def Ns222p1109 := nat_lit 3657608998737997081588275885534871552 

noncomputable def Ns222p1110 := nat_lit 26882111878622134294020096 

noncomputable def Ns222p1111 := nat_lit 13569061627080099203377968 

noncomputable def Ns222p1112 := BSN.log_dyadic_bound 29587415716 2126739415716 2 1 Ns222p1111 67108864 23120000 875415168751403792656 875415168751403792656 1867371 2156326831432 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 29587415716) (BSN.artanhQ 2126739415716) 0 1 875415168751403792656 Ns222p1111 875415168751403792656 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns222p1113 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 519173 4000) qz716 519173 4000 0 1 3129489705737463 281474976710656 781250289 18062500000000000 1624746558996835878099 1125899906842624000 405604056290997 72250000000000000000 (Enclosure.Real.IsNear.const Bool.false 519173 4000) (BSN.isNear_log_sfrac 1078163415716 16000000 3129489705737463 281474976710656 781250289 18062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1078163415716) qz354)) Bool.false Ns222p1110 Ns222p89 1000000369920000 23120000000000000000000 3129489705737463 281474976710656 781250289 18062500000000000 (BSN.log_rat_reduce_isNear 1078163415716 16000000 16 2156326831432 2097152000000 1867371 67108864 24973259072661432 36028797018963968 23120000 1000000000000000 rfl rfl rfl rfl (Ns222p1112 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns222p1114 := BSN.arctan_dyadic_bound_f 1000 1038346 1 0 8388608 2890000 0 1 1 0 1 1 8078 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1038346) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1038346) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz493 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1038346)))

noncomputable def Ns222p1115 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz493 884279719003555 562949953421312 1 2000000000000000 8078 8388608 1 2890000 7413328415347236143104 883737613600163 562949953421312 200000000289 578000000000000000 qz16 (Ns222p1114 rfl) rfl rfl 

noncomputable def Ns222p1116 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 519173 4000) qz716) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz493)) 1624746558996835878099 1125899906842624000 405604056290997 72250000000000000000 883737613600163 2251799813685248 200000000289 2312000000000000000 Ns222p1109 1624304690190035796599 1125899906842624000 1647416225200113 289000000000000000000 (Ns222p1113 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz493) 1 4 0 1 883737613600163 562949953421312 200000000289 578000000000000000 883737613600163 2251799813685248 200000000289 2312000000000000000 qz357 Ns222p1115 rfl) 

noncomputable def Ns222p1117 := @Ns222p1104 Ns222p1098 Ns222p1099 7952796277110222049 591872000000000000000000 (@Ns222p1106 7952796277110222049 591872000000000000000000 (Ns222p1108 (Ns222p1116 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 519173 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz490 (Real.log Real.pi) 519173 2000 0 1 38410761 33554432 1 33554432 19941830020653 67108864000 519173 67108864000 (Enclosure.Real.IsNear.const Bool.false 519173 2000) RS223to240.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns222p1100 Ns222p1101) 

noncomputable def Ns222p1118 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz140) Bool.false Ns222p1098 Ns222p1099 7952796277110222049 591872000000000000000000 1857928043 2097152 113 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz140) (@HAdd.hAdd Real Real Real qz358 qz491 (Enclosure.sfrac Bool.true Ns222p1100 Ns222p1101)) Bool.false Ns222p1098 Ns222p1099 7952796277110222049 591872000000000000000000 Ns222p1102 (Ns222p1117 rfl rfl)) 

noncomputable def Ns222p1119 := nat_lit 857137258461943652152852497649365875843379419665697360788795059932423592450126547972661162381106596531411307809274717233921155259170816 

noncomputable def Ns222p1120 := nat_lit 610992994914236642835445484100061782690006853250848039155076396939846517149203743417840113774578209519307771217886101596081750016 

noncomputable def Ns222p1121 := nat_lit 4280360800174396992040347237407316837832391288249249885794983842083026818772726062791175150994728901687176040829054646932693457437720576 

noncomputable def Ns222p1122 := BSN.sin_dyadic_bound_f 53972145928 34359738368 4 3 16777216 5785645 Ns222p1119 Ns222p574 Ns222p1120 Ns222p1121 Ns222p577 Ns222p1120 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53972145928) qz371 0 3 Ns222p1119 Ns222p574 Ns222p1120 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53972145928) qz372 0 3 Ns222p1121 Ns222p577 Ns222p1120 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1123 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz140) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1857928043) qz373) Bool.false 1857928043 2097152 113 8388608 Bool.false 16777215 16777216 1 2890000 (Ns222p1118 rfl) (Enclosure.sfrac_false_div 1857928043 2097152) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1857928043) qz373) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474744016194518611132416) qz698) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 140 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q3 1857928043 2097152 226375608064910080 72057594037927936 140 474744016194518611132416 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 474744016194518611132416 302231454903657293676544 53972145928 34359738368 5785645 5780000 (Ns222p1122 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p1124 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz140) Bool.false Ns222p1098 Ns222p1099 7952796277110222049 591872000000000000000000 118907394753 134217728 1805 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz140) (@HAdd.hAdd Real Real Real qz358 qz491 (Enclosure.sfrac Bool.true Ns222p1100 Ns222p1101)) Bool.false Ns222p1098 Ns222p1099 7952796277110222049 591872000000000000000000 Ns222p1102 (Ns222p1117 rfl rfl)) 

noncomputable def Ns222p1125 := Ns222p1097 35545 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 334 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 20174233 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 200 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 22802463 134217728) qz143 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz140) qz140 1) Bool.false 16777215 16777216 20934913 1515192320000 134217720 134217728 1855 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz140) qz140 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz140)) Bool.false 16777215 16777216 20934913 1515192320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz140) qz140) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz140)) Bool.false 16777215 16777216 334958608 24243077120000 16777215 16777216 20934913 1515192320000 (Ns222p1123 rfl rfl) rfl)) rfl) (Ns222p1124 rfl) RS223to240.d7 

noncomputable def Ns222p1126 := nat_lit 2779350394880528319745193051888381244229873576913253986615439894949315016471671126233628033984269811449856 

noncomputable def Ns222p1127 := nat_lit 2295439501686742164785245670648643402834966521404774313876193592350288505000930971465348086209970176 

noncomputable def Ns222p1128 := nat_lit 16834248123631390489714234269535580326627471682747992588779530894509879684836704814902964803087489491271680 

noncomputable def Ns222p1129 := BSN.cos_dyadic_bound_f 190577732 134217728 4 3 134217728 67108864 Ns222p1126 Ns222p227 Ns222p1127 Ns222p1128 Ns222p230 Ns222p1127 20174233 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 190577732) qz361 0 3 Ns222p1126 Ns222p227 Ns222p1127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 190577732) qz362 0 3 Ns222p1128 Ns222p230 Ns222p1127 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1130 := nat_lit 2626903246810814051040891514789772214474979305031554166555184227583381760854717082419436426545931635812561 

noncomputable def Ns222p1131 := nat_lit 1938832998505012738843248967618244819991911980503327239612394344412127924834232713686786593116547281 

noncomputable def Ns222p1132 := nat_lit 15912292307609108984329800429253026767824958684337610605102330042622803096926890823927014293369451286522065 

noncomputable def Ns222p1133 := BSN.cos_dyadic_bound_f 187915109 134217728 4 3 134217728 67108864 Ns222p1130 Ns222p227 Ns222p1131 Ns222p1132 Ns222p230 Ns222p1131 22802463 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 187915109) qz361 0 3 Ns222p1130 Ns222p227 Ns222p1131 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 187915109) qz362 0 3 Ns222p1132 Ns222p230 Ns222p1131 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1134 := nat_lit 826495447985122840717230125573865026486423809798779585447355097678080 

noncomputable def Ns222p1135 := nat_lit 708098727048865343653714379143295299222506969038137432265299722496 

noncomputable def Ns222p1136 := nat_lit 2163484489641052134179210981793890686503797347713599072709881437225216 

noncomputable def Ns222p1137 := BSN.sin_dyadic_bound_f 170318462 134217728 3 2 134217728 67108864 Ns222p1134 Ns222p124 Ns222p1135 Ns222p1136 Ns222p127 Ns222p1135 128150496 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 170318462) qz363 0 2 Ns222p1134 Ns222p124 Ns222p1135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 170318462) qz364 0 2 Ns222p1136 Ns222p127 Ns222p1135 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1138 := nat_lit 18576791915412968959688213776 

noncomputable def Ns222p1139 := BSN.cos_dyadic_bound_f 11674618 134217728 2 1 134217728 67108864 Ns222p1138 Ns222p246 Ns222p1138 Ns222p1138 Ns222p247 Ns222p1138 133710303 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 11674618) qz361 0 1 Ns222p1138 Ns222p246 Ns222p1138 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 11674618) qz362 0 1 Ns222p1138 Ns222p247 Ns222p1138 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1140 := Ns222p1095 60388 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 105 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 128150496 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133710303 134217728) qz143 rfl rfl (Ns222p1125 RS223to240.d9 RS223to240.d11 RS223to240.d13 RS223to240.d17 (Ns222p1129 rfl rfl) (Ns222p1133 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns222p1124 rfl) RS223to240.d19 RS223to240.d21 RS223to240.d23 RS223to240.d25 RS223to240.d17 (Ns222p1137 rfl rfl) (Ns222p1139 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns222p1141 := nat_lit 3473945158559308188784328300625 

noncomputable def Ns222p1142 := BSN.cos_dyadic_bound_f 43172355 134217728 2 1 134217728 67108864 Ns222p1141 Ns222p246 Ns222p1141 Ns222p1141 Ns222p247 Ns222p1141 127333997 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 43172355) qz361 0 1 Ns222p1141 Ns222p246 Ns222p1141 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 43172355) qz362 0 1 Ns222p1141 Ns222p247 Ns222p1141 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1143 := nat_lit 1111920562781242434047848711681 

noncomputable def Ns222p1144 := BSN.sin_dyadic_bound_f 32472703 134217728 2 1 134217728 67108864 Ns222p1143 Ns222p117 Ns222p1143 Ns222p1143 Ns222p118 Ns222p1143 32156829 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 32472703) qz363 0 1 Ns222p1143 Ns222p117 Ns222p1143 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 32472703) qz364 0 1 Ns222p1143 Ns222p118 Ns222p1143 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1145 := Ns222p1093 81011 BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 127333997 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 79 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 32156829 134217728) qz143 rfl rfl (Ns222p1140 rfl rfl) (Ns222p1124 rfl) RS223to240.d27 RS223to240.d29 RS223to240.d31 RS223to240.d33 RS223to240.d17 (Ns222p1142 rfl rfl) (Ns222p1144 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p1146 := nat_lit 13644758979303816319297249553361 

noncomputable def Ns222p1147 := BSN.sin_dyadic_bound_f 60777309 134217728 2 1 134217728 67108864 Ns222p1146 Ns222p117 Ns222p1146 Ns222p1146 Ns222p118 Ns222p1146 58721419 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 60777309) qz363 0 1 Ns222p1146 Ns222p117 Ns222p1146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 60777309) qz364 0 1 Ns222p1146 Ns222p118 Ns222p1146 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1148 := nat_lit 2406248499577722982295712389308956128616792356043921776054186247841 

noncomputable def Ns222p1149 := nat_lit 19479432202213304901315362755807786248798650176438089908979361 

noncomputable def Ns222p1150 := nat_lit 7218706539868764520277334537201356770277879470831412451982740784801 

noncomputable def Ns222p1151 := BSN.cos_dyadic_bound_f 45834979 134217728 3 2 134217728 67108864 Ns222p1148 Ns222p105 Ns222p1149 Ns222p1150 Ns222p108 Ns222p1149 126467232 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 45834979) qz361 0 2 Ns222p1148 Ns222p105 Ns222p1149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 45834979) qz362 0 2 Ns222p1150 Ns222p108 Ns222p1149 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1152 := Ns222p1091 99031 BSN.abs_quadSignPos qz664 (BSN.sfrac_eq_quadSignPos_mul Bool.false 58721419 134217728) BSN.abs_quadSignNeg qz408 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 126467232 134217728) qz143 rfl rfl (Ns222p1145 rfl) (Ns222p1124 rfl) RS223to240.d35 RS223to240.d37 RS223to240.d46 RS223to240.d48 RS223to240.d17 (Ns222p1147 rfl rfl) (Ns222p1151 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p1153 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz140) qz140 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz140) qz140 9) 171582646 134217728 99031 134217728 171582646 134217728 99031 134217728 46058865820696576 85791323 33554432 99031 67108864 (Ns222p1152 rfl) 

noncomputable def Ns222p1154 := @Enclosure.Real.IsNear.mulLit_tf qz714 (Zeta.RiemannSiegel.correction qz142) 5564637 16777216 1 16777216 25661540596055 35184372088832 161567560408723 6355177208545280000 142797158277809707035 590295810358705651712 

noncomputable abbrev qz717 := (@HPow.hPow Real Real Real qz6 qz141 qz8)

noncomputable def Ns222p1155 := @Enclosure.Real.IsNear.mulLit_tf qz48 qz717 1 1 0 1 5564637 16777216 1 16777216 5564637 16777216 1 16777216 

noncomputable def Ns222p1156 := @Enclosure.Real.IsNear.sqrt_image qz141 1386283803621 16777216000 519173 16777216000 76252826 76252855 8388608 (@Enclosure.Real.IsNear.of_eq qz141 (@HMul.hMul Real Real Real qz4 qz140 qz2) Bool.false 1386283803621 16777216000 519173 16777216000 (BSN.t_div_two_pi_mk qz140 519173 1000 qz143) (@Enclosure.Real.IsNear.mulLit_ff qz140 qz2 519173 1000 0 1 2670177 16777216 1 16777216 1386283803621 16777216000 519173 16777216000 (Enclosure.Real.IsNear.const Bool.false 519173 1000) RS223to240.d40 rfl)) 

noncomputable abbrev qz890 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 519173 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz718 := qz890

noncomputable abbrev qz494 := qz718

noncomputable abbrev qz146 := qz494

noncomputable def Ns222p1157 := @Enclosure.Real.IsNear.sqrt_image qz146 152505681 16777216 29 16777216 25291403 25291408 8388608 (@Enclosure.Real.IsNear.recentre' qz146 Bool.false 152505681 16777216 29 16777216 152505681 16777216 29 16777216 (Ns222p1156 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns222p1158 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz146) 50582811 16777216 5 16777216 2782318 2782319 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz146) Bool.false 50582811 16777216 5 16777216 50582811 16777216 5 16777216 (Ns222p1157 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns222p1159 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz146)) Bool.false 5564637 16777216 1 16777216 5564637 16777216 1 16777216 (Ns222p1158 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz147 := (@HMul.hMul Real Real Real qz343 qz341 qz488)

noncomputable abbrev qz719 := (@HMul.hMul Real Real Real qz848 qz889 qz889)

noncomputable abbrev qz495 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz719 qz713) qz639)

noncomputable abbrev qz148 := (Real.cos (@HMul.hMul Real Real Real qz343 qz341 qz495))

noncomputable def Ns222p1160 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz142) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz147)) qz148) Bool.false 25661540596055 

noncomputable def Ns222p1161 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz147)) qz148 9937109 8388608 133 

noncomputable def Ns222p1162 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz147)) Bool.false 19874218 16777216 266 16777216 9937109 8388608 133 

noncomputable def Ns222p1163 := @Enclosure.Real.IsNear.recentre' (Real.cos qz147) Bool.false 7081410 8388608 545647216 48486154240000 3540705 4194304 34102951 3030384640000 

noncomputable def Ns222p1164 := @Enclosure.Real.IsNear.cos_image qz147 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 593265) qz645) Bool.false 593265 1048576 183 16777216 Bool.false 7081410 8388608 1 

noncomputable def Ns222p1165 := nat_lit 782596186875254450215614347 

noncomputable def Ns222p1166 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz142 884279719003555 140737488355328 1 500000000000000 1510737 16777216 29 16777216 1335914089848273670035 2361183241434822606848 Ns222p1165 

noncomputable def Ns222p1167 := @Enclosure.Real.IsNear.subLit_ff_p qz146 qz46 152505681 16777216 29 16777216 9 1 0 1 1510737 1510737 16777216 29 

noncomputable def Ns222p1168 := @Ns222p1167 16777216 (@Enclosure.Real.IsNear.recentre' qz146 Bool.false 152505681 16777216 29 16777216 152505681 16777216 29 16777216 (Ns222p1156 rfl rfl rfl rfl rfl rfl) rfl) qz411 

noncomputable def Ns222p1169 := @Enclosure.Real.IsNear.recentre' qz147 Bool.false 1335914089848273670035 2361183241434822606848 Ns222p1165 Ns222p150 593265 1048576 183 16777216 (@Ns222p1166 Ns222p150 RS223to240.d39 (Ns222p1168 rfl rfl) rfl) 

noncomputable def Ns222p1170 := nat_lit 251611411412242814167085119901401337138068991690625 

noncomputable def Ns222p1171 := nat_lit 15345810154885783274179025337327946592562890625 

noncomputable def Ns222p1172 := nat_lit 754803542616418670934707001653529355521021849290625 

noncomputable def Ns222p1173 := BSN.cos_dyadic_bound_f 593265 1048576 3 2 8388608 2890000 Ns222p1170 Ns222p752 Ns222p1171 Ns222p1172 Ns222p755 Ns222p1171 7081410 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 593265) (BSN.cosEvenQ 1048576) 0 2 Ns222p1170 Ns222p752 Ns222p1171 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 593265) (BSN.cosOddQ 1048576) 0 2 Ns222p1172 Ns222p755 Ns222p1171 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1174 := @Enclosure.Real.IsNear.inv_image (Real.cos qz147) 3540705 4194304 34102951 3030384640000 9936976 9937242 8388608 (Ns222p1163 (@Ns222p1164 2890000 (Ns222p1169 rfl) (Enclosure.sfrac_false_div 593265 1048576) (Ns222p1173 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns222p1175 := @Enclosure.Real.IsNear.recentre' qz148 Bool.false 5164790 8388608 

noncomputable abbrev qz149 := (@HMul.hMul Real Real Real qz343 qz341 qz495)

noncomputable def Ns222p1176 := @Enclosure.Real.IsNear.cos_image qz149 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7612945)) qz370) Bool.true 7612945 8388608 

noncomputable def Ns222p1177 := nat_lit 35951117730487225390334155645 

noncomputable def Ns222p1178 := nat_lit 3098880398901390232792673103659761 

noncomputable def Ns222p1179 := @Enclosure.Real.IsNear.recentre' qz149 Bool.true Ns222p1177 Ns222p168 Ns222p1178 

noncomputable abbrev qz150 := qz495

noncomputable def Ns222p1180 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz150 884279719003555 140737488355328 1 500000000000000 40655820729439 

noncomputable abbrev qz496 := (@HSub.hSub Real Real Real qz634 qz719 qz713)

noncomputable abbrev qz151 := qz496

noncomputable def Ns222p1181 := @Enclosure.Real.IsNear.subLit_tf qz151 qz25 23063634685023 281474976710656 574162851 281474976710656 1 16 

noncomputable abbrev qz497 := qz719

noncomputable abbrev qz152 := qz497

noncomputable def Ns222p1182 := @Enclosure.Real.IsNear.subLit_ff_n qz152 qz142 2282326283169 281474976710656 87623587 281474976710656 1510737 16777216 29 16777216 

noncomputable def Ns222p1183 := @Enclosure.Real.IsNear.mulLit_ff qz142 qz142 1510737 16777216 29 16777216 1510737 16777216 29 16777216 2282326283169 281474976710656 

noncomputable def Ns222p1184 := nat_lit 27954708924987607454459740106794835528799836603838195690625 

noncomputable def Ns222p1185 := nat_lit 11282920752861524666842476643805963103331454657062890625 

noncomputable def Ns222p1186 := nat_lit 83841560933457099314045535367096894660192846902200461290625 

noncomputable def Ns222p1187 := BSN.cos_dyadic_bound_f 7612945 8388608 3 2 8388608 2890000 Ns222p1184 Ns222p642 Ns222p1185 Ns222p1186 Ns222p645 Ns222p1185 5164790 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 7612945) (BSN.cosEvenQ 8388608) 0 2 Ns222p1184 Ns222p642 Ns222p1185 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 7612945) (BSN.cosOddQ 8388608) 0 2 Ns222p1186 Ns222p645 Ns222p1185 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1188 := @Ns222p1175 80127152 6060769280000 2582395 4194304 5007947 378798080000 (@Ns222p1176 27 2097152 Bool.false 5164790 8388608 1 2890000 (@Ns222p1179 Ns222p171 7612945 8388608 27 2097152 (@Ns222p1180 281474976710656 574162851 281474976710656 Ns222p1177 Ns222p168 Ns222p1178 Ns222p171 RS223to240.d39 (@Ns222p1181 0 1 650493131671024 40655820729439 281474976710656 574162851 281474976710656 (@Ns222p1182 386943580855722835968 23063634685023 281474976710656 574162851 281474976710656 (@Ns222p1183 87623587 281474976710656 (Ns222p1168 rfl rfl) (Ns222p1168 rfl rfl) rfl) (Ns222p1168 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7612945 8388608) (BSN.cos_neg_of_bound 7612945 8388608 Bool.false 5164790 8388608 1 2890000 (Ns222p1187 rfl rfl)) rfl rfl) 

noncomputable def Ns222p1189 := @Ns222p1154 903700101987837971649 Ns222p874 (Ns222p1155 qz61 (@Enclosure.Real.IsNear.of_eq qz717 (@Inv.inv Real Real.instInv (Real.sqrt qz146)) Bool.false 5564637 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz141 (BSN.t_div_two_pi_nonneg qz140 519173 1000 qz143)) Ns222p1159) rfl) (@Ns222p1160 35184372088832 161567560408723 6355177208545280000 (BSN.correction_mk qz142 (BSN.cos_two_pi_p_ne_zero_mk qz140 519173 1000 9 qz143 rfl rfl (@BSN.floor_sqrt_eq_dec qz140 519173 1000 9 qz143 rfl rfl rfl))) (@Ns222p1161 8388608 2582395 4194304 5007947 378798080000 25661540596055 35184372088832 161567560408723 6355177208545280000 (@Ns222p1162 8388608 (Ns222p1174 rfl rfl rfl rfl rfl) rfl) (Ns222p1188 rfl) rfl)) 

noncomputable def Ns222p1190 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz140) (hardyZApproximantRS₀ qz140) Bool.false 1652054073490395109403 590295810358705651712 158243588636849743891649 Ns222p874 (@Eq.refl Real (hardyZApproximantRS₀ qz140)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz140) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz140) qz140 9) (@HMul.hMul Real Real Real qz4 qz714 (Zeta.RiemannSiegel.correction qz142))) Bool.false 1652054073490395109403 590295810358705651712 158243588636849743891649 Ns222p874 (BSN.hardyZApproximantRS₀_eq qz140 9 (@BSN.floor_sqrt_eq_dec qz140 519173 1000 9 qz143 rfl rfl rfl)) (@Ns222p1089 1652054073490395109403 590295810358705651712 158243588636849743891649 Ns222p874 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz140) qz140 9) (@HAdd.hAdd Real Real Real qz358 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz140) qz140 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz140) qz140 9)) Bool.false 85791323 33554432 99031 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz140) qz140 9) (Ns222p1153 (Ns222p1152 rfl) rfl rfl)) (Ns222p1189 rfl) rfl rfl)) 

theorem RS223to240.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz140) Bool.false 1652054073490395109403 590295810358705651712 158243588636849743891649 Ns222p874 := Ns222p1190 

noncomputable def Ns222p1191 := nat_lit 118448019303194788420978212864 

noncomputable abbrev qz891 := (Enclosure.sfrac Bool.false 520596 1000)

noncomputable abbrev qz720 := qz891

noncomputable abbrev qz498 := qz720

noncomputable abbrev qz153 := qz498

noncomputable abbrev qz892 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 520596 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz721 := qz892

noncomputable abbrev qz499 := qz721

noncomputable abbrev qz154 := qz499

noncomputable abbrev qz893 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 520596 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz722 := qz893

noncomputable abbrev qz500 := qz722

noncomputable abbrev qz155 := qz500

noncomputable abbrev qz723 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz154 qz8))

noncomputable def Ns222p1192 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz153) qz153 9) (@HMul.hMul Real Real Real qz4 qz723 (Zeta.RiemannSiegel.correction qz155)) 116037051 67108864 49651 33554432 276332360508503371215 1180591620717411303424 1975301397696324397761 Ns222p433 Ns222p1191 

noncomputable def Ns222p1193 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz153) qz153 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 520596 1000 123 162 134217728 67108864 2251799813685248 Bool.false 119329078721 1809 

noncomputable def Ns222p1194 := Ns222p1193 279097919 47 47453128 8 294906479 47 44739240 8 Bool.true 86320259 81233 Bool.true 36249680 Bool.true 43802930 7074237752028440 1 Bool.false 35810586 Bool.false Bool.false 127133241 Bool.true Bool.true 116037051 

noncomputable def Ns222p1195 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz153) qz153 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 520596 1000 27 78 134217728 67108864 2251799813685248 Bool.false 119329078721 1809 

noncomputable def Ns222p1196 := Ns222p1195 240485871 47 54794152 8 261175631 47 50729528 8 Bool.true 132505056 60554 Bool.true 174528496 Bool.true 193270372 7074237752028440 1 Bool.false 129338740 Bool.false Bool.false 17508303 Bool.true Bool.true 86320259 

noncomputable def Ns222p1197 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz153) qz153 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 520596 1000 106 32 134217728 67108864 2251799813685248 Bool.false 119329078721 1809 

noncomputable def Ns222p1198 := Ns222p1197 186065264 47 67108856 8 216015088 47 60023992 8 Bool.true 124563569 35644 Bool.false 116402845 Bool.false 125969116 7074237752028440 1 Bool.false 86827017 Bool.true Bool.false 79317841 Bool.false Bool.true 132505056 

noncomputable def Ns222p1199 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz153) qz153 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 520596 1000 336 201 134217728 67108864 2251799813685248 Bool.false 119329078721 1809 

noncomputable def Ns222p1200 := Ns222p1199 93032624 47 94906264 8 147453232 47 77490640 16 Bool.true 134217720 1863 Bool.false 58218848 Bool.false 188944413 7074237752028440 1 Bool.false 121787840 Bool.false Bool.false 132437551 Bool.true Bool.true 124563569 

noncomputable def Ns222p1201 := nat_lit 38007773862146452052240850451021774525072515766119 

noncomputable def Ns222p1202 := nat_lit 42749991106769927129135993726965489501995008000 

noncomputable def Ns222p1203 := nat_lit 18354661799984495845041008148480000 

noncomputable def Ns222p1204 := nat_lit 57332205766577920937869540384812564480 

noncomputable abbrev qz894 := (@Eq.refl Real (Enclosure.sfrac Bool.false 520596 1000))

noncomputable abbrev qz724 := qz894

noncomputable abbrev qz501 := qz724

noncomputable abbrev qz156 := qz501

noncomputable def Ns222p1205 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz153 520596 1000 1084081780864 16000000 1041192 4000 2000 Ns222p1203 Ns222p1204 qz156 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns222p1206 := nat_lit 3586863553674667029641745180227754741996219446277659688960 

noncomputable abbrev qz502 := (Enclosure.sfrac Bool.false 520596 2000)

noncomputable abbrev qz725 := (Real.log (Enclosure.sfrac Bool.false 1084081780864 16000000))

noncomputable abbrev qz157 := (@HSub.hSub Real Real Real qz347 (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 520596 4000) qz725) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1041192)))))) qz502)

noncomputable abbrev qz503 := (@HSub.hSub Real Real Real qz11 qz157 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 520596 2000) (Real.log Real.pi)))

noncomputable def Ns222p1207 := @Enclosure.Real.IsNear.addLit_ft_p qz503 (Enclosure.sfrac Bool.true Ns222p1203 Ns222p1204) 62562826552892675127 70368744177664000 1993613435732582337 147968000000000000000000 Ns222p1203 Ns222p1204 0 1 Ns222p1206 

noncomputable def Ns222p1208 := nat_lit 1049630054648415835423506432000 

noncomputable abbrev qz504 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 520596 2000) (Real.log Real.pi))

noncomputable def Ns222p1209 := @Enclosure.Real.IsNear.subLit_ff_p qz157 qz504 83530664513454691383 70368744177664000 1651863101845101 289000000000000000000 4999122133389 16777216000 130149 16777216000 Ns222p1208 62562826552892675127 70368744177664000 

noncomputable abbrev qz158 := (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 520596 4000) qz725) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1041192))))))

noncomputable def Ns222p1210 := @Enclosure.Real.IsNear.subLit_ff_p qz158 qz502 20369501577082455051 14073748835532800 1651863101845101 289000000000000000000 520596 2000 0 1 33412265805381876553200 83530664513454691383 70368744177664000 1651863101845101 289000000000000000000 

noncomputable def Ns222p1211 := nat_lit 183472159424542550344461214487150592 

noncomputable def Ns222p1212 := nat_lit 26895347885869382143836160 

noncomputable def Ns222p1213 := nat_lit 13644687630839283133759488 

noncomputable def Ns222p1214 := BSN.log_dyadic_bound 35505780864 2132657780864 2 1 Ns222p1213 67108864 23120000 1260660474762388586496 1260660474762388586496 2234744 2168163561728 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 35505780864) (BSN.artanhQ 2132657780864) 0 1 1260660474762388586496 Ns222p1213 1260660474762388586496 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns222p1215 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 520596 4000) qz725 520596 4000 0 1 3131030579780855 281474976710656 781250289 18062500000000000 81500099785579699479 56294995342131200 101678943863061 18062500000000000000 (Enclosure.Real.IsNear.const Bool.false 520596 4000) (BSN.isNear_log_sfrac 1084081780864 16000000 3131030579780855 281474976710656 781250289 18062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1084081780864) qz354)) Bool.false Ns222p1212 Ns222p89 1000000369920000 23120000000000000000000 3131030579780855 281474976710656 781250289 18062500000000000 (BSN.log_rat_reduce_isNear 1084081780864 16000000 16 2168163561728 2097152000000 2234744 67108864 24973259072661432 36028797018963968 23120000 1000000000000000 rfl rfl rfl rfl (Ns222p1214 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns222p1216 := BSN.arctan_dyadic_bound_f 1000 1041192 1 0 8388608 2890000 0 1 1 0 1 1 8056 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1041192) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1041192) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz505 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1041192)))

noncomputable def Ns222p1217 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz505 884279719003555 562949953421312 1 2000000000000000 8056 8388608 1 2890000 7413340800246211411968 883739089995171 562949953421312 200000000289 578000000000000000 qz16 (Ns222p1216 rfl) rfl rfl 

noncomputable def Ns222p1218 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 520596 4000) qz725) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz505)) 81500099785579699479 56294995342131200 101678943863061 18062500000000000000 883739089995171 2251799813685248 200000000289 2312000000000000000 Ns222p1211 20369501577082455051 14073748835532800 1651863101845101 289000000000000000000 (Ns222p1215 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz505) 1 4 0 1 883739089995171 562949953421312 200000000289 578000000000000000 883739089995171 2251799813685248 200000000289 2312000000000000000 qz357 Ns222p1217 rfl) 

noncomputable def Ns222p1219 := @Ns222p1207 Ns222p1201 Ns222p1202 1993613435732582337 147968000000000000000000 (@Ns222p1209 1993613435732582337 147968000000000000000000 (Ns222p1210 (Ns222p1218 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 520596 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz502 (Real.log Real.pi) 520596 2000 0 1 38410761 33554432 1 33554432 4999122133389 16777216000 130149 16777216000 (Enclosure.Real.IsNear.const Bool.false 520596 2000) RS223to240.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns222p1203 Ns222p1204) 

noncomputable def Ns222p1220 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz153) Bool.false Ns222p1201 Ns222p1202 1993613435732582337 147968000000000000000000 1864516855 2097152 227 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz153) (@HAdd.hAdd Real Real Real qz358 qz503 (Enclosure.sfrac Bool.true Ns222p1203 Ns222p1204)) Bool.false Ns222p1201 Ns222p1202 1993613435732582337 147968000000000000000000 Ns222p1205 (Ns222p1219 rfl rfl)) 

noncomputable def Ns222p1221 := nat_lit 857569804151017083531659641892932312823366232136322550477852428636677215045298653292374849254697160327465106080656763309686784000000000 

noncomputable def Ns222p1222 := nat_lit 611916597280464950745661240340707370954265381213420774508709684013410174388750389434379601556854213232801000000000000000000000000 

noncomputable def Ns222p1223 := nat_lit 4282518161915611987264018040676478816977400157413460879488053858973514684365291790793120553142915122944813640528466946148433920000000000 

noncomputable def Ns222p1224 := BSN.sin_dyadic_bound_f 53978940100 34359738368 4 3 16777216 5785645 Ns222p1221 Ns222p574 Ns222p1222 Ns222p1223 Ns222p577 Ns222p1222 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53978940100) qz371 0 3 Ns222p1221 Ns222p574 Ns222p1222 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53978940100) qz372 0 3 Ns222p1223 Ns222p577 Ns222p1222 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1225 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz153) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1864516855) qz373) Bool.false 1864516855 2097152 227 16777216 Bool.true 16777215 16777216 1 2890000 (Ns222p1220 rfl) (Enclosure.sfrac_false_div 1864516855 2097152) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1864516855) qz373) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474803778361890082652160) qz698) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 141 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q1 1864516855 2097152 226375608064910080 72057594037927936 141 474803778361890082652160 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 474803778361890082652160 302231454903657293676544 53978940100 34359738368 5785645 5780000 (Ns222p1224 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p1226 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz153) Bool.false Ns222p1201 Ns222p1202 1993613435732582337 147968000000000000000000 119329078721 134217728 1809 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz153) (@HAdd.hAdd Real Real Real qz358 qz503 (Enclosure.sfrac Bool.true Ns222p1203 Ns222p1204)) Bool.false Ns222p1201 Ns222p1202 1993613435732582337 147968000000000000000000 Ns222p1205 (Ns222p1219 rfl rfl)) 

noncomputable def Ns222p1227 := Ns222p1200 35644 BSN.abs_quadSignPos (BSN.cos_quad_nat0 336 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 121787840 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 201 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132437551 134217728) qz156 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz153) qz153 1) Bool.true 16777215 16777216 42050451 3030384640000 134217720 134217728 1863 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz153) qz153 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz153)) Bool.true 16777215 16777216 42050451 3030384640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz153) qz153) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz153)) Bool.true 16777215 16777216 672807216 48486154240000 16777215 16777216 42050451 3030384640000 (Ns222p1225 rfl rfl) rfl)) rfl) (Ns222p1226 rfl) RS223to240.d7 

noncomputable def Ns222p1228 := nat_lit 6263432411050793404221909984846472830310611016265486653699586523136 

noncomputable def Ns222p1229 := nat_lit 131980223966514554412604503496496342929635745000144033709817856 

noncomputable def Ns222p1230 := nat_lit 18790033272704447183556904745532425498245973777306459673031339933696 

noncomputable def Ns222p1231 := BSN.cos_dyadic_bound_f 58218848 134217728 3 2 134217728 67108864 Ns222p1228 Ns222p105 Ns222p1229 Ns222p1230 Ns222p108 Ns222p1229 121787840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 58218848) qz361 0 2 Ns222p1228 Ns222p105 Ns222p1229 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 58218848) qz362 0 2 Ns222p1230 Ns222p108 Ns222p1229 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1232 := nat_lit 6973938947330961175542222511011278122141570036115265816077562362914836888971838255711007086310951151872881 

noncomputable def Ns222p1233 := nat_lit 2070182603076531754206938274504241457373687501916417667423402608922103894213781778528257084365876081 

noncomputable def Ns222p1234 := nat_lit 34841727851881883069079595671476359822161892101009728482323852518127622076637905763729029421472199833693041 

noncomputable def Ns222p1235 := BSN.sin_dyadic_bound_f 188944413 134217728 4 3 134217728 67108864 Ns222p1232 Ns222p111 Ns222p1233 Ns222p1234 Ns222p114 Ns222p1233 132437551 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 188944413) qz363 0 3 Ns222p1232 Ns222p111 Ns222p1233 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 188944413) qz364 0 3 Ns222p1234 Ns222p114 Ns222p1233 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1236 := nat_lit 100126587973416285168860927145691922590209103083789664139436200190625 

noncomputable def Ns222p1237 := nat_lit 33706119813943890071414024021378201846710012086931002790875390625 

noncomputable def Ns222p1238 := nat_lit 300312351680620967726439953389033011366933889227195130412726849790625 

noncomputable def Ns222p1239 := BSN.cos_dyadic_bound_f 116402845 134217728 3 2 134217728 67108864 Ns222p1236 Ns222p105 Ns222p1237 Ns222p1238 Ns222p108 Ns222p1237 86827017 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 116402845) qz361 0 2 Ns222p1236 Ns222p105 Ns222p1237 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 116402845) qz362 0 2 Ns222p1238 Ns222p108 Ns222p1237 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1240 := nat_lit 137342729998950325052345591637136865499434779021954690726628362878976 

noncomputable def Ns222p1241 := nat_lit 63403415450752972926622554928449422706952425202927284224325124096 

noncomputable def Ns222p1242 := nat_lit 411901383165949469211183529801553697652890432215458217611436438388736 

noncomputable def Ns222p1243 := BSN.cos_dyadic_bound_f 125969116 134217728 3 2 134217728 67108864 Ns222p1240 Ns222p105 Ns222p1241 Ns222p1242 Ns222p108 Ns222p1241 79317841 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 125969116) qz361 0 2 Ns222p1240 Ns222p105 Ns222p1241 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 125969116) qz362 0 2 Ns222p1242 Ns222p108 Ns222p1241 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1244 := Ns222p1198 60554 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 106 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 86827017 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 79317841 134217728) qz156 rfl rfl (Ns222p1227 RS223to240.d9 RS223to240.d11 RS223to240.d13 RS223to240.d17 (Ns222p1231 rfl rfl) (Ns222p1235 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns222p1226 rfl) RS223to240.d19 RS223to240.d21 RS223to240.d23 RS223to240.d25 RS223to240.d17 (Ns222p1239 rfl rfl) (Ns222p1243 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns222p1245 := nat_lit 5075209821111962120426444482289922703272999442830798317263313520202993759488084675598170075125992407433216 

noncomputable def Ns222p1246 := nat_lit 798722932810425258410582168199847687386489820286556368713576510147490031922078836805481143484809216 

noncomputable def Ns222p1247 := nat_lit 25361228448862579961634183086675297059549171685456945365659364703243247067491808102471490748682016785432576 

noncomputable def Ns222p1248 := BSN.sin_dyadic_bound_f 174528496 134217728 4 3 134217728 67108864 Ns222p1245 Ns222p111 Ns222p1246 Ns222p1247 Ns222p114 Ns222p1246 129338740 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 174528496) qz363 0 3 Ns222p1245 Ns222p111 Ns222p1246 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 174528496) qz364 0 3 Ns222p1247 Ns222p114 Ns222p1246 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1249 := nat_lit 2940196556407291744143784756291912179000992590397164811997540075394908340473359678939141471111590545719296 

noncomputable def Ns222p1250 := nat_lit 2716335383238376852928398388887518924948411772643813327351142115076964943255834654577503019588386816 

noncomputable def Ns222p1251 := nat_lit 17806823199262466344842945288723278517619271719845326566471123573620692909458563941885910469041663728680960 

noncomputable def Ns222p1252 := BSN.cos_dyadic_bound_f 193270372 134217728 4 3 134217728 67108864 Ns222p1249 Ns222p227 Ns222p1250 Ns222p1251 Ns222p230 Ns222p1250 17508303 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 193270372) qz361 0 3 Ns222p1249 Ns222p227 Ns222p1250 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 193270372) qz362 0 3 Ns222p1251 Ns222p230 Ns222p1250 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1253 := Ns222p1196 81233 BSN.abs_quadSignPos (BSN.cos_quad_nat3 27 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 129338740 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 78 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 17508303 134217728) qz156 rfl rfl (Ns222p1244 rfl rfl) (Ns222p1226 rfl) RS223to240.d27 RS223to240.d29 RS223to240.d31 RS223to240.d33 RS223to240.d17 (Ns222p1248 rfl rfl) (Ns222p1252 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p1254 := nat_lit 1726699282213605248650485760000 

noncomputable def Ns222p1255 := BSN.sin_dyadic_bound_f 36249680 134217728 2 1 134217728 67108864 Ns222p1254 Ns222p117 Ns222p1254 Ns222p1254 Ns222p118 Ns222p1254 35810586 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 36249680) qz363 0 1 Ns222p1254 Ns222p117 Ns222p1254 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 36249680) qz364 0 1 Ns222p1254 Ns222p118 Ns222p1254 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1256 := nat_lit 3681396936737940347926908010000 

noncomputable def Ns222p1257 := BSN.cos_dyadic_bound_f 43802930 134217728 2 1 134217728 67108864 Ns222p1256 Ns222p246 Ns222p1256 Ns222p1256 Ns222p247 Ns222p1256 127133241 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 43802930) qz361 0 1 Ns222p1256 Ns222p246 Ns222p1256 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 43802930) qz362 0 1 Ns222p1256 Ns222p247 Ns222p1256 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1258 := Ns222p1194 99302 BSN.abs_quadSignPos qz664 (BSN.sfrac_eq_quadSignPos_mul Bool.false 35810586 134217728) BSN.abs_quadSignNeg qz408 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 127133241 134217728) qz156 rfl rfl (Ns222p1253 rfl) (Ns222p1226 rfl) RS223to240.d35 RS223to240.d37 RS223to240.d46 RS223to240.d48 RS223to240.d17 (Ns222p1255 rfl rfl) (Ns222p1257 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p1259 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz153) qz153 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz153) qz153 9) 116037051 134217728 99302 134217728 116037051 134217728 99302 134217728 31148458698080256 116037051 67108864 49651 33554432 (Ns222p1258 rfl) 

noncomputable def Ns222p1260 := @Enclosure.Real.IsNear.mulLit_tf qz723 (Zeta.RiemannSiegel.correction qz155) 2780415 8388608 1 8388608 99385293385521 140737488355328 703977364926171 25420708834181120000 276332360508503371215 1180591620717411303424 

noncomputable abbrev qz726 := (@HPow.hPow Real Real Real qz6 qz154 qz8)

noncomputable def Ns222p1261 := @Enclosure.Real.IsNear.mulLit_tf qz48 qz726 1 1 0 1 2780415 8388608 1 8388608 2780415 8388608 1 8388608 

noncomputable def Ns222p1262 := @Enclosure.Real.IsNear.sqrt_image qz154 347520866373 4194304000 130149 4194304000 76357255 76357285 8388608 (@Enclosure.Real.IsNear.of_eq qz154 (@HMul.hMul Real Real Real qz4 qz153 qz2) Bool.false 347520866373 4194304000 130149 4194304000 (BSN.t_div_two_pi_mk qz153 520596 1000 qz156) (@Enclosure.Real.IsNear.mulLit_ff qz153 qz2 520596 1000 0 1 2670177 16777216 1 16777216 347520866373 4194304000 130149 4194304000 (Enclosure.Real.IsNear.const Bool.false 520596 1000) RS223to240.d40 rfl)) 

noncomputable abbrev qz895 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 520596 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz727 := qz895

noncomputable abbrev qz506 := qz727

noncomputable abbrev qz159 := qz506

noncomputable def Ns222p1263 := @Enclosure.Real.IsNear.sqrt_image qz159 38178635 4194304 15 8388608 25308715 25308721 8388608 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 152714540 16777216 30 16777216 38178635 4194304 15 8388608 (Ns222p1262 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns222p1264 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz159) 12654359 4194304 3 8388608 2780414 2780416 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz159) Bool.false 50617436 16777216 6 16777216 12654359 4194304 3 8388608 (Ns222p1263 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns222p1265 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz159)) Bool.false 5560830 16777216 2 16777216 2780415 8388608 1 8388608 (Ns222p1264 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz343 qz341 qz500)

noncomputable abbrev qz728 := (@HMul.hMul Real Real Real qz848 qz893 qz893)

noncomputable abbrev qz507 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz728 qz722) qz639)

noncomputable abbrev qz161 := (Real.cos (@HMul.hMul Real Real Real qz343 qz341 qz507))

noncomputable def Ns222p1266 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz155) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz160)) qz161) Bool.false 99385293385521 

noncomputable def Ns222p1267 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz160)) qz161 20979387 16777216 305 

noncomputable def Ns222p1268 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz160)) Bool.false 20979387 16777216 305 16777216 20979387 16777216 305 

noncomputable def Ns222p1269 := @Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.false 6708370 8388608 562987216 48486154240000 3354185 4194304 35186701 3030384640000 

noncomputable def Ns222p1270 := @Enclosure.Real.IsNear.cos_image qz160 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2701135) qz676) Bool.false 2701135 4194304 189 16777216 Bool.false 6708370 8388608 1 

noncomputable def Ns222p1271 := nat_lit 404791131143046290409866921 

noncomputable def Ns222p1272 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz155 884279719003555 140737488355328 1 500000000000000 429899 4194304 15 8388608 380150966919909290945 590295810358705651712 Ns222p1271 

noncomputable def Ns222p1273 := @Enclosure.Real.IsNear.subLit_ff_p qz159 qz46 38178635 4194304 15 8388608 9 1 0 1 429899 429899 4194304 15 

noncomputable def Ns222p1274 := @Ns222p1273 8388608 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 152714540 16777216 30 16777216 38178635 4194304 15 8388608 (Ns222p1262 rfl rfl rfl rfl rfl rfl) rfl) qz411 

noncomputable def Ns222p1275 := @Enclosure.Real.IsNear.recentre' qz160 Bool.false 380150966919909290945 590295810358705651712 Ns222p1271 Ns222p263 2701135 4194304 189 16777216 (@Ns222p1272 Ns222p263 RS223to240.d39 (Ns222p1274 rfl rfl) rfl) 

noncomputable def Ns222p1276 := nat_lit 27680792795409091907855090970879691260644800650663690625 

noncomputable def Ns222p1277 := nat_lit 3861888762982039923063034508418779142719222587902677483520 

noncomputable def Ns222p1278 := nat_lit 2833807351646588955324500098987237525151289562890625 

noncomputable def Ns222p1279 := nat_lit 83036710771523982545654623912441099306884099372865290625 

noncomputable def Ns222p1280 := nat_lit 173784994334191796537836552878845061422365016455620486758400 

noncomputable def Ns222p1281 := BSN.cos_dyadic_bound_f 2701135 4194304 3 2 8388608 2890000 Ns222p1276 Ns222p1277 Ns222p1278 Ns222p1279 Ns222p1280 Ns222p1278 6708370 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2701135) (BSN.cosEvenQ 4194304) 0 2 Ns222p1276 Ns222p1277 Ns222p1278 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2701135) (BSN.cosOddQ 4194304) 0 2 Ns222p1279 Ns222p1280 Ns222p1278 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1282 := @Enclosure.Real.IsNear.inv_image (Real.cos qz160) 3354185 4194304 35186701 3030384640000 10489541 10489846 8388608 (Ns222p1269 (@Ns222p1270 2890000 (Ns222p1275 rfl) (Enclosure.sfrac_false_div 2701135 4194304) (Ns222p1281 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns222p1283 := @Enclosure.Real.IsNear.recentre' qz161 Bool.false 4737283 8388608 

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz343 qz341 qz507)

noncomputable def Ns222p1284 := @Enclosure.Real.IsNear.cos_image qz162 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 4071379)) qz676) Bool.true 4071379 4194304 

noncomputable def Ns222p1285 := nat_lit 2403318033879043773160556405 

noncomputable def Ns222p1286 := nat_lit 4091717402870360657215746285211123 

noncomputable def Ns222p1287 := @Enclosure.Real.IsNear.recentre' qz162 Bool.true Ns222p1285 Ns222p421 Ns222p1286 

noncomputable abbrev qz163 := qz507

noncomputable def Ns222p1288 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz163 884279719003555 140737488355328 1 500000000000000 2717825572871 

noncomputable abbrev qz508 := (@HSub.hSub Real Real Real qz634 qz728 qz722)

noncomputable abbrev qz164 := qz508

noncomputable def Ns222p1289 := @Enclosure.Real.IsNear.subLit_tf qz164 qz25 1618313945095 17592186044416 151623285 70368744177664 1 16 

noncomputable abbrev qz509 := qz728

noncomputable abbrev qz165 := qz509

noncomputable def Ns222p1290 := @Enclosure.Real.IsNear.subLit_ff_n qz165 qz155 184813150201 17592186044416 25794165 70368744177664 429899 4194304 15 8388608 

noncomputable def Ns222p1291 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz155 429899 4194304 15 8388608 429899 4194304 15 8388608 184813150201 17592186044416 

noncomputable def Ns222p1292 := nat_lit 142936939331805308824717909174017489630100705735107044641 

noncomputable def Ns222p1293 := nat_lit 75497445607580676261780541768537434688278292640720161 

noncomputable def Ns222p1294 := nat_lit 428659823104200765121630166438515394020925560620039693601 

noncomputable def Ns222p1295 := BSN.cos_dyadic_bound_f 4071379 4194304 3 2 8388608 2890000 Ns222p1292 Ns222p1277 Ns222p1293 Ns222p1294 Ns222p1280 Ns222p1293 4737283 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 4071379) (BSN.cosEvenQ 4194304) 0 2 Ns222p1292 Ns222p1277 Ns222p1293 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 4071379) (BSN.cosOddQ 4194304) 0 2 Ns222p1294 Ns222p1280 Ns222p1293 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1296 := @Ns222p1283 168924304 12121538560000 4737283 8388608 10557769 757596160000 (@Ns222p1284 57 4194304 Bool.false 4737283 8388608 1 2890000 (@Ns222p1287 Ns222p281 4071379 4194304 57 4194304 (@Ns222p1288 17592186044416 151623285 70368744177664 Ns222p1285 Ns222p421 Ns222p1286 Ns222p281 RS223to240.d39 (@Ns222p1289 0 1 43485209165936 2717825572871 17592186044416 151623285 70368744177664 (@Ns222p1290 6787700653167738880 1618313945095 17592186044416 151623285 70368744177664 (@Ns222p1291 25794165 70368744177664 (Ns222p1274 rfl rfl) (Ns222p1274 rfl rfl) rfl) (Ns222p1274 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 4071379 4194304) (BSN.cos_neg_of_bound 4071379 4194304 Bool.false 4737283 8388608 1 2890000 (Ns222p1295 rfl rfl)) rfl rfl) 

noncomputable def Ns222p1297 := @Ns222p1260 1975301397696324397761 Ns222p433 (Ns222p1261 qz61 (@Enclosure.Real.IsNear.of_eq qz726 (@Inv.inv Real Real.instInv (Real.sqrt qz159)) Bool.false 2780415 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz154 (BSN.t_div_two_pi_nonneg qz153 520596 1000 qz156)) Ns222p1265) rfl) (@Ns222p1266 140737488355328 703977364926171 25420708834181120000 (BSN.correction_mk qz155 (BSN.cos_two_pi_p_ne_zero_mk qz153 520596 1000 9 qz156 rfl rfl (@BSN.floor_sqrt_eq_dec qz153 520596 1000 9 qz156 rfl rfl rfl))) (@Ns222p1267 16777216 4737283 8388608 10557769 757596160000 99385293385521 140737488355328 703977364926171 25420708834181120000 (@Ns222p1268 16777216 (Ns222p1282 rfl rfl rfl rfl rfl) rfl) (Ns222p1296 rfl) rfl)) 

noncomputable def Ns222p1298 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz153) (hardyZApproximantRS₀ qz153) Bool.true 1765013028728884286001 1180591620717411303424 317516204979178021677761 Ns222p433 (@Eq.refl Real (hardyZApproximantRS₀ qz153)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz153) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz153) qz153 9) (@HMul.hMul Real Real Real qz4 qz723 (Zeta.RiemannSiegel.correction qz155))) Bool.true 1765013028728884286001 1180591620717411303424 317516204979178021677761 Ns222p433 (BSN.hardyZApproximantRS₀_eq qz153 9 (@BSN.floor_sqrt_eq_dec qz153 520596 1000 9 qz156 rfl rfl rfl)) (@Ns222p1192 1765013028728884286001 1180591620717411303424 317516204979178021677761 Ns222p433 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz153) qz153 9) (@HAdd.hAdd Real Real Real qz358 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz153) qz153 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz153) qz153 9)) Bool.true 116037051 67108864 49651 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz153) qz153 9) (Ns222p1259 (Ns222p1258 rfl) rfl rfl)) (Ns222p1297 rfl) rfl rfl)) 

theorem RS223to240.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz153) Bool.true 1765013028728884286001 1180591620717411303424 317516204979178021677761 Ns222p433 := Ns222p1298 

noncomputable def Ns222p1299 := nat_lit 3408842368892757277298130944 

noncomputable abbrev qz896 := (Enclosure.sfrac Bool.false 522018 1000)

noncomputable abbrev qz729 := qz896

noncomputable abbrev qz510 := qz729

noncomputable abbrev qz166 := qz510

noncomputable abbrev qz897 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 522018 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz730 := qz897

noncomputable abbrev qz511 := qz730

noncomputable abbrev qz167 := qz511

noncomputable abbrev qz898 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 522018 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz731 := qz898

noncomputable abbrev qz512 := qz731

noncomputable abbrev qz168 := qz512

noncomputable abbrev qz732 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz167 qz8))

noncomputable def Ns222p1300 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz166) qz166 9) (@HMul.hMul Real Real Real qz4 qz732 (Zeta.RiemannSiegel.correction qz168)) 15497373 33554432 12447 8388608 33433251992649613525 147573952589676412928 1053477083347675866389 Ns222p874 Ns222p1299 

noncomputable def Ns222p1301 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz166) qz166 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 522018 1000 123 162 134217728 67108864 2251799813685248 Bool.false 119750727348 1814 

noncomputable def Ns222p1302 := Ns222p1301 279097919 47 47453128 8 294906479 47 44739240 8 Bool.false 69557951 81458 Bool.true 11478294 Bool.true 41511317 7074237752028440 1 Bool.false 11464307 Bool.false Bool.false 127849355 Bool.true Bool.false 30994746 

noncomputable def Ns222p1303 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz166) qz166 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 522018 1000 27 78 134217728 67108864 2251799813685248 Bool.false 119750727348 1814 

noncomputable def Ns222p1304 := Ns222p1303 240485871 47 54794152 8 261175631 47 50729528 8 Bool.false 58533860 60722 Bool.true 94850778 Bool.true 143013492 7074237752028440 1 Bool.false 87150602 Bool.false Bool.false 64966400 Bool.true Bool.false 69557951 

noncomputable def Ns222p1305 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz166) qz166 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 522018 1000 107 33 134217728 67108864 2251799813685248 Bool.false 119750727348 1814 

noncomputable def Ns222p1306 := Ns222p1305 186065264 47 67108856 8 216015088 47 60023992 8 Bool.false 41476718 35744 Bool.false 62637953 Bool.false 29615574 7074237752028440 1 Bool.false 60388841 Bool.false Bool.false 29375838 Bool.true Bool.false 58533860 

noncomputable def Ns222p1307 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz166) qz166 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 522018 1000 337 202 134217728 67108864 2251799813685248 Bool.false 119750727348 1814 

noncomputable def Ns222p1308 := Ns222p1307 93032624 47 94906264 8 147453232 47 77490640 16 Bool.false 134217720 1871 Bool.false 136746369 Bool.false 190085830 7074237752028440 1 Bool.false 114286430 Bool.true Bool.false 20660410 Bool.true Bool.false 41476718 

noncomputable def Ns222p1309 := nat_lit 158807919550045566307110522047405599927286262877385237 

noncomputable def Ns222p1310 := nat_lit 177993391960040914479779219996655474182394478592000 

noncomputable def Ns222p1311 := nat_lit 18606712139869329375726167792640000 

noncomputable def Ns222p1312 := nat_lit 58278256897769760337469523800606085120 

noncomputable abbrev qz899 := (@Eq.refl Real (Enclosure.sfrac Bool.false 522018 1000))

noncomputable abbrev qz733 := qz899

noncomputable abbrev qz513 := qz733

noncomputable abbrev qz169 := qz513

noncomputable def Ns222p1313 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz166 522018 1000 1090012169296 16000000 1044036 4000 2000 Ns222p1311 Ns222p1312 qz169 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns222p1314 := nat_lit 29271475731464398781726611423777800178597403973559646883840 

noncomputable abbrev qz514 := (Enclosure.sfrac Bool.false 522018 2000)

noncomputable abbrev qz734 := (Real.log (Enclosure.sfrac Bool.false 1090012169296 16000000))

noncomputable abbrev qz170 := (@HSub.hSub Real Real Real qz347 (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 522018 4000) qz734) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1044036)))))) qz514)

noncomputable abbrev qz515 := (@HSub.hSub Real Real Real qz11 qz170 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 522018 2000) (Real.log Real.pi)))

noncomputable def Ns222p1315 := @Enclosure.Real.IsNear.addLit_ft_p qz515 (Enclosure.sfrac Bool.true Ns222p1311 Ns222p1312) 502271134455161033657 562949953421312000 3998047994583995517 295936000000000000000000 Ns222p1311 Ns222p1312 0 1 Ns222p1314 

noncomputable def Ns222p1316 := nat_lit 16853422626638557952893517824000 

noncomputable abbrev qz516 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 522018 2000) (Real.log Real.pi))

noncomputable def Ns222p1317 := @Enclosure.Real.IsNear.subLit_ff_p qz170 qz516 670472024765446362041 562949953421312000 1656306853488933 289000000000000000000 10025554317849 33554432000 261009 33554432000 Ns222p1316 502271134455161033657 562949953421312000 

noncomputable def Ns222p1318 := nat_lit 1340944049530892724082000 

noncomputable abbrev qz171 := (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 522018 4000) qz734) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1044036))))))

noncomputable def Ns222p1319 := @Enclosure.Real.IsNear.subLit_ff_p qz171 qz514 817407029157989585849 562949953421312000 1656306853488933 289000000000000000000 522018 2000 0 1 Ns222p1318 670472024765446362041 562949953421312000 1656306853488933 289000000000000000000 

noncomputable def Ns222p1320 := nat_lit 1840636995962973028787179693960855552 

noncomputable def Ns222p1321 := nat_lit 26908538532861183118016512 

noncomputable def Ns222p1322 := nat_lit 13720678073558450271406848 

noncomputable def Ns222p1323 := BSN.log_dyadic_bound 41436169296 2138588169296 2 1 Ns222p1322 67108864 23120000 1716956125926773135616 1716956125926773135616 2600858 2180024338592 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 41436169296) (BSN.artanhQ 2138588169296) 0 1 1716956125926773135616 Ns222p1322 1716956125926773135616 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns222p1324 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 522018 4000) qz734 522018 4000 0 1 3132566173195511 281474976710656 781250289 18062500000000000 817627964299587130599 562949953421312000 203913356681601 36125000000000000000 (Enclosure.Real.IsNear.const Bool.false 522018 4000) (BSN.isNear_log_sfrac 1090012169296 16000000 3132566173195511 281474976710656 781250289 18062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1090012169296) qz354)) Bool.false Ns222p1321 Ns222p89 1000000369920000 23120000000000000000000 3132566173195511 281474976710656 781250289 18062500000000000 (BSN.log_rat_reduce_isNear 1090012169296 16000000 16 2180024338592 2097152000000 2600858 67108864 24973259072661432 36028797018963968 23120000 1000000000000000 rfl rfl rfl rfl (Ns222p1323 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns222p1325 := BSN.arctan_dyadic_bound_f 1000 1044036 1 0 8388608 2890000 0 1 1 0 1 1 8034 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1044036) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1044036) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz517 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1044036)))

noncomputable def Ns222p1326 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz517 884279719003555 562949953421312 1 2000000000000000 8034 8388608 1 2890000 7413353185145186680832 883740566390179 562949953421312 200000000289 578000000000000000 qz16 (Ns222p1325 rfl) rfl rfl 

noncomputable def Ns222p1327 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 522018 4000) qz734) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz517)) 817627964299587130599 562949953421312000 203913356681601 36125000000000000000 883740566390179 2251799813685248 200000000289 2312000000000000000 Ns222p1320 817407029157989585849 562949953421312000 1656306853488933 289000000000000000000 (Ns222p1324 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz517) 1 4 0 1 883740566390179 562949953421312 200000000289 578000000000000000 883740566390179 2251799813685248 200000000289 2312000000000000000 qz357 Ns222p1326 rfl) 

noncomputable def Ns222p1328 := @Ns222p1315 Ns222p1309 Ns222p1310 3998047994583995517 295936000000000000000000 (@Ns222p1317 3998047994583995517 295936000000000000000000 (Ns222p1319 (Ns222p1327 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 522018 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz514 (Real.log Real.pi) 522018 2000 0 1 38410761 33554432 1 33554432 10025554317849 33554432000 261009 33554432000 (Enclosure.Real.IsNear.const Bool.false 522018 2000) RS223to240.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns222p1311 Ns222p1312) 

noncomputable def Ns222p1329 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz166) Bool.false Ns222p1309 Ns222p1310 3998047994583995517 295936000000000000000000 7484420459 8388608 57 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz166) (@HAdd.hAdd Real Real Real qz358 qz515 (Enclosure.sfrac Bool.true Ns222p1311 Ns222p1312)) Bool.false Ns222p1309 Ns222p1310 3998047994583995517 295936000000000000000000 Ns222p1313 (Ns222p1328 rfl rfl)) 

noncomputable def Ns222p1330 := nat_lit 1899135811666586651066368 

noncomputable def Ns222p1331 := nat_lit 857426293663047242179427962021664569933952630441529111648398188054200820895707063700589905026097952840339391720560306650887849808756736 

noncomputable def Ns222p1332 := nat_lit 611610060569085214696192766424693558852713256175891739991293317957561364419414402703718810198176953892619201227310295658356801536 

noncomputable def Ns222p1333 := nat_lit 4281802390345350829637207273858617795992210645347506361438341456845364496984006202764663371870432125354562089524363977919506545320656896 

noncomputable def Ns222p1334 := BSN.sin_dyadic_bound_f 53976686208 34359738368 4 3 16777216 5785645 Ns222p1331 Ns222p574 Ns222p1332 Ns222p1333 Ns222p577 Ns222p1332 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53976686208) qz371 0 3 Ns222p1331 Ns222p574 Ns222p1332 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53976686208) qz372 0 3 Ns222p1333 Ns222p577 Ns222p1332 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1335 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz166) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7484420459) qz370) Bool.false 7484420459 8388608 57 4194304 Bool.false 16777215 16777216 1 2890000 (Ns222p1329 rfl) (Enclosure.sfrac_false_div 7484420459 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7484420459) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns222p1330) qz640) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 141 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q3 7484420459 8388608 226375608064910080 72057594037927936 141 Ns222p1330 Ns222p156 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns222p1330 Ns222p156 53976686208 34359738368 5785645 5780000 (Ns222p1334 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p1336 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz166) Bool.false Ns222p1309 Ns222p1310 3998047994583995517 295936000000000000000000 119750727348 134217728 1814 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz166) (@HAdd.hAdd Real Real Real qz358 qz515 (Enclosure.sfrac Bool.true Ns222p1311 Ns222p1312)) Bool.false Ns222p1309 Ns222p1310 3998047994583995517 295936000000000000000000 Ns222p1313 (Ns222p1328 rfl rfl)) 

noncomputable def Ns222p1337 := Ns222p1308 35744 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 337 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 114286430 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 202 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 20660410 134217728) qz169 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz166) qz166 1) Bool.false 16777215 16777216 10557769 757596160000 134217720 134217728 1871 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz166) qz166 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz166)) Bool.false 16777215 16777216 10557769 757596160000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz166) qz166) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz166)) Bool.false 16777215 16777216 168924304 12121538560000 16777215 16777216 10557769 757596160000 (Ns222p1335 rfl rfl) rfl)) rfl) (Ns222p1336 rfl) RS223to240.d7 

noncomputable def Ns222p1338 := nat_lit 343272689811046932863893873151645622831255516382946967865149802916865 

noncomputable def Ns222p1339 := nat_lit 122271834272940720732604329065505021298280367995602344650840714241 

noncomputable def Ns222p1340 := nat_lit 898849557011538158238535927435822956428329136597630131088814789340161 

noncomputable def Ns222p1341 := BSN.sin_dyadic_bound_f 136746369 134217728 3 2 134217728 67108864 Ns222p1338 Ns222p124 Ns222p1339 Ns222p1340 Ns222p127 Ns222p1339 114286430 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 136746369) qz363 0 2 Ns222p1338 Ns222p124 Ns222p1339 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 136746369) qz364 0 2 Ns222p1340 Ns222p127 Ns222p1339 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1342 := nat_lit 2750697739043810091555793467283640914551621232134029309951882380762246616253863645501096806334384704000000 

noncomputable def Ns222p1343 := nat_lit 2225342804443252562948729978614399749060156143691522458495314366690995153780298856144161000000000000 

noncomputable def Ns222p1344 := nat_lit 16660977590006138957185845504166071763987331737922111902111687059687545561508557729960863582838219737600000 

noncomputable def Ns222p1345 := BSN.cos_dyadic_bound_f 190085830 134217728 4 3 134217728 67108864 Ns222p1342 Ns222p227 Ns222p1343 Ns222p1344 Ns222p230 Ns222p1343 20660410 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 190085830) qz361 0 3 Ns222p1342 Ns222p227 Ns222p1343 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 190085830) qz362 0 3 Ns222p1344 Ns222p230 Ns222p1343 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1346 := nat_lit 15393955485542131153860120583681 

noncomputable def Ns222p1347 := BSN.sin_dyadic_bound_f 62637953 134217728 2 1 134217728 67108864 Ns222p1346 Ns222p117 Ns222p1346 Ns222p1346 Ns222p118 Ns222p1346 60388841 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 62637953) qz363 0 1 Ns222p1346 Ns222p117 Ns222p1346 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 62637953) qz364 0 1 Ns222p1346 Ns222p118 Ns222p1346 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1348 := nat_lit 769273226515660103052429474576 

noncomputable def Ns222p1349 := BSN.sin_dyadic_bound_f 29615574 134217728 2 1 134217728 67108864 Ns222p1348 Ns222p117 Ns222p1348 Ns222p1348 Ns222p118 Ns222p1348 29375838 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 29615574) qz363 0 1 Ns222p1348 Ns222p117 Ns222p1348 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 29615574) qz364 0 1 Ns222p1348 Ns222p118 Ns222p1348 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1350 := Ns222p1306 60722 BSN.abs_quadSignPos (BSN.cos_quad_nat3 107 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 60388841 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 33 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 29375838 134217728) qz169 rfl rfl (Ns222p1337 RS223to240.d9 RS223to240.d11 RS223to240.d13 RS223to240.d17 (Ns222p1341 rfl rfl) (Ns222p1345 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns222p1336 rfl) RS223to240.d19 RS223to240.d21 RS223to240.d23 RS223to240.d25 RS223to240.d17 (Ns222p1347 rfl rfl) (Ns222p1349 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns222p1351 := nat_lit 79436614558809913751568187242514325524358984149938150702457133932800 

noncomputable def Ns222p1352 := nat_lit 6551295361884639318115222911097317571606777994884946433866670336 

noncomputable def Ns222p1353 := nat_lit 208037669366297198980925446702824314049633785609274866688399566643456 

noncomputable def Ns222p1354 := BSN.sin_dyadic_bound_f 94850778 134217728 3 2 134217728 67108864 Ns222p1351 Ns222p124 Ns222p1352 Ns222p1353 Ns222p127 Ns222p1352 87150602 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 94850778) qz363 0 2 Ns222p1351 Ns222p124 Ns222p1352 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 94850778) qz364 0 2 Ns222p1353 Ns222p127 Ns222p1352 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1355 := nat_lit 879925630404785697307407612899336273466794702708426006466374179249775288528690547025141226610803255279616 

noncomputable def Ns222p1356 := nat_lit 73202199890033027512198829319361849406587291215268836893335348408418181993601390662166733427572736 

noncomputable def Ns222p1357 := nat_lit 5335486576397375457347480948242250890125251521445876310809446309592996174770123922782199415265778309529600 

noncomputable def Ns222p1358 := BSN.cos_dyadic_bound_f 143013492 134217728 4 3 134217728 67108864 Ns222p1355 Ns222p227 Ns222p1356 Ns222p1357 Ns222p230 Ns222p1356 64966400 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 143013492) qz361 0 3 Ns222p1355 Ns222p227 Ns222p1356 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 143013492) qz362 0 3 Ns222p1357 Ns222p230 Ns222p1356 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1359 := Ns222p1304 81458 BSN.abs_quadSignPos (BSN.cos_quad_nat3 27 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 87150602 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 78 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 64966400 134217728) qz169 rfl rfl (Ns222p1350 rfl rfl) (Ns222p1336 rfl) RS223to240.d27 RS223to240.d29 RS223to240.d31 RS223to240.d33 RS223to240.d17 (Ns222p1354 rfl rfl) (Ns222p1358 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p1360 := nat_lit 17358387436660545997806990096 

noncomputable def Ns222p1361 := BSN.sin_dyadic_bound_f 11478294 134217728 2 1 134217728 67108864 Ns222p1360 Ns222p117 Ns222p1360 Ns222p1360 Ns222p118 Ns222p1360 11464307 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 11478294) qz363 0 1 Ns222p1360 Ns222p117 Ns222p1360 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 11478294) qz364 0 1 Ns222p1360 Ns222p118 Ns222p1360 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1362 := nat_lit 2969381842937852037248890611121 

noncomputable def Ns222p1363 := BSN.cos_dyadic_bound_f 41511317 134217728 2 1 134217728 67108864 Ns222p1362 Ns222p246 Ns222p1362 Ns222p1362 Ns222p247 Ns222p1362 127849355 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 41511317) qz361 0 1 Ns222p1362 Ns222p246 Ns222p1362 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 41511317) qz362 0 1 Ns222p1362 Ns222p247 Ns222p1362 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1364 := Ns222p1302 99576 BSN.abs_quadSignPos qz664 (BSN.sfrac_eq_quadSignPos_mul Bool.false 11464307 134217728) BSN.abs_quadSignNeg qz408 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 127849355 134217728) qz169 rfl rfl (Ns222p1359 rfl) (Ns222p1336 rfl) RS223to240.d35 RS223to240.d37 RS223to240.d46 RS223to240.d48 RS223to240.d17 (Ns222p1361 rfl rfl) (Ns222p1363 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p1365 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz166) qz166 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz166) qz166 9) 30994746 134217728 99576 134217728 30994746 134217728 99576 134217728 8320088776114176 15497373 33554432 12447 8388608 (Ns222p1364 rfl) 

noncomputable def Ns222p1366 := @Enclosure.Real.IsNear.mulLit_tf qz732 (Zeta.RiemannSiegel.correction qz168) 347315 1048576 1 8388608 96262044520535 140737488355328 752042843982043 25420708834181120000 33433251992649613525 147573952589676412928 

noncomputable abbrev qz735 := (@HPow.hPow Real Real Real qz6 qz167 qz8)

noncomputable def Ns222p1367 := @Enclosure.Real.IsNear.mulLit_tf qz48 qz735 1 1 0 1 347315 1048576 1 8388608 347315 1048576 1 8388608 

noncomputable def Ns222p1368 := @Enclosure.Real.IsNear.sqrt_image qz167 696940228593 8388608000 261009 8388608000 76461468 76461498 8388608 (@Enclosure.Real.IsNear.of_eq qz167 (@HMul.hMul Real Real Real qz4 qz166 qz2) Bool.false 696940228593 8388608000 261009 8388608000 (BSN.t_div_two_pi_mk qz166 522018 1000 qz169) (@Enclosure.Real.IsNear.mulLit_ff qz166 qz2 522018 1000 0 1 2670177 16777216 1 16777216 696940228593 8388608000 261009 8388608000 (Enclosure.Real.IsNear.const Bool.false 522018 1000) RS223to240.d40 rfl)) 

noncomputable abbrev qz900 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 522018 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz736 := qz900

noncomputable abbrev qz518 := qz736

noncomputable abbrev qz172 := qz518

noncomputable def Ns222p1369 := @Enclosure.Real.IsNear.sqrt_image qz172 76461483 8388608 15 8388608 25325980 25325986 8388608 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 152922966 16777216 30 16777216 76461483 8388608 15 8388608 (Ns222p1368 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns222p1370 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz172) 25325983 8388608 3 8388608 2778519 2778521 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz172) Bool.false 50651966 16777216 6 16777216 25325983 8388608 3 8388608 (Ns222p1369 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns222p1371 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz172)) Bool.false 5557040 16777216 2 16777216 347315 1048576 1 8388608 (Ns222p1370 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz343 qz341 qz512)

noncomputable abbrev qz737 := (@HMul.hMul Real Real Real qz848 qz898 qz898)

noncomputable abbrev qz519 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz737 qz731) qz639)

noncomputable abbrev qz174 := (Real.cos (@HMul.hMul Real Real Real qz343 qz341 qz519))

noncomputable def Ns222p1372 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz168) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz173)) qz174) Bool.false 96262044520535 

noncomputable def Ns222p1373 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz173)) qz174 22356289 16777216 347 

noncomputable def Ns222p1374 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz173)) Bool.false 22356289 16777216 347 16777216 22356289 16777216 347 

noncomputable def Ns222p1375 := @Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.false 6295208 8388608 562987216 48486154240000 786901 1048576 35186701 3030384640000 

noncomputable def Ns222p1376 := @Enclosure.Real.IsNear.cos_image qz173 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12114119) qz359) Bool.false 12114119 16777216 189 16777216 Bool.false 6295208 8388608 1 

noncomputable def Ns222p1377 := nat_lit 404791131143941473263503017 

noncomputable def Ns222p1378 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz168 884279719003555 140737488355328 1 500000000000000 964011 8388608 15 8388608 852455376196336059105 1180591620717411303424 Ns222p1377 

noncomputable def Ns222p1379 := @Enclosure.Real.IsNear.subLit_ff_p qz172 qz46 76461483 8388608 15 8388608 9 1 0 1 964011 964011 8388608 15 

noncomputable def Ns222p1380 := @Ns222p1379 8388608 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 152922966 16777216 30 16777216 76461483 8388608 15 8388608 (Ns222p1368 rfl rfl rfl rfl rfl rfl) rfl) qz411 

noncomputable def Ns222p1381 := @Enclosure.Real.IsNear.recentre' qz173 Bool.false 852455376196336059105 1180591620717411303424 Ns222p1377 Ns222p263 12114119 16777216 189 16777216 (@Ns222p1378 Ns222p263 RS223to240.d39 (Ns222p1380 rfl rfl) rfl) 

noncomputable def Ns222p1382 := nat_lit 2866991931652432718505703973736745492587467816786074921648321 

noncomputable def Ns222p1383 := nat_lit 463804207639340512109974897378575013793825055962080002241 

noncomputable def Ns222p1384 := nat_lit 8600048186542019474492891971415479327734815800246300604940481 

noncomputable def Ns222p1385 := BSN.cos_dyadic_bound_f 12114119 16777216 3 2 8388608 2890000 Ns222p1382 Ns222p866 Ns222p1383 Ns222p1384 Ns222p869 Ns222p1383 6295208 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 12114119) qz391 0 2 Ns222p1382 Ns222p866 Ns222p1383 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 12114119) (BSN.cosOddQ 16777216) 0 2 Ns222p1384 Ns222p869 Ns222p1383 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1386 := @Enclosure.Real.IsNear.inv_image (Real.cos qz173) 786901 1048576 35186701 3030384640000 11177971 11178318 8388608 (Ns222p1375 (@Ns222p1376 2890000 (Ns222p1381 rfl) (Enclosure.sfrac_false_div 12114119 16777216) (Ns222p1385 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns222p1387 := @Enclosure.Real.IsNear.recentre' qz174 Bool.false 4305815 8388608 

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz343 qz341 qz519)

noncomputable def Ns222p1388 := @Enclosure.Real.IsNear.cos_image qz175 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 17310373)) qz359) Bool.true 17310373 16777216 

noncomputable def Ns222p1389 := nat_lit 10218240961744798670545780405 

noncomputable def Ns222p1390 := nat_lit 4176086399174318565988699381334957 

noncomputable def Ns222p1391 := @Enclosure.Real.IsNear.recentre' qz175 Bool.true Ns222p1389 Ns222p858 Ns222p1390 

noncomputable abbrev qz176 := qz519

noncomputable def Ns222p1392 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz176 884279719003555 140737488355328 1 500000000000000 11555439689671 

noncomputable abbrev qz520 := (@HSub.hSub Real Real Real qz634 qz737 qz731)

noncomputable abbrev qz177 := qz520

noncomputable def Ns222p1393 := @Enclosure.Real.IsNear.subLit_tf qz177 qz25 7157393178567 70368744177664 154749675 70368744177664 1 16 

noncomputable abbrev qz521 := qz737

noncomputable abbrev qz178 := qz521

noncomputable def Ns222p1394 := @Enclosure.Real.IsNear.subLit_ff_n qz178 qz168 929317208121 70368744177664 28920555 70368744177664 964011 8388608 15 8388608 

noncomputable def Ns222p1395 := @Enclosure.Real.IsNear.mulLit_ff qz168 qz168 964011 8388608 15 8388608 964011 8388608 15 8388608 929317208121 70368744177664 

noncomputable def Ns222p1396 := nat_lit 11959346241642990375699444467807115553957645040986710636238561 

noncomputable def Ns222p1397 := nat_lit 8062159918695544700376645960397385375248161991369266566881 

noncomputable def Ns222p1398 := nat_lit 35861914405091580037697580111500551891122438798977393375581921 

noncomputable def Ns222p1399 := BSN.cos_dyadic_bound_f 17310373 16777216 3 2 8388608 2890000 Ns222p1396 Ns222p866 Ns222p1397 Ns222p1398 Ns222p869 Ns222p1397 4305815 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 17310373) qz391 0 2 Ns222p1396 Ns222p866 Ns222p1397 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 17310373) (BSN.cosOddQ 16777216) 0 2 Ns222p1398 Ns222p869 Ns222p1397 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1400 := @Ns222p1387 690147216 48486154240000 4305815 8388608 43134201 3030384640000 (@Ns222p1388 233 16777216 Bool.false 4305815 8388608 1 2890000 (@Ns222p1391 Ns222p281 17310373 16777216 233 16777216 (@Ns222p1392 70368744177664 154749675 70368744177664 Ns222p1389 Ns222p858 Ns222p1390 Ns222p281 RS223to240.d39 (@Ns222p1393 0 1 184887035034736 11555439689671 70368744177664 154749675 70368744177664 (@Ns222p1394 60040565676872564736 7157393178567 70368744177664 154749675 70368744177664 (@Ns222p1395 28920555 70368744177664 (Ns222p1380 rfl rfl) (Ns222p1380 rfl rfl) rfl) (Ns222p1380 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 17310373 16777216) (BSN.cos_neg_of_bound 17310373 16777216 Bool.false 4305815 8388608 1 2890000 (Ns222p1399 rfl rfl)) rfl rfl) 

noncomputable def Ns222p1401 := @Ns222p1366 1053477083347675866389 Ns222p874 (Ns222p1367 qz61 (@Enclosure.Real.IsNear.of_eq qz735 (@Inv.inv Real Real.instInv (Real.sqrt qz172)) Bool.false 347315 1048576 1 8388608 (BSN.rpow_neg_quarter_mk qz167 (BSN.t_div_two_pi_nonneg qz166 522018 1000 qz169)) Ns222p1371) rfl) (@Ns222p1372 140737488355328 752042843982043 25420708834181120000 (BSN.correction_mk qz168 (BSN.cos_two_pi_p_ne_zero_mk qz166 522018 1000 9 qz169 rfl rfl (@BSN.floor_sqrt_eq_dec qz166 522018 1000 9 qz169 rfl rfl rfl))) (@Ns222p1373 16777216 4305815 8388608 43134201 3030384640000 96262044520535 140737488355328 752042843982043 25420708834181120000 (@Ns222p1374 16777216 (Ns222p1386 rfl rfl rfl rfl rfl) rfl) (Ns222p1400 rfl) rfl)) 

noncomputable def Ns222p1402 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz166) (hardyZApproximantRS₀ qz166) Bool.false 101591419246576943317 147573952589676412928 159259258512873876186389 Ns222p874 (@Eq.refl Real (hardyZApproximantRS₀ qz166)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz166) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz166) qz166 9) (@HMul.hMul Real Real Real qz4 qz732 (Zeta.RiemannSiegel.correction qz168))) Bool.false 101591419246576943317 147573952589676412928 159259258512873876186389 Ns222p874 (BSN.hardyZApproximantRS₀_eq qz166 9 (@BSN.floor_sqrt_eq_dec qz166 522018 1000 9 qz169 rfl rfl rfl)) (@Ns222p1300 101591419246576943317 147573952589676412928 159259258512873876186389 Ns222p874 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz166) qz166 9) (@HAdd.hAdd Real Real Real qz358 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz166) qz166 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz166) qz166 9)) Bool.false 15497373 33554432 12447 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz166) qz166 9) (Ns222p1365 (Ns222p1364 rfl) rfl rfl)) (Ns222p1401 rfl) rfl rfl)) 

theorem RS223to240.d58 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz166) Bool.false 101591419246576943317 147573952589676412928 159259258512873876186389 Ns222p874 := Ns222p1402 

noncomputable def Ns222p1403 := nat_lit 61199661753647846198870016 

noncomputable abbrev qz901 := (Enclosure.sfrac Bool.false 523439 1000)

noncomputable abbrev qz738 := qz901

noncomputable abbrev qz522 := qz738

noncomputable abbrev qz179 := qz522

noncomputable abbrev qz902 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 523439 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz739 := qz902

noncomputable abbrev qz523 := qz739

noncomputable abbrev qz180 := qz523

noncomputable abbrev qz903 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 523439 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz740 := qz903

noncomputable abbrev qz524 := qz740

noncomputable abbrev qz181 := qz524

noncomputable abbrev qz741 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz180 qz8))

noncomputable def Ns222p1404 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz179) qz179 9) (@HMul.hMul Real Real Real qz4 qz741 (Zeta.RiemannSiegel.correction qz181)) 30221601 16777216 99843 67108864 505841114488109121 2305843009213693952 28423856240031503 2665554518651030208512 Ns222p1403 

noncomputable def Ns222p1405 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz179) qz179 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 523439 1000 122 162 134217728 67108864 2251799813685248 Bool.false 120172338970 1819 

noncomputable def Ns222p1406 := Ns222p1405 279097919 47 47453128 8 294906479 47 44739240 8 Bool.true 73241685 81675 Bool.true 197293529 Bool.true 38961801 7074237752028440 1 Bool.false 13512255 Bool.true Bool.false 128602255 Bool.true Bool.true 120886404 

noncomputable def Ns222p1407 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz179) qz179 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 523439 1000 27 78 134217728 67108864 2251799813685248 Bool.false 120172338970 1819 

noncomputable def Ns222p1408 := Ns222p1407 240485871 47 54794152 8 261175631 47 50729528 8 Bool.true 40196671 60883 Bool.true 14969578 Bool.true 92532442 7074237752028440 1 Bool.false 14938561 Bool.false Bool.false 103564386 Bool.true Bool.true 73241685 

noncomputable def Ns222p1409 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz179) qz179 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 523439 1000 108 33 134217728 67108864 2251799813685248 Bool.false 120172338970 1819 

noncomputable def Ns222p1410 := Ns222p1409 186065264 47 67108856 8 216015088 47 60023992 8 Bool.true 54360498 35837 Bool.false 9022120 Bool.false 144269755 7074237752028440 1 Bool.false 133914608 Bool.false Bool.false 118049786 Bool.true Bool.true 40196671 

noncomputable def Ns222p1411 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz179) qz179 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 523439 1000 339 203 134217728 67108864 2251799813685248 Bool.false 120172338970 1819 

noncomputable def Ns222p1412 := Ns222p1411 93032624 47 94906264 8 147453232 47 77490640 16 Bool.true 134217720 1871 Bool.false 4501204 Bool.false 191337696 7074237752028440 1 Bool.false 4500360 Bool.false Bool.false 132804976 Bool.false Bool.true 54360498 

noncomputable def Ns222p1413 := nat_lit 186609856209798773143880891750107056316710221608858550837 

noncomputable def Ns222p1414 := nat_lit 208420266572479241964801381851052712157054685413376000 

noncomputable def Ns222p1415 := nat_lit 18861343708222048118744202175520000 

noncomputable def Ns222p1416 := nat_lit 59236602559303503870978994953888079680 

noncomputable abbrev qz525 := (@Eq.refl Real qz738)

noncomputable abbrev qz182 := qz525

noncomputable def Ns222p1417 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz179 523439 1000 1095954546884 16000000 1046878 4000 2000 Ns222p1415 Ns222p1416 qz182 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns222p1418 := nat_lit 59715153987135607406041885360034258021347270914834736267840 

noncomputable abbrev qz526 := (Enclosure.sfrac Bool.false 523439 2000)

noncomputable abbrev qz742 := (Real.log (Enclosure.sfrac Bool.false 1095954546884 16000000))

noncomputable abbrev qz183 := (@HSub.hSub Real Real Real qz347 (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 523439 4000) qz742) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1046878)))))) qz526)

noncomputable abbrev qz527 := (@HSub.hSub Real Real Real qz11 qz183 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 523439 2000) (Real.log Real.pi)))

noncomputable def Ns222p1419 := @Enclosure.Real.IsNear.addLit_ft_p qz527 (Enclosure.sfrac Bool.true Ns222p1415 Ns222p1416) 1008079002561602252413 1125899906842624000 8017723015823207107 591872000000000000000000 Ns222p1415 Ns222p1416 0 1 Ns222p1418 

noncomputable def Ns222p1420 := nat_lit 67651036684162217179277688832000 

noncomputable abbrev qz528 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 523439 2000) (Real.log Real.pi))

noncomputable def Ns222p1421 := @Enclosure.Real.IsNear.subLit_ff_p qz183 qz528 1345396512008117284477 1125899906842624000 1660747480131609 289000000000000000000 20105690327079 67108864000 523439 67108864000 Ns222p1420 1008079002561602252413 1125899906842624000 

noncomputable abbrev qz184 := (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 523439 4000) qz742) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1046878))))))

noncomputable def Ns222p1422 := @Enclosure.Real.IsNear.subLit_ff_p qz184 qz526 328013294535403083289 225179981368524800 1660747480131609 289000000000000000000 523439 2000 0 1 538158604803246913790800 1345396512008117284477 1125899906842624000 1660747480131609 289000000000000000000 

noncomputable def Ns222p1423 := nat_lit 738620275521105038883589516974620672 

noncomputable def Ns222p1424 := nat_lit 26921684035770319330344960 

noncomputable def Ns222p1425 := nat_lit 13797033799555764366328368 

noncomputable def Ns222p1426 := BSN.log_dyadic_bound 47378546884 2144530546884 2 1 Ns222p1425 67108864 23120000 2244726704839386109456 2244726704839386109456 2965719 2191909093768 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 47378546884) (BSN.artanhQ 2144530546884) 0 1 2244726704839386109456 Ns222p1425 2244726704839386109456 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns222p1427 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 523439 4000) qz742 523439 4000 0 1 3134096511147255 281474976710656 781250289 18062500000000000 328101668739681601989 225179981368524800 408936870023871 72250000000000000000 (Enclosure.Real.IsNear.const Bool.false 523439 4000) (BSN.isNear_log_sfrac 1095954546884 16000000 3134096511147255 281474976710656 781250289 18062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1095954546884) qz354)) Bool.false Ns222p1424 Ns222p89 1000000369920000 23120000000000000000000 3134096511147255 281474976710656 781250289 18062500000000000 (BSN.log_rat_reduce_isNear 1095954546884 16000000 16 2191909093768 2097152000000 2965719 67108864 24973259072661432 36028797018963968 23120000 1000000000000000 rfl rfl rfl rfl (Ns222p1426 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns222p1428 := BSN.arctan_dyadic_bound_f 1000 1046878 1 0 8388608 2890000 0 1 1 0 1 1 8012 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1046878) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1046878) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz529 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1046878)))

noncomputable def Ns222p1429 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz529 884279719003555 562949953421312 1 2000000000000000 8012 8388608 1 2890000 7413365570044161949696 883742042785187 562949953421312 200000000289 578000000000000000 qz16 (Ns222p1428 rfl) rfl rfl 

noncomputable def Ns222p1430 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 523439 4000) qz742) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz529)) 328101668739681601989 225179981368524800 408936870023871 72250000000000000000 883742042785187 2251799813685248 200000000289 2312000000000000000 Ns222p1423 328013294535403083289 225179981368524800 1660747480131609 289000000000000000000 (Ns222p1427 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz529) 1 4 0 1 883742042785187 562949953421312 200000000289 578000000000000000 883742042785187 2251799813685248 200000000289 2312000000000000000 qz357 Ns222p1429 rfl) 

noncomputable def Ns222p1431 := @Ns222p1419 Ns222p1413 Ns222p1414 8017723015823207107 591872000000000000000000 (@Ns222p1421 8017723015823207107 591872000000000000000000 (Ns222p1422 (Ns222p1430 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 523439 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz526 (Real.log Real.pi) 523439 2000 0 1 38410761 33554432 1 33554432 20105690327079 67108864000 523439 67108864000 (Enclosure.Real.IsNear.const Bool.false 523439 2000) RS223to240.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns222p1415 Ns222p1416) 

noncomputable def Ns222p1432 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz179) Bool.false Ns222p1413 Ns222p1414 8017723015823207107 591872000000000000000000 15021542371 16777216 57 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz179) (@HAdd.hAdd Real Real Real qz358 qz527 (Enclosure.sfrac Bool.true Ns222p1415 Ns222p1416)) Bool.false Ns222p1413 Ns222p1414 8017723015823207107 591872000000000000000000 Ns222p1417 (Ns222p1431 rfl rfl)) 

noncomputable def Ns222p1433 := nat_lit 3797446487026375109640192 

noncomputable def Ns222p1434 := nat_lit 856679970640340925320101530488280868213926755365708394762870265886673454448824228860429114522907397965818130712843150974705127550540625 

noncomputable def Ns222p1435 := nat_lit 610017570483052764971274201384568189449579305132465500592841046477635724729040949487875804876859760064367676412168244062744140625 

noncomputable def Ns222p1436 := nat_lit 4278080031823817904718217883040087605468181802172682240699461300339453588430099584018142174397619950759327948762635037697779722776140625 

noncomputable def Ns222p1437 := BSN.sin_dyadic_bound_f 53964960315 34359738368 4 3 16777216 5785645 Ns222p1434 Ns222p574 Ns222p1435 Ns222p1436 Ns222p577 Ns222p1435 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53964960315) qz371 0 3 Ns222p1434 Ns222p574 Ns222p1435 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53964960315) qz372 0 3 Ns222p1436 Ns222p577 Ns222p1435 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1438 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz179) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15021542371) qz359) Bool.false 15021542371 16777216 57 4194304 Bool.true 16777215 16777216 1 2890000 (Ns222p1432 rfl) (Enclosure.sfrac_false_div 15021542371 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15021542371) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns222p1433) qz360) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 142 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q1 15021542371 16777216 226375608064910080 72057594037927936 142 Ns222p1433 Ns222p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns222p1433 Ns222p89 53964960315 34359738368 5785645 5780000 (Ns222p1437 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p1439 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz179) Bool.false Ns222p1413 Ns222p1414 8017723015823207107 591872000000000000000000 120172338970 134217728 1819 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz179) (@HAdd.hAdd Real Real Real qz358 qz527 (Enclosure.sfrac Bool.true Ns222p1415 Ns222p1416)) Bool.false Ns222p1413 Ns222p1414 8017723015823207107 591872000000000000000000 Ns222p1417 (Ns222p1431 rfl rfl)) 

noncomputable def Ns222p1440 := Ns222p1412 35837 BSN.abs_quadSignPos (BSN.cos_quad_nat3 339 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 4500360 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 203 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 132804976 134217728) qz182 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz179) qz179 1) Bool.true 16777215 16777216 10557769 757596160000 134217720 134217728 1871 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz179) qz179 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz179)) Bool.true 16777215 16777216 10557769 757596160000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz179) qz179) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz179)) Bool.true 16777215 16777216 168924304 12121538560000 16777215 16777216 10557769 757596160000 (Ns222p1438 rfl rfl) rfl)) rfl) (Ns222p1439 rfl) RS223to240.d7 

noncomputable def Ns222p1441 := BSN.sin_dyadic_bound_f 4501204 134217728 1 0 134217728 67108864 0 1 1 0 1 1 4500360 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 4501204) qz363 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 4501204) qz364 0 0 rfl) rfl rfl 

noncomputable def Ns222p1442 := nat_lit 7334545090457279826764039013986947512281368141733558643611516343250360636917968592872689433199040178159616 

noncomputable def Ns222p1443 := nat_lit 2407722776025087266074360482615161340618177902305631707893058441661290655058600844820906959611887616 

noncomputable def Ns222p1444 := nat_lit 36641795260185460014515869805458101985137142369031378128086749005409189145755193452406000059803403840126976 

noncomputable def Ns222p1445 := BSN.sin_dyadic_bound_f 191337696 134217728 4 3 134217728 67108864 Ns222p1442 Ns222p111 Ns222p1443 Ns222p1444 Ns222p114 Ns222p1443 132804976 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 191337696) qz363 0 3 Ns222p1442 Ns222p111 Ns222p1443 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 191337696) qz364 0 3 Ns222p1444 Ns222p114 Ns222p1443 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1446 := nat_lit 6625740106952725617871360000 

noncomputable def Ns222p1447 := BSN.cos_dyadic_bound_f 9022120 134217728 2 1 134217728 67108864 Ns222p1446 Ns222p246 Ns222p1446 Ns222p1446 Ns222p247 Ns222p1446 133914608 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 9022120) qz361 0 1 Ns222p1446 Ns222p246 Ns222p1446 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 9022120) qz362 0 1 Ns222p1446 Ns222p247 Ns222p1446 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1448 := nat_lit 425318400437015556831135227181068382861348876751983955200928396230625 

noncomputable def Ns222p1449 := nat_lit 187673241050977826457624030174684918304088651705743553985000390625 

noncomputable def Ns222p1450 := nat_lit 1113625292087624875219660870377753417626278533676243916915027227590625 

noncomputable def Ns222p1451 := BSN.sin_dyadic_bound_f 144269755 134217728 3 2 134217728 67108864 Ns222p1448 Ns222p124 Ns222p1449 Ns222p1450 Ns222p127 Ns222p1449 118049786 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 144269755) qz363 0 2 Ns222p1448 Ns222p124 Ns222p1449 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 144269755) qz364 0 2 Ns222p1450 Ns222p127 Ns222p1449 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1452 := Ns222p1410 60883 BSN.abs_quadSignPos (BSN.cos_quad_nat0 108 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133914608 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 33 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 118049786 134217728) qz182 rfl rfl (Ns222p1440 RS223to240.d9 RS223to240.d11 RS223to240.d13 RS223to240.d17 (Ns222p1441 rfl rfl) (Ns222p1445 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns222p1439 rfl) RS223to240.d19 RS223to240.d21 RS223to240.d23 RS223to240.d25 RS223to240.d17 (Ns222p1447 rfl rfl) (Ns222p1451 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns222p1453 := nat_lit 50215550733939784016607671056 

noncomputable def Ns222p1454 := BSN.sin_dyadic_bound_f 14969578 134217728 2 1 134217728 67108864 Ns222p1453 Ns222p117 Ns222p1453 Ns222p1453 Ns222p118 Ns222p1453 14938561 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 14969578) qz363 0 1 Ns222p1453 Ns222p117 Ns222p1453 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 14969578) qz364 0 1 Ns222p1453 Ns222p118 Ns222p1453 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1455 := nat_lit 39974524274559042168607564840115596278005991099739120302261321277696 

noncomputable def Ns222p1456 := nat_lit 5374674768063400451499165556705598996370784580921798579838198016 

noncomputable def Ns222p1457 := nat_lit 119912823474140999704919696189233377636025231730055517309624287437056 

noncomputable def Ns222p1458 := BSN.cos_dyadic_bound_f 92532442 134217728 3 2 134217728 67108864 Ns222p1455 Ns222p105 Ns222p1456 Ns222p1457 Ns222p108 Ns222p1456 103564386 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 92532442) qz361 0 2 Ns222p1455 Ns222p105 Ns222p1456 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 92532442) qz362 0 2 Ns222p1457 Ns222p108 Ns222p1456 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1459 := Ns222p1408 81675 BSN.abs_quadSignPos (BSN.cos_quad_nat3 27 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 14938561 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 78 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 103564386 134217728) qz182 rfl rfl (Ns222p1452 rfl rfl) (Ns222p1439 rfl) RS223to240.d27 RS223to240.d29 RS223to240.d31 RS223to240.d33 RS223to240.d17 (Ns222p1454 rfl rfl) (Ns222p1458 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p1460 := nat_lit 3193463028597018049878283401192454593665799423667112690710715692747126352463065822114745216434840236751521 

noncomputable def Ns222p1461 := nat_lit 3478196338218953153774547087499273399044490910767342680629660425889919651752667232193094095979707041 

noncomputable def Ns222p1462 := nat_lit 19337863478850974742673749046671149164541328904257465951530887947582663972806145799439238632959282962266785 

noncomputable def Ns222p1463 := BSN.cos_dyadic_bound_f 197293529 134217728 4 3 134217728 67108864 Ns222p1460 Ns222p227 Ns222p1461 Ns222p1462 Ns222p230 Ns222p1461 13512255 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 197293529) qz361 0 3 Ns222p1460 Ns222p227 Ns222p1461 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 197293529) qz362 0 3 Ns222p1462 Ns222p230 Ns222p1461 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1464 := nat_lit 2304390601709931782857039287201 

noncomputable def Ns222p1465 := BSN.cos_dyadic_bound_f 38961801 134217728 2 1 134217728 67108864 Ns222p1464 Ns222p246 Ns222p1464 Ns222p1464 Ns222p247 Ns222p1464 128602255 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 38961801) qz361 0 1 Ns222p1464 Ns222p246 Ns222p1464 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 38961801) qz362 0 1 Ns222p1464 Ns222p247 Ns222p1464 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz743 := (BSN.cos_quad_nat2 122 rfl)

noncomputable def Ns222p1466 := Ns222p1406 99843 BSN.abs_quadSignNeg qz743 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 13512255 134217728) BSN.abs_quadSignNeg qz408 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 128602255 134217728) qz182 rfl rfl (Ns222p1459 rfl) (Ns222p1439 rfl) RS223to240.d35 RS223to240.d37 RS223to240.d46 RS223to240.d48 RS223to240.d17 (Ns222p1463 rfl rfl) (Ns222p1465 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p1467 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz179) qz179 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz179) qz179 9) 120886404 134217728 99843 134217728 120886404 134217728 99843 134217728 32450196981940224 30221601 16777216 99843 67108864 (Ns222p1466 rfl) 

noncomputable def Ns222p1468 := @Enclosure.Real.IsNear.mulLit_tf qz741 (Zeta.RiemannSiegel.correction qz181) 347079 1048576 1 8388608 1457423567799 2199023255552 20321921215 635517720854528 505841114488109121 2305843009213693952 

noncomputable abbrev qz744 := (@HPow.hPow Real Real Real qz6 qz180 qz8)

noncomputable def Ns222p1469 := @Enclosure.Real.IsNear.mulLit_tf qz48 qz744 1 1 0 1 347079 1048576 1 8388608 347079 1048576 1 8388608 

noncomputable def Ns222p1470 := @Enclosure.Real.IsNear.sqrt_image qz180 1397674778703 16777216000 523439 16777216000 76565466 76565496 8388608 (@Enclosure.Real.IsNear.of_eq qz180 (@HMul.hMul Real Real Real qz4 qz179 qz2) Bool.false 1397674778703 16777216000 523439 16777216000 (BSN.t_div_two_pi_mk qz179 523439 1000 qz182) (@Enclosure.Real.IsNear.mulLit_ff qz179 qz2 523439 1000 0 1 2670177 16777216 1 16777216 1397674778703 16777216000 523439 16777216000 (Enclosure.Real.IsNear.const Bool.false 523439 1000) RS223to240.d40 rfl)) 

noncomputable abbrev qz904 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 523439 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz745 := qz904

noncomputable abbrev qz530 := qz745

noncomputable abbrev qz185 := qz530

noncomputable def Ns222p1471 := @Enclosure.Real.IsNear.sqrt_image qz185 76565481 8388608 15 8388608 25343197 25343203 8388608 (@Enclosure.Real.IsNear.recentre' qz185 Bool.false 153130962 16777216 30 16777216 76565481 8388608 15 8388608 (Ns222p1470 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns222p1472 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz185) 791975 262144 3 8388608 2776631 2776633 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz185) Bool.false 50686400 16777216 6 16777216 791975 262144 3 8388608 (Ns222p1471 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns222p1473 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz185)) Bool.false 5553264 16777216 2 16777216 347079 1048576 1 8388608 (Ns222p1472 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz186 := (@HMul.hMul Real Real Real qz343 qz341 qz524)

noncomputable abbrev qz746 := (@HMul.hMul Real Real Real qz848 qz903 qz903)

noncomputable abbrev qz531 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz746 qz740) qz639)

noncomputable abbrev qz187 := (Real.cos (@HMul.hMul Real Real Real qz343 qz341 qz531))

noncomputable def Ns222p1474 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz181) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz186)) qz187) Bool.false 1457423567799 

noncomputable def Ns222p1475 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz186)) qz187 6019899 4194304 101 

noncomputable def Ns222p1476 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz186)) Bool.false 24079596 16777216 404 16777216 6019899 4194304 101 

noncomputable def Ns222p1477 := @Enclosure.Real.IsNear.recentre' (Real.cos qz186) Bool.false 5844678 8388608 282938608 24243077120000 2922339 4194304 17683663 1515192320000 

noncomputable def Ns222p1478 := @Enclosure.Real.IsNear.cos_image qz186 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3355249) qz676) Bool.false 3355249 4194304 95 8388608 Bool.false 5844678 8388608 1 

noncomputable def Ns222p1479 := nat_lit 404791131144834809281201833 

noncomputable def Ns222p1480 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz181 884279719003555 140737488355328 1 500000000000000 1068009 8388608 15 8388608 944418698413267771995 1180591620717411303424 Ns222p1479 

noncomputable def Ns222p1481 := @Enclosure.Real.IsNear.subLit_ff_p qz185 qz46 76565481 8388608 15 8388608 9 1 0 1 1068009 1068009 8388608 15 

noncomputable def Ns222p1482 := @Ns222p1481 8388608 (@Enclosure.Real.IsNear.recentre' qz185 Bool.false 153130962 16777216 30 16777216 76565481 8388608 15 8388608 (Ns222p1470 rfl rfl rfl rfl rfl rfl) rfl) qz411 

noncomputable def Ns222p1483 := @Enclosure.Real.IsNear.recentre' qz186 Bool.false 944418698413267771995 1180591620717411303424 Ns222p1479 Ns222p263 3355249 4194304 95 8388608 (@Ns222p1480 Ns222p263 RS223to240.d39 (Ns222p1482 rfl rfl) rfl) 

noncomputable def Ns222p1484 := nat_lit 65910373130132286947165521544585182923722205439991902081 

noncomputable def Ns222p1485 := nat_lit 16061941683712314645471225919179374283329898207408001 

noncomputable def Ns222p1486 := nat_lit 197698995507029436212205622181917190022599956523560890241 

noncomputable def Ns222p1487 := BSN.cos_dyadic_bound_f 3355249 4194304 3 2 8388608 2890000 Ns222p1484 Ns222p1277 Ns222p1485 Ns222p1486 Ns222p1280 Ns222p1485 5844678 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3355249) (BSN.cosEvenQ 4194304) 0 2 Ns222p1484 Ns222p1277 Ns222p1485 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3355249) (BSN.cosOddQ 4194304) 0 2 Ns222p1486 Ns222p1280 Ns222p1485 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1488 := @Enclosure.Real.IsNear.inv_image (Real.cos qz186) 2922339 4194304 17683663 1515192320000 12039596 12040000 8388608 (Ns222p1477 (@Ns222p1478 2890000 (Ns222p1483 rfl) (Enclosure.sfrac_false_div 3355249 4194304) (Ns222p1487 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns222p1489 := @Enclosure.Real.IsNear.recentre' qz187 Bool.false 3873616 8388608 

noncomputable abbrev qz188 := (@HMul.hMul Real Real Real qz343 qz341 qz531)

noncomputable def Ns222p1490 := @Enclosure.Real.IsNear.cos_image qz188 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 9150339)) qz370) Bool.true 9150339 8388608 

noncomputable def Ns222p1491 := nat_lit 10802813912189080193521799725 

noncomputable def Ns222p1492 := nat_lit 852056267058338002835234265927349 

noncomputable def Ns222p1493 := @Enclosure.Real.IsNear.recentre' qz188 Bool.true Ns222p1491 Ns222p858 Ns222p1492 

noncomputable def Ns222p1494 := nat_lit 60446290980731458735308800000000000000 

noncomputable abbrev qz189 := qz531

noncomputable def Ns222p1495 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz189 884279719003555 140737488355328 1 500000000000000 12216512128495 

noncomputable abbrev qz532 := (@HSub.hSub Real Real Real qz634 qz746 qz740)

noncomputable abbrev qz190 := qz532

noncomputable def Ns222p1496 := @Enclosure.Real.IsNear.subLit_tf qz190 qz25 7818465617391 70368744177664 157869615 70368744177664 1 16 

noncomputable abbrev qz533 := qz746

noncomputable abbrev qz191 := qz533

noncomputable def Ns222p1497 := @Enclosure.Real.IsNear.subLit_ff_n qz191 qz181 1140643224081 70368744177664 32040495 70368744177664 1068009 8388608 15 8388608 

noncomputable def Ns222p1498 := @Enclosure.Real.IsNear.mulLit_ff qz181 qz181 1068009 8388608 15 8388608 1068009 8388608 15 8388608 1140643224081 70368744177664 

noncomputable def Ns222p1499 := nat_lit 58369160963273024759931168248625836794309704537723563142561 

noncomputable def Ns222p1500 := nat_lit 49147051958085076544798716606353930015087676408413810081 

noncomputable def Ns222p1501 := nat_lit 175009188785902904126703907312664802522898938260353861807521 

noncomputable def Ns222p1502 := BSN.cos_dyadic_bound_f 9150339 8388608 3 2 8388608 2890000 Ns222p1499 Ns222p642 Ns222p1500 Ns222p1501 Ns222p645 Ns222p1500 3873616 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 9150339) (BSN.cosEvenQ 8388608) 0 2 Ns222p1499 Ns222p642 Ns222p1500 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 9150339) (BSN.cosOddQ 8388608) 0 2 Ns222p1501 Ns222p645 Ns222p1500 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1503 := @Ns222p1489 352298608 24243077120000 242101 524288 22018663 1515192320000 (@Ns222p1490 119 8388608 Bool.false 3873616 8388608 1 2890000 (@Ns222p1493 Ns222p1494 9150339 8388608 119 8388608 (@Ns222p1495 70368744177664 157869615 70368744177664 Ns222p1491 Ns222p858 Ns222p1492 Ns222p1494 RS223to240.d39 (@Ns222p1496 0 1 195464194055920 12216512128495 70368744177664 157869615 70368744177664 (@Ns222p1497 65586043225771081728 7818465617391 70368744177664 157869615 70368744177664 (@Ns222p1498 32040495 70368744177664 (Ns222p1482 rfl rfl) (Ns222p1482 rfl rfl) rfl) (Ns222p1482 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 9150339 8388608) (BSN.cos_neg_of_bound 9150339 8388608 Bool.false 3873616 8388608 1 2890000 (Ns222p1502 rfl rfl)) rfl rfl) 

noncomputable def Ns222p1504 := @Ns222p1468 28423856240031503 2665554518651030208512 (Ns222p1469 qz61 (@Enclosure.Real.IsNear.of_eq qz744 (@Inv.inv Real Real.instInv (Real.sqrt qz185)) Bool.false 347079 1048576 1 8388608 (BSN.rpow_neg_quarter_mk qz180 (BSN.t_div_two_pi_nonneg qz179 523439 1000 qz182)) Ns222p1473) rfl) (@Ns222p1474 2199023255552 20321921215 635517720854528 (BSN.correction_mk qz181 (BSN.cos_two_pi_p_ne_zero_mk qz179 523439 1000 9 qz182 rfl rfl (@BSN.floor_sqrt_eq_dec qz179 523439 1000 9 qz182 rfl rfl rfl))) (@Ns222p1475 4194304 242101 524288 22018663 1515192320000 1457423567799 2199023255552 20321921215 635517720854528 (@Ns222p1476 4194304 (Ns222p1488 rfl rfl rfl rfl rfl) rfl) (Ns222p1503 rfl) rfl)) 

noncomputable def Ns222p1505 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz179) (hardyZApproximantRS₀ qz179) Bool.true 3647784099200239551 2305843009213693952 3994173593944946447 2665554518651030208512 (@Eq.refl Real (hardyZApproximantRS₀ qz179)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz179) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz179) qz179 9) (@HMul.hMul Real Real Real qz4 qz741 (Zeta.RiemannSiegel.correction qz181))) Bool.true 3647784099200239551 2305843009213693952 3994173593944946447 2665554518651030208512 (BSN.hardyZApproximantRS₀_eq qz179 9 (@BSN.floor_sqrt_eq_dec qz179 523439 1000 9 qz182 rfl rfl rfl)) (@Ns222p1404 3647784099200239551 2305843009213693952 3994173593944946447 2665554518651030208512 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz179) qz179 9) (@HAdd.hAdd Real Real Real qz358 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz179) qz179 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz179) qz179 9)) Bool.true 30221601 16777216 99843 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz179) qz179 9) (Ns222p1467 (Ns222p1466 rfl) rfl rfl)) (Ns222p1504 rfl) rfl rfl)) 

theorem RS223to240.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz179) Bool.true 3647784099200239551 2305843009213693952 3994173593944946447 2665554518651030208512 := Ns222p1505 

noncomputable def Ns222p1506 := nat_lit 82244741214048844047712256 

noncomputable abbrev qz905 := (Enclosure.sfrac Bool.false 524859 1000)

noncomputable abbrev qz747 := qz905

noncomputable abbrev qz534 := qz747

noncomputable abbrev qz192 := qz534

noncomputable abbrev qz906 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 524859 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz748 := qz906

noncomputable abbrev qz535 := qz748

noncomputable abbrev qz193 := qz535

noncomputable abbrev qz907 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 524859 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz749 := qz907

noncomputable abbrev qz536 := qz749

noncomputable abbrev qz194 := qz536

noncomputable abbrev qz750 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz193 qz8))

noncomputable def Ns222p1507 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz192) qz192 9) (@HMul.hMul Real Real Real qz4 qz750 (Zeta.RiemannSiegel.correction qz194)) 14268471 16777216 25029 16777216 980081140936147817 4611686018427387904 1197569799643773756287 Ns222p874 Ns222p1506 

noncomputable def Ns222p1508 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz192) qz192 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 524859 1000 122 162 134217728 67108864 2251799813685248 Bool.false 120593912473 1824 

noncomputable def Ns222p1509 := Ns222p1508 279097919 47 47453128 8 294906479 47 44739240 8 Bool.false 113723751 81899 Bool.true 172039071 Bool.true 36155498 7074237752028440 1 Bool.false 38251915 Bool.true Bool.false 129377330 Bool.true Bool.false 57073884 

noncomputable def Ns222p1510 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz192) qz192 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 524859 1000 26 78 134217728 67108864 2251799813685248 Bool.false 120593912473 1824 

noncomputable def Ns222p1511 := Ns222p1510 240485871 47 54794152 8 261175631 47 50729528 8 Bool.false 187561788 61051 Bool.true 145714726 Bool.true 41828335 7074237752028440 1 Bool.false 62589695 Bool.true Bool.false 127752505 Bool.true Bool.false 113723751 

noncomputable def Ns222p1512 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz192) qz192 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 524859 1000 108 34 134217728 67108864 2251799813685248 Bool.false 120593912473 1824 

noncomputable def Ns222p1513 := Ns222p1512 186065264 47 67108856 8 216015088 47 60023992 8 Bool.false 221926232 35937 Bool.false 166382948 Bool.false 48273119 7074237752028440 1 Bool.false 43637901 Bool.false Bool.false 125629883 Bool.true Bool.false 187561788 

noncomputable def Ns222p1514 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz192) qz192 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 524859 1000 340 204 134217728 67108864 2251799813685248 Bool.false 120593912473 1824 

noncomputable def Ns222p1515 := Ns222p1514 93032624 47 94906264 8 147453232 47 77490640 16 Bool.false 134217680 1879 Bool.false 83139667 Bool.false 192698895 7074237752028440 1 Bool.false 109280666 Bool.false Bool.false 18074736 Bool.false Bool.false 221926232 

noncomputable def Ns222p1516 := nat_lit 21148148919690790190540226727115829801306083192167887689 

noncomputable def Ns222p1517 := nat_lit 23537311636961229964869207837061784287418760822784000 

noncomputable def Ns222p1518 := nat_lit 19118573239756812319112874383520000 

noncomputable def Ns222p1519 := nat_lit 60207356890672107762106540614455542080 

noncomputable abbrev qz537 := (@Eq.refl Real qz747)

noncomputable abbrev qz195 := qz537

noncomputable def Ns222p1520 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz192 524859 1000 1101908879524 16000000 1049718 4000 2000 Ns222p1518 Ns222p1519 qz195 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns222p1521 := nat_lit 60906668888709475748755852974093589827761519593443516544320 

noncomputable abbrev qz538 := (Enclosure.sfrac Bool.false 524859 2000)

noncomputable abbrev qz751 := (Real.log (Enclosure.sfrac Bool.false 1101908879524 16000000))

noncomputable abbrev qz196 := (@HSub.hSub Real Real Real qz347 (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 524859 4000) qz751) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1049718)))))) qz538)

noncomputable abbrev qz539 := (@HSub.hSub Real Real Real qz11 qz196 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 524859 2000) (Real.log Real.pi)))

noncomputable def Ns222p1522 := @Enclosure.Real.IsNear.addLit_ft_p qz539 (Enclosure.sfrac Bool.true Ns222p1518 Ns222p1519) 1011615416449971165329 1125899906842624000 8039334822895977567 591872000000000000000000 Ns222p1518 Ns222p1519 0 1 Ns222p1521 

noncomputable def Ns222p1523 := nat_lit 67888361402844477737985376256000 

noncomputable abbrev qz540 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 524859 2000) (Real.log Real.pi))

noncomputable def Ns222p1524 := @Enclosure.Real.IsNear.subLit_ff_p qz196 qz540 1349848010296796551313 1125899906842624000 1665184981773129 289000000000000000000 20160233607699 67108864000 524859 67108864000 Ns222p1523 1011615416449971165329 1125899906842624000 

noncomputable def Ns222p1525 := nat_lit 2699696020593593102626000 

noncomputable abbrev qz197 := (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 524859 4000) qz751) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1049718))))))

noncomputable def Ns222p1526 := @Enclosure.Real.IsNear.subLit_ff_p qz197 qz538 1645317359899552946321 1125899906842624000 1665184981773129 289000000000000000000 524859 2000 0 1 Ns222p1525 1349848010296796551313 1125899906842624000 1665184981773129 289000000000000000000 

noncomputable def Ns222p1527 := nat_lit 3704925324474917453545675695333572608 

noncomputable def Ns222p1528 := nat_lit 26934784682827166932533248 

noncomputable def Ns222p1529 := nat_lit 320801826447935993124409465587042628779665717456640 

noncomputable def Ns222p1530 := nat_lit 65795031117915851842800721853542583567593310208 

noncomputable def Ns222p1531 := nat_lit 24271766468457106119621182747360158167491328 

noncomputable def Ns222p1532 := BSN.log_dyadic_bound 53332879524 2150484879524 3 2 Ns222p1529 67108864 23120000 Ns222p1530 Ns222p1531 3329335 2203817759048 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 53332879524) (BSN.artanhQ 2150484879524) 0 2 Ns222p1530 Ns222p1529 Ns222p1531 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns222p1533 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 524859 4000) qz751 524859 4000 0 1 3135621627190519 281474976710656 781250289 18062500000000000 1645759231625588611821 1125899906842624000 410046245434251 72250000000000000000 (Enclosure.Real.IsNear.const Bool.false 524859 4000) (BSN.isNear_log_sfrac 1101908879524 16000000 3135621627190519 281474976710656 781250289 18062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1101908879524) qz354)) Bool.false Ns222p1528 Ns222p89 1000000369920000 23120000000000000000000 3135621627190519 281474976710656 781250289 18062500000000000 (BSN.log_rat_reduce_isNear 1101908879524 16000000 16 2203817759048 2097152000000 3329335 67108864 24973259072661432 36028797018963968 23120000 1000000000000000 rfl rfl rfl rfl (Ns222p1532 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns222p1534 := BSN.arctan_dyadic_bound_f 1000 1049718 1 0 8388608 2890000 0 1 1 0 1 1 7991 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1049718) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1049718) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz541 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1049718)))

noncomputable def Ns222p1535 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz541 884279719003555 562949953421312 1 2000000000000000 7991 8388608 1 2890000 7413377391993183797248 883743452071331 562949953421312 200000000289 578000000000000000 qz16 (Ns222p1534 rfl) rfl rfl 

noncomputable def Ns222p1536 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 524859 4000) qz751) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz541)) 1645759231625588611821 1125899906842624000 410046245434251 72250000000000000000 883743452071331 2251799813685248 200000000289 2312000000000000000 Ns222p1527 1645317359899552946321 1125899906842624000 1665184981773129 289000000000000000000 (Ns222p1533 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz541) 1 4 0 1 883743452071331 562949953421312 200000000289 578000000000000000 883743452071331 2251799813685248 200000000289 2312000000000000000 qz357 Ns222p1535 rfl) 

noncomputable def Ns222p1537 := @Ns222p1522 Ns222p1516 Ns222p1517 8039334822895977567 591872000000000000000000 (@Ns222p1524 8039334822895977567 591872000000000000000000 (Ns222p1526 (Ns222p1536 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 524859 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz538 (Real.log Real.pi) 524859 2000 0 1 38410761 33554432 1 33554432 20160233607699 67108864000 524859 67108864000 (Enclosure.Real.IsNear.const Bool.false 524859 2000) RS223to240.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns222p1518 Ns222p1519) 

noncomputable def Ns222p1538 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz192) Bool.false Ns222p1516 Ns222p1517 8039334822895977567 591872000000000000000000 15074239059 16777216 229 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz192) (@HAdd.hAdd Real Real Real qz358 qz539 (Enclosure.sfrac Bool.true Ns222p1518 Ns222p1519)) Bool.false Ns222p1516 Ns222p1517 8039334822895977567 591872000000000000000000 Ns222p1520 (Ns222p1537 rfl rfl)) 

noncomputable def Ns222p1539 := nat_lit 3795934641848395463917568 

noncomputable def Ns222p1540 := nat_lit 855313798659785966901724819215864799573871837763695065925921090046719050344622778142212204441124712494607176901078744324152232998179041 

noncomputable def Ns222p1541 := nat_lit 607109609980857914156991102455818506450232815236693703379265845378130538488007056716467291557571144547572298986103505640663126241 

noncomputable def Ns222p1542 := nat_lit 4271266095684424244761821602140583812174876642383558959905508781635140449679870913693599582236587968796852522234891290910321176976920801 

noncomputable def Ns222p1543 := BSN.sin_dyadic_bound_f 53943475703 34359738368 4 3 16777216 5785645 Ns222p1540 Ns222p574 Ns222p1541 Ns222p1542 Ns222p577 Ns222p1541 16777210 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53943475703) qz371 0 3 Ns222p1540 Ns222p574 Ns222p1541 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53943475703) qz372 0 3 Ns222p1542 Ns222p577 Ns222p1541 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1544 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz192) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15074239059) qz359) Bool.false 15074239059 16777216 229 16777216 Bool.false 16777210 16777216 1 2890000 (Ns222p1538 rfl) (Enclosure.sfrac_false_div 15074239059 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15074239059) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns222p1539) qz360) 226375608064910080 72057594037927936 Bool.false 16777210 16777216 142 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q3 15074239059 16777216 226375608064910080 72057594037927936 142 Ns222p1539 Ns222p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777210 16777216 Ns222p1539 Ns222p89 53943475703 34359738368 5785645 5780000 (Ns222p1543 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p1545 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz192) Bool.false Ns222p1516 Ns222p1517 8039334822895977567 591872000000000000000000 120593912473 134217728 1824 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz192) (@HAdd.hAdd Real Real Real qz358 qz539 (Enclosure.sfrac Bool.true Ns222p1518 Ns222p1519)) Bool.false Ns222p1516 Ns222p1517 8039334822895977567 591872000000000000000000 Ns222p1520 (Ns222p1537 rfl rfl)) 

noncomputable def Ns222p1546 := Ns222p1515 35937 BSN.abs_quadSignPos (BSN.cos_quad_nat0 340 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 109280666 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 204 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 18074736 134217728) qz195 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz192) qz192 1) Bool.false 8388605 8388608 42411701 3030384640000 134217680 134217728 1879 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz192) qz192 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz192)) Bool.false 8388605 8388608 42411701 3030384640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz192) qz192) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz192)) Bool.false 16777210 16777216 678587216 48486154240000 8388605 8388608 42411701 3030384640000 (Ns222p1544 rfl rfl) rfl)) rfl) (Ns222p1545 rfl) RS223to240.d7 

noncomputable def Ns222p1547 := nat_lit 26050735806570841306584228670499161430402987097089077249370814738721 

noncomputable def Ns222p1548 := nat_lit 2282791493395489300883169217589684678829637933351604246419403041 

noncomputable def Ns222p1549 := nat_lit 78147641836725732941150919673062304921851302015400528539619605410081 

noncomputable def Ns222p1550 := BSN.cos_dyadic_bound_f 83139667 134217728 3 2 134217728 67108864 Ns222p1547 Ns222p105 Ns222p1548 Ns222p1549 Ns222p108 Ns222p1548 109280666 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 83139667) qz361 0 2 Ns222p1547 Ns222p105 Ns222p1548 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 83139667) qz362 0 2 Ns222p1549 Ns222p108 Ns222p1548 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1551 := nat_lit 2905487875902914756537678289436686907259928436946527757171045811969426860838245931921596914442448321890625 

noncomputable def Ns222p1552 := nat_lit 2621505005372577626079797017100071425953079222016893827527602162717441719536071477636542246337890625 

noncomputable def Ns222p1553 := nat_lit 17596968356931311821405446085441339431582890255544235832269521260504278077285826683223648042397058907490625 

noncomputable def Ns222p1554 := BSN.cos_dyadic_bound_f 192698895 134217728 4 3 134217728 67108864 Ns222p1551 Ns222p227 Ns222p1552 Ns222p1553 Ns222p230 Ns222p1552 18074736 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 192698895) qz361 0 3 Ns222p1551 Ns222p227 Ns222p1552 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 192698895) qz362 0 3 Ns222p1553 Ns222p230 Ns222p1552 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1555 := nat_lit 1613058867874437935241096945525641359016804368681878888528136392568756546315190655483511715811733301886976 

noncomputable def Ns222p1556 := nat_lit 450096648540247147511935874284884798158540586953787752035566324365942067784534290743160473330384896 

noncomputable def Ns222p1557 := nat_lit 9776730506676467846239842875426007334160665036022553304386015835892893760548130625286946034692858073579520 

noncomputable def Ns222p1558 := BSN.cos_dyadic_bound_f 166382948 134217728 4 3 134217728 67108864 Ns222p1555 Ns222p227 Ns222p1556 Ns222p1557 Ns222p230 Ns222p1556 43637901 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 166382948) qz361 0 3 Ns222p1555 Ns222p227 Ns222p1556 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 166382948) qz362 0 3 Ns222p1557 Ns222p230 Ns222p1556 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1559 := nat_lit 2960564857982242765697099555230531217502054510866492302362162673921 

noncomputable def Ns222p1560 := nat_lit 29487834556561077551728300803013706867644104230169064330410241 

noncomputable def Ns222p1561 := nat_lit 8881635598277615174936195209089987625092428244391016568957827201281 

noncomputable def Ns222p1562 := BSN.cos_dyadic_bound_f 48273119 134217728 3 2 134217728 67108864 Ns222p1559 Ns222p105 Ns222p1560 Ns222p1561 Ns222p108 Ns222p1560 125629883 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 48273119) qz361 0 2 Ns222p1559 Ns222p105 Ns222p1560 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 48273119) qz362 0 2 Ns222p1561 Ns222p108 Ns222p1560 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1563 := Ns222p1513 61051 BSN.abs_quadSignPos (BSN.cos_quad_nat0 108 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 43637901 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 34 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 125629883 134217728) qz195 rfl rfl (Ns222p1546 RS223to240.d9 RS223to240.d11 RS223to240.d13 RS223to240.d17 (Ns222p1550 rfl rfl) (Ns222p1554 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns222p1545 rfl) RS223to240.d19 RS223to240.d21 RS223to240.d23 RS223to240.d25 RS223to240.d17 (Ns222p1558 rfl rfl) (Ns222p1562 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns222p1564 := nat_lit 948369510741761924967704468183729124311746852016185624585867540316711468408736164710002242513703694176256 

noncomputable def Ns222p1565 := nat_lit 91630768285087730670210704545528023652390733309126557969426795938175508733013000875828890013208576 

noncomputable def Ns222p1566 := nat_lit 5750272087133484937325007039370585665938162180038310230718592945118232025272327881405279109909083142164480 

noncomputable def Ns222p1567 := BSN.cos_dyadic_bound_f 145714726 134217728 4 3 134217728 67108864 Ns222p1564 Ns222p227 Ns222p1565 Ns222p1566 Ns222p230 Ns222p1565 62589695 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 145714726) qz361 0 3 Ns222p1564 Ns222p227 Ns222p1565 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 145714726) qz362 0 3 Ns222p1566 Ns222p230 Ns222p1565 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1568 := nat_lit 3061133783458020145436376450625 

noncomputable def Ns222p1569 := BSN.cos_dyadic_bound_f 41828335 134217728 2 1 134217728 67108864 Ns222p1568 Ns222p246 Ns222p1568 Ns222p1568 Ns222p247 Ns222p1568 127752505 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 41828335) qz361 0 1 Ns222p1568 Ns222p246 Ns222p1568 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 41828335) qz362 0 1 Ns222p1568 Ns222p247 Ns222p1568 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1570 := Ns222p1511 81899 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 26 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 62589695 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 78 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 127752505 134217728) qz195 rfl rfl (Ns222p1563 rfl rfl) (Ns222p1545 rfl) RS223to240.d27 RS223to240.d29 RS223to240.d31 RS223to240.d33 RS223to240.d17 (Ns222p1567 rfl rfl) (Ns222p1569 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p1571 := nat_lit 1844210794432658361365995150365625652801040969900191507976125532298544464887854412869105960883712698350721 

noncomputable def Ns222p1572 := nat_lit 672241105466267703107057848032042627748121439934851936522595576333182674203068306857109172287962241 

noncomputable def Ns222p1573 := nat_lit 11176243227438670708250147691891386785162234123701271385880007351873353538753339132956704555314542200749185 

noncomputable def Ns222p1574 := BSN.cos_dyadic_bound_f 172039071 134217728 4 3 134217728 67108864 Ns222p1571 Ns222p227 Ns222p1572 Ns222p1573 Ns222p230 Ns222p1572 38251915 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 172039071) qz361 0 3 Ns222p1571 Ns222p227 Ns222p1572 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 172039071) qz362 0 3 Ns222p1573 Ns222p230 Ns222p1572 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1575 := nat_lit 1708824221547280047114669024016 

noncomputable def Ns222p1576 := BSN.cos_dyadic_bound_f 36155498 134217728 2 1 134217728 67108864 Ns222p1575 Ns222p246 Ns222p1575 Ns222p1575 Ns222p247 Ns222p1575 129377330 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 36155498) qz361 0 1 Ns222p1575 Ns222p246 Ns222p1575 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 36155498) qz362 0 1 Ns222p1575 Ns222p247 Ns222p1575 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1577 := Ns222p1509 100116 BSN.abs_quadSignNeg qz743 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 38251915 134217728) BSN.abs_quadSignNeg qz408 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 129377330 134217728) qz195 rfl rfl (Ns222p1570 rfl) (Ns222p1545 rfl) RS223to240.d35 RS223to240.d37 RS223to240.d46 RS223to240.d48 RS223to240.d17 (Ns222p1574 rfl rfl) (Ns222p1576 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p1578 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz192) qz192 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz192) qz192 9) 57073884 134217728 100116 134217728 57073884 134217728 100116 134217728 15320654077231104 14268471 16777216 25029 16777216 (Ns222p1577 rfl) 

noncomputable def Ns222p1579 := @Enclosure.Real.IsNear.mulLit_tf qz750 (Zeta.RiemannSiegel.correction qz194) 86711 262144 1 8388608 11302846708447 17592186044416 428652025206179 12710354417090560000 980081140936147817 4611686018427387904 

noncomputable abbrev qz752 := (@HPow.hPow Real Real Real qz6 qz193 qz8)

noncomputable def Ns222p1580 := @Enclosure.Real.IsNear.mulLit_tf qz48 qz752 1 1 0 1 86711 262144 1 8388608 86711 262144 1 8388608 

noncomputable def Ns222p1581 := @Enclosure.Real.IsNear.sqrt_image qz193 1401466430043 16777216000 524859 16777216000 76669251 76669280 8388608 (@Enclosure.Real.IsNear.of_eq qz193 (@HMul.hMul Real Real Real qz4 qz192 qz2) Bool.false 1401466430043 16777216000 524859 16777216000 (BSN.t_div_two_pi_mk qz192 524859 1000 qz195) (@Enclosure.Real.IsNear.mulLit_ff qz192 qz2 524859 1000 0 1 2670177 16777216 1 16777216 1401466430043 16777216000 524859 16777216000 (Enclosure.Real.IsNear.const Bool.false 524859 1000) RS223to240.d40 rfl)) 

noncomputable abbrev qz908 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 524859 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz753 := qz908

noncomputable abbrev qz542 := qz753

noncomputable abbrev qz198 := qz542

noncomputable def Ns222p1582 := @Enclosure.Real.IsNear.sqrt_image qz198 153338531 16777216 29 16777216 25360368 25360374 8388608 (@Enclosure.Real.IsNear.recentre' qz198 Bool.false 153338531 16777216 29 16777216 153338531 16777216 29 16777216 (Ns222p1581 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns222p1583 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz198) 25360371 8388608 3 8388608 2774751 2774753 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz198) Bool.false 50720742 16777216 6 16777216 25360371 8388608 3 8388608 (Ns222p1582 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns222p1584 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz198)) Bool.false 5549504 16777216 2 16777216 86711 262144 1 8388608 (Ns222p1583 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz199 := (@HMul.hMul Real Real Real qz343 qz341 qz536)

noncomputable abbrev qz754 := (@HMul.hMul Real Real Real qz848 qz907 qz907)

noncomputable abbrev qz543 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz754 qz749) qz639)

noncomputable abbrev qz200 := (Real.cos (@HMul.hMul Real Real Real qz343 qz341 qz543))

noncomputable def Ns222p1585 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz194) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz199)) qz200) Bool.false 11302846708447 

noncomputable def Ns222p1586 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz199)) qz200 13129151 8388608 29 

noncomputable def Ns222p1587 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz199)) Bool.false 26258302 16777216 464 16777216 13129151 8388608 29 

noncomputable def Ns222p1588 := @Enclosure.Real.IsNear.recentre' (Real.cos qz199) Bool.false 5359733 8388608 545647216 48486154240000 5359733 8388608 34102951 3030384640000 

noncomputable def Ns222p1589 := @Enclosure.Real.IsNear.cos_image qz199 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 14725191) qz359) Bool.false 14725191 16777216 183 16777216 Bool.false 5359733 8388608 1 

noncomputable def Ns222p1590 := nat_lit 782596186882408577240561547 

noncomputable def Ns222p1591 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz194 884279719003555 140737488355328 1 500000000000000 2343587 16777216 29 16777216 2072386453820384451785 2361183241434822606848 Ns222p1590 

noncomputable def Ns222p1592 := @Enclosure.Real.IsNear.subLit_ff_p qz198 qz46 153338531 16777216 29 16777216 9 1 0 1 2343587 2343587 16777216 29 

noncomputable def Ns222p1593 := @Ns222p1592 16777216 (@Enclosure.Real.IsNear.recentre' qz198 Bool.false 153338531 16777216 29 16777216 153338531 16777216 29 16777216 (Ns222p1581 rfl rfl rfl rfl rfl rfl) rfl) qz411 

noncomputable def Ns222p1594 := @Enclosure.Real.IsNear.recentre' qz199 Bool.false 2072386453820384451785 2361183241434822606848 Ns222p1590 Ns222p150 14725191 16777216 183 16777216 (@Ns222p1591 Ns222p150 RS223to240.d39 (Ns222p1593 rfl rfl) rfl) 

noncomputable def Ns222p1595 := nat_lit 6260168027242922577288816580238374737502300158020340182033601 

noncomputable def Ns222p1596 := nat_lit 2210484600600538408760521346566869740936928007771124016321 

noncomputable def Ns222p1597 := nat_lit 18776083112527566655048928698021990473025026618045478298068161 

noncomputable def Ns222p1598 := BSN.cos_dyadic_bound_f 14725191 16777216 3 2 8388608 2890000 Ns222p1595 Ns222p866 Ns222p1596 Ns222p1597 Ns222p869 Ns222p1596 5359733 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 14725191) qz391 0 2 Ns222p1595 Ns222p866 Ns222p1596 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 14725191) (BSN.cosOddQ 16777216) 0 2 Ns222p1597 Ns222p869 Ns222p1596 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1599 := @Enclosure.Real.IsNear.inv_image (Real.cos qz199) 5359733 8388608 34102951 3030384640000 13128919 13129383 8388608 (Ns222p1588 (@Ns222p1589 2890000 (Ns222p1594 rfl) (Enclosure.sfrac_false_div 14725191 16777216) (Ns222p1598 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns222p1600 := @Enclosure.Real.IsNear.recentre' qz200 Bool.false 3443588 8388608 

noncomputable abbrev qz201 := (@HMul.hMul Real Real Real qz343 qz341 qz543)

noncomputable def Ns222p1601 := @Enclosure.Real.IsNear.cos_image qz201 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 9628323)) qz370) Bool.true 9628323 8388608 

noncomputable def Ns222p1602 := nat_lit 45468470551083504034924976645 

noncomputable def Ns222p1603 := nat_lit 3359594492611179700757322598245261 

noncomputable def Ns222p1604 := @Enclosure.Real.IsNear.recentre' qz201 Bool.true Ns222p1602 Ns222p168 Ns222p1603 

noncomputable abbrev qz202 := qz543

noncomputable def Ns222p1605 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz202 884279719003555 140737488355328 1 500000000000000 51418651331639 

noncomputable abbrev qz544 := (@HSub.hSub Real Real Real qz634 qz754 qz749)

noncomputable abbrev qz203 := qz544

noncomputable def Ns222p1606 := @Enclosure.Real.IsNear.subLit_tf qz203 qz25 33826465287223 281474976710656 622468151 281474976710656 1 16 

noncomputable abbrev qz545 := qz754

noncomputable abbrev qz204 := qz545

noncomputable def Ns222p1607 := @Enclosure.Real.IsNear.subLit_ff_n qz204 qz194 5492400026569 281474976710656 135928887 281474976710656 2343587 16777216 29 16777216 

noncomputable def Ns222p1608 := @Enclosure.Real.IsNear.mulLit_ff qz194 qz194 2343587 16777216 29 16777216 2343587 16777216 29 16777216 5492400026569 281474976710656 

noncomputable def Ns222p1609 := nat_lit 71568170616787281860229132648807931792182897414625883238561 

noncomputable def Ns222p1610 := nat_lit 73859303603673640760884872342159178347337454777091666081 

noncomputable def Ns222p1611 := nat_lit 214556793243154498299165628201739477019854017334323466383521 

noncomputable def Ns222p1612 := BSN.cos_dyadic_bound_f 9628323 8388608 3 2 8388608 2890000 Ns222p1609 Ns222p642 Ns222p1610 Ns222p1611 Ns222p645 Ns222p1610 3443588 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 9628323) (BSN.cosEvenQ 8388608) 0 2 Ns222p1609 Ns222p642 Ns222p1610 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 9628323) (BSN.cosOddQ 8388608) 0 2 Ns222p1611 Ns222p645 Ns222p1610 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1613 := @Ns222p1600 346518608 24243077120000 860897 2097152 21657413 1515192320000 (@Ns222p1601 117 8388608 Bool.false 3443588 8388608 1 2890000 (@Ns222p1604 Ns222p171 9628323 8388608 117 8388608 (@Ns222p1605 281474976710656 622468151 281474976710656 Ns222p1602 Ns222p168 Ns222p1603 Ns222p171 RS223to240.d39 (@Ns222p1606 0 1 822698421306224 51418651331639 281474976710656 622468151 281474976710656 (@Ns222p1607 567513914640242311168 33826465287223 281474976710656 622468151 281474976710656 (@Ns222p1608 135928887 281474976710656 (Ns222p1593 rfl rfl) (Ns222p1593 rfl rfl) rfl) (Ns222p1593 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 9628323 8388608) (BSN.cos_neg_of_bound 9628323 8388608 Bool.false 3443588 8388608 1 2890000 (Ns222p1612 rfl rfl)) rfl rfl) 

noncomputable def Ns222p1614 := @Ns222p1579 1197569799643773756287 Ns222p874 (Ns222p1580 qz61 (@Enclosure.Real.IsNear.of_eq qz752 (@Inv.inv Real Real.instInv (Real.sqrt qz198)) Bool.false 86711 262144 1 8388608 (BSN.rpow_neg_quarter_mk qz193 (BSN.t_div_two_pi_nonneg qz192 524859 1000 qz195)) Ns222p1584) rfl) (@Ns222p1585 17592186044416 428652025206179 12710354417090560000 (BSN.correction_mk qz194 (BSN.cos_two_pi_p_ne_zero_mk qz192 524859 1000 9 qz195 rfl rfl (@BSN.floor_sqrt_eq_dec qz192 524859 1000 9 qz195 rfl rfl rfl))) (@Ns222p1586 1048576 860897 2097152 21657413 1515192320000 11302846708447 17592186044416 428652025206179 12710354417090560000 (@Ns222p1587 1048576 (Ns222p1599 rfl rfl rfl rfl rfl) rfl) (Ns222p1613 rfl) rfl)) 

noncomputable def Ns222p1615 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz192) (hardyZApproximantRS₀ qz192) Bool.false 4902168584707310441 4611686018427387904 160261300152323586876287 Ns222p874 (@Eq.refl Real (hardyZApproximantRS₀ qz192)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz192) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz192) qz192 9) (@HMul.hMul Real Real Real qz4 qz750 (Zeta.RiemannSiegel.correction qz194))) Bool.false 4902168584707310441 4611686018427387904 160261300152323586876287 Ns222p874 (BSN.hardyZApproximantRS₀_eq qz192 9 (@BSN.floor_sqrt_eq_dec qz192 524859 1000 9 qz195 rfl rfl rfl)) (@Ns222p1507 4902168584707310441 4611686018427387904 160261300152323586876287 Ns222p874 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz192) qz192 9) (@HAdd.hAdd Real Real Real qz358 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz192) qz192 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz192) qz192 9)) Bool.false 14268471 16777216 25029 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz192) qz192 9) (Ns222p1578 (Ns222p1577 rfl) rfl rfl)) (Ns222p1614 rfl) rfl rfl)) 

theorem RS223to240.d60 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz192) Bool.false 4902168584707310441 4611686018427387904 160261300152323586876287 Ns222p874 := Ns222p1615 

noncomputable def Ns222p1616 := nat_lit 733152985897721495861724184576 

noncomputable abbrev qz909 := (Enclosure.sfrac Bool.false 527077 1000)

noncomputable abbrev qz755 := qz909

noncomputable abbrev qz546 := qz755

noncomputable abbrev qz205 := qz546

noncomputable abbrev qz910 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 527077 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz756 := qz910

noncomputable abbrev qz547 := qz756

noncomputable abbrev qz206 := qz547

noncomputable abbrev qz911 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 527077 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz757 := qz911

noncomputable abbrev qz548 := qz757

noncomputable abbrev qz207 := qz548

noncomputable abbrev qz758 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz206 qz8))

noncomputable def Ns222p1617 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz205) qz205 9) (@HMul.hMul Real Real Real qz4 qz758 (Zeta.RiemannSiegel.correction qz207)) 324088465 67108864 100537 67108864 478018319645740990921 2361183241434822606848 68812987096909899659 Ns222p328 Ns222p1616 

noncomputable def Ns222p1618 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz205) qz205 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 527077 1000 122 162 134217728 67108864 2251799813685248 Bool.false 121252914206 1831 

noncomputable def Ns222p1619 := Ns222p1618 279097919 47 47453128 8 294906479 47 44739240 8 Bool.true 254284139 82244 Bool.true 132076522 Bool.true 31256336 7074237752028440 1 Bool.false 74310606 Bool.true Bool.false 130594692 Bool.true Bool.true 324088465 

noncomputable def Ns222p1620 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz205) qz205 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 527077 1000 26 77 134217728 67108864 2251799813685248 Bool.false 121252914206 1831 

noncomputable def Ns222p1621 := Ns222p1620 240485871 47 54794152 8 261175631 47 50729528 8 Bool.true 151382007 61308 Bool.true 20110655 Bool.true 172942866 7074237752028440 1 Bool.false 132713894 Bool.true Bool.false 128906088 Bool.true Bool.true 254284139 

noncomputable def Ns222p1622 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz205) qz205 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 527077 1000 109 35 134217728 67108864 2251799813685248 Bool.false 121252914206 1831 

noncomputable def Ns222p1623 := Ns222p1622 186065264 47 67108856 8 216015088 47 60023992 8 Bool.true 92149147 36088 Bool.false 201863212 Bool.false 17324673 7074237752028440 1 Bool.false 133918399 Bool.true Bool.false 17276604 Bool.false Bool.true 151382007 

noncomputable def Ns222p1624 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz205) qz205 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 527077 1000 342 206 134217728 67108864 2251799813685248 Bool.false 121252914206 1831 

noncomputable def Ns222p1625 := Ns222p1624 93032624 47 94906264 8 147453232 47 77490640 16 Bool.false 26233600 1887 Bool.false 114137612 Bool.false 102991931 7074237752028440 1 Bool.false 88541956 Bool.true Bool.false 96603629 Bool.true Bool.true 92149147 

noncomputable def Ns222p1626 := nat_lit 196277338184688607903613071158607682717443391671313177047 

noncomputable def Ns222p1627 := nat_lit 217264043190181094220398761956133840132846412365824000 

noncomputable def Ns222p1628 := nat_lit 19525967148414438342021145195360000 

noncomputable def Ns222p1629 := nat_lit 61750155052260735777849379802584576320 

noncomputable abbrev qz549 := (@Eq.refl Real qz755)

noncomputable abbrev qz208 := qz549

noncomputable def Ns222p1630 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz205 527077 1000 1111241655716 16000000 1054154 4000 2000 Ns222p1628 Ns222p1629 qz208 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns222p1631 := nat_lit 62808748219100354529156182770754458469581885334820216655040 

noncomputable abbrev qz550 := (Enclosure.sfrac Bool.false 527077 2000)

noncomputable abbrev qz759 := (Real.log (Enclosure.sfrac Bool.false 1111241655716 16000000))

noncomputable abbrev qz209 := (@HSub.hSub Real Real Real qz347 (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 527077 4000) qz759) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1054154)))))) qz550)

noncomputable abbrev qz551 := (@HSub.hSub Real Real Real qz11 qz209 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 527077 2000) (Real.log Real.pi)))

noncomputable def Ns222p1632 := @Enclosure.Real.IsNear.addLit_ft_p qz551 (Enclosure.sfrac Bool.true Ns222p1628 Ns222p1629) 1017143522153560247447 1125899906842624000 8073091856760347201 591872000000000000000000 Ns222p1628 Ns222p1629 0 1 Ns222p1631 

noncomputable def Ns222p1633 := nat_lit 68259346296684261761727070208000 

noncomputable abbrev qz552 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 527077 2000) (Real.log Real.pi))

noncomputable def Ns222p1634 := @Enclosure.Real.IsNear.subLit_ff_p qz209 qz552 1356805452056645045399 1125899906842624000 1672116234337137 289000000000000000000 20245428675597 67108864000 527077 67108864000 Ns222p1633 1017143522153560247447 1125899906842624000 

noncomputable def Ns222p1635 := nat_lit 2713610904113290090798000 

noncomputable abbrev qz210 := (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 527077 4000) qz759) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1054154))))))

noncomputable def Ns222p1636 := @Enclosure.Real.IsNear.subLit_ff_p qz210 qz550 1653523424656089910423 1125899906842624000 1672116234337137 289000000000000000000 527077 2000 0 1 Ns222p1635 1356805452056645045399 1125899906842624000 1672116234337137 289000000000000000000 

noncomputable def Ns222p1637 := nat_lit 3723403739564776469300434449836539904 

noncomputable def Ns222p1638 := nat_lit 26955176801795915443601408 

noncomputable def Ns222p1639 := nat_lit 326407107745096867136931145929050879241080815415040 

noncomputable def Ns222p1640 := nat_lit 91639489538725065204206159432820315907677554688 

noncomputable def Ns222p1641 := nat_lit 46263619582352817622016426216008578659083008 

noncomputable def Ns222p1642 := BSN.log_dyadic_bound 62665655716 2159817655716 3 2 Ns222p1639 67108864 23120000 Ns222p1640 Ns222p1641 3895330 2222483311432 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 62665655716) (BSN.artanhQ 2159817655716) 0 2 Ns222p1640 Ns222p1639 Ns222p1641 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns222p1643 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 527077 4000) qz759 527077 4000 0 1 3137995582282999 281474976710656 781250289 18062500000000000 1653965297522976263923 1125899906842624000 411779058575253 72250000000000000000 (Enclosure.Real.IsNear.const Bool.false 527077 4000) (BSN.isNear_log_sfrac 1111241655716 16000000 3137995582282999 281474976710656 781250289 18062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1111241655716) qz354)) Bool.false Ns222p1638 Ns222p89 1000000369920000 23120000000000000000000 3137995582282999 281474976710656 781250289 18062500000000000 (BSN.log_rat_reduce_isNear 1111241655716 16000000 16 2222483311432 2097152000000 3895330 67108864 24973259072661432 36028797018963968 23120000 1000000000000000 rfl rfl rfl rfl (Ns222p1642 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns222p1644 := BSN.arctan_dyadic_bound_f 1000 1054154 1 0 8388608 2890000 0 1 1 0 1 1 7957 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1054154) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1054154) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz553 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1054154)))

noncomputable def Ns222p1645 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz553 884279719003555 562949953421312 1 2000000000000000 7957 8388608 1 2890000 7413396532291600121856 883745733772707 562949953421312 200000000289 578000000000000000 qz16 (Ns222p1644 rfl) rfl rfl 

noncomputable def Ns222p1646 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 527077 4000) qz759) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz553)) 1653965297522976263923 1125899906842624000 411779058575253 72250000000000000000 883745733772707 2251799813685248 200000000289 2312000000000000000 Ns222p1637 1653523424656089910423 1125899906842624000 1672116234337137 289000000000000000000 (Ns222p1643 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz553) 1 4 0 1 883745733772707 562949953421312 200000000289 578000000000000000 883745733772707 2251799813685248 200000000289 2312000000000000000 qz357 Ns222p1645 rfl) 

noncomputable def Ns222p1647 := @Ns222p1632 Ns222p1626 Ns222p1627 8073091856760347201 591872000000000000000000 (@Ns222p1634 8073091856760347201 591872000000000000000000 (Ns222p1636 (Ns222p1646 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 527077 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz550 (Real.log Real.pi) 527077 2000 0 1 38410761 33554432 1 33554432 20245428675597 67108864000 527077 67108864000 (Enclosure.Real.IsNear.const Bool.false 527077 2000) RS223to240.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns222p1628 Ns222p1629) 

noncomputable def Ns222p1648 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz205) Bool.false Ns222p1626 Ns222p1627 8073091856760347201 591872000000000000000000 15156614275 16777216 115 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz205) (@HAdd.hAdd Real Real Real qz358 qz551 (Enclosure.sfrac Bool.true Ns222p1628 Ns222p1629)) Bool.false Ns222p1626 Ns222p1627 8073091856760347201 591872000000000000000000 Ns222p1630 (Ns222p1647 rfl rfl)) 

noncomputable def Ns222p1649 := nat_lit 2087424096887029216319938938456388980801 

noncomputable def Ns222p1650 := nat_lit 167255588988979673561517887044862711294853120 

noncomputable def Ns222p1651 := nat_lit 1170789122922857714930625209314038979063971840 

noncomputable def Ns222p1652 := BSN.sin_dyadic_bound_f 6759314799 34359738368 2 1 16777216 5785645 Ns222p1649 Ns222p1650 Ns222p1649 Ns222p1649 Ns222p1651 Ns222p1649 3279200 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 6759314799) qz371 0 1 Ns222p1649 Ns222p1650 Ns222p1649 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 6759314799) qz372 0 1 Ns222p1649 Ns222p1651 Ns222p1649 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1653 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz205) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15156614275) qz359) Bool.false 15156614275 16777216 115 8388608 Bool.false 3279200 16777216 1 2890000 (Ns222p1648 rfl) (Enclosure.sfrac_false_div 15156614275 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15156614275) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 475644493932293573836800) qz360) 226375608064910080 72057594037927936 Bool.false 3279200 16777216 143 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q3 15156614275 16777216 226375608064910080 72057594037927936 143 475644493932293573836800 Ns222p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 3279200 16777216 475644493932293573836800 Ns222p89 6759314799 34359738368 5785645 5780000 (Ns222p1652 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p1654 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz205) Bool.false Ns222p1626 Ns222p1627 8073091856760347201 591872000000000000000000 121252914206 134217728 1831 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz205) (@HAdd.hAdd Real Real Real qz358 qz551 (Enclosure.sfrac Bool.true Ns222p1628 Ns222p1629)) Bool.false Ns222p1626 Ns222p1627 8073091856760347201 591872000000000000000000 Ns222p1630 (Ns222p1647 rfl rfl)) 

noncomputable def Ns222p1655 := Ns222p1625 36088 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 342 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 88541956 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 206 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 96603629 134217728) qz208 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz205) qz205 1) Bool.false 102475 524288 21296163 1515192320000 26233600 134217728 1887 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz205) qz205 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz205)) Bool.false 102475 524288 21296163 1515192320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz205) qz205) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz205)) Bool.false 3279200 16777216 340738608 24243077120000 102475 524288 21296163 1515192320000 (Ns222p1653 rfl rfl) rfl)) rfl) (Ns222p1654 rfl) RS223to240.d7 

noncomputable def Ns222p1656 := nat_lit 92554835247414230442473841267708713073300028251202587632500148862976 

noncomputable def Ns222p1657 := nat_lit 28802504662427029909099801029945955374258913065923946360927748096 

noncomputable def Ns222p1658 := nat_lit 277606900732917837267603324201066247309151566927475915004778591092736 

noncomputable def Ns222p1659 := BSN.cos_dyadic_bound_f 114137612 134217728 3 2 134217728 67108864 Ns222p1656 Ns222p105 Ns222p1657 Ns222p1658 Ns222p108 Ns222p1657 88541956 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 114137612) qz361 0 2 Ns222p1656 Ns222p105 Ns222p1657 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 114137612) qz362 0 2 Ns222p1658 Ns222p108 Ns222p1657 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1660 := nat_lit 61355180267441920010603743312748642100060506004144490612250223844321 

noncomputable def Ns222p1661 := nat_lit 12659763908570478498774238077193537154316115123589165378356124641 

noncomputable def Ns222p1662 := nat_lit 184040221274508619074813681462091539225872885782186293505993959283681 

noncomputable def Ns222p1663 := BSN.cos_dyadic_bound_f 102991931 134217728 3 2 134217728 67108864 Ns222p1660 Ns222p105 Ns222p1661 Ns222p1662 Ns222p108 Ns222p1661 96603629 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 102991931) qz361 0 2 Ns222p1660 Ns222p105 Ns222p1661 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 102991931) qz362 0 2 Ns222p1662 Ns222p108 Ns222p1661 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1664 := nat_lit 9089527065271653549705875192777424354884934224792575355413792251572324500012567481260445012334193206624256 

noncomputable def Ns222p1665 := nat_lit 4578109250963762124542343546840943809597268948425992223220695000066517316465212190214465364695187456 

noncomputable def Ns222p1666 := nat_lit 45400159991930178023626300920370627109333430178184794002778263777900584527910593707760838625894404945084416 

noncomputable def Ns222p1667 := BSN.sin_dyadic_bound_f 201863212 134217728 4 3 134217728 67108864 Ns222p1664 Ns222p111 Ns222p1665 Ns222p1666 Ns222p114 Ns222p1665 133918399 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 201863212) qz363 0 3 Ns222p1664 Ns222p111 Ns222p1665 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 201863212) qz364 0 3 Ns222p1666 Ns222p114 Ns222p1665 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1668 := nat_lit 90086597555076559336421911041 

noncomputable def Ns222p1669 := BSN.sin_dyadic_bound_f 17324673 134217728 2 1 134217728 67108864 Ns222p1668 Ns222p117 Ns222p1668 Ns222p1668 Ns222p118 Ns222p1668 17276604 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 17324673) qz363 0 1 Ns222p1668 Ns222p117 Ns222p1668 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 17324673) qz364 0 1 Ns222p1668 Ns222p118 Ns222p1668 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1670 := Ns222p1623 61308 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 109 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133918399 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 35 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 17276604 134217728) qz208 rfl rfl (Ns222p1655 RS223to240.d9 RS223to240.d11 RS223to240.d13 RS223to240.d17 (Ns222p1659 rfl rfl) (Ns222p1663 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns222p1654 rfl) RS223to240.d19 RS223to240.d21 RS223to240.d23 RS223to240.d25 RS223to240.d17 (Ns222p1667 rfl rfl) (Ns222p1669 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns222p1671 := nat_lit 163570455413057231954067450625 

noncomputable def Ns222p1672 := BSN.cos_dyadic_bound_f 20110655 134217728 2 1 134217728 67108864 Ns222p1671 Ns222p246 Ns222p1671 Ns222p1671 Ns222p247 Ns222p1671 132713894 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 20110655) qz361 0 1 Ns222p1671 Ns222p246 Ns222p1671 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 20110655) qz362 0 1 Ns222p1671 Ns222p247 Ns222p1671 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1673 := nat_lit 4893104752728066244919976779613559471434879723904863691096191547337476551081070566025789600016119477702656 

noncomputable def Ns222p1674 := nat_lit 715866140978156903945422305049427897329456632989341570967837484849953094090530441649374257277177856 

noncomputable def Ns222p1675 := nat_lit 24451746767511326312058360494162858247883592773466378535831083351648310139538893880301019550612381517090816 

noncomputable def Ns222p1676 := BSN.sin_dyadic_bound_f 172942866 134217728 4 3 134217728 67108864 Ns222p1673 Ns222p111 Ns222p1674 Ns222p1675 Ns222p114 Ns222p1674 128906088 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 172942866) qz363 0 3 Ns222p1673 Ns222p111 Ns222p1674 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 172942866) qz364 0 3 Ns222p1675 Ns222p114 Ns222p1674 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1677 := Ns222p1621 82244 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 26 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132713894 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 77 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 128906088 134217728) qz208 rfl rfl (Ns222p1670 rfl rfl) (Ns222p1654 rfl) RS223to240.d27 RS223to240.d29 RS223to240.d31 RS223to240.d33 RS223to240.d17 (Ns222p1672 rfl rfl) (Ns222p1676 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p1678 := nat_lit 165994479521397172985480509226295549659504594773261580759490561270016 

noncomputable def Ns222p1679 := nat_lit 92598721883668646724691765156959451186572552635348586540783329536 

noncomputable def Ns222p1680 := nat_lit 497798241120424181662992144148572730076140639214514045105390117150976 

noncomputable def Ns222p1681 := BSN.cos_dyadic_bound_f 132076522 134217728 3 2 134217728 67108864 Ns222p1678 Ns222p105 Ns222p1679 Ns222p1680 Ns222p108 Ns222p1679 74310606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 132076522) qz361 0 2 Ns222p1678 Ns222p105 Ns222p1679 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 132076522) qz362 0 2 Ns222p1680 Ns222p108 Ns222p1679 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1682 := nat_lit 954447989162046369244674850816 

noncomputable def Ns222p1683 := BSN.cos_dyadic_bound_f 31256336 134217728 2 1 134217728 67108864 Ns222p1682 Ns222p246 Ns222p1682 Ns222p1682 Ns222p247 Ns222p1682 130594692 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 31256336) qz361 0 1 Ns222p1682 Ns222p246 Ns222p1682 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 31256336) qz362 0 1 Ns222p1682 Ns222p247 Ns222p1682 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1684 := Ns222p1619 100537 BSN.abs_quadSignNeg qz743 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 74310606 134217728) BSN.abs_quadSignNeg qz408 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 130594692 134217728) qz208 rfl rfl (Ns222p1677 rfl) (Ns222p1654 rfl) RS223to240.d35 RS223to240.d37 RS223to240.d46 RS223to240.d48 RS223to240.d17 (Ns222p1681 rfl rfl) (Ns222p1683 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p1685 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz205) qz205 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz205) qz205 9) 324088465 134217728 100537 134217728 324088465 134217728 100537 134217728 86996834886615040 324088465 67108864 100537 67108864 (Ns222p1684 rfl) 

noncomputable def Ns222p1686 := @Enclosure.Real.IsNear.mulLit_tf qz758 (Zeta.RiemannSiegel.correction qz207) 5543657 16777216 1 16777216 86227975440353 140737488355328 12379867706323 299067162755072000 478018319645740990921 2361183241434822606848 

noncomputable abbrev qz760 := (@HPow.hPow Real Real Real qz6 qz206 qz8)

noncomputable def Ns222p1687 := @Enclosure.Real.IsNear.mulLit_tf qz48 qz760 1 1 0 1 5543657 16777216 1 16777216 5543657 16777216 1 16777216 

noncomputable def Ns222p1688 := @Enclosure.Real.IsNear.sqrt_image qz206 1407388882629 16777216000 527077 16777216000 76831078 76831108 8388608 (@Enclosure.Real.IsNear.of_eq qz206 (@HMul.hMul Real Real Real qz4 qz205 qz2) Bool.false 1407388882629 16777216000 527077 16777216000 (BSN.t_div_two_pi_mk qz205 527077 1000 qz208) (@Enclosure.Real.IsNear.mulLit_ff qz205 qz2 527077 1000 0 1 2670177 16777216 1 16777216 1407388882629 16777216000 527077 16777216000 (Enclosure.Real.IsNear.const Bool.false 527077 1000) RS223to240.d40 rfl)) 

noncomputable abbrev qz912 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 527077 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz761 := qz912

noncomputable abbrev qz554 := qz761

noncomputable abbrev qz211 := qz554

noncomputable def Ns222p1689 := @Enclosure.Real.IsNear.sqrt_image qz211 76831093 8388608 15 8388608 25387118 25387124 8388608 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 153662186 16777216 30 16777216 76831093 8388608 15 8388608 (Ns222p1688 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns222p1690 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz211) 25387121 8388608 3 8388608 2771828 2771829 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz211) Bool.false 50774242 16777216 6 16777216 25387121 8388608 3 8388608 (Ns222p1689 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns222p1691 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz211)) Bool.false 5543657 16777216 1 16777216 5543657 16777216 1 16777216 (Ns222p1690 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz343 qz341 qz548)

noncomputable abbrev qz762 := (@HMul.hMul Real Real Real qz848 qz911 qz911)

noncomputable abbrev qz555 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz762 qz757) qz639)

noncomputable abbrev qz213 := (Real.cos (@HMul.hMul Real Real Real qz343 qz341 qz555))

noncomputable def Ns222p1692 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz207) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz212)) qz213) Bool.false 86227975440353 

noncomputable def Ns222p1693 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz212)) qz213 30998491 16777216 669 

noncomputable def Ns222p1694 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz212)) Bool.false 30998491 16777216 669 16777216 30998491 16777216 669 

noncomputable def Ns222p1695 := @Enclosure.Real.IsNear.recentre' (Real.cos qz212) Bool.false 4540140 8388608 282938608 24243077120000 1135035 2097152 17683663 1515192320000 

noncomputable def Ns222p1696 := @Enclosure.Real.IsNear.cos_image qz212 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16758775) qz359) Bool.false 16758775 16777216 95 8388608 Bool.false 4540140 8388608 1 

noncomputable def Ns222p1697 := nat_lit 404791131147116398988052137 

noncomputable def Ns222p1698 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz207 884279719003555 140737488355328 1 500000000000000 1333621 8388608 15 8388608 1179294003137240022655 1180591620717411303424 Ns222p1697 

noncomputable def Ns222p1699 := @Enclosure.Real.IsNear.subLit_ff_p qz211 qz46 76831093 8388608 15 8388608 9 1 0 1 1333621 1333621 8388608 15 

noncomputable def Ns222p1700 := @Ns222p1699 8388608 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 153662186 16777216 30 16777216 76831093 8388608 15 8388608 (Ns222p1688 rfl rfl rfl rfl rfl rfl) rfl) qz411 

noncomputable def Ns222p1701 := @Enclosure.Real.IsNear.recentre' qz212 Bool.false 1179294003137240022655 1180591620717411303424 Ns222p1697 Ns222p263 16758775 16777216 95 8388608 (@Ns222p1698 Ns222p263 RS223to240.d39 (Ns222p1700 rfl rfl) rfl) 

noncomputable def Ns222p1702 := nat_lit 10505464127833390154028892346024457404309812425201729337890625 

noncomputable def Ns222p1703 := nat_lit 6222116838451426833688126949253112024883925293121337890625 

noncomputable def Ns222p1704 := nat_lit 31503948149823267608419300784174865988879669425018945337890625 

noncomputable def Ns222p1705 := BSN.cos_dyadic_bound_f 16758775 16777216 3 2 8388608 2890000 Ns222p1702 Ns222p866 Ns222p1703 Ns222p1704 Ns222p869 Ns222p1703 4540140 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 16758775) qz391 0 2 Ns222p1702 Ns222p866 Ns222p1703 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 16758775) (BSN.cosOddQ 16777216) 0 2 Ns222p1704 Ns222p869 Ns222p1703 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1706 := @Enclosure.Real.IsNear.inv_image (Real.cos qz212) 1135035 2097152 17683663 1515192320000 15498911 15499580 8388608 (Ns222p1695 (@Ns222p1696 2890000 (Ns222p1701 rfl) (Enclosure.sfrac_false_div 16758775 16777216) (Ns222p1705 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns222p1707 := @Enclosure.Real.IsNear.recentre' qz213 Bool.false 2781683 8388608 

noncomputable abbrev qz214 := (@HMul.hMul Real Real Real qz343 qz341 qz555)

noncomputable def Ns222p1708 := @Enclosure.Real.IsNear.cos_image qz214 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 10341431)) qz370) Bool.true 10341431 8388608 

noncomputable def Ns222p1709 := nat_lit 12209007194314798130833705205 

noncomputable def Ns222p1710 := nat_lit 4475316099151760051599260738862177 

noncomputable def Ns222p1711 := @Enclosure.Real.IsNear.recentre' qz214 Bool.true Ns222p1709 Ns222p858 Ns222p1710 

noncomputable abbrev qz215 := qz555

noncomputable def Ns222p1712 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz215 884279719003555 140737488355328 1 500000000000000 13806725329031 

noncomputable abbrev qz556 := (@HSub.hSub Real Real Real qz634 qz762 qz757)

noncomputable abbrev qz216 := qz556

noncomputable def Ns222p1713 := @Enclosure.Real.IsNear.subLit_tf qz216 qz25 9408678817927 70368744177664 165837975 70368744177664 1 16 

noncomputable abbrev qz557 := qz762

noncomputable abbrev qz217 := qz557

noncomputable def Ns222p1714 := @Enclosure.Real.IsNear.subLit_ff_n qz217 qz207 1778544971641 70368744177664 40008855 70368744177664 1333621 8388608 15 8388608 

noncomputable def Ns222p1715 := @Enclosure.Real.IsNear.mulLit_ff qz207 qz207 1333621 8388608 15 8388608 1333621 8388608 15 8388608 1778544971641 70368744177664 

noncomputable def Ns222p1716 := nat_lit 95277008919152700439732799701819460934390491370902242739521 

noncomputable def Ns222p1717 := nat_lit 130811253956660414137844004464979749232186740527444280641 

noncomputable def Ns222p1718 := nat_lit 285569404249544780490922711096528423304707100631651839657281 

noncomputable def Ns222p1719 := BSN.cos_dyadic_bound_f 10341431 8388608 3 2 8388608 2890000 Ns222p1716 Ns222p642 Ns222p1717 Ns222p1718 Ns222p645 Ns222p1717 2781683 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 10341431) (BSN.cosEvenQ 8388608) 0 2 Ns222p1716 Ns222p642 Ns222p1717 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 10341431) (BSN.cosOddQ 8388608) 0 2 Ns222p1718 Ns222p645 Ns222p1717 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1720 := @Ns222p1707 369638608 24243077120000 2781683 8388608 23102413 1515192320000 (@Ns222p1708 125 8388608 Bool.false 2781683 8388608 1 2890000 (@Ns222p1711 Ns222p281 10341431 8388608 125 8388608 (@Ns222p1712 70368744177664 165837975 70368744177664 Ns222p1709 Ns222p858 Ns222p1710 Ns222p281 RS223to240.d39 (@Ns222p1713 0 1 220907605264496 13806725329031 70368744177664 165837975 70368744177664 (@Ns222p1714 78925718401492975616 9408678817927 70368744177664 165837975 70368744177664 (@Ns222p1715 40008855 70368744177664 (Ns222p1700 rfl rfl) (Ns222p1700 rfl rfl) rfl) (Ns222p1700 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 10341431 8388608) (BSN.cos_neg_of_bound 10341431 8388608 Bool.false 2781683 8388608 1 2890000 (Ns222p1719 rfl rfl)) rfl rfl) 

noncomputable def Ns222p1721 := @Ns222p1686 68812987096909899659 Ns222p328 (Ns222p1687 qz61 (@Enclosure.Real.IsNear.of_eq qz760 (@Inv.inv Real Real.instInv (Real.sqrt qz211)) Bool.false 5543657 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz206 (BSN.t_div_two_pi_nonneg qz205 527077 1000 qz208)) Ns222p1691) rfl) (@Ns222p1692 140737488355328 12379867706323 299067162755072000 (BSN.correction_mk qz207 (BSN.cos_two_pi_p_ne_zero_mk qz205 527077 1000 9 qz208 rfl rfl (@BSN.floor_sqrt_eq_dec qz205 527077 1000 9 qz208 rfl rfl rfl))) (@Ns222p1693 16777216 2781683 8388608 23102413 1515192320000 86227975440353 140737488355328 12379867706323 299067162755072000 (@Ns222p1694 16777216 (Ns222p1706 rfl rfl rfl rfl rfl) rfl) (Ns222p1720 rfl) rfl)) 

noncomputable def Ns222p1722 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz205) (hardyZApproximantRS₀ qz205) Bool.true 10924830822612665531959 2361183241434822606848 7585641822573578315659 Ns222p328 (@Eq.refl Real (hardyZApproximantRS₀ qz205)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz205) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz205) qz205 9) (@HMul.hMul Real Real Real qz4 qz758 (Zeta.RiemannSiegel.correction qz207))) Bool.true 10924830822612665531959 2361183241434822606848 7585641822573578315659 Ns222p328 (BSN.hardyZApproximantRS₀_eq qz205 9 (@BSN.floor_sqrt_eq_dec qz205 527077 1000 9 qz208 rfl rfl rfl)) (@Ns222p1617 10924830822612665531959 2361183241434822606848 7585641822573578315659 Ns222p328 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz205) qz205 9) (@HAdd.hAdd Real Real Real qz358 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz205) qz205 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz205) qz205 9)) Bool.true 324088465 67108864 100537 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz205) qz205 9) (Ns222p1685 (Ns222p1684 rfl) rfl rfl)) (Ns222p1721 rfl) rfl rfl)) 

theorem RS223to240.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz205) Bool.true 10924830822612665531959 2361183241434822606848 7585641822573578315659 Ns222p328 := Ns222p1722 

noncomputable def Ns222p1723 := nat_lit 426488722984164833361920000 

noncomputable def Ns222p1724 := nat_lit 39002052404871491417412730880 

noncomputable abbrev qz913 := (Enclosure.sfrac Bool.false 528141 1000)

noncomputable abbrev qz763 := qz913

noncomputable abbrev qz558 := qz763

noncomputable abbrev qz218 := qz558

noncomputable abbrev qz914 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 528141 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz764 := qz914

noncomputable abbrev qz559 := qz764

noncomputable abbrev qz219 := qz559

noncomputable abbrev qz915 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 528141 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz765 := qz915

noncomputable abbrev qz560 := qz765

noncomputable abbrev qz220 := qz560

noncomputable abbrev qz766 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz219 qz8))

noncomputable def Ns222p1725 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz218) qz218 9) (@HMul.hMul Real Real Real qz4 qz766 (Zeta.RiemannSiegel.correction qz220)) 3238237 67108864 787 524288 467240534256060656361 2361183241434822606848 6245094438358036126983 Ns222p1723 Ns222p1724 

noncomputable def Ns222p1726 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz218) qz218 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 528141 1000 122 162 134217728 67108864 2251799813685248 Bool.false 121569267225 1835 

noncomputable def Ns222p1727 := Ns222p1726 279097919 47 47453128 8 294906479 47 44739240 8 Bool.false 78648468 82406 Bool.true 112683689 Bool.true 28683810 7074237752028440 1 Bool.false 89629420 Bool.true Bool.false 131164352 Bool.true Bool.false 3238237 

noncomputable def Ns222p1728 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz218) qz218 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 528141 1000 25 77 134217728 67108864 2251799813685248 Bool.false 121569267225 1835 

noncomputable def Ns222p1729 := Ns222p1728 240485871 47 54794152 8 261175631 47 50729528 8 Bool.false 173724282 61428 Bool.true 170463317 Bool.true 134480718 7074237752028440 1 Bool.false 128193481 Bool.true Bool.false 113082200 Bool.true Bool.false 78648468 

noncomputable def Ns222p1730 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz218) qz218 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 528141 1000 110 35 134217728 67108864 2251799813685248 Bool.false 121569267225 1835 

noncomputable def Ns222p1731 := Ns222p1730 186065264 47 67108856 8 216015088 47 60023992 8 Bool.false 177800584 36157 Bool.false 109414076 Bool.false 103837638 7074237752028440 1 Bool.false 92036317 Bool.true Bool.false 93784833 Bool.false Bool.false 173724282 

noncomputable def Ns222p1732 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz218) qz218 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 528141 1000 343 207 134217728 67108864 2251799813685248 Bool.false 121569267225 1835 

noncomputable def Ns222p1733 := Ns222p1732 93032624 47 94906264 8 147453232 47 77490640 16 Bool.false 74434336 1887 Bool.false 120675205 Bool.false 51625997 7074237752028440 1 Bool.false 105061256 Bool.false Bool.false 50362363 Bool.false Bool.false 177800584 

noncomputable def Ns222p1734 := nat_lit 22131669058752195459272332155598418698063226246613848647 

noncomputable def Ns222p1735 := nat_lit 24434319673932873133765194266201701034001153654784000 

noncomputable def Ns222p1736 := nat_lit 19723847706392288153486004816480000 

noncomputable def Ns222p1737 := nat_lit 62501862051191170111191794488779382080 

noncomputable abbrev qz767 := (@Eq.refl Real qz913)

noncomputable abbrev qz561 := qz767

noncomputable abbrev qz221 := qz561

noncomputable def Ns222p1738 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz218 528141 1000 1115732663524 16000000 1056282 4000 2000 Ns222p1736 Ns222p1737 qz221 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns222p1739 := nat_lit 63739206889206322922704316608123445850422091590247884103360 

noncomputable abbrev qz562 := (Enclosure.sfrac Bool.false 528141 2000)

noncomputable abbrev qz768 := (Real.log (Enclosure.sfrac Bool.false 1115732663524 16000000))

noncomputable abbrev qz222 := (@HSub.hSub Real Real Real qz347 (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 528141 4000) qz768) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1056282)))))) qz562)

noncomputable abbrev qz563 := (@HSub.hSub Real Real Real qz11 qz222 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 528141 2000) (Real.log Real.pi)))

noncomputable def Ns222p1740 := @Enclosure.Real.IsNear.addLit_ft_p qz563 (Enclosure.sfrac Bool.true Ns222p1736 Ns222p1737) 1019797282904627736367 1125899906842624000 8089285492482479433 591872000000000000000000 Ns222p1736 Ns222p1737 0 1 Ns222p1739 

noncomputable def Ns222p1741 := nat_lit 68437437166016187730480857088000 

noncomputable abbrev qz564 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 528141 2000) (Real.log Real.pi))

noncomputable def Ns222p1742 := @Enclosure.Real.IsNear.subLit_ff_p qz222 qz564 1360144881682311278383 1125899906842624000 1675441235567121 289000000000000000000 20286297725301 67108864000 528141 67108864000 Ns222p1741 1019797282904627736367 1125899906842624000 

noncomputable abbrev qz223 := (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 528141 4000) qz768) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1056282))))))

noncomputable def Ns222p1743 := @Enclosure.Real.IsNear.subLit_ff_p qz223 qz562 13259694664257571355 9007199254740992 1675441235567121 289000000000000000000 528141 2000 0 1 21762318106916980454128 1360144881682311278383 1125899906842624000 1675441235567121 289000000000000000000 

noncomputable def Ns222p1744 := nat_lit 29858177974498476210316328870871040 

noncomputable def Ns222p1745 := nat_lit 26964928680256241401856000 

noncomputable def Ns222p1746 := nat_lit 329130440183326045432065424107356348265135198416640 

noncomputable def Ns222p1747 := nat_lit 105690861001689133644082728345540231796649822208 

noncomputable def Ns222p1748 := nat_lit 61020772351499953635353766560669604063683328 

noncomputable def Ns222p1749 := BSN.log_dyadic_bound 67156663524 2164308663524 3 2 Ns222p1746 67108864 23120000 Ns222p1747 Ns222p1748 4165999 2231465327048 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 67156663524) (BSN.artanhQ 2164308663524) 0 2 Ns222p1747 Ns222p1746 Ns222p1748 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns222p1750 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 528141 4000) qz768 528141 4000 0 1 3139130850352375 281474976710656 781250289 18062500000000000 13263229651487629479 9007199254740992 412610308882749 72250000000000000000 (Enclosure.Real.IsNear.const Bool.false 528141 4000) (BSN.isNear_log_sfrac 1115732663524 16000000 3139130850352375 281474976710656 781250289 18062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1115732663524) qz354)) Bool.false Ns222p1745 Ns222p89 1000000369920000 23120000000000000000000 3139130850352375 281474976710656 781250289 18062500000000000 (BSN.log_rat_reduce_isNear 1115732663524 16000000 16 2231465327048 2097152000000 4165999 67108864 24973259072661432 36028797018963968 23120000 1000000000000000 rfl rfl rfl rfl (Ns222p1749 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns222p1751 := BSN.arctan_dyadic_bound_f 1000 1056282 1 0 8388608 2890000 0 1 1 0 1 1 7941 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1056282) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1056282) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz565 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1056282)))

noncomputable def Ns222p1752 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz565 884279719003555 562949953421312 1 2000000000000000 7941 8388608 1 2890000 7413405539490854862848 883746807514531 562949953421312 200000000289 578000000000000000 qz16 (Ns222p1751 rfl) rfl rfl 

noncomputable def Ns222p1753 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 528141 4000) qz768) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz565)) 13263229651487629479 9007199254740992 412610308882749 72250000000000000000 883746807514531 2251799813685248 200000000289 2312000000000000000 Ns222p1744 13259694664257571355 9007199254740992 1675441235567121 289000000000000000000 (Ns222p1750 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz565) 1 4 0 1 883746807514531 562949953421312 200000000289 578000000000000000 883746807514531 2251799813685248 200000000289 2312000000000000000 qz357 Ns222p1752 rfl) 

noncomputable def Ns222p1754 := @Ns222p1740 Ns222p1734 Ns222p1735 8089285492482479433 591872000000000000000000 (@Ns222p1742 8089285492482479433 591872000000000000000000 (Ns222p1743 (Ns222p1753 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 528141 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz562 (Real.log Real.pi) 528141 2000 0 1 38410761 33554432 1 33554432 20286297725301 67108864000 528141 67108864000 (Enclosure.Real.IsNear.const Bool.false 528141 2000) RS223to240.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns222p1736 Ns222p1737) 

noncomputable def Ns222p1755 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz218) Bool.false Ns222p1734 Ns222p1735 8089285492482479433 591872000000000000000000 15196158403 16777216 115 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz218) (@HAdd.hAdd Real Real Real qz358 qz563 (Enclosure.sfrac Bool.true Ns222p1736 Ns222p1737)) Bool.false Ns222p1734 Ns222p1735 8089285492482479433 591872000000000000000000 Ns222p1738 (Ns222p1754 rfl rfl)) 

noncomputable def Ns222p1756 := nat_lit 2376601464311673453019136 

noncomputable def Ns222p1757 := nat_lit 3048289152408781412022101742163319981571549052897222998983189361979153664780426025390625 

noncomputable def Ns222p1758 := nat_lit 78328409734541396139472704083124282315821843750582265496873076360672620779474006646456320 

noncomputable def Ns222p1759 := nat_lit 1692826615490463712974791372418419413107166564475175987980190687812864780426025390625 

noncomputable def Ns222p1760 := nat_lit 9141481803995363308640355643745123105888432825562718644973607704561835264780426025390625 

noncomputable def Ns222p1761 := nat_lit 3524778438054362826276271683740592704211982968776201947359288436230267935076330299090534400 

noncomputable def Ns222p1762 := BSN.cos_dyadic_bound_f 33773538125 34359738368 3 2 16777216 5785645 Ns222p1757 Ns222p1758 Ns222p1759 Ns222p1760 Ns222p1761 Ns222p1759 9304292 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 33773538125) (BSN.cosEvenQ 34359738368) 0 2 Ns222p1757 Ns222p1758 Ns222p1759 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 33773538125) (BSN.cosOddQ 34359738368) 0 2 Ns222p1760 Ns222p1761 Ns222p1759 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1763 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz218) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15196158403) qz359) Bool.false 15196158403 16777216 115 8388608 Bool.false 9304292 16777216 1 2890000 (Ns222p1755 rfl) (Enclosure.sfrac_false_div 15196158403 16777216) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15196158403) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns222p1756) qz360) 226375608064910080 72057594037927936 Bool.false 9304292 16777216 144 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q0 15196158403 16777216 226375608064910080 72057594037927936 144 Ns222p1756 Ns222p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 9304292 16777216 Ns222p1756 Ns222p89 33773538125 34359738368 5785645 5780000 (Ns222p1762 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p1764 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz218) Bool.false Ns222p1734 Ns222p1735 8089285492482479433 591872000000000000000000 121569267225 134217728 1835 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz218) (@HAdd.hAdd Real Real Real qz358 qz563 (Enclosure.sfrac Bool.true Ns222p1736 Ns222p1737)) Bool.false Ns222p1734 Ns222p1735 8089285492482479433 591872000000000000000000 Ns222p1738 (Ns222p1754 rfl rfl)) 

noncomputable def Ns222p1765 := Ns222p1733 36157 BSN.abs_quadSignPos (BSN.cos_quad_nat3 343 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 105061256 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 207 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 50362363 134217728) qz221 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz218) qz218 1) Bool.false 2326073 4194304 21296163 1515192320000 74434336 134217728 1887 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz218) qz218 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz218)) Bool.false 2326073 4194304 21296163 1515192320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz218) qz218) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz218)) Bool.false 9304292 16777216 340738608 24243077120000 2326073 4194304 21296163 1515192320000 (Ns222p1763 rfl rfl) rfl)) rfl) (Ns222p1764 rfl) RS223to240.d7 

noncomputable def Ns222p1766 := nat_lit 208155235951156346568609034069096560651996512729591794462198842630625 

noncomputable def Ns222p1767 := nat_lit 44972223681587442705866728954754224765586121337268815902000390625 

noncomputable def Ns222p1768 := nat_lit 545095662938496432772452257381707104391322774857241978841917539590625 

noncomputable def Ns222p1769 := BSN.sin_dyadic_bound_f 120675205 134217728 3 2 134217728 67108864 Ns222p1766 Ns222p124 Ns222p1767 Ns222p1768 Ns222p127 Ns222p1767 105061256 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 120675205) qz363 0 2 Ns222p1766 Ns222p124 Ns222p1767 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 120675205) qz364 0 2 Ns222p1768 Ns222p127 Ns222p1767 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1770 := nat_lit 7103523267405083190651728392081 

noncomputable def Ns222p1771 := BSN.sin_dyadic_bound_f 51625997 134217728 2 1 134217728 67108864 Ns222p1770 Ns222p117 Ns222p1770 Ns222p1770 Ns222p118 Ns222p1770 50362363 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 51625997) qz363 0 1 Ns222p1770 Ns222p117 Ns222p1770 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 51625997) qz364 0 1 Ns222p1770 Ns222p118 Ns222p1770 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1772 := nat_lit 78154817012093970139904219559015024976036800737750301218813006381056 

noncomputable def Ns222p1773 := nat_lit 20539297089305292945910001599219339227751616521267555103869566976 

noncomputable def Ns222p1774 := nat_lit 234423372442103299833820838673846636249654898980208368546231280009216 

noncomputable def Ns222p1775 := BSN.cos_dyadic_bound_f 109414076 134217728 3 2 134217728 67108864 Ns222p1772 Ns222p105 Ns222p1773 Ns222p1774 Ns222p108 Ns222p1773 92036317 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 109414076) qz361 0 2 Ns222p1772 Ns222p105 Ns222p1773 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 109414076) qz362 0 2 Ns222p1774 Ns222p108 Ns222p1773 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1776 := nat_lit 114101661300020892913480259017445842320826780622065337777859367706880 

noncomputable def Ns222p1777 := nat_lit 13515695698103682976433722299972538386341506166338676191188132096 

noncomputable def Ns222p1778 := nat_lit 298815801802257789762867404733396298159063682047806574418655467970816 

noncomputable def Ns222p1779 := BSN.sin_dyadic_bound_f 103837638 134217728 3 2 134217728 67108864 Ns222p1776 Ns222p124 Ns222p1777 Ns222p1778 Ns222p127 Ns222p1777 93784833 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 103837638) qz363 0 2 Ns222p1776 Ns222p124 Ns222p1777 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 103837638) qz364 0 2 Ns222p1778 Ns222p127 Ns222p1777 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1780 := Ns222p1731 61428 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 110 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 92036317 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 35 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 93784833 134217728) qz221 rfl rfl (Ns222p1765 RS223to240.d9 RS223to240.d11 RS223to240.d13 RS223to240.d17 (Ns222p1769 rfl rfl) (Ns222p1771 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns222p1764 rfl) RS223to240.d19 RS223to240.d21 RS223to240.d23 RS223to240.d25 RS223to240.d17 (Ns222p1775 rfl rfl) (Ns222p1779 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns222p1781 := nat_lit 829313178257615282656674593671183570315457741122307596955409221780065 

noncomputable def Ns222p1782 := nat_lit 712930968399498223064380441769646203793396414577357865527708844641 

noncomputable def Ns222p1783 := nat_lit 2170856435773488457453948272233091828401009537315775603100931671294561 

noncomputable def Ns222p1784 := BSN.sin_dyadic_bound_f 170463317 134217728 3 2 134217728 67108864 Ns222p1781 Ns222p124 Ns222p1782 Ns222p1783 Ns222p127 Ns222p1782 128193481 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 170463317) qz363 0 2 Ns222p1781 Ns222p124 Ns222p1782 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 170463317) qz364 0 2 Ns222p1783 Ns222p127 Ns222p1782 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1785 := nat_lit 321074722517858138902459159682838912572045989474677375728161339326720 

noncomputable def Ns222p1786 := nat_lit 106974472416253762585667755045021524320382417752454442448120299776 

noncomputable def Ns222p1787 := nat_lit 840736790781906905319397194232600450458839829471603438762173217751296 

noncomputable def Ns222p1788 := BSN.sin_dyadic_bound_f 134480718 134217728 3 2 134217728 67108864 Ns222p1785 Ns222p124 Ns222p1786 Ns222p1787 Ns222p127 Ns222p1786 113082200 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 134480718) qz363 0 2 Ns222p1785 Ns222p124 Ns222p1786 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 134480718) qz364 0 2 Ns222p1787 Ns222p127 Ns222p1786 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1789 := Ns222p1729 82406 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 25 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 128193481 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 77 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 113082200 134217728) qz221 rfl rfl (Ns222p1780 rfl rfl) (Ns222p1764 rfl) RS223to240.d27 RS223to240.d29 RS223to240.d31 RS223to240.d33 RS223to240.d17 (Ns222p1784 rfl rfl) (Ns222p1788 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p1790 := nat_lit 87926837640015480436988785649267617386217823277063325489666923754561 

noncomputable def Ns222p1791 := nat_lit 25994917930404247845834799079950672240792341967118698439418377281 

noncomputable def Ns222p1792 := nat_lit 263728523084185632815274687349642950814171885147255739072121934509121 

noncomputable def Ns222p1793 := BSN.cos_dyadic_bound_f 112683689 134217728 3 2 134217728 67108864 Ns222p1790 Ns222p105 Ns222p1791 Ns222p1792 Ns222p108 Ns222p1791 89629420 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 112683689) qz361 0 2 Ns222p1790 Ns222p105 Ns222p1791 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 112683689) qz362 0 2 Ns222p1792 Ns222p108 Ns222p1791 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1794 := nat_lit 676935590909079029996679210000 

noncomputable def Ns222p1795 := BSN.cos_dyadic_bound_f 28683810 134217728 2 1 134217728 67108864 Ns222p1794 Ns222p246 Ns222p1794 Ns222p1794 Ns222p247 Ns222p1794 131164352 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 28683810) qz361 0 1 Ns222p1794 Ns222p246 Ns222p1794 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 28683810) qz362 0 1 Ns222p1794 Ns222p247 Ns222p1794 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1796 := Ns222p1727 100736 BSN.abs_quadSignNeg qz743 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 89629420 134217728) BSN.abs_quadSignNeg qz408 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 131164352 134217728) qz221 rfl rfl (Ns222p1789 rfl) (Ns222p1764 rfl) RS223to240.d35 RS223to240.d37 RS223to240.d46 RS223to240.d48 RS223to240.d17 (Ns222p1793 rfl rfl) (Ns222p1795 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p1797 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz218) qz218 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz218) qz218 9) 3238237 134217728 100736 134217728 3238237 134217728 100736 134217728 869257625731072 3238237 67108864 787 524288 (Ns222p1796 rfl) 

noncomputable def Ns222p1798 := @Enclosure.Real.IsNear.mulLit_tf qz766 (Zeta.RiemannSiegel.correction qz220) 5540863 16777216 1 16777216 84326310586647 140737488355328 17567947769823 397198575534080000 467240534256060656361 2361183241434822606848 

noncomputable abbrev qz769 := (@HPow.hPow Real Real Real qz6 qz219 qz8)

noncomputable def Ns222p1799 := @Enclosure.Real.IsNear.mulLit_tf qz48 qz769 1 1 0 1 5540863 16777216 1 16777216 5540863 16777216 1 16777216 

noncomputable def Ns222p1800 := @Enclosure.Real.IsNear.sqrt_image qz219 1410229950957 16777216000 528141 16777216000 76908588 76908617 8388608 (@Enclosure.Real.IsNear.of_eq qz219 (@HMul.hMul Real Real Real qz4 qz218 qz2) Bool.false 1410229950957 16777216000 528141 16777216000 (BSN.t_div_two_pi_mk qz218 528141 1000 qz221) (@Enclosure.Real.IsNear.mulLit_ff qz218 qz2 528141 1000 0 1 2670177 16777216 1 16777216 1410229950957 16777216000 528141 16777216000 (Enclosure.Real.IsNear.const Bool.false 528141 1000) RS223to240.d40 rfl)) 

noncomputable abbrev qz916 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 528141 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz770 := qz916

noncomputable abbrev qz566 := qz770

noncomputable abbrev qz224 := qz566

noncomputable def Ns222p1801 := @Enclosure.Real.IsNear.sqrt_image qz224 153817205 16777216 29 16777216 25399921 25399926 8388608 (@Enclosure.Real.IsNear.recentre' qz224 Bool.false 153817205 16777216 29 16777216 153817205 16777216 29 16777216 (Ns222p1800 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns222p1802 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz224) 50799847 16777216 5 16777216 2770431 2770432 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz224) Bool.false 50799847 16777216 5 16777216 50799847 16777216 5 16777216 (Ns222p1801 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns222p1803 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz224)) Bool.false 5540863 16777216 1 16777216 5540863 16777216 1 16777216 (Ns222p1802 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz225 := (@HMul.hMul Real Real Real qz343 qz341 qz560)

noncomputable abbrev qz771 := (@HMul.hMul Real Real Real qz848 qz915 qz915)

noncomputable abbrev qz567 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz771 qz765) qz639)

noncomputable abbrev qz226 := (Real.cos (@HMul.hMul Real Real Real qz343 qz341 qz567))

noncomputable def Ns222p1804 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz220) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz225)) qz226) Bool.false 84326310586647 

noncomputable def Ns222p1805 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz225)) qz226 34133007 16777216 787 

noncomputable def Ns222p1806 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz225)) Bool.false 34133007 16777216 787 16777216 34133007 16777216 787 

noncomputable def Ns222p1807 := @Enclosure.Real.IsNear.recentre' (Real.cos qz225) Bool.false 4123208 8388608 68567152 6060769280000 515401 1048576 4285447 378798080000 

noncomputable def Ns222p1808 := @Enclosure.Real.IsNear.cos_image qz225 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4433197) qz676) Bool.false 4433197 4194304 23 2097152 Bool.false 4123208 8388608 1 

noncomputable def Ns222p1809 := nat_lit 156519237377304071118290511 

noncomputable def Ns222p1810 := nat_lit 14411518807585587200000000000000 

noncomputable def Ns222p1811 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz220 884279719003555 140737488355328 1 500000000000000 2822261 16777216 29 16777216 2495668164034692137855 2361183241434822606848 Ns222p1809 

noncomputable def Ns222p1812 := @Enclosure.Real.IsNear.subLit_ff_p qz224 qz46 153817205 16777216 29 16777216 9 1 0 1 2822261 2822261 16777216 29 

noncomputable def Ns222p1813 := @Ns222p1812 16777216 (@Enclosure.Real.IsNear.recentre' qz224 Bool.false 153817205 16777216 29 16777216 153817205 16777216 29 16777216 (Ns222p1800 rfl rfl rfl rfl rfl rfl) rfl) qz411 

noncomputable def Ns222p1814 := @Enclosure.Real.IsNear.recentre' qz225 Bool.false 2495668164034692137855 2361183241434822606848 Ns222p1809 Ns222p1810 4433197 4194304 23 2097152 (@Ns222p1811 Ns222p1810 RS223to240.d39 (Ns222p1813 rfl rfl) rfl) 

noncomputable def Ns222p1815 := nat_lit 200973840702618006346482814837109778848291732152181271841 

noncomputable def Ns222p1816 := nat_lit 149188808465928214649914026231567716973238759535619361 

noncomputable def Ns222p1817 := nat_lit 602623144490922162610148616458866201110928718937472576801 

noncomputable def Ns222p1818 := BSN.cos_dyadic_bound_f 4433197 4194304 3 2 8388608 2890000 Ns222p1815 Ns222p1277 Ns222p1816 Ns222p1817 Ns222p1280 Ns222p1816 4123208 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 4433197) (BSN.cosEvenQ 4194304) 0 2 Ns222p1815 Ns222p1277 Ns222p1816 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 4433197) (BSN.cosOddQ 4194304) 0 2 Ns222p1817 Ns222p1280 Ns222p1816 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1819 := @Enclosure.Real.IsNear.inv_image (Real.cos qz225) 515401 1048576 4285447 378798080000 17066110 17066897 8388608 (Ns222p1807 (@Ns222p1808 2890000 (Ns222p1814 rfl) (Enclosure.sfrac_false_div 4433197 4194304) (Ns222p1818 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns222p1820 := @Enclosure.Real.IsNear.recentre' qz226 Bool.false 2470521 8388608 

noncomputable abbrev qz227 := (@HMul.hMul Real Real Real qz343 qz341 qz567)

noncomputable def Ns222p1821 := @Enclosure.Real.IsNear.cos_image qz227 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 10669089)) qz370) Bool.true 10669089 8388608 

noncomputable def Ns222p1822 := nat_lit 50383350256051189443112220405 

noncomputable def Ns222p1823 := nat_lit 17547189357403869341377279519371213 

noncomputable def Ns222p1824 := @Enclosure.Real.IsNear.recentre' qz227 Bool.true Ns222p1822 Ns222p168 Ns222p1823 

noncomputable abbrev qz228 := qz567

noncomputable def Ns222p1825 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz228 884279719003555 140737488355328 1 500000000000000 56976711297671 

noncomputable abbrev qz568 := (@HSub.hSub Real Real Real qz634 qz771 qz765)

noncomputable abbrev qz229 := qz568

noncomputable def Ns222p1826 := @Enclosure.Real.IsNear.subLit_tf qz229 qz25 39384525253255 281474976710656 650231243 281474976710656 1 16 

noncomputable abbrev qz569 := qz771

noncomputable abbrev qz230 := qz569

noncomputable def Ns222p1827 := @Enclosure.Real.IsNear.subLit_ff_n qz230 qz220 7965157152121 281474976710656 163691979 281474976710656 2822261 16777216 29 16777216 

noncomputable def Ns222p1828 := @Enclosure.Real.IsNear.mulLit_ff qz220 qz220 2822261 16777216 29 16777216 2822261 16777216 29 16777216 7965157152121 281474976710656 

noncomputable def Ns222p1829 := nat_lit 107957828747926137272507383944829080011366738286148678242561 

noncomputable def Ns222p1830 := nat_lit 167887632060092084878259880325608315358728735419384910081 

noncomputable def Ns222p1831 := nat_lit 323537710979658227647765632073836023403382757387607264907521 

noncomputable def Ns222p1832 := BSN.cos_dyadic_bound_f 10669089 8388608 3 2 8388608 2890000 Ns222p1829 Ns222p642 Ns222p1830 Ns222p1831 Ns222p645 Ns222p1830 2470521 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 10669089) (BSN.cosEvenQ 8388608) 0 2 Ns222p1829 Ns222p642 Ns222p1830 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 10669089) (BSN.cosOddQ 8388608) 0 2 Ns222p1831 Ns222p645 Ns222p1830 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1833 := @Ns222p1820 724827216 48486154240000 2470521 8388608 45301701 3030384640000 (@Ns222p1821 245 16777216 Bool.false 2470521 8388608 1 2890000 (@Ns222p1824 Ns222p532 10669089 8388608 245 16777216 (@Ns222p1825 281474976710656 650231243 281474976710656 Ns222p1822 Ns222p168 Ns222p1823 Ns222p532 RS223to240.d39 (@Ns222p1826 0 1 911627380762736 56976711297671 281474976710656 650231243 281474976710656 (@Ns222p1827 660762687231313838080 39384525253255 281474976710656 650231243 281474976710656 (@Ns222p1828 163691979 281474976710656 (Ns222p1813 rfl rfl) (Ns222p1813 rfl rfl) rfl) (Ns222p1813 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 10669089 8388608) (BSN.cos_neg_of_bound 10669089 8388608 Bool.false 2470521 8388608 1 2890000 (Ns222p1832 rfl rfl)) rfl rfl) 

noncomputable def Ns222p1834 := @Ns222p1798 6245094438358036126983 Ns222p1723 (Ns222p1799 qz61 (@Enclosure.Real.IsNear.of_eq qz769 (@Inv.inv Real Real.instInv (Real.sqrt qz224)) Bool.false 5540863 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz219 (BSN.t_div_two_pi_nonneg qz218 528141 1000 qz221)) Ns222p1803) rfl) (@Ns222p1804 140737488355328 17567947769823 397198575534080000 (BSN.correction_mk qz220 (BSN.cos_two_pi_p_ne_zero_mk qz218 528141 1000 9 qz221 rfl rfl (@BSN.floor_sqrt_eq_dec qz218 528141 1000 9 qz221 rfl rfl rfl))) (@Ns222p1805 16777216 2470521 8388608 45301701 3030384640000 84326310586647 140737488355328 17567947769823 397198575534080000 (@Ns222p1806 16777216 (Ns222p1819 rfl rfl rfl rfl rfl) rfl) (Ns222p1833 rfl) rfl)) 

noncomputable def Ns222p1835 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz218) (hardyZApproximantRS₀ qz218) Bool.false 581175869775883725545 2361183241434822606848 646440225718375362206983 Ns222p1723 (@Eq.refl Real (hardyZApproximantRS₀ qz218)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz218) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz218) qz218 9) (@HMul.hMul Real Real Real qz4 qz766 (Zeta.RiemannSiegel.correction qz220))) Bool.false 581175869775883725545 2361183241434822606848 646440225718375362206983 Ns222p1723 (BSN.hardyZApproximantRS₀_eq qz218 9 (@BSN.floor_sqrt_eq_dec qz218 528141 1000 9 qz221 rfl rfl rfl)) (@Ns222p1725 581175869775883725545 2361183241434822606848 646440225718375362206983 Ns222p1723 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz218) qz218 9) (@HAdd.hAdd Real Real Real qz358 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz218) qz218 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz218) qz218 9)) Bool.false 3238237 67108864 787 524288 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz218) qz218 9) (Ns222p1797 (Ns222p1796 rfl) rfl rfl)) (Ns222p1834 rfl) rfl rfl)) 

theorem RS223to240.d62 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz218) Bool.false 581175869775883725545 2361183241434822606848 646440225718375362206983 Ns222p1723 := Ns222p1835 

noncomputable def Ns222p1836 := nat_lit 42648872298416483336192000 

noncomputable def Ns222p1837 := nat_lit 13503115458744099660292423680 

noncomputable abbrev qz917 := (Enclosure.sfrac Bool.false 528761 1000)

noncomputable abbrev qz772 := qz917

noncomputable abbrev qz570 := qz772

noncomputable abbrev qz231 := qz570

noncomputable abbrev qz918 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 528761 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz773 := qz918

noncomputable abbrev qz571 := qz773

noncomputable abbrev qz232 := qz571

noncomputable abbrev qz919 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 528761 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz774 := qz919

noncomputable abbrev qz572 := qz774

noncomputable abbrev qz233 := qz572

noncomputable abbrev qz775 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz232 qz8))

noncomputable def Ns222p1838 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz231) qz231 9) (@HMul.hMul Real Real Real qz4 qz775 (Zeta.RiemannSiegel.correction qz233)) 14714217 16777216 25213 16777216 230572571568106766733 1180591620717411303424 687715108353106032339 Ns222p1836 Ns222p1837 

noncomputable def Ns222p1839 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz231) qz231 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 528761 1000 122 162 134217728 67108864 2251799813685248 Bool.false 121753674803 1837 

noncomputable def Ns222p1840 := Ns222p1839 279097919 47 47453128 8 294906479 47 44739240 8 Bool.false 19535300 82500 Bool.true 101316821 Bool.true 27118249 7074237752028440 1 Bool.false 97758987 Bool.true Bool.false 131487458 Bool.true Bool.true 58856868 

noncomputable def Ns222p1841 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz231) qz231 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 528761 1000 25 77 134217728 67108864 2251799813685248 Bool.false 121753674803 1837 

noncomputable def Ns222p1842 := Ns222p1841 240485871 47 54794152 8 261175631 47 50729528 8 Bool.false 103436953 61497 Bool.true 135156979 Bool.true 112002031 7074237752028440 1 Bool.false 113445033 Bool.true Bool.false 99448290 Bool.true Bool.false 19535300 

noncomputable def Ns222p1843 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz231) qz231 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 528761 1000 110 35 134217728 67108864 2251799813685248 Bool.false 121753674803 1837 

noncomputable def Ns222p1844 := Ns222p1843 186065264 47 67108856 8 216015088 47 60023992 8 Bool.false 64682878 36197 Bool.false 178461190 Bool.false 154315862 7074237752028440 1 Bool.false 32054704 Bool.true Bool.false 122494994 Bool.false Bool.false 103436953 

noncomputable def Ns222p1845 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz231) qz231 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 528761 1000 344 207 134217728 67108864 2251799813685248 Bool.false 121753674803 1837 

noncomputable def Ns222p1846 := Ns222p1845 93032624 47 94906264 8 147453232 47 77490640 16 Bool.true 94971568 1887 Bool.false 36573842 Bool.false 144612571 7074237752028440 1 Bool.false 129265367 Bool.false Bool.false 118212522 Bool.false Bool.false 64682878 

noncomputable def Ns222p1847 := nat_lit 200896395345852452961902194849317338758151665630917218363 

noncomputable def Ns222p1848 := nat_lit 221462373026867926090088385189190489892418094104576000 

noncomputable def Ns222p1849 := nat_lit 19839891713591104203346630304480000 

noncomputable def Ns222p1850 := nat_lit 62943392159373822235604730277938895680 

noncomputable abbrev qz776 := (@Eq.refl Real qz917)

noncomputable abbrev qz573 := qz776

noncomputable abbrev qz234 := qz573

noncomputable def Ns222p1851 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz231 528761 1000 1118353780484 16000000 1057522 4000 2000 Ns222p1849 Ns222p1850 qz234 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns222p1852 := nat_lit 64286846510672784947808702351781548402608533001893509876160 

noncomputable abbrev qz574 := (Enclosure.sfrac Bool.false 528761 2000)

noncomputable abbrev qz777 := (Real.log (Enclosure.sfrac Bool.false 1118353780484 16000000))

noncomputable abbrev qz235 := (@HSub.hSub Real Real Real qz347 (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 528761 4000) qz777) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1057522)))))) qz574)

noncomputable abbrev qz575 := (@HSub.hSub Real Real Real qz11 qz235 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 528761 2000) (Real.log Real.pi)))

noncomputable def Ns222p1853 := @Enclosure.Real.IsNear.addLit_ft_p qz575 (Enclosure.sfrac Bool.true Ns222p1849 Ns222p1850) 1021344205371542213987 1125899906842624000 8098721633598759493 591872000000000000000000 Ns222p1849 Ns222p1850 0 1 Ns222p1852 

noncomputable def Ns222p1854 := nat_lit 68541249375466895908712480768000 

noncomputable abbrev qz576 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 528761 2000) (Real.log Real.pi))

noncomputable def Ns222p1855 := @Enclosure.Real.IsNear.subLit_ff_p qz235 qz576 1362091348042319009123 1125899906842624000 1677378736283841 289000000000000000000 20310112397121 67108864000 528761 67108864000 Ns222p1854 1021344205371542213987 1125899906842624000 

noncomputable abbrev qz236 := (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 528761 4000) qz777) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1057522))))))

noncomputable def Ns222p1856 := @Enclosure.Real.IsNear.subLit_ff_p qz236 qz574 331951465672665072711 225179981368524800 1677378736283841 289000000000000000000 528761 2000 0 1 544836539216927603649200 1362091348042319009123 1125899906842624000 1677378736283841 289000000000000000000 

noncomputable def Ns222p1857 := nat_lit 747488248554252207891523598788067328 

noncomputable def Ns222p1858 := nat_lit 26970602134922817657896960 

noncomputable def Ns222p1859 := nat_lit 330727731396944644400228006953768894357827605303040 

noncomputable def Ns222p1860 := nat_lit 114383688180587623731719674694414284879746828288 

noncomputable def Ns222p1861 := nat_lit 71119690711161666289181047082617404625060608 

noncomputable def Ns222p1862 := BSN.log_dyadic_bound 69777780484 2166929780484 3 2 Ns222p1859 67108864 23120000 Ns222p1860 Ns222p1861 4323469 2236707560968 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 69777780484) (BSN.artanhQ 2166929780484) 0 2 Ns222p1860 Ns222p1859 Ns222p1861 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns222p1863 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 528761 4000) qz777 528761 4000 0 1 3139791327403255 281474976710656 781250289 18062500000000000 332039840413814503411 225179981368524800 413094684061929 72250000000000000000 (Enclosure.Real.IsNear.const Bool.false 528761 4000) (BSN.isNear_log_sfrac 1118353780484 16000000 3139791327403255 281474976710656 781250289 18062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1118353780484) qz354)) Bool.false Ns222p1858 Ns222p89 1000000369920000 23120000000000000000000 3139791327403255 281474976710656 781250289 18062500000000000 (BSN.log_rat_reduce_isNear 1118353780484 16000000 16 2236707560968 2097152000000 4323469 67108864 24973259072661432 36028797018963968 23120000 1000000000000000 rfl rfl rfl rfl (Ns222p1862 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns222p1864 := BSN.arctan_dyadic_bound_f 1000 1057522 1 0 8388608 2890000 0 1 1 0 1 1 7932 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1057522) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1057522) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz577 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1057522)))

noncomputable def Ns222p1865 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz577 884279719003555 562949953421312 1 2000000000000000 7932 8388608 1 2890000 7413410606040435654656 883747411494307 562949953421312 200000000289 578000000000000000 qz16 (Ns222p1864 rfl) rfl rfl 

noncomputable def Ns222p1866 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 528761 4000) qz777) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz577)) 332039840413814503411 225179981368524800 413094684061929 72250000000000000000 883747411494307 2251799813685248 200000000289 2312000000000000000 Ns222p1857 331951465672665072711 225179981368524800 1677378736283841 289000000000000000000 (Ns222p1863 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz577) 1 4 0 1 883747411494307 562949953421312 200000000289 578000000000000000 883747411494307 2251799813685248 200000000289 2312000000000000000 qz357 Ns222p1865 rfl) 

noncomputable def Ns222p1867 := @Ns222p1853 Ns222p1847 Ns222p1848 8098721633598759493 591872000000000000000000 (@Ns222p1855 8098721633598759493 591872000000000000000000 (Ns222p1856 (Ns222p1866 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 528761 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz574 (Real.log Real.pi) 528761 2000 0 1 38410761 33554432 1 33554432 20310112397121 67108864000 528761 67108864000 (Enclosure.Real.IsNear.const Bool.false 528761 2000) RS223to240.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns222p1849 Ns222p1850) 

noncomputable def Ns222p1868 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz231) Bool.false Ns222p1847 Ns222p1848 8098721633598759493 591872000000000000000000 7609604675 8388608 115 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz231) (@HAdd.hAdd Real Real Real qz358 qz575 (Enclosure.sfrac Bool.true Ns222p1849 Ns222p1850)) Bool.false Ns222p1847 Ns222p1848 8098721633598759493 591872000000000000000000 Ns222p1851 (Ns222p1867 rfl rfl)) 

noncomputable def Ns222p1869 := nat_lit 2243451978085291963747492829785144967214621543415858738983502206821415515168291902514785 

noncomputable def Ns222p1870 := nat_lit 283244526539787680832364284397580574777493736689216572973116199078824229219801818721 

noncomputable def Ns222p1871 := nat_lit 5875248975275652629760181202500640736060083338134514156219596924971865395736313398879841 

noncomputable def Ns222p1872 := BSN.sin_dyadic_bound_f 27009726763 34359738368 3 2 16777216 5785645 Ns222p1869 Ns222p158 Ns222p1870 Ns222p1871 Ns222p161 Ns222p1870 11871446 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 27009726763) qz371 0 2 Ns222p1869 Ns222p158 Ns222p1870 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 27009726763) qz372 0 2 Ns222p1871 Ns222p161 Ns222p1870 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1873 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz231) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7609604675) qz370) Bool.false 7609604675 8388608 115 8388608 Bool.true 11871446 16777216 1 2890000 (Ns222p1868 rfl) (Enclosure.sfrac_false_div 7609604675 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7609604675) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 950320276453460352696320) qz640) 226375608064910080 72057594037927936 Bool.false 11871446 16777216 144 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q1 7609604675 8388608 226375608064910080 72057594037927936 144 950320276453460352696320 Ns222p156 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 11871446 16777216 950320276453460352696320 Ns222p156 27009726763 34359738368 5785645 5780000 (Ns222p1872 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p1874 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz231) Bool.false Ns222p1847 Ns222p1848 8098721633598759493 591872000000000000000000 121753674803 134217728 1837 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz231) (@HAdd.hAdd Real Real Real qz358 qz575 (Enclosure.sfrac Bool.true Ns222p1849 Ns222p1850)) Bool.false Ns222p1847 Ns222p1848 8098721633598759493 591872000000000000000000 Ns222p1851 (Ns222p1867 rfl rfl)) 

noncomputable def Ns222p1875 := Ns222p1846 36197 BSN.abs_quadSignPos (BSN.cos_quad_nat0 344 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 129265367 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 207 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 118212522 134217728) qz234 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 1) Bool.true 5935723 8388608 21296163 1515192320000 94971568 134217728 1887 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz231)) Bool.true 5935723 8388608 21296163 1515192320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz231) qz231) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz231)) Bool.true 11871446 16777216 340738608 24243077120000 5935723 8388608 21296163 1515192320000 (Ns222p1873 rfl rfl) rfl)) rfl) (Ns222p1874 rfl) RS223to240.d7 

noncomputable def Ns222p1876 := nat_lit 1789296603656828480780738849296 

noncomputable def Ns222p1877 := BSN.cos_dyadic_bound_f 36573842 134217728 2 1 134217728 67108864 Ns222p1876 Ns222p246 Ns222p1876 Ns222p1876 Ns222p247 Ns222p1876 129265367 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 36573842) qz361 0 1 Ns222p1876 Ns222p246 Ns222p1876 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 36573842) qz362 0 1 Ns222p1876 Ns222p247 Ns222p1876 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1878 := nat_lit 429377232005734867350308276484417809974525562280977214524364565465825 

noncomputable def Ns222p1879 := nat_lit 191270669687915935128711756000875495347174136985797390850454145761 

noncomputable def Ns222p1880 := nat_lit 1124249740835525169641551381282807132464623904990296651788149317126881 

noncomputable def Ns222p1881 := BSN.sin_dyadic_bound_f 144612571 134217728 3 2 134217728 67108864 Ns222p1878 Ns222p124 Ns222p1879 Ns222p1880 Ns222p127 Ns222p1879 118212522 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 144612571) qz363 0 2 Ns222p1878 Ns222p124 Ns222p1879 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 144612571) qz364 0 2 Ns222p1880 Ns222p127 Ns222p1879 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1882 := nat_lit 2135931813055042098993226916992775894867360448934525912860697507894201929165653135003586824636951104000000 

noncomputable def Ns222p1883 := nat_lit 1043579201477158132940884727287863729023086436036090476021286738869816754354174204076961000000000000 

noncomputable def Ns222p1884 := nat_lit 12941938800857390413405566151549795813121836096226655402606340782962528606798277451962582154137895897600000 

noncomputable def Ns222p1885 := BSN.cos_dyadic_bound_f 178461190 134217728 4 3 134217728 67108864 Ns222p1882 Ns222p227 Ns222p1883 Ns222p1884 Ns222p230 Ns222p1883 32054704 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 178461190) qz361 0 3 Ns222p1882 Ns222p227 Ns222p1883 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 178461190) qz362 0 3 Ns222p1884 Ns222p230 Ns222p1883 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1886 := nat_lit 556819560273335670635242141791742031482143949710636040134839364378880 

noncomputable def Ns222p1887 := nat_lit 321576684329148081737912828429407744992845373114504001185262756096 

noncomputable def Ns222p1888 := nat_lit 1457816295607917659531391845827581517532769547209480431970279338434816 

noncomputable def Ns222p1889 := BSN.sin_dyadic_bound_f 154315862 134217728 3 2 134217728 67108864 Ns222p1886 Ns222p124 Ns222p1887 Ns222p1888 Ns222p127 Ns222p1887 122494994 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 154315862) qz363 0 2 Ns222p1886 Ns222p124 Ns222p1887 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 154315862) qz364 0 2 Ns222p1888 Ns222p127 Ns222p1887 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1890 := Ns222p1844 61497 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 110 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 32054704 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 35 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 122494994 134217728) qz234 rfl rfl (Ns222p1875 RS223to240.d9 RS223to240.d11 RS223to240.d13 RS223to240.d17 (Ns222p1877 rfl rfl) (Ns222p1881 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns222p1874 rfl) RS223to240.d19 RS223to240.d21 RS223to240.d23 RS223to240.d25 RS223to240.d17 (Ns222p1885 rfl rfl) (Ns222p1889 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns222p1891 := nat_lit 327584146344616700741048106149528543428690453154604741654800998254625 

noncomputable def Ns222p1892 := nat_lit 111354509082315576738372943562217827229873518033514138021147363361 

noncomputable def Ns222p1893 := nat_lit 857778190268815229102311483721093070592959963042386729062920756840481 

noncomputable def Ns222p1894 := BSN.sin_dyadic_bound_f 135156979 134217728 3 2 134217728 67108864 Ns222p1891 Ns222p124 Ns222p1892 Ns222p1893 Ns222p127 Ns222p1892 113445033 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 135156979) qz363 0 2 Ns222p1891 Ns222p124 Ns222p1892 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 135156979) qz364 0 2 Ns222p1893 Ns222p127 Ns222p1892 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1895 := nat_lit 154452359234773590011785813622681482980722923142877765252267176590465 

noncomputable def Ns222p1896 := nat_lit 24763223906081482452275918981524514975857166304408553822444813441 

noncomputable def Ns222p1897 := nat_lit 404477990871416222868802017523909987163361029962091771335463408991361 

noncomputable def Ns222p1898 := BSN.sin_dyadic_bound_f 112002031 134217728 3 2 134217728 67108864 Ns222p1895 Ns222p124 Ns222p1896 Ns222p1897 Ns222p127 Ns222p1896 99448290 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 112002031) qz363 0 2 Ns222p1895 Ns222p124 Ns222p1896 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 112002031) qz364 0 2 Ns222p1897 Ns222p127 Ns222p1896 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1899 := Ns222p1842 82500 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 25 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 113445033 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 77 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 99448290 134217728) qz234 rfl rfl (Ns222p1890 rfl rfl) (Ns222p1874 rfl) RS223to240.d27 RS223to240.d29 RS223to240.d31 RS223to240.d33 RS223to240.d17 (Ns222p1894 rfl rfl) (Ns222p1898 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p1900 := nat_lit 57459118907700820174201264130415623374927446690931410725198225094241 

noncomputable def Ns222p1901 := nat_lit 11103309261003737297273085521396789134289767087903971811930289761 

noncomputable def Ns222p1902 := nat_lit 172355150104580453048009246220204076546513760538618424231970814703201 

noncomputable def Ns222p1903 := BSN.cos_dyadic_bound_f 101316821 134217728 3 2 134217728 67108864 Ns222p1900 Ns222p105 Ns222p1901 Ns222p1902 Ns222p108 Ns222p1901 97758987 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 101316821) qz361 0 2 Ns222p1900 Ns222p105 Ns222p1901 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 101316821) qz362 0 2 Ns222p1902 Ns222p108 Ns222p1901 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1904 := nat_lit 540812319917608510537133652001 

noncomputable def Ns222p1905 := BSN.cos_dyadic_bound_f 27118249 134217728 2 1 134217728 67108864 Ns222p1904 Ns222p246 Ns222p1904 Ns222p1904 Ns222p247 Ns222p1904 131487458 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 27118249) qz361 0 1 Ns222p1904 Ns222p246 Ns222p1904 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 27118249) qz362 0 1 Ns222p1904 Ns222p247 Ns222p1904 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1906 := Ns222p1840 100852 BSN.abs_quadSignNeg qz743 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 97758987 134217728) BSN.abs_quadSignNeg qz408 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 131487458 134217728) qz234 rfl rfl (Ns222p1899 rfl) (Ns222p1874 rfl) RS223to240.d35 RS223to240.d37 RS223to240.d46 RS223to240.d48 RS223to240.d17 (Ns222p1903 rfl rfl) (Ns222p1905 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p1907 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 9) 58856868 134217728 100852 134217728 58856868 134217728 100852 134217728 15799270200311808 14714217 16777216 25213 16777216 (Ns222p1906 rfl) 

noncomputable def Ns222p1908 := @Enclosure.Real.IsNear.mulLit_tf qz775 (Zeta.RiemannSiegel.correction qz233) 2769619 8388608 1 8388608 83250646232607 140737488355328 309026003006709 6355177208545280000 230572571568106766733 1180591620717411303424 

noncomputable abbrev qz778 := (@HPow.hPow Real Real Real qz6 qz232 qz8)

noncomputable def Ns222p1909 := @Enclosure.Real.IsNear.mulLit_tf qz48 qz778 1 1 0 1 2769619 8388608 1 8388608 2769619 8388608 1 8388608 

noncomputable def Ns222p1910 := @Enclosure.Real.IsNear.sqrt_image qz232 1411885460697 16777216000 528761 16777216000 76953717 76953747 8388608 (@Enclosure.Real.IsNear.of_eq qz232 (@HMul.hMul Real Real Real qz4 qz231 qz2) Bool.false 1411885460697 16777216000 528761 16777216000 (BSN.t_div_two_pi_mk qz231 528761 1000 qz234) (@Enclosure.Real.IsNear.mulLit_ff qz231 qz2 528761 1000 0 1 2670177 16777216 1 16777216 1411885460697 16777216000 528761 16777216000 (Enclosure.Real.IsNear.const Bool.false 528761 1000) RS223to240.d40 rfl)) 

noncomputable abbrev qz920 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 528761 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz779 := qz920

noncomputable abbrev qz578 := qz779

noncomputable abbrev qz237 := qz578

noncomputable def Ns222p1911 := @Enclosure.Real.IsNear.sqrt_image qz237 19238433 2097152 15 8388608 25407372 25407378 8388608 (@Enclosure.Real.IsNear.recentre' qz237 Bool.false 153907464 16777216 30 16777216 19238433 2097152 15 8388608 (Ns222p1910 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns222p1912 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz237) 25407375 8388608 3 8388608 2769618 2769620 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz237) Bool.false 50814750 16777216 6 16777216 25407375 8388608 3 8388608 (Ns222p1911 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns222p1913 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz237)) Bool.false 5539238 16777216 2 16777216 2769619 8388608 1 8388608 (Ns222p1912 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz238 := (@HMul.hMul Real Real Real qz343 qz341 qz572)

noncomputable abbrev qz780 := (@HMul.hMul Real Real Real qz848 qz919 qz919)

noncomputable abbrev qz579 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz780 qz774) qz639)

noncomputable abbrev qz239 := (Real.cos (@HMul.hMul Real Real Real qz343 qz341 qz579))

noncomputable def Ns222p1914 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz233) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz238)) qz239) Bool.false 83250646232607 

noncomputable def Ns222p1915 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz238)) qz239 36329103 16777216 919 

noncomputable def Ns222p1916 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz238)) Bool.false 36329103 16777216 919 16777216 36329103 16777216 919 

noncomputable def Ns222p1917 := @Enclosure.Real.IsNear.recentre' (Real.cos qz238) Bool.false 3873960 8388608 282938608 24243077120000 484245 1048576 17683663 1515192320000 

noncomputable def Ns222p1918 := @Enclosure.Real.IsNear.cos_image qz238 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9149951) qz370) Bool.false 9149951 8388608 95 8388608 Bool.false 3873960 8388608 1 

noncomputable def Ns222p1919 := nat_lit 16191645245926794399059217 

noncomputable def Ns222p1920 := nat_lit 1441151880758558720000000000000 

noncomputable def Ns222p1921 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz233 884279719003555 140737488355328 1 500000000000000 364065 2097152 15 8388608 321935295899029251075 295147905179352825856 Ns222p1919 

noncomputable def Ns222p1922 := @Enclosure.Real.IsNear.subLit_ff_p qz237 qz46 19238433 2097152 15 8388608 9 1 0 1 364065 364065 2097152 15 

noncomputable def Ns222p1923 := @Ns222p1922 8388608 (@Enclosure.Real.IsNear.recentre' qz237 Bool.false 153907464 16777216 30 16777216 19238433 2097152 15 8388608 (Ns222p1910 rfl rfl rfl rfl rfl rfl) rfl) qz411 

noncomputable def Ns222p1924 := @Enclosure.Real.IsNear.recentre' qz238 Bool.false 321935295899029251075 295147905179352825856 Ns222p1919 Ns222p1920 9149951 8388608 95 8388608 (@Ns222p1921 Ns222p1920 RS223to240.d39 (Ns222p1923 rfl rfl) rfl) 

noncomputable def Ns222p1925 := nat_lit 58359253195421089611974477560171711795215184161280728698881 

noncomputable def Ns222p1926 := nat_lit 49130382650978639082239323028524798320708304530383769601 

noncomputable def Ns222p1927 := nat_lit 174979498820961311557758954034458085789004135874781418557441 

noncomputable def Ns222p1928 := BSN.cos_dyadic_bound_f 9149951 8388608 3 2 8388608 2890000 Ns222p1925 Ns222p642 Ns222p1926 Ns222p1927 Ns222p645 Ns222p1926 3873960 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 9149951) (BSN.cosEvenQ 8388608) 0 2 Ns222p1925 Ns222p642 Ns222p1926 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 9149951) (BSN.cosOddQ 8388608) 0 2 Ns222p1927 Ns222p645 Ns222p1926 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1929 := @Enclosure.Real.IsNear.inv_image (Real.cos qz238) 484245 1048576 17683663 1515192320000 18164092 18165011 8388608 (Ns222p1917 (@Ns222p1918 2890000 (Ns222p1924 rfl) (Enclosure.sfrac_false_div 9149951 8388608) (Ns222p1928 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns222p1930 := @Enclosure.Real.IsNear.recentre' qz239 Bool.false 2291569 8388608 

noncomputable abbrev qz240 := (@HMul.hMul Real Real Real qz343 qz341 qz579)

noncomputable def Ns222p1931 := @Enclosure.Real.IsNear.cos_image qz240 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 10855721)) qz370) Bool.true 10855721 8388608 

noncomputable def Ns222p1932 := nat_lit 801010834476486567353004445 

noncomputable def Ns222p1933 := nat_lit 4574602458220350672795914890768943 

noncomputable def Ns222p1934 := @Enclosure.Real.IsNear.recentre' qz240 Bool.true Ns222p1932 Ns222p278 Ns222p1933 

noncomputable abbrev qz241 := qz579

noncomputable def Ns222p1935 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz241 884279719003555 140737488355328 1 500000000000000 905834225599 

noncomputable abbrev qz580 := (@HSub.hSub Real Real Real qz634 qz780 qz774)

noncomputable abbrev qz242 := qz580

noncomputable def Ns222p1936 := @Enclosure.Real.IsNear.subLit_tf qz242 qz25 630956318655 4398046511104 169517145 70368744177664 1 16 

noncomputable abbrev qz581 := qz780

noncomputable abbrev qz243 := qz581

noncomputable def Ns222p1937 := @Enclosure.Real.IsNear.subLit_ff_n qz243 qz233 132543324225 4398046511104 43688025 70368744177664 364065 2097152 15 8388608 

noncomputable def Ns222p1938 := @Enclosure.Real.IsNear.mulLit_ff qz233 qz233 364065 2097152 15 8388608 364065 2097152 15 8388608 132543324225 4398046511104 

noncomputable def Ns222p1939 := nat_lit 115725213574289761865488627215405164725847897979570322712641 

noncomputable def Ns222p1940 := nat_lit 192872089226024597637170766891387248528205177602743248961 

noncomputable def Ns222p1941 := nat_lit 346789896544417236401191540112432719680487283583505481640001 

noncomputable def Ns222p1942 := BSN.cos_dyadic_bound_f 10855721 8388608 3 2 8388608 2890000 Ns222p1939 Ns222p642 Ns222p1940 Ns222p1941 Ns222p645 Ns222p1940 2291569 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 10855721) (BSN.cosEvenQ 8388608) 0 2 Ns222p1939 Ns222p642 Ns222p1940 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 10855721) (BSN.cosOddQ 8388608) 0 2 Ns222p1941 Ns222p645 Ns222p1940 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1943 := @Ns222p1930 753727216 48486154240000 2291569 8388608 47107951 3030384640000 (@Ns222p1931 255 16777216 Bool.false 2291569 8388608 1 2890000 (@Ns222p1934 Ns222p281 10855721 8388608 255 16777216 (@Ns222p1935 4398046511104 169517145 70368744177664 Ns222p1932 Ns222p278 Ns222p1933 Ns222p281 RS223to240.d39 (@Ns222p1936 0 1 14493347609584 905834225599 4398046511104 169517145 70368744177664 (@Ns222p1937 1323211305579970560 630956318655 4398046511104 169517145 70368744177664 (@Ns222p1938 43688025 70368744177664 (Ns222p1923 rfl rfl) (Ns222p1923 rfl rfl) rfl) (Ns222p1923 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 10855721 8388608) (BSN.cos_neg_of_bound 10855721 8388608 Bool.false 2291569 8388608 1 2890000 (Ns222p1942 rfl rfl)) rfl rfl) 

noncomputable def Ns222p1944 := @Ns222p1908 687715108353106032339 Ns222p1836 (Ns222p1909 qz61 (@Enclosure.Real.IsNear.of_eq qz778 (@Inv.inv Real Real.instInv (Real.sqrt qz237)) Bool.false 2769619 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz232 (BSN.t_div_two_pi_nonneg qz231 528761 1000 qz234)) Ns222p1913) rfl) (@Ns222p1914 140737488355328 309026003006709 6355177208545280000 (BSN.correction_mk qz233 (BSN.cos_two_pi_p_ne_zero_mk qz231 528761 1000 9 qz234 rfl rfl (@BSN.floor_sqrt_eq_dec qz231 528761 1000 9 qz234 rfl rfl rfl))) (@Ns222p1915 16777216 2291569 8388608 47107951 3030384640000 83250646232607 140737488355328 309026003006709 6355177208545280000 (@Ns222p1916 16777216 (Ns222p1929 rfl rfl rfl rfl rfl) rfl) (Ns222p1943 rfl) rfl)) 

noncomputable def Ns222p1945 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz231) (hardyZApproximantRS₀ qz231) Bool.true 804848400279527882355 1180591620717411303424 64780948291973963888339 Ns222p1836 (@Eq.refl Real (hardyZApproximantRS₀ qz231)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz231) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz231) qz231 9) (@HMul.hMul Real Real Real qz4 qz775 (Zeta.RiemannSiegel.correction qz233))) Bool.true 804848400279527882355 1180591620717411303424 64780948291973963888339 Ns222p1836 (BSN.hardyZApproximantRS₀_eq qz231 9 (@BSN.floor_sqrt_eq_dec qz231 528761 1000 9 qz234 rfl rfl rfl)) (@Ns222p1838 804848400279527882355 1180591620717411303424 64780948291973963888339 Ns222p1836 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz231) qz231 9) (@HAdd.hAdd Real Real Real qz358 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 9)) Bool.true 14714217 16777216 25213 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz231) qz231 9) (Ns222p1907 (Ns222p1906 rfl) rfl rfl)) (Ns222p1944 rfl) rfl rfl)) 

theorem RS223to240.d63 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz231) Bool.true 804848400279527882355 1180591620717411303424 64780948291973963888339 Ns222p1836 := Ns222p1945 

noncomputable def Ns222p1946 := nat_lit 247894559302708824989761536 

noncomputable abbrev qz921 := (Enclosure.sfrac Bool.false 530532 1000)

noncomputable abbrev qz781 := qz921

noncomputable abbrev qz582 := qz781

noncomputable abbrev qz244 := qz582

noncomputable abbrev qz922 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 530532 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz782 := qz922

noncomputable abbrev qz583 := qz782

noncomputable abbrev qz245 := qz583

noncomputable abbrev qz923 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 530532 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz783 := qz923

noncomputable abbrev qz584 := qz783

noncomputable abbrev qz246 := qz584

noncomputable abbrev qz784 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz245 qz8))

noncomputable def Ns222p1947 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz244) qz244 9) (@HMul.hMul Real Real Real qz4 qz784 (Zeta.RiemannSiegel.correction qz246)) 10280231 16777216 101203 67108864 3472433628266668765 18446744073709551616 212149664097595193623 Ns222p978 Ns222p1946 

noncomputable def Ns222p1948 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz244) qz244 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 530532 1000 122 162 134217728 67108864 2251799813685248 Bool.false 122280694237 1844 

noncomputable def Ns222p1949 := Ns222p1948 279097919 47 47453128 8 294906479 47 44739240 8 Bool.false 126631963 82789 Bool.true 68579801 Bool.true 22378190 7074237752028440 1 Bool.false 117074873 Bool.true Bool.false 132356482 Bool.true Bool.false 41120924 

noncomputable def Ns222p1950 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz244) qz244 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 530532 1000 25 77 134217728 67108864 2251799813685248 Bool.false 122280694237 1844 

noncomputable def Ns222p1951 := Ns222p1950 240485871 47 54794152 8 261175631 47 50729528 8 Bool.false 157969073 61715 Bool.true 34038023 Bool.true 47524640 7074237752028440 1 Bool.false 33674338 Bool.true Bool.false 46537764 Bool.true Bool.false 126631963 

noncomputable def Ns222p1952 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz244) qz244 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 530532 1000 111 36 134217728 67108864 2251799813685248 Bool.false 122280694237 1844 

noncomputable def Ns222p1953 := Ns222p1952 186065264 47 67108856 8 216015088 47 60023992 8 Bool.false 47119238 36329 Bool.false 165130327 Bool.false 87943861 7074237752028440 1 Bool.false 126512911 Bool.false Bool.false 106422052 Bool.false Bool.false 157969073 

noncomputable def Ns222p1954 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz244) qz244 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 530532 1000 345 208 134217728 67108864 2251799813685248 Bool.false 122280694237 1844 

noncomputable def Ns222p1955 := Ns222p1954 93032624 47 94906264 8 147453232 47 77490640 16 Bool.false 134217720 1903 Bool.false 188003785 Bool.false 199663617 7074237752028440 1 Bool.false 132281608 Bool.true Bool.false 11152224 Bool.false Bool.false 47119238 

noncomputable def Ns222p1956 := nat_lit 21813158028330603118765183210497959685101707139989 

noncomputable def Ns222p1957 := nat_lit 23942557157689803633471071891221351524990976000 

noncomputable def Ns222p1958 := nat_lit 20174377175215706889882141327360000 

noncomputable def Ns222p1959 := nat_lit 64218942647936413497102155393657733120 

noncomputable abbrev qz924 := (@Eq.refl Real (Enclosure.sfrac Bool.false 530532 1000))

noncomputable abbrev qz785 := qz924

noncomputable abbrev qz585 := qz785

noncomputable abbrev qz247 := qz585

noncomputable def Ns222p1960 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz244 530532 1000 1125857812096 16000000 1061064 4000 2000 Ns222p1958 Ns222p1959 qz247 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns222p1961 := nat_lit 2058547859344331144627608867511799771728868689941899509760 

noncomputable abbrev qz786 := (Real.log (Enclosure.sfrac Bool.false 1125857812096 16000000))

noncomputable abbrev qz248 := (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 530532 4000) qz786) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1061064))))))

noncomputable abbrev qz787 := (Enclosure.sfrac Bool.false 530532 2000)

noncomputable abbrev qz586 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz248 qz787) (@HMul.hMul Real Real Real qz4 qz787 (Real.log Real.pi)))

noncomputable def Ns222p1962 := @Enclosure.Real.IsNear.addLit_ft_p qz586 (Enclosure.sfrac Bool.true Ns222p1958 Ns222p1959) 32055161363409226673 35184372088832000 2031418878527485029 147968000000000000000000 Ns222p1958 Ns222p1959 0 1 Ns222p1961 

noncomputable def Ns222p1963 := nat_lit 537796366108771092285882368000 

noncomputable abbrev qz587 := (@HSub.hSub Real Real Real qz11 qz248 qz787)

noncomputable abbrev qz588 := (@HMul.hMul Real Real Real qz4 qz787 (Real.log Real.pi))

noncomputable def Ns222p1964 := @Enclosure.Real.IsNear.subLit_ff_p qz587 qz588 42739174503053872049 35184372088832000 1682913113331117 289000000000000000000 5094534463713 16777216000 132633 16777216000 Ns222p1963 32055161363409226673 35184372088832000 

noncomputable abbrev qz589 := qz787

noncomputable def Ns222p1965 := @Enclosure.Real.IsNear.subLit_ff_p qz248 qz589 52072392149569981361 35184372088832000 1682913113331117 289000000000000000000 530532 2000 0 1 85478349006107744098000 42739174503053872049 35184372088832000 1682913113331117 289000000000000000000 

noncomputable def Ns222p1966 := nat_lit 938052823524374837078574528645300224 

noncomputable def Ns222p1967 := nat_lit 26986771462708161478131712 

noncomputable def Ns222p1968 := nat_lit 335332795663572763491544417529927720660434251939840 

noncomputable def Ns222p1969 := nat_lit 141301252532382523267140278915229685173083701248 

noncomputable def Ns222p1970 := nat_lit 107011497612342651863948449516844600386387968 

noncomputable def Ns222p1971 := BSN.log_dyadic_bound 77281812096 2174433812096 3 2 Ns222p1968 67108864 23120000 Ns222p1969 Ns222p1970 4772258 2251715624192 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 77281812096) (BSN.artanhQ 2174433812096) 0 2 Ns222p1969 Ns222p1968 Ns222p1970 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns222p1972 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 530532 4000) qz786 530532 4000 0 1 3141673684901111 281474976710656 781250289 18062500000000000 416689605849489055263 281474976710656000 103619569580937 18062500000000000000 (Enclosure.Real.IsNear.const Bool.false 530532 4000) (BSN.isNear_log_sfrac 1125857812096 16000000 3141673684901111 281474976710656 781250289 18062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1125857812096) qz354)) Bool.false Ns222p1967 Ns222p89 1000000369920000 23120000000000000000000 3141673684901111 281474976710656 781250289 18062500000000000 (BSN.log_rat_reduce_isNear 1125857812096 16000000 16 2251715624192 2097152000000 4772258 67108864 24973259072661432 36028797018963968 23120000 1000000000000000 rfl rfl rfl rfl (Ns222p1971 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns222p1973 := BSN.arctan_dyadic_bound_f 1000 1061064 1 0 8388608 2890000 0 1 1 0 1 1 7905 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1061064) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1061064) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz590 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1061064)))

noncomputable def Ns222p1974 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz590 884279719003555 562949953421312 1 2000000000000000 7905 8388608 1 2890000 7413425805689178030080 883749223433635 562949953421312 200000000289 578000000000000000 qz16 (Ns222p1973 rfl) rfl rfl 

noncomputable def Ns222p1975 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 530532 4000) qz786) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz590)) 416689605849489055263 281474976710656000 103619569580937 18062500000000000000 883749223433635 2251799813685248 200000000289 2312000000000000000 Ns222p1966 52072392149569981361 35184372088832000 1682913113331117 289000000000000000000 (Ns222p1972 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz590) 1 4 0 1 883749223433635 562949953421312 200000000289 578000000000000000 883749223433635 2251799813685248 200000000289 2312000000000000000 qz357 Ns222p1974 rfl) 

noncomputable def Ns222p1976 := @Ns222p1962 Ns222p1956 Ns222p1957 2031418878527485029 147968000000000000000000 (@Ns222p1964 2031418878527485029 147968000000000000000000 (Ns222p1965 (Ns222p1975 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 530532 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz589 (Real.log Real.pi) 530532 2000 0 1 38410761 33554432 1 33554432 5094534463713 16777216000 132633 16777216000 (Enclosure.Real.IsNear.const Bool.false 530532 2000) RS223to240.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns222p1958 Ns222p1959) 

noncomputable def Ns222p1977 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz244) Bool.false Ns222p1956 Ns222p1957 2031418878527485029 147968000000000000000000 15285086779 16777216 29 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz244) (@HAdd.hAdd Real Real Real qz358 qz586 (Enclosure.sfrac Bool.true Ns222p1958 Ns222p1959)) Bool.false Ns222p1956 Ns222p1957 2031418878527485029 147968000000000000000000 Ns222p1960 (Ns222p1976 rfl rfl)) 

noncomputable def Ns222p1978 := nat_lit 3798673675923085661831168 

noncomputable def Ns222p1979 := nat_lit 857790121214784096433639401681282694262946591845092573282840243485003759302252063714569199055276147526773191459267550401390279921004961 

noncomputable def Ns222p1980 := nat_lit 612387390822537631971562211911287423604062733786698969713222324274725743931442598014762232276110131905002275178620511789570617761 

noncomputable def Ns222p1981 := nat_lit 4283617012669490844460296133593810144870438033526370293802390957249838219622439399635502938441934859477680772369192408044404634459337121 

noncomputable def Ns222p1982 := BSN.sin_dyadic_bound_f 53982399719 34359738368 4 3 16777216 5785645 Ns222p1979 Ns222p574 Ns222p1980 Ns222p1981 Ns222p577 Ns222p1980 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53982399719) qz371 0 3 Ns222p1979 Ns222p574 Ns222p1980 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53982399719) qz372 0 3 Ns222p1981 Ns222p577 Ns222p1980 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1983 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz244) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15285086779) qz359) Bool.false 15285086779 16777216 29 2097152 Bool.false 16777215 16777216 1 2890000 (Ns222p1977 rfl) (Enclosure.sfrac_false_div 15285086779 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15285086779) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns222p1978) qz360) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 144 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q3 15285086779 16777216 226375608064910080 72057594037927936 144 Ns222p1978 Ns222p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns222p1978 Ns222p89 53982399719 34359738368 5785645 5780000 (Ns222p1982 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p1984 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz244) Bool.false Ns222p1956 Ns222p1957 2031418878527485029 147968000000000000000000 122280694237 134217728 1844 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz244) (@HAdd.hAdd Real Real Real qz358 qz586 (Enclosure.sfrac Bool.true Ns222p1958 Ns222p1959)) Bool.false Ns222p1956 Ns222p1957 2031418878527485029 147968000000000000000000 Ns222p1960 (Ns222p1976 rfl rfl)) 

noncomputable def Ns222p1985 := Ns222p1955 36329 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 345 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132281608 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 208 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 11152224 134217728) qz247 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz244) qz244 1) Bool.false 16777215 16777216 5369197 378798080000 134217720 134217728 1903 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz244) qz244 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz244)) Bool.false 16777215 16777216 5369197 378798080000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz244) qz244) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz244)) Bool.false 16777215 16777216 85907152 6060769280000 16777215 16777216 5369197 378798080000 (Ns222p1983 rfl rfl) rfl)) rfl) (Ns222p1984 rfl) RS223to240.d7 

noncomputable def Ns222p1986 := nat_lit 6835922892679249812177240358396501248625199881392532186492078087088727975304990863837016946701629926790625 

noncomputable def Ns222p1987 := nat_lit 1949840621035128074469965238848548911531161393929650610581991463599841043486996723809557910400390625 

noncomputable def Ns222p1988 := nat_lit 34152742347891833094600275397131034493971458485129562306651242241658793550244619711188804870231004032390625 

noncomputable def Ns222p1989 := BSN.sin_dyadic_bound_f 188003785 134217728 4 3 134217728 67108864 Ns222p1986 Ns222p111 Ns222p1987 Ns222p1988 Ns222p114 Ns222p1987 132281608 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 188003785) qz363 0 3 Ns222p1986 Ns222p111 Ns222p1987 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 188003785) qz364 0 3 Ns222p1988 Ns222p114 Ns222p1987 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1990 := nat_lit 3350157265620253512672198065616925062173799092011925941334462999991594199266331024448360290705672275722241 

noncomputable def Ns222p1991 := nat_lit 4014090979461569264085599810762901507239200923574918712754571103382243448429813430266135512248975361 

noncomputable def Ns222p1992 := nat_lit 20284884297763003729711538315097112152085422998953151371993419836274026684665972762406790199988389116084225 

noncomputable def Ns222p1993 := BSN.cos_dyadic_bound_f 199663617 134217728 4 3 134217728 67108864 Ns222p1990 Ns222p227 Ns222p1991 Ns222p1992 Ns222p230 Ns222p1991 11152224 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 199663617) qz361 0 3 Ns222p1990 Ns222p227 Ns222p1991 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 199663617) qz362 0 3 Ns222p1992 Ns222p230 Ns222p1991 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1994 := nat_lit 730226541220420690216531147612406190122328144445031432761231364971585 

noncomputable def Ns222p1995 := nat_lit 552859437201420867016468007799635969766273089229629084286560623681 

noncomputable def Ns222p1996 := nat_lit 1911602978393251888210983486019864420655047364735377210142951524392001 

noncomputable def Ns222p1997 := BSN.sin_dyadic_bound_f 165130327 134217728 3 2 134217728 67108864 Ns222p1994 Ns222p124 Ns222p1995 Ns222p1996 Ns222p127 Ns222p1995 126512911 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 165130327) qz363 0 2 Ns222p1994 Ns222p124 Ns222p1995 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 165130327) qz364 0 2 Ns222p1996 Ns222p127 Ns222p1995 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p1998 := nat_lit 32615089482430655641025516604117860067861556384331052737246404548961 

noncomputable def Ns222p1999 := nat_lit 3578032065446967446974488112096773530697253867159745137845475681 

noncomputable def Ns222p2000 := nat_lit 97838112383161072988182600836129386656523274645258838721463522695521 

noncomputable def Ns222p2001 := BSN.cos_dyadic_bound_f 87943861 134217728 3 2 134217728 67108864 Ns222p1998 Ns222p105 Ns222p1999 Ns222p2000 Ns222p108 Ns222p1999 106422052 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 87943861) qz361 0 2 Ns222p1998 Ns222p105 Ns222p1999 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 87943861) qz362 0 2 Ns222p2000 Ns222p108 Ns222p1999 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p2002 := Ns222p1953 61715 BSN.abs_quadSignPos (BSN.cos_quad_nat3 111 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 126512911 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 106422052 134217728) qz247 rfl rfl (Ns222p1985 RS223to240.d9 RS223to240.d11 RS223to240.d13 RS223to240.d17 (Ns222p1989 rfl rfl) (Ns222p1993 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns222p1984 rfl) RS223to240.d19 RS223to240.d21 RS223to240.d23 RS223to240.d25 RS223to240.d17 (Ns222p1997 rfl rfl) (Ns222p2001 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns222p2003 := nat_lit 1342323859158038032079817663841 

noncomputable def Ns222p2004 := BSN.sin_dyadic_bound_f 34038023 134217728 2 1 134217728 67108864 Ns222p2003 Ns222p117 Ns222p2003 Ns222p2003 Ns222p118 Ns222p2003 33674338 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 34038023) qz363 0 1 Ns222p2003 Ns222p117 Ns222p2003 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 34038023) qz364 0 1 Ns222p2003 Ns222p118 Ns222p2003 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p2005 := nat_lit 5101235144359666541711196160000 

noncomputable def Ns222p2006 := BSN.sin_dyadic_bound_f 47524640 134217728 2 1 134217728 67108864 Ns222p2005 Ns222p117 Ns222p2005 Ns222p2005 Ns222p118 Ns222p2005 46537764 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 47524640) qz363 0 1 Ns222p2005 Ns222p117 Ns222p2005 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 47524640) qz364 0 1 Ns222p2005 Ns222p118 Ns222p2005 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p2007 := Ns222p1951 82789 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 25 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 33674338 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 77 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 46537764 134217728) qz247 rfl rfl (Ns222p2002 rfl rfl) (Ns222p1984 rfl) RS223to240.d27 RS223to240.d29 RS223to240.d31 RS223to240.d33 RS223to240.d17 (Ns222p2004 rfl rfl) (Ns222p2006 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p2008 := nat_lit 12060111303952580162855425959907933991321527142589779350926530604481 

noncomputable def Ns222p2009 := nat_lit 489293858470176044133634071711052445151365893004266100805758401 

noncomputable def Ns222p2010 := nat_lit 36179355324140800136478010611580379869074278695983329520577980296641 

noncomputable def Ns222p2011 := BSN.cos_dyadic_bound_f 68579801 134217728 3 2 134217728 67108864 Ns222p2008 Ns222p105 Ns222p2009 Ns222p2010 Ns222p108 Ns222p2009 117074873 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 68579801) qz361 0 2 Ns222p2008 Ns222p105 Ns222p2009 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 68579801) qz362 0 2 Ns222p2010 Ns222p108 Ns222p2009 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p2012 := nat_lit 250784001372351065358511210000 

noncomputable def Ns222p2013 := BSN.cos_dyadic_bound_f 22378190 134217728 2 1 134217728 67108864 Ns222p2012 Ns222p246 Ns222p2012 Ns222p2012 Ns222p247 Ns222p2012 132356482 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 22378190) qz361 0 1 Ns222p2012 Ns222p246 Ns222p2012 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 22378190) qz362 0 1 Ns222p2012 Ns222p247 Ns222p2012 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p2014 := Ns222p1949 101203 BSN.abs_quadSignNeg qz743 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 117074873 134217728) BSN.abs_quadSignNeg qz408 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132356482 134217728) qz247 rfl rfl (Ns222p2007 rfl) (Ns222p1984 rfl) RS223to240.d35 RS223to240.d37 RS223to240.d46 RS223to240.d48 RS223to240.d17 (Ns222p2011 rfl rfl) (Ns222p2013 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p2015 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz244) qz244 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz244) qz244 9) 41120924 134217728 101203 134217728 41120924 134217728 101203 134217728 11038313985081344 10280231 16777216 101203 67108864 (Ns222p2014 rfl) 

noncomputable def Ns222p2016 := @Enclosure.Real.IsNear.mulLit_tf qz784 (Zeta.RiemannSiegel.correction qz246) 5534609 16777216 1 16777216 627403603085 1099511627776 382659346936843 6355177208545280000 3472433628266668765 18446744073709551616 

noncomputable abbrev qz788 := (@HPow.hPow Real Real Real qz6 qz245 qz8)

noncomputable def Ns222p2017 := @Enclosure.Real.IsNear.mulLit_tf qz48 qz788 1 1 0 1 5534609 16777216 1 16777216 5534609 16777216 1 16777216 

noncomputable def Ns222p2018 := @Enclosure.Real.IsNear.sqrt_image qz245 354153586041 4194304000 132633 4194304000 77082481 77082511 8388608 (@Enclosure.Real.IsNear.of_eq qz245 (@HMul.hMul Real Real Real qz4 qz244 qz2) Bool.false 354153586041 4194304000 132633 4194304000 (BSN.t_div_two_pi_mk qz244 530532 1000 qz247) (@Enclosure.Real.IsNear.mulLit_ff qz244 qz2 530532 1000 0 1 2670177 16777216 1 16777216 354153586041 4194304000 132633 4194304000 (Enclosure.Real.IsNear.const Bool.false 530532 1000) RS223to240.d40 rfl)) 

noncomputable abbrev qz925 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 530532 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz789 := qz925

noncomputable abbrev qz591 := qz789

noncomputable abbrev qz249 := qz591

noncomputable def Ns222p2019 := @Enclosure.Real.IsNear.sqrt_image qz249 602207 65536 15 8388608 25428620 25428625 8388608 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 154164992 16777216 30 16777216 602207 65536 15 8388608 (Ns222p2018 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns222p2020 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz249) 50857245 16777216 5 16777216 2767304 2767305 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz249) Bool.false 50857245 16777216 5 16777216 50857245 16777216 5 16777216 (Ns222p2019 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns222p2021 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 5534609 16777216 1 16777216 5534609 16777216 1 16777216 (Ns222p2020 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz250 := (@HMul.hMul Real Real Real qz343 qz341 qz584)

noncomputable abbrev qz790 := (@HMul.hMul Real Real Real qz848 qz923 qz923)

noncomputable abbrev qz592 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz790 qz783) qz639)

noncomputable abbrev qz251 := (Real.cos (@HMul.hMul Real Real Real qz343 qz341 qz592))

noncomputable def Ns222p2022 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz246) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz250)) qz251) Bool.false 627403603085 

noncomputable def Ns222p2023 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz250)) qz251 5603569 2097152 87 

noncomputable def Ns222p2024 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz250)) Bool.false 44828552 16777216 1392 16777216 5603569 2097152 87 

noncomputable def Ns222p2025 := @Enclosure.Real.IsNear.recentre' (Real.cos qz250) Bool.false 3139461 8388608 562987216 48486154240000 3139461 8388608 35186701 3030384640000 

noncomputable def Ns222p2026 := @Enclosure.Real.IsNear.cos_image qz250 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 19917999) qz359) Bool.false 19917999 16777216 189 16777216 Bool.false 3139461 8388608 1 

noncomputable def Ns222p2027 := nat_lit 404791131149275934314284713 

noncomputable def Ns222p2028 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz246 884279719003555 140737488355328 1 500000000000000 12383 65536 15 8388608 10950035760421021565 9223372036854775808 Ns222p2027 

noncomputable def Ns222p2029 := @Enclosure.Real.IsNear.subLit_ff_p qz249 qz46 602207 65536 15 8388608 9 1 0 1 12383 12383 65536 15 

noncomputable def Ns222p2030 := @Ns222p2029 8388608 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 154164992 16777216 30 16777216 602207 65536 15 8388608 (Ns222p2018 rfl rfl rfl rfl rfl rfl) rfl) qz411 

noncomputable def Ns222p2031 := @Enclosure.Real.IsNear.recentre' qz250 Bool.false 10950035760421021565 9223372036854775808 Ns222p2027 Ns222p263 19917999 16777216 189 16777216 (@Ns222p2028 Ns222p263 RS223to240.d39 (Ns222p2030 rfl rfl) rfl) 

noncomputable def Ns222p2032 := nat_lit 20974177147416052096397116922014019732969103166260885818660481 

noncomputable def Ns222p2033 := nat_lit 24772261157872783816597905330528902957576093664956112656001 

noncomputable def Ns222p2034 := nat_lit 62872986919932410721558154955381001392992157311452745230669441 

noncomputable def Ns222p2035 := BSN.cos_dyadic_bound_f 19917999 16777216 3 2 8388608 2890000 Ns222p2032 Ns222p866 Ns222p2033 Ns222p2034 Ns222p869 Ns222p2033 3139461 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 19917999) qz391 0 2 Ns222p2032 Ns222p866 Ns222p2033 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 19917999) (BSN.cosOddQ 16777216) 0 2 Ns222p2034 Ns222p869 Ns222p2033 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p2036 := @Enclosure.Real.IsNear.inv_image (Real.cos qz250) 3139461 8388608 35186701 3030384640000 22413580 22414972 8388608 (Ns222p2025 (@Ns222p2026 2890000 (Ns222p2031 rfl) (Enclosure.sfrac_false_div 19917999 16777216) (Ns222p2035 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns222p2037 := @Enclosure.Real.IsNear.recentre' qz251 Bool.false 1791440 8388608 

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz343 qz341 qz592)

noncomputable def Ns222p2038 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 11371449)) qz370) Bool.true 11371449 8388608 

noncomputable def Ns222p2039 := nat_lit 935769501729073926943584234659579 

noncomputable def Ns222p2040 := @Enclosure.Real.IsNear.recentre' qz252 Bool.true 819399280375929711290525 604462909807314587353088 Ns222p2039 

noncomputable abbrev qz253 := qz592

noncomputable def Ns222p2041 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz253 884279719003555 140737488355328 1 500000000000000 926629055 

noncomputable abbrev qz593 := (@HSub.hSub Real Real Real qz634 qz790 qz783)

noncomputable abbrev qz254 := qz593

noncomputable def Ns222p2042 := @Enclosure.Real.IsNear.subLit_tf qz254 qz25 658193599 4294967296 173380065 70368744177664 1 16 

noncomputable abbrev qz594 := qz790

noncomputable abbrev qz255 := qz594

noncomputable def Ns222p2043 := @Enclosure.Real.IsNear.subLit_ff_n qz255 qz246 153338689 4294967296 47550945 70368744177664 12383 65536 15 8388608 

noncomputable def Ns222p2044 := @Enclosure.Real.IsNear.mulLit_ff qz246 qz246 12383 65536 15 8388608 12383 65536 15 8388608 153338689 4294967296 

noncomputable def Ns222p2045 := nat_lit 139381189608209943618124995619230605993785714555960039359681 

noncomputable def Ns222p2046 := nat_lit 279593109030507112159675002481291819758848433682226398401 

noncomputable def Ns222p2047 := nat_lit 417584382606568816630055636852729234341839446800515665282241 

noncomputable def Ns222p2048 := BSN.cos_dyadic_bound_f 11371449 8388608 3 2 8388608 2890000 Ns222p2045 Ns222p642 Ns222p2046 Ns222p2047 Ns222p645 Ns222p2046 1791440 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 11371449) (BSN.cosEvenQ 8388608) 0 2 Ns222p2045 Ns222p642 Ns222p2046 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 11371449) (BSN.cosOddQ 8388608) 0 2 Ns222p2047 Ns222p645 Ns222p2046 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p2049 := @Ns222p2037 771067216 48486154240000 111965 524288 48191701 3030384640000 (@Ns222p2038 261 16777216 Bool.false 1791440 8388608 1 2890000 (@Ns222p2040 Ns222p1494 11371449 8388608 261 16777216 (@Ns222p2041 4294967296 173380065 70368744177664 819399280375929711290525 604462909807314587353088 Ns222p2039 Ns222p1494 RS223to240.d39 (@Ns222p2042 0 1 14826064880 926629055 4294967296 173380065 70368744177664 (@Ns222p2043 43135375704064 658193599 4294967296 173380065 70368744177664 (@Ns222p2044 47550945 70368744177664 (Ns222p2030 rfl rfl) (Ns222p2030 rfl rfl) rfl) (Ns222p2030 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 11371449 8388608) (BSN.cos_neg_of_bound 11371449 8388608 Bool.false 1791440 8388608 1 2890000 (Ns222p2048 rfl rfl)) rfl rfl) 

noncomputable def Ns222p2050 := @Ns222p2016 212149664097595193623 Ns222p978 (Ns222p2017 qz61 (@Enclosure.Real.IsNear.of_eq qz788 (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 5534609 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz245 (BSN.t_div_two_pi_nonneg qz244 530532 1000 qz247)) Ns222p2021) rfl) (@Ns222p2022 1099511627776 382659346936843 6355177208545280000 (BSN.correction_mk qz246 (BSN.cos_two_pi_p_ne_zero_mk qz244 530532 1000 9 qz247 rfl rfl (@BSN.floor_sqrt_eq_dec qz244 530532 1000 9 qz247 rfl rfl rfl))) (@Ns222p2023 1048576 111965 524288 48191701 3030384640000 627403603085 1099511627776 382659346936843 6355177208545280000 (@Ns222p2024 1048576 (Ns222p2036 rfl rfl rfl rfl rfl) rfl) (Ns222p2049 rfl) rfl)) 

noncomputable def Ns222p2051 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz244) (hardyZApproximantRS₀ qz244) Bool.false 14775667148989965021 18446744073709551616 16291224640007794489623 Ns222p978 (@Eq.refl Real (hardyZApproximantRS₀ qz244)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz244) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz244) qz244 9) (@HMul.hMul Real Real Real qz4 qz784 (Zeta.RiemannSiegel.correction qz246))) Bool.false 14775667148989965021 18446744073709551616 16291224640007794489623 Ns222p978 (BSN.hardyZApproximantRS₀_eq qz244 9 (@BSN.floor_sqrt_eq_dec qz244 530532 1000 9 qz247 rfl rfl rfl)) (@Ns222p1947 14775667148989965021 18446744073709551616 16291224640007794489623 Ns222p978 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz244) qz244 9) (@HAdd.hAdd Real Real Real qz358 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz244) qz244 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz244) qz244 9)) Bool.false 10280231 16777216 101203 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz244) qz244 9) (Ns222p2015 (Ns222p2014 rfl) rfl rfl)) (Ns222p2050 rfl) rfl rfl)) 

theorem RS223to240.d64 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz244) Bool.false 14775667148989965021 18446744073709551616 16291224640007794489623 Ns222p978 := Ns222p2051 

noncomputable def Ns222p2052 := nat_lit 209316860547503280869081088 

noncomputable abbrev qz926 := (Enclosure.sfrac Bool.false 531948 1000)

noncomputable abbrev qz791 := qz926

noncomputable abbrev qz595 := qz791

noncomputable abbrev qz256 := qz595

noncomputable abbrev qz927 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 531948 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz792 := qz927

noncomputable abbrev qz596 := qz792

noncomputable abbrev qz257 := qz596

noncomputable abbrev qz928 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 531948 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz793 := qz928

noncomputable abbrev qz597 := qz793

noncomputable abbrev qz258 := qz597

noncomputable abbrev qz794 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz257 qz8))

noncomputable def Ns222p2053 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz256) qz256 9) (@HMul.hMul Real Real Real qz4 qz794 (Zeta.RiemannSiegel.correction qz258)) 193829031 67108864 25367 16777216 210893117033003337 1152921504606846976 1318907120774061729221 Ns222p542 Ns222p2052 

noncomputable def Ns222p2054 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz256) qz256 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 531948 1000 122 162 134217728 67108864 2251799813685248 Bool.false 122702357199 1849 

noncomputable def Ns222p2055 := Ns222p2054 279097919 47 47453128 8 294906479 47 44739240 8 Bool.true 104369471 83005 Bool.true 42119492 Bool.true 18302802 7074237752028440 1 Bool.false 127662929 Bool.true Bool.false 132971716 Bool.true Bool.true 193829031 

noncomputable def Ns222p2056 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz256) qz256 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 531948 1000 24 76 134217728 67108864 2251799813685248 Bool.false 122702357199 1849 

noncomputable def Ns222p2057 := Ns222p2056 240485871 47 54794152 8 261175631 47 50729528 8 Bool.true 124834679 61875 Bool.true 163731768 Bool.true 206515086 7074237752028440 1 Bool.false 46136367 Bool.false Bool.false 4312885 Bool.false Bool.true 104369471 

noncomputable def Ns222p2058 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz256) qz256 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 531948 1000 112 36 134217728 67108864 2251799813685248 Bool.false 122702357199 1849 

noncomputable def Ns222p2059 := Ns222p2058 186065264 47 67108856 8 216015088 47 60023992 8 Bool.true 172892536 36421 Bool.false 112496161 Bool.false 203729458 7074237752028440 1 Bool.false 89768918 Bool.false Bool.false 7095946 Bool.false Bool.true 124834679 

noncomputable def Ns222p2060 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz256) qz256 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 531948 1000 347 209 134217728 67108864 2251799813685248 Bool.false 122702357199 1849 

noncomputable def Ns222p2061 := Ns222p2060 93032624 47 94906264 8 147453232 47 77490640 16 Bool.true 134217720 1903 Bool.false 56275123 Bool.false 201704089 7074237752028440 1 Bool.false 54640716 Bool.false Bool.false 133907684 Bool.true Bool.true 172892536 

noncomputable def Ns222p2062 := nat_lit 88964986588852083674338198102231186259524595771803 

noncomputable def Ns222p2063 := nat_lit 97314172636857003773117221834031743362924544000 

noncomputable def Ns222p2064 := nat_lit 20445046908318498710438378864640000 

noncomputable def Ns222p2065 := nat_lit 65254237780847626474354788400701112320 

noncomputable def Ns222p2066 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz256 531948 1000 1131875698816 16000000 1063896 4000 2000 Ns222p2064 Ns222p2065 (@Eq.refl Real qz256) rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns222p2067 := nat_lit 8395789479965294624181256537192065152694053628241269227520 

noncomputable abbrev qz795 := (Real.log (Enclosure.sfrac Bool.false 1131875698816 16000000))

noncomputable abbrev qz259 := (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz343 (Enclosure.sfrac Bool.false 531948 4000) qz795) (@HMul.hMul Real Real Real qz343 qz348 (@HSub.hSub Real Real Real qz347 qz349 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz350 (@Nat.cast Real Real.instNatCast 1063896))))))

noncomputable abbrev qz796 := (Enclosure.sfrac Bool.false 531948 2000)

noncomputable abbrev qz598 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz259 qz796) (@HMul.hMul Real Real Real qz4 qz796 (Real.log Real.pi)))

noncomputable def Ns222p2068 := @Enclosure.Real.IsNear.addLit_ft_p qz598 (Enclosure.sfrac Bool.true Ns222p2064 Ns222p2065) 128662790998288905611 140737488355328000 2036806610713232031 147968000000000000000000 Ns222p2064 Ns222p2065 0 1 Ns222p2067 

noncomputable def Ns222p2069 := nat_lit 2158603435741148599839358976000 

noncomputable abbrev qz599 := (@HSub.hSub Real Real Real qz11 qz259 qz796)

noncomputable abbrev qz600 := (@HMul.hMul Real Real Real qz4 qz796 (Real.log Real.pi))

noncomputable def Ns222p2070 := @Enclosure.Real.IsNear.subLit_ff_p qz599 qz600 171512906894089270667 140737488355328000 1687338114968013 289000000000000000000 5108131873107 16777216000 132987 16777216000 Ns222p2069 128662790998288905611 140737488355328000 

noncomputable abbrev qz601 := qz796

noncomputable def Ns222p2071 := @Enclosure.Real.IsNear.subLit_ff_p qz259 qz601 208945419621909280139 140737488355328000 1687338114968013 289000000000000000000 531948 2000 0 1 343025813788178541334000 171512906894089270667 140737488355328000 1687338114968013 289000000000000000000 

noncomputable def Ns222p2072 := nat_lit 941006513950002557250077808807378944 

noncomputable def Ns222p2073 := nat_lit 26999660836899289875611648 

noncomputable def Ns222p2074 := nat_lit 339060455951402476876284256889580256619924595671040 

noncomputable def Ns222p2075 := nat_lit 165093488436184056056857019777223061949160357888 

noncomputable def Ns222p2076 := nat_lit 144442494260937176860060170147562888215134208 

noncomputable def Ns222p2077 := BSN.log_dyadic_bound 83299698816 2180451698816 3 2 Ns222p2074 67108864 23120000 Ns222p2075 Ns222p2076 5130010 2263751397632 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 83299698816) (BSN.artanhQ 2180451698816) 0 2 Ns222p2075 Ns222p2074 Ns222p2076 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns222p2078 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 531948 4000) qz795 531948 4000 0 1 3143174205545719 281474976710656 781250289 18062500000000000 418001308072908532653 281474976710656000 103896132183243 18062500000000000000 (Enclosure.Real.IsNear.const Bool.false 531948 4000) (BSN.isNear_log_sfrac 1131875698816 16000000 3143174205545719 281474976710656 781250289 18062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1131875698816) qz354)) Bool.false Ns222p2073 Ns222p89 1000000369920000 23120000000000000000000 3143174205545719 281474976710656 781250289 18062500000000000 (BSN.log_rat_reduce_isNear 1131875698816 16000000 16 2263751397632 2097152000000 5130010 67108864 24973259072661432 36028797018963968 23120000 1000000000000000 rfl rfl rfl rfl (Ns222p2077 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns222p2079 := BSN.arctan_dyadic_bound_f 1000 1063896 1 0 8388608 2890000 0 1 1 0 1 1 7884 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1063896) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1063896) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz797 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1063896)))

noncomputable def Ns222p2080 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz797 884279719003555 562949953421312 1 2000000000000000 7884 8388608 1 2890000 7413437627638199877632 883750632719779 562949953421312 200000000289 578000000000000000 qz16 (Ns222p2079 rfl) rfl rfl 

noncomputable def Ns222p2081 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 531948 4000) qz795) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz797)) 418001308072908532653 281474976710656000 103896132183243 18062500000000000000 883750632719779 2251799813685248 200000000289 2312000000000000000 Ns222p2072 208945419621909280139 140737488355328000 1687338114968013 289000000000000000000 (Ns222p2078 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz797) 1 4 0 1 883750632719779 562949953421312 200000000289 578000000000000000 883750632719779 2251799813685248 200000000289 2312000000000000000 qz357 Ns222p2080 rfl) 

noncomputable def Ns222p2082 := @Ns222p2068 Ns222p2062 Ns222p2063 2036806610713232031 147968000000000000000000 (@Ns222p2070 2036806610713232031 147968000000000000000000 (Ns222p2071 (Ns222p2081 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 531948 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz601 (Real.log Real.pi) 531948 2000 0 1 38410761 33554432 1 33554432 5108131873107 16777216000 132987 16777216000 (Enclosure.Real.IsNear.const Bool.false 531948 2000) RS223to240.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns222p2064 Ns222p2065) 

noncomputable def Ns222p2083 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz256) Bool.false Ns222p2062 Ns222p2063 2036806610713232031 147968000000000000000000 15337794649 16777216 29 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz256) (@HAdd.hAdd Real Real Real qz358 qz598 (Enclosure.sfrac Bool.true Ns222p2064 Ns222p2065)) Bool.false Ns222p2062 Ns222p2063 2036806610713232031 147968000000000000000000 Ns222p2066 (Ns222p2082 rfl rfl)) 

noncomputable def Ns222p2084 := nat_lit 3798773326778170236469248 

noncomputable def Ns222p2085 := nat_lit 857880315701638037633288115969430579424582874412137543905840086399430724087819050421798443084646444471099243842018339232807217826369536 

noncomputable def Ns222p2086 := nat_lit 612580196108991635018611350532762904605346115744660125578960181495778845675071716015304862619695109593482547565237696281794318336 

noncomputable def Ns222p2087 := nat_lit 4284066865412495480983827233500334521500119233854881227093721819633636369690823829569466085968902706184872742758678370426170494359965696 

noncomputable def Ns222p2088 := BSN.sin_dyadic_bound_f 53983815842 34359738368 4 3 16777216 5785645 Ns222p2085 Ns222p574 Ns222p2086 Ns222p2087 Ns222p577 Ns222p2086 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53983815842) qz371 0 3 Ns222p2085 Ns222p574 Ns222p2086 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53983815842) qz372 0 3 Ns222p2087 Ns222p577 Ns222p2086 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p2089 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz256) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15337794649) qz359) Bool.false 15337794649 16777216 29 2097152 Bool.true 16777215 16777216 1 2890000 (Ns222p2083 rfl) (Enclosure.sfrac_false_div 15337794649 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15337794649) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns222p2084) qz360) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 145 1000000000000000 5780000 2890000 (BSN.sin_reduce_arg_pos_rat_q1 15337794649 16777216 226375608064910080 72057594037927936 145 Ns222p2084 Ns222p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns222p2084 Ns222p89 53983815842 34359738368 5785645 5780000 (Ns222p2088 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns222p2090 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz256) Bool.false Ns222p2062 Ns222p2063 2036806610713232031 147968000000000000000000 122702357199 134217728 1849 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz256) (@HAdd.hAdd Real Real Real qz358 qz598 (Enclosure.sfrac Bool.true Ns222p2064 Ns222p2065)) Bool.false Ns222p2062 Ns222p2063 2036806610713232031 147968000000000000000000 Ns222p2066 (Ns222p2082 rfl rfl)) 

noncomputable def Ns222p2091 := Ns222p2061 36421 BSN.abs_quadSignPos (BSN.cos_quad_nat3 347 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 54640716 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 209 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133907684 134217728) (@Eq.refl Real qz256) rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 1) Bool.true 16777215 16777216 5369197 378798080000 134217720 134217728 1903 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz256)) Bool.true 16777215 16777216 5369197 378798080000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz256) qz256) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz256)) Bool.true 16777215 16777216 85907152 6060769280000 16777215 16777216 5369197 378798080000 (Ns222p2089 rfl rfl) rfl)) rfl) (Ns222p2090 rfl) RS223to240.d7 

noncomputable def Ns222p2092 := nat_lit 10029188906742103074365140586641 

noncomputable def Ns222p2093 := BSN.sin_dyadic_bound_f 56275123 134217728 2 1 134217728 67108864 Ns222p2092 Ns222p117 Ns222p2092 Ns222p2092 Ns222p118 Ns222p2092 54640716 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 56275123) qz363 0 1 Ns222p2092 Ns222p117 Ns222p2092 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 56275123) qz364 0 1 Ns222p2092 Ns222p118 Ns222p2092 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p2094 := nat_lit 9060852646966334611486146980301145491637696046678355836863316397663270865074470174443700999865497491209121 

noncomputable def Ns222p2095 := nat_lit 4534990997291187277351530872862592351610506055487281797140320876077541035754511478238122118315375521 

noncomputable def Ns222p2096 := nat_lit 45257086520611716820881386677470439255540186568695139397520811423115335128634644849192082976174372713266081 

noncomputable def Ns222p2097 := BSN.sin_dyadic_bound_f 201704089 134217728 4 3 134217728 67108864 Ns222p2094 Ns222p111 Ns222p2095 Ns222p2096 Ns222p114 Ns222p2095 133907684 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 201704089) qz363 0 3 Ns222p2094 Ns222p111 Ns222p2095 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 201704089) qz364 0 3 Ns222p2096 Ns222p114 Ns222p2095 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p2098 := nat_lit 87342814900806916023146159264489608685543413896017264975276894511361 

noncomputable def Ns222p2099 := nat_lit 25650841498341852438021519914169390206112527311456342514527822081 

noncomputable def Ns222p2100 := nat_lit 261977143019424064364562434753640487276218016633428882240801627889921 

noncomputable def Ns222p2101 := BSN.cos_dyadic_bound_f 112496161 134217728 3 2 134217728 67108864 Ns222p2098 Ns222p105 Ns222p2099 Ns222p2100 Ns222p108 Ns222p2099 89768918 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 112496161) qz361 0 2 Ns222p2098 Ns222p105 Ns222p2099 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 112496161) qz362 0 2 Ns222p2100 Ns222p108 Ns222p2099 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p2102 := nat_lit 3632376507554160948526388470774439770508604132039986539037400027778857490806072959317945853321922830012416 

noncomputable def Ns222p2103 := nat_lit 5112648758884450387204672860542856144899364092350438259022383519272266946735421664683278120733249536 

noncomputable def Ns222p2104 := nat_lit 21990116675500269647691443788365799415120623266707517394811319657048827651957929008505623198727605394739200 

noncomputable def Ns222p2105 := BSN.cos_dyadic_bound_f 203729458 134217728 4 3 134217728 67108864 Ns222p2102 Ns222p227 Ns222p2103 Ns222p2104 Ns222p230 Ns222p2103 7095946 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 203729458) qz361 0 3 Ns222p2102 Ns222p227 Ns222p2103 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 203729458) qz362 0 3 Ns222p2104 Ns222p230 Ns222p2103 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p2106 := Ns222p2059 61875 BSN.abs_quadSignPos (BSN.cos_quad_nat0 112 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 89768918 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 7095946 134217728) (@Eq.refl Real qz256) rfl rfl (Ns222p2091 RS223to240.d9 RS223to240.d11 RS223to240.d13 RS223to240.d17 (Ns222p2093 rfl rfl) (Ns222p2097 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns222p2090 rfl) RS223to240.d19 RS223to240.d21 RS223to240.d23 RS223to240.d25 RS223to240.d17 (Ns222p2101 rfl rfl) (Ns222p2105 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns222p2107 := nat_lit 1512546762242636707143831766346516375017914142994742761243812516288146905851491588671657007625737502457856 

noncomputable def Ns222p2108 := nat_lit 371189273044159273013262175676477189781620816912423999207631239884405043106898849430049767005618176 

noncomputable def Ns222p2109 := nat_lit 9168061758644539649293462253345852888094983484605512632443331962622754569923206576101295856270370857287680 

noncomputable def Ns222p2110 := BSN.cos_dyadic_bound_f 163731768 134217728 4 3 134217728 67108864 Ns222p2107 Ns222p227 Ns222p2108 Ns222p2109 Ns222p230 Ns222p2108 46136367 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 163731768) qz361 0 3 Ns222p2107 Ns222p227 Ns222p2108 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 163731768) qz362 0 3 Ns222p2109 Ns222p230 Ns222p2108 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p2111 := nat_lit 3835827775878377796332797248324515289607117360227640186065763262368095811196859114596458893013135584792576 

noncomputable def Ns222p2112 := nat_lit 6017573315009013305934578540919367209454293097149788884016347421677363859807422694083883793229418496 

noncomputable def Ns222p2113 := nat_lit 23219072344260694848274935982941846364134035990525770139307935432337226013742175882244286286173422251806720 

noncomputable def Ns222p2114 := BSN.cos_dyadic_bound_f 206515086 134217728 4 3 134217728 67108864 Ns222p2111 Ns222p227 Ns222p2112 Ns222p2113 Ns222p230 Ns222p2112 4312885 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 206515086) qz361 0 3 Ns222p2111 Ns222p227 Ns222p2112 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 206515086) qz362 0 3 Ns222p2113 Ns222p230 Ns222p2112 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p2115 := Ns222p2057 83005 BSN.abs_quadSignPos (BSN.cos_quad_nat0 24 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 46136367 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 76 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 4312885 134217728) (@Eq.refl Real qz256) rfl rfl (Ns222p2106 rfl rfl) (Ns222p2090 rfl) RS223to240.d27 RS223to240.d29 RS223to240.d31 RS223to240.d33 RS223to240.d17 (Ns222p2110 rfl rfl) (Ns222p2114 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p2116 := nat_lit 3147259101950665200375855268096 

noncomputable def Ns222p2117 := BSN.cos_dyadic_bound_f 42119492 134217728 2 1 134217728 67108864 Ns222p2116 Ns222p246 Ns222p2116 Ns222p2116 Ns222p247 Ns222p2116 127662929 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 42119492) qz361 0 1 Ns222p2116 Ns222p246 Ns222p2116 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 42119492) qz362 0 1 Ns222p2116 Ns222p247 Ns222p2116 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p2118 := nat_lit 112220015959644639189509849616 

noncomputable def Ns222p2119 := BSN.cos_dyadic_bound_f 18302802 134217728 2 1 134217728 67108864 Ns222p2118 Ns222p246 Ns222p2118 Ns222p2118 Ns222p247 Ns222p2118 132971716 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 18302802) qz361 0 1 Ns222p2118 Ns222p246 Ns222p2118 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 18302802) qz362 0 1 Ns222p2118 Ns222p247 Ns222p2118 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p2120 := Ns222p2055 101468 BSN.abs_quadSignNeg qz743 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 127662929 134217728) BSN.abs_quadSignNeg qz408 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132971716 134217728) (@Eq.refl Real qz256) rfl rfl (Ns222p2115 rfl) (Ns222p2090 rfl) RS223to240.d35 RS223to240.d37 RS223to240.d46 RS223to240.d48 RS223to240.d17 (Ns222p2117 rfl rfl) (Ns222p2119 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns222p2121 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 9) 193829031 134217728 101468 134217728 193829031 134217728 101468 134217728 52030584322523136 193829031 67108864 25367 16777216 (Ns222p2120 rfl) 

noncomputable def Ns222p2122 := @Enclosure.Real.IsNear.mulLit_tf qz794 (Zeta.RiemannSiegel.correction qz258) 2765461 8388608 1 8388608 76259660517 137438953472 951291953439791 12710354417090560000 210893117033003337 1152921504606846976 

noncomputable abbrev qz798 := (@HPow.hPow Real Real Real qz6 qz257 qz8)

noncomputable def Ns222p2123 := @Enclosure.Real.IsNear.mulLit_tf qz48 qz798 1 1 0 1 2765461 8388608 1 8388608 2765461 8388608 1 8388608 

noncomputable def Ns222p2124 := @Enclosure.Real.IsNear.sqrt_image qz257 355098828699 4194304000 132987 4194304000 77185280 77185310 8388608 (@Enclosure.Real.IsNear.of_eq qz257 (@HMul.hMul Real Real Real qz4 qz256 qz2) Bool.false 355098828699 4194304000 132987 4194304000 (BSN.t_div_two_pi_mk qz256 531948 1000 (@Eq.refl Real qz256)) (@Enclosure.Real.IsNear.mulLit_ff qz256 qz2 531948 1000 0 1 2670177 16777216 1 16777216 355098828699 4194304000 132987 4194304000 (Enclosure.Real.IsNear.const Bool.false 531948 1000) RS223to240.d40 rfl)) 

noncomputable abbrev qz929 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 531948 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz799 := qz929

noncomputable abbrev qz602 := qz799

noncomputable abbrev qz260 := qz602

noncomputable def Ns222p2125 := @Enclosure.Real.IsNear.sqrt_image qz260 77185295 8388608 15 8388608 25445570 25445576 8388608 (@Enclosure.Real.IsNear.recentre' qz260 Bool.false 154370590 16777216 30 16777216 77185295 8388608 15 8388608 (Ns222p2124 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns222p2126 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz260) 25445573 8388608 3 8388608 2765460 2765462 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz260) Bool.false 50891146 16777216 6 16777216 25445573 8388608 3 8388608 (Ns222p2125 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns222p2127 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz260)) Bool.false 5530922 16777216 2 16777216 2765461 8388608 1 8388608 (Ns222p2126 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz261 := (@HMul.hMul Real Real Real qz343 qz341 qz597)

noncomputable abbrev qz800 := (@HMul.hMul Real Real Real qz848 qz928 qz928)

noncomputable abbrev qz603 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz800 qz793) qz639)

noncomputable abbrev qz262 := (Real.cos (@HMul.hMul Real Real Real qz343 qz341 qz603))

noncomputable def Ns222p2128 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz258) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz261)) qz262) Bool.false 76259660517 

noncomputable def Ns222p2129 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz261)) qz262 434283 131072 535 

noncomputable def Ns222p2130 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz261)) Bool.false 55588224 16777216 2140 16777216 434283 131072 535 

noncomputable def Ns222p2131 := @Enclosure.Real.IsNear.recentre' (Real.cos qz261) Bool.false 2531786 8388608 562987216 48486154240000 1265893 4194304 35186701 3030384640000 

noncomputable def Ns222p2132 := @Enclosure.Real.IsNear.cos_image qz261 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21209809) qz359) Bool.false 21209809 16777216 189 16777216 Bool.false 2531786 8388608 1 

noncomputable def Ns222p2133 := nat_lit 404791131150158971000407721 

noncomputable def Ns222p2134 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz258 884279719003555 140737488355328 1 500000000000000 1687823 8388608 15 8388608 1492507648167737210765 1180591620717411303424 Ns222p2133 

noncomputable def Ns222p2135 := @Enclosure.Real.IsNear.subLit_ff_p qz260 qz46 77185295 8388608 15 8388608 9 1 0 1 1687823 1687823 8388608 15 

noncomputable def Ns222p2136 := @Ns222p2135 8388608 (@Enclosure.Real.IsNear.recentre' qz260 Bool.false 154370590 16777216 30 16777216 77185295 8388608 15 8388608 (Ns222p2124 rfl rfl rfl rfl rfl rfl) rfl) qz411 

noncomputable def Ns222p2137 := @Enclosure.Real.IsNear.recentre' qz261 Bool.false 1492507648167737210765 1180591620717411303424 Ns222p2133 Ns222p263 21209809 16777216 189 16777216 (@Ns222p2134 Ns222p263 RS223to240.d39 (Ns222p2136 rfl rfl) rfl) 

noncomputable def Ns222p2138 := nat_lit 26977126982922309029552640609095105053185312774799874278953601 

noncomputable def Ns222p2139 := nat_lit 40953786393736801567141661964872406061002024404883000136321 

noncomputable def Ns222p2140 := nat_lit 80849473375979453485523638503355570347433934275589856836588161 

noncomputable def Ns222p2141 := BSN.cos_dyadic_bound_f 21209809 16777216 3 2 8388608 2890000 Ns222p2138 Ns222p866 Ns222p2139 Ns222p2140 Ns222p869 Ns222p2139 2531786 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 21209809) qz391 0 2 Ns222p2138 Ns222p866 Ns222p2139 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 21209809) (BSN.cosOddQ 16777216) 0 2 Ns222p2140 Ns222p869 Ns222p2139 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p2142 := @Enclosure.Real.IsNear.inv_image (Real.cos qz261) 1265893 4194304 35186701 3030384640000 27793042 27795182 8388608 (Ns222p2131 (@Ns222p2132 2890000 (Ns222p2137 rfl) (Enclosure.sfrac_false_div 21209809 16777216) (Ns222p2141 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns222p2143 := @Enclosure.Real.IsNear.recentre' qz262 Bool.false 1404792 8388608 

noncomputable abbrev qz263 := (@HMul.hMul Real Real Real qz343 qz341 qz603)

noncomputable def Ns222p2144 := @Enclosure.Real.IsNear.cos_image qz263 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1470669)) qz645) Bool.true 1470669 1048576 

noncomputable def Ns222p2145 := nat_lit 13890076194231261540958925245 

noncomputable def Ns222p2146 := nat_lit 4762071755629116604220735937985973 

noncomputable def Ns222p2147 := @Enclosure.Real.IsNear.recentre' qz263 Bool.true Ns222p2145 Ns222p858 Ns222p2146 

noncomputable abbrev qz264 := qz603

noncomputable def Ns222p2148 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz264 884279719003555 140737488355328 1 500000000000000 15707785552159 

noncomputable abbrev qz604 := (@HSub.hSub Real Real Real qz634 qz800 qz793)

noncomputable abbrev qz265 := qz604

noncomputable def Ns222p2149 := @Enclosure.Real.IsNear.subLit_tf qz265 qz25 11309739041055 70368744177664 176464035 70368744177664 1 16 

noncomputable abbrev qz605 := qz800

noncomputable abbrev qz266 := qz605

noncomputable def Ns222p2150 := @Enclosure.Real.IsNear.subLit_ff_n qz266 qz258 2848746479329 70368744177664 50634915 70368744177664 1687823 8388608 15 8388608 

noncomputable def Ns222p2151 := @Enclosure.Real.IsNear.mulLit_ff qz258 qz258 1687823 8388608 15 8388608 1687823 8388608 15 8388608 2848746479329 70368744177664 

noncomputable def Ns222p2152 := nat_lit 136767927836049338418362607384012048082399056341919667213508021324255379016625841 

noncomputable def Ns222p2153 := nat_lit 846322570984149739285326836131859157750990110577656481930582364989086940895641600 

noncomputable def Ns222p2154 := nat_lit 102371544848208359546222575271330168325385014681709824379231093607341469361 

noncomputable def Ns222p2155 := nat_lit 828453767006601532391262081554148928821369190440724423591798686371799954588937905 

noncomputable def Ns222p2156 := nat_lit 77015353959557626274964742087999183355340100062566739855682995214006911621503385600 

noncomputable def Ns222p2157 := BSN.cos_dyadic_bound_f 1470669 1048576 4 3 8388608 2890000 Ns222p2152 Ns222p2153 Ns222p2154 Ns222p2155 Ns222p2156 Ns222p2154 1404792 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 1470669) (BSN.cosEvenQ 1048576) 0 3 Ns222p2152 Ns222p2153 Ns222p2154 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 1470669) (BSN.cosOddQ 1048576) 0 3 Ns222p2155 Ns222p2156 Ns222p2154 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns222p2158 := @Ns222p2143 782627216 48486154240000 175599 1048576 48914201 3030384640000 (@Ns222p2144 265 16777216 Bool.false 1404792 8388608 1 2890000 (@Ns222p2147 Ns222p281 1470669 1048576 265 16777216 (@Ns222p2148 70368744177664 176464035 70368744177664 Ns222p2145 Ns222p858 Ns222p2146 Ns222p281 RS223to240.d39 (@Ns222p2149 0 1 251324568834544 15707785552159 70368744177664 176464035 70368744177664 (@Ns222p2150 94872967397706301440 11309739041055 70368744177664 176464035 70368744177664 (@Ns222p2151 50634915 70368744177664 (Ns222p2136 rfl rfl) (Ns222p2136 rfl rfl) rfl) (Ns222p2136 rfl rfl) rfl rfl) qz377 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 1470669 1048576) (BSN.cos_neg_of_bound 1470669 1048576 Bool.false 1404792 8388608 1 2890000 (Ns222p2157 rfl rfl)) rfl rfl) 

noncomputable def Ns222p2159 := @Ns222p2122 1318907120774061729221 Ns222p542 (Ns222p2123 qz61 (@Enclosure.Real.IsNear.of_eq qz798 (@Inv.inv Real Real.instInv (Real.sqrt qz260)) Bool.false 2765461 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz257 (BSN.t_div_two_pi_nonneg qz256 531948 1000 (@Eq.refl Real qz256))) Ns222p2127) rfl) (@Ns222p2128 137438953472 951291953439791 12710354417090560000 (BSN.correction_mk qz258 (BSN.cos_two_pi_p_ne_zero_mk qz256 531948 1000 9 (@Eq.refl Real qz256) rfl rfl (@BSN.floor_sqrt_eq_dec qz256 531948 1000 9 (@Eq.refl Real qz256) rfl rfl rfl))) (@Ns222p2129 4194304 175599 1048576 48914201 3030384640000 76259660517 137438953472 951291953439791 12710354417090560000 (@Ns222p2130 4194304 (Ns222p2142 rfl rfl rfl rfl rfl) rfl) (Ns222p2158 rfl) rfl)) 

noncomputable def Ns222p2160 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz256) (hardyZApproximantRS₀ qz256) Bool.true 3119064279608477367 1152921504606846976 81924797245358120609221 Ns222p542 (@Eq.refl Real (hardyZApproximantRS₀ qz256)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz256) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz256) qz256 9) (@HMul.hMul Real Real Real qz4 qz794 (Zeta.RiemannSiegel.correction qz258))) Bool.true 3119064279608477367 1152921504606846976 81924797245358120609221 Ns222p542 (BSN.hardyZApproximantRS₀_eq qz256 9 (@BSN.floor_sqrt_eq_dec qz256 531948 1000 9 (@Eq.refl Real qz256) rfl rfl rfl)) (@Ns222p2053 3119064279608477367 1152921504606846976 81924797245358120609221 Ns222p542 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz256) qz256 9) (@HAdd.hAdd Real Real Real qz358 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 9)) Bool.true 193829031 67108864 25367 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz256) qz256 9) (Ns222p2121 (Ns222p2120 rfl) rfl rfl)) (Ns222p2159 rfl) rfl rfl)) 

theorem RS223to240.d65 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz256) Bool.true 3119064279608477367 1152921504606846976 81924797245358120609221 Ns222p542 := Ns222p2160 

noncomputable def RS223to240.d66 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz267 := (RS223to240.d3 qz342 qz378 (@Enclosure.dec_le_dec qz342 qz378 506327 1000 507758 1000 (@Eq.refl Real qz342) qz382 rfl rfl rfl))

noncomputable abbrev qz801 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz267)

noncomputable def Ns222p2161 := @Enclosure.Real.IsNear.of_eq qz801 (hardyZApproximantRS₀ qz3) Bool.true 9703756050334815151 18446744073709551616 1039976065833158020919 783986623132655943680000 

noncomputable abbrev qz268 := (@Enclosure.dec_le_dec qz342 qz378 506327 1000 507758 1000 (@Eq.refl Real qz342) qz382 rfl rfl rfl)

noncomputable def Ns222p2162 := @Enclosure.Real.IsNear.neg_val qz801 9703756050334815151 18446744073709551616 1039976065833158020919 783986623132655943680000 (Ns222p2161 (RS223to240.d4 qz3 qz27 qz268) RS223to240.d41) rfl 

noncomputable abbrev qz802 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz267)

noncomputable def Ns222p2163 := @Enclosure.Real.IsNear.of_eq qz802 (hardyZApproximantRS₀ qz27) Bool.false 3565644088629970728569 590295810358705651712 28380354784211773180457 Ns222p185 

noncomputable def Ns222p2164 := @Enclosure.Real.IsNear.pos_val qz802 3565644088629970728569 590295810358705651712 28380354784211773180457 Ns222p185 (Ns222p2163 (RS223to240.d42 qz3 qz27 qz268) RS223to240.d43) rfl 

noncomputable def Ns222p2165 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz801 qz3 qz3 506327 1000 506327 1000 

noncomputable def Ns222p2166 := @Enclosure.norm_gt_of_isNear qz801 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 9703756050334815151 18446744073709551616 1039976065833158020919 

noncomputable def Ns222p2167 := @Ns222p2166 783986623132655943680000 39846649 536870912 1421 2684354560 (Ns222p2161 (RS223to240.d4 qz3 qz27 qz268) RS223to240.d41) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2168 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz802 qz3 qz27 506327 1000 507758 1000 

noncomputable def Ns222p2169 := @Enclosure.norm_gt_of_isNear qz802 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 3565644088629970728569 590295810358705651712 28380354784211773180457 

noncomputable def Ns222p2170 := @Ns222p2169 Ns222p185 39846649 536870912 1421 2684354560 (Ns222p2163 (RS223to240.d42 qz3 qz27 qz268) RS223to240.d43) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2171 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz267 (@BSN.thirtyTwoPi_le_dec qz3 506327 1000 qz10 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz801 qz802 (Ns222p2162 rfl rfl) (Ns222p2164 rfl rfl)) (Ns222p2165 qz10 qz10 rfl rfl rfl rfl (Ns222p2167 rfl)) (Ns222p2168 qz10 qz30 rfl rfl rfl rfl (Ns222p2170 rfl)) 

noncomputable abbrev qz269 := (RS223to240.d3 qz378 qz400 (@Enclosure.dec_le_dec qz378 qz400 507758 1000 509188 1000 qz382 qz403 rfl rfl rfl))

noncomputable abbrev qz803 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz269)

noncomputable def Ns222p2172 := @Enclosure.Real.IsNear.of_eq qz803 (hardyZApproximantRS₀ qz27) Bool.false 3565644088629970728569 590295810358705651712 28380354784211773180457 Ns222p185 

noncomputable abbrev qz270 := (@Enclosure.dec_le_dec qz378 qz400 507758 1000 509188 1000 qz382 qz403 rfl rfl rfl)

noncomputable def Ns222p2173 := @Enclosure.Real.IsNear.pos_val qz803 3565644088629970728569 590295810358705651712 28380354784211773180457 Ns222p185 (Ns222p2172 (RS223to240.d4 qz27 qz47 qz270) RS223to240.d43) rfl 

noncomputable abbrev qz804 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz269)

noncomputable def Ns222p2174 := @Enclosure.Real.IsNear.of_eq qz804 (hardyZApproximantRS₀ qz47) Bool.true 4765694910278864980647 2361183241434822606848 7300102652745325262019 Ns222p328 

noncomputable def Ns222p2175 := @Enclosure.Real.IsNear.neg_val qz804 4765694910278864980647 2361183241434822606848 7300102652745325262019 Ns222p328 (Ns222p2174 (RS223to240.d42 qz27 qz47 qz270) RS223to240.d49) rfl 

noncomputable def Ns222p2176 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz803 qz3 qz27 506327 1000 507758 1000 

noncomputable def Ns222p2177 := @Enclosure.norm_gt_of_isNear qz803 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 3565644088629970728569 590295810358705651712 28380354784211773180457 

noncomputable def Ns222p2178 := @Ns222p2177 Ns222p185 39846649 536870912 1421 2684354560 (Ns222p2172 (RS223to240.d4 qz27 qz47 qz270) RS223to240.d43) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2179 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz804 qz3 qz47 506327 1000 509188 1000 

noncomputable def Ns222p2180 := @Enclosure.norm_gt_of_isNear qz804 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 4765694910278864980647 2361183241434822606848 7300102652745325262019 

noncomputable def Ns222p2181 := @Ns222p2180 Ns222p328 39846649 536870912 1421 2684354560 (Ns222p2174 (RS223to240.d42 qz27 qz47 qz270) RS223to240.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2182 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz269 (@BSN.thirtyTwoPi_le_dec qz27 507758 1000 qz30 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz803 qz804 (Ns222p2173 rfl rfl) (Ns222p2175 rfl rfl)) (Ns222p2176 qz10 qz30 rfl rfl rfl rfl (Ns222p2178 rfl)) (Ns222p2179 qz10 qz51 rfl rfl rfl rfl (Ns222p2181 rfl)) 

noncomputable abbrev qz271 := (RS223to240.d3 qz400 qz414 (@Enclosure.dec_le_dec qz400 qz414 509188 1000 510617 1000 qz403 qz417 rfl rfl rfl))

noncomputable abbrev qz805 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz271)

noncomputable def Ns222p2183 := @Enclosure.Real.IsNear.of_eq qz805 (hardyZApproximantRS₀ qz47) Bool.true 4765694910278864980647 2361183241434822606848 7300102652745325262019 Ns222p328 

noncomputable abbrev qz272 := (@Enclosure.dec_le_dec qz400 qz414 509188 1000 510617 1000 qz403 qz417 rfl rfl rfl)

noncomputable def Ns222p2184 := @Enclosure.Real.IsNear.neg_val qz805 4765694910278864980647 2361183241434822606848 7300102652745325262019 Ns222p328 (Ns222p2183 (RS223to240.d4 qz47 qz62 qz272) RS223to240.d49) rfl 

noncomputable abbrev qz806 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz271)

noncomputable def Ns222p2185 := @Enclosure.Real.IsNear.of_eq qz806 (hardyZApproximantRS₀ qz62) Bool.false 1243463128979781572169 1180591620717411303424 311093225479669657895717 Ns222p433 

noncomputable def Ns222p2186 := @Enclosure.Real.IsNear.pos_val qz806 1243463128979781572169 1180591620717411303424 311093225479669657895717 Ns222p433 (Ns222p2185 (RS223to240.d42 qz47 qz62 qz272) RS223to240.d50) rfl 

noncomputable def Ns222p2187 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz805 qz3 qz47 506327 1000 509188 1000 

noncomputable def Ns222p2188 := @Enclosure.norm_gt_of_isNear qz805 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 4765694910278864980647 2361183241434822606848 7300102652745325262019 

noncomputable def Ns222p2189 := @Ns222p2188 Ns222p328 39846649 536870912 1421 2684354560 (Ns222p2183 (RS223to240.d4 qz47 qz62 qz272) RS223to240.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2190 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz806 qz3 qz62 506327 1000 510617 1000 

noncomputable def Ns222p2191 := @Enclosure.norm_gt_of_isNear qz806 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 1243463128979781572169 1180591620717411303424 311093225479669657895717 

noncomputable def Ns222p2192 := @Ns222p2191 Ns222p433 39846649 536870912 1421 2684354560 (Ns222p2185 (RS223to240.d42 qz47 qz62 qz272) RS223to240.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2193 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz271 (@BSN.thirtyTwoPi_le_dec qz47 509188 1000 qz51 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz805 qz806 (Ns222p2184 rfl rfl) (Ns222p2186 rfl rfl)) (Ns222p2187 qz10 qz51 rfl rfl rfl rfl (Ns222p2189 rfl)) (Ns222p2190 qz10 qz65 rfl rfl rfl rfl (Ns222p2192 rfl)) 

noncomputable abbrev qz273 := (RS223to240.d3 qz414 qz426 (@Enclosure.dec_le_dec qz414 qz426 510617 1000 512045 1000 qz417 qz429 rfl rfl rfl))

noncomputable abbrev qz807 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz273)

noncomputable def Ns222p2194 := @Enclosure.Real.IsNear.of_eq qz807 (hardyZApproximantRS₀ qz62) Bool.false 1243463128979781572169 1180591620717411303424 311093225479669657895717 Ns222p433 

noncomputable abbrev qz274 := (@Enclosure.dec_le_dec qz414 qz426 510617 1000 512045 1000 qz417 qz429 rfl rfl rfl)

noncomputable def Ns222p2195 := @Enclosure.Real.IsNear.pos_val qz807 1243463128979781572169 1180591620717411303424 311093225479669657895717 Ns222p433 (Ns222p2194 (RS223to240.d4 qz62 qz75 qz274) RS223to240.d50) rfl 

noncomputable abbrev qz808 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz273)

noncomputable def Ns222p2196 := @Enclosure.Real.IsNear.of_eq qz808 (hardyZApproximantRS₀ qz75) Bool.true 211391144657476931263 295147905179352825856 77986419164945249586703 Ns222p542 

noncomputable def Ns222p2197 := @Enclosure.Real.IsNear.neg_val qz808 211391144657476931263 295147905179352825856 77986419164945249586703 Ns222p542 (Ns222p2196 (RS223to240.d42 qz62 qz75 qz274) RS223to240.d51) rfl 

noncomputable def Ns222p2198 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz807 qz3 qz62 506327 1000 510617 1000 

noncomputable def Ns222p2199 := @Enclosure.norm_gt_of_isNear qz807 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 1243463128979781572169 1180591620717411303424 311093225479669657895717 

noncomputable def Ns222p2200 := @Ns222p2199 Ns222p433 39846649 536870912 1421 2684354560 (Ns222p2194 (RS223to240.d4 qz62 qz75 qz274) RS223to240.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2201 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz808 qz3 qz75 506327 1000 512045 1000 

noncomputable def Ns222p2202 := @Enclosure.norm_gt_of_isNear qz808 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 211391144657476931263 295147905179352825856 77986419164945249586703 

noncomputable def Ns222p2203 := @Ns222p2202 Ns222p542 39846649 536870912 1421 2684354560 (Ns222p2196 (RS223to240.d42 qz62 qz75 qz274) RS223to240.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2204 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz273 (@BSN.thirtyTwoPi_le_dec qz62 510617 1000 qz65 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz807 qz808 (Ns222p2195 rfl rfl) (Ns222p2197 rfl rfl)) (Ns222p2198 qz10 qz65 rfl rfl rfl rfl (Ns222p2200 rfl)) (Ns222p2201 qz10 qz78 rfl rfl rfl rfl (Ns222p2203 rfl)) 

noncomputable abbrev qz275 := (RS223to240.d3 qz426 qz438 (@Enclosure.dec_le_dec qz426 qz438 512045 1000 513472 1000 qz429 qz441 rfl rfl rfl))

noncomputable abbrev qz809 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz275)

noncomputable def Ns222p2205 := @Enclosure.Real.IsNear.of_eq qz809 (hardyZApproximantRS₀ qz75) Bool.true 211391144657476931263 295147905179352825856 77986419164945249586703 Ns222p542 

noncomputable abbrev qz276 := (@Enclosure.dec_le_dec qz426 qz438 512045 1000 513472 1000 qz429 qz441 rfl rfl rfl)

noncomputable def Ns222p2206 := @Enclosure.Real.IsNear.neg_val qz809 211391144657476931263 295147905179352825856 77986419164945249586703 Ns222p542 (Ns222p2205 (RS223to240.d4 qz75 qz88 qz276) RS223to240.d51) rfl 

noncomputable abbrev qz810 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz275)

noncomputable def Ns222p2207 := @Enclosure.Real.IsNear.of_eq qz810 (hardyZApproximantRS₀ qz88) Bool.false 323922911452580522725 590295810358705651712 6256530836436021815687 Ns222p650 

noncomputable def Ns222p2208 := @Enclosure.Real.IsNear.pos_val qz810 323922911452580522725 590295810358705651712 6256530836436021815687 Ns222p650 (Ns222p2207 (RS223to240.d42 qz75 qz88 qz276) RS223to240.d52) rfl 

noncomputable def Ns222p2209 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz809 qz3 qz75 506327 1000 512045 1000 

noncomputable def Ns222p2210 := @Enclosure.norm_gt_of_isNear qz809 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 211391144657476931263 295147905179352825856 77986419164945249586703 

noncomputable def Ns222p2211 := @Ns222p2210 Ns222p542 39846649 536870912 1421 2684354560 (Ns222p2205 (RS223to240.d4 qz75 qz88 qz276) RS223to240.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2212 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz810 qz3 qz88 506327 1000 513472 1000 

noncomputable def Ns222p2213 := @Enclosure.norm_gt_of_isNear qz810 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 323922911452580522725 590295810358705651712 6256530836436021815687 

noncomputable def Ns222p2214 := @Ns222p2213 Ns222p650 39846649 536870912 1421 2684354560 (Ns222p2207 (RS223to240.d42 qz75 qz88 qz276) RS223to240.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2215 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz275 (@BSN.thirtyTwoPi_le_dec qz75 512045 1000 qz78 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz809 qz810 (Ns222p2206 rfl rfl) (Ns222p2208 rfl rfl)) (Ns222p2209 qz10 qz78 rfl rfl rfl rfl (Ns222p2211 rfl)) (Ns222p2212 qz10 qz91 rfl rfl rfl rfl (Ns222p2214 rfl)) 

noncomputable abbrev qz277 := (RS223to240.d3 qz438 qz450 (@Enclosure.dec_le_dec qz438 qz450 513472 1000 514899 1000 qz441 qz453 rfl rfl rfl))

noncomputable abbrev qz811 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz277)

noncomputable def Ns222p2216 := @Enclosure.Real.IsNear.of_eq qz811 (hardyZApproximantRS₀ qz88) Bool.false 323922911452580522725 590295810358705651712 6256530836436021815687 Ns222p650 

noncomputable abbrev qz278 := (@Enclosure.dec_le_dec qz438 qz450 513472 1000 514899 1000 qz441 qz453 rfl rfl rfl)

noncomputable def Ns222p2217 := @Enclosure.Real.IsNear.pos_val qz811 323922911452580522725 590295810358705651712 6256530836436021815687 Ns222p650 (Ns222p2216 (RS223to240.d4 qz88 qz101 qz278) RS223to240.d52) rfl 

noncomputable abbrev qz812 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz277)

noncomputable def Ns222p2218 := @Enclosure.Real.IsNear.of_eq qz812 (hardyZApproximantRS₀ qz101) Bool.true 3452695215562222359395 1180591620717411303424 12550551507324364524161 Ns222p760 

noncomputable def Ns222p2219 := @Enclosure.Real.IsNear.neg_val qz812 3452695215562222359395 1180591620717411303424 12550551507324364524161 Ns222p760 (Ns222p2218 (RS223to240.d42 qz88 qz101 qz278) RS223to240.d53) rfl 

noncomputable def Ns222p2220 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz811 qz3 qz88 506327 1000 513472 1000 

noncomputable def Ns222p2221 := @Enclosure.norm_gt_of_isNear qz811 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 323922911452580522725 590295810358705651712 6256530836436021815687 

noncomputable def Ns222p2222 := @Ns222p2221 Ns222p650 39846649 536870912 1421 2684354560 (Ns222p2216 (RS223to240.d4 qz88 qz101 qz278) RS223to240.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2223 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz812 qz3 qz101 506327 1000 514899 1000 

noncomputable def Ns222p2224 := @Enclosure.norm_gt_of_isNear qz812 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 3452695215562222359395 1180591620717411303424 12550551507324364524161 

noncomputable def Ns222p2225 := @Ns222p2224 Ns222p760 39846649 536870912 1421 2684354560 (Ns222p2218 (RS223to240.d42 qz88 qz101 qz278) RS223to240.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2226 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz277 (@BSN.thirtyTwoPi_le_dec qz88 513472 1000 qz91 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz811 qz812 (Ns222p2217 rfl rfl) (Ns222p2219 rfl rfl)) (Ns222p2220 qz10 qz91 rfl rfl rfl rfl (Ns222p2222 rfl)) (Ns222p2223 qz10 qz104 rfl rfl rfl rfl (Ns222p2225 rfl)) 

noncomputable abbrev qz606 := (@Enclosure.dec_le_dec qz685 qz693 514899 1000 516325 1000 (@Eq.refl Real qz685) (@Eq.refl Real qz693) rfl rfl rfl)

noncomputable abbrev qz279 := (RS223to240.d3 qz450 qz462 qz606)

noncomputable abbrev qz813 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz279)

noncomputable def Ns222p2227 := @Enclosure.Real.IsNear.of_eq qz813 (hardyZApproximantRS₀ qz101) Bool.true 3452695215562222359395 1180591620717411303424 12550551507324364524161 Ns222p760 

noncomputable abbrev qz280 := qz606

noncomputable def Ns222p2228 := @Enclosure.Real.IsNear.neg_val qz813 3452695215562222359395 1180591620717411303424 12550551507324364524161 Ns222p760 (Ns222p2227 (RS223to240.d4 qz101 qz114 qz280) RS223to240.d53) rfl 

noncomputable abbrev qz814 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz279)

noncomputable def Ns222p2229 := @Enclosure.Real.IsNear.of_eq qz814 (hardyZApproximantRS₀ qz114) Bool.false 2853057311497198723319 590295810358705651712 157347262085118387022401 Ns222p874 

noncomputable def Ns222p2230 := @Enclosure.Real.IsNear.pos_val qz814 2853057311497198723319 590295810358705651712 157347262085118387022401 Ns222p874 (Ns222p2229 (RS223to240.d42 qz101 qz114 qz280) RS223to240.d54) rfl 

noncomputable def Ns222p2231 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz813 qz3 qz101 506327 1000 514899 1000 

noncomputable def Ns222p2232 := @Enclosure.norm_gt_of_isNear qz813 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 3452695215562222359395 1180591620717411303424 12550551507324364524161 

noncomputable def Ns222p2233 := @Ns222p2232 Ns222p760 39846649 536870912 1421 2684354560 (Ns222p2227 (RS223to240.d4 qz101 qz114 qz280) RS223to240.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2234 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz814 qz3 qz114 506327 1000 516325 1000 

noncomputable def Ns222p2235 := @Enclosure.norm_gt_of_isNear qz814 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 2853057311497198723319 590295810358705651712 157347262085118387022401 

noncomputable def Ns222p2236 := @Ns222p2235 Ns222p874 39846649 536870912 1421 2684354560 (Ns222p2229 (RS223to240.d42 qz101 qz114 qz280) RS223to240.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2237 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz279 (@BSN.thirtyTwoPi_le_dec qz101 514899 1000 qz104 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz813 qz814 (Ns222p2228 rfl rfl) (Ns222p2230 rfl rfl)) (Ns222p2231 qz10 qz104 rfl rfl rfl rfl (Ns222p2233 rfl)) (Ns222p2234 qz10 qz117 rfl rfl rfl rfl (Ns222p2236 rfl)) 

noncomputable abbrev qz607 := (@Enclosure.dec_le_dec qz693 qz702 516325 1000 517749 1000 (@Eq.refl Real qz693) qz706 rfl rfl rfl)

noncomputable abbrev qz281 := (RS223to240.d3 qz462 qz474 qz607)

noncomputable abbrev qz815 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz281)

noncomputable def Ns222p2238 := @Enclosure.Real.IsNear.of_eq qz815 (hardyZApproximantRS₀ qz114) Bool.false 2853057311497198723319 590295810358705651712 157347262085118387022401 Ns222p874 

noncomputable abbrev qz282 := qz607

noncomputable def Ns222p2239 := @Enclosure.Real.IsNear.pos_val qz815 2853057311497198723319 590295810358705651712 157347262085118387022401 Ns222p874 (Ns222p2238 (RS223to240.d4 qz114 qz127 qz282) RS223to240.d54) rfl 

noncomputable abbrev qz816 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz281)

noncomputable def Ns222p2240 := @Enclosure.Real.IsNear.of_eq qz816 (hardyZApproximantRS₀ qz127) Bool.true 7171163943975227939 18446744073709551616 15780107695729769329649 Ns222p978 

noncomputable def Ns222p2241 := @Enclosure.Real.IsNear.neg_val qz816 7171163943975227939 18446744073709551616 15780107695729769329649 Ns222p978 (Ns222p2240 (RS223to240.d42 qz114 qz127 qz282) RS223to240.d55) rfl 

noncomputable def Ns222p2242 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz815 qz3 qz114 506327 1000 516325 1000 

noncomputable def Ns222p2243 := @Enclosure.norm_gt_of_isNear qz815 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 2853057311497198723319 590295810358705651712 157347262085118387022401 

noncomputable def Ns222p2244 := @Ns222p2243 Ns222p874 39846649 536870912 1421 2684354560 (Ns222p2238 (RS223to240.d4 qz114 qz127 qz282) RS223to240.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2245 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz816 qz3 qz127 506327 1000 517749 1000 

noncomputable def Ns222p2246 := @Enclosure.norm_gt_of_isNear qz816 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 7171163943975227939 18446744073709551616 15780107695729769329649 

noncomputable def Ns222p2247 := @Ns222p2246 Ns222p978 39846649 536870912 1421 2684354560 (Ns222p2240 (RS223to240.d42 qz114 qz127 qz282) RS223to240.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2248 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz281 (@BSN.thirtyTwoPi_le_dec qz114 516325 1000 qz117 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz815 qz816 (Ns222p2239 rfl rfl) (Ns222p2241 rfl rfl)) (Ns222p2242 qz10 qz117 rfl rfl rfl rfl (Ns222p2244 rfl)) (Ns222p2245 qz10 qz130 rfl rfl rfl rfl (Ns222p2247 rfl)) 

noncomputable abbrev qz608 := (@Enclosure.dec_le_dec qz702 qz711 517749 1000 519173 1000 qz706 qz715 rfl rfl rfl)

noncomputable abbrev qz283 := (RS223to240.d3 qz474 qz486 qz608)

noncomputable abbrev qz817 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz283)

noncomputable def Ns222p2249 := @Enclosure.Real.IsNear.of_eq qz817 (hardyZApproximantRS₀ qz127) Bool.true 7171163943975227939 18446744073709551616 15780107695729769329649 Ns222p978 

noncomputable abbrev qz284 := qz608

noncomputable def Ns222p2250 := @Enclosure.Real.IsNear.neg_val qz817 7171163943975227939 18446744073709551616 15780107695729769329649 Ns222p978 (Ns222p2249 (RS223to240.d4 qz127 qz140 qz284) RS223to240.d55) rfl 

noncomputable abbrev qz818 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz283)

noncomputable def Ns222p2251 := @Enclosure.Real.IsNear.of_eq qz818 (hardyZApproximantRS₀ qz140) Bool.false 1652054073490395109403 590295810358705651712 158243588636849743891649 Ns222p874 

noncomputable def Ns222p2252 := @Enclosure.Real.IsNear.pos_val qz818 1652054073490395109403 590295810358705651712 158243588636849743891649 Ns222p874 (Ns222p2251 (RS223to240.d42 qz127 qz140 qz284) RS223to240.d56) rfl 

noncomputable def Ns222p2253 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz817 qz3 qz127 506327 1000 517749 1000 

noncomputable def Ns222p2254 := @Enclosure.norm_gt_of_isNear qz817 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 7171163943975227939 18446744073709551616 15780107695729769329649 

noncomputable def Ns222p2255 := @Ns222p2254 Ns222p978 39846649 536870912 1421 2684354560 (Ns222p2249 (RS223to240.d4 qz127 qz140 qz284) RS223to240.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2256 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz818 qz3 qz140 506327 1000 519173 1000 

noncomputable def Ns222p2257 := @Enclosure.norm_gt_of_isNear qz818 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 1652054073490395109403 590295810358705651712 158243588636849743891649 

noncomputable def Ns222p2258 := @Ns222p2257 Ns222p874 39846649 536870912 1421 2684354560 (Ns222p2251 (RS223to240.d42 qz127 qz140 qz284) RS223to240.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2259 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz283 (@BSN.thirtyTwoPi_le_dec qz127 517749 1000 qz130 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz817 qz818 (Ns222p2250 rfl rfl) (Ns222p2252 rfl rfl)) (Ns222p2253 qz10 qz130 rfl rfl rfl rfl (Ns222p2255 rfl)) (Ns222p2256 qz10 qz143 rfl rfl rfl rfl (Ns222p2258 rfl)) 

noncomputable abbrev qz819 := (@Enclosure.dec_le_dec qz887 qz891 519173 1000 520596 1000 (@Eq.refl Real qz887) qz894 rfl rfl rfl)

noncomputable abbrev qz609 := qz819

noncomputable abbrev qz285 := (RS223to240.d3 qz486 qz498 qz609)

noncomputable abbrev qz820 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz285)

noncomputable def Ns222p2260 := @Enclosure.Real.IsNear.of_eq qz820 (hardyZApproximantRS₀ qz140) Bool.false 1652054073490395109403 590295810358705651712 158243588636849743891649 Ns222p874 

noncomputable abbrev qz286 := qz609

noncomputable def Ns222p2261 := @Enclosure.Real.IsNear.pos_val qz820 1652054073490395109403 590295810358705651712 158243588636849743891649 Ns222p874 (Ns222p2260 (RS223to240.d4 qz140 qz153 qz286) RS223to240.d56) rfl 

noncomputable abbrev qz821 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz285)

noncomputable def Ns222p2262 := @Enclosure.Real.IsNear.of_eq qz821 (hardyZApproximantRS₀ qz153) Bool.true 1765013028728884286001 1180591620717411303424 317516204979178021677761 Ns222p433 

noncomputable def Ns222p2263 := @Enclosure.Real.IsNear.neg_val qz821 1765013028728884286001 1180591620717411303424 317516204979178021677761 Ns222p433 (Ns222p2262 (RS223to240.d42 qz140 qz153 qz286) RS223to240.d57) rfl 

noncomputable def Ns222p2264 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz820 qz3 qz140 506327 1000 519173 1000 

noncomputable def Ns222p2265 := @Enclosure.norm_gt_of_isNear qz820 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 1652054073490395109403 590295810358705651712 158243588636849743891649 

noncomputable def Ns222p2266 := @Ns222p2265 Ns222p874 39846649 536870912 1421 2684354560 (Ns222p2260 (RS223to240.d4 qz140 qz153 qz286) RS223to240.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2267 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz821 qz3 qz153 506327 1000 520596 1000 

noncomputable def Ns222p2268 := @Enclosure.norm_gt_of_isNear qz821 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 1765013028728884286001 1180591620717411303424 317516204979178021677761 

noncomputable def Ns222p2269 := @Ns222p2268 Ns222p433 39846649 536870912 1421 2684354560 (Ns222p2262 (RS223to240.d42 qz140 qz153 qz286) RS223to240.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2270 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz285 (@BSN.thirtyTwoPi_le_dec qz140 519173 1000 qz143 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz820 qz821 (Ns222p2261 rfl rfl) (Ns222p2263 rfl rfl)) (Ns222p2264 qz10 qz143 rfl rfl rfl rfl (Ns222p2266 rfl)) (Ns222p2267 qz10 qz156 rfl rfl rfl rfl (Ns222p2269 rfl)) 

noncomputable abbrev qz930 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 520596 1000) (Enclosure.sfrac Bool.false 522018 1000) 520596 1000 522018 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 520596 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 522018 1000)) rfl rfl rfl)

noncomputable abbrev qz822 := qz930

noncomputable abbrev qz610 := qz822

noncomputable abbrev qz287 := (RS223to240.d3 qz498 qz510 qz610)

noncomputable abbrev qz823 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz287)

noncomputable def Ns222p2271 := @Enclosure.Real.IsNear.of_eq qz823 (hardyZApproximantRS₀ qz153) Bool.true 1765013028728884286001 1180591620717411303424 317516204979178021677761 Ns222p433 

noncomputable abbrev qz288 := qz610

noncomputable def Ns222p2272 := @Enclosure.Real.IsNear.neg_val qz823 1765013028728884286001 1180591620717411303424 317516204979178021677761 Ns222p433 (Ns222p2271 (RS223to240.d4 qz153 qz166 qz288) RS223to240.d57) rfl 

noncomputable abbrev qz824 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz287)

noncomputable def Ns222p2273 := @Enclosure.Real.IsNear.of_eq qz824 (hardyZApproximantRS₀ qz166) Bool.false 101591419246576943317 147573952589676412928 159259258512873876186389 Ns222p874 

noncomputable def Ns222p2274 := @Enclosure.Real.IsNear.pos_val qz824 101591419246576943317 147573952589676412928 159259258512873876186389 Ns222p874 (Ns222p2273 (RS223to240.d42 qz153 qz166 qz288) RS223to240.d58) rfl 

noncomputable def Ns222p2275 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz823 qz3 qz153 506327 1000 520596 1000 

noncomputable def Ns222p2276 := @Enclosure.norm_gt_of_isNear qz823 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 1765013028728884286001 1180591620717411303424 317516204979178021677761 

noncomputable def Ns222p2277 := @Ns222p2276 Ns222p433 39846649 536870912 1421 2684354560 (Ns222p2271 (RS223to240.d4 qz153 qz166 qz288) RS223to240.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2278 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz824 qz3 qz166 506327 1000 522018 1000 

noncomputable def Ns222p2279 := @Enclosure.norm_gt_of_isNear qz824 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 101591419246576943317 147573952589676412928 159259258512873876186389 

noncomputable def Ns222p2280 := @Ns222p2279 Ns222p874 39846649 536870912 1421 2684354560 (Ns222p2273 (RS223to240.d42 qz153 qz166 qz288) RS223to240.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2281 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz287 (@BSN.thirtyTwoPi_le_dec qz153 520596 1000 qz156 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz823 qz824 (Ns222p2272 rfl rfl) (Ns222p2274 rfl rfl)) (Ns222p2275 qz10 qz156 rfl rfl rfl rfl (Ns222p2277 rfl)) (Ns222p2278 qz10 qz169 rfl rfl rfl rfl (Ns222p2280 rfl)) 

noncomputable abbrev qz289 := (RS223to240.d3 qz510 qz522 (@Enclosure.dec_le_dec qz510 qz522 522018 1000 523439 1000 qz513 qz525 rfl rfl rfl))

noncomputable abbrev qz825 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz289)

noncomputable def Ns222p2282 := @Enclosure.Real.IsNear.of_eq qz825 (hardyZApproximantRS₀ qz166) Bool.false 101591419246576943317 147573952589676412928 159259258512873876186389 Ns222p874 

noncomputable abbrev qz290 := (@Enclosure.dec_le_dec qz510 qz522 522018 1000 523439 1000 qz513 qz525 rfl rfl rfl)

noncomputable def Ns222p2283 := @Enclosure.Real.IsNear.pos_val qz825 101591419246576943317 147573952589676412928 159259258512873876186389 Ns222p874 (Ns222p2282 (RS223to240.d4 qz166 qz179 qz290) RS223to240.d58) rfl 

noncomputable abbrev qz826 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz289)

noncomputable def Ns222p2284 := @Enclosure.Real.IsNear.of_eq qz826 (hardyZApproximantRS₀ qz179) Bool.true 3647784099200239551 2305843009213693952 3994173593944946447 2665554518651030208512 

noncomputable def Ns222p2285 := @Enclosure.Real.IsNear.neg_val qz826 3647784099200239551 2305843009213693952 3994173593944946447 2665554518651030208512 (Ns222p2284 (RS223to240.d42 qz166 qz179 qz290) RS223to240.d59) rfl 

noncomputable def Ns222p2286 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz825 qz3 qz166 506327 1000 522018 1000 

noncomputable def Ns222p2287 := @Enclosure.norm_gt_of_isNear qz825 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 101591419246576943317 147573952589676412928 159259258512873876186389 

noncomputable def Ns222p2288 := @Ns222p2287 Ns222p874 39846649 536870912 1421 2684354560 (Ns222p2282 (RS223to240.d4 qz166 qz179 qz290) RS223to240.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2289 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz826 qz3 qz179 506327 1000 523439 1000 

noncomputable def Ns222p2290 := @Enclosure.norm_gt_of_isNear qz826 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 3647784099200239551 2305843009213693952 3994173593944946447 

noncomputable def Ns222p2291 := @Ns222p2290 2665554518651030208512 39846649 536870912 1421 2684354560 (Ns222p2284 (RS223to240.d42 qz166 qz179 qz290) RS223to240.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2292 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz289 (@BSN.thirtyTwoPi_le_dec qz166 522018 1000 qz169 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz825 qz826 (Ns222p2283 rfl rfl) (Ns222p2285 rfl rfl)) (Ns222p2286 qz10 qz169 rfl rfl rfl rfl (Ns222p2288 rfl)) (Ns222p2289 qz10 qz182 rfl rfl rfl rfl (Ns222p2291 rfl)) 

noncomputable abbrev qz291 := (RS223to240.d3 qz522 qz534 (@Enclosure.dec_le_dec qz522 qz534 523439 1000 524859 1000 qz525 qz537 rfl rfl rfl))

noncomputable abbrev qz827 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz291)

noncomputable def Ns222p2293 := @Enclosure.Real.IsNear.of_eq qz827 (hardyZApproximantRS₀ qz179) Bool.true 3647784099200239551 2305843009213693952 3994173593944946447 2665554518651030208512 

noncomputable abbrev qz292 := (@Enclosure.dec_le_dec qz522 qz534 523439 1000 524859 1000 qz525 qz537 rfl rfl rfl)

noncomputable def Ns222p2294 := @Enclosure.Real.IsNear.neg_val qz827 3647784099200239551 2305843009213693952 3994173593944946447 2665554518651030208512 (Ns222p2293 (RS223to240.d4 qz179 qz192 qz292) RS223to240.d59) rfl 

noncomputable abbrev qz828 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz291)

noncomputable def Ns222p2295 := @Enclosure.Real.IsNear.of_eq qz828 (hardyZApproximantRS₀ qz192) Bool.false 4902168584707310441 4611686018427387904 160261300152323586876287 Ns222p874 

noncomputable def Ns222p2296 := @Enclosure.Real.IsNear.pos_val qz828 4902168584707310441 4611686018427387904 160261300152323586876287 Ns222p874 (Ns222p2295 (RS223to240.d42 qz179 qz192 qz292) RS223to240.d60) rfl 

noncomputable def Ns222p2297 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz827 qz3 qz179 506327 1000 523439 1000 

noncomputable def Ns222p2298 := @Enclosure.norm_gt_of_isNear qz827 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 3647784099200239551 2305843009213693952 3994173593944946447 

noncomputable def Ns222p2299 := @Ns222p2298 2665554518651030208512 39846649 536870912 1421 2684354560 (Ns222p2293 (RS223to240.d4 qz179 qz192 qz292) RS223to240.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2300 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz828 qz3 qz192 506327 1000 524859 1000 

noncomputable def Ns222p2301 := @Enclosure.norm_gt_of_isNear qz828 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 4902168584707310441 4611686018427387904 160261300152323586876287 

noncomputable def Ns222p2302 := @Ns222p2301 Ns222p874 39846649 536870912 1421 2684354560 (Ns222p2295 (RS223to240.d42 qz179 qz192 qz292) RS223to240.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2303 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz291 (@BSN.thirtyTwoPi_le_dec qz179 523439 1000 qz182 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz827 qz828 (Ns222p2294 rfl rfl) (Ns222p2296 rfl rfl)) (Ns222p2297 qz10 qz182 rfl rfl rfl rfl (Ns222p2299 rfl)) (Ns222p2300 qz10 qz195 rfl rfl rfl rfl (Ns222p2302 rfl)) 

noncomputable abbrev qz611 := (@Enclosure.dec_le_dec qz747 qz755 524859 1000 527077 1000 (@Eq.refl Real qz747) (@Eq.refl Real qz755) rfl rfl rfl)

noncomputable abbrev qz293 := (RS223to240.d3 qz534 qz546 qz611)

noncomputable abbrev qz829 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz293)

noncomputable def Ns222p2304 := @Enclosure.Real.IsNear.of_eq qz829 (hardyZApproximantRS₀ qz192) Bool.false 4902168584707310441 4611686018427387904 160261300152323586876287 Ns222p874 

noncomputable abbrev qz294 := qz611

noncomputable def Ns222p2305 := @Enclosure.Real.IsNear.pos_val qz829 4902168584707310441 4611686018427387904 160261300152323586876287 Ns222p874 (Ns222p2304 (RS223to240.d4 qz192 qz205 qz294) RS223to240.d60) rfl 

noncomputable abbrev qz830 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz293)

noncomputable def Ns222p2306 := @Enclosure.Real.IsNear.of_eq qz830 (hardyZApproximantRS₀ qz205) Bool.true 10924830822612665531959 2361183241434822606848 7585641822573578315659 Ns222p328 

noncomputable def Ns222p2307 := @Enclosure.Real.IsNear.neg_val qz830 10924830822612665531959 2361183241434822606848 7585641822573578315659 Ns222p328 (Ns222p2306 (RS223to240.d42 qz192 qz205 qz294) RS223to240.d61) rfl 

noncomputable def Ns222p2308 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz829 qz3 qz192 506327 1000 524859 1000 

noncomputable def Ns222p2309 := @Enclosure.norm_gt_of_isNear qz829 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 4902168584707310441 4611686018427387904 160261300152323586876287 

noncomputable def Ns222p2310 := @Ns222p2309 Ns222p874 39846649 536870912 1421 2684354560 (Ns222p2304 (RS223to240.d4 qz192 qz205 qz294) RS223to240.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2311 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz830 qz3 qz205 506327 1000 527077 1000 

noncomputable def Ns222p2312 := @Enclosure.norm_gt_of_isNear qz830 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 10924830822612665531959 2361183241434822606848 7585641822573578315659 

noncomputable def Ns222p2313 := @Ns222p2312 Ns222p328 39846649 536870912 1421 2684354560 (Ns222p2306 (RS223to240.d42 qz192 qz205 qz294) RS223to240.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2314 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz293 (@BSN.thirtyTwoPi_le_dec qz192 524859 1000 qz195 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz829 qz830 (Ns222p2305 rfl rfl) (Ns222p2307 rfl rfl)) (Ns222p2308 qz10 qz195 rfl rfl rfl rfl (Ns222p2310 rfl)) (Ns222p2311 qz10 qz208 rfl rfl rfl rfl (Ns222p2313 rfl)) 

noncomputable abbrev qz612 := (@Enclosure.dec_le_dec qz755 qz763 527077 1000 528141 1000 (@Eq.refl Real qz755) qz767 rfl rfl rfl)

noncomputable abbrev qz295 := (RS223to240.d3 qz546 qz558 qz612)

noncomputable abbrev qz831 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz295)

noncomputable def Ns222p2315 := @Enclosure.Real.IsNear.of_eq qz831 (hardyZApproximantRS₀ qz205) Bool.true 10924830822612665531959 2361183241434822606848 7585641822573578315659 Ns222p328 

noncomputable abbrev qz296 := qz612

noncomputable def Ns222p2316 := @Enclosure.Real.IsNear.neg_val qz831 10924830822612665531959 2361183241434822606848 7585641822573578315659 Ns222p328 (Ns222p2315 (RS223to240.d4 qz205 qz218 qz296) RS223to240.d61) rfl 

noncomputable abbrev qz832 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz295)

noncomputable def Ns222p2317 := @Enclosure.Real.IsNear.of_eq qz832 (hardyZApproximantRS₀ qz218) Bool.false 581175869775883725545 2361183241434822606848 646440225718375362206983 Ns222p1723 

noncomputable def Ns222p2318 := @Enclosure.Real.IsNear.pos_val qz832 581175869775883725545 2361183241434822606848 646440225718375362206983 Ns222p1723 (Ns222p2317 (RS223to240.d42 qz205 qz218 qz296) RS223to240.d62) rfl 

noncomputable def Ns222p2319 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz831 qz3 qz205 506327 1000 527077 1000 

noncomputable def Ns222p2320 := @Enclosure.norm_gt_of_isNear qz831 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 10924830822612665531959 2361183241434822606848 7585641822573578315659 

noncomputable def Ns222p2321 := @Ns222p2320 Ns222p328 39846649 536870912 1421 2684354560 (Ns222p2315 (RS223to240.d4 qz205 qz218 qz296) RS223to240.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2322 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz832 qz3 qz218 506327 1000 528141 1000 

noncomputable def Ns222p2323 := @Enclosure.norm_gt_of_isNear qz832 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 581175869775883725545 2361183241434822606848 646440225718375362206983 

noncomputable def Ns222p2324 := @Ns222p2323 Ns222p1723 39846649 536870912 1421 2684354560 (Ns222p2317 (RS223to240.d42 qz205 qz218 qz296) RS223to240.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2325 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz295 (@BSN.thirtyTwoPi_le_dec qz205 527077 1000 qz208 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz831 qz832 (Ns222p2316 rfl rfl) (Ns222p2318 rfl rfl)) (Ns222p2319 qz10 qz208 rfl rfl rfl rfl (Ns222p2321 rfl)) (Ns222p2322 qz10 qz221 rfl rfl rfl rfl (Ns222p2324 rfl)) 

noncomputable abbrev qz613 := (@Enclosure.dec_le_dec qz763 qz772 528141 1000 528761 1000 qz767 qz776 rfl rfl rfl)

noncomputable abbrev qz297 := (RS223to240.d3 qz558 qz570 qz613)

noncomputable abbrev qz833 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz297)

noncomputable def Ns222p2326 := @Enclosure.Real.IsNear.of_eq qz833 (hardyZApproximantRS₀ qz218) Bool.false 581175869775883725545 2361183241434822606848 646440225718375362206983 Ns222p1723 

noncomputable abbrev qz298 := qz613

noncomputable def Ns222p2327 := @Enclosure.Real.IsNear.pos_val qz833 581175869775883725545 2361183241434822606848 646440225718375362206983 Ns222p1723 (Ns222p2326 (RS223to240.d4 qz218 qz231 qz298) RS223to240.d62) rfl 

noncomputable abbrev qz834 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz297)

noncomputable def Ns222p2328 := @Enclosure.Real.IsNear.of_eq qz834 (hardyZApproximantRS₀ qz231) Bool.true 804848400279527882355 1180591620717411303424 64780948291973963888339 Ns222p1836 

noncomputable def Ns222p2329 := @Enclosure.Real.IsNear.neg_val qz834 804848400279527882355 1180591620717411303424 64780948291973963888339 Ns222p1836 (Ns222p2328 (RS223to240.d42 qz218 qz231 qz298) RS223to240.d63) rfl 

noncomputable def Ns222p2330 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz833 qz3 qz218 506327 1000 528141 1000 

noncomputable def Ns222p2331 := @Enclosure.norm_gt_of_isNear qz833 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 581175869775883725545 2361183241434822606848 646440225718375362206983 

noncomputable def Ns222p2332 := @Ns222p2331 Ns222p1723 39846649 536870912 1421 2684354560 (Ns222p2326 (RS223to240.d4 qz218 qz231 qz298) RS223to240.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2333 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz834 qz3 qz231 506327 1000 528761 1000 

noncomputable def Ns222p2334 := @Enclosure.norm_gt_of_isNear qz834 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 804848400279527882355 1180591620717411303424 64780948291973963888339 

noncomputable def Ns222p2335 := @Ns222p2334 Ns222p1836 39846649 536870912 1421 2684354560 (Ns222p2328 (RS223to240.d42 qz218 qz231 qz298) RS223to240.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2336 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz297 (@BSN.thirtyTwoPi_le_dec qz218 528141 1000 qz221 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz833 qz834 (Ns222p2327 rfl rfl) (Ns222p2329 rfl rfl)) (Ns222p2330 qz10 qz221 rfl rfl rfl rfl (Ns222p2332 rfl)) (Ns222p2333 qz10 qz234 rfl rfl rfl rfl (Ns222p2335 rfl)) 

noncomputable abbrev qz835 := (@Enclosure.dec_le_dec qz917 qz921 528761 1000 530532 1000 (@Eq.refl Real qz917) qz924 rfl rfl rfl)

noncomputable abbrev qz614 := qz835

noncomputable abbrev qz299 := (RS223to240.d3 qz570 qz582 qz614)

noncomputable abbrev qz836 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz299)

noncomputable def Ns222p2337 := @Enclosure.Real.IsNear.of_eq qz836 (hardyZApproximantRS₀ qz231) Bool.true 804848400279527882355 1180591620717411303424 64780948291973963888339 Ns222p1836 

noncomputable abbrev qz300 := qz614

noncomputable def Ns222p2338 := @Enclosure.Real.IsNear.neg_val qz836 804848400279527882355 1180591620717411303424 64780948291973963888339 Ns222p1836 (Ns222p2337 (RS223to240.d4 qz231 qz244 qz300) RS223to240.d63) rfl 

noncomputable abbrev qz837 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz299)

noncomputable def Ns222p2339 := @Enclosure.Real.IsNear.of_eq qz837 (hardyZApproximantRS₀ qz244) Bool.false 14775667148989965021 18446744073709551616 16291224640007794489623 Ns222p978 

noncomputable def Ns222p2340 := @Enclosure.Real.IsNear.pos_val qz837 14775667148989965021 18446744073709551616 16291224640007794489623 Ns222p978 (Ns222p2339 (RS223to240.d42 qz231 qz244 qz300) RS223to240.d64) rfl 

noncomputable def Ns222p2341 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz836 qz3 qz231 506327 1000 528761 1000 

noncomputable def Ns222p2342 := @Enclosure.norm_gt_of_isNear qz836 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 804848400279527882355 1180591620717411303424 64780948291973963888339 

noncomputable def Ns222p2343 := @Ns222p2342 Ns222p1836 39846649 536870912 1421 2684354560 (Ns222p2337 (RS223to240.d4 qz231 qz244 qz300) RS223to240.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2344 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz837 qz3 qz244 506327 1000 530532 1000 

noncomputable def Ns222p2345 := @Enclosure.norm_gt_of_isNear qz837 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 14775667148989965021 18446744073709551616 16291224640007794489623 

noncomputable def Ns222p2346 := @Ns222p2345 Ns222p978 39846649 536870912 1421 2684354560 (Ns222p2339 (RS223to240.d42 qz231 qz244 qz300) RS223to240.d64) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2347 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz299 (@BSN.thirtyTwoPi_le_dec qz231 528761 1000 qz234 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz836 qz837 (Ns222p2338 rfl rfl) (Ns222p2340 rfl rfl)) (Ns222p2341 qz10 qz234 rfl rfl rfl rfl (Ns222p2343 rfl)) (Ns222p2344 qz10 qz247 rfl rfl rfl rfl (Ns222p2346 rfl)) 

noncomputable abbrev qz931 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 530532 1000) (Enclosure.sfrac Bool.false 531948 1000) 530532 1000 531948 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 530532 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 531948 1000)) rfl rfl rfl)

noncomputable abbrev qz838 := qz931

noncomputable abbrev qz615 := qz838

noncomputable abbrev qz301 := (RS223to240.d3 qz582 qz595 qz615)

noncomputable abbrev qz839 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz301)

noncomputable def Ns222p2348 := @Enclosure.Real.IsNear.of_eq qz839 (hardyZApproximantRS₀ qz244) Bool.false 14775667148989965021 18446744073709551616 16291224640007794489623 Ns222p978 

noncomputable abbrev qz302 := qz615

noncomputable def Ns222p2349 := @Enclosure.Real.IsNear.pos_val qz839 14775667148989965021 18446744073709551616 16291224640007794489623 Ns222p978 (Ns222p2348 (RS223to240.d4 qz244 qz256 qz302) RS223to240.d64) rfl 

noncomputable abbrev qz840 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz301)

noncomputable def Ns222p2350 := @Enclosure.Real.IsNear.of_eq qz840 (hardyZApproximantRS₀ qz256) Bool.true 3119064279608477367 1152921504606846976 81924797245358120609221 Ns222p542 

noncomputable def Ns222p2351 := @Enclosure.Real.IsNear.neg_val qz840 3119064279608477367 1152921504606846976 81924797245358120609221 Ns222p542 (Ns222p2350 (RS223to240.d42 qz244 qz256 qz302) RS223to240.d65) rfl 

noncomputable def Ns222p2352 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz839 qz3 qz244 506327 1000 530532 1000 

noncomputable def Ns222p2353 := @Enclosure.norm_gt_of_isNear qz839 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 14775667148989965021 18446744073709551616 16291224640007794489623 

noncomputable def Ns222p2354 := @Ns222p2353 Ns222p978 39846649 536870912 1421 2684354560 (Ns222p2348 (RS223to240.d4 qz244 qz256 qz302) RS223to240.d64) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2355 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz840 qz3 qz256 506327 1000 531948 1000 

noncomputable def Ns222p2356 := @Enclosure.norm_gt_of_isNear qz840 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 3119064279608477367 1152921504606846976 81924797245358120609221 

noncomputable def Ns222p2357 := @Ns222p2356 Ns222p542 39846649 536870912 1421 2684354560 (Ns222p2350 (RS223to240.d42 qz244 qz256 qz302) RS223to240.d65) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 39846649 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS223to240.d44) rfl rfl rfl rfl 

noncomputable def Ns222p2358 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz301 (@BSN.thirtyTwoPi_le_dec qz244 530532 1000 qz247 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz839 qz840 (Ns222p2349 rfl rfl) (Ns222p2351 rfl rfl)) (Ns222p2352 qz10 qz247 rfl rfl rfl rfl (Ns222p2354 rfl)) (Ns222p2355 qz10 (@Eq.refl Real qz256) rfl rfl rfl rfl (Ns222p2357 rfl)) 

noncomputable def Ns222p2359 := @List.cons RS223to240.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz299 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz299) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz299) Ns222p2347)) (@List.cons RS223to240.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz301 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz301) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz301) Ns222p2358)) (@List.nil RS223to240.d0)) 

noncomputable def Ns222p2360 := @List.cons RS223to240.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz295 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz295) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz295) Ns222p2325)) (@List.cons RS223to240.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz297 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz297) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz297) Ns222p2336)) Ns222p2359) 

noncomputable def Ns222p2361 := @List.cons RS223to240.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz291 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz291) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz291) Ns222p2303)) (@List.cons RS223to240.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz293 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz293) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz293) Ns222p2314)) Ns222p2360) 

noncomputable def Ns222p2362 := @List.cons RS223to240.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz287 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz287) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz287) Ns222p2281)) (@List.cons RS223to240.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz289 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz289) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz289) Ns222p2292)) Ns222p2361) 

noncomputable def Ns222p2363 := @List.cons RS223to240.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz283 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz283) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz283) Ns222p2259)) (@List.cons RS223to240.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz285 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz285) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz285) Ns222p2270)) Ns222p2362) 

noncomputable def Ns222p2364 := @List.cons RS223to240.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz279 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz279) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz279) Ns222p2237)) (@List.cons RS223to240.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz281 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz281) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz281) Ns222p2248)) Ns222p2363) 

noncomputable def Ns222p2365 := @List.cons RS223to240.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz275 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz275) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz275) Ns222p2215)) (@List.cons RS223to240.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz277 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz277) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz277) Ns222p2226)) Ns222p2364) 

noncomputable def Ns222p2366 := @List.cons RS223to240.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz271 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz271) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz271) Ns222p2193)) (@List.cons RS223to240.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz273 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz273) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz273) Ns222p2204)) Ns222p2365) 

noncomputable def Ns222p2367 := @List.cons RS223to240.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz267 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz267) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz267) Ns222p2171)) (@List.cons RS223to240.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz269 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz269) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz269) Ns222p2182)) Ns222p2366) 

noncomputable abbrev qz841 := (RS223to240.d2 qz917 qz921 (@Enclosure.dec_le_dec qz917 qz921 528761 1000 530532 1000 (@Eq.refl Real qz917) qz924 rfl rfl rfl))

noncomputable abbrev qz842 := (@List.cons RS223to240.d1 (RS223to240.d2 qz921 qz926 qz931) (@List.nil RS223to240.d1))

noncomputable abbrev qz616 := (@List.cons RS223to240.d1 (RS223to240.d2 qz763 qz772 (@Enclosure.dec_le_dec qz763 qz772 528141 1000 528761 1000 qz767 qz776 rfl rfl rfl)) (@List.cons RS223to240.d1 qz841 qz842))

noncomputable abbrev qz303 := (@List.cons RS223to240.d1 (RS223to240.d2 qz534 qz546 qz611) (@List.cons RS223to240.d1 (RS223to240.d2 qz546 qz558 qz612) qz616))

noncomputable def Ns222p2368 := @List.cons RS223to240.d1 (RS223to240.d2 qz166 qz179 qz290) (@List.cons RS223to240.d1 (RS223to240.d2 qz179 qz192 qz292) qz303) 

noncomputable abbrev qz843 := (RS223to240.d2 qz887 qz891 (@Enclosure.dec_le_dec qz887 qz891 519173 1000 520596 1000 (@Eq.refl Real qz887) qz894 rfl rfl rfl))

noncomputable abbrev qz844 := (@List.cons RS223to240.d1 (RS223to240.d2 qz891 qz896 qz930) Ns222p2368)

noncomputable abbrev qz617 := (@List.cons RS223to240.d1 (RS223to240.d2 qz702 qz711 (@Enclosure.dec_le_dec qz702 qz711 517749 1000 519173 1000 qz706 qz715 rfl rfl rfl)) (@List.cons RS223to240.d1 qz843 qz844))

noncomputable abbrev qz304 := (@List.cons RS223to240.d1 (RS223to240.d2 qz450 qz462 qz606) (@List.cons RS223to240.d1 (RS223to240.d2 qz462 qz474 qz607) qz617))

noncomputable def Ns222p2369 := @List.cons RS223to240.d1 (RS223to240.d2 qz75 qz88 qz276) (@List.cons RS223to240.d1 (RS223to240.d2 qz88 qz101 qz278) qz304) 

noncomputable def Ns222p2370 := @List.IsChain.cons_cons RS223to240.d1 RS223to240.d66 (RS223to240.d2 qz62 qz75 qz274) (RS223to240.d2 qz75 qz88 qz276) (@List.cons RS223to240.d1 (RS223to240.d2 qz88 qz101 qz278) qz304) 

noncomputable def Ns222p2371 := @List.IsChain.cons_cons RS223to240.d1 RS223to240.d66 (RS223to240.d2 qz75 qz88 qz276) (RS223to240.d2 qz88 qz101 qz278) qz304 (@Enclosure.dec_le_dec qz88 qz88 513472 1000 513472 1000 qz91 qz91 rfl rfl rfl) 

noncomputable abbrev qz845 := (RS223to240.d2 qz891 qz896 qz930)

noncomputable abbrev qz618 := qz845

noncomputable abbrev qz305 := qz618

noncomputable def Ns222p2372 := @List.IsChain.cons_cons RS223to240.d1 RS223to240.d66 qz305 (RS223to240.d2 qz166 qz179 qz290) (@List.cons RS223to240.d1 (RS223to240.d2 qz179 qz192 qz292) qz303) 

noncomputable def Ns222p2373 := @List.IsChain.cons_cons RS223to240.d1 RS223to240.d66 (RS223to240.d2 qz166 qz179 qz290) (RS223to240.d2 qz179 qz192 qz292) qz303 (@Enclosure.dec_le_dec qz179 qz179 523439 1000 523439 1000 qz182 qz182 rfl rfl rfl) 

noncomputable abbrev qz306 := qz616

noncomputable abbrev qz619 := (@List.cons RS223to240.d1 qz841 qz842)

noncomputable abbrev qz307 := qz619

noncomputable abbrev qz620 := qz841

noncomputable abbrev qz308 := qz620

noncomputable abbrev qz621 := qz842

noncomputable abbrev qz309 := qz621

noncomputable abbrev qz846 := (RS223to240.d2 qz921 qz926 qz931)

noncomputable abbrev qz622 := qz846

noncomputable abbrev qz310 := qz622

noncomputable def Ns222p2374 := @List.IsChain.cons_cons RS223to240.d1 RS223to240.d66 (RS223to240.d2 qz192 qz205 qz294) (RS223to240.d2 qz205 qz218 qz296) qz306 (@Enclosure.dec_le_dec qz205 qz205 527077 1000 527077 1000 qz208 qz208 rfl rfl rfl) (@List.IsChain.cons_cons RS223to240.d1 RS223to240.d66 (RS223to240.d2 qz205 qz218 qz296) (RS223to240.d2 qz218 qz231 qz298) qz307 (@Enclosure.dec_le_dec qz218 qz218 528141 1000 528141 1000 qz221 qz221 rfl rfl rfl) (@List.IsChain.cons_cons RS223to240.d1 RS223to240.d66 (RS223to240.d2 qz218 qz231 qz298) qz308 qz309 (@Enclosure.dec_le_dec qz231 qz231 528761 1000 528761 1000 qz234 qz234 rfl rfl rfl) (@List.IsChain.cons_cons RS223to240.d1 RS223to240.d66 qz308 qz310 (@List.nil RS223to240.d1) (@Enclosure.dec_le_dec qz244 qz244 530532 1000 530532 1000 qz247 qz247 rfl rfl rfl) (@List.IsChain.singleton RS223to240.d1 RS223to240.d66 qz310)))) 

noncomputable abbrev qz311 := (@List.cons RS223to240.d1 (RS223to240.d2 qz546 qz558 qz612) qz616)

noncomputable def Ns222p2375 := @List.IsChain.cons_cons RS223to240.d1 RS223to240.d66 (RS223to240.d2 qz179 qz192 qz292) (RS223to240.d2 qz192 qz205 qz294) qz311 (@Enclosure.dec_le_dec qz192 qz192 524859 1000 524859 1000 qz195 qz195 rfl rfl rfl) Ns222p2374 

noncomputable abbrev qz312 := qz617

noncomputable abbrev qz623 := (@List.cons RS223to240.d1 qz843 qz844)

noncomputable abbrev qz313 := qz623

noncomputable abbrev qz624 := qz843

noncomputable abbrev qz314 := qz624

noncomputable abbrev qz625 := qz844

noncomputable abbrev qz315 := qz625

noncomputable def Ns222p2376 := @List.IsChain.cons_cons RS223to240.d1 RS223to240.d66 (RS223to240.d2 qz101 qz114 qz280) (RS223to240.d2 qz114 qz127 qz282) qz312 (@Enclosure.dec_le_dec qz114 qz114 516325 1000 516325 1000 qz117 qz117 rfl rfl rfl) (@List.IsChain.cons_cons RS223to240.d1 RS223to240.d66 (RS223to240.d2 qz114 qz127 qz282) (RS223to240.d2 qz127 qz140 qz284) qz313 (@Enclosure.dec_le_dec qz127 qz127 517749 1000 517749 1000 qz130 qz130 rfl rfl rfl) (@List.IsChain.cons_cons RS223to240.d1 RS223to240.d66 (RS223to240.d2 qz127 qz140 qz284) qz314 qz315 (@Enclosure.dec_le_dec qz140 qz140 519173 1000 519173 1000 qz143 qz143 rfl rfl rfl) (@List.IsChain.cons_cons RS223to240.d1 RS223to240.d66 qz314 qz305 Ns222p2368 (@Enclosure.dec_le_dec qz153 qz153 520596 1000 520596 1000 qz156 qz156 rfl rfl rfl) (Ns222p2372 (@Enclosure.dec_le_dec qz166 qz166 522018 1000 522018 1000 qz169 qz169 rfl rfl rfl) (Ns222p2373 Ns222p2375))))) 

noncomputable abbrev qz316 := (@List.cons RS223to240.d1 (RS223to240.d2 qz462 qz474 qz607) qz617)

noncomputable def Ns222p2377 := @List.IsChain.cons_cons RS223to240.d1 RS223to240.d66 (RS223to240.d2 qz88 qz101 qz278) (RS223to240.d2 qz101 qz114 qz280) qz316 (@Enclosure.dec_le_dec qz101 qz101 514899 1000 514899 1000 qz104 qz104 rfl rfl rfl) Ns222p2376 

noncomputable def Ns222p2378 := Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns222p2367 (@List.IsChain.cons_cons RS223to240.d1 RS223to240.d66 (RS223to240.d2 qz3 qz27 qz268) (RS223to240.d2 qz27 qz47 qz270) (@List.cons RS223to240.d1 (RS223to240.d2 qz47 qz62 qz272) (@List.cons RS223to240.d1 (RS223to240.d2 qz62 qz75 qz274) Ns222p2369)) (@Enclosure.dec_le_dec qz27 qz27 507758 1000 507758 1000 qz30 qz30 rfl rfl rfl) (@List.IsChain.cons_cons RS223to240.d1 RS223to240.d66 (RS223to240.d2 qz27 qz47 qz270) (RS223to240.d2 qz47 qz62 qz272) (@List.cons RS223to240.d1 (RS223to240.d2 qz62 qz75 qz274) Ns222p2369) (@Enclosure.dec_le_dec qz47 qz47 509188 1000 509188 1000 qz51 qz51 rfl rfl rfl) (@List.IsChain.cons_cons RS223to240.d1 RS223to240.d66 (RS223to240.d2 qz47 qz62 qz272) (RS223to240.d2 qz62 qz75 qz274) Ns222p2369 (@Enclosure.dec_le_dec qz62 qz62 510617 1000 510617 1000 qz65 qz65 rfl rfl rfl) (Ns222p2370 (@Enclosure.dec_le_dec qz75 qz75 512045 1000 512045 1000 qz78 qz78 rfl rfl rfl) (Ns222p2371 Ns222p2377))))) 

noncomputable abbrev qz626 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz627 := (Zeta.Certificates.CertifiedZeroIntervals.intervals Ns222p2378)

theorem RS223to240.d67 : Zeta.Certificates.BatchSpec 18 506327 1000 531948 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz626 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 18) (And (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz626 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz3)) (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz626 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz256)))) Ns222p2378 (@And.intro (@Eq Nat (@List.length qz626 qz627) 18) (And (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz626 qz627)) (@Option.some Real qz3)) (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz626 qz627)) (@Option.some Real qz256))) (@Eq.refl Nat 18) (@And.intro (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz626 qz627)) (@Option.some Real qz3)) (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz626 qz627)) (@Option.some Real qz256)) (@Eq.refl (Option Real) (@Option.some Real qz3)) (@Eq.refl (Option Real) (@Option.some Real qz256))))

theorem solution : Zeta.Certificates.BatchSpec 18 506327 1000 531948 1000 := RS223to240.d67
#print axioms solution
#check solution
