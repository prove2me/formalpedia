-- Prove2me | solution 1 for RHHeight1000.rs_main_0265_0276
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:10:18.345879+00:00
-- url     : https://prove2.me/submissions/420fd6d3-9935-4eaa-916d-c4f02e79ec7a

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

noncomputable def RS265to276.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS265to276.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS265to276.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS265to276.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS265to276.d2 a b h 

theorem RS265to276.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS265to276.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS265to276.d3 a b h)) 

noncomputable def Ns264p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns264p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns264p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns264p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns264p0 Ns264p1 Ns264p2 Ns264p1 153643044 134217728 1 57760000 153643044 134217728 1 57760000 76821522 67108864 2 67108864 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns264p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns264p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns264p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns264p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns264p8 := nat_lit 167537954069964697925743468333314178468718661948561187618563575975392713740913527107727581163208035826476740967700482432525301063254420572874757592895482956004842597348203117269212172556829666669574421653274845612596416189641484794702002223261246862056663160605878293700340502480877986491439034432953223334258717026053687371824342493299510132312376251152844516906794910572262907940062760396663270105627554083664899640691826599584783763757814813433640133591539937449421955686657622469485188711283992428713614179785896055117030632677201478317872225272595773536303110412989181984739022579128493081560758017763072115692678596043664844667144619713966763611484179303468167142547433165016751768184247559143333542643815355903304572487929375 

noncomputable def Ns264p9 := nat_lit 17907736863639440849562382641391758203535690054199171304015283257442503423240620144819838407313611418261944516207295868563739563278604805791797182761045687776939279949642059267526948014748996956777332184087524644234759874591635243045607722412471722018588244283882362848653445974523544951031470230725674276297342086185092985546835544820091590454230569790847977790484558207349923322458845585052164126500435851662252152223728079705692133047658564669873831757357628115566356048471439549797170528303905720944834637690907185213991407615774042056720704508980680095051114888612186461088301140868302968264130481206655302741383410655080008578156649725227045954510069588220729495895148666460653631514375880874422615237249871322129146554264800 

noncomputable def Ns264p10 := nat_lit 55164646516618494962085419356369025784335016154267579706247610053041231157772817011486486467101704279863254798704146668052276438579475100451766223896220272709675360577301802978530276301158911649961092601279696986330335403118086533522541958716560166657634553390183479955483588238249446822384543398154260439705049143284278540285021213103458182619368483938376641172730818250587232036579805400979202432024046862170503602539341971086573372247299262086029843105216008583038025403798224342134620653974939981235680083776396058604459065501719125356177784467570909658245422960948263734871602033841948787585406240093531041217463298165642337705122589129757920995868559518021463265498464182174549661735402095023640043996665674913376875 

noncomputable def Ns264p11 := BSN.log_dyadic_bound Ns264p6 Ns264p7 15 14 Ns264p8 134217728 57760000 Ns264p9 Ns264p10 153643044 Ns264p4 Ns264p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns264p6) (BSN.artanhQ Ns264p7) 0 14 Ns264p9 Ns264p8 Ns264p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns264p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns264p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns264p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns264p15 := nat_lit 167537954069966963268140139327979112712430526945422964221951926912223381190141639739514890494967825643602350173964944759828460064784215684919760383437959917620844610857567326816719640593037578236900835917107172977527392439886629774248115214831425484905681376157923696414882114961796820014026232307332015059110330001516939277521159573995394989771587717775443426002499543257897301982481613760098955890450106043861450716722534643739571053080256776912576113428445260435254713579381797931690799491102381747484553243404562568585572234105168360737285205910186933811836504830286397217473365026331067977496463917110493303316865058355012304571237619413071097245713770677768486493924969821719264401216877841676972336093778875903304572487929375 

noncomputable def Ns264p16 := nat_lit 17907736863639702486765313263906285882628955290251965205176678923530777959693011244026517850256414903756943142851250712732214241881959351517241344993825585048584379523049477943740273636414656012170312373198803997844271825165684859407921203335666024680974464565759223251918458072775203410604089667122984485578465112081892102496937045858735135721609691262763214794451343726045584198128451069547586972080574568545086657023793200560105564573365716615162566961587407171758966967827997201380802107846920231945878242774600967607639551032178207663699700360114112068650063802902647517702890145150192721997537569966984346993833704449560383184487996362781528900358997452380059737141488304159449328022742959995775545894292303322129146554264800 

noncomputable def Ns264p17 := nat_lit 55164646516619937449385584700664297411818070214438189962773666351465523500358685366424500506990751111492356556545320273548942244833046464529601272738875466881799996765940232256588350019911833156887888425998391295014189841212513610526066550079316346993943774342801096070086869790972589246312728227659319758310961510342377923950694747797317942483020440897997204711883064182772445608288320382376665481938194224815739627075458138172195220395246294556718284728034954178416253903237031389214179719385823921869528509431462690683227358218086518156757026652846493301460983550768858152506145788622699720737745394141184245149692548799188169247529408201840608223422296381897323845616153036586108326210125693898345963996665674913376875 

noncomputable def Ns264p18 := BSN.log_dyadic_bound Ns264p13 Ns264p14 15 14 Ns264p15 134217728 57760000 Ns264p16 Ns264p17 153643044 Ns264p12 Ns264p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns264p13) (BSN.artanhQ Ns264p14) 0 14 Ns264p16 Ns264p15 Ns264p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns264p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 76821522 67108864 2 67108864 38410761 33554432 1 33554432 (Ns264p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns264p0 Ns264p1 153643044 134217728 1 57760000 Bool.false (BSN.logfrac_isNear Ns264p4 Ns264p5 1 Ns264p0 Ns264p1 153643044 134217728 57760000 rfl rfl rfl (Ns264p11 rfl))) (BSN.isNear_log_sfrac Ns264p2 Ns264p1 153643044 134217728 1 57760000 Bool.false (BSN.logfrac_isNear Ns264p12 Ns264p5 1 Ns264p2 Ns264p1 153643044 134217728 57760000 rfl rfl rfl (Ns264p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS265to276.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 33554432 := Ns264p19 

noncomputable def Ns264p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 8388608 3610000 385100712855 135135 5814539 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz579 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz316 := qz579

noncomputable abbrev qz0 := qz316

theorem RS265to276.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 5814539 8388608 1 3610000 := BSN.isNear_log_sfrac 2 1 5814539 8388608 1 3610000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 5814539 8388608 3610000 rfl rfl rfl (Ns264p20 rfl)) 

theorem RS265to276.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 93032624 134217728 38 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 5814539 8388608 1 3610000 93032624 134217728 38 134217728 RS265to276.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz580 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz319 := qz580

noncomputable def Ns264p21 := @Enclosure.Real.IsNear.inv_image qz317 23726567 16777216 1 16777216 5931641 5931642 8388608 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 23726567 16777216 1 16777216 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 23726567 16777216 1 16777216 23726567 16777216 1 16777216 (BSN.sqrt_enclosure 2 1 11863283 11863284 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS265to276.d8 : Enclosure.Real.IsNear qz320 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 11863283 16777216 1 16777216 (Ns264p21 rfl rfl) rfl 

theorem RS265to276.d9 : Enclosure.Real.IsNear qz320 Bool.false 94906264 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 94906264 134217728 8 134217728 RS265to276.d8 rfl 

noncomputable def Ns264p22 := BSN.log_dyadic_bound 1 2 12 11 1326382131865190400 8388608 3610000 130797573554866995 13749310575 9215827 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 1) (BSN.artanhQ 2) 0 11 130797573554866995 1326382131865190400 13749310575 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS265to276.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 9215827 8388608 1 3610000 := BSN.isNear_log_sfrac 3 1 9215827 8388608 1 3610000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 9215827 8388608 3610000 rfl rfl rfl (Ns264p22 rfl)) 

theorem RS265to276.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 147453232 134217728 38 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 9215827 8388608 1 3610000 147453232 134217728 38 134217728 RS265to276.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns264p23 := @Enclosure.Real.IsNear.inv_image qz321 29058991 16777216 1 16777216 4843164 4843166 8388608 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 29058991 16777216 1 16777216 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 29058991 16777216 1 16777216 29058991 16777216 1 16777216 (BSN.sqrt_enclosure 3 1 14529495 14529496 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS265to276.d12 : Enclosure.Real.IsNear qz323 Bool.false 4843165 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 9686330 16777216 2 16777216 4843165 8388608 1 8388608 (Ns264p23 rfl rfl) rfl 

theorem RS265to276.d13 : Enclosure.Real.IsNear qz323 Bool.false 77490640 134217728 16 134217728 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 4843165 8388608 1 8388608 77490640 134217728 16 134217728 RS265to276.d12 rfl 

noncomputable def Ns264p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns264p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns264p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns264p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns264p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns264p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns264p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns264p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns264p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns264p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns264p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns264p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns264p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns264p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns264p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns264p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns264p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns264p25 Ns264p26 Ns264p27 Ns264p28 200200021673987500790625 Ns264p29 Ns264p30 Ns264p31 Ns264p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns264p32 Ns264p33 151412625 Ns264p34 Ns264p35 1322214852783825 Ns264p27 Ns264p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns264p32 Ns264p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns264p34 Ns264p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns264p36 Ns264p37 1267389585 Ns264p38 Ns264p39 1927077560082675 Ns264p29 Ns264p30 Ns264p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns264p36 Ns264p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns264p38 Ns264p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS265to276.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns264p24 Ns264p25 1 Ns264p26 := Ns264p40 rfl rfl rfl 

noncomputable def Ns264p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns264p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns264p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns264p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns264p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns264p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns264p25 Ns264p26 Ns264p42 Ns264p43 9945 Ns264p44 Ns264p45 65835 Ns264p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns264p42 Ns264p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns264p44 Ns264p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS265to276.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns264p41 Ns264p25 1 Ns264p26 := Ns264p46 rfl 

noncomputable def Ns264p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns264p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS265to276.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns264p47 Ns264p25 1 Ns264p48 := BSN.pi_combine Ns264p24 Ns264p41 Ns264p25 Ns264p26 Ns264p48 Ns264p47 rfl rfl rfl rfl RS265to276.d14 RS265to276.d15 

theorem RS265to276.d17 : Enclosure.Real.IsNear Real.pi Bool.false 7074237752028440 2251799813685248 1 2251799813685248 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns264p47 Ns264p25 1 Ns264p48 7074237752028440 2251799813685248 1 2251799813685248 RS265to276.d16 rfl 

noncomputable def Ns264p49 := nat_lit 147443727375074537121690809726715087890625 

noncomputable def Ns264p50 := nat_lit 22889945643899497138335355216896171420000 

noncomputable def Ns264p51 := nat_lit 355592320898650075318906513310625 

noncomputable def Ns264p52 := BSN.log_dyadic_bound 3 5 17 16 Ns264p49 8388608 3610000 Ns264p50 Ns264p51 11629079 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 3) (BSN.artanhQ 5) 0 16 Ns264p50 Ns264p49 Ns264p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS265to276.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 11629079 8388608 1 3610000 := BSN.isNear_log_sfrac 4 1 11629079 8388608 1 3610000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 11629079 8388608 3610000 rfl rfl rfl (Ns264p52 rfl)) 

theorem RS265to276.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 186065264 134217728 38 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 11629079 8388608 1 3610000 186065264 134217728 38 134217728 RS265to276.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns264p53 := @Enclosure.Real.IsNear.inv_image qz325 33554433 16777216 1 16777216 4194303 4194304 8388608 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 33554433 16777216 1 16777216 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 33554433 16777216 1 16777216 33554433 16777216 1 16777216 (BSN.sqrt_enclosure 4 1 16777216 16777217 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS265to276.d20 : Enclosure.Real.IsNear qz327 Bool.false 8388607 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 8388607 16777216 1 16777216 8388607 16777216 1 16777216 (Ns264p53 rfl rfl) rfl 

theorem RS265to276.d21 : Enclosure.Real.IsNear qz327 Bool.false 67108856 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 8388607 16777216 1 16777216 67108856 134217728 8 134217728 RS265to276.d20 rfl 

noncomputable def Ns264p54 := nat_lit 159424323765613091421820433543167414255940625 

noncomputable def Ns264p55 := nat_lit 33013339099500162583200499609923570567289500 

noncomputable def Ns264p56 := nat_lit 351657888879851162997374110924800000 

noncomputable def Ns264p57 := nat_lit 2289063575687431840984260 

noncomputable def Ns264p58 := nat_lit 3325435793429257756623375 

noncomputable def Ns264p59 := BSN.log_dyadic_bound 2 3 21 20 Ns264p54 8388608 3610000 Ns264p55 Ns264p56 13500943 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 20 10 9927050056596826020 47940881637414340575 686533194547200 Ns264p57 Ns264p58 512222703392784384000 Ns264p55 Ns264p54 Ns264p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 10 20 Ns264p57 Ns264p58 512222703392784384000 rfl rfl rfl rfl)) rfl rfl 

theorem RS265to276.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 13500943 8388608 1 3610000 := BSN.isNear_log_sfrac 5 1 13500943 8388608 1 3610000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 13500943 8388608 3610000 rfl rfl rfl (Ns264p59 rfl rfl)) 

theorem RS265to276.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 216015088 134217728 38 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 13500943 8388608 1 3610000 216015088 134217728 38 134217728 RS265to276.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns264p60 := @Enclosure.Real.IsNear.inv_image qz328 37514995 16777216 1 16777216 3751499 3751500 8388608 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 37514995 16777216 1 16777216 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 37514995 16777216 1 16777216 37514995 16777216 1 16777216 (BSN.sqrt_enclosure 5 1 18757497 18757498 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS265to276.d24 : Enclosure.Real.IsNear qz329 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 7502999 16777216 1 16777216 (Ns264p60 rfl rfl) rfl 

theorem RS265to276.d25 : Enclosure.Real.IsNear qz329 Bool.false 60023992 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 60023992 134217728 8 134217728 RS265to276.d24 rfl 

noncomputable def Ns264p61 := BSN.log_dyadic_bound 2 10 5 4 94500000000 8388608 3610000 1291130880 26880 3401287 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz580)

theorem RS265to276.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683410914551 2251799813685248 50000000361 180500000000000000 := BSN.isNear_log_sfrac 6 1 4034683410914551 2251799813685248 50000000361 180500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 541526040612241437360128 302231454903657293676544 1000000007220000 3610000000000000000000 4034683410914551 2251799813685248 50000000361 180500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 3401287 8388608 24973259072661432 36028797018963968 3610000 1000000000000000 rfl rfl rfl rfl (Ns264p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS265to276.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 240485871 134217728 38 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683410914551 2251799813685248 50000000361 180500000000000000 240485871 134217728 38 134217728 RS265to276.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns264p62 := @Enclosure.Real.IsNear.inv_image qz331 41095619 16777216 1 16777216 3424634 3424635 8388608 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 41095619 16777216 1 16777216 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 41095619 16777216 1 16777216 41095619 16777216 1 16777216 (BSN.sqrt_enclosure 6 1 20547809 20547810 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS265to276.d28 : Enclosure.Real.IsNear qz332 Bool.false 6849269 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 6849269 16777216 1 16777216 6849269 16777216 1 16777216 (Ns264p62 rfl rfl) rfl 

theorem RS265to276.d29 : Enclosure.Real.IsNear qz332 Bool.false 54794152 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 6849269 16777216 1 16777216 54794152 134217728 8 134217728 RS265to276.d28 rfl 

noncomputable def Ns264p63 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 8388608 3610000 11010900719820672 5524329195 4694397 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz580)

theorem RS265to276.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 50000000361 180500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 50000000361 180500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 588115238325433934020608 302231454903657293676544 1000000007220000 3610000000000000000000 4381799983422711 2251799813685248 50000000361 180500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 4694397 8388608 24973259072661432 36028797018963968 3610000 1000000000000000 rfl rfl rfl rfl (Ns264p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS265to276.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 261175631 134217728 38 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 50000000361 180500000000000000 261175631 134217728 38 134217728 RS265to276.d30 rfl 

noncomputable abbrev qz334 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns264p64 := @Enclosure.Real.IsNear.inv_image qz334 44388341 16777216 1 16777216 3170595 3170596 8388608 (@Enclosure.Real.IsNear.of_eq qz334 (Real.sqrt qz333) Bool.false 44388341 16777216 1 16777216 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 44388341 16777216 1 16777216 44388341 16777216 1 16777216 (BSN.sqrt_enclosure 7 1 22194170 22194171 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS265to276.d32 : Enclosure.Real.IsNear qz335 Bool.false 6341191 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 6341191 16777216 1 16777216 6341191 16777216 1 16777216 (Ns264p64 rfl rfl) rfl 

theorem RS265to276.d33 : Enclosure.Real.IsNear qz335 Bool.false 50729528 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 6341191 16777216 1 16777216 50729528 134217728 8 134217728 RS265to276.d32 rfl 

noncomputable def Ns264p65 := BSN.log_dyadic_bound 0 16 1 0 1 8388608 3610000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz580)

theorem RS265to276.d34 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 100000001083 361000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 100000001083 361000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false 628472642529000809299968 302231454903657293676544 1000000010830000 3610000000000000000000 9364972152248037 4503599627370496 100000001083 361000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 8388608 24973259072661432 36028797018963968 3610000 1000000000000000 rfl rfl rfl rfl (Ns264p65 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS265to276.d35 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 279097919 134217728 38 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 100000001083 361000000000000000 279097919 134217728 38 134217728 RS265to276.d34 rfl 

noncomputable abbrev qz337 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns264p66 := @Enclosure.Real.IsNear.inv_image qz337 47453133 16777216 1 16777216 2965820 2965821 8388608 (@Enclosure.Real.IsNear.of_eq qz337 (Real.sqrt qz336) Bool.false 47453133 16777216 1 16777216 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 47453133 16777216 1 16777216 47453133 16777216 1 16777216 (BSN.sqrt_enclosure 8 1 23726566 23726567 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz338 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS265to276.d36 : Enclosure.Real.IsNear qz338 Bool.false 5931641 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 5931641 16777216 1 16777216 5931641 16777216 1 16777216 (Ns264p66 rfl rfl) rfl 

theorem RS265to276.d37 : Enclosure.Real.IsNear qz338 Bool.false 47453128 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 5931641 16777216 1 16777216 47453128 134217728 8 134217728 RS265to276.d36 rfl 

noncomputable def Ns264p67 := BSN.log_dyadic_bound 1 17 3 2 1252815 8388608 3610000 1448 3 988035 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz734 := (Enclosure.sfrac Bool.false 9 1)

noncomputable abbrev qz581 := qz734

noncomputable abbrev qz339 := qz581

noncomputable abbrev qz1 := qz339

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz580)

theorem RS265to276.d38 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 9895419403785957 4503599627370496 100000001083 361000000000000000 := BSN.isNear_log_sfrac 9 1 9895419403785957 4503599627370496 100000001083 361000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz340) Bool.false 664070354991632873422848 302231454903657293676544 1000000010830000 3610000000000000000000 9895419403785957 4503599627370496 100000001083 361000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 988035 8388608 24973259072661432 36028797018963968 3610000 1000000000000000 rfl rfl rfl rfl (Ns264p67 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS265to276.d39 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 294906479 134217728 38 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 9895419403785957 4503599627370496 100000001083 361000000000000000 294906479 134217728 38 134217728 RS265to276.d38 rfl 

noncomputable abbrev qz341 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns264p68 := @Enclosure.Real.IsNear.inv_image qz341 50331649 16777216 1 16777216 2796202 2796203 8388608 (@Enclosure.Real.IsNear.of_eq qz341 (Real.sqrt qz340) Bool.false 50331649 16777216 1 16777216 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz340) Bool.false 50331649 16777216 1 16777216 50331649 16777216 1 16777216 (BSN.sqrt_enclosure 9 1 25165824 25165825 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz342 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS265to276.d40 : Enclosure.Real.IsNear qz342 Bool.false 5592405 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz342 Bool.false 5592405 16777216 1 16777216 5592405 16777216 1 16777216 (Ns264p68 rfl rfl) rfl 

theorem RS265to276.d41 : Enclosure.Real.IsNear qz342 Bool.false 44739240 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz342 Bool.false 5592405 16777216 1 16777216 44739240 134217728 8 134217728 RS265to276.d40 rfl 

theorem RS265to276.d42 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz735 := (@instHMul Real Real.instMul)

noncomputable abbrev qz582 := (@HMul.hMul Real Real Real qz735 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz343 := qz582

noncomputable abbrev qz2 := qz343

theorem RS265to276.d43 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS265to276.d42 rfl 

noncomputable abbrev qz344 := (@Inv.inv Real Real.instInv qz582)

noncomputable abbrev qz3 := qz344

theorem RS265to276.d44 : Enclosure.Real.IsNear qz3 Bool.false 2670177 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 2670177 16777216 1 16777216 2670177 16777216 1 16777216 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 1335088 1335089 8388608 RS265to276.d43 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns264p69 := nat_lit 16648186526522870333440000 

noncomputable def Ns264p70 := nat_lit 7793529976150073153943502848 

noncomputable abbrev qz736 := (Enclosure.sfrac Bool.false 565685 1000)

noncomputable abbrev qz583 := qz736

noncomputable abbrev qz345 := qz583

noncomputable abbrev qz4 := qz345

noncomputable abbrev qz584 := qz735

noncomputable abbrev qz346 := qz584

noncomputable abbrev qz5 := qz346

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 9)

noncomputable abbrev qz7 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz737 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 565685 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz585 := qz737

noncomputable abbrev qz347 := qz585

noncomputable abbrev qz8 := qz347

noncomputable abbrev qz9 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz738 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 565685 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz586 := qz738

noncomputable abbrev qz348 := qz586

noncomputable abbrev qz10 := qz348

noncomputable abbrev qz587 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz8 qz9))

noncomputable def Ns264p71 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (@HMul.hMul Real Real Real qz5 qz587 (Zeta.RiemannSiegel.correction qz10)) 109793155 33554432 88239 67108864 9172408258033506521 73786976294838206464 147173365958048685049 Ns264p69 Ns264p70 

noncomputable def Ns264p72 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 565685 1000 118 161 134217728 67108864 2251799813685248 Bool.false 132822055894 1799 

noncomputable def Ns264p73 := Ns264p72 279097919 38 47453128 8 294906479 38 44739240 8 Bool.true 190408706 72218 Bool.true 181662147 Bool.true 58692703 7074237752028440 1 Bool.false 28937554 Bool.true Bool.false 56839905 Bool.true Bool.true 219586310 

noncomputable def Ns264p74 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 565685 1000 15 70 134217728 67108864 2251799813685248 Bool.false 132822055894 1799 

noncomputable def Ns264p75 := Ns264p74 240485871 38 54794152 8 261175631 38 50729528 8 Bool.true 194478308 53883 Bool.true 54763330 Bool.true 163070938 7074237752028440 1 Bool.false 53256435 Bool.false Bool.false 46756366 Bool.true Bool.true 190408706 

noncomputable def Ns264p76 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 565685 1000 130 50 134217728 67108864 2251799813685248 Bool.false 132822055894 1799 

noncomputable def Ns264p77 := Ns264p76 186065264 38 67108856 8 216015088 38 60023992 8 Bool.true 121049770 31797 Bool.false 159994190 Bool.false 84125132 7074237752028440 1 Bool.false 49627850 Bool.true Bool.false 108705586 Bool.true Bool.true 194478308 

noncomputable def Ns264p78 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 565685 1000 380 234 134217728 67108864 2251799813685248 Bool.false 132822055894 1799 

noncomputable def Ns264p79 := Ns264p78 93032624 38 94906264 8 147453232 38 77490640 16 Bool.true 134217720 1846 Bool.false 79984615 Bool.false 76055242 7074237752028440 1 Bool.false 111082060 Bool.false Bool.false 113239624 Bool.true Bool.true 121049770 

noncomputable def Ns264p80 := nat_lit 4205925472980114241276954996219607006119122081264163 

noncomputable def Ns264p81 := nat_lit 4250120639367006628148282740907861219128167628800 

noncomputable def Ns264p82 := nat_lit 27804520601481057255448185500000000 

noncomputable def Ns264p83 := nat_lit 94371635825196845196411626697405000000 

noncomputable abbrev qz349 := (@Eq.refl Real qz583)

noncomputable abbrev qz11 := qz349

noncomputable def Ns264p84 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 565685 1000 1279999076900 16000000 1131370 4000 2000 Ns264p82 Ns264p83 qz11 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns264p85 := nat_lit 21029627364900571206384774981098035030595610406320815000000 

noncomputable abbrev qz739 := (@instHSub Real Real.instSub)

noncomputable abbrev qz588 := qz739

noncomputable abbrev qz350 := qz588

noncomputable abbrev qz589 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz740 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz741 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz590 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1131370))))

noncomputable abbrev qz351 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 565685 4000) (Real.log (Enclosure.sfrac Bool.false 1279999076900 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz590))

noncomputable abbrev qz591 := (Enclosure.sfrac Bool.false 565685 2000)

noncomputable abbrev qz12 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz351 qz591) (@HMul.hMul Real Real Real qz346 qz591 (Real.log Real.pi)))

noncomputable def Ns264p86 := @Enclosure.Real.IsNear.addLit_ft_p qz12 (Enclosure.sfrac Bool.true Ns264p82 Ns264p83) 222838498475059548123 225179981368524800 1980730006914344069 147865600000000000000000 Ns264p82 Ns264p83 0 1 Ns264p85 

noncomputable def Ns264p87 := nat_lit 598177539525079144275514490880 

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz350 qz351 qz591)

noncomputable def Ns264p88 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (@HMul.hMul Real Real Real qz5 qz591 (Real.log Real.pi)) 59149376286267192927 45035996273704960 358553288378853 72200000000000000000 4345678267257 13421772800 113137 13421772800 Ns264p87 222838498475059548123 225179981368524800 

noncomputable abbrev qz14 := qz351

noncomputable def Ns264p89 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz591 359437350311562940379 225179981368524800 358553288378853 72200000000000000000 565685 2000 0 1 591493762862671929270000 59149376286267192927 45035996273704960 358553288378853 72200000000000000000 

noncomputable def Ns264p90 := nat_lit 809380958463096646309460230895828992 

noncomputable def Ns264p91 := nat_lit 27297015938241618472075264 

noncomputable def Ns264p92 := nat_lit 2417851639229258349412352 

noncomputable def Ns264p93 := nat_lit 16739048512926043661078791815645057217510664603433352211666282505000000000000 

noncomputable def Ns264p94 := nat_lit 55440427073565590382883721341495317391623714237918878000080551000000000000 

noncomputable def Ns264p95 := nat_lit 2304258721360351438787008086014749505033674023392051983215000000000000 

noncomputable def Ns264p96 := BSN.log_dyadic_bound 231423076900 2328575076900 4 3 Ns264p93 67108864 28880000 Ns264p94 Ns264p95 13383272 2559998153800 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 231423076900) (BSN.artanhQ 2328575076900) 0 3 Ns264p94 Ns264p93 Ns264p95 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz352 := (Real.log (Enclosure.sfrac Bool.false 1279999076900 16000000))

noncomputable abbrev qz353 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns264p97 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 565685 4000) qz352 565685 4000 0 1 3177790895365367 281474976710656 781250361 22562500000000000 359525728528951526279 225179981368524800 88388322092457 18050000000000000000 (Enclosure.Real.IsNear.const Bool.false 565685 4000) (BSN.isNear_log_sfrac 1279999076900 16000000 3177790895365367 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1279999076900) qz353)) Bool.false Ns264p91 Ns264p92 1000000462080000 28880000000000000000000 3177790895365367 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1279999076900 16000000 16 2559998153800 2097152000000 13383272 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns264p96 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p98 := BSN.arctan_dyadic_bound_f 1000 1131370 1 0 8388608 3610000 0 1 1 0 1 1 7414 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1131370) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1131370) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz592 := qz740

noncomputable abbrev qz354 := qz592

noncomputable abbrev qz15 := qz354

noncomputable abbrev qz593 := qz741

noncomputable abbrev qz355 := qz593

noncomputable abbrev qz16 := qz355

noncomputable abbrev qz742 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz594 := qz742

noncomputable abbrev qz356 := qz594

noncomputable abbrev qz17 := (@Enclosure.Real.IsNear.mulLit_ff qz356 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz357 := (@Nat.cast Real Real.instNatCast 1131370)

noncomputable def Ns264p99 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 qz357)) 884279719003555 562949953421312 1 2000000000000000 7414 8388608 1 3610000 7413702214116307894272 883782173885859 562949953421312 200000000361 722000000000000000 qz17 (Ns264p98 rfl) rfl rfl 

noncomputable abbrev qz358 := (@HMul.hMul Real Real Real qz584 qz589 qz590)

noncomputable abbrev qz18 := qz358

noncomputable abbrev qz359 := qz589

noncomputable abbrev qz19 := qz359

noncomputable abbrev qz360 := qz590

noncomputable abbrev qz20 := qz360

noncomputable abbrev qz361 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns264p100 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 565685 4000) qz352) qz18 359525728528951526279 225179981368524800 88388322092457 18050000000000000000 883782173885859 2251799813685248 200000000361 2888000000000000000 Ns264p90 359437350311562940379 225179981368524800 358553288378853 72200000000000000000 (Ns264p97 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz20 1 4 0 1 883782173885859 562949953421312 200000000361 722000000000000000 883782173885859 2251799813685248 200000000361 2888000000000000000 qz361 Ns264p99 rfl) 

noncomputable def Ns264p101 := @Ns264p86 Ns264p80 Ns264p81 1980730006914344069 147865600000000000000000 (@Ns264p88 1980730006914344069 147865600000000000000000 (Ns264p89 (Ns264p100 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 565685 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz591 (Real.log Real.pi) 565685 2000 0 1 38410761 33554432 1 33554432 4345678267257 13421772800 113137 13421772800 (Enclosure.Real.IsNear.const Bool.false 565685 2000) RS265to276.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns264p82 Ns264p83) 

noncomputable abbrev qz362 := (@instHAdd Real Real.instAdd)

noncomputable def Ns264p102 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns264p80 Ns264p81 1980730006914344069 147865600000000000000000 8301378493 8388608 113 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz362 qz12 (Enclosure.sfrac Bool.true Ns264p82 Ns264p83)) Bool.false Ns264p80 Ns264p81 1980730006914344069 147865600000000000000000 Ns264p84 (Ns264p101 rfl rfl)) 

noncomputable def Ns264p103 := nat_lit 1898669848931551292686336 

noncomputable def Ns264p104 := nat_lit 1208925819614629174706176 

noncomputable def Ns264p105 := nat_lit 856583417258112139254841273081336858584486022077598600456699468457927961620185592250015571262254667793602401335652308828465000000000000 

noncomputable def Ns264p106 := nat_lit 16860812360175734222210805034837902731874731588140993779854824115686058269364094835627812361599730584878593258197117225559879026789580800 

noncomputable def Ns264p107 := nat_lit 609811748451738667880568072449452908657969480323093671700807365100670751194388670656054151219422020971775054931640625000000000000 

noncomputable def Ns264p108 := nat_lit 4277598461871755019203673164401163774164450944659988620065731328358972522100510367472993510331263966183242592538041817579825000000000000 

noncomputable def Ns264p109 := nat_lit 590128432606150697777378176219326595615615605584934782294918844049012039427743319246973432655990570470750764036899102894595765937635328000 

noncomputable abbrev qz363 := (BSN.sinEvenQ 34359738368)

noncomputable abbrev qz364 := (BSN.sinOddQ 34359738368)

noncomputable def Ns264p110 := BSN.sin_dyadic_bound_f 53963442750 34359738368 4 3 16777216 7227051 Ns264p105 Ns264p106 Ns264p107 Ns264p108 Ns264p109 Ns264p107 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53963442750) qz363 0 3 Ns264p105 Ns264p106 Ns264p107 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53963442750) qz364 0 3 Ns264p108 Ns264p109 Ns264p107 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz365 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable abbrev qz366 := (@Nat.cast Real Real.instNatCast Ns264p104)

noncomputable def Ns264p111 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8301378493) qz365) Bool.false 8301378493 8388608 113 8388608 Bool.true 16777215 16777216 1 3610000 (Ns264p102 rfl) (Enclosure.sfrac_false_div 8301378493 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8301378493) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns264p103) qz366) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 157 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q1 8301378493 8388608 226375608064910080 72057594037927936 157 Ns264p103 Ns264p104 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns264p103 Ns264p104 53963442750 34359738368 7227051 7220000 (Ns264p110 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p112 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns264p80 Ns264p81 1980730006914344069 147865600000000000000000 132822055894 134217728 1799 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz362 qz12 (Enclosure.sfrac Bool.true Ns264p82 Ns264p83)) Bool.false Ns264p80 Ns264p81 1980730006914344069 147865600000000000000000 Ns264p84 (Ns264p101 rfl rfl)) 

noncomputable def Ns264p113 := Ns264p79 31797 BSN.abs_quadSignPos (BSN.cos_quad_nat0 380 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 111082060 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 234 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 113239624 134217728) qz11 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 16777215 16777216 26019913 1892679680000 134217720 134217728 1846 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 16777215 16777216 26019913 1892679680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 16777215 16777216 416318608 30282874880000 16777215 16777216 26019913 1892679680000 (Ns264p111 rfl rfl) rfl)) rfl) (Ns264p112 rfl) RS265to276.d7 

noncomputable def Ns264p114 := nat_lit 22315532280990633858125616296209364296417535611019283429749208690625 

noncomputable def Ns264p115 := nat_lit 4246191600076225767660054876205591831097850246550140165773818614251520 

noncomputable def Ns264p116 := nat_lit 1675142162022869540933048031533190770530610978934351570187890625 

noncomputable def Ns264p117 := nat_lit 66943246558647855835294982792565026507711545611099981586107250290625 

noncomputable def Ns264p118 := nat_lit 191078622003430159544702469429251632399403261094756307459821837641318400 

noncomputable abbrev qz367 := (BSN.cosEvenQ 134217728)

noncomputable abbrev qz368 := (BSN.cosOddQ 134217728)

noncomputable def Ns264p119 := BSN.cos_dyadic_bound_f 79984615 134217728 3 2 134217728 67108864 Ns264p114 Ns264p115 Ns264p116 Ns264p117 Ns264p118 Ns264p116 111082060 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 79984615) qz367 0 2 Ns264p114 Ns264p115 Ns264p116 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 79984615) qz368 0 2 Ns264p117 Ns264p118 Ns264p116 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p120 := nat_lit 18242824334396592055316270627031107494322164449235086468999678320896 

noncomputable def Ns264p121 := nat_lit 1119523515752460595131148850739595801070189558901353117591593216 

noncomputable def Ns264p122 := nat_lit 54726233956158271244758549583391843291364352968587456700763851776256 

noncomputable def Ns264p123 := BSN.cos_dyadic_bound_f 76055242 134217728 3 2 134217728 67108864 Ns264p120 Ns264p115 Ns264p121 Ns264p122 Ns264p118 Ns264p121 113239624 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 76055242) qz367 0 2 Ns264p120 Ns264p115 Ns264p121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 76055242) qz368 0 2 Ns264p122 Ns264p118 Ns264p121 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p124 := nat_lit 1378933705801126019723110171017193376526632501187174807121526487531786252137595432059579085255882304000000 

noncomputable def Ns264p125 := nat_lit 16370259324565974446773555668639125346849261288577159159185037526614652227207809159774062022111344040345600 

noncomputable def Ns264p126 := nat_lit 281352348482637673917071381926290957440506692404526874279571291208380866260060971649361000000000000 

noncomputable def Ns264p127 := nat_lit 8358834754431363771981033601044634476462551452597134202907913712273284352632153695550867559056265177600000 

noncomputable def Ns264p128 := nat_lit 1489693598535503674656393565846160406563282777260521483485838414921933352675910633539439644012132307671449600 

noncomputable def Ns264p129 := BSN.cos_dyadic_bound_f 159994190 134217728 4 3 134217728 67108864 Ns264p124 Ns264p125 Ns264p126 Ns264p127 Ns264p128 Ns264p126 49627850 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 159994190) qz367 0 3 Ns264p124 Ns264p125 Ns264p126 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 159994190) qz368 0 3 Ns264p127 Ns264p128 Ns264p126 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p130 := nat_lit 27308116262726252990816522627007856993678276260115158667106420064256 

noncomputable def Ns264p131 := nat_lit 2508453584663858446401399000585670279965958351767794163269042176 

noncomputable def Ns264p132 := nat_lit 81919331881009431255556765083022399640474896863641940412992722108416 

noncomputable def Ns264p133 := BSN.cos_dyadic_bound_f 84125132 134217728 3 2 134217728 67108864 Ns264p130 Ns264p115 Ns264p131 Ns264p132 Ns264p118 Ns264p131 108705586 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 84125132) qz367 0 2 Ns264p130 Ns264p115 Ns264p131 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 84125132) qz368 0 2 Ns264p132 Ns264p118 Ns264p131 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p134 := Ns264p77 53883 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 130 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 49627850 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 50 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 108705586 134217728) qz11 rfl rfl (Ns264p113 RS265to276.d9 RS265to276.d11 RS265to276.d13 RS265to276.d17 (Ns264p119 rfl rfl) (Ns264p123 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns264p112 rfl) RS265to276.d19 RS265to276.d21 RS265to276.d23 RS265to276.d25 RS265to276.d17 (Ns264p129 rfl rfl) (Ns264p133 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns264p135 := nat_lit 8994134832005878285948183210000 

noncomputable def Ns264p136 := nat_lit 38942226439011207213978722469150720 

noncomputable def Ns264p137 := nat_lit 272595585073078450497851057284055040 

noncomputable abbrev qz369 := (BSN.sinEvenQ 134217728)

noncomputable abbrev qz370 := (BSN.sinOddQ 134217728)

noncomputable def Ns264p138 := BSN.sin_dyadic_bound_f 54763330 134217728 2 1 134217728 67108864 Ns264p135 Ns264p136 Ns264p135 Ns264p135 Ns264p137 Ns264p135 53256435 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 54763330) qz369 0 1 Ns264p135 Ns264p136 Ns264p135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 54763330) qz370 0 1 Ns264p135 Ns264p137 Ns264p135 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p139 := nat_lit 1488243875007247061646295411195942155623531435610779073019999745602369167861926490668701047240685762318336 

noncomputable def Ns264p140 := nat_lit 353605353696917438103316711125367169928418209602189534945606732798893403422713290968694739123245056 

noncomputable def Ns264p141 := nat_lit 9020880719167459920151190591689914853833149292608022107742466040698159046105725060663821508672990306570240 

noncomputable def Ns264p142 := BSN.cos_dyadic_bound_f 163070938 134217728 4 3 134217728 67108864 Ns264p139 Ns264p125 Ns264p140 Ns264p141 Ns264p128 Ns264p140 46756366 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 163070938) qz367 0 3 Ns264p139 Ns264p125 Ns264p140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 163070938) qz368 0 3 Ns264p141 Ns264p128 Ns264p140 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p143 := Ns264p75 72218 BSN.abs_quadSignPos (BSN.cos_quad_nat3 15 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 53256435 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 70 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 46756366 134217728) qz11 rfl rfl (Ns264p134 rfl rfl) (Ns264p112 rfl) RS265to276.d27 RS265to276.d29 RS265to276.d31 RS265to276.d33 RS265to276.d17 (Ns264p138 rfl rfl) (Ns264p142 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p144 := nat_lit 2293662336063898791345297565055494961540301290667116501910590756855867754247874449894375725285333219054321 

noncomputable def Ns264p145 := nat_lit 1291734657219934543231685742415139737532003345338214854015535240401748607853651731789407804164313841 

noncomputable def Ns264p146 := nat_lit 13896384313821398282073357180533094337812331243953984926556671941339495748766680305882405969066437603398385 

noncomputable def Ns264p147 := BSN.cos_dyadic_bound_f 181662147 134217728 4 3 134217728 67108864 Ns264p144 Ns264p125 Ns264p145 Ns264p146 Ns264p128 Ns264p145 28937554 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 181662147) qz367 0 3 Ns264p144 Ns264p125 Ns264p145 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 181662147) qz368 0 3 Ns264p146 Ns264p128 Ns264p145 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p148 := nat_lit 11866877053484789544974032471681 

noncomputable def Ns264p149 := BSN.sin_dyadic_bound_f 58692703 134217728 2 1 134217728 67108864 Ns264p148 Ns264p136 Ns264p148 Ns264p148 Ns264p137 Ns264p148 56839905 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 58692703) qz369 0 1 Ns264p148 Ns264p136 Ns264p148 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 58692703) qz370 0 1 Ns264p148 Ns264p137 Ns264p148 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p150 := Ns264p73 88239 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 118 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 28937554 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 161 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 56839905 134217728) qz11 rfl rfl (Ns264p143 rfl) (Ns264p112 rfl) RS265to276.d35 RS265to276.d37 RS265to276.d39 RS265to276.d41 RS265to276.d17 (Ns264p147 rfl rfl) (Ns264p149 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p151 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) 219586310 134217728 88239 134217728 219586310 134217728 88239 134217728 58944751256207360 109793155 33554432 88239 67108864 (Ns264p150 rfl) 

noncomputable def Ns264p152 := @Enclosure.Real.IsNear.mulLit_tf qz587 (Zeta.RiemannSiegel.correction qz10) 2723273 8388608 1 8388608 3368155986577 8796093022208 6720468898997 248077311016960000 9172408258033506521 73786976294838206464 

noncomputable abbrev qz595 := (@HPow.hPow Real Real Real qz7 qz8 qz9)

noncomputable def Ns264p153 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz595 1 1 0 1 2723273 8388608 1 8388608 2723273 8388608 1 8388608 

noncomputable abbrev qz21 := (@Enclosure.Real.IsNear.of_eq qz347 (@HMul.hMul Real Real Real qz346 qz345 qz344) Bool.false 302095815249 3355443200 113137 3355443200 (BSN.t_div_two_pi_mk qz345 565685 1000 qz349) (@Enclosure.Real.IsNear.mulLit_ff qz345 qz344 565685 1000 0 1 2670177 16777216 1 16777216 302095815249 3355443200 113137 3355443200 (Enclosure.Real.IsNear.const Bool.false 565685 1000) RS265to276.d44 rfl))

noncomputable def Ns264p154 := @Enclosure.Real.IsNear.sqrt_image qz8 302095815249 3355443200 113137 3355443200 79595264 79595294 8388608 qz21 

noncomputable abbrev qz743 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 565685 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz596 := qz743

noncomputable abbrev qz371 := qz596

noncomputable abbrev qz22 := qz371

noncomputable def Ns264p155 := @Enclosure.Real.IsNear.sqrt_image qz22 79595279 8388608 15 8388608 25839765 25839771 8388608 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 159190558 16777216 30 16777216 79595279 8388608 15 8388608 (Ns264p154 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz597 := (Real.sqrt qz743)

noncomputable abbrev qz372 := qz597

noncomputable abbrev qz23 := qz372

noncomputable def Ns264p156 := @Enclosure.Real.IsNear.inv_image qz23 3229971 1048576 3 8388608 2723272 2723274 8388608 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 51679536 16777216 6 16777216 3229971 1048576 3 8388608 (Ns264p155 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns264p157 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz23) Bool.false 5446546 16777216 2 16777216 2723273 8388608 1 8388608 (Ns264p156 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz373 := (@HMul.hMul Real Real Real qz584 qz582 qz586)

noncomputable abbrev qz24 := (Real.cos qz373)

noncomputable abbrev qz598 := (@HMul.hMul Real Real Real qz735 qz738 qz738)

noncomputable abbrev qz599 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz374 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz598 qz586) qz599)

noncomputable abbrev qz25 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz374))

noncomputable def Ns264p158 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz10) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz24) qz25) Bool.false 3368155986577 

noncomputable def Ns264p159 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz24) qz25 1051321 1048576 49 

noncomputable abbrev qz26 := (@Neg.neg Real Real.instNeg (Real.cos qz373))

noncomputable def Ns264p160 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz24) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz26)) Bool.true 1051321 1048576 49 4194304 (BSN.inv_eq_neg_inv_neg qz24) 

noncomputable def Ns264p161 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz26) Bool.false 16821136 16777216 196 16777216 1051321 1048576 

noncomputable def Ns264p162 := @Enclosure.Real.IsNear.recentre' qz24 Bool.true 16733411 16777216 699067216 60565749760000 16733411 16777216 43691701 3785359360000 

noncomputable abbrev qz27 := qz373

noncomputable abbrev qz375 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable def Ns264p163 := @Enclosure.Real.IsNear.cos_image qz27 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51494561) qz375) Bool.false 51494561 16777216 189 16777216 Bool.true 16733411 16777216 1 

noncomputable def Ns264p164 := nat_lit 404791131170860575928174249 

noncomputable def Ns264p165 := nat_lit 36028797018963968000000000000000 

noncomputable def Ns264p166 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz10 884279719003555 140737488355328 1 500000000000000 4097807 8388608 15 8388608 3623607622490800703885 1180591620717411303424 Ns264p164 

noncomputable def Ns264p167 := @Enclosure.Real.IsNear.subLit_ff_p qz22 qz1 79595279 8388608 15 8388608 9 1 0 1 4097807 4097807 8388608 15 

noncomputable abbrev qz376 := (Enclosure.Real.IsNear.const Bool.false 9 1)

noncomputable def Ns264p168 := @Ns264p167 8388608 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 159190558 16777216 30 16777216 79595279 8388608 15 8388608 (Ns264p154 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns264p169 := @Enclosure.Real.IsNear.recentre' qz27 Bool.false 3623607622490800703885 1180591620717411303424 Ns264p164 Ns264p165 51494561 16777216 189 16777216 (@Ns264p166 Ns264p165 RS265to276.d43 (Ns264p168 rfl rfl) rfl) 

noncomputable def Ns264p170 := nat_lit 3623195869762294395174912 

noncomputable def Ns264p171 := nat_lit 29672409411645344241469166555930028951308025106835969104431870390002623753991959182132385 

noncomputable def Ns264p172 := nat_lit 704955687610872565255254336748118540842396593755240389471857687246053587015266059818106880 

noncomputable def Ns264p173 := nat_lit 49396490723930145237700121220345472166332490639627395686588521384091161810664872821921 

noncomputable def Ns264p174 := nat_lit 77633477950280014682986778878793326012775527437820522347162326748718343188952149968635041 

noncomputable def Ns264p175 := nat_lit 12924187606199330363012996173715506582110604218846073806984057599510982428613211096665292800 

noncomputable def Ns264p176 := BSN.sin_dyadic_bound_f 51488710109 34359738368 3 2 16777216 7227051 Ns264p171 Ns264p172 Ns264p173 Ns264p174 Ns264p175 Ns264p173 16733411 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 51488710109) qz363 0 2 Ns264p171 Ns264p172 Ns264p173 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 51488710109) qz364 0 2 Ns264p174 Ns264p175 Ns264p173 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz377 := (@Nat.cast Real Real.instNatCast Ns264p92)

noncomputable def Ns264p177 := @Ns264p163 3610000 (Ns264p169 rfl) (Enclosure.sfrac_false_div 51494561 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51494561) qz375) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns264p170) qz377) 226375608064910080 72057594037927936 Bool.false 16733411 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q1 51494561 16777216 226375608064910080 72057594037927936 0 Ns264p170 Ns264p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16733411 16777216 Ns264p170 Ns264p92 51488710109 34359738368 7227051 7220000 (Ns264p176 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p178 := @Enclosure.Real.IsNear.inv_image qz26 16733411 16777216 43691701 3785359360000 8410470 8410666 8388608 (@Enclosure.Real.IsNear.neg qz24 Bool.true 16733411 16777216 43691701 3785359360000 (Ns264p162 (Ns264p177 rfl rfl) rfl)) 

noncomputable def Ns264p179 := Ns264p160 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz26) Bool.false 1051321 1048576 49 4194304 (@Ns264p161 49 4194304 (Ns264p178 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p180 := @Enclosure.Real.IsNear.recentre' qz25 Bool.true 3203737 8388608 

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz346 qz343 qz374)

noncomputable def Ns264p181 := @Enclosure.Real.IsNear.cos_image qz28 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32928037)) qz375) Bool.true 32928037 16777216 

noncomputable def Ns264p182 := nat_lit 19437282543194760706153436605 

noncomputable def Ns264p183 := nat_lit 9903520314283042199192993792 

noncomputable def Ns264p184 := nat_lit 6713152054440690571679301632502197 

noncomputable def Ns264p185 := @Enclosure.Real.IsNear.recentre' qz28 Bool.true Ns264p182 Ns264p183 Ns264p184 

noncomputable def Ns264p186 := nat_lit 302231454903657293676544000000000000000 

noncomputable abbrev qz29 := qz374

noncomputable def Ns264p187 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz29 884279719003555 140737488355328 1 500000000000000 21980920884511 

noncomputable abbrev qz378 := (@HSub.hSub Real Real Real qz588 qz598 qz586)

noncomputable abbrev qz30 := qz378

noncomputable abbrev qz379 := qz599

noncomputable abbrev qz31 := qz379

noncomputable def Ns264p188 := @Enclosure.Real.IsNear.subLit_tf qz30 qz31 17582874373407 70368744177664 248763555 70368744177664 1 16 

noncomputable abbrev qz380 := qz598

noncomputable abbrev qz32 := qz380

noncomputable def Ns264p189 := @Enclosure.Real.IsNear.subLit_ff_n qz32 qz10 16792022209249 70368744177664 122934435 70368744177664 4097807 8388608 15 8388608 

noncomputable def Ns264p190 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz10 4097807 8388608 15 8388608 4097807 8388608 15 8388608 16792022209249 70368744177664 

noncomputable def Ns264p191 := nat_lit 148583980222465667379026625619923368339255348828826302970283796038953707441587665285382870890961 

noncomputable def Ns264p192 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600 

noncomputable def Ns264p193 := nat_lit 1624763271161619378195904953115837732134190889113958541855861795389521985973280715847203281 

noncomputable def Ns264p194 := nat_lit 896140086456564988088899013106420347524663273493946402403225602391430737319008494849976085739985 

noncomputable def Ns264p195 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600 

noncomputable def Ns264p196 := BSN.cos_dyadic_bound_t 32928037 16777216 4 3 8388608 3610000 Ns264p191 Ns264p192 Ns264p193 Ns264p194 Ns264p195 Ns264p193 3203737 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32928037) (BSN.cosEvenQ 16777216) 0 3 Ns264p191 Ns264p192 Ns264p193 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32928037) (BSN.cosOddQ 16777216) 0 3 Ns264p194 Ns264p195 Ns264p193 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz381 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns264p197 := @Ns264p180 683458608 30282874880000 3203737 8388608 42716163 1892679680000 (@Ns264p181 187 8388608 Bool.true 3203737 8388608 1 3610000 (@Ns264p185 Ns264p186 32928037 16777216 187 8388608 (@Ns264p187 70368744177664 248763555 70368744177664 Ns264p182 Ns264p183 Ns264p184 Ns264p186 RS265to276.d43 (@Ns264p188 0 1 351694734152176 21980920884511 70368744177664 248763555 70368744177664 (@Ns264p189 147495840631756947456 17582874373407 70368744177664 248763555 70368744177664 (@Ns264p190 122934435 70368744177664 (Ns264p168 rfl rfl) (Ns264p168 rfl rfl) rfl) (Ns264p168 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32928037 16777216) (BSN.cos_neg_of_bound 32928037 16777216 Bool.true 3203737 8388608 1 3610000 (Ns264p196 rfl rfl)) rfl rfl) 

noncomputable abbrev qz33 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 9) (Enclosure.sfrac Bool.true 1 1) Bool.true 1 1 0 1 (BSN.neg_one_pow_odd_mk 9 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1))

noncomputable def Ns264p198 := @Ns264p152 147173365958048685049 Ns264p69 (Ns264p153 qz33 (@Enclosure.Real.IsNear.of_eq qz595 (@Inv.inv Real Real.instInv qz23) Bool.false 2723273 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz8 (BSN.t_div_two_pi_nonneg qz4 565685 1000 qz11)) Ns264p157) rfl) (@Ns264p158 8796093022208 6720468898997 248077311016960000 (BSN.correction_mk qz10 (BSN.cos_two_pi_p_ne_zero_mk qz4 565685 1000 9 qz11 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 565685 1000 9 qz11 rfl rfl rfl))) (@Ns264p159 4194304 3203737 8388608 42716163 1892679680000 3368155986577 8796093022208 6720468898997 248077311016960000 Ns264p179 (Ns264p197 rfl) rfl)) 

noncomputable abbrev qz34 := qz350

noncomputable def Ns264p199 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 232265292887391840039 73786976294838206464 22037267212783582125049 Ns264p69 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (@HMul.hMul Real Real Real qz5 qz587 (Zeta.RiemannSiegel.correction qz10))) Bool.true 232265292887391840039 73786976294838206464 22037267212783582125049 Ns264p69 (BSN.hardyZApproximantRS₀_eq qz4 9 (@BSN.floor_sqrt_eq_dec qz4 565685 1000 9 qz11 rfl rfl rfl)) (@Ns264p71 232265292887391840039 73786976294838206464 22037267212783582125049 Ns264p69 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9)) Bool.true 109793155 33554432 88239 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (Ns264p151 (Ns264p150 rfl) rfl rfl)) (Ns264p198 rfl) rfl rfl)) 

theorem RS265to276.d45 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 232265292887391840039 73786976294838206464 22037267212783582125049 Ns264p69 := Ns264p199 

theorem RS265to276.d46 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS265to276.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS265to276.d3 a b h)) 

noncomputable def Ns264p200 := nat_lit 26637098442436592533504000 

noncomputable def Ns264p201 := nat_lit 17558587693883781222015959040 

noncomputable abbrev qz744 := (Enclosure.sfrac Bool.false 567081 1000)

noncomputable abbrev qz600 := qz744

noncomputable abbrev qz382 := qz600

noncomputable abbrev qz35 := qz382

noncomputable abbrev qz745 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 567081 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz601 := qz745

noncomputable abbrev qz383 := qz601

noncomputable abbrev qz36 := qz383

noncomputable abbrev qz746 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 567081 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz602 := qz746

noncomputable abbrev qz384 := qz602

noncomputable abbrev qz37 := qz384

noncomputable abbrev qz603 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz36 qz9))

noncomputable def Ns264p202 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) (@HMul.hMul Real Real Real qz5 qz603 (Zeta.RiemannSiegel.correction qz37)) 25579365 33554432 22115 16777216 73289743147720945755 590295810358705651712 244034498026955780839 Ns264p200 Ns264p201 

noncomputable def Ns264p203 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 567081 1000 118 161 134217728 67108864 2251799813685248 Bool.false 133243764335 1804 

noncomputable def Ns264p204 := Ns264p203 279097919 38 47453128 8 294906479 38 44739240 8 Bool.false 87942678 72400 Bool.true 149574401 Bool.true 48673707 7074237752028440 1 Bool.false 59149977 Bool.true Bool.false 47613828 Bool.true Bool.false 51158730 

noncomputable def Ns264p205 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 567081 1000 14 70 134217728 67108864 2251799813685248 Bool.false 133243764335 1804 

noncomputable def Ns264p206 := Ns264p205 240485871 38 54794152 8 261175631 38 50729528 8 Bool.false 136300360 54020 Bool.true 179601879 Bool.true 105963678 7074237752028440 1 Bool.false 30945879 Bool.true Bool.false 94517043 Bool.true Bool.false 87942678 

noncomputable def Ns264p207 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 567081 1000 131 50 134217728 67108864 2251799813685248 Bool.false 133243764335 1804 

noncomputable def Ns264p208 := Ns264p207 186065264 38 67108856 8 216015088 38 60023992 8 Bool.false 89800230 31879 Bool.false 111126809 Bool.false 204276510 7074237752028440 1 Bool.false 98858413 Bool.false Bool.false 6549601 Bool.true Bool.false 136300360 

noncomputable def Ns264p209 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 567081 1000 381 235 134217728 67108864 2251799813685248 Bool.false 133243764335 1804 

noncomputable def Ns264p210 := Ns264p209 93032624 38 94906264 8 147453232 38 77490640 16 Bool.false 134217720 1854 Bool.false 160990799 Bool.false 81090257 7074237752028440 1 Bool.false 125070614 Bool.true Bool.false 76246244 Bool.false Bool.false 89800230 

noncomputable def Ns264p211 := nat_lit 37171354431313356346536360697329778023050996740397303379 

noncomputable def Ns264p212 := nat_lit 37443063570925706981116872869418935221411479814144000 

noncomputable def Ns264p213 := nat_lit 28149298431303843308068857312480000 

noncomputable def Ns264p214 := nat_lit 95777628569729632440058780907966825280 

noncomputable abbrev qz604 := (@Eq.refl Real qz744)

noncomputable abbrev qz385 := qz604

noncomputable abbrev qz38 := qz385

noncomputable def Ns264p215 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz35 567081 1000 1286324442244 16000000 1134162 4000 2000 Ns264p213 Ns264p214 qz38 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns264p216 := nat_lit 107053500762182466278024718808309760706386870612344233731520 

noncomputable abbrev qz605 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1134162))))

noncomputable abbrev qz386 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 567081 4000) (Real.log (Enclosure.sfrac Bool.false 1286324442244 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz605))

noncomputable abbrev qz606 := (Enclosure.sfrac Bool.false 567081 2000)

noncomputable abbrev qz39 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz386 qz606) (@HMul.hMul Real Real Real qz346 qz606 (Real.log Real.pi)))

noncomputable def Ns264p217 := @Enclosure.Real.IsNear.addLit_ft_p qz39 (Enclosure.sfrac Bool.true Ns264p213 Ns264p214) 1117730038362100843059 1125899906842624000 9927963955301690397 739328000000000000000000 Ns264p213 Ns264p214 0 1 Ns264p216 

noncomputable def Ns264p218 := nat_lit 15001918626631401646226354995200 

noncomputable abbrev qz40 := (@HSub.hSub Real Real Real qz350 qz386 qz606)

noncomputable def Ns264p219 := @Enclosure.Real.IsNear.subLit_ff_p qz40 (@HMul.hMul Real Real Real qz5 qz606 (Real.log Real.pi)) 296634314265715353303 225179981368524800 1797128943910089 361000000000000000000 21782012758641 67108864000 567081 67108864000 Ns264p218 1117730038362100843059 1125899906842624000 

noncomputable def Ns264p220 := nat_lit 2966343142657153533030000 

noncomputable abbrev qz41 := qz386

noncomputable def Ns264p221 := @Enclosure.Real.IsNear.subLit_ff_p qz41 qz606 1802409793864687796787 1125899906842624000 1797128943910089 361000000000000000000 567081 2000 0 1 Ns264p220 296634314265715353303 225179981368524800 1797128943910089 361000000000000000000 

noncomputable def Ns264p222 := nat_lit 4058666038008970234534538184203698176 

noncomputable def Ns264p223 := nat_lit 27308934804727447037149184 

noncomputable def Ns264p224 := nat_lit 17013728713342432361420630049570665138629838376208981969550229252207300218880 

noncomputable def Ns264p225 := nat_lit 59168433468699458794735349406601154454422192545579442540845061807319576576 

noncomputable def Ns264p226 := nat_lit 2708927234686798094658885535976514549523496784040443105493628151459840 

noncomputable def Ns264p227 := BSN.log_dyadic_bound 237748442244 2334900442244 4 3 Ns264p224 67108864 28880000 Ns264p225 Ns264p226 13714087 2572648884488 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 237748442244) (BSN.artanhQ 2334900442244) 0 3 Ns264p225 Ns264p224 Ns264p226 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz387 := (Real.log (Enclosure.sfrac Bool.false 1286324442244 16000000))

noncomputable def Ns264p228 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 567081 4000) qz387 567081 4000 0 1 3179178434043127 281474976710656 781250361 22562500000000000 1802851685555610502287 1125899906842624000 443032235966241 90250000000000000000 (Enclosure.Real.IsNear.const Bool.false 567081 4000) (BSN.isNear_log_sfrac 1286324442244 16000000 3179178434043127 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1286324442244) qz353)) Bool.false Ns264p223 Ns264p92 1000000462080000 28880000000000000000000 3179178434043127 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1286324442244 16000000 16 2572648884488 2097152000000 13714087 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns264p227 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p229 := BSN.arctan_dyadic_bound_f 1000 1134162 1 0 8388608 3610000 0 1 1 0 1 1 7396 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1134162) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1134162) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz388 := (@Nat.cast Real Real.instNatCast 1134162)

noncomputable def Ns264p230 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 qz388)) 884279719003555 562949953421312 1 2000000000000000 7396 8388608 1 3610000 7413712347215469477888 883783381845411 562949953421312 200000000361 722000000000000000 qz17 (Ns264p229 rfl) rfl rfl 

noncomputable abbrev qz389 := (@HMul.hMul Real Real Real qz584 qz589 qz605)

noncomputable abbrev qz42 := qz389

noncomputable abbrev qz390 := qz605

noncomputable abbrev qz43 := qz390

noncomputable def Ns264p231 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 567081 4000) qz387) qz42 1802851685555610502287 1125899906842624000 443032235966241 90250000000000000000 883783381845411 2251799813685248 200000000361 2888000000000000000 Ns264p222 1802409793864687796787 1125899906842624000 1797128943910089 361000000000000000000 (Ns264p228 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz43 1 4 0 1 883783381845411 562949953421312 200000000361 722000000000000000 883783381845411 2251799813685248 200000000361 2888000000000000000 qz361 Ns264p230 rfl) 

noncomputable def Ns264p232 := @Ns264p217 Ns264p211 Ns264p212 9927963955301690397 739328000000000000000000 (@Ns264p219 9927963955301690397 739328000000000000000000 (Ns264p221 (Ns264p231 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 567081 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz606 (Real.log Real.pi) 567081 2000 0 1 38410761 33554432 1 33554432 21782012758641 67108864000 567081 67108864000 (Enclosure.Real.IsNear.const Bool.false 567081 2000) RS265to276.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns264p213 Ns264p214) 

noncomputable def Ns264p233 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns264p211 Ns264p212 9927963955301690397 739328000000000000000000 16655470541 16777216 227 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz362 qz39 (Enclosure.sfrac Bool.true Ns264p213 Ns264p214)) Bool.false Ns264p211 Ns264p212 9927963955301690397 739328000000000000000000 Ns264p215 (Ns264p232 rfl rfl)) 

noncomputable def Ns264p234 := nat_lit 3798258643562398400643072 

noncomputable def Ns264p235 := nat_lit 857414549852651470556171467501627146618914508814499734219137647538790312899265082635459663826877461781663604640195819829673718978646016 

noncomputable def Ns264p236 := nat_lit 611584980451787207388448737255214169266909339662702589998729094684351570900733222665067493877657534481053201965958372573793161216 

noncomputable def Ns264p237 := nat_lit 4281743817013115913313742019173899363398883942134239784606922267827589725987146034920096946657242832638874518452687006095381431861579776 

noncomputable def Ns264p238 := BSN.sin_dyadic_bound_f 53976501754 34359738368 4 3 16777216 7227051 Ns264p235 Ns264p106 Ns264p236 Ns264p237 Ns264p109 Ns264p236 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53976501754) qz363 0 3 Ns264p235 Ns264p106 Ns264p236 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53976501754) qz364 0 3 Ns264p237 Ns264p109 Ns264p236 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p239 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz35) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16655470541) qz375) Bool.false 16655470541 16777216 227 16777216 Bool.false 16777215 16777216 1 3610000 (Ns264p233 rfl) (Enclosure.sfrac_false_div 16655470541 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16655470541) qz375) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns264p234) qz377) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 157 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q3 16655470541 16777216 226375608064910080 72057594037927936 157 Ns264p234 Ns264p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns264p234 Ns264p92 53976501754 34359738368 7227051 7220000 (Ns264p238 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p240 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns264p211 Ns264p212 9927963955301690397 739328000000000000000000 133243764335 134217728 1804 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz362 qz39 (Enclosure.sfrac Bool.true Ns264p213 Ns264p214)) Bool.false Ns264p211 Ns264p212 9927963955301690397 739328000000000000000000 Ns264p215 (Ns264p232 rfl rfl)) 

noncomputable def Ns264p241 := Ns264p210 31879 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 381 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 125070614 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 235 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 76246244 134217728) qz38 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) Bool.false 16777215 16777216 52265451 3785359360000 134217720 134217728 1854 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 16777215 16777216 52265451 3785359360000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz35) qz35) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 16777215 16777216 836247216 60565749760000 16777215 16777216 52265451 3785359360000 (Ns264p239 rfl rfl) rfl)) rfl) (Ns264p240 rfl) RS265to276.d7 

noncomputable def Ns264p242 := nat_lit 659663904612418134704540482302069750750638132718725784747816045250945 

noncomputable def Ns264p243 := nat_lit 38215724400686031908940493885850326479880652218951261491964367528263680 

noncomputable def Ns264p244 := nat_lit 451240889222160498971230086143760022642799850232225002932409993601 

noncomputable def Ns264p245 := nat_lit 1726960598259497331037366890651664211929297243077239167191913359477121 

noncomputable def Ns264p246 := nat_lit 700621614012577251663909054573922652131145290680773127352680071351500800 

noncomputable def Ns264p247 := BSN.sin_dyadic_bound_f 160990799 134217728 3 2 134217728 67108864 Ns264p242 Ns264p243 Ns264p244 Ns264p245 Ns264p246 Ns264p244 125070614 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 160990799) qz369 0 2 Ns264p242 Ns264p243 Ns264p244 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 160990799) qz370 0 2 Ns264p245 Ns264p246 Ns264p244 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p248 := nat_lit 42434116156549997447449159861773121180797178049504211891643422716545 

noncomputable def Ns264p249 := nat_lit 1869603079238757987532999364574202785408044440534593770356060801 

noncomputable def Ns264p250 := nat_lit 111133943909788368658958460496148863907101948533893022754866483016321 

noncomputable def Ns264p251 := BSN.sin_dyadic_bound_f 81090257 134217728 3 2 134217728 67108864 Ns264p248 Ns264p243 Ns264p249 Ns264p250 Ns264p246 Ns264p249 76246244 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 81090257) qz369 0 2 Ns264p248 Ns264p243 Ns264p249 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 81090257) qz370 0 2 Ns264p250 Ns264p246 Ns264p249 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p252 := nat_lit 149680139163488162449050208251496683885391480948537875766383187130305 

noncomputable def Ns264p253 := nat_lit 23256842421213350723739707308376094463556828545613804438594320321 

noncomputable def Ns264p254 := nat_lit 391981758159501318132054966846849182213560500952334871323817289775041 

noncomputable def Ns264p255 := BSN.sin_dyadic_bound_f 111126809 134217728 3 2 134217728 67108864 Ns264p252 Ns264p243 Ns264p253 Ns264p254 Ns264p246 Ns264p253 98858413 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 111126809) qz369 0 2 Ns264p252 Ns264p243 Ns264p253 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 111126809) qz370 0 2 Ns264p254 Ns264p246 Ns264p253 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p256 := nat_lit 3671673223407199906170310382664144222373399118710680835524527304895490416576199627424411120095567424000000 

noncomputable def Ns264p257 := nat_lit 5279844761395943953228111132531743352936527655162577205175730610796471107009227584866801000000000000 

noncomputable def Ns264p258 := nat_lit 22227512457294830993911160983602279903628617374530603818693794681232161533413048047076251522891986905600000 

noncomputable def Ns264p259 := BSN.cos_dyadic_bound_f 204276510 134217728 4 3 134217728 67108864 Ns264p256 Ns264p125 Ns264p257 Ns264p258 Ns264p128 Ns264p257 6549601 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 204276510) qz367 0 3 Ns264p256 Ns264p125 Ns264p257 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 204276510) qz368 0 3 Ns264p258 Ns264p128 Ns264p257 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p260 := Ns264p208 54020 BSN.abs_quadSignPos (BSN.cos_quad_nat3 131 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 98858413 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 50 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 6549601 134217728) qz38 rfl rfl (Ns264p241 RS265to276.d9 RS265to276.d11 RS265to276.d13 RS265to276.d17 (Ns264p247 rfl rfl) (Ns264p251 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns264p240 rfl) RS265to276.d19 RS265to276.d21 RS265to276.d23 RS265to276.d25 RS265to276.d17 (Ns264p255 rfl rfl) (Ns264p259 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns264p261 := nat_lit 2191172550787504985842364181271397791338218471944692749918172567870903228905844044268697679561525370228321 

noncomputable def Ns264p262 := nat_lit 1126498224286018691731611985169184755600023415889803615097715755092112065478785605537112238419807841 

noncomputable def Ns264p263 := nat_lit 13276226623975768264523521862853291253819181412383274281888038090350269481587602825905510978450811868876385 

noncomputable def Ns264p264 := BSN.cos_dyadic_bound_f 179601879 134217728 4 3 134217728 67108864 Ns264p261 Ns264p125 Ns264p262 Ns264p263 Ns264p128 Ns264p262 30945879 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 179601879) qz367 0 3 Ns264p261 Ns264p125 Ns264p262 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 179601879) qz368 0 3 Ns264p263 Ns264p128 Ns264p262 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p265 := nat_lit 68750732369127701115257875727501606610171143607400489076618054697216 

noncomputable def Ns264p266 := nat_lit 15894841222973439951234939716353978316387075389369141494455828736 

noncomputable def Ns264p267 := nat_lit 206220407424937156465871157303072111873880656671422728946865252434176 

noncomputable def Ns264p268 := BSN.cos_dyadic_bound_f 105963678 134217728 3 2 134217728 67108864 Ns264p265 Ns264p115 Ns264p266 Ns264p267 Ns264p118 Ns264p266 94517043 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 105963678) qz367 0 2 Ns264p265 Ns264p115 Ns264p266 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 105963678) qz368 0 2 Ns264p267 Ns264p118 Ns264p266 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p269 := Ns264p206 72400 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 14 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 30945879 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 70 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 94517043 134217728) qz38 rfl rfl (Ns264p260 rfl rfl) (Ns264p240 rfl) RS265to276.d27 RS265to276.d29 RS265to276.d31 RS265to276.d33 RS265to276.d17 (Ns264p264 rfl rfl) (Ns264p268 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p270 := nat_lit 1053009915433963156777978309378358559604292142718680073941790258999666326351909944323318941708375655572481 

noncomputable def Ns264p271 := nat_lit 125397034952291001246595290183644402239767920286560868752083265580767919306776420705670281208652801 

noncomputable def Ns264p272 := nat_lit 6384353151445276824865389362446076078251551136434145644526403555863457238183153673941634825238442534626305 

noncomputable def Ns264p273 := BSN.cos_dyadic_bound_f 149574401 134217728 4 3 134217728 67108864 Ns264p270 Ns264p125 Ns264p271 Ns264p272 Ns264p128 Ns264p271 59149977 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 149574401) qz367 0 3 Ns264p270 Ns264p125 Ns264p271 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 149574401) qz368 0 3 Ns264p272 Ns264p128 Ns264p271 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p274 := nat_lit 5612775787127193191561441178801 

noncomputable def Ns264p275 := BSN.sin_dyadic_bound_f 48673707 134217728 2 1 134217728 67108864 Ns264p274 Ns264p136 Ns264p274 Ns264p274 Ns264p137 Ns264p274 47613828 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 48673707) qz369 0 1 Ns264p274 Ns264p136 Ns264p274 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 48673707) qz370 0 1 Ns264p274 Ns264p137 Ns264p274 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p276 := Ns264p204 88460 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 118 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 59149977 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 161 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 47613828 134217728) qz38 rfl rfl (Ns264p269 rfl) (Ns264p240 rfl) RS265to276.d35 RS265to276.d37 RS265to276.d39 RS265to276.d41 RS265to276.d17 (Ns264p273 rfl rfl) (Ns264p275 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p277 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) 51158730 134217728 88460 134217728 51158730 134217728 88460 134217728 13732817015930880 25579365 33554432 22115 16777216 (Ns264p276 rfl) 

noncomputable def Ns264p278 := @Enclosure.Real.IsNear.mulLit_tf qz603 (Zeta.RiemannSiegel.correction qz37) 5443191 16777216 1 16777216 13464481247805 35184372088832 178885413787093 6350779162034176000 73289743147720945755 590295810358705651712 

noncomputable abbrev qz607 := (@HPow.hPow Real Real Real qz7 qz36 qz9)

noncomputable def Ns264p279 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz607 1 1 0 1 5443191 16777216 1 16777216 5443191 16777216 1 16777216 

noncomputable def Ns264p280 := @Enclosure.Real.IsNear.sqrt_image qz36 1514206643337 16777216000 567081 16777216000 79693416 79693447 8388608 (@Enclosure.Real.IsNear.of_eq qz36 (@HMul.hMul Real Real Real qz5 qz35 qz3) Bool.false 1514206643337 16777216000 567081 16777216000 (BSN.t_div_two_pi_mk qz35 567081 1000 qz38) (@Enclosure.Real.IsNear.mulLit_ff qz35 qz3 567081 1000 0 1 2670177 16777216 1 16777216 1514206643337 16777216000 567081 16777216000 (Enclosure.Real.IsNear.const Bool.false 567081 1000) RS265to276.d44 rfl)) 

noncomputable abbrev qz747 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 567081 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz608 := qz747

noncomputable abbrev qz391 := qz608

noncomputable abbrev qz44 := qz391

noncomputable def Ns264p281 := @Enclosure.Real.IsNear.sqrt_image qz44 159386863 16777216 31 16777216 25855692 25855698 8388608 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 159386863 16777216 31 16777216 159386863 16777216 31 16777216 (Ns264p280 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns264p282 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz44) 25855695 8388608 3 8388608 2721595 2721596 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz44) Bool.false 51711390 16777216 6 16777216 25855695 8388608 3 8388608 (Ns264p281 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns264p283 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 5443191 16777216 1 16777216 5443191 16777216 1 16777216 (Ns264p282 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz392 := (@HMul.hMul Real Real Real qz584 qz582 qz602)

noncomputable abbrev qz45 := (Real.cos qz392)

noncomputable abbrev qz609 := (@HMul.hMul Real Real Real qz735 qz746 qz746)

noncomputable abbrev qz393 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz609 qz602) qz599)

noncomputable abbrev qz46 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz393))

noncomputable def Ns264p284 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz37) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz45) qz46) Bool.false 13464481247805 

noncomputable def Ns264p285 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz45) qz46 16777229 16777216 201 

noncomputable abbrev qz47 := (@Neg.neg Real Real.instNeg (Real.cos qz392))

noncomputable def Ns264p286 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz45) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz47)) Bool.true 16777229 16777216 201 16777216 (BSN.inv_eq_neg_inv_neg qz45) 

noncomputable def Ns264p287 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz47) Bool.false 16777229 16777216 201 16777216 16777229 16777216 

noncomputable def Ns264p288 := @Enclosure.Real.IsNear.recentre' qz45 Bool.true 16777203 16777216 720727216 60565749760000 16777203 16777216 45045451 3785359360000 

noncomputable abbrev qz48 := qz392

noncomputable def Ns264p289 := @Enclosure.Real.IsNear.cos_image qz48 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 26363991) qz365) Bool.false 26363991 8388608 195 16777216 Bool.true 16777203 16777216 1 

noncomputable def Ns264p290 := nat_lit 33462733510098057776864001 

noncomputable def Ns264p291 := nat_lit 2882303761517117440000000000000 

noncomputable def Ns264p292 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz37 884279719003555 140737488355328 1 500000000000000 8391919 16777216 31 16777216 7420803775220594272045 2361183241434822606848 Ns264p290 

noncomputable def Ns264p293 := @Enclosure.Real.IsNear.subLit_ff_p qz44 qz1 159386863 16777216 31 16777216 9 1 0 1 8391919 8391919 16777216 31 

noncomputable def Ns264p294 := @Ns264p293 16777216 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 159386863 16777216 31 16777216 159386863 16777216 31 16777216 (Ns264p280 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns264p295 := @Enclosure.Real.IsNear.recentre' qz48 Bool.false 7420803775220594272045 2361183241434822606848 Ns264p290 Ns264p291 26363991 8388608 195 16777216 (@Ns264p292 Ns264p291 RS265to276.d43 (Ns264p294 rfl rfl) rfl) 

noncomputable abbrev qz394 := (BSN.cosEvenQ 34359738368)

noncomputable abbrev qz395 := (BSN.cosOddQ 34359738368)

noncomputable def Ns264p296 := BSN.cos_dyadic_bound_f 42605499 34359738368 1 0 16777216 7227051 0 1 1 0 1 1 16777203 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 42605499) qz394 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 42605499) qz395 0 0 rfl) rfl rfl 

noncomputable def Ns264p297 := @Ns264p289 3610000 (Ns264p295 rfl) (Enclosure.sfrac_false_div 26363991 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 26363991) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1499047758833093967872) qz366) 226375608064910080 72057594037927936 Bool.false 16777203 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 26363991 8388608 226375608064910080 72057594037927936 0 1499047758833093967872 Ns264p104 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777203 16777216 1499047758833093967872 Ns264p104 42605499 34359738368 7227051 7220000 (Ns264p296 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p298 := @Enclosure.Real.IsNear.inv_image qz47 16777203 16777216 45045451 3785359360000 8388514 8388715 8388608 (@Enclosure.Real.IsNear.neg qz45 Bool.true 16777203 16777216 45045451 3785359360000 (Ns264p288 (Ns264p297 rfl rfl) rfl)) 

noncomputable def Ns264p299 := Ns264p286 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz47) Bool.false 16777229 16777216 201 16777216 (@Ns264p287 201 16777216 (Ns264p298 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p300 := @Enclosure.Real.IsNear.recentre' qz46 Bool.true 3210180 8388608 

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz346 qz343 qz393)

noncomputable def Ns264p301 := @Enclosure.Real.IsNear.cos_image qz49 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16470991)) qz365) Bool.true 16470991 8388608 

noncomputable def Ns264p302 := nat_lit 77782056965960365708088021245 

noncomputable def Ns264p303 := nat_lit 39614081257132168796771975168 

noncomputable def Ns264p304 := nat_lit 28076141089955024869298558010171573 

noncomputable def Ns264p305 := @Enclosure.Real.IsNear.recentre' qz49 Bool.true Ns264p302 Ns264p303 Ns264p304 

noncomputable def Ns264p306 := nat_lit 1208925819614629174706176000000000000000 

noncomputable abbrev qz50 := qz393

noncomputable def Ns264p307 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz50 884279719003555 140737488355328 1 500000000000000 87960919259359 

noncomputable abbrev qz396 := (@HSub.hSub Real Real Real qz588 qz609 qz602)

noncomputable abbrev qz51 := qz396

noncomputable def Ns264p308 := @Enclosure.Real.IsNear.subLit_tf qz51 qz31 70368733214943 281474976710656 1040393635 281474976710656 1 16 

noncomputable abbrev qz397 := qz609

noncomputable abbrev qz52 := qz397

noncomputable def Ns264p309 := @Enclosure.Real.IsNear.subLit_ff_n qz52 qz37 70424304502561 281474976710656 520299939 281474976710656 8391919 16777216 31 16777216 

noncomputable def Ns264p310 := @Enclosure.Real.IsNear.mulLit_ff qz37 qz37 8391919 16777216 31 16777216 8391919 16777216 31 16777216 70424304502561 281474976710656 

noncomputable def Ns264p311 := nat_lit 36337415837196502507763063673260027412883202768884040897933588959957598953336689134162256961 

noncomputable def Ns264p312 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600 

noncomputable def Ns264p313 := nat_lit 398691299787077452467693488958875801389272305258263605613161470109543823212208497468481 

noncomputable def Ns264p314 := nat_lit 219156147927771825851748189093657210654608694460607892070906861481674521668963451303188341825 

noncomputable def Ns264p315 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600 

noncomputable def Ns264p316 := BSN.cos_dyadic_bound_t 16470991 8388608 4 3 8388608 3610000 Ns264p311 Ns264p312 Ns264p313 Ns264p314 Ns264p315 Ns264p313 3210180 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16470991) (BSN.cosEvenQ 8388608) 0 3 Ns264p311 Ns264p312 Ns264p313 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16470991) (BSN.cosOddQ 8388608) 0 3 Ns264p314 Ns264p315 Ns264p313 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p317 := @Ns264p300 1428287216 60565749760000 802545 2097152 89267951 3785359360000 (@Ns264p301 391 16777216 Bool.true 3210180 8388608 1 3610000 (@Ns264p305 Ns264p306 16470991 8388608 391 16777216 (@Ns264p307 281474976710656 1040393635 281474976710656 Ns264p302 Ns264p303 Ns264p304 Ns264p306 RS265to276.d43 (@Ns264p308 0 1 1407374708149744 87960919259359 281474976710656 1040393635 281474976710656 (@Ns264p309 1180591436793473138688 70368733214943 281474976710656 1040393635 281474976710656 (@Ns264p310 520299939 281474976710656 (Ns264p294 rfl rfl) (Ns264p294 rfl rfl) rfl) (Ns264p294 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16470991 8388608) (BSN.cos_neg_of_bound 16470991 8388608 Bool.true 3210180 8388608 1 3610000 (Ns264p316 rfl rfl)) rfl rfl) 

noncomputable def Ns264p318 := @Ns264p278 244034498026955780839 Ns264p200 (Ns264p279 qz33 (@Enclosure.Real.IsNear.of_eq qz607 (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 5443191 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz36 (BSN.t_div_two_pi_nonneg qz35 567081 1000 qz38)) Ns264p283) rfl) (@Ns264p284 35184372088832 178885413787093 6350779162034176000 (BSN.correction_mk qz37 (BSN.cos_two_pi_p_ne_zero_mk qz35 567081 1000 9 qz38 rfl rfl (@BSN.floor_sqrt_eq_dec qz35 567081 1000 9 qz38 rfl rfl rfl))) (@Ns264p285 16777216 802545 2097152 89267951 3785359360000 13464481247805 35184372088832 178885413787093 6350779162034176000 Ns264p299 (Ns264p317 rfl) rfl)) 

noncomputable def Ns264p319 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (hardyZApproximantRS₀ qz35) Bool.false 523286691125744021595 590295810358705651712 35355904790123406340839 Ns264p200 (@Eq.refl Real (hardyZApproximantRS₀ qz35)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) (@HMul.hMul Real Real Real qz5 qz603 (Zeta.RiemannSiegel.correction qz37))) Bool.false 523286691125744021595 590295810358705651712 35355904790123406340839 Ns264p200 (BSN.hardyZApproximantRS₀_eq qz35 9 (@BSN.floor_sqrt_eq_dec qz35 567081 1000 9 qz38 rfl rfl rfl)) (@Ns264p202 523286691125744021595 590295810358705651712 35355904790123406340839 Ns264p200 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 9)) Bool.false 25579365 33554432 22115 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) (Ns264p277 (Ns264p276 rfl) rfl rfl)) (Ns264p318 rfl) rfl rfl)) 

theorem RS265to276.d47 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz35) Bool.false 523286691125744021595 590295810358705651712 35355904790123406340839 Ns264p200 := Ns264p319 

noncomputable abbrev qz610 := (@HMul.hMul Real Real Real qz735 (Real.sqrt qz743) qz737)

noncomputable abbrev qz398 := qz610

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv qz398)

noncomputable abbrev qz399 := (@HMul.hMul Real Real Real qz584 (@HMul.hMul Real Real Real qz584 qz610 qz610) qz610)

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz346 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz399))

noncomputable abbrev qz400 := (@HMul.hMul Real Real Real qz584 qz597 qz597)

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz346 qz400 qz372))

noncomputable abbrev qz611 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz53)

noncomputable def Ns264p320 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz362 (@HAdd.hAdd Real Real Real qz362 qz611 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55)) Bool.false 

noncomputable def Ns264p321 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz362 qz611 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55) 12099001 536870912 

noncomputable def Ns264p322 := @Enclosure.Real.IsNear.addLit_ff qz611 qz54 1512375 67108864 25 67108864 

noncomputable def Ns264p323 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz53 25 4 0 1 60495 16777216 1 16777216 1512375 

noncomputable def Ns264p324 := @Enclosure.Real.IsNear.recentre' qz53 Bool.false 60495 16777216 1 16777216 60495 16777216 1 16777216 

noncomputable def Ns264p325 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz8 3229971 1048576 3 8388608 302095815249 3355443200 113137 3355443200 975760722475627779 3518437208883200 1914860808687 

noncomputable def Ns264p326 := @Enclosure.Real.IsNear.sqrt_image qz8 302095815249 3355443200 113137 3355443200 79595264 79595294 8388608 qz21 

noncomputable def Ns264p327 := @Enclosure.Real.IsNear.sqrt_image qz22 79595279 8388608 15 8388608 25839765 25839771 8388608 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 159190558 16777216 30 16777216 79595279 8388608 15 8388608 (Ns264p326 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz401 := (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 51679536 16777216 6 16777216 3229971 1048576 3 8388608 (Ns264p327 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns264p328 := @Ns264p325 14073748835532800 qz401 

noncomputable def Ns264p329 := Ns264p328 qz21 

noncomputable abbrev qz56 := qz398

noncomputable def Ns264p330 := @Enclosure.Real.IsNear.inv_image qz56 975760722475627779 3518437208883200 1914860808687 14073748835532800 30247 30248 8388608 (Ns264p329 rfl) rfl rfl 

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv qz399)

noncomputable def Ns264p331 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz57 1 32 0 1 1 

noncomputable def Ns264p332 := @Enclosure.Real.IsNear.recentre' qz57 Bool.false 1 16777216 1 16777216 

noncomputable def Ns264p333 := nat_lit 929030553544063474850689316740266373682414171838650139 

noncomputable def Ns264p334 := nat_lit 43556142965880123323311949751266331066368000000 

noncomputable def Ns264p335 := nat_lit 87511539852774551729322746423125309848542976385731 

noncomputable def Ns264p336 := nat_lit 2787593149816327892691964784081045188247552000000 

noncomputable abbrev qz58 := qz399

noncomputable def Ns264p337 := @Enclosure.Real.IsNear.inv_image qz58 Ns264p333 Ns264p334 Ns264p335 Ns264p336 0 1 

noncomputable def Ns264p338 := nat_lit 952108987526159094306814660156472841 

noncomputable def Ns264p339 := nat_lit 12379400392853802748991242240000 

noncomputable def Ns264p340 := nat_lit 14947571395689452529783148393353 

noncomputable def Ns264p341 := nat_lit 198070406285660843983859875840000 

noncomputable abbrev qz402 := (@HMul.hMul Real Real Real qz584 qz610 qz610)

noncomputable abbrev qz59 := qz402

noncomputable def Ns264p342 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz56 Ns264p338 Ns264p339 Ns264p340 Ns264p341 975760722475627779 3518437208883200 1914860808687 

noncomputable def Ns264p343 := @Enclosure.Real.IsNear.mulLit_ff qz56 qz56 975760722475627779 3518437208883200 1914860808687 14073748835532800 975760722475627779 3518437208883200 1914860808687 14073748835532800 Ns264p338 

noncomputable def Ns264p344 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz55 13 10 0 1 574015 16777216 1 

noncomputable def Ns264p345 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 574015 16777216 1 16777216 574015 16777216 

noncomputable abbrev qz60 := qz400

noncomputable def Ns264p346 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz23 10432712660841 1099511627776 155038617 70368744177664 3229971 1048576 3 8388608 33697359345849265611 

noncomputable def Ns264p347 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz23 3229971 1048576 3 8388608 3229971 1048576 3 8388608 10432712660841 1099511627776 155038617 

noncomputable def Ns264p348 := @Ns264p347 70368744177664 qz401 

noncomputable def Ns264p349 := Ns264p348 qz401 

noncomputable def Ns264p350 := @Ns264p346 1152921504606846976 6009243190318179 590295810358705651712 (Ns264p349 rfl) qz401 

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz346 qz400 qz372)

noncomputable def Ns264p351 := @Enclosure.Real.IsNear.inv_image qz61 33697359345849265611 1152921504606846976 6009243190318179 590295810358705651712 287007 287008 8388608 (Ns264p350 rfl) 

noncomputable def Ns264p352 := @Ns264p321 201 536870912 1492439 33554432 13 167772160 1207222193356800 35978025 536870912 1213 2684354560 (@Ns264p322 1 536870912 1 536870912 811950212644864 12099001 536870912 201 536870912 (@Ns264p323 67108864 25 67108864 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns264p324 (Ns264p330 rfl rfl rfl rfl) rfl) rfl) (@Ns264p331 16777216 1 16777216 1 536870912 1 536870912 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns264p332 1 16777216 1 16777216 (@Ns264p337 8388608 (@Ns264p342 14073748835532800 Ns264p333 Ns264p334 Ns264p335 Ns264p336 (@Ns264p343 Ns264p339 Ns264p340 Ns264p341 (Ns264p329 rfl) (Ns264p329 rfl) rfl) (Ns264p329 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns264p344 16777216 1492439 33554432 13 167772160 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns264p345 1 16777216 (Ns264p351 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS265to276.d48 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 := @Ns264p320 35978025 536870912 1213 2684354560 (BSN.hardyZErrorBoundRS₀_mk qz4 565685 1000 qz11 rfl rfl) (Ns264p352 rfl rfl) 

noncomputable def Ns264p353 := nat_lit 4261935750789854805360640 

noncomputable def Ns264p354 := nat_lit 164252011529118566733517422592 

noncomputable abbrev qz748 := (Enclosure.sfrac Bool.false 568476 1000)

noncomputable abbrev qz612 := qz748

noncomputable abbrev qz403 := qz612

noncomputable abbrev qz62 := qz403

noncomputable abbrev qz749 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 568476 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz613 := qz749

noncomputable abbrev qz404 := qz613

noncomputable abbrev qz63 := qz404

noncomputable abbrev qz750 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 568476 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz614 := qz750

noncomputable abbrev qz405 := qz614

noncomputable abbrev qz64 := qz405

noncomputable abbrev qz615 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz63 qz9))

noncomputable def Ns264p355 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (@HMul.hMul Real Real Real qz5 qz615 (Zeta.RiemannSiegel.correction qz64)) 77895761 67108864 88673 67108864 293167738957608820899 2361183241434822606848 39574917306258656717 Ns264p353 Ns264p354 

noncomputable def Ns264p356 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 568476 1000 118 161 134217728 67108864 2251799813685248 Bool.false 133665400921 1808 

noncomputable def Ns264p357 := Ns264p356 279097919 38 47453128 8 294906479 38 44739240 8 Bool.true 34798546 72573 Bool.true 117279412 Bool.true 38431659 7074237752028440 1 Bool.false 86156731 Bool.true Bool.false 37908641 Bool.true Bool.true 77895761 

noncomputable def Ns264p358 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 568476 1000 14 70 134217728 67108864 2251799813685248 Bool.false 133665400921 1808 

noncomputable def Ns264p359 := Ns264p358 240485871 38 54794152 8 261175631 38 50729528 8 Bool.false 54674997 54148 Bool.true 93443083 Bool.true 48667098 7074237752028440 1 Bool.false 102982757 Bool.true Bool.false 125490677 Bool.true Bool.true 34798546 

noncomputable def Ns264p360 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 568476 1000 132 51 134217728 67108864 2251799813685248 Bool.false 133665400921 1808 

noncomputable def Ns264p361 := Ns264p360 186065264 38 67108856 8 216015088 38 60023992 8 Bool.true 50310613 31953 Bool.false 62373637 Bool.false 113743334 7074237752028440 1 Bool.false 119983558 Bool.false Bool.false 100609283 Bool.false Bool.false 54674997 

noncomputable def Ns264p362 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 568476 1000 383 236 134217728 67108864 2251799813685248 Bool.false 133665400921 1808 

noncomputable def Ns264p363 := Ns264p362 93032624 38 94906264 8 147453232 38 77490640 16 Bool.true 134217720 1854 Bool.false 31189446 Bool.false 86200871 7074237752028440 1 Bool.false 30909496 Bool.false Bool.false 107475129 Bool.false Bool.true 50310613 

noncomputable def Ns264p364 := nat_lit 144358645151754944327040562596113810923268894000121 

noncomputable def Ns264p365 := nat_lit 144955158446633079528717419066015608414928896000 

noncomputable def Ns264p366 := nat_lit 28497237378129317262753656340480000 

noncomputable def Ns264p367 := nat_lit 97200008185185321849469599991600250880 

noncomputable abbrev qz616 := (@Eq.refl Real qz748)

noncomputable abbrev qz406 := qz616

noncomputable abbrev qz65 := qz406

noncomputable def Ns264p368 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz62 568476 1000 1292660850304 16000000 1136952 4000 2000 Ns264p366 Ns264p367 qz65 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns264p369 := nat_lit 13623390962878193325240379646830437186240984341556378992640 

noncomputable abbrev qz617 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1136952))))

noncomputable abbrev qz407 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 568476 4000) (Real.log (Enclosure.sfrac Bool.false 1292660850304 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz617))

noncomputable abbrev qz618 := (Enclosure.sfrac Bool.false 568476 2000)

noncomputable abbrev qz66 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz407 qz618) (@HMul.hMul Real Real Real qz346 qz618 (Real.log Real.pi)))

noncomputable def Ns264p370 := @Enclosure.Real.IsNear.addLit_ft_p qz66 (Enclosure.sfrac Bool.true Ns264p366 Ns264p367) 140158372698411029253 140737488355328000 2488065114795750003 184832000000000000000000 Ns264p366 Ns264p367 0 1 Ns264p369 

noncomputable def Ns264p371 := nat_lit 18811738343757957556479197184 

noncomputable abbrev qz67 := (@HSub.hSub Real Real Real qz350 qz407 qz618)

noncomputable def Ns264p372 := @Enclosure.Real.IsNear.subLit_ff_p qz67 (@HMul.hMul Real Real Real qz5 qz618 (Real.log Real.pi)) 1487607488313223977 1125899906842624 1801488320924469 361000000000000000000 5458898942559 16777216000 142119 16777216000 Ns264p371 140158372698411029253 140737488355328000 

noncomputable abbrev qz68 := qz407

noncomputable def Ns264p373 := @Enclosure.Real.IsNear.subLit_ff_p qz68 qz618 225953878254294717189 140737488355328000 1801488320924469 361000000000000000000 568476 2000 0 1 371901872078305994250000 1487607488313223977 1125899906842624 1801488320924469 361000000000000000000 

noncomputable def Ns264p374 := nat_lit 1017605801908960107558154064042655744 

noncomputable def Ns264p375 := nat_lit 27320815840976405690056704 

noncomputable def Ns264p376 := nat_lit 17292644204100241020547115471850170728807072161228266544602932998653953966080 

noncomputable def Ns264p377 := nat_lit 63063194361510873732161701353340020154558071195288790098193377154371158016 

noncomputable def Ns264p378 := nat_lit 3172022122757303143765422845877003652394696671818176114745159387709440 

noncomputable def Ns264p379 := BSN.log_dyadic_bound 244084850304 2341236850304 4 3 Ns264p376 67108864 28880000 Ns264p377 Ns264p378 14043852 2585321700608 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 244084850304) (BSN.artanhQ 2341236850304) 0 3 Ns264p377 Ns264p376 Ns264p378 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz408 := (Real.log (Enclosure.sfrac Bool.false 1292660850304 16000000))

noncomputable def Ns264p380 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 568476 4000) qz408 568476 4000 0 1 3180561568701687 281474976710656 781250361 22562500000000000 452018229582315054753 281474976710656000 111030520054959 22562500000000000000 (Enclosure.Real.IsNear.const Bool.false 568476 4000) (BSN.isNear_log_sfrac 1292660850304 16000000 3180561568701687 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1292660850304) qz353)) Bool.false Ns264p375 Ns264p92 1000000462080000 28880000000000000000000 3180561568701687 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1292660850304 16000000 16 2585321700608 2097152000000 14043852 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns264p379 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p381 := BSN.arctan_dyadic_bound_f 1000 1136952 1 0 8388608 3610000 0 1 1 0 1 1 7378 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1136952) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1136952) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz409 := (@Nat.cast Real Real.instNatCast 1136952)

noncomputable def Ns264p382 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 qz409)) 884279719003555 562949953421312 1 2000000000000000 7378 8388608 1 3610000 7413722480314631061504 883784589804963 562949953421312 200000000361 722000000000000000 qz17 (Ns264p381 rfl) rfl rfl 

noncomputable abbrev qz410 := (@HMul.hMul Real Real Real qz584 qz589 qz617)

noncomputable abbrev qz69 := qz410

noncomputable abbrev qz411 := qz617

noncomputable abbrev qz70 := qz411

noncomputable def Ns264p383 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 568476 4000) qz408) qz69 452018229582315054753 281474976710656000 111030520054959 22562500000000000000 883784589804963 2251799813685248 200000000361 2888000000000000000 Ns264p374 225953878254294717189 140737488355328000 1801488320924469 361000000000000000000 (Ns264p380 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz70 1 4 0 1 883784589804963 562949953421312 200000000361 722000000000000000 883784589804963 2251799813685248 200000000361 2888000000000000000 qz361 Ns264p382 rfl) 

noncomputable def Ns264p384 := @Ns264p370 Ns264p364 Ns264p365 2488065114795750003 184832000000000000000000 (@Ns264p372 2488065114795750003 184832000000000000000000 (Ns264p373 (Ns264p383 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 568476 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz618 (Real.log Real.pi) 568476 2000 0 1 38410761 33554432 1 33554432 5458898942559 16777216000 142119 16777216000 (Enclosure.Real.IsNear.const Bool.false 568476 2000) RS265to276.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns264p366 Ns264p367) 

noncomputable def Ns264p385 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns264p364 Ns264p365 2488065114795750003 184832000000000000000000 16708175115 16777216 227 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz362 qz66 (Enclosure.sfrac Bool.true Ns264p366 Ns264p367)) Bool.false Ns264p364 Ns264p365 2488065114795750003 184832000000000000000000 Ns264p368 (Ns264p384 rfl rfl)) 

noncomputable def Ns264p386 := nat_lit 3797883290757584954327040 

noncomputable def Ns264p387 := nat_lit 857074991949048321008231772380617273805722406276648284103620666995196186302146907842986840933304577189501096726387700531330058406400000 

noncomputable def Ns264p388 := nat_lit 610860115438648240362086446515250615263086427326033749618166767262694804108115585089730818719303910164131562838437761000000000000 

noncomputable def Ns264p389 := nat_lit 4280050239944601410119083339306759949147866250755572315441071243535504415352179886283671247759307946470357681081844461302164628032000000 

noncomputable def Ns264p390 := BSN.sin_dyadic_bound_f 53971167670 34359738368 4 3 16777216 7227051 Ns264p387 Ns264p106 Ns264p388 Ns264p389 Ns264p109 Ns264p388 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53971167670) qz363 0 3 Ns264p387 Ns264p106 Ns264p388 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53971167670) qz364 0 3 Ns264p389 Ns264p109 Ns264p388 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p391 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz62) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16708175115) qz375) Bool.false 16708175115 16777216 227 16777216 Bool.true 16777215 16777216 1 3610000 (Ns264p385 rfl) (Enclosure.sfrac_false_div 16708175115 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16708175115) qz375) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns264p386) qz377) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 158 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q1 16708175115 16777216 226375608064910080 72057594037927936 158 Ns264p386 Ns264p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns264p386 Ns264p92 53971167670 34359738368 7227051 7220000 (Ns264p390 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p392 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns264p364 Ns264p365 2488065114795750003 184832000000000000000000 133665400921 134217728 1808 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz362 qz66 (Enclosure.sfrac Bool.true Ns264p366 Ns264p367)) Bool.false Ns264p364 Ns264p365 2488065114795750003 184832000000000000000000 Ns264p368 (Ns264p384 rfl rfl)) 

noncomputable def Ns264p393 := Ns264p363 31953 BSN.abs_quadSignPos (BSN.cos_quad_nat3 383 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 30909496 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 236 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 107475129 134217728) qz65 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) Bool.true 16777215 16777216 52265451 3785359360000 134217720 134217728 1854 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 16777215 16777216 52265451 3785359360000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz62) qz62) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 16777215 16777216 836247216 60565749760000 16777215 16777216 52265451 3785359360000 (Ns264p391 rfl rfl) rfl)) rfl) (Ns264p392 rfl) RS265to276.d7 

noncomputable def Ns264p394 := nat_lit 946303928041329399854348791056 

noncomputable def Ns264p395 := BSN.sin_dyadic_bound_f 31189446 134217728 2 1 134217728 67108864 Ns264p394 Ns264p136 Ns264p394 Ns264p394 Ns264p137 Ns264p394 30909496 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 31189446) qz369 0 1 Ns264p394 Ns264p136 Ns264p394 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 31189446) qz370 0 1 Ns264p394 Ns264p137 Ns264p394 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p396 := nat_lit 30105053982755429835281555970012567730953710023442978372619957128641 

noncomputable def Ns264p397 := nat_lit 3048549370671891448725847192048474645560959682823601405674868161 

noncomputable def Ns264p398 := nat_lit 90309064849524945722947216215653606243570008150963287915048521649601 

noncomputable def Ns264p399 := BSN.cos_dyadic_bound_f 86200871 134217728 3 2 134217728 67108864 Ns264p396 Ns264p115 Ns264p397 Ns264p398 Ns264p118 Ns264p397 107475129 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 86200871) qz367 0 2 Ns264p396 Ns264p115 Ns264p397 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 86200871) qz368 0 2 Ns264p398 Ns264p118 Ns264p397 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p400 := nat_lit 8252112577409751543917567257904648772205616302608791460232090783201 

noncomputable def Ns264p401 := nat_lit 229091274124779345591450171955475131953717658294124759400484321 

noncomputable def Ns264p402 := nat_lit 24755879549681005073061518873370035366352941472509786131177471380961 

noncomputable def Ns264p403 := BSN.cos_dyadic_bound_f 62373637 134217728 3 2 134217728 67108864 Ns264p400 Ns264p115 Ns264p401 Ns264p402 Ns264p118 Ns264p401 119983558 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 62373637) qz367 0 2 Ns264p400 Ns264p115 Ns264p401 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 62373637) qz368 0 2 Ns264p402 Ns264p118 Ns264p401 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p404 := nat_lit 164285488052496042779343437447379370085279776901464646800140580430080 

noncomputable def Ns264p405 := nat_lit 28016096960027003293425365769327726389331342699397906783152906496 

noncomputable def Ns264p406 := nat_lit 430226156932887687369138695103319438666340498282322668817957367849216 

noncomputable def Ns264p407 := BSN.sin_dyadic_bound_f 113743334 134217728 3 2 134217728 67108864 Ns264p404 Ns264p243 Ns264p405 Ns264p406 Ns264p246 Ns264p405 100609283 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 113743334) qz369 0 2 Ns264p404 Ns264p243 Ns264p405 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 113743334) qz370 0 2 Ns264p406 Ns264p246 Ns264p405 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p408 := Ns264p361 54148 BSN.abs_quadSignPos (BSN.cos_quad_nat0 132 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 119983558 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 51 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 100609283 134217728) qz65 rfl rfl (Ns264p393 RS265to276.d9 RS265to276.d11 RS265to276.d13 RS265to276.d17 (Ns264p395 rfl rfl) (Ns264p399 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns264p392 rfl) RS265to276.d19 RS265to276.d21 RS265to276.d23 RS265to276.d25 RS265to276.d17 (Ns264p403 rfl rfl) (Ns264p407 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns264p409 := nat_lit 41571737606981918099673994370504587698965603680450245116004131322721 

noncomputable def Ns264p410 := nat_lit 5812691454930416225903049429118322137947921458405678074626227041 

noncomputable def Ns264p411 := nat_lit 124703587438035893466570177012655526452620915198433923991863141514081 

noncomputable def Ns264p412 := BSN.cos_dyadic_bound_f 93443083 134217728 3 2 134217728 67108864 Ns264p409 Ns264p115 Ns264p410 Ns264p411 Ns264p118 Ns264p410 102982757 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 93443083) qz367 0 2 Ns264p409 Ns264p115 Ns264p410 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 93443083) qz368 0 2 Ns264p411 Ns264p118 Ns264p410 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p413 := nat_lit 3058405618887394732764567189539944462135985268963371474548508795136 

noncomputable def Ns264p414 := nat_lit 31469047767211822568351902264974786195117070640191007411609856 

noncomputable def Ns264p415 := nat_lit 9175153918566649774648564864815303436835565572748834041630703165696 

noncomputable def Ns264p416 := BSN.cos_dyadic_bound_f 48667098 134217728 3 2 134217728 67108864 Ns264p413 Ns264p115 Ns264p414 Ns264p415 Ns264p118 Ns264p414 125490677 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 48667098) qz367 0 2 Ns264p413 Ns264p115 Ns264p414 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 48667098) qz368 0 2 Ns264p415 Ns264p118 Ns264p414 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p417 := Ns264p359 72573 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 14 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 102982757 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 70 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 125490677 134217728) qz65 rfl rfl (Ns264p408 rfl rfl) (Ns264p392 rfl) RS265to276.d27 RS265to276.d29 RS265to276.d31 RS265to276.d33 RS265to276.d17 (Ns264p412 rfl rfl) (Ns264p416 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p418 := nat_lit 103177882365840438220504518273207690258969004315552418937190628786176 

noncomputable def Ns264p419 := nat_lit 35791033493298072175532837861750721622873966742384679182149943296 

noncomputable def Ns264p420 := nat_lit 309462065030534718517162489143899569333661265013172487453207586471936 

noncomputable def Ns264p421 := BSN.cos_dyadic_bound_f 117279412 134217728 3 2 134217728 67108864 Ns264p418 Ns264p115 Ns264p419 Ns264p420 Ns264p118 Ns264p419 86156731 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 117279412) qz367 0 2 Ns264p418 Ns264p115 Ns264p419 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 117279412) qz368 0 2 Ns264p420 Ns264p118 Ns264p419 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p422 := nat_lit 2181506589513753173370446582961 

noncomputable def Ns264p423 := BSN.sin_dyadic_bound_f 38431659 134217728 2 1 134217728 67108864 Ns264p422 Ns264p136 Ns264p422 Ns264p422 Ns264p137 Ns264p422 37908641 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 38431659) qz369 0 1 Ns264p422 Ns264p136 Ns264p422 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 38431659) qz370 0 1 Ns264p422 Ns264p137 Ns264p422 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p424 := Ns264p357 88673 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 118 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 86156731 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 161 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 37908641 134217728) qz65 rfl rfl (Ns264p417 rfl) (Ns264p392 rfl) RS265to276.d35 RS265to276.d37 RS265to276.d39 RS265to276.d41 RS265to276.d17 (Ns264p421 rfl rfl) (Ns264p423 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p425 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) 77895761 134217728 88673 134217728 77895761 134217728 88673 134217728 20909984124502016 77895761 67108864 88673 67108864 (Ns264p424 rfl) 

noncomputable def Ns264p426 := @Enclosure.Real.IsNear.mulLit_tf qz615 (Zeta.RiemannSiegel.correction qz64) 5439849 16777216 1 16777216 53892624401451 140737488355328 181427985694523 6350779162034176000 293167738957608820899 2361183241434822606848 

noncomputable abbrev qz619 := (@HPow.hPow Real Real Real qz7 qz63 qz9)

noncomputable def Ns264p427 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz619 1 1 0 1 5439849 16777216 1 16777216 5439849 16777216 1 16777216 

noncomputable def Ns264p428 := @Enclosure.Real.IsNear.sqrt_image qz63 379482885063 4194304000 142119 4194304000 79791377 79791408 8388608 (@Enclosure.Real.IsNear.of_eq qz63 (@HMul.hMul Real Real Real qz5 qz62 qz3) Bool.false 379482885063 4194304000 142119 4194304000 (BSN.t_div_two_pi_mk qz62 568476 1000 qz65) (@Enclosure.Real.IsNear.mulLit_ff qz62 qz3 568476 1000 0 1 2670177 16777216 1 16777216 379482885063 4194304000 142119 4194304000 (Enclosure.Real.IsNear.const Bool.false 568476 1000) RS265to276.d44 rfl)) 

noncomputable abbrev qz751 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 568476 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz620 := qz751

noncomputable abbrev qz412 := qz620

noncomputable abbrev qz71 := qz412

noncomputable def Ns264p429 := @Enclosure.Real.IsNear.sqrt_image qz71 159582785 16777216 31 16777216 25871578 25871584 8388608 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 159582785 16777216 31 16777216 159582785 16777216 31 16777216 (Ns264p428 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns264p430 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz71) 25871581 8388608 3 8388608 2719924 2719925 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz71) Bool.false 51743162 16777216 6 16777216 25871581 8388608 3 8388608 (Ns264p429 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns264p431 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 5439849 16777216 1 16777216 5439849 16777216 1 16777216 (Ns264p430 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz413 := (@HMul.hMul Real Real Real qz584 qz582 qz614)

noncomputable abbrev qz72 := (Real.cos qz413)

noncomputable abbrev qz621 := (@HMul.hMul Real Real Real qz735 qz750 qz750)

noncomputable abbrev qz414 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz621 qz614) qz599)

noncomputable abbrev qz73 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz414))

noncomputable def Ns264p432 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz64) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz72) qz73) Bool.false 53892624401451 

noncomputable def Ns264p433 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz72) qz73 16824027 16777216 203 

noncomputable abbrev qz74 := (@Neg.neg Real Real.instNeg (Real.cos qz413))

noncomputable def Ns264p434 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz72) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz74)) Bool.true 16824027 16777216 203 16777216 (BSN.inv_eq_neg_inv_neg qz72) 

noncomputable def Ns264p435 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz74) Bool.false 16824027 16777216 203 16777216 16824027 16777216 

noncomputable def Ns264p436 := @Enclosure.Real.IsNear.recentre' qz72 Bool.true 16730536 16777216 181084304 15141437440000 2091317 2097152 11317769 946339840000 

noncomputable abbrev qz75 := qz413

noncomputable abbrev qz415 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable def Ns264p437 := @Enclosure.Real.IsNear.cos_image qz75 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13489749) qz415) Bool.false 13489749 4194304 49 4194304 Bool.true 16730536 16777216 1 

noncomputable def Ns264p438 := nat_lit 836568337754134401586733849 

noncomputable def Ns264p439 := nat_lit 72057594037927936000000000000000 

noncomputable def Ns264p440 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz64 884279719003555 140737488355328 1 500000000000000 8587841 16777216 31 16777216 7594053626327208774755 2361183241434822606848 Ns264p438 

noncomputable def Ns264p441 := @Enclosure.Real.IsNear.subLit_ff_p qz71 qz1 159582785 16777216 31 16777216 9 1 0 1 8587841 8587841 16777216 31 

noncomputable def Ns264p442 := @Ns264p441 16777216 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 159582785 16777216 31 16777216 159582785 16777216 31 16777216 (Ns264p428 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns264p443 := @Enclosure.Real.IsNear.recentre' qz75 Bool.false 7594053626327208774755 2361183241434822606848 Ns264p438 Ns264p439 13489749 4194304 49 4194304 (@Ns264p440 Ns264p439 RS265to276.d43 (Ns264p442 rfl rfl) rfl) 

noncomputable def Ns264p444 := nat_lit 43200008939029253627904742141300404081 

noncomputable def Ns264p445 := nat_lit 33451117797795934712303577408972542258970624 

noncomputable def Ns264p446 := nat_lit 501766766966939020684553661134588133884559360 

noncomputable def Ns264p447 := BSN.cos_dyadic_bound_f 2563722171 34359738368 2 1 16777216 7227051 Ns264p444 Ns264p445 Ns264p444 Ns264p444 Ns264p446 Ns264p444 16730536 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 2563722171) qz394 0 1 Ns264p444 Ns264p445 Ns264p444 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 2563722171) qz395 0 1 Ns264p444 Ns264p446 Ns264p444 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p448 := @Ns264p437 3610000 (Ns264p443 rfl) (Enclosure.sfrac_false_div 13489749 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13489749) qz415) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 45101477412919457087488) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 16730536 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 13489749 4194304 226375608064910080 72057594037927936 0 45101477412919457087488 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16730536 16777216 45101477412919457087488 604462909807314587353088 2563722171 34359738368 7227051 7220000 (Ns264p447 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p449 := @Enclosure.Real.IsNear.inv_image qz74 2091317 2097152 11317769 946339840000 8411912 8412115 8388608 (@Enclosure.Real.IsNear.neg qz72 Bool.true 2091317 2097152 11317769 946339840000 (Ns264p436 (Ns264p448 rfl rfl) rfl)) 

noncomputable def Ns264p450 := Ns264p434 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz74) Bool.false 16824027 16777216 203 16777216 (@Ns264p435 203 16777216 (Ns264p449 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p451 := @Enclosure.Real.IsNear.recentre' qz73 Bool.true 3203313 8388608 

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz346 qz343 qz414)

noncomputable def Ns264p452 := @Enclosure.Real.IsNear.cos_image qz76 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 2057945)) (@Nat.cast Real Real.instNatCast 1048576)) Bool.true 2057945 1048576 

noncomputable def Ns264p453 := nat_lit 77746966248117827580251127005 

noncomputable def Ns264p454 := nat_lit 5680789074732941819957979046956581 

noncomputable def Ns264p455 := @Enclosure.Real.IsNear.recentre' qz76 Bool.true Ns264p453 Ns264p303 Ns264p454 

noncomputable def Ns264p456 := nat_lit 241785163922925834941235200000000000000 

noncomputable abbrev qz77 := qz414

noncomputable def Ns264p457 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz77 884279719003555 140737488355328 1 500000000000000 87921236433791 

noncomputable abbrev qz416 := (@HSub.hSub Real Real Real qz588 qz621 qz614)

noncomputable abbrev qz78 := qz416

noncomputable def Ns264p458 := @Enclosure.Real.IsNear.subLit_tf qz78 qz31 70329050389375 281474976710656 1052540799 281474976710656 1 16 

noncomputable abbrev qz417 := qz621

noncomputable abbrev qz79 := qz417

noncomputable def Ns264p459 := @Enclosure.Real.IsNear.subLit_ff_n qz79 qz64 73751013041281 281474976710656 532447103 281474976710656 8587841 16777216 31 16777216 

noncomputable def Ns264p460 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz64 8587841 16777216 31 16777216 8587841 16777216 31 16777216 73751013041281 281474976710656 

noncomputable def Ns264p461 := nat_lit 527817022941721818309896701265799665302845548451721202689084022580373591659390625 

noncomputable def Ns264p462 := nat_lit 846322570984149739285326836131859157750990110577656481930582364989086940895641600 

noncomputable def Ns264p463 := nat_lit 5770389981203367841426434084658803116982390719668455848506348507207275390625 

noncomputable def Ns264p464 := nat_lit 3183373466203288591697934372117000396879168203063936858854042273109804134404990625 

noncomputable def Ns264p465 := nat_lit 77015353959557626274964742087999183355340100062566739855682995214006911621503385600 

noncomputable def Ns264p466 := BSN.cos_dyadic_bound_t 2057945 1048576 4 3 8388608 3610000 Ns264p461 Ns264p462 Ns264p463 Ns264p464 Ns264p465 Ns264p463 3203313 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 2057945) (BSN.cosEvenQ 1048576) 0 3 Ns264p461 Ns264p462 Ns264p463 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 2057945) (BSN.cosOddQ 1048576) 0 3 Ns264p464 Ns264p465 Ns264p463 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p467 := @Ns264p451 361584304 15141437440000 3203313 8388608 22599019 946339840000 (@Ns264p452 99 4194304 Bool.true 3203313 8388608 1 3610000 (@Ns264p455 Ns264p456 2057945 1048576 99 4194304 (@Ns264p457 281474976710656 1052540799 281474976710656 Ns264p453 Ns264p303 Ns264p454 Ns264p456 RS265to276.d43 (@Ns264p458 0 1 1406739782940656 87921236433791 281474976710656 1052540799 281474976710656 (@Ns264p459 1179925669457428480000 70329050389375 281474976710656 1052540799 281474976710656 (@Ns264p460 532447103 281474976710656 (Ns264p442 rfl rfl) (Ns264p442 rfl rfl) rfl) (Ns264p442 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 2057945 1048576) (BSN.cos_neg_of_bound 2057945 1048576 Bool.true 3203313 8388608 1 3610000 (Ns264p466 rfl rfl)) rfl rfl) 

noncomputable def Ns264p468 := @Ns264p426 39574917306258656717 Ns264p353 (Ns264p427 qz33 (@Enclosure.Real.IsNear.of_eq qz619 (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 5439849 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz63 (BSN.t_div_two_pi_nonneg qz62 568476 1000 qz65)) Ns264p431) rfl) (@Ns264p432 140737488355328 181427985694523 6350779162034176000 (BSN.correction_mk qz64 (BSN.cos_two_pi_p_ne_zero_mk qz62 568476 1000 9 qz65 rfl rfl (@BSN.floor_sqrt_eq_dec qz62 568476 1000 9 qz65 rfl rfl rfl))) (@Ns264p433 16777216 3203313 8388608 22599019 946339840000 53892624401451 140737488355328 181427985694523 6350779162034176000 Ns264p450 (Ns264p467 rfl) rfl)) 

noncomputable def Ns264p469 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (hardyZApproximantRS₀ qz62) Bool.true 2447545700209119420253 2361183241434822606848 5671001323656823541197 Ns264p353 (@Eq.refl Real (hardyZApproximantRS₀ qz62)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (@HMul.hMul Real Real Real qz5 qz615 (Zeta.RiemannSiegel.correction qz64))) Bool.true 2447545700209119420253 2361183241434822606848 5671001323656823541197 Ns264p353 (BSN.hardyZApproximantRS₀_eq qz62 9 (@BSN.floor_sqrt_eq_dec qz62 568476 1000 9 qz65 rfl rfl rfl)) (@Ns264p355 2447545700209119420253 2361183241434822606848 5671001323656823541197 Ns264p353 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 9)) Bool.true 77895761 67108864 88673 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (Ns264p425 (Ns264p424 rfl) rfl rfl)) (Ns264p468 rfl) rfl rfl)) 

theorem RS265to276.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz62) Bool.true 2447545700209119420253 2361183241434822606848 5671001323656823541197 Ns264p353 := Ns264p469 

noncomputable def Ns264p470 := nat_lit 106548393769746370134016000 

noncomputable def Ns264p471 := nat_lit 67018676328191193739285233664 

noncomputable abbrev qz752 := (Enclosure.sfrac Bool.false 569870 1000)

noncomputable abbrev qz622 := qz752

noncomputable abbrev qz418 := qz622

noncomputable abbrev qz80 := qz418

noncomputable abbrev qz753 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 569870 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz623 := qz753

noncomputable abbrev qz419 := qz623

noncomputable abbrev qz81 := qz419

noncomputable abbrev qz754 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 569870 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz624 := qz754

noncomputable abbrev qz420 := qz624

noncomputable abbrev qz82 := qz420

noncomputable abbrev qz625 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz81 qz9))

noncomputable def Ns264p472 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) (@HMul.hMul Real Real Real qz5 qz625 (Zeta.RiemannSiegel.correction qz82)) 24212045 33554432 88887 67108864 293540997306269532897 2361183241434822606848 1004449736150280377211 Ns264p470 Ns264p471 

noncomputable def Ns264p473 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 569870 1000 118 161 134217728 67108864 2251799813685248 Bool.false 134086964954 1813 

noncomputable def Ns264p474 := Ns264p473 279097919 38 47453128 8 294906479 38 44739240 8 Bool.false 95976602 72748 Bool.true 84777878 Bool.true 27967258 7074237752028440 1 Bool.false 108321439 Bool.true Bool.false 27765311 Bool.true Bool.false 48424090 

noncomputable def Ns264p475 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 569870 1000 14 69 134217728 67108864 2251799813685248 Bool.false 134086964954 1813 

noncomputable def Ns264p476 := Ns264p475 240485871 38 54794152 8 261175631 38 50729528 8 Bool.false 201313834 54277 Bool.true 7116354 Bool.true 202010608 7074237752028440 1 Bool.false 134029114 Bool.true Bool.false 133928157 Bool.true Bool.false 95976602 

noncomputable def Ns264p477 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 569870 1000 133 52 134217728 67108864 2251799813685248 Bool.false 134086964954 1813 

noncomputable def Ns264p478 := Ns264p477 186065264 38 67108856 8 216015088 38 60023992 8 Bool.false 149051186 32027 Bool.false 13733978 Bool.false 23353620 7074237752028440 1 Bool.false 13710023 Bool.true Bool.false 132191106 Bool.false Bool.false 201313834 

noncomputable def Ns264p479 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 569870 1000 384 237 134217728 67108864 2251799813685248 Bool.false 134086964954 1813 

noncomputable def Ns264p480 := Ns264p479 93032624 38 94906264 8 147453232 38 77490640 16 Bool.false 134217688 1854 Bool.false 112237287 Bool.false 91386384 7074237752028440 1 Bool.false 89961202 Bool.false Bool.false 84487147 Bool.true Bool.false 149051186 

noncomputable def Ns264p481 := nat_lit 34671668520605037029860268773564859307441332005739 

noncomputable def Ns264p482 := nat_lit 34705480703281253986287001670460580617938534400 

noncomputable def Ns264p483 := nat_lit 28848355292460668224769936000000000 

noncomputable def Ns264p484 := nat_lit 98638908819115312059827265529920000000 

noncomputable abbrev qz626 := (@Eq.refl Real qz752)

noncomputable abbrev qz421 := qz626

noncomputable abbrev qz83 := qz421

noncomputable def Ns264p485 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz80 569870 1000 1299008267600 16000000 1139740 4000 2000 Ns264p483 Ns264p484 qz83 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns264p486 := nat_lit 11094933926593611849555286007540754978381226241836480000000 

noncomputable abbrev qz627 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1139740))))

noncomputable abbrev qz422 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 569870 4000) (Real.log (Enclosure.sfrac Bool.false 1299008267600 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz627))

noncomputable abbrev qz628 := (Enclosure.sfrac Bool.false 569870 2000)

noncomputable abbrev qz84 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz422 qz628) (@HMul.hMul Real Real Real qz346 qz628 (Real.log Real.pi)))

noncomputable def Ns264p487 := @Enclosure.Real.IsNear.addLit_ft_p qz84 (Enclosure.sfrac Bool.true Ns264p483 Ns264p484) 112480331620209172919 112589990684262400 997653954621564919 73932800000000000000000 Ns264p483 Ns264p484 0 1 Ns264p486 

noncomputable def Ns264p488 := nat_lit 754842727737551703697365401600 

noncomputable abbrev qz85 := (@HSub.hSub Real Real Real qz350 qz422 qz628)

noncomputable def Ns264p489 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (@HMul.hMul Real Real Real qz5 qz628 (Real.log Real.pi)) 149204215226185327031 112589990684262400 361168914587481 72200000000000000000 2188914037107 6710886400 56987 6710886400 Ns264p488 112480331620209172919 112589990684262400 

noncomputable abbrev qz86 := qz422

noncomputable def Ns264p490 := @Enclosure.Real.IsNear.subLit_ff_p qz86 qz628 7251401768872225359 4503599627370496 361168914587481 72200000000000000000 569870 2000 0 1 11936337218094826162480 149204215226185327031 112589990684262400 361168914587481 72200000000000000000 

noncomputable def Ns264p491 := nat_lit 16328705152103354843606212549804032 

noncomputable def Ns264p492 := nat_lit 27332659299190073563545600 

noncomputable def Ns264p493 := nat_lit 17575854212542843154855202200709216813202373113045379888109588480000000000000 

noncomputable def Ns264p494 := nat_lit 67129370511059114844388169911750247818098711982765275312746496000000000000 

noncomputable def Ns264p495 := nat_lit 3700266251910593215418156716353081990878469482246521712640000000000000 

noncomputable def Ns264p496 := BSN.log_dyadic_bound 250432267600 2347584267600 4 3 Ns264p493 67108864 28880000 Ns264p494 Ns264p495 14372574 2598016535200 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 250432267600) (BSN.artanhQ 2347584267600) 0 3 Ns264p494 Ns264p493 Ns264p495 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz423 := (Real.log (Enclosure.sfrac Bool.false 1299008267600 16000000))

noncomputable def Ns264p497 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 569870 4000) qz423 569870 4000 0 1 3181940328701175 281474976710656 781250361 22562500000000000 7253169340467754389 4503599627370496 44521114322307 9025000000000000000 (Enclosure.Real.IsNear.const Bool.false 569870 4000) (BSN.isNear_log_sfrac 1299008267600 16000000 3181940328701175 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1299008267600) qz353)) Bool.false Ns264p492 Ns264p92 1000000462080000 28880000000000000000000 3181940328701175 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1299008267600 16000000 16 2598016535200 2097152000000 14372574 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns264p496 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p498 := BSN.arctan_dyadic_bound_f 1000 1139740 1 0 8388608 3610000 0 1 1 0 1 1 7360 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1139740) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1139740) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns264p499 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1139740))) 884279719003555 562949953421312 1 2000000000000000 7360 8388608 1 3610000 7413732613413792645120 883785797764515 562949953421312 200000000361 722000000000000000 qz17 (Ns264p498 rfl) rfl rfl 

noncomputable abbrev qz424 := (@HMul.hMul Real Real Real qz584 qz589 qz627)

noncomputable abbrev qz87 := qz424

noncomputable abbrev qz425 := qz627

noncomputable abbrev qz88 := qz425

noncomputable def Ns264p500 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 569870 4000) qz423) qz87 7253169340467754389 4503599627370496 44521114322307 9025000000000000000 883785797764515 2251799813685248 200000000361 2888000000000000000 Ns264p491 7251401768872225359 4503599627370496 361168914587481 72200000000000000000 (Ns264p497 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz88 1 4 0 1 883785797764515 562949953421312 200000000361 722000000000000000 883785797764515 2251799813685248 200000000361 2888000000000000000 qz361 Ns264p499 rfl) 

noncomputable def Ns264p501 := @Ns264p487 Ns264p481 Ns264p482 997653954621564919 73932800000000000000000 (@Ns264p489 997653954621564919 73932800000000000000000 (Ns264p490 (Ns264p500 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 569870 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz628 (Real.log Real.pi) 569870 2000 0 1 38410761 33554432 1 33554432 2188914037107 6710886400 56987 6710886400 (Enclosure.Real.IsNear.const Bool.false 569870 2000) RS265to276.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns264p483 Ns264p484) 

noncomputable def Ns264p502 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns264p481 Ns264p482 997653954621564919 73932800000000000000000 16760870619 16777216 227 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz362 qz84 (Enclosure.sfrac Bool.true Ns264p483 Ns264p484)) Bool.false Ns264p481 Ns264p482 997653954621564919 73932800000000000000000 Ns264p485 (Ns264p501 rfl rfl)) 

noncomputable def Ns264p503 := nat_lit 3796200813196923495251968 

noncomputable def Ns264p504 := nat_lit 855554204229407552810723146705231562053239337342587966597578952558391847083548068437171930761609493192317047947242787846819368332824576 

noncomputable def Ns264p505 := nat_lit 607620654226453989217788026466356552160208384863770409049350956469567665073880575172067135740155285474847721267792368487558680576 

noncomputable def Ns264p506 := nat_lit 4272465147402244795021559263800139815942829348167927609399419358188378738802207721154432531682969686796119032218507596261605391092289536 

noncomputable def Ns264p507 := BSN.sin_dyadic_bound_f 53947258226 34359738368 4 3 16777216 7227051 Ns264p504 Ns264p106 Ns264p505 Ns264p506 Ns264p109 Ns264p505 16777211 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53947258226) qz363 0 3 Ns264p504 Ns264p106 Ns264p505 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53947258226) qz364 0 3 Ns264p506 Ns264p109 Ns264p505 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p508 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz80) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16760870619) qz375) Bool.false 16760870619 16777216 227 16777216 Bool.false 16777211 16777216 1 3610000 (Ns264p502 rfl) (Enclosure.sfrac_false_div 16760870619 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16760870619) qz375) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns264p503) qz377) 226375608064910080 72057594037927936 Bool.false 16777211 16777216 158 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q3 16760870619 16777216 226375608064910080 72057594037927936 158 Ns264p503 Ns264p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777211 16777216 Ns264p503 Ns264p92 53947258226 34359738368 7227051 7220000 (Ns264p507 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p509 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns264p481 Ns264p482 997653954621564919 73932800000000000000000 134086964954 134217728 1813 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz362 qz84 (Enclosure.sfrac Bool.true Ns264p483 Ns264p484)) Bool.false Ns264p481 Ns264p482 997653954621564919 73932800000000000000000 Ns264p485 (Ns264p501 rfl rfl)) 

noncomputable def Ns264p510 := Ns264p480 32027 BSN.abs_quadSignPos (BSN.cos_quad_nat0 384 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 89961202 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 237 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 84487147 134217728) qz83 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) Bool.false 16777211 16777216 52265451 3785359360000 134217688 134217728 1854 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 16777211 16777216 52265451 3785359360000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz80) qz80) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 16777211 16777216 836247216 60565749760000 16777211 16777216 52265451 3785359360000 (Ns264p508 rfl rfl) rfl)) rfl) (Ns264p509 rfl) RS265to276.d7 

noncomputable def Ns264p511 := nat_lit 86541386200422278184980221474859454929531509996250814108579765540801 

noncomputable def Ns264p512 := nat_lit 25182409567892987403378414090007935669412914572132557219924137921 

noncomputable def Ns264p513 := nat_lit 259573793782131048580133907596398348917255704159608177211299448346561 

noncomputable def Ns264p514 := BSN.cos_dyadic_bound_f 112237287 134217728 3 2 134217728 67108864 Ns264p511 Ns264p115 Ns264p512 Ns264p513 Ns264p118 Ns264p512 89961202 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 112237287) qz367 0 2 Ns264p511 Ns264p115 Ns264p512 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 112237287) qz368 0 2 Ns264p513 Ns264p118 Ns264p512 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p515 := nat_lit 68450741591408401297006117260821087981979474607793074104953607290880 

noncomputable def Ns264p516 := nat_lit 4864653896383888241158308512466081901601273630348960057939460096 

noncomputable def Ns264p517 := nat_lit 179267875680713572339768431755035047248772221910723200530022783778816 

noncomputable def Ns264p518 := BSN.sin_dyadic_bound_f 91386384 134217728 3 2 134217728 67108864 Ns264p515 Ns264p243 Ns264p516 Ns264p517 Ns264p246 Ns264p516 84487147 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 91386384) qz369 0 2 Ns264p515 Ns264p243 Ns264p516 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 91386384) qz370 0 2 Ns264p517 Ns264p246 Ns264p516 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p519 := nat_lit 35578316113629376346465706256 

noncomputable def Ns264p520 := BSN.sin_dyadic_bound_f 13733978 134217728 2 1 134217728 67108864 Ns264p519 Ns264p136 Ns264p519 Ns264p519 Ns264p137 Ns264p519 13710023 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 13733978) qz369 0 1 Ns264p519 Ns264p136 Ns264p519 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 13733978) qz370 0 1 Ns264p519 Ns264p137 Ns264p519 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p521 := nat_lit 297451961468593248200499360000 

noncomputable def Ns264p522 := nat_lit 7788445287802241442795744493830144 

noncomputable def Ns264p523 := nat_lit 116826679317033621641936167407452160 

noncomputable def Ns264p524 := BSN.cos_dyadic_bound_f 23353620 134217728 2 1 134217728 67108864 Ns264p521 Ns264p522 Ns264p521 Ns264p521 Ns264p523 Ns264p521 132191106 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 23353620) qz367 0 1 Ns264p521 Ns264p522 Ns264p521 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 23353620) qz368 0 1 Ns264p521 Ns264p523 Ns264p521 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p525 := Ns264p478 54277 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 133 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 13710023 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 132191106 134217728) qz83 rfl rfl (Ns264p510 RS265to276.d9 RS265to276.d11 RS265to276.d13 RS265to276.d17 (Ns264p514 rfl rfl) (Ns264p518 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns264p509 rfl) RS265to276.d19 RS265to276.d21 RS265to276.d23 RS265to276.d25 RS265to276.d17 (Ns264p520 rfl rfl) (Ns264p524 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns264p526 := nat_lit 2564662224197144084376995856 

noncomputable def Ns264p527 := BSN.cos_dyadic_bound_f 7116354 134217728 2 1 134217728 67108864 Ns264p526 Ns264p522 Ns264p526 Ns264p526 Ns264p523 Ns264p526 134029114 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 7116354) qz367 0 1 Ns264p526 Ns264p522 Ns264p526 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 7116354) qz368 0 1 Ns264p526 Ns264p523 Ns264p526 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p528 := nat_lit 9116149084567051051510407406987584718716260631496765617519695050895241312211416029740856515400034508865536 

noncomputable def Ns264p529 := nat_lit 212813371219357667808056223692308629509040396751503069069405487845990478953701519077062806287447472524492800 

noncomputable def Ns264p530 := nat_lit 4618384735669086209897325791098026559451229424000894793572212046091105475668200750166938304313819136 

noncomputable def Ns264p531 := nat_lit 45532992001365811163072703476512948597392881281033462782502507213620427910474803274418915308257373423927296 

noncomputable def Ns264p532 := nat_lit 7448467992677518373281967829230802032816413886302607417429192074609666763379553167697198220060661538357248000 

noncomputable def Ns264p533 := BSN.sin_dyadic_bound_f 202010608 134217728 4 3 134217728 67108864 Ns264p528 Ns264p529 Ns264p530 Ns264p531 Ns264p532 Ns264p530 133928157 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 202010608) qz369 0 3 Ns264p528 Ns264p529 Ns264p530 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 202010608) qz370 0 3 Ns264p531 Ns264p532 Ns264p530 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p534 := Ns264p476 72748 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 14 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 134029114 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 69 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133928157 134217728) qz83 rfl rfl (Ns264p525 rfl rfl) (Ns264p509 rfl) RS265to276.d27 RS265to276.d29 RS265to276.d31 RS265to276.d33 RS265to276.d17 (Ns264p527 rfl rfl) (Ns264p533 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p535 := nat_lit 28165672735955064699283708879839306743852774165777561839167449948416 

noncomputable def Ns264p536 := nat_lit 2668457777413039766872984526989267618789135952116046650277191936 

noncomputable def Ns264p537 := nat_lit 84491681292310368018317380670463941696320744225428453424201795461376 

noncomputable def Ns264p538 := BSN.cos_dyadic_bound_f 84777878 134217728 3 2 134217728 67108864 Ns264p535 Ns264p115 Ns264p536 Ns264p537 Ns264p118 Ns264p536 108321439 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 84777878) qz367 0 2 Ns264p535 Ns264p115 Ns264p536 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 84777878) qz368 0 2 Ns264p537 Ns264p118 Ns264p536 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p539 := nat_lit 611786029403277416484047182096 

noncomputable def Ns264p540 := BSN.sin_dyadic_bound_f 27967258 134217728 2 1 134217728 67108864 Ns264p539 Ns264p136 Ns264p539 Ns264p539 Ns264p137 Ns264p539 27765311 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 27967258) qz369 0 1 Ns264p539 Ns264p136 Ns264p539 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 27967258) qz370 0 1 Ns264p539 Ns264p137 Ns264p539 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p541 := Ns264p474 88887 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 118 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 108321439 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 161 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 27765311 134217728) qz83 rfl rfl (Ns264p534 rfl) (Ns264p509 rfl) RS265to276.d35 RS265to276.d37 RS265to276.d39 RS265to276.d41 RS265to276.d17 (Ns264p538 rfl rfl) (Ns264p540 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p542 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) 48424090 134217728 88887 134217728 48424090 134217728 88887 134217728 12998742680535040 24212045 33554432 88887 67108864 (Ns264p541 rfl) 

noncomputable def Ns264p543 := @Enclosure.Real.IsNear.mulLit_tf qz625 (Zeta.RiemannSiegel.correction qz82) 5436519 16777216 1 16777216 53994292543863 140737488355328 921557580675909 31753895810170880000 293540997306269532897 2361183241434822606848 

noncomputable abbrev qz629 := (@HPow.hPow Real Real Real qz7 qz81 qz9)

noncomputable def Ns264p544 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz629 1 1 0 1 5436519 16777216 1 16777216 5436519 16777216 1 16777216 

noncomputable def Ns264p545 := @Enclosure.Real.IsNear.sqrt_image qz81 152165376699 1677721600 56987 1677721600 79889148 79889179 8388608 (@Enclosure.Real.IsNear.of_eq qz81 (@HMul.hMul Real Real Real qz5 qz80 qz3) Bool.false 152165376699 1677721600 56987 1677721600 (BSN.t_div_two_pi_mk qz80 569870 1000 qz83) (@Enclosure.Real.IsNear.mulLit_ff qz80 qz3 569870 1000 0 1 2670177 16777216 1 16777216 152165376699 1677721600 56987 1677721600 (Enclosure.Real.IsNear.const Bool.false 569870 1000) RS265to276.d44 rfl)) 

noncomputable abbrev qz755 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 569870 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz630 := qz755

noncomputable abbrev qz426 := qz630

noncomputable abbrev qz89 := qz426

noncomputable def Ns264p546 := @Enclosure.Real.IsNear.sqrt_image qz89 159778327 16777216 31 16777216 25887424 25887430 8388608 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 159778327 16777216 31 16777216 159778327 16777216 31 16777216 (Ns264p545 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns264p547 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz89) 25887427 8388608 3 8388608 2718259 2718260 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz89) Bool.false 51774854 16777216 6 16777216 25887427 8388608 3 8388608 (Ns264p546 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns264p548 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 5436519 16777216 1 16777216 5436519 16777216 1 16777216 (Ns264p547 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz427 := (@HMul.hMul Real Real Real qz584 qz582 qz624)

noncomputable abbrev qz90 := (Real.cos qz427)

noncomputable abbrev qz631 := (@HMul.hMul Real Real Real qz735 qz754 qz754)

noncomputable abbrev qz428 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz631 qz624) qz599)

noncomputable abbrev qz91 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz428))

noncomputable def Ns264p549 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz82) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz90) qz91) Bool.false 53994292543863 

noncomputable def Ns264p550 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz90) qz91 16962263 16777216 205 

noncomputable abbrev qz92 := (@Neg.neg Real Real.instNeg (Real.cos qz427))

noncomputable def Ns264p551 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz90) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz92)) Bool.true 16962263 16777216 205 16777216 (BSN.inv_eq_neg_inv_neg qz90) 

noncomputable def Ns264p552 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz92) Bool.false 16962263 16777216 205 16777216 16962263 16777216 

noncomputable def Ns264p553 := @Enclosure.Real.IsNear.recentre' qz90 Bool.true 16594187 16777216 720727216 60565749760000 16594187 16777216 45045451 3785359360000 

noncomputable abbrev qz93 := qz427

noncomputable def Ns264p554 := @Enclosure.Real.IsNear.cos_image qz93 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 55187623) qz375) Bool.false 55187623 16777216 195 16777216 Bool.true 16594187 16777216 1 

noncomputable def Ns264p555 := nat_lit 836568337755814094576722713 

noncomputable def Ns264p556 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz82 884279719003555 140737488355328 1 500000000000000 8783383 16777216 31 16777216 7766967451140601926565 2361183241434822606848 Ns264p555 

noncomputable def Ns264p557 := @Enclosure.Real.IsNear.subLit_ff_p qz89 qz1 159778327 16777216 31 16777216 9 1 0 1 8783383 8783383 16777216 31 

noncomputable def Ns264p558 := @Ns264p557 16777216 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 159778327 16777216 31 16777216 159778327 16777216 31 16777216 (Ns264p545 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns264p559 := @Enclosure.Real.IsNear.recentre' qz93 Bool.false 7766967451140601926565 2361183241434822606848 Ns264p555 Ns264p439 55187623 16777216 195 16777216 (@Ns264p556 Ns264p439 RS265to276.d43 (Ns264p558 rfl rfl) rfl) 

noncomputable def Ns264p560 := nat_lit 665944202051645169474713067725409521521 

noncomputable def Ns264p561 := BSN.cos_dyadic_bound_f 5079950267 34359738368 2 1 16777216 7227051 Ns264p560 Ns264p445 Ns264p560 Ns264p560 Ns264p446 Ns264p560 16594187 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 5079950267) qz394 0 1 Ns264p560 Ns264p445 Ns264p560 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 5079950267) qz395 0 1 Ns264p560 Ns264p446 Ns264p560 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p562 := @Ns264p554 3610000 (Ns264p559 rfl) (Enclosure.sfrac_false_div 55187623 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 55187623) qz375) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 357469720831752400797696) qz377) 226375608064910080 72057594037927936 Bool.false 16594187 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 55187623 16777216 226375608064910080 72057594037927936 0 357469720831752400797696 Ns264p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16594187 16777216 357469720831752400797696 Ns264p92 5079950267 34359738368 7227051 7220000 (Ns264p561 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p563 := @Enclosure.Real.IsNear.inv_image qz92 16594187 16777216 45045451 3785359360000 8481029 8481234 8388608 (@Enclosure.Real.IsNear.neg qz90 Bool.true 16594187 16777216 45045451 3785359360000 (Ns264p553 (Ns264p562 rfl rfl) rfl)) 

noncomputable def Ns264p564 := Ns264p551 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz92) Bool.false 16962263 16777216 205 16777216 (@Ns264p552 205 16777216 (Ns264p563 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p565 := @Enclosure.Real.IsNear.recentre' qz91 Bool.true 3183201 8388608 

noncomputable abbrev qz94 := (@HMul.hMul Real Real Real qz346 qz343 qz428)

noncomputable def Ns264p566 := @Enclosure.Real.IsNear.cos_image qz94 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8220905)) qz415) Bool.true 8220905 4194304 

noncomputable def Ns264p567 := nat_lit 77644254052868073540930772525 

noncomputable def Ns264p568 := nat_lit 28731113865437099374372766238653061 

noncomputable def Ns264p569 := @Enclosure.Real.IsNear.recentre' qz94 Bool.true Ns264p567 Ns264p303 Ns264p568 

noncomputable abbrev qz95 := qz428

noncomputable def Ns264p570 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz95 884279719003555 140737488355328 1 500000000000000 87805082921455 

noncomputable abbrev qz429 := (@HSub.hSub Real Real Real qz588 qz631 qz624)

noncomputable abbrev qz96 := qz429

noncomputable def Ns264p571 := @Enclosure.Real.IsNear.subLit_tf qz96 qz31 70212896877039 281474976710656 1064664403 281474976710656 1 16 

noncomputable abbrev qz430 := qz631

noncomputable abbrev qz97 := qz430

noncomputable def Ns264p572 := @Enclosure.Real.IsNear.subLit_ff_n qz97 qz82 77147816924689 281474976710656 544570707 281474976710656 8783383 16777216 31 16777216 

noncomputable def Ns264p573 := @Enclosure.Real.IsNear.mulLit_ff qz82 qz82 8783383 16777216 31 16777216 8783383 16777216 31 16777216 77147816924689 281474976710656 

noncomputable def Ns264p574 := nat_lit 8808190237887659018443273313524142172249167280635820446207081262115431067167270294390625 

noncomputable def Ns264p575 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600 

noncomputable def Ns264p576 := nat_lit 95287417072876559091223209725203708156431357937750320197670688849099401504150390625 

noncomputable def Ns264p577 := nat_lit 53125649765703703382824253360538555622193715825143827233302922735878256701755768623990625 

noncomputable def Ns264p578 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600 

noncomputable def Ns264p579 := BSN.cos_dyadic_bound_t 8220905 4194304 4 3 8388608 3610000 Ns264p574 Ns264p575 Ns264p576 Ns264p577 Ns264p578 Ns264p576 3183201 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 8220905) (BSN.cosEvenQ 4194304) 0 3 Ns264p574 Ns264p575 Ns264p576 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 8220905) (BSN.cosOddQ 4194304) 0 3 Ns264p577 Ns264p578 Ns264p576 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p580 := @Ns264p565 91298576 3785359360000 3183201 8388608 5706161 236584960000 (@Ns264p566 25 1048576 Bool.true 3183201 8388608 1 3610000 (@Ns264p569 Ns264p306 8220905 4194304 25 1048576 (@Ns264p570 281474976710656 1064664403 281474976710656 Ns264p567 Ns264p303 Ns264p568 Ns264p306 RS265to276.d43 (@Ns264p571 0 1 1404881326743280 87805082921455 281474976710656 1064664403 281474976710656 (@Ns264p572 1177976936891808743424 70212896877039 281474976710656 1064664403 281474976710656 (@Ns264p573 544570707 281474976710656 (Ns264p558 rfl rfl) (Ns264p558 rfl rfl) rfl) (Ns264p558 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8220905 4194304) (BSN.cos_neg_of_bound 8220905 4194304 Bool.true 3183201 8388608 1 3610000 (Ns264p579 rfl rfl)) rfl rfl) 

noncomputable def Ns264p581 := @Ns264p543 1004449736150280377211 Ns264p470 (Ns264p544 qz33 (@Enclosure.Real.IsNear.of_eq qz629 (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 5436519 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz81 (BSN.t_div_two_pi_nonneg qz80 569870 1000 qz83)) Ns264p548) rfl) (@Ns264p549 140737488355328 921557580675909 31753895810170880000 (BSN.correction_mk qz82 (BSN.cos_two_pi_p_ne_zero_mk qz80 569870 1000 9 qz83 rfl rfl (@BSN.floor_sqrt_eq_dec qz80 569870 1000 9 qz83 rfl rfl rfl))) (@Ns264p550 16777216 3183201 8388608 5706161 236584960000 53994292543863 140737488355328 921557580675909 31753895810170880000 Ns264p564 (Ns264p580 rfl) rfl)) 

noncomputable def Ns264p582 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (hardyZApproximantRS₀ qz80) Bool.false 1997312197929358295777 2361183241434822606848 142129876580083230905211 Ns264p470 (@Eq.refl Real (hardyZApproximantRS₀ qz80)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) (@HMul.hMul Real Real Real qz5 qz625 (Zeta.RiemannSiegel.correction qz82))) Bool.false 1997312197929358295777 2361183241434822606848 142129876580083230905211 Ns264p470 (BSN.hardyZApproximantRS₀_eq qz80 9 (@BSN.floor_sqrt_eq_dec qz80 569870 1000 9 qz83 rfl rfl rfl)) (@Ns264p472 1997312197929358295777 2361183241434822606848 142129876580083230905211 Ns264p470 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 9)) Bool.false 24212045 33554432 88887 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) (Ns264p542 (Ns264p541 rfl) rfl rfl)) (Ns264p581 rfl) rfl rfl)) 

theorem RS265to276.d50 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz80) Bool.false 1997312197929358295777 2361183241434822606848 142129876580083230905211 Ns264p470 := Ns264p582 

noncomputable def Ns264p583 := nat_lit 33511006593355747010631696384 

noncomputable abbrev qz756 := (Enclosure.sfrac Bool.false 571264 1000)

noncomputable abbrev qz632 := qz756

noncomputable abbrev qz431 := qz632

noncomputable abbrev qz98 := qz431

noncomputable abbrev qz757 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 571264 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz633 := qz757

noncomputable abbrev qz432 := qz633

noncomputable abbrev qz99 := qz432

noncomputable abbrev qz758 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 571264 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz634 := qz758

noncomputable abbrev qz433 := qz634

noncomputable abbrev qz100 := qz433

noncomputable abbrev qz635 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz99 qz9))

noncomputable def Ns264p584 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) (@HMul.hMul Real Real Real qz5 qz635 (Zeta.RiemannSiegel.correction qz100)) 462522699 67108864 89103 67108864 9196174645153284243 73786976294838206464 257419751327838225 26637098442436592533504 Ns264p583 

noncomputable def Ns264p585 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 571264 1000 118 161 134217728 67108864 2251799813685248 Bool.false 134508757578 1816 

noncomputable def Ns264p586 := Ns264p585 279097919 38 47453128 8 294906479 38 44739240 8 Bool.true 412850830 72925 Bool.true 52047753 Bool.true 17274266 7074237752028440 1 Bool.false 124251865 Bool.true Bool.false 17226615 Bool.true Bool.true 462522699 

noncomputable def Ns264p587 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 571264 1000 13 69 134217728 67108864 2251799813685248 Bool.false 134508757578 1816 

noncomputable def Ns264p588 := Ns264p587 240485871 38 54794152 8 261175631 38 50729528 8 Bool.true 322753631 54410 Bool.true 131389749 Bool.true 144296814 7074237752028440 1 Bool.false 111387404 Bool.true Bool.false 118062659 Bool.true Bool.true 412850830 

noncomputable def Ns264p589 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 571264 1000 133 52 134217728 67108864 2251799813685248 Bool.false 134508757578 1816 

noncomputable def Ns264p590 := Ns264p589 186065264 38 67108856 8 216015088 38 60023992 8 Bool.true 286530863 32107 Bool.false 176151624 Bool.false 144021211 7074237752028440 1 Bool.false 129762927 Bool.true Bool.false 64082775 Bool.false Bool.true 322753631 

noncomputable def Ns264p591 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 571264 1000 385 238 134217728 67108864 2251799813685248 Bool.false 134508757578 1816 

noncomputable def Ns264p592 := Ns264p591 93032624 38 94906264 8 147453232 38 77490640 16 Bool.true 134217720 1862 Bool.false 193513719 Bool.false 96800489 7074237752028440 1 Bool.false 133102400 Bool.true Bool.false 100797624 Bool.true Bool.true 286530863 

noncomputable def Ns264p593 := nat_lit 21541957695805714332212882539980644141261507233848361 

noncomputable def Ns264p594 := nat_lit 21495348486320072237407978879700318847410110464000 

noncomputable def Ns264p595 := nat_lit 29202925643441851588502770155520000 

noncomputable def Ns264p596 := nat_lit 100095516472682693216055533288513863680 

noncomputable abbrev qz636 := (@Eq.refl Real qz756)

noncomputable abbrev qz434 := qz636

noncomputable abbrev qz101 := qz434

noncomputable def Ns264p597 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz98 571264 1000 1305371230784 16000000 1142528 4000 2000 Ns264p595 Ns264p596 qz101 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns264p598 := nat_lit 28235474791046465889518069402803429888834282761549723729920 

noncomputable abbrev qz637 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1142528))))

noncomputable abbrev qz435 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 571264 4000) (Real.log (Enclosure.sfrac Bool.false 1305371230784 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz637))

noncomputable abbrev qz638 := (Enclosure.sfrac Bool.false 571264 2000)

noncomputable abbrev qz102 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz435 qz638) (@HMul.hMul Real Real Real qz346 qz638 (Real.log Real.pi)))

noncomputable def Ns264p599 := @Enclosure.Real.IsNear.addLit_ft_p qz102 (Enclosure.sfrac Bool.true Ns264p595 Ns264p596) 282085392092912517769 281474976710656000 78131395572252331 5776000000000000000000 Ns264p595 Ns264p596 0 1 Ns264p598 

noncomputable def Ns264p600 := nat_lit 29578797209921783623214694400 

noncomputable abbrev qz103 := (@HSub.hSub Real Real Real qz350 qz435 qz638)

noncomputable def Ns264p601 := @Enclosure.Real.IsNear.subLit_ff_p qz103 (@HMul.hMul Real Real Real qz5 qz638 (Real.log Real.pi)) 74823936688261870517 56294995342131200 1810200824950341 361000000000000000000 171427226343 524288000 4463 524288000 Ns264p600 282085392092912517769 281474976710656000 

noncomputable abbrev qz104 := qz435

noncomputable def Ns264p602 := @Enclosure.Real.IsNear.subLit_ff_p qz104 qz638 454517943989127447177 281474976710656000 1810200824950341 361000000000000000000 571264 2000 0 1 748239366882618705170000 74823936688261870517 56294995342131200 1810200824950341 361000000000000000000 

noncomputable def Ns264p603 := nat_lit 31983856924728724114656174463254528 

noncomputable def Ns264p604 := nat_lit 27344473790250938190004224 

noncomputable def Ns264p605 := nat_lit 17863626774618010770762711385892604329221985629788934059883267215953944903680 

noncomputable def Ns264p606 := nat_lit 71374832082987646568216781445156257198200911263560350366548344470593601536 

noncomputable def Ns264p607 := nat_lit 4301431205335695345399274600586986788705194077385928369485358814986240 

noncomputable def Ns264p608 := BSN.log_dyadic_bound 256795230784 2353947230784 4 3 Ns264p605 67108864 28880000 Ns264p606 Ns264p607 14700492 2610742461568 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 256795230784) (BSN.artanhQ 2353947230784) 0 3 Ns264p606 Ns264p605 Ns264p607 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz436 := (Real.log (Enclosure.sfrac Bool.false 1305371230784 16000000))

noncomputable def Ns264p609 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 571264 4000) qz436 571264 4000 0 1 3183315716480247 281474976710656 781250361 22562500000000000 14207138042651342361 8796093022208000 3486720361143 705078125000000000 (Enclosure.Real.IsNear.const Bool.false 571264 4000) (BSN.isNear_log_sfrac 1305371230784 16000000 3183315716480247 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1305371230784) qz353)) Bool.false Ns264p604 Ns264p92 1000000462080000 28880000000000000000000 3183315716480247 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1305371230784 16000000 16 2610742461568 2097152000000 14700492 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns264p608 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p610 := BSN.arctan_dyadic_bound_f 1000 1142528 1 0 8388608 3610000 0 1 1 0 1 1 7342 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1142528) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1142528) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns264p611 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1142528))) 884279719003555 562949953421312 1 2000000000000000 7342 8388608 1 3610000 7413742746512954228736 883787005724067 562949953421312 200000000361 722000000000000000 qz17 (Ns264p610 rfl) rfl rfl 

noncomputable abbrev qz437 := (@HMul.hMul Real Real Real qz584 qz589 qz637)

noncomputable abbrev qz105 := qz437

noncomputable abbrev qz438 := qz637

noncomputable abbrev qz106 := qz438

noncomputable def Ns264p612 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 571264 4000) qz436) qz105 14207138042651342361 8796093022208000 3486720361143 705078125000000000 883787005724067 2251799813685248 200000000361 2888000000000000000 Ns264p603 454517943989127447177 281474976710656000 1810200824950341 361000000000000000000 (Ns264p609 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz106 1 4 0 1 883787005724067 562949953421312 200000000361 722000000000000000 883787005724067 2251799813685248 200000000361 2888000000000000000 qz361 Ns264p611 rfl) 

noncomputable def Ns264p613 := @Ns264p599 Ns264p593 Ns264p594 78131395572252331 5776000000000000000000 (@Ns264p601 78131395572252331 5776000000000000000000 (Ns264p602 (Ns264p612 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 571264 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz638 (Real.log Real.pi) 571264 2000 0 1 38410761 33554432 1 33554432 171427226343 524288000 4463 524288000 (Enclosure.Real.IsNear.const Bool.false 571264 2000) RS265to276.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns264p595 Ns264p596) 

noncomputable def Ns264p614 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns264p593 Ns264p594 78131395572252331 5776000000000000000000 16813594697 16777216 57 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz362 qz102 (Enclosure.sfrac Bool.true Ns264p595 Ns264p596)) Bool.false Ns264p593 Ns264p594 78131395572252331 5776000000000000000000 Ns264p597 (Ns264p613 rfl rfl)) 

noncomputable def Ns264p615 := nat_lit 3798636283020341541863424 

noncomputable def Ns264p616 := nat_lit 857756278476449923272441154183588788078779163206604465892252707470278106457420738699643776052641330661225557980182693227653526697133361 

noncomputable def Ns264p617 := nat_lit 612315056920306420973964859724837352968318850915299834046806286125082528195159424520096603949344758250297125951608635411169658161 

noncomputable def Ns264p618 := nat_lit 4283448219077704749239269984614303057764377607390571535084677467022386478294259844401801653755417177948743593859210467298067429868553521 

noncomputable def Ns264p619 := BSN.sin_dyadic_bound_f 53981868333 34359738368 4 3 16777216 7227051 Ns264p616 Ns264p106 Ns264p617 Ns264p618 Ns264p109 Ns264p617 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53981868333) qz363 0 3 Ns264p616 Ns264p106 Ns264p617 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53981868333) qz364 0 3 Ns264p618 Ns264p109 Ns264p617 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p620 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz98) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16813594697) qz375) Bool.false 16813594697 16777216 57 4194304 Bool.true 16777215 16777216 1 3610000 (Ns264p614 rfl) (Enclosure.sfrac_false_div 16813594697 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16813594697) qz375) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns264p615) qz377) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 159 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q1 16813594697 16777216 226375608064910080 72057594037927936 159 Ns264p615 Ns264p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns264p615 Ns264p92 53981868333 34359738368 7227051 7220000 (Ns264p619 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p621 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns264p593 Ns264p594 78131395572252331 5776000000000000000000 134508757578 134217728 1816 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz362 qz102 (Enclosure.sfrac Bool.true Ns264p595 Ns264p596)) Bool.false Ns264p593 Ns264p594 78131395572252331 5776000000000000000000 Ns264p597 (Ns264p613 rfl rfl)) 

noncomputable def Ns264p622 := Ns264p592 32107 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 385 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133102400 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 238 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 100797624 134217728) qz101 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) Bool.true 16777215 16777216 13122769 946339840000 134217720 134217728 1862 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 16777215 16777216 13122769 946339840000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz98) qz98) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 16777215 16777216 209964304 15141437440000 16777215 16777216 13122769 946339840000 (Ns264p620 rfl rfl) rfl)) rfl) (Ns264p621 rfl) RS265to276.d7 

noncomputable def Ns264p623 := nat_lit 7674418563399346231848308588572953916478938506477789352415632693792655517770854712762677633069687650856161 

noncomputable def Ns264p624 := nat_lit 2757662496520130651686085724008008863948039224548483210418245908031811842115840089371476654543809761 

noncomputable def Ns264p625 := nat_lit 38338233466018287590176705385063942084754824303261332004113121221057119483100408981852953483017758597917921 

noncomputable def Ns264p626 := BSN.sin_dyadic_bound_f 193513719 134217728 4 3 134217728 67108864 Ns264p623 Ns264p529 Ns264p624 Ns264p625 Ns264p532 Ns264p624 133102400 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 193513719) qz369 0 3 Ns264p623 Ns264p529 Ns264p624 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 193513719) qz370 0 3 Ns264p625 Ns264p532 Ns264p624 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p627 := nat_lit 47877223394859729250771944812882647949481066672749163375915500996161 

noncomputable def Ns264p628 := nat_lit 7709396985126210278641473023556467579664559164535481730370274881 

noncomputable def Ns264p629 := nat_lit 143616251390608935331758551492600830913283870899918419164285762438721 

noncomputable def Ns264p630 := BSN.cos_dyadic_bound_f 96800489 134217728 3 2 134217728 67108864 Ns264p627 Ns264p115 Ns264p628 Ns264p629 Ns264p118 Ns264p628 100797624 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 96800489) qz367 0 2 Ns264p627 Ns264p115 Ns264p628 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 96800489) qz368 0 2 Ns264p629 Ns264p118 Ns264p628 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p631 := nat_lit 5266846998631036380374299988392793488184585637556486585375925353842996109589808490003253060112123036696576 

noncomputable def Ns264p632 := nat_lit 892564926746835788400419487544342239735004353800409735265251947268748669908315272647163854901477376 

noncomputable def Ns264p633 := nat_lit 26318274973522036559963214888172357001566990736130812729163516827036114569368140908881856939244790938075136 

noncomputable def Ns264p634 := BSN.sin_dyadic_bound_f 176151624 134217728 4 3 134217728 67108864 Ns264p631 Ns264p529 Ns264p632 Ns264p633 Ns264p532 Ns264p632 129762927 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 176151624) qz369 0 3 Ns264p631 Ns264p529 Ns264p632 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 176151624) qz370 0 3 Ns264p633 Ns264p532 Ns264p632 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p635 := nat_lit 905009720253043828463508885403743170024386190671881818733721499869795788706981923021204164902256108149201 

noncomputable def Ns264p636 := nat_lit 79637478400492021046544137815425633578459807640827339281046023222450667146816409926908579846855121 

noncomputable def Ns264p637 := nat_lit 5487505698766624001644125163609287068129875658122658030229714526079947248373442483473166041574727836539345 

noncomputable def Ns264p638 := BSN.cos_dyadic_bound_f 144021211 134217728 4 3 134217728 67108864 Ns264p635 Ns264p125 Ns264p636 Ns264p637 Ns264p128 Ns264p636 64082775 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 144021211) qz367 0 3 Ns264p635 Ns264p125 Ns264p636 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 144021211) qz368 0 3 Ns264p637 Ns264p128 Ns264p636 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p639 := Ns264p590 54410 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 133 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 129762927 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 64082775 134217728) qz101 rfl rfl (Ns264p622 RS265to276.d9 RS265to276.d11 RS265to276.d13 RS265to276.d17 (Ns264p626 rfl rfl) (Ns264p630 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns264p621 rfl) RS265to276.d19 RS265to276.d21 RS265to276.d23 RS265to276.d25 RS265to276.d17 (Ns264p634 rfl rfl) (Ns264p638 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns264p640 := nat_lit 292549337904609645607120428510295276804482780068811831226125587234145 

noncomputable def Ns264p641 := nat_lit 88816133722423649656256188254516978713988896269564093525103132001 

noncomputable def Ns264p642 := nat_lit 766056849343188957347776707507885078427156061014832644678907323399521 

noncomputable def Ns264p643 := BSN.sin_dyadic_bound_f 131389749 134217728 3 2 134217728 67108864 Ns264p640 Ns264p243 Ns264p641 Ns264p642 Ns264p246 Ns264p641 111387404 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 131389749) qz369 0 2 Ns264p640 Ns264p243 Ns264p641 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 131389749) qz370 0 2 Ns264p642 Ns264p246 Ns264p641 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p644 := nat_lit 425637719266392935256761630057486396183442214526424852703408786325760 

noncomputable def Ns264p645 := nat_lit 187955023472778372702766015075082256459483303888430915525717606656 

noncomputable def Ns264p646 := nat_lit 1114461147088263665449999790888057094922366636505769535598076611870976 

noncomputable def Ns264p647 := BSN.sin_dyadic_bound_f 144296814 134217728 3 2 134217728 67108864 Ns264p644 Ns264p243 Ns264p645 Ns264p646 Ns264p246 Ns264p645 118062659 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 144296814) qz369 0 2 Ns264p644 Ns264p243 Ns264p645 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 144296814) qz370 0 2 Ns264p646 Ns264p246 Ns264p645 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p648 := Ns264p588 72925 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 13 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 111387404 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 69 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 118062659 134217728) qz101 rfl rfl (Ns264p639 rfl rfl) (Ns264p621 rfl) RS265to276.d27 RS265to276.d29 RS265to276.d31 RS265to276.d33 RS265to276.d17 (Ns264p643 rfl rfl) (Ns264p647 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p649 := nat_lit 4000945162641726500345883764197178976976774471115199443564675167041 

noncomputable def Ns264p650 := nat_lit 53853741265628273390391968490349442515893772001087350575690561 

noncomputable def Ns264p651 := nat_lit 12002727780442648244490870508654556232045291625801596155992874120001 

noncomputable def Ns264p652 := BSN.cos_dyadic_bound_f 52047753 134217728 3 2 134217728 67108864 Ns264p649 Ns264p115 Ns264p650 Ns264p651 Ns264p118 Ns264p650 124251865 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 52047753) qz367 0 2 Ns264p649 Ns264p115 Ns264p650 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 52047753) qz368 0 2 Ns264p651 Ns264p118 Ns264p650 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p653 := nat_lit 89042718652640251044191627536 

noncomputable def Ns264p654 := BSN.sin_dyadic_bound_f 17274266 134217728 2 1 134217728 67108864 Ns264p653 Ns264p136 Ns264p653 Ns264p653 Ns264p137 Ns264p653 17226615 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 17274266) qz369 0 1 Ns264p653 Ns264p136 Ns264p653 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 17274266) qz370 0 1 Ns264p653 Ns264p137 Ns264p653 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p655 := Ns264p586 89103 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 118 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 124251865 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 161 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 17226615 134217728) qz101 rfl rfl (Ns264p648 rfl) (Ns264p621 rfl) RS265to276.d35 RS265to276.d37 RS265to276.d39 RS265to276.d41 RS265to276.d17 (Ns264p652 rfl rfl) (Ns264p654 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p656 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) 462522699 134217728 89103 134217728 462522699 134217728 89103 134217728 124157491616415744 462522699 67108864 89103 67108864 (Ns264p655 rfl) 

noncomputable def Ns264p657 := @Enclosure.Real.IsNear.mulLit_tf qz635 (Zeta.RiemannSiegel.correction qz100) 5433199 16777216 1 16777216 1692589328157 4398046511104 4726656971589 158769479050854400 9196174645153284243 73786976294838206464 

noncomputable abbrev qz639 := (@HPow.hPow Real Real Real qz7 qz99 qz9)

noncomputable def Ns264p658 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz639 1 1 0 1 5433199 16777216 1 16777216 5433199 16777216 1 16777216 

noncomputable def Ns264p659 := @Enclosure.Real.IsNear.sqrt_image qz99 11916999951 131072000 4463 131072000 79986800 79986831 8388608 (@Enclosure.Real.IsNear.of_eq qz99 (@HMul.hMul Real Real Real qz5 qz98 qz3) Bool.false 11916999951 131072000 4463 131072000 (BSN.t_div_two_pi_mk qz98 571264 1000 qz101) (@Enclosure.Real.IsNear.mulLit_ff qz98 qz3 571264 1000 0 1 2670177 16777216 1 16777216 11916999951 131072000 4463 131072000 (Enclosure.Real.IsNear.const Bool.false 571264 1000) RS265to276.d44 rfl)) 

noncomputable abbrev qz759 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 571264 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz640 := qz759

noncomputable abbrev qz439 := qz640

noncomputable abbrev qz107 := qz439

noncomputable def Ns264p660 := @Enclosure.Real.IsNear.sqrt_image qz107 159973631 16777216 31 16777216 25903241 25903247 8388608 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 159973631 16777216 31 16777216 159973631 16777216 31 16777216 (Ns264p659 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns264p661 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz107) 6475811 2097152 3 8388608 2716599 2716600 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz107) Bool.false 51806488 16777216 6 16777216 6475811 2097152 3 8388608 (Ns264p660 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns264p662 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 5433199 16777216 1 16777216 5433199 16777216 1 16777216 (Ns264p661 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz440 := (@HMul.hMul Real Real Real qz584 qz582 qz634)

noncomputable abbrev qz108 := (Real.cos qz440)

noncomputable abbrev qz641 := (@HMul.hMul Real Real Real qz735 qz758 qz758)

noncomputable abbrev qz441 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz641 qz634) qz599)

noncomputable abbrev qz109 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz441))

noncomputable def Ns264p663 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz100) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz108) qz109) Bool.false 1692589328157 

noncomputable def Ns264p664 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz108) qz109 4298847 4194304 53 

noncomputable abbrev qz110 := (@Neg.neg Real Real.instNeg (Real.cos qz440))

noncomputable def Ns264p665 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz108) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz110)) Bool.true 4298847 4194304 53 4194304 (BSN.inv_eq_neg_inv_neg qz108) 

noncomputable def Ns264p666 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz110) Bool.false 17195388 16777216 212 16777216 4298847 4194304 

noncomputable def Ns264p667 := @Enclosure.Real.IsNear.recentre' qz108 Bool.true 16369214 16777216 181084304 15141437440000 8184607 8388608 11317769 946339840000 

noncomputable abbrev qz111 := qz440

noncomputable def Ns264p668 := @Enclosure.Real.IsNear.cos_image qz111 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 28207377) qz365) Bool.false 28207377 8388608 49 4194304 Bool.true 16369214 16777216 1 

noncomputable def Ns264p669 := nat_lit 836568337757491743162278681 

noncomputable def Ns264p670 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz100 884279719003555 140737488355328 1 500000000000000 8978687 16777216 31 16777216 7939670817380872232285 2361183241434822606848 Ns264p669 

noncomputable def Ns264p671 := @Enclosure.Real.IsNear.subLit_ff_p qz107 qz1 159973631 16777216 31 16777216 9 1 0 1 8978687 8978687 16777216 31 

noncomputable def Ns264p672 := @Ns264p671 16777216 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 159973631 16777216 31 16777216 159973631 16777216 31 16777216 (Ns264p659 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns264p673 := @Enclosure.Real.IsNear.recentre' qz111 Bool.false 7939670817380872232285 2361183241434822606848 Ns264p669 Ns264p439 28207377 8388608 49 4194304 (@Ns264p670 Ns264p439 RS265to276.d43 (Ns264p672 rfl rfl) rfl) 

noncomputable def Ns264p674 := nat_lit 3324143839846682116053115853978746400625 

noncomputable def Ns264p675 := BSN.cos_dyadic_bound_f 7593114555 34359738368 2 1 16777216 7227051 Ns264p674 Ns264p445 Ns264p674 Ns264p674 Ns264p446 Ns264p674 16369214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 7593114555) qz394 0 1 Ns264p674 Ns264p445 Ns264p674 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 7593114555) qz395 0 1 Ns264p674 Ns264p446 Ns264p674 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p676 := @Ns264p668 3610000 (Ns264p673 rfl) (Enclosure.sfrac_false_div 28207377 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 28207377) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 267158967845232746430464) qz366) 226375608064910080 72057594037927936 Bool.false 16369214 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 28207377 8388608 226375608064910080 72057594037927936 0 267158967845232746430464 Ns264p104 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16369214 16777216 267158967845232746430464 Ns264p104 7593114555 34359738368 7227051 7220000 (Ns264p675 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p677 := @Enclosure.Real.IsNear.inv_image qz110 8184607 8388608 11317769 946339840000 8597588 8597800 8388608 (@Enclosure.Real.IsNear.neg qz108 Bool.true 8184607 8388608 11317769 946339840000 (Ns264p667 (Ns264p676 rfl rfl) rfl)) 

noncomputable def Ns264p678 := Ns264p665 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz110) Bool.false 4298847 4194304 53 4194304 (@Ns264p666 53 4194304 (Ns264p677 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p679 := @Enclosure.Real.IsNear.recentre' qz109 Bool.true 3149848 8388608 

noncomputable abbrev qz112 := (@HMul.hMul Real Real Real qz346 qz343 qz441)

noncomputable def Ns264p680 := @Enclosure.Real.IsNear.cos_image qz112 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32811585)) qz375) Bool.true 32811585 16777216 

noncomputable def Ns264p681 := nat_lit 77474166451812878369261207645 

noncomputable def Ns264p682 := nat_lit 5811576830136019861434883787412881 

noncomputable def Ns264p683 := @Enclosure.Real.IsNear.recentre' qz112 Bool.true Ns264p681 Ns264p303 Ns264p682 

noncomputable abbrev qz113 := qz441

noncomputable def Ns264p684 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz113 884279719003555 140737488355328 1 500000000000000 87612736995839 

noncomputable abbrev qz442 := (@HSub.hSub Real Real Real qz588 qz641 qz634)

noncomputable abbrev qz114 := qz442

noncomputable def Ns264p685 := @Enclosure.Real.IsNear.subLit_tf qz114 qz31 70020550951423 281474976710656 1076773251 281474976710656 1 16 

noncomputable abbrev qz443 := qz641

noncomputable abbrev qz115 := qz443

noncomputable def Ns264p686 := @Enclosure.Real.IsNear.subLit_ff_n qz115 qz100 80616820243969 281474976710656 556679555 281474976710656 8978687 16777216 31 16777216 

noncomputable def Ns264p687 := @Enclosure.Real.IsNear.mulLit_ff qz100 qz100 8978687 16777216 31 16777216 8978687 16777216 31 16777216 80616820243969 281474976710656 

noncomputable def Ns264p688 := nat_lit 146475107441466916746347635912130160106243495168390016185045013145452694603929182297834896890625 

noncomputable def Ns264p689 := nat_lit 1557135907493247374496162713305139169473535158854262437014310770810018934381230605712890625 

noncomputable def Ns264p690 := nat_lit 883493622727443194903172681888004104324715707687850534181202957589284492685556486576561962490625 

noncomputable def Ns264p691 := BSN.cos_dyadic_bound_t 32811585 16777216 4 3 8388608 3610000 Ns264p688 Ns264p192 Ns264p689 Ns264p690 Ns264p195 Ns264p689 3149848 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32811585) (BSN.cosEvenQ 16777216) 0 3 Ns264p688 Ns264p192 Ns264p689 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32811585) (BSN.cosOddQ 16777216) 0 3 Ns264p690 Ns264p195 Ns264p689 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p692 := @Ns264p679 1478827216 60565749760000 393731 1048576 92426701 3785359360000 (@Ns264p680 405 16777216 Bool.true 3149848 8388608 1 3610000 (@Ns264p683 Ns264p456 32811585 16777216 405 16777216 (@Ns264p684 281474976710656 1076773251 281474976710656 Ns264p681 Ns264p303 Ns264p682 Ns264p456 RS265to276.d43 (@Ns264p685 0 1 1401803791933424 87612736995839 281474976710656 1076773251 281474976710656 (@Ns264p686 1174749907751029178368 70020550951423 281474976710656 1076773251 281474976710656 (@Ns264p687 556679555 281474976710656 (Ns264p672 rfl rfl) (Ns264p672 rfl rfl) rfl) (Ns264p672 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32811585 16777216) (BSN.cos_neg_of_bound 32811585 16777216 Bool.true 3149848 8388608 1 3610000 (Ns264p691 rfl rfl)) rfl rfl) 

noncomputable def Ns264p693 := @Ns264p657 257419751327838225 26637098442436592533504 (Ns264p658 qz33 (@Enclosure.Real.IsNear.of_eq qz639 (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 5433199 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz99 (BSN.t_div_two_pi_nonneg qz98 571264 1000 qz101)) Ns264p662) rfl) (@Ns264p663 4398046511104 4726656971589 158769479050854400 (BSN.correction_mk qz100 (BSN.cos_two_pi_p_ne_zero_mk qz98 571264 1000 9 qz101 rfl rfl (@BSN.floor_sqrt_eq_dec qz98 571264 1000 9 qz101 rfl rfl rfl))) (@Ns264p664 4194304 393731 1048576 92426701 3785359360000 1692589328157 4398046511104 4726656971589 158769479050854400 Ns264p678 (Ns264p692 rfl) rfl)) 

noncomputable def Ns264p694 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (hardyZApproximantRS₀ qz98) Bool.true 499352911015685603181 73786976294838206464 35624511980998537233 26637098442436592533504 (@Eq.refl Real (hardyZApproximantRS₀ qz98)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) (@HMul.hMul Real Real Real qz5 qz635 (Zeta.RiemannSiegel.correction qz100))) Bool.true 499352911015685603181 73786976294838206464 35624511980998537233 26637098442436592533504 (BSN.hardyZApproximantRS₀_eq qz98 9 (@BSN.floor_sqrt_eq_dec qz98 571264 1000 9 qz101 rfl rfl rfl)) (@Ns264p584 499352911015685603181 73786976294838206464 35624511980998537233 26637098442436592533504 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 9)) Bool.true 462522699 67108864 89103 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) (Ns264p656 (Ns264p655 rfl) rfl rfl)) (Ns264p693 rfl) rfl rfl)) 

theorem RS265to276.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz98) Bool.true 499352911015685603181 73786976294838206464 35624511980998537233 26637098442436592533504 := Ns264p694 

noncomputable def Ns264p695 := nat_lit 66592746106091481333760000 

noncomputable def Ns264p696 := nat_lit 2944982450193620857736134656 

noncomputable abbrev qz760 := (Enclosure.sfrac Bool.false 572657 1000)

noncomputable abbrev qz642 := qz760

noncomputable abbrev qz444 := qz642

noncomputable abbrev qz116 := qz444

noncomputable abbrev qz761 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 572657 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz643 := qz761

noncomputable abbrev qz445 := qz643

noncomputable abbrev qz117 := qz445

noncomputable abbrev qz762 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 572657 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz644 := qz762

noncomputable abbrev qz446 := qz644

noncomputable abbrev qz118 := qz446

noncomputable abbrev qz645 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz117 qz9))

noncomputable def Ns264p697 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) (@HMul.hMul Real Real Real qz5 qz645 (Zeta.RiemannSiegel.correction qz118)) 35714403 33554432 22329 16777216 9230513651619027027 73786976294838206464 641581197822073155819 Ns264p695 Ns264p696 

noncomputable def Ns264p698 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 572657 1000 118 161 134217728 67108864 2251799813685248 Bool.false 134930475826 1821 

noncomputable def Ns264p699 := Ns264p698 279097919 38 47453128 8 294906479 38 44739240 8 Bool.false 120521064 73098 Bool.true 19112907 Bool.true 6360743 7074237752028440 1 Bool.false 132859165 Bool.true Bool.false 6358362 Bool.true Bool.false 71428806 

noncomputable def Ns264p700 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 572657 1000 13 69 134217728 67108864 2251799813685248 Bool.false 134930475826 1821 

noncomputable def Ns264p701 := Ns264p700 240485871 38 54794152 8 261175631 38 50729528 8 Bool.false 168867926 54538 Bool.true 44668319 Bool.true 86396220 7074237752028440 1 Bool.false 43848302 Bool.true Bool.false 80552205 Bool.true Bool.false 120521064 

noncomputable def Ns264p702 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 572657 1000 134 53 134217728 67108864 2251799813685248 Bool.false 134930475826 1821 

noncomputable def Ns264p703 := Ns264p702 186065264 38 67108856 8 216015088 38 60023992 8 Bool.false 231267386 32181 Bool.false 127852245 Bool.false 54001728 7074237752028440 1 Bool.false 77790967 Bool.true Bool.false 52556500 Bool.true Bool.false 168867926 

noncomputable def Ns264p704 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 572657 1000 387 239 134217728 67108864 2251799813685248 Bool.false 134930475826 1821 

noncomputable def Ns264p705 := Ns264p704 93032624 38 94906264 8 147453232 38 77490640 16 Bool.false 134217688 1862 Bool.false 63980094 Bool.false 102287670 7074237752028440 1 Bool.false 61584418 Bool.false Bool.false 92669812 Bool.false Bool.false 231267386 

noncomputable def Ns264p706 := nat_lit 359261680908859632531400823117205367498170763163960827763 

noncomputable def Ns264p707 := nat_lit 357363940752541142539689072728175229808019278659584000 

noncomputable def Ns264p708 := nat_lit 29560715726688163927082362427360000 

noncomputable def Ns264p709 := nat_lit 101568940849728375763927793038924173120 

noncomputable abbrev qz646 := (@Eq.refl Real qz760)

noncomputable abbrev qz447 := qz646

noncomputable abbrev qz119 := qz447

noncomputable def Ns264p710 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz116 572657 1000 1311745158596 16000000 1145314 4000 2000 Ns264p708 Ns264p709 qz119 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns264p711 := nat_lit 114963737890835082410048263397505717599414644212467464884160 

noncomputable abbrev qz647 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1145314))))

noncomputable abbrev qz448 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 572657 4000) (Real.log (Enclosure.sfrac Bool.false 1311745158596 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz647))

noncomputable abbrev qz648 := (Enclosure.sfrac Bool.false 572657 2000)

noncomputable abbrev qz120 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz448 qz648) (@HMul.hMul Real Real Real qz346 qz648 (Real.log Real.pi)))

noncomputable def Ns264p712 := @Enclosure.Real.IsNear.addLit_ft_p qz120 (Enclosure.sfrac Bool.true Ns264p708 Ns264p709) 1131879196646654912043 1125899906842624000 10025080303432287109 739328000000000000000000 Ns264p708 Ns264p709 0 1 Ns264p711 

noncomputable def Ns264p713 := nat_lit 3038365082887584821889025966080 

noncomputable abbrev qz121 := (@HSub.hSub Real Real Real qz350 qz448 qz648)

noncomputable def Ns264p714 := @Enclosure.Real.IsNear.subLit_ff_p qz121 (@HMul.hMul Real Real Real qz5 qz648 (Real.log Real.pi)) 60036561877937361123 45035996273704960 1814553951961833 361000000000000000000 21996191161977 67108864000 572657 67108864000 Ns264p713 1131879196646654912043 1125899906842624000 

noncomputable def Ns264p715 := nat_lit 3001828093896868056150000 

noncomputable abbrev qz122 := qz448

noncomputable def Ns264p716 := @Enclosure.Real.IsNear.subLit_ff_p qz122 qz648 1823291278424822294059 1125899906842624000 1814553951961833 361000000000000000000 572657 2000 0 1 Ns264p715 60036561877937361123 45035996273704960 1814553951961833 361000000000000000000 

noncomputable def Ns264p717 := nat_lit 4105686961050952478278339838326341632 

noncomputable def Ns264p718 := nat_lit 27356251063564482226683904 

noncomputable def Ns264p719 := nat_lit 18155821167180533474263041348776039648461580265618697549153868281924436398080 

noncomputable def Ns264p720 := nat_lit 75801595465971263849349961054673276551728184434633633453037509807397564416 

noncomputable def Ns264p721 := nat_lit 4983118451721778928223386657433546767738120540591880442116363239485440 

noncomputable def Ns264p722 := BSN.log_dyadic_bound 263169158596 2360321158596 4 3 Ns264p719 67108864 28880000 Ns264p720 Ns264p721 15027377 2623490317192 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 263169158596) (BSN.artanhQ 2360321158596) 0 3 Ns264p720 Ns264p719 Ns264p721 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz449 := (Real.log (Enclosure.sfrac Bool.false 1311745158596 16000000))

noncomputable def Ns264p723 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 572657 4000) qz449 572657 4000 0 1 3184686771543287 281474976710656 781250361 22562500000000000 1823733172531664103559 1125899906842624000 447388487979177 90250000000000000000 (Enclosure.Real.IsNear.const Bool.false 572657 4000) (BSN.isNear_log_sfrac 1311745158596 16000000 3184686771543287 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1311745158596) qz353)) Bool.false Ns264p718 Ns264p92 1000000462080000 28880000000000000000000 3184686771543287 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1311745158596 16000000 16 2623490317192 2097152000000 15027377 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns264p722 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p724 := BSN.arctan_dyadic_bound_f 1000 1145314 1 0 8388608 3610000 0 1 1 0 1 1 7324 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1145314) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1145314) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns264p725 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1145314))) 884279719003555 562949953421312 1 2000000000000000 7324 8388608 1 3610000 7413752879612115812352 883788213683619 562949953421312 200000000361 722000000000000000 qz17 (Ns264p724 rfl) rfl rfl 

noncomputable abbrev qz450 := (@HMul.hMul Real Real Real qz584 qz589 qz647)

noncomputable abbrev qz123 := qz450

noncomputable abbrev qz451 := qz647

noncomputable abbrev qz124 := qz451

noncomputable def Ns264p726 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 572657 4000) qz449) qz123 1823733172531664103559 1125899906842624000 447388487979177 90250000000000000000 883788213683619 2251799813685248 200000000361 2888000000000000000 Ns264p717 1823291278424822294059 1125899906842624000 1814553951961833 361000000000000000000 (Ns264p723 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz124 1 4 0 1 883788213683619 562949953421312 200000000361 722000000000000000 883788213683619 2251799813685248 200000000361 2888000000000000000 qz361 Ns264p725 rfl) 

noncomputable def Ns264p727 := @Ns264p712 Ns264p706 Ns264p707 10025080303432287109 739328000000000000000000 (@Ns264p714 10025080303432287109 739328000000000000000000 (Ns264p716 (Ns264p726 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 572657 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz648 (Real.log Real.pi) 572657 2000 0 1 38410761 33554432 1 33554432 21996191161977 67108864000 572657 67108864000 (Enclosure.Real.IsNear.const Bool.false 572657 2000) RS265to276.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns264p708 Ns264p709) 

noncomputable def Ns264p728 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns264p706 Ns264p707 10025080303432287109 739328000000000000000000 8433154739 8388608 57 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz362 qz120 (Enclosure.sfrac Bool.true Ns264p708 Ns264p709)) Bool.false Ns264p706 Ns264p707 10025080303432287109 739328000000000000000000 Ns264p710 (Ns264p727 rfl rfl)) 

noncomputable def Ns264p729 := BSN.cos_dyadic_bound_f 25287367 34359738368 1 0 16777216 7227051 0 1 1 0 1 1 16777211 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 25287367) qz394 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 25287367) qz395 0 0 rfl) rfl rfl 

noncomputable def Ns264p730 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz116) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8433154739) qz365) Bool.false 8433154739 8388608 57 4194304 Bool.false 16777211 16777216 1 3610000 (Ns264p728 rfl) (Enclosure.sfrac_false_div 8433154739 8388608) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8433154739) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 889720151939961847808) qz366) 226375608064910080 72057594037927936 Bool.false 16777211 16777216 160 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q0 8433154739 8388608 226375608064910080 72057594037927936 160 889720151939961847808 Ns264p104 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777211 16777216 889720151939961847808 Ns264p104 25287367 34359738368 7227051 7220000 (Ns264p729 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p731 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns264p706 Ns264p707 10025080303432287109 739328000000000000000000 134930475826 134217728 1821 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz362 qz120 (Enclosure.sfrac Bool.true Ns264p708 Ns264p709)) Bool.false Ns264p706 Ns264p707 10025080303432287109 739328000000000000000000 Ns264p710 (Ns264p727 rfl rfl)) 

noncomputable def Ns264p732 := Ns264p705 32181 BSN.abs_quadSignPos (BSN.cos_quad_nat3 387 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 61584418 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 92669812 134217728) qz119 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) Bool.false 16777211 16777216 13122769 946339840000 134217688 134217728 1862 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 16777211 16777216 13122769 946339840000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz116) qz116) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 16777211 16777216 209964304 15141437440000 16777211 16777216 13122769 946339840000 (Ns264p730 rfl rfl) rfl)) rfl) (Ns264p731 rfl) RS265to276.d7 

noncomputable def Ns264p733 := nat_lit 16756352782336291840809535354896 

noncomputable def Ns264p734 := BSN.sin_dyadic_bound_f 63980094 134217728 2 1 134217728 67108864 Ns264p733 Ns264p136 Ns264p733 Ns264p733 Ns264p137 Ns264p733 61584418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 63980094) qz369 0 1 Ns264p733 Ns264p136 Ns264p733 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 63980094) qz370 0 1 Ns264p733 Ns264p137 Ns264p733 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p735 := nat_lit 107439234546718751114212058504150097753177545186391955856208750240000 

noncomputable def Ns264p736 := nat_lit 11983571951012989157088430928373010639123159325769359744100000000 

noncomputable def Ns264p737 := nat_lit 281369069458247469983348676717937652098239752277832448279056279200000 

noncomputable def Ns264p738 := BSN.sin_dyadic_bound_f 102287670 134217728 3 2 134217728 67108864 Ns264p735 Ns264p243 Ns264p736 Ns264p737 Ns264p246 Ns264p736 92669812 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 102287670) qz369 0 2 Ns264p735 Ns264p243 Ns264p736 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 102287670) qz370 0 2 Ns264p737 Ns264p246 Ns264p736 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p739 := nat_lit 145745462382091278121206241024457010037438271867006481240980479190625 

noncomputable def Ns264p740 := nat_lit 71394846928777093392976658418650803374754877271960077971250390625 

noncomputable def Ns264p741 := nat_lit 437093597452416280176832769756533728505565305846475523566998936790625 

noncomputable def Ns264p742 := BSN.cos_dyadic_bound_f 127852245 134217728 3 2 134217728 67108864 Ns264p739 Ns264p115 Ns264p740 Ns264p741 Ns264p118 Ns264p740 77790967 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 127852245) qz367 0 2 Ns264p739 Ns264p115 Ns264p740 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 127852245) qz368 0 2 Ns264p741 Ns264p118 Ns264p740 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p743 := nat_lit 8504144443411890585472132448256 

noncomputable def Ns264p744 := BSN.sin_dyadic_bound_f 54001728 134217728 2 1 134217728 67108864 Ns264p743 Ns264p136 Ns264p743 Ns264p743 Ns264p137 Ns264p743 52556500 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 54001728) qz369 0 1 Ns264p743 Ns264p136 Ns264p743 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 54001728) qz370 0 1 Ns264p743 Ns264p137 Ns264p743 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p745 := Ns264p703 54538 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 134 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 77790967 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 53 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 52556500 134217728) qz119 rfl rfl (Ns264p732 RS265to276.d9 RS265to276.d11 RS265to276.d13 RS265to276.d17 (Ns264p734 rfl rfl) (Ns264p738 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns264p731 rfl) RS265to276.d19 RS265to276.d21 RS265to276.d23 RS265to276.d25 RS265to276.d17 (Ns264p742 rfl rfl) (Ns264p744 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns264p746 := nat_lit 3981057368857407539396543349121 

noncomputable def Ns264p747 := BSN.sin_dyadic_bound_f 44668319 134217728 2 1 134217728 67108864 Ns264p746 Ns264p136 Ns264p746 Ns264p746 Ns264p137 Ns264p746 43848302 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 44668319) qz369 0 1 Ns264p746 Ns264p136 Ns264p746 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 44668319) qz370 0 1 Ns264p746 Ns264p137 Ns264p746 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p748 := nat_lit 54679551244944160569612375375417591093085276700752029340213616640000 

noncomputable def Ns264p749 := nat_lit 3104258889337149835655679456944228540468583248408711193600000000 

noncomputable def Ns264p750 := nat_lit 143203322555699588963536588216496733635681632700519796072912691200000 

noncomputable def Ns264p751 := BSN.sin_dyadic_bound_f 86396220 134217728 3 2 134217728 67108864 Ns264p748 Ns264p243 Ns264p749 Ns264p750 Ns264p246 Ns264p749 80552205 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 86396220) qz369 0 2 Ns264p748 Ns264p243 Ns264p749 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 86396220) qz370 0 2 Ns264p750 Ns264p246 Ns264p749 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p752 := Ns264p701 73098 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 13 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 43848302 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 69 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 80552205 134217728) qz119 rfl rfl (Ns264p745 rfl rfl) (Ns264p731 rfl) RS265to276.d27 RS265to276.d29 RS265to276.d31 RS265to276.d33 RS265to276.d17 (Ns264p747 rfl rfl) (Ns264p751 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p753 := nat_lit 133446438151897895291859441201 

noncomputable def Ns264p754 := BSN.cos_dyadic_bound_f 19112907 134217728 2 1 134217728 67108864 Ns264p753 Ns264p522 Ns264p753 Ns264p753 Ns264p523 Ns264p753 132859165 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 19112907) qz367 0 1 Ns264p753 Ns264p522 Ns264p753 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 19112907) qz368 0 1 Ns264p753 Ns264p523 Ns264p753 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p755 := BSN.sin_dyadic_bound_f 6360743 134217728 1 0 134217728 67108864 0 1 1 0 1 1 6358362 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 6360743) qz369 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 6360743) qz370 0 0 rfl) rfl rfl 

noncomputable def Ns264p756 := Ns264p699 89316 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 118 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132859165 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 161 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 6358362 134217728) qz119 rfl rfl (Ns264p752 rfl) (Ns264p731 rfl) RS265to276.d35 RS265to276.d37 RS265to276.d39 RS265to276.d41 RS265to276.d17 (Ns264p754 rfl rfl) (Ns264p755 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p757 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) 71428806 134217728 89316 134217728 71428806 134217728 89316 134217728 19174024110145536 35714403 33554432 22329 16777216 (Ns264p756 rfl) 

noncomputable def Ns264p758 := @Enclosure.Real.IsNear.mulLit_tf qz645 (Zeta.RiemannSiegel.correction qz118) 1357473 4194304 1 8388608 6799776976499 17592186044416 235184259015527 7938473952542720000 9230513651619027027 73786976294838206464 

noncomputable abbrev qz649 := (@HPow.hPow Real Real Real qz7 qz117 qz9)

noncomputable def Ns264p759 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz649 1 1 0 1 1357473 4194304 1 8388608 1357473 4194304 1 8388608 

noncomputable def Ns264p760 := @Enclosure.Real.IsNear.sqrt_image qz117 1529095550289 16777216000 572657 16777216000 80084263 80084293 8388608 (@Enclosure.Real.IsNear.of_eq qz117 (@HMul.hMul Real Real Real qz5 qz116 qz3) Bool.false 1529095550289 16777216000 572657 16777216000 (BSN.t_div_two_pi_mk qz116 572657 1000 qz119) (@Enclosure.Real.IsNear.mulLit_ff qz116 qz3 572657 1000 0 1 2670177 16777216 1 16777216 1529095550289 16777216000 572657 16777216000 (Enclosure.Real.IsNear.const Bool.false 572657 1000) RS265to276.d44 rfl)) 

noncomputable abbrev qz763 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 572657 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz650 := qz763

noncomputable abbrev qz452 := qz650

noncomputable abbrev qz125 := qz452

noncomputable def Ns264p761 := @Enclosure.Real.IsNear.sqrt_image qz125 40042139 4194304 15 8388608 25919017 25919023 8388608 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 160168556 16777216 30 16777216 40042139 4194304 15 8388608 (Ns264p760 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns264p762 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz125) 6479755 2097152 3 8388608 2714945 2714947 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz125) Bool.false 51838040 16777216 6 16777216 6479755 2097152 3 8388608 (Ns264p761 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns264p763 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 5429892 16777216 2 16777216 1357473 4194304 1 8388608 (Ns264p762 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz453 := (@HMul.hMul Real Real Real qz584 qz582 qz644)

noncomputable abbrev qz126 := (Real.cos qz453)

noncomputable abbrev qz651 := (@HMul.hMul Real Real Real qz735 qz762 qz762)

noncomputable abbrev qz454 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz651 qz644) qz599)

noncomputable abbrev qz127 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz454))

noncomputable def Ns264p764 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz118) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz126) qz127) Bool.false 6799776976499 

noncomputable def Ns264p765 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz126) qz127 2191163 2097152 53 

noncomputable abbrev qz128 := (@Neg.neg Real Real.instNeg (Real.cos qz453))

noncomputable def Ns264p766 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz126) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz128)) Bool.true 2191163 2097152 53 4194304 (BSN.inv_eq_neg_inv_neg qz126) 

noncomputable def Ns264p767 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz128) Bool.false 17529304 16777216 212 16777216 2191163 2097152 

noncomputable def Ns264p768 := @Enclosure.Real.IsNear.recentre' qz126 Bool.true 16057396 16777216 699067216 60565749760000 4014349 4194304 43691701 3785359360000 

noncomputable abbrev qz129 := qz453

noncomputable def Ns264p769 := @Enclosure.Real.IsNear.cos_image qz129 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3602469) (@Nat.cast Real Real.instNatCast 1048576)) Bool.false 3602469 1048576 189 16777216 Bool.true 16057396 16777216 1 

noncomputable def Ns264p770 := nat_lit 404791131175061045353727657 

noncomputable def Ns264p771 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz118 884279719003555 140737488355328 1 500000000000000 2293403 4194304 15 8388608 2028009760401910047665 590295810358705651712 Ns264p770 

noncomputable def Ns264p772 := @Enclosure.Real.IsNear.subLit_ff_p qz125 qz1 40042139 4194304 15 8388608 9 1 0 1 2293403 2293403 4194304 15 

noncomputable def Ns264p773 := @Ns264p772 8388608 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 160168556 16777216 30 16777216 40042139 4194304 15 8388608 (Ns264p760 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns264p774 := @Enclosure.Real.IsNear.recentre' qz129 Bool.false 2028009760401910047665 590295810358705651712 Ns264p770 Ns264p165 3602469 1048576 189 16777216 (@Ns264p771 Ns264p165 RS265to276.d43 (Ns264p773 rfl rfl) rfl) 

noncomputable def Ns264p775 := nat_lit 10411821519407962306411160816146810400625 

noncomputable def Ns264p776 := BSN.cos_dyadic_bound_f 10101402555 34359738368 2 1 16777216 7227051 Ns264p775 Ns264p445 Ns264p775 Ns264p775 Ns264p446 Ns264p775 16057396 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 10101402555) qz394 0 1 Ns264p775 Ns264p445 Ns264p775 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 10101402555) qz395 0 1 Ns264p775 Ns264p446 Ns264p775 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p777 := @Ns264p769 3610000 (Ns264p774 rfl) (Enclosure.sfrac_false_div 3602469 1048576) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3602469) (@Nat.cast Real Real.instNatCast 1048576)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44426438267898123255808) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false 16057396 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 3602469 1048576 226375608064910080 72057594037927936 0 44426438267898123255808 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16057396 16777216 44426438267898123255808 151115727451828646838272 10101402555 34359738368 7227051 7220000 (Ns264p776 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p778 := @Enclosure.Real.IsNear.inv_image qz128 4014349 4194304 43691701 3785359360000 8764546 8764758 8388608 (@Enclosure.Real.IsNear.neg qz126 Bool.true 4014349 4194304 43691701 3785359360000 (Ns264p768 (Ns264p777 rfl rfl) rfl)) 

noncomputable def Ns264p779 := Ns264p766 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz128) Bool.false 2191163 2097152 53 4194304 (@Ns264p767 53 4194304 (Ns264p778 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p780 := @Enclosure.Real.IsNear.recentre' qz127 Bool.true 3103273 8388608 

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz346 qz343 qz454)

noncomputable def Ns264p781 := @Enclosure.Real.IsNear.cos_image qz130 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32711203)) qz375) Bool.true 32711203 16777216 

noncomputable def Ns264p782 := nat_lit 4827321614808653850297189845 

noncomputable def Ns264p783 := nat_lit 2475880078570760549798248448 

noncomputable def Ns264p784 := nat_lit 7109036971107861087232955786788147 

noncomputable def Ns264p785 := @Enclosure.Real.IsNear.recentre' qz130 Bool.true Ns264p782 Ns264p783 Ns264p784 

noncomputable abbrev qz131 := qz454

noncomputable def Ns264p786 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz131 884279719003555 140737488355328 1 500000000000000 5459043683879 

noncomputable abbrev qz455 := (@HSub.hSub Real Real Real qz588 qz651 qz644)

noncomputable abbrev qz132 := qz455

noncomputable def Ns264p787 := @Enclosure.Real.IsNear.subLit_tf qz132 qz31 4359532056103 17592186044416 263433525 70368744177664 1 16 

noncomputable abbrev qz456 := qz651

noncomputable abbrev qz133 := qz456

noncomputable def Ns264p788 := @Enclosure.Real.IsNear.subLit_ff_n qz133 qz118 5259697320409 17592186044416 137604405 70368744177664 2293403 4194304 15 8388608 

noncomputable def Ns264p789 := @Enclosure.Real.IsNear.mulLit_ff qz118 qz118 2293403 4194304 15 8388608 2293403 4194304 15 8388608 5259697320409 17592186044416 

noncomputable def Ns264p790 := nat_lit 144675591336610949307827133068872802437252781423686261352549539335925406694940897774346882475121 

noncomputable def Ns264p791 := nat_lit 1500922245515337530355465901183339018681570316307023122964303139274605392942040418924848241 

noncomputable def Ns264p792 := nat_lit 872700678477777970259412109330153470010235505981066660332946082989406841139042741930080242721905 

noncomputable def Ns264p793 := BSN.cos_dyadic_bound_t 32711203 16777216 4 3 8388608 3610000 Ns264p790 Ns264p192 Ns264p791 Ns264p792 Ns264p195 Ns264p791 3103273 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32711203) (BSN.cosEvenQ 16777216) 0 3 Ns264p790 Ns264p192 Ns264p791 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32711203) (BSN.cosOddQ 16777216) 0 3 Ns264p792 Ns264p195 Ns264p791 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p794 := @Ns264p780 361584304 15141437440000 3103273 8388608 22599019 946339840000 (@Ns264p781 99 4194304 Bool.true 3103273 8388608 1 3610000 (@Ns264p785 Ns264p186 32711203 16777216 99 4194304 (@Ns264p786 17592186044416 263433525 70368744177664 Ns264p782 Ns264p783 Ns264p784 Ns264p186 RS265to276.d43 (@Ns264p787 0 1 87344698942064 5459043683879 17592186044416 263433525 70368744177664 (@Ns264p788 18285202741041037312 4359532056103 17592186044416 263433525 70368744177664 (@Ns264p789 137604405 70368744177664 (Ns264p773 rfl rfl) (Ns264p773 rfl rfl) rfl) (Ns264p773 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32711203 16777216) (BSN.cos_neg_of_bound 32711203 16777216 Bool.true 3103273 8388608 1 3610000 (Ns264p793 rfl rfl)) rfl rfl) 

noncomputable def Ns264p795 := @Ns264p758 641581197822073155819 Ns264p695 (Ns264p759 qz33 (@Enclosure.Real.IsNear.of_eq qz649 (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 1357473 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz117 (BSN.t_div_two_pi_nonneg qz116 572657 1000 qz119)) Ns264p763) rfl) (@Ns264p764 17592186044416 235184259015527 7938473952542720000 (BSN.correction_mk qz118 (BSN.cos_two_pi_p_ne_zero_mk qz116 572657 1000 9 qz119 rfl rfl (@BSN.floor_sqrt_eq_dec qz116 572657 1000 9 qz119 rfl rfl rfl))) (@Ns264p765 4194304 3103273 8388608 22599019 946339840000 6799776976499 17592186044416 235184259015527 7938473952542720000 Ns264p779 (Ns264p794 rfl) rfl)) 

noncomputable def Ns264p796 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (hardyZApproximantRS₀ qz116) Bool.false 87767316406775142483 73786976294838206464 89270673640985270595819 Ns264p695 (@Eq.refl Real (hardyZApproximantRS₀ qz116)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) (@HMul.hMul Real Real Real qz5 qz645 (Zeta.RiemannSiegel.correction qz118))) Bool.false 87767316406775142483 73786976294838206464 89270673640985270595819 Ns264p695 (BSN.hardyZApproximantRS₀_eq qz116 9 (@BSN.floor_sqrt_eq_dec qz116 572657 1000 9 qz119 rfl rfl rfl)) (@Ns264p697 87767316406775142483 73786976294838206464 89270673640985270595819 Ns264p695 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 9)) Bool.false 35714403 33554432 22329 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) (Ns264p757 (Ns264p756 rfl) rfl rfl)) (Ns264p795 rfl) rfl rfl)) 

theorem RS265to276.d52 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz116) Bool.false 87767316406775142483 73786976294838206464 89270673640985270595819 Ns264p695 := Ns264p796 

noncomputable def Ns264p797 := nat_lit 10654839376974637013401600 

noncomputable def Ns264p798 := nat_lit 25706863407897346309456134144 

noncomputable abbrev qz764 := (Enclosure.sfrac Bool.false 574049 1000)

noncomputable abbrev qz652 := qz764

noncomputable abbrev qz457 := qz652

noncomputable abbrev qz134 := qz457

noncomputable abbrev qz765 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 574049 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz653 := qz765

noncomputable abbrev qz458 := qz653

noncomputable abbrev qz135 := qz458

noncomputable abbrev qz766 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 574049 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz654 := qz766

noncomputable abbrev qz459 := qz654

noncomputable abbrev qz136 := qz459

noncomputable abbrev qz655 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz135 qz9))

noncomputable def Ns264p799 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) (@HMul.hMul Real Real Real qz5 qz655 (Zeta.RiemannSiegel.correction qz136)) 23883717 16777216 89535 67108864 148418709867515697129 1180591620717411303424 109617451065353715147 Ns264p797 Ns264p798 

noncomputable def Ns264p800 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 574049 1000 117 160 134217728 67108864 2251799813685248 Bool.false 135352118487 1825 

noncomputable def Ns264p801 := Ns264p800 279097919 38 47453128 8 294906479 38 44739240 8 Bool.true 49930957 73278 Bool.true 196803263 Bool.true 206056615 7074237752028440 1 Bool.false 133485580 Bool.true Bool.false 4771093 Bool.false Bool.true 95534868 

noncomputable def Ns264p802 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 574049 1000 12 69 134217728 67108864 2251799813685248 Bool.false 135352118487 1825 

noncomputable def Ns264p803 := Ns264p802 240485871 38 54794152 8 261175631 38 50729528 8 Bool.true 56262550 54673 Bool.true 168610705 Bool.true 28310037 7074237752028440 1 Bool.false 41525263 Bool.false Bool.false 28100585 Bool.true Bool.true 49930957 

noncomputable def Ns264p804 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 574049 1000 135 53 134217728 67108864 2251799813685248 Bool.false 135352118487 1825 

noncomputable def Ns264p805 := Ns264p804 186065264 38 67108856 8 216015088 38 60023992 8 Bool.true 35904084 32262 Bool.false 79663345 Bool.false 174951386 7074237752028440 1 Bool.false 75067645 Bool.false Bool.false 129451083 Bool.true Bool.true 56262550 

noncomputable def Ns264p806 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 574049 1000 388 240 134217728 67108864 2251799813685248 Bool.false 135352118487 1825 

noncomputable def Ns264p807 := Ns264p806 93032624 38 94906264 8 147453232 38 77490640 16 Bool.true 134217696 1870 Bool.false 145292628 Bool.false 107846718 7074237752028440 1 Bool.false 62962777 Bool.false Bool.false 93170836 Bool.false Bool.true 35904084 

noncomputable def Ns264p808 := nat_lit 365672452194471505406367179871345625949821571197617799907 

noncomputable def Ns264p809 := nat_lit 362607739533878071069200436112149668469300386594816000 

noncomputable def Ns264p810 := nat_lit 29921743502591601938613941719520000 

noncomputable def Ns264p811 := nat_lit 103059318102475023996817195698028418880 

noncomputable abbrev qz656 := (@Eq.refl Real qz764)

noncomputable abbrev qz460 := qz656

noncomputable abbrev qz137 := qz460

noncomputable def Ns264p812 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz134 574049 1000 1318130017604 16000000 1148098 4000 2000 Ns264p810 Ns264p811 qz137 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns264p813 := nat_lit 117015184702230881730037497558830600303942902783237695970240 

noncomputable abbrev qz657 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1148098))))

noncomputable abbrev qz461 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 574049 4000) (Real.log (Enclosure.sfrac Bool.false 1318130017604 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz657))

noncomputable abbrev qz658 := (Enclosure.sfrac Bool.false 574049 2000)

noncomputable abbrev qz138 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz461 qz658) (@HMul.hMul Real Real Real qz346 qz658 (Real.log Real.pi)))

noncomputable def Ns264p814 := @Enclosure.Real.IsNear.addLit_ft_p qz138 (Enclosure.sfrac Bool.true Ns264p810 Ns264p811) 1135416190846200849723 1125899906842624000 10049324556767615413 739328000000000000000000 Ns264p810 Ns264p811 0 1 Ns264p813 

noncomputable def Ns264p815 := nat_lit 76196490734895737740745244672000 

noncomputable abbrev qz139 := (@HSub.hSub Real Real Real qz350 qz461 qz658)

noncomputable def Ns264p816 := @Enclosure.Real.IsNear.subLit_ff_p qz139 (@HMul.hMul Real Real Real qz5 qz658 (Real.log Real.pi)) 1505348081630537721147 1125899906842624000 1818903953971881 361000000000000000000 22049658941289 67108864000 574049 67108864000 Ns264p815 1135416190846200849723 1125899906842624000 

noncomputable abbrev qz140 := qz461

noncomputable def Ns264p817 := @Enclosure.Real.IsNear.subLit_ff_p qz140 qz658 365701787888417690687 225179981368524800 1818903953971881 361000000000000000000 574049 2000 0 1 602139232652215088458800 1505348081630537721147 1125899906842624000 1818903953971881 361000000000000000000 

noncomputable def Ns264p818 := nat_lit 823487217831501039501840887238885376 

noncomputable def Ns264p819 := nat_lit 27367991299274690768404480 

noncomputable def Ns264p820 := nat_lit 18452498946336755405323578078360468025233881564518928607330508935535706542080 

noncomputable def Ns264p821 := nat_lit 80414632779125646551436105299858155093650297078990829172831018259556233216 

noncomputable def Ns264p822 := nat_lit 5753950406022969935601226895630354064636685808536280329685079638077440 

noncomputable def Ns264p823 := BSN.log_dyadic_bound 269554017604 2366706017604 4 3 Ns264p820 67108864 28880000 Ns264p821 Ns264p822 15353234 2636260035208 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 269554017604) (BSN.artanhQ 2366706017604) 0 3 Ns264p821 Ns264p820 Ns264p822 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz462 := (Real.log (Enclosure.sfrac Bool.false 1318130017604 16000000))

noncomputable def Ns264p824 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 574049 4000) qz462 574049 4000 0 1 3186053514861815 281474976710656 781250361 22562500000000000 365790166830582007787 225179981368524800 448475988481689 90250000000000000000 (Enclosure.Real.IsNear.const Bool.false 574049 4000) (BSN.isNear_log_sfrac 1318130017604 16000000 3186053514861815 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1318130017604) qz353)) Bool.false Ns264p819 Ns264p92 1000000462080000 28880000000000000000000 3186053514861815 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1318130017604 16000000 16 2636260035208 2097152000000 15353234 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns264p823 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p825 := BSN.arctan_dyadic_bound_f 1000 1148098 1 0 8388608 3610000 0 1 1 0 1 1 7306 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1148098) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1148098) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns264p826 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1148098))) 884279719003555 562949953421312 1 2000000000000000 7306 8388608 1 3610000 7413763012711277395968 883789421643171 562949953421312 200000000361 722000000000000000 qz17 (Ns264p825 rfl) rfl rfl 

noncomputable abbrev qz463 := (@HMul.hMul Real Real Real qz584 qz589 qz657)

noncomputable abbrev qz141 := qz463

noncomputable abbrev qz464 := qz657

noncomputable abbrev qz142 := qz464

noncomputable def Ns264p827 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 574049 4000) qz462) qz141 365790166830582007787 225179981368524800 448475988481689 90250000000000000000 883789421643171 2251799813685248 200000000361 2888000000000000000 Ns264p818 365701787888417690687 225179981368524800 1818903953971881 361000000000000000000 (Ns264p824 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz142 1 4 0 1 883789421643171 562949953421312 200000000361 722000000000000000 883789421643171 2251799813685248 200000000361 2888000000000000000 qz361 Ns264p826 rfl) 

noncomputable def Ns264p828 := @Ns264p814 Ns264p808 Ns264p809 10049324556767615413 739328000000000000000000 (@Ns264p816 10049324556767615413 739328000000000000000000 (Ns264p817 (Ns264p827 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 574049 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz658 (Real.log Real.pi) 574049 2000 0 1 38410761 33554432 1 33554432 22049658941289 67108864000 574049 67108864000 (Enclosure.Real.IsNear.const Bool.false 574049 2000) RS265to276.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns264p810 Ns264p811) 

noncomputable def Ns264p829 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns264p808 Ns264p809 10049324556767615413 739328000000000000000000 8459507405 8388608 229 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz362 qz138 (Enclosure.sfrac Bool.true Ns264p810 Ns264p811)) Bool.false Ns264p808 Ns264p809 10049324556767615413 739328000000000000000000 Ns264p812 (Ns264p828 rfl rfl)) 

noncomputable def Ns264p830 := BSN.cos_dyadic_bound_f 21505667 34359738368 1 0 16777216 7227051 0 1 1 0 1 1 16777212 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 21505667) qz394 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 21505667) qz395 0 0 rfl) rfl rfl 

noncomputable def Ns264p831 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz134) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8459507405) qz365) Bool.false 8459507405 8388608 229 16777216 Bool.true 16777212 16777216 1 3610000 (Ns264p829 rfl) (Enclosure.sfrac_false_div 8459507405 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8459507405) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 756663405813988065280) qz366) 226375608064910080 72057594037927936 Bool.false 16777212 16777216 160 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 8459507405 8388608 226375608064910080 72057594037927936 160 756663405813988065280 Ns264p104 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777212 16777216 756663405813988065280 Ns264p104 21505667 34359738368 7227051 7220000 (Ns264p830 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p832 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns264p808 Ns264p809 10049324556767615413 739328000000000000000000 135352118487 134217728 1825 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz362 qz138 (Enclosure.sfrac Bool.true Ns264p810 Ns264p811)) Bool.false Ns264p808 Ns264p809 10049324556767615413 739328000000000000000000 Ns264p812 (Ns264p828 rfl rfl)) 

noncomputable def Ns264p833 := Ns264p807 32262 BSN.abs_quadSignPos (BSN.cos_quad_nat0 388 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 62962777 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 93170836 134217728) qz137 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) Bool.true 4194303 4194304 52716701 3785359360000 134217696 134217728 1870 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 4194303 4194304 52716701 3785359360000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz134) qz134) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 16777212 16777216 843467216 60565749760000 4194303 4194304 52716701 3785359360000 (Ns264p831 rfl rfl) rfl)) rfl) (Ns264p832 rfl) RS265to276.d7 

noncomputable def Ns264p834 := nat_lit 937419500099968289789986718575698059505758432591627106339459935805331584303525731244299635439570094391296 

noncomputable def Ns264p835 := nat_lit 88495859244623267990833525763407255934985333849694738656171391982103214140479384398181456010018816 

noncomputable def Ns264p836 := nat_lit 5683914739777934212157995043302777469352815680149745482140086222199412181242802648416960960759577140264960 

noncomputable def Ns264p837 := BSN.cos_dyadic_bound_f 145292628 134217728 4 3 134217728 67108864 Ns264p834 Ns264p125 Ns264p835 Ns264p836 Ns264p128 Ns264p835 62962777 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 145292628) qz367 0 3 Ns264p834 Ns264p125 Ns264p835 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 145292628) qz368 0 3 Ns264p836 Ns264p128 Ns264p835 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p838 := nat_lit 73770766187575280135193394667548018697273717665487707193460324761856 

noncomputable def Ns264p839 := nat_lit 18300184373134478183261035003915226774586991338190000782946795776 

noncomputable def Ns264p840 := nat_lit 221275698193979571449213661932636225638271979013786741578815080694016 

noncomputable def Ns264p841 := BSN.cos_dyadic_bound_f 107846718 134217728 3 2 134217728 67108864 Ns264p838 Ns264p115 Ns264p839 Ns264p840 Ns264p118 Ns264p839 93170836 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 107846718) qz367 0 2 Ns264p838 Ns264p115 Ns264p839 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 107846718) qz368 0 2 Ns264p840 Ns264p118 Ns264p839 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p842 := nat_lit 39525128849255979505212738554623728734621830363322182490120851530625 

noncomputable def Ns264p843 := nat_lit 1622065192837927715625646374498059620001822205556302390562890625 

noncomputable def Ns264p844 := nat_lit 103515568404405827773541397548932006970339076572749101079779414090625 

noncomputable def Ns264p845 := BSN.sin_dyadic_bound_f 79663345 134217728 3 2 134217728 67108864 Ns264p842 Ns264p243 Ns264p843 Ns264p844 Ns264p246 Ns264p843 75067645 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 79663345) qz369 0 2 Ns264p842 Ns264p243 Ns264p843 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 79663345) qz370 0 2 Ns264p844 Ns264p246 Ns264p843 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p846 := nat_lit 5124625795888962139153498822361241605084056354712696515563426502535150190631815385016630775594019027357696 

noncomputable def Ns264p847 := nat_lit 822259024756011737147338035732560066843548550755759492972563847043560732352164085401899262795780096 

noncomputable def Ns264p848 := nat_lit 25608018554151109798865595689973006051770363862893399026221144698907037815615259851550084913371001181638656 

noncomputable def Ns264p849 := BSN.sin_dyadic_bound_f 174951386 134217728 4 3 134217728 67108864 Ns264p846 Ns264p529 Ns264p847 Ns264p848 Ns264p532 Ns264p847 129451083 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 174951386) qz369 0 3 Ns264p846 Ns264p529 Ns264p847 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 174951386) qz370 0 3 Ns264p848 Ns264p532 Ns264p847 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p850 := Ns264p805 54673 BSN.abs_quadSignPos (BSN.cos_quad_nat3 135 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 75067645 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 53 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 129451083 134217728) qz137 rfl rfl (Ns264p833 RS265to276.d9 RS265to276.d11 RS265to276.d13 RS265to276.d17 (Ns264p837 rfl rfl) (Ns264p841 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns264p832 rfl) RS265to276.d19 RS265to276.d21 RS265to276.d23 RS265to276.d25 RS265to276.d17 (Ns264p845 rfl rfl) (Ns264p849 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns264p851 := nat_lit 1701331167510451544263983874877688605506892033722681866445242201705859790435901312844482061821975391890625 

noncomputable def Ns264p852 := nat_lit 527985178598790806802525169861523882378741867040869178819139465106457023317052173372118965087890625 

noncomputable def Ns264p853 := nat_lit 10311220587687816462942333470417338956635693910086981995340535308212458288632356542814523679025673465490625 

noncomputable def Ns264p854 := BSN.cos_dyadic_bound_f 168610705 134217728 4 3 134217728 67108864 Ns264p851 Ns264p125 Ns264p852 Ns264p853 Ns264p128 Ns264p852 41525263 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 168610705) qz367 0 3 Ns264p851 Ns264p125 Ns264p852 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 168610705) qz368 0 3 Ns264p853 Ns264p128 Ns264p852 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p855 := nat_lit 642335238238677434141347594161 

noncomputable def Ns264p856 := BSN.sin_dyadic_bound_f 28310037 134217728 2 1 134217728 67108864 Ns264p855 Ns264p136 Ns264p855 Ns264p855 Ns264p137 Ns264p855 28100585 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 28310037) qz369 0 1 Ns264p855 Ns264p136 Ns264p855 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 28310037) qz370 0 1 Ns264p855 Ns264p137 Ns264p855 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p857 := Ns264p803 73278 BSN.abs_quadSignPos (BSN.cos_quad_nat0 12 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 41525263 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 69 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 28100585 134217728) qz137 rfl rfl (Ns264p850 rfl rfl) (Ns264p832 rfl) RS265to276.d27 RS265to276.d29 RS265to276.d31 RS265to276.d33 RS265to276.d17 (Ns264p854 rfl rfl) (Ns264p856 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p858 := nat_lit 8210523877394227380699499787637732432529479833818722060268467556379281957969755520953959897162725309505281 

noncomputable def Ns264p859 := nat_lit 3375884170110826377574577597027266072715398853271830374828303421083844234734533603190208131297140481 

noncomputable def Ns264p860 := nat_lit 41013871075648920246378151356124207146757971759060807253385287349637660939347514492272830602774414379933441 

noncomputable def Ns264p861 := BSN.sin_dyadic_bound_f 196803263 134217728 4 3 134217728 67108864 Ns264p858 Ns264p529 Ns264p859 Ns264p860 Ns264p532 Ns264p859 133485580 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 196803263) qz369 0 3 Ns264p858 Ns264p529 Ns264p859 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 196803263) qz370 0 3 Ns264p860 Ns264p532 Ns264p859 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p862 := nat_lit 3801766337261781162485742045829456786039382637221627600757287601710175831492747051621408421198101699390625 

noncomputable def Ns264p863 := nat_lit 5859205549814932835904859268714284607939372937263106313446424997675321443776690564102241582275390625 

noncomputable def Ns264p864 := nat_lit 23013342841665749802619335833124733391951404019657317435983853585692213410394229978332222013650277980990625 

noncomputable def Ns264p865 := BSN.cos_dyadic_bound_f 206056615 134217728 4 3 134217728 67108864 Ns264p862 Ns264p125 Ns264p863 Ns264p864 Ns264p128 Ns264p863 4771093 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 206056615) qz367 0 3 Ns264p862 Ns264p125 Ns264p863 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 206056615) qz368 0 3 Ns264p864 Ns264p128 Ns264p863 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz659 := (BSN.cos_quad_nat0 160 rfl)

noncomputable def Ns264p866 := Ns264p801 89535 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 117 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133485580 134217728) BSN.abs_quadSignPos qz659 (BSN.sfrac_eq_quadSignPos_mul Bool.false 4771093 134217728) qz137 rfl rfl (Ns264p857 rfl) (Ns264p832 rfl) RS265to276.d35 RS265to276.d37 RS265to276.d39 RS265to276.d41 RS265to276.d17 (Ns264p861 rfl rfl) (Ns264p865 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p867 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) 95534868 134217728 89535 134217728 95534868 134217728 89535 134217728 25644945855479808 23883717 16777216 89535 67108864 (Ns264p866 rfl) 

noncomputable def Ns264p868 := @Enclosure.Real.IsNear.mulLit_tf qz655 (Zeta.RiemannSiegel.correction qz136) 2713299 8388608 1 8388608 54700462377171 140737488355328 502726289907123 15876947905085440000 148418709867515697129 1180591620717411303424 

noncomputable abbrev qz660 := (@HPow.hPow Real Real Real qz7 qz135 qz9)

noncomputable def Ns264p869 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz660 1 1 0 1 2713299 8388608 1 8388608 2713299 8388608 1 8388608 

noncomputable def Ns264p870 := @Enclosure.Real.IsNear.sqrt_image qz135 1532812436673 16777216000 574049 16777216000 80181537 80181568 8388608 (@Enclosure.Real.IsNear.of_eq qz135 (@HMul.hMul Real Real Real qz5 qz134 qz3) Bool.false 1532812436673 16777216000 574049 16777216000 (BSN.t_div_two_pi_mk qz134 574049 1000 qz137) (@Enclosure.Real.IsNear.mulLit_ff qz134 qz3 574049 1000 0 1 2670177 16777216 1 16777216 1532812436673 16777216000 574049 16777216000 (Enclosure.Real.IsNear.const Bool.false 574049 1000) RS265to276.d44 rfl)) 

noncomputable abbrev qz767 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 574049 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz661 := qz767

noncomputable abbrev qz465 := qz661

noncomputable abbrev qz143 := qz465

noncomputable def Ns264p871 := @Enclosure.Real.IsNear.sqrt_image qz143 160363105 16777216 31 16777216 25934754 25934760 8388608 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 160363105 16777216 31 16777216 160363105 16777216 31 16777216 (Ns264p870 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns264p872 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz143) 25934757 8388608 3 8388608 2713298 2713300 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz143) Bool.false 51869514 16777216 6 16777216 25934757 8388608 3 8388608 (Ns264p871 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns264p873 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 5426598 16777216 2 16777216 2713299 8388608 1 8388608 (Ns264p872 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz466 := (@HMul.hMul Real Real Real qz584 qz582 qz654)

noncomputable abbrev qz144 := (Real.cos qz466)

noncomputable abbrev qz662 := (@HMul.hMul Real Real Real qz735 qz766 qz766)

noncomputable abbrev qz467 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz662 qz654) qz599)

noncomputable abbrev qz145 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz467))

noncomputable def Ns264p874 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz136) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz144) qz145) Bool.false 54700462377171 

noncomputable def Ns264p875 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz144) qz145 17973111 16777216 231 

noncomputable abbrev qz146 := (@Neg.neg Real Real.instNeg (Real.cos qz466))

noncomputable def Ns264p876 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz144) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz146)) Bool.true 17973111 16777216 231 16777216 (BSN.inv_eq_neg_inv_neg qz144) 

noncomputable def Ns264p877 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz146) Bool.false 17973111 16777216 231 16777216 17973111 16777216 

noncomputable def Ns264p878 := @Enclosure.Real.IsNear.recentre' qz144 Bool.true 15660893 16777216 181084304 15141437440000 15660893 16777216 11317769 946339840000 

noncomputable abbrev qz147 := qz466

noncomputable def Ns264p879 := @Enclosure.Real.IsNear.cos_image qz147 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 58861891) qz375) Bool.false 58861891 16777216 49 4194304 Bool.true 15660893 16777216 1 

noncomputable def Ns264p880 := nat_lit 836568337760837299347563289 

noncomputable def Ns264p881 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz136 884279719003555 140737488355328 1 500000000000000 9368161 16777216 31 16777216 8284074776660062812355 2361183241434822606848 Ns264p880 

noncomputable def Ns264p882 := @Enclosure.Real.IsNear.subLit_ff_p qz143 qz1 160363105 16777216 31 16777216 9 1 0 1 9368161 9368161 16777216 31 

noncomputable def Ns264p883 := @Ns264p882 16777216 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 160363105 16777216 31 16777216 160363105 16777216 31 16777216 (Ns264p870 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns264p884 := @Enclosure.Real.IsNear.recentre' qz147 Bool.false 8284074776660062812355 2361183241434822606848 Ns264p880 Ns264p439 58861891 16777216 49 4194304 (@Ns264p881 Ns264p439 RS265to276.d43 (Ns264p883 rfl rfl) rfl) 

noncomputable def Ns264p885 := nat_lit 25243576366899509648874813722940818263921 

noncomputable def Ns264p886 := BSN.cos_dyadic_bound_f 12604851131 34359738368 2 1 16777216 7227051 Ns264p885 Ns264p445 Ns264p885 Ns264p885 Ns264p446 Ns264p885 15660893 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 12604851131) qz394 0 1 Ns264p885 Ns264p445 Ns264p885 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 12604851131) qz395 0 1 Ns264p885 Ns264p446 Ns264p885 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p887 := @Ns264p879 3610000 (Ns264p884 rfl) (Enclosure.sfrac_false_div 58861891 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 58861891) qz375) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 886987544692851203899392) qz377) 226375608064910080 72057594037927936 Bool.false 15660893 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 58861891 16777216 226375608064910080 72057594037927936 0 886987544692851203899392 Ns264p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 15660893 16777216 886987544692851203899392 Ns264p92 12604851131 34359738368 7227051 7220000 (Ns264p886 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p888 := @Enclosure.Real.IsNear.inv_image qz146 15660893 16777216 11317769 946339840000 8986440 8986671 8388608 (@Enclosure.Real.IsNear.neg qz144 Bool.true 15660893 16777216 11317769 946339840000 (Ns264p878 (Ns264p887 rfl rfl) rfl)) 

noncomputable def Ns264p889 := Ns264p876 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz146) Bool.false 17973111 16777216 231 16777216 (@Ns264p877 231 16777216 (Ns264p888 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p890 := @Enclosure.Real.IsNear.recentre' qz145 Bool.true 3043461 8388608 

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz346 qz343 qz467)

noncomputable def Ns264p891 := @Enclosure.Real.IsNear.cos_image qz148 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16291319)) qz365) Bool.true 16291319 8388608 

noncomputable def Ns264p892 := nat_lit 76933578976401563900684773405 

noncomputable def Ns264p893 := nat_lit 5941905476834858657964759987789669 

noncomputable def Ns264p894 := @Enclosure.Real.IsNear.recentre' qz148 Bool.true Ns264p892 Ns264p303 Ns264p893 

noncomputable abbrev qz149 := qz467

noncomputable def Ns264p895 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz149 884279719003555 140737488355328 1 500000000000000 87001406142271 

noncomputable abbrev qz468 := (@HSub.hSub Real Real Real qz588 qz662 qz654)

noncomputable abbrev qz150 := qz468

noncomputable def Ns264p896 := @Enclosure.Real.IsNear.subLit_tf qz150 qz31 69409220097855 281474976710656 1100920639 281474976710656 1 16 

noncomputable abbrev qz469 := qz662

noncomputable abbrev qz151 := qz469

noncomputable def Ns264p897 := @Enclosure.Real.IsNear.subLit_ff_n qz151 qz136 87762440521921 281474976710656 580826943 281474976710656 9368161 16777216 31 16777216 

noncomputable def Ns264p898 := @Enclosure.Real.IsNear.mulLit_ff qz136 qz136 9368161 16777216 31 16777216 9368161 16777216 31 16777216 87762440521921 281474976710656 

noncomputable def Ns264p899 := nat_lit 34764516683759012072469360001834733029112824842416890477898224788498781760555389080365756641 

noncomputable def Ns264p900 := nat_lit 349522366434369532031832853920978960837898649234993018004667062352396245640123228942561 

noncomputable def Ns264p901 := nat_lit 209722412243585999225879605263867468171157521708541090514392030389383987946356199237407273185 

noncomputable def Ns264p902 := BSN.cos_dyadic_bound_t 16291319 8388608 4 3 8388608 3610000 Ns264p899 Ns264p312 Ns264p900 Ns264p901 Ns264p315 Ns264p900 3043461 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16291319) (BSN.cosEvenQ 8388608) 0 3 Ns264p899 Ns264p312 Ns264p900 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16291319) (BSN.cosOddQ 8388608) 0 3 Ns264p901 Ns264p315 Ns264p900 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p903 := @Ns264p890 1507707216 60565749760000 3043461 8388608 94231701 3785359360000 (@Ns264p891 413 16777216 Bool.true 3043461 8388608 1 3610000 (@Ns264p894 Ns264p456 16291319 8388608 413 16777216 (@Ns264p895 281474976710656 1100920639 281474976710656 Ns264p892 Ns264p303 Ns264p893 Ns264p456 RS265to276.d43 (@Ns264p896 0 1 1392022498276336 87001406142271 281474976710656 1100920639 281474976710656 (@Ns264p897 1164493477973254471680 69409220097855 281474976710656 1100920639 281474976710656 (@Ns264p898 580826943 281474976710656 (Ns264p883 rfl rfl) (Ns264p883 rfl rfl) rfl) (Ns264p883 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16291319 8388608) (BSN.cos_neg_of_bound 16291319 8388608 Bool.true 3043461 8388608 1 3610000 (Ns264p902 rfl rfl)) rfl rfl) 

noncomputable def Ns264p904 := @Ns264p868 109617451065353715147 Ns264p797 (Ns264p869 qz33 (@Enclosure.Real.IsNear.of_eq qz660 (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 2713299 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz135 (BSN.t_div_two_pi_nonneg qz134 574049 1000 qz137)) Ns264p873) rfl) (@Ns264p874 140737488355328 502726289907123 15876947905085440000 (BSN.correction_mk qz136 (BSN.cos_two_pi_p_ne_zero_mk qz134 574049 1000 9 qz137 rfl rfl (@BSN.floor_sqrt_eq_dec qz134 574049 1000 9 qz137 rfl rfl rfl))) (@Ns264p875 16777216 3043461 8388608 94231701 3785359360000 54700462377171 140737488355328 502726289907123 15876947905085440000 Ns264p889 (Ns264p903 rfl) rfl)) 

noncomputable def Ns264p905 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (hardyZApproximantRS₀ qz134) Bool.true 1532248461717208999959 1180591620717411303424 14325042757883602419147 Ns264p797 (@Eq.refl Real (hardyZApproximantRS₀ qz134)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) (@HMul.hMul Real Real Real qz5 qz655 (Zeta.RiemannSiegel.correction qz136))) Bool.true 1532248461717208999959 1180591620717411303424 14325042757883602419147 Ns264p797 (BSN.hardyZApproximantRS₀_eq qz134 9 (@BSN.floor_sqrt_eq_dec qz134 574049 1000 9 qz137 rfl rfl rfl)) (@Ns264p799 1532248461717208999959 1180591620717411303424 14325042757883602419147 Ns264p797 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 9)) Bool.true 23883717 16777216 89535 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) (Ns264p867 (Ns264p866 rfl) rfl rfl)) (Ns264p904 rfl) rfl rfl)) 

theorem RS265to276.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz134) Bool.true 1532248461717208999959 1180591620717411303424 14325042757883602419147 Ns264p797 := Ns264p905 

noncomputable def Ns264p906 := nat_lit 266370984424365925335040000 

noncomputable def Ns264p907 := nat_lit 28866354095645924013132218368 

noncomputable abbrev qz768 := (Enclosure.sfrac Bool.false 575440 1000)

noncomputable abbrev qz663 := qz768

noncomputable abbrev qz470 := qz663

noncomputable abbrev qz152 := qz470

noncomputable abbrev qz769 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 575440 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz664 := qz769

noncomputable abbrev qz471 := qz664

noncomputable abbrev qz153 := qz471

noncomputable abbrev qz770 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 575440 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz665 := qz770

noncomputable abbrev qz472 := qz665

noncomputable abbrev qz154 := qz472

noncomputable abbrev qz666 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz153 qz9))

noncomputable def Ns264p908 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (@HMul.hMul Real Real Real qz5 qz666 (Zeta.RiemannSiegel.correction qz154)) 15962307 67108864 89751 67108864 149330321015820570925 1180591620717411303424 2850333056972363638619 Ns264p906 Ns264p907 

noncomputable def Ns264p909 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 575440 1000 117 160 134217728 67108864 2251799813685248 Bool.false 135773684650 1830 

noncomputable def Ns264p910 := Ns264p909 279097919 38 47453128 8 294906479 38 44739240 8 Bool.false 55129454 73454 Bool.true 163462305 Bool.true 194705364 7074237752028440 1 Bool.false 125946138 Bool.true Bool.false 16084599 Bool.false Bool.false 15962307 

noncomputable def Ns264p911 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 575440 1000 12 68 134217728 67108864 2251799813685248 Bool.false 135773684650 1830 

noncomputable def Ns264p912 := Ns264p911 240485871 38 54794152 8 261175631 38 50729528 8 Bool.true 1085723 54803 Bool.true 81560388 Bool.true 180867891 7074237752028440 1 Bool.false 110189975 Bool.false Bool.false 29712619 Bool.false Bool.false 55129454 

noncomputable def Ns264p913 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 575440 1000 136 54 134217728 67108864 2251799813685248 Bool.false 135773684650 1830 

noncomputable def Ns264p914 := Ns264p913 186065264 38 67108856 8 216015088 38 60023992 8 Bool.true 18017086 32337 Bool.false 31584011 Bool.false 85211848 7074237752028440 1 Bool.false 130518682 Bool.false Bool.false 108064626 Bool.true Bool.true 1085723 

noncomputable def Ns264p915 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 575440 1000 390 241 134217728 67108864 2251799813685248 Bool.false 135773684650 1830 

noncomputable def Ns264p916 := Ns264p915 93032624 38 94906264 8 147453232 38 77490640 16 Bool.false 134217720 1870 Bool.false 15792983 Bool.false 113476721 7074237752028440 1 Bool.false 133289643 Bool.true Bool.false 100432615 Bool.true Bool.true 18017086 

noncomputable def Ns264p917 := nat_lit 290763114139123674851537054550227266179073857689 

noncomputable def Ns264p918 := nat_lit 287430989786093292078831343264603521102643200 

noncomputable def Ns264p919 := nat_lit 30286026951093131456714752000000000 

noncomputable def Ns264p920 := nat_lit 104566784934320200437953223905280000000 

noncomputable abbrev qz667 := (@Eq.refl Real qz768)

noncomputable abbrev qz473 := qz667

noncomputable abbrev qz155 := qz473

noncomputable def Ns264p921 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz152 575440 1000 1324525774400 16000000 1150880 4000 2000 Ns264p919 Ns264p920 qz155 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns264p922 := nat_lit 5954828577569252860959478877188654411347432605470720000000 

noncomputable abbrev qz668 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1150880))))

noncomputable abbrev qz474 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 575440 4000) (Real.log (Enclosure.sfrac Bool.false 1324525774400 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz668))

noncomputable abbrev qz669 := (Enclosure.sfrac Bool.false 575440 2000)

noncomputable abbrev qz156 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz474 qz669) (@HMul.hMul Real Real Real qz346 qz669 (Real.log Real.pi)))

noncomputable def Ns264p923 := @Enclosure.Real.IsNear.addLit_ft_p qz156 (Enclosure.sfrac Bool.true Ns264p919 Ns264p920) 56947627167281730449 56294995342131200 125919392415678541 9241600000000000000000 Ns264p919 Ns264p920 0 1 Ns264p922 

noncomputable def Ns264p924 := nat_lit 47771132083647686229832499200 

noncomputable abbrev qz157 := (@HSub.hSub Real Real Real qz350 qz474 qz669)

noncomputable def Ns264p925 := @Enclosure.Real.IsNear.subLit_ff_p qz157 (@HMul.hMul Real Real Real qz5 qz669 (Real.log Real.pi)) 75489041509344760721 56294995342131200 364650166196097 72200000000000000000 276288603873 838860800 7193 838860800 Ns264p924 56947627167281730449 56294995342131200 

noncomputable abbrev qz158 := qz474

noncomputable def Ns264p926 := @Enclosure.Real.IsNear.subLit_ff_p qz158 qz669 18337247513836549917 11258999068426240 364650166196097 72200000000000000000 575440 2000 0 1 30195616603737904288400 75489041509344760721 56294995342131200 364650166196097 72200000000000000000 

noncomputable def Ns264p927 := nat_lit 10322952633789355050006808419631104 

noncomputable def Ns264p928 := nat_lit 27379694713554345928949760 

noncomputable def Ns264p929 := nat_lit 18753722412005028137600680063426904659091854168401914241094778880000000000000 

noncomputable def Ns264p930 := nat_lit 85219019727604844319885454943026146368059840555723290706968576000000000000 

noncomputable def Ns264p931 := nat_lit 6623255657789485523231211604450920964353171426075570339840000000000000 

noncomputable def Ns264p932 := BSN.log_dyadic_bound 275949774400 2373101774400 4 3 Ns264p929 67108864 28880000 Ns264p930 Ns264p931 15678069 2649051548800 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 275949774400) (BSN.artanhQ 2373101774400) 0 3 Ns264p930 Ns264p929 Ns264p931 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz475 := (Real.log (Enclosure.sfrac Bool.false 1324525774400 16000000))

noncomputable def Ns264p933 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 575440 4000) qz475 575440 4000 0 1 3187415971601655 281474976710656 781250361 22562500000000000 4585416616746140883 2814749767106560 5619533846673 1128125000000000000 (Enclosure.Real.IsNear.const Bool.false 575440 4000) (BSN.isNear_log_sfrac 1324525774400 16000000 3187415971601655 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1324525774400) qz353)) Bool.false Ns264p928 Ns264p92 1000000462080000 28880000000000000000000 3187415971601655 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1324525774400 16000000 16 2649051548800 2097152000000 15678069 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns264p932 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p934 := BSN.arctan_dyadic_bound_f 1000 1150880 1 0 8388608 3610000 0 1 1 0 1 1 7288 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1150880) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1150880) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns264p935 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1150880))) 884279719003555 562949953421312 1 2000000000000000 7288 8388608 1 3610000 7413773145810438979584 883790629602723 562949953421312 200000000361 722000000000000000 qz17 (Ns264p934 rfl) rfl rfl 

noncomputable abbrev qz476 := (@HMul.hMul Real Real Real qz584 qz589 qz668)

noncomputable abbrev qz159 := qz476

noncomputable abbrev qz477 := qz668

noncomputable abbrev qz160 := qz477

noncomputable def Ns264p936 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 575440 4000) qz475) qz159 4585416616746140883 2814749767106560 5619533846673 1128125000000000000 883790629602723 2251799813685248 200000000361 2888000000000000000 Ns264p927 18337247513836549917 11258999068426240 364650166196097 72200000000000000000 (Ns264p933 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz160 1 4 0 1 883790629602723 562949953421312 200000000361 722000000000000000 883790629602723 2251799813685248 200000000361 2888000000000000000 qz361 Ns264p935 rfl) 

noncomputable def Ns264p937 := @Ns264p923 Ns264p917 Ns264p918 125919392415678541 9241600000000000000000 (@Ns264p925 125919392415678541 9241600000000000000000 (Ns264p926 (Ns264p936 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 575440 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz669 (Real.log Real.pi) 575440 2000 0 1 38410761 33554432 1 33554432 276288603873 838860800 7193 838860800 (Enclosure.Real.IsNear.const Bool.false 575440 2000) RS265to276.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns264p919 Ns264p920) 

noncomputable def Ns264p938 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns264p917 Ns264p918 125919392415678541 9241600000000000000000 16971710581 16777216 229 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz362 qz156 (Enclosure.sfrac Bool.true Ns264p919 Ns264p920)) Bool.false Ns264p917 Ns264p918 125919392415678541 9241600000000000000000 Ns264p921 (Ns264p937 rfl rfl)) 

noncomputable def Ns264p939 := nat_lit 3797821801642521203310592 

noncomputable def Ns264p940 := nat_lit 857019376280321600457410673264365432802920080816942557742211142792437806826512844696646405314850783390869930620741314820882392233884801 

noncomputable def Ns264p941 := nat_lit 610741445414404526944484146219105212868261875306115854587744026139315915380995808626323834470625047176619927325519562744608668801 

noncomputable def Ns264p942 := nat_lit 4279772851393436788424465169087945301536045450285431279935155281468404419483900186996240552394914249217554790511106962187922043868101761 

noncomputable def Ns264p943 := BSN.sin_dyadic_bound_f 53970293857 34359738368 4 3 16777216 7227051 Ns264p940 Ns264p106 Ns264p941 Ns264p942 Ns264p109 Ns264p941 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53970293857) qz363 0 3 Ns264p940 Ns264p106 Ns264p941 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53970293857) qz364 0 3 Ns264p942 Ns264p109 Ns264p941 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p944 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz152) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16971710581) qz375) Bool.false 16971710581 16777216 229 16777216 Bool.false 16777215 16777216 1 3610000 (Ns264p938 rfl) (Enclosure.sfrac_false_div 16971710581 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16971710581) qz375) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns264p939) qz377) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 160 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q3 16971710581 16777216 226375608064910080 72057594037927936 160 Ns264p939 Ns264p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns264p939 Ns264p92 53970293857 34359738368 7227051 7220000 (Ns264p943 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p945 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns264p917 Ns264p918 125919392415678541 9241600000000000000000 135773684650 134217728 1830 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz362 qz156 (Enclosure.sfrac Bool.true Ns264p919 Ns264p920)) Bool.false Ns264p917 Ns264p918 125919392415678541 9241600000000000000000 Ns264p921 (Ns264p937 rfl rfl)) 

noncomputable def Ns264p946 := Ns264p916 32337 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 390 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133289643 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 100432615 134217728) qz155 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) Bool.false 16777215 16777216 52716701 3785359360000 134217720 134217728 1870 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 16777215 16777216 52716701 3785359360000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz152) qz152) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 16777215 16777216 843467216 60565749760000 16777215 16777216 52716701 3785359360000 (Ns264p944 rfl rfl) rfl)) rfl) (Ns264p945 rfl) RS265to276.d7 

noncomputable def Ns264p947 := nat_lit 62209494380029299497802047521 

noncomputable def Ns264p948 := BSN.cos_dyadic_bound_f 15792983 134217728 2 1 134217728 67108864 Ns264p947 Ns264p522 Ns264p947 Ns264p947 Ns264p523 Ns264p947 133289643 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 15792983) qz367 0 1 Ns264p947 Ns264p522 Ns264p947 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 15792983) qz368 0 1 Ns264p947 Ns264p523 Ns264p947 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p949 := nat_lit 162750303274113248087474816843573529729393630673030623996844879511425 

noncomputable def Ns264p950 := nat_lit 27495031664340474621909068177387015127197761889032716332306136961 

noncomputable def Ns264p951 := nat_lit 426206278523792431841617619908500617933444045862497962260531903070081 

noncomputable def Ns264p952 := BSN.sin_dyadic_bound_f 113476721 134217728 3 2 134217728 67108864 Ns264p949 Ns264p243 Ns264p950 Ns264p951 Ns264p246 Ns264p950 100432615 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 113476721) qz369 0 2 Ns264p949 Ns264p243 Ns264p950 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 113476721) qz370 0 2 Ns264p951 Ns264p246 Ns264p950 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p953 := nat_lit 995105505417148283758809230641 

noncomputable def Ns264p954 := BSN.cos_dyadic_bound_f 31584011 134217728 2 1 134217728 67108864 Ns264p953 Ns264p522 Ns264p953 Ns264p953 Ns264p523 Ns264p953 130518682 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 31584011) qz367 0 1 Ns264p953 Ns264p522 Ns264p953 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 31584011) qz368 0 1 Ns264p953 Ns264p523 Ns264p953 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p955 := nat_lit 28746881986957316938300629472076206431227207638761177275873294811136 

noncomputable def Ns264p956 := nat_lit 2779712448856760537102263567164432775911085655696244810088185856 

noncomputable def Ns264p957 := nat_lit 86235086535974237293827683889094290428129800744972139337999708061696 

noncomputable def Ns264p958 := BSN.cos_dyadic_bound_f 85211848 134217728 3 2 134217728 67108864 Ns264p955 Ns264p115 Ns264p956 Ns264p957 Ns264p118 Ns264p956 108064626 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 85211848) qz367 0 2 Ns264p955 Ns264p115 Ns264p956 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 85211848) qz368 0 2 Ns264p957 Ns264p118 Ns264p956 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p959 := Ns264p914 54803 BSN.abs_quadSignPos (BSN.cos_quad_nat0 136 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 130518682 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 54 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 108064626 134217728) qz155 rfl rfl (Ns264p946 RS265to276.d9 RS265to276.d11 RS265to276.d13 RS265to276.d17 (Ns264p948 rfl rfl) (Ns264p952 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns264p945 rfl) RS265to276.d19 RS265to276.d21 RS265to276.d23 RS265to276.d25 RS265to276.d17 (Ns264p954 rfl rfl) (Ns264p958 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns264p960 := nat_lit 24126881660043586229611917307308242438290688562835386556609923710976 

noncomputable def Ns264p961 := nat_lit 1958097284495461629147274824299520435506743045542942273500676096 

noncomputable def Ns264p962 := nat_lit 72376728785561767765577457372276128274001052202415073785282769780736 

noncomputable def Ns264p963 := BSN.cos_dyadic_bound_f 81560388 134217728 3 2 134217728 67108864 Ns264p960 Ns264p115 Ns264p961 Ns264p962 Ns264p118 Ns264p961 110189975 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 81560388) qz367 0 2 Ns264p960 Ns264p115 Ns264p961 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 81560388) qz368 0 2 Ns264p962 Ns264p118 Ns264p961 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p964 := nat_lit 2253733494241970534371274660989844964463059096729321518716315194384964817927968477056961405055740828368561 

noncomputable def Ns264p965 := nat_lit 1225568794993388117993156641431814703542222845996672261825968334205017664503048189518798141644783281 

noncomputable def Ns264p966 := nat_lit 13654786731819562446177226408875867244465712062097107116683086105799596112571797912272920486250840694374065 

noncomputable def Ns264p967 := BSN.cos_dyadic_bound_f 180867891 134217728 4 3 134217728 67108864 Ns264p964 Ns264p125 Ns264p965 Ns264p966 Ns264p128 Ns264p965 29712619 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 180867891) qz367 0 3 Ns264p964 Ns264p125 Ns264p965 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 180867891) qz368 0 3 Ns264p966 Ns264p128 Ns264p965 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p968 := Ns264p912 73454 BSN.abs_quadSignPos (BSN.cos_quad_nat0 12 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 110189975 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 68 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 29712619 134217728) qz155 rfl rfl (Ns264p959 rfl rfl) (Ns264p945 rfl) RS265to276.d27 RS265to276.d29 RS265to276.d31 RS265to276.d33 RS265to276.d17 (Ns264p963 rfl rfl) (Ns264p967 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p969 := nat_lit 701144673797652246892557561781044911200304255160745743616054646330625 

noncomputable def Ns264p970 := nat_lit 509730885761413005680248823445788078037319480647572171328312890625 

noncomputable def Ns264p971 := nat_lit 1835506009940713596995120830379062539112545960547571354526563948090625 

noncomputable def Ns264p972 := BSN.sin_dyadic_bound_f 163462305 134217728 3 2 134217728 67108864 Ns264p969 Ns264p243 Ns264p970 Ns264p971 Ns264p246 Ns264p970 125946138 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 163462305) qz369 0 2 Ns264p969 Ns264p243 Ns264p970 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 163462305) qz370 0 2 Ns264p971 Ns264p246 Ns264p970 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p973 := nat_lit 3028727606914420503930345541698977729880868590960124664218762601159300270237293485988153304421541846450176 

noncomputable def Ns264p974 := nat_lit 2968485927385820698317546076987743050099660625793333988899131915458472939142454705708880458831364096 

noncomputable def Ns264p975 := nat_lit 18342059672052865834324281461291276747906868859667903016356704749965369214754245556523206852084471085137920 

noncomputable def Ns264p976 := BSN.cos_dyadic_bound_f 194705364 134217728 4 3 134217728 67108864 Ns264p973 Ns264p125 Ns264p974 Ns264p975 Ns264p128 Ns264p974 16084599 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 194705364) qz367 0 3 Ns264p973 Ns264p125 Ns264p974 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 194705364) qz368 0 3 Ns264p975 Ns264p128 Ns264p974 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p977 := Ns264p910 89751 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 117 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 125946138 134217728) BSN.abs_quadSignPos qz659 (BSN.sfrac_eq_quadSignPos_mul Bool.false 16084599 134217728) qz155 rfl rfl (Ns264p968 rfl) (Ns264p945 rfl) RS265to276.d35 RS265to276.d37 RS265to276.d39 RS265to276.d41 RS265to276.d17 (Ns264p972 rfl rfl) (Ns264p976 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p978 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) 15962307 134217728 89751 134217728 15962307 134217728 89751 134217728 4284849158356992 15962307 67108864 89751 67108864 (Ns264p977 rfl) 

noncomputable def Ns264p979 := @Enclosure.Real.IsNear.mulLit_tf qz666 (Zeta.RiemannSiegel.correction qz154) 5423315 16777216 1 16777216 27534878762495 70368744177664 524424632448409 15876947905085440000 149330321015820570925 1180591620717411303424 

noncomputable abbrev qz670 := (@HPow.hPow Real Real Real qz7 qz153 qz9)

noncomputable def Ns264p980 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz670 1 1 0 1 5423315 16777216 1 16777216 5423315 16777216 1 16777216 

noncomputable def Ns264p981 := @Enclosure.Real.IsNear.sqrt_image qz153 19206583161 209715200 7193 209715200 80278624 80278655 8388608 (@Enclosure.Real.IsNear.of_eq qz153 (@HMul.hMul Real Real Real qz5 qz152 qz3) Bool.false 19206583161 209715200 7193 209715200 (BSN.t_div_two_pi_mk qz152 575440 1000 qz155) (@Enclosure.Real.IsNear.mulLit_ff qz152 qz3 575440 1000 0 1 2670177 16777216 1 16777216 19206583161 209715200 7193 209715200 (Enclosure.Real.IsNear.const Bool.false 575440 1000) RS265to276.d44 rfl)) 

noncomputable abbrev qz771 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 575440 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz671 := qz771

noncomputable abbrev qz478 := qz671

noncomputable abbrev qz161 := qz478

noncomputable def Ns264p982 := @Enclosure.Real.IsNear.sqrt_image qz161 160557279 16777216 31 16777216 25950451 25950457 8388608 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 160557279 16777216 31 16777216 160557279 16777216 31 16777216 (Ns264p981 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns264p983 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz161) 12975227 4194304 3 8388608 2711657 2711658 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz161) Bool.false 51900908 16777216 6 16777216 12975227 4194304 3 8388608 (Ns264p982 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns264p984 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 5423315 16777216 1 16777216 5423315 16777216 1 16777216 (Ns264p983 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz479 := (@HMul.hMul Real Real Real qz584 qz582 qz665)

noncomputable abbrev qz162 := (Real.cos qz479)

noncomputable abbrev qz672 := (@HMul.hMul Real Real Real qz735 qz770 qz770)

noncomputable abbrev qz480 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz672 qz665) qz599)

noncomputable abbrev qz163 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz480))

noncomputable def Ns264p985 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz154) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz162) qz163) Bool.false 27534878762495 

noncomputable def Ns264p986 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz162) qz163 9269845 8388608 123 

noncomputable abbrev qz164 := (@Neg.neg Real Real.instNeg (Real.cos qz479))

noncomputable def Ns264p987 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz162) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz164)) Bool.true 9269845 8388608 123 8388608 (BSN.inv_eq_neg_inv_neg qz162) 

noncomputable def Ns264p988 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz164) Bool.false 18539690 16777216 246 16777216 9269845 8388608 

noncomputable def Ns264p989 := @Enclosure.Real.IsNear.recentre' qz162 Bool.true 15182292 16777216 181084304 15141437440000 3795573 4194304 11317769 946339840000 

noncomputable abbrev qz165 := qz479

noncomputable def Ns264p990 := @Enclosure.Real.IsNear.cos_image qz165 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 30040961) qz365) Bool.false 30040961 8388608 49 4194304 Bool.true 15182292 16777216 1 

noncomputable def Ns264p991 := nat_lit 836568337762505241307030297 

noncomputable def Ns264p992 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz154 884279719003555 140737488355328 1 500000000000000 9562335 16777216 31 16777216 8455778906817859100925 2361183241434822606848 Ns264p991 

noncomputable def Ns264p993 := @Enclosure.Real.IsNear.subLit_ff_p qz161 qz1 160557279 16777216 31 16777216 9 1 0 1 9562335 9562335 16777216 31 

noncomputable def Ns264p994 := @Ns264p993 16777216 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 160557279 16777216 31 16777216 160557279 16777216 31 16777216 (Ns264p981 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns264p995 := @Enclosure.Real.IsNear.recentre' qz165 Bool.false 8455778906817859100925 2361183241434822606848 Ns264p991 Ns264p439 30040961 8388608 49 4194304 (@Ns264p992 Ns264p439 RS265to276.d43 (Ns264p994 rfl rfl) rfl) 

noncomputable def Ns264p996 := nat_lit 52036428390933722724047951244570281815921 

noncomputable def Ns264p997 := BSN.cos_dyadic_bound_f 15103474619 34359738368 2 1 16777216 7227051 Ns264p996 Ns264p445 Ns264p996 Ns264p996 Ns264p446 Ns264p996 15182292 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 15103474619) qz394 0 1 Ns264p996 Ns264p445 Ns264p996 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 15103474619) qz395 0 1 Ns264p996 Ns264p446 Ns264p996 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p998 := @Ns264p990 3610000 (Ns264p995 rfl) (Enclosure.sfrac_false_div 30040961 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 30040961) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 531406270858112859635712) qz366) 226375608064910080 72057594037927936 Bool.false 15182292 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 30040961 8388608 226375608064910080 72057594037927936 0 531406270858112859635712 Ns264p104 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 15182292 16777216 531406270858112859635712 Ns264p104 15103474619 34359738368 7227051 7220000 (Ns264p997 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p999 := @Enclosure.Real.IsNear.inv_image qz164 3795573 4194304 11317769 946339840000 9269722 9269968 8388608 (@Enclosure.Real.IsNear.neg qz162 Bool.true 3795573 4194304 11317769 946339840000 (Ns264p989 (Ns264p998 rfl rfl) rfl)) 

noncomputable def Ns264p1000 := Ns264p987 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz164) Bool.false 9269845 8388608 123 8388608 (@Ns264p988 123 8388608 (Ns264p999 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p1001 := @Enclosure.Real.IsNear.recentre' qz163 Bool.true 2970371 8388608 

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz346 qz343 qz480)

noncomputable def Ns264p1002 := @Enclosure.Real.IsNear.cos_image qz166 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8106513)) qz415) Bool.true 8106513 4194304 

noncomputable def Ns264p1003 := nat_lit 76563851907015384308432763805 

noncomputable def Ns264p1004 := nat_lit 30034407024972196289658461517854101 

noncomputable def Ns264p1005 := @Enclosure.Real.IsNear.recentre' qz166 Bool.true Ns264p1003 Ns264p303 Ns264p1004 

noncomputable abbrev qz167 := qz480

noncomputable def Ns264p1006 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz167 884279719003555 140737488355328 1 500000000000000 86583295151551 

noncomputable abbrev qz481 := (@HSub.hSub Real Real Real qz588 qz672 qz665)

noncomputable abbrev qz168 := qz481

noncomputable def Ns264p1007 := @Enclosure.Real.IsNear.subLit_tf qz168 qz31 68991109107135 281474976710656 1112959427 281474976710656 1 16 

noncomputable abbrev qz482 := qz672

noncomputable abbrev qz169 := qz482

noncomputable def Ns264p1008 := @Enclosure.Real.IsNear.subLit_ff_n qz169 qz154 91438250652225 281474976710656 592865731 281474976710656 9562335 16777216 31 16777216 

noncomputable def Ns264p1009 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz154 9562335 16777216 31 16777216 9562335 16777216 31 16777216 91438250652225 281474976710656 

noncomputable def Ns264p1010 := nat_lit 8324109982627322788596034818553775221843846418719924230571157009919274599102114908461761 

noncomputable def Ns264p1011 := nat_lit 80539513501804711354231268904299507353666521511355660087367024701121684215352908481 

noncomputable def Ns264p1012 := nat_lit 50221868401434804613800269895151644409166460249971753173522970037933931094872074285865665 

noncomputable def Ns264p1013 := BSN.cos_dyadic_bound_t 8106513 4194304 4 3 8388608 3610000 Ns264p1010 Ns264p575 Ns264p1011 Ns264p1012 Ns264p578 Ns264p1011 2970371 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 8106513) (BSN.cosEvenQ 4194304) 0 3 Ns264p1010 Ns264p575 Ns264p1011 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 8106513) (BSN.cosOddQ 4194304) 0 3 Ns264p1012 Ns264p578 Ns264p1011 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1014 := @Ns264p1001 762878608 30282874880000 2970371 8388608 47679913 1892679680000 (@Ns264p1002 209 8388608 Bool.true 2970371 8388608 1 3610000 (@Ns264p1005 Ns264p306 8106513 4194304 209 8388608 (@Ns264p1006 281474976710656 1112959427 281474976710656 Ns264p1003 Ns264p303 Ns264p1004 Ns264p306 RS265to276.d43 (@Ns264p1007 0 1 1385332722424816 86583295151551 281474976710656 1112959427 281474976710656 (@Ns264p1008 1157478739569971036160 68991109107135 281474976710656 1112959427 281474976710656 (@Ns264p1009 592865731 281474976710656 (Ns264p994 rfl rfl) (Ns264p994 rfl rfl) rfl) (Ns264p994 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8106513 4194304) (BSN.cos_neg_of_bound 8106513 4194304 Bool.true 2970371 8388608 1 3610000 (Ns264p1013 rfl rfl)) rfl rfl) 

noncomputable def Ns264p1015 := @Ns264p979 2850333056972363638619 Ns264p906 (Ns264p980 qz33 (@Enclosure.Real.IsNear.of_eq qz670 (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 5423315 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz153 (BSN.t_div_two_pi_nonneg qz152 575440 1000 qz155)) Ns264p984) rfl) (@Ns264p985 70368744177664 524424632448409 15876947905085440000 (BSN.correction_mk qz154 (BSN.cos_two_pi_p_ne_zero_mk qz152 575440 1000 9 qz155 rfl rfl (@BSN.floor_sqrt_eq_dec qz152 575440 1000 9 qz155 rfl rfl rfl))) (@Ns264p986 8388608 2970371 8388608 47679913 1892679680000 27534878762495 70368744177664 524424632448409 15876947905085440000 Ns264p1000 (Ns264p1014 rfl) rfl)) 

noncomputable def Ns264p1016 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (hardyZApproximantRS₀ qz152) Bool.false 430142195457904398637 1180591620717411303424 359093320914303194998619 Ns264p906 (@Eq.refl Real (hardyZApproximantRS₀ qz152)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (@HMul.hMul Real Real Real qz5 qz666 (Zeta.RiemannSiegel.correction qz154))) Bool.false 430142195457904398637 1180591620717411303424 359093320914303194998619 Ns264p906 (BSN.hardyZApproximantRS₀_eq qz152 9 (@BSN.floor_sqrt_eq_dec qz152 575440 1000 9 qz155 rfl rfl rfl)) (@Ns264p908 430142195457904398637 1180591620717411303424 359093320914303194998619 Ns264p906 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 9)) Bool.false 15962307 67108864 89751 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (Ns264p978 (Ns264p977 rfl) rfl rfl)) (Ns264p1015 rfl) rfl rfl)) 

theorem RS265to276.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz152) Bool.false 430142195457904398637 1180591620717411303424 359093320914303194998619 Ns264p906 := Ns264p1016 

noncomputable def Ns264p1017 := nat_lit 33296373053045740666880000 

noncomputable def Ns264p1018 := nat_lit 3649034003629780511620071424 

noncomputable abbrev qz772 := (Enclosure.sfrac Bool.false 576831 1000)

noncomputable abbrev qz673 := qz772

noncomputable abbrev qz483 := qz673

noncomputable abbrev qz170 := qz483

noncomputable abbrev qz773 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 576831 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz674 := qz773

noncomputable abbrev qz484 := qz674

noncomputable abbrev qz171 := qz484

noncomputable abbrev qz774 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 576831 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz675 := qz774

noncomputable abbrev qz485 := qz675

noncomputable abbrev qz172 := qz485

noncomputable abbrev qz676 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz171 qz9))

noncomputable def Ns264p1019 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) (@HMul.hMul Real Real Real qz5 qz676 (Zeta.RiemannSiegel.correction qz172)) 29002139 33554432 89969 67108864 18803068463665985499 147573952589676412928 372795415965814764629 Ns264p1017 Ns264p1018 

noncomputable def Ns264p1020 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 576831 1000 117 160 134217728 67108864 2251799813685248 Bool.false 136195476256 1834 

noncomputable def Ns264p1021 := Ns264p1020 279097919 38 47453128 8 294906479 38 44739240 8 Bool.true 28087923 73633 Bool.true 129895905 Bool.true 183128670 7074237752028440 1 Bool.false 110547090 Bool.true Bool.false 27503823 Bool.false Bool.true 58004278 

noncomputable def Ns264p1022 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 576831 1000 11 68 134217728 67108864 2251799813685248 Bool.false 136195476256 1834 

noncomputable def Ns264p1023 := Ns264p1022 240485871 38 54794152 8 261175631 38 50729528 8 Bool.true 113897724 54938 Bool.true 205113343 Bool.true 122371588 7074237752028440 1 Bool.false 134096058 Bool.false Bool.false 82191121 Bool.false Bool.true 28087923 

noncomputable def Ns264p1024 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 576831 1000 136 54 134217728 67108864 2251799813685248 Bool.false 136195476256 1834 

noncomputable def Ns264p1025 := Ns264p1024 186065264 38 67108856 8 216015088 38 60023992 8 Bool.true 120089059 32418 Bool.false 194558835 Bool.false 206526466 7074237752028440 1 Bool.false 16230062 Bool.false Bool.false 4301511 Bool.true Bool.true 113897724 

noncomputable def Ns264p1026 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 576831 1000 391 242 134217728 67108864 2251799813685248 Bool.false 136195476256 1834 

noncomputable def Ns264p1027 := Ns264p1026 93032624 38 94906264 8 147453232 38 77490640 16 Bool.true 134217664 1878 Bool.false 97347495 Bool.false 119332167 7074237752028440 1 Bool.false 89034200 Bool.false Bool.false 84572717 Bool.true Bool.true 120089059 

noncomputable def Ns264p1028 := nat_lit 42086723312945076099155532555341499644728856345415446237 

noncomputable def Ns264p1029 := nat_lit 41475565395362521859734463189794026927930310918144000 

noncomputable def Ns264p1030 := nat_lit 30653849779272333637351628712480000 

noncomputable def Ns264p1031 := nat_lit 106092582131584179233416923781347305280 

noncomputable abbrev qz677 := (@Eq.refl Real qz772)

noncomputable abbrev qz486 := qz677

noncomputable abbrev qz173 := qz486

noncomputable def Ns264p1032 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz170 576831 1000 1330937010244 16000000 1153662 4000 2000 Ns264p1030 Ns264p1031 qz173 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns264p1033 := nat_lit 121209763141281819165567933759383518976819106274796485162560 

noncomputable abbrev qz678 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1153662))))

noncomputable abbrev qz487 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 576831 4000) (Real.log (Enclosure.sfrac Bool.false 1330937010244 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz678))

noncomputable abbrev qz679 := (Enclosure.sfrac Bool.false 576831 2000)

noncomputable abbrev qz174 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz487 qz679) (@HMul.hMul Real Real Real qz346 qz679 (Real.log Real.pi)))

noncomputable def Ns264p1034 := @Enclosure.Real.IsNear.addLit_ft_p qz174 (Enclosure.sfrac Bool.true Ns264p1030 Ns264p1031) 1142490787000685095277 1125899906842624000 10097778229740951147 739328000000000000000000 Ns264p1030 Ns264p1031 0 1 Ns264p1033 

noncomputable def Ns264p1035 := nat_lit 76671258846081943965771235328000 

noncomputable abbrev qz175 := (@HSub.hSub Real Real Real qz350 qz487 qz679)

noncomputable def Ns264p1036 := @Enclosure.Real.IsNear.subLit_ff_p qz175 (@HMul.hMul Real Real Real qz5 qz679 (Real.log Real.pi)) 1514215469898869434733 1125899906842624000 1827597707989089 361000000000000000000 22156517678391 67108864000 576831 67108864000 Ns264p1035 1142490787000685095277 1125899906842624000 

noncomputable abbrev qz176 := qz487

noncomputable def Ns264p1037 := @Enclosure.Real.IsNear.subLit_ff_p qz176 qz679 367788490896167651401 225179981368524800 1827597707989089 361000000000000000000 576831 2000 0 1 605686187959547773893200 1514215469898869434733 1125899906842624000 1827597707989089 361000000000000000000 

noncomputable def Ns264p1038 := nat_lit 828186055275568847651038078800232448 

noncomputable def Ns264p1039 := nat_lit 27391369845228341202780160 

noncomputable def Ns264p1040 := nat_lit 971262179982902887940187811501030538693838220772856049400629571278805741889264337972089842848926597120 

noncomputable def Ns264p1041 := nat_lit 4597685598535735630093633278126871849927783893490850342465390737050281385726834517722762999042146304 

noncomputable def Ns264p1042 := nat_lit 4242551428693095739899965871327022496715296697997611436438416760163908171187496805585027399680 

noncomputable def Ns264p1043 := BSN.log_dyadic_bound 282361010244 2379513010244 5 4 Ns264p1040 67108864 28880000 Ns264p1041 Ns264p1042 16002119 2661874020488 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 282361010244) (BSN.artanhQ 2379513010244) 0 4 Ns264p1041 Ns264p1040 Ns264p1042 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz488 := (Real.log (Enclosure.sfrac Bool.false 1330937010244 16000000))

noncomputable def Ns264p1044 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 576831 4000) qz488 576831 4000 0 1 3188775135812855 281474976710656 781250361 22562500000000000 367876870073212992501 225179981368524800 450649426985991 90250000000000000000 (Enclosure.Real.IsNear.const Bool.false 576831 4000) (BSN.isNear_log_sfrac 1330937010244 16000000 3188775135812855 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1330937010244) qz353)) Bool.false Ns264p1039 Ns264p92 1000000462080000 28880000000000000000000 3188775135812855 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1330937010244 16000000 16 2661874020488 2097152000000 16002119 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns264p1043 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p1045 := BSN.arctan_dyadic_bound_f 1000 1153662 1 0 8388608 3610000 0 1 1 0 1 1 7271 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1153662) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1153662) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns264p1046 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1153662))) 884279719003555 562949953421312 1 2000000000000000 7271 8388608 1 3610000 7413782715959647141888 883791770453411 562949953421312 200000000361 722000000000000000 qz17 (Ns264p1045 rfl) rfl rfl 

noncomputable abbrev qz489 := (@HMul.hMul Real Real Real qz584 qz589 qz678)

noncomputable abbrev qz177 := qz489

noncomputable abbrev qz490 := qz678

noncomputable abbrev qz178 := qz490

noncomputable def Ns264p1047 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 576831 4000) qz488) qz177 367876870073212992501 225179981368524800 450649426985991 90250000000000000000 883791770453411 2251799813685248 200000000361 2888000000000000000 Ns264p1038 367788490896167651401 225179981368524800 1827597707989089 361000000000000000000 (Ns264p1044 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz178 1 4 0 1 883791770453411 562949953421312 200000000361 722000000000000000 883791770453411 2251799813685248 200000000361 2888000000000000000 qz361 Ns264p1046 rfl) 

noncomputable def Ns264p1048 := @Ns264p1034 Ns264p1028 Ns264p1029 10097778229740951147 739328000000000000000000 (@Ns264p1036 10097778229740951147 739328000000000000000000 (Ns264p1037 (Ns264p1047 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 576831 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz679 (Real.log Real.pi) 576831 2000 0 1 38410761 33554432 1 33554432 22156517678391 67108864000 576831 67108864000 (Enclosure.Real.IsNear.const Bool.false 576831 2000) RS265to276.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns264p1030 Ns264p1031) 

noncomputable def Ns264p1049 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns264p1028 Ns264p1029 10097778229740951147 739328000000000000000000 4256108633 4194304 115 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz362 qz174 (Enclosure.sfrac Bool.true Ns264p1030 Ns264p1031)) Bool.false Ns264p1028 Ns264p1029 10097778229740951147 739328000000000000000000 Ns264p1032 (Ns264p1048 rfl rfl)) 

noncomputable def Ns264p1050 := BSN.cos_dyadic_bound_f 32493051 34359738368 1 0 16777216 7227051 0 1 1 0 1 1 16777208 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 32493051) qz394 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 32493051) qz395 0 0 rfl) rfl rfl 

noncomputable def Ns264p1051 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz170) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4256108633) qz415) Bool.false 4256108633 4194304 115 8388608 Bool.true 16777208 16777216 1 3610000 (Ns264p1049 rfl) (Enclosure.sfrac_false_div 4256108633 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4256108633) qz415) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 571623800178795872256) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 16777208 16777216 161 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 4256108633 4194304 226375608064910080 72057594037927936 161 571623800178795872256 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777208 16777216 571623800178795872256 604462909807314587353088 32493051 34359738368 7227051 7220000 (Ns264p1050 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p1052 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns264p1028 Ns264p1029 10097778229740951147 739328000000000000000000 136195476256 134217728 1834 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz362 qz174 (Enclosure.sfrac Bool.true Ns264p1030 Ns264p1031)) Bool.false Ns264p1028 Ns264p1029 10097778229740951147 739328000000000000000000 Ns264p1032 (Ns264p1048 rfl rfl)) 

noncomputable def Ns264p1053 := Ns264p1027 32418 BSN.abs_quadSignPos (BSN.cos_quad_nat3 391 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 89034200 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 242 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 84572717 134217728) qz173 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) Bool.true 2097151 2097152 26471163 1892679680000 134217664 134217728 1878 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 2097151 2097152 26471163 1892679680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz170) qz170) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 16777208 16777216 423538608 30282874880000 2097151 2097152 26471163 1892679680000 (Ns264p1051 rfl rfl) rfl)) rfl) (Ns264p1052 rfl) RS265to276.d7 

noncomputable def Ns264p1054 := nat_lit 88137389220734510579216907501475477783917725278898844959204791730625 

noncomputable def Ns264p1055 := nat_lit 8064886205648552253732567369898836981001415237485113767187890625 

noncomputable def Ns264p1056 := nat_lit 230822961952828858622871571680503557983720040105779141851818055090625 

noncomputable def Ns264p1057 := BSN.sin_dyadic_bound_f 97347495 134217728 3 2 134217728 67108864 Ns264p1054 Ns264p243 Ns264p1055 Ns264p1056 Ns264p246 Ns264p1055 89034200 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 97347495) qz369 0 2 Ns264p1054 Ns264p243 Ns264p1055 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 97347495) qz370 0 2 Ns264p1056 Ns264p246 Ns264p1055 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1058 := nat_lit 110596256457608294052406429850870175479757648014121294621729463958721 

noncomputable def Ns264p1059 := nat_lit 41120673365123006655936056890435766583084456062440769553087823041 

noncomputable def Ns264p1060 := nat_lit 331706528026094636143907417438829654906106775130239002326082216230081 

noncomputable def Ns264p1061 := BSN.cos_dyadic_bound_f 119332167 134217728 3 2 134217728 67108864 Ns264p1058 Ns264p115 Ns264p1059 Ns264p1060 Ns264p118 Ns264p1059 84572717 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 119332167) qz367 0 2 Ns264p1058 Ns264p115 Ns264p1059 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 119332167) qz368 0 2 Ns264p1060 Ns264p118 Ns264p1059 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1062 := nat_lit 3019596711890532888881319410974568583533727852521937324831158921570231668466211030947252362958182525640625 

noncomputable def Ns264p1063 := nat_lit 2941788765097123092673378546896616037416685085941323281572363737698578012100635912426332461181640625 

noncomputable def Ns264p1064 := nat_lit 18286859099107392412641651378477223557611146379649622859218221886649696638341805854422077775633920535240625 

noncomputable def Ns264p1065 := BSN.cos_dyadic_bound_f 194558835 134217728 4 3 134217728 67108864 Ns264p1062 Ns264p125 Ns264p1063 Ns264p1064 Ns264p128 Ns264p1063 16230062 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 194558835) qz367 0 3 Ns264p1062 Ns264p125 Ns264p1063 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 194558835) qz368 0 3 Ns264p1064 Ns264p128 Ns264p1063 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1066 := nat_lit 3836676152792672390406572995779725287484879243950502964053202719040940808406070085902255981018145347342336 

noncomputable def Ns264p1067 := nat_lit 6021553696927735987374523302443685173933959764614063237716419511732763341240118394455416061778989056 

noncomputable def Ns264p1068 := nat_lit 23224196398652881497113366785114147548676914626291658706097568963473529023054881785537215895731688538378240 

noncomputable def Ns264p1069 := BSN.cos_dyadic_bound_f 206526466 134217728 4 3 134217728 67108864 Ns264p1066 Ns264p125 Ns264p1067 Ns264p1068 Ns264p128 Ns264p1067 4301511 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 206526466) qz367 0 3 Ns264p1066 Ns264p125 Ns264p1067 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 206526466) qz368 0 3 Ns264p1068 Ns264p128 Ns264p1067 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1070 := Ns264p1025 54938 BSN.abs_quadSignPos (BSN.cos_quad_nat0 136 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 16230062 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 54 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 4301511 134217728) qz173 rfl rfl (Ns264p1053 RS265to276.d9 RS265to276.d11 RS265to276.d13 RS265to276.d17 (Ns264p1057 rfl rfl) (Ns264p1061 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns264p1052 rfl) RS265to276.d19 RS265to276.d21 RS265to276.d23 RS265to276.d25 RS265to276.d17 (Ns264p1065 rfl rfl) (Ns264p1069 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns264p1071 := nat_lit 9690287169354406061550991779325642023446483257956442615574872673837805656679184248774676261949197496524801 

noncomputable def Ns264p1072 := nat_lit 5545324373956746153625473016435061931849717763421004749761193743273068755657591578576466308005273601 

noncomputable def Ns264p1073 := nat_lit 48397488144360225656587098131388827898371873736917462191811428980898093495034236238501221219036046075535361 

noncomputable def Ns264p1074 := BSN.sin_dyadic_bound_f 205113343 134217728 4 3 134217728 67108864 Ns264p1071 Ns264p529 Ns264p1072 Ns264p1073 Ns264p532 Ns264p1072 134096058 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 205113343) qz369 0 3 Ns264p1071 Ns264p529 Ns264p1072 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 205113343) qz370 0 3 Ns264p1073 Ns264p532 Ns264p1072 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1075 := nat_lit 122306571323339011982034388857270927955183008889241138792663498162176 

noncomputable def Ns264p1076 := nat_lit 50285730887464162736947208948887205535473335169331191057492279296 

noncomputable def Ns264p1077 := nat_lit 366819142508242107620629272153915009454478079997384753995875509927936 

noncomputable def Ns264p1078 := BSN.cos_dyadic_bound_f 122371588 134217728 3 2 134217728 67108864 Ns264p1075 Ns264p115 Ns264p1076 Ns264p1077 Ns264p118 Ns264p1076 82191121 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 122371588) qz367 0 2 Ns264p1075 Ns264p115 Ns264p1076 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 122371588) qz368 0 2 Ns264p1077 Ns264p118 Ns264p1076 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1079 := Ns264p1023 73633 BSN.abs_quadSignPos (BSN.cos_quad_nat3 11 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 134096058 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 68 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 82191121 134217728) qz173 rfl rfl (Ns264p1070 rfl rfl) (Ns264p1052 rfl) RS265to276.d27 RS265to276.d29 RS265to276.d31 RS265to276.d33 RS265to276.d17 (Ns264p1074 rfl rfl) (Ns264p1078 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p1080 := nat_lit 279466099159315311984688696590496053979808295215074323893703057530625 

noncomputable def Ns264p1081 := nat_lit 81051989668147003439904764459662362410070298602327195489312890625 

noncomputable def Ns264p1082 := nat_lit 731803794576839293382901026213602592788929230794124223309858644090625 

noncomputable def Ns264p1083 := BSN.sin_dyadic_bound_f 129895905 134217728 3 2 134217728 67108864 Ns264p1080 Ns264p243 Ns264p1081 Ns264p1082 Ns264p246 Ns264p1081 110547090 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 129895905) qz369 0 2 Ns264p1080 Ns264p243 Ns264p1081 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 129895905) qz370 0 2 Ns264p1082 Ns264p246 Ns264p1081 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1084 := nat_lit 2368783622270018359305226125185018874859797447206671278065712703162276991185651703868442558642634304000000 

noncomputable def Ns264p1085 := nat_lit 1422578024068629554712100823800211861285484700508940835238785500824094378258750782453361000000000000 

noncomputable def Ns264p1086 := nat_lit 14350890770005325635917979840835181873138802906037526469456852237546790097682197179644418598475093977600000 

noncomputable def Ns264p1087 := BSN.cos_dyadic_bound_f 183128670 134217728 4 3 134217728 67108864 Ns264p1084 Ns264p125 Ns264p1085 Ns264p1086 Ns264p128 Ns264p1085 27503823 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 183128670) qz367 0 3 Ns264p1084 Ns264p125 Ns264p1085 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 183128670) qz368 0 3 Ns264p1086 Ns264p128 Ns264p1085 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1088 := Ns264p1021 89969 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 117 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 110547090 134217728) BSN.abs_quadSignPos qz659 (BSN.sfrac_eq_quadSignPos_mul Bool.false 27503823 134217728) qz173 rfl rfl (Ns264p1079 rfl) (Ns264p1052 rfl) RS265to276.d35 RS265to276.d37 RS265to276.d39 RS265to276.d41 RS265to276.d17 (Ns264p1083 rfl rfl) (Ns264p1087 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p1089 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) 58004278 134217728 89969 134217728 58004278 134217728 89969 134217728 15570404814880768 29002139 33554432 89969 67108864 (Ns264p1088 rfl) 

noncomputable def Ns264p1090 := @Enclosure.Real.IsNear.mulLit_tf qz676 (Zeta.RiemannSiegel.correction qz172) 5420043 16777216 1 16777216 3469173300593 8796093022208 68636469323841 1984618488135680000 18803068463665985499 147573952589676412928 

noncomputable abbrev qz680 := (@HPow.hPow Real Real Real qz7 qz171 qz9)

noncomputable def Ns264p1091 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz680 1 1 0 1 5420043 16777216 1 16777216 5420043 16777216 1 16777216 

noncomputable def Ns264p1092 := @Enclosure.Real.IsNear.sqrt_image qz171 1540240869087 16777216000 576831 16777216000 80375593 80375624 8388608 (@Enclosure.Real.IsNear.of_eq qz171 (@HMul.hMul Real Real Real qz5 qz170 qz3) Bool.false 1540240869087 16777216000 576831 16777216000 (BSN.t_div_two_pi_mk qz170 576831 1000 qz173) (@Enclosure.Real.IsNear.mulLit_ff qz170 qz3 576831 1000 0 1 2670177 16777216 1 16777216 1540240869087 16777216000 576831 16777216000 (Enclosure.Real.IsNear.const Bool.false 576831 1000) RS265to276.d44 rfl)) 

noncomputable abbrev qz775 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 576831 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz681 := qz775

noncomputable abbrev qz491 := qz681

noncomputable abbrev qz179 := qz491

noncomputable def Ns264p1093 := @Enclosure.Real.IsNear.sqrt_image qz179 160751217 16777216 31 16777216 25966119 25966125 8388608 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 160751217 16777216 31 16777216 160751217 16777216 31 16777216 (Ns264p1092 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns264p1094 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz179) 12983061 4194304 3 8388608 2710021 2710022 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz179) Bool.false 51932244 16777216 6 16777216 12983061 4194304 3 8388608 (Ns264p1093 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns264p1095 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 5420043 16777216 1 16777216 5420043 16777216 1 16777216 (Ns264p1094 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz492 := (@HMul.hMul Real Real Real qz584 qz582 qz675)

noncomputable abbrev qz180 := (Real.cos qz492)

noncomputable abbrev qz682 := (@HMul.hMul Real Real Real qz735 qz774 qz774)

noncomputable abbrev qz493 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz682 qz675) qz599)

noncomputable abbrev qz181 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz493))

noncomputable def Ns264p1096 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz172) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz180) qz181) Bool.false 3469173300593 

noncomputable def Ns264p1097 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz180) qz181 1202953 1048576 33 

noncomputable abbrev qz182 := (@Neg.neg Real Real.instNeg (Real.cos qz492))

noncomputable def Ns264p1098 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz180) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz182)) Bool.true 1202953 1048576 33 2097152 (BSN.inv_eq_neg_inv_neg qz180) 

noncomputable def Ns264p1099 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz182) Bool.false 19247248 16777216 264 16777216 1202953 1048576 

noncomputable def Ns264p1100 := @Enclosure.Real.IsNear.recentre' qz180 Bool.true 14624167 16777216 720727216 60565749760000 14624167 16777216 45045451 3785359360000 

noncomputable abbrev qz183 := qz492

noncomputable def Ns264p1101 := @Enclosure.Real.IsNear.cos_image qz183 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 61300471) qz375) Bool.false 61300471 16777216 195 16777216 Bool.true 14624167 16777216 1 

noncomputable def Ns264p1102 := nat_lit 836568337764171156041933593 

noncomputable def Ns264p1103 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz172 884279719003555 140737488355328 1 500000000000000 9756273 16777216 31 16777216 8627274346961970550515 2361183241434822606848 Ns264p1102 

noncomputable def Ns264p1104 := @Enclosure.Real.IsNear.subLit_ff_p qz179 qz1 160751217 16777216 31 16777216 9 1 0 1 9756273 9756273 16777216 31 

noncomputable def Ns264p1105 := @Ns264p1104 16777216 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 160751217 16777216 31 16777216 160751217 16777216 31 16777216 (Ns264p1092 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns264p1106 := @Enclosure.Real.IsNear.recentre' qz183 Bool.false 8627274346961970550515 2361183241434822606848 Ns264p1102 Ns264p439 61300471 16777216 195 16777216 (@Ns264p1103 Ns264p439 RS265to276.d43 (Ns264p1105 rfl rfl) rfl) 

noncomputable def Ns264p1107 := nat_lit 1238423960030871816241152 

noncomputable def Ns264p1108 := nat_lit 224638736452320835708675709531268681322440692691149847887379672423508172751000061571041 

noncomputable def Ns264p1109 := nat_lit 78328409734541396139472704083124282315821843750582265496873076360672620779474006646456320 

noncomputable def Ns264p1110 := nat_lit 9202723250979028464316896211088150448665102076778493949894894982772260719230676961 

noncomputable def Ns264p1111 := nat_lit 673897803910460549069098494801383867666424747869295986674239227480558973731561723359201 

noncomputable def Ns264p1112 := nat_lit 3524778438054362826276271683740592704211982968776201947359288436230267935076330299090534400 

noncomputable def Ns264p1113 := BSN.cos_dyadic_bound_f 17599062971 34359738368 3 2 16777216 7227051 Ns264p1108 Ns264p1109 Ns264p1110 Ns264p1111 Ns264p1112 Ns264p1110 14624167 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 17599062971) qz394 0 2 Ns264p1108 Ns264p1109 Ns264p1110 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 17599062971) qz395 0 2 Ns264p1111 Ns264p1112 Ns264p1110 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1114 := @Ns264p1101 3610000 (Ns264p1106 rfl) (Enclosure.sfrac_false_div 61300471 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 61300471) qz375) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns264p1107) qz377) 226375608064910080 72057594037927936 Bool.false 14624167 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 61300471 16777216 226375608064910080 72057594037927936 0 Ns264p1107 Ns264p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 14624167 16777216 Ns264p1107 Ns264p92 17599062971 34359738368 7227051 7220000 (Ns264p1113 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p1115 := @Enclosure.Real.IsNear.inv_image qz182 14624167 16777216 45045451 3785359360000 9623492 9623756 8388608 (@Enclosure.Real.IsNear.neg qz180 Bool.true 14624167 16777216 45045451 3785359360000 (Ns264p1100 (Ns264p1114 rfl rfl) rfl)) 

noncomputable def Ns264p1116 := Ns264p1098 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz182) Bool.false 1202953 1048576 33 2097152 (@Ns264p1099 33 2097152 (Ns264p1115 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p1117 := @Enclosure.Real.IsNear.recentre' qz181 Bool.true 2883881 8388608 

noncomputable abbrev qz184 := (@HMul.hMul Real Real Real qz346 qz343 qz493)

noncomputable def Ns264p1118 := @Enclosure.Real.IsNear.cos_image qz184 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8060367)) qz415) Bool.true 8060367 4194304 

noncomputable def Ns264p1119 := nat_lit 76128014767396660623336334525 

noncomputable def Ns264p1120 := nat_lit 30358891805514071960702538826192921 

noncomputable def Ns264p1121 := @Enclosure.Real.IsNear.recentre' qz184 Bool.true Ns264p1119 Ns264p303 Ns264p1120 

noncomputable abbrev qz185 := qz493

noncomputable def Ns264p1122 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz185 884279719003555 140737488355328 1 500000000000000 86090422669855 

noncomputable abbrev qz494 := (@HSub.hSub Real Real Real qz588 qz682 qz675)

noncomputable abbrev qz186 := qz494

noncomputable def Ns264p1123 := @Enclosure.Real.IsNear.subLit_tf qz186 qz31 68498236625439 281474976710656 1124983583 281474976710656 1 16 

noncomputable abbrev qz495 := qz682

noncomputable abbrev qz187 := qz495

noncomputable def Ns264p1124 := @Enclosure.Real.IsNear.subLit_ff_n qz187 qz172 95184862850529 281474976710656 604889887 281474976710656 9756273 16777216 31 16777216 

noncomputable def Ns264p1125 := @Enclosure.Real.IsNear.mulLit_ff qz172 qz172 9756273 16777216 31 16777216 9756273 16777216 31 16777216 95184862850529 281474976710656 

noncomputable def Ns264p1126 := nat_lit 8134667019677829558534414669594960511620260845240808240551036817435807455834926706994241 

noncomputable def Ns264p1127 := nat_lit 75206918708173167896260712060387262460016515582147072880030093545347863424097463361 

noncomputable def Ns264p1128 := nat_lit 49084988585668810437446374601571185522803394571313430367282754081883093361056434722319425 

noncomputable def Ns264p1129 := BSN.cos_dyadic_bound_t 8060367 4194304 4 3 8388608 3610000 Ns264p1126 Ns264p575 Ns264p1127 Ns264p1128 Ns264p578 Ns264p1127 2883881 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 8060367) (BSN.cosEvenQ 4194304) 0 3 Ns264p1126 Ns264p575 Ns264p1127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 8060367) (BSN.cosOddQ 4194304) 0 3 Ns264p1128 Ns264p578 Ns264p1127 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1130 := @Ns264p1117 770098608 30282874880000 2883881 8388608 48131163 1892679680000 (@Ns264p1118 211 8388608 Bool.true 2883881 8388608 1 3610000 (@Ns264p1121 Ns264p306 8060367 4194304 211 8388608 (@Ns264p1122 281474976710656 1124983583 281474976710656 Ns264p1119 Ns264p303 Ns264p1120 Ns264p306 RS265to276.d43 (@Ns264p1123 0 1 1377446762717680 86090422669855 281474976710656 1124983583 281474976710656 (@Ns264p1124 1149209711484101197824 68498236625439 281474976710656 1124983583 281474976710656 (@Ns264p1125 604889887 281474976710656 (Ns264p1105 rfl rfl) (Ns264p1105 rfl rfl) rfl) (Ns264p1105 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8060367 4194304) (BSN.cos_neg_of_bound 8060367 4194304 Bool.true 2883881 8388608 1 3610000 (Ns264p1129 rfl rfl)) rfl rfl) 

noncomputable def Ns264p1131 := @Ns264p1090 372795415965814764629 Ns264p1017 (Ns264p1091 qz33 (@Enclosure.Real.IsNear.of_eq qz680 (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 5420043 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz171 (BSN.t_div_two_pi_nonneg qz170 576831 1000 qz173)) Ns264p1095) rfl) (@Ns264p1096 8796093022208 68636469323841 1984618488135680000 (BSN.correction_mk qz172 (BSN.cos_two_pi_p_ne_zero_mk qz170 576831 1000 9 qz173 rfl rfl (@BSN.floor_sqrt_eq_dec qz170 576831 1000 9 qz173 rfl rfl rfl))) (@Ns264p1097 2097152 2883881 8388608 48131163 1892679680000 3469173300593 8796093022208 68636469323841 1984618488135680000 Ns264p1116 (Ns264p1130 rfl) rfl)) 

noncomputable def Ns264p1132 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (hardyZApproximantRS₀ qz170) Bool.true 108749687779837265957 147573952589676412928 45011330605735563244629 Ns264p1017 (@Eq.refl Real (hardyZApproximantRS₀ qz170)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) (@HMul.hMul Real Real Real qz5 qz676 (Zeta.RiemannSiegel.correction qz172))) Bool.true 108749687779837265957 147573952589676412928 45011330605735563244629 Ns264p1017 (BSN.hardyZApproximantRS₀_eq qz170 9 (@BSN.floor_sqrt_eq_dec qz170 576831 1000 9 qz173 rfl rfl rfl)) (@Ns264p1019 108749687779837265957 147573952589676412928 45011330605735563244629 Ns264p1017 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 9)) Bool.true 29002139 33554432 89969 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) (Ns264p1089 (Ns264p1088 rfl) rfl rfl)) (Ns264p1131 rfl) rfl rfl)) 

theorem RS265to276.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz170) Bool.true 108749687779837265957 147573952589676412928 45011330605735563244629 Ns264p1017 := Ns264p1132 

noncomputable def Ns264p1133 := nat_lit 83522608303863021430636544000 

noncomputable abbrev qz776 := (Enclosure.sfrac Bool.false 578220 1000)

noncomputable abbrev qz683 := qz776

noncomputable abbrev qz496 := qz683

noncomputable abbrev qz188 := qz496

noncomputable abbrev qz777 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 578220 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz684 := qz777

noncomputable abbrev qz497 := qz684

noncomputable abbrev qz189 := qz497

noncomputable abbrev qz778 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 578220 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz685 := qz778

noncomputable abbrev qz498 := qz685

noncomputable abbrev qz190 := qz498

noncomputable abbrev qz686 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz189 qz9))

noncomputable def Ns264p1134 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (@HMul.hMul Real Real Real qz5 qz686 (Zeta.RiemannSiegel.correction qz190)) 274362425 67108864 22547 16777216 37925143617178800675 295147905179352825856 331078997898792693 28039050992038518456320 Ns264p1133 

noncomputable def Ns264p1135 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 578220 1000 117 160 134217728 67108864 2251799813685248 Bool.false 136616885943 1838 

noncomputable def Ns264p1136 := Ns264p1135 279097919 38 47453128 8 294906479 38 44739240 8 Bool.false 292551042 73813 Bool.true 96153227 Bool.true 171344083 7074237752028440 1 Bool.false 88137013 Bool.true Bool.false 38917564 Bool.false Bool.false 274362425 

noncomputable def Ns264p1137 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 578220 1000 11 68 134217728 67108864 2251799813685248 Bool.false 136616885943 1838 

noncomputable def Ns264p1138 := Ns264p1137 240485871 38 54794152 8 261175631 38 50729528 8 Bool.false 205299655 55073 Bool.true 117738531 Bool.true 63734852 7074237752028440 1 Bool.false 103208720 Bool.false Bool.false 119367339 Bool.false Bool.false 292551042 

noncomputable def Ns264p1139 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 578220 1000 137 55 134217728 67108864 2251799813685248 Bool.false 136616885943 1838 

noncomputable def Ns264p1140 := Ns264p1139 186065264 38 67108856 8 216015088 38 60023992 8 Bool.false 218929432 32499 Bool.false 146695156 Bool.false 117062482 7074237752028440 1 Bool.false 119184518 Bool.true Bool.false 102775220 Bool.false Bool.false 205299655 

noncomputable def Ns264p1141 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 578220 1000 392 243 134217728 67108864 2251799813685248 Bool.false 136616885943 1838 

noncomputable def Ns264p1142 := Ns264p1141 93032624 38 94906264 8 147453232 38 77490640 16 Bool.false 134217672 1886 Bool.false 178706153 Bool.false 125100601 7074237752028440 1 Bool.false 31816776 Bool.false Bool.false 107757642 Bool.false Bool.false 218929432 

noncomputable def Ns264p1143 := nat_lit 2091336706680936949135121446231263445928565247 

noncomputable def Ns264p1144 := nat_lit 2054610301764822446828310864919753077555200 

noncomputable def Ns264p1145 := nat_lit 31024701157570395779598336000000000 

noncomputable def Ns264p1146 := nat_lit 107634653778999357143503135211520000000 

noncomputable abbrev qz687 := (@Eq.refl Real qz776)

noncomputable abbrev qz499 := qz687

noncomputable abbrev qz191 := qz499

noncomputable def Ns264p1147 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz188 578220 1000 1337354473600 16000000 1156440 4000 2000 Ns264p1145 Ns264p1146 qz191 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns264p1148 := nat_lit 3083801454203442387716684679754771826828425170616320000000 

noncomputable abbrev qz688 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1156440))))

noncomputable abbrev qz500 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 578220 4000) (Real.log (Enclosure.sfrac Bool.false 1337354473600 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz688))

noncomputable abbrev qz689 := (Enclosure.sfrac Bool.false 578220 2000)

noncomputable abbrev qz192 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz500 qz689) (@HMul.hMul Real Real Real qz346 qz689 (Real.log Real.pi)))

noncomputable def Ns264p1149 := @Enclosure.Real.IsNear.addLit_ft_p qz192 (Enclosure.sfrac Bool.true Ns264p1145 Ns264p1146) 28650645672191755991 28147497671065600 506098511626514907 36966400000000000000000 Ns264p1145 Ns264p1146 0 1 Ns264p1148 

noncomputable def Ns264p1150 := nat_lit 96135614196365256736060211200 

noncomputable abbrev qz193 := (@HSub.hSub Real Real Real qz350 qz500 qz689)

noncomputable def Ns264p1151 := @Enclosure.Real.IsNear.subLit_ff_p qz193 (@HMul.hMul Real Real Real qz5 qz689 (Real.log Real.pi)) 37966140424787756759 28147497671065600 366387666998961 72200000000000000000 1110493511271 3355443200 28911 3355443200 Ns264p1150 28650645672191755991 28147497671065600 

noncomputable abbrev qz194 := qz500

noncomputable def Ns264p1152 := @Enclosure.Real.IsNear.subLit_ff_p qz194 qz689 1844154539058781295 1125899906842624 366387666998961 72200000000000000000 578220 2000 0 1 3037291233983020540720 37966140424787756759 28147497671065600 366387666998961 72200000000000000000 

noncomputable def Ns264p1153 := nat_lit 8305333694918736251339699199672320 

noncomputable def Ns264p1154 := nat_lit 27403000121050047866470400 

noncomputable def Ns264p1155 := nat_lit 992416740144885464892623645274885164846931685425101063959224000101089833211437200179200000000000000000 

noncomputable def Ns264p1156 := nat_lit 4889083993994488574936731985762701724552885449314971072874057126669685505191984496640000000000000000 

noncomputable def Ns264p1157 := nat_lit 5078176965066829566272523819095655296328670222180478379072216940515634760908800000000000000000 

noncomputable def Ns264p1158 := BSN.log_dyadic_bound 288778473600 2385930473600 5 4 Ns264p1155 67108864 28880000 Ns264p1156 Ns264p1157 16324924 2674708947200 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 288778473600) (BSN.artanhQ 2385930473600) 0 4 Ns264p1156 Ns264p1155 Ns264p1157 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz501 := (Real.log (Enclosure.sfrac Bool.false 1337354473600 16000000))

noncomputable def Ns264p1159 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 578220 4000) qz501 578220 4000 0 1 3190129078115575 281474976710656 781250361 22562500000000000 3689192871095975553 2251799813685248 22586729186871 4512500000000000000 (Enclosure.Real.IsNear.const Bool.false 578220 4000) (BSN.isNear_log_sfrac 1337354473600 16000000 3190129078115575 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1337354473600) qz353)) Bool.false Ns264p1154 Ns264p92 1000000462080000 28880000000000000000000 3190129078115575 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1337354473600 16000000 16 2674708947200 2097152000000 16324924 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns264p1158 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p1160 := BSN.arctan_dyadic_bound_f 1000 1156440 1 0 8388608 3610000 0 1 1 0 1 1 7253 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1156440) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1156440) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns264p1161 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1156440))) 884279719003555 562949953421312 1 2000000000000000 7253 8388608 1 3610000 7413792849058808725504 883792978412963 562949953421312 200000000361 722000000000000000 qz17 (Ns264p1160 rfl) rfl rfl 

noncomputable abbrev qz502 := (@HMul.hMul Real Real Real qz584 qz589 qz688)

noncomputable abbrev qz195 := qz502

noncomputable abbrev qz503 := qz688

noncomputable abbrev qz196 := qz503

noncomputable def Ns264p1162 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 578220 4000) qz501) qz195 3689192871095975553 2251799813685248 22586729186871 4512500000000000000 883792978412963 2251799813685248 200000000361 2888000000000000000 Ns264p1153 1844154539058781295 1125899906842624 366387666998961 72200000000000000000 (Ns264p1159 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz196 1 4 0 1 883792978412963 562949953421312 200000000361 722000000000000000 883792978412963 2251799813685248 200000000361 2888000000000000000 qz361 Ns264p1161 rfl) 

noncomputable def Ns264p1163 := @Ns264p1149 Ns264p1143 Ns264p1144 506098511626514907 36966400000000000000000 (@Ns264p1151 506098511626514907 36966400000000000000000 (Ns264p1152 (Ns264p1162 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 578220 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz689 (Real.log Real.pi) 578220 2000 0 1 38410761 33554432 1 33554432 1110493511271 3355443200 28911 3355443200 (Enclosure.Real.IsNear.const Bool.false 578220 2000) RS265to276.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns264p1145 Ns264p1146) 

noncomputable def Ns264p1164 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz188) Bool.false Ns264p1143 Ns264p1144 506098511626514907 36966400000000000000000 8538555371 8388608 231 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz188) (@HAdd.hAdd Real Real Real qz362 qz192 (Enclosure.sfrac Bool.true Ns264p1145 Ns264p1146)) Bool.false Ns264p1143 Ns264p1144 506098511626514907 36966400000000000000000 Ns264p1147 (Ns264p1163 rfl rfl)) 

noncomputable def Ns264p1165 := nat_lit 1897887966418828296978432 

noncomputable def Ns264p1166 := nat_lit 855170477177017847132897518396384192795808312554490610656102015388281577203911729176089892636086987185256986282877655457324529190085281 

noncomputable def Ns264p1167 := nat_lit 606805079188831823889601375599605963197358186887586969549639298995651604828768482737815254640075636482851671723423418354756395681 

noncomputable def Ns264p1168 := nat_lit 4270551262140657788397022730796306234418442581777914925485375784135880010521297449261325161659787112830294844316024634919908300978823841 

noncomputable def Ns264p1169 := BSN.sin_dyadic_bound_f 53941220313 34359738368 4 3 16777216 7227051 Ns264p1166 Ns264p106 Ns264p1167 Ns264p1168 Ns264p109 Ns264p1167 16777209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53941220313) qz363 0 3 Ns264p1166 Ns264p106 Ns264p1167 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53941220313) qz364 0 3 Ns264p1168 Ns264p109 Ns264p1167 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1170 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz188) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8538555371) qz365) Bool.false 8538555371 8388608 231 16777216 Bool.false 16777209 16777216 1 3610000 (Ns264p1164 rfl) (Enclosure.sfrac_false_div 8538555371 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8538555371) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns264p1165) qz366) 226375608064910080 72057594037927936 Bool.false 16777209 16777216 161 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q3 8538555371 8388608 226375608064910080 72057594037927936 161 Ns264p1165 Ns264p104 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777209 16777216 Ns264p1165 Ns264p104 53941220313 34359738368 7227051 7220000 (Ns264p1169 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p1171 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz188) Bool.false Ns264p1143 Ns264p1144 506098511626514907 36966400000000000000000 136616885943 134217728 1838 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz188) (@HAdd.hAdd Real Real Real qz362 qz192 (Enclosure.sfrac Bool.true Ns264p1145 Ns264p1146)) Bool.false Ns264p1143 Ns264p1144 506098511626514907 36966400000000000000000 Ns264p1147 (Ns264p1163 rfl rfl)) 

noncomputable def Ns264p1172 := Ns264p1142 32499 BSN.abs_quadSignPos (BSN.cos_quad_nat0 392 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 31816776 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 243 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 107757642 134217728) qz191 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 1) Bool.false 16777209 16777216 53167951 3785359360000 134217672 134217728 1886 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz188)) Bool.false 16777209 16777216 53167951 3785359360000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz188) qz188) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz188)) Bool.false 16777209 16777216 850687216 60565749760000 16777209 16777216 53167951 3785359360000 (Ns264p1170 rfl rfl) rfl)) rfl) (Ns264p1171 rfl) RS265to276.d7 

noncomputable def Ns264p1173 := nat_lit 2147705399631331387874234097367667157415947714543243989532964815852313111811626308196753887904363715399521 

noncomputable def Ns264p1174 := nat_lit 1060899074531176541775996233358654294331239214665956843273636554061610224967329985269829444594995041 

noncomputable def Ns264p1175 := nat_lit 13013188127849788113896609609034325297264617680733993864350570024260375838878234901094746714329947015122785 

noncomputable def Ns264p1176 := BSN.cos_dyadic_bound_f 178706153 134217728 4 3 134217728 67108864 Ns264p1173 Ns264p125 Ns264p1174 Ns264p1175 Ns264p128 Ns264p1174 31816776 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 178706153) qz367 0 3 Ns264p1173 Ns264p125 Ns264p1174 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 178706153) qz368 0 3 Ns264p1175 Ns264p128 Ns264p1174 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1177 := nat_lit 240418167334796169521517322824088067693928478106582583486810669668545 

noncomputable def Ns264p1178 := nat_lit 59989489869304174905808226542782335903042294655717158176466884801 

noncomputable def Ns264p1179 := nat_lit 629569502893249189606507394077256624940255374183035605161742236080321 

noncomputable def Ns264p1180 := BSN.sin_dyadic_bound_f 125100601 134217728 3 2 134217728 67108864 Ns264p1177 Ns264p243 Ns264p1178 Ns264p1179 Ns264p246 Ns264p1178 107757642 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 125100601) qz369 0 2 Ns264p1177 Ns264p243 Ns264p1178 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 125100601) qz370 0 2 Ns264p1179 Ns264p246 Ns264p1178 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1181 := nat_lit 454662675352846976592071383105318429966080603023776238108927594659840 

noncomputable def Ns264p1182 := nat_lit 214450067082269656774464157658062854742749478169888631509515042816 

noncomputable def Ns264p1183 := nat_lit 1190435992482180311630171156639625691003484746859519851548556866420736 

noncomputable def Ns264p1184 := BSN.sin_dyadic_bound_f 146695156 134217728 3 2 134217728 67108864 Ns264p1181 Ns264p243 Ns264p1182 Ns264p1183 Ns264p246 Ns264p1182 119184518 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 146695156) qz369 0 2 Ns264p1181 Ns264p243 Ns264p1182 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 146695156) qz370 0 2 Ns264p1183 Ns264p246 Ns264p1182 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1185 := nat_lit 184321216751754576391289190418438304683385348212241771495002418725120 

noncomputable def Ns264p1186 := nat_lit 35264832348875205281365384681718835079261527313670128951051960576 

noncomputable def Ns264p1187 := nat_lit 482688948430792378311492335711187062723499964749744411801942726820096 

noncomputable def Ns264p1188 := BSN.sin_dyadic_bound_f 117062482 134217728 3 2 134217728 67108864 Ns264p1185 Ns264p243 Ns264p1186 Ns264p1187 Ns264p246 Ns264p1186 102775220 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 117062482) qz369 0 2 Ns264p1185 Ns264p243 Ns264p1186 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 117062482) qz370 0 2 Ns264p1187 Ns264p246 Ns264p1186 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1189 := Ns264p1140 55073 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 137 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 119184518 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 55 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 102775220 134217728) qz191 rfl rfl (Ns264p1172 RS265to276.d9 RS265to276.d11 RS265to276.d13 RS265to276.d17 (Ns264p1176 rfl rfl) (Ns264p1180 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns264p1171 rfl) RS265to276.d19 RS265to276.d21 RS265to276.d23 RS265to276.d25 RS265to276.d17 (Ns264p1184 rfl rfl) (Ns264p1188 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns264p1190 := nat_lit 188616987666248510370123628023669630384136542526712815116902082786465 

noncomputable def Ns264p1191 := nat_lit 36927414667563879508506811010996712230720982411660293510697825441 

noncomputable def Ns264p1192 := nat_lit 493937085216427185640643348082259799186269777407962303878583372723361 

noncomputable def Ns264p1193 := BSN.sin_dyadic_bound_f 117738531 134217728 3 2 134217728 67108864 Ns264p1190 Ns264p243 Ns264p1191 Ns264p1192 Ns264p246 Ns264p1191 103208720 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 117738531) qz369 0 2 Ns264p1190 Ns264p243 Ns264p1191 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 117738531) qz370 0 2 Ns264p1192 Ns264p246 Ns264p1191 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1194 := nat_lit 8996423355602594386173469950841743914511659673034005319268066983936 

noncomputable def Ns264p1195 := nat_lit 272280069820537708158623080002302730547623375370039603620806656 

noncomputable def Ns264p1196 := nat_lit 26988725506668142083104092606365227138073883772351275878596959338496 

noncomputable def Ns264p1197 := BSN.cos_dyadic_bound_f 63734852 134217728 3 2 134217728 67108864 Ns264p1194 Ns264p115 Ns264p1195 Ns264p1196 Ns264p118 Ns264p1195 119367339 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 63734852) qz367 0 2 Ns264p1194 Ns264p115 Ns264p1195 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 63734852) qz368 0 2 Ns264p1196 Ns264p118 Ns264p1195 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1198 := Ns264p1138 73813 BSN.abs_quadSignPos (BSN.cos_quad_nat3 11 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 103208720 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 68 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 119367339 134217728) qz191 rfl rfl (Ns264p1189 rfl rfl) (Ns264p1171 rfl) RS265to276.d27 RS265to276.d29 RS265to276.d31 RS265to276.d33 RS265to276.d17 (Ns264p1193 rfl rfl) (Ns264p1197 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p1199 := nat_lit 83890851406783897166279562608985607990070344476644901614964497004385 

noncomputable def Ns264p1200 := nat_lit 7306525653673398204196872903636545539454375448980790917201213281 

noncomputable def Ns264p1201 := nat_lit 219702305023851878505068249991213561757406071307152582949136309237601 

noncomputable def Ns264p1202 := BSN.sin_dyadic_bound_f 96153227 134217728 3 2 134217728 67108864 Ns264p1199 Ns264p243 Ns264p1200 Ns264p1201 Ns264p246 Ns264p1200 88137013 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 96153227) qz369 0 2 Ns264p1199 Ns264p243 Ns264p1200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 96153227) qz370 0 2 Ns264p1201 Ns264p246 Ns264p1200 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1203 := nat_lit 1814543801421642460857183945470731112523036781250353147988735908000202083174737560759361401995073831669041 

noncomputable def Ns264p1204 := nat_lit 640367583637246758315346228156724597266514247453005610012311941529102536639025119508836182142586161 

noncomputable def Ns264p1205 := nat_lit 10996644905620306070630393231148044546766332049554241827263800801635113890715772511316050868679835517291825 

noncomputable def Ns264p1206 := BSN.cos_dyadic_bound_f 171344083 134217728 4 3 134217728 67108864 Ns264p1203 Ns264p125 Ns264p1204 Ns264p1205 Ns264p128 Ns264p1204 38917564 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 171344083) qz367 0 3 Ns264p1203 Ns264p125 Ns264p1204 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 171344083) qz368 0 3 Ns264p1205 Ns264p128 Ns264p1204 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1207 := Ns264p1136 90188 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 117 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 88137013 134217728) BSN.abs_quadSignPos qz659 (BSN.sfrac_eq_quadSignPos_mul Bool.false 38917564 134217728) qz191 rfl rfl (Ns264p1198 rfl) (Ns264p1171 rfl) RS265to276.d35 RS265to276.d37 RS265to276.d39 RS265to276.d41 RS265to276.d17 (Ns264p1202 rfl rfl) (Ns264p1206 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p1208 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) 274362425 134217728 90188 134217728 274362425 134217728 90188 134217728 73648602664140800 274362425 67108864 22547 16777216 (Ns264p1207 rfl) 

noncomputable def Ns264p1209 := @Enclosure.Real.IsNear.mulLit_tf qz686 (Zeta.RiemannSiegel.correction qz190) 5416785 16777216 1 16777216 7001412021555 17592186044416 289741158843 7938473952542720 37925143617178800675 295147905179352825856 

noncomputable abbrev qz690 := (@HPow.hPow Real Real Real qz7 qz189 qz9)

noncomputable def Ns264p1210 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz690 1 1 0 1 5416785 16777216 1 16777216 5416785 16777216 1 16777216 

noncomputable def Ns264p1211 := @Enclosure.Real.IsNear.sqrt_image qz189 77197487247 838860800 28911 838860800 80472306 80472337 8388608 (@Enclosure.Real.IsNear.of_eq qz189 (@HMul.hMul Real Real Real qz5 qz188 qz3) Bool.false 77197487247 838860800 28911 838860800 (BSN.t_div_two_pi_mk qz188 578220 1000 qz191) (@Enclosure.Real.IsNear.mulLit_ff qz188 qz3 578220 1000 0 1 2670177 16777216 1 16777216 77197487247 838860800 28911 838860800 (Enclosure.Real.IsNear.const Bool.false 578220 1000) RS265to276.d44 rfl)) 

noncomputable abbrev qz779 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 578220 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz691 := qz779

noncomputable abbrev qz504 := qz691

noncomputable abbrev qz197 := qz504

noncomputable def Ns264p1212 := @Enclosure.Real.IsNear.sqrt_image qz197 160944643 16777216 31 16777216 25981736 25981742 8388608 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 160944643 16777216 31 16777216 160944643 16777216 31 16777216 (Ns264p1211 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns264p1213 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz197) 25981739 8388608 3 8388608 2708392 2708393 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz197) Bool.false 51963478 16777216 6 16777216 25981739 8388608 3 8388608 (Ns264p1212 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns264p1214 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz197)) Bool.false 5416785 16777216 1 16777216 5416785 16777216 1 16777216 (Ns264p1213 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz505 := (@HMul.hMul Real Real Real qz584 qz582 qz685)

noncomputable abbrev qz198 := (Real.cos qz505)

noncomputable abbrev qz692 := (@HMul.hMul Real Real Real qz735 qz778 qz778)

noncomputable abbrev qz506 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz692 qz685) qz599)

noncomputable abbrev qz199 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz506))

noncomputable def Ns264p1215 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz190) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz198) qz199) Bool.false 7001412021555 

noncomputable def Ns264p1216 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz198) qz199 20118711 16777216 289 

noncomputable abbrev qz200 := (@Neg.neg Real Real.instNeg (Real.cos qz505))

noncomputable def Ns264p1217 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz198) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz200)) Bool.true 20118711 16777216 289 16777216 (BSN.inv_eq_neg_inv_neg qz198) 

noncomputable def Ns264p1218 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz200) Bool.false 20118711 16777216 289 16777216 20118711 16777216 

noncomputable def Ns264p1219 := @Enclosure.Real.IsNear.recentre' qz198 Bool.true 13990706 16777216 181084304 15141437440000 6995353 8388608 11317769 946339840000 

noncomputable abbrev qz201 := qz505

noncomputable def Ns264p1220 := @Enclosure.Real.IsNear.cos_image qz201 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 31257901) qz365) Bool.false 31257901 8388608 49 4194304 Bool.true 13990706 16777216 1 

noncomputable def Ns264p1221 := nat_lit 167313667553166534546065157 

noncomputable def Ns264p1222 := nat_lit 14411518807585587200000000000000 

noncomputable def Ns264p1223 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz190 884279719003555 140737488355328 1 500000000000000 9949699 16777216 31 16777216 8798317035889952179945 2361183241434822606848 Ns264p1221 

noncomputable def Ns264p1224 := @Enclosure.Real.IsNear.subLit_ff_p qz197 qz1 160944643 16777216 31 16777216 9 1 0 1 9949699 9949699 16777216 31 

noncomputable def Ns264p1225 := @Ns264p1224 16777216 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 160944643 16777216 31 16777216 160944643 16777216 31 16777216 (Ns264p1211 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns264p1226 := @Enclosure.Real.IsNear.recentre' qz201 Bool.false 8798317035889952179945 2361183241434822606848 Ns264p1221 Ns264p1222 31257901 8388608 49 4194304 (@Ns264p1223 Ns264p1222 RS265to276.d43 (Ns264p1225 rfl rfl) rfl) 

noncomputable def Ns264p1227 := nat_lit 381321187549339445268742937954106066663266608759483283319322525021743796581636665618401 

noncomputable def Ns264p1228 := nat_lit 26515762694459672647860504263973160817203863747568432927361800741684455148012285921 

noncomputable def Ns264p1229 := nat_lit 1143910531122629416460933092853790253668165418550954713092112851463748020834613972283361 

noncomputable def Ns264p1230 := BSN.cos_dyadic_bound_f 20088060859 34359738368 3 2 16777216 7227051 Ns264p1227 Ns264p1109 Ns264p1228 Ns264p1229 Ns264p1112 Ns264p1228 13990706 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 20088060859) qz394 0 2 Ns264p1227 Ns264p1109 Ns264p1228 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 20088060859) qz395 0 2 Ns264p1229 Ns264p1112 Ns264p1228 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1231 := @Ns264p1220 3610000 (Ns264p1226 rfl) (Enclosure.sfrac_false_div 31257901 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 31257901) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 706785807835144904507392) qz366) 226375608064910080 72057594037927936 Bool.false 13990706 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 31257901 8388608 226375608064910080 72057594037927936 0 706785807835144904507392 Ns264p104 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 13990706 16777216 706785807835144904507392 Ns264p104 20088060859 34359738368 7227051 7220000 (Ns264p1230 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p1232 := @Enclosure.Real.IsNear.inv_image qz200 6995353 8388608 11317769 946339840000 10059211 10059500 8388608 (@Enclosure.Real.IsNear.neg qz198 Bool.true 6995353 8388608 11317769 946339840000 (Ns264p1219 (Ns264p1231 rfl rfl) rfl)) 

noncomputable def Ns264p1233 := Ns264p1217 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz200) Bool.false 20118711 16777216 289 16777216 (@Ns264p1218 289 16777216 (Ns264p1232 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p1234 := @Enclosure.Real.IsNear.recentre' qz199 Bool.true 2784040 8388608 

noncomputable abbrev qz202 := (@HMul.hMul Real Real Real qz346 qz343 qz506)

noncomputable def Ns264p1235 := @Enclosure.Real.IsNear.cos_image qz202 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32029311)) qz375) Bool.true 32029311 16777216 

noncomputable def Ns264p1236 := nat_lit 75627072465942700858253445445 

noncomputable def Ns264p1237 := nat_lit 30682519940077530502977423845398173 

noncomputable def Ns264p1238 := @Enclosure.Real.IsNear.recentre' qz202 Bool.true Ns264p1236 Ns264p303 Ns264p1237 

noncomputable abbrev qz203 := qz506

noncomputable def Ns264p1239 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz203 884279719003555 140737488355328 1 500000000000000 85523925111799 

noncomputable abbrev qz507 := (@HSub.hSub Real Real Real qz588 qz692 qz685)

noncomputable abbrev qz204 := qz507

noncomputable def Ns264p1240 := @Enclosure.Real.IsNear.subLit_tf qz204 qz31 67931739067383 281474976710656 1136975995 281474976710656 1 16 

noncomputable abbrev qz508 := qz692

noncomputable abbrev qz205 := qz508

noncomputable def Ns264p1241 := @Enclosure.Real.IsNear.subLit_ff_n qz205 qz190 98996510190601 281474976710656 616882299 281474976710656 9949699 16777216 31 16777216 

noncomputable def Ns264p1242 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz190 9949699 16777216 31 16777216 9949699 16777216 31 16777216 98996510190601 281474976710656 

noncomputable def Ns264p1243 := nat_lit 132892192372884211980940114047486175380901389027890209943288905085091911186940163351153138188801 

noncomputable def Ns264p1244 := nat_lit 1165658022546174605934893023218640143211015991836875125270379771841004384745454625303544321 

noncomputable def Ns264p1245 := nat_lit 801990387287374114409905627247196922128855670756547404878402200168712294709505181556837127012865 

noncomputable def Ns264p1246 := BSN.cos_dyadic_bound_t 32029311 16777216 4 3 8388608 3610000 Ns264p1243 Ns264p192 Ns264p1244 Ns264p1245 Ns264p195 Ns264p1244 2784040 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32029311) (BSN.cosEvenQ 16777216) 0 3 Ns264p1243 Ns264p192 Ns264p1244 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32029311) (BSN.cosOddQ 16777216) 0 3 Ns264p1245 Ns264p195 Ns264p1244 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1247 := @Ns264p1234 777318608 30282874880000 348005 1048576 48582413 1892679680000 (@Ns264p1235 213 8388608 Bool.true 2784040 8388608 1 3610000 (@Ns264p1238 Ns264p306 32029311 16777216 213 8388608 (@Ns264p1239 281474976710656 1136975995 281474976710656 Ns264p1236 Ns264p303 Ns264p1237 Ns264p306 RS265to276.d43 (@Ns264p1240 0 1 1368382801788784 85523925111799 281474976710656 1136975995 281474976710656 (@Ns264p1241 1139705459589123145728 67931739067383 281474976710656 1136975995 281474976710656 (@Ns264p1242 616882299 281474976710656 (Ns264p1225 rfl rfl) (Ns264p1225 rfl rfl) rfl) (Ns264p1225 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32029311 16777216) (BSN.cos_neg_of_bound 32029311 16777216 Bool.true 2784040 8388608 1 3610000 (Ns264p1246 rfl rfl)) rfl rfl) 

noncomputable def Ns264p1248 := @Ns264p1209 331078997898792693 28039050992038518456320 (Ns264p1210 qz33 (@Enclosure.Real.IsNear.of_eq qz690 (@Inv.inv Real Real.instInv (Real.sqrt qz197)) Bool.false 5416785 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz189 (BSN.t_div_two_pi_nonneg qz188 578220 1000 qz191)) Ns264p1214) rfl) (@Ns264p1215 17592186044416 289741158843 7938473952542720 (BSN.correction_mk qz190 (BSN.cos_two_pi_p_ne_zero_mk qz188 578220 1000 9 qz191 rfl rfl (@BSN.floor_sqrt_eq_dec qz188 578220 1000 9 qz191 rfl rfl rfl))) (@Ns264p1216 16777216 348005 1048576 48582413 1892679680000 7001412021555 17592186044416 289741158843 7938473952542720 Ns264p1233 (Ns264p1247 rfl) rfl)) 

noncomputable def Ns264p1249 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz188) (hardyZApproximantRS₀ qz188) Bool.false 1244583849666461667875 295147905179352825856 38012925778526310133 28039050992038518456320 (@Eq.refl Real (hardyZApproximantRS₀ qz188)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz188) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (@HMul.hMul Real Real Real qz5 qz686 (Zeta.RiemannSiegel.correction qz190))) Bool.false 1244583849666461667875 295147905179352825856 38012925778526310133 28039050992038518456320 (BSN.hardyZApproximantRS₀_eq qz188 9 (@BSN.floor_sqrt_eq_dec qz188 578220 1000 9 qz191 rfl rfl rfl)) (@Ns264p1134 1244583849666461667875 295147905179352825856 38012925778526310133 28039050992038518456320 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 9)) Bool.false 274362425 67108864 22547 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (Ns264p1208 (Ns264p1207 rfl) rfl rfl)) (Ns264p1248 rfl) rfl rfl)) 

theorem RS265to276.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz188) Bool.false 1244583849666461667875 295147905179352825856 38012925778526310133 28039050992038518456320 := Ns264p1249 

noncomputable def Ns264p1250 := nat_lit 60885355809159360360889712640 

noncomputable abbrev qz780 := (Enclosure.sfrac Bool.false 579609 1000)

noncomputable abbrev qz693 := qz780

noncomputable abbrev qz509 := qz693

noncomputable abbrev qz206 := qz509

noncomputable abbrev qz781 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 579609 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz694 := qz781

noncomputable abbrev qz510 := qz694

noncomputable abbrev qz207 := qz510

noncomputable abbrev qz782 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 579609 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz695 := qz782

noncomputable abbrev qz511 := qz695

noncomputable abbrev qz208 := qz511

noncomputable abbrev qz696 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz207 qz9))

noncomputable def Ns264p1251 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) (@HMul.hMul Real Real Real qz5 qz696 (Zeta.RiemannSiegel.correction qz208)) 55925013 33554432 90401 67108864 153161463950661900921 1180591620717411303424 837137873832230518269 Ns264p695 Ns264p1250 

noncomputable def Ns264p1252 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 579609 1000 117 160 134217728 67108864 2251799813685248 Bool.false 137038519700 1843 

noncomputable def Ns264p1253 := Ns264p1252 279097919 38 47453128 8 294906479 38 44739240 8 Bool.true 107388461 73987 Bool.true 62186480 Bool.true 159335425 7074237752028440 1 Bool.false 59985306 Bool.true Bool.false 50239327 Bool.false Bool.true 111850026 

noncomputable def Ns264p1254 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 579609 1000 11 68 134217728 67108864 2251799813685248 Bool.false 137038519700 1843 

noncomputable def Ns264p1255 := Ns264p1254 240485871 38 54794152 8 261175631 38 50729528 8 Bool.true 170285850 55202 Bool.true 30139648 Bool.true 4874047 7074237752028440 1 Bool.false 29886981 Bool.false Bool.false 134129238 Bool.false Bool.true 107388461 

noncomputable def Ns264p1256 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 579609 1000 138 56 134217728 67108864 2251799813685248 Bool.false 137038519700 1843 

noncomputable def Ns264p1257 := Ns264p1256 186065264 38 67108856 8 216015088 38 60023992 8 Bool.true 179377591 32573 Bool.false 99055547 Bool.false 27822567 7074237752028440 1 Bool.false 99294449 Bool.true Bool.false 131344310 Bool.false Bool.true 170285850 

noncomputable def Ns264p1258 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 579609 1000 394 244 134217728 67108864 2251799813685248 Bool.false 137038519700 1843 

noncomputable def Ns264p1259 := Ns264p1258 93032624 38 94906264 8 147453232 38 77490640 16 Bool.true 134217648 1886 Bool.false 49460167 Bool.false 131093105 7074237752028440 1 Bool.false 125207183 Bool.true Bool.false 75127539 Bool.false Bool.true 179377591 

noncomputable def Ns264p1260 := nat_lit 43585722676668099266269444768062989590742109632354981059 

noncomputable def Ns264p1261 := nat_lit 42688557083627272715786371305915346302393106038784000 

noncomputable def Ns264p1262 := nat_lit 31399133142011960619447329783520000 

noncomputable def Ns264p1263 := nat_lit 109195358889066214499643291945073462080 

noncomputable abbrev qz783 := (@Eq.refl Real (Enclosure.sfrac Bool.false 579609 1000))

noncomputable abbrev qz697 := qz783

noncomputable abbrev qz512 := qz697

noncomputable abbrev qz209 := qz512

noncomputable def Ns264p1264 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz206 579609 1000 1343787371524 16000000 1159218 4000 2000 Ns264p1262 Ns264p1263 qz209 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns264p1265 := nat_lit 125526881308804125886856000932021410021337275741182345449920 

noncomputable abbrev qz698 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1159218))))

noncomputable abbrev qz513 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 579609 4000) (Real.log (Enclosure.sfrac Bool.false 1343787371524 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz698))

noncomputable abbrev qz699 := (Enclosure.sfrac Bool.false 579609 2000)

noncomputable abbrev qz210 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz513 qz699) (@HMul.hMul Real Real Real qz346 qz699 (Real.log Real.pi)))

noncomputable def Ns264p1266 := @Enclosure.Real.IsNear.addLit_ft_p qz210 (Enclosure.sfrac Bool.true Ns264p1262 Ns264p1263) 1149562746422314088899 1125899906842624000 10146162235319645133 739328000000000000000000 Ns264p1262 Ns264p1263 0 1 Ns264p1265 

noncomputable def Ns264p1267 := nat_lit 77145850009121562757206900736000 

noncomputable abbrev qz211 := (@HSub.hSub Real Real Real qz350 qz513 qz699)

noncomputable def Ns264p1268 := @Enclosure.Real.IsNear.subLit_ff_p qz211 (@HMul.hMul Real Real Real qz5 qz699 (Real.log Real.pi)) 1523077643731809810883 1125899906842624000 1836278962000521 361000000000000000000 22263222772449 67108864000 579609 67108864000 Ns264p1267 1149562746422314088899 1125899906842624000 

noncomputable def Ns264p1269 := nat_lit 3046155287463619621766000 

noncomputable abbrev qz212 := qz513

noncomputable def Ns264p1270 := @Enclosure.Real.IsNear.subLit_ff_p qz212 qz699 1849368503284383037891 1125899906842624000 1836278962000521 361000000000000000000 579609 2000 0 1 Ns264p1269 1523077643731809810883 1125899906842624000 1836278962000521 361000000000000000000 

noncomputable def Ns264p1271 := nat_lit 4164407651131139678681942622331731968 

noncomputable def Ns264p1272 := nat_lit 27414602510582861852049408 

noncomputable def Ns264p1273 := nat_lit 1014025705374687980630447242184121772522686416495029382263847576768032916062713209606675156974812856320 

noncomputable def Ns264p1274 := nat_lit 5194366841011619734579107143777478279509733385945859599250676170033684819217090866004114117184978944 

noncomputable def Ns264p1275 := nat_lit 6056949585018405620793180521564386640099150045058960114480898304377531282519379518220881428480 

noncomputable def Ns264p1276 := BSN.log_dyadic_bound 295211371524 2392363371524 5 4 Ns264p1273 67108864 28880000 Ns264p1274 Ns264p1275 16646955 2687574743048 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 295211371524) (BSN.artanhQ 2392363371524) 0 4 Ns264p1274 Ns264p1273 Ns264p1275 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz514 := (Real.log (Enclosure.sfrac Bool.false 1343787371524 16000000))

noncomputable def Ns264p1277 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 579609 4000) qz514 579609 4000 0 1 3191479774026999 281474976710656 781250361 22562500000000000 1849810400344014863391 1125899906842624000 452819740488849 90250000000000000000 (Enclosure.Real.IsNear.const Bool.false 579609 4000) (BSN.isNear_log_sfrac 1343787371524 16000000 3191479774026999 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1343787371524) qz353)) Bool.false Ns264p1272 Ns264p92 1000000462080000 28880000000000000000000 3191479774026999 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1343787371524 16000000 16 2687574743048 2097152000000 16646955 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns264p1276 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p1278 := BSN.arctan_dyadic_bound_f 1000 1159218 1 0 8388608 3610000 0 1 1 0 1 1 7236 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1159218) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1159218) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns264p1279 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1159218))) 884279719003555 562949953421312 1 2000000000000000 7236 8388608 1 3610000 7413802419208016887808 883794119263651 562949953421312 200000000361 722000000000000000 qz17 (Ns264p1278 rfl) rfl rfl 

noncomputable abbrev qz515 := (@HMul.hMul Real Real Real qz584 qz589 qz698)

noncomputable abbrev qz213 := qz515

noncomputable abbrev qz516 := qz698

noncomputable abbrev qz214 := qz516

noncomputable def Ns264p1280 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 579609 4000) qz514) qz213 1849810400344014863391 1125899906842624000 452819740488849 90250000000000000000 883794119263651 2251799813685248 200000000361 2888000000000000000 Ns264p1271 1849368503284383037891 1125899906842624000 1836278962000521 361000000000000000000 (Ns264p1277 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz214 1 4 0 1 883794119263651 562949953421312 200000000361 722000000000000000 883794119263651 2251799813685248 200000000361 2888000000000000000 qz361 Ns264p1279 rfl) 

noncomputable def Ns264p1281 := @Ns264p1266 Ns264p1260 Ns264p1261 10146162235319645133 739328000000000000000000 (@Ns264p1268 10146162235319645133 739328000000000000000000 (Ns264p1270 (Ns264p1280 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 579609 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz699 (Real.log Real.pi) 579609 2000 0 1 38410761 33554432 1 33554432 22263222772449 67108864000 579609 67108864000 (Enclosure.Real.IsNear.const Bool.false 579609 2000) RS265to276.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns264p1262 Ns264p1263) 

noncomputable def Ns264p1282 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns264p1260 Ns264p1261 10146162235319645133 739328000000000000000000 8564907481 8388608 231 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz362 qz210 (Enclosure.sfrac Bool.true Ns264p1262 Ns264p1263)) Bool.false Ns264p1260 Ns264p1261 10146162235319645133 739328000000000000000000 Ns264p1264 (Ns264p1281 rfl rfl)) 

noncomputable def Ns264p1283 := nat_lit 1897674781628132147331072 

noncomputable def Ns264p1284 := nat_lit 854785535296047408529169601811174555423145088063451525387214186983018453710431224896239793466470134070264875121023632272065418489757696 

noncomputable def Ns264p1285 := nat_lit 605987654279327779826386193483539510597450962248364041701306621813180898269898185157333078632208719561349511744392997866932535296 

noncomputable def Ns264p1286 := nat_lit 4268631315644364942360942126763790904609669218108662951437256574433464491548962023572083308384770856969795639659698419495659221398061056 

noncomputable def Ns264p1287 := BSN.sin_dyadic_bound_f 53935161236 34359738368 4 3 16777216 7227051 Ns264p1284 Ns264p106 Ns264p1285 Ns264p1286 Ns264p109 Ns264p1285 16777206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53935161236) qz363 0 3 Ns264p1284 Ns264p106 Ns264p1285 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53935161236) qz364 0 3 Ns264p1286 Ns264p109 Ns264p1285 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1288 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz206) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8564907481) qz365) Bool.false 8564907481 8388608 231 16777216 Bool.true 16777206 16777216 1 3610000 (Ns264p1282 rfl) (Enclosure.sfrac_false_div 8564907481 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8564907481) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns264p1283) qz366) 226375608064910080 72057594037927936 Bool.false 16777206 16777216 162 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q1 8564907481 8388608 226375608064910080 72057594037927936 162 Ns264p1283 Ns264p104 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777206 16777216 Ns264p1283 Ns264p104 53935161236 34359738368 7227051 7220000 (Ns264p1287 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p1289 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns264p1260 Ns264p1261 10146162235319645133 739328000000000000000000 137038519700 134217728 1843 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz362 qz210 (Enclosure.sfrac Bool.true Ns264p1262 Ns264p1263)) Bool.false Ns264p1260 Ns264p1261 10146162235319645133 739328000000000000000000 Ns264p1264 (Ns264p1281 rfl rfl)) 

noncomputable def Ns264p1290 := Ns264p1259 32573 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 394 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 125207183 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 244 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 75127539 134217728) qz209 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) Bool.true 8388603 8388608 53167951 3785359360000 134217648 134217728 1886 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.true 8388603 8388608 53167951 3785359360000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz206) qz206) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.true 16777206 16777216 850687216 60565749760000 8388603 8388608 53167951 3785359360000 (Ns264p1288 rfl rfl) rfl)) rfl) (Ns264p1289 rfl) RS265to276.d7 

noncomputable def Ns264p1291 := nat_lit 3262690618335203473357056622658111914262463329169319518118650390721 

noncomputable def Ns264p1292 := nat_lit 35813323626194623393039107834182166240313196876648092909775041 

noncomputable def Ns264p1293 := nat_lit 9788000228358358030824383789758667378454909361114205258170131622081 

noncomputable def Ns264p1294 := BSN.cos_dyadic_bound_f 49460167 134217728 3 2 134217728 67108864 Ns264p1291 Ns264p115 Ns264p1292 Ns264p1293 Ns264p118 Ns264p1292 125207183 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 49460167) qz367 0 2 Ns264p1291 Ns264p115 Ns264p1292 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 49460167) qz368 0 2 Ns264p1293 Ns264p118 Ns264p1292 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1295 := nat_lit 161102920561248594131887250958851504841396296608651191682511775690625 

noncomputable def Ns264p1296 := nat_lit 87224562619015671417481441055163805590911811052960171812562890625 

noncomputable def Ns264p1297 := nat_lit 483134312558507751052826789994444186913007066203847654703910201290625 

noncomputable def Ns264p1298 := BSN.cos_dyadic_bound_f 131093105 134217728 3 2 134217728 67108864 Ns264p1295 Ns264p115 Ns264p1296 Ns264p1297 Ns264p118 Ns264p1296 75127539 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 131093105) qz367 0 2 Ns264p1295 Ns264p115 Ns264p1296 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 131093105) qz368 0 2 Ns264p1297 Ns264p118 Ns264p1296 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1299 := nat_lit 52497751285799623438117440567530573602908756453991888440853570998241 

noncomputable def Ns264p1300 := nat_lit 9268947120145463992648081134945574832118699249685842325731233761 

noncomputable def Ns264p1301 := nat_lit 157474715963158579386367025540321829659062031963476293637909250527201 

noncomputable def Ns264p1302 := BSN.cos_dyadic_bound_f 99055547 134217728 3 2 134217728 67108864 Ns264p1299 Ns264p115 Ns264p1300 Ns264p1301 Ns264p118 Ns264p1300 99294449 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 99055547) qz367 0 2 Ns264p1299 Ns264p115 Ns264p1300 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 99055547) qz368 0 2 Ns264p1301 Ns264p118 Ns264p1300 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1303 := nat_lit 599223432028373150851271921121 

noncomputable def Ns264p1304 := BSN.cos_dyadic_bound_f 27822567 134217728 2 1 134217728 67108864 Ns264p1303 Ns264p522 Ns264p1303 Ns264p1303 Ns264p523 Ns264p1303 131344310 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 27822567) qz367 0 1 Ns264p1303 Ns264p522 Ns264p1303 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 27822567) qz368 0 1 Ns264p1303 Ns264p523 Ns264p1303 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1305 := Ns264p1257 55202 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 138 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 99294449 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 56 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131344310 134217728) qz209 rfl rfl (Ns264p1290 RS265to276.d9 RS265to276.d11 RS265to276.d13 RS265to276.d17 (Ns264p1294 rfl rfl) (Ns264p1298 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns264p1289 rfl) RS265to276.d19 RS265to276.d21 RS265to276.d23 RS265to276.d25 RS265to276.d17 (Ns264p1302 rfl rfl) (Ns264p1304 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns264p1306 := nat_lit 825187619627920122596835721216 

noncomputable def Ns264p1307 := BSN.sin_dyadic_bound_f 30139648 134217728 2 1 134217728 67108864 Ns264p1306 Ns264p136 Ns264p1306 Ns264p1306 Ns264p137 Ns264p1306 29886981 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 30139648) qz369 0 1 Ns264p1306 Ns264p136 Ns264p1306 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 30139648) qz370 0 1 Ns264p1306 Ns264p137 Ns264p1306 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1308 := nat_lit 564363412636487716642087681 

noncomputable def Ns264p1309 := BSN.cos_dyadic_bound_f 4874047 134217728 2 1 134217728 67108864 Ns264p1308 Ns264p522 Ns264p1308 Ns264p1308 Ns264p523 Ns264p1308 134129238 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 4874047) qz367 0 1 Ns264p1308 Ns264p522 Ns264p1308 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 4874047) qz368 0 1 Ns264p1308 Ns264p523 Ns264p1308 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1310 := Ns264p1255 73987 BSN.abs_quadSignPos (BSN.cos_quad_nat3 11 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 29886981 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 68 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 134129238 134217728) qz209 rfl rfl (Ns264p1305 rfl rfl) (Ns264p1289 rfl) RS265to276.d27 RS265to276.d29 RS265to276.d31 RS265to276.d33 RS265to276.d17 (Ns264p1307 rfl rfl) (Ns264p1309 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p1311 := nat_lit 14954913276966194267779932160000 

noncomputable def Ns264p1312 := BSN.sin_dyadic_bound_f 62186480 134217728 2 1 134217728 67108864 Ns264p1311 Ns264p136 Ns264p1311 Ns264p1311 Ns264p137 Ns264p1311 59985306 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 62186480) qz369 0 1 Ns264p1311 Ns264p136 Ns264p1311 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 62186480) qz370 0 1 Ns264p1311 Ns264p137 Ns264p1311 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1313 := nat_lit 1356336268552566484625764534481167625293093942736577309215522865091324536425903019630178590762758212890625 

noncomputable def Ns264p1314 := nat_lit 267761490749045313116996749931756940789238046276794080290446952634843277330888280928134918212890625 

noncomputable def Ns264p1315 := nat_lit 8221961080538186916972797708558633539201913226002564800573149944693228896171861975900560134743814212890625 

noncomputable def Ns264p1316 := BSN.cos_dyadic_bound_f 159335425 134217728 4 3 134217728 67108864 Ns264p1313 Ns264p125 Ns264p1314 Ns264p1315 Ns264p128 Ns264p1314 50239327 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 159335425) qz367 0 3 Ns264p1313 Ns264p125 Ns264p1314 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 159335425) qz368 0 3 Ns264p1315 Ns264p128 Ns264p1314 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1317 := Ns264p1253 90401 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 117 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 59985306 134217728) BSN.abs_quadSignPos qz659 (BSN.sfrac_eq_quadSignPos_mul Bool.false 50239327 134217728) qz209 rfl rfl (Ns264p1310 rfl) (Ns264p1289 rfl) RS265to276.d35 RS265to276.d37 RS265to276.d39 RS265to276.d41 RS265to276.d17 (Ns264p1312 rfl rfl) (Ns264p1316 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p1318 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) 111850026 134217728 90401 134217728 111850026 134217728 90401 134217728 30024512732921856 55925013 33554432 90401 67108864 (Ns264p1317 rfl) 

noncomputable def Ns264p1319 := @Enclosure.Real.IsNear.mulLit_tf qz696 (Zeta.RiemannSiegel.correction qz208) 5413537 16777216 1 16777216 28292309436633 70368744177664 1234744465823379 31753895810170880000 153161463950661900921 1180591620717411303424 

noncomputable abbrev qz700 := (@HPow.hPow Real Real Real qz7 qz207 qz9)

noncomputable def Ns264p1320 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz700 1 1 0 1 5413537 16777216 1 16777216 5413537 16777216 1 16777216 

noncomputable def Ns264p1321 := @Enclosure.Real.IsNear.sqrt_image qz207 1547658620793 16777216000 579609 16777216000 80568904 80568935 8388608 (@Enclosure.Real.IsNear.of_eq qz207 (@HMul.hMul Real Real Real qz5 qz206 qz3) Bool.false 1547658620793 16777216000 579609 16777216000 (BSN.t_div_two_pi_mk qz206 579609 1000 qz209) (@Enclosure.Real.IsNear.mulLit_ff qz206 qz3 579609 1000 0 1 2670177 16777216 1 16777216 1547658620793 16777216000 579609 16777216000 (Enclosure.Real.IsNear.const Bool.false 579609 1000) RS265to276.d44 rfl)) 

noncomputable abbrev qz784 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 579609 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz701 := qz784

noncomputable abbrev qz517 := qz701

noncomputable abbrev qz215 := qz517

noncomputable def Ns264p1322 := @Enclosure.Real.IsNear.sqrt_image qz215 161137839 16777216 31 16777216 25997325 25997331 8388608 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 161137839 16777216 31 16777216 161137839 16777216 31 16777216 (Ns264p1321 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns264p1323 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz215) 1624833 524288 3 8388608 2706768 2706769 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz215) Bool.false 51994656 16777216 6 16777216 1624833 524288 3 8388608 (Ns264p1322 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns264p1324 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 5413537 16777216 1 16777216 5413537 16777216 1 16777216 (Ns264p1323 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz216 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz511))

noncomputable abbrev qz702 := (@HMul.hMul Real Real Real qz735 qz782 qz782)

noncomputable abbrev qz518 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz702 qz695) qz599)

noncomputable abbrev qz217 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz518))

noncomputable def Ns264p1325 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz208) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz216) qz217) Bool.false 28292309436633 

noncomputable def Ns264p1326 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz216) qz217 21187837 16777216 321 

noncomputable abbrev qz703 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz216))

noncomputable def Ns264p1327 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz216) (@Neg.neg Real Real.instNeg qz703) Bool.true 21187837 16777216 321 16777216 (BSN.inv_eq_neg_inv_neg qz216) 

noncomputable def Ns264p1328 := @Enclosure.Real.IsNear.recentre' qz703 Bool.false 21187837 16777216 321 16777216 21187837 16777216 

noncomputable def Ns264p1329 := @Enclosure.Real.IsNear.recentre' qz216 Bool.true 13284743 16777216 181084304 15141437440000 13284743 16777216 11317769 946339840000 

noncomputable abbrev qz218 := (@HMul.hMul Real Real Real qz346 qz343 qz511)

noncomputable abbrev qz704 := (@Nat.cast Real Real.instNatCast 2097152)

noncomputable def Ns264p1330 := @Enclosure.Real.IsNear.cos_image qz218 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7966211) qz704) Bool.false 7966211 2097152 49 4194304 Bool.true 13284743 16777216 1 

noncomputable def Ns264p1331 := nat_lit 836568337767492213733761817 

noncomputable def Ns264p1332 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz208 884279719003555 140737488355328 1 500000000000000 10142895 16777216 31 16777216 8969156340482562991725 2361183241434822606848 Ns264p1331 

noncomputable def Ns264p1333 := @Enclosure.Real.IsNear.subLit_ff_p qz215 qz1 161137839 16777216 31 16777216 9 1 0 1 10142895 10142895 16777216 31 

noncomputable def Ns264p1334 := @Ns264p1333 16777216 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 161137839 16777216 31 16777216 161137839 16777216 31 16777216 (Ns264p1321 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns264p1335 := @Enclosure.Real.IsNear.recentre' qz218 Bool.false 8969156340482562991725 2361183241434822606848 Ns264p1331 Ns264p439 7966211 2097152 49 4194304 (@Ns264p1332 Ns264p439 RS265to276.d43 (Ns264p1334 rfl rfl) rfl) 

noncomputable def Ns264p1336 := nat_lit 608132994066443571350845658448199652503563973171432857273401229248157112733611452280801 

noncomputable def Ns264p1337 := nat_lit 67434705042265077335341902646676531358210796396221645692338082965377972167653732321 

noncomputable def Ns264p1338 := nat_lit 1824264112789246183897866291539305604447975497921506128528819011578540582256499049377761 

noncomputable def Ns264p1339 := BSN.cos_dyadic_bound_f 22574099387 34359738368 3 2 16777216 7227051 Ns264p1336 Ns264p1109 Ns264p1337 Ns264p1338 Ns264p1112 Ns264p1337 13284743 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 22574099387) qz394 0 2 Ns264p1336 Ns264p1109 Ns264p1337 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 22574099387) qz395 0 2 Ns264p1338 Ns264p1112 Ns264p1337 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1340 := @Ns264p1330 3610000 (Ns264p1335 rfl) (Enclosure.sfrac_false_div 7966211 2097152) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7966211) qz704) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 198563878107867273756672) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 13284743 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 7966211 2097152 226375608064910080 72057594037927936 0 198563878107867273756672 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 13284743 16777216 198563878107867273756672 302231454903657293676544 22574099387 34359738368 7227051 7220000 (Ns264p1339 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p1341 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz216) 13284743 16777216 11317769 946339840000 10593758 10594079 8388608 (@Enclosure.Real.IsNear.neg qz216 Bool.true 13284743 16777216 11317769 946339840000 (Ns264p1329 (Ns264p1340 rfl rfl) rfl)) 

noncomputable def Ns264p1342 := Ns264p1327 (@Enclosure.Real.IsNear.neg qz703 Bool.false 21187837 16777216 321 16777216 (@Ns264p1328 321 16777216 (Ns264p1341 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p1343 := @Enclosure.Real.IsNear.recentre' qz217 Bool.true 2670618 8388608 

noncomputable abbrev qz219 := (@HMul.hMul Real Real Real qz346 qz343 qz518)

noncomputable def Ns264p1344 := @Enclosure.Real.IsNear.cos_image qz219 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3973679)) qz704) Bool.true 3973679 2097152 

noncomputable def Ns264p1345 := nat_lit 75060675593961060010315892605 

noncomputable def Ns264p1346 := nat_lit 31005763253205020248401457172907061 

noncomputable def Ns264p1347 := @Enclosure.Real.IsNear.recentre' qz219 Bool.true Ns264p1345 Ns264p303 Ns264p1346 

noncomputable abbrev qz220 := qz518

noncomputable def Ns264p1348 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz220 884279719003555 140737488355328 1 500000000000000 84883407343711 

noncomputable abbrev qz519 := (@HSub.hSub Real Real Real qz588 qz702 qz695)

noncomputable abbrev qz221 := qz519

noncomputable def Ns264p1349 := @Enclosure.Real.IsNear.subLit_tf qz221 qz31 67291221299295 281474976710656 1148954147 281474976710656 1 16 

noncomputable abbrev qz520 := qz702

noncomputable abbrev qz222 := qz520

noncomputable def Ns264p1350 := @Enclosure.Real.IsNear.subLit_ff_n qz222 qz208 102878318981025 281474976710656 628860451 281474976710656 10142895 16777216 31 16777216 

noncomputable def Ns264p1351 := @Enclosure.Real.IsNear.mulLit_ff qz208 qz208 10142895 16777216 31 16777216 10142895 16777216 31 16777216 102878318981025 281474976710656 

noncomputable def Ns264p1352 := nat_lit 1876113694830560483749028862243862983193163935171765317229663913581720026858632771521 

noncomputable def Ns264p1353 := nat_lit 3466537250751077332112698720796095110148055492926080949987665366995300109908547993600 

noncomputable def Ns264p1354 := nat_lit 15499346038777711884286161106056562135166140586762329246359949882900232747874241 

noncomputable def Ns264p1355 := nat_lit 11323903251639641388828457728558946870642622137054124912347538107287731225561017612225 

noncomputable def Ns264p1356 := nat_lit 315454889818348037222255583592444655023473049856273366448877548396572310001677867417600 

noncomputable def Ns264p1357 := BSN.cos_dyadic_bound_t 3973679 2097152 4 3 8388608 3610000 Ns264p1352 Ns264p1353 Ns264p1354 Ns264p1355 Ns264p1356 Ns264p1354 2670618 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3973679) (BSN.cosEvenQ 2097152) 0 3 Ns264p1352 Ns264p1353 Ns264p1354 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3973679) (BSN.cosOddQ 2097152) 0 3 Ns264p1355 Ns264p1356 Ns264p1354 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1358 := @Ns264p1343 1572687216 60565749760000 1335309 4194304 98292951 3785359360000 (@Ns264p1344 431 16777216 Bool.true 2670618 8388608 1 3610000 (@Ns264p1347 Ns264p306 3973679 2097152 431 16777216 (@Ns264p1348 281474976710656 1148954147 281474976710656 Ns264p1345 Ns264p303 Ns264p1346 Ns264p306 RS265to276.d43 (@Ns264p1349 0 1 1358134517499376 84883407343711 281474976710656 1148954147 281474976710656 (@Ns264p1350 1128959354642072862720 67291221299295 281474976710656 1148954147 281474976710656 (@Ns264p1351 628860451 281474976710656 (Ns264p1334 rfl rfl) (Ns264p1334 rfl rfl) rfl) (Ns264p1334 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 3973679 2097152) (BSN.cos_neg_of_bound 3973679 2097152 Bool.true 2670618 8388608 1 3610000 (Ns264p1357 rfl rfl)) rfl rfl) 

noncomputable def Ns264p1359 := @Ns264p1319 837137873832230518269 Ns264p695 (Ns264p1320 qz33 (@Enclosure.Real.IsNear.of_eq qz700 (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 5413537 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz207 (BSN.t_div_two_pi_nonneg qz206 579609 1000 qz209)) Ns264p1324) rfl) (@Ns264p1325 70368744177664 1234744465823379 31753895810170880000 (BSN.correction_mk qz208 (BSN.cos_two_pi_p_ne_zero_mk qz206 579609 1000 9 qz209 rfl rfl (@BSN.floor_sqrt_eq_dec qz206 579609 1000 9 qz209 rfl rfl rfl))) (@Ns264p1326 16777216 1335309 4194304 98292951 3785359360000 28292309436633 70368744177664 1234744465823379 31753895810170880000 Ns264p1342 (Ns264p1358 rfl) rfl)) 

noncomputable def Ns264p1360 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (hardyZApproximantRS₀ qz206) Bool.true 1814525002514104853895 1180591620717411303424 90542885846809034358269 Ns264p695 (@Eq.refl Real (hardyZApproximantRS₀ qz206)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) (@HMul.hMul Real Real Real qz5 qz696 (Zeta.RiemannSiegel.correction qz208))) Bool.true 1814525002514104853895 1180591620717411303424 90542885846809034358269 Ns264p695 (BSN.hardyZApproximantRS₀_eq qz206 9 (@BSN.floor_sqrt_eq_dec qz206 579609 1000 9 qz209 rfl rfl rfl)) (@Ns264p1251 1814525002514104853895 1180591620717411303424 90542885846809034358269 Ns264p695 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 9)) Bool.true 55925013 33554432 90401 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) (Ns264p1318 (Ns264p1317 rfl) rfl rfl)) (Ns264p1359 rfl) rfl rfl)) 

theorem RS265to276.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz206) Bool.true 1814525002514104853895 1180591620717411303424 90542885846809034358269 Ns264p695 := Ns264p1360 

noncomputable def Ns264p1361 := nat_lit 8914850370078845812367949824 

noncomputable abbrev qz785 := (Enclosure.sfrac Bool.false 580998 1000)

noncomputable abbrev qz705 := qz785

noncomputable abbrev qz521 := qz705

noncomputable abbrev qz223 := qz521

noncomputable abbrev qz786 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 580998 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz706 := qz786

noncomputable abbrev qz522 := qz706

noncomputable abbrev qz224 := qz522

noncomputable abbrev qz787 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 580998 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz707 := qz787

noncomputable abbrev qz523 := qz707

noncomputable abbrev qz225 := qz523

noncomputable abbrev qz708 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz224 qz9))

noncomputable def Ns264p1362 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (@HMul.hMul Real Real Real qz5 qz708 (Zeta.RiemannSiegel.correction qz225)) 116418815 33554432 90611 67108864 9675563198348617527 73786976294838206464 1800276577705053937 133185492212182962667520 Ns264p1361 

noncomputable def Ns264p1363 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 580998 1000 117 160 134217728 67108864 2251799813685248 Bool.false 137460376784 1847 

noncomputable def Ns264p1364 := Ns264p1363 279097919 38 47453128 8 294906479 38 44739240 8 Bool.false 222211601 74158 Bool.true 27996405 Bool.true 147103440 7074237752028440 1 Bool.false 27793827 Bool.true Bool.false 61357895 Bool.false Bool.false 232837630 

noncomputable def Ns264p1365 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 580998 1000 10 67 134217728 67108864 2251799813685248 Bool.false 137460376784 1847 

noncomputable def Ns264p1366 := Ns264p1365 240485871 38 54794152 8 261175631 38 50729528 8 Bool.false 198394499 55328 Bool.true 153146153 Bool.true 156618628 7074237752028440 1 Bool.false 55923216 Bool.true Bool.false 123418111 Bool.false Bool.false 222211601 

noncomputable def Ns264p1367 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 580998 1000 139 56 134217728 67108864 2251799813685248 Bool.false 137460376784 1847 

noncomputable def Ns264p1368 := Ns264p1367 186065264 38 67108856 8 216015088 38 60023992 8 Bool.false 146778705 32646 Bool.false 51639266 Bool.false 149634694 7074237752028440 1 Bool.false 50374662 Bool.false Bool.false 59095848 Bool.false Bool.false 198394499 

noncomputable def Ns264p1369 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 580998 1000 395 245 134217728 67108864 2251799813685248 Bool.false 137460376784 1847 

noncomputable def Ns264p1370 := Ns264p1369 93032624 38 94906264 8 147453232 38 77490640 16 Bool.false 134217712 1886 Bool.false 131266222 Bool.false 137308935 7074237752028440 1 Bool.false 111318440 Bool.false Bool.false 114580409 Bool.true Bool.false 146778705 

noncomputable def Ns264p1371 := nat_lit 346502402312476925110921392136888762807082460119548899 

noncomputable def Ns264p1372 := nat_lit 338328515263100107599552379996536258696222605312000 

noncomputable def Ns264p1373 := nat_lit 31777171598568063596365478384640000 

noncomputable def Ns264p1374 := nat_lit 110774877152576699459895150356490424320 

noncomputable abbrev qz788 := (@Eq.refl Real (Enclosure.sfrac Bool.false 580998 1000))

noncomputable abbrev qz709 := qz788

noncomputable abbrev qz524 := qz709

noncomputable abbrev qz226 := qz524

noncomputable def Ns264p1375 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz223 580998 1000 1350235704016 16000000 1161996 4000 2000 Ns264p1373 Ns264p1374 qz226 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns264p1376 := nat_lit 63867322794235746836445030998671336760601439049235253063680 

noncomputable abbrev qz710 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1161996))))

noncomputable abbrev qz525 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 580998 4000) (Real.log (Enclosure.sfrac Bool.false 1350235704016 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz710))

noncomputable abbrev qz711 := (Enclosure.sfrac Bool.false 580998 2000)

noncomputable abbrev qz227 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz525 qz711) (@HMul.hMul Real Real Real qz346 qz711 (Real.log Real.pi)))

noncomputable def Ns264p1377 := @Enclosure.Real.IsNear.addLit_ft_p qz227 (Enclosure.sfrac Bool.true Ns264p1373 Ns264p1374) 576550769676998193399 562949953421312000 5085177119054496063 369664000000000000000000 Ns264p1373 Ns264p1374 0 1 Ns264p1376 

noncomputable def Ns264p1378 := nat_lit 19345833595674497844529594368000 

noncomputable abbrev qz228 := (@HSub.hSub Real Real Real qz350 qz525 qz711)

noncomputable def Ns264p1379 := @Enclosure.Real.IsNear.subLit_ff_p qz228 (@HMul.hMul Real Real Real qz5 qz711 (Real.log Real.pi)) 763755771934573900023 562949953421312000 1840619589006237 361000000000000000000 11158287659739 33554432000 290499 33554432000 Ns264p1378 576550769676998193399 562949953421312000 

noncomputable def Ns264p1380 := nat_lit 1527511543869147800046000 

noncomputable abbrev qz229 := qz525

noncomputable def Ns264p1381 := @Enclosure.Real.IsNear.subLit_ff_p qz229 qz711 927292170453511614711 562949953421312000 1840619589006237 361000000000000000000 580998 2000 0 1 Ns264p1380 763755771934573900023 562949953421312000 1840619589006237 361000000000000000000 

noncomputable def Ns264p1382 := nat_lit 2088076336659006684418485776000483328 

noncomputable def Ns264p1383 := nat_lit 27426177121913174216409088 

noncomputable def Ns264p1384 := nat_lit 1036098587340298575843155655699608590980371474470533050426147511331093426219896086358412982810805534720 

noncomputable def Ns264p1385 := nat_lit 5514042662224656763533509825458844541851715692559648636666972421774951393656735210716778510862516224 

noncomputable def Ns264p1386 := nat_lit 7199920544871799109150440421885111360684793143688919380970560068670986475479634425770231726080 

noncomputable def Ns264p1387 := BSN.log_dyadic_bound 301659704016 2398811704016 5 4 Ns264p1384 67108864 28880000 Ns264p1385 Ns264p1386 16968215 2700471408032 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 301659704016) (BSN.artanhQ 2398811704016) 0 4 Ns264p1385 Ns264p1384 Ns264p1386 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz526 := (Real.log (Enclosure.sfrac Bool.false 1350235704016 16000000))

noncomputable def Ns264p1388 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 580998 4000) qz526 580998 4000 0 1 3192827236130039 281474976710656 781250361 22562500000000000 927513119268540199461 562949953421312000 226952448620139 45125000000000000000 (Enclosure.Real.IsNear.const Bool.false 580998 4000) (BSN.isNear_log_sfrac 1350235704016 16000000 3192827236130039 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1350235704016) qz353)) Bool.false Ns264p1383 Ns264p92 1000000462080000 28880000000000000000000 3192827236130039 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1350235704016 16000000 16 2700471408032 2097152000000 16968215 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns264p1387 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p1389 := BSN.arctan_dyadic_bound_f 1000 1161996 1 0 8388608 3610000 0 1 1 0 1 1 7219 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1161996) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1161996) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns264p1390 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1161996))) 884279719003555 562949953421312 1 2000000000000000 7219 8388608 1 3610000 7413811989357225050112 883795260114339 562949953421312 200000000361 722000000000000000 qz17 (Ns264p1389 rfl) rfl rfl 

noncomputable abbrev qz527 := (@HMul.hMul Real Real Real qz584 qz589 qz710)

noncomputable abbrev qz230 := qz527

noncomputable abbrev qz528 := qz710

noncomputable abbrev qz231 := qz528

noncomputable def Ns264p1391 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 580998 4000) qz526) qz230 927513119268540199461 562949953421312000 226952448620139 45125000000000000000 883795260114339 2251799813685248 200000000361 2888000000000000000 Ns264p1382 927292170453511614711 562949953421312000 1840619589006237 361000000000000000000 (Ns264p1388 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz231 1 4 0 1 883795260114339 562949953421312 200000000361 722000000000000000 883795260114339 2251799813685248 200000000361 2888000000000000000 qz361 Ns264p1390 rfl) 

noncomputable def Ns264p1392 := @Ns264p1377 Ns264p1371 Ns264p1372 5085177119054496063 369664000000000000000000 (@Ns264p1379 5085177119054496063 369664000000000000000000 (Ns264p1381 (Ns264p1391 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 580998 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz711 (Real.log Real.pi) 580998 2000 0 1 38410761 33554432 1 33554432 11158287659739 33554432000 290499 33554432000 (Enclosure.Real.IsNear.const Bool.false 580998 2000) RS265to276.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns264p1373 Ns264p1374) 

noncomputable def Ns264p1393 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns264p1371 Ns264p1372 5085177119054496063 369664000000000000000000 8591273549 8388608 231 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz362 qz227 (Enclosure.sfrac Bool.true Ns264p1373 Ns264p1374)) Bool.false Ns264p1371 Ns264p1372 5085177119054496063 369664000000000000000000 Ns264p1375 (Ns264p1392 rfl rfl)) 

noncomputable def Ns264p1394 := nat_lit 1899473156632598793945088 

noncomputable def Ns264p1395 := nat_lit 858036903683809247032692524174247730570450215407015000990258430988064312977670711883451915470093439460846695533317039963402513328111616 

noncomputable def Ns264p1396 := nat_lit 612915024134351594728309461781928103523325173422199597442851680005977701699761749032181580887408360641062637478348120064121634816 

noncomputable def Ns264p1397 := nat_lit 4284847861132669242438046006920750409648411022993098320509745082991881786566009765167241407302140612473109843241655552333214277357797376 

noncomputable def Ns264p1398 := BSN.sin_dyadic_bound_f 53986274128 34359738368 4 3 16777216 7227051 Ns264p1395 Ns264p106 Ns264p1396 Ns264p1397 Ns264p109 Ns264p1396 16777214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53986274128) qz363 0 3 Ns264p1395 Ns264p106 Ns264p1396 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53986274128) qz364 0 3 Ns264p1397 Ns264p109 Ns264p1396 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1399 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz223) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8591273549) qz365) Bool.false 8591273549 8388608 231 16777216 Bool.false 16777214 16777216 1 3610000 (Ns264p1393 rfl) (Enclosure.sfrac_false_div 8591273549 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8591273549) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns264p1394) qz366) 226375608064910080 72057594037927936 Bool.false 16777214 16777216 162 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q3 8591273549 8388608 226375608064910080 72057594037927936 162 Ns264p1394 Ns264p104 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777214 16777216 Ns264p1394 Ns264p104 53986274128 34359738368 7227051 7220000 (Ns264p1398 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p1400 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns264p1371 Ns264p1372 5085177119054496063 369664000000000000000000 137460376784 134217728 1847 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz362 qz227 (Enclosure.sfrac Bool.true Ns264p1373 Ns264p1374)) Bool.false Ns264p1371 Ns264p1372 5085177119054496063 369664000000000000000000 Ns264p1375 (Ns264p1392 rfl rfl)) 

noncomputable def Ns264p1401 := Ns264p1370 32646 BSN.abs_quadSignPos (BSN.cos_quad_nat3 395 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 111318440 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 245 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 114580409 134217728) qz226 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) Bool.false 8388607 8388608 53167951 3785359360000 134217712 134217728 1886 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 8388607 8388608 53167951 3785359360000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz223) qz223) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 16777214 16777216 850687216 60565749760000 8388607 8388608 53167951 3785359360000 (Ns264p1399 rfl rfl) rfl)) rfl) (Ns264p1400 rfl) RS265to276.d7 

noncomputable def Ns264p1402 := nat_lit 291450386848578708285623896196870890095413096100311186258173169516800 

noncomputable def Ns264p1403 := nat_lit 88150318790121319029778358363693727780409707926264222857195438336 

noncomputable def Ns264p1404 := nat_lit 763179722182522134802966753649692065166818397878458202886779984691456 

noncomputable def Ns264p1405 := BSN.sin_dyadic_bound_f 131266222 134217728 3 2 134217728 67108864 Ns264p1402 Ns264p243 Ns264p1403 Ns264p1404 Ns264p246 Ns264p1403 111318440 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 131266222) qz369 0 2 Ns264p1402 Ns264p243 Ns264p1403 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 131266222) qz370 0 2 Ns264p1404 Ns264p246 Ns264p1403 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1406 := nat_lit 348958511241745878167395076941630929695440104797713671897546226130625 

noncomputable def Ns264p1407 := nat_lit 126354405687327590151232596058336856077877416680807574611687890625 

noncomputable def Ns264p1408 := nat_lit 913734384214412102911504158263034175244883711033671642706106907090625 

noncomputable def Ns264p1409 := BSN.sin_dyadic_bound_f 137308935 134217728 3 2 134217728 67108864 Ns264p1406 Ns264p243 Ns264p1407 Ns264p1408 Ns264p246 Ns264p1407 114580409 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 137308935) qz369 0 2 Ns264p1406 Ns264p243 Ns264p1407 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 137308935) qz370 0 2 Ns264p1408 Ns264p246 Ns264p1407 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1410 := nat_lit 7110829121117876865603367787536 

noncomputable def Ns264p1411 := BSN.sin_dyadic_bound_f 51639266 134217728 2 1 134217728 67108864 Ns264p1410 Ns264p136 Ns264p1410 Ns264p1410 Ns264p137 Ns264p1410 50374662 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 51639266) qz369 0 1 Ns264p1410 Ns264p136 Ns264p1410 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 51639266) qz370 0 1 Ns264p1410 Ns264p137 Ns264p1410 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1412 := nat_lit 1054710364284411007257463290398235525581894186612318590250426001295666494878520966621685240699128833314816 

noncomputable def Ns264p1413 := nat_lit 126004947638828510099021770576588944910677554027703400611764159947282216533140032905191339380903936 

noncomputable def Ns264p1414 := nat_lit 6394656589778016091746749650827988593946045469252856874577575367416525715341700942125036799992471292416000 

noncomputable def Ns264p1415 := BSN.cos_dyadic_bound_f 149634694 134217728 4 3 134217728 67108864 Ns264p1412 Ns264p125 Ns264p1413 Ns264p1414 Ns264p128 Ns264p1413 59095848 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 149634694) qz367 0 3 Ns264p1412 Ns264p125 Ns264p1413 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 149634694) qz368 0 3 Ns264p1414 Ns264p128 Ns264p1413 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1416 := Ns264p1368 55328 BSN.abs_quadSignPos (BSN.cos_quad_nat3 139 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 50374662 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 56 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 59095848 134217728) qz226 rfl rfl (Ns264p1401 RS265to276.d9 RS265to276.d11 RS265to276.d13 RS265to276.d17 (Ns264p1405 rfl rfl) (Ns264p1409 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns264p1400 rfl) RS265to276.d19 RS265to276.d21 RS265to276.d23 RS265to276.d25 RS265to276.d17 (Ns264p1411 rfl rfl) (Ns264p1415 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns264p1417 := nat_lit 1157356572465194371577406890885267838820574077283772749727837095787969580806546573445524151861140830759521 

noncomputable def Ns264p1418 := nat_lit 166445900338845089723293066570965913003323490920306152156367967077337858538408567778946275675155041 

noncomputable def Ns264p1419 := nat_lit 7016577634969312390880447663186685544286669318949626215600786907630957030323261414844428056266373605042785 

noncomputable def Ns264p1420 := BSN.cos_dyadic_bound_f 153146153 134217728 4 3 134217728 67108864 Ns264p1417 Ns264p125 Ns264p1418 Ns264p1419 Ns264p128 Ns264p1418 55923216 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 153146153) qz367 0 3 Ns264p1417 Ns264p125 Ns264p1418 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 153146153) qz368 0 3 Ns264p1419 Ns264p128 Ns264p1418 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1421 := nat_lit 590828146427087508151568416572664594520558520267156455090285722009600 

noncomputable def Ns264p1422 := nat_lit 362032301647441376787114932046134846542665461944091968388097703936 

noncomputable def Ns264p1423 := nat_lit 1546820902630180949596452428752713529230869904237500281097167589933056 

noncomputable def Ns264p1424 := BSN.sin_dyadic_bound_f 156618628 134217728 3 2 134217728 67108864 Ns264p1421 Ns264p243 Ns264p1422 Ns264p1423 Ns264p246 Ns264p1422 123418111 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 156618628) qz369 0 2 Ns264p1421 Ns264p243 Ns264p1422 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 156618628) qz370 0 2 Ns264p1423 Ns264p246 Ns264p1422 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1425 := Ns264p1366 74158 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 10 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 55923216 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 67 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 123418111 134217728) qz226 rfl rfl (Ns264p1416 rfl rfl) (Ns264p1400 rfl) RS265to276.d27 RS265to276.d29 RS265to276.d31 RS265to276.d33 RS265to276.d17 (Ns264p1420 rfl rfl) (Ns264p1424 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p1426 := nat_lit 614340391029410037604422200625 

noncomputable def Ns264p1427 := BSN.sin_dyadic_bound_f 27996405 134217728 2 1 134217728 67108864 Ns264p1426 Ns264p136 Ns264p1426 Ns264p1426 Ns264p137 Ns264p1426 27793827 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 27996405) qz369 0 1 Ns264p1426 Ns264p136 Ns264p1426 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 27996405) qz370 0 1 Ns264p1426 Ns264p137 Ns264p1426 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1428 := nat_lit 985074329021321750000341817385804538725056663788068928071402118505823369196633964869870183728021504000000 

noncomputable def Ns264p1429 := nat_lit 102677183071606599381651317735951948145519329317033655201092902371220094124447168987136000000000000 

noncomputable def Ns264p1430 := nat_lit 5972698088616438775081819128627995942960848714503538931069121715170162130348927548821265371090229657600000 

noncomputable def Ns264p1431 := BSN.cos_dyadic_bound_f 147103440 134217728 4 3 134217728 67108864 Ns264p1428 Ns264p125 Ns264p1429 Ns264p1430 Ns264p128 Ns264p1429 61357895 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 147103440) qz367 0 3 Ns264p1428 Ns264p125 Ns264p1429 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 147103440) qz368 0 3 Ns264p1430 Ns264p128 Ns264p1429 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1432 := Ns264p1364 90611 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 117 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 27793827 134217728) BSN.abs_quadSignPos qz659 (BSN.sfrac_eq_quadSignPos_mul Bool.false 61357895 134217728) qz226 rfl rfl (Ns264p1425 rfl) (Ns264p1400 rfl) RS265to276.d35 RS265to276.d37 RS265to276.d39 RS265to276.d41 RS265to276.d17 (Ns264p1427 rfl rfl) (Ns264p1431 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p1433 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) 232837630 134217728 90611 134217728 232837630 134217728 90611 134217728 62501875383009280 116418815 33554432 90611 67108864 (Ns264p1432 rfl) 

noncomputable def Ns264p1434 := @Enclosure.Real.IsNear.mulLit_tf qz708 (Zeta.RiemannSiegel.correction qz225) 2705149 8388608 1 8388608 3576720985923 8796093022208 16577829291587 396923697627136000 9675563198348617527 73786976294838206464 

noncomputable abbrev qz712 := (@HPow.hPow Real Real Real qz7 qz224 qz9)

noncomputable def Ns264p1435 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz712 1 1 0 1 2705149 8388608 1 8388608 2705149 8388608 1 8388608 

noncomputable def Ns264p1436 := @Enclosure.Real.IsNear.sqrt_image qz224 775683748323 8388608000 290499 8388608000 80665385 80665416 8388608 (@Enclosure.Real.IsNear.of_eq qz224 (@HMul.hMul Real Real Real qz5 qz223 qz3) Bool.false 775683748323 8388608000 290499 8388608000 (BSN.t_div_two_pi_mk qz223 580998 1000 qz226) (@Enclosure.Real.IsNear.mulLit_ff qz223 qz3 580998 1000 0 1 2670177 16777216 1 16777216 775683748323 8388608000 290499 8388608000 (Enclosure.Real.IsNear.const Bool.false 580998 1000) RS265to276.d44 rfl)) 

noncomputable abbrev qz789 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 580998 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz713 := qz789

noncomputable abbrev qz529 := qz713

noncomputable abbrev qz232 := qz529

noncomputable def Ns264p1437 := @Enclosure.Real.IsNear.sqrt_image qz232 161330801 16777216 31 16777216 26012887 26012893 8388608 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 161330801 16777216 31 16777216 161330801 16777216 31 16777216 (Ns264p1436 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns264p1438 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz232) 13006445 4194304 3 8388608 2705148 2705150 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz232) Bool.false 52025780 16777216 6 16777216 13006445 4194304 3 8388608 (Ns264p1437 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns264p1439 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 5410298 16777216 2 16777216 2705149 8388608 1 8388608 (Ns264p1438 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz233 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz523))

noncomputable abbrev qz714 := (@HMul.hMul Real Real Real qz735 qz787 qz787)

noncomputable abbrev qz530 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz714 qz707) qz599)

noncomputable abbrev qz234 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz530))

noncomputable def Ns264p1440 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz225) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz233) qz234) Bool.false 3576720985923 

noncomputable def Ns264p1441 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz233) qz234 11249779 8388608 181 

noncomputable abbrev qz715 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz233))

noncomputable def Ns264p1442 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz233) (@Neg.neg Real Real.instNeg qz715) Bool.true 11249779 8388608 181 8388608 (BSN.inv_eq_neg_inv_neg qz233) 

noncomputable def Ns264p1443 := @Enclosure.Real.IsNear.recentre' qz715 Bool.false 22499558 16777216 362 16777216 11249779 8388608 

noncomputable def Ns264p1444 := @Enclosure.Real.IsNear.recentre' qz233 Bool.true 12510245 16777216 181084304 15141437440000 12510245 16777216 11317769 946339840000 

noncomputable abbrev qz235 := (@HMul.hMul Real Real Real qz346 qz343 qz523)

noncomputable def Ns264p1445 := @Enclosure.Real.IsNear.cos_image qz235 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8117763) qz704) Bool.false 8117763 2097152 49 4194304 Bool.true 12510245 16777216 1 

noncomputable def Ns264p1446 := nat_lit 836568337769149744692503321 

noncomputable def Ns264p1447 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz225 884279719003555 140737488355328 1 500000000000000 10335857 16777216 31 16777216 9139788723620926971635 2361183241434822606848 Ns264p1446 

noncomputable def Ns264p1448 := @Enclosure.Real.IsNear.subLit_ff_p qz232 qz1 161330801 16777216 31 16777216 9 1 0 1 10335857 10335857 16777216 31 

noncomputable def Ns264p1449 := @Ns264p1448 16777216 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 161330801 16777216 31 16777216 161330801 16777216 31 16777216 (Ns264p1436 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns264p1450 := @Enclosure.Real.IsNear.recentre' qz235 Bool.false 9139788723620926971635 2361183241434822606848 Ns264p1446 Ns264p439 8117763 2097152 49 4194304 (@Ns264p1447 Ns264p439 RS265to276.d43 (Ns264p1449 rfl rfl) rfl) 

noncomputable def Ns264p1451 := nat_lit 923223613251746299072869691464460245545478247921241492352592853290921803955720309190625 

noncomputable def Ns264p1452 := nat_lit 155399723824578089926904648386117541720550457236788191197838397268569041241000390625 

noncomputable def Ns264p1453 := nat_lit 2769360040307589741038755265096608501552993642849250900675382883078228273784678926790625 

noncomputable def Ns264p1454 := BSN.cos_dyadic_bound_f 25057127355 34359738368 3 2 16777216 7227051 Ns264p1451 Ns264p1109 Ns264p1452 Ns264p1453 Ns264p1112 Ns264p1452 12510245 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 25057127355) qz394 0 2 Ns264p1451 Ns264p1109 Ns264p1452 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 25057127355) qz395 0 2 Ns264p1453 Ns264p1112 Ns264p1452 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1455 := @Ns264p1445 3610000 (Ns264p1450 rfl) (Enclosure.sfrac_false_div 8117763 2097152) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8117763) qz704) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 220404823091139382870016) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 12510245 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 8117763 2097152 226375608064910080 72057594037927936 0 220404823091139382870016 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 12510245 16777216 220404823091139382870016 302231454903657293676544 25057127355 34359738368 7227051 7220000 (Ns264p1454 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p1456 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz233) 12510245 16777216 11317769 946339840000 11249598 11249960 8388608 (@Enclosure.Real.IsNear.neg qz233 Bool.true 12510245 16777216 11317769 946339840000 (Ns264p1444 (Ns264p1455 rfl rfl) rfl)) 

noncomputable def Ns264p1457 := Ns264p1442 (@Enclosure.Real.IsNear.neg qz715 Bool.false 11249779 8388608 181 8388608 (@Ns264p1443 181 8388608 (Ns264p1456 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p1458 := @Enclosure.Real.IsNear.recentre' qz234 Bool.true 2543496 8388608 

noncomputable abbrev qz236 := (@HMul.hMul Real Real Real qz346 qz343 qz530)

noncomputable def Ns264p1459 := @Enclosure.Real.IsNear.cos_image qz236 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15760969)) qz365) Bool.true 15760969 8388608 

noncomputable def Ns264p1460 := nat_lit 74429073685008612757575750845 

noncomputable def Ns264p1461 := nat_lit 6265723010469968435606404092438533 

noncomputable def Ns264p1462 := @Enclosure.Real.IsNear.recentre' qz236 Bool.true Ns264p1460 Ns264p303 Ns264p1461 

noncomputable abbrev qz237 := qz530

noncomputable def Ns264p1463 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz237 884279719003555 140737488355328 1 500000000000000 84169151554079 

noncomputable abbrev qz531 := (@HSub.hSub Real Real Real qz588 qz714 qz707)

noncomputable abbrev qz238 := qz531

noncomputable def Ns264p1464 := @Enclosure.Real.IsNear.subLit_tf qz238 qz31 66576965509663 281474976710656 1160917791 281474976710656 1 16 

noncomputable abbrev qz532 := qz714

noncomputable abbrev qz239 := qz532

noncomputable def Ns264p1465 := @Enclosure.Real.IsNear.subLit_ff_n qz239 qz225 106829939924449 281474976710656 640824095 281474976710656 10335857 16777216 31 16777216 

noncomputable def Ns264p1466 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz225 10335857 16777216 31 16777216 10335857 16777216 31 16777216 106829939924449 281474976710656 

noncomputable def Ns264p1467 := nat_lit 30422119455943504518072496073676445317547140705246068827273528721122675838117008846046415841 

noncomputable def Ns264p1468 := nat_lit 234960565059609855528951401805751428684955363588277954921368551454463463848596077857761 

noncomputable def Ns264p1469 := nat_lit 183653730070985042399595180390940876351870198205807709874938159132338745673531872786145135585 

noncomputable def Ns264p1470 := BSN.cos_dyadic_bound_t 15760969 8388608 4 3 8388608 3610000 Ns264p1467 Ns264p312 Ns264p1468 Ns264p1469 Ns264p315 Ns264p1468 2543496 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 15760969) (BSN.cosEvenQ 8388608) 0 3 Ns264p1467 Ns264p312 Ns264p1468 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 15760969) (BSN.cosOddQ 8388608) 0 3 Ns264p1469 Ns264p315 Ns264p1468 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1471 := @Ns264p1458 397684304 15141437440000 317937 1048576 24855269 946339840000 (@Ns264p1459 109 4194304 Bool.true 2543496 8388608 1 3610000 (@Ns264p1462 Ns264p456 15760969 8388608 109 4194304 (@Ns264p1463 281474976710656 1160917791 281474976710656 Ns264p1460 Ns264p303 Ns264p1461 Ns264p456 RS265to276.d43 (@Ns264p1464 0 1 1346706424865264 84169151554079 281474976710656 1160917791 281474976710656 (@Ns264p1465 1116976130980166238208 66576965509663 281474976710656 1160917791 281474976710656 (@Ns264p1466 640824095 281474976710656 (Ns264p1449 rfl rfl) (Ns264p1449 rfl rfl) rfl) (Ns264p1449 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 15760969 8388608) (BSN.cos_neg_of_bound 15760969 8388608 Bool.true 2543496 8388608 1 3610000 (Ns264p1470 rfl rfl)) rfl rfl) 

noncomputable def Ns264p1472 := @Ns264p1434 1800276577705053937 133185492212182962667520 (Ns264p1435 qz33 (@Enclosure.Real.IsNear.of_eq qz712 (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 2705149 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz224 (BSN.t_div_two_pi_nonneg qz223 580998 1000 qz226)) Ns264p1439) rfl) (@Ns264p1440 8796093022208 16577829291587 396923697627136000 (BSN.correction_mk qz225 (BSN.cos_two_pi_p_ne_zero_mk qz223 580998 1000 9 qz226 rfl rfl (@BSN.floor_sqrt_eq_dec qz223 580998 1000 9 qz226 rfl rfl rfl))) (@Ns264p1441 8388608 317937 1048576 24855269 946339840000 3576720985923 8796093022208 16577829291587 396923697627136000 Ns264p1457 (Ns264p1471 rfl) rfl)) 

noncomputable def Ns264p1473 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (hardyZApproximantRS₀ qz223) Bool.false 265683244767154628407 73786976294838206464 181628542406167154417 133185492212182962667520 (@Eq.refl Real (hardyZApproximantRS₀ qz223)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (@HMul.hMul Real Real Real qz5 qz708 (Zeta.RiemannSiegel.correction qz225))) Bool.false 265683244767154628407 73786976294838206464 181628542406167154417 133185492212182962667520 (BSN.hardyZApproximantRS₀_eq qz223 9 (@BSN.floor_sqrt_eq_dec qz223 580998 1000 9 qz226 rfl rfl rfl)) (@Ns264p1362 265683244767154628407 73786976294838206464 181628542406167154417 133185492212182962667520 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 9)) Bool.false 116418815 33554432 90611 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (Ns264p1433 (Ns264p1432 rfl) rfl rfl)) (Ns264p1472 rfl) rfl rfl)) 

theorem RS265to276.d58 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz223) Bool.false 265683244767154628407 73786976294838206464 181628542406167154417 133185492212182962667520 := Ns264p1473 

noncomputable def Ns264p1474 := nat_lit 32962666426305052977362108416 

noncomputable abbrev qz790 := (Enclosure.sfrac Bool.false 582385 1000)

noncomputable abbrev qz716 := qz790

noncomputable abbrev qz533 := qz716

noncomputable abbrev qz240 := qz533

noncomputable abbrev qz791 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 582385 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz717 := qz791

noncomputable abbrev qz534 := qz717

noncomputable abbrev qz241 := qz534

noncomputable abbrev qz792 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 582385 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz718 := qz792

noncomputable abbrev qz535 := qz718

noncomputable abbrev qz242 := qz535

noncomputable abbrev qz719 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz241 qz9))

noncomputable def Ns264p1475 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (@HMul.hMul Real Real Real qz5 qz719 (Zeta.RiemannSiegel.correction qz242)) 120585961 67108864 45415 33554432 39160659266771150925 295147905179352825856 973257165932343606701 Ns264p695 Ns264p1474 

noncomputable def Ns264p1476 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 582385 1000 116 160 134217728 67108864 2251799813685248 Bool.false 137881848819 1851 

noncomputable def Ns264p1477 := Ns264p1476 279097919 38 47453128 8 294906479 38 44739240 8 Bool.true 146882775 74338 Bool.true 204461898 Bool.true 134666692 7074237752028440 1 Bool.false 6364428 Bool.false Bool.false 72139952 Bool.false Bool.true 120585961 

noncomputable def Ns264p1478 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 582385 1000 10 67 134217728 67108864 2251799813685248 Bool.false 137881848819 1851 

noncomputable def Ns264p1479 := Ns264p1478 240485871 38 54794152 8 261175631 38 50729528 8 Bool.true 132098804 55463 Bool.true 65228022 Bool.true 97397194 7074237752028440 1 Bool.false 118677266 Bool.true Bool.false 89071384 Bool.false Bool.true 146882775 

noncomputable def Ns264p1480 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 582385 1000 140 57 134217728 67108864 2251799813685248 Bool.false 137881848819 1851 

noncomputable def Ns264p1481 := Ns264p1480 186065264 38 67108856 8 216015088 38 60023992 8 Bool.true 172958768 32727 Bool.false 4210065 Bool.false 60665088 7074237752028440 1 Bool.false 134151703 Bool.false Bool.false 58620488 Bool.true Bool.true 132098804 

noncomputable def Ns264p1482 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 582385 1000 397 246 134217728 67108864 2251799813685248 Bool.false 137881848819 1851 

noncomputable def Ns264p1483 := Ns264p1482 93032624 38 94906264 8 147453232 38 77490640 16 Bool.true 134217664 1894 Bool.false 2044579 Bool.false 143434623 7074237752028440 1 Bool.false 2044499 Bool.true Bool.false 64597571 Bool.true Bool.true 172958768 

noncomputable def Ns264p1484 := nat_lit 5198900694646549423709969895377168101340296701367583 

noncomputable def Ns264p1485 := nat_lit 5060743276284416580260991138798330270045752524800 

noncomputable def Ns264p1486 := nat_lit 32158290331431324396823235500000000 

noncomputable def Ns264p1487 := nat_lit 112371074140958184367744346650005000000 

noncomputable abbrev qz793 := (@Eq.refl Real (Enclosure.sfrac Bool.false 582385 1000))

noncomputable abbrev qz720 := qz793

noncomputable abbrev qz536 := qz720

noncomputable abbrev qz243 := qz536

noncomputable def Ns264p1488 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz240 582385 1000 1356690152900 16000000 1164770 4000 2000 Ns264p1486 Ns264p1487 qz243 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns264p1489 := nat_lit 25994503473232747118549849476885840506701483506837915000000 

noncomputable abbrev qz721 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1164770))))

noncomputable abbrev qz537 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 582385 4000) (Real.log (Enclosure.sfrac Bool.false 1356690152900 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz721))

noncomputable abbrev qz722 := (Enclosure.sfrac Bool.false 582385 2000)

noncomputable abbrev qz244 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz537 qz722) (@HMul.hMul Real Real Real qz346 qz722 (Real.log Real.pi)))

noncomputable def Ns264p1490 := @Enclosure.Real.IsNear.addLit_ft_p qz244 (Enclosure.sfrac Bool.true Ns264p1486 Ns264p1487) 231327420453670057583 225179981368524800 2038902281440203649 147865600000000000000000 Ns264p1486 Ns264p1487 0 1 Ns264p1489 

noncomputable def Ns264p1491 := nat_lit 620964815947846487808388628480 

noncomputable abbrev qz245 := (@HSub.hSub Real Real Real qz350 qz537 qz722)

noncomputable def Ns264p1492 := @Enclosure.Real.IsNear.subLit_ff_p qz245 (@HMul.hMul Real Real Real qz5 qz722 (Real.log Real.pi)) 61277637005515573987 45035996273704960 368990793201813 72200000000000000000 4473970208997 13421772800 116477 13421772800 Ns264p1491 231327420453670057583 225179981368524800 

noncomputable abbrev qz246 := qz537

noncomputable def Ns264p1493 := @Enclosure.Real.IsNear.subLit_ff_p qz246 qz722 371958906752232027759 225179981368524800 368990793201813 72200000000000000000 582385 2000 0 1 612776370055155739870000 61277637005515573987 45035996273704960 368990793201813 72200000000000000000 

noncomputable def Ns264p1494 := nat_lit 837576996923244614374480501624799232 

noncomputable def Ns264p1495 := nat_lit 27437707489880747293016064 

noncomputable def Ns264p1496 := nat_lit 1058612280314728643891296789872470552074434760514605017021218112796528672195542057081450000000000000000 

noncomputable def Ns264p1497 := nat_lit 5848143033461165718638880780337522737603453891103527547718910567910722659260883949840000000000000000 

noncomputable def Ns264p1498 := nat_lit 8528692968384720922449750360606236870831320556714040091135047212786115361009050000000000000000 

noncomputable def Ns264p1499 := BSN.log_dyadic_bound 308114152900 2405266152900 5 4 Ns264p1496 67108864 28880000 Ns264p1497 Ns264p1498 17288247 2713380305800 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 308114152900) (BSN.artanhQ 2405266152900) 0 4 Ns264p1497 Ns264p1496 Ns264p1498 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz538 := (Real.log (Enclosure.sfrac Bool.false 1356690152900 16000000))

noncomputable def Ns264p1500 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 582385 4000) qz538 582385 4000 0 1 3194169547627767 281474976710656 781250361 22562500000000000 372047286399039416859 225179981368524800 90997698298197 18050000000000000000 (Enclosure.Real.IsNear.const Bool.false 582385 4000) (BSN.isNear_log_sfrac 1356690152900 16000000 3194169547627767 281474976710656 781250361 22562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1356690152900) qz353)) Bool.false Ns264p1495 Ns264p92 1000000462080000 28880000000000000000000 3194169547627767 281474976710656 781250361 22562500000000000 (BSN.log_rat_reduce_isNear 1356690152900 16000000 16 2713380305800 2097152000000 17288247 67108864 24973259072661432 36028797018963968 28880000 1000000000000000 rfl rfl rfl rfl (Ns264p1499 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p1501 := BSN.arctan_dyadic_bound_f 1000 1164770 1 0 8388608 3610000 0 1 1 0 1 1 7201 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1164770) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1164770) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns264p1502 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1164770))) 884279719003555 562949953421312 1 2000000000000000 7201 8388608 1 3610000 7413822122456386633728 883796468073891 562949953421312 200000000361 722000000000000000 qz17 (Ns264p1501 rfl) rfl rfl 

noncomputable abbrev qz539 := (@HMul.hMul Real Real Real qz584 qz589 qz721)

noncomputable abbrev qz247 := qz539

noncomputable abbrev qz540 := qz721

noncomputable abbrev qz248 := qz540

noncomputable def Ns264p1503 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 582385 4000) qz538) qz247 372047286399039416859 225179981368524800 90997698298197 18050000000000000000 883796468073891 2251799813685248 200000000361 2888000000000000000 Ns264p1494 371958906752232027759 225179981368524800 368990793201813 72200000000000000000 (Ns264p1500 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz248 1 4 0 1 883796468073891 562949953421312 200000000361 722000000000000000 883796468073891 2251799813685248 200000000361 2888000000000000000 qz361 Ns264p1502 rfl) 

noncomputable def Ns264p1504 := @Ns264p1490 Ns264p1484 Ns264p1485 2038902281440203649 147865600000000000000000 (@Ns264p1492 2038902281440203649 147865600000000000000000 (Ns264p1493 (Ns264p1503 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 582385 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz722 (Real.log Real.pi) 582385 2000 0 1 38410761 33554432 1 33554432 4473970208997 13421772800 116477 13421772800 (Enclosure.Real.IsNear.const Bool.false 582385 2000) RS265to276.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns264p1486 Ns264p1487) 

noncomputable def Ns264p1505 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns264p1484 Ns264p1485 2038902281440203649 147865600000000000000000 8617615551 8388608 29 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz362 qz244 (Enclosure.sfrac Bool.true Ns264p1486 Ns264p1487)) Bool.false Ns264p1484 Ns264p1485 2038902281440203649 147865600000000000000000 Ns264p1488 (Ns264p1504 rfl rfl)) 

noncomputable def Ns264p1506 := nat_lit 1897803255520831893143552 

noncomputable def Ns264p1507 := nat_lit 855017501426565709941598481885047178924205370223833912687956641655418443545715280620648257943194757037153306822294116068642007973625856 

noncomputable def Ns264p1508 := nat_lit 606480147071681496129518932072769532258936134534940627213786848432206939957923761325490397317175836343770826277982870445286752256 

noncomputable def Ns264p1509 := nat_lit 4269788276421767767619292625846363294580591786259014013099694780693341232973211316109345228437016461662038525829664777375801421296828416 

noncomputable def Ns264p1510 := BSN.sin_dyadic_bound_f 53938812684 34359738368 4 3 16777216 7227051 Ns264p1507 Ns264p106 Ns264p1508 Ns264p1509 Ns264p109 Ns264p1508 16777208 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53938812684) qz363 0 3 Ns264p1507 Ns264p106 Ns264p1508 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53938812684) qz364 0 3 Ns264p1509 Ns264p109 Ns264p1508 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1511 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz240) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8617615551) qz365) Bool.false 8617615551 8388608 29 2097152 Bool.true 16777208 16777216 1 3610000 (Ns264p1505 rfl) (Enclosure.sfrac_false_div 8617615551 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8617615551) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns264p1506) qz366) 226375608064910080 72057594037927936 Bool.false 16777208 16777216 163 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q1 8617615551 8388608 226375608064910080 72057594037927936 163 Ns264p1506 Ns264p104 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777208 16777216 Ns264p1506 Ns264p104 53938812684 34359738368 7227051 7220000 (Ns264p1510 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p1512 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns264p1484 Ns264p1485 2038902281440203649 147865600000000000000000 137881848819 134217728 1851 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz362 qz244 (Enclosure.sfrac Bool.true Ns264p1486 Ns264p1487)) Bool.false Ns264p1484 Ns264p1485 2038902281440203649 147865600000000000000000 Ns264p1488 (Ns264p1504 rfl rfl)) 

noncomputable def Ns264p1513 := Ns264p1483 32727 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 397 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 2044499 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 246 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 64597571 134217728) qz243 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) Bool.true 2097151 2097152 6674197 473169920000 134217664 134217728 1894 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 2097151 2097152 6674197 473169920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz240) qz240) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 16777208 16777216 106787152 7570718720000 2097151 2097152 6674197 473169920000 (Ns264p1511 rfl rfl) rfl)) rfl) (Ns264p1512 rfl) RS265to276.d7 

noncomputable def Ns264p1514 := BSN.sin_dyadic_bound_f 2044579 134217728 1 0 134217728 67108864 0 1 1 0 1 1 2044499 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 2044579) qz369 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 2044579) qz370 0 0 rfl) rfl rfl 

noncomputable def Ns264p1515 := nat_lit 890344025922067462356122373587540624193941090397190018568317663354627611691035225742516235590846844556801 

noncomputable def Ns264p1516 := nat_lit 75831204635734708216032526878041621453501509016121558846826631326652632488902776689122106787550721 

noncomputable def Ns264p1517 := nat_lit 5398626551673601198444430331108445208933791534764194074507264944341667008404432677408748783907951749420545 

noncomputable def Ns264p1518 := BSN.cos_dyadic_bound_f 143434623 134217728 4 3 134217728 67108864 Ns264p1515 Ns264p125 Ns264p1516 Ns264p1517 Ns264p128 Ns264p1516 64597571 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 143434623) qz367 0 3 Ns264p1515 Ns264p125 Ns264p1516 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 143434623) qz368 0 3 Ns264p1517 Ns264p128 Ns264p1516 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1519 := nat_lit 314163122059170559702850625 

noncomputable def Ns264p1520 := BSN.cos_dyadic_bound_f 4210065 134217728 2 1 134217728 67108864 Ns264p1519 Ns264p522 Ns264p1519 Ns264p1519 Ns264p523 Ns264p1519 134151703 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 4210065) qz367 0 1 Ns264p1519 Ns264p522 Ns264p1519 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 4210065) qz368 0 1 Ns264p1519 Ns264p523 Ns264p1519 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1521 := nat_lit 13544261423030841593108455489536 

noncomputable def Ns264p1522 := BSN.sin_dyadic_bound_f 60665088 134217728 2 1 134217728 67108864 Ns264p1521 Ns264p136 Ns264p1521 Ns264p1521 Ns264p137 Ns264p1521 58620488 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 60665088) qz369 0 1 Ns264p1521 Ns264p136 Ns264p1521 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 60665088) qz370 0 1 Ns264p1521 Ns264p137 Ns264p1521 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1523 := Ns264p1481 55463 BSN.abs_quadSignPos (BSN.cos_quad_nat0 140 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 134151703 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58620488 134217728) qz243 rfl rfl (Ns264p1513 RS265to276.d9 RS265to276.d11 RS265to276.d13 RS265to276.d17 (Ns264p1514 rfl rfl) (Ns264p1518 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns264p1512 rfl) RS265to276.d19 RS265to276.d21 RS265to276.d23 RS265to276.d25 RS265to276.d17 (Ns264p1520 rfl rfl) (Ns264p1522 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns264p1524 := nat_lit 9869611765781596714775557448312211851748869178034985516217144566016 

noncomputable def Ns264p1525 := nat_lit 327697910390329521060956029574540767371493854683947556431585536 

noncomputable def Ns264p1526 := nat_lit 29608179901524009485284550432877486473711864546395588653538570526976 

noncomputable def Ns264p1527 := BSN.cos_dyadic_bound_f 65228022 134217728 3 2 134217728 67108864 Ns264p1524 Ns264p115 Ns264p1525 Ns264p1526 Ns264p118 Ns264p1525 118677266 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 65228022) qz367 0 2 Ns264p1524 Ns264p115 Ns264p1525 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 65228022) qz368 0 2 Ns264p1526 Ns264p118 Ns264p1525 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1528 := nat_lit 88317531407126162422725921935999874963979043416941784082480984285440 

noncomputable def Ns264p1529 := nat_lit 8097884175685742262267086274816338440783651358794171394258166016 

noncomputable def Ns264p1530 := nat_lit 231294709491903124667286125026030922262469559227885672509954731335936 

noncomputable def Ns264p1531 := BSN.sin_dyadic_bound_f 97397194 134217728 3 2 134217728 67108864 Ns264p1528 Ns264p243 Ns264p1529 Ns264p1530 Ns264p246 Ns264p1529 89071384 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 97397194) qz369 0 2 Ns264p1528 Ns264p243 Ns264p1529 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 97397194) qz370 0 2 Ns264p1530 Ns264p246 Ns264p1529 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1532 := Ns264p1479 74338 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 10 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 118677266 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 67 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 89071384 134217728) qz243 rfl rfl (Ns264p1523 rfl rfl) (Ns264p1512 rfl) RS265to276.d27 RS265to276.d29 RS265to276.d31 RS265to276.d33 RS265to276.d17 (Ns264p1527 rfl rfl) (Ns264p1531 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p1533 := nat_lit 3685062746746496897420448877897062686055566003448983823146100918389411430129625455374355397258888544587776 

noncomputable def Ns264p1534 := nat_lit 5337632339121623924732025667463878737620374144403639772857726447638342620931797011186154889394589696 

noncomputable def Ns264p1535 := nat_lit 22308397593263420118626547935175787713764862677000239792287196487231975678493757182956324631392086635909120 

noncomputable def Ns264p1536 := BSN.cos_dyadic_bound_f 204461898 134217728 4 3 134217728 67108864 Ns264p1533 Ns264p125 Ns264p1534 Ns264p1535 Ns264p128 Ns264p1534 6364428 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 204461898) qz367 0 3 Ns264p1533 Ns264p125 Ns264p1534 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 204461898) qz368 0 3 Ns264p1535 Ns264p128 Ns264p1534 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1537 := nat_lit 179412000072565601673505055391105975775227270800513438107877674909696 

noncomputable def Ns264p1538 := nat_lit 108163700442882302725089540644434566630965216691557104346443350016 

noncomputable def Ns264p1539 := nat_lit 538019672816811040415064987092029058192419881968157200114940138029056 

noncomputable def Ns264p1540 := BSN.cos_dyadic_bound_f 134666692 134217728 3 2 134217728 67108864 Ns264p1537 Ns264p115 Ns264p1538 Ns264p1539 Ns264p118 Ns264p1538 72139952 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 134666692) qz367 0 2 Ns264p1537 Ns264p115 Ns264p1538 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 134666692) qz368 0 2 Ns264p1539 Ns264p118 Ns264p1538 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1541 := Ns264p1477 90830 BSN.abs_quadSignPos (BSN.cos_quad_nat0 116 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 6364428 134217728) BSN.abs_quadSignPos qz659 (BSN.sfrac_eq_quadSignPos_mul Bool.false 72139952 134217728) qz243 rfl rfl (Ns264p1532 rfl) (Ns264p1512 rfl) RS265to276.d35 RS265to276.d37 RS265to276.d39 RS265to276.d41 RS265to276.d17 (Ns264p1536 rfl rfl) (Ns264p1540 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns264p1542 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) 120585961 134217728 90830 134217728 120585961 134217728 90830 134217728 32369547428233216 120585961 67108864 45415 33554432 (Ns264p1541 rfl) 

noncomputable def Ns264p1543 := @Enclosure.Real.IsNear.mulLit_tf qz719 (Zeta.RiemannSiegel.correction qz242) 2703537 8388608 1 8388608 14484972562525 35184372088832 89696260418563 1984618488135680000 39160659266771150925 295147905179352825856 

noncomputable abbrev qz723 := (@HPow.hPow Real Real Real qz7 qz241 qz9)

noncomputable def Ns264p1544 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz723 1 1 0 1 2703537 8388608 1 8388608 2703537 8388608 1 8388608 

noncomputable def Ns264p1545 := @Enclosure.Real.IsNear.sqrt_image qz241 311014206429 3355443200 116477 3355443200 80761613 80761644 8388608 (@Enclosure.Real.IsNear.of_eq qz241 (@HMul.hMul Real Real Real qz5 qz240 qz3) Bool.false 311014206429 3355443200 116477 3355443200 (BSN.t_div_two_pi_mk qz240 582385 1000 qz243) (@Enclosure.Real.IsNear.mulLit_ff qz240 qz3 582385 1000 0 1 2670177 16777216 1 16777216 311014206429 3355443200 116477 3355443200 (Enclosure.Real.IsNear.const Bool.false 582385 1000) RS265to276.d44 rfl)) 

noncomputable abbrev qz794 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 582385 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz724 := qz794

noncomputable abbrev qz541 := qz724

noncomputable abbrev qz249 := qz541

noncomputable def Ns264p1546 := @Enclosure.Real.IsNear.sqrt_image qz249 161523257 16777216 31 16777216 26028398 26028404 8388608 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 161523257 16777216 31 16777216 161523257 16777216 31 16777216 (Ns264p1545 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns264p1547 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz249) 26028401 8388608 3 8388608 2703536 2703538 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz249) Bool.false 52056802 16777216 6 16777216 26028401 8388608 3 8388608 (Ns264p1546 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns264p1548 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 5407074 16777216 2 16777216 2703537 8388608 1 8388608 (Ns264p1547 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz535))

noncomputable abbrev qz725 := (@HMul.hMul Real Real Real qz735 qz792 qz792)

noncomputable abbrev qz542 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz725 qz718) qz599)

noncomputable abbrev qz251 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz542))

noncomputable def Ns264p1549 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz242) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz250) qz251) Bool.false 14484972562525 

noncomputable def Ns264p1550 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz250) qz251 6028475 4194304 13 

noncomputable abbrev qz726 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz250))

noncomputable def Ns264p1551 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz250) (@Neg.neg Real Real.instNeg qz726) Bool.true 6028475 4194304 13 524288 (BSN.inv_eq_neg_inv_neg qz250) 

noncomputable def Ns264p1552 := @Enclosure.Real.IsNear.recentre' qz726 Bool.false 24113900 16777216 416 16777216 6028475 4194304 

noncomputable def Ns264p1553 := @Enclosure.Real.IsNear.recentre' qz250 Bool.true 11672727 16777216 181084304 15141437440000 11672727 16777216 11317769 946339840000 

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz346 qz343 qz535)

noncomputable def Ns264p1554 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 66151341) qz375) Bool.false 66151341 16777216 49 4194304 Bool.true 11672727 16777216 1 

noncomputable def Ns264p1555 := nat_lit 836568337770802929144341273 

noncomputable def Ns264p1556 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz242 884279719003555 140737488355328 1 500000000000000 10528313 16777216 31 16777216 9309973661221475152715 2361183241434822606848 Ns264p1555 

noncomputable def Ns264p1557 := @Enclosure.Real.IsNear.subLit_ff_p qz249 qz1 161523257 16777216 31 16777216 9 1 0 1 10528313 10528313 16777216 31 

noncomputable def Ns264p1558 := @Ns264p1557 16777216 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 161523257 16777216 31 16777216 161523257 16777216 31 16777216 (Ns264p1545 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns264p1559 := @Enclosure.Real.IsNear.recentre' qz252 Bool.false 9309973661221475152715 2361183241434822606848 Ns264p1555 Ns264p439 66151341 16777216 49 4194304 (@Ns264p1556 Ns264p439 RS265to276.d43 (Ns264p1558 rfl rfl) rfl) 

noncomputable def Ns264p1560 := nat_lit 1937508002412398790049792 

noncomputable def Ns264p1561 := nat_lit 1346077523430083200331437302090377800798764315173762603808843295582809171528239681892321 

noncomputable def Ns264p1562 := nat_lit 330300807173824339238986610174183095219505041296253225575855411878747604120082051041 

noncomputable def Ns264p1563 := nat_lit 4037571968675901952315833933050785036205853935438695304975378175924670019376478881574881 

noncomputable def Ns264p1564 := BSN.cos_dyadic_bound_f 27533644731 34359738368 3 2 16777216 7227051 Ns264p1561 Ns264p1109 Ns264p1562 Ns264p1563 Ns264p1112 Ns264p1562 11672727 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 27533644731) qz394 0 2 Ns264p1561 Ns264p1109 Ns264p1562 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 27533644731) qz395 0 2 Ns264p1563 Ns264p1112 Ns264p1562 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1565 := @Ns264p1554 3610000 (Ns264p1559 rfl) (Enclosure.sfrac_false_div 66151341 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 66151341) qz375) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns264p1560) qz377) 226375608064910080 72057594037927936 Bool.false 11672727 16777216 0 1000000000000000 7220000 3610000 (BSN.sin_reduce_arg_pos_rat_q2 66151341 16777216 226375608064910080 72057594037927936 0 Ns264p1560 Ns264p92 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 11672727 16777216 Ns264p1560 Ns264p92 27533644731 34359738368 7227051 7220000 (Ns264p1564 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns264p1566 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz250) 11672727 16777216 11317769 946339840000 12056742 12057158 8388608 (@Enclosure.Real.IsNear.neg qz250 Bool.true 11672727 16777216 11317769 946339840000 (Ns264p1553 (Ns264p1565 rfl rfl) rfl)) 

noncomputable def Ns264p1567 := Ns264p1551 (@Enclosure.Real.IsNear.neg qz726 Bool.false 6028475 4194304 13 524288 (@Ns264p1552 13 524288 (Ns264p1566 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns264p1568 := @Enclosure.Real.IsNear.recentre' qz251 Bool.true 2402759 8388608 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz346 qz343 qz542)

noncomputable def Ns264p1569 := @Enclosure.Real.IsNear.cos_image qz253 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 31227367)) qz375) Bool.true 31227367 16777216 

noncomputable def Ns264p1570 := nat_lit 73733535673542301966718120525 

noncomputable def Ns264p1571 := nat_lit 31650620244336310499575283457117481 

noncomputable def Ns264p1572 := @Enclosure.Real.IsNear.recentre' qz253 Bool.true Ns264p1570 Ns264p303 Ns264p1571 

noncomputable abbrev qz254 := qz542

noncomputable def Ns264p1573 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz254 884279719003555 140737488355328 1 500000000000000 83382592735055 

noncomputable abbrev qz543 := (@HSub.hSub Real Real Real qz588 qz725 qz718)

noncomputable abbrev qz255 := qz543

noncomputable def Ns264p1574 := @Enclosure.Real.IsNear.subLit_tf qz255 qz31 65790406690639 281474976710656 1172850063 281474976710656 1 16 

noncomputable abbrev qz544 := qz725

noncomputable abbrev qz256 := qz544

noncomputable def Ns264p1575 := @Enclosure.Real.IsNear.subLit_ff_n qz256 qz242 110845374625969 281474976710656 652756367 281474976710656 10528313 16777216 31 16777216 

noncomputable def Ns264p1576 := @Enclosure.Real.IsNear.mulLit_ff qz242 qz242 10528313 16777216 31 16777216 10528313 16777216 31 16777216 110845374625969 281474976710656 

noncomputable def Ns264p1577 := nat_lit 119983387847153564487548708694346731814784744259392999886343056187010888697122902208858540852641 

noncomputable def Ns264p1578 := nat_lit 859853390435699407649224649653757525773509085028282150906435604489358772097468431552595361 

noncomputable def Ns264p1579 := nat_lit 724452649247928250268883478078663796632936549460321481537643643284352595154641858794804835632545 

noncomputable def Ns264p1580 := BSN.cos_dyadic_bound_t 31227367 16777216 4 3 8388608 3610000 Ns264p1577 Ns264p192 Ns264p1578 Ns264p1579 Ns264p195 Ns264p1578 2402759 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 31227367) (BSN.cosEvenQ 16777216) 0 3 Ns264p1577 Ns264p192 Ns264p1578 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 31227367) (BSN.cosOddQ 16777216) 0 3 Ns264p1579 Ns264p195 Ns264p1578 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns264p1581 := @Ns264p1568 200647152 7570718720000 2402759 8388608 12540447 473169920000 (@Ns264p1569 55 2097152 Bool.true 2402759 8388608 1 3610000 (@Ns264p1572 Ns264p306 31227367 16777216 55 2097152 (@Ns264p1573 281474976710656 1172850063 281474976710656 Ns264p1570 Ns264p303 Ns264p1571 Ns264p306 RS265to276.d43 (@Ns264p1574 0 1 1334121483760880 83382592735055 281474976710656 1172850063 281474976710656 (@Ns264p1575 1103779863776695681024 65790406690639 281474976710656 1172850063 281474976710656 (@Ns264p1576 652756367 281474976710656 (Ns264p1558 rfl rfl) (Ns264p1558 rfl rfl) rfl) (Ns264p1558 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 31227367 16777216) (BSN.cos_neg_of_bound 31227367 16777216 Bool.true 2402759 8388608 1 3610000 (Ns264p1580 rfl rfl)) rfl rfl) 

noncomputable def Ns264p1582 := @Ns264p1543 973257165932343606701 Ns264p695 (Ns264p1544 qz33 (@Enclosure.Real.IsNear.of_eq qz723 (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 2703537 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz241 (BSN.t_div_two_pi_nonneg qz240 582385 1000 qz243)) Ns264p1548) rfl) (@Ns264p1549 35184372088832 89696260418563 1984618488135680000 (BSN.correction_mk qz242 (BSN.cos_two_pi_p_ne_zero_mk qz240 582385 1000 9 qz243 rfl rfl (@BSN.floor_sqrt_eq_dec qz240 582385 1000 9 qz243 rfl rfl rfl))) (@Ns264p1550 524288 2402759 8388608 12540447 473169920000 14484972562525 35184372088832 89696260418563 1984618488135680000 Ns264p1567 (Ns264p1581 rfl) rfl)) 

noncomputable def Ns264p1583 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (hardyZApproximantRS₀ qz240) Bool.true 491182005797401860019 295147905179352825856 91104705804614250806701 Ns264p695 (@Eq.refl Real (hardyZApproximantRS₀ qz240)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (@HMul.hMul Real Real Real qz5 qz719 (Zeta.RiemannSiegel.correction qz242))) Bool.true 491182005797401860019 295147905179352825856 91104705804614250806701 Ns264p695 (BSN.hardyZApproximantRS₀_eq qz240 9 (@BSN.floor_sqrt_eq_dec qz240 582385 1000 9 qz243 rfl rfl rfl)) (@Ns264p1475 491182005797401860019 295147905179352825856 91104705804614250806701 Ns264p695 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 9)) Bool.true 120585961 67108864 45415 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (Ns264p1542 (Ns264p1541 rfl) rfl rfl)) (Ns264p1582 rfl) rfl rfl)) 

theorem RS265to276.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz240) Bool.true 491182005797401860019 295147905179352825856 91104705804614250806701 Ns264p695 := Ns264p1583 

noncomputable def RS265to276.d60 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz545 := (RS265to276.d3 qz583 qz600 (@Enclosure.dec_le_dec qz583 qz600 565685 1000 567081 1000 (@Eq.refl Real qz583) qz604 rfl rfl rfl))

noncomputable abbrev qz257 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz545)

noncomputable def Ns264p1584 := @Enclosure.Real.IsNear.of_eq qz257 (hardyZApproximantRS₀ qz4) Bool.true 232265292887391840039 73786976294838206464 22037267212783582125049 Ns264p69 

noncomputable abbrev qz546 := (@Enclosure.dec_le_dec qz583 qz600 565685 1000 567081 1000 (@Eq.refl Real qz583) qz604 rfl rfl rfl)

noncomputable abbrev qz258 := qz546

noncomputable def Ns264p1585 := @Enclosure.Real.IsNear.neg_val qz257 232265292887391840039 73786976294838206464 22037267212783582125049 Ns264p69 (Ns264p1584 (RS265to276.d4 qz4 qz35 qz258) RS265to276.d45) rfl 

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz545)

noncomputable def Ns264p1586 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantRS₀ qz35) Bool.false 523286691125744021595 590295810358705651712 35355904790123406340839 Ns264p200 

noncomputable def Ns264p1587 := @Enclosure.Real.IsNear.pos_val qz259 523286691125744021595 590295810358705651712 35355904790123406340839 Ns264p200 (Ns264p1586 (RS265to276.d46 qz4 qz35 qz258) RS265to276.d47) rfl 

noncomputable def Ns264p1588 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz257 qz4 qz4 565685 1000 565685 1000 

noncomputable def Ns264p1589 := @Enclosure.norm_gt_of_isNear qz257 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 232265292887391840039 73786976294838206464 22037267212783582125049 

noncomputable def Ns264p1590 := @Ns264p1589 Ns264p69 35978025 536870912 1213 2684354560 (Ns264p1584 (RS265to276.d4 qz4 qz35 qz258) RS265to276.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable def Ns264p1591 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz259 qz4 qz35 565685 1000 567081 1000 

noncomputable def Ns264p1592 := @Enclosure.norm_gt_of_isNear qz259 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 523286691125744021595 590295810358705651712 35355904790123406340839 

noncomputable def Ns264p1593 := @Ns264p1592 Ns264p200 35978025 536870912 1213 2684354560 (Ns264p1586 (RS265to276.d46 qz4 qz35 qz258) RS265to276.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable abbrev qz260 := qz545

noncomputable def Ns264p1594 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz260 (@BSN.thirtyTwoPi_le_dec qz4 565685 1000 qz11 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz257 qz259 (Ns264p1585 rfl rfl) (Ns264p1587 rfl rfl)) (Ns264p1588 qz11 qz11 rfl rfl rfl rfl (Ns264p1590 rfl)) (Ns264p1591 qz11 qz38 rfl rfl rfl rfl (Ns264p1593 rfl)) 

noncomputable abbrev qz547 := (RS265to276.d3 qz600 qz612 (@Enclosure.dec_le_dec qz600 qz612 567081 1000 568476 1000 qz604 qz616 rfl rfl rfl))

noncomputable abbrev qz261 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz547)

noncomputable def Ns264p1595 := @Enclosure.Real.IsNear.of_eq qz261 (hardyZApproximantRS₀ qz35) Bool.false 523286691125744021595 590295810358705651712 35355904790123406340839 Ns264p200 

noncomputable abbrev qz548 := (@Enclosure.dec_le_dec qz600 qz612 567081 1000 568476 1000 qz604 qz616 rfl rfl rfl)

noncomputable abbrev qz262 := qz548

noncomputable def Ns264p1596 := @Enclosure.Real.IsNear.pos_val qz261 523286691125744021595 590295810358705651712 35355904790123406340839 Ns264p200 (Ns264p1595 (RS265to276.d4 qz35 qz62 qz262) RS265to276.d47) rfl 

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz547)

noncomputable def Ns264p1597 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantRS₀ qz62) Bool.true 2447545700209119420253 2361183241434822606848 5671001323656823541197 Ns264p353 

noncomputable def Ns264p1598 := @Enclosure.Real.IsNear.neg_val qz263 2447545700209119420253 2361183241434822606848 5671001323656823541197 Ns264p353 (Ns264p1597 (RS265to276.d46 qz35 qz62 qz262) RS265to276.d49) rfl 

noncomputable def Ns264p1599 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz261 qz4 qz35 565685 1000 567081 1000 

noncomputable def Ns264p1600 := @Enclosure.norm_gt_of_isNear qz261 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 523286691125744021595 590295810358705651712 35355904790123406340839 

noncomputable def Ns264p1601 := @Ns264p1600 Ns264p200 35978025 536870912 1213 2684354560 (Ns264p1595 (RS265to276.d4 qz35 qz62 qz262) RS265to276.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable def Ns264p1602 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz263 qz4 qz62 565685 1000 568476 1000 

noncomputable def Ns264p1603 := @Enclosure.norm_gt_of_isNear qz263 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2447545700209119420253 2361183241434822606848 5671001323656823541197 

noncomputable def Ns264p1604 := @Ns264p1603 Ns264p353 35978025 536870912 1213 2684354560 (Ns264p1597 (RS265to276.d46 qz35 qz62 qz262) RS265to276.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable abbrev qz264 := qz547

noncomputable def Ns264p1605 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz264 (@BSN.thirtyTwoPi_le_dec qz35 567081 1000 qz38 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz261 qz263 (Ns264p1596 rfl rfl) (Ns264p1598 rfl rfl)) (Ns264p1599 qz11 qz38 rfl rfl rfl rfl (Ns264p1601 rfl)) (Ns264p1602 qz11 qz65 rfl rfl rfl rfl (Ns264p1604 rfl)) 

noncomputable abbrev qz549 := (RS265to276.d3 qz612 qz622 (@Enclosure.dec_le_dec qz612 qz622 568476 1000 569870 1000 qz616 qz626 rfl rfl rfl))

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz549)

noncomputable def Ns264p1606 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantRS₀ qz62) Bool.true 2447545700209119420253 2361183241434822606848 5671001323656823541197 Ns264p353 

noncomputable abbrev qz550 := (@Enclosure.dec_le_dec qz612 qz622 568476 1000 569870 1000 qz616 qz626 rfl rfl rfl)

noncomputable abbrev qz266 := qz550

noncomputable def Ns264p1607 := @Enclosure.Real.IsNear.neg_val qz265 2447545700209119420253 2361183241434822606848 5671001323656823541197 Ns264p353 (Ns264p1606 (RS265to276.d4 qz62 qz80 qz266) RS265to276.d49) rfl 

noncomputable abbrev qz267 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz549)

noncomputable def Ns264p1608 := @Enclosure.Real.IsNear.of_eq qz267 (hardyZApproximantRS₀ qz80) Bool.false 1997312197929358295777 2361183241434822606848 142129876580083230905211 Ns264p470 

noncomputable def Ns264p1609 := @Enclosure.Real.IsNear.pos_val qz267 1997312197929358295777 2361183241434822606848 142129876580083230905211 Ns264p470 (Ns264p1608 (RS265to276.d46 qz62 qz80 qz266) RS265to276.d50) rfl 

noncomputable def Ns264p1610 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz265 qz4 qz62 565685 1000 568476 1000 

noncomputable def Ns264p1611 := @Enclosure.norm_gt_of_isNear qz265 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2447545700209119420253 2361183241434822606848 5671001323656823541197 

noncomputable def Ns264p1612 := @Ns264p1611 Ns264p353 35978025 536870912 1213 2684354560 (Ns264p1606 (RS265to276.d4 qz62 qz80 qz266) RS265to276.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable def Ns264p1613 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz267 qz4 qz80 565685 1000 569870 1000 

noncomputable def Ns264p1614 := @Enclosure.norm_gt_of_isNear qz267 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1997312197929358295777 2361183241434822606848 142129876580083230905211 

noncomputable def Ns264p1615 := @Ns264p1614 Ns264p470 35978025 536870912 1213 2684354560 (Ns264p1608 (RS265to276.d46 qz62 qz80 qz266) RS265to276.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable abbrev qz268 := qz549

noncomputable def Ns264p1616 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz62 568476 1000 qz65 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz265 qz267 (Ns264p1607 rfl rfl) (Ns264p1609 rfl rfl)) (Ns264p1610 qz11 qz65 rfl rfl rfl rfl (Ns264p1612 rfl)) (Ns264p1613 qz11 qz83 rfl rfl rfl rfl (Ns264p1615 rfl)) 

noncomputable abbrev qz551 := (RS265to276.d3 qz622 qz632 (@Enclosure.dec_le_dec qz622 qz632 569870 1000 571264 1000 qz626 qz636 rfl rfl rfl))

noncomputable abbrev qz269 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz551)

noncomputable def Ns264p1617 := @Enclosure.Real.IsNear.of_eq qz269 (hardyZApproximantRS₀ qz80) Bool.false 1997312197929358295777 2361183241434822606848 142129876580083230905211 Ns264p470 

noncomputable abbrev qz552 := (@Enclosure.dec_le_dec qz622 qz632 569870 1000 571264 1000 qz626 qz636 rfl rfl rfl)

noncomputable abbrev qz270 := qz552

noncomputable def Ns264p1618 := @Enclosure.Real.IsNear.pos_val qz269 1997312197929358295777 2361183241434822606848 142129876580083230905211 Ns264p470 (Ns264p1617 (RS265to276.d4 qz80 qz98 qz270) RS265to276.d50) rfl 

noncomputable abbrev qz271 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz551)

noncomputable def Ns264p1619 := @Enclosure.Real.IsNear.of_eq qz271 (hardyZApproximantRS₀ qz98) Bool.true 499352911015685603181 73786976294838206464 35624511980998537233 26637098442436592533504 

noncomputable def Ns264p1620 := @Enclosure.Real.IsNear.neg_val qz271 499352911015685603181 73786976294838206464 35624511980998537233 26637098442436592533504 (Ns264p1619 (RS265to276.d46 qz80 qz98 qz270) RS265to276.d51) rfl 

noncomputable def Ns264p1621 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz269 qz4 qz80 565685 1000 569870 1000 

noncomputable def Ns264p1622 := @Enclosure.norm_gt_of_isNear qz269 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1997312197929358295777 2361183241434822606848 142129876580083230905211 

noncomputable def Ns264p1623 := @Ns264p1622 Ns264p470 35978025 536870912 1213 2684354560 (Ns264p1617 (RS265to276.d4 qz80 qz98 qz270) RS265to276.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable def Ns264p1624 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz271 qz4 qz98 565685 1000 571264 1000 

noncomputable def Ns264p1625 := @Enclosure.norm_gt_of_isNear qz271 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 499352911015685603181 73786976294838206464 35624511980998537233 

noncomputable def Ns264p1626 := @Ns264p1625 26637098442436592533504 35978025 536870912 1213 2684354560 (Ns264p1619 (RS265to276.d46 qz80 qz98 qz270) RS265to276.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable abbrev qz272 := qz551

noncomputable def Ns264p1627 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz80 569870 1000 qz83 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz269 qz271 (Ns264p1618 rfl rfl) (Ns264p1620 rfl rfl)) (Ns264p1621 qz11 qz83 rfl rfl rfl rfl (Ns264p1623 rfl)) (Ns264p1624 qz11 qz101 rfl rfl rfl rfl (Ns264p1626 rfl)) 

noncomputable abbrev qz553 := (RS265to276.d3 qz632 qz642 (@Enclosure.dec_le_dec qz632 qz642 571264 1000 572657 1000 qz636 qz646 rfl rfl rfl))

noncomputable abbrev qz273 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz553)

noncomputable def Ns264p1628 := @Enclosure.Real.IsNear.of_eq qz273 (hardyZApproximantRS₀ qz98) Bool.true 499352911015685603181 73786976294838206464 35624511980998537233 26637098442436592533504 

noncomputable abbrev qz554 := (@Enclosure.dec_le_dec qz632 qz642 571264 1000 572657 1000 qz636 qz646 rfl rfl rfl)

noncomputable abbrev qz274 := qz554

noncomputable def Ns264p1629 := @Enclosure.Real.IsNear.neg_val qz273 499352911015685603181 73786976294838206464 35624511980998537233 26637098442436592533504 (Ns264p1628 (RS265to276.d4 qz98 qz116 qz274) RS265to276.d51) rfl 

noncomputable abbrev qz275 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz553)

noncomputable def Ns264p1630 := @Enclosure.Real.IsNear.of_eq qz275 (hardyZApproximantRS₀ qz116) Bool.false 87767316406775142483 73786976294838206464 89270673640985270595819 Ns264p695 

noncomputable def Ns264p1631 := @Enclosure.Real.IsNear.pos_val qz275 87767316406775142483 73786976294838206464 89270673640985270595819 Ns264p695 (Ns264p1630 (RS265to276.d46 qz98 qz116 qz274) RS265to276.d52) rfl 

noncomputable def Ns264p1632 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz273 qz4 qz98 565685 1000 571264 1000 

noncomputable def Ns264p1633 := @Enclosure.norm_gt_of_isNear qz273 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 499352911015685603181 73786976294838206464 35624511980998537233 

noncomputable def Ns264p1634 := @Ns264p1633 26637098442436592533504 35978025 536870912 1213 2684354560 (Ns264p1628 (RS265to276.d4 qz98 qz116 qz274) RS265to276.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable def Ns264p1635 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz275 qz4 qz116 565685 1000 572657 1000 

noncomputable def Ns264p1636 := @Enclosure.norm_gt_of_isNear qz275 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 87767316406775142483 73786976294838206464 89270673640985270595819 

noncomputable def Ns264p1637 := @Ns264p1636 Ns264p695 35978025 536870912 1213 2684354560 (Ns264p1630 (RS265to276.d46 qz98 qz116 qz274) RS265to276.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable abbrev qz276 := qz553

noncomputable def Ns264p1638 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz98 571264 1000 qz101 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz273 qz275 (Ns264p1629 rfl rfl) (Ns264p1631 rfl rfl)) (Ns264p1632 qz11 qz101 rfl rfl rfl rfl (Ns264p1634 rfl)) (Ns264p1635 qz11 qz119 rfl rfl rfl rfl (Ns264p1637 rfl)) 

noncomputable abbrev qz555 := (RS265to276.d3 qz642 qz652 (@Enclosure.dec_le_dec qz642 qz652 572657 1000 574049 1000 qz646 qz656 rfl rfl rfl))

noncomputable abbrev qz277 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz555)

noncomputable def Ns264p1639 := @Enclosure.Real.IsNear.of_eq qz277 (hardyZApproximantRS₀ qz116) Bool.false 87767316406775142483 73786976294838206464 89270673640985270595819 Ns264p695 

noncomputable abbrev qz556 := (@Enclosure.dec_le_dec qz642 qz652 572657 1000 574049 1000 qz646 qz656 rfl rfl rfl)

noncomputable abbrev qz278 := qz556

noncomputable def Ns264p1640 := @Enclosure.Real.IsNear.pos_val qz277 87767316406775142483 73786976294838206464 89270673640985270595819 Ns264p695 (Ns264p1639 (RS265to276.d4 qz116 qz134 qz278) RS265to276.d52) rfl 

noncomputable abbrev qz279 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz555)

noncomputable def Ns264p1641 := @Enclosure.Real.IsNear.of_eq qz279 (hardyZApproximantRS₀ qz134) Bool.true 1532248461717208999959 1180591620717411303424 14325042757883602419147 Ns264p797 

noncomputable def Ns264p1642 := @Enclosure.Real.IsNear.neg_val qz279 1532248461717208999959 1180591620717411303424 14325042757883602419147 Ns264p797 (Ns264p1641 (RS265to276.d46 qz116 qz134 qz278) RS265to276.d53) rfl 

noncomputable def Ns264p1643 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz277 qz4 qz116 565685 1000 572657 1000 

noncomputable def Ns264p1644 := @Enclosure.norm_gt_of_isNear qz277 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 87767316406775142483 73786976294838206464 89270673640985270595819 

noncomputable def Ns264p1645 := @Ns264p1644 Ns264p695 35978025 536870912 1213 2684354560 (Ns264p1639 (RS265to276.d4 qz116 qz134 qz278) RS265to276.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable def Ns264p1646 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz279 qz4 qz134 565685 1000 574049 1000 

noncomputable def Ns264p1647 := @Enclosure.norm_gt_of_isNear qz279 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1532248461717208999959 1180591620717411303424 14325042757883602419147 

noncomputable def Ns264p1648 := @Ns264p1647 Ns264p797 35978025 536870912 1213 2684354560 (Ns264p1641 (RS265to276.d46 qz116 qz134 qz278) RS265to276.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable abbrev qz280 := qz555

noncomputable def Ns264p1649 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz116 572657 1000 qz119 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz277 qz279 (Ns264p1640 rfl rfl) (Ns264p1642 rfl rfl)) (Ns264p1643 qz11 qz119 rfl rfl rfl rfl (Ns264p1645 rfl)) (Ns264p1646 qz11 qz137 rfl rfl rfl rfl (Ns264p1648 rfl)) 

noncomputable abbrev qz557 := (RS265to276.d3 qz652 qz663 (@Enclosure.dec_le_dec qz652 qz663 574049 1000 575440 1000 qz656 qz667 rfl rfl rfl))

noncomputable abbrev qz281 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz557)

noncomputable def Ns264p1650 := @Enclosure.Real.IsNear.of_eq qz281 (hardyZApproximantRS₀ qz134) Bool.true 1532248461717208999959 1180591620717411303424 14325042757883602419147 Ns264p797 

noncomputable abbrev qz558 := (@Enclosure.dec_le_dec qz652 qz663 574049 1000 575440 1000 qz656 qz667 rfl rfl rfl)

noncomputable abbrev qz282 := qz558

noncomputable def Ns264p1651 := @Enclosure.Real.IsNear.neg_val qz281 1532248461717208999959 1180591620717411303424 14325042757883602419147 Ns264p797 (Ns264p1650 (RS265to276.d4 qz134 qz152 qz282) RS265to276.d53) rfl 

noncomputable abbrev qz283 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz557)

noncomputable def Ns264p1652 := @Enclosure.Real.IsNear.of_eq qz283 (hardyZApproximantRS₀ qz152) Bool.false 430142195457904398637 1180591620717411303424 359093320914303194998619 Ns264p906 

noncomputable def Ns264p1653 := @Enclosure.Real.IsNear.pos_val qz283 430142195457904398637 1180591620717411303424 359093320914303194998619 Ns264p906 (Ns264p1652 (RS265to276.d46 qz134 qz152 qz282) RS265to276.d54) rfl 

noncomputable def Ns264p1654 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz281 qz4 qz134 565685 1000 574049 1000 

noncomputable def Ns264p1655 := @Enclosure.norm_gt_of_isNear qz281 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1532248461717208999959 1180591620717411303424 14325042757883602419147 

noncomputable def Ns264p1656 := @Ns264p1655 Ns264p797 35978025 536870912 1213 2684354560 (Ns264p1650 (RS265to276.d4 qz134 qz152 qz282) RS265to276.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable def Ns264p1657 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz283 qz4 qz152 565685 1000 575440 1000 

noncomputable def Ns264p1658 := @Enclosure.norm_gt_of_isNear qz283 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 430142195457904398637 1180591620717411303424 359093320914303194998619 

noncomputable def Ns264p1659 := @Ns264p1658 Ns264p906 35978025 536870912 1213 2684354560 (Ns264p1652 (RS265to276.d46 qz134 qz152 qz282) RS265to276.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable abbrev qz284 := qz557

noncomputable def Ns264p1660 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz134 574049 1000 qz137 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz281 qz283 (Ns264p1651 rfl rfl) (Ns264p1653 rfl rfl)) (Ns264p1654 qz11 qz137 rfl rfl rfl rfl (Ns264p1656 rfl)) (Ns264p1657 qz11 qz155 rfl rfl rfl rfl (Ns264p1659 rfl)) 

noncomputable abbrev qz559 := (RS265to276.d3 qz663 qz673 (@Enclosure.dec_le_dec qz663 qz673 575440 1000 576831 1000 qz667 qz677 rfl rfl rfl))

noncomputable abbrev qz285 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz559)

noncomputable def Ns264p1661 := @Enclosure.Real.IsNear.of_eq qz285 (hardyZApproximantRS₀ qz152) Bool.false 430142195457904398637 1180591620717411303424 359093320914303194998619 Ns264p906 

noncomputable abbrev qz560 := (@Enclosure.dec_le_dec qz663 qz673 575440 1000 576831 1000 qz667 qz677 rfl rfl rfl)

noncomputable abbrev qz286 := qz560

noncomputable def Ns264p1662 := @Enclosure.Real.IsNear.pos_val qz285 430142195457904398637 1180591620717411303424 359093320914303194998619 Ns264p906 (Ns264p1661 (RS265to276.d4 qz152 qz170 qz286) RS265to276.d54) rfl 

noncomputable abbrev qz287 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz559)

noncomputable def Ns264p1663 := @Enclosure.Real.IsNear.of_eq qz287 (hardyZApproximantRS₀ qz170) Bool.true 108749687779837265957 147573952589676412928 45011330605735563244629 Ns264p1017 

noncomputable def Ns264p1664 := @Enclosure.Real.IsNear.neg_val qz287 108749687779837265957 147573952589676412928 45011330605735563244629 Ns264p1017 (Ns264p1663 (RS265to276.d46 qz152 qz170 qz286) RS265to276.d55) rfl 

noncomputable def Ns264p1665 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz285 qz4 qz152 565685 1000 575440 1000 

noncomputable def Ns264p1666 := @Enclosure.norm_gt_of_isNear qz285 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 430142195457904398637 1180591620717411303424 359093320914303194998619 

noncomputable def Ns264p1667 := @Ns264p1666 Ns264p906 35978025 536870912 1213 2684354560 (Ns264p1661 (RS265to276.d4 qz152 qz170 qz286) RS265to276.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable def Ns264p1668 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz287 qz4 qz170 565685 1000 576831 1000 

noncomputable def Ns264p1669 := @Enclosure.norm_gt_of_isNear qz287 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 108749687779837265957 147573952589676412928 45011330605735563244629 

noncomputable def Ns264p1670 := @Ns264p1669 Ns264p1017 35978025 536870912 1213 2684354560 (Ns264p1663 (RS265to276.d46 qz152 qz170 qz286) RS265to276.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable abbrev qz288 := qz559

noncomputable def Ns264p1671 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz152 575440 1000 qz155 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz285 qz287 (Ns264p1662 rfl rfl) (Ns264p1664 rfl rfl)) (Ns264p1665 qz11 qz155 rfl rfl rfl rfl (Ns264p1667 rfl)) (Ns264p1668 qz11 qz173 rfl rfl rfl rfl (Ns264p1670 rfl)) 

noncomputable abbrev qz727 := (@Enclosure.dec_le_dec qz772 qz776 576831 1000 578220 1000 (@Eq.refl Real qz772) (@Eq.refl Real qz776) rfl rfl rfl)

noncomputable abbrev qz561 := (RS265to276.d3 qz673 qz683 qz727)

noncomputable abbrev qz289 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz561)

noncomputable def Ns264p1672 := @Enclosure.Real.IsNear.of_eq qz289 (hardyZApproximantRS₀ qz170) Bool.true 108749687779837265957 147573952589676412928 45011330605735563244629 Ns264p1017 

noncomputable abbrev qz562 := qz727

noncomputable abbrev qz290 := qz562

noncomputable def Ns264p1673 := @Enclosure.Real.IsNear.neg_val qz289 108749687779837265957 147573952589676412928 45011330605735563244629 Ns264p1017 (Ns264p1672 (RS265to276.d4 qz170 qz188 qz290) RS265to276.d55) rfl 

noncomputable abbrev qz291 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz561)

noncomputable def Ns264p1674 := @Enclosure.Real.IsNear.of_eq qz291 (hardyZApproximantRS₀ qz188) Bool.false 1244583849666461667875 295147905179352825856 38012925778526310133 28039050992038518456320 

noncomputable def Ns264p1675 := @Enclosure.Real.IsNear.pos_val qz291 1244583849666461667875 295147905179352825856 38012925778526310133 28039050992038518456320 (Ns264p1674 (RS265to276.d46 qz170 qz188 qz290) RS265to276.d56) rfl 

noncomputable def Ns264p1676 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz289 qz4 qz170 565685 1000 576831 1000 

noncomputable def Ns264p1677 := @Enclosure.norm_gt_of_isNear qz289 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 108749687779837265957 147573952589676412928 45011330605735563244629 

noncomputable def Ns264p1678 := @Ns264p1677 Ns264p1017 35978025 536870912 1213 2684354560 (Ns264p1672 (RS265to276.d4 qz170 qz188 qz290) RS265to276.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable def Ns264p1679 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz291 qz4 qz188 565685 1000 578220 1000 

noncomputable def Ns264p1680 := @Enclosure.norm_gt_of_isNear qz291 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1244583849666461667875 295147905179352825856 38012925778526310133 

noncomputable def Ns264p1681 := @Ns264p1680 28039050992038518456320 35978025 536870912 1213 2684354560 (Ns264p1674 (RS265to276.d46 qz170 qz188 qz290) RS265to276.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable abbrev qz292 := qz561

noncomputable def Ns264p1682 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz170 576831 1000 qz173 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz289 qz291 (Ns264p1673 rfl rfl) (Ns264p1675 rfl rfl)) (Ns264p1676 qz11 qz173 rfl rfl rfl rfl (Ns264p1678 rfl)) (Ns264p1679 qz11 qz191 rfl rfl rfl rfl (Ns264p1681 rfl)) 

noncomputable abbrev qz728 := (@Enclosure.dec_le_dec qz776 qz780 578220 1000 579609 1000 (@Eq.refl Real qz776) qz783 rfl rfl rfl)

noncomputable abbrev qz563 := (RS265to276.d3 qz683 qz693 qz728)

noncomputable abbrev qz293 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz563)

noncomputable def Ns264p1683 := @Enclosure.Real.IsNear.of_eq qz293 (hardyZApproximantRS₀ qz188) Bool.false 1244583849666461667875 295147905179352825856 38012925778526310133 28039050992038518456320 

noncomputable abbrev qz564 := qz728

noncomputable abbrev qz294 := qz564

noncomputable def Ns264p1684 := @Enclosure.Real.IsNear.pos_val qz293 1244583849666461667875 295147905179352825856 38012925778526310133 28039050992038518456320 (Ns264p1683 (RS265to276.d4 qz188 qz206 qz294) RS265to276.d56) rfl 

noncomputable abbrev qz295 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz563)

noncomputable def Ns264p1685 := @Enclosure.Real.IsNear.of_eq qz295 (hardyZApproximantRS₀ qz206) Bool.true 1814525002514104853895 1180591620717411303424 90542885846809034358269 Ns264p695 

noncomputable def Ns264p1686 := @Enclosure.Real.IsNear.neg_val qz295 1814525002514104853895 1180591620717411303424 90542885846809034358269 Ns264p695 (Ns264p1685 (RS265to276.d46 qz188 qz206 qz294) RS265to276.d57) rfl 

noncomputable def Ns264p1687 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz293 qz4 qz188 565685 1000 578220 1000 

noncomputable def Ns264p1688 := @Enclosure.norm_gt_of_isNear qz293 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1244583849666461667875 295147905179352825856 38012925778526310133 

noncomputable def Ns264p1689 := @Ns264p1688 28039050992038518456320 35978025 536870912 1213 2684354560 (Ns264p1683 (RS265to276.d4 qz188 qz206 qz294) RS265to276.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable def Ns264p1690 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz295 qz4 qz206 565685 1000 579609 1000 

noncomputable def Ns264p1691 := @Enclosure.norm_gt_of_isNear qz295 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1814525002514104853895 1180591620717411303424 90542885846809034358269 

noncomputable def Ns264p1692 := @Ns264p1691 Ns264p695 35978025 536870912 1213 2684354560 (Ns264p1685 (RS265to276.d46 qz188 qz206 qz294) RS265to276.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable abbrev qz296 := qz563

noncomputable def Ns264p1693 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz188 578220 1000 qz191 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz293 qz295 (Ns264p1684 rfl rfl) (Ns264p1686 rfl rfl)) (Ns264p1687 qz11 qz191 rfl rfl rfl rfl (Ns264p1689 rfl)) (Ns264p1690 qz11 qz209 rfl rfl rfl rfl (Ns264p1692 rfl)) 

noncomputable abbrev qz729 := (@Enclosure.dec_le_dec qz780 qz785 579609 1000 580998 1000 qz783 qz788 rfl rfl rfl)

noncomputable abbrev qz565 := (RS265to276.d3 qz693 qz705 qz729)

noncomputable abbrev qz297 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz565)

noncomputable def Ns264p1694 := @Enclosure.Real.IsNear.of_eq qz297 (hardyZApproximantRS₀ qz206) Bool.true 1814525002514104853895 1180591620717411303424 90542885846809034358269 Ns264p695 

noncomputable abbrev qz566 := qz729

noncomputable abbrev qz298 := qz566

noncomputable def Ns264p1695 := @Enclosure.Real.IsNear.neg_val qz297 1814525002514104853895 1180591620717411303424 90542885846809034358269 Ns264p695 (Ns264p1694 (RS265to276.d4 qz206 qz223 qz298) RS265to276.d57) rfl 

noncomputable abbrev qz299 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz565)

noncomputable def Ns264p1696 := @Enclosure.Real.IsNear.of_eq qz299 (hardyZApproximantRS₀ qz223) Bool.false 265683244767154628407 73786976294838206464 181628542406167154417 133185492212182962667520 

noncomputable def Ns264p1697 := @Enclosure.Real.IsNear.pos_val qz299 265683244767154628407 73786976294838206464 181628542406167154417 133185492212182962667520 (Ns264p1696 (RS265to276.d46 qz206 qz223 qz298) RS265to276.d58) rfl 

noncomputable def Ns264p1698 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz297 qz4 qz206 565685 1000 579609 1000 

noncomputable def Ns264p1699 := @Enclosure.norm_gt_of_isNear qz297 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1814525002514104853895 1180591620717411303424 90542885846809034358269 

noncomputable def Ns264p1700 := @Ns264p1699 Ns264p695 35978025 536870912 1213 2684354560 (Ns264p1694 (RS265to276.d4 qz206 qz223 qz298) RS265to276.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable def Ns264p1701 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz299 qz4 qz223 565685 1000 580998 1000 

noncomputable def Ns264p1702 := @Enclosure.norm_gt_of_isNear qz299 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 265683244767154628407 73786976294838206464 181628542406167154417 

noncomputable def Ns264p1703 := @Ns264p1702 133185492212182962667520 35978025 536870912 1213 2684354560 (Ns264p1696 (RS265to276.d46 qz206 qz223 qz298) RS265to276.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable abbrev qz300 := qz565

noncomputable def Ns264p1704 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz206 579609 1000 qz209 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz297 qz299 (Ns264p1695 rfl rfl) (Ns264p1697 rfl rfl)) (Ns264p1698 qz11 qz209 rfl rfl rfl rfl (Ns264p1700 rfl)) (Ns264p1701 qz11 qz226 rfl rfl rfl rfl (Ns264p1703 rfl)) 

noncomputable abbrev qz795 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 580998 1000) (Enclosure.sfrac Bool.false 582385 1000) 580998 1000 582385 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 580998 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 582385 1000)) rfl rfl rfl)

noncomputable abbrev qz730 := qz795

noncomputable abbrev qz567 := (RS265to276.d3 qz705 qz716 qz730)

noncomputable abbrev qz301 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz567)

noncomputable def Ns264p1705 := @Enclosure.Real.IsNear.of_eq qz301 (hardyZApproximantRS₀ qz223) Bool.false 265683244767154628407 73786976294838206464 181628542406167154417 133185492212182962667520 

noncomputable abbrev qz568 := qz730

noncomputable abbrev qz302 := qz568

noncomputable def Ns264p1706 := @Enclosure.Real.IsNear.pos_val qz301 265683244767154628407 73786976294838206464 181628542406167154417 133185492212182962667520 (Ns264p1705 (RS265to276.d4 qz223 qz240 qz302) RS265to276.d58) rfl 

noncomputable abbrev qz303 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz567)

noncomputable def Ns264p1707 := @Enclosure.Real.IsNear.of_eq qz303 (hardyZApproximantRS₀ qz240) Bool.true 491182005797401860019 295147905179352825856 91104705804614250806701 Ns264p695 

noncomputable def Ns264p1708 := @Enclosure.Real.IsNear.neg_val qz303 491182005797401860019 295147905179352825856 91104705804614250806701 Ns264p695 (Ns264p1707 (RS265to276.d46 qz223 qz240 qz302) RS265to276.d59) rfl 

noncomputable def Ns264p1709 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz301 qz4 qz223 565685 1000 580998 1000 

noncomputable def Ns264p1710 := @Enclosure.norm_gt_of_isNear qz301 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 265683244767154628407 73786976294838206464 181628542406167154417 

noncomputable def Ns264p1711 := @Ns264p1710 133185492212182962667520 35978025 536870912 1213 2684354560 (Ns264p1705 (RS265to276.d4 qz223 qz240 qz302) RS265to276.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable def Ns264p1712 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz303 qz4 qz240 565685 1000 582385 1000 

noncomputable def Ns264p1713 := @Enclosure.norm_gt_of_isNear qz303 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 491182005797401860019 295147905179352825856 91104705804614250806701 

noncomputable def Ns264p1714 := @Ns264p1713 Ns264p695 35978025 536870912 1213 2684354560 (Ns264p1707 (RS265to276.d46 qz223 qz240 qz302) RS265to276.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 35978025 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS265to276.d48) rfl rfl rfl rfl 

noncomputable abbrev qz304 := qz567

noncomputable def Ns264p1715 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz223 580998 1000 qz226 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz301 qz303 (Ns264p1706 rfl rfl) (Ns264p1708 rfl rfl)) (Ns264p1709 qz11 qz226 rfl rfl rfl rfl (Ns264p1711 rfl)) (Ns264p1712 qz11 qz243 rfl rfl rfl rfl (Ns264p1714 rfl)) 

noncomputable def Ns264p1716 := @List.cons RS265to276.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns264p1704)) (@List.cons RS265to276.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns264p1715)) (@List.nil RS265to276.d0)) 

noncomputable def Ns264p1717 := @List.cons RS265to276.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns264p1682)) (@List.cons RS265to276.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns264p1693)) Ns264p1716) 

noncomputable def Ns264p1718 := @List.cons RS265to276.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns264p1660)) (@List.cons RS265to276.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns264p1671)) Ns264p1717) 

noncomputable def Ns264p1719 := @List.cons RS265to276.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns264p1638)) (@List.cons RS265to276.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns264p1649)) Ns264p1718) 

noncomputable def Ns264p1720 := @List.cons RS265to276.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns264p1616)) (@List.cons RS265to276.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns264p1627)) Ns264p1719) 

noncomputable def Ns264p1721 := @List.cons RS265to276.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz260 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz260) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz260) Ns264p1594)) (@List.cons RS265to276.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz264 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz264) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz264) Ns264p1605)) Ns264p1720) 

noncomputable abbrev qz569 := (RS265to276.d2 qz673 qz683 qz727)

noncomputable abbrev qz731 := (RS265to276.d2 qz780 qz785 (@Enclosure.dec_le_dec qz780 qz785 579609 1000 580998 1000 qz783 qz788 rfl rfl rfl))

noncomputable abbrev qz732 := (@List.cons RS265to276.d1 (RS265to276.d2 qz785 qz790 qz795) (@List.nil RS265to276.d1))

noncomputable abbrev qz570 := (@List.cons RS265to276.d1 (RS265to276.d2 qz683 qz693 qz728) (@List.cons RS265to276.d1 qz731 qz732))

noncomputable abbrev qz305 := (@List.cons RS265to276.d1 (RS265to276.d2 qz470 qz483 qz560) (@List.cons RS265to276.d1 qz569 qz570))

noncomputable def Ns264p1722 := @List.cons RS265to276.d1 (RS265to276.d2 qz116 qz134 qz278) (@List.cons RS265to276.d1 (RS265to276.d2 qz134 qz152 qz282) qz305) 

noncomputable abbrev qz306 := (RS265to276.d2 qz431 qz444 qz554)

noncomputable def Ns264p1723 := @List.IsChain.cons_cons RS265to276.d1 RS265to276.d60 qz306 (RS265to276.d2 qz116 qz134 qz278) (@List.cons RS265to276.d1 (RS265to276.d2 qz134 qz152 qz282) qz305) 

noncomputable def Ns264p1724 := @List.IsChain.cons_cons RS265to276.d1 RS265to276.d60 (RS265to276.d2 qz116 qz134 qz278) (RS265to276.d2 qz134 qz152 qz282) qz305 (@Enclosure.dec_le_dec qz134 qz134 574049 1000 574049 1000 qz137 qz137 rfl rfl rfl) 

noncomputable abbrev qz307 := (RS265to276.d2 qz470 qz483 qz560)

noncomputable abbrev qz308 := qz569

noncomputable abbrev qz309 := qz570

noncomputable abbrev qz571 := (RS265to276.d2 qz683 qz693 qz728)

noncomputable abbrev qz310 := qz571

noncomputable abbrev qz572 := (@List.cons RS265to276.d1 qz731 qz732)

noncomputable abbrev qz311 := qz572

noncomputable abbrev qz573 := qz731

noncomputable abbrev qz312 := qz573

noncomputable abbrev qz574 := qz732

noncomputable abbrev qz313 := qz574

noncomputable abbrev qz733 := (RS265to276.d2 qz785 qz790 qz795)

noncomputable abbrev qz575 := qz733

noncomputable abbrev qz314 := qz575

noncomputable def Ns264p1725 := @List.IsChain.cons_cons RS265to276.d1 RS265to276.d60 qz307 qz308 qz309 (@Enclosure.dec_le_dec qz170 qz170 576831 1000 576831 1000 qz173 qz173 rfl rfl rfl) (@List.IsChain.cons_cons RS265to276.d1 RS265to276.d60 qz308 qz310 qz311 (@Enclosure.dec_le_dec qz188 qz188 578220 1000 578220 1000 qz191 qz191 rfl rfl rfl) (@List.IsChain.cons_cons RS265to276.d1 RS265to276.d60 qz310 qz312 qz313 (@Enclosure.dec_le_dec qz206 qz206 579609 1000 579609 1000 qz209 qz209 rfl rfl rfl) (@List.IsChain.cons_cons RS265to276.d1 RS265to276.d60 qz312 qz314 (@List.nil RS265to276.d1) (@Enclosure.dec_le_dec qz223 qz223 580998 1000 580998 1000 qz226 qz226 rfl rfl rfl) (@List.IsChain.singleton RS265to276.d1 RS265to276.d60 qz314)))) 

noncomputable abbrev qz315 := (@List.cons RS265to276.d1 qz569 qz570)

noncomputable def Ns264p1726 := @List.IsChain.cons_cons RS265to276.d1 RS265to276.d60 (RS265to276.d2 qz134 qz152 qz282) qz307 qz315 (@Enclosure.dec_le_dec qz152 qz152 575440 1000 575440 1000 qz155 qz155 rfl rfl rfl) Ns264p1725 

noncomputable def Ns264p1727 := @List.IsChain.cons_cons RS265to276.d1 RS265to276.d60 (RS265to276.d2 qz4 qz35 qz258) (RS265to276.d2 qz35 qz62 qz262) (@List.cons RS265to276.d1 (RS265to276.d2 qz62 qz80 qz266) (@List.cons RS265to276.d1 (RS265to276.d2 qz80 qz98 qz270) (@List.cons RS265to276.d1 qz306 Ns264p1722))) (@Enclosure.dec_le_dec qz35 qz35 567081 1000 567081 1000 qz38 qz38 rfl rfl rfl) (@List.IsChain.cons_cons RS265to276.d1 RS265to276.d60 (RS265to276.d2 qz35 qz62 qz262) (RS265to276.d2 qz62 qz80 qz266) (@List.cons RS265to276.d1 (RS265to276.d2 qz80 qz98 qz270) (@List.cons RS265to276.d1 qz306 Ns264p1722)) (@Enclosure.dec_le_dec qz62 qz62 568476 1000 568476 1000 qz65 qz65 rfl rfl rfl) (@List.IsChain.cons_cons RS265to276.d1 RS265to276.d60 (RS265to276.d2 qz62 qz80 qz266) (RS265to276.d2 qz80 qz98 qz270) (@List.cons RS265to276.d1 qz306 Ns264p1722) (@Enclosure.dec_le_dec qz80 qz80 569870 1000 569870 1000 qz83 qz83 rfl rfl rfl) (@List.IsChain.cons_cons RS265to276.d1 RS265to276.d60 (RS265to276.d2 qz80 qz98 qz270) qz306 Ns264p1722 (@Enclosure.dec_le_dec qz98 qz98 571264 1000 571264 1000 qz101 qz101 rfl rfl rfl) (Ns264p1723 (@Enclosure.dec_le_dec qz116 qz116 572657 1000 572657 1000 qz119 qz119 rfl rfl rfl) (Ns264p1724 Ns264p1726))))) 

noncomputable abbrev qz576 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz577 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns264p1721 Ns264p1727)

noncomputable abbrev qz578 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns264p1721 Ns264p1727))

theorem RS265to276.d61 : Zeta.Certificates.BatchSpec 12 565685 1000 582385 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz576 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz576 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz576 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz240)))) qz577 (@And.intro (@Eq Nat (@List.length qz576 qz578) 12) (And (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz576 qz578)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz576 qz578)) (@Option.some Real qz240))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz576 qz578)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz576 qz578)) (@Option.some Real qz240)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz240))))

theorem solution : Zeta.Certificates.BatchSpec 12 565685 1000 582385 1000 := RS265to276.d61
#print axioms solution
#check solution
