-- Prove2me | solution 1 for RHHeight1000.rs_main_0187_0204
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T07:49:44.090694+00:00
-- url     : https://prove2.me/submissions/c922b6dc-ffd0-43f3-ba7a-3703e7f5a43f

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

noncomputable def RS187to204.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS187to204.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS187to204.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS187to204.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS187to204.d2 a b h 

theorem RS187to204.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS187to204.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS187to204.d3 a b h)) 

noncomputable def Ns186p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns186p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns186p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns186p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns186p0 Ns186p1 Ns186p2 Ns186p1 153643044 134217728 1 36000000 153643044 134217728 1 36000000 76821522 67108864 2 67108864 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns186p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns186p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns186p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns186p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns186p8 := nat_lit 167537954069964697925743468333314178468718661948561187618563575975392713740913527107727581163208035826476740967700482432525301063254420572874757592895482956004842597348203117269212172556829666669574421653274845612596416189641484794702002223261246862056663160605878293700340502480877986491439034432953223334258717026053687371824342493299510132312376251152844516906794910572262907940062760396663270105627554083664899640691826599584783763757814813433640133591539937449421955686657622469485188711283992428713614179785896055117030632677201478317872225272595773536303110412989181984739022579128493081560758017763072115692678596043664844667144619713966763611484179303468167142547433165016751768184247559143333542643815355903304572487929375 

noncomputable def Ns186p9 := nat_lit 17907736863639440849562382641391758203535690054199171304015283257442503423240620144819838407313611418261944516207295868563739563278604805791797182761045687776939279949642059267526948014748996956777332184087524644234759874591635243045607722412471722018588244283882362848653445974523544951031470230725674276297342086185092985546835544820091590454230569790847977790484558207349923322458845585052164126500435851662252152223728079705692133047658564669873831757357628115566356048471439549797170528303905720944834637690907185213991407615774042056720704508980680095051114888612186461088301140868302968264130481206655302741383410655080008578156649725227045954510069588220729495895148666460653631514375880874422615237249871322129146554264800 

noncomputable def Ns186p10 := nat_lit 55164646516618494962085419356369025784335016154267579706247610053041231157772817011486486467101704279863254798704146668052276438579475100451766223896220272709675360577301802978530276301158911649961092601279696986330335403118086533522541958716560166657634553390183479955483588238249446822384543398154260439705049143284278540285021213103458182619368483938376641172730818250587232036579805400979202432024046862170503602539341971086573372247299262086029843105216008583038025403798224342134620653974939981235680083776396058604459065501719125356177784467570909658245422960948263734871602033841948787585406240093531041217463298165642337705122589129757920995868559518021463265498464182174549661735402095023640043996665674913376875 

noncomputable def Ns186p11 := BSN.log_dyadic_bound Ns186p6 Ns186p7 15 14 Ns186p8 134217728 36000000 Ns186p9 Ns186p10 153643044 Ns186p4 Ns186p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns186p6) (BSN.artanhQ Ns186p7) 0 14 Ns186p9 Ns186p8 Ns186p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns186p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns186p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns186p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns186p15 := nat_lit 167537954069966963268140139327979112712430526945422964221951926912223381190141639739514890494967825643602350173964944759828460064784215684919760383437959917620844610857567326816719640593037578236900835917107172977527392439886629774248115214831425484905681376157923696414882114961796820014026232307332015059110330001516939277521159573995394989771587717775443426002499543257897301982481613760098955890450106043861450716722534643739571053080256776912576113428445260435254713579381797931690799491102381747484553243404562568585572234105168360737285205910186933811836504830286397217473365026331067977496463917110493303316865058355012304571237619413071097245713770677768486493924969821719264401216877841676972336093778875903304572487929375 

noncomputable def Ns186p16 := nat_lit 17907736863639702486765313263906285882628955290251965205176678923530777959693011244026517850256414903756943142851250712732214241881959351517241344993825585048584379523049477943740273636414656012170312373198803997844271825165684859407921203335666024680974464565759223251918458072775203410604089667122984485578465112081892102496937045858735135721609691262763214794451343726045584198128451069547586972080574568545086657023793200560105564573365716615162566961587407171758966967827997201380802107846920231945878242774600967607639551032178207663699700360114112068650063802902647517702890145150192721997537569966984346993833704449560383184487996362781528900358997452380059737141488304159449328022742959995775545894292303322129146554264800 

noncomputable def Ns186p17 := nat_lit 55164646516619937449385584700664297411818070214438189962773666351465523500358685366424500506990751111492356556545320273548942244833046464529601272738875466881799996765940232256588350019911833156887888425998391295014189841212513610526066550079316346993943774342801096070086869790972589246312728227659319758310961510342377923950694747797317942483020440897997204711883064182772445608288320382376665481938194224815739627075458138172195220395246294556718284728034954178416253903237031389214179719385823921869528509431462690683227358218086518156757026652846493301460983550768858152506145788622699720737745394141184245149692548799188169247529408201840608223422296381897323845616153036586108326210125693898345963996665674913376875 

noncomputable def Ns186p18 := BSN.log_dyadic_bound Ns186p13 Ns186p14 15 14 Ns186p15 134217728 36000000 Ns186p16 Ns186p17 153643044 Ns186p12 Ns186p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns186p13) (BSN.artanhQ Ns186p14) 0 14 Ns186p16 Ns186p15 Ns186p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns186p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 76821522 67108864 2 67108864 38410761 33554432 1 33554432 (Ns186p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns186p0 Ns186p1 153643044 134217728 1 36000000 Bool.false (BSN.logfrac_isNear Ns186p4 Ns186p5 1 Ns186p0 Ns186p1 153643044 134217728 36000000 rfl rfl rfl (Ns186p11 rfl))) (BSN.isNear_log_sfrac Ns186p2 Ns186p1 153643044 134217728 1 36000000 Bool.false (BSN.logfrac_isNear Ns186p12 Ns186p5 1 Ns186p2 Ns186p1 153643044 134217728 36000000 rfl rfl rfl (Ns186p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS187to204.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 33554432 := Ns186p19 

noncomputable def Ns186p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 8388608 2250000 385100712855 135135 5814539 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz316 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz0 := qz316

theorem RS187to204.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 5814539 8388608 1 2250000 := BSN.isNear_log_sfrac 2 1 5814539 8388608 1 2250000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 5814539 8388608 2250000 rfl rfl rfl (Ns186p20 rfl)) 

theorem RS187to204.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 93032624 134217728 60 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 5814539 8388608 1 2250000 93032624 134217728 60 134217728 RS187to204.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz319 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def Ns186p21 := @Enclosure.Real.IsNear.inv_image qz317 23726567 16777216 1 16777216 5931641 5931642 8388608 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 23726567 16777216 1 16777216 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 23726567 16777216 1 16777216 23726567 16777216 1 16777216 (BSN.sqrt_enclosure 2 1 11863283 11863284 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS187to204.d8 : Enclosure.Real.IsNear qz320 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 11863283 16777216 1 16777216 (Ns186p21 rfl rfl) rfl 

theorem RS187to204.d9 : Enclosure.Real.IsNear qz320 Bool.false 94906264 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 94906264 134217728 8 134217728 RS187to204.d8 rfl 

noncomputable def Ns186p22 := BSN.log_dyadic_bound 1 2 12 11 1326382131865190400 8388608 2250000 130797573554866995 13749310575 9215827 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 1) (BSN.artanhQ 2) 0 11 130797573554866995 1326382131865190400 13749310575 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS187to204.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 9215827 8388608 1 2250000 := BSN.isNear_log_sfrac 3 1 9215827 8388608 1 2250000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 9215827 8388608 2250000 rfl rfl rfl (Ns186p22 rfl)) 

theorem RS187to204.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 147453232 134217728 60 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 9215827 8388608 1 2250000 147453232 134217728 60 134217728 RS187to204.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns186p23 := @Enclosure.Real.IsNear.inv_image qz321 29058991 16777216 1 16777216 4843164 4843166 8388608 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 29058991 16777216 1 16777216 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 29058991 16777216 1 16777216 29058991 16777216 1 16777216 (BSN.sqrt_enclosure 3 1 14529495 14529496 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS187to204.d12 : Enclosure.Real.IsNear qz323 Bool.false 4843165 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 9686330 16777216 2 16777216 4843165 8388608 1 8388608 (Ns186p23 rfl rfl) rfl 

theorem RS187to204.d13 : Enclosure.Real.IsNear qz323 Bool.false 77490640 134217728 16 134217728 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 4843165 8388608 1 8388608 77490640 134217728 16 134217728 RS187to204.d12 rfl 

noncomputable def Ns186p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns186p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns186p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns186p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns186p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns186p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns186p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns186p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns186p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns186p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns186p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns186p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns186p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns186p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns186p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns186p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns186p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns186p25 Ns186p26 Ns186p27 Ns186p28 200200021673987500790625 Ns186p29 Ns186p30 Ns186p31 Ns186p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns186p32 Ns186p33 151412625 Ns186p34 Ns186p35 1322214852783825 Ns186p27 Ns186p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns186p32 Ns186p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns186p34 Ns186p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns186p36 Ns186p37 1267389585 Ns186p38 Ns186p39 1927077560082675 Ns186p29 Ns186p30 Ns186p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns186p36 Ns186p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns186p38 Ns186p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS187to204.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns186p24 Ns186p25 1 Ns186p26 := Ns186p40 rfl rfl rfl 

noncomputable def Ns186p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns186p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns186p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns186p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns186p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns186p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns186p25 Ns186p26 Ns186p42 Ns186p43 9945 Ns186p44 Ns186p45 65835 Ns186p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns186p42 Ns186p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns186p44 Ns186p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS187to204.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns186p41 Ns186p25 1 Ns186p26 := Ns186p46 rfl 

noncomputable def Ns186p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns186p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS187to204.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns186p47 Ns186p25 1 Ns186p48 := BSN.pi_combine Ns186p24 Ns186p41 Ns186p25 Ns186p26 Ns186p48 Ns186p47 rfl rfl rfl rfl RS187to204.d14 RS187to204.d15 

theorem RS187to204.d17 : Enclosure.Real.IsNear Real.pi Bool.false 7074237752028440 2251799813685248 1 2251799813685248 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns186p47 Ns186p25 1 Ns186p48 7074237752028440 2251799813685248 1 2251799813685248 RS187to204.d16 rfl 

noncomputable def Ns186p49 := nat_lit 178719669545544893480837345123291015625 

noncomputable def Ns186p50 := nat_lit 27745388228251122714770036239987464375 

noncomputable def Ns186p51 := nat_lit 1274524447665412456340166714375 

noncomputable def Ns186p52 := BSN.log_dyadic_bound 3 5 16 15 Ns186p49 8388608 2250000 Ns186p50 Ns186p51 11629079 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP 3) (BSN.artanhQ 5) 0 15 Ns186p50 Ns186p49 Ns186p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS187to204.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 11629079 8388608 1 2250000 := BSN.isNear_log_sfrac 4 1 11629079 8388608 1 2250000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 11629079 8388608 2250000 rfl rfl rfl (Ns186p52 rfl)) 

theorem RS187to204.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 186065264 134217728 60 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 11629079 8388608 1 2250000 186065264 134217728 60 134217728 RS187to204.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns186p53 := @Enclosure.Real.IsNear.inv_image qz325 33554433 16777216 1 16777216 4194303 4194304 8388608 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 33554433 16777216 1 16777216 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 33554433 16777216 1 16777216 33554433 16777216 1 16777216 (BSN.sqrt_enclosure 4 1 16777216 16777217 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS187to204.d20 : Enclosure.Real.IsNear qz327 Bool.false 8388607 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 8388607 16777216 1 16777216 8388607 16777216 1 16777216 (Ns186p53 rfl rfl) rfl 

theorem RS187to204.d21 : Enclosure.Real.IsNear qz327 Bool.false 67108856 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 8388607 16777216 1 16777216 67108856 134217728 8 134217728 RS187to204.d20 rfl 

noncomputable def Ns186p54 := nat_lit 159424323765613091421820433543167414255940625 

noncomputable def Ns186p55 := nat_lit 33013339099500162583200499609923570567289500 

noncomputable def Ns186p56 := nat_lit 351657888879851162997374110924800000 

noncomputable def Ns186p57 := nat_lit 2289063575687431840984260 

noncomputable def Ns186p58 := nat_lit 3325435793429257756623375 

noncomputable def Ns186p59 := BSN.log_dyadic_bound 2 3 21 20 Ns186p54 8388608 2250000 Ns186p55 Ns186p56 13500943 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 20 10 9927050056596826020 47940881637414340575 686533194547200 Ns186p57 Ns186p58 512222703392784384000 Ns186p55 Ns186p54 Ns186p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 10 20 Ns186p57 Ns186p58 512222703392784384000 rfl rfl rfl rfl)) rfl rfl 

theorem RS187to204.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 13500943 8388608 1 2250000 := BSN.isNear_log_sfrac 5 1 13500943 8388608 1 2250000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 13500943 8388608 2250000 rfl rfl rfl (Ns186p59 rfl rfl)) 

theorem RS187to204.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 216015088 134217728 60 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 13500943 8388608 1 2250000 216015088 134217728 60 134217728 RS187to204.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns186p60 := @Enclosure.Real.IsNear.inv_image qz328 37514995 16777216 1 16777216 3751499 3751500 8388608 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 37514995 16777216 1 16777216 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 37514995 16777216 1 16777216 37514995 16777216 1 16777216 (BSN.sqrt_enclosure 5 1 18757497 18757498 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS187to204.d24 : Enclosure.Real.IsNear qz329 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 7502999 16777216 1 16777216 (Ns186p60 rfl rfl) rfl 

theorem RS187to204.d25 : Enclosure.Real.IsNear qz329 Bool.false 60023992 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 60023992 134217728 8 134217728 RS187to204.d24 rfl 

noncomputable def Ns186p61 := BSN.log_dyadic_bound 2 10 5 4 94500000000 8388608 2250000 1291130880 26880 3401287 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) (@Nat.cast Real Real.instNatCast 1))

theorem RS187to204.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683410914551 2251799813685248 2000000009 4500000000000000 := BSN.isNear_log_sfrac 6 1 4034683410914551 2251799813685248 2000000009 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 541526040612241437360128 302231454903657293676544 1000000004500000 2250000000000000000000 4034683410914551 2251799813685248 2000000009 4500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 3401287 8388608 24973259072661432 36028797018963968 2250000 1000000000000000 rfl rfl rfl rfl (Ns186p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS187to204.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 240485871 134217728 61 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683410914551 2251799813685248 2000000009 4500000000000000 240485871 134217728 61 134217728 RS187to204.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns186p62 := @Enclosure.Real.IsNear.inv_image qz331 41095619 16777216 1 16777216 3424634 3424635 8388608 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 41095619 16777216 1 16777216 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 41095619 16777216 1 16777216 41095619 16777216 1 16777216 (BSN.sqrt_enclosure 6 1 20547809 20547810 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS187to204.d28 : Enclosure.Real.IsNear qz332 Bool.false 6849269 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 6849269 16777216 1 16777216 6849269 16777216 1 16777216 (Ns186p62 rfl rfl) rfl 

theorem RS187to204.d29 : Enclosure.Real.IsNear qz332 Bool.false 54794152 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 6849269 16777216 1 16777216 54794152 134217728 8 134217728 RS187to204.d28 rfl 

noncomputable def Ns186p63 := BSN.log_dyadic_bound 3 11 6 5 269619528727395 8388608 2250000 6999933372849 55801305 4694397 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 3) (BSN.artanhQ 11) 0 5 6999933372849 269619528727395 55801305 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) (@Nat.cast Real Real.instNatCast 1))

theorem RS187to204.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 2000000009 4500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 2000000009 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 588115238325433934020608 302231454903657293676544 1000000004500000 2250000000000000000000 4381799983422711 2251799813685248 2000000009 4500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 4694397 8388608 24973259072661432 36028797018963968 2250000 1000000000000000 rfl rfl rfl rfl (Ns186p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS187to204.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 261175631 134217728 61 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 2000000009 4500000000000000 261175631 134217728 61 134217728 RS187to204.d30 rfl 

noncomputable abbrev qz334 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns186p64 := @Enclosure.Real.IsNear.inv_image qz334 44388341 16777216 1 16777216 3170595 3170596 8388608 (@Enclosure.Real.IsNear.of_eq qz334 (Real.sqrt qz333) Bool.false 44388341 16777216 1 16777216 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 44388341 16777216 1 16777216 44388341 16777216 1 16777216 (BSN.sqrt_enclosure 7 1 22194170 22194171 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS187to204.d32 : Enclosure.Real.IsNear qz335 Bool.false 6341191 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 6341191 16777216 1 16777216 6341191 16777216 1 16777216 (Ns186p64 rfl rfl) rfl 

theorem RS187to204.d33 : Enclosure.Real.IsNear qz335 Bool.false 50729528 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 6341191 16777216 1 16777216 50729528 134217728 8 134217728 RS187to204.d32 rfl 

noncomputable def Ns186p65 := BSN.log_dyadic_bound 0 16 1 0 1 8388608 2250000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz890 := (Enclosure.sfrac Bool.false 8 1)

noncomputable abbrev qz627 := qz890

noncomputable abbrev qz336 := qz627

noncomputable abbrev qz1 := qz336

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) (@Nat.cast Real Real.instNatCast 1))

theorem RS187to204.d34 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 9364972152248037 4503599627370496 4000000027 9000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 4000000027 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz337) Bool.false 628472642529000809299968 302231454903657293676544 1000000006750000 2250000000000000000000 9364972152248037 4503599627370496 4000000027 9000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 8388608 24973259072661432 36028797018963968 2250000 1000000000000000 rfl rfl rfl rfl (Ns186p65 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS187to204.d35 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 279097919 134217728 60 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 9364972152248037 4503599627370496 4000000027 9000000000000000 279097919 134217728 60 134217728 RS187to204.d34 rfl 

noncomputable abbrev qz338 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns186p66 := @Enclosure.Real.IsNear.inv_image qz338 47453133 16777216 1 16777216 2965820 2965821 8388608 (@Enclosure.Real.IsNear.of_eq qz338 (Real.sqrt qz337) Bool.false 47453133 16777216 1 16777216 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz337) Bool.false 47453133 16777216 1 16777216 47453133 16777216 1 16777216 (BSN.sqrt_enclosure 8 1 23726566 23726567 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz339 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS187to204.d36 : Enclosure.Real.IsNear qz339 Bool.false 5931641 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz339 Bool.false 5931641 16777216 1 16777216 5931641 16777216 1 16777216 (Ns186p66 rfl rfl) rfl 

theorem RS187to204.d37 : Enclosure.Real.IsNear qz339 Bool.false 47453128 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz339 Bool.false 5931641 16777216 1 16777216 47453128 134217728 8 134217728 RS187to204.d36 rfl 

theorem RS187to204.d38 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz891 := (@instHMul Real Real.instMul)

noncomputable abbrev qz628 := qz891

noncomputable abbrev qz340 := (@HMul.hMul Real Real Real qz628 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz2 := qz340

theorem RS187to204.d39 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS187to204.d38 rfl 

noncomputable abbrev qz3 := (@Inv.inv Real Real.instInv qz340)

theorem RS187to204.d40 : Enclosure.Real.IsNear qz3 Bool.false 2670177 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 2670177 16777216 1 16777216 2670177 16777216 1 16777216 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 1335088 1335089 8388608 RS187to204.d39 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns186p67 := nat_lit 6432173487392806690600517632 

noncomputable abbrev qz892 := (Enclosure.sfrac Bool.false 454159 1000)

noncomputable abbrev qz629 := qz892

noncomputable abbrev qz341 := qz629

noncomputable abbrev qz4 := qz341

noncomputable abbrev qz342 := qz628

noncomputable abbrev qz5 := qz342

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 8)

noncomputable abbrev qz7 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz893 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 454159 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz630 := qz893

noncomputable abbrev qz343 := qz630

noncomputable abbrev qz8 := qz343

noncomputable abbrev qz9 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz894 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 454159 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz631 := qz894

noncomputable abbrev qz344 := qz631

noncomputable abbrev qz10 := qz344

noncomputable abbrev qz632 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz8 qz9))

noncomputable def Ns186p68 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) (@HMul.hMul Real Real Real qz5 qz632 (Zeta.RiemannSiegel.correction qz10)) 34778261 67108864 50057 33554432 19368649235776282791 147573952589676412928 1308925416801214079 147573952589676412928000 Ns186p67 

noncomputable def Ns186p69 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin BSN.quadSignPos 7 8 454159 1000 127 134217728 67108864 2251799813685248 Bool.false 99932830475 1771 279097919 60 47453128 8 

noncomputable def Ns186p70 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 454159 1000 44 88 134217728 67108864 2251799813685248 Bool.false 99932830475 1771 

noncomputable def Ns186p71 := Ns186p70 240485871 61 54794152 8 261175631 61 50729528 8 Bool.true 134522948 66650 Bool.true 9528790 Bool.true 129506080 7074237752028440 1 Bool.false 133879621 Bool.false Bool.false 76437370 Bool.false Bool.true 50976221 

noncomputable def Ns186p72 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 454159 1000 73 8 134217728 67108864 2251799813685248 Bool.false 99932830475 1771 

noncomputable def Ns186p73 := Ns186p72 186065264 60 67108856 8 216015088 60 60023992 8 Bool.true 145075463 39141 Bool.false 39120110 Bool.false 141004410 7074237752028440 1 Bool.false 38568560 Bool.true Bool.false 66717098 Bool.false Bool.true 134522948 

noncomputable def Ns186p74 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 454159 1000 273 156 134217728 67108864 2251799813685248 Bool.false 99932830475 1771 

noncomputable def Ns186p75 := Ns186p74 93032624 60 94906264 8 147453232 60 77490640 16 Bool.true 134217720 1836 Bool.false 124988033 Bool.false 76338678 7074237752028440 1 Bool.false 107690494 Bool.true Bool.false 113087219 Bool.false Bool.true 145075463 

noncomputable def Ns186p76 := nat_lit 1059277407687923438438187454748063349457064528121589049791 

noncomputable def Ns186p77 := nat_lit 1422693686398748389042812827373023766996595922436096000 

noncomputable def Ns186p78 := nat_lit 9274322541723626034831843903520000 

noncomputable def Ns186p79 := nat_lit 25272116602059717909917197207168438080 

noncomputable abbrev qz11 := (@Eq.refl Real qz341)

noncomputable def Ns186p80 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 454159 1000 825042589124 16000000 908318 4000 2000 Ns186p78 Ns186p79 qz11 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns186p81 := nat_lit 338968770460135500300219985519380271826260648998908495933120 

noncomputable abbrev qz895 := (@instHSub Real Real.instSub)

noncomputable abbrev qz633 := qz895

noncomputable abbrev qz345 := qz633

noncomputable abbrev qz12 := qz345

noncomputable abbrev qz346 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz347 := (@HMul.hMul Real Real Real qz628 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz348 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz634 := (Real.log (Enclosure.sfrac Bool.false 825042589124 16000000))

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 454159 4000) qz634) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 908318))))))

noncomputable abbrev qz635 := (Enclosure.sfrac Bool.false 454159 2000)

noncomputable abbrev qz349 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz13 qz635) (@HMul.hMul Real Real Real qz5 qz635 (Real.log Real.pi)))

noncomputable def Ns186p82 := @Enclosure.Real.IsNear.addLit_ft_p qz349 (Enclosure.sfrac Bool.true Ns186p78 Ns186p79) 13412764069941461175639 18014398509481984000 5401138450373799 409600000000000000000 Ns186p78 Ns186p79 0 1 Ns186p81 

noncomputable def Ns186p83 := nat_lit 900115359833788005997237764096000 

noncomputable abbrev qz350 := (@HSub.hSub Real Real Real qz12 qz13 qz635)

noncomputable abbrev qz351 := (@HMul.hMul Real Real Real qz5 qz635 (Real.log Real.pi))

noncomputable def Ns186p84 := @Enclosure.Real.IsNear.subLit_ff_p qz350 qz351 18095511294285686820183 18014398509481984000 5135101362577 800000000000000000 17444592804999 67108864000 454159 67108864000 Ns186p83 13412764069941461175639 18014398509481984000 

noncomputable def Ns186p85 := nat_lit 36191022588571373640366000 

noncomputable abbrev qz352 := qz635

noncomputable def Ns186p86 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz352 22186211900619601005911 18014398509481984000 5135101362577 800000000000000000 454159 2000 0 1 Ns186p85 18095511294285686820183 18014398509481984000 5135101362577 800000000000000000 

noncomputable def Ns186p87 := nat_lit 49958907824196649461720782044741500928 

noncomputable def Ns186p88 := nat_lit 26235144756741606209486848 

noncomputable def Ns186p89 := nat_lit 2417851639229258349412352 

noncomputable def Ns186p90 := nat_lit 207973572624665683199690194527594740856878809447753709701533065682512133340720082482087137145730438571913389671742309814763520 

noncomputable def Ns186p91 := nat_lit 3550544147471439469191024545983692754379718721913860855276412237323483867843116295783592985416821016269258382775075292053504 

noncomputable def Ns186p92 := nat_lit 5722086738950500790947465715751606242462353729359577405217987868784896649068788301947224175466997573862172453183160320 

noncomputable def Ns186p93 := BSN.log_dyadic_bound 300754589124 1349330589124 6 5 Ns186p90 67108864 18000000 Ns186p91 Ns186p92 30426746 1650085178248 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 300754589124) (BSN.artanhQ 1349330589124) 0 5 Ns186p91 Ns186p90 Ns186p92 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz353 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns186p94 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 454159 4000) qz634 454159 4000 0 1 48866765120516729 4503599627370496 100000027 1800000000000000 22193281180368757125911 18014398509481984000 45415912262293 7200000000000000000 (Enclosure.Real.IsNear.const Bool.false 454159 4000) (BSN.isNear_log_sfrac 825042589124 16000000 48866765120516729 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 825042589124) qz353)) Bool.false Ns186p88 Ns186p89 1000000270000000 18000000000000000000000 48866765120516729 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 825042589124 16000000 15 1650085178248 1048576000000 30426746 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns186p93 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p95 := BSN.arctan_dyadic_bound_f 1000 908318 1 0 8388608 2250000 0 1 1 0 1 1 9235 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 908318) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 908318) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz14 := qz347

noncomputable abbrev qz15 := qz348

noncomputable abbrev qz354 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz16 := (@Enclosure.Real.IsNear.mulLit_ff qz354 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz355 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 908318)))

noncomputable def Ns186p96 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz355 884279719003555 562949953421312 1 2000000000000000 9235 8388608 1 2250000 7412677082251127685120 883659968644515 562949953421312 8000000009 18000000000000000 qz16 (Ns186p95 rfl) rfl rfl 

noncomputable abbrev qz17 := qz346

noncomputable abbrev qz356 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns186p97 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 454159 4000) qz634) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz355)) 22193281180368757125911 18014398509481984000 45415912262293 7200000000000000000 883659968644515 2251799813685248 8000000009 72000000000000000 Ns186p87 22186211900619601005911 18014398509481984000 5135101362577 800000000000000000 (Ns186p94 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz355) 1 4 0 1 883659968644515 562949953421312 8000000009 18000000000000000 883659968644515 2251799813685248 8000000009 72000000000000000 qz356 Ns186p96 rfl) 

noncomputable def Ns186p98 := @Ns186p82 Ns186p76 Ns186p77 5401138450373799 409600000000000000000 (@Ns186p84 5401138450373799 409600000000000000000 (Ns186p86 (Ns186p97 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 454159 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz352 (Real.log Real.pi) 454159 2000 0 1 38410761 33554432 1 33554432 17444592804999 67108864000 454159 67108864000 (Enclosure.Real.IsNear.const Bool.false 454159 2000) RS187to204.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns186p78 Ns186p79) 

noncomputable abbrev qz357 := (@instHAdd Real Real.instAdd)

noncomputable def Ns186p99 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns186p76 Ns186p77 5401138450373799 409600000000000000000 12491603809 16777216 111 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz357 qz349 (Enclosure.sfrac Bool.true Ns186p78 Ns186p79)) Bool.false Ns186p76 Ns186p77 5401138450373799 409600000000000000000 Ns186p80 (Ns186p98 rfl rfl)) 

noncomputable def Ns186p100 := nat_lit 3798312273124512925483008 

noncomputable def Ns186p101 := nat_lit 857463073390863937500826548120023451419154255766386188076804060700206756791037509023979467088142452898342333516784728880538215174373376 

noncomputable def Ns186p102 := nat_lit 16860812360175734222210805034837902731874731588140993779854824115686058269364094835627812361599730584878593258197117225559879026789580800 

noncomputable def Ns186p103 := nat_lit 611688611895388051221923761944960104481303093462814793506316398583448333498430349048312270210007538462962761564511019586474213376 

noncomputable def Ns186p104 := nat_lit 4281985832600757662060411377129428832349782403599607400092094235768950381980152096903158874139945650538676502772321928123774311476494336 

noncomputable def Ns186p105 := nat_lit 590128432606150697777378176219326595615615605584934782294918844049012039427743319246973432655990570470750764036899102894595765937635328000 

noncomputable abbrev qz358 := (BSN.sinEvenQ 34359738368)

noncomputable abbrev qz359 := (BSN.sinOddQ 34359738368)

noncomputable def Ns186p106 := BSN.sin_dyadic_bound_f 53977263876 34359738368 4 3 16777216 4504395 Ns186p101 Ns186p102 Ns186p103 Ns186p104 Ns186p105 Ns186p103 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53977263876) qz358 0 3 Ns186p101 Ns186p102 Ns186p103 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53977263876) qz359 0 3 Ns186p104 Ns186p105 Ns186p103 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz360 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable abbrev qz361 := (@Nat.cast Real Real.instNatCast Ns186p89)

noncomputable def Ns186p107 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12491603809) qz360) Bool.false 12491603809 16777216 111 8388608 Bool.true 16777215 16777216 1 2250000 (Ns186p99 rfl) (Enclosure.sfrac_false_div 12491603809 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12491603809) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p100) qz361) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 118 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 12491603809 16777216 226375608064910080 72057594037927936 118 Ns186p100 Ns186p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns186p100 Ns186p89 53977263876 34359738368 4504395 4500000 (Ns186p106 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p108 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns186p76 Ns186p77 5401138450373799 409600000000000000000 99932830475 134217728 1771 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz357 qz349 (Enclosure.sfrac Bool.true Ns186p78 Ns186p79)) Bool.false Ns186p76 Ns186p77 5401138450373799 409600000000000000000 Ns186p80 (Ns186p98 rfl rfl)) 

noncomputable def Ns186p109 := Ns186p75 39141 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 273 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 107690494 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 156 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 113087219 134217728) qz11 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 16777215 16777216 16133663 1179648000000 134217720 134217728 1836 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 16777215 16777216 16133663 1179648000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 16777215 16777216 258138608 18874368000000 16777215 16777216 16133663 1179648000000 (Ns186p107 rfl rfl) rfl)) rfl) (Ns186p108 rfl) RS187to204.d7 

noncomputable def Ns186p110 := nat_lit 239553787620077192617356242846488501189922928063222910068830683812865 

noncomputable def Ns186p111 := nat_lit 38215724400686031908940493885850326479880652218951261491964367528263680 

noncomputable def Ns186p112 := nat_lit 59559009586665378621248530173995846125675629945673866039890826241 

noncomputable def Ns186p113 := nat_lit 627306348227538046241974805072902462222737527240909863920968158172161 

noncomputable def Ns186p114 := nat_lit 700621614012577251663909054573922652131145290680773127352680071351500800 

noncomputable abbrev qz362 := (BSN.sinEvenQ 134217728)

noncomputable abbrev qz363 := (BSN.sinOddQ 134217728)

noncomputable def Ns186p115 := BSN.sin_dyadic_bound_f 124988033 134217728 3 2 134217728 67108864 Ns186p110 Ns186p111 Ns186p112 Ns186p113 Ns186p114 Ns186p112 107690494 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 124988033) qz362 0 2 Ns186p110 Ns186p111 Ns186p112 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 124988033) qz363 0 2 Ns186p113 Ns186p114 Ns186p112 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p116 := nat_lit 18516308354252603464002564829086227016289706814142294843185350697216 

noncomputable def Ns186p117 := nat_lit 4246191600076225767660054876205591831097850246550140165773818614251520 

noncomputable def Ns186p118 := nat_lit 1153339265986793131566099996370453902037380636292693190711828736 

noncomputable def Ns186p119 := nat_lit 55546618384225836805744562287265940141065045681154299143174628434176 

noncomputable def Ns186p120 := nat_lit 191078622003430159544702469429251632399403261094756307459821837641318400 

noncomputable abbrev qz364 := (BSN.cosEvenQ 134217728)

noncomputable abbrev qz365 := (BSN.cosOddQ 134217728)

noncomputable def Ns186p121 := BSN.cos_dyadic_bound_f 76338678 134217728 3 2 134217728 67108864 Ns186p116 Ns186p117 Ns186p118 Ns186p119 Ns186p120 Ns186p118 113087219 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 76338678) qz364 0 2 Ns186p116 Ns186p117 Ns186p118 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 76338678) qz365 0 2 Ns186p119 Ns186p120 Ns186p118 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p122 := nat_lit 2342072146314937709715026410000 

noncomputable def Ns186p123 := nat_lit 38942226439011207213978722469150720 

noncomputable def Ns186p124 := nat_lit 272595585073078450497851057284055040 

noncomputable def Ns186p125 := BSN.sin_dyadic_bound_f 39120110 134217728 2 1 134217728 67108864 Ns186p122 Ns186p123 Ns186p122 Ns186p122 Ns186p124 Ns186p122 38568560 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 39120110) qz362 0 1 Ns186p122 Ns186p123 Ns186p122 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 39120110) qz363 0 1 Ns186p122 Ns186p124 Ns186p122 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p126 := nat_lit 831477271241628160034883498867915815497111426082620016846834690408459941133619536577700783364057664000000 

noncomputable def Ns186p127 := nat_lit 16370259324565974446773555668639125346849261288577159159185037526614652227207809159774062022111344040345600 

noncomputable def Ns186p128 := nat_lit 61772097513348401594819253733196123587500194216534128006551891095610463407263290462881000000000000 

noncomputable def Ns186p129 := nat_lit 5041858576470899163258376401991502698593251008118657074838360573999269322830809595453228052318438361600000 

noncomputable def Ns186p130 := nat_lit 1489693598535503674656393565846160406563282777260521483485838414921933352675910633539439644012132307671449600 

noncomputable def Ns186p131 := BSN.cos_dyadic_bound_f 141004410 134217728 4 3 134217728 67108864 Ns186p126 Ns186p127 Ns186p128 Ns186p129 Ns186p130 Ns186p128 66717098 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 141004410) qz364 0 3 Ns186p126 Ns186p127 Ns186p128 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 141004410) qz365 0 3 Ns186p129 Ns186p130 Ns186p128 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p132 := Ns186p73 66650 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 73 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 38568560 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 8 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66717098 134217728) qz11 rfl rfl (Ns186p109 RS187to204.d9 RS187to204.d11 RS187to204.d13 RS187to204.d17 (Ns186p115 rfl rfl) (Ns186p121 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns186p108 rfl) RS187to204.d19 RS187to204.d21 RS187to204.d23 RS187to204.d25 RS187to204.d17 (Ns186p125 rfl rfl) (Ns186p131 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns186p133 := nat_lit 8244247542391068378268810000 

noncomputable def Ns186p134 := nat_lit 7788445287802241442795744493830144 

noncomputable def Ns186p135 := nat_lit 116826679317033621641936167407452160 

noncomputable def Ns186p136 := BSN.cos_dyadic_bound_f 9528790 134217728 2 1 134217728 67108864 Ns186p133 Ns186p134 Ns186p133 Ns186p133 Ns186p135 Ns186p133 133879621 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 9528790) qz364 0 1 Ns186p133 Ns186p134 Ns186p133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 9528790) qz365 0 1 Ns186p133 Ns186p135 Ns186p133 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p137 := nat_lit 153438189003908136719395180626736014400187001539808700878605516800000 

noncomputable def Ns186p138 := nat_lit 79126373889405827698315279906528438608494181637644982681600000000 

noncomputable def Ns186p139 := nat_lit 460156314263945598502788911320394986323344016256150812670453350400000 

noncomputable def Ns186p140 := BSN.cos_dyadic_bound_f 129506080 134217728 3 2 134217728 67108864 Ns186p137 Ns186p117 Ns186p138 Ns186p139 Ns186p120 Ns186p138 76437370 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 129506080) qz364 0 2 Ns186p137 Ns186p117 Ns186p138 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 129506080) qz365 0 2 Ns186p139 Ns186p120 Ns186p138 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p141 := Ns186p71 89843 BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133879621 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 88 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 76437370 134217728) qz11 rfl rfl (Ns186p132 rfl rfl) (Ns186p108 rfl) RS187to204.d27 RS187to204.d29 RS187to204.d31 RS187to204.d33 RS187to204.d17 (Ns186p136 rfl rfl) (Ns186p140 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns186p142 := nat_lit 4778573960295225283730712890625 

noncomputable def Ns186p143 := BSN.sin_dyadic_bound_f 46754625 134217728 2 1 134217728 67108864 Ns186p142 Ns186p123 Ns186p142 Ns186p142 Ns186p124 Ns186p142 45814755 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 46754625) qz362 0 1 Ns186p142 Ns186p123 Ns186p142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 46754625) qz363 0 1 Ns186p142 Ns186p124 Ns186p142 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p144 := Ns186p69 Bool.true 50976221 89843 Bool.true 46754625 7074237752028440 1 Bool.false 45814755 Bool.false Bool.true 34778261 100114 BSN.abs_quadSignPos (BSN.cos_quad_nat3 127 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 45814755 134217728) qz11 rfl (Ns186p141 rfl) (Ns186p108 rfl) RS187to204.d35 RS187to204.d37 RS187to204.d17 (Ns186p143 rfl rfl) rfl 

noncomputable def Ns186p145 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) 34778261 134217728 100114 134217728 34778261 134217728 100114 134217728 9335718350422016 34778261 67108864 50057 33554432 (Ns186p144 rfl rfl rfl rfl) 

noncomputable def Ns186p146 := @Enclosure.Real.IsNear.mulLit_ff qz632 (Zeta.RiemannSiegel.correction qz10) 1438477 4194304 1 8388608 13464691639683 35184372088832 6789433990007 263882790666240000 19368649235776282791 147573952589676412928 

noncomputable abbrev qz636 := (@HPow.hPow Real Real Real qz7 qz8 qz9)

noncomputable def Ns186p147 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz636 1 1 0 1 1438477 4194304 1 8388608 1438477 4194304 1 8388608 

noncomputable abbrev qz366 := (@Enclosure.Real.IsNear.of_eq qz8 (@HMul.hMul Real Real Real qz5 qz4 qz3) Bool.false 1212684916143 16777216000 454159 16777216000 (BSN.t_div_two_pi_mk qz4 454159 1000 qz11) (@Enclosure.Real.IsNear.mulLit_ff qz4 qz3 454159 1000 0 1 2670177 16777216 1 16777216 1212684916143 16777216000 454159 16777216000 (Enclosure.Real.IsNear.const Bool.false 454159 1000) RS187to204.d40 rfl))

noncomputable def Ns186p148 := @Enclosure.Real.IsNear.sqrt_image qz8 1212684916143 16777216000 454159 16777216000 71318772 71318800 8388608 qz366 

noncomputable abbrev qz896 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 454159 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz637 := qz896

noncomputable abbrev qz367 := qz637

noncomputable abbrev qz18 := qz367

noncomputable def Ns186p149 := @Enclosure.Real.IsNear.sqrt_image qz18 35659393 4194304 7 4194304 24459460 24459466 8388608 (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 142637572 16777216 28 16777216 35659393 4194304 7 4194304 (Ns186p148 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz638 := (Real.sqrt qz896)

noncomputable abbrev qz368 := qz638

noncomputable abbrev qz19 := qz368

noncomputable def Ns186p150 := @Enclosure.Real.IsNear.inv_image qz19 24459463 8388608 3 8388608 2876953 2876955 8388608 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 48918926 16777216 6 16777216 24459463 8388608 3 8388608 (Ns186p149 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns186p151 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz19) Bool.false 5753908 16777216 2 16777216 1438477 4194304 1 8388608 (Ns186p150 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz20 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz344))

noncomputable abbrev qz639 := (@HMul.hMul Real Real Real qz891 qz894 qz894)

noncomputable abbrev qz640 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz369 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz639 qz631) qz640)

noncomputable abbrev qz21 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz369))

noncomputable def Ns186p152 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz10) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz20) qz21) Bool.false 13464691639683 

noncomputable def Ns186p153 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz20) qz21 4194591 4194304 93 

noncomputable abbrev qz641 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz20))

noncomputable def Ns186p154 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz20) (@Neg.neg Real Real.instNeg qz641) Bool.true 4194591 4194304 93 8388608 (BSN.inv_eq_neg_inv_neg qz20) 

noncomputable def Ns186p155 := @Enclosure.Real.IsNear.recentre' qz641 Bool.false 16778364 16777216 186 16777216 4194591 4194304 

noncomputable def Ns186p156 := @Enclosure.Real.IsNear.recentre' qz20 Bool.true 16776068 16777216 415027216 37748736000000 4194017 4194304 25939201 2359296000000 

noncomputable abbrev qz22 := (@HMul.hMul Real Real Real qz342 qz340 qz344)

noncomputable def Ns186p157 := @Enclosure.Real.IsNear.cos_image qz22 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3306465) (@Nat.cast Real Real.instNatCast 1048576)) Bool.false 3306465 1048576 177 16777216 Bool.true 16776068 16777216 1 

noncomputable def Ns186p158 := nat_lit 188902527881389795494893681 

noncomputable def Ns186p159 := nat_lit 18014398509481984000000000000000 

noncomputable def Ns186p160 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz10 884279719003555 140737488355328 1 500000000000000 2104961 4194304 7 4194304 1861374321593442136355 590295810358705651712 Ns186p158 

noncomputable def Ns186p161 := @Enclosure.Real.IsNear.subLit_ff_p qz18 qz1 35659393 4194304 7 4194304 8 1 0 1 2104961 2104961 4194304 7 

noncomputable abbrev qz370 := (Enclosure.Real.IsNear.const Bool.false 8 1)

noncomputable def Ns186p162 := @Ns186p161 4194304 (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 142637572 16777216 28 16777216 35659393 4194304 7 4194304 (Ns186p148 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns186p163 := @Enclosure.Real.IsNear.recentre' qz22 Bool.false 1861374321593442136355 590295810358705651712 Ns186p158 Ns186p159 3306465 1048576 177 16777216 (@Ns186p160 Ns186p159 RS187to204.d39 (Ns186p162 rfl rfl) rfl) 

noncomputable abbrev qz371 := (BSN.cosEvenQ 34359738368)

noncomputable abbrev qz372 := (BSN.cosOddQ 34359738368)

noncomputable def Ns186p164 := BSN.cos_dyadic_bound_f 401943483 34359738368 1 0 16777216 4504395 0 1 1 0 1 1 16776068 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 401943483) qz371 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 401943483) qz372 0 0 rfl) rfl rfl 

noncomputable def Ns186p165 := @Ns186p157 2250000 (Ns186p163 rfl) (Enclosure.sfrac_false_div 3306465 1048576) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3306465) (@Nat.cast Real Real.instNatCast 1048576)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1767766136692481720320) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false 16776068 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 3306465 1048576 226375608064910080 72057594037927936 0 1767766136692481720320 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16776068 16777216 1767766136692481720320 151115727451828646838272 401943483 34359738368 4504395 4500000 (Ns186p164 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p166 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz20) 4194017 4194304 25939201 2359296000000 8389089 8389275 8388608 (@Enclosure.Real.IsNear.neg qz20 Bool.true 4194017 4194304 25939201 2359296000000 (Ns186p156 (Ns186p165 rfl rfl) rfl)) 

noncomputable def Ns186p167 := Ns186p154 (@Enclosure.Real.IsNear.neg qz641 Bool.false 4194591 4194304 93 8388608 (@Ns186p155 93 8388608 (Ns186p166 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p168 := @Enclosure.Real.IsNear.recentre' qz21 Bool.true 3210013 8388608 

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz342 qz340 qz369)

noncomputable def Ns186p169 := @Enclosure.Real.IsNear.cos_image qz23 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32941621)) qz360) Bool.true 32941621 16777216 

noncomputable def Ns186p170 := nat_lit 4861325242451909812279108445 

noncomputable def Ns186p171 := nat_lit 2475880078570760549798248448 

noncomputable def Ns186p172 := nat_lit 317516171699891679577034128939877 

noncomputable def Ns186p173 := @Enclosure.Real.IsNear.recentre' qz23 Bool.true Ns186p170 Ns186p171 Ns186p172 

noncomputable def Ns186p174 := nat_lit 15111572745182864683827200000000000000 

noncomputable abbrev qz24 := qz369

noncomputable def Ns186p175 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz24 884279719003555 140737488355328 1 500000000000000 5497497158399 

noncomputable abbrev qz373 := (@HSub.hSub Real Real Real qz633 qz639 qz631)

noncomputable abbrev qz25 := qz373

noncomputable abbrev qz374 := qz640

noncomputable abbrev qz26 := qz374

noncomputable def Ns186p176 := @Enclosure.Real.IsNear.subLit_tf qz25 qz26 4397985530623 17592186044416 58829631 17592186044416 1 16 

noncomputable abbrev qz375 := qz639

noncomputable abbrev qz27 := qz375

noncomputable def Ns186p177 := @Enclosure.Real.IsNear.subLit_ff_n qz27 qz10 4430860811521 17592186044416 29469503 17592186044416 2104961 4194304 7 4194304 

noncomputable def Ns186p178 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz10 2104961 4194304 7 4194304 2104961 4194304 7 4194304 4430860811521 17592186044416 

noncomputable def Ns186p179 := nat_lit 148831473758586876779423415065210873241751752253219570951609081585878498308507679567259678008721 

noncomputable def Ns186p180 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600 

noncomputable def Ns186p181 := nat_lit 1632824825755218606920095423316081764547881942203395535433843624488962750558746854727869841 

noncomputable def Ns186p182 := nat_lit 897624117958881591990262969523755521707421281568642534640038840395404717825599980393329986889105 

noncomputable def Ns186p183 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600 

noncomputable abbrev qz642 := (BSN.cosEvenQ 16777216)

noncomputable def Ns186p184 := BSN.cos_dyadic_bound_t 32941621 16777216 4 3 8388608 2250000 Ns186p179 Ns186p180 Ns186p181 Ns186p182 Ns186p183 Ns186p181 3210013 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32941621) qz642 0 3 Ns186p179 Ns186p180 Ns186p181 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32941621) (BSN.cosOddQ 16777216) 0 3 Ns186p182 Ns186p183 Ns186p181 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz376 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns186p185 := @Ns186p168 811027216 37748736000000 3210013 8388608 50689201 2359296000000 (@Ns186p169 353 16777216 Bool.true 3210013 8388608 1 2250000 (@Ns186p173 Ns186p174 32941621 16777216 353 16777216 (@Ns186p175 17592186044416 58829631 17592186044416 Ns186p170 Ns186p171 Ns186p172 Ns186p174 RS187to204.d39 (@Ns186p176 0 1 87959954534384 5497497158399 17592186044416 58829631 17592186044416 (@Ns186p177 18446488303034171392 4397985530623 17592186044416 58829631 17592186044416 (@Ns186p178 29469503 17592186044416 (Ns186p162 rfl rfl) (Ns186p162 rfl rfl) rfl) (Ns186p162 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32941621 16777216) (BSN.cos_neg_of_bound 32941621 16777216 Bool.true 3210013 8388608 1 2250000 (Ns186p184 rfl rfl)) rfl rfl) 

noncomputable abbrev qz28 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 8) (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 8 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1))

noncomputable def Ns186p186 := @Ns186p146 1308925416801214079 147573952589676412928000 (Ns186p147 qz28 (@Enclosure.Real.IsNear.of_eq qz636 (@Inv.inv Real Real.instInv qz19) Bool.false 1438477 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz8 (BSN.t_div_two_pi_nonneg qz4 454159 1000 qz11)) Ns186p151) rfl) (@Ns186p152 35184372088832 6789433990007 263882790666240000 (BSN.correction_mk qz10 (BSN.cos_two_pi_p_ne_zero_mk qz4 454159 1000 8 qz11 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 454159 1000 8 qz11 rfl rfl rfl))) (@Ns186p153 8388608 3210013 8388608 50689201 2359296000000 13464691639683 35184372088832 6789433990007 263882790666240000 Ns186p167 (Ns186p185 rfl) rfl)) 

noncomputable def Ns186p187 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 95846853962433437863 147573952589676412928 221461939623134142079 147573952589676412928000 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) (@HMul.hMul Real Real Real qz5 qz632 (Zeta.RiemannSiegel.correction qz10))) Bool.true 95846853962433437863 147573952589676412928 221461939623134142079 147573952589676412928000 (BSN.hardyZApproximantRS₀_eq qz4 8 (@BSN.floor_sqrt_eq_dec qz4 454159 1000 8 qz11 rfl rfl rfl)) (@Ns186p68 95846853962433437863 147573952589676412928 221461939623134142079 147573952589676412928000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 8)) Bool.true 34778261 67108864 50057 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) (Ns186p145 (Ns186p144 rfl rfl rfl rfl) rfl rfl)) (Ns186p186 rfl) rfl rfl)) 

theorem RS187to204.d41 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 95846853962433437863 147573952589676412928 221461939623134142079 147573952589676412928000 := Ns186p187 

theorem RS187to204.d42 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS187to204.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS187to204.d3 a b h)) 

noncomputable def Ns186p188 := nat_lit 18446744073709551616000000 

noncomputable def Ns186p189 := nat_lit 28878773037918014989412597760 

noncomputable abbrev qz897 := (Enclosure.sfrac Bool.false 455626 1000)

noncomputable abbrev qz643 := qz897

noncomputable abbrev qz377 := qz643

noncomputable abbrev qz29 := qz377

noncomputable abbrev qz898 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 455626 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz644 := qz898

noncomputable abbrev qz378 := qz644

noncomputable abbrev qz30 := qz378

noncomputable abbrev qz899 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 455626 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz645 := qz899

noncomputable abbrev qz379 := qz645

noncomputable abbrev qz31 := qz379

noncomputable abbrev qz646 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz30 qz9))

noncomputable def Ns186p190 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz29) qz29 8) (@HMul.hMul Real Real Real qz5 qz646 (Zeta.RiemannSiegel.correction qz31)) 26663865 16777216 12555 8388608 154993686498537251625 1180591620717411303424 166068891306902209839 Ns186p188 Ns186p189 

noncomputable def Ns186p191 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz29) qz29 Real.sin BSN.quadSignPos 7 8 455626 1000 127 134217728 67108864 2251799813685248 Bool.false 100354405955 1777 279097919 60 47453128 8 

noncomputable def Ns186p192 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz29) qz29 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 455626 1000 43 88 134217728 67108864 2251799813685248 Bool.false 100354405955 1777 

noncomputable def Ns186p193 := Ns186p192 240485871 61 54794152 8 261175631 61 50729528 8 Bool.false 5519885 66868 Bool.true 151574797 Bool.true 91075251 7074237752028440 1 Bool.false 121349194 Bool.false Bool.false 104485169 Bool.false Bool.false 94552158 

noncomputable def Ns186p194 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz29) qz29 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 455626 1000 73 9 134217728 67108864 2251799813685248 Bool.false 100354405955 1777 

noncomputable def Ns186p195 := Ns186p194 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 87051948 39270 Bool.false 187737848 Bool.false 34857042 7074237752028440 1 Bool.false 132236341 Bool.true Bool.false 34466528 Bool.true Bool.false 5519885 

noncomputable def Ns186p196 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz29) qz29 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 455626 1000 274 157 134217728 67108864 2251799813685248 Bool.false 100354405955 1777 

noncomputable def Ns186p197 := Ns186p196 93032624 60 94906264 8 147453232 60 77490640 16 Bool.false 134217712 1844 Bool.false 199255939 Bool.false 70771552 7074237752028440 1 Bool.false 11558440 Bool.true Bool.false 67537360 Bool.true Bool.false 87051948 

noncomputable def Ns186p198 := nat_lit 8472887290485268112302983676809316097921513043368933561 

noncomputable def Ns186p199 := nat_lit 11331955691423490994674526593192797979006260477952000 

noncomputable def Ns186p200 := nat_lit 9425080246699603379920772500480000 

noncomputable def Ns186p201 := nat_lit 25765884155188111878202395458158202880 

noncomputable abbrev qz380 := (@Eq.refl Real qz643)

noncomputable abbrev qz32 := qz380

noncomputable def Ns186p202 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz29 455626 1000 830381207504 16000000 911252 4000 2000 Ns186p200 Ns186p201 qz32 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns186p203 := nat_lit 173524731709138290939965105701054793685432587128195759329280 

noncomputable abbrev qz647 := (Real.log (Enclosure.sfrac Bool.false 830381207504 16000000))

noncomputable abbrev qz33 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 455626 4000) qz647) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 911252))))))

noncomputable abbrev qz648 := (Enclosure.sfrac Bool.false 455626 2000)

noncomputable abbrev qz381 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz33 qz648) (@HMul.hMul Real Real Real qz5 qz648 (Real.log Real.pi)))

noncomputable def Ns186p204 := @Enclosure.Real.IsNear.addLit_ft_p qz381 (Enclosure.sfrac Bool.true Ns186p200 Ns186p201) 6734673475886672626781 9007199254740992000 2709218955024493 204800000000000000000 Ns186p200 Ns186p201 0 1 Ns186p203 

noncomputable def Ns186p205 := nat_lit 225978143188842996361584443392000 

noncomputable abbrev qz382 := (@HSub.hSub Real Real Real qz12 qz33 qz648)

noncomputable abbrev qz383 := (@HMul.hMul Real Real Real qz5 qz648 (Real.log Real.pi))

noncomputable def Ns186p206 := @Enclosure.Real.IsNear.subLit_ff_p qz382 qz383 9083610067299660317789 9007199254740992000 2575700683489 400000000000000000 8750470695693 33554432000 227813 33554432000 Ns186p205 6734673475886672626781 9007199254740992000 

noncomputable def Ns186p207 := nat_lit 3633444026919864127115600 

noncomputable abbrev qz384 := qz648

noncomputable def Ns186p208 := @Enclosure.Real.IsNear.subLit_ff_p qz33 qz384 2227113430223993985657 1801439850948198400 2575700683489 400000000000000000 455626 2000 0 1 Ns186p207 9083610067299660317789 9007199254740992000 2575700683489 400000000000000000 

noncomputable def Ns186p209 := nat_lit 5015013607234303228849688712824487936 

noncomputable def Ns186p210 := nat_lit 26250739605358482649251840 

noncomputable def Ns186p211 := nat_lit 216350092356222940983330487458915707963469452782649179959004402176560600106607977984929751706784689977088247168004745875947520 

noncomputable def Ns186p212 := nat_lit 3799012822394876663768083364719279538633864604149201487515443237209595669430073788353124276271027886244290127349880983650304 

noncomputable def Ns186p213 := nat_lit 6822895686659907591021538948747556873767376265186779559781481207341933209161654885948613206363011396925007447006904320 

noncomputable def Ns186p214 := BSN.log_dyadic_bound 306093207504 1354669207504 6 5 Ns186p211 67108864 18000000 Ns186p212 Ns186p213 30859590 1660762415008 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 306093207504) (BSN.artanhQ 1354669207504) 0 5 Ns186p212 Ns186p211 Ns186p213 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns186p215 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 455626 4000) qz647 455626 4000 0 1 48895812789645945 4503599627370496 100000027 1800000000000000 2227820359809522333657 1801439850948198400 22781306150951 3600000000000000000 (Enclosure.Real.IsNear.const Bool.false 455626 4000) (BSN.isNear_log_sfrac 830381207504 16000000 48895812789645945 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 830381207504) qz353)) Bool.false Ns186p210 Ns186p89 1000000270000000 18000000000000000000000 48895812789645945 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 830381207504 16000000 15 1660762415008 1048576000000 30859590 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns186p214 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p216 := BSN.arctan_dyadic_bound_f 1000 911252 1 0 8388608 2250000 0 1 1 0 1 1 9205 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 911252) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 911252) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz385 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 911252)))

noncomputable def Ns186p217 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz385 884279719003555 562949953421312 1 2000000000000000 9205 8388608 1 2250000 7412693970749730324480 883661981910435 562949953421312 8000000009 18000000000000000 qz16 (Ns186p216 rfl) rfl rfl 

noncomputable def Ns186p218 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 455626 4000) qz647) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz385)) 2227820359809522333657 1801439850948198400 22781306150951 3600000000000000000 883661981910435 2251799813685248 8000000009 72000000000000000 Ns186p209 2227113430223993985657 1801439850948198400 2575700683489 400000000000000000 (Ns186p215 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz385) 1 4 0 1 883661981910435 562949953421312 8000000009 18000000000000000 883661981910435 2251799813685248 8000000009 72000000000000000 qz356 Ns186p217 rfl) 

noncomputable def Ns186p219 := @Ns186p204 Ns186p198 Ns186p199 2709218955024493 204800000000000000000 (@Ns186p206 2709218955024493 204800000000000000000 (Ns186p208 (Ns186p218 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 455626 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz384 (Real.log Real.pi) 455626 2000 0 1 38410761 33554432 1 33554432 8750470695693 33554432000 227813 33554432000 (Enclosure.Real.IsNear.const Bool.false 455626 2000) RS187to204.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns186p200 Ns186p201) 

noncomputable def Ns186p220 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz29) Bool.false Ns186p198 Ns186p199 2709218955024493 204800000000000000000 1568037593 2097152 223 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz29) (@HAdd.hAdd Real Real Real qz357 qz381 (Enclosure.sfrac Bool.true Ns186p200 Ns186p201)) Bool.false Ns186p198 Ns186p199 2709218955024493 204800000000000000000 Ns186p202 (Ns186p219 rfl rfl)) 

noncomputable def Ns186p221 := nat_lit 856128131414087239148262228000165089262155960628288372855149890120279264447211242426391652667381453657945906530094255204762805862400000 

noncomputable def Ns186p222 := nat_lit 608841842039765071183288892009338658257639361251159602228641638974319372025858458214683864008314346969573044053344256000000000000 

noncomputable def Ns186p223 := nat_lit 4275327674959716496450722245834987930940333986337299904532324216537473779927294569493014872715446075198680251633308366531368845312000000 

noncomputable def Ns186p224 := BSN.sin_dyadic_bound_f 53956285120 34359738368 4 3 16777216 4504395 Ns186p221 Ns186p102 Ns186p222 Ns186p223 Ns186p105 Ns186p222 16777214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53956285120) qz358 0 3 Ns186p221 Ns186p102 Ns186p222 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53956285120) qz359 0 3 Ns186p223 Ns186p105 Ns186p222 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz649 := (@Nat.cast Real Real.instNatCast 2097152)

noncomputable def Ns186p225 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz29) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1568037593) qz649) Bool.false 1568037593 2097152 223 16777216 Bool.false 16777214 16777216 1 2250000 (Ns186p220 rfl) (Enclosure.sfrac_false_div 1568037593 2097152) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1568037593) qz649) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474604503049748502020096) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 16777214 16777216 118 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q3 1568037593 2097152 226375608064910080 72057594037927936 118 474604503049748502020096 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777214 16777216 474604503049748502020096 302231454903657293676544 53956285120 34359738368 4504395 4500000 (Ns186p224 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p226 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz29) Bool.false Ns186p198 Ns186p199 2709218955024493 204800000000000000000 100354405955 134217728 1777 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz29) (@HAdd.hAdd Real Real Real qz357 qz381 (Enclosure.sfrac Bool.true Ns186p200 Ns186p201)) Bool.false Ns186p198 Ns186p199 2709218955024493 204800000000000000000 Ns186p202 (Ns186p219 rfl rfl)) 

noncomputable def Ns186p227 := Ns186p197 39270 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 274 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 11558440 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 157 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 67537360 134217728) qz32 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 1) Bool.false 8388607 8388608 32407951 2359296000000 134217712 134217728 1844 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz29)) Bool.false 8388607 8388608 32407951 2359296000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz29) qz29) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz29)) Bool.false 16777214 16777216 518527216 37748736000000 8388607 8388608 32407951 2359296000000 (Ns186p225 rfl rfl) rfl)) rfl) (Ns186p226 rfl) RS187to204.d7 

noncomputable def Ns186p228 := nat_lit 3322800520184001123950789562151190251628751330263858892141444490867677476541742087129345729290612396284401 

noncomputable def Ns186p229 := nat_lit 3916835185881603467968221269985543768214570299019282577706524295280330145030630206289724949727566321 

noncomputable def Ns186p230 := nat_lit 20119559257950478925151550626361757631091038444287952048481800532831445621133889181009638329732568384821745 

noncomputable def Ns186p231 := BSN.cos_dyadic_bound_f 199255939 134217728 4 3 134217728 67108864 Ns186p228 Ns186p127 Ns186p229 Ns186p230 Ns186p130 Ns186p229 11558440 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 199255939) qz364 0 3 Ns186p228 Ns186p127 Ns186p229 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 199255939) qz365 0 3 Ns186p230 Ns186p130 Ns186p229 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p232 := nat_lit 24618823739095826587641393110060605066367993056683252231897780060160 

noncomputable def Ns186p233 := nat_lit 629317425487578394626303288035805359555504710902480384563347456 

noncomputable def Ns186p234 := nat_lit 64476852802752565935945682225787621965143558617019437543871559499776 

noncomputable def Ns186p235 := BSN.sin_dyadic_bound_f 70771552 134217728 3 2 134217728 67108864 Ns186p232 Ns186p111 Ns186p233 Ns186p234 Ns186p114 Ns186p233 67537360 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 70771552) qz362 0 2 Ns186p232 Ns186p111 Ns186p233 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 70771552) qz363 0 2 Ns186p234 Ns186p114 Ns186p233 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p236 := nat_lit 6797277592715545276656422103828995501678245989164661322298573575682166847985892864278970768134740268548096 

noncomputable def Ns186p237 := nat_lit 212813371219357667808056223692308629509040396751503069069405487845990478953701519077062806287447472524492800 

noncomputable def Ns186p238 := nat_lit 1916999607554717112540189190265808230137334666198396907415064125978475902928371364251218832833642496 

noncomputable def Ns186p239 := nat_lit 33959818481668470633400787035141616802738823691536728690572051125444413951248023914842581381103654646317056 

noncomputable def Ns186p240 := nat_lit 7448467992677518373281967829230802032816413886302607417429192074609666763379553167697198220060661538357248000 

noncomputable def Ns186p241 := BSN.sin_dyadic_bound_f 187737848 134217728 4 3 134217728 67108864 Ns186p236 Ns186p237 Ns186p238 Ns186p239 Ns186p240 Ns186p238 132236341 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 187737848) qz362 0 3 Ns186p236 Ns186p237 Ns186p238 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 187737848) qz363 0 3 Ns186p239 Ns186p240 Ns186p238 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p242 := nat_lit 1476257506264070375146160775696 

noncomputable def Ns186p243 := BSN.sin_dyadic_bound_f 34857042 134217728 2 1 134217728 67108864 Ns186p242 Ns186p123 Ns186p242 Ns186p242 Ns186p124 Ns186p242 34466528 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 34857042) qz362 0 1 Ns186p242 Ns186p123 Ns186p242 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 34857042) qz363 0 1 Ns186p242 Ns186p124 Ns186p242 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p244 := Ns186p195 66868 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 73 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132236341 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 9 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 34466528 134217728) qz32 rfl rfl (Ns186p227 RS187to204.d9 RS187to204.d11 RS187to204.d13 RS187to204.d17 (Ns186p231 rfl rfl) (Ns186p235 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns186p226 rfl) RS187to204.d19 RS187to204.d21 RS187to204.d23 RS187to204.d25 RS187to204.d17 (Ns186p241 rfl rfl) (Ns186p243 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns186p245 := nat_lit 518278073540525496250901845087290263778459780557952468555724058785825 

noncomputable def Ns186p246 := nat_lit 278622357218343009247853029892530064428172718086581083395667785761 

noncomputable def Ns186p247 := nat_lit 1356943851646832315785008308418315165982130002774878191129970025166881 

noncomputable def Ns186p248 := BSN.sin_dyadic_bound_f 151574797 134217728 3 2 134217728 67108864 Ns186p245 Ns186p111 Ns186p246 Ns186p247 Ns186p114 Ns186p246 121349194 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 151574797) qz362 0 2 Ns186p245 Ns186p111 Ns186p246 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 151574797) qz363 0 2 Ns186p247 Ns186p114 Ns186p246 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p249 := nat_lit 37515014993646027567619753354219471019558048588082504063421695042081 

noncomputable def Ns186p250 := nat_lit 4733724891049100395814371035919349916100684237289158507592852001 

noncomputable def Ns186p251 := nat_lit 112535577531155984502067631320586574358841944395772933873249899422241 

noncomputable def Ns186p252 := BSN.cos_dyadic_bound_f 91075251 134217728 3 2 134217728 67108864 Ns186p249 Ns186p117 Ns186p250 Ns186p251 Ns186p120 Ns186p250 104485169 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 91075251) qz364 0 2 Ns186p249 Ns186p117 Ns186p250 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 91075251) qz365 0 2 Ns186p251 Ns186p120 Ns186p250 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p253 := Ns186p193 90136 BSN.abs_quadSignPos (BSN.cos_quad_nat3 43 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 121349194 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 88 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 104485169 134217728) qz32 rfl rfl (Ns186p244 rfl rfl) (Ns186p226 rfl) RS187to204.d27 RS187to204.d29 RS187to204.d31 RS187to204.d33 RS187to204.d17 (Ns186p248 rfl rfl) (Ns186p252 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns186p254 := nat_lit 1435810385703516011802824605696 

noncomputable def Ns186p255 := BSN.sin_dyadic_bound_f 34615792 134217728 2 1 134217728 67108864 Ns186p254 Ns186p123 Ns186p254 Ns186p254 Ns186p124 Ns186p254 34233313 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 34615792) qz362 0 1 Ns186p254 Ns186p123 Ns186p254 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 34615792) qz363 0 1 Ns186p254 Ns186p124 Ns186p254 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p256 := Ns186p191 Bool.false 94552158 90136 Bool.true 34615792 7074237752028440 1 Bool.false 34233313 Bool.false Bool.false 106655460 100440 BSN.abs_quadSignPos (BSN.cos_quad_nat3 127 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 34233313 134217728) qz32 rfl (Ns186p253 rfl) (Ns186p226 rfl) RS187to204.d35 RS187to204.d37 RS187to204.d17 (Ns186p255 rfl rfl) rfl 

noncomputable def Ns186p257 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 8) 106655460 134217728 100440 134217728 106655460 134217728 100440 134217728 28630107039989760 26663865 16777216 12555 8388608 (Ns186p256 rfl rfl rfl rfl) 

noncomputable def Ns186p258 := @Enclosure.Real.IsNear.mulLit_ff qz646 (Zeta.RiemannSiegel.correction qz31) 2874635 8388608 1 8388608 53917692680475 140737488355328 517296049388141 19791209299968000000 154993686498537251625 1180591620717411303424 

noncomputable abbrev qz650 := (@HPow.hPow Real Real Real qz7 qz30 qz9)

noncomputable def Ns186p259 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz650 1 1 0 1 2874635 8388608 1 8388608 2874635 8388608 1 8388608 

noncomputable def Ns186p260 := @Enclosure.Real.IsNear.sqrt_image qz30 608301032901 8388608000 227813 8388608000 71433864 71433892 8388608 (@Enclosure.Real.IsNear.of_eq qz30 (@HMul.hMul Real Real Real qz5 qz29 qz3) Bool.false 608301032901 8388608000 227813 8388608000 (BSN.t_div_two_pi_mk qz29 455626 1000 qz32) (@Enclosure.Real.IsNear.mulLit_ff qz29 qz3 455626 1000 0 1 2670177 16777216 1 16777216 608301032901 8388608000 227813 8388608000 (Enclosure.Real.IsNear.const Bool.false 455626 1000) RS187to204.d40 rfl)) 

noncomputable abbrev qz900 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 455626 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz651 := qz900

noncomputable abbrev qz386 := qz651

noncomputable abbrev qz34 := qz386

noncomputable def Ns186p261 := @Enclosure.Real.IsNear.sqrt_image qz34 35716939 4194304 7 4194304 24479188 24479194 8388608 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 142867756 16777216 28 16777216 35716939 4194304 7 4194304 (Ns186p260 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns186p262 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz34) 24479191 8388608 3 8388608 2874634 2874636 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz34) Bool.false 48958382 16777216 6 16777216 24479191 8388608 3 8388608 (Ns186p261 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns186p263 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz34)) Bool.false 5749270 16777216 2 16777216 2874635 8388608 1 8388608 (Ns186p262 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz35 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz379))

noncomputable abbrev qz652 := (@HMul.hMul Real Real Real qz891 qz899 qz899)

noncomputable abbrev qz387 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz652 qz645) qz640)

noncomputable abbrev qz36 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz387))

noncomputable def Ns186p264 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz31) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz35) qz36) Bool.false 53917692680475 

noncomputable def Ns186p265 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz35) qz36 16857945 16777216 187 

noncomputable abbrev qz653 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz35))

noncomputable def Ns186p266 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz35) (@Neg.neg Real Real.instNeg qz653) Bool.true 16857945 16777216 187 16777216 (BSN.inv_eq_neg_inv_neg qz35) 

noncomputable def Ns186p267 := @Enclosure.Real.IsNear.recentre' qz653 Bool.false 16857945 16777216 187 16777216 16857945 16777216 

noncomputable def Ns186p268 := @Enclosure.Real.IsNear.recentre' qz35 Bool.true 16696874 16777216 415027216 37748736000000 8348437 8388608 25939201 2359296000000 

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz342 qz340 qz379)

noncomputable def Ns186p269 := @Enclosure.Real.IsNear.cos_image qz37 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1698429) (@Nat.cast Real Real.instNatCast 524288)) Bool.false 1698429 524288 177 16777216 Bool.true 16696874 16777216 1 

noncomputable def Ns186p270 := nat_lit 188902527881884111870924913 

noncomputable def Ns186p271 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz31 884279719003555 140737488355328 1 500000000000000 2162507 4194304 7 4194304 1912261082303220712385 590295810358705651712 Ns186p270 

noncomputable def Ns186p272 := @Enclosure.Real.IsNear.subLit_ff_p qz34 qz1 35716939 4194304 7 4194304 8 1 0 1 2162507 2162507 4194304 7 

noncomputable def Ns186p273 := @Ns186p272 4194304 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 142867756 16777216 28 16777216 35716939 4194304 7 4194304 (Ns186p260 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns186p274 := @Enclosure.Real.IsNear.recentre' qz37 Bool.false 1912261082303220712385 590295810358705651712 Ns186p270 Ns186p159 1698429 524288 177 16777216 (@Ns186p271 Ns186p159 RS187to204.d39 (Ns186p273 rfl rfl) rfl) 

noncomputable def Ns186p275 := nat_lit 128054144488830365941920964829976326001 

noncomputable def Ns186p276 := nat_lit 33451117797795934712303577408972542258970624 

noncomputable def Ns186p277 := nat_lit 501766766966939020684553661134588133884559360 

noncomputable def Ns186p278 := BSN.cos_dyadic_bound_f 3363941307 34359738368 2 1 16777216 4504395 Ns186p275 Ns186p276 Ns186p275 Ns186p275 Ns186p277 Ns186p275 16696874 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 3363941307) qz371 0 1 Ns186p275 Ns186p276 Ns186p275 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 3363941307) qz372 0 1 Ns186p275 Ns186p277 Ns186p275 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p279 := @Ns186p269 2250000 (Ns186p274 rfl) (Enclosure.sfrac_false_div 1698429 524288) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1698429) (@Nat.cast Real Real.instNatCast 524288)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7397385166216660779008) (@Nat.cast Real Real.instNatCast 75557863725914323419136)) 226375608064910080 72057594037927936 Bool.false 16696874 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 1698429 524288 226375608064910080 72057594037927936 0 7397385166216660779008 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16696874 16777216 7397385166216660779008 75557863725914323419136 3363941307 34359738368 4504395 4500000 (Ns186p278 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p280 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz35) 8348437 8388608 25939201 2359296000000 8428879 8429066 8388608 (@Enclosure.Real.IsNear.neg qz35 Bool.true 8348437 8388608 25939201 2359296000000 (Ns186p268 (Ns186p279 rfl rfl) rfl)) 

noncomputable def Ns186p281 := Ns186p266 (@Enclosure.Real.IsNear.neg qz653 Bool.false 16857945 16777216 187 16777216 (@Ns186p267 187 16777216 (Ns186p280 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p282 := @Enclosure.Real.IsNear.recentre' qz36 Bool.true 3198355 8388608 

noncomputable abbrev qz38 := (@HMul.hMul Real Real Real qz342 qz340 qz387)

noncomputable def Ns186p283 := @Enclosure.Real.IsNear.cos_image qz38 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 4114549)) qz649) Bool.true 4114549 2097152 

noncomputable def Ns186p284 := nat_lit 4857602163491339572542449525 

noncomputable def Ns186p285 := nat_lit 321864405647253222535703768578217 

noncomputable def Ns186p286 := @Enclosure.Real.IsNear.recentre' qz38 Bool.true Ns186p284 Ns186p171 Ns186p285 

noncomputable abbrev qz39 := qz387

noncomputable def Ns186p287 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz39 884279719003555 140737488355328 1 500000000000000 5493286862855 

noncomputable abbrev qz388 := (@HSub.hSub Real Real Real qz633 qz652 qz645)

noncomputable abbrev qz40 := qz388

noncomputable def Ns186p288 := @Enclosure.Real.IsNear.subLit_tf qz40 qz26 4393775235079 17592186044416 59635275 17592186044416 1 16 

noncomputable abbrev qz389 := qz652

noncomputable abbrev qz41 := qz389

noncomputable def Ns186p289 := @Enclosure.Real.IsNear.subLit_ff_n qz41 qz31 4676436525049 17592186044416 30275147 17592186044416 2162507 4194304 7 4194304 

noncomputable def Ns186p290 := @Enclosure.Real.IsNear.mulLit_ff qz31 qz31 2162507 4194304 7 4194304 2162507 4194304 7 4194304 4676436525049 17592186044416 

noncomputable def Ns186p291 := nat_lit 2159097692201929479736092673735817087489424343276443065496623318815660892540624372881 

noncomputable def Ns186p292 := nat_lit 3466537250751077332112698720796095110148055492926080949987665366995300109908547993600 

noncomputable def Ns186p293 := nat_lit 23543274390767364388545431020986720574105305556226128680420678476489486774240401 

noncomputable def Ns186p294 := nat_lit 13022063073922869365563420721926540733681804645204702558456608070456298796238195328145 

noncomputable def Ns186p295 := nat_lit 315454889818348037222255583592444655023473049856273366448877548396572310001677867417600 

noncomputable def Ns186p296 := BSN.cos_dyadic_bound_t 4114549 2097152 4 3 8388608 2250000 Ns186p291 Ns186p292 Ns186p293 Ns186p294 Ns186p295 Ns186p293 3198355 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 4114549) (BSN.cosEvenQ 2097152) 0 3 Ns186p291 Ns186p292 Ns186p293 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 4114549) (BSN.cosOddQ 2097152) 0 3 Ns186p294 Ns186p295 Ns186p293 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p297 := @Ns186p282 411138608 18874368000000 3198355 8388608 25696163 1179648000000 (@Ns186p283 179 8388608 Bool.true 3198355 8388608 1 2250000 (@Ns186p286 Ns186p174 4114549 2097152 179 8388608 (@Ns186p287 17592186044416 59635275 17592186044416 Ns186p284 Ns186p171 Ns186p285 Ns186p174 RS187to204.d39 (@Ns186p288 0 1 87892589805680 5493286862855 17592186044416 59635275 17592186044416 (@Ns186p289 18428829043592790016 4393775235079 17592186044416 59635275 17592186044416 (@Ns186p290 30275147 17592186044416 (Ns186p273 rfl rfl) (Ns186p273 rfl rfl) rfl) (Ns186p273 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 4114549 2097152) (BSN.cos_neg_of_bound 4114549 2097152 Bool.true 3198355 8388608 1 2250000 (Ns186p296 rfl rfl)) rfl rfl) 

noncomputable def Ns186p298 := @Ns186p258 166068891306902209839 Ns186p188 (Ns186p259 qz28 (@Enclosure.Real.IsNear.of_eq qz650 (@Inv.inv Real Real.instInv (Real.sqrt qz34)) Bool.false 2874635 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz30 (BSN.t_div_two_pi_nonneg qz29 455626 1000 qz32)) Ns186p263) rfl) (@Ns186p264 140737488355328 517296049388141 19791209299968000000 (BSN.correction_mk qz31 (BSN.cos_two_pi_p_ne_zero_mk qz29 455626 1000 8 qz32 rfl rfl (@BSN.floor_sqrt_eq_dec qz29 455626 1000 8 qz32 rfl rfl rfl))) (@Ns186p265 16777216 3198355 8388608 25696163 1179648000000 53917692680475 140737488355328 517296049388141 19791209299968000000 Ns186p281 (Ns186p297 rfl) rfl)) 

noncomputable def Ns186p299 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz29) (hardyZApproximantRS₀ qz29) Bool.false 1721309008474231659735 1180591620717411303424 27774805864762262209839 Ns186p188 (@Eq.refl Real (hardyZApproximantRS₀ qz29)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz29) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz29) qz29 8) (@HMul.hMul Real Real Real qz5 qz646 (Zeta.RiemannSiegel.correction qz31))) Bool.false 1721309008474231659735 1180591620717411303424 27774805864762262209839 Ns186p188 (BSN.hardyZApproximantRS₀_eq qz29 8 (@BSN.floor_sqrt_eq_dec qz29 455626 1000 8 qz32 rfl rfl rfl)) (@Ns186p190 1721309008474231659735 1180591620717411303424 27774805864762262209839 Ns186p188 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz29) qz29 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 8)) Bool.false 26663865 16777216 12555 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz29) qz29 8) (Ns186p257 (Ns186p256 rfl rfl rfl rfl) rfl rfl)) (Ns186p298 rfl) rfl rfl)) 

theorem RS187to204.d43 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz29) Bool.false 1721309008474231659735 1180591620717411303424 27774805864762262209839 Ns186p188 := Ns186p299 

noncomputable abbrev qz654 := (@HMul.hMul Real Real Real qz891 (Real.sqrt qz896) qz893)

noncomputable abbrev qz390 := qz654

noncomputable abbrev qz42 := qz390

noncomputable abbrev qz391 := (@HMul.hMul Real Real Real qz628 (@HMul.hMul Real Real Real qz628 qz654 qz654) qz654)

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz391))

noncomputable abbrev qz44 := (@HMul.hMul Real Real Real qz342 (@HMul.hMul Real Real Real qz342 qz368 qz368) qz368)

noncomputable abbrev qz655 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz42))

noncomputable def Ns186p300 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz357 (@HAdd.hAdd Real Real Real qz357 qz655 qz43) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz44))) Bool.false 

noncomputable def Ns186p301 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz357 qz655 qz43) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz44)) 15920801 536870912 

noncomputable def Ns186p302 := @Enclosure.Real.IsNear.addLit_ff qz655 qz43 497525 16777216 25 33554432 

noncomputable def Ns186p303 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz42) 25 4 0 1 19901 4194304 1 8388608 497525 

noncomputable def Ns186p304 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz42) Bool.false 79604 16777216 2 16777216 19901 4194304 1 8388608 

noncomputable def Ns186p305 := @Enclosure.Real.IsNear.mulLit_ff qz19 qz8 24459463 8388608 3 8388608 1212684916143 16777216000 454159 16777216000 29661621837057811209 140737488355328000 14746541367523 

noncomputable def Ns186p306 := @Enclosure.Real.IsNear.sqrt_image qz8 1212684916143 16777216000 454159 16777216000 71318772 71318800 8388608 qz366 

noncomputable def Ns186p307 := @Enclosure.Real.IsNear.sqrt_image qz18 35659393 4194304 7 4194304 24459460 24459466 8388608 (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 142637572 16777216 28 16777216 35659393 4194304 7 4194304 (Ns186p306 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz392 := (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 48918926 16777216 6 16777216 24459463 8388608 3 8388608 (Ns186p307 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns186p308 := @Ns186p305 140737488355328000 qz392 

noncomputable def Ns186p309 := Ns186p308 qz366 

noncomputable def Ns186p310 := @Enclosure.Real.IsNear.inv_image qz42 29661621837057811209 140737488355328000 14746541367523 140737488355328000 39801 39803 8388608 (Ns186p309 rfl) rfl rfl 

noncomputable abbrev qz45 := (@Inv.inv Real Real.instInv qz391)

noncomputable def Ns186p311 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz45 1 32 0 1 1 

noncomputable def Ns186p312 := @Enclosure.Real.IsNear.recentre' qz45 Bool.false 1 16777216 1 16777216 

noncomputable def Ns186p313 := nat_lit 26096645196134537112310863990100429090781841578346803002329 

noncomputable def Ns186p314 := nat_lit 2787593149816327892691964784081045188247552000000000 

noncomputable def Ns186p315 := nat_lit 38922563106300435698814940813638450203278145511236839 

noncomputable abbrev qz46 := qz391

noncomputable def Ns186p316 := @Enclosure.Real.IsNear.inv_image qz46 Ns186p313 Ns186p314 Ns186p315 Ns186p314 0 1 

noncomputable def Ns186p317 := nat_lit 879811810004624803007598884001886041681 

noncomputable def Ns186p318 := nat_lit 19807040628566084398385987584000000 

noncomputable def Ns186p319 := nat_lit 874812884356475453636662995086143 

noncomputable abbrev qz393 := (@HMul.hMul Real Real Real qz628 qz654 qz654)

noncomputable abbrev qz47 := qz393

noncomputable def Ns186p320 := @Enclosure.Real.IsNear.mulLit_ff qz47 qz42 Ns186p317 Ns186p318 Ns186p319 Ns186p318 29661621837057811209 140737488355328000 14746541367523 

noncomputable def Ns186p321 := @Enclosure.Real.IsNear.mulLit_ff qz42 qz42 29661621837057811209 140737488355328000 14746541367523 140737488355328000 29661621837057811209 140737488355328000 14746541367523 140737488355328000 Ns186p317 

noncomputable def Ns186p322 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz44) 13 10 0 1 338391 8388608 1 

noncomputable def Ns186p323 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz44) Bool.false 676782 16777216 2 16777216 338391 8388608 

noncomputable def Ns186p324 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz19 qz19) qz19 598265330248369 70368744177664 146756787 70368744177664 24459463 8388608 3 8388608 14633248709392762365847 

noncomputable def Ns186p325 := @Enclosure.Real.IsNear.mulLit_ff qz19 qz19 24459463 8388608 3 8388608 24459463 8388608 3 8388608 598265330248369 70368744177664 146756787 

noncomputable def Ns186p326 := @Ns186p325 70368744177664 qz392 

noncomputable def Ns186p327 := Ns186p326 qz392 

noncomputable def Ns186p328 := @Ns186p324 590295810358705651712 5384388632640849 590295810358705651712 (Ns186p327 rfl) qz392 

noncomputable def Ns186p329 := @Enclosure.Real.IsNear.inv_image qz44 14633248709392762365847 590295810358705651712 5384388632640849 590295810358705651712 338390 338392 8388608 (Ns186p328 rfl) 

noncomputable def Ns186p330 := @Ns186p301 401 536870912 4399083 83886080 13 83886080 3697273288523776 220374661 2684354560 2421 2684354560 (@Ns186p302 1 536870912 1 536870912 267106717270016 15920801 536870912 401 536870912 (@Ns186p303 16777216 25 33554432 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns186p304 (Ns186p310 rfl rfl rfl rfl) rfl) rfl) (@Ns186p311 16777216 1 16777216 1 536870912 1 536870912 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns186p312 1 16777216 1 16777216 (@Ns186p316 8388608 (@Ns186p320 140737488355328000 Ns186p313 Ns186p314 Ns186p315 Ns186p314 (@Ns186p321 Ns186p318 Ns186p319 Ns186p318 (Ns186p309 rfl) (Ns186p309 rfl) rfl) (Ns186p309 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns186p322 8388608 4399083 83886080 13 83886080 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns186p323 1 8388608 (Ns186p329 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS187to204.d44 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 := @Ns186p300 220374661 2684354560 2421 2684354560 (BSN.hardyZErrorBoundRS₀_mk qz4 454159 1000 qz11 rfl rfl) (Ns186p330 rfl rfl) 

noncomputable def Ns186p331 := nat_lit 83010348331692982272000000 

noncomputable def Ns186p332 := nat_lit 19487819522116366686159372288 

noncomputable abbrev qz901 := (Enclosure.sfrac Bool.false 457092 1000)

noncomputable abbrev qz656 := qz901

noncomputable abbrev qz394 := qz656

noncomputable abbrev qz48 := qz394

noncomputable abbrev qz902 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 457092 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz657 := qz902

noncomputable abbrev qz395 := qz657

noncomputable abbrev qz49 := qz395

noncomputable abbrev qz903 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 457092 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz658 := qz903

noncomputable abbrev qz396 := qz658

noncomputable abbrev qz50 := qz396

noncomputable abbrev qz659 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz49 qz9))

noncomputable def Ns186p333 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz48) qz48 8) (@HMul.hMul Real Real Real qz5 qz659 (Zeta.RiemannSiegel.correction qz50)) 30806649 16777216 100755 67108864 77651958836624478075 590295810358705651712 763149280375386199597 Ns186p331 Ns186p332 

noncomputable def Ns186p334 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz48) qz48 Real.sin BSN.quadSignPos 7 8 457092 1000 127 134217728 67108864 2251799813685248 Bool.false 100776010504 1782 279097919 60 47453128 8 

noncomputable def Ns186p335 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz48) qz48 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 457092 1000 43 88 134217728 67108864 2251799813685248 Bool.false 100776010504 1782 

noncomputable def Ns186p336 := Ns186p335 240485871 61 54794152 8 261175631 61 50729528 8 Bool.true 209554553 67075 Bool.true 82522535 Bool.true 52354177 7074237752028440 1 Bool.false 77420608 Bool.false Bool.false 124135670 Bool.false Bool.true 131028857 

noncomputable def Ns186p337 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz48) qz48 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 457092 1000 74 9 134217728 67108864 2251799813685248 Bool.false 100776010504 1782 

noncomputable def Ns186p338 := Ns186p337 186065264 60 67108856 8 216015088 60 60023992 8 Bool.true 117994594 39389 Bool.false 125742005 Bool.false 139783472 7074237752028440 1 Bool.false 79500937 Bool.true Bool.false 115849554 Bool.true Bool.true 209554553 

noncomputable def Ns186p339 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz48) qz48 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 457092 1000 276 158 134217728 67108864 2251799813685248 Bool.false 100776010504 1782 

noncomputable def Ns186p340 := Ns186p339 93032624 60 94906264 8 147453232 60 77490640 16 Bool.true 134217672 1844 Bool.false 62817233 Bool.false 65380949 7074237752028440 1 Bool.false 119784096 Bool.false Bool.false 118605760 Bool.true Bool.true 117994594 

noncomputable def Ns186p341 := nat_lit 941196707745544516386889846548021284138979607533541 

noncomputable def Ns186p342 := nat_lit 1253525348769981545760031431450706867669434368000 

noncomputable def Ns186p343 := nat_lit 9577687341422745931778196111360000 

noncomputable def Ns186p344 := nat_lit 26267320241150059532002273209058590720 

noncomputable abbrev qz397 := (@Eq.refl Real qz656)

noncomputable abbrev qz51 := qz397

noncomputable def Ns186p345 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz48 457092 1000 835733385856 16000000 914184 4000 2000 Ns186p343 Ns186p344 qz51 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns186p346 := nat_lit 88822465111889287813340946696054416943358321285418125885440 

noncomputable abbrev qz660 := (Real.log (Enclosure.sfrac Bool.false 835733385856 16000000))

noncomputable abbrev qz52 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 457092 4000) qz660) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 914184))))))

noncomputable abbrev qz661 := (Enclosure.sfrac Bool.false 457092 2000)

noncomputable abbrev qz398 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz52 qz661) (@HMul.hMul Real Real Real qz5 qz661 (Real.log Real.pi)))

noncomputable def Ns186p347 := @Enclosure.Real.IsNear.addLit_ft_p qz398 (Enclosure.sfrac Bool.true Ns186p343 Ns186p344) 3381483433807236457577 4503599627370496000 12230382548965777 921600000000000000000 Ns186p343 Ns186p344 0 1 Ns186p346 

noncomputable def Ns186p348 := nat_lit 11346375593881141682368833126400 

noncomputable abbrev qz399 := (@HSub.hSub Real Real Real qz12 qz52 qz661)

noncomputable abbrev qz400 := (@HMul.hMul Real Real Real qz5 qz661 (Real.log Real.pi))

noncomputable def Ns186p349 := @Enclosure.Real.IsNear.subLit_ff_p qz399 qz400 911946128286326330389 900719925474099200 2906825771399 450000000000000000 4389312891753 16777216000 114273 16777216000 Ns186p348 3381483433807236457577 4503599627370496000 

noncomputable def Ns186p350 := nat_lit 9119461282863263303890000 

noncomputable abbrev qz401 := qz661

noncomputable def Ns186p351 := @Enclosure.Real.IsNear.subLit_ff_p qz52 qz401 5589010321868649030761 4503599627370496000 2906825771399 450000000000000000 457092 2000 0 1 Ns186p350 911946128286326330389 900719925474099200 2906825771399 450000000000000000 

noncomputable def Ns186p352 := nat_lit 12585332401468751843070099058723913728 

noncomputable def Ns186p353 := nat_lit 26266273709423585115766784 

noncomputable def Ns186p354 := nat_lit 225051477853170622652220784651539518960980565507172176139765965130704989357745405622851023484879471518010837829876014666219520 

noncomputable def Ns186p355 := nat_lit 4062602755479806764973250830413604907691002427036342575132186685495845029719861223388520791066828753063923388265946576584704 

noncomputable def Ns186p356 := nat_lit 8114295496010319348969337311242858952908234221146534530032095190687269678484898961527632677071388846423276217769656320 

noncomputable def Ns186p357 := BSN.log_dyadic_bound 311445385856 1360021385856 6 5 Ns186p354 67108864 18000000 Ns186p355 Ns186p356 31290748 1671466771712 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 311445385856) (BSN.artanhQ 1360021385856) 0 5 Ns186p355 Ns186p354 Ns186p356 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns186p358 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 457092 4000) qz660 457092 4000 0 1 48924747313230457 4503599627370496 100000027 1800000000000000 5590777649724784012761 4503599627370496000 1269700342819 200000000000000000 (Enclosure.Real.IsNear.const Bool.false 457092 4000) (BSN.isNear_log_sfrac 835733385856 16000000 48924747313230457 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 835733385856) qz353)) Bool.false Ns186p353 Ns186p89 1000000270000000 18000000000000000000000 48924747313230457 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 835733385856 16000000 15 1671466771712 1048576000000 31290748 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns186p357 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p359 := BSN.arctan_dyadic_bound_f 1000 914184 1 0 8388608 2250000 0 1 1 0 1 1 9176 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 914184) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 914184) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz402 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 914184)))

noncomputable def Ns186p360 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz402 884279719003555 562949953421312 1 2000000000000000 9176 8388608 1 2250000 7412710296298379542528 883663928067491 562949953421312 8000000009 18000000000000000 qz16 (Ns186p359 rfl) rfl rfl 

noncomputable def Ns186p361 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 457092 4000) qz660) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz402)) 5590777649724784012761 4503599627370496000 1269700342819 200000000000000000 883663928067491 2251799813685248 8000000009 72000000000000000 Ns186p352 5589010321868649030761 4503599627370496000 2906825771399 450000000000000000 (Ns186p358 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz402) 1 4 0 1 883663928067491 562949953421312 8000000009 18000000000000000 883663928067491 2251799813685248 8000000009 72000000000000000 qz356 Ns186p360 rfl) 

noncomputable def Ns186p362 := @Ns186p347 Ns186p341 Ns186p342 12230382548965777 921600000000000000000 (@Ns186p349 12230382548965777 921600000000000000000 (Ns186p351 (Ns186p361 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 457092 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz401 (Real.log Real.pi) 457092 2000 0 1 38410761 33554432 1 33554432 4389312891753 16777216000 114273 16777216000 (Enclosure.Real.IsNear.const Bool.false 457092 2000) RS187to204.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns186p343 Ns186p344) 

noncomputable def Ns186p363 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz48) Bool.false Ns186p341 Ns186p342 12230382548965777 921600000000000000000 12597001313 16777216 223 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz48) (@HAdd.hAdd Real Real Real qz357 qz398 (Enclosure.sfrac Bool.true Ns186p343 Ns186p344)) Bool.false Ns186p341 Ns186p342 12230382548965777 921600000000000000000 Ns186p345 (Ns186p362 rfl rfl)) 

noncomputable def Ns186p364 := nat_lit 3795883490264930767077376 

noncomputable def Ns186p365 := nat_lit 855267604438778290252733363728751154177200331376260267052982172947169660253956137028238444910643398039263310807321224346782058690540625 

noncomputable def Ns186p366 := nat_lit 607011444976751347324019609992937718295220445105514310885620157825386619658350910049409749279238644693146122106087520625244140625 

noncomputable def Ns186p367 := nat_lit 4271035696351132255302169216620180742020057003281897951097791439454527556790758724475148708027869634363314647359134034144725328476140625 

noncomputable def Ns186p368 := BSN.sin_dyadic_bound_f 53942748795 34359738368 4 3 16777216 4504395 Ns186p365 Ns186p102 Ns186p366 Ns186p367 Ns186p105 Ns186p366 16777209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53942748795) qz358 0 3 Ns186p365 Ns186p102 Ns186p366 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53942748795) qz359 0 3 Ns186p367 Ns186p105 Ns186p366 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p369 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz48) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12597001313) qz360) Bool.false 12597001313 16777216 223 16777216 Bool.true 16777209 16777216 1 2250000 (Ns186p363 rfl) (Enclosure.sfrac_false_div 12597001313 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12597001313) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p364) qz361) 226375608064910080 72057594037927936 Bool.false 16777209 16777216 119 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 12597001313 16777216 226375608064910080 72057594037927936 119 Ns186p364 Ns186p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777209 16777216 Ns186p364 Ns186p89 53942748795 34359738368 4504395 4500000 (Ns186p368 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p370 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz48) Bool.false Ns186p341 Ns186p342 12230382548965777 921600000000000000000 100776010504 134217728 1782 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz48) (@HAdd.hAdd Real Real Real qz357 qz398 (Enclosure.sfrac Bool.true Ns186p343 Ns186p344)) Bool.false Ns186p341 Ns186p342 12230382548965777 921600000000000000000 Ns186p345 (Ns186p362 rfl rfl)) 

noncomputable def Ns186p371 := Ns186p340 39389 BSN.abs_quadSignPos (BSN.cos_quad_nat0 276 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 119784096 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 158 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 118605760 134217728) qz51 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 1) Bool.true 16777209 16777216 32407951 2359296000000 134217672 134217728 1844 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz48)) Bool.true 16777209 16777216 32407951 2359296000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz48) qz48) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz48)) Bool.true 16777209 16777216 518527216 37748736000000 16777209 16777216 32407951 2359296000000 (Ns186p369 rfl rfl) rfl)) rfl) (Ns186p370 rfl) RS187to204.d7 

noncomputable def Ns186p372 := nat_lit 8489388857145898077471369648955433363630561860649611177716006165121 

noncomputable def Ns186p373 := nat_lit 242454595389304869268109566585527772990473568727571772201933441 

noncomputable def Ns186p374 := nat_lit 25467681662246915622675572727733129035345704634811378389603614628481 

noncomputable def Ns186p375 := BSN.cos_dyadic_bound_f 62817233 134217728 3 2 134217728 67108864 Ns186p372 Ns186p117 Ns186p373 Ns186p374 Ns186p120 Ns186p373 119784096 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 62817233) qz364 0 2 Ns186p372 Ns186p117 Ns186p373 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 62817233) qz365 0 2 Ns186p374 Ns186p120 Ns186p373 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p376 := nat_lit 9962498048099091614251110426047377297424490613839724133229154128481 

noncomputable def Ns186p377 := nat_lit 333894880612848640688772980734795065114013475526982750242722401 

noncomputable def Ns186p378 := nat_lit 29886826354536049145471953732180662302143243814568118434186976940641 

noncomputable def Ns186p379 := BSN.cos_dyadic_bound_f 65380949 134217728 3 2 134217728 67108864 Ns186p376 Ns186p117 Ns186p377 Ns186p378 Ns186p120 Ns186p377 118605760 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 65380949) qz364 0 2 Ns186p376 Ns186p117 Ns186p377 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 65380949) qz365 0 2 Ns186p378 Ns186p120 Ns186p377 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p380 := nat_lit 136354486218692551119518051351631485126976166946345506144351499190625 

noncomputable def Ns186p381 := nat_lit 62494679963030737036376352592853776710693520761270100338750390625 

noncomputable def Ns186p382 := nat_lit 408938469296151591884481401349708747827507113797513978232376996790625 

noncomputable def Ns186p383 := BSN.cos_dyadic_bound_f 125742005 134217728 3 2 134217728 67108864 Ns186p380 Ns186p117 Ns186p381 Ns186p382 Ns186p120 Ns186p381 79500937 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 125742005) qz364 0 2 Ns186p380 Ns186p117 Ns186p381 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 125742005) qz365 0 2 Ns186p382 Ns186p120 Ns186p381 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p384 := nat_lit 374812046268487365500788600278828150852299907591539901267264195788800 

noncomputable def Ns186p385 := nat_lit 145762761560689467863905521884931990615384866421840891715136782336 

noncomputable def Ns186p386 := nat_lit 981414600517797221935047629885307648056931992003635808541962672275456 

noncomputable def Ns186p387 := BSN.sin_dyadic_bound_f 139783472 134217728 3 2 134217728 67108864 Ns186p384 Ns186p111 Ns186p385 Ns186p386 Ns186p114 Ns186p385 115849554 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 139783472) qz362 0 2 Ns186p384 Ns186p111 Ns186p385 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 139783472) qz363 0 2 Ns186p386 Ns186p114 Ns186p385 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p388 := Ns186p338 67075 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 74 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 79500937 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 9 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 115849554 134217728) qz51 rfl rfl (Ns186p371 RS187to204.d9 RS187to204.d11 RS187to204.d13 RS187to204.d17 (Ns186p375 rfl rfl) (Ns186p379 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns186p370 rfl) RS187to204.d19 RS187to204.d21 RS187to204.d23 RS187to204.d25 RS187to204.d17 (Ns186p383 rfl rfl) (Ns186p387 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns186p389 := nat_lit 45512645864805996498638272174354295263426118022072495407981687730625 

noncomputable def Ns186p390 := nat_lit 2150703215294915017365972320489231577686778999407153247187890625 

noncomputable def Ns186p391 := nat_lit 119196304697857608586405453644313790743561673368000352582313735090625 

noncomputable def Ns186p392 := BSN.sin_dyadic_bound_f 82522535 134217728 3 2 134217728 67108864 Ns186p389 Ns186p111 Ns186p390 Ns186p391 Ns186p114 Ns186p390 77420608 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 82522535) qz362 0 2 Ns186p389 Ns186p111 Ns186p390 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 82522535) qz363 0 2 Ns186p391 Ns186p114 Ns186p390 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p393 := nat_lit 4096001865969434817221021869501750100979761787750637768112052495361 

noncomputable def Ns186p394 := nat_lit 56443078838651071545834270604494797596139752546530669043246081 

noncomputable def Ns186p395 := nat_lit 12287892711750627149519973939964041313344093083746820242998070993921 

noncomputable def Ns186p396 := BSN.cos_dyadic_bound_f 52354177 134217728 3 2 134217728 67108864 Ns186p393 Ns186p117 Ns186p394 Ns186p395 Ns186p120 Ns186p394 124135670 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 52354177) qz364 0 2 Ns186p393 Ns186p117 Ns186p394 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 52354177) qz365 0 2 Ns186p395 Ns186p120 Ns186p394 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p397 := Ns186p336 90418 BSN.abs_quadSignPos (BSN.cos_quad_nat3 43 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 77420608 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 88 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 124135670 134217728) qz51 rfl rfl (Ns186p388 rfl rfl) (Ns186p370 rfl) RS187to204.d27 RS187to204.d29 RS187to204.d31 RS187to204.d33 RS187to204.d17 (Ns186p392 rfl rfl) (Ns186p396 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns186p398 := nat_lit 241528349975324722528975261696 

noncomputable def Ns186p399 := BSN.sin_dyadic_bound_f 22168792 134217728 2 1 134217728 67108864 Ns186p398 Ns186p123 Ns186p398 Ns186p398 Ns186p124 Ns186p398 22068130 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 22168792) qz362 0 1 Ns186p398 Ns186p123 Ns186p398 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 22168792) qz363 0 1 Ns186p398 Ns186p124 Ns186p398 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p400 := Ns186p334 Bool.true 131028857 90418 Bool.true 22168792 7074237752028440 1 Bool.false 22068130 Bool.false Bool.true 123226596 100755 BSN.abs_quadSignPos (BSN.cos_quad_nat3 127 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 22068130 134217728) qz51 rfl (Ns186p397 rfl) (Ns186p370 rfl) RS187to204.d35 RS187to204.d37 RS187to204.d17 (Ns186p399 rfl rfl) rfl 

noncomputable def Ns186p401 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 8) 123226596 134217728 100755 134217728 123226596 134217728 100755 134217728 33078387488587776 30806649 16777216 100755 67108864 (Ns186p400 rfl rfl rfl rfl) 

noncomputable def Ns186p402 := @Enclosure.Real.IsNear.mulLit_ff qz659 (Zeta.RiemannSiegel.correction qz50) 5744655 16777216 1 16777216 13517253662165 35184372088832 265028373005849 9895604649984000000 77651958836624478075 590295810358705651712 

noncomputable abbrev qz662 := (@HPow.hPow Real Real Real qz7 qz49 qz9)

noncomputable def Ns186p403 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz662 1 1 0 1 5744655 16777216 1 16777216 5744655 16777216 1 16777216 

noncomputable def Ns186p404 := @Enclosure.Real.IsNear.sqrt_image qz49 305129136321 4194304000 114273 4194304000 71548693 71548721 8388608 (@Enclosure.Real.IsNear.of_eq qz49 (@HMul.hMul Real Real Real qz5 qz48 qz3) Bool.false 305129136321 4194304000 114273 4194304000 (BSN.t_div_two_pi_mk qz48 457092 1000 qz51) (@Enclosure.Real.IsNear.mulLit_ff qz48 qz3 457092 1000 0 1 2670177 16777216 1 16777216 305129136321 4194304000 114273 4194304000 (Enclosure.Real.IsNear.const Bool.false 457092 1000) RS187to204.d40 rfl)) 

noncomputable abbrev qz904 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 457092 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz663 := qz904

noncomputable abbrev qz403 := qz663

noncomputable abbrev qz53 := qz403

noncomputable def Ns186p405 := @Enclosure.Real.IsNear.sqrt_image qz53 71548707 8388608 7 4194304 24498855 24498861 8388608 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 143097414 16777216 28 16777216 71548707 8388608 7 4194304 (Ns186p404 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns186p406 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz53) 12249429 4194304 3 8388608 2872327 2872328 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz53) Bool.false 48997716 16777216 6 16777216 12249429 4194304 3 8388608 (Ns186p405 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns186p407 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz53)) Bool.false 5744655 16777216 1 16777216 5744655 16777216 1 16777216 (Ns186p406 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz54 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz396))

noncomputable abbrev qz664 := (@HMul.hMul Real Real Real qz891 qz903 qz903)

noncomputable abbrev qz404 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz664 qz658) qz640)

noncomputable abbrev qz55 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz404))

noncomputable def Ns186p408 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz50) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz54) qz55) Bool.false 13517253662165 

noncomputable def Ns186p409 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz54) qz55 4266251 4194304 3 

noncomputable abbrev qz665 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz54))

noncomputable def Ns186p410 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz54) (@Neg.neg Real Real.instNeg qz665) Bool.true 4266251 4194304 3 262144 (BSN.inv_eq_neg_inv_neg qz54) 

noncomputable def Ns186p411 := @Enclosure.Real.IsNear.recentre' qz665 Bool.false 17065004 16777216 192 16777216 4266251 4194304 

noncomputable def Ns186p412 := @Enclosure.Real.IsNear.recentre' qz54 Bool.true 16494281 16777216 415027216 37748736000000 16494281 16777216 25939201 2359296000000 

noncomputable abbrev qz56 := (@HMul.hMul Real Real Real qz342 qz340 qz396)

noncomputable def Ns186p413 := @Enclosure.Real.IsNear.cos_image qz56 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6974089) qz649) Bool.false 6974089 2097152 177 16777216 Bool.true 16494281 16777216 1 

noncomputable def Ns186p414 := nat_lit 188902527882377298670557297 

noncomputable def Ns186p415 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz50 884279719003555 140737488355328 1 500000000000000 4439843 8388608 7 4194304 3926063120459900641865 1180591620717411303424 Ns186p414 

noncomputable def Ns186p416 := @Enclosure.Real.IsNear.subLit_ff_p qz53 qz1 71548707 8388608 7 4194304 8 1 0 1 4439843 4439843 8388608 7 

noncomputable def Ns186p417 := @Ns186p416 4194304 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 143097414 16777216 28 16777216 71548707 8388608 7 4194304 (Ns186p404 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns186p418 := @Enclosure.Real.IsNear.recentre' qz56 Bool.false 3926063120459900641865 1180591620717411303424 Ns186p414 Ns186p159 6974089 2097152 177 16777216 (@Ns186p415 Ns186p159 RS187to204.d39 (Ns186p417 rfl rfl) rfl) 

noncomputable def Ns186p419 := nat_lit 1594559958160989060373268568623513923441 

noncomputable def Ns186p420 := BSN.cos_dyadic_bound_f 6319172539 34359738368 2 1 16777216 4504395 Ns186p419 Ns186p276 Ns186p419 Ns186p419 Ns186p277 Ns186p419 16494281 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 6319172539) qz371 0 1 Ns186p419 Ns186p276 Ns186p419 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 6319172539) qz372 0 1 Ns186p419 Ns186p277 Ns186p419 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p421 := @Ns186p413 2250000 (Ns186p418 rfl) (Enclosure.sfrac_false_div 6974089 2097152) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6974089) qz649) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 55584029483672994316288) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 16494281 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 6974089 2097152 226375608064910080 72057594037927936 0 55584029483672994316288 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16494281 16777216 55584029483672994316288 302231454903657293676544 6319172539 34359738368 4504395 4500000 (Ns186p420 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p422 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz54) 16494281 16777216 25939201 2359296000000 8532406 8532598 8388608 (@Enclosure.Real.IsNear.neg qz54 Bool.true 16494281 16777216 25939201 2359296000000 (Ns186p412 (Ns186p421 rfl rfl) rfl)) 

noncomputable def Ns186p423 := Ns186p410 (@Enclosure.Real.IsNear.neg qz665 Bool.false 4266251 4194304 3 262144 (@Ns186p411 3 262144 (Ns186p422 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p424 := @Enclosure.Real.IsNear.recentre' qz55 Bool.true 3168415 8388608 

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz342 qz340 qz404)

noncomputable def Ns186p425 := @Enclosure.Real.IsNear.cos_image qz57 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32851671)) qz360) Bool.true 32851671 16777216 

noncomputable def Ns186p426 := nat_lit 19392203970866450113197021445 

noncomputable def Ns186p427 := nat_lit 9903520314283042199192993792 

noncomputable def Ns186p428 := nat_lit 815506758304094581513716290824389 

noncomputable def Ns186p429 := @Enclosure.Real.IsNear.recentre' qz57 Bool.true Ns186p426 Ns186p427 Ns186p428 

noncomputable def Ns186p430 := nat_lit 37778931862957161709568000000000000000 

noncomputable abbrev qz58 := qz404

noncomputable def Ns186p431 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz58 884279719003555 140737488355328 1 500000000000000 21929943154999 

noncomputable abbrev qz405 := (@HSub.hSub Real Real Real qz633 qz664 qz658)

noncomputable abbrev qz59 := qz405

noncomputable def Ns186p432 := @Enclosure.Real.IsNear.subLit_tf qz59 qz26 17531896643895 70368744177664 30219539 8796093022208 1 16 

noncomputable abbrev qz406 := qz664

noncomputable abbrev qz60 := qz406

noncomputable def Ns186p433 := @Enclosure.Real.IsNear.subLit_ff_n qz60 qz50 19712205864649 70368744177664 15539475 8796093022208 4439843 8388608 7 4194304 

noncomputable def Ns186p434 := @Enclosure.Real.IsNear.mulLit_ff qz50 qz50 4439843 8388608 7 4194304 4439843 8388608 7 4194304 19712205864649 70368744177664 

noncomputable def Ns186p435 := nat_lit 147198452645595439982079531818230296828925138958120000070602206124999925235647512862250183668321 

noncomputable def Ns186p436 := nat_lit 1580118210020570234381703187216318293287449635405578963521120540957359569425316042053497441 

noncomputable def Ns186p437 := nat_lit 887831602608289503450147671016264497037270034548364838082441345136721623110514713928921652638305 

noncomputable def Ns186p438 := BSN.cos_dyadic_bound_t 32851671 16777216 4 3 8388608 2250000 Ns186p435 Ns186p180 Ns186p436 Ns186p437 Ns186p183 Ns186p436 3168415 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32851671) qz642 0 3 Ns186p435 Ns186p180 Ns186p436 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32851671) (BSN.cosOddQ 16777216) 0 3 Ns186p437 Ns186p183 Ns186p436 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p439 := @Ns186p424 833527216 37748736000000 3168415 8388608 52095451 2359296000000 (@Ns186p425 363 16777216 Bool.true 3168415 8388608 1 2250000 (@Ns186p429 Ns186p430 32851671 16777216 363 16777216 (@Ns186p431 70368744177664 30219539 8796093022208 Ns186p426 Ns186p427 Ns186p428 Ns186p430 RS187to204.d39 (@Ns186p432 0 1 350879090479984 21929943154999 70368744177664 30219539 8796093022208 (@Ns186p433 147068208442150748160 17531896643895 70368744177664 30219539 8796093022208 (@Ns186p434 15539475 8796093022208 (Ns186p417 rfl rfl) (Ns186p417 rfl rfl) rfl) (Ns186p417 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32851671 16777216) (BSN.cos_neg_of_bound 32851671 16777216 Bool.true 3168415 8388608 1 2250000 (Ns186p438 rfl rfl)) rfl rfl) 

noncomputable def Ns186p440 := @Ns186p402 763149280375386199597 Ns186p331 (Ns186p403 qz28 (@Enclosure.Real.IsNear.of_eq qz662 (@Inv.inv Real Real.instInv (Real.sqrt qz53)) Bool.false 5744655 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz49 (BSN.t_div_two_pi_nonneg qz48 457092 1000 qz51)) Ns186p407) rfl) (@Ns186p408 35184372088832 265028373005849 9895604649984000000 (BSN.correction_mk qz50 (BSN.cos_two_pi_p_ne_zero_mk qz48 457092 1000 8 qz51 rfl rfl (@BSN.floor_sqrt_eq_dec qz48 457092 1000 8 qz51 rfl rfl rfl))) (@Ns186p409 262144 3168415 8388608 52095451 2359296000000 13517253662165 35184372088832 265028373005849 9895604649984000000 Ns186p423 (Ns186p439 rfl) rfl)) 

noncomputable def Ns186p441 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz48) (hardyZApproximantRS₀ qz48) Bool.true 1161564560062668722043 590295810358705651712 125392105094017626199597 Ns186p331 (@Eq.refl Real (hardyZApproximantRS₀ qz48)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz48) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz48) qz48 8) (@HMul.hMul Real Real Real qz5 qz659 (Zeta.RiemannSiegel.correction qz50))) Bool.true 1161564560062668722043 590295810358705651712 125392105094017626199597 Ns186p331 (BSN.hardyZApproximantRS₀_eq qz48 8 (@BSN.floor_sqrt_eq_dec qz48 457092 1000 8 qz51 rfl rfl rfl)) (@Ns186p333 1161564560062668722043 590295810358705651712 125392105094017626199597 Ns186p331 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz48) qz48 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 8)) Bool.true 30806649 16777216 100755 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz48) qz48 8) (Ns186p401 (Ns186p400 rfl rfl rfl rfl) rfl rfl)) (Ns186p440 rfl) rfl rfl)) 

theorem RS187to204.d45 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz48) Bool.true 1161564560062668722043 590295810358705651712 125392105094017626199597 Ns186p331 := Ns186p441 

noncomputable def Ns186p442 := nat_lit 55340232221128654848000000 

noncomputable def Ns186p443 := nat_lit 32404037226098096709134450688 

noncomputable abbrev qz905 := (Enclosure.sfrac Bool.false 458557 1000)

noncomputable abbrev qz666 := qz905

noncomputable abbrev qz407 := qz666

noncomputable abbrev qz61 := qz407

noncomputable abbrev qz906 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 458557 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz667 := qz906

noncomputable abbrev qz408 := qz667

noncomputable abbrev qz62 := qz408

noncomputable abbrev qz907 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 458557 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz668 := qz907

noncomputable abbrev qz409 := qz668

noncomputable abbrev qz63 := qz409

noncomputable abbrev qz669 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz62 qz9))

noncomputable def Ns186p444 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 8) (@HMul.hMul Real Real Real qz5 qz669 (Zeta.RiemannSiegel.correction qz63)) 29662455 16777216 101081 67108864 155878579426359164427 1180591620717411303424 524845597512166858933 Ns186p442 Ns186p443 

noncomputable def Ns186p445 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.sin BSN.quadSignPos 7 8 458557 1000 127 134217728 67108864 2251799813685248 Bool.false 101197642968 1788 279097919 60 47453128 8 

noncomputable def Ns186p446 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 458557 1000 43 88 134217728 67108864 2251799813685248 Bool.false 101197642968 1788 

noncomputable def Ns186p447 := Ns186p446 240485871 61 54794152 8 261175631 61 50729528 8 Bool.false 59463952 67293 Bool.true 13201872 Bool.true 13344012 7074237752028440 1 Bool.false 13180594 Bool.false Bool.false 133554939 Bool.false Bool.false 115323923 

noncomputable def Ns186p448 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 458557 1000 75 10 134217728 67108864 2251799813685248 Bool.false 101197642968 1788 

noncomputable def Ns186p449 := Ns186p448 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 86774935 39518 Bool.false 63960143 Bool.false 34125118 7074237752028440 1 Bool.false 61566690 Bool.false Bool.false 129902858 Bool.true Bool.false 59463952 

noncomputable def Ns186p450 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 458557 1000 277 159 134217728 67108864 2251799813685248 Bool.false 101197642968 1788 

noncomputable def Ns186p451 := Ns186p450 93032624 60 94906264 8 147453232 60 77490640 16 Bool.false 134217648 1852 Bool.false 137328189 Bool.false 60165714 7074237752028440 1 Bool.false 114590435 Bool.true Bool.false 58170857 Bool.false Bool.false 86774935 

noncomputable def Ns186p452 := nat_lit 1136538896490377259752681447865802298578268206863748266661 

noncomputable def Ns186p453 := nat_lit 1507383610885673672222209115641590686777045516550144000 

noncomputable def Ns186p454 := nat_lit 9732158710717883546351384587360000 

noncomputable def Ns186p455 := nat_lit 26776511867966122654788725221692237120 

noncomputable abbrev qz410 := (@Eq.refl Real qz666)

noncomputable abbrev qz64 := qz410

noncomputable def Ns186p456 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz61 458557 1000 841099088996 16000000 917114 4000 2000 Ns186p454 Ns186p455 qz64 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns186p457 := nat_lit 363692446876920723120858063317056735545045826196399445331520 

noncomputable abbrev qz670 := (Real.log (Enclosure.sfrac Bool.false 841099088996 16000000))

noncomputable abbrev qz65 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 458557 4000) qz670) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 917114))))))

noncomputable abbrev qz671 := (Enclosure.sfrac Bool.false 458557 2000)

noncomputable abbrev qz411 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz65 qz671) (@HMul.hMul Real Real Real qz5 qz671 (Real.log Real.pi)))

noncomputable def Ns186p458 := @Enclosure.Real.IsNear.addLit_ft_p qz411 (Enclosure.sfrac Bool.true Ns186p454 Ns186p455) 13582524265642195609621 18014398509481984000 16359004356543631 1228800000000000000000 Ns186p454 Ns186p455 0 1 Ns186p457 

noncomputable def Ns186p459 := nat_lit 911507773719681977827452780544000 

noncomputable abbrev qz412 := (@HSub.hSub Real Real Real qz12 qz65 qz671)

noncomputable abbrev qz413 := (@HMul.hMul Real Real Real qz5 qz671 (Real.log Real.pi))

noncomputable def Ns186p460 := @Enclosure.Real.IsNear.subLit_ff_p qz412 qz413 18310618433001237440533 18014398509481984000 15551904127313 2400000000000000000 17613523331877 67108864000 458557 67108864000 Ns186p459 13582524265642195609621 18014398509481984000 

noncomputable def Ns186p461 := nat_lit 36621236866002474881066000 

noncomputable abbrev qz414 := qz671

noncomputable def Ns186p462 := @Enclosure.Real.IsNear.subLit_ff_p qz65 qz414 22440932701657502509077 18014398509481984000 15551904127313 2400000000000000000 458557 2000 0 1 Ns186p461 18310618433001237440533 18014398509481984000 15551904127313 2400000000000000000 

noncomputable def Ns186p463 := nat_lit 50532488076515553191932019681940996096 

noncomputable def Ns186p464 := nat_lit 26281747573340071874527232 

noncomputable def Ns186p465 := nat_lit 234089757877581874737822920031358785251643974573386678013606223979121297234796726906933370933633180099102628424526657376747520 

noncomputable def Ns186p466 := nat_lit 4342127307329753720136736145238764710155185068963625584265008917069620057790596132226831664928745502025897123195774963810304 

noncomputable def Ns186p467 := nat_lit 9625771582444328030895613444861424914174195556723809652919959703991125195558355552222667344451397018734189662379704320 

noncomputable def Ns186p468 := BSN.log_dyadic_bound 316811088996 1365387088996 6 5 Ns186p465 67108864 18000000 Ns186p466 Ns186p467 31720234 1682198177992 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 316811088996) (BSN.artanhQ 1365387088996) 0 5 Ns186p466 Ns186p465 Ns186p467 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns186p469 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 458557 4000) qz670 458557 4000 0 1 48953569630794361 4503599627370496 100000027 1800000000000000 22448002029188169797077 18014398509481984000 45855712381039 7200000000000000000 (Enclosure.Real.IsNear.const Bool.false 458557 4000) (BSN.isNear_log_sfrac 841099088996 16000000 48953569630794361 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 841099088996) qz353)) Bool.false Ns186p464 Ns186p89 1000000270000000 18000000000000000000000 48953569630794361 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 841099088996 16000000 15 1682198177992 1048576000000 31720234 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns186p468 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p470 := BSN.arctan_dyadic_bound_f 1000 917114 1 0 8388608 2250000 0 1 1 0 1 1 9146 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 917114) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 917114) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz415 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 917114)))

noncomputable def Ns186p471 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz415 884279719003555 562949953421312 1 2000000000000000 9146 8388608 1 2250000 7412727184796982181888 883665941333411 562949953421312 8000000009 18000000000000000 qz16 (Ns186p470 rfl) rfl rfl 

noncomputable def Ns186p472 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 458557 4000) qz670) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz415)) 22448002029188169797077 18014398509481984000 45855712381039 7200000000000000000 883665941333411 2251799813685248 8000000009 72000000000000000 Ns186p463 22440932701657502509077 18014398509481984000 15551904127313 2400000000000000000 (Ns186p469 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz415) 1 4 0 1 883665941333411 562949953421312 8000000009 18000000000000000 883665941333411 2251799813685248 8000000009 72000000000000000 qz356 Ns186p471 rfl) 

noncomputable def Ns186p473 := @Ns186p458 Ns186p452 Ns186p453 16359004356543631 1228800000000000000000 (@Ns186p460 16359004356543631 1228800000000000000000 (Ns186p462 (Ns186p472 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 458557 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz414 (Real.log Real.pi) 458557 2000 0 1 38410761 33554432 1 33554432 17613523331877 67108864000 458557 67108864000 (Enclosure.Real.IsNear.const Bool.false 458557 2000) RS187to204.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns186p454 Ns186p455) 

noncomputable def Ns186p474 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz61) Bool.false Ns186p452 Ns186p453 16359004356543631 1228800000000000000000 12649705371 16777216 7 524288 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz61) (@HAdd.hAdd Real Real Real qz357 qz411 (Enclosure.sfrac Bool.true Ns186p454 Ns186p455)) Bool.false Ns186p452 Ns186p453 16359004356543631 1228800000000000000000 Ns186p456 (Ns186p473 rfl rfl)) 

noncomputable def Ns186p475 := nat_lit 3795433774023070179131392 

noncomputable def Ns186p476 := nat_lit 854861553478571862779543264887897282023331506329163681915957799600488979269046231074537828395323925429861851515498648342112985856620001 

noncomputable def Ns186p477 := nat_lit 606149020962220397072033915093976226626097000118198928984242737809829336082238738026076328593520925105492724039586838616914540001 

noncomputable def Ns186p478 := nat_lit 4269010466148562408310236817891644077385049156171212173824351198365254630842743801941723307856286374928222896600909773428955881805460961 

noncomputable def Ns186p479 := BSN.sin_dyadic_bound_f 53936357943 34359738368 4 3 16777216 4504395 Ns186p476 Ns186p102 Ns186p477 Ns186p478 Ns186p105 Ns186p477 16777206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53936357943) qz358 0 3 Ns186p476 Ns186p102 Ns186p477 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53936357943) qz359 0 3 Ns186p478 Ns186p105 Ns186p477 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p480 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz61) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12649705371) qz360) Bool.false 12649705371 16777216 7 524288 Bool.false 16777206 16777216 1 2250000 (Ns186p474 rfl) (Enclosure.sfrac_false_div 12649705371 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12649705371) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p475) qz361) 226375608064910080 72057594037927936 Bool.false 16777206 16777216 119 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q3 12649705371 16777216 226375608064910080 72057594037927936 119 Ns186p475 Ns186p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777206 16777216 Ns186p475 Ns186p89 53936357943 34359738368 4504395 4500000 (Ns186p479 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p481 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz61) Bool.false Ns186p452 Ns186p453 16359004356543631 1228800000000000000000 101197642968 134217728 1788 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz61) (@HAdd.hAdd Real Real Real qz357 qz411 (Enclosure.sfrac Bool.true Ns186p454 Ns186p455)) Bool.false Ns186p452 Ns186p453 16359004356543631 1228800000000000000000 Ns186p456 (Ns186p473 rfl rfl)) 

noncomputable def Ns186p482 := Ns186p451 39518 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 277 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 114590435 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 159 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 58170857 134217728) qz64 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 1) Bool.false 8388603 8388608 1017143 73728000000 134217648 134217728 1852 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz61)) Bool.false 8388603 8388608 1017143 73728000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz61) qz61) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz61)) Bool.false 16777206 16777216 16274288 1179648000000 8388603 8388608 1017143 73728000000 (Ns186p480 rfl rfl) rfl)) rfl) (Ns186p481 rfl) RS187to204.d7 

noncomputable def Ns186p483 := nat_lit 349154352691598562482248909964344063514047047906298035394930071188385 

noncomputable def Ns186p484 := nat_lit 126496218573979779378890258363860147914218205570126476756384101281 

noncomputable def Ns186p485 := nat_lit 914247072695543124953562275202597726106833534088428935548163659805601 

noncomputable def Ns186p486 := BSN.sin_dyadic_bound_f 137328189 134217728 3 2 134217728 67108864 Ns186p483 Ns186p111 Ns186p484 Ns186p485 Ns186p114 Ns186p484 114590435 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 137328189) qz362 0 2 Ns186p483 Ns186p111 Ns186p484 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 137328189) qz363 0 2 Ns186p485 Ns186p114 Ns186p484 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p487 := nat_lit 13103771149324186373115319001616 

noncomputable def Ns186p488 := BSN.sin_dyadic_bound_f 60165714 134217728 2 1 134217728 67108864 Ns186p487 Ns186p123 Ns186p487 Ns186p487 Ns186p124 Ns186p487 58170857 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 60165714) qz362 0 1 Ns186p487 Ns186p123 Ns186p487 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 60165714) qz363 0 1 Ns186p487 Ns186p124 Ns186p487 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p489 := nat_lit 16735461931114729167159937041601 

noncomputable def Ns186p490 := BSN.sin_dyadic_bound_f 63960143 134217728 2 1 134217728 67108864 Ns186p489 Ns186p123 Ns186p489 Ns186p489 Ns186p124 Ns186p489 61566690 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 63960143) qz362 0 1 Ns186p489 Ns186p123 Ns186p489 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 63960143) qz363 0 1 Ns186p489 Ns186p124 Ns186p489 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p491 := nat_lit 1356115397819601017649061877776 

noncomputable def Ns186p492 := BSN.cos_dyadic_bound_f 34125118 134217728 2 1 134217728 67108864 Ns186p491 Ns186p134 Ns186p491 Ns186p491 Ns186p135 Ns186p491 129902858 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 34125118) qz364 0 1 Ns186p491 Ns186p134 Ns186p491 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 34125118) qz365 0 1 Ns186p491 Ns186p135 Ns186p491 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p493 := Ns186p449 67293 BSN.abs_quadSignPos (BSN.cos_quad_nat3 75 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 61566690 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 10 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 129902858 134217728) qz64 rfl rfl (Ns186p482 RS187to204.d9 RS187to204.d11 RS187to204.d13 RS187to204.d17 (Ns186p486 rfl rfl) (Ns186p488 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns186p481 rfl) RS187to204.d19 RS187to204.d21 RS187to204.d23 RS187to204.d25 RS187to204.d17 (Ns186p490 rfl rfl) (Ns186p492 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns186p494 := nat_lit 30376803424353600162281619456 

noncomputable def Ns186p495 := BSN.sin_dyadic_bound_f 13201872 134217728 2 1 134217728 67108864 Ns186p494 Ns186p123 Ns186p494 Ns186p494 Ns186p124 Ns186p494 13180594 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 13201872) qz362 0 1 Ns186p494 Ns186p123 Ns186p494 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 13201872) qz363 0 1 Ns186p494 Ns186p124 Ns186p494 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p496 := nat_lit 31706309552993697982537748736 

noncomputable def Ns186p497 := BSN.cos_dyadic_bound_f 13344012 134217728 2 1 134217728 67108864 Ns186p496 Ns186p134 Ns186p496 Ns186p496 Ns186p135 Ns186p496 133554939 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 13344012) qz364 0 1 Ns186p496 Ns186p134 Ns186p496 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 13344012) qz365 0 1 Ns186p496 Ns186p135 Ns186p496 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p498 := Ns186p447 90711 BSN.abs_quadSignPos (BSN.cos_quad_nat3 43 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 13180594 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 88 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133554939 134217728) qz64 rfl rfl (Ns186p493 rfl rfl) (Ns186p481 rfl) RS187to204.d27 RS187to204.d29 RS187to204.d31 RS187to204.d33 RS187to204.d17 (Ns186p495 rfl rfl) (Ns186p497 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns186p499 := nat_lit 7856706322097704472930183281 

noncomputable def Ns186p500 := BSN.sin_dyadic_bound_f 9414779 134217728 2 1 134217728 67108864 Ns186p499 Ns186p123 Ns186p499 Ns186p499 Ns186p124 Ns186p499 9407060 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 9414779) qz362 0 1 Ns186p499 Ns186p123 Ns186p499 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 9414779) qz363 0 1 Ns186p499 Ns186p124 Ns186p499 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p501 := Ns186p445 Bool.false 115323923 90711 Bool.true 9414779 7074237752028440 1 Bool.false 9407060 Bool.false Bool.false 118649820 101081 BSN.abs_quadSignPos (BSN.cos_quad_nat3 127 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 9407060 134217728) qz64 rfl (Ns186p498 rfl) (Ns186p481 rfl) RS187to204.d35 RS187to204.d37 RS187to204.d17 (Ns186p500 rfl rfl) rfl 

noncomputable def Ns186p502 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 8) 118649820 134217728 101081 134217728 118649820 134217728 101081 134217728 31849818536017920 29662455 16777216 101081 67108864 (Ns186p501 rfl rfl rfl rfl) 

noncomputable def Ns186p503 := @Enclosure.Real.IsNear.mulLit_ff qz669 (Zeta.RiemannSiegel.correction qz63) 5740061 16777216 1 16777216 27156258344007 70368744177664 68410321339163 2473901162496000000 155878579426359164427 1180591620717411303424 

noncomputable abbrev qz672 := (@HPow.hPow Real Real Real qz7 qz62 qz9)

noncomputable def Ns186p504 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz672 1 1 0 1 5740061 16777216 1 16777216 5740061 16777216 1 16777216 

noncomputable def Ns186p505 := @Enclosure.Real.IsNear.sqrt_image qz62 1224428354589 16777216000 458557 16777216000 71663259 71663287 8388608 (@Enclosure.Real.IsNear.of_eq qz62 (@HMul.hMul Real Real Real qz5 qz61 qz3) Bool.false 1224428354589 16777216000 458557 16777216000 (BSN.t_div_two_pi_mk qz61 458557 1000 qz64) (@Enclosure.Real.IsNear.mulLit_ff qz61 qz3 458557 1000 0 1 2670177 16777216 1 16777216 1224428354589 16777216000 458557 16777216000 (Enclosure.Real.IsNear.const Bool.false 458557 1000) RS187to204.d40 rfl)) 

noncomputable abbrev qz908 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 458557 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz673 := qz908

noncomputable abbrev qz416 := qz673

noncomputable abbrev qz66 := qz416

noncomputable def Ns186p506 := @Enclosure.Real.IsNear.sqrt_image qz66 71663273 8388608 7 4194304 24518462 24518467 8388608 (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 143326546 16777216 28 16777216 71663273 8388608 7 4194304 (Ns186p505 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns186p507 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz66) 49036929 16777216 5 16777216 2870030 2870031 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz66) Bool.false 49036929 16777216 5 16777216 49036929 16777216 5 16777216 (Ns186p506 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns186p508 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz66)) Bool.false 5740061 16777216 1 16777216 5740061 16777216 1 16777216 (Ns186p507 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz67 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz409))

noncomputable abbrev qz674 := (@HMul.hMul Real Real Real qz891 qz907 qz907)

noncomputable abbrev qz417 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz674 qz668) qz640)

noncomputable abbrev qz68 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz417))

noncomputable def Ns186p509 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz63) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz67) qz68) Bool.false 27156258344007 

noncomputable def Ns186p510 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz67) qz68 8703279 8388608 25 

noncomputable abbrev qz675 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz67))

noncomputable def Ns186p511 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz67) (@Neg.neg Real Real.instNeg qz675) Bool.true 8703279 8388608 25 2097152 (BSN.inv_eq_neg_inv_neg qz67) 

noncomputable def Ns186p512 := @Enclosure.Real.IsNear.recentre' qz675 Bool.false 17406558 16777216 200 16777216 8703279 8388608 

noncomputable def Ns186p513 := @Enclosure.Real.IsNear.recentre' qz67 Bool.true 16170628 16777216 415027216 37748736000000 4042657 4194304 25939201 2359296000000 

noncomputable abbrev qz69 := (@HMul.hMul Real Real Real qz342 qz340 qz409)

noncomputable def Ns186p514 := @Enclosure.Real.IsNear.cos_image qz69 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 57232391) qz360) Bool.false 57232391 16777216 177 16777216 Bool.true 16170628 16777216 1 

noncomputable def Ns186p515 := nat_lit 188902527882869355893790833 

noncomputable def Ns186p516 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz63 884279719003555 140737488355328 1 500000000000000 4554409 8388608 7 4194304 4027371510747261923995 1180591620717411303424 Ns186p515 

noncomputable def Ns186p517 := @Enclosure.Real.IsNear.subLit_ff_p qz66 qz1 71663273 8388608 7 4194304 8 1 0 1 4554409 4554409 8388608 7 

noncomputable def Ns186p518 := @Ns186p517 4194304 (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 143326546 16777216 28 16777216 71663273 8388608 7 4194304 (Ns186p505 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns186p519 := @Enclosure.Real.IsNear.recentre' qz69 Bool.false 4027371510747261923995 1180591620717411303424 Ns186p515 Ns186p159 57232391 16777216 177 16777216 (@Ns186p516 Ns186p159 RS187to204.d39 (Ns186p518 rfl rfl) rfl) 

noncomputable def Ns186p520 := nat_lit 7376930785950579326066039762852983639921 

noncomputable def Ns186p521 := BSN.cos_dyadic_bound_f 9267635131 34359738368 2 1 16777216 4504395 Ns186p520 Ns186p276 Ns186p520 Ns186p520 Ns186p277 Ns186p520 16170628 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 9267635131) qz371 0 1 Ns186p520 Ns186p276 Ns186p520 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 9267635131) qz372 0 1 Ns186p520 Ns186p277 Ns186p520 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p522 := @Ns186p514 2250000 (Ns186p519 rfl) (Enclosure.sfrac_false_div 57232391 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 57232391) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 652151845723244060475392) qz361) 226375608064910080 72057594037927936 Bool.false 16170628 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 57232391 16777216 226375608064910080 72057594037927936 0 652151845723244060475392 Ns186p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16170628 16777216 652151845723244060475392 Ns186p89 9267635131 34359738368 4504395 4500000 (Ns186p521 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p523 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz67) 4042657 4194304 25939201 2359296000000 8703179 8703379 8388608 (@Enclosure.Real.IsNear.neg qz67 Bool.true 4042657 4194304 25939201 2359296000000 (Ns186p513 (Ns186p522 rfl rfl) rfl)) 

noncomputable def Ns186p524 := Ns186p511 (@Enclosure.Real.IsNear.neg qz675 Bool.false 8703279 8388608 25 2097152 (@Ns186p512 25 2097152 (Ns186p523 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p525 := @Enclosure.Real.IsNear.recentre' qz68 Bool.true 3120233 8388608 

noncomputable abbrev qz70 := (@HMul.hMul Real Real Real qz342 qz340 qz417)

noncomputable def Ns186p526 := @Enclosure.Real.IsNear.cos_image qz70 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 2046733)) (@Nat.cast Real Real.instNatCast 1048576)) Bool.true 2046733 1048576 

noncomputable def Ns186p527 := nat_lit 19330847152139251476842679725 

noncomputable def Ns186p528 := nat_lit 20658191545190349225703709636543 

noncomputable def Ns186p529 := @Enclosure.Real.IsNear.recentre' qz70 Bool.true Ns186p527 Ns186p427 Ns186p528 

noncomputable def Ns186p530 := nat_lit 944473296573929042739200000000000000 

noncomputable abbrev qz71 := qz417

noncomputable def Ns186p531 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz71 884279719003555 140737488355328 1 500000000000000 21860556944495 

noncomputable abbrev qz418 := (@HSub.hSub Real Real Real qz633 qz674 qz668)

noncomputable abbrev qz72 := qz418

noncomputable def Ns186p532 := @Enclosure.Real.IsNear.subLit_tf qz72 qz26 17462510433391 70368744177664 3827565 1099511627776 1 16 

noncomputable abbrev qz419 := qz674

noncomputable abbrev qz73 := qz419

noncomputable def Ns186p533 := @Enclosure.Real.IsNear.subLit_ff_n qz73 qz63 20742641339281 70368744177664 1992557 1099511627776 4554409 8388608 7 4194304 

noncomputable def Ns186p534 := @Enclosure.Real.IsNear.mulLit_ff qz63 qz63 4554409 8388608 7 4194304 4554409 8388608 7 4194304 20742641339281 70368744177664 

noncomputable def Ns186p535 := nat_lit 516310215874892410133599684755188438172130332963569673354739478266959620906616241 

noncomputable def Ns186p536 := nat_lit 846322570984149739285326836131859157750990110577656481930582364989086940895641600 

noncomputable def Ns186p537 := nat_lit 5404235952384234103836622579038685461944832682818848166210537095206203491761 

noncomputable def Ns186p538 := nat_lit 3114366482949682554834295909242318151166045158404592805521457975757820016541238705 

noncomputable def Ns186p539 := nat_lit 77015353959557626274964742087999183355340100062566739855682995214006911621503385600 

noncomputable def Ns186p540 := BSN.cos_dyadic_bound_t 2046733 1048576 4 3 8388608 2250000 Ns186p535 Ns186p536 Ns186p537 Ns186p538 Ns186p539 Ns186p537 3120233 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 2046733) (BSN.cosEvenQ 1048576) 0 3 Ns186p535 Ns186p536 Ns186p537 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 2046733) (BSN.cosOddQ 1048576) 0 3 Ns186p538 Ns186p539 Ns186p537 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p541 := @Ns186p525 52798576 2359296000000 3120233 8388608 3299911 147456000000 (@Ns186p526 23 1048576 Bool.true 3120233 8388608 1 2250000 (@Ns186p529 Ns186p530 2046733 1048576 23 1048576 (@Ns186p531 70368744177664 3827565 1099511627776 Ns186p527 Ns186p427 Ns186p528 Ns186p530 RS187to204.d39 (@Ns186p532 0 1 349768911111920 21860556944495 70368744177664 3827565 1099511627776 (@Ns186p533 146486154721627209728 17462510433391 70368744177664 3827565 1099511627776 (@Ns186p534 1992557 1099511627776 (Ns186p518 rfl rfl) (Ns186p518 rfl rfl) rfl) (Ns186p518 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 2046733 1048576) (BSN.cos_neg_of_bound 2046733 1048576 Bool.true 3120233 8388608 1 2250000 (Ns186p540 rfl rfl)) rfl rfl) 

noncomputable def Ns186p542 := @Ns186p503 524845597512166858933 Ns186p442 (Ns186p504 qz28 (@Enclosure.Real.IsNear.of_eq qz672 (@Inv.inv Real Real.instInv (Real.sqrt qz66)) Bool.false 5740061 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz62 (BSN.t_div_two_pi_nonneg qz61 458557 1000 qz64)) Ns186p508) rfl) (@Ns186p509 70368744177664 68410321339163 2473901162496000000 (BSN.correction_mk qz63 (BSN.cos_two_pi_p_ne_zero_mk qz61 458557 1000 8 qz64 rfl rfl (@BSN.floor_sqrt_eq_dec qz61 458557 1000 8 qz64 rfl rfl rfl))) (@Ns186p510 2097152 3120233 8388608 3299911 147456000000 27156258344007 70368744177664 68410321339163 2473901162496000000 Ns186p524 (Ns186p541 rfl) rfl)) 

noncomputable def Ns186p543 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz61) (hardyZApproximantRS₀ qz61) Bool.false 1931431128150111240693 1180591620717411303424 83879646732931558858933 Ns186p442 (@Eq.refl Real (hardyZApproximantRS₀ qz61)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz61) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 8) (@HMul.hMul Real Real Real qz5 qz669 (Zeta.RiemannSiegel.correction qz63))) Bool.false 1931431128150111240693 1180591620717411303424 83879646732931558858933 Ns186p442 (BSN.hardyZApproximantRS₀_eq qz61 8 (@BSN.floor_sqrt_eq_dec qz61 458557 1000 8 qz64 rfl rfl rfl)) (@Ns186p444 1931431128150111240693 1180591620717411303424 83879646732931558858933 Ns186p442 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 8)) Bool.false 29662455 16777216 101081 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz61) qz61 8) (Ns186p502 (Ns186p501 rfl rfl rfl rfl) rfl rfl)) (Ns186p542 rfl) rfl rfl)) 

theorem RS187to204.d46 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz61) Bool.false 1931431128150111240693 1180591620717411303424 83879646732931558858933 Ns186p442 := Ns186p543 

noncomputable def Ns186p544 := nat_lit 7378697629483820646400000 

noncomputable def Ns186p545 := nat_lit 2490810540673980603620655104 

noncomputable abbrev qz909 := (Enclosure.sfrac Bool.false 460021 1000)

noncomputable abbrev qz676 := qz909

noncomputable abbrev qz420 := qz676

noncomputable abbrev qz74 := qz420

noncomputable abbrev qz910 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 460021 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz677 := qz910

noncomputable abbrev qz421 := qz677

noncomputable abbrev qz75 := qz421

noncomputable abbrev qz911 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 460021 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz678 := qz911

noncomputable abbrev qz422 := qz678

noncomputable abbrev qz76 := qz422

noncomputable abbrev qz679 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz75 qz9))

noncomputable def Ns186p546 := @Enclosure.Real.IsNear.subLit_ff_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz74) qz74 8) (@HMul.hMul Real Real Real qz5 qz679 (Zeta.RiemannSiegel.correction qz76)) 58643 8388608 101405 67108864 313434292018585551471 2361183241434822606848 72734712012340956217 Ns186p544 Ns186p545 

noncomputable def Ns186p547 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz74) qz74 Real.cos BSN.quadSignNeg 7 8 460021 1000 126 134217728 67108864 2251799813685248 Bool.false 101619301107 1794 279097919 60 47453128 8 

noncomputable def Ns186p548 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz74) qz74 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 460021 1000 42 87 134217728 67108864 2251799813685248 Bool.false 101619301107 1794 

noncomputable def Ns186p549 := Ns186p548 240485871 61 54794152 8 261175631 61 50729528 8 Bool.true 25678831 67510 Bool.true 154443762 Bool.true 184875711 7074237752028440 1 Bool.false 54741013 Bool.true Bool.false 131716336 Bool.false Bool.false 1757337 

noncomputable def Ns186p550 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz74) qz74 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 460021 1000 76 10 134217728 67108864 2251799813685248 Bool.false 101619301107 1794 

noncomputable def Ns186p551 := Ns186p550 186065264 60 67108856 8 216015088 60 60023992 8 Bool.true 62372686 39646 Bool.false 2390022 Bool.false 139537168 7074237752028440 1 Bool.false 134196448 Bool.false Bool.false 67986217 Bool.true Bool.true 25678831 

noncomputable def Ns186p552 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz74) qz74 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 460021 1000 279 160 134217728 67108864 2251799813685248 Bool.false 101619301107 1794 

noncomputable def Ns186p553 := Ns186p552 93032624 60 94906264 8 147453232 60 77490640 16 Bool.true 134217648 1860 Bool.false 1129138 Bool.false 55123607 7074237752028440 1 Bool.false 1129124 Bool.false Bool.false 123056238 Bool.false Bool.true 62372686 

noncomputable def Ns186p554 := nat_lit 46532466448426759209417582465851020631446055021223430453 

noncomputable def Ns186p555 := nat_lit 61459603213631174206716391189874560092417708565463040 

noncomputable def Ns186p556 := nat_lit 9888509286062719060324328368480000 

noncomputable def Ns186p557 := nat_lit 27293546628839837267717701147995228480 

noncomputable abbrev qz423 := (@Eq.refl Real qz676)

noncomputable abbrev qz77 := qz423

noncomputable def Ns186p558 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz74 460021 1000 846478281764 16000000 920042 4000 2000 Ns186p556 Ns186p557 qz77 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns186p559 := nat_lit 14890389263496562947013626389072326602062737606791497744960 

noncomputable abbrev qz680 := (Real.log (Enclosure.sfrac Bool.false 846478281764 16000000))

noncomputable abbrev qz78 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 460021 4000) qz680) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 920042))))))

noncomputable abbrev qz681 := (Enclosure.sfrac Bool.false 460021 2000)

noncomputable abbrev qz424 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz78 qz681) (@HMul.hMul Real Real Real qz5 qz681 (Real.log Real.pi)))

noncomputable def Ns186p560 := @Enclosure.Real.IsNear.addLit_ft_p qz424 (Enclosure.sfrac Bool.true Ns186p556 Ns186p557) 545564729692712147477 720575940379279360 16410796603914743 1228800000000000000000 Ns186p556 Ns186p557 0 1 Ns186p559 

noncomputable def Ns186p561 := nat_lit 915305731203624532404548403200000 

noncomputable abbrev qz425 := (@HSub.hSub Real Real Real qz12 qz78 qz681)

noncomputable abbrev qz426 := (@HMul.hMul Real Real Real qz5 qz681 (Real.log Real.pi))

noncomputable def Ns186p562 := @Enclosure.Real.IsNear.subLit_ff_p qz425 qz426 18382307435728162229261 18014398509481984000 15600704140489 2400000000000000000 17669756685981 67108864000 460021 67108864000 Ns186p561 545564729692712147477 720575940379279360 

noncomputable def Ns186p563 := nat_lit 36764614871456324458522000 

noncomputable abbrev qz427 := qz681

noncomputable def Ns186p564 := @Enclosure.Real.IsNear.subLit_ff_p qz78 qz427 22525808244093368110093 18014398509481984000 15600704140489 2400000000000000000 460021 2000 0 1 Ns186p563 18382307435728162229261 18014398509481984000 15600704140489 2400000000000000000 

noncomputable def Ns186p565 := nat_lit 50723610807159069712496073123314008064 

noncomputable def Ns186p566 := nat_lit 26297161521367116096208896 

noncomputable def Ns186p567 := nat_lit 243477382595839793942273734566819161799169507112683683554994768300325393723271774076410148975977876238566819182619486736875520 

noncomputable def Ns186p568 := nat_lit 4638439103153651818628043647185200450646913273668391981172526022175404673153790282231412494305890243331898094382213736955904 

noncomputable def Ns186p569 := nat_lit 11390851102235914287113978224406832411835370485460976818753845413124812756292695282694940415068718015707220120903352320 

noncomputable def Ns186p570 := BSN.log_dyadic_bound 322190281764 1370766281764 6 5 Ns186p567 67108864 18000000 Ns186p568 Ns186p569 32148057 1692956563528 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 322190281764) (BSN.artanhQ 1370766281764) 0 5 Ns186p568 Ns186p567 Ns186p569 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns186p571 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 460021 4000) qz680 460021 4000 0 1 48982280346317433 4503599627370496 100000027 1800000000000000 22532877587193291846093 18014398509481984000 46002112420567 7200000000000000000 (Enclosure.Real.IsNear.const Bool.false 460021 4000) (BSN.isNear_log_sfrac 846478281764 16000000 48982280346317433 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 846478281764) qz353)) Bool.false Ns186p566 Ns186p89 1000000270000000 18000000000000000000000 48982280346317433 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 846478281764 16000000 15 1692956563528 1048576000000 32148057 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns186p570 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p572 := BSN.arctan_dyadic_bound_f 1000 920042 1 0 8388608 2250000 0 1 1 0 1 1 9117 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 920042) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 920042) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz428 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 920042)))

noncomputable def Ns186p573 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz428 884279719003555 562949953421312 1 2000000000000000 9117 8388608 1 2250000 7412743510345631399936 883667887490467 562949953421312 8000000009 18000000000000000 qz16 (Ns186p572 rfl) rfl rfl 

noncomputable def Ns186p574 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 460021 4000) qz680) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz428)) 22532877587193291846093 18014398509481984000 46002112420567 7200000000000000000 883667887490467 2251799813685248 8000000009 72000000000000000 Ns186p565 22525808244093368110093 18014398509481984000 15600704140489 2400000000000000000 (Ns186p571 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz428) 1 4 0 1 883667887490467 562949953421312 8000000009 18000000000000000 883667887490467 2251799813685248 8000000009 72000000000000000 qz356 Ns186p573 rfl) 

noncomputable def Ns186p575 := @Ns186p560 Ns186p554 Ns186p555 16410796603914743 1228800000000000000000 (@Ns186p562 16410796603914743 1228800000000000000000 (Ns186p564 (Ns186p574 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 460021 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz427 (Real.log Real.pi) 460021 2000 0 1 38410761 33554432 1 33554432 17669756685981 67108864000 460021 67108864000 (Enclosure.Real.IsNear.const Bool.false 460021 2000) RS187to204.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns186p556 Ns186p557) 

noncomputable def Ns186p576 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz74) Bool.false Ns186p554 Ns186p555 16410796603914743 1228800000000000000000 6351206319 8388608 225 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz74) (@HAdd.hAdd Real Real Real qz357 qz424 (Enclosure.sfrac Bool.true Ns186p556 Ns186p557)) Bool.false Ns186p554 Ns186p555 16410796603914743 1228800000000000000000 Ns186p558 (Ns186p575 rfl rfl)) 

noncomputable def Ns186p577 := nat_lit 1897723261709872506339328 

noncomputable def Ns186p578 := nat_lit 1208925819614629174706176 

noncomputable def Ns186p579 := nat_lit 854873062983334528942594995624008694842385223953984643118260368152131505302037595523410960362991569592184866208509516615856488549747121 

noncomputable def Ns186p580 := nat_lit 606173455116729334877628557791035545349842586087308074486975101908455511606124377532775259772290722986588330818470039209060108721 

noncomputable def Ns186p581 := nat_lit 4269067871282935849621068298879185461165118203934681482008601526656704927145324025925543348673247652974365642130006906663995367706626481 

noncomputable def Ns186p582 := BSN.sin_dyadic_bound_f 53936539123 34359738368 4 3 16777216 4504395 Ns186p579 Ns186p102 Ns186p580 Ns186p581 Ns186p105 Ns186p580 16777206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53936539123) qz358 0 3 Ns186p579 Ns186p102 Ns186p580 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53936539123) qz359 0 3 Ns186p581 Ns186p105 Ns186p580 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz429 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable abbrev qz430 := (@Nat.cast Real Real.instNatCast Ns186p578)

noncomputable def Ns186p583 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz74) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6351206319) qz429) Bool.false 6351206319 8388608 225 16777216 Bool.true 16777206 16777216 1 2250000 (Ns186p576 rfl) (Enclosure.sfrac_false_div 6351206319 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6351206319) qz429) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p577) qz430) 226375608064910080 72057594037927936 Bool.false 16777206 16777216 120 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 6351206319 8388608 226375608064910080 72057594037927936 120 Ns186p577 Ns186p578 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777206 16777216 Ns186p577 Ns186p578 53936539123 34359738368 4504395 4500000 (Ns186p582 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p584 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz74) Bool.false Ns186p554 Ns186p555 16410796603914743 1228800000000000000000 101619301107 134217728 1794 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz74) (@HAdd.hAdd Real Real Real qz357 qz424 (Enclosure.sfrac Bool.true Ns186p556 Ns186p557)) Bool.false Ns186p554 Ns186p555 16410796603914743 1228800000000000000000 Ns186p558 (Ns186p575 rfl rfl)) 

noncomputable def Ns186p585 := Ns186p553 39646 BSN.abs_quadSignPos (BSN.cos_quad_nat3 279 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 1129124 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 160 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 123056238 134217728) qz77 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 1) Bool.true 8388603 8388608 32689201 2359296000000 134217648 134217728 1860 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz74)) Bool.true 8388603 8388608 32689201 2359296000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz74) qz74) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz74)) Bool.true 16777206 16777216 523027216 37748736000000 8388603 8388608 32689201 2359296000000 (Ns186p583 rfl rfl) rfl)) rfl) (Ns186p584 rfl) RS187to204.d7 

noncomputable def Ns186p586 := BSN.sin_dyadic_bound_f 1129138 134217728 1 0 134217728 67108864 0 1 1 0 1 1 1129124 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1129138) qz362 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1129138) qz363 0 0 rfl) rfl rfl 

noncomputable def Ns186p587 := nat_lit 5033924290890920900581493662542777075968351443822374945369924041281 

noncomputable def Ns186p588 := nat_lit 85251302353690521514727345438773750213162382067162700274203201 

noncomputable def Ns186p589 := nat_lit 15101602370068055320701451532937453680404628006702990510709223717441 

noncomputable def Ns186p590 := BSN.cos_dyadic_bound_f 55123607 134217728 3 2 134217728 67108864 Ns186p587 Ns186p117 Ns186p588 Ns186p589 Ns186p120 Ns186p588 123056238 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 55123607) qz364 0 2 Ns186p587 Ns186p117 Ns186p588 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 55123607) qz365 0 2 Ns186p589 Ns186p120 Ns186p588 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p591 := nat_lit 32629287795460040195114256 

noncomputable def Ns186p592 := BSN.cos_dyadic_bound_f 2390022 134217728 2 1 134217728 67108864 Ns186p591 Ns186p134 Ns186p591 Ns186p591 Ns186p135 Ns186p591 134196448 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 2390022) qz364 0 1 Ns186p591 Ns186p134 Ns186p591 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 2390022) qz365 0 1 Ns186p591 Ns186p135 Ns186p591 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p593 := nat_lit 206828469384277565162199607100362293762474023389364419558176043565056 

noncomputable def Ns186p594 := nat_lit 143720670777065873750409914957391689413217507219507622205745790976 

noncomputable def Ns186p595 := nat_lit 620197966811278563739098001471172097908595635153654243430116639113216 

noncomputable def Ns186p596 := BSN.cos_dyadic_bound_f 139537168 134217728 3 2 134217728 67108864 Ns186p593 Ns186p117 Ns186p594 Ns186p595 Ns186p120 Ns186p594 67986217 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 139537168) qz364 0 2 Ns186p593 Ns186p117 Ns186p594 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 139537168) qz365 0 2 Ns186p595 Ns186p120 Ns186p594 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p597 := Ns186p551 67510 BSN.abs_quadSignPos (BSN.cos_quad_nat0 76 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 134196448 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 10 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 67986217 134217728) qz77 rfl rfl (Ns186p585 RS187to204.d9 RS187to204.d11 RS187to204.d13 RS187to204.d17 (Ns186p586 rfl rfl) (Ns186p590 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns186p584 rfl) RS187to204.d19 RS187to204.d21 RS187to204.d23 RS187to204.d25 RS187to204.d17 (Ns186p592 rfl rfl) (Ns186p596 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns186p598 := nat_lit 1197124534926278410395257429059828814331611923033889372224616215255864999826586667596404970359451568705536 

noncomputable def Ns186p599 := nat_lit 184180845155025709427811195785608708696451168908007037707947612049786657469866677050859961438048256 

noncomputable def Ns186p600 := nat_lit 7257507061347768031691783096985985325160716435445863033257552281590075146682886689127668318601216075632640 

noncomputable def Ns186p601 := BSN.cos_dyadic_bound_f 154443762 134217728 4 3 134217728 67108864 Ns186p598 Ns186p127 Ns186p599 Ns186p600 Ns186p130 Ns186p599 54741013 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 154443762) qz364 0 3 Ns186p598 Ns186p127 Ns186p599 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 154443762) qz365 0 3 Ns186p600 Ns186p130 Ns186p599 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p602 := nat_lit 6391670139426173219323681183657777774545382118466615543192167391916241783838939996602013076324645979774721 

noncomputable def Ns186p603 := nat_lit 1594256831904806639426613414044335665320110563051926499045928016583311945135417472152751439621349121 

noncomputable def Ns186p604 := nat_lit 31934854380240037185600643988191580334674519431194820958248808310890118310898980515341358732336837239463681 

noncomputable def Ns186p605 := BSN.sin_dyadic_bound_f 184875711 134217728 4 3 134217728 67108864 Ns186p602 Ns186p237 Ns186p603 Ns186p604 Ns186p240 Ns186p603 131716336 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 184875711) qz362 0 3 Ns186p602 Ns186p237 Ns186p603 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 184875711) qz363 0 3 Ns186p604 Ns186p240 Ns186p603 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p606 := Ns186p549 91002 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 42 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 54741013 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 87 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131716336 134217728) qz77 rfl rfl (Ns186p597 rfl rfl) (Ns186p584 rfl) RS187to204.d27 RS187to204.d29 RS187to204.d31 RS187to204.d33 RS187to204.d17 (Ns186p601 rfl rfl) (Ns186p605 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns186p607 := nat_lit 3885989283476786803123117342643290544916523082254127981716754917223820371186969294926161635575868912828416 

noncomputable def Ns186p608 := nat_lit 6255937069917971398129466623063501351540007055930203605293594487891422154171832526455208279367745536 

noncomputable def Ns186p609 := nat_lit 23522030871732723493321808861065903407698088465127498701223642135264727588381091369466556949738250515251200 

noncomputable def Ns186p610 := BSN.cos_dyadic_bound_f 207184708 134217728 4 3 134217728 67108864 Ns186p607 Ns186p127 Ns186p608 Ns186p609 Ns186p130 Ns186p608 3643558 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 207184708) qz364 0 3 Ns186p607 Ns186p127 Ns186p608 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 207184708) qz365 0 3 Ns186p609 Ns186p130 Ns186p608 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz431 := (BSN.cos_quad_nat2 126 rfl)

noncomputable def Ns186p611 := Ns186p547 Bool.false 1757337 91002 Bool.true 207184708 7074237752028440 1 Bool.false 3643558 Bool.true Bool.false 469144 101405 BSN.abs_quadSignNeg qz431 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 3643558 134217728) qz77 rfl (Ns186p606 rfl) (Ns186p584 rfl) RS187to204.d35 RS187to204.d37 RS187to204.d17 (Ns186p610 rfl rfl) rfl 

noncomputable def Ns186p612 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 8) 469144 134217728 101405 134217728 469144 134217728 101405 134217728 125934883569664 58643 8388608 101405 67108864 (Ns186p611 rfl rfl rfl rfl) 

noncomputable def Ns186p613 := @Enclosure.Real.IsNear.mulLit_ff qz679 (Zeta.RiemannSiegel.correction qz76) 5735489 16777216 1 16777216 54648224766639 140737488355328 189776121072337 6597069766656000000 313434292018585551471 2361183241434822606848 

noncomputable abbrev qz682 := (@HPow.hPow Real Real Real qz7 qz75 qz9)

noncomputable def Ns186p614 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz682 1 1 0 1 5735489 16777216 1 16777216 5735489 16777216 1 16777216 

noncomputable def Ns186p615 := @Enclosure.Real.IsNear.sqrt_image qz75 1228337493717 16777216000 460021 16777216000 71777565 71777593 8388608 (@Enclosure.Real.IsNear.of_eq qz75 (@HMul.hMul Real Real Real qz5 qz74 qz3) Bool.false 1228337493717 16777216000 460021 16777216000 (BSN.t_div_two_pi_mk qz74 460021 1000 qz77) (@Enclosure.Real.IsNear.mulLit_ff qz74 qz3 460021 1000 0 1 2670177 16777216 1 16777216 1228337493717 16777216000 460021 16777216000 (Enclosure.Real.IsNear.const Bool.false 460021 1000) RS187to204.d40 rfl)) 

noncomputable abbrev qz912 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 460021 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz683 := qz912

noncomputable abbrev qz432 := qz683

noncomputable abbrev qz79 := qz432

noncomputable def Ns186p616 := @Enclosure.Real.IsNear.sqrt_image qz79 71777579 8388608 7 4194304 24538008 24538014 8388608 (@Enclosure.Real.IsNear.recentre' qz79 Bool.false 143555158 16777216 28 16777216 71777579 8388608 7 4194304 (Ns186p615 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns186p617 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz79) 24538011 8388608 3 8388608 2867744 2867745 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz79) Bool.false 49076022 16777216 6 16777216 24538011 8388608 3 8388608 (Ns186p616 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns186p618 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz79)) Bool.false 5735489 16777216 1 16777216 5735489 16777216 1 16777216 (Ns186p617 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz80 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz422))

noncomputable abbrev qz684 := (@HMul.hMul Real Real Real qz891 qz911 qz911)

noncomputable abbrev qz433 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz684 qz678) qz640)

noncomputable abbrev qz81 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz433))

noncomputable def Ns186p619 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz76) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz80) qz81) Bool.false 54648224766639 

noncomputable def Ns186p620 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz80) qz81 17895161 16777216 211 

noncomputable abbrev qz685 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz80))

noncomputable def Ns186p621 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz80) (@Neg.neg Real Real.instNeg qz685) Bool.true 17895161 16777216 211 16777216 (BSN.inv_eq_neg_inv_neg qz80) 

noncomputable def Ns186p622 := @Enclosure.Real.IsNear.recentre' qz685 Bool.false 17895161 16777216 211 16777216 17895161 16777216 

noncomputable def Ns186p623 := @Enclosure.Real.IsNear.recentre' qz80 Bool.true 15729111 16777216 415027216 37748736000000 15729111 16777216 25939201 2359296000000 

noncomputable abbrev qz82 := (@HMul.hMul Real Real Real qz342 qz340 qz422)

noncomputable def Ns186p624 := @Enclosure.Real.IsNear.cos_image qz82 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 29334401) qz429) Bool.false 29334401 8388608 177 16777216 Bool.true 15729111 16777216 1 

noncomputable def Ns186p625 := nat_lit 188902527883360296425527409 

noncomputable def Ns186p626 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz76 884279719003555 140737488355328 1 500000000000000 4668715 8388608 7 4194304 4128449988307682281825 1180591620717411303424 Ns186p625 

noncomputable def Ns186p627 := @Enclosure.Real.IsNear.subLit_ff_p qz79 qz1 71777579 8388608 7 4194304 8 1 0 1 4668715 4668715 8388608 7 

noncomputable def Ns186p628 := @Ns186p627 4194304 (@Enclosure.Real.IsNear.recentre' qz79 Bool.false 143555158 16777216 28 16777216 71777579 8388608 7 4194304 (Ns186p615 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns186p629 := @Enclosure.Real.IsNear.recentre' qz82 Bool.false 4128449988307682281825 1180591620717411303424 Ns186p625 Ns186p159 29334401 8388608 177 16777216 (@Ns186p626 Ns186p159 RS187to204.d39 (Ns186p628 rfl rfl) rfl) 

noncomputable def Ns186p630 := nat_lit 22221735808838913035588385610684571234161 

noncomputable def Ns186p631 := BSN.cos_dyadic_bound_f 12209404859 34359738368 2 1 16777216 4504395 Ns186p630 Ns186p276 Ns186p630 Ns186p630 Ns186p277 Ns186p630 15729111 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 12209404859) qz371 0 1 Ns186p630 Ns186p276 Ns186p630 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 12209404859) qz372 0 1 Ns186p630 Ns186p277 Ns186p630 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p632 := @Ns186p624 2250000 (Ns186p629 rfl) (Enclosure.sfrac_false_div 29334401 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 29334401) qz429) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 429580243571236134715392) qz430) 226375608064910080 72057594037927936 Bool.false 15729111 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 29334401 8388608 226375608064910080 72057594037927936 0 429580243571236134715392 Ns186p578 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 15729111 16777216 429580243571236134715392 Ns186p578 12209404859 34359738368 4504395 4500000 (Ns186p631 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p633 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz80) 15729111 16777216 25939201 2359296000000 8947475 8947686 8388608 (@Enclosure.Real.IsNear.neg qz80 Bool.true 15729111 16777216 25939201 2359296000000 (Ns186p623 (Ns186p632 rfl rfl) rfl)) 

noncomputable def Ns186p634 := Ns186p621 (@Enclosure.Real.IsNear.neg qz685 Bool.false 17895161 16777216 211 16777216 (@Ns186p622 211 16777216 (Ns186p633 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p635 := @Enclosure.Real.IsNear.recentre' qz81 Bool.true 3053799 8388608 

noncomputable abbrev qz83 := (@HMul.hMul Real Real Real qz342 qz340 qz433)

noncomputable def Ns186p636 := @Enclosure.Real.IsNear.cos_image qz83 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32604831)) qz360) Bool.true 32604831 16777216 

noncomputable def Ns186p637 := nat_lit 19246495545359439721507819445 

noncomputable def Ns186p638 := nat_lit 837124007982483204905247619144073 

noncomputable def Ns186p639 := @Enclosure.Real.IsNear.recentre' qz83 Bool.true Ns186p637 Ns186p427 Ns186p638 

noncomputable abbrev qz84 := qz433

noncomputable def Ns186p640 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz84 884279719003555 140737488355328 1 500000000000000 21765166758599 

noncomputable abbrev qz434 := (@HSub.hSub Real Real Real qz633 qz684 qz678)

noncomputable abbrev qz85 := qz434

noncomputable def Ns186p641 := @Enclosure.Real.IsNear.subLit_tf qz85 qz26 17367120247495 70368744177664 31020591 8796093022208 1 16 

noncomputable abbrev qz435 := qz684

noncomputable abbrev qz86 := qz435

noncomputable def Ns186p642 := @Enclosure.Real.IsNear.subLit_ff_n qz86 qz76 21796899751225 70368744177664 16340527 8796093022208 4668715 8388608 7 4194304 

noncomputable def Ns186p643 := @Enclosure.Real.IsNear.mulLit_ff qz76 qz76 4668715 8388608 7 4194304 4668715 8388608 7 4194304 21796899751225 70368744177664 

noncomputable def Ns186p644 := nat_lit 142787093456817011713741496176118364757636771649018568738239929489353237362880308632815666112641 

noncomputable def Ns186p645 := nat_lit 1443389167876043708178968316430955101570502829210065433851343198452868066697420638226655361 

noncomputable def Ns186p646 := nat_lit 861372436705736921275073202949707179223169240124772146674162017280623912532710954044807032252545 

noncomputable def Ns186p647 := BSN.cos_dyadic_bound_t 32604831 16777216 4 3 8388608 2250000 Ns186p644 Ns186p180 Ns186p645 Ns186p646 Ns186p183 Ns186p645 3053799 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32604831) qz642 0 3 Ns186p644 Ns186p180 Ns186p645 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32604831) (BSN.cosOddQ 16777216) 0 3 Ns186p646 Ns186p183 Ns186p645 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p648 := @Ns186p635 856027216 37748736000000 3053799 8388608 53501701 2359296000000 (@Ns186p636 373 16777216 Bool.true 3053799 8388608 1 2250000 (@Ns186p639 Ns186p430 32604831 16777216 373 16777216 (@Ns186p640 70368744177664 31020591 8796093022208 Ns186p637 Ns186p427 Ns186p638 Ns186p430 RS187to204.d39 (@Ns186p641 0 1 348242668137584 21765166758599 70368744177664 31020591 8796093022208 (@Ns186p642 145685963845098536960 17367120247495 70368744177664 31020591 8796093022208 (@Ns186p643 16340527 8796093022208 (Ns186p628 rfl rfl) (Ns186p628 rfl rfl) rfl) (Ns186p628 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32604831 16777216) (BSN.cos_neg_of_bound 32604831 16777216 Bool.true 3053799 8388608 1 2250000 (Ns186p647 rfl rfl)) rfl rfl) 

noncomputable def Ns186p649 := @Ns186p613 72734712012340956217 Ns186p544 (Ns186p614 qz28 (@Enclosure.Real.IsNear.of_eq qz682 (@Inv.inv Real Real.instInv (Real.sqrt qz79)) Bool.false 5735489 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz75 (BSN.t_div_two_pi_nonneg qz74 460021 1000 qz77)) Ns186p618) rfl) (@Ns186p619 140737488355328 189776121072337 6597069766656000000 (BSN.correction_mk qz76 (BSN.cos_two_pi_p_ne_zero_mk qz74 460021 1000 8 qz77 rfl rfl (@BSN.floor_sqrt_eq_dec qz74 460021 1000 8 qz77 rfl rfl rfl))) (@Ns186p620 16777216 3053799 8388608 53501701 2359296000000 54648224766639 140737488355328 189776121072337 6597069766656000000 Ns186p634 (Ns186p648 rfl) rfl)) 

noncomputable def Ns186p650 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz74) (hardyZApproximantRS₀ qz74) Bool.true 296927754959342551663 2361183241434822606848 11222332373474868956217 Ns186p544 (@Eq.refl Real (hardyZApproximantRS₀ qz74)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz74) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz74) qz74 8) (@HMul.hMul Real Real Real qz5 qz679 (Zeta.RiemannSiegel.correction qz76))) Bool.true 296927754959342551663 2361183241434822606848 11222332373474868956217 Ns186p544 (BSN.hardyZApproximantRS₀_eq qz74 8 (@BSN.floor_sqrt_eq_dec qz74 460021 1000 8 qz77 rfl rfl rfl)) (@Ns186p546 296927754959342551663 2361183241434822606848 11222332373474868956217 Ns186p544 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz74) qz74 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 8)) Bool.false 58643 8388608 101405 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz74) qz74 8) (Ns186p612 (Ns186p611 rfl rfl rfl rfl) rfl rfl)) (Ns186p649 rfl) rfl rfl)) 

theorem RS187to204.d47 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz74) Bool.true 296927754959342551663 2361183241434822606848 11222332373474868956217 Ns186p544 := Ns186p650 

noncomputable def Ns186p651 := nat_lit 33204139332677192908800000 

noncomputable def Ns186p652 := nat_lit 63553835399093795528156119040 

noncomputable abbrev qz913 := (Enclosure.sfrac Bool.false 461484 1000)

noncomputable abbrev qz686 := qz913

noncomputable abbrev qz436 := qz686

noncomputable abbrev qz87 := qz436

noncomputable abbrev qz914 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 461484 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz687 := qz914

noncomputable abbrev qz437 := qz687

noncomputable abbrev qz88 := qz437

noncomputable abbrev qz915 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 461484 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz688 := qz915

noncomputable abbrev qz438 := qz688

noncomputable abbrev qz89 := qz438

noncomputable abbrev qz689 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz88 qz9))

noncomputable def Ns186p653 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz87) qz87 8) (@HMul.hMul Real Real Real qz5 qz689 (Zeta.RiemannSiegel.correction qz89)) 56074945 16777216 12715 8388608 157819676404947272165 1180591620717411303424 343993870160106977999 Ns186p651 Ns186p652 

noncomputable def Ns186p654 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz87) qz87 Real.cos BSN.quadSignNeg 7 8 461484 1000 126 134217728 67108864 2251799813685248 Bool.false 102040983856 1799 279097919 60 47453128 8 

noncomputable def Ns186p655 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz87) qz87 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 461484 1000 42 87 134217728 67108864 2251799813685248 Bool.false 102040983856 1799 

noncomputable def Ns186p656 := Ns186p655 240485871 61 54794152 8 261175631 61 50729528 8 Bool.false 229761918 67717 Bool.true 84591842 Bool.true 145292910 7074237752028440 1 Bool.false 108431185 Bool.true Bool.false 118533195 Bool.false Bool.false 230296409 

noncomputable def Ns186p657 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz87) qz87 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 461484 1000 76 11 134217728 67108864 2251799813685248 Bool.false 102040983856 1799 

noncomputable def Ns186p658 := Ns186p657 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 186017236 39765 Bool.false 151859290 Bool.false 34361129 7074237752028440 1 Bool.false 57090466 Bool.false Bool.false 33987011 Bool.false Bool.false 229761918 

noncomputable def Ns186p659 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz87) qz87 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 461484 1000 280 161 134217728 67108864 2251799813685248 Bool.false 102040983856 1799 

noncomputable def Ns186p660 := Ns186p659 93032624 60 94906264 8 147453232 60 77490640 16 Bool.false 134217672 1860 Bool.false 75876444 Bool.false 50253564 7074237752028440 1 Bool.false 113335505 Bool.false Bool.false 49087600 Bool.true Bool.false 186017236 

noncomputable def Ns186p661 := nat_lit 1009290099758489181336399469734290901812648734585347 

noncomputable def Ns186p662 := nat_lit 1327551136449178584198817555539488446928125952000 

noncomputable def Ns186p663 := nat_lit 10046754045280029044449186283520000 

noncomputable def Ns186p664 := nat_lit 27818512702459951997244167141279662080 

noncomputable abbrev qz439 := (@Eq.refl Real qz686)

noncomputable abbrev qz90 := qz439

noncomputable def Ns186p665 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz87 461484 1000 851870929024 16000000 922968 4000 2000 Ns186p663 Ns186p664 qz90 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns186p666 := nat_lit 95248563807992179662809676933849343499318996356490833428480 

noncomputable abbrev qz690 := (Real.log (Enclosure.sfrac Bool.false 851870929024 16000000))

noncomputable abbrev qz91 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 461484 4000) qz690) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 922968))))))

noncomputable abbrev qz691 := (Enclosure.sfrac Bool.false 461484 2000)

noncomputable abbrev qz440 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz91 qz691) (@HMul.hMul Real Real Real qz5 qz691 (Real.log Real.pi)))

noncomputable def Ns186p667 := @Enclosure.Real.IsNear.addLit_ft_p qz440 (Enclosure.sfrac Bool.true Ns186p663 Ns186p664) 3423928880501481791331 4503599627370496000 12346915105550779 921600000000000000000 Ns186p663 Ns186p664 0 1 Ns186p666 

noncomputable def Ns186p668 := nat_lit 57443994396811548333227114496000 

noncomputable abbrev qz441 := (@HSub.hSub Real Real Real qz12 qz91 qz691)

noncomputable abbrev qz442 := (@HMul.hMul Real Real Real qz5 qz691 (Real.log Real.pi))

noncomputable def Ns186p669 := @Enclosure.Real.IsNear.subLit_ff_p qz441 qz442 4613497357664364519267 4503599627370496000 5868551557621 900000000000000000 4431487907331 16777216000 115371 16777216000 Ns186p668 3423928880501481791331 4503599627370496000 

noncomputable def Ns186p670 := nat_lit 9226994715328729038534000 

noncomputable abbrev qz443 := qz691

noncomputable def Ns186p671 := @Enclosure.Real.IsNear.subLit_ff_p qz91 qz443 5652666942883087507299 4503599627370496000 5868551557621 900000000000000000 461484 2000 0 1 Ns186p670 4613497357664364519267 4503599627370496000 5868551557621 900000000000000000 

noncomputable def Ns186p672 := nat_lit 12728674368808896847075274283288625152 

noncomputable def Ns186p673 := nat_lit 26312516057907876046307328 

noncomputable def Ns186p674 := nat_lit 6234346753899325460252215898223803956626515856636578277849884177658931411807821833821263602973673536727095936551244786164023108948199190215918364917760 

noncomputable def Ns186p675 := nat_lit 121926776568761274994601620219230291136223331284031989260085080631979374997606415260341970279085551418833998347270318236203607139719631637000038121472 

noncomputable def Ns186p676 := nat_lit 15873753602476525771891695812522328614740297066180599873563584884485795615648673677758337681520184722149959133846961383748433185344757191147520 

noncomputable def Ns186p677 := BSN.log_dyadic_bound 327582929024 1376158929024 7 6 Ns186p674 67108864 18000000 Ns186p675 Ns186p676 32574231 1703741858048 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 327582929024) (BSN.artanhQ 1376158929024) 0 6 Ns186p675 Ns186p674 Ns186p676 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns186p678 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 461484 4000) qz690 461484 4000 0 1 49010880399323769 4503599627370496 100000027 1800000000000000 5654434282550382553299 4503599627370496000 1281900346113 200000000000000000 (Enclosure.Real.IsNear.const Bool.false 461484 4000) (BSN.isNear_log_sfrac 851870929024 16000000 49010880399323769 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 851870929024) qz353)) Bool.false Ns186p673 Ns186p89 1000000270000000 18000000000000000000000 49010880399323769 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 851870929024 16000000 15 1703741858048 1048576000000 32574231 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns186p677 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p679 := BSN.arctan_dyadic_bound_f 1000 922968 1 0 8388608 2250000 0 1 1 0 1 1 9088 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 922968) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 922968) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz444 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 922968)))

noncomputable def Ns186p680 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz444 884279719003555 562949953421312 1 2000000000000000 9088 8388608 1 2250000 7412759835894280617984 883669833647523 562949953421312 8000000009 18000000000000000 qz16 (Ns186p679 rfl) rfl rfl 

noncomputable def Ns186p681 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 461484 4000) qz690) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz444)) 5654434282550382553299 4503599627370496000 1281900346113 200000000000000000 883669833647523 2251799813685248 8000000009 72000000000000000 Ns186p672 5652666942883087507299 4503599627370496000 5868551557621 900000000000000000 (Ns186p678 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz444) 1 4 0 1 883669833647523 562949953421312 8000000009 18000000000000000 883669833647523 2251799813685248 8000000009 72000000000000000 qz356 Ns186p680 rfl) 

noncomputable def Ns186p682 := @Ns186p667 Ns186p661 Ns186p662 12346915105550779 921600000000000000000 (@Ns186p669 12346915105550779 921600000000000000000 (Ns186p671 (Ns186p681 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 461484 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz443 (Real.log Real.pi) 461484 2000 0 1 38410761 33554432 1 33554432 4431487907331 16777216000 115371 16777216000 (Enclosure.Real.IsNear.const Bool.false 461484 2000) RS187to204.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns186p663 Ns186p664) 

noncomputable def Ns186p683 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz87) Bool.false Ns186p661 Ns186p662 12346915105550779 921600000000000000000 6377561491 8388608 225 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz87) (@HAdd.hAdd Real Real Real qz357 qz440 (Enclosure.sfrac Bool.true Ns186p663 Ns186p664)) Bool.false Ns186p661 Ns186p662 12346915105550779 921600000000000000000 Ns186p665 (Ns186p682 rfl rfl)) 

noncomputable def Ns186p684 := nat_lit 1897951357625064627372032 

noncomputable def Ns186p685 := nat_lit 855284966038711281426639924437443274582787880156775568293195589386852797838626707802504997898862007359742657905183330142968761638936001 

noncomputable def Ns186p686 := nat_lit 607048337996441146824059951772124683561887051620408058474820371936319133503515500234350414701788782864824252225173541296627736001 

noncomputable def Ns186p687 := nat_lit 4271122289460153647473052648501154904244131017964971446016982539312695297681621137810238671651933909132099624645902968009796010949696961 

noncomputable def Ns186p688 := BSN.sin_dyadic_bound_f 53943021999 34359738368 4 3 16777216 4504395 Ns186p685 Ns186p102 Ns186p686 Ns186p687 Ns186p105 Ns186p686 16777209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53943021999) qz358 0 3 Ns186p685 Ns186p102 Ns186p686 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53943021999) qz359 0 3 Ns186p687 Ns186p105 Ns186p686 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p689 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz87) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6377561491) qz429) Bool.false 6377561491 8388608 225 16777216 Bool.false 16777209 16777216 1 2250000 (Ns186p683 rfl) (Enclosure.sfrac_false_div 6377561491 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6377561491) qz429) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p684) qz430) 226375608064910080 72057594037927936 Bool.false 16777209 16777216 120 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q3 6377561491 8388608 226375608064910080 72057594037927936 120 Ns186p684 Ns186p578 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777209 16777216 Ns186p684 Ns186p578 53943021999 34359738368 4504395 4500000 (Ns186p688 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p690 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz87) Bool.false Ns186p661 Ns186p662 12346915105550779 921600000000000000000 102040983856 134217728 1799 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz87) (@HAdd.hAdd Real Real Real qz357 qz440 (Enclosure.sfrac Bool.true Ns186p663 Ns186p664)) Bool.false Ns186p661 Ns186p662 12346915105550779 921600000000000000000 Ns186p665 (Ns186p682 rfl rfl)) 

noncomputable def Ns186p691 := Ns186p660 39765 BSN.abs_quadSignPos (BSN.cos_quad_nat0 280 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 113335505 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 161 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 49087600 134217728) qz90 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 1) Bool.false 16777209 16777216 32689201 2359296000000 134217672 134217728 1860 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz87)) Bool.false 16777209 16777216 32689201 2359296000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz87) qz87) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz87)) Bool.false 16777209 16777216 523027216 37748736000000 16777209 16777216 32689201 2359296000000 (Ns186p689 rfl rfl) rfl)) rfl) (Ns186p690 rfl) RS187to204.d7 

noncomputable def Ns186p692 := nat_lit 18071869966570405484963365538387936392202555858977707640180346781696 

noncomputable def Ns186p693 := nat_lit 1098640876550100388802093632967506148273976865696932768493142016 

noncomputable def Ns186p694 := nat_lit 54213412617958116254112492427897874164311119623201729055004054061056 

noncomputable def Ns186p695 := BSN.cos_dyadic_bound_f 75876444 134217728 3 2 134217728 67108864 Ns186p692 Ns186p117 Ns186p693 Ns186p694 Ns186p120 Ns186p693 113335505 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 75876444) qz364 0 2 Ns186p692 Ns186p117 Ns186p693 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 75876444) qz365 0 2 Ns186p694 Ns186p120 Ns186p693 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p696 := nat_lit 6377749685229617171642186793216 

noncomputable def Ns186p697 := BSN.sin_dyadic_bound_f 50253564 134217728 2 1 134217728 67108864 Ns186p696 Ns186p123 Ns186p696 Ns186p696 Ns186p124 Ns186p696 49087600 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 50253564) qz362 0 1 Ns186p696 Ns186p123 Ns186p696 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 50253564) qz363 0 1 Ns186p696 Ns186p124 Ns186p696 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p698 := nat_lit 1118906358356043131919206055659202624245463385102677281602011403405456018706372140221949871907617344000000 

noncomputable def Ns186p699 := nat_lit 150416812292215189178599155070233166470415162758667632470564742106142887799324882262241000000000000 

noncomputable def Ns186p700 := nat_lit 6783621072363993352905393048460594807077946529938162913182523651921509824592647038321717942768161753600000 

noncomputable def Ns186p701 := BSN.cos_dyadic_bound_f 151859290 134217728 4 3 134217728 67108864 Ns186p698 Ns186p127 Ns186p699 Ns186p700 Ns186p130 Ns186p699 57090466 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 151859290) qz364 0 3 Ns186p698 Ns186p127 Ns186p699 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 151859290) qz365 0 3 Ns186p700 Ns186p130 Ns186p699 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p702 := nat_lit 1394022231549763890284365838881 

noncomputable def Ns186p703 := BSN.sin_dyadic_bound_f 34361129 134217728 2 1 134217728 67108864 Ns186p702 Ns186p123 Ns186p702 Ns186p702 Ns186p124 Ns186p702 33987011 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 34361129) qz362 0 1 Ns186p702 Ns186p123 Ns186p702 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 34361129) qz363 0 1 Ns186p702 Ns186p124 Ns186p702 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p704 := Ns186p658 67717 BSN.abs_quadSignPos (BSN.cos_quad_nat0 76 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 57090466 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 11 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 33987011 134217728) qz90 rfl rfl (Ns186p691 RS187to204.d9 RS187to204.d11 RS187to204.d13 RS187to204.d17 (Ns186p695 rfl rfl) (Ns186p697 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns186p690 rfl) RS187to204.d19 RS187to204.d21 RS187to204.d23 RS187to204.d25 RS187to204.d17 (Ns186p701 rfl rfl) (Ns186p703 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns186p705 := nat_lit 27919235927920875244442194657589083373849379864218694771203986391296 

noncomputable def Ns186p706 := nat_lit 2621970826131305642204214973494810538618042412991413854565007616 

noncomputable def Ns186p707 := nat_lit 83752463842110363122042175542820260500470903507830101485902829158656 

noncomputable def Ns186p708 := BSN.cos_dyadic_bound_f 84591842 134217728 3 2 134217728 67108864 Ns186p705 Ns186p117 Ns186p706 Ns186p707 Ns186p120 Ns186p706 108431185 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 84591842) qz364 0 2 Ns186p705 Ns186p117 Ns186p706 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 84591842) qz365 0 2 Ns186p707 Ns186p120 Ns186p706 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p709 := nat_lit 437518254369623974144763460524719455106259062168321871590802055840000 

noncomputable def Ns186p710 := nat_lit 198589085998822981644388512674741506351439864118985763312100000000 

noncomputable def Ns186p711 := nat_lit 1145559617209778980789813386639458515220395212565602734359119127200000 

noncomputable def Ns186p712 := BSN.sin_dyadic_bound_f 145292910 134217728 3 2 134217728 67108864 Ns186p709 Ns186p111 Ns186p710 Ns186p711 Ns186p114 Ns186p710 118533195 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 145292910) qz362 0 2 Ns186p709 Ns186p111 Ns186p710 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 145292910) qz363 0 2 Ns186p711 Ns186p114 Ns186p710 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p713 := Ns186p656 91284 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 42 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 108431185 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 87 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 118533195 134217728) qz90 rfl rfl (Ns186p704 rfl rfl) (Ns186p690 rfl) RS187to204.d27 RS187to204.d29 RS187to204.d31 RS187to204.d33 RS187to204.d17 (Ns186p708 rfl rfl) (Ns186p712 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns186p714 := nat_lit 2974008250940351818239290595490886786352626297590328049906205890249784547286591663641431709866941089390625 

noncomputable def Ns186p715 := nat_lit 2810882091367181122651881232676768491358579634559934104002234405554600136557143330208883301025390625 

noncomputable def Ns186p716 := nat_lit 18011246641638706834156442992093214142539239981843466908389099784135959247605176036175550589918245946990625 

noncomputable def Ns186p717 := BSN.cos_dyadic_bound_f 193822215 134217728 4 3 134217728 67108864 Ns186p714 Ns186p127 Ns186p715 Ns186p716 Ns186p130 Ns186p715 16961029 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 193822215) qz364 0 3 Ns186p714 Ns186p127 Ns186p715 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 193822215) qz365 0 3 Ns186p716 Ns186p130 Ns186p715 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p718 := Ns186p654 Bool.false 230296409 91284 Bool.true 193822215 7074237752028440 1 Bool.false 16961029 Bool.true Bool.false 224299780 101720 BSN.abs_quadSignNeg qz431 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 16961029 134217728) qz90 rfl (Ns186p713 rfl) (Ns186p690 rfl) RS187to204.d35 RS187to204.d37 RS187to204.d17 (Ns186p717 rfl rfl) rfl 

noncomputable def Ns186p719 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 8) 224299780 134217728 101720 134217728 224299780 134217728 101720 134217728 60210013724999680 56074945 16777216 12715 8388608 (Ns186p718 rfl rfl rfl rfl) 

noncomputable def Ns186p720 := @Enclosure.Real.IsNear.mulLit_ff qz689 (Zeta.RiemannSiegel.correction qz89) 2865469 8388608 1 8388608 55076385891785 140737488355328 597536960440871 19791209299968000000 157819676404947272165 1180591620717411303424 

noncomputable abbrev qz692 := (@HPow.hPow Real Real Real qz7 qz88 qz9)

noncomputable def Ns186p721 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz692 1 1 0 1 2865469 8388608 1 8388608 2865469 8388608 1 8388608 

noncomputable def Ns186p722 := @Enclosure.Real.IsNear.sqrt_image qz88 308060990667 4194304000 115371 4194304000 71891611 71891639 8388608 (@Enclosure.Real.IsNear.of_eq qz88 (@HMul.hMul Real Real Real qz5 qz87 qz3) Bool.false 308060990667 4194304000 115371 4194304000 (BSN.t_div_two_pi_mk qz87 461484 1000 qz90) (@Enclosure.Real.IsNear.mulLit_ff qz87 qz3 461484 1000 0 1 2670177 16777216 1 16777216 308060990667 4194304000 115371 4194304000 (Enclosure.Real.IsNear.const Bool.false 461484 1000) RS187to204.d40 rfl)) 

noncomputable abbrev qz916 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 461484 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz693 := qz916

noncomputable abbrev qz445 := qz693

noncomputable abbrev qz92 := qz445

noncomputable def Ns186p723 := @Enclosure.Real.IsNear.sqrt_image qz92 71891625 8388608 7 4194304 24557494 24557500 8388608 (@Enclosure.Real.IsNear.recentre' qz92 Bool.false 143783250 16777216 28 16777216 71891625 8388608 7 4194304 (Ns186p722 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns186p724 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz92) 24557497 8388608 3 8388608 2865468 2865470 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz92) Bool.false 49114994 16777216 6 16777216 24557497 8388608 3 8388608 (Ns186p723 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns186p725 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz92)) Bool.false 5730938 16777216 2 16777216 2865469 8388608 1 8388608 (Ns186p724 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz93 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz438))

noncomputable abbrev qz694 := (@HMul.hMul Real Real Real qz891 qz915 qz915)

noncomputable abbrev qz446 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz694 qz688) qz640)

noncomputable abbrev qz94 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz446))

noncomputable def Ns186p726 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz89) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz93) qz94) Bool.false 55076385891785 

noncomputable def Ns186p727 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz93) qz94 18550115 16777216 227 

noncomputable abbrev qz695 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz93))

noncomputable def Ns186p728 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz93) (@Neg.neg Real Real.instNeg qz695) Bool.true 18550115 16777216 227 16777216 (BSN.inv_eq_neg_inv_neg qz93) 

noncomputable def Ns186p729 := @Enclosure.Real.IsNear.recentre' qz695 Bool.false 18550115 16777216 227 16777216 18550115 16777216 

noncomputable def Ns186p730 := @Enclosure.Real.IsNear.recentre' qz93 Bool.true 15173759 16777216 415027216 37748736000000 15173759 16777216 25939201 2359296000000 

noncomputable abbrev qz95 := (@HMul.hMul Real Real Real qz342 qz340 qz438)

noncomputable def Ns186p731 := @Enclosure.Real.IsNear.cos_image qz95 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 60101947) qz360) Bool.false 60101947 16777216 177 16777216 Bool.true 15173759 16777216 1 

noncomputable def Ns186p732 := nat_lit 7556101115354004810630681 

noncomputable def Ns186p733 := nat_lit 720575940379279360000000000000 

noncomputable def Ns186p734 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz89 884279719003555 140737488355328 1 500000000000000 4782761 8388608 7 4194304 4229298553141161715355 1180591620717411303424 Ns186p732 

noncomputable def Ns186p735 := @Enclosure.Real.IsNear.subLit_ff_p qz92 qz1 71891625 8388608 7 4194304 8 1 0 1 4782761 4782761 8388608 7 

noncomputable def Ns186p736 := @Ns186p735 4194304 (@Enclosure.Real.IsNear.recentre' qz92 Bool.false 143783250 16777216 28 16777216 71891625 8388608 7 4194304 (Ns186p722 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns186p737 := @Enclosure.Real.IsNear.recentre' qz95 Bool.false 4229298553141161715355 1180591620717411303424 Ns186p732 Ns186p733 60101947 16777216 177 16777216 (@Ns186p734 Ns186p733 RS187to204.d39 (Ns186p736 rfl rfl) rfl) 

noncomputable def Ns186p738 := nat_lit 52603922775842275764097200041129776779121 

noncomputable def Ns186p739 := BSN.cos_dyadic_bound_f 15144485819 34359738368 2 1 16777216 4504395 Ns186p738 Ns186p276 Ns186p738 Ns186p738 Ns186p277 Ns186p738 15173759 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 15144485819) qz371 0 1 Ns186p738 Ns186p276 Ns186p738 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 15144485819) qz372 0 1 Ns186p738 Ns186p277 Ns186p738 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p740 := @Ns186p731 2250000 (Ns186p737 rfl) (Enclosure.sfrac_false_div 60101947 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 60101947) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1065698448357444733108224) qz361) 226375608064910080 72057594037927936 Bool.false 15173759 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 60101947 16777216 226375608064910080 72057594037927936 0 1065698448357444733108224 Ns186p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 15173759 16777216 1065698448357444733108224 Ns186p89 15144485819 34359738368 4504395 4500000 (Ns186p739 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p741 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz93) 15173759 16777216 25939201 2359296000000 9274944 9275171 8388608 (@Enclosure.Real.IsNear.neg qz93 Bool.true 15173759 16777216 25939201 2359296000000 (Ns186p730 (Ns186p740 rfl rfl) rfl)) 

noncomputable def Ns186p742 := Ns186p728 (@Enclosure.Real.IsNear.neg qz695 Bool.false 18550115 16777216 227 16777216 (@Ns186p729 227 16777216 (Ns186p741 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p743 := @Enclosure.Real.IsNear.recentre' qz94 Bool.true 2969059 8388608 

noncomputable abbrev qz96 := (@HMul.hMul Real Real Real qz342 qz340 qz446)

noncomputable def Ns186p744 := @Enclosure.Real.IsNear.cos_image qz96 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16211623)) qz429) Bool.true 16211623 8388608 

noncomputable def Ns186p745 := nat_lit 19139306832952009102950655405 

noncomputable def Ns186p746 := nat_lit 105986974603587810076477671142011 

noncomputable def Ns186p747 := @Enclosure.Real.IsNear.recentre' qz96 Bool.true Ns186p745 Ns186p427 Ns186p746 

noncomputable def Ns186p748 := nat_lit 4722366482869645213696000000000000000 

noncomputable abbrev qz97 := qz446

noncomputable def Ns186p749 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz97 884279719003555 140737488355328 1 500000000000000 21643950914671 

noncomputable abbrev qz447 := (@HSub.hSub Real Real Real qz633 qz694 qz688)

noncomputable abbrev qz98 := qz447

noncomputable def Ns186p750 := @Enclosure.Real.IsNear.subLit_tf qz98 qz26 17245904403567 70368744177664 3927469 1099511627776 1 16 

noncomputable abbrev qz448 := qz694

noncomputable abbrev qz99 := qz448

noncomputable def Ns186p751 := @Enclosure.Real.IsNear.subLit_ff_n qz99 qz89 22874802783121 70368744177664 2092461 1099511627776 4782761 8388608 7 4194304 

noncomputable def Ns186p752 := @Enclosure.Real.IsNear.mulLit_ff qz89 qz89 4782761 8388608 7 4194304 4782761 8388608 7 4194304 22874802783121 70368744177664 

noncomputable def Ns186p753 := nat_lit 34083656737716959407370521170898327912348276256845852869396368466605703082730129576398116001 

noncomputable def Ns186p754 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600 

noncomputable def Ns186p755 := nat_lit 329547444668383673129386354269323839817071406075931234427010101817960822534750802498721 

noncomputable def Ns186p756 := nat_lit 205637381156418501675197956177635110405454247783829829846791675035724007100379804278902969505 

noncomputable def Ns186p757 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600 

noncomputable def Ns186p758 := BSN.cos_dyadic_bound_t 16211623 8388608 4 3 8388608 2250000 Ns186p753 Ns186p754 Ns186p755 Ns186p756 Ns186p757 Ns186p755 2969059 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16211623) (BSN.cosEvenQ 8388608) 0 3 Ns186p753 Ns186p754 Ns186p755 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16211623) (BSN.cosOddQ 8388608) 0 3 Ns186p756 Ns186p757 Ns186p755 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p759 := @Ns186p743 433638608 18874368000000 2969059 8388608 27102413 1179648000000 (@Ns186p744 189 8388608 Bool.true 2969059 8388608 1 2250000 (@Ns186p747 Ns186p748 16211623 8388608 189 8388608 (@Ns186p749 70368744177664 3927469 1099511627776 Ns186p745 Ns186p427 Ns186p746 Ns186p748 RS187to204.d39 (@Ns186p750 0 1 346303214634736 21643950914671 70368744177664 3927469 1099511627776 (@Ns186p751 144669131646997364736 17245904403567 70368744177664 3927469 1099511627776 (@Ns186p752 2092461 1099511627776 (Ns186p736 rfl rfl) (Ns186p736 rfl rfl) rfl) (Ns186p736 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16211623 8388608) (BSN.cos_neg_of_bound 16211623 8388608 Bool.true 2969059 8388608 1 2250000 (Ns186p758 rfl rfl)) rfl rfl) 

noncomputable def Ns186p760 := @Ns186p720 343993870160106977999 Ns186p651 (Ns186p721 qz28 (@Enclosure.Real.IsNear.of_eq qz692 (@Inv.inv Real Real.instInv (Real.sqrt qz92)) Bool.false 2865469 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz88 (BSN.t_div_two_pi_nonneg qz87 461484 1000 qz90)) Ns186p725) rfl) (@Ns186p726 140737488355328 597536960440871 19791209299968000000 (BSN.correction_mk qz89 (BSN.cos_two_pi_p_ne_zero_mk qz87 461484 1000 8 qz90 rfl rfl (@BSN.floor_sqrt_eq_dec qz87 461484 1000 8 qz90 rfl rfl rfl))) (@Ns186p727 16777216 2969059 8388608 27102413 1179648000000 55076385891785 140737488355328 597536960440871 19791209299968000000 Ns186p742 (Ns186p759 rfl) rfl)) 

noncomputable def Ns186p761 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz87) (hardyZApproximantRS₀ qz87) Bool.false 3788103783076631756315 1180591620717411303424 50673039119978730977999 Ns186p651 (@Eq.refl Real (hardyZApproximantRS₀ qz87)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz87) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz87) qz87 8) (@HMul.hMul Real Real Real qz5 qz689 (Zeta.RiemannSiegel.correction qz89))) Bool.false 3788103783076631756315 1180591620717411303424 50673039119978730977999 Ns186p651 (BSN.hardyZApproximantRS₀_eq qz87 8 (@BSN.floor_sqrt_eq_dec qz87 461484 1000 8 qz90 rfl rfl rfl)) (@Ns186p653 3788103783076631756315 1180591620717411303424 50673039119978730977999 Ns186p651 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz87) qz87 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 8)) Bool.false 56074945 16777216 12715 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz87) qz87 8) (Ns186p719 (Ns186p718 rfl rfl rfl rfl) rfl rfl)) (Ns186p760 rfl) rfl rfl)) 

theorem RS187to204.d48 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz87) Bool.false 3788103783076631756315 1180591620717411303424 50673039119978730977999 Ns186p651 := Ns186p761 

noncomputable def Ns186p762 := nat_lit 11854051784882952512278102016 

noncomputable abbrev qz917 := (Enclosure.sfrac Bool.false 462946 1000)

noncomputable abbrev qz696 := qz917

noncomputable abbrev qz449 := qz696

noncomputable abbrev qz100 := qz449

noncomputable abbrev qz918 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 462946 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz697 := qz918

noncomputable abbrev qz450 := qz697

noncomputable abbrev qz101 := qz450

noncomputable abbrev qz919 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 462946 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz698 := qz919

noncomputable abbrev qz451 := qz698

noncomputable abbrev qz102 := qz451

noncomputable abbrev qz699 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz101 qz9))

noncomputable def Ns186p763 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz100) qz100 8) (@HMul.hMul Real Real Real qz5 qz699 (Zeta.RiemannSiegel.correction qz102)) 156127993 33554432 102045 67108864 9949185443856927077 73786976294838206464 363787526695348850171 Ns186p651 Ns186p762 

noncomputable def Ns186p764 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz100) qz100 Real.cos BSN.quadSignNeg 7 8 462946 1000 126 134217728 67108864 2251799813685248 Bool.false 102462689041 1805 279097919 60 47453128 8 

noncomputable def Ns186p765 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz100) qz100 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 462946 1000 42 87 134217728 67108864 2251799813685248 Bool.false 102462689041 1805 

noncomputable def Ns186p766 := Ns186p765 240485871 61 54794152 8 261175631 61 50729528 8 Bool.true 282905165 67935 Bool.true 14477001 Bool.true 105426498 7074237752028440 1 Bool.false 133437725 Bool.true Bool.false 94914850 Bool.false Bool.true 301506445 

noncomputable def Ns186p767 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz100) qz100 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 462946 1000 77 11 134217728 67108864 2251799813685248 Bool.false 102462689041 1805 

noncomputable def Ns186p768 := Ns186p767 186065264 60 67108856 8 216015088 60 60023992 8 Bool.true 292840599 39894 Bool.false 90708345 Bool.false 140252256 7074237752028440 1 Bool.false 83959223 Bool.true Bool.false 116085561 Bool.false Bool.true 282905165 

noncomputable def Ns186p769 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz100) qz100 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 462946 1000 281 162 134217728 67108864 2251799813685248 Bool.false 102462689041 1805 

noncomputable def Ns186p770 := Ns186p769 93032624 60 94906264 8 147453232 60 77490640 16 Bool.true 134217704 1868 Bool.false 150739219 Bool.false 45553409 7074237752028440 1 Bool.false 120989824 Bool.true Bool.false 126561251 Bool.true Bool.true 292840599 

noncomputable def Ns186p771 := nat_lit 9519008353050733371218057309119294296472361886243066701 

noncomputable def Ns186p772 := nat_lit 12469121061622861343281924189694571691592009121792000 

noncomputable def Ns186p773 := nat_lit 10206908012228348527565571988480000 

noncomputable def Ns186p774 := nat_lit 28351498853278056556705278557489172480 

noncomputable abbrev qz452 := (@Eq.refl Real qz696)

noncomputable abbrev qz103 := qz452

noncomputable def Ns186p775 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz100 462946 1000 857276995664 16000000 925892 4000 2000 Ns186p773 Ns186p774 qz103 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns186p776 := nat_lit 194949291070479019442545813690763147191753971430258006036480 

noncomputable abbrev qz700 := (Real.log (Enclosure.sfrac Bool.false 857276995664 16000000))

noncomputable abbrev qz104 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 462946 4000) qz700) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 925892))))))

noncomputable abbrev qz701 := (Enclosure.sfrac Bool.false 462946 2000)

noncomputable abbrev qz453 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz104 qz701) (@HMul.hMul Real Real Real qz5 qz701 (Real.log Real.pi)))

noncomputable def Ns186p777 := @Enclosure.Real.IsNear.addLit_ft_p qz453 (Enclosure.sfrac Bool.true Ns186p773 Ns186p774) 6876157906677756681801 9007199254740992000 8257137483501259 614400000000000000000 Ns186p773 Ns186p774 0 1 Ns186p776 

noncomputable def Ns186p778 := nat_lit 230725572900881132492037292032000 

noncomputable abbrev qz454 := (@HSub.hSub Real Real Real qz12 qz104 qz701)

noncomputable abbrev qz455 := (@HMul.hMul Real Real Real qz5 qz701 (Real.log Real.pi))

noncomputable def Ns186p779 := @Enclosure.Real.IsNear.subLit_ff_p qz454 qz455 9262832063219036151369 9007199254740992000 7849102083407 1200000000000000000 8891054080953 33554432000 231473 33554432000 Ns186p778 6876157906677756681801 9007199254740992000 

noncomputable def Ns186p780 := nat_lit 3705132825287614460547600 

noncomputable abbrev qz456 := qz701

noncomputable def Ns186p781 := @Enclosure.Real.IsNear.subLit_ff_p qz104 qz456 2269551099262339558517 1801439850948198400 7849102083407 1200000000000000000 462946 2000 0 1 Ns186p780 9262832063219036151369 9007199254740992000 7849102083407 1200000000000000000 

noncomputable def Ns186p782 := nat_lit 5110574742468086007478402815115657216 

noncomputable def Ns186p783 := nat_lit 26327811507221524895498240 

noncomputable def Ns186p784 := nat_lit 6534670579196418232790960865475616935816071952931576095656086448380091028426197304463838242003229249037580025169659031032592826984735875288095743016960 

noncomputable def Ns186p785 := nat_lit 131139785242518833707991211033257013530125361771051198842760790456193292298794317447028913545590992509676504299181603864845816685442512794542210547712 

noncomputable def Ns186p786 := nat_lit 19318930151170379387366271620052276217576579494237823388088810231282728297859988320019567872446507386932884272728534896907921429573530466385920 

noncomputable def Ns186p787 := BSN.log_dyadic_bound 332988995664 1381564995664 7 6 Ns186p784 67108864 18000000 Ns186p785 Ns186p786 32998765 1714553991328 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 332988995664) (BSN.artanhQ 1381564995664) 0 6 Ns186p785 Ns186p784 Ns186p786 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns186p788 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 462946 4000) qz700 462946 4000 0 1 49039370393793145 4503599627370496 100000027 1800000000000000 2270258036632496130517 1801439850948198400 23147306249771 3600000000000000000 (Enclosure.Real.IsNear.const Bool.false 462946 4000) (BSN.isNear_log_sfrac 857276995664 16000000 49039370393793145 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 857276995664) qz353)) Bool.false Ns186p783 Ns186p89 1000000270000000 18000000000000000000000 49039370393793145 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 857276995664 16000000 15 1714553991328 1048576000000 32998765 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns186p787 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p789 := BSN.arctan_dyadic_bound_f 1000 925892 1 0 8388608 2250000 0 1 1 0 1 1 9060 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 925892) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 925892) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz457 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 925892)))

noncomputable def Ns186p790 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz457 884279719003555 562949953421312 1 2000000000000000 9060 8388608 1 2250000 7412775598492976414720 883671712695715 562949953421312 8000000009 18000000000000000 qz16 (Ns186p789 rfl) rfl rfl 

noncomputable def Ns186p791 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 462946 4000) qz700) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz457)) 2270258036632496130517 1801439850948198400 23147306249771 3600000000000000000 883671712695715 2251799813685248 8000000009 72000000000000000 Ns186p782 2269551099262339558517 1801439850948198400 7849102083407 1200000000000000000 (Ns186p788 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz457) 1 4 0 1 883671712695715 562949953421312 8000000009 18000000000000000 883671712695715 2251799813685248 8000000009 72000000000000000 qz356 Ns186p790 rfl) 

noncomputable def Ns186p792 := @Ns186p777 Ns186p771 Ns186p772 8257137483501259 614400000000000000000 (@Ns186p779 8257137483501259 614400000000000000000 (Ns186p781 (Ns186p791 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 462946 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz456 (Real.log Real.pi) 462946 2000 0 1 38410761 33554432 1 33554432 8891054080953 33554432000 231473 33554432000 (Enclosure.Real.IsNear.const Bool.false 462946 2000) RS187to204.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns186p773 Ns186p774) 

noncomputable def Ns186p793 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz100) Bool.false Ns186p771 Ns186p772 8257137483501259 614400000000000000000 6403918065 8388608 113 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz100) (@HAdd.hAdd Real Real Real qz357 qz453 (Enclosure.sfrac Bool.true Ns186p773 Ns186p774)) Bool.false Ns186p771 Ns186p772 8257137483501259 614400000000000000000 Ns186p775 (Ns186p792 rfl rfl)) 

noncomputable def Ns186p794 := nat_lit 1898381503033939098337280 

noncomputable def Ns186p795 := nat_lit 856062143017683018503472001703413070349836772131538798995369024048283535767451460294046486522583155048928974003804887225622232936966161 

noncomputable def Ns186p796 := nat_lit 608701350586004551569425864456819040302051730681376439949008702505372751414234441883374005285160793676294643968491801254198994961 

noncomputable def Ns186p797 := nat_lit 4274998550517160833472077889283392035111749869626275624388893094093686534134336880405997879509490368469598777445554164548630059696482321 

noncomputable def Ns186p798 := BSN.sin_dyadic_bound_f 53955247467 34359738368 4 3 16777216 4504395 Ns186p795 Ns186p102 Ns186p796 Ns186p797 Ns186p105 Ns186p796 16777213 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53955247467) qz358 0 3 Ns186p795 Ns186p102 Ns186p796 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53955247467) qz359 0 3 Ns186p797 Ns186p105 Ns186p796 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p799 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz100) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6403918065) qz429) Bool.false 6403918065 8388608 113 8388608 Bool.true 16777213 16777216 1 2250000 (Ns186p793 rfl) (Enclosure.sfrac_false_div 6403918065 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6403918065) qz429) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p794) qz430) 226375608064910080 72057594037927936 Bool.false 16777213 16777216 121 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 6403918065 8388608 226375608064910080 72057594037927936 121 Ns186p794 Ns186p578 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777213 16777216 Ns186p794 Ns186p578 53955247467 34359738368 4504395 4500000 (Ns186p798 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p800 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz100) Bool.false Ns186p771 Ns186p772 8257137483501259 614400000000000000000 102462689041 134217728 1805 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz100) (@HAdd.hAdd Real Real Real qz357 qz453 (Enclosure.sfrac Bool.true Ns186p773 Ns186p774)) Bool.false Ns186p771 Ns186p772 8257137483501259 614400000000000000000 Ns186p775 (Ns186p792 rfl rfl)) 

noncomputable def Ns186p801 := Ns186p770 39894 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 281 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 120989824 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 162 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 126561251 134217728) qz103 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 1) Bool.true 16777213 16777216 16414913 1179648000000 134217704 134217728 1868 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz100)) Bool.true 16777213 16777216 16414913 1179648000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz100) qz100) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz100)) Bool.true 16777213 16777216 262638608 18874368000000 16777213 16777216 16414913 1179648000000 (Ns186p799 rfl rfl) rfl)) rfl) (Ns186p800 rfl) RS187to204.d7 

noncomputable def Ns186p802 := nat_lit 506937935817408727350844212922894926892963758746310192966318891250465 

noncomputable def Ns186p803 := nat_lit 266569272310580937780685340395811693618757651564838981032446833441 

noncomputable def Ns186p804 := nat_lit 1327263005461853345352947067104083970549046141471136004180592182211361 

noncomputable def Ns186p805 := BSN.sin_dyadic_bound_f 150739219 134217728 3 2 134217728 67108864 Ns186p802 Ns186p111 Ns186p803 Ns186p804 Ns186p114 Ns186p803 120989824 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 150739219) qz362 0 2 Ns186p802 Ns186p111 Ns186p803 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 150739219) qz363 0 2 Ns186p804 Ns186p114 Ns186p803 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p806 := nat_lit 2347663110597919747561218726535572501408271695142441524132186470401 

noncomputable def Ns186p807 := nat_lit 18542447772547025370741979669351064761217416094348274562283521 

noncomputable def Ns186p808 := nat_lit 7042952246898214148632914695647378802095292650595135875847434844161 

noncomputable def Ns186p809 := BSN.cos_dyadic_bound_f 45553409 134217728 3 2 134217728 67108864 Ns186p806 Ns186p117 Ns186p807 Ns186p808 Ns186p120 Ns186p807 126561251 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 45553409) qz364 0 2 Ns186p806 Ns186p117 Ns186p807 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 45553409) qz365 0 2 Ns186p808 Ns186p120 Ns186p807 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p810 := nat_lit 66441625805199648112281596419671500131372781588188542980348136530625 

noncomputable def Ns186p811 := nat_lit 4583296417832619885240691933997291484205232943082834893687890625 

noncomputable def Ns186p812 := nat_lit 174006361295608301766637600931246504729287619496681192739655339090625 

noncomputable def Ns186p813 := BSN.sin_dyadic_bound_f 90708345 134217728 3 2 134217728 67108864 Ns186p810 Ns186p111 Ns186p811 Ns186p812 Ns186p114 Ns186p811 83959223 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 90708345) qz362 0 2 Ns186p810 Ns186p111 Ns186p811 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 90708345) qz363 0 2 Ns186p812 Ns186p114 Ns186p811 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p814 := nat_lit 379867332125681839900622030283895071046175831755652468585005307658240 

noncomputable def Ns186p815 := nat_lit 149719664737251357846220492970929307656811942579450599514220527616 

noncomputable def Ns186p816 := nat_lit 994648228491020697541306674707296062432349482881580211990086115393536 

noncomputable def Ns186p817 := BSN.sin_dyadic_bound_f 140252256 134217728 3 2 134217728 67108864 Ns186p814 Ns186p111 Ns186p815 Ns186p816 Ns186p114 Ns186p815 116085561 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 140252256) qz362 0 2 Ns186p814 Ns186p111 Ns186p815 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 140252256) qz363 0 2 Ns186p816 Ns186p114 Ns186p815 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p818 := Ns186p768 67935 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 77 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 83959223 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 11 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 116085561 134217728) qz103 rfl rfl (Ns186p801 RS187to204.d9 RS187to204.d11 RS187to204.d13 RS187to204.d17 (Ns186p805 rfl rfl) (Ns186p809 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns186p800 rfl) RS187to204.d19 RS187to204.d21 RS187to204.d23 RS187to204.d25 RS187to204.d17 (Ns186p813 rfl rfl) (Ns186p817 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns186p819 := nat_lit 43925267764658095833231908001 

noncomputable def Ns186p820 := BSN.cos_dyadic_bound_f 14477001 134217728 2 1 134217728 67108864 Ns186p819 Ns186p134 Ns186p819 Ns186p819 Ns186p135 Ns186p819 133437725 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 14477001) qz364 0 1 Ns186p819 Ns186p134 Ns186p819 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 14477001) qz365 0 1 Ns186p819 Ns186p135 Ns186p819 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p821 := nat_lit 121248146723746894954665937334805018694606110340484442678307303522560 

noncomputable def Ns186p822 := nat_lit 15261535976668521571926217419408390366966975346789509492875264256 

noncomputable def Ns186p823 := nat_lit 317529960837279642513008622001048387758612342455469214475435425464576 

noncomputable def Ns186p824 := BSN.sin_dyadic_bound_f 105426498 134217728 3 2 134217728 67108864 Ns186p821 Ns186p111 Ns186p822 Ns186p823 Ns186p114 Ns186p822 94914850 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 105426498) qz362 0 2 Ns186p821 Ns186p111 Ns186p822 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 105426498) qz363 0 2 Ns186p823 Ns186p114 Ns186p822 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p825 := Ns186p766 91576 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 42 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133437725 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 87 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 94914850 134217728) qz103 rfl rfl (Ns186p818 rfl rfl) (Ns186p800 rfl) RS187to204.d27 RS187to204.d29 RS187to204.d31 RS187to204.d33 RS187to204.d17 (Ns186p820 rfl rfl) (Ns186p824 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns186p826 := nat_lit 2218499774196419108812882135171094380263714864365035084545090486484539652211976957001027958504577497234961 

noncomputable def Ns186p827 := nat_lit 1169090234096481655015686057410158138249756629199606465273187032342837566600462341484586183851441681 

noncomputable def Ns186p828 := nat_lit 13441588692314010962716989896689932841104332599882708691382988111289486105919183327408781430249790415502865 

noncomputable def Ns186p829 := BSN.cos_dyadic_bound_f 180158187 134217728 4 3 134217728 67108864 Ns186p826 Ns186p127 Ns186p827 Ns186p828 Ns186p130 Ns186p827 30404296 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 180158187) qz364 0 3 Ns186p826 Ns186p127 Ns186p827 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 180158187) qz365 0 3 Ns186p828 Ns186p130 Ns186p827 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p830 := Ns186p764 Bool.true 301506445 91576 Bool.true 180158187 7074237752028440 1 Bool.false 30404296 Bool.true Bool.true 312255986 102045 BSN.abs_quadSignNeg qz431 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 30404296 134217728) qz103 rfl (Ns186p825 rfl) (Ns186p800 rfl) RS187to204.d35 RS187to204.d37 RS187to204.d17 (Ns186p829 rfl rfl) rfl 

noncomputable def Ns186p831 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 8) 312255986 134217728 102045 134217728 312255986 134217728 102045 134217728 83820577990639616 156127993 33554432 102045 67108864 (Ns186p830 rfl rfl rfl rfl) 

noncomputable def Ns186p832 := @Enclosure.Real.IsNear.mulLit_ff qz699 (Zeta.RiemannSiegel.correction qz102) 715801 2097152 1 8388608 13899373490477 35184372088832 632549620403831 19791209299968000000 9949185443856927077 73786976294838206464 

noncomputable abbrev qz702 := (@HPow.hPow Real Real Real qz7 qz101 qz9)

noncomputable def Ns186p833 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz702 1 1 0 1 715801 2097152 1 8388608 715801 2097152 1 8388608 

noncomputable def Ns186p834 := @Enclosure.Real.IsNear.sqrt_image qz101 618073880721 8388608000 231473 8388608000 72005399 72005427 8388608 (@Enclosure.Real.IsNear.of_eq qz101 (@HMul.hMul Real Real Real qz5 qz100 qz3) Bool.false 618073880721 8388608000 231473 8388608000 (BSN.t_div_two_pi_mk qz100 462946 1000 qz103) (@Enclosure.Real.IsNear.mulLit_ff qz100 qz3 462946 1000 0 1 2670177 16777216 1 16777216 618073880721 8388608000 231473 8388608000 (Enclosure.Real.IsNear.const Bool.false 462946 1000) RS187to204.d40 rfl)) 

noncomputable abbrev qz920 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 462946 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz703 := qz920

noncomputable abbrev qz458 := qz703

noncomputable abbrev qz105 := qz458

noncomputable def Ns186p835 := @Enclosure.Real.IsNear.sqrt_image qz105 72005413 8388608 7 4194304 24576921 24576927 8388608 (@Enclosure.Real.IsNear.recentre' qz105 Bool.false 144010826 16777216 28 16777216 72005413 8388608 7 4194304 (Ns186p834 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns186p836 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz105) 6144231 2097152 3 8388608 2863203 2863205 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz105) Bool.false 49153848 16777216 6 16777216 6144231 2097152 3 8388608 (Ns186p835 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns186p837 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz105)) Bool.false 5726408 16777216 2 16777216 715801 2097152 1 8388608 (Ns186p836 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz106 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz451))

noncomputable abbrev qz704 := (@HMul.hMul Real Real Real qz891 qz919 qz919)

noncomputable abbrev qz459 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz704 qz698) qz640)

noncomputable abbrev qz107 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz459))

noncomputable def Ns186p838 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz102) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz106) qz107) Bool.false 13899373490477 

noncomputable def Ns186p839 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz106) qz107 9699757 8388608 31 

noncomputable abbrev qz705 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz106))

noncomputable def Ns186p840 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz106) (@Neg.neg Real Real.instNeg qz705) Bool.true 9699757 8388608 31 2097152 (BSN.inv_eq_neg_inv_neg qz106) 

noncomputable def Ns186p841 := @Enclosure.Real.IsNear.recentre' qz705 Bool.false 19399514 16777216 248 16777216 9699757 8388608 

noncomputable def Ns186p842 := @Enclosure.Real.IsNear.recentre' qz106 Bool.true 14509383 16777216 415027216 37748736000000 14509383 16777216 25939201 2359296000000 

noncomputable abbrev qz108 := (@HMul.hMul Real Real Real qz342 qz340 qz451)

noncomputable def Ns186p843 := @Enclosure.Real.IsNear.cos_image qz108 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 61531849) qz360) Bool.false 61531849 16777216 177 16777216 Bool.true 14509383 16777216 1 

noncomputable def Ns186p844 := nat_lit 188902527884338836004444273 

noncomputable def Ns186p845 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz102 884279719003555 140737488355328 1 500000000000000 4896549 8388608 7 4194304 4329918973807138231695 1180591620717411303424 Ns186p844 

noncomputable def Ns186p846 := @Enclosure.Real.IsNear.subLit_ff_p qz105 qz1 72005413 8388608 7 4194304 8 1 0 1 4896549 4896549 8388608 7 

noncomputable def Ns186p847 := @Ns186p846 4194304 (@Enclosure.Real.IsNear.recentre' qz105 Bool.false 144010826 16777216 28 16777216 72005413 8388608 7 4194304 (Ns186p834 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns186p848 := @Enclosure.Real.IsNear.recentre' qz108 Bool.false 4329918973807138231695 1180591620717411303424 Ns186p844 Ns186p159 61531849 16777216 177 16777216 (@Ns186p845 Ns186p159 RS187to204.d39 (Ns186p847 rfl rfl) rfl) 

noncomputable def Ns186p849 := nat_lit 1271769044017487196192768 

noncomputable def Ns186p850 := nat_lit 249828659718298382767137252649677987689091129626994372066033685529214592802036597190625 

noncomputable def Ns186p851 := nat_lit 78328409734541396139472704083124282315821843750582265496873076360672620779474006646456320 

noncomputable def Ns186p852 := nat_lit 11382236177157364808757550176186936103893626324008490860684593116058502713000390625 

noncomputable def Ns186p853 := nat_lit 749463214682540833571794242848681589195065601628335099216379687401411661400683790790625 

noncomputable def Ns186p854 := nat_lit 3524778438054362826276271683740592704211982968776201947359288436230267935076330299090534400 

noncomputable def Ns186p855 := BSN.cos_dyadic_bound_f 18072925115 34359738368 3 2 16777216 4504395 Ns186p850 Ns186p851 Ns186p852 Ns186p853 Ns186p854 Ns186p852 14509383 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 18072925115) qz371 0 2 Ns186p850 Ns186p851 Ns186p852 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 18072925115) qz372 0 2 Ns186p853 Ns186p854 Ns186p852 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p856 := @Ns186p843 2250000 (Ns186p848 rfl) (Enclosure.sfrac_false_div 61531849 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 61531849) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p849) qz361) 226375608064910080 72057594037927936 Bool.false 14509383 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 61531849 16777216 226375608064910080 72057594037927936 0 Ns186p849 Ns186p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 14509383 16777216 Ns186p849 Ns186p89 18072925115 34359738368 4504395 4500000 (Ns186p855 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p857 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz106) 14509383 16777216 25939201 2359296000000 9699633 9699881 8388608 (@Enclosure.Real.IsNear.neg qz106 Bool.true 14509383 16777216 25939201 2359296000000 (Ns186p842 (Ns186p856 rfl rfl) rfl)) 

noncomputable def Ns186p858 := Ns186p840 (@Enclosure.Real.IsNear.neg qz705 Bool.false 9699757 8388608 31 2097152 (@Ns186p841 31 2097152 (Ns186p857 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p859 := @Enclosure.Real.IsNear.recentre' qz107 Bool.true 2865922 8388608 

noncomputable abbrev qz109 := (@HMul.hMul Real Real Real qz342 qz340 qz459)

noncomputable abbrev qz460 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable def Ns186p860 := @Enclosure.Real.IsNear.cos_image qz109 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8050809)) qz460) Bool.true 8050809 4194304 

noncomputable def Ns186p861 := nat_lit 19009435854757591881357584725 

noncomputable def Ns186p862 := nat_lit 17172864344975996949427410025171 

noncomputable def Ns186p863 := @Enclosure.Real.IsNear.recentre' qz109 Bool.true Ns186p861 Ns186p427 Ns186p862 

noncomputable def Ns186p864 := nat_lit 755578637259143234191360000000000000 

noncomputable abbrev qz110 := qz459

noncomputable def Ns186p865 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz110 884279719003555 140737488355328 1 500000000000000 21497084515495 

noncomputable abbrev qz461 := (@HSub.hSub Real Real Real qz633 qz704 qz698)

noncomputable abbrev qz111 := qz461

noncomputable def Ns186p866 := @Enclosure.Real.IsNear.subLit_tf qz111 qz26 17099038004391 70368744177664 15909005 4398046511104 1 16 

noncomputable abbrev qz462 := qz704

noncomputable abbrev qz112 := qz462

noncomputable def Ns186p867 := @Enclosure.Real.IsNear.subLit_ff_n qz112 qz102 23976192109401 70368744177664 8568973 4398046511104 4896549 8388608 7 4194304 

noncomputable def Ns186p868 := @Enclosure.Real.IsNear.mulLit_ff qz102 qz102 4896549 8388608 7 4194304 4896549 8388608 7 4194304 23976192109401 70368744177664 

noncomputable def Ns186p869 := nat_lit 8095841770605181368977176372323445369718709353657946729139479168348297149531585141104161 

noncomputable def Ns186p870 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600 

noncomputable def Ns186p871 := nat_lit 74143704470650438340463789679469082345721190067129963229587813528779361431969422881 

noncomputable def Ns186p872 := nat_lit 48851957087274293580133911014403856127535268557671827119772778457311575898925894625746465 

noncomputable def Ns186p873 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600 

noncomputable def Ns186p874 := BSN.cos_dyadic_bound_t 8050809 4194304 4 3 8388608 2250000 Ns186p869 Ns186p870 Ns186p871 Ns186p872 Ns186p873 Ns186p871 2865922 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 8050809) (BSN.cosEvenQ 4194304) 0 3 Ns186p869 Ns186p870 Ns186p871 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 8050809) (BSN.cosOddQ 4194304) 0 3 Ns186p872 Ns186p873 Ns186p871 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p875 := @Ns186p859 878527216 37748736000000 1432961 4194304 54907951 2359296000000 (@Ns186p860 383 16777216 Bool.true 2865922 8388608 1 2250000 (@Ns186p863 Ns186p864 8050809 4194304 383 16777216 (@Ns186p865 70368744177664 15909005 4398046511104 Ns186p861 Ns186p427 Ns186p862 Ns186p864 RS187to204.d39 (@Ns186p866 0 1 343953352247920 21497084515495 70368744177664 15909005 4398046511104 (@Ns186p867 143437126995938377728 17099038004391 70368744177664 15909005 4398046511104 (@Ns186p868 8568973 4398046511104 (Ns186p847 rfl rfl) (Ns186p847 rfl rfl) rfl) (Ns186p847 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8050809 4194304) (BSN.cos_neg_of_bound 8050809 4194304 Bool.true 2865922 8388608 1 2250000 (Ns186p874 rfl rfl)) rfl rfl) 

noncomputable def Ns186p876 := @Ns186p832 363787526695348850171 Ns186p651 (Ns186p833 qz28 (@Enclosure.Real.IsNear.of_eq qz702 (@Inv.inv Real Real.instInv (Real.sqrt qz105)) Bool.false 715801 2097152 1 8388608 (BSN.rpow_neg_quarter_mk qz101 (BSN.t_div_two_pi_nonneg qz100 462946 1000 qz103)) Ns186p837) rfl) (@Ns186p838 35184372088832 632549620403831 19791209299968000000 (BSN.correction_mk qz102 (BSN.cos_two_pi_p_ne_zero_mk qz100 462946 1000 8 qz103 rfl rfl (@BSN.floor_sqrt_eq_dec qz100 462946 1000 8 qz103 rfl rfl rfl))) (@Ns186p839 2097152 1432961 4194304 54907951 2359296000000 13899373490477 35184372088832 632549620403831 19791209299968000000 Ns186p858 (Ns186p875 rfl) rfl)) 

noncomputable def Ns186p877 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz100) (hardyZApproximantRS₀ qz100) Bool.true 353278272893516794213 73786976294838206464 50853636352076212850171 Ns186p651 (@Eq.refl Real (hardyZApproximantRS₀ qz100)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz100) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz100) qz100 8) (@HMul.hMul Real Real Real qz5 qz699 (Zeta.RiemannSiegel.correction qz102))) Bool.true 353278272893516794213 73786976294838206464 50853636352076212850171 Ns186p651 (BSN.hardyZApproximantRS₀_eq qz100 8 (@BSN.floor_sqrt_eq_dec qz100 462946 1000 8 qz103 rfl rfl rfl)) (@Ns186p763 353278272893516794213 73786976294838206464 50853636352076212850171 Ns186p651 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz100) qz100 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 8)) Bool.true 156127993 33554432 102045 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz100) qz100 8) (Ns186p831 (Ns186p830 rfl rfl rfl rfl) rfl rfl)) (Ns186p876 rfl) rfl rfl)) 

theorem RS187to204.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz100) Bool.true 353278272893516794213 73786976294838206464 50853636352076212850171 Ns186p651 := Ns186p877 

noncomputable def Ns186p878 := nat_lit 16155427756060998871220748288 

noncomputable abbrev qz921 := (Enclosure.sfrac Bool.false 464407 1000)

noncomputable abbrev qz706 := qz921

noncomputable abbrev qz463 := qz706

noncomputable abbrev qz113 := qz463

noncomputable abbrev qz922 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 464407 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz707 := qz922

noncomputable abbrev qz464 := qz707

noncomputable abbrev qz114 := qz464

noncomputable abbrev qz923 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 464407 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz708 := qz923

noncomputable abbrev qz465 := qz708

noncomputable abbrev qz115 := qz465

noncomputable abbrev qz709 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz114 qz9))

noncomputable def Ns186p879 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz113) qz113 8) (@HMul.hMul Real Real Real qz5 qz709 (Zeta.RiemannSiegel.correction qz115)) 59307513 33554432 51183 33554432 40205134966559296245 295147905179352825856 12893660584871615719 1106804644422573096960000 Ns186p878 

noncomputable def Ns186p880 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz113) qz113 Real.cos BSN.quadSignNeg 7 8 464407 1000 126 134217728 67108864 2251799813685248 Bool.false 102884415442 1810 279097919 60 47453128 8 

noncomputable def Ns186p881 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz113) qz113 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 464407 1000 41 87 134217728 67108864 2251799813685248 Bool.false 102884415442 1810 

noncomputable def Ns186p882 := Ns186p881 240485871 61 54794152 8 261175631 61 50729528 8 Bool.false 160505348 68149 Bool.true 154929172 Bool.true 65277694 7074237752028440 1 Bool.false 122744388 Bool.true Bool.false 62734464 Bool.false Bool.false 134106563 

noncomputable def Ns186p883 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz113) qz113 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 464407 1000 78 12 134217728 67108864 2251799813685248 Bool.false 102884415442 1810 

noncomputable def Ns186p884 := Ns186p883 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 168040217 40021 Bool.false 29764681 Bool.false 35551899 7074237752028440 1 Bool.false 130930861 Bool.true Bool.false 129536659 Bool.false Bool.false 160505348 

noncomputable def Ns186p885 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz113) qz113 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 464407 1000 283 163 134217728 67108864 2251799813685248 Bool.false 102884415442 1810 

noncomputable def Ns186p886 := Ns186p885 93032624 60 94906264 8 147453232 60 77490640 16 Bool.false 134217720 1876 Bool.false 14887528 Bool.false 41021924 7074237752028440 1 Bool.false 14857018 Bool.false Bool.false 40386229 Bool.false Bool.false 168040217 

noncomputable def Ns186p887 := nat_lit 249359567523572984527877902029468988713390745951875810059 

noncomputable def Ns186p888 := nat_lit 325301693791620884352010290948147070059187964529868800 

noncomputable def Ns186p889 := nat_lit 10368986256491154601985842627360000 

noncomputable def Ns186p890 := nat_lit 28892594431761587645724835033802253120 

noncomputable abbrev qz466 := (@Eq.refl Real qz706)

noncomputable abbrev qz116 := qz466

noncomputable def Ns186p891 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz113 464407 1000 862696446596 16000000 928814 4000 2000 Ns186p889 Ns186p890 qz116 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns186p892 := nat_lit 79795061607543355048920928649430076388285038704600259218880 

noncomputable abbrev qz710 := (Real.log (Enclosure.sfrac Bool.false 862696446596 16000000))

noncomputable abbrev qz117 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 464407 4000) qz710) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 928814))))))

noncomputable abbrev qz711 := (Enclosure.sfrac Bool.false 464407 2000)

noncomputable abbrev qz467 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz117 qz711) (@HMul.hMul Real Real Real qz5 qz711 (Real.log Real.pi)))

noncomputable def Ns186p893 := @Enclosure.Real.IsNear.addLit_ft_p qz467 (Enclosure.sfrac Bool.true Ns186p889 Ns186p890) 2761783790452366918099 3602879701896396800 16565961082719181 1228800000000000000000 Ns186p889 Ns186p890 0 1 Ns186p892 

noncomputable def Ns186p894 := nat_lit 926700863954361949924024647680000 

noncomputable abbrev qz468 := (@HSub.hSub Real Real Real qz12 qz117 qz711)

noncomputable abbrev qz469 := (@HMul.hMul Real Real Real qz5 qz711 (Real.log Real.pi))

noncomputable def Ns186p895 := @Enclosure.Real.IsNear.subLit_ff_p qz468 qz469 18597331358965277215007 18014398509481984000 15746904179963 2400000000000000000 17838226283727 67108864000 464407 67108864000 Ns186p894 2761783790452366918099 3602879701896396800 

noncomputable def Ns186p896 := nat_lit 37194662717930554430014000 

noncomputable abbrev qz470 := qz711

noncomputable def Ns186p897 := @Enclosure.Real.IsNear.subLit_ff_p qz117 qz470 22780337743261777086751 18014398509481984000 15746904179963 2400000000000000000 464407 2000 0 1 Ns186p896 18597331358965277215007 18014398509481984000 15746904179963 2400000000000000000 

noncomputable def Ns186p898 := nat_lit 51296760285963892531888232802704949248 

noncomputable def Ns186p899 := nat_lit 26343048337682423890313216 

noncomputable def Ns186p900 := nat_lit 6848996400120556721578342943963269380616508230177240269097750800742624349761680041738738722336583704145192441623606780810182418902947790868755681116160 

noncomputable def Ns186p901 := nat_lit 140978820373974285878751941746204430370418627697737411814158294534200618423522755014653812615691123558844954421364969184460323741510864525103518973952 

noncomputable def Ns186p902 := nat_lit 23448703023963981371423744226960201595712456297798806951730243271163634342285298509880982443443076999737848805945278547845989612549654781624320 

noncomputable def Ns186p903 := BSN.log_dyadic_bound 338408446596 1386984446596 7 6 Ns186p900 67108864 18000000 Ns186p901 Ns186p902 33421672 1725392893192 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 338408446596) (BSN.artanhQ 1386984446596) 0 6 Ns186p901 Ns186p900 Ns186p902 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns186p904 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 464407 4000) qz710 464407 4000 0 1 49067751202140793 4503599627370496 100000027 1800000000000000 22787407132532599254751 18014398509481984000 46440712538989 7200000000000000000 (Enclosure.Real.IsNear.const Bool.false 464407 4000) (BSN.isNear_log_sfrac 862696446596 16000000 49067751202140793 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 862696446596) qz353)) Bool.false Ns186p899 Ns186p89 1000000270000000 18000000000000000000000 49067751202140793 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 862696446596 16000000 15 1725392893192 1048576000000 33421672 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns186p903 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p905 := BSN.arctan_dyadic_bound_f 1000 928814 1 0 8388608 2250000 0 1 1 0 1 1 9031 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 928814) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 928814) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz471 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 928814)))

noncomputable def Ns186p906 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz471 884279719003555 562949953421312 1 2000000000000000 9031 8388608 1 2250000 7412791924041625632768 883673658852771 562949953421312 8000000009 18000000000000000 qz16 (Ns186p905 rfl) rfl rfl 

noncomputable def Ns186p907 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 464407 4000) qz710) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz471)) 22787407132532599254751 18014398509481984000 46440712538989 7200000000000000000 883673658852771 2251799813685248 8000000009 72000000000000000 Ns186p898 22780337743261777086751 18014398509481984000 15746904179963 2400000000000000000 (Ns186p904 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz471) 1 4 0 1 883673658852771 562949953421312 8000000009 18000000000000000 883673658852771 2251799813685248 8000000009 72000000000000000 qz356 Ns186p906 rfl) 

noncomputable def Ns186p908 := @Ns186p893 Ns186p887 Ns186p888 16565961082719181 1228800000000000000000 (@Ns186p895 16565961082719181 1228800000000000000000 (Ns186p897 (Ns186p907 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 464407 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz470 (Real.log Real.pi) 464407 2000 0 1 38410761 33554432 1 33554432 17838226283727 67108864000 464407 67108864000 (Enclosure.Real.IsNear.const Bool.false 464407 2000) RS187to204.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns186p889 Ns186p890) 

noncomputable def Ns186p909 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz113) Bool.false Ns186p887 Ns186p888 16565961082719181 1228800000000000000000 6430275965 8388608 227 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz113) (@HAdd.hAdd Real Real Real qz357 qz467 (Enclosure.sfrac Bool.true Ns186p889 Ns186p890)) Bool.false Ns186p887 Ns186p888 16565961082719181 1228800000000000000000 Ns186p891 (Ns186p908 rfl rfl)) 

noncomputable def Ns186p910 := nat_lit 1899002745182202154188800 

noncomputable def Ns186p911 := nat_lit 857185527093119390716439807329261514740943515317921221783690840187421596449808665072255166792558381043688159688417339190231773392627361 

noncomputable def Ns186p912 := nat_lit 611096015526224585629031837280111445928235410007398474410836551092828745575784159120399649442517559756884239643048467873627072161 

noncomputable def Ns186p913 := nat_lit 4280601544582615480052219217486413379541399688244989478216552923911095508874536741926570156330998250708876274580441978032254041538127521 

noncomputable def Ns186p914 := BSN.sin_dyadic_bound_f 53972904231 34359738368 4 3 16777216 4504395 Ns186p911 Ns186p102 Ns186p912 Ns186p913 Ns186p105 Ns186p912 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53972904231) qz358 0 3 Ns186p911 Ns186p102 Ns186p912 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53972904231) qz359 0 3 Ns186p913 Ns186p105 Ns186p912 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p915 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz113) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6430275965) qz429) Bool.false 6430275965 8388608 227 16777216 Bool.false 16777215 16777216 1 2250000 (Ns186p909 rfl) (Enclosure.sfrac_false_div 6430275965 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6430275965) qz429) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p910) qz430) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 121 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q3 6430275965 8388608 226375608064910080 72057594037927936 121 Ns186p910 Ns186p578 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns186p910 Ns186p578 53972904231 34359738368 4504395 4500000 (Ns186p914 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p916 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz113) Bool.false Ns186p887 Ns186p888 16565961082719181 1228800000000000000000 102884415442 134217728 1810 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz113) (@HAdd.hAdd Real Real Real qz357 qz467 (Enclosure.sfrac Bool.true Ns186p889 Ns186p890)) Bool.false Ns186p887 Ns186p888 16565961082719181 1228800000000000000000 Ns186p891 (Ns186p908 rfl rfl)) 

noncomputable def Ns186p917 := Ns186p886 40021 BSN.abs_quadSignPos (BSN.cos_quad_nat3 283 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 14857018 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 163 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 40386229 134217728) qz116 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 1) Bool.false 16777215 16777216 32970451 2359296000000 134217720 134217728 1876 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz113)) Bool.false 16777215 16777216 32970451 2359296000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz113) qz113) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz113)) Bool.false 16777215 16777216 527527216 37748736000000 16777215 16777216 32970451 2359296000000 (Ns186p915 rfl rfl) rfl)) rfl) (Ns186p916 rfl) RS187to204.d7 

noncomputable def Ns186p918 := nat_lit 49123620227663780154742214656 

noncomputable def Ns186p919 := BSN.sin_dyadic_bound_f 14887528 134217728 2 1 134217728 67108864 Ns186p918 Ns186p123 Ns186p918 Ns186p918 Ns186p124 Ns186p918 14857018 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 14887528) qz362 0 1 Ns186p918 Ns186p123 Ns186p918 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 14887528) qz363 0 1 Ns186p918 Ns186p124 Ns186p918 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p920 := nat_lit 2831809945699140491174843474176 

noncomputable def Ns186p921 := BSN.sin_dyadic_bound_f 41021924 134217728 2 1 134217728 67108864 Ns186p920 Ns186p123 Ns186p920 Ns186p920 Ns186p124 Ns186p920 40386229 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 41021924) qz362 0 1 Ns186p920 Ns186p123 Ns186p920 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 41021924) qz363 0 1 Ns186p920 Ns186p124 Ns186p920 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p922 := nat_lit 784883012542251666520678761121 

noncomputable def Ns186p923 := BSN.cos_dyadic_bound_f 29764681 134217728 2 1 134217728 67108864 Ns186p922 Ns186p134 Ns186p922 Ns186p922 Ns186p135 Ns186p922 130930861 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 29764681) qz364 0 1 Ns186p922 Ns186p134 Ns186p922 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 29764681) qz365 0 1 Ns186p922 Ns186p135 Ns186p922 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p924 := nat_lit 1597538060799113359404083452401 

noncomputable def Ns186p925 := BSN.cos_dyadic_bound_f 35551899 134217728 2 1 134217728 67108864 Ns186p924 Ns186p134 Ns186p924 Ns186p924 Ns186p135 Ns186p924 129536659 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 35551899) qz364 0 1 Ns186p924 Ns186p134 Ns186p924 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 35551899) qz365 0 1 Ns186p924 Ns186p135 Ns186p924 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p926 := Ns186p884 68149 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 78 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 130930861 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 12 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 129536659 134217728) qz116 rfl rfl (Ns186p917 RS187to204.d9 RS187to204.d11 RS187to204.d13 RS187to204.d17 (Ns186p919 rfl rfl) (Ns186p921 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns186p916 rfl) RS187to204.d19 RS187to204.d21 RS187to204.d23 RS187to204.d25 RS187to204.d17 (Ns186p923 rfl rfl) (Ns186p925 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns186p927 := nat_lit 565729749343238574686492198775291326298226729427104500901813539635200 

noncomputable def Ns186p928 := nat_lit 331944592938044323828952063290846130918937164273473498076518875136 

noncomputable def Ns186p929 := nat_lit 1481135718938963242892708883928054008473867916900259497650721097056256 

noncomputable def Ns186p930 := BSN.sin_dyadic_bound_f 154929172 134217728 3 2 134217728 67108864 Ns186p927 Ns186p111 Ns186p928 Ns186p929 Ns186p114 Ns186p928 122744388 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 154929172) qz362 0 2 Ns186p927 Ns186p111 Ns186p928 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 154929172) qz363 0 2 Ns186p929 Ns186p114 Ns186p928 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p931 := nat_lit 17819215112874107376948919202332847682638346661203043432761173213440 

noncomputable def Ns186p932 := nat_lit 329699609704632573710680619011374772333755919097673442830582016 

noncomputable def Ns186p933 := nat_lit 46668839115302188010699256808917154085849986603091336566895632711936 

noncomputable def Ns186p934 := BSN.sin_dyadic_bound_f 65277694 134217728 3 2 134217728 67108864 Ns186p931 Ns186p111 Ns186p932 Ns186p933 Ns186p114 Ns186p932 62734464 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 65277694) qz362 0 2 Ns186p931 Ns186p111 Ns186p932 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 65277694) qz363 0 2 Ns186p933 Ns186p114 Ns186p932 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p935 := Ns186p882 91864 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 122744388 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 87 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 62734464 134217728) qz116 rfl rfl (Ns186p926 rfl rfl) (Ns186p916 rfl) RS187to204.d27 RS187to204.d29 RS187to204.d31 RS187to204.d33 RS187to204.d17 (Ns186p930 rfl rfl) (Ns186p934 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns186p936 := nat_lit 1605727859366416990797746697211823082219814247230172054125612487429558218460220477797882192179461680336896 

noncomputable def Ns186p937 := nat_lit 443996205774426130484501604813404923657465574993919695833270907767047121500733655463820546358972416 

noncomputable def Ns186p938 := nat_lit 9732338687200749862003325155489819418948228673771789244214350111223705199982173706981332883307485747548160 

noncomputable def Ns186p939 := BSN.cos_dyadic_bound_f 166193846 134217728 4 3 134217728 67108864 Ns186p936 Ns186p127 Ns186p937 Ns186p938 Ns186p130 Ns186p937 43816686 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 166193846) qz364 0 3 Ns186p936 Ns186p127 Ns186p937 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 166193846) qz365 0 3 Ns186p938 Ns186p130 Ns186p937 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p940 := Ns186p880 Bool.false 134106563 91864 Bool.true 166193846 7074237752028440 1 Bool.false 43816686 Bool.true Bool.false 118615026 102366 BSN.abs_quadSignNeg qz431 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 43816686 134217728) qz116 rfl (Ns186p935 rfl) (Ns186p916 rfl) RS187to204.d35 RS187to204.d37 RS187to204.d17 (Ns186p939 rfl rfl) rfl 

noncomputable def Ns186p941 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 8) 118615026 134217728 102366 134217728 118615026 134217728 102366 134217728 31840478592761856 59307513 33554432 51183 33554432 (Ns186p940 rfl rfl rfl rfl) 

noncomputable def Ns186p942 := @Enclosure.Real.IsNear.mulLit_ff qz709 (Zeta.RiemannSiegel.correction qz115) 5721899 16777216 1 16777216 7026536988255 17592186044416 674634880258253 19791209299968000000 40205134966559296245 295147905179352825856 

noncomputable abbrev qz712 := (@HPow.hPow Real Real Real qz7 qz114 qz9)

noncomputable def Ns186p943 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz712 1 1 0 1 5721899 16777216 1 16777216 5721899 16777216 1 16777216 

noncomputable def Ns186p944 := @Enclosure.Real.IsNear.sqrt_image qz114 1240048890039 16777216000 464407 16777216000 72118930 72118958 8388608 (@Enclosure.Real.IsNear.of_eq qz114 (@HMul.hMul Real Real Real qz5 qz113 qz3) Bool.false 1240048890039 16777216000 464407 16777216000 (BSN.t_div_two_pi_mk qz113 464407 1000 qz116) (@Enclosure.Real.IsNear.mulLit_ff qz113 qz3 464407 1000 0 1 2670177 16777216 1 16777216 1240048890039 16777216000 464407 16777216000 (Enclosure.Real.IsNear.const Bool.false 464407 1000) RS187to204.d40 rfl)) 

noncomputable abbrev qz924 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 464407 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz713 := qz924

noncomputable abbrev qz472 := qz713

noncomputable abbrev qz118 := qz472

noncomputable def Ns186p945 := @Enclosure.Real.IsNear.sqrt_image qz118 2253717 262144 7 4194304 24596289 24596294 8388608 (@Enclosure.Real.IsNear.recentre' qz118 Bool.false 144237888 16777216 28 16777216 2253717 262144 7 4194304 (Ns186p944 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns186p946 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz118) 49192583 16777216 5 16777216 2860949 2860950 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz118) Bool.false 49192583 16777216 5 16777216 49192583 16777216 5 16777216 (Ns186p945 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns186p947 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz118)) Bool.false 5721899 16777216 1 16777216 5721899 16777216 1 16777216 (Ns186p946 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz119 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz465))

noncomputable abbrev qz714 := (@HMul.hMul Real Real Real qz891 qz923 qz923)

noncomputable abbrev qz473 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz714 qz708) qz640)

noncomputable abbrev qz120 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz473))

noncomputable def Ns186p948 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz115) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz119) qz120) Bool.false 7026536988255 

noncomputable def Ns186p949 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz119) qz120 10241765 8388608 69 

noncomputable abbrev qz715 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz119))

noncomputable def Ns186p950 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz119) (@Neg.neg Real Real.instNeg qz715) Bool.true 10241765 8388608 69 4194304 (BSN.inv_eq_neg_inv_neg qz119) 

noncomputable def Ns186p951 := @Enclosure.Real.IsNear.recentre' qz715 Bool.false 20483530 16777216 276 16777216 10241765 8388608 

noncomputable def Ns186p952 := @Enclosure.Real.IsNear.recentre' qz119 Bool.true 13741527 16777216 415027216 37748736000000 13741527 16777216 25939201 2359296000000 

noncomputable abbrev qz121 := (@HMul.hMul Real Real Real qz342 qz340 qz465)

noncomputable def Ns186p953 := @Enclosure.Real.IsNear.cos_image qz121 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 31479261) qz429) Bool.false 31479261 8388608 177 16777216 Bool.true 13741527 16777216 1 

noncomputable def Ns186p954 := nat_lit 188902527884826447936526449 

noncomputable def Ns186p955 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz115 884279719003555 140737488355328 1 500000000000000 156565 262144 7 4194304 138447254205791588575 36893488147419103232 Ns186p954 

noncomputable def Ns186p956 := @Enclosure.Real.IsNear.subLit_ff_p qz118 qz1 2253717 262144 7 4194304 8 1 0 1 156565 156565 262144 7 

noncomputable def Ns186p957 := @Ns186p956 4194304 (@Enclosure.Real.IsNear.recentre' qz118 Bool.false 144237888 16777216 28 16777216 2253717 262144 7 4194304 (Ns186p944 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns186p958 := @Enclosure.Real.IsNear.recentre' qz121 Bool.false 138447254205791588575 36893488147419103232 Ns186p954 Ns186p159 31479261 8388608 177 16777216 (@Ns186p955 Ns186p159 RS187to204.d39 (Ns186p957 rfl rfl) rfl) 

noncomputable def Ns186p959 := nat_lit 454975127389221383880864781682051115762887718451914054150881191510881359057135793713121 

noncomputable def Ns186p960 := nat_lit 37747300209405564766514584909628203388786830451264672176707415786318386684394319841 

noncomputable def Ns186p961 := nat_lit 1364849887567245340513061315876334090881885581694839633108290159701071440398038592499681 

noncomputable def Ns186p962 := BSN.cos_dyadic_bound_f 20994751419 34359738368 3 2 16777216 4504395 Ns186p959 Ns186p851 Ns186p960 Ns186p961 Ns186p854 Ns186p960 13741527 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 20994751419) qz371 0 2 Ns186p959 Ns186p851 Ns186p960 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 20994751419) qz372 0 2 Ns186p961 Ns186p854 Ns186p960 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p963 := @Ns186p953 2250000 (Ns186p958 rfl) (Enclosure.sfrac_false_div 31479261 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 31479261) qz429) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 738687145867616360333312) qz430) 226375608064910080 72057594037927936 Bool.false 13741527 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 31479261 8388608 226375608064910080 72057594037927936 0 738687145867616360333312 Ns186p578 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 13741527 16777216 738687145867616360333312 Ns186p578 20994751419 34359738368 4504395 4500000 (Ns186p962 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p964 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz119) 13741527 16777216 25939201 2359296000000 10241627 10241903 8388608 (@Enclosure.Real.IsNear.neg qz119 Bool.true 13741527 16777216 25939201 2359296000000 (Ns186p952 (Ns186p963 rfl rfl) rfl)) 

noncomputable def Ns186p965 := Ns186p950 (@Enclosure.Real.IsNear.neg qz715 Bool.false 10241765 8388608 69 4194304 (@Ns186p951 69 4194304 (Ns186p964 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p966 := @Enclosure.Real.IsNear.recentre' qz120 Bool.true 2744268 8388608 

noncomputable abbrev qz122 := (@HMul.hMul Real Real Real qz342 qz340 qz473)

noncomputable def Ns186p967 := @Enclosure.Real.IsNear.cos_image qz122 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 31945063)) qz360) Bool.true 31945063 16777216 

noncomputable def Ns186p968 := nat_lit 18415075125429608562897205 

noncomputable def Ns186p969 := nat_lit 9671406556917033397649408 

noncomputable def Ns186p970 := nat_lit 1738732727388078849038360860017591 

noncomputable def Ns186p971 := @Enclosure.Real.IsNear.recentre' qz122 Bool.true Ns186p968 Ns186p969 Ns186p970 

noncomputable def Ns186p972 := nat_lit 75557863725914323419136000000000000000 

noncomputable abbrev qz123 := qz473

noncomputable def Ns186p973 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz123 884279719003555 140737488355328 1 500000000000000 20824943431 

noncomputable abbrev qz474 := (@HSub.hSub Real Real Real qz633 qz714 qz708)

noncomputable abbrev qz124 := qz474

noncomputable def Ns186p974 := @Enclosure.Real.IsNear.subLit_tf qz124 qz26 16529976135 68719476736 64430737 17592186044416 1 16 

noncomputable abbrev qz475 := qz714

noncomputable abbrev qz125 := qz475

noncomputable def Ns186p975 := @Enclosure.Real.IsNear.subLit_ff_n qz125 qz115 24512599225 68719476736 35070609 17592186044416 156565 262144 7 4194304 

noncomputable def Ns186p976 := @Enclosure.Real.IsNear.mulLit_ff qz115 qz115 156565 262144 7 4194304 156565 262144 7 4194304 24512599225 68719476736 

noncomputable def Ns186p977 := nat_lit 131488657491404472071227105240094593159674944815786362828533506377140803691956162155060647955361 

noncomputable def Ns186p978 := nat_lit 1129392729120472117529838427675928677206197862446102227694511843634863020871504657184459681 

noncomputable def Ns186p979 := nat_lit 793563703524273432334115003516267671973836923320812594095333632808612349724797546866367910906785 

noncomputable def Ns186p980 := BSN.cos_dyadic_bound_t 31945063 16777216 4 3 8388608 2250000 Ns186p977 Ns186p180 Ns186p978 Ns186p979 Ns186p183 Ns186p978 2744268 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 31945063) qz642 0 3 Ns186p977 Ns186p180 Ns186p978 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 31945063) (BSN.cosOddQ 16777216) 0 3 Ns186p979 Ns186p183 Ns186p978 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p981 := @Ns186p966 887527216 37748736000000 686067 2097152 55470451 2359296000000 (@Ns186p967 387 16777216 Bool.true 2744268 8388608 1 2250000 (@Ns186p971 Ns186p972 31945063 16777216 387 16777216 (@Ns186p973 68719476736 64430737 17592186044416 Ns186p968 Ns186p969 Ns186p970 Ns186p972 RS187to204.d39 (@Ns186p974 0 1 333199094896 20824943431 68719476736 64430737 17592186044416 (@Ns186p975 4333234063933440 16529976135 68719476736 64430737 17592186044416 (@Ns186p976 35070609 17592186044416 (Ns186p957 rfl rfl) (Ns186p957 rfl rfl) rfl) (Ns186p957 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 31945063 16777216) (BSN.cos_neg_of_bound 31945063 16777216 Bool.true 2744268 8388608 1 2250000 (Ns186p980 rfl rfl)) rfl rfl) 

noncomputable def Ns186p982 := @Ns186p942 12893660584871615719 1106804644422573096960000 (Ns186p943 qz28 (@Enclosure.Real.IsNear.of_eq qz712 (@Inv.inv Real Real.instInv (Real.sqrt qz118)) Bool.false 5721899 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz114 (BSN.t_div_two_pi_nonneg qz113 464407 1000 qz116)) Ns186p947) rfl) (@Ns186p948 17592186044416 674634880258253 19791209299968000000 (BSN.correction_mk qz115 (BSN.cos_two_pi_p_ne_zero_mk qz113 464407 1000 8 qz116 rfl rfl (@BSN.floor_sqrt_eq_dec qz113 464407 1000 8 qz116 rfl rfl rfl))) (@Ns186p949 4194304 686067 2097152 55470451 2359296000000 7026536988255 17592186044416 674634880258253 19791209299968000000 Ns186p965 (Ns186p981 rfl) rfl)) 

noncomputable def Ns186p983 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz113) (hardyZApproximantRS₀ qz113) Bool.false 481469266297250952459 295147905179352825856 1701182769918641855719 1106804644422573096960000 (@Eq.refl Real (hardyZApproximantRS₀ qz113)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz113) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz113) qz113 8) (@HMul.hMul Real Real Real qz5 qz709 (Zeta.RiemannSiegel.correction qz115))) Bool.false 481469266297250952459 295147905179352825856 1701182769918641855719 1106804644422573096960000 (BSN.hardyZApproximantRS₀_eq qz113 8 (@BSN.floor_sqrt_eq_dec qz113 464407 1000 8 qz116 rfl rfl rfl)) (@Ns186p879 481469266297250952459 295147905179352825856 1701182769918641855719 1106804644422573096960000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz113) qz113 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 8)) Bool.false 59307513 33554432 51183 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz113) qz113 8) (Ns186p941 (Ns186p940 rfl rfl rfl rfl) rfl rfl)) (Ns186p982 rfl) rfl rfl)) 

theorem RS187to204.d50 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz113) Bool.false 481469266297250952459 295147905179352825856 1701182769918641855719 1106804644422573096960000 := Ns186p983 

noncomputable def Ns186p984 := nat_lit 431043632067468858331496448 

noncomputable abbrev qz925 := (Enclosure.sfrac Bool.false 465867 1000)

noncomputable abbrev qz716 := qz925

noncomputable abbrev qz476 := qz716

noncomputable abbrev qz126 := qz476

noncomputable abbrev qz926 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 465867 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz717 := qz926

noncomputable abbrev qz477 := qz717

noncomputable abbrev qz127 := qz477

noncomputable abbrev qz927 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 465867 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz718 := qz927

noncomputable abbrev qz478 := qz718

noncomputable abbrev qz128 := qz478

noncomputable abbrev qz719 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz127 qz9))

noncomputable def Ns186p985 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz126) qz126 8) (@HMul.hMul Real Real Real qz5 qz719 (Zeta.RiemannSiegel.correction qz128)) 3529307 16777216 102691 67108864 10170146234110731625 73786976294838206464 14526963075283943393 1152921504606846976000000 Ns186p984 

noncomputable def Ns186p986 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz126) qz126 Real.cos BSN.quadSignNeg 7 8 465867 1000 126 134217728 67108864 2251799813685248 Bool.false 103306161427 1816 279097919 60 47453128 8 

noncomputable def Ns186p987 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz126) qz126 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 465867 1000 41 87 134217728 67108864 2251799813685248 Bool.false 103306161427 1816 

noncomputable def Ns186p988 := Ns186p987 240485871 61 54794152 8 261175631 61 50729528 8 Bool.false 28900591 68366 Bool.true 84292558 Bool.true 24848130 7074237752028440 1 Bool.false 78859704 Bool.true Bool.false 24706431 Bool.false Bool.false 6044407 

noncomputable def Ns186p989 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz126) qz126 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 465867 1000 78 12 134217728 67108864 2251799813685248 Bool.false 103306161427 1816 

noncomputable def Ns186p990 := Ns186p989 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 14767744 40149 Bool.false 179855380 Bool.false 141915856 7074237752028440 1 Bool.false 30699153 Bool.true Bool.false 65924700 Bool.false Bool.false 28900591 

noncomputable def Ns186p991 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz126) qz126 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 465867 1000 284 164 134217728 67108864 2251799813685248 Bool.false 103306161427 1816 

noncomputable def Ns186p992 := Ns186p991 93032624 60 94906264 8 147453232 60 77490640 16 Bool.true 134217696 1884 Bool.false 89977168 Bool.false 36657477 7074237752028440 1 Bool.false 105170904 Bool.false Bool.false 129242832 Bool.false Bool.false 14767744 

noncomputable def Ns186p993 := nat_lit 141745505271340708757743534669768596625274369351254322107 

noncomputable def Ns186p994 := nat_lit 184159002800877651023205233463112801727810105245696000 

noncomputable def Ns186p995 := nat_lit 10533003893064563771891536371360000 

noncomputable def Ns186p996 := nat_lit 29441889374622200733868153242554214720 

noncomputable abbrev qz720 := (@Eq.refl Real qz925)

noncomputable abbrev qz479 := qz720

noncomputable abbrev qz129 := qz479

noncomputable def Ns186p997 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz126 465867 1000 868129246756 16000000 931734 4000 2000 Ns186p995 Ns186p996 qz129 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns186p998 := nat_lit 408227055181461241222301379848933558280790183731612447668160 

noncomputable abbrev qz721 := (Real.log (Enclosure.sfrac Bool.false 868129246756 16000000))

noncomputable abbrev qz130 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 465867 4000) qz721) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 931734))))))

noncomputable abbrev qz722 := (Enclosure.sfrac Bool.false 465867 2000)

noncomputable abbrev qz480 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz130 qz722) (@HMul.hMul Real Real Real qz5 qz722 (Real.log Real.pi)))

noncomputable def Ns186p999 := @Enclosure.Real.IsNear.addLit_ft_p qz480 (Enclosure.sfrac Bool.true Ns186p995 Ns186p996) 13865524719995292689203 18014398509481984000 49852835463653083 3686400000000000000000 Ns186p995 Ns186p996 0 1 Ns186p998 

noncomputable def Ns186p1000 := nat_lit 37219984508912087108796735815680 

noncomputable abbrev qz481 := (@HSub.hSub Real Real Real qz12 qz130 qz722)

noncomputable abbrev qz482 := (@HMul.hMul Real Real Real qz5 qz722 (Real.log Real.pi))

noncomputable def Ns186p1001 := @Enclosure.Real.IsNear.subLit_ff_p qz481 qz482 746759636380378986283 720575940379279360 47386712579309 7200000000000000000 17894305994787 67108864000 465867 67108864000 Ns186p1000 13865524719995292689203 18014398509481984000 

noncomputable def Ns186p1002 := nat_lit 37337981819018949314150000 

noncomputable abbrev qz483 := qz722

noncomputable def Ns186p1003 := @Enclosure.Real.IsNear.subLit_ff_p qz130 qz483 22865147804717896377139 18014398509481984000 47386712579309 7200000000000000000 465867 2000 0 1 Ns186p1002 746759636380378986283 720575940379279360 47386712579309 7200000000000000000 

noncomputable def Ns186p1004 := nat_lit 51487735566549416382682306731648745472 

noncomputable def Ns186p1005 := nat_lit 26358226945607340239355904 

noncomputable def Ns186p1006 := nat_lit 7177952380047486484364984494450808154249197643544580691639640304988450480087989357318344556887960810236422213899272331939271102030120667940308501135360 

noncomputable def Ns186p1007 := nat_lit 151482587141408307714371085993979417794307141449352712239012390568341062697050662751298321491461836294955301162654592712680713595245857253546044424192 

noncomputable def Ns186p1008 := nat_lit 28387043828884013452350600485605776228928864767081204248773875888013200453685664317126072536542649420767635956623305637328896979117936444702720 

noncomputable def Ns186p1009 := BSN.log_dyadic_bound 343841246756 1392417246756 7 6 Ns186p1006 67108864 18000000 Ns186p1007 Ns186p1008 33842963 1736258493512 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 343841246756) (BSN.artanhQ 1392417246756) 0 6 Ns186p1007 Ns186p1006 Ns186p1008 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns186p1010 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 465867 4000) qz721 465867 4000 0 1 49096023562564217 4503599627370496 100000027 1800000000000000 22872217209021104081139 18014398509481984000 5176301397601 800000000000000000 (Enclosure.Real.IsNear.const Bool.false 465867 4000) (BSN.isNear_log_sfrac 868129246756 16000000 49096023562564217 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 868129246756) qz353)) Bool.false Ns186p1005 Ns186p89 1000000270000000 18000000000000000000000 49096023562564217 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 868129246756 16000000 15 1736258493512 1048576000000 33842963 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns186p1009 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p1011 := BSN.arctan_dyadic_bound_f 1000 931734 1 0 8388608 2250000 0 1 1 0 1 1 9003 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 931734) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 931734) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz723 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 931734)))

noncomputable def Ns186p1012 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz723 884279719003555 562949953421312 1 2000000000000000 9003 8388608 1 2250000 7412807686640321429504 883675537900963 562949953421312 8000000009 18000000000000000 qz16 (Ns186p1011 rfl) rfl rfl 

noncomputable def Ns186p1013 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 465867 4000) qz721) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz723)) 22872217209021104081139 18014398509481984000 5176301397601 800000000000000000 883675537900963 2251799813685248 8000000009 72000000000000000 Ns186p1004 22865147804717896377139 18014398509481984000 47386712579309 7200000000000000000 (Ns186p1010 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz723) 1 4 0 1 883675537900963 562949953421312 8000000009 18000000000000000 883675537900963 2251799813685248 8000000009 72000000000000000 qz356 Ns186p1012 rfl) 

noncomputable def Ns186p1014 := @Ns186p999 Ns186p993 Ns186p994 49852835463653083 3686400000000000000000 (@Ns186p1001 49852835463653083 3686400000000000000000 (Ns186p1003 (Ns186p1013 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 465867 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz483 (Real.log Real.pi) 465867 2000 0 1 38410761 33554432 1 33554432 17894305994787 67108864000 465867 67108864000 (Enclosure.Real.IsNear.const Bool.false 465867 2000) RS187to204.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns186p995 Ns186p996) 

noncomputable def Ns186p1015 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz126) Bool.false Ns186p993 Ns186p994 49852835463653083 3686400000000000000000 6456635089 8388608 57 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz126) (@HAdd.hAdd Real Real Real qz357 qz480 (Enclosure.sfrac Bool.true Ns186p995 Ns186p996)) Bool.false Ns186p993 Ns186p994 49852835463653083 3686400000000000000000 Ns186p997 (Ns186p1014 rfl rfl)) 

noncomputable def Ns186p1016 := BSN.cos_dyadic_bound_f 23423680 34359738368 1 0 16777216 4504395 0 1 1 0 1 1 16777212 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 23423680) qz371 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 23423680) qz372 0 0 rfl) rfl rfl 

noncomputable def Ns186p1017 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz126) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6456635089) qz429) Bool.false 6456635089 8388608 57 4194304 Bool.true 16777212 16777216 1 2250000 (Ns186p1015 rfl) (Enclosure.sfrac_false_div 6456635089 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6456635089) qz429) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 824147502500841259008) qz430) 226375608064910080 72057594037927936 Bool.false 16777212 16777216 122 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 6456635089 8388608 226375608064910080 72057594037927936 122 824147502500841259008 Ns186p578 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777212 16777216 824147502500841259008 Ns186p578 23423680 34359738368 4504395 4500000 (Ns186p1016 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p1018 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz126) Bool.false Ns186p993 Ns186p994 49852835463653083 3686400000000000000000 103306161427 134217728 1816 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz126) (@HAdd.hAdd Real Real Real qz357 qz480 (Enclosure.sfrac Bool.true Ns186p995 Ns186p996)) Bool.false Ns186p993 Ns186p994 49852835463653083 3686400000000000000000 Ns186p997 (Ns186p1014 rfl rfl)) 

noncomputable def Ns186p1019 := Ns186p992 40149 BSN.abs_quadSignPos (BSN.cos_quad_nat0 284 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 105170904 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 164 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 129242832 134217728) qz129 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz126) qz126 1) Bool.true 4194303 4194304 8277769 589824000000 134217696 134217728 1884 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz126) qz126 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz126)) Bool.true 4194303 4194304 8277769 589824000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz126) qz126) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz126)) Bool.true 16777212 16777216 132444304 9437184000000 4194303 4194304 8277769 589824000000 (Ns186p1017 rfl rfl) rfl)) rfl) (Ns186p1018 rfl) RS187to204.d7 

noncomputable def Ns186p1020 := nat_lit 35738004628161747698601109014759461076312985586491584637094965805056 

noncomputable def Ns186p1021 := nat_lit 4295943473337558684051086798732401555562126066032736376482430976 

noncomputable def Ns186p1022 := nat_lit 107205421997538567978435224870680918425827832507342688438531932553216 

noncomputable def Ns186p1023 := BSN.cos_dyadic_bound_f 89977168 134217728 3 2 134217728 67108864 Ns186p1020 Ns186p117 Ns186p1021 Ns186p1022 Ns186p120 Ns186p1021 105170904 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 89977168) qz364 0 2 Ns186p1020 Ns186p117 Ns186p1021 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 89977168) qz365 0 2 Ns186p1022 Ns186p120 Ns186p1021 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1024 := nat_lit 1805719479190043815515990569841 

noncomputable def Ns186p1025 := BSN.cos_dyadic_bound_f 36657477 134217728 2 1 134217728 67108864 Ns186p1024 Ns186p134 Ns186p1024 Ns186p1024 Ns186p135 Ns186p1024 129242832 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 36657477) qz364 0 1 Ns186p1024 Ns186p134 Ns186p1024 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 36657477) qz365 0 1 Ns186p1024 Ns186p135 Ns186p1024 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1026 := nat_lit 2203593544955889305537957512094537711145094097897782480011399579737638233689119218604193551346827264000000 

noncomputable def Ns186p1027 := nat_lit 1145727138951366068790796014859398350013950152744805115618112593474319725901215285907456000000000000 

noncomputable def Ns186p1028 := nat_lit 13351388996940896672338984368604609694061626891218753985473670124039816863783695158326784222337800601600000 

noncomputable def Ns186p1029 := BSN.cos_dyadic_bound_f 179855380 134217728 4 3 134217728 67108864 Ns186p1026 Ns186p127 Ns186p1027 Ns186p1028 Ns186p130 Ns186p1027 30699153 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 179855380) qz364 0 3 Ns186p1026 Ns186p127 Ns186p1027 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 179855380) qz365 0 3 Ns186p1028 Ns186p130 Ns186p1027 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1030 := nat_lit 853201284387500851170787354455303736525576702604175829702962620132371594827697569442939295216979637436416 

noncomputable def Ns186p1031 := nat_lit 66737672005953721271689951272117212748262561351309887083319689047651715932528888754269818544193536 

noncomputable def Ns186p1032 := nat_lit 5173522011725458243081149590049843244122334973897047598672132525687857927393051578973482527963655385907200 

noncomputable def Ns186p1033 := BSN.cos_dyadic_bound_f 141915856 134217728 4 3 134217728 67108864 Ns186p1030 Ns186p127 Ns186p1031 Ns186p1032 Ns186p130 Ns186p1031 65924700 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 141915856) qz364 0 3 Ns186p1030 Ns186p127 Ns186p1031 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 141915856) qz365 0 3 Ns186p1032 Ns186p130 Ns186p1031 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1034 := Ns186p990 68366 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 78 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 30699153 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 12 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 65924700 134217728) qz129 rfl rfl (Ns186p1019 RS187to204.d9 RS187to204.d11 RS187to204.d13 RS187to204.d17 (Ns186p1023 rfl rfl) (Ns186p1025 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns186p1018 rfl) RS187to204.d19 RS187to204.d21 RS187to204.d23 RS187to204.d25 RS187to204.d17 (Ns186p1029 rfl rfl) (Ns186p1033 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns186p1035 := nat_lit 49545086799341943116090078437905052336758412300684390127677701341440 

noncomputable def Ns186p1036 := nat_lit 2548671528890248491347324750680167787503938112772031182897398016 

noncomputable def Ns186p1037 := nat_lit 129756815196753552520773738335393083467473216316276533712478812487936 

noncomputable def Ns186p1038 := BSN.sin_dyadic_bound_f 84292558 134217728 3 2 134217728 67108864 Ns186p1035 Ns186p111 Ns186p1036 Ns186p1037 Ns186p114 Ns186p1036 78859704 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 84292558) qz362 0 2 Ns186p1035 Ns186p111 Ns186p1036 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 84292558) qz363 0 2 Ns186p1037 Ns186p114 Ns186p1036 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1039 := nat_lit 381219267114831596950109610000 

noncomputable def Ns186p1040 := BSN.sin_dyadic_bound_f 24848130 134217728 2 1 134217728 67108864 Ns186p1039 Ns186p123 Ns186p1039 Ns186p1039 Ns186p124 Ns186p1039 24706431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 24848130) qz362 0 1 Ns186p1039 Ns186p123 Ns186p1039 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 24848130) qz363 0 1 Ns186p1039 Ns186p124 Ns186p1039 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1041 := Ns186p988 92156 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 78859704 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 87 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 24706431 134217728) qz129 rfl rfl (Ns186p1034 rfl rfl) (Ns186p1018 rfl) RS187to204.d27 RS187to204.d29 RS187to204.d31 RS187to204.d33 RS187to204.d17 (Ns186p1038 rfl rfl) (Ns186p1040 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns186p1042 := nat_lit 1121018113296910949203873655613139914245054813372517960216295863796521074540111710638551773049663702634496 

noncomputable def Ns186p1043 := nat_lit 151269248870318203467242353102940238233165012615413944527118035910656777671869859943219573758038016 

noncomputable def Ns186p1044 := nat_lit 6796415735316576017179729969024152326316422295012977174210466373005695782846549091021869500159753178255360 

noncomputable def Ns186p1045 := BSN.cos_dyadic_bound_f 151930822 134217728 4 3 134217728 67108864 Ns186p1042 Ns186p127 Ns186p1043 Ns186p1044 Ns186p130 Ns186p1043 57025720 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 151930822) qz364 0 3 Ns186p1042 Ns186p127 Ns186p1043 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 151930822) qz365 0 3 Ns186p1044 Ns186p130 Ns186p1043 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1046 := Ns186p986 Bool.false 6044407 92156 Bool.true 151930822 7074237752028440 1 Bool.false 57025720 Bool.true Bool.true 14117228 102691 BSN.abs_quadSignNeg qz431 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 57025720 134217728) qz129 rfl (Ns186p1041 rfl) (Ns186p1018 rfl) RS187to204.d35 RS187to204.d37 RS187to204.d17 (Ns186p1045 rfl rfl) rfl 

noncomputable def Ns186p1047 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz126) qz126 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz126) qz126 8) 14117228 134217728 102691 134217728 14117228 134217728 102691 134217728 3789564535635968 3529307 16777216 102691 67108864 (Ns186p1046 rfl rfl rfl rfl) 

noncomputable def Ns186p1048 := @Enclosure.Real.IsNear.mulLit_ff qz719 (Zeta.RiemannSiegel.correction qz128) 2858705 8388608 1 8388608 3557606060825 8796093022208 355936772959 9663676416000000 10170146234110731625 73786976294838206464 

noncomputable abbrev qz724 := (@HPow.hPow Real Real Real qz7 qz127 qz9)

noncomputable def Ns186p1049 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz724 1 1 0 1 2858705 8388608 1 8388608 2858705 8388608 1 8388608 

noncomputable def Ns186p1050 := @Enclosure.Real.IsNear.sqrt_image qz127 1243947348459 16777216000 465867 16777216000 72232204 72232232 8388608 (@Enclosure.Real.IsNear.of_eq qz127 (@HMul.hMul Real Real Real qz5 qz126 qz3) Bool.false 1243947348459 16777216000 465867 16777216000 (BSN.t_div_two_pi_mk qz126 465867 1000 qz129) (@Enclosure.Real.IsNear.mulLit_ff qz126 qz3 465867 1000 0 1 2670177 16777216 1 16777216 1243947348459 16777216000 465867 16777216000 (Enclosure.Real.IsNear.const Bool.false 465867 1000) RS187to204.d40 rfl)) 

noncomputable abbrev qz928 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 465867 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz725 := qz928

noncomputable abbrev qz484 := qz725

noncomputable abbrev qz131 := qz484

noncomputable def Ns186p1051 := @Enclosure.Real.IsNear.sqrt_image qz131 36116109 4194304 7 4194304 24615597 24615603 8388608 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 144464436 16777216 28 16777216 36116109 4194304 7 4194304 (Ns186p1050 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns186p1052 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz131) 1538475 524288 3 8388608 2858704 2858706 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz131) Bool.false 49231200 16777216 6 16777216 1538475 524288 3 8388608 (Ns186p1051 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns186p1053 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz131)) Bool.false 5717410 16777216 2 16777216 2858705 8388608 1 8388608 (Ns186p1052 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz132 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz478))

noncomputable abbrev qz726 := (@HMul.hMul Real Real Real qz891 qz927 qz927)

noncomputable abbrev qz485 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz726 qz718) qz640)

noncomputable abbrev qz133 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz485))

noncomputable def Ns186p1054 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz128) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz132) qz133) Bool.false 3557606060825 

noncomputable def Ns186p1055 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz132) qz133 5464925 4194304 157 

noncomputable abbrev qz727 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz132))

noncomputable def Ns186p1056 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz132) (@Neg.neg Real Real.instNeg qz727) Bool.true 5464925 4194304 157 8388608 (BSN.inv_eq_neg_inv_neg qz132) 

noncomputable def Ns186p1057 := @Enclosure.Real.IsNear.recentre' qz727 Bool.false 21859700 16777216 314 16777216 5464925 4194304 

noncomputable def Ns186p1058 := @Enclosure.Real.IsNear.recentre' qz132 Bool.true 12876434 16777216 415027216 37748736000000 6438217 8388608 25939201 2359296000000 

noncomputable abbrev qz134 := (@HMul.hMul Real Real Real qz342 qz340 qz478)

noncomputable def Ns186p1059 := @Enclosure.Real.IsNear.cos_image qz134 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 64381965) qz360) Bool.false 64381965 16777216 177 16777216 Bool.true 12876434 16777216 1 

noncomputable def Ns186p1060 := nat_lit 188902527885312956062013553 

noncomputable def Ns186p1061 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz128 884279719003555 140737488355328 1 500000000000000 2561677 4194304 7 4194304 2265239017737869761735 590295810358705651712 Ns186p1060 

noncomputable def Ns186p1062 := @Enclosure.Real.IsNear.subLit_ff_p qz131 qz1 36116109 4194304 7 4194304 8 1 0 1 2561677 2561677 4194304 7 

noncomputable def Ns186p1063 := @Ns186p1062 4194304 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 144464436 16777216 28 16777216 36116109 4194304 7 4194304 (Ns186p1050 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns186p1064 := @Enclosure.Real.IsNear.recentre' qz134 Bool.false 2265239017737869761735 590295810358705651712 Ns186p1060 Ns186p159 64381965 16777216 177 16777216 (@Ns186p1061 Ns186p159 RS187to204.d39 (Ns186p1063 rfl rfl) rfl) 

noncomputable def Ns186p1065 := nat_lit 1682514047395493230673920 

noncomputable def Ns186p1066 := nat_lit 765393694720925567153990954509247894715996324615725194373502226638329070363547577085921 

noncomputable def Ns186p1067 := nat_lit 106814739679524143872322940497995005781560176302428330203779226617550368873132060641 

noncomputable def Ns186p1068 := nat_lit 2295967454683417653174228217646747694136425853494570726460099121461752110352896467136481 

noncomputable def Ns186p1069 := BSN.cos_dyadic_bound_f 23909962683 34359738368 3 2 16777216 4504395 Ns186p1066 Ns186p851 Ns186p1067 Ns186p1068 Ns186p854 Ns186p1067 12876434 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 23909962683) qz371 0 2 Ns186p1066 Ns186p851 Ns186p1067 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 23909962683) qz372 0 2 Ns186p1068 Ns186p854 Ns186p1067 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1070 := @Ns186p1059 2250000 (Ns186p1064 rfl) (Enclosure.sfrac_false_div 64381965 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 64381965) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p1065) qz361) 226375608064910080 72057594037927936 Bool.false 12876434 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 64381965 16777216 226375608064910080 72057594037927936 0 Ns186p1065 Ns186p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 12876434 16777216 Ns186p1065 Ns186p89 23909962683 34359738368 4504395 4500000 (Ns186p1069 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p1071 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz132) 6438217 8388608 25939201 2359296000000 10929693 10930007 8388608 (@Enclosure.Real.IsNear.neg qz132 Bool.true 6438217 8388608 25939201 2359296000000 (Ns186p1058 (Ns186p1070 rfl rfl) rfl)) 

noncomputable def Ns186p1072 := Ns186p1056 (@Enclosure.Real.IsNear.neg qz727 Bool.false 5464925 4194304 157 8388608 (@Ns186p1057 157 8388608 (Ns186p1071 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p1073 := @Enclosure.Real.IsNear.recentre' qz133 Bool.true 2603956 8388608 

noncomputable abbrev qz135 := (@HMul.hMul Real Real Real qz342 qz340 qz485)

noncomputable def Ns186p1074 := @Enclosure.Real.IsNear.cos_image qz135 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 31648987)) qz360) Bool.true 31648987 16777216 

noncomputable def Ns186p1075 := nat_lit 4670566215063227734272871525 

noncomputable def Ns186p1076 := nat_lit 352026094465768559891860389226269 

noncomputable def Ns186p1077 := @Enclosure.Real.IsNear.recentre' qz135 Bool.true Ns186p1075 Ns186p171 Ns186p1076 

noncomputable abbrev qz136 := qz485

noncomputable def Ns186p1078 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz136 884279719003555 140737488355328 1 500000000000000 5281774663255 

noncomputable abbrev qz486 := (@HSub.hSub Real Real Real qz633 qz726 qz718)

noncomputable abbrev qz137 := qz486

noncomputable def Ns186p1079 := @Enclosure.Real.IsNear.subLit_tf qz137 qz26 4182263035479 17592186044416 65223655 17592186044416 1 16 

noncomputable abbrev qz487 := qz726

noncomputable abbrev qz138 := qz487

noncomputable def Ns186p1080 := @Enclosure.Real.IsNear.subLit_ff_n qz138 qz128 6562189052329 17592186044416 35863527 17592186044416 2561677 4194304 7 4194304 

noncomputable def Ns186p1081 := @Enclosure.Real.IsNear.mulLit_ff qz128 qz128 2561677 4194304 7 4194304 2561677 4194304 7 4194304 6562189052329 17592186044416 

noncomputable def Ns186p1082 := nat_lit 126645277833610971744112677957672755201736780553847232586153001358302773070441731642295942558161 

noncomputable def Ns186p1083 := nat_lit 1009991613358712883414968244912816848709940448027782974370339528845476771273988902394966481 

noncomputable def Ns186p1084 := nat_lit 764477498439416734815283147904770120772533136093355606474961973178109386348301357705821963858385 

noncomputable def Ns186p1085 := BSN.cos_dyadic_bound_t 31648987 16777216 4 3 8388608 2250000 Ns186p1082 Ns186p180 Ns186p1083 Ns186p1084 Ns186p183 Ns186p1083 2603956 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 31648987) qz642 0 3 Ns186p1082 Ns186p180 Ns186p1083 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 31648987) (BSN.cosOddQ 16777216) 0 3 Ns186p1084 Ns186p183 Ns186p1083 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1086 := @Ns186p1073 112347152 4718592000000 650989 2097152 7021697 294912000000 (@Ns186p1074 49 2097152 Bool.true 2603956 8388608 1 2250000 (@Ns186p1077 Ns186p174 31648987 16777216 49 2097152 (@Ns186p1078 17592186044416 65223655 17592186044416 Ns186p1075 Ns186p171 Ns186p1076 Ns186p174 RS187to204.d39 (@Ns186p1079 0 1 84508394612080 5281774663255 17592186044416 65223655 17592186044416 (@Ns186p1080 17541682578761711616 4182263035479 17592186044416 65223655 17592186044416 (@Ns186p1081 35863527 17592186044416 (Ns186p1063 rfl rfl) (Ns186p1063 rfl rfl) rfl) (Ns186p1063 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 31648987 16777216) (BSN.cos_neg_of_bound 31648987 16777216 Bool.true 2603956 8388608 1 2250000 (Ns186p1085 rfl rfl)) rfl rfl) 

noncomputable def Ns186p1087 := @Ns186p1048 14526963075283943393 1152921504606846976000000 (Ns186p1049 qz28 (@Enclosure.Real.IsNear.of_eq qz724 (@Inv.inv Real Real.instInv (Real.sqrt qz131)) Bool.false 2858705 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz127 (BSN.t_div_two_pi_nonneg qz126 465867 1000 qz129)) Ns186p1053) rfl) (@Ns186p1054 8796093022208 355936772959 9663676416000000 (BSN.correction_mk qz128 (BSN.cos_two_pi_p_ne_zero_mk qz126 465867 1000 8 qz129 rfl rfl (@BSN.floor_sqrt_eq_dec qz126 465867 1000 8 qz129 rfl rfl rfl))) (@Ns186p1055 8388608 650989 2097152 7021697 294912000000 3557606060825 8796093022208 355936772959 9663676416000000 Ns186p1072 (Ns186p1086 rfl) rfl)) 

noncomputable def Ns186p1088 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz126) (hardyZApproximantRS₀ qz126) Bool.true 25692202572075656553 73786976294838206464 1778744909449427943393 1152921504606846976000000 (@Eq.refl Real (hardyZApproximantRS₀ qz126)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz126) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz126) qz126 8) (@HMul.hMul Real Real Real qz5 qz719 (Zeta.RiemannSiegel.correction qz128))) Bool.true 25692202572075656553 73786976294838206464 1778744909449427943393 1152921504606846976000000 (BSN.hardyZApproximantRS₀_eq qz126 8 (@BSN.floor_sqrt_eq_dec qz126 465867 1000 8 qz129 rfl rfl rfl)) (@Ns186p985 25692202572075656553 73786976294838206464 1778744909449427943393 1152921504606846976000000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz126) qz126 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz126) qz126 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz126) qz126 8)) Bool.true 3529307 16777216 102691 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz126) qz126 8) (Ns186p1047 (Ns186p1046 rfl rfl rfl rfl) rfl rfl)) (Ns186p1087 rfl) rfl rfl)) 

theorem RS187to204.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz126) Bool.true 25692202572075656553 73786976294838206464 1778744909449427943393 1152921504606846976000000 := Ns186p1088 

noncomputable def Ns186p1089 := nat_lit 9223372036854775808000000 

noncomputable def Ns186p1090 := nat_lit 150110239512440780892405760 

noncomputable abbrev qz929 := (Enclosure.sfrac Bool.false 467325 1000)

noncomputable abbrev qz728 := qz929

noncomputable abbrev qz488 := qz728

noncomputable abbrev qz139 := qz488

noncomputable abbrev qz930 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 467325 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz729 := qz930

noncomputable abbrev qz489 := qz729

noncomputable abbrev qz140 := qz489

noncomputable abbrev qz931 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 467325 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz730 := qz931

noncomputable abbrev qz490 := qz730

noncomputable abbrev qz141 := qz490

noncomputable abbrev qz731 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz140 qz9))

noncomputable def Ns186p1091 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz139) qz139 8) (@HMul.hMul Real Real Real qz5 qz731 (Zeta.RiemannSiegel.correction qz141)) 801503 2097152 3219 2097152 41223379102957747979 295147905179352825856 126975428193846018993 Ns186p1089 Ns186p1090 

noncomputable def Ns186p1092 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz139) qz139 Real.cos BSN.quadSignNeg 7 8 467325 1000 126 134217728 67108864 2251799813685248 Bool.false 103727636025 1822 279097919 60 47453128 8 

noncomputable def Ns186p1093 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz139) qz139 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 467325 1000 41 86 134217728 67108864 2251799813685248 Bool.false 103727636025 1822 

noncomputable def Ns186p1094 := Ns186p1093 240485871 61 54794152 8 261175631 61 50729528 8 Bool.false 61789502 68575 Bool.true 13446360 Bool.true 194996316 7074237752028440 1 Bool.false 13423878 Bool.true Bool.false 15795706 Bool.true Bool.false 50339012 

noncomputable def Ns186p1095 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz139) qz139 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 467325 1000 79 13 134217728 67108864 2251799813685248 Bool.false 103727636025 1822 

noncomputable def Ns186p1096 := Ns186p1095 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 26316550 40269 Bool.false 119218109 Bool.false 37611741 7074237752028440 1 Bool.false 104148310 Bool.false Bool.false 37121404 Bool.true Bool.false 61789502 

noncomputable def Ns186p1097 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz139) qz139 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 467325 1000 285 165 134217728 67108864 2251799813685248 Bool.false 103727636025 1822 

noncomputable def Ns186p1098 := Ns186p1097 93032624 60 94906264 8 147453232 60 77490640 16 Bool.false 134217696 1884 Bool.false 164981486 Bool.false 32316548 7074237752028440 1 Bool.false 126463129 Bool.true Bool.false 32005200 Bool.true Bool.false 26316550 

noncomputable def Ns186p1099 := nat_lit 23759641414492424269522526908700436683884832117 

noncomputable def Ns186p1100 := nat_lit 30743639891241191443635977235245065452912640 

noncomputable def Ns186p1101 := nat_lit 10698861612509618373998437500000000 

noncomputable def Ns186p1102 := nat_lit 29999089044176145321405550078125000000 

noncomputable abbrev qz732 := (@Eq.refl Real qz929)

noncomputable abbrev qz491 := qz732

noncomputable abbrev qz142 := qz491

noncomputable def Ns186p1103 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz139 467325 1000 873571622500 16000000 934650 4000 2000 Ns186p1101 Ns186p1102 qz142 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns186p1104 := nat_lit 16705997869564985814508026732679994543356522582265625000000 

noncomputable abbrev qz733 := (Real.log (Enclosure.sfrac Bool.false 873571622500 16000000))

noncomputable abbrev qz143 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 467325 4000) qz733) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 934650))))))

noncomputable abbrev qz734 := (Enclosure.sfrac Bool.false 467325 2000)

noncomputable abbrev qz492 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz143 qz734) (@HMul.hMul Real Real Real qz5 qz734 (Real.log Real.pi)))

noncomputable def Ns186p1105 := @Enclosure.Real.IsNear.addLit_ft_p qz492 (Enclosure.sfrac Bool.true Ns186p1101 Ns186p1102) 556883762513797509533 720575940379279360 2000303016633589 147456000000000000000 Ns186p1101 Ns186p1102 0 1 Ns186p1104 

noncomputable def Ns186p1106 := nat_lit 1494873467293869407631552020480 

noncomputable abbrev qz493 := (@HSub.hSub Real Real Real qz12 qz143 qz734)

noncomputable abbrev qz494 := (@HMul.hMul Real Real Real qz5 qz734 (Real.log Real.pi))

noncomputable def Ns186p1107 := @Enclosure.Real.IsNear.subLit_ff_p qz493 qz494 749623736541982814621 720575940379279360 1901300504747 288000000000000000 718012355373 2684354560 18693 2684354560 Ns186p1106 556883762513797509533 720575940379279360 

noncomputable def Ns186p1108 := nat_lit 1499247473083965629242000 

noncomputable abbrev qz495 := qz734

noncomputable def Ns186p1109 := @Enclosure.Real.IsNear.subLit_ff_p qz143 qz495 917995312210856178077 720575940379279360 1901300504747 288000000000000000 467325 2000 0 1 Ns186p1108 749623736541982814621 720575940379279360 1901300504747 288000000000000000 

noncomputable def Ns186p1110 := nat_lit 2067141673000337010065548073915908096 

noncomputable def Ns186p1111 := nat_lit 26373337351019499689607168 

noncomputable def Ns186p1112 := nat_lit 7521952219642963355299204263911482194279952288289009754622590624874162731380393914603766905339140996832688041627407073974609375000000000000000000000000 

noncomputable def Ns186p1113 := nat_lit 162684051286581108595115816920358034104394882140954034687984258083962492647623063586420402898129157300972811698913574218750000000000000000000000000000 

noncomputable def Ns186p1114 := nat_lit 34273871515514464839420980264927685940990648327519109825480083434175551232548854584114069170179437541663646697998046875000000000000000000000000 

noncomputable def Ns186p1115 := BSN.log_dyadic_bound 349283622500 1397859622500 7 6 Ns186p1112 67108864 18000000 Ns186p1113 Ns186p1114 34262361 1747143245000 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 349283622500) (BSN.artanhQ 1397859622500) 0 6 Ns186p1113 Ns186p1112 Ns186p1114 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns186p1116 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 467325 4000) qz733 467325 4000 0 1 49124168885908089 4503599627370496 100000027 1800000000000000 918278088984279907677 720575940379279360 207700056079 32000000000000000 (Enclosure.Real.IsNear.const Bool.false 467325 4000) (BSN.isNear_log_sfrac 873571622500 16000000 49124168885908089 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 873571622500) qz353)) Bool.false Ns186p1111 Ns186p89 1000000270000000 18000000000000000000000 49124168885908089 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 873571622500 16000000 15 1747143245000 1048576000000 34262361 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns186p1115 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p1117 := BSN.arctan_dyadic_bound_f 1000 934650 1 0 8388608 2250000 0 1 1 0 1 1 8975 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 934650) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 934650) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz735 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 934650)))

noncomputable def Ns186p1118 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz735 884279719003555 562949953421312 1 2000000000000000 8975 8388608 1 2250000 7412823449239017226240 883677416949155 562949953421312 8000000009 18000000000000000 qz16 (Ns186p1117 rfl) rfl rfl 

noncomputable def Ns186p1119 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 467325 4000) qz733) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz735)) 918278088984279907677 720575940379279360 207700056079 32000000000000000 883677416949155 2251799813685248 8000000009 72000000000000000 Ns186p1110 917995312210856178077 720575940379279360 1901300504747 288000000000000000 (Ns186p1116 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz735) 1 4 0 1 883677416949155 562949953421312 8000000009 18000000000000000 883677416949155 2251799813685248 8000000009 72000000000000000 qz356 Ns186p1118 rfl) 

noncomputable def Ns186p1120 := @Ns186p1105 Ns186p1099 Ns186p1100 2000303016633589 147456000000000000000 (@Ns186p1107 2000303016633589 147456000000000000000 (Ns186p1109 (Ns186p1119 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 467325 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz495 (Real.log Real.pi) 467325 2000 0 1 38410761 33554432 1 33554432 718012355373 2684354560 18693 2684354560 (Enclosure.Real.IsNear.const Bool.false 467325 2000) RS187to204.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns186p1101 Ns186p1102) 

noncomputable def Ns186p1121 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz139) Bool.false Ns186p1099 Ns186p1100 2000303016633589 147456000000000000000 12965954503 16777216 57 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz139) (@HAdd.hAdd Real Real Real qz357 qz492 (Enclosure.sfrac Bool.true Ns186p1101 Ns186p1102)) Bool.false Ns186p1099 Ns186p1100 2000303016633589 147456000000000000000 Ns186p1103 (Ns186p1120 rfl rfl)) 

noncomputable def Ns186p1122 := nat_lit 3796307227393178663387136 

noncomputable def Ns186p1123 := nat_lit 855650331541543257910598977487407847553106161497923085824251517925656525076009251039185955328607640970827954946833669552333427956781056 

noncomputable def Ns186p1124 := nat_lit 607825077777213577506590119895147315029281672436873960117890529900949008126250122584682678484576916293088807566708843708433043456 

noncomputable def Ns186p1125 := nat_lit 4272944593710215771552487590677969222876030721157592983173131433074515187084404944810358186378820712742698759087042326125164134060527616 

noncomputable def Ns186p1126 := BSN.sin_dyadic_bound_f 53948770462 34359738368 4 3 16777216 4504395 Ns186p1123 Ns186p102 Ns186p1124 Ns186p1125 Ns186p105 Ns186p1124 16777212 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53948770462) qz358 0 3 Ns186p1123 Ns186p102 Ns186p1124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53948770462) qz359 0 3 Ns186p1125 Ns186p105 Ns186p1124 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1127 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz139) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12965954503) qz360) Bool.false 12965954503 16777216 57 4194304 Bool.false 16777212 16777216 1 2250000 (Ns186p1121 rfl) (Enclosure.sfrac_false_div 12965954503 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12965954503) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p1122) qz361) 226375608064910080 72057594037927936 Bool.false 16777212 16777216 122 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q3 12965954503 16777216 226375608064910080 72057594037927936 122 Ns186p1122 Ns186p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777212 16777216 Ns186p1122 Ns186p89 53948770462 34359738368 4504395 4500000 (Ns186p1126 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p1128 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz139) Bool.false Ns186p1099 Ns186p1100 2000303016633589 147456000000000000000 103727636025 134217728 1822 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz139) (@HAdd.hAdd Real Real Real qz357 qz492 (Enclosure.sfrac Bool.true Ns186p1101 Ns186p1102)) Bool.false Ns186p1099 Ns186p1100 2000303016633589 147456000000000000000 Ns186p1103 (Ns186p1120 rfl rfl)) 

noncomputable def Ns186p1129 := Ns186p1098 40269 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 285 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 126463129 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 165 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 32005200 134217728) qz142 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz139) qz139 1) Bool.false 4194303 4194304 8277769 589824000000 134217696 134217728 1884 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz139) qz139 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz139)) Bool.false 4194303 4194304 8277769 589824000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz139) qz139) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz139)) Bool.false 16777212 16777216 132444304 9437184000000 4194303 4194304 8277769 589824000000 (Ns186p1127 rfl rfl) rfl)) rfl) (Ns186p1128 rfl) RS187to204.d7 

noncomputable def Ns186p1130 := nat_lit 727595342681191081090040647649381716500507896512387207509701164744960 

noncomputable def Ns186p1131 := nat_lit 548885411468576069857669673917224287352401659955858924984882381056 

noncomputable def Ns186p1132 := nat_lit 1904718178260741803503670231038228989607521554844895105218289431429376 

noncomputable def Ns186p1133 := BSN.sin_dyadic_bound_f 164981486 134217728 3 2 134217728 67108864 Ns186p1130 Ns186p111 Ns186p1131 Ns186p1132 Ns186p114 Ns186p1131 126463129 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 164981486) qz362 0 2 Ns186p1130 Ns186p111 Ns186p1131 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 164981486) qz363 0 2 Ns186p1132 Ns186p114 Ns186p1131 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1134 := nat_lit 1090686294518867043371474780416 

noncomputable def Ns186p1135 := BSN.sin_dyadic_bound_f 32316548 134217728 2 1 134217728 67108864 Ns186p1134 Ns186p123 Ns186p1134 Ns186p1134 Ns186p124 Ns186p1134 32005200 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 32316548) qz362 0 1 Ns186p1134 Ns186p123 Ns186p1134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 32316548) qz363 0 1 Ns186p1134 Ns186p124 Ns186p1134 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1136 := nat_lit 198280325787941225476870808834177901729541398588889106942684154163105 

noncomputable def Ns186p1137 := nat_lit 40807297224363242351112519492229382657544583957518828100887637921 

noncomputable def Ns186p1138 := nat_lit 519239546201482811951807460010335656957829543168302154366295157108641 

noncomputable def Ns186p1139 := BSN.sin_dyadic_bound_f 119218109 134217728 3 2 134217728 67108864 Ns186p1136 Ns186p111 Ns186p1137 Ns186p1138 Ns186p114 Ns186p1137 104148310 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 119218109) qz362 0 2 Ns186p1136 Ns186p111 Ns186p1137 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 119218109) qz363 0 2 Ns186p1138 Ns186p114 Ns186p1137 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1140 := nat_lit 2001214990179972485400491268561 

noncomputable def Ns186p1141 := BSN.sin_dyadic_bound_f 37611741 134217728 2 1 134217728 67108864 Ns186p1140 Ns186p123 Ns186p1140 Ns186p1140 Ns186p124 Ns186p1140 37121404 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 37611741) qz362 0 1 Ns186p1140 Ns186p123 Ns186p1140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 37611741) qz363 0 1 Ns186p1140 Ns186p124 Ns186p1140 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1142 := Ns186p1096 68575 BSN.abs_quadSignPos (BSN.cos_quad_nat3 79 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 104148310 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 13 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 37121404 134217728) qz142 rfl rfl (Ns186p1129 RS187to204.d9 RS187to204.d11 RS187to204.d13 RS187to204.d17 (Ns186p1133 rfl rfl) (Ns186p1135 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns186p1128 rfl) RS187to204.d19 RS187to204.d21 RS187to204.d23 RS187to204.d25 RS187to204.d17 (Ns186p1139 rfl rfl) (Ns186p1141 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns186p1143 := nat_lit 32690302386590063884700160000 

noncomputable def Ns186p1144 := BSN.sin_dyadic_bound_f 13446360 134217728 2 1 134217728 67108864 Ns186p1143 Ns186p123 Ns186p1143 Ns186p1143 Ns186p124 Ns186p1143 13423878 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 13446360) qz362 0 1 Ns186p1143 Ns186p123 Ns186p1143 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 13446360) qz363 0 1 Ns186p1143 Ns186p124 Ns186p1143 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1145 := nat_lit 3046919797392578733658237615712279986359595379708264399097990381609394538658000509052551766663135322177536 

noncomputable def Ns186p1146 := nat_lit 3022155994351341433815386564663861974778628663536284579793736440062884759892893881996206759011680256 

noncomputable def Ns186p1147 := nat_lit 18452038326385658985416186308361748109173092299936150111146039513609617625246882076146966480690996723056640 

noncomputable def Ns186p1148 := BSN.cos_dyadic_bound_f 194996316 134217728 4 3 134217728 67108864 Ns186p1145 Ns186p127 Ns186p1146 Ns186p1147 Ns186p130 Ns186p1146 15795706 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 194996316) qz364 0 3 Ns186p1145 Ns186p127 Ns186p1146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 194996316) qz365 0 3 Ns186p1147 Ns186p130 Ns186p1146 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1149 := Ns186p1094 92440 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 13423878 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 86 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 15795706 134217728) qz142 rfl rfl (Ns186p1142 rfl rfl) (Ns186p1128 rfl) RS187to204.d27 RS187to204.d29 RS187to204.d31 RS187to204.d33 RS187to204.d17 (Ns186p1144 rfl rfl) (Ns186p1148 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns186p1150 := nat_lit 194329637949503325288896250710858214008893484339514830034127280800000 

noncomputable def Ns186p1151 := nat_lit 126885832502371169052658397799421548534833566074675917520100000000 

noncomputable def Ns186p1152 := nat_lit 582735142183505233528583435336975798929610785886395138267341642400000 

noncomputable def Ns186p1153 := BSN.cos_dyadic_bound_f 137380990 134217728 3 2 134217728 67108864 Ns186p1150 Ns186p117 Ns186p1151 Ns186p1152 Ns186p120 Ns186p1151 69836461 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 137380990) qz364 0 2 Ns186p1150 Ns186p117 Ns186p1151 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 137380990) qz365 0 2 Ns186p1152 Ns186p120 Ns186p1151 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1154 := Ns186p1092 Bool.false 50339012 92440 Bool.true 137380990 7074237752028440 1 Bool.false 69836461 Bool.true Bool.false 25648096 103008 BSN.abs_quadSignNeg qz431 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 69836461 134217728) qz142 rfl (Ns186p1149 rfl) (Ns186p1128 rfl) RS187to204.d35 RS187to204.d37 RS187to204.d17 (Ns186p1153 rfl rfl) rfl 

noncomputable def Ns186p1155 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz139) qz139 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz139) qz139 8) 25648096 134217728 103008 134217728 25648096 134217728 103008 134217728 6884858345291776 801503 2097152 3219 2097152 (Ns186p1154 rfl rfl rfl rfl) 

noncomputable def Ns186p1156 := @Enclosure.Real.IsNear.mulLit_ff qz731 (Zeta.RiemannSiegel.correction qz141) 2856473 8388608 1 8388608 14431566166723 35184372088832 797290628768351 19791209299968000000 41223379102957747979 295147905179352825856 

noncomputable abbrev qz736 := (@HPow.hPow Real Real Real qz7 qz140 qz9)

noncomputable def Ns186p1157 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz736 1 1 0 1 2856473 8388608 1 8388608 2856473 8388608 1 8388608 

noncomputable def Ns186p1158 := @Enclosure.Real.IsNear.sqrt_image qz140 49913618661 671088640 18693 671088640 72345147 72345175 8388608 (@Enclosure.Real.IsNear.of_eq qz140 (@HMul.hMul Real Real Real qz5 qz139 qz3) Bool.false 49913618661 671088640 18693 671088640 (BSN.t_div_two_pi_mk qz139 467325 1000 qz142) (@Enclosure.Real.IsNear.mulLit_ff qz139 qz3 467325 1000 0 1 2670177 16777216 1 16777216 49913618661 671088640 18693 671088640 (Enclosure.Real.IsNear.const Bool.false 467325 1000) RS187to204.d40 rfl)) 

noncomputable abbrev qz932 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 467325 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz737 := qz932

noncomputable abbrev qz496 := qz737

noncomputable abbrev qz144 := qz496

noncomputable def Ns186p1159 := @Enclosure.Real.IsNear.sqrt_image qz144 72345161 8388608 7 4194304 24634834 24634840 8388608 (@Enclosure.Real.IsNear.recentre' qz144 Bool.false 144690322 16777216 28 16777216 72345161 8388608 7 4194304 (Ns186p1158 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns186p1160 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz144) 24634837 8388608 3 8388608 2856472 2856474 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz144) Bool.false 49269674 16777216 6 16777216 24634837 8388608 3 8388608 (Ns186p1159 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns186p1161 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz144)) Bool.false 5712946 16777216 2 16777216 2856473 8388608 1 8388608 (Ns186p1160 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz145 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz490))

noncomputable abbrev qz738 := (@HMul.hMul Real Real Real qz891 qz931 qz931)

noncomputable abbrev qz497 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz738 qz730) qz640)

noncomputable abbrev qz146 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz497))

noncomputable def Ns186p1162 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz141) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz145) qz146) Bool.false 14431566166723 

noncomputable def Ns186p1163 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz145) qz146 5902609 4194304 183 

noncomputable abbrev qz739 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz145))

noncomputable def Ns186p1164 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz145) (@Neg.neg Real Real.instNeg qz739) Bool.true 5902609 4194304 183 8388608 (BSN.inv_eq_neg_inv_neg qz145) 

noncomputable def Ns186p1165 := @Enclosure.Real.IsNear.recentre' qz739 Bool.false 23610436 16777216 366 16777216 5902609 4194304 

noncomputable def Ns186p1166 := @Enclosure.Real.IsNear.recentre' qz145 Bool.true 11921634 16777216 415027216 37748736000000 5960817 8388608 25939201 2359296000000 

noncomputable abbrev qz147 := (@HMul.hMul Real Real Real qz342 qz340 qz490)

noncomputable def Ns186p1167 := @Enclosure.Real.IsNear.cos_image qz147 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2056289) (@Nat.cast Real Real.instNatCast 524288)) Bool.false 2056289 524288 177 16777216 Bool.true 11921634 16777216 1 

noncomputable def Ns186p1168 := nat_lit 188902527885798042553325681 

noncomputable def Ns186p1169 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz141 884279719003555 140737488355328 1 500000000000000 5236297 8388608 7 4194304 4630351239779158035835 1180591620717411303424 Ns186p1168 

noncomputable def Ns186p1170 := @Enclosure.Real.IsNear.subLit_ff_p qz144 qz1 72345161 8388608 7 4194304 8 1 0 1 5236297 5236297 8388608 7 

noncomputable def Ns186p1171 := @Ns186p1170 4194304 (@Enclosure.Real.IsNear.recentre' qz144 Bool.false 144690322 16777216 28 16777216 72345161 8388608 7 4194304 (Ns186p1158 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns186p1172 := @Enclosure.Real.IsNear.recentre' qz147 Bool.false 4630351239779158035835 1180591620717411303424 Ns186p1168 Ns186p159 2056289 524288 177 16777216 (@Ns186p1169 Ns186p159 RS187to204.d39 (Ns186p1171 rfl rfl) rfl) 

noncomputable def Ns186p1173 := nat_lit 1211219773962000620964732659964667266005169992000993002822397313916794780796859473866721 

noncomputable def Ns186p1174 := nat_lit 267446391895203449767762120240450676325186268571295773991722628412075560729568489441 

noncomputable def Ns186p1175 := nat_lit 3633124429102211455994662455653520896662859603465836416919208496493560191269119284621281 

noncomputable def Ns186p1176 := BSN.cos_dyadic_bound_f 26816654267 34359738368 3 2 16777216 4504395 Ns186p1173 Ns186p851 Ns186p1174 Ns186p1175 Ns186p854 Ns186p1174 11921634 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 26816654267) qz371 0 2 Ns186p1173 Ns186p851 Ns186p1174 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 26816654267) qz372 0 2 Ns186p1175 Ns186p854 Ns186p1174 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1177 := @Ns186p1167 2250000 (Ns186p1172 rfl) (Enclosure.sfrac_false_div 2056289 524288) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2056289) (@Nat.cast Real Real.instNatCast 524288)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 58970446371042443132928) (@Nat.cast Real Real.instNatCast 75557863725914323419136)) 226375608064910080 72057594037927936 Bool.false 11921634 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 2056289 524288 226375608064910080 72057594037927936 0 58970446371042443132928 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 11921634 16777216 58970446371042443132928 75557863725914323419136 26816654267 34359738368 4504395 4500000 (Ns186p1176 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p1178 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz145) 5960817 8388608 25939201 2359296000000 11805035 11805401 8388608 (@Enclosure.Real.IsNear.neg qz145 Bool.true 5960817 8388608 25939201 2359296000000 (Ns186p1166 (Ns186p1177 rfl rfl) rfl)) 

noncomputable def Ns186p1179 := Ns186p1164 (@Enclosure.Real.IsNear.neg qz739 Bool.false 5902609 4194304 183 8388608 (@Ns186p1165 183 8388608 (Ns186p1178 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p1180 := @Enclosure.Real.IsNear.recentre' qz146 Bool.true 2444947 8388608 

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz342 qz340 qz497)

noncomputable def Ns186p1181 := @Enclosure.Real.IsNear.cos_image qz148 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 31315503)) qz360) Bool.true 31315503 16777216 

noncomputable def Ns186p1182 := nat_lit 18485410480023088002224039405 

noncomputable def Ns186p1183 := nat_lit 22268321131660379595920704015697 

noncomputable def Ns186p1184 := @Enclosure.Real.IsNear.recentre' qz148 Bool.true Ns186p1182 Ns186p427 Ns186p1183 

noncomputable abbrev qz149 := qz497

noncomputable def Ns186p1185 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz149 884279719003555 140737488355328 1 500000000000000 20904483143471 

noncomputable abbrev qz498 := (@HSub.hSub Real Real Real qz633 qz738 qz730)

noncomputable abbrev qz150 := qz498

noncomputable def Ns186p1186 := @Enclosure.Real.IsNear.subLit_tf qz150 qz26 16506436632367 70368744177664 4125891 1099511627776 1 16 

noncomputable abbrev qz499 := qz738

noncomputable abbrev qz151 := qz499

noncomputable def Ns186p1187 := @Enclosure.Real.IsNear.subLit_ff_n qz151 qz141 27418806272209 70368744177664 2290883 1099511627776 5236297 8388608 7 4194304 

noncomputable def Ns186p1188 := @Enclosure.Real.IsNear.mulLit_ff qz141 qz141 5236297 8388608 7 4194304 5236297 8388608 7 4194304 27418806272209 70368744177664 

noncomputable def Ns186p1189 := nat_lit 121353474428141688220812308981077142315232451815528677805588335118523937799172519487187746064321 

noncomputable def Ns186p1190 := nat_lit 889431901812325949766614108506537778102758339068026236350938193362914227449207885031573441 

noncomputable def Ns186p1191 := nat_lit 732685863527650432106713771203189315036810817400141298468605317588884119497527914663517843130305 

noncomputable def Ns186p1192 := BSN.cos_dyadic_bound_t 31315503 16777216 4 3 8388608 2250000 Ns186p1189 Ns186p180 Ns186p1190 Ns186p1191 Ns186p183 Ns186p1190 2444947 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 31315503) qz642 0 3 Ns186p1189 Ns186p180 Ns186p1190 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 31315503) (BSN.cosOddQ 16777216) 0 3 Ns186p1191 Ns186p183 Ns186p1190 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1193 := @Ns186p1180 910027216 37748736000000 2444947 8388608 56876701 2359296000000 (@Ns186p1181 397 16777216 Bool.true 2444947 8388608 1 2250000 (@Ns186p1184 Ns186p530 31315503 16777216 397 16777216 (@Ns186p1185 70368744177664 4125891 1099511627776 Ns186p1182 Ns186p427 Ns186p1183 Ns186p530 RS187to204.d39 (@Ns186p1186 0 1 334471730295536 20904483143471 70368744177664 4125891 1099511627776 (@Ns186p1187 138466026385766875136 16506436632367 70368744177664 4125891 1099511627776 (@Ns186p1188 2290883 1099511627776 (Ns186p1171 rfl rfl) (Ns186p1171 rfl rfl) rfl) (Ns186p1171 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 31315503 16777216) (BSN.cos_neg_of_bound 31315503 16777216 Bool.true 2444947 8388608 1 2250000 (Ns186p1192 rfl rfl)) rfl rfl) 

noncomputable def Ns186p1194 := @Ns186p1156 126975428193846018993 Ns186p1089 (Ns186p1157 qz28 (@Enclosure.Real.IsNear.of_eq qz736 (@Inv.inv Real Real.instInv (Real.sqrt qz144)) Bool.false 2856473 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz140 (BSN.t_div_two_pi_nonneg qz139 467325 1000 qz142)) Ns186p1161) rfl) (@Ns186p1162 35184372088832 797290628768351 19791209299968000000 (BSN.correction_mk qz141 (BSN.cos_two_pi_p_ne_zero_mk qz139 467325 1000 8 qz142 rfl rfl (@BSN.floor_sqrt_eq_dec qz139 467325 1000 8 qz142 rfl rfl rfl))) (@Ns186p1163 8388608 2444947 8388608 56876701 2359296000000 14431566166723 35184372088832 797290628768351 19791209299968000000 Ns186p1179 (Ns186p1193 rfl) rfl)) 

noncomputable def Ns186p1195 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz139) (hardyZApproximantRS₀ qz139) Bool.false 71578140026302710005 295147905179352825856 14284287147437622018993 Ns186p1089 (@Eq.refl Real (hardyZApproximantRS₀ qz139)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz139) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz139) qz139 8) (@HMul.hMul Real Real Real qz5 qz731 (Zeta.RiemannSiegel.correction qz141))) Bool.false 71578140026302710005 295147905179352825856 14284287147437622018993 Ns186p1089 (BSN.hardyZApproximantRS₀_eq qz139 8 (@BSN.floor_sqrt_eq_dec qz139 467325 1000 8 qz142 rfl rfl rfl)) (@Ns186p1091 71578140026302710005 295147905179352825856 14284287147437622018993 Ns186p1089 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz139) qz139 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz139) qz139 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz139) qz139 8)) Bool.false 801503 2097152 3219 2097152 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz139) qz139 8) (Ns186p1155 (Ns186p1154 rfl rfl rfl rfl) rfl rfl)) (Ns186p1194 rfl) rfl rfl)) 

theorem RS187to204.d52 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz139) Bool.false 71578140026302710005 295147905179352825856 14284287147437622018993 Ns186p1089 := Ns186p1195 

noncomputable def Ns186p1196 := nat_lit 64322780802823475669692841984 

noncomputable abbrev qz933 := (Enclosure.sfrac Bool.false 468783 1000)

noncomputable abbrev qz740 := qz933

noncomputable abbrev qz500 := qz740

noncomputable abbrev qz152 := qz500

noncomputable abbrev qz934 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 468783 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz741 := qz934

noncomputable abbrev qz501 := qz741

noncomputable abbrev qz153 := qz501

noncomputable abbrev qz935 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 468783 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz742 := qz935

noncomputable abbrev qz502 := qz742

noncomputable abbrev qz154 := qz502

noncomputable abbrev qz743 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz153 qz9))

noncomputable def Ns186p1197 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 8) (@HMul.hMul Real Real Real qz5 qz743 (Zeta.RiemannSiegel.correction qz154)) 104210937 33554432 103329 67108864 83670058791889357495 590295810358705651712 5055581922861640717 332041393326771929088000 Ns186p1196 

noncomputable def Ns186p1198 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos BSN.quadSignNeg 7 8 468783 1000 126 134217728 67108864 2251799813685248 Bool.false 104149415755 1827 279097919 60 47453128 8 

noncomputable def Ns186p1199 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 468783 1000 40 86 134217728 67108864 2251799813685248 Bool.false 104149415755 1827 

noncomputable def Ns186p1200 := Ns186p1199 240485871 61 54794152 8 261175631 61 50729528 8 Bool.true 181405470 68789 Bool.true 153123744 Bool.true 154010656 7074237752028440 1 Bool.false 55943586 Bool.false Bool.false 55136174 Bool.true Bool.true 179406113 

noncomputable def Ns186p1201 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 468783 1000 80 13 134217728 67108864 2251799813685248 Bool.false 104149415755 1827 

noncomputable def Ns186p1202 := Ns186p1201 186065264 60 67108856 8 216015088 60 60023992 8 Bool.true 189328472 40396 Bool.false 58885970 Bool.false 144441473 7074237752028440 1 Bool.false 121505952 Bool.false Bool.false 118131397 Bool.true Bool.true 181405470 

noncomputable def Ns186p1203 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 468783 1000 287 166 134217728 67108864 2251799813685248 Bool.false 104149415755 1827 

noncomputable def Ns186p1204 := Ns186p1203 93032624 60 94906264 8 147453232 60 77490640 16 Bool.true 134217720 1892 Bool.false 29462222 Bool.false 28280752 7074237752028440 1 Bool.false 29226185 Bool.false Bool.false 131249244 Bool.true Bool.true 189328472 

noncomputable def Ns186p1205 := nat_lit 29670804550403050148183333625496451765924032967070902907 

noncomputable def Ns186p1206 := nat_lit 38236872917611367381882673931180182399178201314099200 

noncomputable def Ns186p1207 := nat_lit 10866802123549560009542257988640000 

noncomputable def Ns186p1208 := nat_lit 30565048826014722965722120429587750720 

noncomputable abbrev qz936 := (@Eq.refl Real (Enclosure.sfrac Bool.false 468783 1000))

noncomputable abbrev qz744 := qz936

noncomputable abbrev qz503 := qz744

noncomputable abbrev qz155 := qz503

noncomputable def Ns186p1209 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz152 468783 1000 879031004356 16000000 937566 4000 2000 Ns186p1207 Ns186p1208 qz155 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns186p1210 := nat_lit 85451917105160784426768000841429781085861214945164200372160 

noncomputable abbrev qz745 := (Real.log (Enclosure.sfrac Bool.false 879031004356 16000000))

noncomputable abbrev qz156 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 468783 4000) qz745) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 937566))))))

noncomputable abbrev qz746 := (Enclosure.sfrac Bool.false 468783 2000)

noncomputable abbrev qz504 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz156 qz746) (@HMul.hMul Real Real Real qz5 qz746 (Real.log Real.pi)))

noncomputable def Ns186p1211 := @Enclosure.Real.IsNear.addLit_ft_p qz504 (Enclosure.sfrac Bool.true Ns186p1207 Ns186p1208) 2795740871979604221003 3602879701896396800 50162315368026367 3686400000000000000000 Ns186p1207 Ns186p1208 0 1 Ns186p1210 

noncomputable def Ns186p1212 := nat_lit 938094969784603352205581352960000 

noncomputable abbrev qz505 := (@HSub.hSub Real Real Real qz12 qz156 qz746)

noncomputable abbrev qz506 := (@HMul.hMul Real Real Real qz5 qz746 (Real.log Real.pi))

noncomputable def Ns186p1213 := @Enclosure.Real.IsNear.subLit_ff_p qz505 qz506 18812236871793104391543 18014398509481984000 47678312658041 7200000000000000000 18006311773863 67108864000 468783 67108864000 Ns186p1212 2795740871979604221003 3602879701896396800 

noncomputable def Ns186p1214 := nat_lit 37624473743586208783086000 

noncomputable abbrev qz507 := qz746

noncomputable def Ns186p1215 := @Enclosure.Real.IsNear.subLit_ff_p qz156 qz507 23034658760028350844279 18014398509481984000 47678312658041 7200000000000000000 468783 2000 0 1 Ns186p1214 18812236871793104391543 18014398509481984000 47678312658041 7200000000000000000 

noncomputable def Ns186p1216 := nat_lit 51869440304135106151837751679167496192 

noncomputable def Ns186p1217 := nat_lit 26388400666793955353952256 

noncomputable def Ns186p1218 := nat_lit 7882150552626874267545143093644414848590975555638997734255291355159000495092672461256844285072171674678293416687829723640081234806074695227377304207360 

noncomputable def Ns186p1219 := nat_lit 174641767762105576011179861726172289649888539780223906473240216804108493673581328577602115205588760227091616428924074568640042789662668429916836462592 

noncomputable def Ns186p1220 := nat_lit 41284836703584547884275834411243442736746654786645903514004942422827674429703434420784709335478104305938739617133225126028706133717677737246720 

noncomputable def Ns186p1221 := BSN.log_dyadic_bound 354743004356 1403319004356 7 6 Ns186p1218 67108864 18000000 Ns186p1219 Ns186p1220 34680452 1758062008712 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 354743004356) (BSN.artanhQ 1403319004356) 0 6 Ns186p1219 Ns186p1218 Ns186p1220 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns186p1222 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 468783 4000) qz745 468783 4000 0 1 49152226497966713 4503599627370496 100000027 1800000000000000 23041728194396329620279 18014398509481984000 5208701406349 800000000000000000 (Enclosure.Real.IsNear.const Bool.false 468783 4000) (BSN.isNear_log_sfrac 879031004356 16000000 49152226497966713 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 879031004356) qz353)) Bool.false Ns186p1217 Ns186p89 1000000270000000 18000000000000000000000 49152226497966713 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 879031004356 16000000 15 1758062008712 1048576000000 34680452 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns186p1221 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p1223 := BSN.arctan_dyadic_bound_f 1000 937566 1 0 8388608 2250000 0 1 1 0 1 1 8947 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 937566) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 937566) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz747 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 937566)))

noncomputable def Ns186p1224 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz747 884279719003555 562949953421312 1 2000000000000000 8947 8388608 1 2250000 7412839211837713022976 883679295997347 562949953421312 8000000009 18000000000000000 qz16 (Ns186p1223 rfl) rfl rfl 

noncomputable def Ns186p1225 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 468783 4000) qz745) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz747)) 23041728194396329620279 18014398509481984000 5208701406349 800000000000000000 883679295997347 2251799813685248 8000000009 72000000000000000 Ns186p1216 23034658760028350844279 18014398509481984000 47678312658041 7200000000000000000 (Ns186p1222 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz747) 1 4 0 1 883679295997347 562949953421312 8000000009 18000000000000000 883679295997347 2251799813685248 8000000009 72000000000000000 qz356 Ns186p1224 rfl) 

noncomputable def Ns186p1226 := @Ns186p1211 Ns186p1205 Ns186p1206 50162315368026367 3686400000000000000000 (@Ns186p1213 50162315368026367 3686400000000000000000 (Ns186p1215 (Ns186p1225 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 468783 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz507 (Real.log Real.pi) 468783 2000 0 1 38410761 33554432 1 33554432 18006311773863 67108864000 468783 67108864000 (Enclosure.Real.IsNear.const Bool.false 468783 2000) RS187to204.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns186p1207 Ns186p1208) 

noncomputable def Ns186p1227 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns186p1205 Ns186p1206 50162315368026367 3686400000000000000000 13018676969 16777216 229 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz357 qz504 (Enclosure.sfrac Bool.true Ns186p1207 Ns186p1208)) Bool.false Ns186p1205 Ns186p1206 50162315368026367 3686400000000000000000 Ns186p1209 (Ns186p1226 rfl rfl)) 

noncomputable def Ns186p1228 := nat_lit 3798510383533418430332928 

noncomputable def Ns186p1229 := nat_lit 857642339761536460591437516212795518193082702160594248153881800856946137897394719814728138326611054513332468643687351330514234147803136 

noncomputable def Ns186p1230 := nat_lit 612071571371267312166394423953148059049511998850573835076362549546443505675998813923629492872029728075846315536800975133560999936 

noncomputable def Ns186p1231 := nat_lit 4282879939736797942156668979272179287298652367604004014537605198447063990476123291389095882322428654191488734762293795956849969533751296 

noncomputable def Ns186p1232 := BSN.sin_dyadic_bound_f 53980079194 34359738368 4 3 16777216 4504395 Ns186p1229 Ns186p102 Ns186p1230 Ns186p1231 Ns186p105 Ns186p1230 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53980079194) qz358 0 3 Ns186p1229 Ns186p102 Ns186p1230 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53980079194) qz359 0 3 Ns186p1231 Ns186p105 Ns186p1230 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1233 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz152) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13018676969) qz360) Bool.false 13018676969 16777216 229 16777216 Bool.true 16777215 16777216 1 2250000 (Ns186p1227 rfl) (Enclosure.sfrac_false_div 13018676969 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13018676969) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p1228) qz361) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 123 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 13018676969 16777216 226375608064910080 72057594037927936 123 Ns186p1228 Ns186p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns186p1228 Ns186p89 53980079194 34359738368 4504395 4500000 (Ns186p1232 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p1234 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns186p1205 Ns186p1206 50162315368026367 3686400000000000000000 104149415755 134217728 1827 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz357 qz504 (Enclosure.sfrac Bool.true Ns186p1207 Ns186p1208)) Bool.false Ns186p1205 Ns186p1206 50162315368026367 3686400000000000000000 Ns186p1209 (Ns186p1226 rfl rfl)) 

noncomputable def Ns186p1235 := Ns186p1204 40396 BSN.abs_quadSignPos (BSN.cos_quad_nat3 287 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 29226185 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 166 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 131249244 134217728) qz155 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) Bool.true 16777215 16777216 33251701 2359296000000 134217720 134217728 1892 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.true 16777215 16777216 33251701 2359296000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz152) qz152) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.true 16777215 16777216 532027216 37748736000000 16777215 16777216 33251701 2359296000000 (Ns186p1233 rfl rfl) rfl)) rfl) (Ns186p1234 rfl) RS187to204.d7 

noncomputable def Ns186p1236 := nat_lit 753463104215148635675629616656 

noncomputable def Ns186p1237 := BSN.sin_dyadic_bound_f 29462222 134217728 2 1 134217728 67108864 Ns186p1236 Ns186p123 Ns186p1236 Ns186p1236 Ns186p124 Ns186p1236 29226185 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 29462222) qz362 0 1 Ns186p1236 Ns186p123 Ns186p1236 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 29462222) qz363 0 1 Ns186p1236 Ns186p124 Ns186p1236 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1238 := nat_lit 639681533524203967020379734016 

noncomputable def Ns186p1239 := BSN.cos_dyadic_bound_f 28280752 134217728 2 1 134217728 67108864 Ns186p1238 Ns186p134 Ns186p1238 Ns186p1238 Ns186p135 Ns186p1238 131249244 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 28280752) qz364 0 1 Ns186p1238 Ns186p134 Ns186p1238 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 28280752) qz365 0 1 Ns186p1238 Ns186p135 Ns186p1238 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1240 := nat_lit 6555498539842988230228632273430327189318556827292811676482224800000 

noncomputable def Ns186p1241 := nat_lit 144575488024922672951311716988400338010304571422858096100000000 

noncomputable def Ns186p1242 := nat_lit 19666206468552914845339994196857004767279649872735589313254474400000 

noncomputable def Ns186p1243 := BSN.cos_dyadic_bound_f 58885970 134217728 3 2 134217728 67108864 Ns186p1240 Ns186p117 Ns186p1241 Ns186p1242 Ns186p120 Ns186p1241 121505952 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 58885970) qz364 0 2 Ns186p1240 Ns186p117 Ns186p1241 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 58885970) qz365 0 2 Ns186p1242 Ns186p120 Ns186p1241 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1244 := nat_lit 427347869809225984732277213549455652391685074408799138767311322153985 

noncomputable def Ns186p1245 := nat_lit 189467737618901323849814254258215672895943277167610156456507540481 

noncomputable def Ns186p1246 := nat_lit 1118937663639446976917350145741680073745915096240964470803933402956801 

noncomputable def Ns186p1247 := BSN.sin_dyadic_bound_f 144441473 134217728 3 2 134217728 67108864 Ns186p1244 Ns186p111 Ns186p1245 Ns186p1246 Ns186p114 Ns186p1245 118131397 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 144441473) qz362 0 2 Ns186p1244 Ns186p111 Ns186p1245 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 144441473) qz363 0 2 Ns186p1246 Ns186p114 Ns186p1245 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1248 := Ns186p1202 68789 BSN.abs_quadSignPos (BSN.cos_quad_nat0 80 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 121505952 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 13 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 118131397 134217728) qz155 rfl rfl (Ns186p1235 RS187to204.d9 RS187to204.d11 RS187to204.d13 RS187to204.d17 (Ns186p1237 rfl rfl) (Ns186p1239 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns186p1234 rfl) RS187to204.d19 RS187to204.d21 RS187to204.d23 RS187to204.d25 RS187to204.d17 (Ns186p1243 rfl rfl) (Ns186p1247 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns186p1249 := nat_lit 1156678641253071973743994599403244362436778070005149198423126704025315370873373643903095541796788257161216 

noncomputable def Ns186p1250 := nat_lit 166153874520079892237275538069413607447508365489991156959997161092362251680174088397258428132622336 

noncomputable def Ns186p1251 := nat_lit 7012470373869645543600271658766589613286644732519399057211042348259755782704686974620281848112528280780800 

noncomputable def Ns186p1252 := BSN.cos_dyadic_bound_f 153123744 134217728 4 3 134217728 67108864 Ns186p1249 Ns186p127 Ns186p1250 Ns186p1251 Ns186p130 Ns186p1250 55943586 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 153123744) qz364 0 3 Ns186p1249 Ns186p127 Ns186p1250 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 153123744) qz365 0 3 Ns186p1251 Ns186p130 Ns186p1250 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1253 := nat_lit 1183738760888665785121121459723286613107504908076074854598493408303506309218604136929854512486790532694016 

noncomputable def Ns186p1254 := nat_lit 178077581425638403131580296176229832970782106525659369366644899872183280443696859002440576334299136 

noncomputable def Ns186p1255 := nat_lit 7176412195743223530411891692439745685275231265446650251269137132097403775255770683015713362695422371430400 

noncomputable def Ns186p1256 := BSN.cos_dyadic_bound_f 154010656 134217728 4 3 134217728 67108864 Ns186p1253 Ns186p127 Ns186p1254 Ns186p1255 Ns186p130 Ns186p1254 55136174 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 154010656) qz364 0 3 Ns186p1253 Ns186p127 Ns186p1254 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 154010656) qz365 0 3 Ns186p1255 Ns186p130 Ns186p1254 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1257 := Ns186p1200 92728 BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 55943586 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 86 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 55136174 134217728) qz155 rfl rfl (Ns186p1248 rfl rfl) (Ns186p1234 rfl) RS187to204.d27 RS187to204.d29 RS187to204.d31 RS187to204.d33 RS187to204.d17 (Ns186p1252 rfl rfl) (Ns186p1256 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns186p1258 := nat_lit 122925420531591069805558599743192245004381786601324287516593975910656 

noncomputable def Ns186p1259 := nat_lit 50795680507222238081243881149385589871051940706232626221951672576 

noncomputable def Ns186p1260 := nat_lit 368674670233758764940513311467277963833403255922560397297338024386816 

noncomputable def Ns186p1261 := BSN.cos_dyadic_bound_f 122526026 134217728 3 2 134217728 67108864 Ns186p1258 Ns186p117 Ns186p1259 Ns186p1260 Ns186p120 Ns186p1259 82068973 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 122526026) qz364 0 2 Ns186p1258 Ns186p117 Ns186p1259 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 122526026) qz365 0 2 Ns186p1260 Ns186p120 Ns186p1259 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1262 := Ns186p1198 Bool.true 179406113 92728 Bool.true 122526026 7074237752028440 1 Bool.false 82068973 Bool.true Bool.true 208421874 103329 BSN.abs_quadSignNeg qz431 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 82068973 134217728) qz155 rfl (Ns186p1257 rfl) (Ns186p1234 rfl) RS187to204.d35 RS187to204.d37 RS187to204.d17 (Ns186p1261 rfl rfl) rfl 

noncomputable def Ns186p1263 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 8) 208421874 134217728 103329 134217728 208421874 134217728 103329 134217728 55947820787564544 104210937 33554432 103329 67108864 (Ns186p1262 rfl rfl rfl rfl) 

noncomputable def Ns186p1264 := @Enclosure.Real.IsNear.mulLit_ff qz743 (Zeta.RiemannSiegel.correction qz154) 2854249 8388608 1 8388608 29314211476255 70368744177664 882734987983927 19791209299968000000 83670058791889357495 590295810358705651712 

noncomputable abbrev qz748 := (@HPow.hPow Real Real Real qz7 qz153 qz9)

noncomputable def Ns186p1265 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz748 1 1 0 1 2854249 8388608 1 8388608 2854249 8388608 1 8388608 

noncomputable def Ns186p1266 := @Enclosure.Real.IsNear.sqrt_image qz153 1251733584591 16777216000 468783 16777216000 72457913 72457941 8388608 (@Enclosure.Real.IsNear.of_eq qz153 (@HMul.hMul Real Real Real qz5 qz152 qz3) Bool.false 1251733584591 16777216000 468783 16777216000 (BSN.t_div_two_pi_mk qz152 468783 1000 qz155) (@Enclosure.Real.IsNear.mulLit_ff qz152 qz3 468783 1000 0 1 2670177 16777216 1 16777216 1251733584591 16777216000 468783 16777216000 (Enclosure.Real.IsNear.const Bool.false 468783 1000) RS187to204.d40 rfl)) 

noncomputable abbrev qz937 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 468783 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz749 := qz937

noncomputable abbrev qz508 := qz749

noncomputable abbrev qz157 := qz508

noncomputable def Ns186p1267 := @Enclosure.Real.IsNear.sqrt_image qz157 72457927 8388608 7 4194304 24654026 24654032 8388608 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 144915854 16777216 28 16777216 72457927 8388608 7 4194304 (Ns186p1266 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns186p1268 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz157) 24654029 8388608 3 8388608 2854248 2854250 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz157) Bool.false 49308058 16777216 6 16777216 24654029 8388608 3 8388608 (Ns186p1267 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns186p1269 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz157)) Bool.false 5708498 16777216 2 16777216 2854249 8388608 1 8388608 (Ns186p1268 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz158 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz502))

noncomputable abbrev qz750 := (@HMul.hMul Real Real Real qz891 qz935 qz935)

noncomputable abbrev qz509 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz750 qz742) qz640)

noncomputable abbrev qz159 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz509))

noncomputable def Ns186p1270 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz154) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz158) qz159) Bool.false 29314211476255 

noncomputable def Ns186p1271 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz158) qz159 25863115 16777216 439 

noncomputable abbrev qz751 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz158))

noncomputable def Ns186p1272 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz158) (@Neg.neg Real Real.instNeg qz751) Bool.true 25863115 16777216 439 16777216 (BSN.inv_eq_neg_inv_neg qz158) 

noncomputable def Ns186p1273 := @Enclosure.Real.IsNear.recentre' qz751 Bool.false 25863115 16777216 439 16777216 25863115 16777216 

noncomputable def Ns186p1274 := @Enclosure.Real.IsNear.recentre' qz158 Bool.true 10883259 16777216 415027216 37748736000000 10883259 16777216 25939201 2359296000000 

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz342 qz340 qz502)

noncomputable def Ns186p1275 := @Enclosure.Real.IsNear.cos_image qz160 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16804577) qz460) Bool.false 16804577 4194304 177 16777216 Bool.true 10883259 16777216 1 

noncomputable def Ns186p1276 := nat_lit 188902527886282368835426417 

noncomputable def Ns186p1277 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz154 884279719003555 140737488355328 1 500000000000000 5349063 8388608 7 4194304 4730067926572312918965 1180591620717411303424 Ns186p1276 

noncomputable def Ns186p1278 := @Enclosure.Real.IsNear.subLit_ff_p qz157 qz1 72457927 8388608 7 4194304 8 1 0 1 5349063 5349063 8388608 7 

noncomputable def Ns186p1279 := @Ns186p1278 4194304 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 144915854 16777216 28 16777216 72457927 8388608 7 4194304 (Ns186p1266 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns186p1280 := @Enclosure.Real.IsNear.recentre' qz160 Bool.false 4730067926572312918965 1180591620717411303424 Ns186p1276 Ns186p159 16804577 4194304 177 16777216 (@Ns186p1277 Ns186p159 RS187to204.d39 (Ns186p1279 rfl rfl) rfl) 

noncomputable def Ns186p1281 := nat_lit 1827165996535463544649590758204800582782712011213415957270323554548079414196034572726241 

noncomputable def Ns186p1282 := nat_lit 608484266424509967026567499973117336178453565253508070767834873146757139110447624161 

noncomputable def Ns186p1283 := nat_lit 5480281021073541614014719139614455513675779126509740855669434993897944728309882822930401 

noncomputable def Ns186p1284 := BSN.cos_dyadic_bound_f 29718793147 34359738368 3 2 16777216 4504395 Ns186p1281 Ns186p851 Ns186p1282 Ns186p1283 Ns186p854 Ns186p1282 10883259 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 29718793147) qz371 0 2 Ns186p1281 Ns186p851 Ns186p1282 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 29718793147) qz372 0 2 Ns186p1283 Ns186p854 Ns186p1282 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz752 := (@Nat.cast Real Real.instNatCast 604462909807314587353088)

noncomputable def Ns186p1285 := @Ns186p1275 2250000 (Ns186p1280 rfl) (Enclosure.sfrac_false_div 16804577 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16804577) qz460) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 522818538072032625557504) qz752) 226375608064910080 72057594037927936 Bool.false 10883259 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 16804577 4194304 226375608064910080 72057594037927936 0 522818538072032625557504 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 10883259 16777216 522818538072032625557504 604462909807314587353088 29718793147 34359738368 4504395 4500000 (Ns186p1284 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p1286 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz158) 10883259 16777216 25939201 2359296000000 12931338 12931777 8388608 (@Enclosure.Real.IsNear.neg qz158 Bool.true 10883259 16777216 25939201 2359296000000 (Ns186p1274 (Ns186p1285 rfl rfl) rfl)) 

noncomputable def Ns186p1287 := Ns186p1272 (@Enclosure.Real.IsNear.neg qz751 Bool.false 25863115 16777216 439 16777216 (@Ns186p1273 439 16777216 (Ns186p1286 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p1288 := @Enclosure.Real.IsNear.recentre' qz159 Bool.true 2266874 8388608 

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz342 qz340 qz509)

noncomputable def Ns186p1289 := @Enclosure.Real.IsNear.cos_image qz161 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 30944413)) qz360) Bool.true 30944413 16777216 

noncomputable def Ns186p1290 := nat_lit 18266357648876851426398445645 

noncomputable def Ns186p1291 := nat_lit 901383736494666110558905364690039 

noncomputable def Ns186p1292 := @Enclosure.Real.IsNear.recentre' qz161 Bool.true Ns186p1290 Ns186p427 Ns186p1291 

noncomputable abbrev qz162 := qz509

noncomputable def Ns186p1293 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz162 884279719003555 140737488355328 1 500000000000000 20656764207439 

noncomputable abbrev qz510 := (@HSub.hSub Real Real Real qz633 qz750 qz742)

noncomputable abbrev qz163 := qz510

noncomputable def Ns186p1294 := @Enclosure.Real.IsNear.subLit_tf qz163 qz26 16258717696335 70368744177664 33401809 8796093022208 1 16 

noncomputable abbrev qz511 := qz750

noncomputable abbrev qz164 := qz511

noncomputable def Ns186p1295 := @Enclosure.Real.IsNear.subLit_ff_n qz164 qz154 28612474977969 70368744177664 18721745 8796093022208 5349063 8388608 7 4194304 

noncomputable def Ns186p1296 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz154 5349063 8388608 7 4194304 5349063 8388608 7 4194304 28612474977969 70368744177664 

noncomputable def Ns186p1297 := nat_lit 115664015573549062132175519468559014748841199077903995077627417139205298187078009815778577979761 

noncomputable def Ns186p1298 := nat_lit 770880367042399395235666556892199587595898550601169541618880391948268828316344156613876081 

noncomputable def Ns186p1299 := nat_lit 698490658444882283020891351530643811613002649312085356691785616377507495499044873737870913673585 

noncomputable def Ns186p1300 := BSN.cos_dyadic_bound_t 30944413 16777216 4 3 8388608 2250000 Ns186p1297 Ns186p180 Ns186p1298 Ns186p1299 Ns186p183 Ns186p1298 2266874 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 30944413) qz642 0 3 Ns186p1297 Ns186p180 Ns186p1298 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 30944413) (BSN.cosOddQ 16777216) 0 3 Ns186p1299 Ns186p183 Ns186p1298 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1301 := @Ns186p1288 919027216 37748736000000 1133437 4194304 57439201 2359296000000 (@Ns186p1289 401 16777216 Bool.true 2266874 8388608 1 2250000 (@Ns186p1292 Ns186p430 30944413 16777216 401 16777216 (@Ns186p1293 70368744177664 33401809 8796093022208 Ns186p1290 Ns186p427 Ns186p1291 Ns186p430 RS187to204.d39 (@Ns186p1294 0 1 330508227319024 20656764207439 70368744177664 33401809 8796093022208 (@Ns186p1295 136388009337217351680 16258717696335 70368744177664 33401809 8796093022208 (@Ns186p1296 18721745 8796093022208 (Ns186p1279 rfl rfl) (Ns186p1279 rfl rfl) rfl) (Ns186p1279 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 30944413 16777216) (BSN.cos_neg_of_bound 30944413 16777216 Bool.true 2266874 8388608 1 2250000 (Ns186p1300 rfl rfl)) rfl rfl) 

noncomputable def Ns186p1302 := @Ns186p1264 5055581922861640717 332041393326771929088000 (Ns186p1265 qz28 (@Enclosure.Real.IsNear.of_eq qz748 (@Inv.inv Real Real.instInv (Real.sqrt qz157)) Bool.false 2854249 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz153 (BSN.t_div_two_pi_nonneg qz152 468783 1000 qz155)) Ns186p1269) rfl) (@Ns186p1270 70368744177664 882734987983927 19791209299968000000 (BSN.correction_mk qz154 (BSN.cos_two_pi_p_ne_zero_mk qz152 468783 1000 8 qz155 rfl rfl (@BSN.floor_sqrt_eq_dec qz152 468783 1000 8 qz155 rfl rfl rfl))) (@Ns186p1271 16777216 1133437 4194304 57439201 2359296000000 29314211476255 70368744177664 882734987983927 19791209299968000000 Ns186p1287 (Ns186p1301 rfl) rfl)) 

noncomputable def Ns186p1303 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (hardyZApproximantRS₀ qz152) Bool.true 1916968250358804335287 590295810358705651712 516307048361960008717 332041393326771929088000 (@Eq.refl Real (hardyZApproximantRS₀ qz152)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 8) (@HMul.hMul Real Real Real qz5 qz743 (Zeta.RiemannSiegel.correction qz154))) Bool.true 1916968250358804335287 590295810358705651712 516307048361960008717 332041393326771929088000 (BSN.hardyZApproximantRS₀_eq qz152 8 (@BSN.floor_sqrt_eq_dec qz152 468783 1000 8 qz155 rfl rfl rfl)) (@Ns186p1197 1916968250358804335287 590295810358705651712 516307048361960008717 332041393326771929088000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 8)) Bool.true 104210937 33554432 103329 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz152) qz152 8) (Ns186p1263 (Ns186p1262 rfl rfl rfl rfl) rfl rfl)) (Ns186p1302 rfl) rfl rfl)) 

theorem RS187to204.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz152) Bool.true 1916968250358804335287 590295810358705651712 516307048361960008717 332041393326771929088000 := Ns186p1303 

noncomputable def Ns186p1304 := nat_lit 166020696663385964544000000 

noncomputable def Ns186p1305 := nat_lit 150362626419935311672977129472 

noncomputable abbrev qz938 := (Enclosure.sfrac Bool.false 470239 1000)

noncomputable abbrev qz753 := qz938

noncomputable abbrev qz512 := qz753

noncomputable abbrev qz165 := qz512

noncomputable abbrev qz939 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 470239 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz754 := qz939

noncomputable abbrev qz513 := qz754

noncomputable abbrev qz166 := qz513

noncomputable abbrev qz940 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 470239 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz755 := qz940

noncomputable abbrev qz514 := qz755

noncomputable abbrev qz167 := qz514

noncomputable abbrev qz756 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz166 qz9))

noncomputable def Ns186p1306 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz165) qz165 8) (@HMul.hMul Real Real Real qz5 qz756 (Zeta.RiemannSiegel.correction qz167)) 137029039 67108864 103653 67108864 170062613761783388301 1180591620717411303424 2849408976216793175539 Ns186p1304 Ns186p1305 

noncomputable def Ns186p1307 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz165) qz165 Real.cos BSN.quadSignNeg 7 8 470239 1000 126 134217728 67108864 2251799813685248 Bool.false 104570920874 1833 279097919 60 47453128 8 

noncomputable def Ns186p1308 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz165) qz165 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 470239 1000 40 86 134217728 67108864 2251799813685248 Bool.false 104570920874 1833 

noncomputable def Ns186p1309 := Ns186p1308 240485871 61 54794152 8 261175631 61 50729528 8 Bool.false 159000109 69006 Bool.true 81766053 Bool.true 112777256 7074237752028440 1 Bool.false 110072419 Bool.false Bool.false 89559751 Bool.true Bool.false 170086580 

noncomputable def Ns186p1310 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz165) qz165 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 470239 1000 80 14 134217728 67108864 2251799813685248 Bool.false 104570920874 1833 

noncomputable def Ns186p1311 := Ns186p1310 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 215624508 40524 Bool.false 209480065 Bool.false 40599910 7074237752028440 1 Bool.false 1348626 Bool.false Bool.false 128123815 Bool.true Bool.false 159000109 

noncomputable def Ns186p1312 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz165) qz165 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 470239 1000 288 167 134217728 67108864 2251799813685248 Bool.false 104570920874 1833 

noncomputable def Ns186p1313 := Ns186p1312 93032624 60 94906264 8 147453232 60 77490640 16 Bool.false 134217672 1900 Bool.false 104683126 Bool.false 24265251 7074237752028440 1 Bool.false 95421913 Bool.false Bool.false 24133281 Bool.false Bool.false 215624508 

noncomputable def Ns186p1314 := nat_lit 1365767169651005828220832215124978520865973951859011400047 

noncomputable def Ns186p1315 := nat_lit 1752974583696560606695051440747545252679838089609216000 

noncomputable def Ns186p1316 := nat_lit 11036610277325437370159831295520000 

noncomputable def Ns186p1317 := nat_lit 31139083910441922261736839074820175680 

noncomputable abbrev qz757 := (@Eq.refl Real qz938)

noncomputable abbrev qz515 := qz757

noncomputable abbrev qz168 := qz515

noncomputable def Ns186p1318 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz165 470239 1000 884499868484 16000000 940478 4000 2000 Ns186p1316 Ns186p1317 qz168 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns186p1319 := nat_lit 437045494288321865030666308839993126677111664594883648015040 

noncomputable abbrev qz758 := (Real.log (Enclosure.sfrac Bool.false 884499868484 16000000))

noncomputable abbrev qz169 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 470239 4000) qz758) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 940478))))))

noncomputable abbrev qz759 := (Enclosure.sfrac Bool.false 470239 2000)

noncomputable abbrev qz516 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz169 qz759) (@HMul.hMul Real Real Real qz5 qz759 (Real.log Real.pi)))

noncomputable def Ns186p1320 := @Enclosure.Real.IsNear.addLit_ft_p qz516 (Enclosure.sfrac Bool.true Ns186p1316 Ns186p1317) 14035277799539321544103 18014398509481984000 16772281018968037 1228800000000000000000 Ns186p1316 Ns186p1317 0 1 Ns186p1319 

noncomputable def Ns186p1321 := nat_lit 941891549051503592155478228992000 

noncomputable abbrev qz517 := (@HSub.hSub Real Real Real qz12 qz169 qz759)

noncomputable abbrev qz518 := (@HMul.hMul Real Real Real qz5 qz759 (Real.log Real.pi))

noncomputable def Ns186p1322 := @Enclosure.Real.IsNear.subLit_ff_p qz517 qz518 18883822851004566805927 18014398509481984000 15941304232451 2400000000000000000 18062237841879 67108864000 470239 67108864000 Ns186p1321 14035277799539321544103 18014398509481984000 

noncomputable def Ns186p1323 := nat_lit 7553529140401826722370800 

noncomputable abbrev qz519 := qz759

noncomputable def Ns186p1324 := @Enclosure.Real.IsNear.subLit_ff_p qz169 qz519 4623871844270943228603 3602879701896396800 15941304232451 2400000000000000000 470239 2000 0 1 Ns186p1323 18883822851004566805927 18014398509481984000 15941304232451 2400000000000000000 

noncomputable def Ns186p1325 := nat_lit 10412033757433774017044826956752748544 

noncomputable def Ns186p1326 := nat_lit 26403396680775579593605120 

noncomputable def Ns186p1327 := nat_lit 8258764522954764412525950918222615062701493373187685588901969974060994827006494764723876288006668051534026477853115742741456336016161898730437014978560 

noncomputable def Ns186p1328 := nat_lit 187384911282599131927901388119336400373249506831073373335825193876350106588135382231066759429060765874641728559408205103550795011259005176887726047232 

noncomputable def Ns186p1329 := nat_lit 49604458278840821677837037449215366459871014197250002255978652549635754738714670916816635930354504872109421523264552769843174769982465764229120 

noncomputable def Ns186p1330 := BSN.log_dyadic_bound 360211868484 1408787868484 7 6 Ns186p1327 67108864 18000000 Ns186p1328 Ns186p1329 35096675 1768999736968 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 360211868484) (BSN.artanhQ 1408787868484) 0 6 Ns186p1328 Ns186p1327 Ns186p1329 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns186p1331 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 470239 4000) qz758 470239 4000 0 1 49180158750667385 4503599627370496 100000027 1800000000000000 4625285734151016091003 3602879701896396800 47023912696453 7200000000000000000 (Enclosure.Real.IsNear.const Bool.false 470239 4000) (BSN.isNear_log_sfrac 884499868484 16000000 49180158750667385 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 884499868484) qz353)) Bool.false Ns186p1326 Ns186p89 1000000270000000 18000000000000000000000 49180158750667385 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 884499868484 16000000 15 1768999736968 1048576000000 35096675 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns186p1330 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p1332 := BSN.arctan_dyadic_bound_f 1000 940478 1 0 8388608 2250000 0 1 1 0 1 1 8919 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 940478) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 940478) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz760 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 940478)))

noncomputable def Ns186p1333 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz760 884279719003555 562949953421312 1 2000000000000000 8919 8388608 1 2250000 7412854974436408819712 883681175045539 562949953421312 8000000009 18000000000000000 qz16 (Ns186p1332 rfl) rfl rfl 

noncomputable def Ns186p1334 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 470239 4000) qz758) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz760)) 4625285734151016091003 3602879701896396800 47023912696453 7200000000000000000 883681175045539 2251799813685248 8000000009 72000000000000000 Ns186p1325 4623871844270943228603 3602879701896396800 15941304232451 2400000000000000000 (Ns186p1331 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz760) 1 4 0 1 883681175045539 562949953421312 8000000009 18000000000000000 883681175045539 2251799813685248 8000000009 72000000000000000 qz356 Ns186p1333 rfl) 

noncomputable def Ns186p1335 := @Ns186p1320 Ns186p1314 Ns186p1315 16772281018968037 1228800000000000000000 (@Ns186p1322 16772281018968037 1228800000000000000000 (Ns186p1324 (Ns186p1334 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 470239 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz519 (Real.log Real.pi) 470239 2000 0 1 38410761 33554432 1 33554432 18062237841879 67108864000 470239 67108864000 (Enclosure.Real.IsNear.const Bool.false 470239 2000) RS187to204.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns186p1316 Ns186p1317) 

noncomputable def Ns186p1336 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz165) Bool.false Ns186p1314 Ns186p1315 16772281018968037 1228800000000000000000 13071365109 16777216 115 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz165) (@HAdd.hAdd Real Real Real qz357 qz516 (Enclosure.sfrac Bool.true Ns186p1316 Ns186p1317)) Bool.false Ns186p1314 Ns186p1315 16772281018968037 1228800000000000000000 Ns186p1318 (Ns186p1335 rfl rfl)) 

noncomputable def Ns186p1337 := nat_lit 3795766641727766368616448 

noncomputable def Ns186p1338 := nat_lit 855162087413388166422850399460311116043166752468071425056000267147630532526847507754478385060176364229279703933589444780920150002569216 

noncomputable def Ns186p1339 := nat_lit 606787255692169505721139401633834906378917524427966645845537755919691032179240842299247828971869266426839370149710671702441660416 

noncomputable def Ns186p1340 := nat_lit 4270509417152286822735035200257459905668762064575641269580895536199774643357475468031092683689337620659071551198997476075316960670846976 

noncomputable def Ns186p1341 := BSN.sin_dyadic_bound_f 53941088278 34359738368 4 3 16777216 4504395 Ns186p1338 Ns186p102 Ns186p1339 Ns186p1340 Ns186p105 Ns186p1339 16777209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53941088278) qz358 0 3 Ns186p1338 Ns186p102 Ns186p1339 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53941088278) qz359 0 3 Ns186p1340 Ns186p105 Ns186p1339 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1342 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz165) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13071365109) qz360) Bool.false 13071365109 16777216 115 8388608 Bool.false 16777209 16777216 1 2250000 (Ns186p1336 rfl) (Enclosure.sfrac_false_div 13071365109 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13071365109) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p1337) qz361) 226375608064910080 72057594037927936 Bool.false 16777209 16777216 123 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q3 13071365109 16777216 226375608064910080 72057594037927936 123 Ns186p1337 Ns186p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777209 16777216 Ns186p1337 Ns186p89 53941088278 34359738368 4504395 4500000 (Ns186p1341 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p1343 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz165) Bool.false Ns186p1314 Ns186p1315 16772281018968037 1228800000000000000000 104570920874 134217728 1833 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz165) (@HAdd.hAdd Real Real Real qz357 qz516 (Enclosure.sfrac Bool.true Ns186p1316 Ns186p1317)) Bool.false Ns186p1314 Ns186p1315 16772281018968037 1228800000000000000000 Ns186p1318 (Ns186p1335 rfl rfl)) 

noncomputable def Ns186p1344 := Ns186p1313 40524 BSN.abs_quadSignPos (BSN.cos_quad_nat0 288 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 95421913 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 167 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 24133281 134217728) qz168 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz165) qz165 1) Bool.false 16777209 16777216 16696163 1179648000000 134217672 134217728 1900 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz165) qz165 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz165)) Bool.false 16777209 16777216 16696163 1179648000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz165) qz165) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz165)) Bool.false 16777209 16777216 267138608 18874368000000 16777209 16777216 16696163 1179648000000 (Ns186p1342 rfl rfl) rfl)) rfl) (Ns186p1343 rfl) RS187to204.d7 

noncomputable def Ns186p1345 := nat_lit 65486412133859476757268446060068272201426376323990306570289700659456 

noncomputable def Ns186p1346 := nat_lit 14421600571318083976838056646489181698424080343742865629058949376 

noncomputable def Ns186p1347 := nat_lit 196430393200435794103851662066911838240882280811283433979610984079616 

noncomputable def Ns186p1348 := BSN.cos_dyadic_bound_f 104683126 134217728 3 2 134217728 67108864 Ns186p1345 Ns186p117 Ns186p1346 Ns186p1347 Ns186p120 Ns186p1346 95421913 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 104683126) qz364 0 2 Ns186p1345 Ns186p117 Ns186p1346 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 104683126) qz365 0 2 Ns186p1347 Ns186p120 Ns186p1346 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1349 := nat_lit 346688273420907261129461186001 

noncomputable def Ns186p1350 := BSN.sin_dyadic_bound_f 24265251 134217728 2 1 134217728 67108864 Ns186p1349 Ns186p123 Ns186p1349 Ns186p1349 Ns186p124 Ns186p1349 24133281 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 24265251) qz362 0 1 Ns186p1349 Ns186p123 Ns186p1349 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 24265251) qz363 0 1 Ns186p1349 Ns186p124 Ns186p1349 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1351 := nat_lit 4061697534221644642862019692685348782711288122301780541957488564352035540045026739769887197644815116890625 

noncomputable def Ns186p1352 := nat_lit 7140233262254966279256838110379064561575700392927769938841299377603341287778630424003649043212890625 

noncomputable def Ns186p1353 := nat_lit 24583111744858264918401819143334301195159304292554947515196947092782527910368135430263307394651198630490625 

noncomputable def Ns186p1354 := BSN.cos_dyadic_bound_f 209480065 134217728 4 3 134217728 67108864 Ns186p1351 Ns186p127 Ns186p1352 Ns186p1353 Ns186p130 Ns186p1352 1348626 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 209480065) qz364 0 3 Ns186p1351 Ns186p127 Ns186p1352 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 209480065) qz365 0 3 Ns186p1353 Ns186p130 Ns186p1352 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1355 := nat_lit 2717066597250350177610465610000 

noncomputable def Ns186p1356 := BSN.cos_dyadic_bound_f 40599910 134217728 2 1 134217728 67108864 Ns186p1355 Ns186p134 Ns186p1355 Ns186p1355 Ns186p135 Ns186p1355 128123815 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 40599910) qz364 0 1 Ns186p1355 Ns186p134 Ns186p1355 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 40599910) qz365 0 1 Ns186p1355 Ns186p135 Ns186p1355 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1357 := Ns186p1311 69006 BSN.abs_quadSignPos (BSN.cos_quad_nat0 80 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 1348626 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 14 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 128123815 134217728) qz168 rfl rfl (Ns186p1344 RS187to204.d9 RS187to204.d11 RS187to204.d13 RS187to204.d17 (Ns186p1348 rfl rfl) (Ns186p1350 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns186p1343 rfl) RS187to204.d19 RS187to204.d21 RS187to204.d23 RS187to204.d25 RS187to204.d17 (Ns186p1354 rfl rfl) (Ns186p1356 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns186p1358 := nat_lit 24371179845994302275144622018798020447169509740328025962880021935841 

noncomputable def Ns186p1359 := nat_lit 1997948421580294580739328252154220578483550446744794421659547361 

noncomputable def Ns186p1360 := nat_lit 73109543641139746236272387399889752900351562120090588299796746712801 

noncomputable def Ns186p1361 := BSN.cos_dyadic_bound_f 81766053 134217728 3 2 134217728 67108864 Ns186p1358 Ns186p117 Ns186p1359 Ns186p1360 Ns186p120 Ns186p1359 110072419 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 81766053) qz364 0 2 Ns186p1358 Ns186p117 Ns186p1359 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 81766053) qz365 0 2 Ns186p1360 Ns186p120 Ns186p1359 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1362 := nat_lit 88219328827276693160191214845464910851649496281759309793484441911296 

noncomputable def Ns186p1363 := nat_lit 26168099833127327789011643620526915993897245885779475190687727616 

noncomputable def Ns186p1364 := nat_lit 264605650282163824824995621249153678722960694353506370430071950278656 

noncomputable def Ns186p1365 := BSN.cos_dyadic_bound_f 112777256 134217728 3 2 134217728 67108864 Ns186p1362 Ns186p117 Ns186p1363 Ns186p1364 Ns186p120 Ns186p1363 89559751 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 112777256) qz364 0 2 Ns186p1362 Ns186p117 Ns186p1363 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 112777256) qz365 0 2 Ns186p1364 Ns186p120 Ns186p1363 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1366 := Ns186p1309 93019 BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 110072419 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 86 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 89559751 134217728) qz168 rfl rfl (Ns186p1357 rfl rfl) (Ns186p1343 rfl) RS187to204.d27 RS187to204.d29 RS187to204.d31 RS187to204.d33 RS187to204.d17 (Ns186p1361 rfl rfl) (Ns186p1365 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns186p1367 := nat_lit 72521920132434328818979567856689218891338047053367437092365373182561 

noncomputable def Ns186p1368 := nat_lit 17685979293737911218430792892940231206587298985135982451168285281 

noncomputable def Ns186p1369 := nat_lit 217530388438715510634501841984281776211600966562132039312193782977121 

noncomputable def Ns186p1370 := BSN.cos_dyadic_bound_f 107387477 134217728 3 2 134217728 67108864 Ns186p1367 Ns186p117 Ns186p1368 Ns186p1369 Ns186p120 Ns186p1368 93500854 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 107387477) qz364 0 2 Ns186p1367 Ns186p117 Ns186p1368 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 107387477) qz365 0 2 Ns186p1369 Ns186p120 Ns186p1368 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1371 := Ns186p1307 Bool.false 170086580 93019 Bool.true 107387477 7074237752028440 1 Bool.false 93500854 Bool.true Bool.false 137029039 103653 BSN.abs_quadSignNeg qz431 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 93500854 134217728) qz168 rfl (Ns186p1366 rfl) (Ns186p1343 rfl) RS187to204.d35 RS187to204.d37 RS187to204.d17 (Ns186p1370 rfl rfl) rfl 

noncomputable def Ns186p1372 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz165) qz165 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz165) qz165 8) 137029039 134217728 103653 134217728 137029039 134217728 103653 134217728 36783452569206784 137029039 67108864 103653 67108864 (Ns186p1371 rfl rfl rfl rfl) 

noncomputable def Ns186p1373 := @Enclosure.Real.IsNear.mulLit_ff qz756 (Zeta.RiemannSiegel.correction qz167) 2852037 8388608 1 8388608 59628473880873 140737488355328 996138102675103 19791209299968000000 170062613761783388301 1180591620717411303424 

noncomputable abbrev qz761 := (@HPow.hPow Real Real Real qz7 qz166 qz9)

noncomputable def Ns186p1374 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz761 1 1 0 1 2852037 8388608 1 8388608 2852037 8388608 1 8388608 

noncomputable def Ns186p1375 := @Enclosure.Real.IsNear.sqrt_image qz166 1255621362303 16777216000 470239 16777216000 72570350 72570378 8388608 (@Enclosure.Real.IsNear.of_eq qz166 (@HMul.hMul Real Real Real qz5 qz165 qz3) Bool.false 1255621362303 16777216000 470239 16777216000 (BSN.t_div_two_pi_mk qz165 470239 1000 qz168) (@Enclosure.Real.IsNear.mulLit_ff qz165 qz3 470239 1000 0 1 2670177 16777216 1 16777216 1255621362303 16777216000 470239 16777216000 (Enclosure.Real.IsNear.const Bool.false 470239 1000) RS187to204.d40 rfl)) 

noncomputable abbrev qz941 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 470239 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz762 := qz941

noncomputable abbrev qz520 := qz762

noncomputable abbrev qz170 := qz520

noncomputable def Ns186p1376 := @Enclosure.Real.IsNear.sqrt_image qz170 18142591 2097152 7 4194304 24673147 24673153 8388608 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 145140728 16777216 28 16777216 18142591 2097152 7 4194304 (Ns186p1375 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns186p1377 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz170) 12336575 4194304 3 8388608 2852036 2852038 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz170) Bool.false 49346300 16777216 6 16777216 12336575 4194304 3 8388608 (Ns186p1376 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns186p1378 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz170)) Bool.false 5704074 16777216 2 16777216 2852037 8388608 1 8388608 (Ns186p1377 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz171 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz514))

noncomputable abbrev qz763 := (@HMul.hMul Real Real Real qz891 qz940 qz940)

noncomputable abbrev qz521 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz763 qz755) qz640)

noncomputable abbrev qz172 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz521))

noncomputable def Ns186p1379 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz167) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz171) qz172) Bool.false 59628473880873 

noncomputable def Ns186p1380 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz171) qz172 28808211 16777216 545 

noncomputable abbrev qz764 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz171))

noncomputable def Ns186p1381 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz171) (@Neg.neg Real Real.instNeg qz764) Bool.true 28808211 16777216 545 16777216 (BSN.inv_eq_neg_inv_neg qz171) 

noncomputable def Ns186p1382 := @Enclosure.Real.IsNear.recentre' qz764 Bool.false 28808211 16777216 545 16777216 28808211 16777216 

noncomputable def Ns186p1383 := @Enclosure.Real.IsNear.recentre' qz171 Bool.true 9770651 16777216 415027216 37748736000000 9770651 16777216 25939201 2359296000000 

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz342 qz340 qz514)

noncomputable def Ns186p1384 := @Enclosure.Real.IsNear.cos_image qz173 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 68631233) qz360) Bool.false 68631233 16777216 177 16777216 Bool.true 9770651 16777216 1 

noncomputable def Ns186p1385 := nat_lit 188902527886765282073286769 

noncomputable def Ns186p1386 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz167 884279719003555 140737488355328 1 500000000000000 1365375 2097152 7 4194304 1207373421334478908125 295147905179352825856 Ns186p1385 

noncomputable def Ns186p1387 := @Enclosure.Real.IsNear.subLit_ff_p qz170 qz1 18142591 2097152 7 4194304 8 1 0 1 1365375 1365375 2097152 7 

noncomputable def Ns186p1388 := @Ns186p1387 4194304 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 145140728 16777216 28 16777216 18142591 2097152 7 4194304 (Ns186p1375 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns186p1389 := @Enclosure.Real.IsNear.recentre' qz173 Bool.false 1207373421334478908125 295147905179352825856 Ns186p1385 Ns186p159 68631233 16777216 177 16777216 (@Ns186p1386 Ns186p159 RS187to204.d39 (Ns186p1388 rfl rfl) rfl) 

noncomputable def Ns186p1390 := nat_lit 2294898104400209160175616 

noncomputable def Ns186p1391 := nat_lit 2650042585033775394048672845707090202883808968151720828749806742065092095581831021391841 

noncomputable def Ns186p1392 := nat_lit 1279584154278035215409638304288841910092800153224095157653257279732107502066498465761 

noncomputable def Ns186p1393 := nat_lit 7947568586792770111715199260512692924831241304148714295934113711635812071741360067244001 

noncomputable def Ns186p1394 := BSN.cos_dyadic_bound_f 32612463547 34359738368 3 2 16777216 4504395 Ns186p1391 Ns186p851 Ns186p1392 Ns186p1393 Ns186p854 Ns186p1392 9770651 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 32612463547) qz371 0 2 Ns186p1391 Ns186p851 Ns186p1392 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 32612463547) qz372 0 2 Ns186p1393 Ns186p854 Ns186p1392 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1395 := @Ns186p1384 2250000 (Ns186p1389 rfl) (Enclosure.sfrac_false_div 68631233 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 68631233) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p1390) qz361) 226375608064910080 72057594037927936 Bool.false 9770651 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 68631233 16777216 226375608064910080 72057594037927936 0 Ns186p1390 Ns186p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 9770651 16777216 Ns186p1390 Ns186p89 32612463547 34359738368 4504395 4500000 (Ns186p1394 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p1396 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz171) 9770651 16777216 25939201 2359296000000 14403833 14404378 8388608 (@Enclosure.Real.IsNear.neg qz171 Bool.true 9770651 16777216 25939201 2359296000000 (Ns186p1383 (Ns186p1395 rfl rfl) rfl)) 

noncomputable def Ns186p1397 := Ns186p1381 (@Enclosure.Real.IsNear.neg qz764 Bool.false 28808211 16777216 545 16777216 (@Ns186p1382 545 16777216 (Ns186p1396 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p1398 := @Enclosure.Real.IsNear.recentre' qz172 Bool.true 2069843 8388608 

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz342 qz340 qz521)

noncomputable def Ns186p1399 := @Enclosure.Real.IsNear.cos_image qz174 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15268237)) qz429) Bool.true 15268237 8388608 

noncomputable def Ns186p1400 := nat_lit 1126597058456606631646174045 

noncomputable def Ns186p1401 := nat_lit 618970019642690137449562112 

noncomputable def Ns186p1402 := nat_lit 1824007106514114221424209526964051 

noncomputable def Ns186p1403 := @Enclosure.Real.IsNear.recentre' qz174 Bool.true Ns186p1400 Ns186p1401 Ns186p1402 

noncomputable abbrev qz175 := qz521

noncomputable def Ns186p1404 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz175 884279719003555 140737488355328 1 500000000000000 1274027928319 

noncomputable abbrev qz522 := (@HSub.hSub Real Real Real qz633 qz763 qz755)

noncomputable abbrev qz176 := qz522

noncomputable def Ns186p1405 := @Enclosure.Real.IsNear.subLit_tf qz176 qz26 999150021375 4398046511104 67590677 17592186044416 1 16 

noncomputable abbrev qz523 := qz763

noncomputable abbrev qz177 := qz523

noncomputable def Ns186p1406 := @Enclosure.Real.IsNear.subLit_ff_n qz177 qz167 1864248890625 4398046511104 38230549 17592186044416 1365375 2097152 7 4194304 

noncomputable def Ns186p1407 := @Enclosure.Real.IsNear.mulLit_ff qz167 qz167 1365375 2097152 7 4194304 1365375 2097152 7 4194304 1864248890625 4398046511104 

noncomputable def Ns186p1408 := nat_lit 26768926086425072039505414996030356418557080892031318225331297698470968103210374083894102961 

noncomputable def Ns186p1409 := nat_lit 160496923339632221603645157949213982021038174473404897395396681435063780125135875394481 

noncomputable def Ns186p1410 := nat_lit 161694677070751303526318732405725739242430567829311109904126200380319455608555115802845563825 

noncomputable def Ns186p1411 := BSN.cos_dyadic_bound_t 15268237 8388608 4 3 8388608 2250000 Ns186p1408 Ns186p754 Ns186p1409 Ns186p1410 Ns186p757 Ns186p1409 2069843 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 15268237) (BSN.cosEvenQ 8388608) 0 3 Ns186p1408 Ns186p754 Ns186p1409 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 15268237) (BSN.cosOddQ 8388608) 0 3 Ns186p1410 Ns186p757 Ns186p1409 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1412 := @Ns186p1398 465138608 18874368000000 2069843 8388608 29071163 1179648000000 (@Ns186p1399 203 8388608 Bool.true 2069843 8388608 1 2250000 (@Ns186p1403 Ns186p972 15268237 8388608 203 8388608 (@Ns186p1404 4398046511104 67590677 17592186044416 Ns186p1400 Ns186p1401 Ns186p1402 Ns186p972 RS187to204.d39 (@Ns186p1405 0 1 20384446853104 1274027928319 4398046511104 67590677 17592186044416 (@Ns186p1406 2095369465626624000 999150021375 4398046511104 67590677 17592186044416 (@Ns186p1407 38230549 17592186044416 (Ns186p1388 rfl rfl) (Ns186p1388 rfl rfl) rfl) (Ns186p1388 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 15268237 8388608) (BSN.cos_neg_of_bound 15268237 8388608 Bool.true 2069843 8388608 1 2250000 (Ns186p1411 rfl rfl)) rfl rfl) 

noncomputable def Ns186p1413 := @Ns186p1373 2849408976216793175539 Ns186p1304 (Ns186p1374 qz28 (@Enclosure.Real.IsNear.of_eq qz761 (@Inv.inv Real Real.instInv (Real.sqrt qz170)) Bool.false 2852037 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz166 (BSN.t_div_two_pi_nonneg qz165 470239 1000 qz168)) Ns186p1378) rfl) (@Ns186p1379 140737488355328 996138102675103 19791209299968000000 (BSN.correction_mk qz167 (BSN.cos_two_pi_p_ne_zero_mk qz165 470239 1000 8 qz168 rfl rfl (@BSN.floor_sqrt_eq_dec qz165 470239 1000 8 qz168 rfl rfl rfl))) (@Ns186p1380 16777216 2069843 8388608 29071163 1179648000000 59628473880873 140737488355328 996138102675103 19791209299968000000 Ns186p1397 (Ns186p1412 rfl) rfl)) 

noncomputable def Ns186p1414 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz165) (hardyZApproximantRS₀ qz165) Bool.false 2240577733813752407923 1180591620717411303424 259276686172414681175539 Ns186p1304 (@Eq.refl Real (hardyZApproximantRS₀ qz165)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz165) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz165) qz165 8) (@HMul.hMul Real Real Real qz5 qz756 (Zeta.RiemannSiegel.correction qz167))) Bool.false 2240577733813752407923 1180591620717411303424 259276686172414681175539 Ns186p1304 (BSN.hardyZApproximantRS₀_eq qz165 8 (@BSN.floor_sqrt_eq_dec qz165 470239 1000 8 qz168 rfl rfl rfl)) (@Ns186p1306 2240577733813752407923 1180591620717411303424 259276686172414681175539 Ns186p1304 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz165) qz165 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz165) qz165 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz165) qz165 8)) Bool.false 137029039 67108864 103653 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz165) qz165 8) (Ns186p1372 (Ns186p1371 rfl rfl rfl rfl) rfl rfl)) (Ns186p1413 rfl) rfl rfl)) 

theorem RS187to204.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz165) Bool.false 2240577733813752407923 1180591620717411303424 259276686172414681175539 Ns186p1304 := Ns186p1414 

noncomputable def Ns186p1415 := nat_lit 20153995602833446037069234176 

noncomputable abbrev qz942 := (Enclosure.sfrac Bool.false 471695 1000)

noncomputable abbrev qz765 := qz942

noncomputable abbrev qz524 := qz765

noncomputable abbrev qz178 := qz524

noncomputable abbrev qz943 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 471695 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz766 := qz943

noncomputable abbrev qz525 := qz766

noncomputable abbrev qz179 := qz525

noncomputable abbrev qz944 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 471695 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz767 := qz944

noncomputable abbrev qz526 := qz767

noncomputable abbrev qz180 := qz526

noncomputable abbrev qz768 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz179 qz9))

noncomputable def Ns186p1416 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz178) qz178 8) (@HMul.hMul Real Real Real qz5 qz768 (Zeta.RiemannSiegel.correction qz180)) 65824937 16777216 103977 67108864 43267210645709787269 295147905179352825856 2272445355627563449 115292150460684697600000 Ns186p1415 

noncomputable def Ns186p1417 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz178) qz178 Real.cos BSN.quadSignNeg 7 8 471695 1000 126 134217728 67108864 2251799813685248 Bool.false 104992728242 1839 279097919 60 47453128 8 

noncomputable def Ns186p1418 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz178) qz178 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 471695 1000 40 86 134217728 67108864 2251799813685248 Bool.false 104992728242 1839 

noncomputable def Ns186p1419 := Ns186p1418 240485871 61 54794152 8 261175631 61 50729528 8 Bool.true 237442235 69222 Bool.true 10106114 Bool.true 71241607 7074237752028440 1 Bool.false 133837430 Bool.false Bool.false 115750275 Bool.true Bool.true 226552827 

noncomputable def Ns186p1420 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz178) qz178 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 471695 1000 81 14 134217728 67108864 2251799813685248 Bool.false 104992728242 1839 

noncomputable def Ns186p1421 := Ns186p1420 186065264 60 67108856 8 216015088 60 60023992 8 Bool.true 150080574 40652 Bool.false 149547694 Bool.false 147889309 7074237752028440 1 Bool.false 120469258 Bool.true Bool.false 60657904 Bool.true Bool.true 237442235 

noncomputable def Ns186p1422 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz178) qz178 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 471695 1000 289 168 134217728 67108864 2251799813685248 Bool.false 104992728242 1839 

noncomputable def Ns186p1423 := Ns186p1422 93032624 60 94906264 8 147453232 60 77490640 16 Bool.true 134217720 1908 Bool.false 180206279 Bool.false 20551999 7074237752028440 1 Bool.false 130739525 Bool.true Bool.false 132647294 Bool.false Bool.true 150080574 

noncomputable def Ns186p1424 := nat_lit 17880953891686128145897335060052410653959979001304987 

noncomputable def Ns186p1425 := nat_lit 22858164046080480087527362060187115103068566323200 

noncomputable def Ns186p1426 := nat_lit 11208534609970380824455548500000000 

noncomputable def Ns186p1427 := nat_lit 31722075030771845882037410308245000000 

noncomputable abbrev qz527 := (@Eq.refl Real qz765)

noncomputable abbrev qz181 := qz527

noncomputable def Ns186p1428 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz178 471695 1000 889985692100 16000000 943390 4000 2000 Ns186p1426 Ns186p1427 qz181 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns186p1429 := nat_lit 89404769458430640729486675300262053269799895006524935000000 

noncomputable abbrev qz769 := (Real.log (Enclosure.sfrac Bool.false 889985692100 16000000))

noncomputable abbrev qz182 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 471695 4000) qz769) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 943390))))))

noncomputable abbrev qz770 := (Enclosure.sfrac Bool.false 471695 2000)

noncomputable abbrev qz528 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz182 qz770) (@HMul.hMul Real Real Real qz5 qz770 (Real.log Real.pi)))

noncomputable def Ns186p1430 := @Enclosure.Real.IsNear.addLit_ft_p qz528 (Enclosure.sfrac Bool.true Ns186p1426 Ns186p1427) 2818378361273837553963 3602879701896396800 10094274149156371 737280000000000000000 Ns186p1426 Ns186p1427 0 1 Ns186p1429 

noncomputable def Ns186p1431 := nat_lit 37827634029453766233399125606400 

noncomputable abbrev qz529 := (@HSub.hSub Real Real Real qz12 qz182 qz770)

noncomputable abbrev qz530 := (@HMul.hMul Real Real Real qz5 qz770 (Real.log Real.pi))

noncomputable def Ns186p1432 := @Enclosure.Real.IsNear.subLit_ff_p qz529 qz530 3791089879480919001387 3602879701896396800 9593902547333 1440000000000000000 3623632781979 13421772800 94339 13421772800 Ns186p1431 2818378361273837553963 3602879701896396800 

noncomputable abbrev qz531 := qz770

noncomputable def Ns186p1433 := @Enclosure.Real.IsNear.subLit_ff_p qz182 qz531 185632801998957177827 144115188075855872 9593902547333 1440000000000000000 471695 2000 0 1 303287190358473520110960 3791089879480919001387 3602879701896396800 9593902547333 1440000000000000000 

noncomputable def Ns186p1434 := nat_lit 418007908955122305530027754542596096 

noncomputable def Ns186p1435 := nat_lit 26418346289666643407667200 

noncomputable def Ns186p1436 := nat_lit 8653053720844049652888108679923828405007524565445455059166180492524116741805471928660624998302528478192246628233734986777769535000000000000000000000000 

noncomputable def Ns186p1437 := nat_lit 200979163921492370421477644970067731280155282847372968617847046269545462344510679100814671624948702848445713887370538161800752000000000000000000000000 

noncomputable def Ns186p1438 := nat_lit 59469067426614411119110417226464954769114106829337806417609397057921228748543547462362191109837690747457166759638659195000000000000000000000000 

noncomputable def Ns186p1439 := BSN.log_dyadic_bound 365697692100 1414273692100 7 6 Ns186p1436 67108864 18000000 Ns186p1437 Ns186p1438 35511610 1779971384200 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 365697692100) (BSN.artanhQ 1414273692100) 0 6 Ns186p1437 Ns186p1436 Ns186p1438 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns186p1440 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 471695 4000) qz769 471695 4000 0 1 49208004567151225 4503599627370496 100000027 1800000000000000 185689357714419176611 144115188075855872 9433902547153 1440000000000000000 (Enclosure.Real.IsNear.const Bool.false 471695 4000) (BSN.isNear_log_sfrac 889985692100 16000000 49208004567151225 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 889985692100) qz353)) Bool.false Ns186p1435 Ns186p89 1000000270000000 18000000000000000000000 49208004567151225 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 889985692100 16000000 15 1779971384200 1048576000000 35511610 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns186p1439 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p1441 := BSN.arctan_dyadic_bound_f 1000 943390 1 0 8388608 2250000 0 1 1 0 1 1 8891 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 943390) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 943390) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz771 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 943390)))

noncomputable def Ns186p1442 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz771 884279719003555 562949953421312 1 2000000000000000 8891 8388608 1 2250000 7412870737035104616448 883683054093731 562949953421312 8000000009 18000000000000000 qz16 (Ns186p1441 rfl) rfl rfl 

noncomputable def Ns186p1443 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 471695 4000) qz769) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz771)) 185689357714419176611 144115188075855872 9433902547153 1440000000000000000 883683054093731 2251799813685248 8000000009 72000000000000000 Ns186p1434 185632801998957177827 144115188075855872 9593902547333 1440000000000000000 (Ns186p1440 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz771) 1 4 0 1 883683054093731 562949953421312 8000000009 18000000000000000 883683054093731 2251799813685248 8000000009 72000000000000000 qz356 Ns186p1442 rfl) 

noncomputable def Ns186p1444 := @Ns186p1430 Ns186p1424 Ns186p1425 10094274149156371 737280000000000000000 (@Ns186p1432 10094274149156371 737280000000000000000 (Ns186p1433 (Ns186p1443 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 471695 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz531 (Real.log Real.pi) 471695 2000 0 1 38410761 33554432 1 33554432 3623632781979 13421772800 94339 13421772800 (Enclosure.Real.IsNear.const Bool.false 471695 2000) RS187to204.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns186p1426 Ns186p1427) 

noncomputable def Ns186p1445 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz178) Bool.false Ns186p1424 Ns186p1425 10094274149156371 737280000000000000000 6562045515 8388608 231 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz178) (@HAdd.hAdd Real Real Real qz357 qz528 (Enclosure.sfrac Bool.true Ns186p1426 Ns186p1427)) Bool.false Ns186p1424 Ns186p1425 10094274149156371 737280000000000000000 Ns186p1428 (Ns186p1444 rfl rfl)) 

noncomputable def Ns186p1446 := nat_lit 1899233857921404108800000 

noncomputable def Ns186p1447 := nat_lit 857603728209878478951244218266732259658508107255283676000207247312828312321884470834763643249747733969281725262464605703365224000000000 

noncomputable def Ns186p1448 := nat_lit 611989073604737247137584921365699061376243935667925383458925060963708163037666404868437205105595124767030859619140625000000000000 

noncomputable def Ns186p1449 := nat_lit 4282687361191617246656374070139627524057057121560839126650178400650205846817690103531051435140292147499868821439929313554326120000000000 

noncomputable def Ns186p1450 := BSN.sin_dyadic_bound_f 53979472850 34359738368 4 3 16777216 4504395 Ns186p1447 Ns186p102 Ns186p1448 Ns186p1449 Ns186p105 Ns186p1448 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53979472850) qz358 0 3 Ns186p1447 Ns186p102 Ns186p1448 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53979472850) qz359 0 3 Ns186p1449 Ns186p105 Ns186p1448 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1451 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz178) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6562045515) qz429) Bool.false 6562045515 8388608 231 16777216 Bool.true 16777215 16777216 1 2250000 (Ns186p1445 rfl) (Enclosure.sfrac_false_div 6562045515 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6562045515) qz429) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p1446) qz430) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 124 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 6562045515 8388608 226375608064910080 72057594037927936 124 Ns186p1446 Ns186p578 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns186p1446 Ns186p578 53979472850 34359738368 4504395 4500000 (Ns186p1450 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p1452 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz178) Bool.false Ns186p1424 Ns186p1425 10094274149156371 737280000000000000000 104992728242 134217728 1839 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz178) (@HAdd.hAdd Real Real Real qz357 qz528 (Enclosure.sfrac Bool.true Ns186p1426 Ns186p1427)) Bool.false Ns186p1424 Ns186p1425 10094274149156371 737280000000000000000 Ns186p1428 (Ns186p1444 rfl rfl)) 

noncomputable def Ns186p1453 := Ns186p1423 40652 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 289 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 130739525 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 168 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 132647294 134217728) qz181 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 1) Bool.true 16777215 16777216 33532951 2359296000000 134217720 134217728 1908 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz178)) Bool.true 16777215 16777216 33532951 2359296000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz178) qz178) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz178)) Bool.true 16777215 16777216 536527216 37748736000000 16777215 16777216 33532951 2359296000000 (Ns186p1451 rfl rfl) rfl)) rfl) (Ns186p1452 rfl) RS187to204.d7 

noncomputable def Ns186p1454 := nat_lit 5769316351983196457525830172569280647250815106631458367354322854663923891238841043483658669748927894667041 

noncomputable def Ns186p1455 := nat_lit 1172840705336057828941237399827310119939799406491053346118942912924175470723322205829898244756619041 

noncomputable def Ns186p1456 := nat_lit 28827434403484290606529673896247820094362571155613668907012940280076591946687872751157514798250733229850401 

noncomputable def Ns186p1457 := BSN.sin_dyadic_bound_f 180206279 134217728 4 3 134217728 67108864 Ns186p1454 Ns186p237 Ns186p1455 Ns186p1456 Ns186p240 Ns186p1455 130739525 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 180206279) qz362 0 3 Ns186p1454 Ns186p237 Ns186p1455 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 180206279) qz363 0 3 Ns186p1456 Ns186p240 Ns186p1455 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1458 := nat_lit 178408803449768403876141792001 

noncomputable def Ns186p1459 := BSN.cos_dyadic_bound_f 20551999 134217728 2 1 134217728 67108864 Ns186p1458 Ns186p134 Ns186p1458 Ns186p1458 Ns186p135 Ns186p1458 132647294 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 20551999) qz364 0 1 Ns186p1458 Ns186p134 Ns186p1458 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 20551999) qz365 0 1 Ns186p1458 Ns186p135 Ns186p1458 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1460 := nat_lit 491090458296069696023780550154438309573613054096850796885194919133440 

noncomputable def Ns186p1461 := nat_lit 250171461307785299119026768477740997358616198019737347831320822016 

noncomputable def Ns186p1462 := nat_lit 1285784256028541361006565873731707801554215477361624893279021697351936 

noncomputable def Ns186p1463 := BSN.sin_dyadic_bound_f 149547694 134217728 3 2 134217728 67108864 Ns186p1460 Ns186p111 Ns186p1461 Ns186p1462 Ns186p114 Ns186p1461 120469258 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 149547694) qz362 0 2 Ns186p1460 Ns186p111 Ns186p1461 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 149547694) qz363 0 2 Ns186p1462 Ns186p114 Ns186p1461 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1464 := nat_lit 1006312426205904949092178526609278293250397537992204632054377315034127815109207655839948772276962466978161 

noncomputable def Ns186p1465 := nat_lit 109456449584623860799697366610628278506531277622027308193572985493437394617152207258440674681280881 

noncomputable def Ns186p1466 := nat_lit 6101393627222165729925327220065087770037968517502105689133847342804093308299441195476491700907302910417265 

noncomputable def Ns186p1467 := BSN.cos_dyadic_bound_f 147889309 134217728 4 3 134217728 67108864 Ns186p1464 Ns186p127 Ns186p1465 Ns186p1466 Ns186p130 Ns186p1465 60657904 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 147889309) qz364 0 3 Ns186p1464 Ns186p127 Ns186p1465 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 147889309) qz365 0 3 Ns186p1466 Ns186p130 Ns186p1465 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1468 := Ns186p1421 69222 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 81 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 120469258 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 14 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 60657904 134217728) qz181 rfl rfl (Ns186p1453 RS187to204.d9 RS187to204.d11 RS187to204.d13 RS187to204.d17 (Ns186p1457 rfl rfl) (Ns186p1459 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns186p1452 rfl) RS187to204.d19 RS187to204.d21 RS187to204.d23 RS187to204.d25 RS187to204.d17 (Ns186p1463 rfl rfl) (Ns186p1467 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns186p1469 := nat_lit 10431260029903124444439552016 

noncomputable def Ns186p1470 := BSN.cos_dyadic_bound_f 10106114 134217728 2 1 134217728 67108864 Ns186p1469 Ns186p134 Ns186p1469 Ns186p1469 Ns186p135 Ns186p1469 133837430 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 10106114) qz364 0 1 Ns186p1469 Ns186p134 Ns186p1469 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 10106114) qz365 0 1 Ns186p1469 Ns186p135 Ns186p1469 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1471 := nat_lit 14044431422245703520221418404101333029269794939394775858790175513281 

noncomputable def Ns186p1472 := nat_lit 663543895991836282226867611839587122961470678665140635781995201 

noncomputable def Ns186p1473 := nat_lit 42131967178945126888099801477080319913563461876826997295098962549441 

noncomputable def Ns186p1474 := BSN.cos_dyadic_bound_f 71241607 134217728 3 2 134217728 67108864 Ns186p1471 Ns186p117 Ns186p1472 Ns186p1473 Ns186p120 Ns186p1472 115750275 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 71241607) qz364 0 2 Ns186p1471 Ns186p117 Ns186p1472 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 71241607) qz365 0 2 Ns186p1473 Ns186p120 Ns186p1472 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1475 := Ns186p1419 93310 BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133837430 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 86 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 115750275 134217728) qz181 rfl rfl (Ns186p1468 rfl rfl) (Ns186p1452 rfl) RS187to204.d27 RS187to204.d29 RS187to204.d31 RS187to204.d33 RS187to204.d17 (Ns186p1470 rfl rfl) (Ns186p1474 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns186p1476 := nat_lit 38971752471281962609871619892147799216525153381954401381835467346241 

noncomputable def Ns186p1477 := nat_lit 5108440995038061117644844119280649432882484718190638726528061761 

noncomputable def Ns186p1478 := nat_lit 116905040531855811707379569988204836350709695176426822868053345915201 

noncomputable def Ns186p1479 := BSN.cos_dyadic_bound_f 91946679 134217728 3 2 134217728 67108864 Ns186p1476 Ns186p117 Ns186p1477 Ns186p1478 Ns186p120 Ns186p1477 103935997 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 91946679) qz364 0 2 Ns186p1476 Ns186p117 Ns186p1477 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 91946679) qz365 0 2 Ns186p1478 Ns186p120 Ns186p1477 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1480 := Ns186p1417 Bool.true 226552827 93310 Bool.true 91946679 7074237752028440 1 Bool.false 103935997 Bool.true Bool.true 263299748 103977 BSN.abs_quadSignNeg qz431 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 103935997 134217728) qz181 rfl (Ns186p1475 rfl) (Ns186p1452 rfl) RS187to204.d35 RS187to204.d37 RS187to204.d17 (Ns186p1479 rfl rfl) rfl 

noncomputable def Ns186p1481 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 8) 263299748 134217728 103977 134217728 263299748 134217728 103977 134217728 70678987919065088 65824937 16777216 103977 67108864 (Ns186p1480 rfl rfl rfl rfl) 

noncomputable def Ns186p1482 := @Enclosure.Real.IsNear.mulLit_ff qz768 (Zeta.RiemannSiegel.correction qz180) 1424917 4194304 1 8388608 30364723451057 70368744177664 63625150103877 1099511627776000000 43267210645709787269 295147905179352825856 

noncomputable abbrev qz772 := (@HPow.hPow Real Real Real qz7 qz179 qz9)

noncomputable def Ns186p1483 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz772 1 1 0 1 1424917 4194304 1 8388608 1424917 4194304 1 8388608 

noncomputable def Ns186p1484 := @Enclosure.Real.IsNear.sqrt_image qz179 251901828003 3355443200 94339 3355443200 72682613 72682641 8388608 (@Enclosure.Real.IsNear.of_eq qz179 (@HMul.hMul Real Real Real qz5 qz178 qz3) Bool.false 251901828003 3355443200 94339 3355443200 (BSN.t_div_two_pi_mk qz178 471695 1000 qz181) (@Enclosure.Real.IsNear.mulLit_ff qz178 qz3 471695 1000 0 1 2670177 16777216 1 16777216 251901828003 3355443200 94339 3355443200 (Enclosure.Real.IsNear.const Bool.false 471695 1000) RS187to204.d40 rfl)) 

noncomputable abbrev qz945 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 471695 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz773 := qz945

noncomputable abbrev qz532 := qz773

noncomputable abbrev qz183 := qz532

noncomputable def Ns186p1485 := @Enclosure.Real.IsNear.sqrt_image qz183 72682627 8388608 7 4194304 24692224 24692230 8388608 (@Enclosure.Real.IsNear.recentre' qz183 Bool.false 145365254 16777216 28 16777216 72682627 8388608 7 4194304 (Ns186p1484 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns186p1486 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz183) 24692227 8388608 3 8388608 2849833 2849835 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz183) Bool.false 49384454 16777216 6 16777216 24692227 8388608 3 8388608 (Ns186p1485 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns186p1487 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz183)) Bool.false 5699668 16777216 2 16777216 1424917 4194304 1 8388608 (Ns186p1486 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz184 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz526))

noncomputable abbrev qz774 := (@HMul.hMul Real Real Real qz891 qz944 qz944)

noncomputable abbrev qz533 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz774 qz767) qz640)

noncomputable abbrev qz185 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz533))

noncomputable def Ns186p1488 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz180) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz184) qz185) Bool.false 30364723451057 

noncomputable def Ns186p1489 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz184) qz185 16382609 8388608 11 

noncomputable abbrev qz775 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz184))

noncomputable def Ns186p1490 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz184) (@Neg.neg Real Real.instNeg qz775) Bool.true 16382609 8388608 11 262144 (BSN.inv_eq_neg_inv_neg qz184) 

noncomputable def Ns186p1491 := @Enclosure.Real.IsNear.recentre' qz775 Bool.false 32765218 16777216 704 16777216 16382609 8388608 

noncomputable def Ns186p1492 := @Enclosure.Real.IsNear.recentre' qz184 Bool.true 8590664 16777216 415027216 37748736000000 1073833 2097152 25939201 2359296000000 

noncomputable abbrev qz186 := (@HMul.hMul Real Real Real qz342 qz340 qz526)

noncomputable def Ns186p1493 := @Enclosure.Real.IsNear.cos_image qz186 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 70041971) qz360) Bool.false 70041971 16777216 177 16777216 Bool.true 8590664 16777216 1 

noncomputable def Ns186p1494 := nat_lit 188902527887247447986837617 

noncomputable def Ns186p1495 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz180 884279719003555 140737488355328 1 500000000000000 5573763 8388608 7 4194304 4928765579432411727465 1180591620717411303424 Ns186p1494 

noncomputable def Ns186p1496 := @Enclosure.Real.IsNear.subLit_ff_p qz183 qz1 72682627 8388608 7 4194304 8 1 0 1 5573763 5573763 8388608 7 

noncomputable def Ns186p1497 := @Ns186p1496 4194304 (@Enclosure.Real.IsNear.recentre' qz183 Bool.false 145365254 16777216 28 16777216 72682627 8388608 7 4194304 (Ns186p1484 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns186p1498 := @Enclosure.Real.IsNear.recentre' qz186 Bool.false 4928765579432411727465 1180591620717411303424 Ns186p1494 Ns186p159 70041971 16777216 177 16777216 (@Ns186p1495 Ns186p159 RS187to204.d39 (Ns186p1497 rfl rfl) rfl) 

noncomputable def Ns186p1499 := nat_lit 2498206876595965921329152 

noncomputable def Ns186p1500 := nat_lit 3722181924133633299774314167918922767128995200002891072322601530638439922837956486787041 

noncomputable def Ns186p1501 := nat_lit 2523415644949738011583289847555312183700046604984501412452633703659132227838615252961 

noncomputable def Ns186p1502 := nat_lit 11161498941111000423299775924061657677019585506798704214142899324508001504058192229855201 

noncomputable def Ns186p1503 := BSN.cos_dyadic_bound_f 35501654971 34359738368 3 2 16777216 4504395 Ns186p1500 Ns186p851 Ns186p1501 Ns186p1502 Ns186p854 Ns186p1501 8590664 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 35501654971) qz371 0 2 Ns186p1500 Ns186p851 Ns186p1501 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 35501654971) qz372 0 2 Ns186p1502 Ns186p854 Ns186p1501 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1504 := @Ns186p1493 2250000 (Ns186p1498 rfl) (Enclosure.sfrac_false_div 70041971 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 70041971) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p1499) qz361) 226375608064910080 72057594037927936 Bool.false 8590664 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 70041971 16777216 226375608064910080 72057594037927936 0 Ns186p1499 Ns186p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 8590664 16777216 Ns186p1499 Ns186p89 35501654971 34359738368 4504395 4500000 (Ns186p1503 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p1505 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz184) 1073833 2097152 25939201 2359296000000 16382257 16382961 8388608 (@Enclosure.Real.IsNear.neg qz184 Bool.true 1073833 2097152 25939201 2359296000000 (Ns186p1492 (Ns186p1504 rfl rfl) rfl)) 

noncomputable def Ns186p1506 := Ns186p1490 (@Enclosure.Real.IsNear.neg qz775 Bool.false 16382609 8388608 11 262144 (@Ns186p1491 11 262144 (Ns186p1505 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p1507 := @Enclosure.Real.IsNear.recentre' qz185 Bool.true 1853473 8388608 

noncomputable abbrev qz187 := (@HMul.hMul Real Real Real qz342 qz340 qz533)

noncomputable def Ns186p1508 := @Enclosure.Real.IsNear.cos_image qz187 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15045689)) qz429) Bool.true 15045689 8388608 

noncomputable def Ns186p1509 := nat_lit 17762814480441037544119192645 

noncomputable def Ns186p1510 := nat_lit 922606935499497369867890251676789 

noncomputable def Ns186p1511 := @Enclosure.Real.IsNear.recentre' qz187 Bool.true Ns186p1509 Ns186p427 Ns186p1510 

noncomputable abbrev qz188 := qz533

noncomputable def Ns186p1512 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz188 884279719003555 140737488355328 1 500000000000000 20087325422839 

noncomputable abbrev qz534 := (@HSub.hSub Real Real Real qz633 qz774 qz767)

noncomputable abbrev qz189 := qz534

noncomputable def Ns186p1513 := @Enclosure.Real.IsNear.subLit_tf qz189 qz26 15689278911735 70368744177664 34188259 8796093022208 1 16 

noncomputable abbrev qz535 := qz774

noncomputable abbrev qz190 := qz535

noncomputable def Ns186p1514 := @Enclosure.Real.IsNear.subLit_ff_n qz190 qz180 31066833980169 70368744177664 19508195 8796093022208 5573763 8388608 7 4194304 

noncomputable def Ns186p1515 := @Enclosure.Real.IsNear.mulLit_ff qz180 qz180 5573763 8388608 7 4194304 5573763 8388608 7 4194304 31066833980169 70368744177664 

noncomputable def Ns186p1516 := nat_lit 25232634855012007021681010641078595873756433551547302044955180039669740950820263040399053601 

noncomputable def Ns186p1517 := nat_lit 134568981855956972670357988849115882226569697156301224964265010764530583520854129644321 

noncomputable def Ns186p1518 := nat_lit 152452516581220589407753399095423395551923209759515691560938050557545400755765953072534524705 

noncomputable def Ns186p1519 := BSN.cos_dyadic_bound_t 15045689 8388608 4 3 8388608 2250000 Ns186p1516 Ns186p754 Ns186p1517 Ns186p1518 Ns186p757 Ns186p1517 1853473 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 15045689) (BSN.cosEvenQ 8388608) 0 3 Ns186p1516 Ns186p754 Ns186p1517 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 15045689) (BSN.cosOddQ 8388608) 0 3 Ns186p1518 Ns186p757 Ns186p1517 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1520 := @Ns186p1507 469638608 18874368000000 1853473 8388608 29352413 1179648000000 (@Ns186p1508 205 8388608 Bool.true 1853473 8388608 1 2250000 (@Ns186p1511 Ns186p430 15045689 8388608 205 8388608 (@Ns186p1512 70368744177664 34188259 8796093022208 Ns186p1509 Ns186p427 Ns186p1510 Ns186p430 RS187to204.d39 (@Ns186p1513 0 1 321397206765424 20087325422839 70368744177664 34188259 8796093022208 (@Ns186p1514 131611210593211514880 15689278911735 70368744177664 34188259 8796093022208 (@Ns186p1515 19508195 8796093022208 (Ns186p1497 rfl rfl) (Ns186p1497 rfl rfl) rfl) (Ns186p1497 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 15045689 8388608) (BSN.cos_neg_of_bound 15045689 8388608 Bool.true 1853473 8388608 1 2250000 (Ns186p1519 rfl rfl)) rfl rfl) 

noncomputable def Ns186p1521 := @Ns186p1482 2272445355627563449 115292150460684697600000 (Ns186p1483 qz28 (@Enclosure.Real.IsNear.of_eq qz772 (@Inv.inv Real Real.instInv (Real.sqrt qz183)) Bool.false 1424917 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz179 (BSN.t_div_two_pi_nonneg qz178 471695 1000 qz181)) Ns186p1487) rfl) (@Ns186p1488 70368744177664 63625150103877 1099511627776000000 (BSN.correction_mk qz180 (BSN.cos_two_pi_p_ne_zero_mk qz178 471695 1000 8 qz181 rfl rfl (@BSN.floor_sqrt_eq_dec qz178 471695 1000 8 qz181 rfl rfl rfl))) (@Ns186p1489 262144 1853473 8388608 29352413 1179648000000 30364723451057 70368744177664 63625150103877 1099511627776000000 Ns186p1506 (Ns186p1520 rfl) rfl)) 

noncomputable def Ns186p1522 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz178) (hardyZApproximantRS₀ qz178) Bool.true 1201271748711672189061 295147905179352825856 180903571170104363449 115292150460684697600000 (@Eq.refl Real (hardyZApproximantRS₀ qz178)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz178) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz178) qz178 8) (@HMul.hMul Real Real Real qz5 qz768 (Zeta.RiemannSiegel.correction qz180))) Bool.true 1201271748711672189061 295147905179352825856 180903571170104363449 115292150460684697600000 (BSN.hardyZApproximantRS₀_eq qz178 8 (@BSN.floor_sqrt_eq_dec qz178 471695 1000 8 qz181 rfl rfl rfl)) (@Ns186p1416 1201271748711672189061 295147905179352825856 180903571170104363449 115292150460684697600000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz178) qz178 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 8)) Bool.true 65824937 16777216 103977 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz178) qz178 8) (Ns186p1481 (Ns186p1480 rfl rfl rfl rfl) rfl rfl)) (Ns186p1521 rfl) rfl rfl)) 

theorem RS187to204.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz178) Bool.true 1201271748711672189061 295147905179352825856 180903571170104363449 115292150460684697600000 := Ns186p1522 

noncomputable def Ns186p1523 := nat_lit 2075258708292324556800000 

noncomputable def Ns186p1524 := nat_lit 21261531891320350723673161728 

noncomputable abbrev qz946 := (Enclosure.sfrac Bool.false 473149 1000)

noncomputable abbrev qz776 := qz946

noncomputable abbrev qz536 := qz776

noncomputable abbrev qz191 := qz536

noncomputable abbrev qz947 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 473149 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz777 := qz947

noncomputable abbrev qz537 := qz777

noncomputable abbrev qz192 := qz537

noncomputable abbrev qz948 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 473149 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz778 := qz948

noncomputable abbrev qz538 := qz778

noncomputable abbrev qz193 := qz538

noncomputable abbrev qz779 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz192 qz9))

noncomputable def Ns186p1525 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz191) qz191 8) (@HMul.hMul Real Real Real qz5 qz779 (Zeta.RiemannSiegel.correction qz193)) 82061733 67108864 26073 16777216 44089804575100809105 295147905179352825856 50052391457276590417 Ns186p1523 Ns186p1524 

noncomputable def Ns186p1526 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz191) qz191 Real.cos BSN.quadSignNeg 7 8 473149 1000 126 134217728 67108864 2251799813685248 Bool.false 105414257467 1845 279097919 60 47453128 8 

noncomputable def Ns186p1527 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz191) qz191 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 473149 1000 39 86 134217728 67108864 2251799813685248 Bool.false 105414257467 1845 

noncomputable def Ns186p1528 := Ns186p1527 240485871 61 54794152 8 261175631 61 50729528 8 Bool.false 122482396 69430 Bool.true 149072059 Bool.true 29461749 7074237752028440 1 Bool.false 120258804 Bool.false Bool.false 130997158 Bool.true Bool.false 122065574 

noncomputable def Ns186p1529 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz191) qz191 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 473149 1000 82 15 134217728 67108864 2251799813685248 Bool.false 105414257467 1845 

noncomputable def Ns186p1530 := Ns186p1529 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 155610907 40772 Bool.false 89709311 Bool.false 44503882 7074237752028440 1 Bool.false 105337111 Bool.true Bool.false 43692855 Bool.false Bool.false 122482396 

noncomputable def Ns186p1531 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz191) qz191 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 473149 1000 291 169 134217728 67108864 2251799813685248 Bool.false 105414257467 1845 

noncomputable def Ns186p1532 := Ns186p1531 93032624 60 94906264 8 147453232 60 77490640 16 Bool.false 134217688 1908 Bool.false 44808641 Bool.false 16855510 7074237752028440 1 Bool.false 43980901 Bool.false Bool.false 16811239 Bool.true Bool.false 155610907 

noncomputable def Ns186p1533 := nat_lit 1428699065175248942924021792333880640404530089687114408357 

noncomputable def Ns186p1534 := nat_lit 1819077866025946794553519700525430075288562440339456000 

noncomputable def Ns186p1535 := nat_lit 11382354271576714438156403559520000 

noncomputable def Ns186p1536 := nat_lit 32313314087168031011172780973435970880 

noncomputable abbrev qz539 := (@Eq.refl Real qz776)

noncomputable abbrev qz194 := qz539

noncomputable def Ns186p1537 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz191 473149 1000 895480904804 16000000 946298 4000 2000 Ns186p1535 Ns186p1536 qz194 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns186p1538 := nat_lit 457183700856079661735686973546841804929449628699876610674240 

noncomputable abbrev qz780 := (Real.log (Enclosure.sfrac Bool.false 895480904804 16000000))

noncomputable abbrev qz195 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 473149 4000) qz780) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 946298))))))

noncomputable abbrev qz781 := (Enclosure.sfrac Bool.false 473149 2000)

noncomputable abbrev qz540 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz195 qz781) (@HMul.hMul Real Real Real qz5 qz781 (Real.log Real.pi)))

noncomputable def Ns186p1539 := @Enclosure.Real.IsNear.addLit_ft_p qz540 (Enclosure.sfrac Bool.true Ns186p1535 Ns186p1536) 14148468481724014647573 18014398509481984000 5625076241261189 409600000000000000000 Ns186p1535 Ns186p1536 0 1 Ns186p1538 

noncomputable def Ns186p1540 := nat_lit 949487647148303384517984387072000 

noncomputable abbrev qz541 := (@HSub.hSub Real Real Real qz12 qz195 qz781)

noncomputable abbrev qz542 := (@HMul.hMul Real Real Real qz5 qz781 (Real.log Real.pi))

noncomputable def Ns186p1541 := @Enclosure.Real.IsNear.subLit_ff_p qz541 qz542 19027017990709295175957 18014398509481984000 5346101419547 800000000000000000 18174013156389 67108864000 473149 67108864000 Ns186p1540 14148468481724014647573 18014398509481984000 

noncomputable def Ns186p1542 := nat_lit 7610807196283718070382800 

noncomputable abbrev qz543 := qz781

noncomputable def Ns186p1543 := @Enclosure.Real.IsNear.subLit_ff_p qz195 qz543 4657753062178148159953 3602879701896396800 5346101419547 800000000000000000 473149 2000 0 1 Ns186p1542 19027017990709295175957 18014398509481984000 5346101419547 800000000000000000 

noncomputable def Ns186p1544 := nat_lit 10488327477604647369619911159100473344 

noncomputable def Ns186p1545 := nat_lit 26433229425427207233208320 

noncomputable def Ns186p1546 := nat_lit 9065249643222941352206441094784208367756200942785543007205920607539354039958133235604890031930576576123140832478155639761422739849383660272396439388160 

noncomputable def Ns186p1547 := nat_lit 215456671877988966374008337571373640551684904412074928821785950850375051307990147617003862695612832188846179526254434581365493599900140938444356452352 

noncomputable def Ns186p1548 := nat_lit 71124706768884459403844820439244179133905850485797976991632554240754223679817042962328265515086683086828535850730668828350156205019076304568320 

noncomputable def Ns186p1549 := BSN.log_dyadic_bound 371192904804 1419768904804 7 6 Ns186p1546 67108864 18000000 Ns186p1547 Ns186p1548 35924700 1790961809608 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 371192904804) (BSN.artanhQ 1419768904804) 0 6 Ns186p1547 Ns186p1546 Ns186p1548 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns186p1550 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 473149 4000) qz780 473149 4000 0 1 49235726567780985 4503599627370496 100000027 1800000000000000 4659166957963801054353 3602879701896396800 47314912775023 7200000000000000000 (Enclosure.Real.IsNear.const Bool.false 473149 4000) (BSN.isNear_log_sfrac 895480904804 16000000 49235726567780985 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 895480904804) qz353)) Bool.false Ns186p1545 Ns186p89 1000000270000000 18000000000000000000000 49235726567780985 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 895480904804 16000000 15 1790961809608 1048576000000 35924700 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns186p1549 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p1551 := BSN.arctan_dyadic_bound_f 1000 946298 1 0 8388608 2250000 0 1 1 0 1 1 8864 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 946298) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 946298) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz782 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 946298)))

noncomputable def Ns186p1552 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz782 884279719003555 562949953421312 1 2000000000000000 8864 8388608 1 2250000 7412885936683846991872 883684866033059 562949953421312 8000000009 18000000000000000 qz16 (Ns186p1551 rfl) rfl rfl 

noncomputable def Ns186p1553 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 473149 4000) qz780) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz782)) 4659166957963801054353 3602879701896396800 47314912775023 7200000000000000000 883684866033059 2251799813685248 8000000009 72000000000000000 Ns186p1544 4657753062178148159953 3602879701896396800 5346101419547 800000000000000000 (Ns186p1550 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz782) 1 4 0 1 883684866033059 562949953421312 8000000009 18000000000000000 883684866033059 2251799813685248 8000000009 72000000000000000 qz356 Ns186p1552 rfl) 

noncomputable def Ns186p1554 := @Ns186p1539 Ns186p1533 Ns186p1534 5625076241261189 409600000000000000000 (@Ns186p1541 5625076241261189 409600000000000000000 (Ns186p1543 (Ns186p1553 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 473149 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz543 (Real.log Real.pi) 473149 2000 0 1 38410761 33554432 1 33554432 18174013156389 67108864000 473149 67108864000 (Enclosure.Real.IsNear.const Bool.false 473149 2000) RS187to204.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns186p1535 Ns186p1536) 

noncomputable def Ns186p1555 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz191) Bool.false Ns186p1533 Ns186p1534 5625076241261189 409600000000000000000 13176782183 16777216 231 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz191) (@HAdd.hAdd Real Real Real qz357 qz540 (Enclosure.sfrac Bool.true Ns186p1535 Ns186p1536)) Bool.false Ns186p1533 Ns186p1534 5625076241261189 409600000000000000000 Ns186p1537 (Ns186p1554 rfl rfl)) 

noncomputable def Ns186p1556 := nat_lit 3796158193098828709625856 

noncomputable def Ns186p1557 := nat_lit 855515706408874569818847151286879578187229599209107463058277737209077904302542366927621722417379649966122937695753734683983249400795136 

noncomputable def Ns186p1558 := nat_lit 607538797907934967707374317857800991748832669309409746076995213827575987873110755028469227765301341300153962394311148807696551936 

noncomputable def Ns186p1559 := nat_lit 4272273134944024828334809380576009712337721765310542277271070949288568654344933758671948651733631911566732295621911118890740557968183296 

noncomputable def Ns186p1560 := BSN.sin_dyadic_bound_f 53946652558 34359738368 4 3 16777216 4504395 Ns186p1557 Ns186p102 Ns186p1558 Ns186p1559 Ns186p105 Ns186p1558 16777211 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53946652558) qz358 0 3 Ns186p1557 Ns186p102 Ns186p1558 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53946652558) qz359 0 3 Ns186p1559 Ns186p105 Ns186p1558 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1561 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz191) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13176782183) qz360) Bool.false 13176782183 16777216 231 16777216 Bool.false 16777211 16777216 1 2250000 (Ns186p1555 rfl) (Enclosure.sfrac_false_div 13176782183 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13176782183) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p1556) qz361) 226375608064910080 72057594037927936 Bool.false 16777211 16777216 124 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q3 13176782183 16777216 226375608064910080 72057594037927936 124 Ns186p1556 Ns186p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777211 16777216 Ns186p1556 Ns186p89 53946652558 34359738368 4504395 4500000 (Ns186p1560 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p1562 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz191) Bool.false Ns186p1533 Ns186p1534 5625076241261189 409600000000000000000 105414257467 134217728 1845 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz191) (@HAdd.hAdd Real Real Real qz357 qz540 (Enclosure.sfrac Bool.true Ns186p1535 Ns186p1536)) Bool.false Ns186p1533 Ns186p1534 5625076241261189 409600000000000000000 Ns186p1537 (Ns186p1554 rfl rfl)) 

noncomputable def Ns186p1563 := Ns186p1532 40772 BSN.abs_quadSignPos (BSN.cos_quad_nat3 291 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 43980901 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 169 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 16811239 134217728) qz194 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz191) qz191 1) Bool.false 16777211 16777216 33532951 2359296000000 134217688 134217728 1908 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz191) qz191 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz191)) Bool.false 16777211 16777216 33532951 2359296000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz191) qz191) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz191)) Bool.false 16777211 16777216 536527216 37748736000000 16777211 16777216 33532951 2359296000000 (Ns186p1561 rfl rfl) rfl)) rfl) (Ns186p1562 rfl) RS187to204.d7 

noncomputable def Ns186p1564 := nat_lit 4031318296481213844737921468161 

noncomputable def Ns186p1565 := BSN.sin_dyadic_bound_f 44808641 134217728 2 1 134217728 67108864 Ns186p1564 Ns186p123 Ns186p1564 Ns186p1564 Ns186p124 Ns186p1564 43980901 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 44808641) qz362 0 1 Ns186p1564 Ns186p123 Ns186p1564 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 44808641) qz363 0 1 Ns186p1564 Ns186p124 Ns186p1564 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1566 := nat_lit 80717479171533827013072010000 

noncomputable def Ns186p1567 := BSN.sin_dyadic_bound_f 16855510 134217728 2 1 134217728 67108864 Ns186p1566 Ns186p123 Ns186p1566 Ns186p1566 Ns186p124 Ns186p1566 16811239 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 16855510) qz362 0 1 Ns186p1566 Ns186p123 Ns186p1566 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 16855510) qz363 0 1 Ns186p1566 Ns186p124 Ns186p1566 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1568 := nat_lit 35314290670366731354979692594633114141547461704992582067942342338561 

noncomputable def Ns186p1569 := nat_lit 4194692883035397877509261844100070690782999381349944116626401281 

noncomputable def Ns186p1570 := nat_lit 105934482625334123269184059260211142283260819116215046315593774213121 

noncomputable def Ns186p1571 := BSN.cos_dyadic_bound_f 89709311 134217728 3 2 134217728 67108864 Ns186p1568 Ns186p117 Ns186p1569 Ns186p1570 Ns186p120 Ns186p1569 105337111 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 89709311) qz364 0 2 Ns186p1568 Ns186p117 Ns186p1569 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 89709311) qz365 0 2 Ns186p1570 Ns186p120 Ns186p1569 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1572 := nat_lit 3922758586392715490306913365776 

noncomputable def Ns186p1573 := BSN.sin_dyadic_bound_f 44503882 134217728 2 1 134217728 67108864 Ns186p1572 Ns186p123 Ns186p1572 Ns186p1572 Ns186p124 Ns186p1572 43692855 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 44503882) qz362 0 1 Ns186p1572 Ns186p123 Ns186p1572 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 44503882) qz363 0 1 Ns186p1572 Ns186p124 Ns186p1572 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1574 := Ns186p1530 69430 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 82 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 105337111 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 15 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 43692855 134217728) qz194 rfl rfl (Ns186p1563 RS187to204.d9 RS187to204.d11 RS187to204.d13 RS187to204.d17 (Ns186p1565 rfl rfl) (Ns186p1567 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns186p1562 rfl) RS187to204.d19 RS187to204.d21 RS187to204.d23 RS187to204.d25 RS187to204.d17 (Ns186p1571 rfl rfl) (Ns186p1573 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns186p1575 := nat_lit 484869439656931551697426891201276811063724381991653115983653568014305 

noncomputable def Ns186p1576 := nat_lit 243876526190425714914581018849440185709994645581868791848373348321 

noncomputable def Ns186p1577 := nat_lit 1269501303773369565192923012449016363913842913885292278103719121283041 

noncomputable def Ns186p1578 := BSN.sin_dyadic_bound_f 149072059 134217728 3 2 134217728 67108864 Ns186p1575 Ns186p111 Ns186p1576 Ns186p1577 Ns186p114 Ns186p1576 120258804 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 149072059) qz362 0 2 Ns186p1575 Ns186p111 Ns186p1576 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 149072059) qz363 0 2 Ns186p1577 Ns186p114 Ns186p1576 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1579 := nat_lit 753414719613883965820629278001 

noncomputable def Ns186p1580 := BSN.cos_dyadic_bound_f 29461749 134217728 2 1 134217728 67108864 Ns186p1579 Ns186p134 Ns186p1579 Ns186p1579 Ns186p135 Ns186p1579 130997158 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 29461749) qz364 0 1 Ns186p1579 Ns186p134 Ns186p1579 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 29461749) qz365 0 1 Ns186p1579 Ns186p135 Ns186p1579 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1581 := Ns186p1528 93592 BSN.abs_quadSignPos (BSN.cos_quad_nat3 39 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 120258804 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 86 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 130997158 134217728) qz194 rfl rfl (Ns186p1574 rfl rfl) (Ns186p1562 rfl) RS187to204.d27 RS187to204.d29 RS187to204.d31 RS187to204.d33 RS187to204.d17 (Ns186p1578 rfl rfl) (Ns186p1580 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns186p1582 := nat_lit 18407055889583556946322889702312168755426460086781128649226143587041 

noncomputable def Ns186p1583 := nat_lit 1139770074678936716097133640644282598580645197137941944703310561 

noncomputable def Ns186p1584 := nat_lit 55218888128601312965536474839655217701082218969949110063789024140001 

noncomputable def Ns186p1585 := BSN.cos_dyadic_bound_f 76225829 134217728 3 2 134217728 67108864 Ns186p1582 Ns186p117 Ns186p1583 Ns186p1584 Ns186p120 Ns186p1583 113147959 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 76225829) qz364 0 2 Ns186p1582 Ns186p117 Ns186p1583 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 76225829) qz365 0 2 Ns186p1584 Ns186p120 Ns186p1583 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1586 := Ns186p1526 Bool.false 122065574 93592 Bool.true 76225829 7074237752028440 1 Bool.false 113147959 Bool.true Bool.false 82061733 104292 BSN.abs_quadSignNeg qz431 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 113147959 134217728) qz194 rfl (Ns186p1581 rfl) (Ns186p1562 rfl) RS187to204.d35 RS187to204.d37 RS187to204.d17 (Ns186p1585 rfl rfl) rfl 

noncomputable def Ns186p1587 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz191) qz191 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz191) qz191 8) 82061733 134217728 104292 134217728 82061733 134217728 104292 134217728 22028278718005248 82061733 67108864 26073 16777216 (Ns186p1586 rfl rfl rfl rfl) 

noncomputable def Ns186p1588 := @Enclosure.Real.IsNear.mulLit_ff qz779 (Zeta.RiemannSiegel.correction qz193) 1423821 4194304 1 8388608 30965833890005 70368744177664 140308394549477 1979120929996800000 44089804575100809105 295147905179352825856 

noncomputable abbrev qz783 := (@HPow.hPow Real Real Real qz7 qz192 qz9)

noncomputable def Ns186p1589 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz783 1 1 0 1 1423821 4194304 1 8388608 1423821 4194304 1 8388608 

noncomputable def Ns186p1590 := @Enclosure.Real.IsNear.sqrt_image qz192 1263391577373 16777216000 473149 16777216000 72794548 72794577 8388608 (@Enclosure.Real.IsNear.of_eq qz192 (@HMul.hMul Real Real Real qz5 qz191 qz3) Bool.false 1263391577373 16777216000 473149 16777216000 (BSN.t_div_two_pi_mk qz191 473149 1000 qz194) (@Enclosure.Real.IsNear.mulLit_ff qz191 qz3 473149 1000 0 1 2670177 16777216 1 16777216 1263391577373 16777216000 473149 16777216000 (Enclosure.Real.IsNear.const Bool.false 473149 1000) RS187to204.d40 rfl)) 

noncomputable abbrev qz949 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 473149 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz784 := qz949

noncomputable abbrev qz544 := qz784

noncomputable abbrev qz196 := qz544

noncomputable def Ns186p1591 := @Enclosure.Real.IsNear.sqrt_image qz196 145589125 16777216 29 16777216 24711230 24711236 8388608 (@Enclosure.Real.IsNear.recentre' qz196 Bool.false 145589125 16777216 29 16777216 145589125 16777216 29 16777216 (Ns186p1590 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns186p1592 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz196) 24711233 8388608 3 8388608 2847641 2847643 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz196) Bool.false 49422466 16777216 6 16777216 24711233 8388608 3 8388608 (Ns186p1591 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns186p1593 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz196)) Bool.false 5695284 16777216 2 16777216 1423821 4194304 1 8388608 (Ns186p1592 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz197 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz538))

noncomputable abbrev qz785 := (@HMul.hMul Real Real Real qz891 qz948 qz948)

noncomputable abbrev qz545 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz785 qz778) qz640)

noncomputable abbrev qz198 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz545))

noncomputable def Ns186p1594 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz193) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz197) qz198) Bool.false 30965833890005 

noncomputable def Ns186p1595 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz197) qz198 19138399 8388608 31 

noncomputable abbrev qz786 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz197))

noncomputable def Ns186p1596 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz197) (@Neg.neg Real Real.instNeg qz786) Bool.true 19138399 8388608 31 524288 (BSN.inv_eq_neg_inv_neg qz197) 

noncomputable def Ns186p1597 := @Enclosure.Real.IsNear.recentre' qz786 Bool.false 38276798 16777216 992 16777216 19138399 8388608 

noncomputable def Ns186p1598 := @Enclosure.Real.IsNear.recentre' qz197 Bool.true 7353671 16777216 428527216 37748736000000 7353671 16777216 26782951 2359296000000 

noncomputable abbrev qz199 := (@HMul.hMul Real Real Real qz342 qz340 qz538)

noncomputable def Ns186p1599 := @Enclosure.Real.IsNear.cos_image qz199 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 35724297) qz429) Bool.false 35724297 8388608 183 16777216 Bool.true 7353671 16777216 1 

noncomputable def Ns186p1600 := nat_lit 782596186959956874649565067 

noncomputable def Ns186p1601 := nat_lit 72057594037927936000000000000000 

noncomputable def Ns186p1602 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz193 884279719003555 140737488355328 1 500000000000000 11371397 16777216 29 16777216 10055495743837868316335 2361183241434822606848 Ns186p1600 

noncomputable def Ns186p1603 := @Enclosure.Real.IsNear.subLit_ff_p qz196 qz1 145589125 16777216 29 16777216 8 1 0 1 11371397 11371397 16777216 29 

noncomputable def Ns186p1604 := @Ns186p1603 16777216 (@Enclosure.Real.IsNear.recentre' qz196 Bool.false 145589125 16777216 29 16777216 145589125 16777216 29 16777216 (Ns186p1590 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns186p1605 := @Enclosure.Real.IsNear.recentre' qz199 Bool.false 10055495743837868316335 2361183241434822606848 Ns186p1600 Ns186p1601 35724297 8388608 183 16777216 (@Ns186p1602 Ns186p1601 RS187to204.d39 (Ns186p1604 rfl rfl) rfl) 

noncomputable def Ns186p1606 := nat_lit 1350461307396395267784704 

noncomputable def Ns186p1607 := nat_lit 5086749922949827742856394216474321292187474073341947373764744321082304290897535400390625 

noncomputable def Ns186p1608 := nat_lit 4710410163175080291202153601506098079240924106618813235184409785556852817535400390625 

noncomputable def Ns186p1609 := nat_lit 15250828948523133067986778342219951680403940371812604494823864143675799167057535400390625 

noncomputable def Ns186p1610 := BSN.cos_dyadic_bound_f 38382418875 34359738368 3 2 16777216 4504395 Ns186p1607 Ns186p851 Ns186p1608 Ns186p1609 Ns186p854 Ns186p1608 7353671 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 38382418875) qz371 0 2 Ns186p1607 Ns186p851 Ns186p1608 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 38382418875) qz372 0 2 Ns186p1609 Ns186p854 Ns186p1608 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1611 := @Ns186p1599 2250000 (Ns186p1605 rfl) (Enclosure.sfrac_false_div 35724297 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 35724297) qz429) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p1606) qz430) 226375608064910080 72057594037927936 Bool.false 7353671 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 35724297 8388608 226375608064910080 72057594037927936 0 Ns186p1606 Ns186p578 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 7353671 16777216 Ns186p1606 Ns186p578 38382418875 34359738368 4504395 4500000 (Ns186p1610 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p1612 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz197) 7353671 16777216 26782951 2359296000000 19137903 19138895 8388608 (@Enclosure.Real.IsNear.neg qz197 Bool.true 7353671 16777216 26782951 2359296000000 (Ns186p1598 (Ns186p1611 rfl rfl) rfl)) 

noncomputable def Ns186p1613 := Ns186p1596 (@Enclosure.Real.IsNear.neg qz786 Bool.false 19138399 8388608 31 524288 (@Ns186p1597 31 524288 (Ns186p1612 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p1614 := @Enclosure.Real.IsNear.recentre' qz198 Bool.true 1617995 8388608 

noncomputable abbrev qz200 := (@HMul.hMul Real Real Real qz342 qz340 qz545)

noncomputable def Ns186p1615 := @Enclosure.Real.IsNear.cos_image qz200 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 14804993)) qz429) Bool.true 14804993 8388608 

noncomputable def Ns186p1616 := nat_lit 69914603278472323684433652245 

noncomputable def Ns186p1617 := nat_lit 39614081257132168796771975168 

noncomputable def Ns186p1618 := nat_lit 6185646365345528194738891974534921 

noncomputable def Ns186p1619 := @Enclosure.Real.IsNear.recentre' qz200 Bool.true Ns186p1616 Ns186p1617 Ns186p1618 

noncomputable def Ns186p1620 := nat_lit 241785163922925834941235200000000000000 

noncomputable abbrev qz201 := qz545

noncomputable def Ns186p1621 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz201 884279719003555 140737488355328 1 500000000000000 79063900003559 

noncomputable abbrev qz546 := (@HSub.hSub Real Real Real qz633 qz785 qz778)

noncomputable abbrev qz202 := qz546

noncomputable def Ns186p1622 := @Enclosure.Real.IsNear.subLit_tf qz202 qz26 61471713959143 281474976710656 1146081131 281474976710656 1 16 

noncomputable abbrev qz547 := qz785

noncomputable abbrev qz203 := qz547

noncomputable def Ns186p1623 := @Enclosure.Real.IsNear.subLit_ff_n qz203 qz193 129308669731609 281474976710656 659541867 281474976710656 11371397 16777216 29 16777216 

noncomputable def Ns186p1624 := @Enclosure.Real.IsNear.mulLit_ff qz193 qz193 11371397 16777216 29 16777216 11371397 16777216 29 16777216 129308669731609 281474976710656 

noncomputable def Ns186p1625 := nat_lit 23647252664256586374501268724416049797859274632429315953917203071200225673058128238891950081 

noncomputable def Ns186p1626 := nat_lit 110891555796369237958261297770831318534993148342097942706317698497506368510397529907201 

noncomputable def Ns186p1627 := nat_lit 142910275533393500654926792943615038209907905009568712940504185088862636217991250456377483265 

noncomputable def Ns186p1628 := BSN.cos_dyadic_bound_t 14804993 8388608 4 3 8388608 2250000 Ns186p1625 Ns186p754 Ns186p1626 Ns186p1627 Ns186p757 Ns186p1626 1617995 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 14804993) (BSN.cosEvenQ 8388608) 0 3 Ns186p1625 Ns186p754 Ns186p1626 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 14804993) (BSN.cosOddQ 8388608) 0 3 Ns186p1627 Ns186p757 Ns186p1626 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1629 := @Ns186p1614 492138608 18874368000000 1617995 8388608 30758663 1179648000000 (@Ns186p1615 215 8388608 Bool.true 1617995 8388608 1 2250000 (@Ns186p1619 Ns186p1620 14804993 8388608 215 8388608 (@Ns186p1621 281474976710656 1146081131 281474976710656 Ns186p1616 Ns186p1617 Ns186p1618 Ns186p1620 RS187to204.d39 (@Ns186p1622 0 1 1265022400056944 79063900003559 281474976710656 1146081131 281474976710656 (@Ns186p1623 1031324222982757285888 61471713959143 281474976710656 1146081131 281474976710656 (@Ns186p1624 659541867 281474976710656 (Ns186p1604 rfl rfl) (Ns186p1604 rfl rfl) rfl) (Ns186p1604 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 14804993 8388608) (BSN.cos_neg_of_bound 14804993 8388608 Bool.true 1617995 8388608 1 2250000 (Ns186p1628 rfl rfl)) rfl rfl) 

noncomputable def Ns186p1630 := @Ns186p1588 50052391457276590417 Ns186p1523 (Ns186p1589 qz28 (@Enclosure.Real.IsNear.of_eq qz783 (@Inv.inv Real Real.instInv (Real.sqrt qz196)) Bool.false 1423821 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz192 (BSN.t_div_two_pi_nonneg qz191 473149 1000 qz194)) Ns186p1593) rfl) (@Ns186p1594 70368744177664 140308394549477 1979120929996800000 (BSN.correction_mk qz193 (BSN.cos_two_pi_p_ne_zero_mk qz191 473149 1000 8 qz194 rfl rfl (@BSN.floor_sqrt_eq_dec qz191 473149 1000 8 qz194 rfl rfl rfl))) (@Ns186p1595 524288 1617995 8388608 30758663 1179648000000 30965833890005 70368744177664 140308394549477 1979120929996800000 Ns186p1613 (Ns186p1629 rfl) rfl)) 

noncomputable def Ns186p1631 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz191) (hardyZApproximantRS₀ qz191) Bool.false 316821513940697174127 295147905179352825856 3275153641945186990417 Ns186p1523 (@Eq.refl Real (hardyZApproximantRS₀ qz191)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz191) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz191) qz191 8) (@HMul.hMul Real Real Real qz5 qz779 (Zeta.RiemannSiegel.correction qz193))) Bool.false 316821513940697174127 295147905179352825856 3275153641945186990417 Ns186p1523 (BSN.hardyZApproximantRS₀_eq qz191 8 (@BSN.floor_sqrt_eq_dec qz191 473149 1000 8 qz194 rfl rfl rfl)) (@Ns186p1525 316821513940697174127 295147905179352825856 3275153641945186990417 Ns186p1523 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz191) qz191 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz191) qz191 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz191) qz191 8)) Bool.false 82061733 67108864 26073 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz191) qz191 8) (Ns186p1587 (Ns186p1586 rfl rfl rfl rfl) rfl rfl)) (Ns186p1630 rfl) rfl rfl)) 

theorem RS187to204.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz191) Bool.false 316821513940697174127 295147905179352825856 3275153641945186990417 Ns186p1523 := Ns186p1631 

noncomputable def Ns186p1632 := nat_lit 4611686018427387904000000 

noncomputable def Ns186p1633 := nat_lit 5777957197960902478871396352 

noncomputable abbrev qz950 := (Enclosure.sfrac Bool.false 474603 1000)

noncomputable abbrev qz787 := qz950

noncomputable abbrev qz548 := qz787

noncomputable abbrev qz204 := qz548

noncomputable abbrev qz951 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 474603 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz788 := qz951

noncomputable abbrev qz549 := qz788

noncomputable abbrev qz205 := qz549

noncomputable abbrev qz952 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 474603 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz789 := qz952

noncomputable abbrev qz550 := qz789

noncomputable abbrev qz206 := qz550

noncomputable abbrev qz790 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz205 qz9))

noncomputable def Ns186p1634 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 8) (@HMul.hMul Real Real Real qz5 qz790 (Zeta.RiemannSiegel.correction qz206)) 73191625 33554432 26153 16777216 11246457669294328561 73786976294838206464 131734087801125298773 Ns186p1632 Ns186p1633 

noncomputable def Ns186p1635 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.cos BSN.quadSignNeg 7 8 474603 1000 126 134217728 67108864 2251799813685248 Bool.false 105836086189 1850 279097919 60 47453128 8 

noncomputable def Ns186p1636 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 474603 1000 39 85 134217728 67108864 2251799813685248 Bool.false 105836086189 1850 

noncomputable def Ns186p1637 := Ns186p1636 240485871 61 54794152 8 261175631 61 50729528 8 Bool.true 82827112 69644 Bool.true 76909794 Bool.true 198211109 7074237752028440 1 Bool.false 72769406 Bool.false Bool.false 133625083 Bool.true Bool.true 103624659 

noncomputable def Ns186p1638 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 474603 1000 83 15 134217728 67108864 2251799813685248 Bool.false 105836086189 1850 

noncomputable def Ns186p1639 := Ns186p1638 186065264 60 67108856 8 216015088 60 60023992 8 Bool.true 152182313 40898 Bool.false 30170425 Bool.false 152246666 7074237752028440 1 Bool.false 29916984 Bool.false Bool.false 121634745 Bool.false Bool.true 82827112 

noncomputable def Ns186p1640 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 474603 1000 292 170 134217728 67108864 2251799813685248 Bool.false 105836086189 1850 

noncomputable def Ns186p1641 := Ns186p1640 93032624 60 94906264 8 147453232 60 77490640 16 Bool.true 134217704 1916 Bool.false 120539213 Bool.false 13458519 7074237752028440 1 Bool.false 83632037 Bool.false Bool.false 133543524 Bool.true Bool.true 152182313 

noncomputable def Ns186p1642 := nat_lit 162340909548537209028385261243517997847603278658894620827 

noncomputable def Ns186p1643 := nat_lit 205875224845355467862437681677530416444422316097536000 

noncomputable def Ns186p1644 := nat_lit 11558323724205515731105206356640000 

noncomputable def Ns186p1645 := nat_lit 32913707734540040142013934866898483520 

noncomputable abbrev qz551 := (@Eq.refl Real qz787)

noncomputable abbrev qz207 := qz551

noncomputable def Ns186p1646 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz204 474603 1000 900993030436 16000000 949206 4000 2000 Ns186p1644 Ns186p1645 qz207 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns186p1647 := nat_lit 467541819499787162001749552381331833801097442537616507981760 

noncomputable abbrev qz791 := (Real.log (Enclosure.sfrac Bool.false 900993030436 16000000))

noncomputable abbrev qz208 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 474603 4000) qz791) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 949206))))))

noncomputable abbrev qz792 := (Enclosure.sfrac Bool.false 474603 2000)

noncomputable abbrev qz552 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz208 qz792) (@HMul.hMul Real Real Real qz5 qz792 (Real.log Real.pi)))

noncomputable def Ns186p1648 := @Enclosure.Real.IsNear.addLit_ft_p qz552 (Enclosure.sfrac Bool.true Ns186p1644 Ns186p1645) 14205085354920151188563 18014398509481984000 50780001596919547 3686400000000000000000 Ns186p1644 Ns186p1645 0 1 Ns186p1647 

noncomputable def Ns186p1649 := nat_lit 953287141191728156972712722432000 

noncomputable abbrev qz553 := (@HSub.hSub Real Real Real qz12 qz208 qz792)

noncomputable abbrev qz554 := (@HMul.hMul Real Real Real qz5 qz792 (Real.log Real.pi))

noncomputable def Ns186p1650 := @Enclosure.Real.IsNear.subLit_ff_p qz553 qz554 19098626781855305008211 18014398509481984000 48260312815181 7200000000000000000 18229862402883 67108864000 474603 67108864000 Ns186p1649 14205085354920151188563 18014398509481984000 

noncomputable def Ns186p1651 := nat_lit 38197253563710610016422000 

noncomputable abbrev qz555 := qz792

noncomputable def Ns186p1652 := @Enclosure.Real.IsNear.subLit_ff_p qz208 qz555 23373470569753144034387 18014398509481984000 48260312815181 7200000000000000000 474603 2000 0 1 Ns186p1651 19098626781855305008211 18014398509481984000 48260312815181 7200000000000000000 

noncomputable def Ns186p1653 := nat_lit 52632376674147757153776914612906622976 

noncomputable def Ns186p1654 := nat_lit 26448066840644353993474048 

noncomputable def Ns186p1655 := nat_lit 9496725957935535226182096162971235743917496456238532732180676986324551259865338766466190936206509209877645326074293199269812557711835304241384086568960 

noncomputable def Ns186p1656 := nat_lit 230891045029622305758135479769779103103041949968025419875097468858040849893728145870982237205459798747560526958302273710026589802797732641826890842112 

noncomputable def Ns186p1657 := nat_lit 84887067401784837164149781930927895119551777551471448839500328786791469923255312636828752870143863654722525033786707257700741832497510135889920 

noncomputable def Ns186p1658 := BSN.log_dyadic_bound 376705030436 1425281030436 7 6 Ns186p1655 67108864 18000000 Ns186p1656 Ns186p1657 36336521 1801986060872 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 376705030436) (BSN.artanhQ 1425281030436) 0 6 Ns186p1656 Ns186p1655 Ns186p1657 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns186p1659 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 474603 4000) qz791 474603 4000 0 1 49263363407262329 4503599627370496 100000027 1800000000000000 23380540063176923130387 18014398509481984000 15820104271427 2400000000000000000 (Enclosure.Real.IsNear.const Bool.false 474603 4000) (BSN.isNear_log_sfrac 900993030436 16000000 49263363407262329 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 900993030436) qz353)) Bool.false Ns186p1654 Ns186p89 1000000270000000 18000000000000000000000 49263363407262329 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 900993030436 16000000 15 1801986060872 1048576000000 36336521 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns186p1658 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p1660 := BSN.arctan_dyadic_bound_f 1000 949206 1 0 8388608 2250000 0 1 1 0 1 1 8837 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 949206) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 949206) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz793 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 949206)))

noncomputable def Ns186p1661 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz793 884279719003555 562949953421312 1 2000000000000000 8837 8388608 1 2250000 7412901136332589367296 883686677972387 562949953421312 8000000009 18000000000000000 qz16 (Ns186p1660 rfl) rfl rfl 

noncomputable def Ns186p1662 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 474603 4000) qz791) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz793)) 23380540063176923130387 18014398509481984000 15820104271427 2400000000000000000 883686677972387 2251799813685248 8000000009 72000000000000000 Ns186p1653 23373470569753144034387 18014398509481984000 48260312815181 7200000000000000000 (Ns186p1659 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz793) 1 4 0 1 883686677972387 562949953421312 8000000009 18000000000000000 883686677972387 2251799813685248 8000000009 72000000000000000 qz356 Ns186p1661 rfl) 

noncomputable def Ns186p1663 := @Ns186p1648 Ns186p1642 Ns186p1643 50780001596919547 3686400000000000000000 (@Ns186p1650 50780001596919547 3686400000000000000000 (Ns186p1652 (Ns186p1662 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 474603 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz555 (Real.log Real.pi) 474603 2000 0 1 38410761 33554432 1 33554432 18229862402883 67108864000 474603 67108864000 (Enclosure.Real.IsNear.const Bool.false 474603 2000) RS187to204.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns186p1644 Ns186p1645) 

noncomputable def Ns186p1664 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz204) Bool.false Ns186p1642 Ns186p1643 50780001596919547 3686400000000000000000 13229510773 16777216 29 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz204) (@HAdd.hAdd Real Real Real qz357 qz552 (Enclosure.sfrac Bool.true Ns186p1644 Ns186p1645)) Bool.false Ns186p1642 Ns186p1643 50780001596919547 3686400000000000000000 Ns186p1646 (Ns186p1663 rfl rfl)) 

noncomputable def Ns186p1665 := BSN.cos_dyadic_bound_f 18352423 34359738368 1 0 16777216 4504395 0 1 1 0 1 1 16777213 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 18352423) qz371 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 18352423) qz372 0 0 rfl) rfl rfl 

noncomputable def Ns186p1666 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz204) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13229510773) qz360) Bool.false 13229510773 16777216 29 2097152 Bool.true 16777213 16777216 1 2250000 (Ns186p1664 rfl) (Enclosure.sfrac_false_div 13229510773 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13229510773) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1291437014506585194496) qz361) 226375608064910080 72057594037927936 Bool.false 16777213 16777216 125 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 13229510773 16777216 226375608064910080 72057594037927936 125 1291437014506585194496 Ns186p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777213 16777216 1291437014506585194496 Ns186p89 18352423 34359738368 4504395 4500000 (Ns186p1665 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p1667 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz204) Bool.false Ns186p1642 Ns186p1643 50780001596919547 3686400000000000000000 105836086189 134217728 1850 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz204) (@HAdd.hAdd Real Real Real qz357 qz552 (Enclosure.sfrac Bool.true Ns186p1644 Ns186p1645)) Bool.false Ns186p1642 Ns186p1643 50780001596919547 3686400000000000000000 Ns186p1646 (Ns186p1663 rfl rfl)) 

noncomputable def Ns186p1668 := Ns186p1641 40898 BSN.abs_quadSignPos (BSN.cos_quad_nat0 292 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 83632037 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 170 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133543524 134217728) qz207 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 1) Bool.true 16777213 16777216 4209197 294912000000 134217704 134217728 1916 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz204)) Bool.true 16777213 16777216 4209197 294912000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz204) qz204) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz204)) Bool.true 16777213 16777216 67347152 4718592000000 16777213 16777216 4209197 294912000000 (Ns186p1666 rfl rfl) rfl)) rfl) (Ns186p1667 rfl) RS187to204.d7 

noncomputable def Ns186p1669 := nat_lit 115141095598858816069315328760311840094532504793732756034893175904801 

noncomputable def Ns186p1670 := nat_lit 44568376379023041832799192650731945360967494173348457934931941921 

noncomputable def Ns186p1671 := nat_lit 345334150043818402124280387895634056392875579392851571188809663830561 

noncomputable def Ns186p1672 := BSN.cos_dyadic_bound_f 120539213 134217728 3 2 134217728 67108864 Ns186p1669 Ns186p117 Ns186p1670 Ns186p1671 Ns186p120 Ns186p1670 83632037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 120539213) qz364 0 2 Ns186p1669 Ns186p117 Ns186p1670 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 120539213) qz365 0 2 Ns186p1671 Ns186p120 Ns186p1670 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1673 := nat_lit 32808704943517379182641036321 

noncomputable def Ns186p1674 := BSN.cos_dyadic_bound_f 13458519 134217728 2 1 134217728 67108864 Ns186p1673 Ns186p134 Ns186p1673 Ns186p1673 Ns186p135 Ns186p1673 133543524 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 13458519) qz364 0 1 Ns186p1673 Ns186p134 Ns186p1673 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 13458519) qz365 0 1 Ns186p1673 Ns186p135 Ns186p1673 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1675 := nat_lit 828563336111731934483250390625 

noncomputable def Ns186p1676 := BSN.sin_dyadic_bound_f 30170425 134217728 2 1 134217728 67108864 Ns186p1675 Ns186p123 Ns186p1675 Ns186p1675 Ns186p124 Ns186p1675 29916984 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 30170425) qz362 0 1 Ns186p1675 Ns186p123 Ns186p1675 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 30170425) qz363 0 1 Ns186p1675 Ns186p124 Ns186p1675 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1677 := nat_lit 527533672183432480661474154073293401344604123021112443056674278990080 

noncomputable def Ns186p1678 := nat_lit 288657155385675333844074812701087456049184880995460589036700426496 

noncomputable def Ns186p1679 := nat_lit 1381168458419317784525256187161871433354645451438444700385230358569216 

noncomputable def Ns186p1680 := BSN.sin_dyadic_bound_f 152246666 134217728 3 2 134217728 67108864 Ns186p1677 Ns186p111 Ns186p1678 Ns186p1679 Ns186p114 Ns186p1678 121634745 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 152246666) qz362 0 2 Ns186p1677 Ns186p111 Ns186p1678 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 152246666) qz363 0 2 Ns186p1679 Ns186p114 Ns186p1678 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1681 := Ns186p1639 69644 BSN.abs_quadSignPos (BSN.cos_quad_nat3 83 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 29916984 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 15 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 121634745 134217728) qz207 rfl rfl (Ns186p1668 RS187to204.d9 RS187to204.d11 RS187to204.d13 RS187to204.d17 (Ns186p1672 rfl rfl) (Ns186p1674 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns186p1667 rfl) RS187to204.d19 RS187to204.d21 RS187to204.d23 RS187to204.d25 RS187to204.d17 (Ns186p1676 rfl rfl) (Ns186p1680 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns186p1682 := nat_lit 34337082738784889611760235734626149130011315696223233200000626295040 

noncomputable def Ns186p1683 := nat_lit 1224202282565613040846470509461845385287412932174690409778217216 

noncomputable def Ns186p1684 := nat_lit 89928472750264842752544008828910309495596313869170661263147713659136 

noncomputable def Ns186p1685 := BSN.sin_dyadic_bound_f 76909794 134217728 3 2 134217728 67108864 Ns186p1682 Ns186p111 Ns186p1683 Ns186p1684 Ns186p114 Ns186p1683 72769406 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 76909794) qz362 0 2 Ns186p1682 Ns186p111 Ns186p1683 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 76909794) qz363 0 2 Ns186p1684 Ns186p114 Ns186p1683 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1686 := nat_lit 8448368278388940052953686037219143266511326422672229326556703034509694585921803287848346959834860481136081 

noncomputable def Ns186p1687 := nat_lit 3677357878070950190510017701748342751685120723840009916085426703604116849271681651325033743850915281 

noncomputable def Ns186p1688 := nat_lit 42200818834562569231053491106061767862969490253826254888682250505288381812486030373958722556678502513100241 

noncomputable def Ns186p1689 := BSN.sin_dyadic_bound_f 198211109 134217728 4 3 134217728 67108864 Ns186p1686 Ns186p237 Ns186p1687 Ns186p1688 Ns186p240 Ns186p1687 133625083 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 198211109) qz362 0 3 Ns186p1686 Ns186p237 Ns186p1687 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 198211109) qz363 0 3 Ns186p1688 Ns186p240 Ns186p1687 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz794 := (BSN.cos_quad_nat1 85 rfl)

noncomputable def Ns186p1690 := Ns186p1637 93880 BSN.abs_quadSignPos (BSN.cos_quad_nat3 39 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 72769406 134217728) BSN.abs_quadSignNeg qz794 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133625083 134217728) qz207 rfl rfl (Ns186p1681 rfl rfl) (Ns186p1667 rfl) RS187to204.d27 RS187to204.d29 RS187to204.d31 RS187to204.d33 RS187to204.d17 (Ns186p1685 rfl rfl) (Ns186p1689 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns186p1691 := nat_lit 7163139369844265831001179680012651380135428176332906408474697542721 

noncomputable def Ns186p1692 := nat_lit 172618859802974813460266502130404670059299866523442179931647041 

noncomputable def Ns186p1693 := nat_lit 21489072871813191543376618507033693331066165929265672341064229334081 

noncomputable def Ns186p1694 := BSN.cos_dyadic_bound_f 60205481 134217728 3 2 134217728 67108864 Ns186p1691 Ns186p117 Ns186p1692 Ns186p1693 Ns186p120 Ns186p1692 120939569 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 60205481) qz364 0 2 Ns186p1691 Ns186p117 Ns186p1692 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 60205481) qz365 0 2 Ns186p1693 Ns186p120 Ns186p1692 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1695 := Ns186p1635 Bool.true 103624659 93880 Bool.true 60205481 7074237752028440 1 Bool.false 120939569 Bool.true Bool.true 146383250 104612 BSN.abs_quadSignNeg qz431 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 120939569 134217728) qz207 rfl (Ns186p1690 rfl) (Ns186p1667 rfl) RS187to204.d35 RS187to204.d37 RS187to204.d17 (Ns186p1694 rfl rfl) rfl 

noncomputable def Ns186p1696 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 8) 146383250 134217728 104612 134217728 146383250 134217728 104612 134217728 39294454464512000 73191625 33554432 26153 16777216 (Ns186p1695 rfl rfl rfl rfl) 

noncomputable def Ns186p1697 := @Enclosure.Real.IsNear.mulLit_ff qz790 (Zeta.RiemannSiegel.correction qz206) 5690917 16777216 1 16777216 1976211859933 4398046511104 46252845168347 549755813888000000 11246457669294328561 73786976294838206464 

noncomputable abbrev qz795 := (@HPow.hPow Real Real Real qz7 qz205 qz9)

noncomputable def Ns186p1698 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz795 1 1 0 1 5690917 16777216 1 16777216 5690917 16777216 1 16777216 

noncomputable def Ns186p1699 := @Enclosure.Real.IsNear.sqrt_image qz205 1267274014731 16777216000 474603 16777216000 72906313 72906341 8388608 (@Enclosure.Real.IsNear.of_eq qz205 (@HMul.hMul Real Real Real qz5 qz204 qz3) Bool.false 1267274014731 16777216000 474603 16777216000 (BSN.t_div_two_pi_mk qz204 474603 1000 qz207) (@Enclosure.Real.IsNear.mulLit_ff qz204 qz3 474603 1000 0 1 2670177 16777216 1 16777216 1267274014731 16777216000 474603 16777216000 (Enclosure.Real.IsNear.const Bool.false 474603 1000) RS187to204.d40 rfl)) 

noncomputable abbrev qz953 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 474603 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz796 := qz953

noncomputable abbrev qz556 := qz796

noncomputable abbrev qz209 := qz556

noncomputable def Ns186p1700 := @Enclosure.Real.IsNear.sqrt_image qz209 72906327 8388608 7 4194304 24730193 24730199 8388608 (@Enclosure.Real.IsNear.recentre' qz209 Bool.false 145812654 16777216 28 16777216 72906327 8388608 7 4194304 (Ns186p1699 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns186p1701 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz209) 6182549 2097152 3 8388608 2845458 2845459 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz209) Bool.false 49460392 16777216 6 16777216 6182549 2097152 3 8388608 (Ns186p1700 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns186p1702 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz209)) Bool.false 5690917 16777216 1 16777216 5690917 16777216 1 16777216 (Ns186p1701 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz210 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz550))

noncomputable abbrev qz797 := (@HMul.hMul Real Real Real qz891 qz952 qz952)

noncomputable abbrev qz557 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz797 qz789) qz640)

noncomputable abbrev qz211 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz557))

noncomputable def Ns186p1703 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz206) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz210) qz211) Bool.false 1976211859933 

noncomputable def Ns186p1704 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz210) qz211 1449821 524288 353 

noncomputable abbrev qz798 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz210))

noncomputable def Ns186p1705 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz210) (@Neg.neg Real Real.instNeg qz798) Bool.true 1449821 524288 353 4194304 (BSN.inv_eq_neg_inv_neg qz210) 

noncomputable def Ns186p1706 := @Enclosure.Real.IsNear.recentre' qz798 Bool.false 46394272 16777216 1412 16777216 1449821 524288 

noncomputable def Ns186p1707 := @Enclosure.Real.IsNear.recentre' qz210 Bool.true 6067020 16777216 415027216 37748736000000 1516755 4194304 25939201 2359296000000 

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz342 qz340 qz550)

noncomputable def Ns186p1708 := @Enclosure.Real.IsNear.cos_image qz212 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18213267) qz460) Bool.false 18213267 4194304 177 16777216 Bool.true 6067020 16777216 1 

noncomputable def Ns186p1709 := nat_lit 188902527888208232170952817 

noncomputable def Ns186p1710 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz206 884279719003555 140737488355328 1 500000000000000 5797463 8388608 7 4194304 5126578952573506980965 1180591620717411303424 Ns186p1709 

noncomputable def Ns186p1711 := @Enclosure.Real.IsNear.subLit_ff_p qz209 qz1 72906327 8388608 7 4194304 8 1 0 1 5797463 5797463 8388608 7 

noncomputable def Ns186p1712 := @Ns186p1711 4194304 (@Enclosure.Real.IsNear.recentre' qz209 Bool.false 145812654 16777216 28 16777216 72906327 8388608 7 4194304 (Ns186p1699 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns186p1713 := @Enclosure.Real.IsNear.recentre' qz212 Bool.false 5126578952573506980965 1180591620717411303424 Ns186p1709 Ns186p159 18213267 4194304 177 16777216 (@Ns186p1710 Ns186p159 RS187to204.d39 (Ns186p1712 rfl rfl) rfl) 

noncomputable def Ns186p1714 := nat_lit 6793778647089646227185958544500182211208786179860842809139462641756787970634228016033761 

noncomputable def Ns186p1715 := nat_lit 8397136110380039893641075620974032300177307549613679670508350285651879553618644774881 

noncomputable def Ns186p1716 := nat_lit 20364541669048178601770593482258598569026003924483301068077371224699060152795446758551521 

noncomputable def Ns186p1717 := BSN.cos_dyadic_bound_f 41258781627 34359738368 3 2 16777216 4504395 Ns186p1714 Ns186p851 Ns186p1715 Ns186p1716 Ns186p854 Ns186p1715 6067020 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 41258781627) qz371 0 2 Ns186p1714 Ns186p851 Ns186p1715 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 41258781627) qz372 0 2 Ns186p1716 Ns186p854 Ns186p1715 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1718 := @Ns186p1708 2250000 (Ns186p1713 rfl) (Enclosure.sfrac_false_div 18213267 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18213267) qz460) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 725832162362610033885184) qz752) 226375608064910080 72057594037927936 Bool.false 6067020 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 18213267 4194304 226375608064910080 72057594037927936 0 725832162362610033885184 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 6067020 16777216 725832162362610033885184 604462909807314587353088 41258781627 34359738368 4504395 4500000 (Ns186p1717 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p1719 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz210) 1516755 4194304 25939201 2359296000000 23196430 23197842 8388608 (@Enclosure.Real.IsNear.neg qz210 Bool.true 1516755 4194304 25939201 2359296000000 (Ns186p1707 (Ns186p1718 rfl rfl) rfl)) 

noncomputable def Ns186p1720 := Ns186p1705 (@Enclosure.Real.IsNear.neg qz798 Bool.false 1449821 524288 353 4194304 (@Ns186p1706 353 4194304 (Ns186p1719 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p1721 := @Enclosure.Real.IsNear.recentre' qz211 Bool.true 1363073 8388608 

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz342 qz340 qz557)

noncomputable def Ns186p1722 := @Enclosure.Real.IsNear.cos_image qz213 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7272969)) qz460) Bool.true 7272969 4194304 

noncomputable def Ns186p1723 := nat_lit 17172812753069690301315529645 

noncomputable def Ns186p1724 := nat_lit 943735683240291992206600466991039 

noncomputable def Ns186p1725 := @Enclosure.Real.IsNear.recentre' qz213 Bool.true Ns186p1723 Ns186p427 Ns186p1724 

noncomputable abbrev qz214 := qz557

noncomputable def Ns186p1726 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz214 884279719003555 140737488355328 1 500000000000000 19420113776239 

noncomputable abbrev qz558 := (@HSub.hSub Real Real Real qz633 qz797 qz789)

noncomputable abbrev qz215 := qz558

noncomputable def Ns186p1727 := @Enclosure.Real.IsNear.subLit_tf qz215 qz26 15022067265135 70368744177664 34971209 8796093022208 1 16 

noncomputable abbrev qz559 := qz797

noncomputable abbrev qz216 := qz559

noncomputable def Ns186p1728 := @Enclosure.Real.IsNear.subLit_ff_n qz216 qz206 33610577236369 70368744177664 20291145 8796093022208 5797463 8388608 7 4194304 

noncomputable def Ns186p1729 := @Enclosure.Real.IsNear.mulLit_ff qz206 qz206 5797463 8388608 7 4194304 5797463 8388608 7 4194304 33610577236369 70368744177664 

noncomputable def Ns186p1730 := nat_lit 5377550967835718865102514628906270135526391003192452475700257589599377509523456418492641 

noncomputable def Ns186p1731 := nat_lit 21904877938355453591802356312391560240162643933163196323207914445018417237872193761 

noncomputable def Ns186p1732 := nat_lit 32507283251665916951154038647308718898215519793970310608812428652038107073457281494528225 

noncomputable def Ns186p1733 := BSN.cos_dyadic_bound_t 7272969 4194304 4 3 8388608 2250000 Ns186p1730 Ns186p870 Ns186p1731 Ns186p1732 Ns186p873 Ns186p1731 1363073 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 7272969) (BSN.cosEvenQ 4194304) 0 3 Ns186p1730 Ns186p870 Ns186p1731 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 7272969) (BSN.cosOddQ 4194304) 0 3 Ns186p1732 Ns186p873 Ns186p1731 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1734 := @Ns186p1721 240444304 9437184000000 1363073 8388608 15027769 589824000000 (@Ns186p1722 105 4194304 Bool.true 1363073 8388608 1 2250000 (@Ns186p1725 Ns186p430 7272969 4194304 105 4194304 (@Ns186p1726 70368744177664 34971209 8796093022208 Ns186p1723 Ns186p427 Ns186p1724 Ns186p430 RS187to204.d39 (@Ns186p1727 0 1 310721820419824 19420113776239 70368744177664 34971209 8796093022208 (@Ns186p1728 126014233636849582080 15022067265135 70368744177664 34971209 8796093022208 (@Ns186p1729 20291145 8796093022208 (Ns186p1712 rfl rfl) (Ns186p1712 rfl rfl) rfl) (Ns186p1712 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7272969 4194304) (BSN.cos_neg_of_bound 7272969 4194304 Bool.true 1363073 8388608 1 2250000 (Ns186p1733 rfl rfl)) rfl rfl) 

noncomputable def Ns186p1735 := @Ns186p1697 131734087801125298773 Ns186p1632 (Ns186p1698 qz28 (@Enclosure.Real.IsNear.of_eq qz795 (@Inv.inv Real Real.instInv (Real.sqrt qz209)) Bool.false 5690917 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz205 (BSN.t_div_two_pi_nonneg qz204 474603 1000 qz207)) Ns186p1702) rfl) (@Ns186p1703 4398046511104 46252845168347 549755813888000000 (BSN.correction_mk qz206 (BSN.cos_two_pi_p_ne_zero_mk qz204 474603 1000 8 qz207 rfl rfl (@BSN.floor_sqrt_eq_dec qz204 474603 1000 8 qz207 rfl rfl rfl))) (@Ns186p1704 4194304 1363073 8388608 15027769 589824000000 1976211859933 4398046511104 46252845168347 549755813888000000 Ns186p1720 (Ns186p1734 rfl) rfl)) 

noncomputable def Ns186p1736 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz204) (hardyZApproximantRS₀ qz204) Bool.true 172196543155935480561 73786976294838206464 7320615988107557298773 Ns186p1632 (@Eq.refl Real (hardyZApproximantRS₀ qz204)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz204) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 8) (@HMul.hMul Real Real Real qz5 qz790 (Zeta.RiemannSiegel.correction qz206))) Bool.true 172196543155935480561 73786976294838206464 7320615988107557298773 Ns186p1632 (BSN.hardyZApproximantRS₀_eq qz204 8 (@BSN.floor_sqrt_eq_dec qz204 474603 1000 8 qz207 rfl rfl rfl)) (@Ns186p1634 172196543155935480561 73786976294838206464 7320615988107557298773 Ns186p1632 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 8)) Bool.true 73191625 33554432 26153 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz204) qz204 8) (Ns186p1696 (Ns186p1695 rfl rfl rfl rfl) rfl rfl)) (Ns186p1735 rfl) rfl rfl)) 

theorem RS187to204.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz204) Bool.true 172196543155935480561 73786976294838206464 7320615988107557298773 Ns186p1632 := Ns186p1736 

noncomputable def Ns186p1737 := nat_lit 13835058055282163712000000 

noncomputable def Ns186p1738 := nat_lit 619411857432409155922034688 

noncomputable abbrev qz954 := (Enclosure.sfrac Bool.false 476055 1000)

noncomputable abbrev qz799 := qz954

noncomputable abbrev qz560 := qz799

noncomputable abbrev qz217 := qz560

noncomputable abbrev qz955 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 476055 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz800 := qz955

noncomputable abbrev qz561 := qz800

noncomputable abbrev qz218 := qz561

noncomputable abbrev qz956 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 476055 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz801 := qz956

noncomputable abbrev qz562 := qz801

noncomputable abbrev qz219 := qz562

noncomputable abbrev qz802 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz218 qz9))

noncomputable def Ns186p1739 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz217) qz217 8) (@HMul.hMul Real Real Real qz5 qz802 (Zeta.RiemannSiegel.correction qz219)) 77605821 67108864 104935 67108864 1436106888594448245 9223372036854775808 511286294323928353481 Ns186p1737 Ns186p1738 

noncomputable def Ns186p1740 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz217) qz217 Real.cos BSN.quadSignNeg 7 8 476055 1000 126 134217728 67108864 2251799813685248 Bool.false 106257633379 1856 279097919 60 47453128 8 

noncomputable def Ns186p1741 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz217) qz217 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 476055 1000 39 85 134217728 67108864 2251799813685248 Bool.false 106257633379 1856 

noncomputable def Ns186p1742 := Ns186p1741 240485871 61 54794152 8 261175631 61 50729528 8 Bool.false 167224715 69860 Bool.true 4548088 Bool.true 155890935 7074237752028440 1 Bool.false 4547217 Bool.false Bool.false 123130312 Bool.true Bool.false 122542229 

noncomputable def Ns186p1743 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz217) qz217 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 476055 1000 83 16 134217728 67108864 2251799813685248 Bool.false 106257633379 1856 

noncomputable def Ns186p1744 := Ns186p1743 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 45687873 41026 Bool.false 181550852 Bool.false 49311235 7074237752028440 1 Bool.false 131037076 Bool.false Bool.false 125260755 Bool.false Bool.false 167224715 

noncomputable def Ns186p1745 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz217) qz217 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 476055 1000 293 171 134217728 67108864 2251799813685248 Bool.false 106257633379 1856 

noncomputable def Ns186p1746 := Ns186p1745 93032624 60 94906264 8 147453232 60 77490640 16 Bool.false 134217720 1924 Bool.false 196174319 Bool.false 10074902 7074237752028440 1 Bool.false 133418511 Bool.true Bool.false 10065443 Bool.false Bool.false 45687873 

noncomputable def Ns186p1747 := nat_lit 2124830120809632207517698334174592293557378489425947 

noncomputable def Ns186p1748 := nat_lit 2683947139893032423892191418717391591733775564800 

noncomputable def Ns186p1749 := nat_lit 11736216315375721976893576500000000 

noncomputable def Ns186p1750 := nat_lit 33522524005343406781939511974245000000 

noncomputable abbrev qz803 := (@Eq.refl Real qz954)

noncomputable abbrev qz563 := qz803

noncomputable abbrev qz220 := qz563

noncomputable def Ns186p1751 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz217 476055 1000 906514452100 16000000 952110 4000 2000 Ns186p1749 Ns186p1750 qz220 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns186p1752 := nat_lit 95617355436433449338296425037856653210082032024167615000000 

noncomputable abbrev qz804 := (Real.log (Enclosure.sfrac Bool.false 906514452100 16000000))

noncomputable abbrev qz221 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 476055 4000) qz804) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 952110))))))

noncomputable abbrev qz805 := (Enclosure.sfrac Bool.false 476055 2000)

noncomputable abbrev qz564 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz221 qz805) (@HMul.hMul Real Real Real qz5 qz805 (Real.log Real.pi)))

noncomputable def Ns186p1753 := @Enclosure.Real.IsNear.addLit_ft_p qz564 (Enclosure.sfrac Bool.true Ns186p1749 Ns186p1750) 2852332888340025177427 3602879701896396800 10186820951835899 737280000000000000000 Ns186p1749 Ns186p1750 0 1 Ns186p1752 

noncomputable def Ns186p1754 := nat_lit 38283363977267587077704882585600 

noncomputable abbrev qz565 := (@HSub.hSub Real Real Real qz12 qz221 qz805)

noncomputable abbrev qz566 := (@HMul.hMul Real Real Real qz5 qz805 (Real.log Real.pi))

noncomputable def Ns186p1755 := @Enclosure.Real.IsNear.subLit_ff_p qz565 qz566 3834035432992972862803 3602879701896396800 9681102570877 1440000000000000000 3657126965571 13421772800 95211 13421772800 Ns186p1754 2852332888340025177427 3602879701896396800 

noncomputable def Ns186p1756 := nat_lit 1533614173197189145121200 

noncomputable abbrev qz567 := qz805

noncomputable def Ns186p1757 := @Enclosure.Real.IsNear.subLit_ff_p qz221 qz567 938323976247223490423 720575940379279360 9681102570877 1440000000000000000 476055 2000 0 1 Ns186p1756 3834035432992972862803 3602879701896396800 9681102570877 1440000000000000000 

noncomputable def Ns186p1758 := nat_lit 2112917754889898925579176093264379904 

noncomputable def Ns186p1759 := nat_lit 26462838611393332201390080 

noncomputable def Ns186p1760 := nat_lit 9947729221324116211764259456563189917619060219585255002687892646403172916109640150670547530687551191884843024249938714862721535000000000000000000000000 

noncomputable def Ns186p1761 := nat_lit 247317669318954102158636446578992202176704284855060473504481645440314772769034991904470250243405819501366362691167176152175152000000000000000000000000 

noncomputable def Ns186p1762 := nat_lit 101081892548349319566570699024786443575062923868480781222705399619308900458250573382611277696637783344598468344235963195000000000000000000000000 

noncomputable def Ns186p1763 := BSN.log_dyadic_bound 382226452100 1430802452100 7 6 Ns186p1760 67108864 18000000 Ns186p1761 Ns186p1762 36746520 1813028904200 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 382226452100) (BSN.artanhQ 1430802452100) 0 6 Ns186p1761 Ns186p1760 Ns186p1762 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns186p1764 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 476055 4000) qz804 476055 4000 0 1 49290877974393465 4503599627370496 100000027 1800000000000000 938606756563995239223 720575940379279360 1057900285633 160000000000000000 (Enclosure.Real.IsNear.const Bool.false 476055 4000) (BSN.isNear_log_sfrac 906514452100 16000000 49290877974393465 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 906514452100) qz353)) Bool.false Ns186p1759 Ns186p89 1000000270000000 18000000000000000000000 49290877974393465 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 906514452100 16000000 15 1813028904200 1048576000000 36746520 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns186p1763 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p1765 := BSN.arctan_dyadic_bound_f 1000 952110 1 0 8388608 2250000 0 1 1 0 1 1 8810 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 952110) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 952110) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz806 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 952110)))

noncomputable def Ns186p1766 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz806 884279719003555 562949953421312 1 2000000000000000 8810 8388608 1 2250000 7412916335981331742720 883688489911715 562949953421312 8000000009 18000000000000000 qz16 (Ns186p1765 rfl) rfl rfl 

noncomputable def Ns186p1767 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 476055 4000) qz804) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz806)) 938606756563995239223 720575940379279360 1057900285633 160000000000000000 883688489911715 2251799813685248 8000000009 72000000000000000 Ns186p1758 938323976247223490423 720575940379279360 9681102570877 1440000000000000000 (Ns186p1764 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz806) 1 4 0 1 883688489911715 562949953421312 8000000009 18000000000000000 883688489911715 2251799813685248 8000000009 72000000000000000 qz356 Ns186p1766 rfl) 

noncomputable def Ns186p1768 := @Ns186p1753 Ns186p1747 Ns186p1748 10186820951835899 737280000000000000000 (@Ns186p1755 10186820951835899 737280000000000000000 (Ns186p1757 (Ns186p1767 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 476055 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz567 (Real.log Real.pi) 476055 2000 0 1 38410761 33554432 1 33554432 3657126965571 13421772800 95211 13421772800 (Enclosure.Real.IsNear.const Bool.false 476055 2000) RS187to204.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns186p1749 Ns186p1750) 

noncomputable def Ns186p1769 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz217) Bool.false Ns186p1747 Ns186p1748 10186820951835899 737280000000000000000 3320551043 4194304 233 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz217) (@HAdd.hAdd Real Real Real qz357 qz564 (Enclosure.sfrac Bool.true Ns186p1749 Ns186p1750)) Bool.false Ns186p1747 Ns186p1748 10186820951835899 737280000000000000000 Ns186p1751 (Ns186p1768 rfl rfl)) 

noncomputable def Ns186p1770 := nat_lit 856509619518100376888212650942109343934687519558982866318201609432502090905726852741947900224766786349532461551208422698405753409605201 

noncomputable def Ns186p1771 := nat_lit 609654465588074256866590462264268229611845003488995864088695323314139240470173951522911460393004789324354366841373825705070661201 

noncomputable def Ns186p1772 := nat_lit 4277230387941710172479071735932560099216179336532567823417498313936229159904810506350030851762169346201070398096596659673591590005870161 

noncomputable def Ns186p1773 := BSN.sin_dyadic_bound_f 53962282757 34359738368 4 3 16777216 4504395 Ns186p1770 Ns186p102 Ns186p1771 Ns186p1772 Ns186p105 Ns186p1771 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53962282757) qz358 0 3 Ns186p1770 Ns186p102 Ns186p1771 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53962282757) qz359 0 3 Ns186p1772 Ns186p105 Ns186p1771 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1774 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz217) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3320551043) qz460) Bool.false 3320551043 4194304 233 16777216 Bool.false 16777215 16777216 1 2250000 (Ns186p1769 rfl) (Enclosure.sfrac_false_div 3320551043 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3320551043) qz460) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949314517654820970561536) qz752) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 125 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q3 3320551043 4194304 226375608064910080 72057594037927936 125 949314517654820970561536 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 949314517654820970561536 604462909807314587353088 53962282757 34359738368 4504395 4500000 (Ns186p1773 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p1775 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz217) Bool.false Ns186p1747 Ns186p1748 10186820951835899 737280000000000000000 106257633379 134217728 1856 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz217) (@HAdd.hAdd Real Real Real qz357 qz564 (Enclosure.sfrac Bool.true Ns186p1749 Ns186p1750)) Bool.false Ns186p1747 Ns186p1748 10186820951835899 737280000000000000000 Ns186p1751 (Ns186p1768 rfl rfl)) 

noncomputable def Ns186p1776 := Ns186p1746 41026 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 293 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133418511 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 171 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 10065443 134217728) qz220 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz217) qz217 1) Bool.false 16777215 16777216 33814201 2359296000000 134217720 134217728 1924 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz217) qz217 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz217)) Bool.false 16777215 16777216 33814201 2359296000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz217) qz217) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz217)) Bool.false 16777215 16777216 541027216 37748736000000 16777215 16777216 33814201 2359296000000 (Ns186p1774 rfl rfl) rfl)) rfl) (Ns186p1775 rfl) RS187to204.d7 

noncomputable def Ns186p1777 := nat_lit 8105911660064730961836945517977640157454211354156682146438763987013973022206835237661463679862480103008961 

noncomputable def Ns186p1778 := nat_lit 3248671841191295273837969104421445666214757115320686719783850645571675536696345444948242334646266561 

noncomputable def Ns186p1779 := nat_lit 40491789801251139176661569713091821942578163882926822700294034126163526799945782895984992535586001719126721 

noncomputable def Ns186p1780 := BSN.sin_dyadic_bound_f 196174319 134217728 4 3 134217728 67108864 Ns186p1777 Ns186p237 Ns186p1778 Ns186p1779 Ns186p240 Ns186p1778 133418511 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 196174319) qz362 0 3 Ns186p1777 Ns186p237 Ns186p1778 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 196174319) qz363 0 3 Ns186p1779 Ns186p240 Ns186p1778 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1781 := nat_lit 10302991026174372205054636816 

noncomputable def Ns186p1782 := BSN.sin_dyadic_bound_f 10074902 134217728 2 1 134217728 67108864 Ns186p1781 Ns186p123 Ns186p1781 Ns186p1781 Ns186p124 Ns186p1781 10065443 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 10074902) qz362 0 1 Ns186p1781 Ns186p123 Ns186p1781 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 10074902) qz363 0 1 Ns186p1781 Ns186p124 Ns186p1781 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1783 := nat_lit 5943632075364438866957525493886903525370189685994369760066350288207049202622811925127100357657220974903296 

noncomputable def Ns186p1784 := nat_lit 1282270043173402436545419660779399772318958367965311212698147605433617031556548227987907585503133696 

noncomputable def Ns186p1785 := nat_lit 29697839660622179329216436145457321582782160730406943727359470053660358518206084510398419601200535102816256 

noncomputable def Ns186p1786 := BSN.sin_dyadic_bound_f 181550852 134217728 4 3 134217728 67108864 Ns186p1783 Ns186p237 Ns186p1784 Ns186p1785 Ns186p240 Ns186p1784 131037076 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 181550852) qz362 0 3 Ns186p1783 Ns186p237 Ns186p1784 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 181550852) qz363 0 3 Ns186p1785 Ns186p240 Ns186p1784 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1787 := nat_lit 3223569527231997400736541198289929470732828991572215476408548190625 

noncomputable def Ns186p1788 := nat_lit 34959646825404621703256581185378016943618794054194660375390625 

noncomputable def Ns186p1789 := nat_lit 9670638662402341392966217081707417656164599737128538039904893790625 

noncomputable def Ns186p1790 := BSN.cos_dyadic_bound_f 49311235 134217728 3 2 134217728 67108864 Ns186p1787 Ns186p117 Ns186p1788 Ns186p1789 Ns186p120 Ns186p1788 125260755 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 49311235) qz364 0 2 Ns186p1787 Ns186p117 Ns186p1788 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 49311235) qz365 0 2 Ns186p1789 Ns186p120 Ns186p1788 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1791 := Ns186p1744 69860 BSN.abs_quadSignPos (BSN.cos_quad_nat3 83 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131037076 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 16 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 125260755 134217728) qz220 rfl rfl (Ns186p1776 RS187to204.d9 RS187to204.d11 RS187to204.d13 RS187to204.d17 (Ns186p1780 rfl rfl) (Ns186p1782 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns186p1775 rfl) RS187to204.d19 RS187to204.d21 RS187to204.d23 RS187to204.d25 RS187to204.d17 (Ns186p1786 rfl rfl) (Ns186p1790 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns186p1792 := BSN.sin_dyadic_bound_f 4548088 134217728 1 0 134217728 67108864 0 1 1 0 1 1 4547217 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 4548088) qz362 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 4548088) qz363 0 0 rfl) rfl rfl 

noncomputable def Ns186p1793 := nat_lit 579917282673822250987867579884849665775353132921745229295796388130625 

noncomputable def Ns186p1794 := nat_lit 348792304879902961709573018612670626094611998498820385302937890625 

noncomputable def Ns186p1795 := nat_lit 1518266267080681290649266257668280991255105023940334653246119117090625 

noncomputable def Ns186p1796 := BSN.sin_dyadic_bound_f 155890935 134217728 3 2 134217728 67108864 Ns186p1793 Ns186p111 Ns186p1794 Ns186p1795 Ns186p114 Ns186p1794 123130312 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 155890935) qz362 0 2 Ns186p1793 Ns186p111 Ns186p1794 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 155890935) qz363 0 2 Ns186p1795 Ns186p114 Ns186p1794 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1797 := Ns186p1742 94170 BSN.abs_quadSignPos (BSN.cos_quad_nat3 39 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 4547217 134217728) BSN.abs_quadSignNeg qz794 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 123130312 134217728) qz220 rfl rfl (Ns186p1791 rfl rfl) (Ns186p1775 rfl) RS187to204.d27 RS187to204.d29 RS187to204.d31 RS187to204.d33 RS187to204.d17 (Ns186p1792 rfl rfl) (Ns186p1796 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns186p1798 := nat_lit 3717005276255123164821081929521 

noncomputable def Ns186p1799 := BSN.cos_dyadic_bound_f 43908469 134217728 2 1 134217728 67108864 Ns186p1798 Ns186p134 Ns186p1798 Ns186p1798 Ns186p135 Ns186p1798 127099367 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 43908469) qz364 0 1 Ns186p1798 Ns186p134 Ns186p1798 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 43908469) qz365 0 1 Ns186p1798 Ns186p135 Ns186p1798 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1800 := Ns186p1740 Bool.false 122542229 94170 Bool.true 43908469 7074237752028440 1 Bool.false 127099367 Bool.true Bool.false 77605821 104935 BSN.abs_quadSignNeg qz431 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 127099367 134217728) qz220 rfl (Ns186p1797 rfl) (Ns186p1775 rfl) RS187to204.d35 RS187to204.d37 RS187to204.d17 (Ns186p1799 rfl rfl) rfl 

noncomputable def Ns186p1801 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz217) qz217 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz217) qz217 8) 77605821 134217728 104935 134217728 77605821 134217728 104935 134217728 20832153948389376 77605821 67108864 104935 67108864 (Ns186p1800 rfl rfl rfl rfl) 

noncomputable def Ns186p1802 := @Enclosure.Real.IsNear.mulLit_ff qz802 (Zeta.RiemannSiegel.correction qz219) 1421643 4194304 1 8388608 1010174065215 2199023255552 179555797137263 1649267441664000000 1436106888594448245 9223372036854775808 

noncomputable abbrev qz807 := (@HPow.hPow Real Real Real qz7 qz218 qz9)

noncomputable def Ns186p1803 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz807 1 1 0 1 1421643 4194304 1 8388608 1421643 4194304 1 8388608 

noncomputable def Ns186p1804 := @Enclosure.Real.IsNear.sqrt_image qz218 254230222347 3355443200 95211 3355443200 73017752 73017780 8388608 (@Enclosure.Real.IsNear.of_eq qz218 (@HMul.hMul Real Real Real qz5 qz217 qz3) Bool.false 254230222347 3355443200 95211 3355443200 (BSN.t_div_two_pi_mk qz217 476055 1000 qz220) (@Enclosure.Real.IsNear.mulLit_ff qz217 qz3 476055 1000 0 1 2670177 16777216 1 16777216 254230222347 3355443200 95211 3355443200 (Enclosure.Real.IsNear.const Bool.false 476055 1000) RS187to204.d40 rfl)) 

noncomputable abbrev qz957 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 476055 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz808 := qz957

noncomputable abbrev qz568 := qz808

noncomputable abbrev qz222 := qz568

noncomputable def Ns186p1805 := @Enclosure.Real.IsNear.sqrt_image qz222 36508883 4194304 7 4194304 24749086 24749092 8388608 (@Enclosure.Real.IsNear.recentre' qz222 Bool.false 146035532 16777216 28 16777216 36508883 4194304 7 4194304 (Ns186p1804 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns186p1806 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz222) 24749089 8388608 3 8388608 2843285 2843287 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz222) Bool.false 49498178 16777216 6 16777216 24749089 8388608 3 8388608 (Ns186p1805 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns186p1807 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz222)) Bool.false 5686572 16777216 2 16777216 1421643 4194304 1 8388608 (Ns186p1806 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz223 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz562))

noncomputable abbrev qz809 := (@HMul.hMul Real Real Real qz891 qz956 qz956)

noncomputable abbrev qz569 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz809 qz801) qz640)

noncomputable abbrev qz224 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz569))

noncomputable def Ns186p1808 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz219) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz223) qz224) Bool.false 1010174065215 

noncomputable def Ns186p1809 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz223) qz224 1855011 524288 1155 

noncomputable abbrev qz810 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz223))

noncomputable def Ns186p1810 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz223) (@Neg.neg Real Real.instNeg qz810) Bool.true 1855011 524288 1155 8388608 (BSN.inv_eq_neg_inv_neg qz223) 

noncomputable def Ns186p1811 := @Enclosure.Real.IsNear.recentre' qz810 Bool.false 59360352 16777216 2310 16777216 1855011 524288 

noncomputable def Ns186p1812 := @Enclosure.Real.IsNear.recentre' qz223 Bool.true 4741801 16777216 415027216 37748736000000 4741801 16777216 25939201 2359296000000 

noncomputable abbrev qz225 := (@HMul.hMul Real Real Real qz342 qz340 qz562)

noncomputable def Ns186p1813 := @Enclosure.Real.IsNear.cos_image qz225 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18563363) qz460) Bool.false 18563363 4194304 177 16777216 Bool.true 4741801 16777216 1 

noncomputable def Ns186p1814 := nat_lit 188902527888686859031451761 

noncomputable def Ns186p1815 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz219 884279719003555 140737488355328 1 500000000000000 2954451 4194304 7 4194304 2612561100089772073305 590295810358705651712 Ns186p1814 

noncomputable def Ns186p1816 := @Enclosure.Real.IsNear.subLit_ff_p qz222 qz1 36508883 4194304 7 4194304 8 1 0 1 2954451 2954451 4194304 7 

noncomputable def Ns186p1817 := @Ns186p1816 4194304 (@Enclosure.Real.IsNear.recentre' qz222 Bool.false 146035532 16777216 28 16777216 36508883 4194304 7 4194304 (Ns186p1804 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns186p1818 := @Enclosure.Real.IsNear.recentre' qz225 Bool.false 2612561100089772073305 590295810358705651712 Ns186p1814 Ns186p159 18563363 4194304 177 16777216 (@Ns186p1815 Ns186p159 RS187to204.d39 (Ns186p1817 rfl rfl) rfl) 

noncomputable def Ns186p1819 := nat_lit 8892416466906544358105594249070014754609098968065571762431027095617025975318452127608801 

noncomputable def Ns186p1820 := nat_lit 14375301412408854484885575309693603751363036163648522517020292944576052505211869540321 

noncomputable def Ns186p1821 := nat_lit 26648498797894815365347011596590657056324570831869418242259040700961925820944932643745761 

noncomputable def Ns186p1822 := BSN.cos_dyadic_bound_f 44126768059 34359738368 3 2 16777216 4504395 Ns186p1819 Ns186p851 Ns186p1820 Ns186p1821 Ns186p854 Ns186p1820 4741801 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 44126768059) qz371 0 2 Ns186p1819 Ns186p851 Ns186p1820 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 44126768059) qz372 0 2 Ns186p1821 Ns186p854 Ns186p1820 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1823 := @Ns186p1813 2250000 (Ns186p1818 rfl) (Enclosure.sfrac_false_div 18563363 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18563363) qz460) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 776286313247214871248896) qz752) 226375608064910080 72057594037927936 Bool.false 4741801 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 18563363 4194304 226375608064910080 72057594037927936 0 776286313247214871248896 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 4741801 16777216 776286313247214871248896 604462909807314587353088 44126768059 34359738368 4504395 4500000 (Ns186p1822 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p1824 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz223) 4741801 16777216 25939201 2359296000000 29679021 29681331 8388608 (@Enclosure.Real.IsNear.neg qz223 Bool.true 4741801 16777216 25939201 2359296000000 (Ns186p1812 (Ns186p1823 rfl rfl) rfl)) 

noncomputable def Ns186p1825 := Ns186p1810 (@Enclosure.Real.IsNear.neg qz810 Bool.false 1855011 524288 1155 8388608 (@Ns186p1811 1155 8388608 (Ns186p1824 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p1826 := @Enclosure.Real.IsNear.recentre' qz224 Bool.true 1089130 8388608 

noncomputable abbrev qz226 := (@HMul.hMul Real Real Real qz342 qz340 qz569)

noncomputable def Ns186p1827 := @Enclosure.Real.IsNear.cos_image qz226 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 14269007)) qz429) Bool.true 14269007 8388608 

noncomputable def Ns186p1828 := nat_lit 4211467550880506813184167845 

noncomputable def Ns186p1829 := nat_lit 381704495056469843255029351620473 

noncomputable def Ns186p1830 := @Enclosure.Real.IsNear.recentre' qz226 Bool.true Ns186p1828 Ns186p171 Ns186p1829 

noncomputable abbrev qz227 := qz569

noncomputable def Ns186p1831 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz227 884279719003555 140737488355328 1 500000000000000 4762596563479 

noncomputable abbrev qz570 := (@HSub.hSub Real Real Real qz633 qz809 qz801)

noncomputable abbrev qz228 := qz570

noncomputable def Ns186p1832 := @Enclosure.Real.IsNear.subLit_tf qz228 qz26 3663084935703 17592186044416 70722491 17592186044416 1 16 

noncomputable abbrev qz571 := qz809

noncomputable abbrev qz229 := qz571

noncomputable def Ns186p1833 := @Enclosure.Real.IsNear.subLit_ff_n qz229 qz219 8728780711401 17592186044416 41362363 17592186044416 2954451 4194304 7 4194304 

noncomputable def Ns186p1834 := @Enclosure.Real.IsNear.mulLit_ff qz219 qz219 2954451 4194304 7 4194304 2954451 4194304 7 4194304 8728780711401 17592186044416 

noncomputable def Ns186p1835 := nat_lit 20388263463675689048653811011424083288345619887095961560450413709324388377771864353313814081 

noncomputable def Ns186p1836 := nat_lit 71240180658989153552353949888551883542908895859846352017012730983874986227996065691201 

noncomputable def Ns186p1837 := nat_lit 123279567699415138306082140022163449038914830587137342453696084329054135041199914902141171265 

noncomputable def Ns186p1838 := BSN.cos_dyadic_bound_t 14269007 8388608 4 3 8388608 2250000 Ns186p1835 Ns186p754 Ns186p1836 Ns186p1837 Ns186p757 Ns186p1836 1089130 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 14269007) (BSN.cosEvenQ 8388608) 0 3 Ns186p1835 Ns186p754 Ns186p1836 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 14269007) (BSN.cosOddQ 8388608) 0 3 Ns186p1837 Ns186p757 Ns186p1836 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1839 := @Ns186p1826 121347152 4718592000000 544565 4194304 7584197 294912000000 (@Ns186p1827 53 2097152 Bool.true 1089130 8388608 1 2250000 (@Ns186p1830 Ns186p174 14269007 8388608 53 2097152 (@Ns186p1831 17592186044416 70722491 17592186044416 Ns186p1828 Ns186p171 Ns186p1829 Ns186p174 RS187to204.d39 (@Ns186p1832 0 1 76201545015664 4762596563479 17592186044416 70722491 17592186044416 (@Ns186p1833 15364091798158835712 3663084935703 17592186044416 70722491 17592186044416 (@Ns186p1834 41362363 17592186044416 (Ns186p1817 rfl rfl) (Ns186p1817 rfl rfl) rfl) (Ns186p1817 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 14269007 8388608) (BSN.cos_neg_of_bound 14269007 8388608 Bool.true 1089130 8388608 1 2250000 (Ns186p1838 rfl rfl)) rfl rfl) 

noncomputable def Ns186p1840 := @Ns186p1802 511286294323928353481 Ns186p1737 (Ns186p1803 qz28 (@Enclosure.Real.IsNear.of_eq qz807 (@Inv.inv Real Real.instInv (Real.sqrt qz222)) Bool.false 1421643 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz218 (BSN.t_div_two_pi_nonneg qz217 476055 1000 qz220)) Ns186p1807) rfl) (@Ns186p1808 2199023255552 179555797137263 1649267441664000000 (BSN.correction_mk qz219 (BSN.cos_two_pi_p_ne_zero_mk qz217 476055 1000 8 qz220 rfl rfl (@BSN.floor_sqrt_eq_dec qz217 476055 1000 8 qz220 rfl rfl rfl))) (@Ns186p1809 8388608 544565 4194304 7584197 294912000000 1010174065215 2199023255552 179555797137263 1649267441664000000 Ns186p1825 (Ns186p1839 rfl) rfl)) 

noncomputable def Ns186p1841 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz217) (hardyZApproximantRS₀ qz217) Bool.false 9229955932980912267 9223372036854775808 22144521168200408353481 Ns186p1737 (@Eq.refl Real (hardyZApproximantRS₀ qz217)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz217) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz217) qz217 8) (@HMul.hMul Real Real Real qz5 qz802 (Zeta.RiemannSiegel.correction qz219))) Bool.false 9229955932980912267 9223372036854775808 22144521168200408353481 Ns186p1737 (BSN.hardyZApproximantRS₀_eq qz217 8 (@BSN.floor_sqrt_eq_dec qz217 476055 1000 8 qz220 rfl rfl rfl)) (@Ns186p1739 9229955932980912267 9223372036854775808 22144521168200408353481 Ns186p1737 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz217) qz217 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz217) qz217 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz217) qz217 8)) Bool.false 77605821 67108864 104935 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz217) qz217 8) (Ns186p1801 (Ns186p1800 rfl rfl rfl rfl) rfl rfl)) (Ns186p1840 rfl) rfl rfl)) 

theorem RS187to204.d58 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz217) Bool.false 9229955932980912267 9223372036854775808 22144521168200408353481 Ns186p1737 := Ns186p1841 

noncomputable def Ns186p1842 := nat_lit 880940277819613378376630272 

noncomputable abbrev qz958 := (Enclosure.sfrac Bool.false 477779 1000)

noncomputable abbrev qz811 := qz958

noncomputable abbrev qz572 := qz811

noncomputable abbrev qz230 := qz572

noncomputable abbrev qz959 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 477779 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz812 := qz959

noncomputable abbrev qz573 := qz812

noncomputable abbrev qz231 := qz573

noncomputable abbrev qz960 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 477779 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz813 := qz960

noncomputable abbrev qz574 := qz813

noncomputable abbrev qz232 := qz574

noncomputable abbrev qz814 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz231 qz9))

noncomputable def Ns186p1843 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz230) qz230 8) (@HMul.hMul Real Real Real qz5 qz814 (Zeta.RiemannSiegel.correction qz232)) 18511259 33554432 52657 33554432 5900721648612862137 36893488147419103232 525220494517596701307 Ns186p1089 Ns186p1842 

noncomputable def Ns186p1844 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz230) qz230 Real.cos BSN.quadSignNeg 7 8 477779 1000 126 134217728 67108864 2251799813685248 Bool.false 106758533598 1862 279097919 60 47453128 8 

noncomputable def Ns186p1845 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz230) qz230 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 477779 1000 38 85 134217728 67108864 2251799813685248 Bool.false 106758533598 1862 

noncomputable def Ns186p1846 := Ns186p1845 240485871 61 54794152 8 261175631 61 50729528 8 Bool.false 76842494 70112 Bool.true 129074225 Bool.true 105257504 7074237752028440 1 Bool.false 76791954 Bool.true Bool.false 94795288 Bool.true Bool.false 9663065 

noncomputable def Ns186p1847 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz230) qz230 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 477779 1000 84 16 134217728 67108864 2251799813685248 Bool.false 106758533598 1862 

noncomputable def Ns186p1848 := Ns186p1847 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 33217850 41174 Bool.false 150845842 Bool.false 177801442 7074237752028440 1 Bool.false 58006026 Bool.false Bool.false 32694970 Bool.false Bool.false 76842494 

noncomputable def Ns186p1849 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz230) qz230 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 477779 1000 295 172 134217728 67108864 2251799813685248 Bool.false 106758533598 1862 

noncomputable def Ns186p1850 := Ns186p1849 93032624 60 94906264 8 147453232 60 77490640 16 Bool.true 111518184 1932 Bool.false 115028866 Bool.false 45937035 7074237752028440 1 Bool.false 101455541 Bool.false Bool.false 126433017 Bool.false Bool.false 33217850 

noncomputable def Ns186p1851 := nat_lit 1533976695721601014976876424016910231144436542443984906571 

noncomputable def Ns186p1852 := nat_lit 1928528427331167149085190575755747605744856938315776000 

noncomputable def Ns186p1853 := nat_lit 11950270281896438983651195951520000 

noncomputable def Ns186p1854 := nat_lit 34257546618675276823132779493543644480 

noncomputable abbrev qz815 := (@Eq.refl Real qz958)

noncomputable abbrev qz575 := qz815

noncomputable abbrev qz233 := qz575

noncomputable def Ns186p1855 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz230 477779 1000 913092091364 16000000 955558 4000 2000 Ns186p1853 Ns186p1854 qz233 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns186p1856 := nat_lit 490872542630912324792600455685411273966219693582075170102720 

noncomputable abbrev qz816 := (Real.log (Enclosure.sfrac Bool.false 913092091364 16000000))

noncomputable abbrev qz234 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 477779 4000) qz816) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 955558))))))

noncomputable abbrev qz817 := (Enclosure.sfrac Bool.false 477779 2000)

noncomputable abbrev qz576 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz234 qz817) (@HMul.hMul Real Real Real qz5 qz817 (Real.log Real.pi)))

noncomputable def Ns186p1857 := @Enclosure.Real.IsNear.addLit_ft_p qz576 (Enclosure.sfrac Bool.true Ns186p1853 Ns186p1854) 14328894108261897974139 18014398509481984000 51117075731449571 3686400000000000000000 Ns186p1853 Ns186p1854 0 1 Ns186p1856 

noncomputable def Ns186p1858 := nat_lit 961595805981748987528369668096000 

noncomputable abbrev qz577 := (@HSub.hSub Real Real Real qz12 qz234 qz817)

noncomputable abbrev qz578 := (@HMul.hMul Real Real Real qz5 qz817 (Real.log Real.pi))

noncomputable def Ns186p1859 := @Enclosure.Real.IsNear.subLit_ff_p qz577 qz578 19255182668215482036603 18014398509481984000 48577912900933 7200000000000000000 18351854979819 67108864000 477779 67108864000 Ns186p1858 14328894108261897974139 18014398509481984000 

noncomputable def Ns186p1860 := nat_lit 38510365336430964073206000 

noncomputable abbrev qz579 := qz817

noncomputable def Ns186p1861 := @Enclosure.Real.IsNear.subLit_ff_p qz234 qz579 23558633320946378453371 18014398509481984000 48577912900933 7200000000000000000 477779 2000 0 1 Ns186p1860 19255182668215482036603 18014398509481984000 48577912900933 7200000000000000000 

noncomputable def Ns186p1862 := nat_lit 53049326122786130350239910962038571008 

noncomputable def Ns186p1863 := nat_lit 26480319099159790158348288 

noncomputable def Ns186p1864 := nat_lit 10510596154437218763090833085851554536744011418112521734162171471009199457688830567184569416118836214230562125820750070537964076762910622777827351592960 

noncomputable def Ns186p1865 := nat_lit 268222203451318501491752448695998766313012499665896672729585056209702364080504914297068954299056100063545895294594035395970962312931123608404111654912 

noncomputable def Ns186p1866 := nat_lit 124049326210419212004256704194915939231523422465945495093349143444624199081452018957303821821510127330433260728585720275076062115536907974737920 

noncomputable def Ns186p1867 := BSN.log_dyadic_bound 388804091364 1437380091364 7 6 Ns186p1864 67108864 18000000 Ns186p1865 Ns186p1866 37231701 1826184182728 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 388804091364) (BSN.artanhQ 1437380091364) 0 6 Ns186p1865 Ns186p1864 Ns186p1866 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns186p1868 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 477779 4000) qz816 477779 4000 0 1 49323437920137849 4503599627370496 100000027 1800000000000000 23565702846045541357371 18014398509481984000 47777912900033 7200000000000000000 (Enclosure.Real.IsNear.const Bool.false 477779 4000) (BSN.isNear_log_sfrac 913092091364 16000000 49323437920137849 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 913092091364) qz353)) Bool.false Ns186p1863 Ns186p89 1000000270000000 18000000000000000000000 49323437920137849 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 913092091364 16000000 15 1826184182728 1048576000000 37231701 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns186p1867 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p1869 := BSN.arctan_dyadic_bound_f 1000 955558 1 0 8388608 2250000 0 1 1 0 1 1 8778 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 955558) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 955558) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz818 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 955558)))

noncomputable def Ns186p1870 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz818 884279719003555 562949953421312 1 2000000000000000 8778 8388608 1 2250000 7412934350379841224704 883690637395363 562949953421312 8000000009 18000000000000000 qz16 (Ns186p1869 rfl) rfl rfl 

noncomputable def Ns186p1871 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 477779 4000) qz816) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz818)) 23565702846045541357371 18014398509481984000 47777912900033 7200000000000000000 883690637395363 2251799813685248 8000000009 72000000000000000 Ns186p1862 23558633320946378453371 18014398509481984000 48577912900933 7200000000000000000 (Ns186p1868 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz818) 1 4 0 1 883690637395363 562949953421312 8000000009 18000000000000000 883690637395363 2251799813685248 8000000009 72000000000000000 qz356 Ns186p1870 rfl) 

noncomputable def Ns186p1872 := @Ns186p1857 Ns186p1851 Ns186p1852 51117075731449571 3686400000000000000000 (@Ns186p1859 51117075731449571 3686400000000000000000 (Ns186p1861 (Ns186p1871 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 477779 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz579 (Real.log Real.pi) 477779 2000 0 1 38410761 33554432 1 33554432 18351854979819 67108864000 477779 67108864000 (Enclosure.Real.IsNear.const Bool.false 477779 2000) RS187to204.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns186p1853 Ns186p1854) 

noncomputable def Ns186p1873 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz230) Bool.false Ns186p1851 Ns186p1852 51117075731449571 3686400000000000000000 13344816699 16777216 117 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz230) (@HAdd.hAdd Real Real Real qz357 qz576 (Enclosure.sfrac Bool.true Ns186p1853 Ns186p1854)) Bool.false Ns186p1851 Ns186p1852 51117075731449571 3686400000000000000000 Ns186p1855 (Ns186p1872 rfl rfl)) 

noncomputable def Ns186p1874 := nat_lit 1426816754219872417742848 

noncomputable def Ns186p1875 := nat_lit 395816251993876278888827059843325087445701596505499641104402091160002304012337116506881 

noncomputable def Ns186p1876 := nat_lit 28569799880744265111465353176081399254472146331226712673489614885654541458379795201 

noncomputable def Ns186p1877 := nat_lit 1187391616381867348136258248823623099538595845223836469887859294250235602954094589930241 

noncomputable def Ns186p1878 := BSN.cos_dyadic_bound_f 20276285599 34359738368 3 2 16777216 4504395 Ns186p1875 Ns186p851 Ns186p1876 Ns186p1877 Ns186p854 Ns186p1876 13939773 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 20276285599) qz371 0 2 Ns186p1875 Ns186p851 Ns186p1876 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 20276285599) qz372 0 2 Ns186p1877 Ns186p854 Ns186p1876 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1879 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz230) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13344816699) qz360) Bool.false 13344816699 16777216 117 8388608 Bool.true 13939773 16777216 1 2250000 (Ns186p1873 rfl) (Enclosure.sfrac_false_div 13344816699 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13344816699) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p1874) qz361) 226375608064910080 72057594037927936 Bool.false 13939773 16777216 126 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 13344816699 16777216 226375608064910080 72057594037927936 126 Ns186p1874 Ns186p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 13939773 16777216 Ns186p1874 Ns186p89 20276285599 34359738368 4504395 4500000 (Ns186p1878 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p1880 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz230) Bool.false Ns186p1851 Ns186p1852 51117075731449571 3686400000000000000000 106758533598 134217728 1862 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz230) (@HAdd.hAdd Real Real Real qz357 qz576 (Enclosure.sfrac Bool.true Ns186p1853 Ns186p1854)) Bool.false Ns186p1851 Ns186p1852 51117075731449571 3686400000000000000000 Ns186p1855 (Ns186p1872 rfl rfl)) 

noncomputable def Ns186p1881 := Ns186p1850 41174 BSN.abs_quadSignPos (BSN.cos_quad_nat3 295 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 101455541 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 172 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 126433017 134217728) qz233 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz230) qz230 1) Bool.true 13939773 16777216 16977413 1179648000000 111518184 134217728 1932 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz230) qz230 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz230)) Bool.true 13939773 16777216 16977413 1179648000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz230) qz230) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz230)) Bool.true 13939773 16777216 271638608 18874368000000 13939773 16777216 16977413 1179648000000 (Ns186p1879 rfl rfl) rfl)) rfl) (Ns186p1880 rfl) RS187to204.d7 

noncomputable def Ns186p1882 := nat_lit 171840744349160720835114044702182659482499711808852038224592367386880 

noncomputable def Ns186p1883 := nat_lit 30651709925345375545976018679304412017312782606124422600470692096 

noncomputable def Ns186p1884 := nat_lit 450009465765065614436319489237378567691852167375154946284960200130816 

noncomputable def Ns186p1885 := BSN.sin_dyadic_bound_f 115028866 134217728 3 2 134217728 67108864 Ns186p1882 Ns186p111 Ns186p1883 Ns186p1884 Ns186p114 Ns186p1883 101455541 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 115028866) qz362 0 2 Ns186p1882 Ns186p111 Ns186p1883 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 115028866) qz363 0 2 Ns186p1884 Ns186p114 Ns186p1883 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1886 := nat_lit 2427751335865660852451751695699239578916289181680349322336579190625 

noncomputable def Ns186p1887 := nat_lit 19829131015345837935197317603455012104367460238996933750390625 

noncomputable def Ns186p1888 := nat_lit 7283214349334951865679384692462511826724658810120569973142236790625 

noncomputable def Ns186p1889 := BSN.cos_dyadic_bound_f 45937035 134217728 3 2 134217728 67108864 Ns186p1886 Ns186p117 Ns186p1887 Ns186p1888 Ns186p120 Ns186p1887 126433017 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 45937035) qz364 0 2 Ns186p1886 Ns186p117 Ns186p1887 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 45937035) qz365 0 2 Ns186p1888 Ns186p120 Ns186p1887 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1890 := nat_lit 1089307433366083018839796536665069782225952428095255605782979453501823696473693133233677154229099211657216 

noncomputable def Ns186p1891 := nat_lit 138803405792807980377453616719477781135338859494930874560362589847780905475407053351805655357198336 

noncomputable def Ns186p1892 := nat_lit 6604284341345872384250132167148432033121682943749907320157476192968447907975034004436352802074663925452800 

noncomputable def Ns186p1893 := BSN.cos_dyadic_bound_f 150845842 134217728 4 3 134217728 67108864 Ns186p1890 Ns186p127 Ns186p1891 Ns186p1892 Ns186p130 Ns186p1891 58006026 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 150845842) qz364 0 3 Ns186p1890 Ns186p127 Ns186p1891 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 150845842) qz365 0 3 Ns186p1892 Ns186p130 Ns186p1891 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1894 := nat_lit 2104463970827855009552854837809239769905850294197330267145994556876927250549877514056331623109456823586816 

noncomputable def Ns186p1895 := nat_lit 998213286634554017396608237616235377588561547559735137627231287393788349558735290807937307373735936 

noncomputable def Ns186p1896 := nat_lit 12751502476323958162773491609503854323122490336665995507085949287089895019530451847856910993215503608320000 

noncomputable def Ns186p1897 := BSN.cos_dyadic_bound_f 177801442 134217728 4 3 134217728 67108864 Ns186p1894 Ns186p127 Ns186p1895 Ns186p1896 Ns186p130 Ns186p1895 32694970 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 177801442) qz364 0 3 Ns186p1894 Ns186p127 Ns186p1895 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 177801442) qz365 0 3 Ns186p1896 Ns186p130 Ns186p1895 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1898 := Ns186p1848 70112 BSN.abs_quadSignPos (BSN.cos_quad_nat0 84 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 58006026 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 16 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 32694970 134217728) qz233 rfl rfl (Ns186p1881 RS187to204.d9 RS187to204.d11 RS187to204.d13 RS187to204.d17 (Ns186p1885 rfl rfl) (Ns186p1889 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns186p1880 rfl) RS187to204.d19 RS187to204.d21 RS187to204.d23 RS187to204.d25 RS187to204.d17 (Ns186p1893 rfl rfl) (Ns186p1897 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns186p1899 := nat_lit 151400728201568494864535459476860897178850157252403879400789962890625 

noncomputable def Ns186p1900 := nat_lit 77039988404882563166087177128756690514418710531966162261962890625 

noncomputable def Ns186p1901 := nat_lit 454048104627895719467274204076325178155521634336147705877845962890625 

noncomputable def Ns186p1902 := BSN.cos_dyadic_bound_f 129074225 134217728 3 2 134217728 67108864 Ns186p1899 Ns186p117 Ns186p1900 Ns186p1901 Ns186p120 Ns186p1900 76791954 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 129074225) qz364 0 2 Ns186p1899 Ns186p117 Ns186p1900 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 129074225) qz365 0 2 Ns186p1901 Ns186p120 Ns186p1900 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1903 := nat_lit 120472495386218334125867064726149899499637817560697340760718468710400 

noncomputable def Ns186p1904 := nat_lit 15066921934082026410321776946356848702392083957341963927511105536 

noncomputable def Ns186p1905 := nat_lit 315498808137916647048797029501050873315438030237324005479332400070656 

noncomputable def Ns186p1906 := BSN.sin_dyadic_bound_f 105257504 134217728 3 2 134217728 67108864 Ns186p1903 Ns186p111 Ns186p1904 Ns186p1905 Ns186p114 Ns186p1904 94795288 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 105257504) qz362 0 2 Ns186p1903 Ns186p111 Ns186p1904 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 105257504) qz363 0 2 Ns186p1905 Ns186p114 Ns186p1904 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1907 := Ns186p1846 94510 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 76791954 134217728) BSN.abs_quadSignNeg qz794 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 94795288 134217728) qz233 rfl rfl (Ns186p1898 rfl rfl) (Ns186p1880 rfl) RS187to204.d27 RS187to204.d29 RS187to204.d31 RS187to204.d33 RS187to204.d17 (Ns186p1902 rfl rfl) (Ns186p1906 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns186p1908 := nat_lit 341449700120716954046766276961 

noncomputable def Ns186p1909 := BSN.cos_dyadic_bound_f 24173063 134217728 2 1 134217728 67108864 Ns186p1908 Ns186p134 Ns186p1908 Ns186p1908 Ns186p135 Ns186p1908 132046780 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 24173063) qz364 0 1 Ns186p1908 Ns186p134 Ns186p1908 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 24173063) qz365 0 1 Ns186p1908 Ns186p135 Ns186p1908 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1910 := Ns186p1844 Bool.false 9663065 94510 Bool.true 24173063 7074237752028440 1 Bool.false 132046780 Bool.true Bool.true 37022518 105314 BSN.abs_quadSignNeg qz431 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132046780 134217728) qz233 rfl (Ns186p1907 rfl) (Ns186p1880 rfl) RS187to204.d35 RS187to204.d37 RS187to204.d17 (Ns186p1909 rfl rfl) rfl 

noncomputable def Ns186p1911 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz230) qz230 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz230) qz230 8) 37022518 134217728 105314 134217728 37022518 134217728 105314 134217728 9938156501598208 18511259 33554432 52657 33554432 (Ns186p1910 rfl rfl rfl rfl) 

noncomputable def Ns186p1912 := @Enclosure.Real.IsNear.mulLit_ff qz814 (Zeta.RiemannSiegel.correction qz232) 1420359 4194304 1 8388608 4154387481343 8796093022208 184707180147853 1099511627776000000 5900721648612862137 36893488147419103232 

noncomputable abbrev qz819 := (@HPow.hPow Real Real Real qz7 qz231 qz9)

noncomputable def Ns186p1913 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz819 1 1 0 1 1420359 4194304 1 8388608 1420359 4194304 1 8388608 

noncomputable def Ns186p1914 := @Enclosure.Real.IsNear.sqrt_image qz231 1275754496883 16777216000 477779 16777216000 73149847 73149875 8388608 (@Enclosure.Real.IsNear.of_eq qz231 (@HMul.hMul Real Real Real qz5 qz230 qz3) Bool.false 1275754496883 16777216000 477779 16777216000 (BSN.t_div_two_pi_mk qz230 477779 1000 qz233) (@Enclosure.Real.IsNear.mulLit_ff qz230 qz3 477779 1000 0 1 2670177 16777216 1 16777216 1275754496883 16777216000 477779 16777216000 (Enclosure.Real.IsNear.const Bool.false 477779 1000) RS187to204.d40 rfl)) 

noncomputable abbrev qz961 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 477779 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz820 := qz961

noncomputable abbrev qz580 := qz820

noncomputable abbrev qz235 := qz580

noncomputable def Ns186p1915 := @Enclosure.Real.IsNear.sqrt_image qz235 73149861 8388608 7 4194304 24771463 24771468 8388608 (@Enclosure.Real.IsNear.recentre' qz235 Bool.false 146299722 16777216 28 16777216 73149861 8388608 7 4194304 (Ns186p1914 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns186p1916 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz235) 49542931 16777216 5 16777216 2840717 2840719 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz235) Bool.false 49542931 16777216 5 16777216 49542931 16777216 5 16777216 (Ns186p1915 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns186p1917 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz235)) Bool.false 5681436 16777216 2 16777216 1420359 4194304 1 8388608 (Ns186p1916 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz236 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz574))

noncomputable abbrev qz821 := (@HMul.hMul Real Real Real qz891 qz960 qz960)

noncomputable abbrev qz581 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz821 qz813) qz640)

noncomputable abbrev qz237 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz581))

noncomputable def Ns186p1918 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz232) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz236) qz237) Bool.false 4154387481343 

noncomputable def Ns186p1919 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz236) qz237 89958803 16777216 5305 

noncomputable abbrev qz822 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz236))

noncomputable def Ns186p1920 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz236) (@Neg.neg Real Real.instNeg qz822) Bool.true 89958803 16777216 5305 16777216 (BSN.inv_eq_neg_inv_neg qz236) 

noncomputable def Ns186p1921 := @Enclosure.Real.IsNear.recentre' qz822 Bool.false 89958803 16777216 5305 16777216 89958803 16777216 

noncomputable def Ns186p1922 := @Enclosure.Real.IsNear.recentre' qz236 Bool.true 3128932 16777216 415027216 37748736000000 782233 4194304 25939201 2359296000000 

noncomputable abbrev qz238 := (@HMul.hMul Real Real Real qz342 qz340 qz574)

noncomputable def Ns186p1923 := @Enclosure.Real.IsNear.cos_image qz238 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 75913407) qz360) Bool.false 75913407 16777216 177 16777216 Bool.true 3128932 16777216 1 

noncomputable def Ns186p1924 := nat_lit 188902527889254202736416881 

noncomputable def Ns186p1925 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz232 884279719003555 140737488355328 1 500000000000000 6040997 8388608 7 4194304 5341931129661318744335 1180591620717411303424 Ns186p1924 

noncomputable def Ns186p1926 := @Enclosure.Real.IsNear.subLit_ff_p qz235 qz1 73149861 8388608 7 4194304 8 1 0 1 6040997 6040997 8388608 7 

noncomputable def Ns186p1927 := @Ns186p1926 4194304 (@Enclosure.Real.IsNear.recentre' qz235 Bool.false 146299722 16777216 28 16777216 73149861 8388608 7 4194304 (Ns186p1914 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns186p1928 := @Enclosure.Real.IsNear.recentre' qz238 Bool.false 5341931129661318744335 1180591620717411303424 Ns186p1924 Ns186p159 75913407 16777216 177 16777216 (@Ns186p1925 Ns186p159 RS187to204.d39 (Ns186p1927 rfl rfl) rfl) 

noncomputable def Ns186p1929 := nat_lit 3344369980011316819001344 

noncomputable def Ns186p1930 := nat_lit 198247673919723242201837023198448787291058179502845193961745453761768736286106197663229738539179597565761279131474821767276902476550481 

noncomputable def Ns186p1931 := nat_lit 1296985566167364170939292694987530979374979352933922598450371085822004482258776525817524027815363891144507173707470555812298386676121600 

noncomputable def Ns186p1932 := nat_lit 132804927952739424687160255182273410130320359064652863995384158479158394641071571510705057532257162290347491695385159634481189201 

noncomputable def Ns186p1933 := nat_lit 1200958667713988991133628697703290038919841600539156083618119772408623267353990402325081863689895645378570425377611833971885771796123985 

noncomputable def Ns186p1934 := nat_lit 118025686521230139555475635243865319123123121116986956458983768809802407885548663849394686531198114094150152807379820578919153187527065600 

noncomputable def Ns186p1935 := BSN.cos_dyadic_bound_f 47526355899 34359738368 4 3 16777216 4504395 Ns186p1930 Ns186p1931 Ns186p1932 Ns186p1933 Ns186p1934 Ns186p1932 3128932 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 47526355899) qz371 0 3 Ns186p1930 Ns186p1931 Ns186p1932 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 47526355899) qz372 0 3 Ns186p1933 Ns186p1934 Ns186p1932 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1936 := @Ns186p1923 2250000 (Ns186p1928 rfl) (Enclosure.sfrac_false_div 75913407 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 75913407) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p1929) qz361) 226375608064910080 72057594037927936 Bool.false 3128932 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 75913407 16777216 226375608064910080 72057594037927936 0 Ns186p1929 Ns186p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 3128932 16777216 Ns186p1929 Ns186p89 47526355899 34359738368 4504395 4500000 (Ns186p1935 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p1937 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz236) 782233 4194304 25939201 2359296000000 44976749 44982054 8388608 (@Enclosure.Real.IsNear.neg qz236 Bool.true 782233 4194304 25939201 2359296000000 (Ns186p1922 (Ns186p1936 rfl rfl) rfl)) 

noncomputable def Ns186p1938 := Ns186p1920 (@Enclosure.Real.IsNear.neg qz822 Bool.false 89958803 16777216 5305 16777216 (@Ns186p1921 5305 16777216 (Ns186p1937 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p1939 := @Enclosure.Real.IsNear.recentre' qz237 Bool.true 738896 8388608 

noncomputable abbrev qz239 := (@HMul.hMul Real Real Real qz342 qz340 qz581)

noncomputable def Ns186p1940 := @Enclosure.Real.IsNear.cos_image qz239 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 13916649)) qz429) Bool.true 13916649 8388608 

noncomputable def Ns186p1941 := nat_lit 16429879614238948713830008405 

noncomputable def Ns186p1942 := nat_lit 96673777734972134527537555119423 

noncomputable def Ns186p1943 := @Enclosure.Real.IsNear.recentre' qz239 Bool.true Ns186p1941 Ns186p427 Ns186p1942 

noncomputable def Ns186p1944 := nat_lit 3777893186295716170956800000000000000 

noncomputable abbrev qz240 := qz581

noncomputable def Ns186p1945 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz240 884279719003555 140737488355328 1 500000000000000 18579957519271 

noncomputable abbrev qz582 := (@HSub.hSub Real Real Real qz633 qz821 qz813)

noncomputable abbrev qz241 := qz582

noncomputable def Ns186p1946 := @Enclosure.Real.IsNear.subLit_tf qz241 qz26 14181911008167 70368744177664 17911789 4398046511104 1 16 

noncomputable abbrev qz583 := qz821

noncomputable abbrev qz242 := qz583

noncomputable def Ns186p1947 := @Enclosure.Real.IsNear.subLit_ff_n qz242 qz232 36493644754009 70368744177664 10571757 4398046511104 6040997 8388608 7 4194304 

noncomputable def Ns186p1948 := @Enclosure.Real.IsNear.mulLit_ff qz232 qz232 6040997 8388608 7 4194304 6040997 8388608 7 4194304 36493644754009 70368744177664 

noncomputable def Ns186p1949 := nat_lit 18439054504340289415181742442187551279128791118657755583122099188640561880562667644435338081 

noncomputable def Ns186p1950 := nat_lit 52773522760793544425328047791205516645457234590961024046940647145553393023784625935201 

noncomputable def Ns186p1951 := nat_lit 111528586322184651221630145965993238082429801653882349485212673352987817369098752898687079265 

noncomputable def Ns186p1952 := BSN.cos_dyadic_bound_t 13916649 8388608 4 3 8388608 2250000 Ns186p1949 Ns186p754 Ns186p1950 Ns186p1951 Ns186p757 Ns186p1950 738896 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 13916649) (BSN.cosEvenQ 8388608) 0 3 Ns186p1949 Ns186p754 Ns186p1950 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 13916649) (BSN.cosOddQ 8388608) 0 3 Ns186p1951 Ns186p757 Ns186p1950 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1953 := @Ns186p1939 986527216 37748736000000 46181 524288 61657951 2359296000000 (@Ns186p1940 431 16777216 Bool.true 738896 8388608 1 2250000 (@Ns186p1943 Ns186p1944 13916649 8388608 431 16777216 (@Ns186p1945 70368744177664 17911789 4398046511104 Ns186p1941 Ns186p427 Ns186p1942 Ns186p1944 RS187to204.d39 (@Ns186p1946 0 1 297279320308336 18579957519271 70368744177664 17911789 4398046511104 (@Ns186p1947 118966492138397761536 14181911008167 70368744177664 17911789 4398046511104 (@Ns186p1948 10571757 4398046511104 (Ns186p1927 rfl rfl) (Ns186p1927 rfl rfl) rfl) (Ns186p1927 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 13916649 8388608) (BSN.cos_neg_of_bound 13916649 8388608 Bool.true 738896 8388608 1 2250000 (Ns186p1952 rfl rfl)) rfl rfl) 

noncomputable def Ns186p1954 := @Ns186p1912 525220494517596701307 Ns186p1089 (Ns186p1913 qz28 (@Enclosure.Real.IsNear.of_eq qz819 (@Inv.inv Real Real.instInv (Real.sqrt qz235)) Bool.false 1420359 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz231 (BSN.t_div_two_pi_nonneg qz230 477779 1000 qz233)) Ns186p1917) rfl) (@Ns186p1918 8796093022208 184707180147853 1099511627776000000 (BSN.correction_mk qz232 (BSN.cos_two_pi_p_ne_zero_mk qz230 477779 1000 8 qz233 rfl rfl (@BSN.floor_sqrt_eq_dec qz230 477779 1000 8 qz233 rfl rfl rfl))) (@Ns186p1919 16777216 46181 524288 61657951 2359296000000 4154387481343 8796093022208 184707180147853 1099511627776000000 Ns186p1938 (Ns186p1953 rfl) rfl)) 

noncomputable def Ns186p1955 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz230) (hardyZApproximantRS₀ qz230) Bool.true 26254066163885992121 36893488147419103232 14999466440467804701307 Ns186p1089 (@Eq.refl Real (hardyZApproximantRS₀ qz230)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz230) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz230) qz230 8) (@HMul.hMul Real Real Real qz5 qz814 (Zeta.RiemannSiegel.correction qz232))) Bool.true 26254066163885992121 36893488147419103232 14999466440467804701307 Ns186p1089 (BSN.hardyZApproximantRS₀_eq qz230 8 (@BSN.floor_sqrt_eq_dec qz230 477779 1000 8 qz233 rfl rfl rfl)) (@Ns186p1843 26254066163885992121 36893488147419103232 14999466440467804701307 Ns186p1089 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz230) qz230 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz230) qz230 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz230) qz230 8)) Bool.true 18511259 33554432 52657 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz230) qz230 8) (Ns186p1911 (Ns186p1910 rfl rfl rfl rfl) rfl rfl)) (Ns186p1954 rfl) rfl rfl)) 

theorem RS187to204.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz230) Bool.true 26254066163885992121 36893488147419103232 14999466440467804701307 Ns186p1089 := Ns186p1955 

noncomputable def Ns186p1956 := nat_lit 2594073385365405696000000 

noncomputable def Ns186p1957 := nat_lit 14540692391745832337014784 

noncomputable abbrev qz962 := (Enclosure.sfrac Bool.false 478504 1000)

noncomputable abbrev qz823 := qz962

noncomputable abbrev qz584 := qz823

noncomputable abbrev qz243 := qz584

noncomputable abbrev qz963 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 478504 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz824 := qz963

noncomputable abbrev qz585 := qz824

noncomputable abbrev qz244 := qz585

noncomputable abbrev qz964 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 478504 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz825 := qz964

noncomputable abbrev qz586 := qz825

noncomputable abbrev qz245 := qz586

noncomputable abbrev qz826 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz244 qz9))

noncomputable def Ns186p1958 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz243) qz243 8) (@HMul.hMul Real Real Real qz5 qz826 (Zeta.RiemannSiegel.correction qz245)) 7663567 8388608 103 65536 373159647088638375 2305843009213693952 196724089021660589261 Ns186p1956 Ns186p1957 

noncomputable def Ns186p1959 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.cos BSN.quadSignNeg 7 8 478504 1000 126 134217728 67108864 2251799813685248 Bool.false 106969303960 1865 279097919 60 47453128 8 

noncomputable def Ns186p1960 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 478504 1000 38 85 134217728 67108864 2251799813685248 Bool.false 106969303960 1865 

noncomputable def Ns186p1961 := Ns186p1960 240485871 61 54794152 8 261175631 61 50729528 8 Bool.false 180350639 70216 Bool.true 92656119 Bool.true 83839474 7074237752028440 1 Bool.false 103485673 Bool.true Bool.false 78492626 Bool.true Bool.false 108435373 

noncomputable def Ns186p1962 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 478504 1000 85 17 134217728 67108864 2251799813685248 Bool.false 106969303960 1865 

noncomputable def Ns186p1963 := Ns186p1962 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 197688765 41234 Bool.false 15890173 Bool.false 21132151 7074237752028440 1 Bool.false 15853078 Bool.true Bool.false 21044949 Bool.true Bool.false 180350639 

noncomputable def Ns186p1964 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 478504 1000 296 172 134217728 67108864 2251799813685248 Bool.false 106969303960 1865 

noncomputable def Ns186p1965 := Ns186p1964 93032624 60 94906264 8 147453232 60 77490640 16 Bool.false 74638136 1932 Bool.false 47521862 Bool.false 149803804 7074237752028440 1 Bool.false 125892325 Bool.false Bool.false 58943966 Bool.false Bool.false 197688765 

noncomputable def Ns186p1966 := nat_lit 47334357361336961013145942496973394165615954488186641 

noncomputable def Ns186p1967 := nat_lit 59391897171865141187154591553582967313747935232000 

noncomputable def Ns186p1968 := nat_lit 12041214737588376068588646891520000 

noncomputable def Ns186p1969 := nat_lit 34570634115874500239241514095095316480 

noncomputable abbrev qz965 := (@Eq.refl Real (Enclosure.sfrac Bool.false 478504 1000))

noncomputable abbrev qz827 := qz965

noncomputable abbrev qz587 := qz827

noncomputable abbrev qz246 := qz587

noncomputable def Ns186p1970 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz243 478504 1000 915865312064 16000000 957008 4000 2000 Ns186p1968 Ns186p1969 qz246 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns186p1971 := nat_lit 62042088880651581539150649749632967200756143866755994091520 

noncomputable abbrev qz828 := (Real.log (Enclosure.sfrac Bool.false 915865312064 16000000))

noncomputable abbrev qz247 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 478504 4000) qz828) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 957008))))))

noncomputable abbrev qz829 := (Enclosure.sfrac Bool.false 478504 2000)

noncomputable abbrev qz588 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz247 qz829) (@HMul.hMul Real Real Real qz5 qz829 (Real.log Real.pi)))

noncomputable def Ns186p1972 := @Enclosure.Real.IsNear.addLit_ft_p qz588 (Enclosure.sfrac Bool.true Ns186p1968 Ns186p1969) 1794647902236989793349 2251799813685248000 711028071957293 51200000000000000000 Ns186p1968 Ns186p1969 0 1 Ns186p1971 

noncomputable def Ns186p1973 := nat_lit 15054597749888430476405768192000 

noncomputable abbrev qz589 := (@HSub.hSub Real Real Real qz12 qz247 qz829)

noncomputable abbrev qz590 := (@HMul.hMul Real Real Real qz5 qz829 (Real.log Real.pi))

noncomputable def Ns186p1974 := @Enclosure.Real.IsNear.subLit_ff_p qz589 qz590 2411368389400518796357 2251799813685248000 1351400358903 200000000000000000 2297462847693 8388608000 59813 8388608000 Ns186p1973 1794647902236989793349 2251799813685248000 

noncomputable def Ns186p1975 := nat_lit 4822736778801037592714000 

noncomputable abbrev qz591 := qz829

noncomputable def Ns186p1976 := @Enclosure.Real.IsNear.subLit_ff_p qz247 qz591 2950115998424341750853 2251799813685248000 1351400358903 200000000000000000 478504 2000 0 1 Ns186p1975 2411368389400518796357 2251799813685248000 1351400358903 200000000000000000 

noncomputable def Ns186p1977 := nat_lit 6643070655601802136907161326577516544 

noncomputable def Ns186p1978 := nat_lit 26487651427727510572367872 

noncomputable def Ns186p1979 := nat_lit 10756539501843867630949898753960400785570897221567999294488928563495977076537506684555379712856131344786067264958797286152924759088249034971951356968960 

noncomputable def Ns186p1980 := nat_lit 277492105960343270274409255294191061698009524535469278845170190379653062782967300538584555837416113214794080801534583955956544315134112696171717722112 

noncomputable def Ns186p1981 := nat_lit 135093590491753214729783541048111755054407969057354350693844950815119367560997485093992302284225390199362240237392739006588663698253546436689920 

noncomputable def Ns186p1982 := BSN.log_dyadic_bound 391577312064 1440153312064 7 6 Ns186p1979 67108864 18000000 Ns186p1980 Ns186p1981 37435214 1831730624128 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 391577312064) (BSN.artanhQ 1440153312064) 0 6 Ns186p1980 Ns186p1979 Ns186p1981 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns186p1983 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 478504 4000) qz828 478504 4000 0 1 49337095446377081 4503599627370496 100000027 1800000000000000 2950999689934152345853 2251799813685248000 5981301614951 900000000000000000 (Enclosure.Real.IsNear.const Bool.false 478504 4000) (BSN.isNear_log_sfrac 915865312064 16000000 49337095446377081 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 915865312064) qz353)) Bool.false Ns186p1978 Ns186p89 1000000270000000 18000000000000000000000 49337095446377081 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 915865312064 16000000 15 1831730624128 1048576000000 37435214 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns186p1982 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p1984 := BSN.arctan_dyadic_bound_f 1000 957008 1 0 8388608 2250000 0 1 1 0 1 1 8765 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 957008) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 957008) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz830 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 957008)))

noncomputable def Ns186p1985 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz830 884279719003555 562949953421312 1 2000000000000000 8765 8388608 1 2250000 7412941668729235701760 883691509810595 562949953421312 8000000009 18000000000000000 qz16 (Ns186p1984 rfl) rfl rfl 

noncomputable def Ns186p1986 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 478504 4000) qz828) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz830)) 2950999689934152345853 2251799813685248000 5981301614951 900000000000000000 883691509810595 2251799813685248 8000000009 72000000000000000 Ns186p1977 2950115998424341750853 2251799813685248000 1351400358903 200000000000000000 (Ns186p1983 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz830) 1 4 0 1 883691509810595 562949953421312 8000000009 18000000000000000 883691509810595 2251799813685248 8000000009 72000000000000000 qz356 Ns186p1985 rfl) 

noncomputable def Ns186p1987 := @Ns186p1972 Ns186p1966 Ns186p1967 711028071957293 51200000000000000000 (@Ns186p1974 711028071957293 51200000000000000000 (Ns186p1976 (Ns186p1986 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 478504 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz591 (Real.log Real.pi) 478504 2000 0 1 38410761 33554432 1 33554432 2297462847693 8388608000 59813 8388608000 (Enclosure.Real.IsNear.const Bool.false 478504 2000) RS187to204.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns186p1968 Ns186p1969) 

noncomputable def Ns186p1988 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz243) Bool.false Ns186p1966 Ns186p1967 711028071957293 51200000000000000000 13371162995 16777216 117 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz243) (@HAdd.hAdd Real Real Real qz357 qz588 (Enclosure.sfrac Bool.true Ns186p1968 Ns186p1969)) Bool.false Ns186p1966 Ns186p1967 711028071957293 51200000000000000000 Ns186p1970 (Ns186p1987 rfl rfl)) 

noncomputable def Ns186p1989 := nat_lit 1425765683725703242055680 

noncomputable def Ns186p1990 := nat_lit 168528528298810805971810776220628103938641 

noncomputable def Ns186p1991 := nat_lit 167255588988979673561517887044862711294853120 

noncomputable def Ns186p1992 := nat_lit 1170789122922857714930625209314038979063971840 

noncomputable def Ns186p1993 := BSN.sin_dyadic_bound_f 20261348989 34359738368 2 1 16777216 4504395 Ns186p1990 Ns186p1991 Ns186p1990 Ns186p1990 Ns186p1992 Ns186p1990 9329767 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 20261348989) qz358 0 1 Ns186p1990 Ns186p1991 Ns186p1990 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 20261348989) qz359 0 1 Ns186p1990 Ns186p1992 Ns186p1990 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p1994 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz243) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13371162995) qz360) Bool.false 13371162995 16777216 117 8388608 Bool.false 9329767 16777216 1 2250000 (Ns186p1988 rfl) (Enclosure.sfrac_false_div 13371162995 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13371162995) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p1989) qz361) 226375608064910080 72057594037927936 Bool.false 9329767 16777216 126 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q3 13371162995 16777216 226375608064910080 72057594037927936 126 Ns186p1989 Ns186p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 9329767 16777216 Ns186p1989 Ns186p89 20261348989 34359738368 4504395 4500000 (Ns186p1993 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p1995 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz243) Bool.false Ns186p1966 Ns186p1967 711028071957293 51200000000000000000 106969303960 134217728 1865 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz243) (@HAdd.hAdd Real Real Real qz357 qz588 (Enclosure.sfrac Bool.true Ns186p1968 Ns186p1969)) Bool.false Ns186p1966 Ns186p1967 711028071957293 51200000000000000000 Ns186p1970 (Ns186p1987 rfl rfl)) 

noncomputable def Ns186p1996 := Ns186p1965 41234 BSN.abs_quadSignPos (BSN.cos_quad_nat0 296 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 125892325 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 172 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 58943966 134217728) qz246 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 1) Bool.false 9329767 16777216 16977413 1179648000000 74638136 134217728 1932 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz243)) Bool.false 9329767 16777216 16977413 1179648000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz243) qz243) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz243)) Bool.false 9329767 16777216 271638608 18874368000000 9329767 16777216 16977413 1179648000000 (Ns186p1994 rfl rfl) rfl)) rfl) (Ns186p1995 rfl) RS187to204.d7 

noncomputable def Ns186p1997 := nat_lit 2780524149249947842803636965118180248444776670252531344018024734976 

noncomputable def Ns186p1998 := nat_lit 26010433510156278832856408680347079210078863283956394136740096 

noncomputable def Ns186p1999 := nat_lit 8341520426882823215853245182537180051175909853031026119265800724736 

noncomputable def Ns186p2000 := BSN.cos_dyadic_bound_f 47521862 134217728 3 2 134217728 67108864 Ns186p1997 Ns186p117 Ns186p1998 Ns186p1999 Ns186p120 Ns186p1998 125892325 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 47521862) qz364 0 2 Ns186p1997 Ns186p117 Ns186p1998 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 47521862) qz365 0 2 Ns186p1999 Ns186p120 Ns186p1998 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p2001 := nat_lit 1059490795494975561780036743184322773526258432974876908245122655849267031392548577339353634318115034628096 

noncomputable def Ns186p2002 := nat_lit 127724467177904976360535102134240274917142707109802377857030981521809984337781216997837239658479616 

noncomputable def Ns186p2003 := nat_lit 6423622290900443612161904964880563425926631421705584190567417478239551913404958108396781125978924053954560 

noncomputable def Ns186p2004 := BSN.cos_dyadic_bound_f 149803804 134217728 4 3 134217728 67108864 Ns186p2001 Ns186p127 Ns186p2002 Ns186p2003 Ns186p130 Ns186p2002 58943966 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 149803804) qz364 0 3 Ns186p2001 Ns186p127 Ns186p2002 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 149803804) qz365 0 3 Ns186p2003 Ns186p130 Ns186p2002 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p2005 := nat_lit 63755036980583893461988265041 

noncomputable def Ns186p2006 := BSN.sin_dyadic_bound_f 15890173 134217728 2 1 134217728 67108864 Ns186p2005 Ns186p123 Ns186p2005 Ns186p2005 Ns186p124 Ns186p2005 15853078 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 15890173) qz362 0 1 Ns186p2005 Ns186p123 Ns186p2005 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 15890173) qz363 0 1 Ns186p2005 Ns186p124 Ns186p2005 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p2007 := nat_lit 199422805254551577870026013601 

noncomputable def Ns186p2008 := BSN.sin_dyadic_bound_f 21132151 134217728 2 1 134217728 67108864 Ns186p2007 Ns186p123 Ns186p2007 Ns186p2007 Ns186p124 Ns186p2007 21044949 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 21132151) qz362 0 1 Ns186p2007 Ns186p123 Ns186p2007 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 21132151) qz363 0 1 Ns186p2007 Ns186p124 Ns186p2007 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p2009 := Ns186p1963 70216 BSN.abs_quadSignNeg qz794 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 15853078 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 17 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 21044949 134217728) qz246 rfl rfl (Ns186p1996 RS187to204.d9 RS187to204.d11 RS187to204.d13 RS187to204.d17 (Ns186p2000 rfl rfl) (Ns186p2004 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns186p1995 rfl) RS187to204.d19 RS187to204.d21 RS187to204.d23 RS187to204.d25 RS187to204.d17 (Ns186p2006 rfl rfl) (Ns186p2008 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns186p2010 := nat_lit 40188698656073699202310609614863387599165664465067137639650750809921 

noncomputable def Ns186p2011 := nat_lit 5432413788895843133508638700688151410043781025334929137471506241 

noncomputable def Ns186p2012 := nat_lit 120555231140643305920664811567188786494676905833150743060677309417281 

noncomputable def Ns186p2013 := BSN.cos_dyadic_bound_f 92656119 134217728 3 2 134217728 67108864 Ns186p2010 Ns186p117 Ns186p2011 Ns186p2012 Ns186p120 Ns186p2011 103485673 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 92656119) qz364 0 2 Ns186p2010 Ns186p117 Ns186p2011 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 92656119) qz365 0 2 Ns186p2012 Ns186p120 Ns186p2011 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p2014 := nat_lit 48488345226781803969005247327649906022520774350811205296090496549120 

noncomputable def Ns186p2015 := nat_lit 2441115675050230239356715398816848812935337188896648898533048576 

noncomputable def Ns186p2016 := nat_lit 126989332835240357641292879747485002779952513706199705010591770788096 

noncomputable def Ns186p2017 := BSN.sin_dyadic_bound_f 83839474 134217728 3 2 134217728 67108864 Ns186p2014 Ns186p111 Ns186p2015 Ns186p2016 Ns186p114 Ns186p2015 78492626 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 83839474) qz362 0 2 Ns186p2014 Ns186p111 Ns186p2015 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 83839474) qz363 0 2 Ns186p2016 Ns186p114 Ns186p2015 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p2018 := Ns186p1961 94651 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 103485673 134217728) BSN.abs_quadSignNeg qz794 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 78492626 134217728) qz246 rfl rfl (Ns186p2009 rfl rfl) (Ns186p1995 rfl) RS187to204.d27 RS187to204.d29 RS187to204.d31 RS187to204.d33 RS187to204.d17 (Ns186p2013 rfl rfl) (Ns186p2017 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns186p2019 := nat_lit 61514565110266226889999626496 

noncomputable def Ns186p2020 := BSN.cos_dyadic_bound_f 15748692 134217728 2 1 134217728 67108864 Ns186p2019 Ns186p134 Ns186p2019 Ns186p2019 Ns186p135 Ns186p2019 133294836 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 15748692) qz364 0 1 Ns186p2019 Ns186p134 Ns186p2019 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 15748692) qz365 0 1 Ns186p2019 Ns186p135 Ns186p2019 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p2021 := Ns186p1959 Bool.false 108435373 94651 Bool.true 15748692 7074237752028440 1 Bool.false 133294836 Bool.true Bool.false 61308536 105472 BSN.abs_quadSignNeg qz431 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133294836 134217728) qz246 rfl (Ns186p2018 rfl) (Ns186p1995 rfl) RS187to204.d35 RS187to204.d37 RS187to204.d17 (Ns186p2020 rfl rfl) rfl 

noncomputable def Ns186p2022 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 8) 61308536 134217728 105472 134217728 61308536 134217728 105472 134217728 16457384817852416 7663567 8388608 103 65536 (Ns186p2021 rfl rfl rfl rfl) 

noncomputable def Ns186p2023 := @Enclosure.Real.IsNear.mulLit_ff qz826 (Zeta.RiemannSiegel.correction qz245) 2839641 8388608 1 8388608 131410853375 274877906944 138451432829641 618475290624000000 373159647088638375 2305843009213693952 

noncomputable abbrev qz831 := (@HPow.hPow Real Real Real qz7 qz244 qz9)

noncomputable def Ns186p2024 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz831 1 1 0 1 2839641 8388608 1 8388608 2839641 8388608 1 8388608 

noncomputable def Ns186p2025 := @Enclosure.Real.IsNear.sqrt_image qz244 159711296901 2097152000 59813 2097152000 73205326 73205355 8388608 (@Enclosure.Real.IsNear.of_eq qz244 (@HMul.hMul Real Real Real qz5 qz243 qz3) Bool.false 159711296901 2097152000 59813 2097152000 (BSN.t_div_two_pi_mk qz243 478504 1000 qz246) (@Enclosure.Real.IsNear.mulLit_ff qz243 qz3 478504 1000 0 1 2670177 16777216 1 16777216 159711296901 2097152000 59813 2097152000 (Enclosure.Real.IsNear.const Bool.false 478504 1000) RS187to204.d40 rfl)) 

noncomputable abbrev qz966 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 478504 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz832 := qz966

noncomputable abbrev qz592 := qz832

noncomputable abbrev qz248 := qz592

noncomputable def Ns186p2026 := @Enclosure.Real.IsNear.sqrt_image qz248 146410681 16777216 29 16777216 24780855 24780861 8388608 (@Enclosure.Real.IsNear.recentre' qz248 Bool.false 146410681 16777216 29 16777216 146410681 16777216 29 16777216 (Ns186p2025 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns186p2027 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz248) 12390429 4194304 3 8388608 2839640 2839642 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz248) Bool.false 49561716 16777216 6 16777216 12390429 4194304 3 8388608 (Ns186p2026 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns186p2028 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz248)) Bool.false 5679282 16777216 2 16777216 2839641 8388608 1 8388608 (Ns186p2027 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz249 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz586))

noncomputable abbrev qz833 := (@HMul.hMul Real Real Real qz891 qz964 qz964)

noncomputable abbrev qz593 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz833 qz825) qz640)

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz593))

noncomputable def Ns186p2029 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz245) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz249) qz250) Bool.false 131410853375 

noncomputable def Ns186p2030 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz249) qz250 3602765 524288 4497 

noncomputable abbrev qz834 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz249))

noncomputable def Ns186p2031 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz249) (@Neg.neg Real Real.instNeg qz834) Bool.true 3602765 524288 4497 8388608 (BSN.inv_eq_neg_inv_neg qz249) 

noncomputable def Ns186p2032 := @Enclosure.Real.IsNear.recentre' qz834 Bool.false 115288480 16777216 8994 16777216 3602765 524288 

noncomputable def Ns186p2033 := @Enclosure.Real.IsNear.recentre' qz249 Bool.true 2441484 16777216 428527216 37748736000000 610371 4194304 26782951 2359296000000 

noncomputable abbrev qz251 := (@HMul.hMul Real Real Real qz342 qz340 qz586)

noncomputable def Ns186p2034 := @Enclosure.Real.IsNear.cos_image qz251 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 76610583) qz360) Bool.false 76610583 16777216 183 16777216 Bool.true 2441484 16777216 1 

noncomputable def Ns186p2035 := nat_lit 782596186967013986953230219 

noncomputable def Ns186p2036 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz245 884279719003555 140737488355328 1 500000000000000 12192953 16777216 29 16777216 10781981052663552947915 2361183241434822606848 Ns186p2035 

noncomputable def Ns186p2037 := @Enclosure.Real.IsNear.subLit_ff_p qz248 qz1 146410681 16777216 29 16777216 8 1 0 1 12192953 12192953 16777216 29 

noncomputable def Ns186p2038 := @Ns186p2037 16777216 (@Enclosure.Real.IsNear.recentre' qz248 Bool.false 146410681 16777216 29 16777216 146410681 16777216 29 16777216 (Ns186p2025 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns186p2039 := @Enclosure.Real.IsNear.recentre' qz251 Bool.false 10781981052663552947915 2361183241434822606848 Ns186p2035 Ns186p1601 76610583 16777216 183 16777216 (@Ns186p2036 Ns186p1601 RS187to204.d39 (Ns186p2038 rfl rfl) rfl) 

noncomputable def Ns186p2040 := nat_lit 3444843630373289712418816 

noncomputable def Ns186p2041 := nat_lit 223227466729562343571100921640975173756438523700677225766048416912536776340191501170134586839015097302747787377259887133990848956535121 

noncomputable def Ns186p2042 := nat_lit 189442122028381514280166513683193816520974409641213271004815016387358834874207998701555031043490968101799483707137143681106121041 

noncomputable def Ns186p2043 := nat_lit 1352036688479345970844694749536175599907934030438743687164187122998698732429856410466246350785819268674680054377892725156726445096112465 

noncomputable def Ns186p2044 := BSN.cos_dyadic_bound_f 48954172347 34359738368 4 3 16777216 4504395 Ns186p2041 Ns186p1931 Ns186p2042 Ns186p2043 Ns186p1934 Ns186p2042 2441484 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 48954172347) qz371 0 3 Ns186p2041 Ns186p1931 Ns186p2042 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 48954172347) qz372 0 3 Ns186p2043 Ns186p1934 Ns186p2042 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p2045 := @Ns186p2034 2250000 (Ns186p2039 rfl) (Enclosure.sfrac_false_div 76610583 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 76610583) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p2040) qz361) 226375608064910080 72057594037927936 Bool.false 2441484 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 76610583 16777216 226375608064910080 72057594037927936 0 Ns186p2040 Ns186p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 2441484 16777216 Ns186p2040 Ns186p89 48954172347 34359738368 4504395 4500000 (Ns186p2044 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p2046 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz249) 610371 4194304 26782951 2359296000000 57639743 57648737 8388608 (@Enclosure.Real.IsNear.neg qz249 Bool.true 610371 4194304 26782951 2359296000000 (Ns186p2033 (Ns186p2045 rfl rfl) rfl)) 

noncomputable def Ns186p2047 := Ns186p2031 (@Enclosure.Real.IsNear.neg qz834 Bool.false 3602765 524288 4497 8388608 (@Ns186p2032 4497 8388608 (Ns186p2046 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p2048 := @Enclosure.Real.IsNear.recentre' qz250 Bool.true 583600 8388608 

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz342 qz340 qz593)

noncomputable def Ns186p2049 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 27521731)) qz360) Bool.true 27521731 16777216 

noncomputable def Ns186p2050 := nat_lit 64983850138441019448159560525 

noncomputable def Ns186p2051 := nat_lit 32214125012467393615698509954374053 

noncomputable def Ns186p2052 := @Enclosure.Real.IsNear.recentre' qz252 Bool.true Ns186p2050 Ns186p1617 Ns186p2051 

noncomputable def Ns186p2053 := nat_lit 1208925819614629174706176000000000000000 

noncomputable abbrev qz253 := qz593

noncomputable def Ns186p2054 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz253 884279719003555 140737488355328 1 500000000000000 73487889343055 

noncomputable abbrev qz594 := (@HSub.hSub Real Real Real qz633 qz833 qz825)

noncomputable abbrev qz254 := qz594

noncomputable def Ns186p2055 := @Enclosure.Real.IsNear.subLit_tf qz254 qz26 55895703298639 281474976710656 1193731379 281474976710656 1 16 

noncomputable abbrev qz595 := qz833

noncomputable abbrev qz255 := qz595

noncomputable def Ns186p2056 := @Enclosure.Real.IsNear.subLit_ff_n qz255 qz245 148668102860209 281474976710656 707192115 281474976710656 12192953 16777216 29 16777216 

noncomputable def Ns186p2057 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz245 12192953 16777216 29 16777216 12192953 16777216 29 16777216 148668102860209 281474976710656 

noncomputable def Ns186p2058 := nat_lit 72186661003288503488432453621424395299827417835741520904052975352124927024310382577763321075441 

noncomputable def Ns186p2059 := nat_lit 188846503566577330481618950600315587602793758254537846707129843015785956071205246667282161 

noncomputable def Ns186p2060 := nat_lit 436678425009236247776551811981628945667029345160865260351536928490527907565684850569360702396145 

noncomputable def Ns186p2061 := BSN.cos_dyadic_bound_t 27521731 16777216 4 3 8388608 2250000 Ns186p2058 Ns186p180 Ns186p2059 Ns186p2060 Ns186p183 Ns186p2059 583600 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 27521731) qz642 0 3 Ns186p2058 Ns186p180 Ns186p2059 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 27521731) (BSN.cosOddQ 16777216) 0 3 Ns186p2060 Ns186p183 Ns186p2059 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p2062 := @Ns186p2048 16012144 589824000000 36475 524288 1000759 36864000000 (@Ns186p2049 7 262144 Bool.true 583600 8388608 1 2250000 (@Ns186p2052 Ns186p2053 27521731 16777216 7 262144 (@Ns186p2054 281474976710656 1193731379 281474976710656 Ns186p2050 Ns186p1617 Ns186p2051 Ns186p2053 RS187to204.d39 (@Ns186p2055 0 1 1175806229488880 73487889343055 281474976710656 1193731379 281474976710656 (@Ns186p2056 937774287713179009024 55895703298639 281474976710656 1193731379 281474976710656 (@Ns186p2057 707192115 281474976710656 (Ns186p2038 rfl rfl) (Ns186p2038 rfl rfl) rfl) (Ns186p2038 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 27521731 16777216) (BSN.cos_neg_of_bound 27521731 16777216 Bool.true 583600 8388608 1 2250000 (Ns186p2061 rfl rfl)) rfl rfl) 

noncomputable def Ns186p2063 := @Ns186p2023 196724089021660589261 Ns186p1956 (Ns186p2024 qz28 (@Enclosure.Real.IsNear.of_eq qz831 (@Inv.inv Real Real.instInv (Real.sqrt qz248)) Bool.false 2839641 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz244 (BSN.t_div_two_pi_nonneg qz243 478504 1000 qz246)) Ns186p2028) rfl) (@Ns186p2029 274877906944 138451432829641 618475290624000000 (BSN.correction_mk qz245 (BSN.cos_two_pi_p_ne_zero_mk qz243 478504 1000 8 qz246 rfl rfl (@BSN.floor_sqrt_eq_dec qz243 478504 1000 8 qz246 rfl rfl rfl))) (@Ns186p2030 8388608 36475 524288 1000759 36864000000 131410853375 274877906944 138451432829641 618475290624000000 Ns186p2047 (Ns186p2062 rfl) rfl)) 

noncomputable def Ns186p2064 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz243) (hardyZApproximantRS₀ qz243) Bool.false 1733385609596470873 2305843009213693952 4273713204815068589261 Ns186p1956 (@Eq.refl Real (hardyZApproximantRS₀ qz243)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz243) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz243) qz243 8) (@HMul.hMul Real Real Real qz5 qz826 (Zeta.RiemannSiegel.correction qz245))) Bool.false 1733385609596470873 2305843009213693952 4273713204815068589261 Ns186p1956 (BSN.hardyZApproximantRS₀_eq qz243 8 (@BSN.floor_sqrt_eq_dec qz243 478504 1000 8 qz246 rfl rfl rfl)) (@Ns186p1958 1733385609596470873 2305843009213693952 4273713204815068589261 Ns186p1956 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz243) qz243 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 8)) Bool.false 7663567 8388608 103 65536 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz243) qz243 8) (Ns186p2022 (Ns186p2021 rfl rfl rfl rfl) rfl rfl)) (Ns186p2063 rfl) rfl rfl)) 

theorem RS187to204.d60 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz243) Bool.false 1733385609596470873 2305843009213693952 4273713204815068589261 Ns186p1956 := Ns186p2064 

noncomputable def Ns186p2065 := nat_lit 24659003037143860329475735552 

noncomputable abbrev qz967 := (Enclosure.sfrac Bool.false 479682 1000)

noncomputable abbrev qz835 := qz967

noncomputable abbrev qz596 := qz835

noncomputable abbrev qz256 := qz596

noncomputable abbrev qz968 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 479682 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz836 := qz968

noncomputable abbrev qz597 := qz836

noncomputable abbrev qz257 := qz597

noncomputable abbrev qz837 := (@HSub.hSub Real Real Real qz895 (Real.sqrt qz968) qz890)

noncomputable abbrev qz598 := qz837

noncomputable abbrev qz258 := qz598

noncomputable abbrev qz838 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz257 qz9))

noncomputable def Ns186p2066 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz256) qz256 8) (@HMul.hMul Real Real Real qz5 qz838 (Zeta.RiemannSiegel.correction qz258)) 323115497 67108864 105723 67108864 12178533069938342471 73786976294838206464 11379657259172541027613 Ns186p331 Ns186p2065 

noncomputable def Ns186p2067 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz256) qz256 Real.cos BSN.quadSignNeg 7 8 479682 1000 126 134217728 67108864 2251799813685248 Bool.false 107311926387 1869 279097919 60 47453128 8 

noncomputable def Ns186p2068 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz256) qz256 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 479682 1000 38 85 134217728 67108864 2251799813685248 Bool.false 107311926387 1869 

noncomputable def Ns186p2069 := Ns186p2068 240485871 61 54794152 8 261175631 61 50729528 8 Bool.true 204483518 70382 Bool.true 33326048 Bool.true 48881941 7074237752028440 1 Bool.false 130101538 Bool.true Bool.false 47808461 Bool.true Bool.true 275667141 

noncomputable def Ns186p2070 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz256) qz256 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 479682 1000 85 17 134217728 67108864 2251799813685248 Bool.false 107311926387 1869 

noncomputable def Ns186p2071 := Ns186p2070 186065264 60 67108856 8 216015088 60 60023992 8 Bool.true 103023422 41330 Bool.false 139327719 Bool.false 109288804 7074237752028440 1 Bool.false 115618752 Bool.true Bool.false 97605993 Bool.true Bool.true 204483518 

noncomputable def Ns186p2072 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz256) qz256 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 479682 1000 297 173 134217728 67108864 2251799813685248 Bool.false 107311926387 1869 

noncomputable def Ns186p2073 := Ns186p2072 93032624 60 94906264 8 147453232 60 77490640 16 Bool.true 110888 1932 Bool.false 69723143 Bool.false 107897609 7074237752028440 1 Bool.false 66629301 Bool.true Bool.false 96645846 Bool.true Bool.true 103023422 

noncomputable def Ns186p2074 := nat_lit 1370786603712998560979510171896213367482081027646763957 

noncomputable def Ns186p2075 := nat_lit 1714477315961045426656670117327212157331593756672000 

noncomputable def Ns186p2076 := nat_lit 12190163831546127657043510287360000 

noncomputable def Ns186p2077 := nat_lit 35084430791469933046551048064304517120 

noncomputable def Ns186p2078 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz256 479682 1000 920380284496 16000000 959364 4000 2000 Ns186p2076 Ns186p2077 (@Eq.refl Real qz256) rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns186p2079 := nat_lit 252663386796379894759743314883910047894297175015851532554240 

noncomputable abbrev qz839 := (Real.log (Enclosure.sfrac Bool.false 920380284496 16000000))

noncomputable abbrev qz259 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 479682 4000) qz839) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 959364))))))

noncomputable abbrev qz840 := (Enclosure.sfrac Bool.false 479682 2000)

noncomputable abbrev qz599 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz259 qz840) (@HMul.hMul Real Real Real qz5 qz840 (Real.log Real.pi)))

noncomputable def Ns186p2080 := @Enclosure.Real.IsNear.addLit_ft_p qz599 (Enclosure.sfrac Bool.true Ns186p2076 Ns186p2077) 7201584603078254080377 9007199254740992000 25659522134933009 1843200000000000000000 Ns186p2076 Ns186p2077 0 1 Ns186p2079 

noncomputable def Ns186p2081 := nat_lit 241645080856236267218732580864000 

noncomputable abbrev qz600 := (@HSub.hSub Real Real Real qz12 qz259 qz840)

noncomputable abbrev qz601 := (@HMul.hMul Real Real Real qz5 qz840 (Real.log Real.pi))

noncomputable def Ns186p2082 := @Enclosure.Real.IsNear.subLit_ff_p qz600 qz601 9674539618907387539833 9007199254740992000 24384106476157 3600000000000000000 9212475329001 33554432000 239841 33554432000 Ns186p2081 7201584603078254080377 9007199254740992000 

noncomputable def Ns186p2083 := nat_lit 3869815847562955015933200 

noncomputable abbrev qz602 := qz840

noncomputable def Ns186p2084 := @Enclosure.Real.IsNear.subLit_ff_p qz259 qz602 2366967059072744360421 1801439850948198400 24384106476157 3600000000000000000 479682 2000 0 1 Ns186p2083 9674539618907387539833 9007199254740992000 24384106476157 3600000000000000000 

noncomputable def Ns186p2085 := nat_lit 5329935982619125147488292328762769408 

noncomputable def Ns186p2086 := nat_lit 26499541507204520985231360 

noncomputable def Ns186p2087 := nat_lit 11168259831851740602653958129328519518096189406056817696918290524487719530539100333003121943731970358013636558482812543500675724622018739888300658524160 

noncomputable def Ns186p2088 := nat_lit 293189012733425944213184324096916368806279685894228445596732093666008011482099582792100386847335755089537362171821476855760857525305937710896279191552 

noncomputable def Ns186p2089 := nat_lit 155017628176169014319640407138691354928714566023536023717242280492647240727283685502885310214737626497267614023852380598883764711207517626040320 

noncomputable def Ns186p2090 := BSN.log_dyadic_bound 396092284496 1444668284496 7 6 Ns186p2087 67108864 18000000 Ns186p2088 Ns186p2089 37765230 1840760568992 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 396092284496) (BSN.artanhQ 1444668284496) 0 6 Ns186p2088 Ns186p2087 Ns186p2089 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns186p2091 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 479682 4000) qz839 479682 4000 0 1 49359242445238905 4503599627370496 100000027 1800000000000000 2367674013461708842821 1801439850948198400 2664900719523 400000000000000000 (Enclosure.Real.IsNear.const Bool.false 479682 4000) (BSN.isNear_log_sfrac 920380284496 16000000 49359242445238905 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 920380284496) qz353)) Bool.false Ns186p2086 Ns186p89 1000000270000000 18000000000000000000000 49359242445238905 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 920380284496 16000000 15 1840760568992 1048576000000 37765230 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns186p2090 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p2092 := BSN.arctan_dyadic_bound_f 1000 959364 1 0 8388608 2250000 0 1 1 0 1 1 8743 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 959364) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 959364) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz841 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 959364)))

noncomputable def Ns186p2093 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz841 884279719003555 562949953421312 1 2000000000000000 8743 8388608 1 2250000 7412954053628210970624 883692986205603 562949953421312 8000000009 18000000000000000 qz16 (Ns186p2092 rfl) rfl rfl 

noncomputable def Ns186p2094 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 479682 4000) qz839) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz841)) 2367674013461708842821 1801439850948198400 2664900719523 400000000000000000 883692986205603 2251799813685248 8000000009 72000000000000000 Ns186p2085 2366967059072744360421 1801439850948198400 24384106476157 3600000000000000000 (Ns186p2091 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz841) 1 4 0 1 883692986205603 562949953421312 8000000009 18000000000000000 883692986205603 2251799813685248 8000000009 72000000000000000 qz356 Ns186p2093 rfl) 

noncomputable def Ns186p2095 := @Ns186p2080 Ns186p2074 Ns186p2075 25659522134933009 1843200000000000000000 (@Ns186p2082 25659522134933009 1843200000000000000000 (Ns186p2084 (Ns186p2094 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 479682 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz602 (Real.log Real.pi) 479682 2000 0 1 38410761 33554432 1 33554432 9212475329001 33554432000 239841 33554432000 (Enclosure.Real.IsNear.const Bool.false 479682 2000) RS187to204.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns186p2076 Ns186p2077) 

noncomputable def Ns186p2096 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz256) Bool.false Ns186p2074 Ns186p2075 25659522134933009 1843200000000000000000 6706995399 8388608 117 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz256) (@HAdd.hAdd Real Real Real qz357 qz599 (Enclosure.sfrac Bool.true Ns186p2076 Ns186p2077)) Bool.false Ns186p2074 Ns186p2075 25659522134933009 1843200000000000000000 Ns186p2078 (Ns186p2095 rfl rfl)) 

noncomputable def Ns186p2097 := BSN.sin_dyadic_bound_f 28387897 34359738368 1 0 16777216 4504395 0 1 1 0 1 1 13861 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 28387897) qz358 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 28387897) qz359 0 0 rfl) rfl rfl 

noncomputable def Ns186p2098 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz256) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6706995399) qz429) Bool.false 6706995399 8388608 117 8388608 Bool.true 13861 16777216 1 2250000 (Ns186p2096 rfl) (Enclosure.sfrac_false_div 6706995399 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6706995399) qz429) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 998810336865359495168) qz430) 226375608064910080 72057594037927936 Bool.false 13861 16777216 127 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 6706995399 8388608 226375608064910080 72057594037927936 127 998810336865359495168 Ns186p578 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 13861 16777216 998810336865359495168 Ns186p578 28387897 34359738368 4504395 4500000 (Ns186p2097 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p2099 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz256) Bool.false Ns186p2074 Ns186p2075 25659522134933009 1843200000000000000000 107311926387 134217728 1869 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz256) (@HAdd.hAdd Real Real Real qz357 qz599 (Enclosure.sfrac Bool.true Ns186p2076 Ns186p2077)) Bool.false Ns186p2074 Ns186p2075 25659522134933009 1843200000000000000000 Ns186p2078 (Ns186p2095 rfl rfl)) 

noncomputable def Ns186p2100 := Ns186p2073 41330 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 297 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66629301 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 173 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 96645846 134217728) (@Eq.refl Real qz256) rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 1) Bool.true 13861 16777216 16977413 1179648000000 110888 134217728 1932 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz256)) Bool.true 13861 16777216 16977413 1179648000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz256) qz256) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz256)) Bool.true 13861 16777216 271638608 18874368000000 13861 16777216 16977413 1179648000000 (Ns186p2098 rfl rfl) rfl)) rfl) (Ns186p2099 rfl) RS187to204.d7 

noncomputable def Ns186p2101 := nat_lit 23192074715632226108332944603867987738309879706879304872995852375745 

noncomputable def Ns186p2102 := nat_lit 558490318608356492557736598832569717325697307923410467956971201 

noncomputable def Ns186p2103 := nat_lit 60740243842330464373217380484208524677935919531899636764707683030721 

noncomputable def Ns186p2104 := BSN.sin_dyadic_bound_f 69723143 134217728 3 2 134217728 67108864 Ns186p2101 Ns186p111 Ns186p2102 Ns186p2103 Ns186p114 Ns186p2102 66629301 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 69723143) qz362 0 2 Ns186p2101 Ns186p111 Ns186p2102 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 69723143) qz363 0 2 Ns186p2103 Ns186p114 Ns186p2102 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p2105 := nat_lit 133023563699405584460125514069668597302757761665164565331436988215105 

noncomputable def Ns186p2106 := nat_lit 18369382902471836715640607003961907993388328917887466212639321921 

noncomputable def Ns186p2107 := nat_lit 348365306878505862040884356818744673656185794685754424732276410232641 

noncomputable def Ns186p2108 := BSN.sin_dyadic_bound_f 107897609 134217728 3 2 134217728 67108864 Ns186p2105 Ns186p111 Ns186p2106 Ns186p2107 Ns186p114 Ns186p2106 96645846 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 107897609) qz362 0 2 Ns186p2105 Ns186p111 Ns186p2106 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 107897609) qz363 0 2 Ns186p2107 Ns186p114 Ns186p2106 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p2109 := nat_lit 369945852860445487325177922782589343278442994096390802420760922646465 

noncomputable def Ns186p2110 := nat_lit 142003882017759844699214474879259618198068350762532394184324245441 

noncomputable def Ns186p2111 := nat_lit 968675894063614188960238688614119954918839540541693715797123034343361 

noncomputable def Ns186p2112 := BSN.sin_dyadic_bound_f 139327719 134217728 3 2 134217728 67108864 Ns186p2109 Ns186p111 Ns186p2110 Ns186p2111 Ns186p114 Ns186p2110 115618752 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 139327719) qz362 0 2 Ns186p2109 Ns186p111 Ns186p2110 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 139327719) qz363 0 2 Ns186p2111 Ns186p114 Ns186p2110 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p2113 := nat_lit 140019054753510824627495964828910080750224032835439392429221204787200 

noncomputable def Ns186p2114 := nat_lit 20351919977469972266857666730331106932816628381559034091772379136 

noncomputable def Ns186p2115 := nat_lit 366683621245898160735962138329582056363171716218294932211811714400256 

noncomputable def Ns186p2116 := BSN.sin_dyadic_bound_f 109288804 134217728 3 2 134217728 67108864 Ns186p2113 Ns186p111 Ns186p2114 Ns186p2115 Ns186p114 Ns186p2114 97605993 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 109288804) qz362 0 2 Ns186p2113 Ns186p111 Ns186p2114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 109288804) qz363 0 2 Ns186p2115 Ns186p114 Ns186p2114 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p2117 := Ns186p2071 70382 BSN.abs_quadSignNeg qz794 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 115618752 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 17 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 97605993 134217728) (@Eq.refl Real qz256) rfl rfl (Ns186p2100 RS187to204.d9 RS187to204.d11 RS187to204.d13 RS187to204.d17 (Ns186p2104 rfl rfl) (Ns186p2108 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns186p2099 rfl) RS187to204.d19 RS187to204.d21 RS187to204.d23 RS187to204.d25 RS187to204.d17 (Ns186p2112 rfl rfl) (Ns186p2116 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns186p2118 := nat_lit 1233488946381583668477785276416 

noncomputable def Ns186p2119 := BSN.cos_dyadic_bound_f 33326048 134217728 2 1 134217728 67108864 Ns186p2118 Ns186p134 Ns186p2118 Ns186p2118 Ns186p135 Ns186p2118 130101538 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 33326048) qz364 0 1 Ns186p2118 Ns186p134 Ns186p2118 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 33326048) qz365 0 1 Ns186p2118 Ns186p135 Ns186p2118 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p2120 := nat_lit 5709443374295992134507331005361 

noncomputable def Ns186p2121 := BSN.sin_dyadic_bound_f 48881941 134217728 2 1 134217728 67108864 Ns186p2120 Ns186p123 Ns186p2120 Ns186p2120 Ns186p124 Ns186p2120 47808461 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 48881941) qz362 0 1 Ns186p2120 Ns186p123 Ns186p2120 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 48881941) qz363 0 1 Ns186p2120 Ns186p124 Ns186p2120 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p2122 := Ns186p2069 94876 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 130101538 134217728) BSN.abs_quadSignNeg qz794 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 47808461 134217728) (@Eq.refl Real qz256) rfl rfl (Ns186p2117 rfl rfl) (Ns186p2099 rfl) RS187to204.d27 RS187to204.d29 RS187to204.d31 RS187to204.d33 RS187to204.d17 (Ns186p2119 rfl rfl) (Ns186p2121 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns186p2123 := BSN.cos_dyadic_bound_f 1903613 134217728 1 0 134217728 67108864 0 1 1 0 1 1 134204228 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 1903613) qz364 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 1903613) qz365 0 0 rfl) rfl rfl 

noncomputable def Ns186p2124 := Ns186p2067 Bool.true 275667141 94876 Bool.true 1903613 7074237752028440 1 Bool.false 134204228 Bool.true Bool.true 323115497 105723 BSN.abs_quadSignNeg qz431 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 134204228 134217728) (@Eq.refl Real qz256) rfl (Ns186p2122 rfl) (Ns186p2099 rfl) RS187to204.d35 RS187to204.d37 RS187to204.d17 (Ns186p2123 rfl rfl) rfl 

noncomputable def Ns186p2125 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 8) 323115497 134217728 105723 134217728 323115497 134217728 105723 134217728 86735655777861632 323115497 67108864 105723 67108864 (Ns186p2124 rfl rfl rfl rfl) 

noncomputable def Ns186p2126 := @Enclosure.Real.IsNear.mulLit_ff qz838 (Zeta.RiemannSiegel.correction qz258) 354737 1048576 1 8388608 34331161028983 70368744177664 2004094834952227 4947802324992000000 12178533069938342471 73786976294838206464 

noncomputable abbrev qz842 := (@HPow.hPow Real Real Real qz7 qz257 qz9)

noncomputable def Ns186p2127 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz842 1 1 0 1 354737 1048576 1 8388608 354737 1048576 1 8388608 

noncomputable def Ns186p2128 := @Enclosure.Real.IsNear.sqrt_image qz257 640417921857 8388608000 239841 8388608000 73295381 73295409 8388608 (@Enclosure.Real.IsNear.of_eq qz257 (@HMul.hMul Real Real Real qz5 qz256 qz3) Bool.false 640417921857 8388608000 239841 8388608000 (BSN.t_div_two_pi_mk qz256 479682 1000 (@Eq.refl Real qz256)) (@Enclosure.Real.IsNear.mulLit_ff qz256 qz3 479682 1000 0 1 2670177 16777216 1 16777216 640417921857 8388608000 239841 8388608000 (Enclosure.Real.IsNear.const Bool.false 479682 1000) RS187to204.d40 rfl)) 

noncomputable abbrev qz843 := (Real.sqrt qz968)

noncomputable abbrev qz603 := qz843

noncomputable abbrev qz260 := qz603

noncomputable def Ns186p2129 := @Enclosure.Real.IsNear.sqrt_image qz260 73295395 8388608 7 4194304 24796092 24796098 8388608 (@Enclosure.Real.IsNear.recentre' qz260 Bool.false 146590790 16777216 28 16777216 73295395 8388608 7 4194304 (Ns186p2128 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns186p2130 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz260) 24796095 8388608 3 8388608 2837895 2837897 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz260) Bool.false 49592190 16777216 6 16777216 24796095 8388608 3 8388608 (Ns186p2129 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns186p2131 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz260)) Bool.false 5675792 16777216 2 16777216 354737 1048576 1 8388608 (Ns186p2130 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz261 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz598))

noncomputable abbrev qz604 := (@HSub.hSub Real Real Real qz633 (@HMul.hMul Real Real Real qz628 qz837 qz837) qz837)

noncomputable abbrev qz262 := (@HMul.hMul Real Real Real qz342 qz340 (@HSub.hSub Real Real Real qz345 qz604 qz374))

noncomputable def Ns186p2132 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz258) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz261) (Real.cos qz262)) Bool.false 34331161028983 

noncomputable def Ns186p2133 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz261) (Real.cos qz262) 106848469 8388608 3741 

noncomputable abbrev qz844 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz261))

noncomputable def Ns186p2134 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz261) (@Neg.neg Real Real.instNeg qz844) Bool.true 106848469 8388608 3741 2097152 (BSN.inv_eq_neg_inv_neg qz261) 

noncomputable def Ns186p2135 := @Enclosure.Real.IsNear.recentre' qz844 Bool.false 213696938 16777216 29928 16777216 106848469 8388608 

noncomputable def Ns186p2136 := @Enclosure.Real.IsNear.recentre' qz261 Bool.true 1317169 16777216 415027216 37748736000000 1317169 16777216 25939201 2359296000000 

noncomputable abbrev qz263 := (@HMul.hMul Real Real Real qz342 qz340 qz598)

noncomputable def Ns186p2137 := @Enclosure.Real.IsNear.cos_image qz263 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 77742241) qz360) Bool.false 77742241 16777216 177 16777216 Bool.true 1317169 16777216 1 

noncomputable def Ns186p2138 := nat_lit 37780505577975853301374589 

noncomputable def Ns186p2139 := nat_lit 3602879701896396800000000000000 

noncomputable def Ns186p2140 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz258 884279719003555 140737488355328 1 500000000000000 6186531 8388608 7 4194304 5470623894286782117705 1180591620717411303424 Ns186p2138 

noncomputable def Ns186p2141 := @Enclosure.Real.IsNear.subLit_ff_p qz260 qz1 73295395 8388608 7 4194304 8 1 0 1 6186531 6186531 8388608 7 

noncomputable def Ns186p2142 := @Ns186p2141 4194304 (@Enclosure.Real.IsNear.recentre' qz260 Bool.false 146590790 16777216 28 16777216 73295395 8388608 7 4194304 (Ns186p2128 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns186p2143 := @Enclosure.Real.IsNear.recentre' qz263 Bool.false 5470623894286782117705 1180591620717411303424 Ns186p2138 Ns186p2139 77742241 16777216 177 16777216 (@Ns186p2140 Ns186p2139 RS187to204.d39 (Ns186p2142 rfl rfl) rfl) 

noncomputable def Ns186p2144 := nat_lit 3607932735880836616814592 

noncomputable def Ns186p2145 := nat_lit 268732004664613096023469637660920973304390298245053250621540622450533481084453758506762599277550747881307548457942225610988059314377041 

noncomputable def Ns186p2146 := nat_lit 330022522948073978271199661820135066440807581406656697338309082028569819794537974009259991095257833082724415400732721441643188561 

noncomputable def Ns186p2147 := nat_lit 1627107636531951176189230222340064988005147739026803785969095446687465418648162777829695872208516218988052674868155615665790289255354705 

noncomputable def Ns186p2148 := BSN.cos_dyadic_bound_f 51271807931 34359738368 4 3 16777216 4504395 Ns186p2145 Ns186p1931 Ns186p2146 Ns186p2147 Ns186p1934 Ns186p2146 1317169 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 51271807931) qz371 0 3 Ns186p2145 Ns186p1931 Ns186p2146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 51271807931) qz372 0 3 Ns186p2147 Ns186p1934 Ns186p2146 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p2149 := @Ns186p2137 2250000 (Ns186p2143 rfl) (Enclosure.sfrac_false_div 77742241 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 77742241) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns186p2144) qz361) 226375608064910080 72057594037927936 Bool.false 1317169 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 77742241 16777216 226375608064910080 72057594037927936 0 Ns186p2144 Ns186p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1317169 16777216 Ns186p2144 Ns186p89 51271807931 34359738368 4504395 4500000 (Ns186p2148 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns186p2150 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz261) 1317169 16777216 25939201 2359296000000 106833505 106863433 8388608 (@Enclosure.Real.IsNear.neg qz261 Bool.true 1317169 16777216 25939201 2359296000000 (Ns186p2136 (Ns186p2149 rfl rfl) rfl)) 

noncomputable def Ns186p2151 := Ns186p2134 (@Enclosure.Real.IsNear.neg qz844 Bool.false 106848469 8388608 3741 2097152 (@Ns186p2135 3741 2097152 (Ns186p2150 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns186p2152 := @Enclosure.Real.IsNear.recentre' (Real.cos qz262) Bool.true 321307 8388608 

noncomputable def Ns186p2153 := @Enclosure.Real.IsNear.cos_image qz262 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3374545)) qz649) Bool.true 3374545 2097152 

noncomputable def Ns186p2154 := nat_lit 15935838386262964860532448005 

noncomputable def Ns186p2155 := nat_lit 980483647594150809212409714443333 

noncomputable def Ns186p2156 := @Enclosure.Real.IsNear.recentre' qz262 Bool.true Ns186p2154 Ns186p427 Ns186p2155 

noncomputable abbrev qz264 := (@HSub.hSub Real Real Real qz345 qz604 qz374)

noncomputable def Ns186p2157 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz264 884279719003555 140737488355328 1 500000000000000 18021264135991 

noncomputable abbrev qz265 := qz604

noncomputable def Ns186p2158 := @Enclosure.Real.IsNear.subLit_tf qz265 qz26 13623217624887 70368744177664 36332947 8796093022208 1 16 

noncomputable abbrev qz605 := (@HMul.hMul Real Real Real qz628 qz837 qz837)

noncomputable abbrev qz266 := qz605

noncomputable def Ns186p2159 := @Enclosure.Real.IsNear.subLit_ff_n qz266 qz258 38273165813961 70368744177664 21652883 8796093022208 6186531 8388608 7 4194304 

noncomputable def Ns186p2160 := @Enclosure.Real.IsNear.mulLit_ff qz258 qz258 6186531 8388608 7 4194304 6186531 8388608 7 4194304 38273165813961 70368744177664 

noncomputable def Ns186p2161 := nat_lit 972201944920285458819641803111353943630919659033630775113892170541234956662571890625 

noncomputable def Ns186p2162 := nat_lit 2180633535272882464318257824634016809420804333906106652902951893448652587890625 

noncomputable def Ns186p2163 := nat_lit 5882385603957497757937239170681308148556396671517382340327563675407510727004357490625 

noncomputable def Ns186p2164 := BSN.cos_dyadic_bound_t 3374545 2097152 4 3 8388608 2250000 Ns186p2161 Ns186p292 Ns186p2162 Ns186p2163 Ns186p295 Ns186p2162 321307 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3374545) (BSN.cosEvenQ 2097152) 0 3 Ns186p2161 Ns186p292 Ns186p2162 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3374545) (BSN.cosOddQ 2097152) 0 3 Ns186p2163 Ns186p295 Ns186p2162 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns186p2165 := @Ns186p2152 249444304 9437184000000 321307 8388608 15590269 589824000000 (@Ns186p2153 109 4194304 Bool.true 321307 8388608 1 2250000 (@Ns186p2156 Ns186p430 3374545 2097152 109 4194304 (@Ns186p2157 70368744177664 36332947 8796093022208 Ns186p2154 Ns186p427 Ns186p2155 Ns186p430 RS187to204.d39 (@Ns186p2158 0 1 288340226175856 18021264135991 70368744177664 36332947 8796093022208 (@Ns186p2159 114279832353868087296 13623217624887 70368744177664 36332947 8796093022208 (@Ns186p2160 21652883 8796093022208 (Ns186p2142 rfl rfl) (Ns186p2142 rfl rfl) rfl) (Ns186p2142 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 3374545 2097152) (BSN.cos_neg_of_bound 3374545 2097152 Bool.true 321307 8388608 1 2250000 (Ns186p2164 rfl rfl)) rfl rfl) 

noncomputable def Ns186p2166 := @Ns186p2126 11379657259172541027613 Ns186p331 (Ns186p2127 qz28 (@Enclosure.Real.IsNear.of_eq qz842 (@Inv.inv Real Real.instInv (Real.sqrt qz260)) Bool.false 354737 1048576 1 8388608 (BSN.rpow_neg_quarter_mk qz257 (BSN.t_div_two_pi_nonneg qz256 479682 1000 (@Eq.refl Real qz256))) Ns186p2131) rfl) (@Ns186p2132 70368744177664 2004094834952227 4947802324992000000 (BSN.correction_mk qz258 (BSN.cos_two_pi_p_ne_zero_mk qz256 479682 1000 8 (@Eq.refl Real qz256) rfl rfl (@BSN.floor_sqrt_eq_dec qz256 479682 1000 8 (@Eq.refl Real qz256) rfl rfl rfl))) (@Ns186p2133 2097152 321307 8388608 15590269 589824000000 34331161028983 70368744177664 2004094834952227 4947802324992000000 Ns186p2151 (Ns186p2165 rfl) rfl)) 

noncomputable def Ns186p2167 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz256) (hardyZApproximantRS₀ qz256) Bool.true 367447779136059587143 73786976294838206464 142153783560454845027613 Ns186p331 (@Eq.refl Real (hardyZApproximantRS₀ qz256)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz256) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz256) qz256 8) (@HMul.hMul Real Real Real qz5 qz838 (Zeta.RiemannSiegel.correction qz258))) Bool.true 367447779136059587143 73786976294838206464 142153783560454845027613 Ns186p331 (BSN.hardyZApproximantRS₀_eq qz256 8 (@BSN.floor_sqrt_eq_dec qz256 479682 1000 8 (@Eq.refl Real qz256) rfl rfl rfl)) (@Ns186p2066 367447779136059587143 73786976294838206464 142153783560454845027613 Ns186p331 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz256) qz256 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 8)) Bool.true 323115497 67108864 105723 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz256) qz256 8) (Ns186p2125 (Ns186p2124 rfl rfl rfl rfl) rfl rfl)) (Ns186p2166 rfl) rfl rfl)) 

theorem RS187to204.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz256) Bool.true 367447779136059587143 73786976294838206464 142153783560454845027613 Ns186p331 := Ns186p2167 

noncomputable def RS187to204.d62 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz267 := (RS187to204.d3 qz341 qz377 (@Enclosure.dec_le_dec qz341 qz377 454159 1000 455626 1000 (@Eq.refl Real qz341) qz380 rfl rfl rfl))

noncomputable abbrev qz845 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz267)

noncomputable def Ns186p2168 := @Enclosure.Real.IsNear.of_eq qz845 (hardyZApproximantRS₀ qz4) Bool.true 95846853962433437863 147573952589676412928 221461939623134142079 147573952589676412928000 

noncomputable abbrev qz268 := (@Enclosure.dec_le_dec qz341 qz377 454159 1000 455626 1000 (@Eq.refl Real qz341) qz380 rfl rfl rfl)

noncomputable def Ns186p2169 := @Enclosure.Real.IsNear.neg_val qz845 95846853962433437863 147573952589676412928 221461939623134142079 147573952589676412928000 (Ns186p2168 (RS187to204.d4 qz4 qz29 qz268) RS187to204.d41) rfl 

noncomputable abbrev qz846 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz267)

noncomputable def Ns186p2170 := @Enclosure.Real.IsNear.of_eq qz846 (hardyZApproximantRS₀ qz29) Bool.false 1721309008474231659735 1180591620717411303424 27774805864762262209839 Ns186p188 

noncomputable def Ns186p2171 := @Enclosure.Real.IsNear.pos_val qz846 1721309008474231659735 1180591620717411303424 27774805864762262209839 Ns186p188 (Ns186p2170 (RS187to204.d42 qz4 qz29 qz268) RS187to204.d43) rfl 

noncomputable def Ns186p2172 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz845 qz4 qz4 454159 1000 454159 1000 

noncomputable def Ns186p2173 := @Enclosure.norm_gt_of_isNear qz845 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 95846853962433437863 147573952589676412928 221461939623134142079 

noncomputable def Ns186p2174 := @Ns186p2173 147573952589676412928000 220374661 2684354560 2421 2684354560 (Ns186p2168 (RS187to204.d4 qz4 qz29 qz268) RS187to204.d41) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2175 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz846 qz4 qz29 454159 1000 455626 1000 

noncomputable def Ns186p2176 := @Enclosure.norm_gt_of_isNear qz846 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1721309008474231659735 1180591620717411303424 27774805864762262209839 

noncomputable def Ns186p2177 := @Ns186p2176 Ns186p188 220374661 2684354560 2421 2684354560 (Ns186p2170 (RS187to204.d42 qz4 qz29 qz268) RS187to204.d43) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2178 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz267 (@BSN.thirtyTwoPi_le_dec qz4 454159 1000 qz11 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz845 qz846 (Ns186p2169 rfl rfl) (Ns186p2171 rfl rfl)) (Ns186p2172 qz11 qz11 rfl rfl rfl rfl (Ns186p2174 rfl)) (Ns186p2175 qz11 qz32 rfl rfl rfl rfl (Ns186p2177 rfl)) 

noncomputable abbrev qz269 := (RS187to204.d3 qz377 qz394 (@Enclosure.dec_le_dec qz377 qz394 455626 1000 457092 1000 qz380 qz397 rfl rfl rfl))

noncomputable abbrev qz847 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz269)

noncomputable def Ns186p2179 := @Enclosure.Real.IsNear.of_eq qz847 (hardyZApproximantRS₀ qz29) Bool.false 1721309008474231659735 1180591620717411303424 27774805864762262209839 Ns186p188 

noncomputable abbrev qz270 := (@Enclosure.dec_le_dec qz377 qz394 455626 1000 457092 1000 qz380 qz397 rfl rfl rfl)

noncomputable def Ns186p2180 := @Enclosure.Real.IsNear.pos_val qz847 1721309008474231659735 1180591620717411303424 27774805864762262209839 Ns186p188 (Ns186p2179 (RS187to204.d4 qz29 qz48 qz270) RS187to204.d43) rfl 

noncomputable abbrev qz848 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz269)

noncomputable def Ns186p2181 := @Enclosure.Real.IsNear.of_eq qz848 (hardyZApproximantRS₀ qz48) Bool.true 1161564560062668722043 590295810358705651712 125392105094017626199597 Ns186p331 

noncomputable def Ns186p2182 := @Enclosure.Real.IsNear.neg_val qz848 1161564560062668722043 590295810358705651712 125392105094017626199597 Ns186p331 (Ns186p2181 (RS187to204.d42 qz29 qz48 qz270) RS187to204.d45) rfl 

noncomputable def Ns186p2183 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz847 qz4 qz29 454159 1000 455626 1000 

noncomputable def Ns186p2184 := @Enclosure.norm_gt_of_isNear qz847 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1721309008474231659735 1180591620717411303424 27774805864762262209839 

noncomputable def Ns186p2185 := @Ns186p2184 Ns186p188 220374661 2684354560 2421 2684354560 (Ns186p2179 (RS187to204.d4 qz29 qz48 qz270) RS187to204.d43) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2186 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz848 qz4 qz48 454159 1000 457092 1000 

noncomputable def Ns186p2187 := @Enclosure.norm_gt_of_isNear qz848 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1161564560062668722043 590295810358705651712 125392105094017626199597 

noncomputable def Ns186p2188 := @Ns186p2187 Ns186p331 220374661 2684354560 2421 2684354560 (Ns186p2181 (RS187to204.d42 qz29 qz48 qz270) RS187to204.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2189 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz269 (@BSN.thirtyTwoPi_le_dec qz29 455626 1000 qz32 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz847 qz848 (Ns186p2180 rfl rfl) (Ns186p2182 rfl rfl)) (Ns186p2183 qz11 qz32 rfl rfl rfl rfl (Ns186p2185 rfl)) (Ns186p2186 qz11 qz51 rfl rfl rfl rfl (Ns186p2188 rfl)) 

noncomputable abbrev qz271 := (RS187to204.d3 qz394 qz407 (@Enclosure.dec_le_dec qz394 qz407 457092 1000 458557 1000 qz397 qz410 rfl rfl rfl))

noncomputable abbrev qz849 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz271)

noncomputable def Ns186p2190 := @Enclosure.Real.IsNear.of_eq qz849 (hardyZApproximantRS₀ qz48) Bool.true 1161564560062668722043 590295810358705651712 125392105094017626199597 Ns186p331 

noncomputable abbrev qz272 := (@Enclosure.dec_le_dec qz394 qz407 457092 1000 458557 1000 qz397 qz410 rfl rfl rfl)

noncomputable def Ns186p2191 := @Enclosure.Real.IsNear.neg_val qz849 1161564560062668722043 590295810358705651712 125392105094017626199597 Ns186p331 (Ns186p2190 (RS187to204.d4 qz48 qz61 qz272) RS187to204.d45) rfl 

noncomputable abbrev qz850 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz271)

noncomputable def Ns186p2192 := @Enclosure.Real.IsNear.of_eq qz850 (hardyZApproximantRS₀ qz61) Bool.false 1931431128150111240693 1180591620717411303424 83879646732931558858933 Ns186p442 

noncomputable def Ns186p2193 := @Enclosure.Real.IsNear.pos_val qz850 1931431128150111240693 1180591620717411303424 83879646732931558858933 Ns186p442 (Ns186p2192 (RS187to204.d42 qz48 qz61 qz272) RS187to204.d46) rfl 

noncomputable def Ns186p2194 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz849 qz4 qz48 454159 1000 457092 1000 

noncomputable def Ns186p2195 := @Enclosure.norm_gt_of_isNear qz849 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1161564560062668722043 590295810358705651712 125392105094017626199597 

noncomputable def Ns186p2196 := @Ns186p2195 Ns186p331 220374661 2684354560 2421 2684354560 (Ns186p2190 (RS187to204.d4 qz48 qz61 qz272) RS187to204.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2197 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz850 qz4 qz61 454159 1000 458557 1000 

noncomputable def Ns186p2198 := @Enclosure.norm_gt_of_isNear qz850 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1931431128150111240693 1180591620717411303424 83879646732931558858933 

noncomputable def Ns186p2199 := @Ns186p2198 Ns186p442 220374661 2684354560 2421 2684354560 (Ns186p2192 (RS187to204.d42 qz48 qz61 qz272) RS187to204.d46) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2200 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz271 (@BSN.thirtyTwoPi_le_dec qz48 457092 1000 qz51 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz849 qz850 (Ns186p2191 rfl rfl) (Ns186p2193 rfl rfl)) (Ns186p2194 qz11 qz51 rfl rfl rfl rfl (Ns186p2196 rfl)) (Ns186p2197 qz11 qz64 rfl rfl rfl rfl (Ns186p2199 rfl)) 

noncomputable abbrev qz273 := (RS187to204.d3 qz407 qz420 (@Enclosure.dec_le_dec qz407 qz420 458557 1000 460021 1000 qz410 qz423 rfl rfl rfl))

noncomputable abbrev qz851 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz273)

noncomputable def Ns186p2201 := @Enclosure.Real.IsNear.of_eq qz851 (hardyZApproximantRS₀ qz61) Bool.false 1931431128150111240693 1180591620717411303424 83879646732931558858933 Ns186p442 

noncomputable abbrev qz274 := (@Enclosure.dec_le_dec qz407 qz420 458557 1000 460021 1000 qz410 qz423 rfl rfl rfl)

noncomputable def Ns186p2202 := @Enclosure.Real.IsNear.pos_val qz851 1931431128150111240693 1180591620717411303424 83879646732931558858933 Ns186p442 (Ns186p2201 (RS187to204.d4 qz61 qz74 qz274) RS187to204.d46) rfl 

noncomputable abbrev qz852 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz273)

noncomputable def Ns186p2203 := @Enclosure.Real.IsNear.of_eq qz852 (hardyZApproximantRS₀ qz74) Bool.true 296927754959342551663 2361183241434822606848 11222332373474868956217 Ns186p544 

noncomputable def Ns186p2204 := @Enclosure.Real.IsNear.neg_val qz852 296927754959342551663 2361183241434822606848 11222332373474868956217 Ns186p544 (Ns186p2203 (RS187to204.d42 qz61 qz74 qz274) RS187to204.d47) rfl 

noncomputable def Ns186p2205 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz851 qz4 qz61 454159 1000 458557 1000 

noncomputable def Ns186p2206 := @Enclosure.norm_gt_of_isNear qz851 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1931431128150111240693 1180591620717411303424 83879646732931558858933 

noncomputable def Ns186p2207 := @Ns186p2206 Ns186p442 220374661 2684354560 2421 2684354560 (Ns186p2201 (RS187to204.d4 qz61 qz74 qz274) RS187to204.d46) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2208 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz852 qz4 qz74 454159 1000 460021 1000 

noncomputable def Ns186p2209 := @Enclosure.norm_gt_of_isNear qz852 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 296927754959342551663 2361183241434822606848 11222332373474868956217 

noncomputable def Ns186p2210 := @Ns186p2209 Ns186p544 220374661 2684354560 2421 2684354560 (Ns186p2203 (RS187to204.d42 qz61 qz74 qz274) RS187to204.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2211 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz273 (@BSN.thirtyTwoPi_le_dec qz61 458557 1000 qz64 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz851 qz852 (Ns186p2202 rfl rfl) (Ns186p2204 rfl rfl)) (Ns186p2205 qz11 qz64 rfl rfl rfl rfl (Ns186p2207 rfl)) (Ns186p2208 qz11 qz77 rfl rfl rfl rfl (Ns186p2210 rfl)) 

noncomputable abbrev qz275 := (RS187to204.d3 qz420 qz436 (@Enclosure.dec_le_dec qz420 qz436 460021 1000 461484 1000 qz423 qz439 rfl rfl rfl))

noncomputable abbrev qz853 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz275)

noncomputable def Ns186p2212 := @Enclosure.Real.IsNear.of_eq qz853 (hardyZApproximantRS₀ qz74) Bool.true 296927754959342551663 2361183241434822606848 11222332373474868956217 Ns186p544 

noncomputable abbrev qz276 := (@Enclosure.dec_le_dec qz420 qz436 460021 1000 461484 1000 qz423 qz439 rfl rfl rfl)

noncomputable def Ns186p2213 := @Enclosure.Real.IsNear.neg_val qz853 296927754959342551663 2361183241434822606848 11222332373474868956217 Ns186p544 (Ns186p2212 (RS187to204.d4 qz74 qz87 qz276) RS187to204.d47) rfl 

noncomputable abbrev qz854 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz275)

noncomputable def Ns186p2214 := @Enclosure.Real.IsNear.of_eq qz854 (hardyZApproximantRS₀ qz87) Bool.false 3788103783076631756315 1180591620717411303424 50673039119978730977999 Ns186p651 

noncomputable def Ns186p2215 := @Enclosure.Real.IsNear.pos_val qz854 3788103783076631756315 1180591620717411303424 50673039119978730977999 Ns186p651 (Ns186p2214 (RS187to204.d42 qz74 qz87 qz276) RS187to204.d48) rfl 

noncomputable def Ns186p2216 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz853 qz4 qz74 454159 1000 460021 1000 

noncomputable def Ns186p2217 := @Enclosure.norm_gt_of_isNear qz853 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 296927754959342551663 2361183241434822606848 11222332373474868956217 

noncomputable def Ns186p2218 := @Ns186p2217 Ns186p544 220374661 2684354560 2421 2684354560 (Ns186p2212 (RS187to204.d4 qz74 qz87 qz276) RS187to204.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2219 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz854 qz4 qz87 454159 1000 461484 1000 

noncomputable def Ns186p2220 := @Enclosure.norm_gt_of_isNear qz854 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 3788103783076631756315 1180591620717411303424 50673039119978730977999 

noncomputable def Ns186p2221 := @Ns186p2220 Ns186p651 220374661 2684354560 2421 2684354560 (Ns186p2214 (RS187to204.d42 qz74 qz87 qz276) RS187to204.d48) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2222 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz275 (@BSN.thirtyTwoPi_le_dec qz74 460021 1000 qz77 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz853 qz854 (Ns186p2213 rfl rfl) (Ns186p2215 rfl rfl)) (Ns186p2216 qz11 qz77 rfl rfl rfl rfl (Ns186p2218 rfl)) (Ns186p2219 qz11 qz90 rfl rfl rfl rfl (Ns186p2221 rfl)) 

noncomputable abbrev qz277 := (RS187to204.d3 qz436 qz449 (@Enclosure.dec_le_dec qz436 qz449 461484 1000 462946 1000 qz439 qz452 rfl rfl rfl))

noncomputable abbrev qz855 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz277)

noncomputable def Ns186p2223 := @Enclosure.Real.IsNear.of_eq qz855 (hardyZApproximantRS₀ qz87) Bool.false 3788103783076631756315 1180591620717411303424 50673039119978730977999 Ns186p651 

noncomputable abbrev qz278 := (@Enclosure.dec_le_dec qz436 qz449 461484 1000 462946 1000 qz439 qz452 rfl rfl rfl)

noncomputable def Ns186p2224 := @Enclosure.Real.IsNear.pos_val qz855 3788103783076631756315 1180591620717411303424 50673039119978730977999 Ns186p651 (Ns186p2223 (RS187to204.d4 qz87 qz100 qz278) RS187to204.d48) rfl 

noncomputable abbrev qz856 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz277)

noncomputable def Ns186p2225 := @Enclosure.Real.IsNear.of_eq qz856 (hardyZApproximantRS₀ qz100) Bool.true 353278272893516794213 73786976294838206464 50853636352076212850171 Ns186p651 

noncomputable def Ns186p2226 := @Enclosure.Real.IsNear.neg_val qz856 353278272893516794213 73786976294838206464 50853636352076212850171 Ns186p651 (Ns186p2225 (RS187to204.d42 qz87 qz100 qz278) RS187to204.d49) rfl 

noncomputable def Ns186p2227 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz855 qz4 qz87 454159 1000 461484 1000 

noncomputable def Ns186p2228 := @Enclosure.norm_gt_of_isNear qz855 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 3788103783076631756315 1180591620717411303424 50673039119978730977999 

noncomputable def Ns186p2229 := @Ns186p2228 Ns186p651 220374661 2684354560 2421 2684354560 (Ns186p2223 (RS187to204.d4 qz87 qz100 qz278) RS187to204.d48) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2230 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz856 qz4 qz100 454159 1000 462946 1000 

noncomputable def Ns186p2231 := @Enclosure.norm_gt_of_isNear qz856 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 353278272893516794213 73786976294838206464 50853636352076212850171 

noncomputable def Ns186p2232 := @Ns186p2231 Ns186p651 220374661 2684354560 2421 2684354560 (Ns186p2225 (RS187to204.d42 qz87 qz100 qz278) RS187to204.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2233 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz277 (@BSN.thirtyTwoPi_le_dec qz87 461484 1000 qz90 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz855 qz856 (Ns186p2224 rfl rfl) (Ns186p2226 rfl rfl)) (Ns186p2227 qz11 qz90 rfl rfl rfl rfl (Ns186p2229 rfl)) (Ns186p2230 qz11 qz103 rfl rfl rfl rfl (Ns186p2232 rfl)) 

noncomputable abbrev qz606 := (@Enclosure.dec_le_dec qz696 qz706 462946 1000 464407 1000 (@Eq.refl Real qz696) (@Eq.refl Real qz706) rfl rfl rfl)

noncomputable abbrev qz279 := (RS187to204.d3 qz449 qz463 qz606)

noncomputable abbrev qz857 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz279)

noncomputable def Ns186p2234 := @Enclosure.Real.IsNear.of_eq qz857 (hardyZApproximantRS₀ qz100) Bool.true 353278272893516794213 73786976294838206464 50853636352076212850171 Ns186p651 

noncomputable abbrev qz280 := qz606

noncomputable def Ns186p2235 := @Enclosure.Real.IsNear.neg_val qz857 353278272893516794213 73786976294838206464 50853636352076212850171 Ns186p651 (Ns186p2234 (RS187to204.d4 qz100 qz113 qz280) RS187to204.d49) rfl 

noncomputable abbrev qz858 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz279)

noncomputable def Ns186p2236 := @Enclosure.Real.IsNear.of_eq qz858 (hardyZApproximantRS₀ qz113) Bool.false 481469266297250952459 295147905179352825856 1701182769918641855719 1106804644422573096960000 

noncomputable def Ns186p2237 := @Enclosure.Real.IsNear.pos_val qz858 481469266297250952459 295147905179352825856 1701182769918641855719 1106804644422573096960000 (Ns186p2236 (RS187to204.d42 qz100 qz113 qz280) RS187to204.d50) rfl 

noncomputable def Ns186p2238 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz857 qz4 qz100 454159 1000 462946 1000 

noncomputable def Ns186p2239 := @Enclosure.norm_gt_of_isNear qz857 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 353278272893516794213 73786976294838206464 50853636352076212850171 

noncomputable def Ns186p2240 := @Ns186p2239 Ns186p651 220374661 2684354560 2421 2684354560 (Ns186p2234 (RS187to204.d4 qz100 qz113 qz280) RS187to204.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2241 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz858 qz4 qz113 454159 1000 464407 1000 

noncomputable def Ns186p2242 := @Enclosure.norm_gt_of_isNear qz858 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 481469266297250952459 295147905179352825856 1701182769918641855719 

noncomputable def Ns186p2243 := @Ns186p2242 1106804644422573096960000 220374661 2684354560 2421 2684354560 (Ns186p2236 (RS187to204.d42 qz100 qz113 qz280) RS187to204.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2244 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz279 (@BSN.thirtyTwoPi_le_dec qz100 462946 1000 qz103 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz857 qz858 (Ns186p2235 rfl rfl) (Ns186p2237 rfl rfl)) (Ns186p2238 qz11 qz103 rfl rfl rfl rfl (Ns186p2240 rfl)) (Ns186p2241 qz11 qz116 rfl rfl rfl rfl (Ns186p2243 rfl)) 

noncomputable abbrev qz607 := (@Enclosure.dec_le_dec qz706 qz716 464407 1000 465867 1000 (@Eq.refl Real qz706) qz720 rfl rfl rfl)

noncomputable abbrev qz281 := (RS187to204.d3 qz463 qz476 qz607)

noncomputable abbrev qz859 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz281)

noncomputable def Ns186p2245 := @Enclosure.Real.IsNear.of_eq qz859 (hardyZApproximantRS₀ qz113) Bool.false 481469266297250952459 295147905179352825856 1701182769918641855719 1106804644422573096960000 

noncomputable abbrev qz282 := qz607

noncomputable def Ns186p2246 := @Enclosure.Real.IsNear.pos_val qz859 481469266297250952459 295147905179352825856 1701182769918641855719 1106804644422573096960000 (Ns186p2245 (RS187to204.d4 qz113 qz126 qz282) RS187to204.d50) rfl 

noncomputable abbrev qz860 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz281)

noncomputable def Ns186p2247 := @Enclosure.Real.IsNear.of_eq qz860 (hardyZApproximantRS₀ qz126) Bool.true 25692202572075656553 73786976294838206464 1778744909449427943393 1152921504606846976000000 

noncomputable def Ns186p2248 := @Enclosure.Real.IsNear.neg_val qz860 25692202572075656553 73786976294838206464 1778744909449427943393 1152921504606846976000000 (Ns186p2247 (RS187to204.d42 qz113 qz126 qz282) RS187to204.d51) rfl 

noncomputable def Ns186p2249 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz859 qz4 qz113 454159 1000 464407 1000 

noncomputable def Ns186p2250 := @Enclosure.norm_gt_of_isNear qz859 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 481469266297250952459 295147905179352825856 1701182769918641855719 

noncomputable def Ns186p2251 := @Ns186p2250 1106804644422573096960000 220374661 2684354560 2421 2684354560 (Ns186p2245 (RS187to204.d4 qz113 qz126 qz282) RS187to204.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2252 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz860 qz4 qz126 454159 1000 465867 1000 

noncomputable def Ns186p2253 := @Enclosure.norm_gt_of_isNear qz860 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 25692202572075656553 73786976294838206464 1778744909449427943393 

noncomputable def Ns186p2254 := @Ns186p2253 1152921504606846976000000 220374661 2684354560 2421 2684354560 (Ns186p2247 (RS187to204.d42 qz113 qz126 qz282) RS187to204.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2255 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz281 (@BSN.thirtyTwoPi_le_dec qz113 464407 1000 qz116 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz859 qz860 (Ns186p2246 rfl rfl) (Ns186p2248 rfl rfl)) (Ns186p2249 qz11 qz116 rfl rfl rfl rfl (Ns186p2251 rfl)) (Ns186p2252 qz11 qz129 rfl rfl rfl rfl (Ns186p2254 rfl)) 

noncomputable abbrev qz608 := (@Enclosure.dec_le_dec qz716 qz728 465867 1000 467325 1000 qz720 qz732 rfl rfl rfl)

noncomputable abbrev qz283 := (RS187to204.d3 qz476 qz488 qz608)

noncomputable abbrev qz861 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz283)

noncomputable def Ns186p2256 := @Enclosure.Real.IsNear.of_eq qz861 (hardyZApproximantRS₀ qz126) Bool.true 25692202572075656553 73786976294838206464 1778744909449427943393 1152921504606846976000000 

noncomputable abbrev qz284 := qz608

noncomputable def Ns186p2257 := @Enclosure.Real.IsNear.neg_val qz861 25692202572075656553 73786976294838206464 1778744909449427943393 1152921504606846976000000 (Ns186p2256 (RS187to204.d4 qz126 qz139 qz284) RS187to204.d51) rfl 

noncomputable abbrev qz862 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz283)

noncomputable def Ns186p2258 := @Enclosure.Real.IsNear.of_eq qz862 (hardyZApproximantRS₀ qz139) Bool.false 71578140026302710005 295147905179352825856 14284287147437622018993 Ns186p1089 

noncomputable def Ns186p2259 := @Enclosure.Real.IsNear.pos_val qz862 71578140026302710005 295147905179352825856 14284287147437622018993 Ns186p1089 (Ns186p2258 (RS187to204.d42 qz126 qz139 qz284) RS187to204.d52) rfl 

noncomputable def Ns186p2260 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz861 qz4 qz126 454159 1000 465867 1000 

noncomputable def Ns186p2261 := @Enclosure.norm_gt_of_isNear qz861 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 25692202572075656553 73786976294838206464 1778744909449427943393 

noncomputable def Ns186p2262 := @Ns186p2261 1152921504606846976000000 220374661 2684354560 2421 2684354560 (Ns186p2256 (RS187to204.d4 qz126 qz139 qz284) RS187to204.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2263 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz862 qz4 qz139 454159 1000 467325 1000 

noncomputable def Ns186p2264 := @Enclosure.norm_gt_of_isNear qz862 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 71578140026302710005 295147905179352825856 14284287147437622018993 

noncomputable def Ns186p2265 := @Ns186p2264 Ns186p1089 220374661 2684354560 2421 2684354560 (Ns186p2258 (RS187to204.d42 qz126 qz139 qz284) RS187to204.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2266 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz283 (@BSN.thirtyTwoPi_le_dec qz126 465867 1000 qz129 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz861 qz862 (Ns186p2257 rfl rfl) (Ns186p2259 rfl rfl)) (Ns186p2260 qz11 qz129 rfl rfl rfl rfl (Ns186p2262 rfl)) (Ns186p2263 qz11 qz142 rfl rfl rfl rfl (Ns186p2265 rfl)) 

noncomputable abbrev qz863 := (@Enclosure.dec_le_dec qz929 qz933 467325 1000 468783 1000 (@Eq.refl Real qz929) qz936 rfl rfl rfl)

noncomputable abbrev qz609 := qz863

noncomputable abbrev qz285 := (RS187to204.d3 qz488 qz500 qz609)

noncomputable abbrev qz864 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz285)

noncomputable def Ns186p2267 := @Enclosure.Real.IsNear.of_eq qz864 (hardyZApproximantRS₀ qz139) Bool.false 71578140026302710005 295147905179352825856 14284287147437622018993 Ns186p1089 

noncomputable abbrev qz286 := qz609

noncomputable def Ns186p2268 := @Enclosure.Real.IsNear.pos_val qz864 71578140026302710005 295147905179352825856 14284287147437622018993 Ns186p1089 (Ns186p2267 (RS187to204.d4 qz139 qz152 qz286) RS187to204.d52) rfl 

noncomputable abbrev qz865 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz285)

noncomputable def Ns186p2269 := @Enclosure.Real.IsNear.of_eq qz865 (hardyZApproximantRS₀ qz152) Bool.true 1916968250358804335287 590295810358705651712 516307048361960008717 332041393326771929088000 

noncomputable def Ns186p2270 := @Enclosure.Real.IsNear.neg_val qz865 1916968250358804335287 590295810358705651712 516307048361960008717 332041393326771929088000 (Ns186p2269 (RS187to204.d42 qz139 qz152 qz286) RS187to204.d53) rfl 

noncomputable def Ns186p2271 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz864 qz4 qz139 454159 1000 467325 1000 

noncomputable def Ns186p2272 := @Enclosure.norm_gt_of_isNear qz864 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 71578140026302710005 295147905179352825856 14284287147437622018993 

noncomputable def Ns186p2273 := @Ns186p2272 Ns186p1089 220374661 2684354560 2421 2684354560 (Ns186p2267 (RS187to204.d4 qz139 qz152 qz286) RS187to204.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2274 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz865 qz4 qz152 454159 1000 468783 1000 

noncomputable def Ns186p2275 := @Enclosure.norm_gt_of_isNear qz865 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1916968250358804335287 590295810358705651712 516307048361960008717 

noncomputable def Ns186p2276 := @Ns186p2275 332041393326771929088000 220374661 2684354560 2421 2684354560 (Ns186p2269 (RS187to204.d42 qz139 qz152 qz286) RS187to204.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2277 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz285 (@BSN.thirtyTwoPi_le_dec qz139 467325 1000 qz142 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz864 qz865 (Ns186p2268 rfl rfl) (Ns186p2270 rfl rfl)) (Ns186p2271 qz11 qz142 rfl rfl rfl rfl (Ns186p2273 rfl)) (Ns186p2274 qz11 qz155 rfl rfl rfl rfl (Ns186p2276 rfl)) 

noncomputable abbrev qz866 := (@Enclosure.dec_le_dec qz933 qz938 468783 1000 470239 1000 qz936 (@Eq.refl Real qz938) rfl rfl rfl)

noncomputable abbrev qz610 := qz866

noncomputable abbrev qz287 := (RS187to204.d3 qz500 qz512 qz610)

noncomputable abbrev qz867 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz287)

noncomputable def Ns186p2278 := @Enclosure.Real.IsNear.of_eq qz867 (hardyZApproximantRS₀ qz152) Bool.true 1916968250358804335287 590295810358705651712 516307048361960008717 332041393326771929088000 

noncomputable abbrev qz288 := qz610

noncomputable def Ns186p2279 := @Enclosure.Real.IsNear.neg_val qz867 1916968250358804335287 590295810358705651712 516307048361960008717 332041393326771929088000 (Ns186p2278 (RS187to204.d4 qz152 qz165 qz288) RS187to204.d53) rfl 

noncomputable abbrev qz868 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz287)

noncomputable def Ns186p2280 := @Enclosure.Real.IsNear.of_eq qz868 (hardyZApproximantRS₀ qz165) Bool.false 2240577733813752407923 1180591620717411303424 259276686172414681175539 Ns186p1304 

noncomputable def Ns186p2281 := @Enclosure.Real.IsNear.pos_val qz868 2240577733813752407923 1180591620717411303424 259276686172414681175539 Ns186p1304 (Ns186p2280 (RS187to204.d42 qz152 qz165 qz288) RS187to204.d54) rfl 

noncomputable def Ns186p2282 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz867 qz4 qz152 454159 1000 468783 1000 

noncomputable def Ns186p2283 := @Enclosure.norm_gt_of_isNear qz867 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1916968250358804335287 590295810358705651712 516307048361960008717 

noncomputable def Ns186p2284 := @Ns186p2283 332041393326771929088000 220374661 2684354560 2421 2684354560 (Ns186p2278 (RS187to204.d4 qz152 qz165 qz288) RS187to204.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2285 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz868 qz4 qz165 454159 1000 470239 1000 

noncomputable def Ns186p2286 := @Enclosure.norm_gt_of_isNear qz868 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2240577733813752407923 1180591620717411303424 259276686172414681175539 

noncomputable def Ns186p2287 := @Ns186p2286 Ns186p1304 220374661 2684354560 2421 2684354560 (Ns186p2280 (RS187to204.d42 qz152 qz165 qz288) RS187to204.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2288 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz287 (@BSN.thirtyTwoPi_le_dec qz152 468783 1000 qz155 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz867 qz868 (Ns186p2279 rfl rfl) (Ns186p2281 rfl rfl)) (Ns186p2282 qz11 qz155 rfl rfl rfl rfl (Ns186p2284 rfl)) (Ns186p2285 qz11 qz168 rfl rfl rfl rfl (Ns186p2287 rfl)) 

noncomputable abbrev qz289 := (RS187to204.d3 qz512 qz524 (@Enclosure.dec_le_dec qz512 qz524 470239 1000 471695 1000 qz515 qz527 rfl rfl rfl))

noncomputable abbrev qz869 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz289)

noncomputable def Ns186p2289 := @Enclosure.Real.IsNear.of_eq qz869 (hardyZApproximantRS₀ qz165) Bool.false 2240577733813752407923 1180591620717411303424 259276686172414681175539 Ns186p1304 

noncomputable abbrev qz290 := (@Enclosure.dec_le_dec qz512 qz524 470239 1000 471695 1000 qz515 qz527 rfl rfl rfl)

noncomputable def Ns186p2290 := @Enclosure.Real.IsNear.pos_val qz869 2240577733813752407923 1180591620717411303424 259276686172414681175539 Ns186p1304 (Ns186p2289 (RS187to204.d4 qz165 qz178 qz290) RS187to204.d54) rfl 

noncomputable abbrev qz870 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz289)

noncomputable def Ns186p2291 := @Enclosure.Real.IsNear.of_eq qz870 (hardyZApproximantRS₀ qz178) Bool.true 1201271748711672189061 295147905179352825856 180903571170104363449 115292150460684697600000 

noncomputable def Ns186p2292 := @Enclosure.Real.IsNear.neg_val qz870 1201271748711672189061 295147905179352825856 180903571170104363449 115292150460684697600000 (Ns186p2291 (RS187to204.d42 qz165 qz178 qz290) RS187to204.d55) rfl 

noncomputable def Ns186p2293 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz869 qz4 qz165 454159 1000 470239 1000 

noncomputable def Ns186p2294 := @Enclosure.norm_gt_of_isNear qz869 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2240577733813752407923 1180591620717411303424 259276686172414681175539 

noncomputable def Ns186p2295 := @Ns186p2294 Ns186p1304 220374661 2684354560 2421 2684354560 (Ns186p2289 (RS187to204.d4 qz165 qz178 qz290) RS187to204.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2296 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz870 qz4 qz178 454159 1000 471695 1000 

noncomputable def Ns186p2297 := @Enclosure.norm_gt_of_isNear qz870 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1201271748711672189061 295147905179352825856 180903571170104363449 

noncomputable def Ns186p2298 := @Ns186p2297 115292150460684697600000 220374661 2684354560 2421 2684354560 (Ns186p2291 (RS187to204.d42 qz165 qz178 qz290) RS187to204.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2299 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz289 (@BSN.thirtyTwoPi_le_dec qz165 470239 1000 qz168 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz869 qz870 (Ns186p2290 rfl rfl) (Ns186p2292 rfl rfl)) (Ns186p2293 qz11 qz168 rfl rfl rfl rfl (Ns186p2295 rfl)) (Ns186p2296 qz11 qz181 rfl rfl rfl rfl (Ns186p2298 rfl)) 

noncomputable abbrev qz291 := (RS187to204.d3 qz524 qz536 (@Enclosure.dec_le_dec qz524 qz536 471695 1000 473149 1000 qz527 qz539 rfl rfl rfl))

noncomputable abbrev qz871 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz291)

noncomputable def Ns186p2300 := @Enclosure.Real.IsNear.of_eq qz871 (hardyZApproximantRS₀ qz178) Bool.true 1201271748711672189061 295147905179352825856 180903571170104363449 115292150460684697600000 

noncomputable abbrev qz292 := (@Enclosure.dec_le_dec qz524 qz536 471695 1000 473149 1000 qz527 qz539 rfl rfl rfl)

noncomputable def Ns186p2301 := @Enclosure.Real.IsNear.neg_val qz871 1201271748711672189061 295147905179352825856 180903571170104363449 115292150460684697600000 (Ns186p2300 (RS187to204.d4 qz178 qz191 qz292) RS187to204.d55) rfl 

noncomputable abbrev qz872 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz291)

noncomputable def Ns186p2302 := @Enclosure.Real.IsNear.of_eq qz872 (hardyZApproximantRS₀ qz191) Bool.false 316821513940697174127 295147905179352825856 3275153641945186990417 Ns186p1523 

noncomputable def Ns186p2303 := @Enclosure.Real.IsNear.pos_val qz872 316821513940697174127 295147905179352825856 3275153641945186990417 Ns186p1523 (Ns186p2302 (RS187to204.d42 qz178 qz191 qz292) RS187to204.d56) rfl 

noncomputable def Ns186p2304 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz871 qz4 qz178 454159 1000 471695 1000 

noncomputable def Ns186p2305 := @Enclosure.norm_gt_of_isNear qz871 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1201271748711672189061 295147905179352825856 180903571170104363449 

noncomputable def Ns186p2306 := @Ns186p2305 115292150460684697600000 220374661 2684354560 2421 2684354560 (Ns186p2300 (RS187to204.d4 qz178 qz191 qz292) RS187to204.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2307 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz872 qz4 qz191 454159 1000 473149 1000 

noncomputable def Ns186p2308 := @Enclosure.norm_gt_of_isNear qz872 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 316821513940697174127 295147905179352825856 3275153641945186990417 

noncomputable def Ns186p2309 := @Ns186p2308 Ns186p1523 220374661 2684354560 2421 2684354560 (Ns186p2302 (RS187to204.d42 qz178 qz191 qz292) RS187to204.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2310 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz291 (@BSN.thirtyTwoPi_le_dec qz178 471695 1000 qz181 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz871 qz872 (Ns186p2301 rfl rfl) (Ns186p2303 rfl rfl)) (Ns186p2304 qz11 qz181 rfl rfl rfl rfl (Ns186p2306 rfl)) (Ns186p2307 qz11 qz194 rfl rfl rfl rfl (Ns186p2309 rfl)) 

noncomputable abbrev qz611 := (@Enclosure.dec_le_dec qz776 qz787 473149 1000 474603 1000 (@Eq.refl Real qz776) (@Eq.refl Real qz787) rfl rfl rfl)

noncomputable abbrev qz293 := (RS187to204.d3 qz536 qz548 qz611)

noncomputable abbrev qz873 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz293)

noncomputable def Ns186p2311 := @Enclosure.Real.IsNear.of_eq qz873 (hardyZApproximantRS₀ qz191) Bool.false 316821513940697174127 295147905179352825856 3275153641945186990417 Ns186p1523 

noncomputable abbrev qz294 := qz611

noncomputable def Ns186p2312 := @Enclosure.Real.IsNear.pos_val qz873 316821513940697174127 295147905179352825856 3275153641945186990417 Ns186p1523 (Ns186p2311 (RS187to204.d4 qz191 qz204 qz294) RS187to204.d56) rfl 

noncomputable abbrev qz874 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz293)

noncomputable def Ns186p2313 := @Enclosure.Real.IsNear.of_eq qz874 (hardyZApproximantRS₀ qz204) Bool.true 172196543155935480561 73786976294838206464 7320615988107557298773 Ns186p1632 

noncomputable def Ns186p2314 := @Enclosure.Real.IsNear.neg_val qz874 172196543155935480561 73786976294838206464 7320615988107557298773 Ns186p1632 (Ns186p2313 (RS187to204.d42 qz191 qz204 qz294) RS187to204.d57) rfl 

noncomputable def Ns186p2315 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz873 qz4 qz191 454159 1000 473149 1000 

noncomputable def Ns186p2316 := @Enclosure.norm_gt_of_isNear qz873 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 316821513940697174127 295147905179352825856 3275153641945186990417 

noncomputable def Ns186p2317 := @Ns186p2316 Ns186p1523 220374661 2684354560 2421 2684354560 (Ns186p2311 (RS187to204.d4 qz191 qz204 qz294) RS187to204.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2318 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz874 qz4 qz204 454159 1000 474603 1000 

noncomputable def Ns186p2319 := @Enclosure.norm_gt_of_isNear qz874 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 172196543155935480561 73786976294838206464 7320615988107557298773 

noncomputable def Ns186p2320 := @Ns186p2319 Ns186p1632 220374661 2684354560 2421 2684354560 (Ns186p2313 (RS187to204.d42 qz191 qz204 qz294) RS187to204.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2321 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz293 (@BSN.thirtyTwoPi_le_dec qz191 473149 1000 qz194 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz873 qz874 (Ns186p2312 rfl rfl) (Ns186p2314 rfl rfl)) (Ns186p2315 qz11 qz194 rfl rfl rfl rfl (Ns186p2317 rfl)) (Ns186p2318 qz11 qz207 rfl rfl rfl rfl (Ns186p2320 rfl)) 

noncomputable abbrev qz612 := (@Enclosure.dec_le_dec qz787 qz799 474603 1000 476055 1000 (@Eq.refl Real qz787) qz803 rfl rfl rfl)

noncomputable abbrev qz295 := (RS187to204.d3 qz548 qz560 qz612)

noncomputable abbrev qz875 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz295)

noncomputable def Ns186p2322 := @Enclosure.Real.IsNear.of_eq qz875 (hardyZApproximantRS₀ qz204) Bool.true 172196543155935480561 73786976294838206464 7320615988107557298773 Ns186p1632 

noncomputable abbrev qz296 := qz612

noncomputable def Ns186p2323 := @Enclosure.Real.IsNear.neg_val qz875 172196543155935480561 73786976294838206464 7320615988107557298773 Ns186p1632 (Ns186p2322 (RS187to204.d4 qz204 qz217 qz296) RS187to204.d57) rfl 

noncomputable abbrev qz876 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz295)

noncomputable def Ns186p2324 := @Enclosure.Real.IsNear.of_eq qz876 (hardyZApproximantRS₀ qz217) Bool.false 9229955932980912267 9223372036854775808 22144521168200408353481 Ns186p1737 

noncomputable def Ns186p2325 := @Enclosure.Real.IsNear.pos_val qz876 9229955932980912267 9223372036854775808 22144521168200408353481 Ns186p1737 (Ns186p2324 (RS187to204.d42 qz204 qz217 qz296) RS187to204.d58) rfl 

noncomputable def Ns186p2326 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz875 qz4 qz204 454159 1000 474603 1000 

noncomputable def Ns186p2327 := @Enclosure.norm_gt_of_isNear qz875 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 172196543155935480561 73786976294838206464 7320615988107557298773 

noncomputable def Ns186p2328 := @Ns186p2327 Ns186p1632 220374661 2684354560 2421 2684354560 (Ns186p2322 (RS187to204.d4 qz204 qz217 qz296) RS187to204.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2329 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz876 qz4 qz217 454159 1000 476055 1000 

noncomputable def Ns186p2330 := @Enclosure.norm_gt_of_isNear qz876 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 9229955932980912267 9223372036854775808 22144521168200408353481 

noncomputable def Ns186p2331 := @Ns186p2330 Ns186p1737 220374661 2684354560 2421 2684354560 (Ns186p2324 (RS187to204.d42 qz204 qz217 qz296) RS187to204.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2332 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz295 (@BSN.thirtyTwoPi_le_dec qz204 474603 1000 qz207 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz875 qz876 (Ns186p2323 rfl rfl) (Ns186p2325 rfl rfl)) (Ns186p2326 qz11 qz207 rfl rfl rfl rfl (Ns186p2328 rfl)) (Ns186p2329 qz11 qz220 rfl rfl rfl rfl (Ns186p2331 rfl)) 

noncomputable abbrev qz613 := (@Enclosure.dec_le_dec qz799 qz811 476055 1000 477779 1000 qz803 qz815 rfl rfl rfl)

noncomputable abbrev qz297 := (RS187to204.d3 qz560 qz572 qz613)

noncomputable abbrev qz877 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz297)

noncomputable def Ns186p2333 := @Enclosure.Real.IsNear.of_eq qz877 (hardyZApproximantRS₀ qz217) Bool.false 9229955932980912267 9223372036854775808 22144521168200408353481 Ns186p1737 

noncomputable abbrev qz298 := qz613

noncomputable def Ns186p2334 := @Enclosure.Real.IsNear.pos_val qz877 9229955932980912267 9223372036854775808 22144521168200408353481 Ns186p1737 (Ns186p2333 (RS187to204.d4 qz217 qz230 qz298) RS187to204.d58) rfl 

noncomputable abbrev qz878 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz297)

noncomputable def Ns186p2335 := @Enclosure.Real.IsNear.of_eq qz878 (hardyZApproximantRS₀ qz230) Bool.true 26254066163885992121 36893488147419103232 14999466440467804701307 Ns186p1089 

noncomputable def Ns186p2336 := @Enclosure.Real.IsNear.neg_val qz878 26254066163885992121 36893488147419103232 14999466440467804701307 Ns186p1089 (Ns186p2335 (RS187to204.d42 qz217 qz230 qz298) RS187to204.d59) rfl 

noncomputable def Ns186p2337 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz877 qz4 qz217 454159 1000 476055 1000 

noncomputable def Ns186p2338 := @Enclosure.norm_gt_of_isNear qz877 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 9229955932980912267 9223372036854775808 22144521168200408353481 

noncomputable def Ns186p2339 := @Ns186p2338 Ns186p1737 220374661 2684354560 2421 2684354560 (Ns186p2333 (RS187to204.d4 qz217 qz230 qz298) RS187to204.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2340 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz878 qz4 qz230 454159 1000 477779 1000 

noncomputable def Ns186p2341 := @Enclosure.norm_gt_of_isNear qz878 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 26254066163885992121 36893488147419103232 14999466440467804701307 

noncomputable def Ns186p2342 := @Ns186p2341 Ns186p1089 220374661 2684354560 2421 2684354560 (Ns186p2335 (RS187to204.d42 qz217 qz230 qz298) RS187to204.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2343 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz297 (@BSN.thirtyTwoPi_le_dec qz217 476055 1000 qz220 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz877 qz878 (Ns186p2334 rfl rfl) (Ns186p2336 rfl rfl)) (Ns186p2337 qz11 qz220 rfl rfl rfl rfl (Ns186p2339 rfl)) (Ns186p2340 qz11 qz233 rfl rfl rfl rfl (Ns186p2342 rfl)) 

noncomputable abbrev qz879 := (@Enclosure.dec_le_dec qz958 qz962 477779 1000 478504 1000 (@Eq.refl Real qz958) qz965 rfl rfl rfl)

noncomputable abbrev qz614 := qz879

noncomputable abbrev qz299 := (RS187to204.d3 qz572 qz584 qz614)

noncomputable abbrev qz880 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz299)

noncomputable def Ns186p2344 := @Enclosure.Real.IsNear.of_eq qz880 (hardyZApproximantRS₀ qz230) Bool.true 26254066163885992121 36893488147419103232 14999466440467804701307 Ns186p1089 

noncomputable abbrev qz300 := qz614

noncomputable def Ns186p2345 := @Enclosure.Real.IsNear.neg_val qz880 26254066163885992121 36893488147419103232 14999466440467804701307 Ns186p1089 (Ns186p2344 (RS187to204.d4 qz230 qz243 qz300) RS187to204.d59) rfl 

noncomputable abbrev qz881 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz299)

noncomputable def Ns186p2346 := @Enclosure.Real.IsNear.of_eq qz881 (hardyZApproximantRS₀ qz243) Bool.false 1733385609596470873 2305843009213693952 4273713204815068589261 Ns186p1956 

noncomputable def Ns186p2347 := @Enclosure.Real.IsNear.pos_val qz881 1733385609596470873 2305843009213693952 4273713204815068589261 Ns186p1956 (Ns186p2346 (RS187to204.d42 qz230 qz243 qz300) RS187to204.d60) rfl 

noncomputable def Ns186p2348 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz880 qz4 qz230 454159 1000 477779 1000 

noncomputable def Ns186p2349 := @Enclosure.norm_gt_of_isNear qz880 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 26254066163885992121 36893488147419103232 14999466440467804701307 

noncomputable def Ns186p2350 := @Ns186p2349 Ns186p1089 220374661 2684354560 2421 2684354560 (Ns186p2344 (RS187to204.d4 qz230 qz243 qz300) RS187to204.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2351 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz881 qz4 qz243 454159 1000 478504 1000 

noncomputable def Ns186p2352 := @Enclosure.norm_gt_of_isNear qz881 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1733385609596470873 2305843009213693952 4273713204815068589261 

noncomputable def Ns186p2353 := @Ns186p2352 Ns186p1956 220374661 2684354560 2421 2684354560 (Ns186p2346 (RS187to204.d42 qz230 qz243 qz300) RS187to204.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2354 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz299 (@BSN.thirtyTwoPi_le_dec qz230 477779 1000 qz233 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz880 qz881 (Ns186p2345 rfl rfl) (Ns186p2347 rfl rfl)) (Ns186p2348 qz11 qz233 rfl rfl rfl rfl (Ns186p2350 rfl)) (Ns186p2351 qz11 qz246 rfl rfl rfl rfl (Ns186p2353 rfl)) 

noncomputable abbrev qz969 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 478504 1000) (Enclosure.sfrac Bool.false 479682 1000) 478504 1000 479682 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 478504 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 479682 1000)) rfl rfl rfl)

noncomputable abbrev qz882 := qz969

noncomputable abbrev qz615 := qz882

noncomputable abbrev qz301 := (RS187to204.d3 qz584 qz596 qz615)

noncomputable abbrev qz883 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz301)

noncomputable def Ns186p2355 := @Enclosure.Real.IsNear.of_eq qz883 (hardyZApproximantRS₀ qz243) Bool.false 1733385609596470873 2305843009213693952 4273713204815068589261 Ns186p1956 

noncomputable abbrev qz302 := qz615

noncomputable def Ns186p2356 := @Enclosure.Real.IsNear.pos_val qz883 1733385609596470873 2305843009213693952 4273713204815068589261 Ns186p1956 (Ns186p2355 (RS187to204.d4 qz243 qz256 qz302) RS187to204.d60) rfl 

noncomputable abbrev qz884 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz301)

noncomputable def Ns186p2357 := @Enclosure.Real.IsNear.of_eq qz884 (hardyZApproximantRS₀ qz256) Bool.true 367447779136059587143 73786976294838206464 142153783560454845027613 Ns186p331 

noncomputable def Ns186p2358 := @Enclosure.Real.IsNear.neg_val qz884 367447779136059587143 73786976294838206464 142153783560454845027613 Ns186p331 (Ns186p2357 (RS187to204.d42 qz243 qz256 qz302) RS187to204.d61) rfl 

noncomputable def Ns186p2359 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz883 qz4 qz243 454159 1000 478504 1000 

noncomputable def Ns186p2360 := @Enclosure.norm_gt_of_isNear qz883 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1733385609596470873 2305843009213693952 4273713204815068589261 

noncomputable def Ns186p2361 := @Ns186p2360 Ns186p1956 220374661 2684354560 2421 2684354560 (Ns186p2355 (RS187to204.d4 qz243 qz256 qz302) RS187to204.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2362 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz884 qz4 qz256 454159 1000 479682 1000 

noncomputable def Ns186p2363 := @Enclosure.norm_gt_of_isNear qz884 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 367447779136059587143 73786976294838206464 142153783560454845027613 

noncomputable def Ns186p2364 := @Ns186p2363 Ns186p331 220374661 2684354560 2421 2684354560 (Ns186p2357 (RS187to204.d42 qz243 qz256 qz302) RS187to204.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 220374661 2684354560 2421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS187to204.d44) rfl rfl rfl rfl 

noncomputable def Ns186p2365 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz301 (@BSN.thirtyTwoPi_le_dec qz243 478504 1000 qz246 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz883 qz884 (Ns186p2356 rfl rfl) (Ns186p2358 rfl rfl)) (Ns186p2359 qz11 qz246 rfl rfl rfl rfl (Ns186p2361 rfl)) (Ns186p2362 qz11 (@Eq.refl Real qz256) rfl rfl rfl rfl (Ns186p2364 rfl)) 

noncomputable def Ns186p2366 := @List.cons RS187to204.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz299 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz299) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz299) Ns186p2354)) (@List.cons RS187to204.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz301 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz301) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz301) Ns186p2365)) (@List.nil RS187to204.d0)) 

noncomputable def Ns186p2367 := @List.cons RS187to204.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz295 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz295) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz295) Ns186p2332)) (@List.cons RS187to204.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz297 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz297) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz297) Ns186p2343)) Ns186p2366) 

noncomputable def Ns186p2368 := @List.cons RS187to204.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz291 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz291) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz291) Ns186p2310)) (@List.cons RS187to204.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz293 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz293) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz293) Ns186p2321)) Ns186p2367) 

noncomputable def Ns186p2369 := @List.cons RS187to204.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz287 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz287) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz287) Ns186p2288)) (@List.cons RS187to204.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz289 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz289) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz289) Ns186p2299)) Ns186p2368) 

noncomputable def Ns186p2370 := @List.cons RS187to204.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz283 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz283) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz283) Ns186p2266)) (@List.cons RS187to204.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz285 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz285) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz285) Ns186p2277)) Ns186p2369) 

noncomputable def Ns186p2371 := @List.cons RS187to204.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz279 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz279) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz279) Ns186p2244)) (@List.cons RS187to204.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz281 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz281) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz281) Ns186p2255)) Ns186p2370) 

noncomputable def Ns186p2372 := @List.cons RS187to204.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz275 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz275) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz275) Ns186p2222)) (@List.cons RS187to204.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz277 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz277) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz277) Ns186p2233)) Ns186p2371) 

noncomputable def Ns186p2373 := @List.cons RS187to204.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz271 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz271) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz271) Ns186p2200)) (@List.cons RS187to204.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz273 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz273) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz273) Ns186p2211)) Ns186p2372) 

noncomputable def Ns186p2374 := @List.cons RS187to204.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz267 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz267) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz267) Ns186p2178)) (@List.cons RS187to204.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz269 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz269) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz269) Ns186p2189)) Ns186p2373) 

noncomputable abbrev qz885 := (RS187to204.d2 qz958 qz962 (@Enclosure.dec_le_dec qz958 qz962 477779 1000 478504 1000 (@Eq.refl Real qz958) qz965 rfl rfl rfl))

noncomputable abbrev qz886 := (@List.cons RS187to204.d1 (RS187to204.d2 qz962 qz967 qz969) (@List.nil RS187to204.d1))

noncomputable abbrev qz616 := (@List.cons RS187to204.d1 (RS187to204.d2 qz799 qz811 (@Enclosure.dec_le_dec qz799 qz811 476055 1000 477779 1000 qz803 qz815 rfl rfl rfl)) (@List.cons RS187to204.d1 qz885 qz886))

noncomputable abbrev qz303 := (@List.cons RS187to204.d1 (RS187to204.d2 qz536 qz548 qz611) (@List.cons RS187to204.d1 (RS187to204.d2 qz548 qz560 qz612) qz616))

noncomputable def Ns186p2375 := @List.cons RS187to204.d1 (RS187to204.d2 qz165 qz178 qz290) (@List.cons RS187to204.d1 (RS187to204.d2 qz178 qz191 qz292) qz303) 

noncomputable abbrev qz887 := (RS187to204.d2 qz929 qz933 (@Enclosure.dec_le_dec qz929 qz933 467325 1000 468783 1000 (@Eq.refl Real qz929) qz936 rfl rfl rfl))

noncomputable abbrev qz888 := (RS187to204.d2 qz933 qz938 (@Enclosure.dec_le_dec qz933 qz938 468783 1000 470239 1000 qz936 (@Eq.refl Real qz938) rfl rfl rfl))

noncomputable abbrev qz617 := (@List.cons RS187to204.d1 (RS187to204.d2 qz716 qz728 (@Enclosure.dec_le_dec qz716 qz728 465867 1000 467325 1000 qz720 qz732 rfl rfl rfl)) (@List.cons RS187to204.d1 qz887 (@List.cons RS187to204.d1 qz888 Ns186p2375)))

noncomputable abbrev qz304 := (@List.cons RS187to204.d1 (RS187to204.d2 qz449 qz463 qz606) (@List.cons RS187to204.d1 (RS187to204.d2 qz463 qz476 qz607) qz617))

noncomputable def Ns186p2376 := @List.cons RS187to204.d1 (RS187to204.d2 qz74 qz87 qz276) (@List.cons RS187to204.d1 (RS187to204.d2 qz87 qz100 qz278) qz304) 

noncomputable def Ns186p2377 := @List.IsChain.cons_cons RS187to204.d1 RS187to204.d62 (RS187to204.d2 qz61 qz74 qz274) (RS187to204.d2 qz74 qz87 qz276) (@List.cons RS187to204.d1 (RS187to204.d2 qz87 qz100 qz278) qz304) 

noncomputable def Ns186p2378 := @List.IsChain.cons_cons RS187to204.d1 RS187to204.d62 (RS187to204.d2 qz74 qz87 qz276) (RS187to204.d2 qz87 qz100 qz278) qz304 (@Enclosure.dec_le_dec qz87 qz87 461484 1000 461484 1000 qz90 qz90 rfl rfl rfl) 

noncomputable abbrev qz618 := qz888

noncomputable abbrev qz305 := qz618

noncomputable def Ns186p2379 := @List.IsChain.cons_cons RS187to204.d1 RS187to204.d62 qz305 (RS187to204.d2 qz165 qz178 qz290) (@List.cons RS187to204.d1 (RS187to204.d2 qz178 qz191 qz292) qz303) 

noncomputable def Ns186p2380 := @List.IsChain.cons_cons RS187to204.d1 RS187to204.d62 (RS187to204.d2 qz165 qz178 qz290) (RS187to204.d2 qz178 qz191 qz292) qz303 (@Enclosure.dec_le_dec qz178 qz178 471695 1000 471695 1000 qz181 qz181 rfl rfl rfl) 

noncomputable abbrev qz306 := qz616

noncomputable abbrev qz619 := (@List.cons RS187to204.d1 qz885 qz886)

noncomputable abbrev qz307 := qz619

noncomputable abbrev qz620 := qz885

noncomputable abbrev qz308 := qz620

noncomputable abbrev qz621 := qz886

noncomputable abbrev qz309 := qz621

noncomputable abbrev qz889 := (RS187to204.d2 qz962 qz967 qz969)

noncomputable abbrev qz622 := qz889

noncomputable abbrev qz310 := qz622

noncomputable def Ns186p2381 := @List.IsChain.cons_cons RS187to204.d1 RS187to204.d62 (RS187to204.d2 qz191 qz204 qz294) (RS187to204.d2 qz204 qz217 qz296) qz306 (@Enclosure.dec_le_dec qz204 qz204 474603 1000 474603 1000 qz207 qz207 rfl rfl rfl) (@List.IsChain.cons_cons RS187to204.d1 RS187to204.d62 (RS187to204.d2 qz204 qz217 qz296) (RS187to204.d2 qz217 qz230 qz298) qz307 (@Enclosure.dec_le_dec qz217 qz217 476055 1000 476055 1000 qz220 qz220 rfl rfl rfl) (@List.IsChain.cons_cons RS187to204.d1 RS187to204.d62 (RS187to204.d2 qz217 qz230 qz298) qz308 qz309 (@Enclosure.dec_le_dec qz230 qz230 477779 1000 477779 1000 qz233 qz233 rfl rfl rfl) (@List.IsChain.cons_cons RS187to204.d1 RS187to204.d62 qz308 qz310 (@List.nil RS187to204.d1) (@Enclosure.dec_le_dec qz243 qz243 478504 1000 478504 1000 qz246 qz246 rfl rfl rfl) (@List.IsChain.singleton RS187to204.d1 RS187to204.d62 qz310)))) 

noncomputable abbrev qz311 := (@List.cons RS187to204.d1 (RS187to204.d2 qz548 qz560 qz612) qz616)

noncomputable def Ns186p2382 := @List.IsChain.cons_cons RS187to204.d1 RS187to204.d62 (RS187to204.d2 qz178 qz191 qz292) (RS187to204.d2 qz191 qz204 qz294) qz311 (@Enclosure.dec_le_dec qz191 qz191 473149 1000 473149 1000 qz194 qz194 rfl rfl rfl) Ns186p2381 

noncomputable abbrev qz312 := qz617

noncomputable abbrev qz623 := (@List.cons RS187to204.d1 qz887 (@List.cons RS187to204.d1 qz888 Ns186p2375))

noncomputable abbrev qz313 := qz623

noncomputable abbrev qz624 := qz887

noncomputable abbrev qz314 := qz624

noncomputable def Ns186p2383 := @List.IsChain.cons_cons RS187to204.d1 RS187to204.d62 (RS187to204.d2 qz100 qz113 qz280) (RS187to204.d2 qz113 qz126 qz282) qz312 (@Enclosure.dec_le_dec qz113 qz113 464407 1000 464407 1000 qz116 qz116 rfl rfl rfl) (@List.IsChain.cons_cons RS187to204.d1 RS187to204.d62 (RS187to204.d2 qz113 qz126 qz282) (RS187to204.d2 qz126 qz139 qz284) qz313 (@Enclosure.dec_le_dec qz126 qz126 465867 1000 465867 1000 qz129 qz129 rfl rfl rfl) (@List.IsChain.cons_cons RS187to204.d1 RS187to204.d62 (RS187to204.d2 qz126 qz139 qz284) qz314 (@List.cons RS187to204.d1 qz305 Ns186p2375) (@Enclosure.dec_le_dec qz139 qz139 467325 1000 467325 1000 qz142 qz142 rfl rfl rfl) (@List.IsChain.cons_cons RS187to204.d1 RS187to204.d62 qz314 qz305 Ns186p2375 (@Enclosure.dec_le_dec qz152 qz152 468783 1000 468783 1000 qz155 qz155 rfl rfl rfl) (Ns186p2379 (@Enclosure.dec_le_dec qz165 qz165 470239 1000 470239 1000 qz168 qz168 rfl rfl rfl) (Ns186p2380 Ns186p2382))))) 

noncomputable abbrev qz315 := (@List.cons RS187to204.d1 (RS187to204.d2 qz463 qz476 qz607) qz617)

noncomputable def Ns186p2384 := @List.IsChain.cons_cons RS187to204.d1 RS187to204.d62 (RS187to204.d2 qz87 qz100 qz278) (RS187to204.d2 qz100 qz113 qz280) qz315 (@Enclosure.dec_le_dec qz100 qz100 462946 1000 462946 1000 qz103 qz103 rfl rfl rfl) Ns186p2383 

noncomputable def Ns186p2385 := Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns186p2374 (@List.IsChain.cons_cons RS187to204.d1 RS187to204.d62 (RS187to204.d2 qz4 qz29 qz268) (RS187to204.d2 qz29 qz48 qz270) (@List.cons RS187to204.d1 (RS187to204.d2 qz48 qz61 qz272) (@List.cons RS187to204.d1 (RS187to204.d2 qz61 qz74 qz274) Ns186p2376)) (@Enclosure.dec_le_dec qz29 qz29 455626 1000 455626 1000 qz32 qz32 rfl rfl rfl) (@List.IsChain.cons_cons RS187to204.d1 RS187to204.d62 (RS187to204.d2 qz29 qz48 qz270) (RS187to204.d2 qz48 qz61 qz272) (@List.cons RS187to204.d1 (RS187to204.d2 qz61 qz74 qz274) Ns186p2376) (@Enclosure.dec_le_dec qz48 qz48 457092 1000 457092 1000 qz51 qz51 rfl rfl rfl) (@List.IsChain.cons_cons RS187to204.d1 RS187to204.d62 (RS187to204.d2 qz48 qz61 qz272) (RS187to204.d2 qz61 qz74 qz274) Ns186p2376 (@Enclosure.dec_le_dec qz61 qz61 458557 1000 458557 1000 qz64 qz64 rfl rfl rfl) (Ns186p2377 (@Enclosure.dec_le_dec qz74 qz74 460021 1000 460021 1000 qz77 qz77 rfl rfl rfl) (Ns186p2378 Ns186p2384))))) 

noncomputable abbrev qz625 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz626 := (Zeta.Certificates.CertifiedZeroIntervals.intervals Ns186p2385)

theorem RS187to204.d63 : Zeta.Certificates.BatchSpec 18 454159 1000 479682 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz625 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 18) (And (@Eq (Option Real) (@Option.map qz625 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz625 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz625 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz625 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz256)))) Ns186p2385 (@And.intro (@Eq Nat (@List.length qz625 qz626) 18) (And (@Eq (Option Real) (@Option.map qz625 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz625 qz626)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz625 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz625 qz626)) (@Option.some Real qz256))) (@Eq.refl Nat 18) (@And.intro (@Eq (Option Real) (@Option.map qz625 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz625 qz626)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz625 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz625 qz626)) (@Option.some Real qz256)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz256))))

theorem solution : Zeta.Certificates.BatchSpec 18 454159 1000 479682 1000 := RS187to204.d63
#print axioms solution
#check solution
