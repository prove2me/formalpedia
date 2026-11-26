-- Prove2me | solution 1 for RHHeight1000.rs_main_0169_0186
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T07:48:27.071278+00:00
-- url     : https://prove2.me/submissions/b1a67bbd-560b-49b1-9a68-0e19915b6dca

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

noncomputable def RS169to186.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS169to186.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS169to186.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS169to186.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS169to186.d2 a b h 

theorem RS169to186.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS169to186.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS169to186.d3 a b h)) 

noncomputable def Ns168p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns168p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns168p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns168p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns168p0 Ns168p1 Ns168p2 Ns168p1 153643044 134217728 1 36000000 153643044 134217728 1 36000000 76821522 67108864 2 67108864 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns168p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns168p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns168p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns168p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns168p8 := nat_lit 167537954069964697925743468333314178468718661948561187618563575975392713740913527107727581163208035826476740967700482432525301063254420572874757592895482956004842597348203117269212172556829666669574421653274845612596416189641484794702002223261246862056663160605878293700340502480877986491439034432953223334258717026053687371824342493299510132312376251152844516906794910572262907940062760396663270105627554083664899640691826599584783763757814813433640133591539937449421955686657622469485188711283992428713614179785896055117030632677201478317872225272595773536303110412989181984739022579128493081560758017763072115692678596043664844667144619713966763611484179303468167142547433165016751768184247559143333542643815355903304572487929375 

noncomputable def Ns168p9 := nat_lit 17907736863639440849562382641391758203535690054199171304015283257442503423240620144819838407313611418261944516207295868563739563278604805791797182761045687776939279949642059267526948014748996956777332184087524644234759874591635243045607722412471722018588244283882362848653445974523544951031470230725674276297342086185092985546835544820091590454230569790847977790484558207349923322458845585052164126500435851662252152223728079705692133047658564669873831757357628115566356048471439549797170528303905720944834637690907185213991407615774042056720704508980680095051114888612186461088301140868302968264130481206655302741383410655080008578156649725227045954510069588220729495895148666460653631514375880874422615237249871322129146554264800 

noncomputable def Ns168p10 := nat_lit 55164646516618494962085419356369025784335016154267579706247610053041231157772817011486486467101704279863254798704146668052276438579475100451766223896220272709675360577301802978530276301158911649961092601279696986330335403118086533522541958716560166657634553390183479955483588238249446822384543398154260439705049143284278540285021213103458182619368483938376641172730818250587232036579805400979202432024046862170503602539341971086573372247299262086029843105216008583038025403798224342134620653974939981235680083776396058604459065501719125356177784467570909658245422960948263734871602033841948787585406240093531041217463298165642337705122589129757920995868559518021463265498464182174549661735402095023640043996665674913376875 

noncomputable def Ns168p11 := BSN.log_dyadic_bound Ns168p6 Ns168p7 15 14 Ns168p8 134217728 36000000 Ns168p9 Ns168p10 153643044 Ns168p4 Ns168p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns168p6) (BSN.artanhQ Ns168p7) 0 14 Ns168p9 Ns168p8 Ns168p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns168p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns168p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns168p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns168p15 := nat_lit 167537954069966963268140139327979112712430526945422964221951926912223381190141639739514890494967825643602350173964944759828460064784215684919760383437959917620844610857567326816719640593037578236900835917107172977527392439886629774248115214831425484905681376157923696414882114961796820014026232307332015059110330001516939277521159573995394989771587717775443426002499543257897301982481613760098955890450106043861450716722534643739571053080256776912576113428445260435254713579381797931690799491102381747484553243404562568585572234105168360737285205910186933811836504830286397217473365026331067977496463917110493303316865058355012304571237619413071097245713770677768486493924969821719264401216877841676972336093778875903304572487929375 

noncomputable def Ns168p16 := nat_lit 17907736863639702486765313263906285882628955290251965205176678923530777959693011244026517850256414903756943142851250712732214241881959351517241344993825585048584379523049477943740273636414656012170312373198803997844271825165684859407921203335666024680974464565759223251918458072775203410604089667122984485578465112081892102496937045858735135721609691262763214794451343726045584198128451069547586972080574568545086657023793200560105564573365716615162566961587407171758966967827997201380802107846920231945878242774600967607639551032178207663699700360114112068650063802902647517702890145150192721997537569966984346993833704449560383184487996362781528900358997452380059737141488304159449328022742959995775545894292303322129146554264800 

noncomputable def Ns168p17 := nat_lit 55164646516619937449385584700664297411818070214438189962773666351465523500358685366424500506990751111492356556545320273548942244833046464529601272738875466881799996765940232256588350019911833156887888425998391295014189841212513610526066550079316346993943774342801096070086869790972589246312728227659319758310961510342377923950694747797317942483020440897997204711883064182772445608288320382376665481938194224815739627075458138172195220395246294556718284728034954178416253903237031389214179719385823921869528509431462690683227358218086518156757026652846493301460983550768858152506145788622699720737745394141184245149692548799188169247529408201840608223422296381897323845616153036586108326210125693898345963996665674913376875 

noncomputable def Ns168p18 := BSN.log_dyadic_bound Ns168p13 Ns168p14 15 14 Ns168p15 134217728 36000000 Ns168p16 Ns168p17 153643044 Ns168p12 Ns168p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns168p13) (BSN.artanhQ Ns168p14) 0 14 Ns168p16 Ns168p15 Ns168p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns168p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 76821522 67108864 2 67108864 38410761 33554432 1 33554432 (Ns168p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns168p0 Ns168p1 153643044 134217728 1 36000000 Bool.false (BSN.logfrac_isNear Ns168p4 Ns168p5 1 Ns168p0 Ns168p1 153643044 134217728 36000000 rfl rfl rfl (Ns168p11 rfl))) (BSN.isNear_log_sfrac Ns168p2 Ns168p1 153643044 134217728 1 36000000 Bool.false (BSN.logfrac_isNear Ns168p12 Ns168p5 1 Ns168p2 Ns168p1 153643044 134217728 36000000 rfl rfl rfl (Ns168p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS169to186.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 33554432 := Ns168p19 

noncomputable def Ns168p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 8388608 2250000 385100712855 135135 5814539 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz316 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz0 := qz316

theorem RS169to186.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 5814539 8388608 1 2250000 := BSN.isNear_log_sfrac 2 1 5814539 8388608 1 2250000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 5814539 8388608 2250000 rfl rfl rfl (Ns168p20 rfl)) 

theorem RS169to186.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 93032624 134217728 60 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 5814539 8388608 1 2250000 93032624 134217728 60 134217728 RS169to186.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz319 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def Ns168p21 := @Enclosure.Real.IsNear.inv_image qz317 23726567 16777216 1 16777216 5931641 5931642 8388608 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 23726567 16777216 1 16777216 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 23726567 16777216 1 16777216 23726567 16777216 1 16777216 (BSN.sqrt_enclosure 2 1 11863283 11863284 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS169to186.d8 : Enclosure.Real.IsNear qz320 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 11863283 16777216 1 16777216 (Ns168p21 rfl rfl) rfl 

theorem RS169to186.d9 : Enclosure.Real.IsNear qz320 Bool.false 94906264 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 94906264 134217728 8 134217728 RS169to186.d8 rfl 

noncomputable def Ns168p22 := BSN.log_dyadic_bound 1 2 12 11 1326382131865190400 8388608 2250000 130797573554866995 13749310575 9215827 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 1) (BSN.artanhQ 2) 0 11 130797573554866995 1326382131865190400 13749310575 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS169to186.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 9215827 8388608 1 2250000 := BSN.isNear_log_sfrac 3 1 9215827 8388608 1 2250000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 9215827 8388608 2250000 rfl rfl rfl (Ns168p22 rfl)) 

theorem RS169to186.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 147453232 134217728 60 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 9215827 8388608 1 2250000 147453232 134217728 60 134217728 RS169to186.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns168p23 := @Enclosure.Real.IsNear.inv_image qz321 29058991 16777216 1 16777216 4843164 4843166 8388608 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 29058991 16777216 1 16777216 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 29058991 16777216 1 16777216 29058991 16777216 1 16777216 (BSN.sqrt_enclosure 3 1 14529495 14529496 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS169to186.d12 : Enclosure.Real.IsNear qz323 Bool.false 4843165 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 9686330 16777216 2 16777216 4843165 8388608 1 8388608 (Ns168p23 rfl rfl) rfl 

theorem RS169to186.d13 : Enclosure.Real.IsNear qz323 Bool.false 77490640 134217728 16 134217728 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 4843165 8388608 1 8388608 77490640 134217728 16 134217728 RS169to186.d12 rfl 

noncomputable def Ns168p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns168p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns168p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns168p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns168p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns168p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns168p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns168p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns168p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns168p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns168p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns168p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns168p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns168p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns168p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns168p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns168p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns168p25 Ns168p26 Ns168p27 Ns168p28 200200021673987500790625 Ns168p29 Ns168p30 Ns168p31 Ns168p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns168p32 Ns168p33 151412625 Ns168p34 Ns168p35 1322214852783825 Ns168p27 Ns168p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns168p32 Ns168p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns168p34 Ns168p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns168p36 Ns168p37 1267389585 Ns168p38 Ns168p39 1927077560082675 Ns168p29 Ns168p30 Ns168p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns168p36 Ns168p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns168p38 Ns168p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS169to186.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns168p24 Ns168p25 1 Ns168p26 := Ns168p40 rfl rfl rfl 

noncomputable def Ns168p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns168p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns168p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns168p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns168p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns168p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns168p25 Ns168p26 Ns168p42 Ns168p43 9945 Ns168p44 Ns168p45 65835 Ns168p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns168p42 Ns168p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns168p44 Ns168p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS169to186.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns168p41 Ns168p25 1 Ns168p26 := Ns168p46 rfl 

noncomputable def Ns168p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns168p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS169to186.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns168p47 Ns168p25 1 Ns168p48 := BSN.pi_combine Ns168p24 Ns168p41 Ns168p25 Ns168p26 Ns168p48 Ns168p47 rfl rfl rfl rfl RS169to186.d14 RS169to186.d15 

theorem RS169to186.d17 : Enclosure.Real.IsNear Real.pi Bool.false 7074237752028440 2251799813685248 1 2251799813685248 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns168p47 Ns168p25 1 Ns168p48 7074237752028440 2251799813685248 1 2251799813685248 RS169to186.d16 rfl 

noncomputable def Ns168p49 := nat_lit 178719669545544893480837345123291015625 

noncomputable def Ns168p50 := nat_lit 27745388228251122714770036239987464375 

noncomputable def Ns168p51 := nat_lit 1274524447665412456340166714375 

noncomputable def Ns168p52 := BSN.log_dyadic_bound 3 5 16 15 Ns168p49 8388608 2250000 Ns168p50 Ns168p51 11629079 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP 3) (BSN.artanhQ 5) 0 15 Ns168p50 Ns168p49 Ns168p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS169to186.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 11629079 8388608 1 2250000 := BSN.isNear_log_sfrac 4 1 11629079 8388608 1 2250000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 11629079 8388608 2250000 rfl rfl rfl (Ns168p52 rfl)) 

theorem RS169to186.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 186065264 134217728 60 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 11629079 8388608 1 2250000 186065264 134217728 60 134217728 RS169to186.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns168p53 := @Enclosure.Real.IsNear.inv_image qz325 33554433 16777216 1 16777216 4194303 4194304 8388608 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 33554433 16777216 1 16777216 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 33554433 16777216 1 16777216 33554433 16777216 1 16777216 (BSN.sqrt_enclosure 4 1 16777216 16777217 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS169to186.d20 : Enclosure.Real.IsNear qz327 Bool.false 8388607 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 8388607 16777216 1 16777216 8388607 16777216 1 16777216 (Ns168p53 rfl rfl) rfl 

theorem RS169to186.d21 : Enclosure.Real.IsNear qz327 Bool.false 67108856 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 8388607 16777216 1 16777216 67108856 134217728 8 134217728 RS169to186.d20 rfl 

noncomputable def Ns168p54 := nat_lit 159424323765613091421820433543167414255940625 

noncomputable def Ns168p55 := nat_lit 33013339099500162583200499609923570567289500 

noncomputable def Ns168p56 := nat_lit 351657888879851162997374110924800000 

noncomputable def Ns168p57 := nat_lit 2289063575687431840984260 

noncomputable def Ns168p58 := nat_lit 3325435793429257756623375 

noncomputable def Ns168p59 := BSN.log_dyadic_bound 2 3 21 20 Ns168p54 8388608 2250000 Ns168p55 Ns168p56 13500943 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 20 10 9927050056596826020 47940881637414340575 686533194547200 Ns168p57 Ns168p58 512222703392784384000 Ns168p55 Ns168p54 Ns168p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 10 20 Ns168p57 Ns168p58 512222703392784384000 rfl rfl rfl rfl)) rfl rfl 

theorem RS169to186.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 13500943 8388608 1 2250000 := BSN.isNear_log_sfrac 5 1 13500943 8388608 1 2250000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 13500943 8388608 2250000 rfl rfl rfl (Ns168p59 rfl rfl)) 

theorem RS169to186.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 216015088 134217728 60 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 13500943 8388608 1 2250000 216015088 134217728 60 134217728 RS169to186.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns168p60 := @Enclosure.Real.IsNear.inv_image qz328 37514995 16777216 1 16777216 3751499 3751500 8388608 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 37514995 16777216 1 16777216 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 37514995 16777216 1 16777216 37514995 16777216 1 16777216 (BSN.sqrt_enclosure 5 1 18757497 18757498 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS169to186.d24 : Enclosure.Real.IsNear qz329 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 7502999 16777216 1 16777216 (Ns168p60 rfl rfl) rfl 

theorem RS169to186.d25 : Enclosure.Real.IsNear qz329 Bool.false 60023992 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 60023992 134217728 8 134217728 RS169to186.d24 rfl 

noncomputable def Ns168p61 := BSN.log_dyadic_bound 2 10 5 4 94500000000 8388608 2250000 1291130880 26880 3401287 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) (@Nat.cast Real Real.instNatCast 1))

theorem RS169to186.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683410914551 2251799813685248 2000000009 4500000000000000 := BSN.isNear_log_sfrac 6 1 4034683410914551 2251799813685248 2000000009 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 541526040612241437360128 302231454903657293676544 1000000004500000 2250000000000000000000 4034683410914551 2251799813685248 2000000009 4500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 3401287 8388608 24973259072661432 36028797018963968 2250000 1000000000000000 rfl rfl rfl rfl (Ns168p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS169to186.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 240485871 134217728 61 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683410914551 2251799813685248 2000000009 4500000000000000 240485871 134217728 61 134217728 RS169to186.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns168p62 := @Enclosure.Real.IsNear.inv_image qz331 41095619 16777216 1 16777216 3424634 3424635 8388608 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 41095619 16777216 1 16777216 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 41095619 16777216 1 16777216 41095619 16777216 1 16777216 (BSN.sqrt_enclosure 6 1 20547809 20547810 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS169to186.d28 : Enclosure.Real.IsNear qz332 Bool.false 6849269 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 6849269 16777216 1 16777216 6849269 16777216 1 16777216 (Ns168p62 rfl rfl) rfl 

theorem RS169to186.d29 : Enclosure.Real.IsNear qz332 Bool.false 54794152 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 6849269 16777216 1 16777216 54794152 134217728 8 134217728 RS169to186.d28 rfl 

noncomputable def Ns168p63 := BSN.log_dyadic_bound 3 11 6 5 269619528727395 8388608 2250000 6999933372849 55801305 4694397 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 3) (BSN.artanhQ 11) 0 5 6999933372849 269619528727395 55801305 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) (@Nat.cast Real Real.instNatCast 1))

theorem RS169to186.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 2000000009 4500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 2000000009 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 588115238325433934020608 302231454903657293676544 1000000004500000 2250000000000000000000 4381799983422711 2251799813685248 2000000009 4500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 4694397 8388608 24973259072661432 36028797018963968 2250000 1000000000000000 rfl rfl rfl rfl (Ns168p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS169to186.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 261175631 134217728 61 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 2000000009 4500000000000000 261175631 134217728 61 134217728 RS169to186.d30 rfl 

noncomputable abbrev qz334 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns168p64 := @Enclosure.Real.IsNear.inv_image qz334 44388341 16777216 1 16777216 3170595 3170596 8388608 (@Enclosure.Real.IsNear.of_eq qz334 (Real.sqrt qz333) Bool.false 44388341 16777216 1 16777216 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 44388341 16777216 1 16777216 44388341 16777216 1 16777216 (BSN.sqrt_enclosure 7 1 22194170 22194171 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS169to186.d32 : Enclosure.Real.IsNear qz335 Bool.false 6341191 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 6341191 16777216 1 16777216 6341191 16777216 1 16777216 (Ns168p64 rfl rfl) rfl 

theorem RS169to186.d33 : Enclosure.Real.IsNear qz335 Bool.false 50729528 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 6341191 16777216 1 16777216 50729528 134217728 8 134217728 RS169to186.d32 rfl 

noncomputable def Ns168p65 := BSN.log_dyadic_bound 0 16 1 0 1 8388608 2250000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz889 := (Enclosure.sfrac Bool.false 8 1)

noncomputable abbrev qz627 := qz889

noncomputable abbrev qz336 := qz627

noncomputable abbrev qz1 := qz336

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) (@Nat.cast Real Real.instNatCast 1))

theorem RS169to186.d34 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 9364972152248037 4503599627370496 4000000027 9000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 4000000027 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz337) Bool.false 628472642529000809299968 302231454903657293676544 1000000006750000 2250000000000000000000 9364972152248037 4503599627370496 4000000027 9000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 8388608 24973259072661432 36028797018963968 2250000 1000000000000000 rfl rfl rfl rfl (Ns168p65 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS169to186.d35 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 279097919 134217728 60 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 9364972152248037 4503599627370496 4000000027 9000000000000000 279097919 134217728 60 134217728 RS169to186.d34 rfl 

noncomputable abbrev qz338 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns168p66 := @Enclosure.Real.IsNear.inv_image qz338 47453133 16777216 1 16777216 2965820 2965821 8388608 (@Enclosure.Real.IsNear.of_eq qz338 (Real.sqrt qz337) Bool.false 47453133 16777216 1 16777216 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz337) Bool.false 47453133 16777216 1 16777216 47453133 16777216 1 16777216 (BSN.sqrt_enclosure 8 1 23726566 23726567 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz339 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS169to186.d36 : Enclosure.Real.IsNear qz339 Bool.false 5931641 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz339 Bool.false 5931641 16777216 1 16777216 5931641 16777216 1 16777216 (Ns168p66 rfl rfl) rfl 

theorem RS169to186.d37 : Enclosure.Real.IsNear qz339 Bool.false 47453128 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz339 Bool.false 5931641 16777216 1 16777216 47453128 134217728 8 134217728 RS169to186.d36 rfl 

theorem RS169to186.d38 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz890 := (@instHMul Real Real.instMul)

noncomputable abbrev qz628 := qz890

noncomputable abbrev qz340 := (@HMul.hMul Real Real Real qz628 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz2 := qz340

theorem RS169to186.d39 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS169to186.d38 rfl 

noncomputable abbrev qz3 := (@Inv.inv Real Real.instInv qz340)

theorem RS169to186.d40 : Enclosure.Real.IsNear qz3 Bool.false 2670177 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 2670177 16777216 1 16777216 2670177 16777216 1 16777216 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 1335088 1335089 8388608 RS169to186.d39 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns168p67 := nat_lit 3689348814741910323200000 

noncomputable def Ns168p68 := nat_lit 36348216143175594649571033088 

noncomputable abbrev qz891 := (Enclosure.sfrac Bool.false 427552 1000)

noncomputable abbrev qz629 := qz891

noncomputable abbrev qz341 := qz629

noncomputable abbrev qz4 := qz341

noncomputable abbrev qz342 := qz628

noncomputable abbrev qz5 := qz342

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 8)

noncomputable abbrev qz7 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz892 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 427552 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz630 := qz892

noncomputable abbrev qz343 := qz630

noncomputable abbrev qz8 := qz343

noncomputable abbrev qz9 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz893 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 427552 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz631 := qz893

noncomputable abbrev qz344 := qz631

noncomputable abbrev qz10 := qz344

noncomputable abbrev qz632 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz8 qz9))

noncomputable def Ns168p69 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) (@HMul.hMul Real Real Real qz5 qz632 (Zeta.RiemannSiegel.correction qz10)) 49871449 67108864 94259 67108864 102956723301972955975 590295810358705651712 4569043084705786373409 Ns168p67 Ns168p68 

noncomputable def Ns168p70 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin BSN.quadSignPos 7 8 427552 1000 127 134217728 67108864 2251799813685248 Bool.false 92342948307 1668 279097919 60 47453128 8 

noncomputable def Ns168p71 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 427552 1000 49 91 134217728 67108864 2251799813685248 Bool.false 92342948307 1668 

noncomputable def Ns168p72 := Ns168p71 240485871 61 54794152 8 261175631 61 50729528 8 Bool.true 92078409 62753 Bool.true 146659818 Bool.true 137802092 7074237752028440 1 Bool.false 119168264 Bool.true Bool.false 114836462 Bool.false Bool.true 97324546 

noncomputable def Ns168p73 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 427552 1000 60 0 134217728 67108864 2251799813685248 Bool.false 92342948307 1668 

noncomputable def Ns168p74 := Ns168p73 186065264 60 67108856 8 216015088 60 60023992 8 Bool.true 185253378 36854 Bool.false 140649705 Bool.true 14734597 7074237752028440 1 Bool.false 67024643 Bool.false Bool.false 133409748 Bool.false Bool.true 92078409 

noncomputable def Ns168p75 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 427552 1000 249 138 134217728 67108864 2251799813685248 Bool.false 92342948307 1668 

noncomputable def Ns168p76 := Ns168p75 93032624 60 94906264 8 147453232 60 77490640 16 Bool.true 134217720 1732 Bool.false 70314031 Bool.false 204661508 7074237752028440 1 Bool.false 67141590 Bool.true Bool.false 6165036 Bool.true Bool.true 185253378 

noncomputable def Ns168p77 := nat_lit 5198542972424447019449666999420351431940907357084443 

noncomputable def Ns168p78 := nat_lit 7555927544657740362946556402045826114017820672000 

noncomputable def Ns168p79 := nat_lit 6857841661489284600005345935360000 

noncomputable def Ns168p80 := nat_lit 17592514736246644432997695175106232320 

noncomputable abbrev qz11 := (@Eq.refl Real qz341)

noncomputable def Ns168p81 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 427552 1000 731203850816 16000000 855104 4000 2000 Ns168p79 Ns168p80 qz11 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns168p82 := nat_lit 6813834244816171197333067529480243028873586091077721128960 

noncomputable abbrev qz894 := (@instHSub Real Real.instSub)

noncomputable abbrev qz633 := qz894

noncomputable abbrev qz345 := qz633

noncomputable abbrev qz12 := qz345

noncomputable abbrev qz346 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz347 := (@HMul.hMul Real Real Real qz628 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz348 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz634 := (Real.log (Enclosure.sfrac Bool.false 731203850816 16000000))

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 427552 4000) qz634) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 855104))))))

noncomputable abbrev qz635 := (Enclosure.sfrac Bool.false 427552 2000)

noncomputable abbrev qz349 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz13 qz635) (@HMul.hMul Real Real Real qz5 qz635 (Real.log Real.pi)))

noncomputable def Ns168p83 := @Enclosure.Real.IsNear.addLit_ft_p qz349 (Enclosure.sfrac Bool.true Ns168p79 Ns168p80) 387314616903458372603 562949953421312000 476941678369163 38400000000000000000 Ns168p79 Ns168p80 0 1 Ns168p82 

noncomputable def Ns168p84 := nat_lit 812257623468321533021126656000 

noncomputable abbrev qz350 := (@HSub.hSub Real Real Real qz12 qz13 qz635)

noncomputable abbrev qz351 := (@HMul.hMul Real Real Real qz5 qz635 (Real.log Real.pi))

noncomputable def Ns168p85 := @Enclosure.Real.IsNear.subLit_ff_p qz350 qz351 525077351242012048379 562949953421312000 3629600962067 600000000000000000 513206177721 2097152000 13361 2097152000 Ns168p84 387314616903458372603 562949953421312000 

noncomputable abbrev qz352 := qz635

noncomputable def Ns168p86 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz352 645422540484606442491 562949953421312000 3629600962067 600000000000000000 427552 2000 0 1 1050154702484024096758000 525077351242012048379 562949953421312000 3629600962067 600000000000000000 

noncomputable def Ns168p87 := nat_lit 1453362356411496221601824649687072768 

noncomputable def Ns168p88 := nat_lit 25943206765175063940431872 

noncomputable def Ns168p89 := nat_lit 2417851639229258349412352 

noncomputable def Ns168p90 := nat_lit 5833685249720805284291059410033083490959440101669868749889464140084847805584357549083153985668382720 

noncomputable def Ns168p91 := nat_lit 53695774364043362543832052398524985081122461476737161239103475320961311424236251084762274357837824 

noncomputable def Ns168p92 := nat_lit 352808782949650493573162882660333824996240746459798850645598435674869795440693998583367598080 

noncomputable def Ns168p93 := BSN.log_dyadic_bound 206915850816 1255491850816 5 4 Ns168p90 67108864 18000000 Ns168p91 Ns168p92 22323839 1462407701632 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 206915850816) (BSN.artanhQ 1255491850816) 0 4 Ns168p91 Ns168p90 Ns168p92 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz353 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns168p94 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 427552 4000) qz634 427552 4000 0 1 48322988236649081 4503599627370496 100000027 1800000000000000 645643445829868371241 562949953421312000 1336100360747 225000000000000000 (Enclosure.Real.IsNear.const Bool.false 427552 4000) (BSN.isNear_log_sfrac 731203850816 16000000 48322988236649081 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 731203850816) qz353)) Bool.false Ns168p88 Ns168p89 1000000270000000 18000000000000000000000 48322988236649081 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 731203850816 16000000 15 1462407701632 1048576000000 22323839 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns168p93 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p95 := BSN.arctan_dyadic_bound_f 1000 855104 1 0 8388608 2250000 0 1 1 0 1 1 9810 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 855104) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 855104) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz14 := qz347

noncomputable abbrev qz15 := qz348

noncomputable abbrev qz354 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz16 := (@Enclosure.Real.IsNear.mulLit_ff qz354 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz355 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 855104)))

noncomputable def Ns168p96 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz355 884279719003555 562949953421312 1 2000000000000000 9810 8388608 1 2250000 7412353386027910430720 883621381047715 562949953421312 8000000009 18000000000000000 qz16 (Ns168p95 rfl) rfl rfl 

noncomputable abbrev qz17 := qz346

noncomputable abbrev qz356 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns168p97 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 427552 4000) qz634) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz355)) 645643445829868371241 562949953421312000 1336100360747 225000000000000000 883621381047715 2251799813685248 8000000009 72000000000000000 Ns168p87 645422540484606442491 562949953421312000 3629600962067 600000000000000000 (Ns168p94 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz355) 1 4 0 1 883621381047715 562949953421312 8000000009 18000000000000000 883621381047715 2251799813685248 8000000009 72000000000000000 qz356 Ns168p96 rfl) 

noncomputable def Ns168p98 := @Ns168p83 Ns168p77 Ns168p78 476941678369163 38400000000000000000 (@Ns168p85 476941678369163 38400000000000000000 (Ns168p86 (Ns168p97 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 427552 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz352 (Real.log Real.pi) 427552 2000 0 1 38410761 33554432 1 33554432 513206177721 2097152000 13361 2097152000 (Enclosure.Real.IsNear.const Bool.false 427552 2000) RS169to186.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns168p79 Ns168p80) 

noncomputable abbrev qz357 := (@instHAdd Real Real.instAdd)

noncomputable def Ns168p99 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns168p77 Ns168p78 476941678369163 38400000000000000000 5771434269 8388608 209 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz357 qz349 (Enclosure.sfrac Bool.true Ns168p79 Ns168p80)) Bool.false Ns168p77 Ns168p78 476941678369163 38400000000000000000 Ns168p81 (Ns168p98 rfl rfl)) 

noncomputable def Ns168p100 := nat_lit 1898719654834803612581888 

noncomputable def Ns168p101 := nat_lit 1208925819614629174706176 

noncomputable def Ns168p102 := nat_lit 856673481001777856599127115369854858122459367800250661629626239320768216148323349387228528880907465413243148177990480134549986289181761 

noncomputable def Ns168p103 := nat_lit 16860812360175734222210805034837902731874731588140993779854824115686058269364094835627812361599730584878593258197117225559879026789580800 

noncomputable def Ns168p104 := nat_lit 610003735126560193898473383913595058369649245893050085045281128687682471031281210357957367537377604868742192746269438016746218561 

noncomputable def Ns168p105 := nat_lit 4278047664086371406951943638311457040800514333367801705045121612367576527398650594869309545699174435254151438482831147152592144807289921 

noncomputable def Ns168p106 := nat_lit 590128432606150697777378176219326595615615605584934782294918844049012039427743319246973432655990570470750764036899102894595765937635328000 

noncomputable abbrev qz358 := (BSN.sinEvenQ 34359738368)

noncomputable abbrev qz359 := (BSN.sinOddQ 34359738368)

noncomputable def Ns168p107 := BSN.sin_dyadic_bound_f 53964858319 34359738368 4 3 16777216 4504395 Ns168p102 Ns168p103 Ns168p104 Ns168p105 Ns168p106 Ns168p104 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53964858319) qz358 0 3 Ns168p102 Ns168p103 Ns168p104 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53964858319) qz359 0 3 Ns168p105 Ns168p106 Ns168p104 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz360 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable abbrev qz636 := (@Nat.cast Real Real.instNatCast Ns168p101)

noncomputable def Ns168p108 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5771434269) qz360) Bool.false 5771434269 8388608 209 16777216 Bool.true 16777215 16777216 1 2250000 (Ns168p99 rfl) (Enclosure.sfrac_false_div 5771434269 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5771434269) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns168p100) qz636) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 109 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 5771434269 8388608 226375608064910080 72057594037927936 109 Ns168p100 Ns168p101 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns168p100 Ns168p101 53964858319 34359738368 4504395 4500000 (Ns168p107 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p109 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns168p77 Ns168p78 476941678369163 38400000000000000000 92342948307 134217728 1668 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz357 qz349 (Enclosure.sfrac Bool.true Ns168p79 Ns168p80)) Bool.false Ns168p77 Ns168p78 476941678369163 38400000000000000000 Ns168p81 (Ns168p98 rfl rfl)) 

noncomputable def Ns168p110 := Ns168p76 36854 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 249 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 67141590 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 138 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 6165036 134217728) qz11 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 16777215 16777216 30439201 2359296000000 134217720 134217728 1732 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 16777215 16777216 30439201 2359296000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 16777215 16777216 487027216 37748736000000 16777215 16777216 30439201 2359296000000 (Ns168p108 rfl rfl) rfl)) rfl) (Ns168p109 rfl) RS169to186.d7 

noncomputable def Ns168p111 := nat_lit 23988335843721041534983656332194353780005444598717529699639317838465 

noncomputable def Ns168p112 := nat_lit 38215724400686031908940493885850326479880652218951261491964367528263680 

noncomputable def Ns168p113 := nat_lit 597497329979846220799354477387386425835229279416265478225869441 

noncomputable def Ns168p114 := nat_lit 62825626499782760459647329534212299369610526434950665735900133407361 

noncomputable def Ns168p115 := nat_lit 700621614012577251663909054573922652131145290680773127352680071351500800 

noncomputable abbrev qz361 := (BSN.sinEvenQ 134217728)

noncomputable abbrev qz362 := (BSN.sinOddQ 134217728)

noncomputable def Ns168p116 := BSN.sin_dyadic_bound_f 70314031 134217728 3 2 134217728 67108864 Ns168p111 Ns168p112 Ns168p113 Ns168p114 Ns168p115 Ns168p113 67141590 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 70314031) qz361 0 2 Ns168p111 Ns168p112 Ns168p113 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 70314031) qz362 0 2 Ns168p114 Ns168p115 Ns168p113 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p117 := nat_lit 3699520568681695651218003578503427799915281405947931298831052977842210373007207739064369949240325482479616 

noncomputable def Ns168p118 := nat_lit 16370259324565974446773555668639125346849261288577159159185037526614652227207809159774062022111344040345600 

noncomputable def Ns168p119 := nat_lit 5400500835350328920769950388072282071940738415511679974820677788079850473953584199381532710310772736 

noncomputable def Ns168p120 := nat_lit 22395734846930902113640787973669920624876697808128246214762638508478297991730827945429123892667859179929600 

noncomputable def Ns168p121 := nat_lit 1489693598535503674656393565846160406563282777260521483485838414921933352675910633539439644012132307671449600 

noncomputable abbrev qz363 := (BSN.cosEvenQ 134217728)

noncomputable abbrev qz364 := (BSN.cosOddQ 134217728)

noncomputable def Ns168p122 := BSN.cos_dyadic_bound_f 204661508 134217728 4 3 134217728 67108864 Ns168p117 Ns168p118 Ns168p119 Ns168p120 Ns168p121 Ns168p119 6165036 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 204661508) qz363 0 3 Ns168p117 Ns168p118 Ns168p119 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 204661508) qz364 0 3 Ns168p120 Ns168p121 Ns168p119 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p123 := nat_lit 213508781880817328078890546022442515046447242418163454539795874690625 

noncomputable def Ns168p124 := nat_lit 4246191600076225767660054876205591831097850246550140165773818614251520 

noncomputable def Ns168p125 := nat_lit 153147744429630129345398768581491778918752722726971863220437890625 

noncomputable def Ns168p126 := nat_lit 640220050153592723977980840530164561581504221809036419892946748290625 

noncomputable def Ns168p127 := nat_lit 191078622003430159544702469429251632399403261094756307459821837641318400 

noncomputable def Ns168p128 := BSN.cos_dyadic_bound_f 140649705 134217728 3 2 134217728 67108864 Ns168p123 Ns168p124 Ns168p125 Ns168p126 Ns168p127 Ns168p125 67024643 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 140649705) qz363 0 2 Ns168p123 Ns168p124 Ns168p125 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 140649705) qz364 0 2 Ns168p126 Ns168p127 Ns168p125 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p129 := nat_lit 47136035097997654586783303281 

noncomputable def Ns168p130 := nat_lit 7788445287802241442795744493830144 

noncomputable def Ns168p131 := nat_lit 116826679317033621641936167407452160 

noncomputable def Ns168p132 := BSN.cos_dyadic_bound_f 14734597 134217728 2 1 134217728 67108864 Ns168p129 Ns168p130 Ns168p129 Ns168p129 Ns168p131 Ns168p129 133409748 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 14734597) qz363 0 1 Ns168p129 Ns168p130 Ns168p129 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 14734597) qz364 0 1 Ns168p129 Ns168p131 Ns168p129 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p133 := Ns168p74 62753 BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 67024643 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 0 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133409748 134217728) qz11 rfl rfl (Ns168p110 RS169to186.d9 RS169to186.d11 RS169to186.d13 RS169to186.d17 (Ns168p116 rfl rfl) (Ns168p122 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns168p109 rfl) RS169to186.d19 RS169to186.d21 RS169to186.d23 RS169to186.d25 RS169to186.d17 (Ns168p128 rfl rfl) (Ns168p132 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns168p134 := nat_lit 454224525012449218200278837126572627523521781589107899981340428427520 

noncomputable def Ns168p135 := nat_lit 214037137285790034752287480326511278380016115278898433342031749376 

noncomputable def Ns168p136 := nat_lit 1189289124429380482849226584172875863348989401880069140582861642096896 

noncomputable def Ns168p137 := BSN.sin_dyadic_bound_f 146659818 134217728 3 2 134217728 67108864 Ns168p134 Ns168p112 Ns168p135 Ns168p136 Ns168p115 Ns168p135 119168264 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 146659818) qz361 0 2 Ns168p134 Ns168p112 Ns168p135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 146659818) qz362 0 2 Ns168p136 Ns168p115 Ns168p135 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p138 := nat_lit 354000695274224727793772011067032671140211021134583511073950430986240 

noncomputable def Ns168p139 := nat_lit 130030875250410214561951982071858225549945723476487531985192943616 

noncomputable def Ns168p140 := nat_lit 926934151920183146731540678156969225382995619419232977760941768769536 

noncomputable def Ns168p141 := BSN.sin_dyadic_bound_f 137802092 134217728 3 2 134217728 67108864 Ns168p138 Ns168p112 Ns168p139 Ns168p140 Ns168p115 Ns168p139 114836462 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 137802092) qz361 0 2 Ns168p138 Ns168p112 Ns168p139 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 137802092) qz362 0 2 Ns168p140 Ns168p115 Ns168p139 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p142 := Ns168p72 84589 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 119168264 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 91 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 114836462 134217728) qz11 rfl rfl (Ns168p133 rfl rfl) (Ns168p109 rfl) RS169to186.d27 RS169to186.d29 RS169to186.d31 RS169to186.d33 RS169to186.d17 (Ns168p137 rfl rfl) (Ns168p141 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns168p143 := nat_lit 10787727764022471068979608276073383123599141731505280742242822552043519584375503646953439104997378592608256 

noncomputable def Ns168p144 := nat_lit 212813371219357667808056223692308629509040396751503069069405487845990478953701519077062806287447472524492800 

noncomputable def Ns168p145 := nat_lit 7646129882929455872782960321398032172910883315276239360499803289936984899904929890542531227206291456 

noncomputable def Ns168p146 := nat_lit 53871803975056225559974091840402868654599944497675694964677627677837056245432191298564178833373376028348416 

noncomputable def Ns168p147 := nat_lit 7448467992677518373281967829230802032816413886302607417429192074609666763379553167697198220060661538357248000 

noncomputable def Ns168p148 := BSN.sin_dyadic_bound_f 210678462 134217728 4 3 134217728 67108864 Ns168p143 Ns168p144 Ns168p145 Ns168p146 Ns168p147 Ns168p145 134217643 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 210678462) qz361 0 3 Ns168p143 Ns168p144 Ns168p145 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 210678462) qz362 0 3 Ns168p146 Ns168p147 Ns168p145 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz365 := (BSN.cos_quad_nat3 127 rfl)

noncomputable def Ns168p149 := Ns168p70 Bool.true 97324546 84589 Bool.true 210678462 7074237752028440 1 Bool.false 134217643 Bool.false Bool.true 49871449 94259 BSN.abs_quadSignPos qz365 (BSN.sfrac_eq_quadSignPos_mul Bool.false 134217643 134217728) qz11 rfl (Ns168p142 rfl) (Ns168p109 rfl) RS169to186.d35 RS169to186.d37 RS169to186.d17 (Ns168p148 rfl rfl) rfl 

noncomputable def Ns168p150 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) 49871449 134217728 94259 134217728 49871449 134217728 94259 134217728 13387265153695744 49871449 67108864 94259 67108864 (Ns168p149 rfl rfl rfl rfl) 

noncomputable def Ns168p151 := @Enclosure.Real.IsNear.mulLit_ff qz632 (Zeta.RiemannSiegel.correction qz10) 5841409 16777216 1 16777216 17625323496775 35184372088832 7821626844261799 2199023255552000000 102956723301972955975 590295810358705651712 

noncomputable abbrev qz637 := (@HPow.hPow Real Real Real qz7 qz8 qz9)

noncomputable def Ns168p152 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz637 1 1 0 1 5841409 16777216 1 16777216 5841409 16777216 1 16777216 

noncomputable abbrev qz366 := (@Enclosure.Real.IsNear.of_eq qz8 (@HMul.hMul Real Real Real qz5 qz4 qz3) Bool.false 35676234897 524288000 13361 524288000 (BSN.t_div_two_pi_mk qz4 427552 1000 qz11) (@Enclosure.Real.IsNear.mulLit_ff qz4 qz3 427552 1000 0 1 2670177 16777216 1 16777216 35676234897 524288000 13361 524288000 (Enclosure.Real.IsNear.const Bool.false 427552 1000) RS169to186.d40 rfl))

noncomputable def Ns168p153 := @Enclosure.Real.IsNear.sqrt_image qz8 35676234897 524288000 13361 524288000 69198131 69198158 8388608 qz366 

noncomputable abbrev qz895 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 427552 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz638 := qz895

noncomputable abbrev qz367 := qz638

noncomputable abbrev qz18 := qz367

noncomputable def Ns168p154 := @Enclosure.Real.IsNear.sqrt_image qz18 138396289 16777216 27 16777216 24093069 24093075 8388608 (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 138396289 16777216 27 16777216 138396289 16777216 27 16777216 (Ns168p153 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz639 := (Real.sqrt qz895)

noncomputable abbrev qz368 := qz639

noncomputable abbrev qz19 := qz368

noncomputable def Ns168p155 := @Enclosure.Real.IsNear.inv_image qz19 1505817 524288 3 8388608 2920704 2920705 8388608 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 48186144 16777216 6 16777216 1505817 524288 3 8388608 (Ns168p154 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns168p156 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz19) Bool.false 5841409 16777216 1 16777216 5841409 16777216 1 16777216 (Ns168p155 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz20 := (@HMul.hMul Real Real Real qz342 qz340 qz344)

noncomputable abbrev qz640 := (@HMul.hMul Real Real Real qz890 qz893 qz893)

noncomputable abbrev qz641 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz369 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz640 qz631) qz641)

noncomputable abbrev qz21 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz369))

noncomputable def Ns168p157 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz10) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz20)) qz21) Bool.false 17625323496775 

noncomputable def Ns168p158 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz20)) qz21 711415681 4194304 2552629 

noncomputable def Ns168p159 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz20)) Bool.false 2845662724 16777216 5105258 16777216 711415681 4194304 2552629 

noncomputable def Ns168p160 := @Enclosure.Real.IsNear.recentre' (Real.cos qz20) Bool.false 49457 8388608 199638608 18874368000000 49457 8388608 12477413 1179648000000 

noncomputable abbrev qz370 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable def Ns168p161 := @Enclosure.Real.IsNear.cos_image qz20 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 26254673) qz370) Bool.false 26254673 16777216 85 8388608 Bool.false 49457 8388608 1 

noncomputable def Ns168p162 := nat_lit 728624036080082792968244221 

noncomputable def Ns168p163 := nat_lit 72057594037927936000000000000000 

noncomputable def Ns168p164 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz10 884279719003555 140737488355328 1 500000000000000 4178561 16777216 27 16777216 3695016746919213784355 2361183241434822606848 Ns168p162 

noncomputable def Ns168p165 := @Enclosure.Real.IsNear.subLit_ff_p qz18 qz1 138396289 16777216 27 16777216 8 1 0 1 4178561 4178561 16777216 27 

noncomputable abbrev qz371 := (Enclosure.Real.IsNear.const Bool.false 8 1)

noncomputable def Ns168p166 := @Ns168p165 16777216 (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 138396289 16777216 27 16777216 138396289 16777216 27 16777216 (Ns168p153 rfl rfl rfl rfl rfl rfl) rfl) qz371 

noncomputable def Ns168p167 := @Enclosure.Real.IsNear.recentre' qz20 Bool.false 3695016746919213784355 2361183241434822606848 Ns168p162 Ns168p163 26254673 16777216 85 8388608 (@Ns168p164 Ns168p163 RS169to186.d39 (Ns168p166 rfl rfl) rfl) 

noncomputable def Ns168p168 := nat_lit 59739238909655440951393671953043539516178118414996557613884427761659503866827644531159832318401 

noncomputable def Ns168p169 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600 

noncomputable def Ns168p170 := nat_lit 107270267250759245825244176033295436765197798731698869350517830076396713307908712163561921 

noncomputable def Ns168p171 := nat_lit 361558081230466886507839901251910151613022647279244028472022180838596743150098866442057902576065 

noncomputable def Ns168p172 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600 

noncomputable abbrev qz642 := (BSN.cosEvenQ 16777216)

noncomputable def Ns168p173 := BSN.cos_dyadic_bound_f 26254673 16777216 4 3 8388608 2250000 Ns168p168 Ns168p169 Ns168p170 Ns168p171 Ns168p172 Ns168p170 49457 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 26254673) qz642 0 3 Ns168p168 Ns168p169 Ns168p170 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 26254673) (BSN.cosOddQ 16777216) 0 3 Ns168p171 Ns168p172 Ns168p170 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p174 := @Enclosure.Real.IsNear.inv_image (Real.cos qz20) 49457 8388608 12477413 1179648000000 1420278733 1425383991 8388608 (Ns168p160 (@Ns168p161 2250000 (Ns168p167 rfl) (Enclosure.sfrac_false_div 26254673 16777216) (Ns168p173 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns168p175 := @Enclosure.Real.IsNear.recentre' qz21 Bool.false 24775 8388608 

noncomputable abbrev qz22 := (@HMul.hMul Real Real Real qz342 qz340 qz369)

noncomputable def Ns168p176 := @Enclosure.Real.IsNear.cos_image qz22 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 13152019)) qz360) Bool.true 13152019 8388608 

noncomputable def Ns168p177 := nat_lit 62108654545671929560824941405 

noncomputable def Ns168p178 := nat_lit 39614081257132168796771975168 

noncomputable def Ns168p179 := nat_lit 18313502470311134545921200168373417 

noncomputable def Ns168p180 := @Enclosure.Real.IsNear.recentre' qz22 Bool.true Ns168p177 Ns168p178 Ns168p179 

noncomputable def Ns168p181 := nat_lit 1208925819614629174706176000000000000000 

noncomputable abbrev qz23 := qz369

noncomputable def Ns168p182 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz23 884279719003555 140737488355328 1 500000000000000 70236434479871 

noncomputable abbrev qz372 := (@HSub.hSub Real Real Real qz633 qz640 qz631)

noncomputable abbrev qz24 := qz372

noncomputable abbrev qz373 := qz641

noncomputable abbrev qz25 := qz373

noncomputable def Ns168p183 := @Enclosure.Real.IsNear.subLit_tf qz24 qz25 52644248435455 281474976710656 678627855 281474976710656 1 16 

noncomputable abbrev qz374 := qz640

noncomputable abbrev qz26 := qz374

noncomputable def Ns168p184 := @Enclosure.Real.IsNear.subLit_ff_n qz26 qz10 17460372030721 281474976710656 225643023 281474976710656 4178561 16777216 27 16777216 

noncomputable def Ns168p185 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz10 4178561 16777216 27 16777216 4178561 16777216 27 16777216 17460372030721 281474976710656 

noncomputable def Ns168p186 := nat_lit 14695170828580798829266757459642587638409114604437285652048338967595036704565055371874248241 

noncomputable def Ns168p187 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600 

noncomputable def Ns168p188 := nat_lit 26786078124866322791578545052290989708588746110401270168968970265965482448603498522161 

noncomputable def Ns168p189 := nat_lit 88937569893642308239782075981209331784607168732737484082793841766015487381083645244444878385 

noncomputable def Ns168p190 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600 

noncomputable def Ns168p191 := BSN.cos_dyadic_bound_f 13152019 8388608 4 3 8388608 2250000 Ns168p186 Ns168p187 Ns168p188 Ns168p189 Ns168p190 Ns168p188 24775 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 13152019) (BSN.cosEvenQ 8388608) 0 3 Ns168p186 Ns168p187 Ns168p188 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 13152019) (BSN.cosOddQ 8388608) 0 3 Ns168p189 Ns168p190 Ns168p188 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz375 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns168p192 := @Ns168p175 590527216 37748736000000 24775 8388608 36907951 2359296000000 (@Ns168p176 255 16777216 Bool.false 24775 8388608 1 2250000 (@Ns168p180 Ns168p181 13152019 8388608 255 16777216 (@Ns168p182 281474976710656 678627855 281474976710656 Ns168p177 Ns168p178 Ns168p179 Ns168p181 RS169to186.d39 (@Ns168p183 0 1 1123782951677936 70236434479871 281474976710656 678627855 281474976710656 (@Ns168p184 883223927159290593280 52644248435455 281474976710656 678627855 281474976710656 (@Ns168p185 225643023 281474976710656 (Ns168p166 rfl rfl) (Ns168p166 rfl rfl) rfl) (Ns168p166 rfl rfl) rfl rfl) qz375 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 13152019 8388608) (BSN.cos_neg_of_bound 13152019 8388608 Bool.false 24775 8388608 1 2250000 (Ns168p191 rfl rfl)) rfl rfl) 

noncomputable abbrev qz27 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 8) (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 8 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1))

noncomputable def Ns168p193 := @Ns168p151 4569043084705786373409 Ns168p67 (Ns168p152 qz27 (@Enclosure.Real.IsNear.of_eq qz637 (@Inv.inv Real Real.instInv qz19) Bool.false 5841409 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz8 (BSN.t_div_two_pi_nonneg qz4 427552 1000 qz11)) Ns168p156) rfl) (@Ns168p157 35184372088832 7821626844261799 2199023255552000000 (BSN.correction_mk qz10 (BSN.cos_two_pi_p_ne_zero_mk qz4 427552 1000 8 qz11 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 427552 1000 8 qz11 rfl rfl rfl))) (@Ns168p158 8388608 24775 8388608 36907951 2359296000000 17625323496775 35184372088832 7821626844261799 2199023255552000000 (@Ns168p159 8388608 (Ns168p174 rfl rfl rfl rfl rfl) rfl) (Ns168p192 rfl) rfl)) 

noncomputable def Ns168p194 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 541630627858275095367 590295810358705651712 9750986410832685573409 Ns168p67 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) (@HMul.hMul Real Real Real qz5 qz632 (Zeta.RiemannSiegel.correction qz10))) Bool.true 541630627858275095367 590295810358705651712 9750986410832685573409 Ns168p67 (BSN.hardyZApproximantRS₀_eq qz4 8 (@BSN.floor_sqrt_eq_dec qz4 427552 1000 8 qz11 rfl rfl rfl)) (@Ns168p69 541630627858275095367 590295810358705651712 9750986410832685573409 Ns168p67 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 8)) Bool.true 49871449 67108864 94259 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) (Ns168p150 (Ns168p149 rfl rfl rfl rfl) rfl rfl)) (Ns168p193 rfl) rfl rfl)) 

theorem RS169to186.d41 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 541630627858275095367 590295810358705651712 9750986410832685573409 Ns168p67 := Ns168p194 

theorem RS169to186.d42 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS169to186.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS169to186.d3 a b h)) 

noncomputable def Ns168p195 := nat_lit 16602069666338596454400000 

noncomputable def Ns168p196 := nat_lit 32165842729773052537694322688 

noncomputable abbrev qz896 := (Enclosure.sfrac Bool.false 429040 1000)

noncomputable abbrev qz643 := qz896

noncomputable abbrev qz376 := qz643

noncomputable abbrev qz28 := qz376

noncomputable abbrev qz897 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 429040 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz644 := qz897

noncomputable abbrev qz377 := qz644

noncomputable abbrev qz29 := qz377

noncomputable abbrev qz898 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 429040 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz645 := qz898

noncomputable abbrev qz378 := qz645

noncomputable abbrev qz30 := qz378

noncomputable abbrev qz646 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz29 qz9))

noncomputable def Ns168p197 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz28) qz28 8) (@HMul.hMul Real Real Real qz5 qz646 (Zeta.RiemannSiegel.correction qz30)) 57333563 16777216 94591 67108864 100011783961287173223 590295810358705651712 1449329686621140124639 Ns168p195 Ns168p196 

noncomputable def Ns168p198 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz28) qz28 Real.sin BSN.quadSignPos 7 8 429040 1000 127 134217728 67108864 2251799813685248 Bool.false 92764542538 1674 279097919 60 47453128 8 

noncomputable def Ns168p199 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz28) qz28 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 429040 1000 49 91 134217728 67108864 2251799813685248 Bool.false 92764542538 1674 

noncomputable def Ns168p200 := Ns168p199 240485871 61 54794152 8 261175631 61 50729528 8 Bool.false 177954674 62975 Bool.true 82908563 Bool.true 104837200 7074237752028440 1 Bool.false 77735620 Bool.true Bool.false 94497277 Bool.false Bool.false 181935853 

noncomputable def Ns168p201 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz28) qz28 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 429040 1000 61 0 134217728 67108864 2251799813685248 Bool.false 92764542538 1674 

noncomputable def Ns168p202 := Ns168p201 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 165072158 36985 Bool.false 74550109 Bool.false 85429182 7074237752028440 1 Bool.false 70775499 Bool.true Bool.false 107935588 Bool.false Bool.false 177954674 

noncomputable def Ns168p203 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz28) qz28 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 429040 1000 250 139 134217728 67108864 2251799813685248 Bool.false 92764542538 1674 

noncomputable def Ns168p204 := Ns168p203 93032624 60 94906264 8 147453232 60 77490640 16 Bool.false 134217696 1740 Bool.false 142647003 Bool.false 196016616 7074237752028440 1 Bool.false 65286852 Bool.true Bool.false 133401235 Bool.false Bool.false 165072158 

noncomputable def Ns168p205 := nat_lit 136506368071274796681438151306607421185754121127 

noncomputable def Ns168p206 := nat_lit 197506224670755518909773933355996287913164800 

noncomputable def Ns168p207 := nat_lit 6978011026738774527281152000000000 

noncomputable def Ns168p208 := nat_lit 17963086490522575232696356884480000000 

noncomputable abbrev qz379 := (@Eq.refl Real qz643)

noncomputable abbrev qz31 := qz379

noncomputable def Ns168p209 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz28 429040 1000 736302286400 16000000 858080 4000 2000 Ns168p207 Ns168p208 qz31 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns168p210 := nat_lit 2795650418099707836035853338759319985884244400680960000000 

noncomputable abbrev qz647 := (Real.log (Enclosure.sfrac Bool.false 736302286400 16000000))

noncomputable abbrev qz32 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 429040 4000) qz647) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 858080))))))

noncomputable abbrev qz648 := (Enclosure.sfrac Bool.false 429040 2000)

noncomputable abbrev qz380 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz32 qz648) (@HMul.hMul Real Real Real qz5 qz648 (Real.log Real.pi)))

noncomputable def Ns168p211 := @Enclosure.Real.IsNear.addLit_ft_p qz380 (Enclosure.sfrac Bool.true Ns168p207 Ns168p208) 155633164204999092527 225179981368524800 63811562535083 5120000000000000000 Ns168p207 Ns168p208 0 1 Ns168p210 

noncomputable def Ns168p212 := nat_lit 26110912126307380551294648320 

noncomputable abbrev qz381 := (@HSub.hSub Real Real Real qz12 qz32 qz648)

noncomputable abbrev qz382 := (@HMul.hMul Real Real Real qz5 qz648 (Real.log Real.pi))

noncomputable def Ns168p213 := @Enclosure.Real.IsNear.subLit_ff_p qz381 qz382 42186007801821064867 45035996273704960 242800064361 40000000000000000 205996911243 838860800 5363 838860800 Ns168p212 155633164204999092527 225179981368524800 

noncomputable abbrev qz383 := qz648

noncomputable def Ns168p214 := @Enclosure.Real.IsNear.subLit_ff_p qz32 qz383 259235648612281264431 225179981368524800 242800064361 40000000000000000 429040 2000 0 1 421860078018210648670000 42186007801821064867 45035996273704960 242800064361 40000000000000000 

noncomputable def Ns168p215 := nat_lit 583746785245709370489397863291813888 

noncomputable def Ns168p216 := nat_lit 25960007137340194914566144 

noncomputable def Ns168p217 := nat_lit 6025921349430083372104948064941254593895813171334228567520946404230998471243674419200000000000000000 

noncomputable def Ns168p218 := nat_lit 57802042773561307688964546162831155041392996675625418949246431158816715955649904640000000000000000 

noncomputable def Ns168p219 := nat_lit 428657385611342532303978190421581641534709963523907957352579569284346072268800000000000000000 

noncomputable def Ns168p220 := BSN.log_dyadic_bound 212014286400 1260590286400 5 4 Ns168p217 67108864 18000000 Ns168p218 Ns168p219 22790143 1472604572800 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 212014286400) (BSN.artanhQ 1260590286400) 0 4 Ns168p218 Ns168p217 Ns168p219 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns168p221 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 429040 4000) qz647 429040 4000 0 1 48354281368367737 4503599627370496 100000027 1800000000000000 259324010978556173531 225179981368524800 536300144801 90000000000000000 (Enclosure.Real.IsNear.const Bool.false 429040 4000) (BSN.isNear_log_sfrac 736302286400 16000000 48354281368367737 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 736302286400) qz353)) Bool.false Ns168p216 Ns168p89 1000000270000000 18000000000000000000000 48354281368367737 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 736302286400 16000000 15 1472604572800 1048576000000 22790143 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns168p220 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p222 := BSN.arctan_dyadic_bound_f 1000 858080 1 0 8388608 2250000 0 1 1 0 1 1 9776 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 858080) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 858080) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz384 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 858080)))

noncomputable def Ns168p223 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz384 884279719003555 562949953421312 1 2000000000000000 9776 8388608 1 2250000 7412372526326326755328 883623662749091 562949953421312 8000000009 18000000000000000 qz16 (Ns168p222 rfl) rfl rfl 

noncomputable def Ns168p224 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 429040 4000) qz647) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz384)) 259324010978556173531 225179981368524800 536300144801 90000000000000000 883623662749091 2251799813685248 8000000009 72000000000000000 Ns168p215 259235648612281264431 225179981368524800 242800064361 40000000000000000 (Ns168p221 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz384) 1 4 0 1 883623662749091 562949953421312 8000000009 18000000000000000 883623662749091 2251799813685248 8000000009 72000000000000000 qz356 Ns168p223 rfl) 

noncomputable def Ns168p225 := @Ns168p211 Ns168p205 Ns168p206 63811562535083 5120000000000000000 (@Ns168p213 63811562535083 5120000000000000000 (Ns168p214 (Ns168p224 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 429040 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz383 (Real.log Real.pi) 429040 2000 0 1 38410761 33554432 1 33554432 205996911243 838860800 5363 838860800 (Enclosure.Real.IsNear.const Bool.false 429040 2000) RS169to186.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns168p207 Ns168p208) 

noncomputable def Ns168p226 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz28) Bool.false Ns168p205 Ns168p206 63811562535083 5120000000000000000 11595567817 16777216 105 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz28) (@HAdd.hAdd Real Real Real qz357 qz380 (Enclosure.sfrac Bool.true Ns168p207 Ns168p208)) Bool.false Ns168p205 Ns168p206 63811562535083 5120000000000000000 Ns168p209 (Ns168p225 rfl rfl)) 

noncomputable def Ns168p227 := nat_lit 3796300866943932122005504 

noncomputable def Ns168p228 := nat_lit 855644585742146481987225554960093962279299785841207743569642829083504347196460445329632408644271217181946602898884533527947974869140625 

noncomputable def Ns168p229 := nat_lit 607812857521905521618118368067507794612370940299145048362490131498261255104453358824095344298402955922638580336630344390869140625 

noncomputable def Ns168p230 := nat_lit 4272915935861716467109787083364264371473107336339599539423927560514410382299895651284886775891850761218540186248648290718362310869140625 

noncomputable def Ns168p231 := BSN.sin_dyadic_bound_f 53948680075 34359738368 4 3 16777216 4504395 Ns168p228 Ns168p103 Ns168p229 Ns168p230 Ns168p106 Ns168p229 16777212 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53948680075) qz358 0 3 Ns168p228 Ns168p103 Ns168p229 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53948680075) qz359 0 3 Ns168p230 Ns168p106 Ns168p229 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz385 := (@Nat.cast Real Real.instNatCast Ns168p89)

noncomputable def Ns168p232 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz28) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11595567817) qz370) Bool.false 11595567817 16777216 105 8388608 Bool.false 16777212 16777216 1 2250000 (Ns168p226 rfl) (Enclosure.sfrac_false_div 11595567817 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11595567817) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns168p227) qz385) 226375608064910080 72057594037927936 Bool.false 16777212 16777216 109 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q3 11595567817 16777216 226375608064910080 72057594037927936 109 Ns168p227 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777212 16777216 Ns168p227 Ns168p89 53948680075 34359738368 4504395 4500000 (Ns168p231 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p233 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz28) Bool.false Ns168p205 Ns168p206 63811562535083 5120000000000000000 92764542538 134217728 1674 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz28) (@HAdd.hAdd Real Real Real qz357 qz380 (Enclosure.sfrac Bool.true Ns168p207 Ns168p208)) Bool.false Ns168p205 Ns168p206 63811562535083 5120000000000000000 Ns168p209 (Ns168p225 rfl rfl)) 

noncomputable def Ns168p234 := Ns168p204 36985 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 250 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 65286852 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 139 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133401235 134217728) qz31 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz28) qz28 1) Bool.false 4194303 4194304 15289913 1179648000000 134217696 134217728 1740 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz28) qz28 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz28)) Bool.false 4194303 4194304 15289913 1179648000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz28) qz28) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz28)) Bool.false 16777212 16777216 244638608 18874368000000 4194303 4194304 15289913 1179648000000 (Ns168p232 rfl rfl) rfl)) rfl) (Ns168p233 rfl) RS169to186.d7 

noncomputable def Ns168p235 := nat_lit 870933767841114185465637480840227810456129896234306271394189762868571878735739036367029277418207697811921 

noncomputable def Ns168p236 := nat_lit 70982586318801034246434351921941710392373376800230394111252575975257885770605393635180473363839441 

noncomputable def Ns168p237 := nat_lit 5280991393337770295472662222729768800437100060286520325604596848061367491891270979210149300246281170565585 

noncomputable def Ns168p238 := BSN.cos_dyadic_bound_f 142647003 134217728 4 3 134217728 67108864 Ns168p235 Ns168p118 Ns168p236 Ns168p237 Ns168p121 Ns168p236 65286852 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 142647003) qz363 0 3 Ns168p235 Ns168p118 Ns168p236 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 142647003) qz364 0 3 Ns168p237 Ns168p121 Ns168p236 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p239 := nat_lit 8079838832060142488398516267063569000480396611517235378506504919059291639833262658243473848314245893062656 

noncomputable def Ns168p240 := nat_lit 3217471050488633049467768663260272831760871329538324497077181309030160786117840207091451373977337856 

noncomputable def Ns168p241 := nat_lit 40361667914786937727095381917743531757949951701343614314882421398946776705504768657538072543304879823650816 

noncomputable def Ns168p242 := BSN.sin_dyadic_bound_f 196016616 134217728 4 3 134217728 67108864 Ns168p239 Ns168p144 Ns168p240 Ns168p241 Ns168p147 Ns168p240 133401235 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 196016616) qz361 0 3 Ns168p239 Ns168p144 Ns168p240 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 196016616) qz362 0 3 Ns168p241 Ns168p147 Ns168p240 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p243 := nat_lit 30312944127857900705147382965772457494751325228257455216240140755105 

noncomputable def Ns168p244 := nat_lit 954083229777917569763217660346991213558198472322569603808501921 

noncomputable def Ns168p245 := nat_lit 79389499438208194742177814938906350690955328990766717596508488212641 

noncomputable def Ns168p246 := BSN.sin_dyadic_bound_f 74550109 134217728 3 2 134217728 67108864 Ns168p243 Ns168p112 Ns168p244 Ns168p245 Ns168p115 Ns168p244 70775499 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 74550109) qz361 0 2 Ns168p243 Ns168p112 Ns168p244 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 74550109) qz362 0 2 Ns168p245 Ns168p115 Ns168p244 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p247 := nat_lit 29041311951270588479091667571347005491648577128564561469288862515456 

noncomputable def Ns168p248 := nat_lit 2836938907219873354208614868622219374350664284962431308172165376 

noncomputable def Ns168p249 := nat_lit 87118261975997325690566585484303772036197030057123759545250243215616 

noncomputable def Ns168p250 := BSN.cos_dyadic_bound_f 85429182 134217728 3 2 134217728 67108864 Ns168p247 Ns168p124 Ns168p248 Ns168p249 Ns168p127 Ns168p248 107935588 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 85429182) qz363 0 2 Ns168p247 Ns168p124 Ns168p248 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 85429182) qz364 0 2 Ns168p249 Ns168p127 Ns168p248 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p251 := Ns168p202 62975 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 70775499 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 0 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 107935588 134217728) qz31 rfl rfl (Ns168p234 RS169to186.d9 RS169to186.d11 RS169to186.d13 RS169to186.d17 (Ns168p238 rfl rfl) (Ns168p242 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns168p233 rfl) RS169to186.d19 RS169to186.d21 RS169to186.d23 RS169to186.d25 RS169to186.d17 (Ns168p246 rfl rfl) (Ns168p250 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns168p252 := nat_lit 46370286565716298793622828652236957838838569191345954027385445039905 

noncomputable def Ns168p253 := nat_lit 2232518687821841525805542002376926991738332785424248335205023521 

noncomputable def Ns168p254 := nat_lit 121442374070429071001779913687854850743733438200443954622038214590241 

noncomputable def Ns168p255 := BSN.sin_dyadic_bound_f 82908563 134217728 3 2 134217728 67108864 Ns168p252 Ns168p112 Ns168p253 Ns168p254 Ns168p115 Ns168p253 77735620 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 82908563) qz361 0 2 Ns168p252 Ns168p112 Ns168p253 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 82908563) qz362 0 2 Ns168p254 Ns168p115 Ns168p253 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p256 := nat_lit 118559518744349802893929781968211449680528601687576057112166400000000 

noncomputable def Ns168p257 := nat_lit 14592285095983950159384580002520347319548248719360000000000000000 

noncomputable def Ns168p258 := nat_lit 310489399678379795469558044406264001934295640588582138150912000000000 

noncomputable def Ns168p259 := BSN.sin_dyadic_bound_f 104837200 134217728 3 2 134217728 67108864 Ns168p256 Ns168p112 Ns168p257 Ns168p258 Ns168p115 Ns168p257 94497277 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 104837200) qz361 0 2 Ns168p256 Ns168p112 Ns168p257 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 104837200) qz362 0 2 Ns168p258 Ns168p115 Ns168p257 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p260 := Ns168p200 84887 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 77735620 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 91 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 94497277 134217728) qz31 rfl rfl (Ns168p251 rfl rfl) (Ns168p233 rfl) RS169to186.d27 RS169to186.d29 RS169to186.d31 RS169to186.d33 RS169to186.d17 (Ns168p255 rfl rfl) (Ns168p259 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns168p261 := nat_lit 9552563053104941226637045732461395018386187542928113039382468965186978641145179108448947608922033757229056 

noncomputable def Ns168p262 := nat_lit 5312635904875365906383274475929879443961328774090953580081983688365267397646716638440517772988256256 

noncomputable def Ns168p263 := nat_lit 47710387765197539415798529324128128995676486365930629373418562784075957635369536241506463092335753472905216 

noncomputable def Ns168p264 := BSN.sin_dyadic_bound_f 204381934 134217728 4 3 134217728 67108864 Ns168p261 Ns168p144 Ns168p262 Ns168p263 Ns168p147 Ns168p262 134062931 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 204381934) qz361 0 3 Ns168p261 Ns168p144 Ns168p262 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 204381934) qz362 0 3 Ns168p263 Ns168p147 Ns168p262 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p265 := Ns168p198 Bool.false 181935853 84887 Bool.true 204381934 7074237752028440 1 Bool.false 134062931 Bool.false Bool.false 229334252 94591 BSN.abs_quadSignPos qz365 (BSN.sfrac_eq_quadSignPos_mul Bool.false 134062931 134217728) qz31 rfl (Ns168p260 rfl) (Ns168p233 rfl) RS169to186.d35 RS169to186.d37 RS169to186.d17 (Ns168p264 rfl rfl) rfl 

noncomputable def Ns168p266 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz28) qz28 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz28) qz28 8) 229334252 134217728 94591 134217728 229334252 134217728 94591 134217728 61561444512038912 57333563 16777216 94591 67108864 (Ns168p265 rfl rfl rfl rfl) 

noncomputable def Ns168p267 := @Enclosure.Real.IsNear.mulLit_ff qz646 (Zeta.RiemannSiegel.correction qz30) 2918169 8388608 1 8388608 34272101431167 70368744177664 1240816833639223 4947802324992000000 100011783961287173223 590295810358705651712 

noncomputable abbrev qz649 := (@HPow.hPow Real Real Real qz7 qz29 qz9)

noncomputable def Ns168p268 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz649 1 1 0 1 2918169 8388608 1 8388608 2918169 8388608 1 8388608 

noncomputable def Ns168p269 := @Enclosure.Real.IsNear.sqrt_image qz29 14320159251 209715200 5363 209715200 69318441 69318468 8388608 (@Enclosure.Real.IsNear.of_eq qz29 (@HMul.hMul Real Real Real qz5 qz28 qz3) Bool.false 14320159251 209715200 5363 209715200 (BSN.t_div_two_pi_mk qz28 429040 1000 qz31) (@Enclosure.Real.IsNear.mulLit_ff qz28 qz3 429040 1000 0 1 2670177 16777216 1 16777216 14320159251 209715200 5363 209715200 (Enclosure.Real.IsNear.const Bool.false 429040 1000) RS169to186.d40 rfl)) 

noncomputable abbrev qz899 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 429040 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz650 := qz899

noncomputable abbrev qz386 := qz650

noncomputable abbrev qz33 := qz386

noncomputable def Ns168p270 := @Enclosure.Real.IsNear.sqrt_image qz33 138636909 16777216 27 16777216 24114004 24114010 8388608 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 138636909 16777216 27 16777216 138636909 16777216 27 16777216 (Ns168p269 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns168p271 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz33) 24114007 8388608 3 8388608 2918168 2918170 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz33) Bool.false 48228014 16777216 6 16777216 24114007 8388608 3 8388608 (Ns168p270 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns168p272 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz33)) Bool.false 5836338 16777216 2 16777216 2918169 8388608 1 8388608 (Ns168p271 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz34 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz378))

noncomputable abbrev qz651 := (@HMul.hMul Real Real Real qz890 qz898 qz898)

noncomputable abbrev qz387 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz651 qz645) qz641)

noncomputable abbrev qz35 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz387))

noncomputable def Ns168p273 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz30) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz34) qz35) Bool.false 34272101431167 

noncomputable def Ns168p274 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz34) qz35 99723577 8388608 3135 

noncomputable abbrev qz652 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz34))

noncomputable def Ns168p275 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz34) (@Neg.neg Real Real.instNeg qz652) Bool.true 99723577 8388608 3135 2097152 (BSN.inv_eq_neg_inv_neg qz34) 

noncomputable def Ns168p276 := @Enclosure.Real.IsNear.recentre' qz652 Bool.false 199447154 16777216 25080 16777216 99723577 8388608 

noncomputable def Ns168p277 := @Enclosure.Real.IsNear.recentre' qz34 Bool.true 705638 8388608 199638608 18874368000000 352819 4194304 12477413 1179648000000 

noncomputable abbrev qz36 := (@HMul.hMul Real Real Real qz342 qz340 qz378)

noncomputable def Ns168p278 := @Enclosure.Real.IsNear.cos_image qz36 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 27766533) qz370) Bool.false 27766533 16777216 85 8388608 Bool.true 705638 8388608 1 

noncomputable def Ns168p279 := nat_lit 728624036082149703029771261 

noncomputable def Ns168p280 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz30 884279719003555 140737488355328 1 500000000000000 4419181 16777216 27 16777216 3907792132905849188455 2361183241434822606848 Ns168p279 

noncomputable def Ns168p281 := @Enclosure.Real.IsNear.subLit_ff_p qz33 qz1 138636909 16777216 27 16777216 8 1 0 1 4419181 4419181 16777216 27 

noncomputable def Ns168p282 := @Ns168p281 16777216 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 138636909 16777216 27 16777216 138636909 16777216 27 16777216 (Ns168p269 rfl rfl rfl rfl rfl rfl) rfl) qz371 

noncomputable def Ns168p283 := @Enclosure.Real.IsNear.recentre' qz36 Bool.false 3907792132905849188455 2361183241434822606848 Ns168p279 Ns168p163 27766533 16777216 85 8388608 (@Ns168p280 Ns168p163 RS169to186.d39 (Ns168p282 rfl rfl) rfl) 

noncomputable def Ns168p284 := nat_lit 74801082189856381962496200763076700608416973210765198363892464984617841066718184478054766620241 

noncomputable def Ns168p285 := nat_lit 210019621884916849631929422989350109657693281358030871296782980736998258952878090280250961 

noncomputable def Ns168p286 := nat_lit 452447149696460424971098103659176352766916302141318475339631503226164152228563518491304041393745 

noncomputable def Ns168p287 := BSN.cos_dyadic_bound_t 27766533 16777216 4 3 8388608 2250000 Ns168p284 Ns168p169 Ns168p285 Ns168p286 Ns168p172 Ns168p285 705638 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 27766533) qz642 0 3 Ns168p284 Ns168p169 Ns168p285 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 27766533) (BSN.cosOddQ 16777216) 0 3 Ns168p286 Ns168p172 Ns168p285 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p288 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz34) 352819 4194304 12477413 1179648000000 99711037 99736117 8388608 (@Enclosure.Real.IsNear.neg qz34 Bool.true 352819 4194304 12477413 1179648000000 (Ns168p277 (@Ns168p278 2250000 (Ns168p283 rfl) (Enclosure.sfrac_false_div 27766533 16777216) (Ns168p287 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns168p289 := Ns168p275 (@Enclosure.Real.IsNear.neg qz652 Bool.false 99723577 8388608 3135 2097152 (@Ns168p276 3135 2097152 (Ns168p288 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p290 := @Enclosure.Real.IsNear.recentre' qz35 Bool.true 343671 8388608 

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz342 qz340 qz387)

noncomputable def Ns168p291 := @Enclosure.Real.IsNear.cos_image qz37 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 13520561)) qz360) Bool.true 13520561 8388608 

noncomputable def Ns168p292 := nat_lit 63849045283189578196140384805 

noncomputable def Ns168p293 := nat_lit 18664145501433946406770627861685537 

noncomputable def Ns168p294 := @Enclosure.Real.IsNear.recentre' qz37 Bool.true Ns168p292 Ns168p178 Ns168p293 

noncomputable abbrev qz38 := qz387

noncomputable def Ns168p295 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz38 884279719003555 140737488355328 1 500000000000000 72204579513751 

noncomputable abbrev qz388 := (@HSub.hSub Real Real Real qz633 qz651 qz645)

noncomputable abbrev qz39 := qz388

noncomputable def Ns168p296 := @Enclosure.Real.IsNear.subLit_tf qz39 qz25 54612393469335 281474976710656 691621335 281474976710656 1 16 

noncomputable abbrev qz389 := qz651

noncomputable abbrev qz40 := qz389

noncomputable def Ns168p297 := @Enclosure.Real.IsNear.subLit_ff_n qz40 qz30 19529160710761 281474976710656 238636503 281474976710656 4419181 16777216 27 16777216 

noncomputable def Ns168p298 := @Enclosure.Real.IsNear.mulLit_ff qz30 qz30 4419181 16777216 27 16777216 4419181 16777216 27 16777216 19529160710761 281474976710656 

noncomputable def Ns168p299 := nat_lit 16419724199429671511362966487832758601623403490673395324402110183800204504036080308083073601 

noncomputable def Ns168p300 := nat_lit 37319562393244313922288185966620189814174094592209103058532781170470688946885615264321 

noncomputable def Ns168p301 := nat_lit 99347103744335176977960195644544077136229080370800398039499585299862516813154572179814064705 

noncomputable def Ns168p302 := BSN.cos_dyadic_bound_t 13520561 8388608 4 3 8388608 2250000 Ns168p299 Ns168p187 Ns168p300 Ns168p301 Ns168p190 Ns168p300 343671 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 13520561) (BSN.cosEvenQ 8388608) 0 3 Ns168p299 Ns168p187 Ns168p300 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 13520561) (BSN.cosOddQ 8388608) 0 3 Ns168p301 Ns168p190 Ns168p300 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p303 := @Ns168p290 150444304 9437184000000 343671 8388608 9402769 589824000000 (@Ns168p291 65 4194304 Bool.true 343671 8388608 1 2250000 (@Ns168p294 Ns168p181 13520561 8388608 65 4194304 (@Ns168p295 281474976710656 691621335 281474976710656 Ns168p292 Ns168p178 Ns168p293 Ns168p181 RS169to186.d39 (@Ns168p296 0 1 1155273272220016 72204579513751 281474976710656 691621335 281474976710656 (@Ns168p297 916243921512022671360 54612393469335 281474976710656 691621335 281474976710656 (@Ns168p298 238636503 281474976710656 (Ns168p282 rfl rfl) (Ns168p282 rfl rfl) rfl) (Ns168p282 rfl rfl) rfl rfl) qz375 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 13520561 8388608) (BSN.cos_neg_of_bound 13520561 8388608 Bool.true 343671 8388608 1 2250000 (Ns168p302 rfl rfl)) rfl rfl) 

noncomputable def Ns168p304 := @Ns168p267 1449329686621140124639 Ns168p195 (Ns168p268 qz27 (@Enclosure.Real.IsNear.of_eq qz649 (@Inv.inv Real Real.instInv (Real.sqrt qz33)) Bool.false 2918169 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz29 (BSN.t_div_two_pi_nonneg qz28 429040 1000 qz31)) Ns168p272) rfl) (@Ns168p273 70368744177664 1240816833639223 4947802324992000000 (BSN.correction_mk qz30 (BSN.cos_two_pi_p_ne_zero_mk qz28 429040 1000 8 qz31 rfl rfl (@BSN.floor_sqrt_eq_dec qz28 429040 1000 8 qz31 rfl rfl rfl))) (@Ns168p274 2097152 343671 8388608 9402769 589824000000 34272101431167 70368744177664 1240816833639223 4947802324992000000 Ns168p289 (Ns168p303 rfl) rfl)) 

noncomputable def Ns168p305 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz28) (hardyZApproximantRS₀ qz28) Bool.false 1917233629809203895193 590295810358705651712 24850208172787053724639 Ns168p195 (@Eq.refl Real (hardyZApproximantRS₀ qz28)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz28) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz28) qz28 8) (@HMul.hMul Real Real Real qz5 qz646 (Zeta.RiemannSiegel.correction qz30))) Bool.false 1917233629809203895193 590295810358705651712 24850208172787053724639 Ns168p195 (BSN.hardyZApproximantRS₀_eq qz28 8 (@BSN.floor_sqrt_eq_dec qz28 429040 1000 8 qz31 rfl rfl rfl)) (@Ns168p197 1917233629809203895193 590295810358705651712 24850208172787053724639 Ns168p195 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz28) qz28 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz28) qz28 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz28) qz28 8)) Bool.false 57333563 16777216 94591 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz28) qz28 8) (Ns168p266 (Ns168p265 rfl rfl rfl rfl) rfl rfl)) (Ns168p304 rfl) rfl rfl)) 

theorem RS169to186.d43 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz28) Bool.false 1917233629809203895193 590295810358705651712 24850208172787053724639 Ns168p195 := Ns168p305 

noncomputable abbrev qz653 := (@HMul.hMul Real Real Real qz890 (Real.sqrt qz895) qz892)

noncomputable abbrev qz390 := qz653

noncomputable abbrev qz41 := qz390

noncomputable abbrev qz391 := (@HMul.hMul Real Real Real qz628 (@HMul.hMul Real Real Real qz628 qz653 qz653) qz653)

noncomputable abbrev qz42 := (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz391))

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz342 (@HMul.hMul Real Real Real qz342 qz368 qz368) qz368)

noncomputable abbrev qz654 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz41))

noncomputable def Ns168p306 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz357 (@HAdd.hAdd Real Real Real qz357 qz654 qz42) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz43))) Bool.false 

noncomputable def Ns168p307 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz357 qz654 qz42) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz43)) 17168603 536870912 

noncomputable def Ns168p308 := @Enclosure.Real.IsNear.addLit_ff qz654 qz42 2146075 67108864 25 67108864 

noncomputable def Ns168p309 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz41) 25 4 0 1 85843 16777216 1 16777216 2146075 

noncomputable def Ns168p310 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz41) Bool.false 85843 16777216 1 16777216 85843 16777216 1 16777216 

noncomputable def Ns168p311 := @Enclosure.Real.IsNear.mulLit_ff qz19 qz8 1505817 524288 3 8388608 35676234897 524288000 13361 524288000 53721881003895849 274877906944000 214468139883 

noncomputable def Ns168p312 := @Enclosure.Real.IsNear.sqrt_image qz8 35676234897 524288000 13361 524288000 69198131 69198158 8388608 qz366 

noncomputable def Ns168p313 := @Enclosure.Real.IsNear.sqrt_image qz18 138396289 16777216 27 16777216 24093069 24093075 8388608 (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 138396289 16777216 27 16777216 138396289 16777216 27 16777216 (Ns168p312 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz392 := (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 48186144 16777216 6 16777216 1505817 524288 3 8388608 (Ns168p313 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns168p314 := @Ns168p311 2199023255552000 qz392 

noncomputable def Ns168p315 := Ns168p314 qz366 

noncomputable def Ns168p316 := @Enclosure.Real.IsNear.inv_image qz41 53721881003895849 274877906944000 214468139883 2199023255552000 42921 42922 8388608 (Ns168p315 rfl) rfl rfl 

noncomputable abbrev qz44 := (@Inv.inv Real Real.instInv qz391)

noncomputable def Ns168p317 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz44 1 32 0 1 3 

noncomputable def Ns168p318 := @Enclosure.Real.IsNear.recentre' qz44 Bool.false 3 16777216 1 16777216 

noncomputable def Ns168p319 := nat_lit 155043524238038616009647785079213326961441846645049 

noncomputable def Ns168p320 := nat_lit 20769187434139310514121985316880384000000000 

noncomputable def Ns168p321 := nat_lit 118841096877882485057541373539615640442614031787 

noncomputable def Ns168p322 := nat_lit 10633823966279326983230456482242756608000000000 

noncomputable abbrev qz45 := qz391

noncomputable def Ns168p323 := @Enclosure.Real.IsNear.inv_image qz45 Ns168p319 Ns168p320 Ns168p321 Ns168p322 1 2 

noncomputable def Ns168p324 := nat_lit 2886040498596745672759115639430801 

noncomputable def Ns168p325 := nat_lit 75557863725914323419136000000 

noncomputable def Ns168p326 := nat_lit 184346156235325671454775984361 

noncomputable def Ns168p327 := nat_lit 4835703278458516698824704000000 

noncomputable abbrev qz393 := (@HMul.hMul Real Real Real qz628 qz653 qz653)

noncomputable abbrev qz46 := qz393

noncomputable def Ns168p328 := @Enclosure.Real.IsNear.mulLit_ff qz46 qz41 Ns168p324 Ns168p325 Ns168p326 Ns168p327 53721881003895849 274877906944000 214468139883 

noncomputable def Ns168p329 := @Enclosure.Real.IsNear.mulLit_ff qz41 qz41 53721881003895849 274877906944000 214468139883 2199023255552000 53721881003895849 274877906944000 214468139883 2199023255552000 Ns168p324 

noncomputable def Ns168p330 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz43) 13 10 0 1 354065 8388608 1 

noncomputable def Ns168p331 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz43) Bool.false 708130 16777216 2 16777216 354065 8388608 

noncomputable def Ns168p332 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz19 qz19) qz19 2267484837489 274877906944 144558441 70368744177664 1505817 524288 3 8388608 3414417215533173513 

noncomputable def Ns168p333 := @Enclosure.Real.IsNear.mulLit_ff qz19 qz19 1505817 524288 3 8388608 1505817 524288 3 8388608 2267484837489 274877906944 144558441 

noncomputable def Ns168p334 := @Ns168p333 70368744177664 qz392 

noncomputable def Ns168p335 := Ns168p334 qz392 

noncomputable def Ns168p336 := @Ns168p332 144115188075855872 5224285716087627 590295810358705651712 (Ns168p335 rfl) qz392 

noncomputable def Ns168p337 := @Enclosure.Real.IsNear.inv_image qz43 3414417215533173513 144115188075855872 5224285716087627 590295810358705651712 354064 354066 8388608 (Ns168p336 rfl) 

noncomputable def Ns168p338 := @Ns168p307 201 536870912 920569 16777216 13 83886080 782268079538176 46626811 536870912 1421 2684354560 (@Ns168p308 3 536870912 1 536870912 1152165443796992 17168603 536870912 201 536870912 (@Ns168p309 67108864 25 67108864 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns168p310 (Ns168p316 rfl rfl rfl rfl) rfl) rfl) (@Ns168p317 16777216 1 16777216 3 536870912 1 536870912 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns168p318 3 16777216 1 16777216 (@Ns168p323 8388608 (@Ns168p328 2199023255552000 Ns168p319 Ns168p320 Ns168p321 Ns168p322 (@Ns168p329 Ns168p325 Ns168p326 Ns168p327 (Ns168p315 rfl) (Ns168p315 rfl) rfl) (Ns168p315 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns168p330 8388608 920569 16777216 13 83886080 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns168p331 1 8388608 (Ns168p337 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS169to186.d44 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 := @Ns168p306 46626811 536870912 1421 2684354560 (BSN.hardyZErrorBoundRS₀_mk qz4 427552 1000 qz11 rfl rfl) (Ns168p338 rfl rfl) 

noncomputable def Ns168p339 := nat_lit 166020696663385964544000000 

noncomputable def Ns168p340 := nat_lit 2036534750353761802486022144 

noncomputable abbrev qz900 := (Enclosure.sfrac Bool.false 430527 1000)

noncomputable abbrev qz655 := qz900

noncomputable abbrev qz394 := qz655

noncomputable abbrev qz47 := qz394

noncomputable abbrev qz901 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 430527 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz656 := qz901

noncomputable abbrev qz395 := qz656

noncomputable abbrev qz48 := qz395

noncomputable abbrev qz902 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 430527 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz657 := qz902

noncomputable abbrev qz396 := qz657

noncomputable abbrev qz49 := qz396

noncomputable abbrev qz658 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz48 qz9))

noncomputable def Ns168p341 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz47) qz47 8) (@HMul.hMul Real Real Real qz5 qz658 (Zeta.RiemannSiegel.correction qz49)) 4135145 16777216 11865 8388608 48640690206938198889 295147905179352825856 7099474019224969857067 Ns168p339 Ns168p340 

noncomputable def Ns168p342 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz47) qz47 Real.sin BSN.quadSignPos 7 8 430527 1000 127 134217728 67108864 2251799813685248 Bool.false 93186199245 1680 279097919 60 47453128 8 

noncomputable def Ns168p343 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz47) qz47 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 430527 1000 49 91 134217728 67108864 2251799813685248 Bool.false 93186199245 1680 

noncomputable def Ns168p344 := Ns168p343 240485871 61 54794152 8 261175631 61 50729528 8 Bool.true 81876533 63195 Bool.true 18854346 Bool.true 71548656 7074237752028440 1 Bool.false 18792396 Bool.true Bool.false 68207778 Bool.false Bool.true 63768382 

noncomputable def Ns168p345 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz47) qz47 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 430527 1000 62 0 134217728 67108864 2251799813685248 Bool.false 93186199245 1680 

noncomputable def Ns168p346 := Ns168p345 186065264 60 67108856 8 216015088 60 60023992 8 Bool.true 26005599 37115 Bool.false 8699054 Bool.false 185871453 7074237752028440 1 Bool.false 133935920 Bool.true Bool.false 24813689 Bool.false Bool.true 81876533 

noncomputable def Ns168p347 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz47) qz47 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 430527 1000 252 140 134217728 67108864 2251799813685248 Bool.false 93186199245 1680 

noncomputable def Ns168p348 := Ns168p347 93032624 60 94906264 8 147453232 60 77490640 16 Bool.true 134217696 1748 Bool.false 4306770 Bool.false 187581653 7074237752028440 1 Bool.false 134148636 Bool.false Bool.false 23131001 Bool.false Bool.true 26005599 

noncomputable def Ns168p349 := nat_lit 79646298369288682713062522289969078609380870936100461271 

noncomputable def Ns168p350 := nat_lit 114715969717528532885076492879710356856913239474176000 

noncomputable def Ns168p351 := nat_lit 7099776638842554567030960675360000 

noncomputable def Ns168p352 := nat_lit 18339884765654744497810363340260288320 

noncomputable abbrev qz397 := (@Eq.refl Real qz655)

noncomputable abbrev qz50 := qz397

noncomputable def Ns168p353 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz47 430527 1000 741414990916 16000000 861054 4000 2000 Ns168p351 Ns168p352 qz50 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns168p354 := nat_lit 229381339303551406213620064195110946395016908295969328460480 

noncomputable abbrev qz659 := (Real.log (Enclosure.sfrac Bool.false 741414990916 16000000))

noncomputable abbrev qz51 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 430527 4000) qz659) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 861054))))))

noncomputable abbrev qz660 := (Enclosure.sfrac Bool.false 430527 2000)

noncomputable abbrev qz398 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz51 qz660) (@HMul.hMul Real Real Real qz5 qz660 (Real.log Real.pi)))

noncomputable def Ns168p355 := @Enclosure.Real.IsNear.addLit_ft_p qz398 (Enclosure.sfrac Bool.true Ns168p351 Ns168p352) 12507246917457284008839 18014398509481984000 46102142795425423 3686400000000000000000 Ns168p351 Ns168p352 0 1 Ns168p354 

noncomputable def Ns168p356 := nat_lit 839347132398060098358551248896000 

noncomputable abbrev qz399 := (@HSub.hSub Real Real Real qz12 qz51 qz660)

noncomputable abbrev qz400 := (@HMul.hMul Real Real Real qz5 qz660 (Real.log Real.pi))

noncomputable def Ns168p357 := @Enclosure.Real.IsNear.subLit_ff_p qz399 qz400 16946329076470419131271 18014398509481984000 43852711625129 7200000000000000000 16536869701047 67108864000 430527 67108864000 Ns168p356 12507246917457284008839 18014398509481984000 

noncomputable def Ns168p358 := nat_lit 6778531630588167652508400 

noncomputable abbrev qz401 := qz660

noncomputable def Ns168p359 := @Enclosure.Real.IsNear.subLit_ff_p qz51 qz401 4164834310003258838811 3602879701896396800 43852711625129 7200000000000000000 430527 2000 0 1 Ns168p358 16946329076470419131271 18014398509481984000 43852711625129 7200000000000000000 

noncomputable def Ns168p360 := nat_lit 9378373123295266663886320055120560128 

noncomputable def Ns168p361 := nat_lit 25976738082013470345134080 

noncomputable def Ns168p362 := nat_lit 6224238984815806417959211625500230343614849358112857336422229178174975094339829282169286214034718720 

noncomputable def Ns168p363 := nat_lit 62157337379048605503458144006207691085370652497721214422721471068106659299395108213572923331969024 

noncomputable def Ns168p364 := nat_lit 518680365828882631732453895716192679607508133104780542219116727681648352500874216667408302080 

noncomputable def Ns168p365 := BSN.log_dyadic_bound 217126990916 1265702990916 5 4 Ns168p362 67108864 18000000 Ns168p363 Ns168p364 23254520 1482829981832 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 217126990916) (BSN.artanhQ 1265702990916) 0 4 Ns168p363 Ns168p362 Ns168p364 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns168p366 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 430527 4000) qz659 430527 4000 0 1 48385445181305465 4503599627370496 100000027 1800000000000000 4166248111514379586011 3602879701896396800 14350903874743 2400000000000000000 (Enclosure.Real.IsNear.const Bool.false 430527 4000) (BSN.isNear_log_sfrac 741414990916 16000000 48385445181305465 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 741414990916) qz353)) Bool.false Ns168p361 Ns168p89 1000000270000000 18000000000000000000000 48385445181305465 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 741414990916 16000000 15 1482829981832 1048576000000 23254520 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns168p365 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p367 := BSN.arctan_dyadic_bound_f 1000 861054 1 0 8388608 2250000 0 1 1 0 1 1 9742 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 861054) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 861054) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz402 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 861054)))

noncomputable def Ns168p368 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz402 884279719003555 562949953421312 1 2000000000000000 9742 8388608 1 2250000 7412391666624743079936 883625944450467 562949953421312 8000000009 18000000000000000 qz16 (Ns168p367 rfl) rfl rfl 

noncomputable def Ns168p369 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 430527 4000) qz659) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz402)) 4166248111514379586011 3602879701896396800 14350903874743 2400000000000000000 883625944450467 2251799813685248 8000000009 72000000000000000 Ns168p360 4164834310003258838811 3602879701896396800 43852711625129 7200000000000000000 (Ns168p366 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz402) 1 4 0 1 883625944450467 562949953421312 8000000009 18000000000000000 883625944450467 2251799813685248 8000000009 72000000000000000 qz356 Ns168p368 rfl) 

noncomputable def Ns168p370 := @Ns168p355 Ns168p349 Ns168p350 46102142795425423 3686400000000000000000 (@Ns168p357 46102142795425423 3686400000000000000000 (Ns168p359 (Ns168p369 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 430527 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz401 (Real.log Real.pi) 430527 2000 0 1 38410761 33554432 1 33554432 16536869701047 67108864000 430527 67108864000 (Enclosure.Real.IsNear.const Bool.false 430527 2000) RS169to186.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns168p351 Ns168p352) 

noncomputable def Ns168p371 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz47) Bool.false Ns168p349 Ns168p350 46102142795425423 3686400000000000000000 11648274905 16777216 211 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz47) (@HAdd.hAdd Real Real Real qz357 qz398 (Enclosure.sfrac Bool.true Ns168p351 Ns168p352)) Bool.false Ns168p349 Ns168p350 46102142795425423 3686400000000000000000 Ns168p353 (Ns168p370 rfl rfl)) 

noncomputable def Ns168p372 := nat_lit 3796287819721941377351680 

noncomputable def Ns168p373 := nat_lit 855632799401802093237224969698511823153984726643727938592004022127406804072703285728312948622462459743866353814110533405583518771259681 

noncomputable def Ns168p374 := nat_lit 607787790661955206780205473434228002024688340622524881789824005848075091001295722811390184145965444271510187997015047604211362081 

noncomputable def Ns168p375 := nat_lit 4272857150105171294386052187287851890128830335010376748516884195282613212303345817583325736852160500055096064112511455320489089146366241 

noncomputable def Ns168p376 := BSN.sin_dyadic_bound_f 53948494663 34359738368 4 3 16777216 4504395 Ns168p373 Ns168p103 Ns168p374 Ns168p375 Ns168p106 Ns168p374 16777212 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53948494663) qz358 0 3 Ns168p373 Ns168p103 Ns168p374 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53948494663) qz359 0 3 Ns168p375 Ns168p106 Ns168p374 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p377 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz47) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11648274905) qz370) Bool.false 11648274905 16777216 211 16777216 Bool.true 16777212 16777216 1 2250000 (Ns168p371 rfl) (Enclosure.sfrac_false_div 11648274905 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11648274905) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns168p372) qz385) 226375608064910080 72057594037927936 Bool.false 16777212 16777216 110 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 11648274905 16777216 226375608064910080 72057594037927936 110 Ns168p372 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777212 16777216 Ns168p372 Ns168p89 53948494663 34359738368 4504395 4500000 (Ns168p376 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p378 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz47) Bool.false Ns168p349 Ns168p350 46102142795425423 3686400000000000000000 93186199245 134217728 1680 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz47) (@HAdd.hAdd Real Real Real qz357 qz398 (Enclosure.sfrac Bool.true Ns168p351 Ns168p352)) Bool.false Ns168p349 Ns168p350 46102142795425423 3686400000000000000000 Ns168p353 (Ns168p370 rfl rfl)) 

noncomputable def Ns168p379 := Ns168p348 37115 BSN.abs_quadSignPos (BSN.cos_quad_nat0 252 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 134148636 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 140 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 23131001 134217728) qz50 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz47) qz47 1) Bool.true 4194303 4194304 30720451 2359296000000 134217696 134217728 1748 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz47) qz47 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz47)) Bool.true 4194303 4194304 30720451 2359296000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz47) qz47) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz47)) Bool.true 16777212 16777216 491527216 37748736000000 4194303 4194304 30720451 2359296000000 (Ns168p377 rfl rfl) rfl)) rfl) (Ns168p378 rfl) RS169to186.d7 

noncomputable def Ns168p380 := nat_lit 344038239600992862322410000 

noncomputable def Ns168p381 := BSN.cos_dyadic_bound_f 4306770 134217728 2 1 134217728 67108864 Ns168p380 Ns168p130 Ns168p380 Ns168p380 Ns168p131 Ns168p380 134148636 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 4306770) qz363 0 1 Ns168p380 Ns168p130 Ns168p380 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 4306770) qz364 0 1 Ns168p380 Ns168p131 Ns168p380 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p382 := nat_lit 2608264861340374171282940346118367130724658015955684593088848891929386705403011472990679607724035922421521 

noncomputable def Ns168p383 := nat_lit 1897947973416439519578917055783984795047392023066619306053079888400748963205740328818626583210977041 

noncomputable def Ns168p384 := nat_lit 15799561684696958566133109289239804133759614380436859840014422574477430233742424965648269096845498992256785 

noncomputable def Ns168p385 := BSN.cos_dyadic_bound_f 187581653 134217728 4 3 134217728 67108864 Ns168p382 Ns168p118 Ns168p383 Ns168p384 Ns168p121 Ns168p383 23131001 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 187581653) qz363 0 3 Ns168p382 Ns168p118 Ns168p383 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 187581653) qz364 0 3 Ns168p384 Ns168p121 Ns168p383 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p386 := nat_lit 5726484731035691690221847056 

noncomputable def Ns168p387 := BSN.cos_dyadic_bound_f 8699054 134217728 2 1 134217728 67108864 Ns168p386 Ns168p130 Ns168p386 Ns168p386 Ns168p131 Ns168p386 133935920 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 8699054) qz363 0 1 Ns168p386 Ns168p130 Ns168p386 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 8699054) qz364 0 1 Ns168p386 Ns168p131 Ns168p386 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p388 := nat_lit 2514233505418899766931600658143528056103161260120840515779174474881748826133813343482065752736361564932721 

noncomputable def Ns168p389 := nat_lit 1700404819339368034049200569102944120566189410098694606827190210489172188513416658641710273240304241 

noncomputable def Ns168p390 := nat_lit 15230794514547040222970171891329861343415940013425896533502228680102263716018366954284951635989999774403185 

noncomputable def Ns168p391 := BSN.cos_dyadic_bound_f 185871453 134217728 4 3 134217728 67108864 Ns168p388 Ns168p118 Ns168p389 Ns168p390 Ns168p121 Ns168p389 24813689 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 185871453) qz363 0 3 Ns168p388 Ns168p118 Ns168p389 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 185871453) qz364 0 3 Ns168p390 Ns168p121 Ns168p389 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p392 := Ns168p346 63195 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 62 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133935920 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 0 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 24813689 134217728) qz50 rfl rfl (Ns168p379 RS169to186.d9 RS169to186.d11 RS169to186.d13 RS169to186.d17 (Ns168p381 rfl rfl) (Ns168p385 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns168p378 rfl) RS169to186.d19 RS169to186.d21 RS169to186.d23 RS169to186.d25 RS169to186.d17 (Ns168p387 rfl rfl) (Ns168p391 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns168p393 := nat_lit 126370554341331452641510096656 

noncomputable def Ns168p394 := nat_lit 38942226439011207213978722469150720 

noncomputable def Ns168p395 := nat_lit 272595585073078450497851057284055040 

noncomputable def Ns168p396 := BSN.sin_dyadic_bound_f 18854346 134217728 2 1 134217728 67108864 Ns168p393 Ns168p394 Ns168p393 Ns168p393 Ns168p395 Ns168p393 18792396 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 18854346) qz361 0 1 Ns168p393 Ns168p394 Ns168p393 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 18854346) qz362 0 1 Ns168p393 Ns168p395 Ns168p393 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p397 := nat_lit 25718097403609350201511945796937827783691957797981741246731612323840 

noncomputable def Ns168p398 := nat_lit 686770831618845663854985472607203323010068986688910449564450816 

noncomputable def Ns168p399 := nat_lit 67355809856678058110980283301214851580479777930640397410235880308736 

noncomputable def Ns168p400 := BSN.sin_dyadic_bound_f 71548656 134217728 3 2 134217728 67108864 Ns168p397 Ns168p112 Ns168p398 Ns168p399 Ns168p115 Ns168p398 68207778 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 71548656) qz361 0 2 Ns168p397 Ns168p112 Ns168p398 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 71548656) qz362 0 2 Ns168p399 Ns168p115 Ns168p398 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p401 := Ns168p344 85183 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 18792396 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 91 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 68207778 134217728) qz50 rfl rfl (Ns168p392 rfl rfl) (Ns168p378 rfl) RS169to186.d27 RS169to186.d29 RS169to186.d31 RS169to186.d33 RS169to186.d17 (Ns168p396 rfl rfl) (Ns168p400 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns168p402 := nat_lit 8368859018509781282600222250941087876678050649807909208839325525547070057752180211598863744915100019494561 

noncomputable def Ns168p403 := nat_lit 3574665241462956189896811741045617804198995573766512470116749436100735271953829820550363365229760161 

noncomputable def Ns168p404 := nat_lit 41804039991477036308094493323761025522860135729261253761304398232822036484770834290900724980315778077724321 

noncomputable def Ns168p405 := BSN.sin_dyadic_bound_f 197743833 134217728 4 3 134217728 67108864 Ns168p402 Ns168p144 Ns168p403 Ns168p404 Ns168p147 Ns168p403 133580410 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 197743833) qz361 0 3 Ns168p402 Ns168p144 Ns168p403 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 197743833) qz362 0 3 Ns168p404 Ns168p147 Ns168p403 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p406 := Ns168p342 Bool.true 63768382 85183 Bool.true 197743833 7074237752028440 1 Bool.false 133580410 Bool.false Bool.true 16540580 94920 BSN.abs_quadSignPos qz365 (BSN.sfrac_eq_quadSignPos_mul Bool.false 133580410 134217728) qz50 rfl (Ns168p401 rfl) (Ns168p378 rfl) RS169to186.d35 RS169to186.d37 RS169to186.d17 (Ns168p405 rfl rfl) rfl 

noncomputable def Ns168p407 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz47) qz47 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz47) qz47 8) 16540580 134217728 94920 134217728 16540580 134217728 94920 134217728 4440078134804480 4135145 16777216 11865 8388608 (Ns168p406 rfl rfl rfl rfl) 

noncomputable def Ns168p408 := @Enclosure.Real.IsNear.mulLit_ff qz658 (Zeta.RiemannSiegel.correction qz49) 1457823 4194304 1 8388608 33365292087543 70368744177664 2431738146224611 19791209299968000000 48640690206938198889 295147905179352825856 

noncomputable abbrev qz661 := (@HPow.hPow Real Real Real qz7 qz48 qz9)

noncomputable def Ns168p409 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz661 1 1 0 1 1457823 4194304 1 8388608 1457823 4194304 1 8388608 

noncomputable def Ns168p410 := @Enclosure.Real.IsNear.sqrt_image qz48 1149583293279 16777216000 430527 16777216000 69438461 69438488 8388608 (@Enclosure.Real.IsNear.of_eq qz48 (@HMul.hMul Real Real Real qz5 qz47 qz3) Bool.false 1149583293279 16777216000 430527 16777216000 (BSN.t_div_two_pi_mk qz47 430527 1000 qz50) (@Enclosure.Real.IsNear.mulLit_ff qz47 qz3 430527 1000 0 1 2670177 16777216 1 16777216 1149583293279 16777216000 430527 16777216000 (Enclosure.Real.IsNear.const Bool.false 430527 1000) RS169to186.d40 rfl)) 

noncomputable abbrev qz903 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 430527 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz662 := qz903

noncomputable abbrev qz403 := qz662

noncomputable abbrev qz52 := qz403

noncomputable def Ns168p411 := @Enclosure.Real.IsNear.sqrt_image qz52 138876949 16777216 27 16777216 24134871 24134877 8388608 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 138876949 16777216 27 16777216 138876949 16777216 27 16777216 (Ns168p410 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns168p412 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz52) 12067437 4194304 3 8388608 2915645 2915647 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz52) Bool.false 48269748 16777216 6 16777216 12067437 4194304 3 8388608 (Ns168p411 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns168p413 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz52)) Bool.false 5831292 16777216 2 16777216 1457823 4194304 1 8388608 (Ns168p412 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz53 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz396))

noncomputable abbrev qz663 := (@HMul.hMul Real Real Real qz890 qz902 qz902)

noncomputable abbrev qz404 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz663 qz657) qz641)

noncomputable abbrev qz54 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz404))

noncomputable def Ns168p414 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz49) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz53) qz54) Bool.false 33365292087543 

noncomputable def Ns168p415 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz53) qz54 48422937 8388608 1487 

noncomputable abbrev qz664 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz53))

noncomputable def Ns168p416 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz53) (@Neg.neg Real Real.instNeg qz664) Bool.true 48422937 8388608 1487 4194304 (BSN.inv_eq_neg_inv_neg qz53) 

noncomputable def Ns168p417 := @Enclosure.Real.IsNear.recentre' qz664 Bool.false 96845874 16777216 5948 16777216 48422937 8388608 

noncomputable def Ns168p418 := @Enclosure.Real.IsNear.recentre' qz53 Bool.true 1453211 8388608 401527216 37748736000000 1453211 8388608 25095451 2359296000000 

noncomputable abbrev qz55 := (@HMul.hMul Real Real Real qz342 qz340 qz396)

noncomputable abbrev qz405 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable def Ns168p419 := @Enclosure.Real.IsNear.cos_image qz55 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7318687) qz405) Bool.false 7318687 4194304 171 16777216 Bool.true 1453211 8388608 1 

noncomputable def Ns168p420 := nat_lit 728624036084211630929234941 

noncomputable def Ns168p421 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz49 884279719003555 140737488355328 1 500000000000000 4659221 16777216 27 16777216 4120054636655462530655 2361183241434822606848 Ns168p420 

noncomputable def Ns168p422 := @Enclosure.Real.IsNear.subLit_ff_p qz52 qz1 138876949 16777216 27 16777216 8 1 0 1 4659221 4659221 16777216 27 

noncomputable def Ns168p423 := @Ns168p422 16777216 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 138876949 16777216 27 16777216 138876949 16777216 27 16777216 (Ns168p410 rfl rfl rfl rfl rfl rfl) rfl) qz371 

noncomputable def Ns168p424 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 4120054636655462530655 2361183241434822606848 Ns168p420 Ns168p163 7318687 4194304 171 16777216 (@Ns168p421 Ns168p163 RS169to186.d39 (Ns168p423 rfl rfl) rfl) 

noncomputable def Ns168p425 := nat_lit 5514795033877461563542672272014248611283309085894611132260281620255586409811043571576961 

noncomputable def Ns168p426 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600 

noncomputable def Ns168p427 := nat_lit 23615551258455948690546048328130173613884713032300553871145672259937931470691479681 

noncomputable def Ns168p428 := nat_lit 33333903861351165025788966527017889296981691247614603599960038440307637393779772568744065 

noncomputable def Ns168p429 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600 

noncomputable def Ns168p430 := BSN.cos_dyadic_bound_t 7318687 4194304 4 3 8388608 2250000 Ns168p425 Ns168p426 Ns168p427 Ns168p428 Ns168p429 Ns168p427 1453211 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 7318687) (BSN.cosEvenQ 4194304) 0 3 Ns168p425 Ns168p426 Ns168p427 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 7318687) (BSN.cosOddQ 4194304) 0 3 Ns168p428 Ns168p429 Ns168p427 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p431 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz53) 1453211 8388608 25095451 2359296000000 48419963 48425911 8388608 (@Enclosure.Real.IsNear.neg qz53 Bool.true 1453211 8388608 25095451 2359296000000 (Ns168p418 (@Ns168p419 2250000 (Ns168p424 rfl) (Enclosure.sfrac_false_div 7318687 4194304) (Ns168p430 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns168p432 := Ns168p416 (@Enclosure.Real.IsNear.neg qz664 Bool.false 48422937 8388608 1487 4194304 (@Ns168p417 1487 4194304 (Ns168p431 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p433 := @Enclosure.Real.IsNear.recentre' qz54 Bool.true 689039 8388608 

noncomputable abbrev qz56 := (@HMul.hMul Real Real Real qz342 qz340 qz404)

noncomputable def Ns168p434 := @Enclosure.Real.IsNear.cos_image qz56 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6933305)) qz405) Bool.true 6933305 4194304 

noncomputable def Ns168p435 := nat_lit 65483214818732153889656535605 

noncomputable def Ns168p436 := nat_lit 19013943328673915170387182411049777 

noncomputable def Ns168p437 := @Enclosure.Real.IsNear.recentre' qz56 Bool.true Ns168p435 Ns168p178 Ns168p436 

noncomputable abbrev qz57 := qz404

noncomputable def Ns168p438 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz57 884279719003555 140737488355328 1 500000000000000 74052602826311 

noncomputable abbrev qz406 := (@HSub.hSub Real Real Real qz633 qz663 qz657)

noncomputable abbrev qz58 := qz406

noncomputable def Ns168p439 := @Enclosure.Real.IsNear.subLit_tf qz58 qz25 56460416781895 281474976710656 704583495 281474976710656 1 16 

noncomputable abbrev qz407 := qz663

noncomputable abbrev qz59 := qz407

noncomputable def Ns168p440 := @Enclosure.Real.IsNear.subLit_ff_n qz59 qz49 21708340326841 281474976710656 251598663 281474976710656 4659221 16777216 27 16777216 

noncomputable def Ns168p441 := @Enclosure.Real.IsNear.mulLit_ff qz49 qz49 4659221 16777216 27 16777216 4659221 16777216 27 16777216 21708340326841 281474976710656 

noncomputable def Ns168p442 := nat_lit 4437039419559236882215944317368803441338498524445289842248809212084333031963200349390625 

noncomputable def Ns168p443 := nat_lit 12339105166305429981164942809799074845243836637161903626739754011470026738525390625 

noncomputable def Ns168p444 := nat_lit 26838573542014626106945757744686120736953328767705579120520335367090536236926444790990625 

noncomputable def Ns168p445 := BSN.cos_dyadic_bound_t 6933305 4194304 4 3 8388608 2250000 Ns168p442 Ns168p426 Ns168p443 Ns168p444 Ns168p429 Ns168p443 689039 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 6933305) (BSN.cosEvenQ 4194304) 0 3 Ns168p442 Ns168p426 Ns168p443 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 6933305) (BSN.cosOddQ 4194304) 0 3 Ns168p444 Ns168p429 Ns168p443 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p446 := @Ns168p433 613027216 37748736000000 689039 8388608 38314201 2359296000000 (@Ns168p434 265 16777216 Bool.true 689039 8388608 1 2250000 (@Ns168p437 Ns168p181 6933305 4194304 265 16777216 (@Ns168p438 281474976710656 704583495 281474976710656 Ns168p435 Ns168p178 Ns168p436 Ns168p181 RS169to186.d39 (@Ns168p439 0 1 1184841645220976 74052602826311 281474976710656 704583495 281474976710656 (@Ns168p440 947248607799877304320 56460416781895 281474976710656 704583495 281474976710656 (@Ns168p441 251598663 281474976710656 (Ns168p423 rfl rfl) (Ns168p423 rfl rfl) rfl) (Ns168p423 rfl rfl) rfl rfl) qz375 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6933305 4194304) (BSN.cos_neg_of_bound 6933305 4194304 Bool.true 689039 8388608 1 2250000 (Ns168p445 rfl rfl)) rfl rfl) 

noncomputable def Ns168p447 := @Ns168p408 7099474019224969857067 Ns168p339 (Ns168p409 qz27 (@Enclosure.Real.IsNear.of_eq qz661 (@Inv.inv Real Real.instInv (Real.sqrt qz52)) Bool.false 1457823 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz48 (BSN.t_div_two_pi_nonneg qz47 430527 1000 qz50)) Ns168p413) rfl) (@Ns168p414 70368744177664 2431738146224611 19791209299968000000 (BSN.correction_mk qz49 (BSN.cos_two_pi_p_ne_zero_mk qz47 430527 1000 8 qz50 rfl rfl (@BSN.floor_sqrt_eq_dec qz47 430527 1000 8 qz50 rfl rfl rfl))) (@Ns168p415 4194304 689039 8388608 38314201 2359296000000 33365292087543 70368744177664 2431738146224611 19791209299968000000 Ns168p432 (Ns168p446 rfl) rfl)) 

noncomputable def Ns168p448 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz47) (hardyZApproximantRS₀ qz47) Bool.true 121386930367574799209 295147905179352825856 241922172363345289857067 Ns168p339 (@Eq.refl Real (hardyZApproximantRS₀ qz47)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz47) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz47) qz47 8) (@HMul.hMul Real Real Real qz5 qz658 (Zeta.RiemannSiegel.correction qz49))) Bool.true 121386930367574799209 295147905179352825856 241922172363345289857067 Ns168p339 (BSN.hardyZApproximantRS₀_eq qz47 8 (@BSN.floor_sqrt_eq_dec qz47 430527 1000 8 qz50 rfl rfl rfl)) (@Ns168p341 121386930367574799209 295147905179352825856 241922172363345289857067 Ns168p339 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz47) qz47 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz47) qz47 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz47) qz47 8)) Bool.true 4135145 16777216 11865 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz47) qz47 8) (Ns168p407 (Ns168p406 rfl rfl rfl rfl) rfl rfl)) (Ns168p447 rfl) rfl rfl)) 

theorem RS169to186.d45 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz47) Bool.true 121386930367574799209 295147905179352825856 241922172363345289857067 Ns168p339 := Ns168p448 

noncomputable def Ns168p449 := nat_lit 83010348331692982272000000 

noncomputable def Ns168p450 := nat_lit 9546621246323464531706118144 

noncomputable abbrev qz904 := (Enclosure.sfrac Bool.false 432013 1000)

noncomputable abbrev qz665 := qz904

noncomputable abbrev qz408 := qz665

noncomputable abbrev qz60 := qz408

noncomputable abbrev qz905 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 432013 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz666 := qz905

noncomputable abbrev qz409 := qz666

noncomputable abbrev qz61 := qz409

noncomputable abbrev qz906 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 432013 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz667 := qz906

noncomputable abbrev qz410 := qz667

noncomputable abbrev qz62 := qz410

noncomputable abbrev qz668 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz61 qz9))

noncomputable def Ns168p451 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz60) qz60 8) (@HMul.hMul Real Real Real qz5 qz668 (Zeta.RiemannSiegel.correction qz62)) 26945247 67108864 47621 33554432 94757157070294288605 590295810358705651712 2370030593231387363011 Ns168p449 Ns168p450 

noncomputable def Ns168p452 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.sin BSN.quadSignPos 7 8 432013 1000 127 134217728 67108864 2251799813685248 Bool.false 93607916673 1686 279097919 60 47453128 8 

noncomputable def Ns168p453 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 432013 1000 48 91 134217728 67108864 2251799813685248 Bool.false 93607916673 1686 

noncomputable def Ns168p454 := Ns168p453 240485871 61 54794152 8 261175631 61 50729528 8 Bool.true 52349793 63407 Bool.true 165327636 Bool.true 37938216 7074237752028440 1 Bool.false 44634519 Bool.false Bool.false 37435034 Bool.false Bool.true 19978718 

noncomputable def Ns168p455 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 432013 1000 62 1 134217728 67108864 2251799813685248 Bool.false 93607916673 1686 

noncomputable def Ns168p456 := Ns168p455 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 7368887 37237 Bool.false 153923500 Bool.false 75761746 7074237752028440 1 Bool.false 55215625 Bool.true Bool.false 71802090 Bool.true Bool.true 52349793 

noncomputable def Ns168p457 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 432013 1000 253 141 134217728 67108864 2251799813685248 Bool.false 93607916673 1686 

noncomputable def Ns168p458 := Ns168p457 93032624 60 94906264 8 147453232 60 77490640 16 Bool.false 134217720 1748 Bool.false 76949005 Bool.false 179354864 7074237752028440 1 Bool.false 72802350 Bool.true Bool.false 130544322 Bool.true Bool.false 7368887 

noncomputable def Ns168p459 := nat_lit 735102011831247932636008804772703581746081800652183823701 

noncomputable def Ns168p460 := nat_lit 1054010444649294990687212947942455282147808461717504000 

noncomputable def Ns168p461 := nat_lit 7223152589393251747230511020640000 

noncomputable def Ns168p462 := nat_lit 18722986621520742834818181917854489920 

noncomputable abbrev qz411 := (@Eq.refl Real qz665)

noncomputable abbrev qz63 := qz411

noncomputable def Ns168p463 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz60 432013 1000 746541928676 16000000 864026 4000 2000 Ns168p461 Ns168p462 qz63 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns168p464 := nat_lit 235232643785999338443522817527265146158746176208698823584320 

noncomputable abbrev qz669 := (Real.log (Enclosure.sfrac Bool.false 746541928676 16000000))

noncomputable abbrev qz64 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 432013 4000) qz669) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 864026))))))

noncomputable abbrev qz670 := (Enclosure.sfrac Bool.false 432013 2000)

noncomputable abbrev qz412 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz64 qz670) (@HMul.hMul Real Real Real qz5 qz670 (Real.log Real.pi)))

noncomputable def Ns168p465 := @Enclosure.Real.IsNear.addLit_ft_p qz412 (Enclosure.sfrac Bool.true Ns168p461 Ns168p462) 12563848848578742158821 18014398509481984000 15419951477978879 1228800000000000000000 Ns168p461 Ns168p462 0 1 Ns168p464 

noncomputable def Ns168p466 := nat_lit 843145623695827400827384889344000 

noncomputable abbrev qz413 := (@HSub.hSub Real Real Real qz12 qz64 qz670)

noncomputable abbrev qz414 := (@HMul.hMul Real Real Real qz5 qz670 (Real.log Real.pi))

noncomputable def Ns168p467 := @Enclosure.Real.IsNear.subLit_ff_p qz413 qz414 17018252871466369517029 18014398509481984000 14667103888417 2400000000000000000 16593948091893 67108864000 432013 67108864000 Ns168p466 12563848848578742158821 18014398509481984000 

noncomputable def Ns168p468 := nat_lit 1361460229717309561362320 

noncomputable abbrev qz415 := qz670

noncomputable def Ns168p469 := @Enclosure.Real.IsNear.subLit_ff_p qz64 qz415 836379201724191587757 720575940379279360 14667103888417 2400000000000000000 432013 2000 0 1 Ns168p468 17018252871466369517029 18014398509481984000 14667103888417 2400000000000000000 

noncomputable def Ns168p470 := nat_lit 1883358530612751070110484526568308736 

noncomputable def Ns168p471 := nat_lit 25993400139626845516595200 

noncomputable def Ns168p472 := nat_lit 6428820227420398731821418760503795880177689508097442532777626697955731514051365446210381272170168320 

noncomputable def Ns168p473 := nat_lit 66773915478824989026870179454146948437005528697231589529999543926239059938658837621627387753529344 

noncomputable def Ns168p474 := nat_lit 625150915148443091101638439723793726380146354993168991934720690601532812613587278509067796480 

noncomputable def Ns168p475 := BSN.log_dyadic_bound 222253928676 1270829928676 5 4 Ns168p472 67108864 18000000 Ns168p473 Ns168p474 23716985 1493083857352 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 222253928676) (BSN.artanhQ 1270829928676) 0 4 Ns168p473 Ns168p472 Ns168p474 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns168p476 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 432013 4000) qz669 432013 4000 0 1 48416480682095225 4503599627370496 100000027 1800000000000000 836661962756560177517 720575940379279360 43201311664351 7200000000000000000 (Enclosure.Real.IsNear.const Bool.false 432013 4000) (BSN.isNear_log_sfrac 746541928676 16000000 48416480682095225 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 746541928676) qz353)) Bool.false Ns168p471 Ns168p89 1000000270000000 18000000000000000000000 48416480682095225 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 746541928676 16000000 15 1493083857352 1048576000000 23716985 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns168p475 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p477 := BSN.arctan_dyadic_bound_f 1000 864026 1 0 8388608 2250000 0 1 1 0 1 1 9708 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 864026) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 864026) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz416 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 864026)))

noncomputable def Ns168p478 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz416 884279719003555 562949953421312 1 2000000000000000 9708 8388608 1 2250000 7412410806923159404544 883628226151843 562949953421312 8000000009 18000000000000000 qz16 (Ns168p477 rfl) rfl rfl 

noncomputable def Ns168p479 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 432013 4000) qz669) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz416)) 836661962756560177517 720575940379279360 43201311664351 7200000000000000000 883628226151843 2251799813685248 8000000009 72000000000000000 Ns168p470 836379201724191587757 720575940379279360 14667103888417 2400000000000000000 (Ns168p476 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz416) 1 4 0 1 883628226151843 562949953421312 8000000009 18000000000000000 883628226151843 2251799813685248 8000000009 72000000000000000 qz356 Ns168p478 rfl) 

noncomputable def Ns168p480 := @Ns168p465 Ns168p459 Ns168p460 15419951477978879 1228800000000000000000 (@Ns168p467 15419951477978879 1228800000000000000000 (Ns168p469 (Ns168p479 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 432013 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz415 (Real.log Real.pi) 432013 2000 0 1 38410761 33554432 1 33554432 16593948091893 67108864000 432013 67108864000 (Enclosure.Real.IsNear.const Bool.false 432013 2000) RS169to186.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns168p461 Ns168p462) 

noncomputable def Ns168p481 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz60) Bool.false Ns168p459 Ns168p460 15419951477978879 1228800000000000000000 731311849 1048576 211 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz60) (@HAdd.hAdd Real Real Real qz357 qz412 (Enclosure.sfrac Bool.true Ns168p461 Ns168p462)) Bool.false Ns168p459 Ns168p460 15419951477978879 1228800000000000000000 Ns168p463 (Ns168p480 rfl rfl)) 

noncomputable def Ns168p482 := nat_lit 856609684713672718290966002428258261711248226269446313054484333265365865751918157175993360158309895518090784404344856268949062135320576 

noncomputable def Ns168p483 := nat_lit 609867737989600325968656029101024381961421351745654320485376320868900099951533100486934346983344558183459719103838307056594456576 

noncomputable def Ns168p484 := nat_lit 4277729473528789873819103015188632517963438915175179041789344318218184045213490723002307315636854946262574690281027029901068583242305536 

noncomputable def Ns168p485 := BSN.sin_dyadic_bound_f 53963855618 34359738368 4 3 16777216 4504395 Ns168p482 Ns168p103 Ns168p483 Ns168p484 Ns168p106 Ns168p483 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53963855618) qz358 0 3 Ns168p482 Ns168p103 Ns168p483 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53963855618) qz359 0 3 Ns168p484 Ns168p106 Ns168p483 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz671 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable def Ns168p486 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz60) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 731311849) qz671) Bool.false 731311849 1048576 211 16777216 Bool.false 16777215 16777216 1 2250000 (Ns168p481 rfl) (Enclosure.sfrac_false_div 731311849 1048576) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 731311849) qz671) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 237335546930789653413888) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 110 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q3 731311849 1048576 226375608064910080 72057594037927936 110 237335546930789653413888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 237335546930789653413888 151115727451828646838272 53963855618 34359738368 4504395 4500000 (Ns168p485 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p487 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz60) Bool.false Ns168p459 Ns168p460 15419951477978879 1228800000000000000000 93607916673 134217728 1686 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz60) (@HAdd.hAdd Real Real Real qz357 qz412 (Enclosure.sfrac Bool.true Ns168p461 Ns168p462)) Bool.false Ns168p459 Ns168p460 15419951477978879 1228800000000000000000 Ns168p463 (Ns168p480 rfl rfl)) 

noncomputable def Ns168p488 := Ns168p458 37237 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 253 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 72802350 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 141 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 130544322 134217728) qz63 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 1) Bool.false 16777215 16777216 30720451 2359296000000 134217720 134217728 1748 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz60)) Bool.false 16777215 16777216 30720451 2359296000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz60) qz60) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz60)) Bool.false 16777215 16777216 491527216 37748736000000 16777215 16777216 30720451 2359296000000 (Ns168p486 rfl rfl) rfl)) rfl) (Ns168p487 rfl) RS169to186.d7 

noncomputable def Ns168p489 := nat_lit 34407163253440096793762214150279199762359438312098673465812677230625 

noncomputable def Ns168p490 := nat_lit 1229204291920025254746180276307190870617858933257386030625390625 

noncomputable def Ns168p491 := nat_lit 90112008856822859180869543244569597259055623807699823309269332590625 

noncomputable def Ns168p492 := BSN.sin_dyadic_bound_f 76949005 134217728 3 2 134217728 67108864 Ns168p489 Ns168p112 Ns168p490 Ns168p491 Ns168p115 Ns168p490 72802350 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 76949005) qz361 0 2 Ns168p489 Ns168p112 Ns168p490 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 76949005) qz362 0 2 Ns168p491 Ns168p115 Ns168p490 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p493 := nat_lit 5660940117669409105283903432465107984148367128612559439684693637016745150531507419949226607861735878557696 

noncomputable def Ns168p494 := nat_lit 1108046299894857793457349810212063439943252144933310466886814835872915440990307722629310848062980096 

noncomputable def Ns168p495 := nat_lit 28286265180781605172617012711395187249440459597923876979176804237248332685105149598823340004648905296838656 

noncomputable def Ns168p496 := BSN.sin_dyadic_bound_f 179354864 134217728 4 3 134217728 67108864 Ns168p493 Ns168p144 Ns168p494 Ns168p495 Ns168p147 Ns168p494 130544322 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 179354864) qz361 0 3 Ns168p493 Ns168p144 Ns168p494 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 179354864) qz362 0 3 Ns168p495 Ns168p147 Ns168p494 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p497 := nat_lit 1181058726930596712804941186710870156027453253573018485110772092578130071060976262659280998400000000000000 

noncomputable def Ns168p498 := nat_lit 176872030059268342730104311533399132348182324084142105205162963633056640625000000000000000000000000 

noncomputable def Ns168p499 := nat_lit 7160175628791333940926774032830460964453907112356024827989484950116999754774628698799638056960000000000000 

noncomputable def Ns168p500 := BSN.cos_dyadic_bound_f 153923500 134217728 4 3 134217728 67108864 Ns168p497 Ns168p118 Ns168p498 Ns168p499 Ns168p121 Ns168p498 55215625 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 153923500) qz363 0 3 Ns168p497 Ns168p118 Ns168p498 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 153923500) qz364 0 3 Ns168p499 Ns168p121 Ns168p498 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p501 := nat_lit 32332240292096200520510430838310980675543817063310653896264263942400 

noncomputable def Ns168p502 := nat_lit 1085424946078620040240036903740281536708400325480034534367969536 

noncomputable def Ns168p503 := nat_lit 84677919600815445502224073088208417503936278708143792529541238374656 

noncomputable def Ns168p504 := BSN.sin_dyadic_bound_f 75761746 134217728 3 2 134217728 67108864 Ns168p501 Ns168p112 Ns168p502 Ns168p503 Ns168p115 Ns168p502 71802090 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 75761746) qz361 0 2 Ns168p501 Ns168p112 Ns168p502 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 75761746) qz362 0 2 Ns168p503 Ns168p115 Ns168p502 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p505 := Ns168p456 63407 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 62 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 55215625 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 1 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 71802090 134217728) qz63 rfl rfl (Ns168p488 RS169to186.d9 RS169to186.d11 RS169to186.d13 RS169to186.d17 (Ns168p492 rfl rfl) (Ns168p496 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns168p487 rfl) RS169to186.d19 RS169to186.d21 RS169to186.d23 RS169to186.d25 RS169to186.d17 (Ns168p500 rfl rfl) (Ns168p504 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns168p506 := nat_lit 1572466690338869277240758306222100482360874015392078463539853230210363728811695178991918906546236399026176 

noncomputable def Ns168p507 := nat_lit 417009040562882072981582161348952907451018339015005328594344002462816697051335139856956624098820096 

noncomputable def Ns168p508 := nat_lit 9530925951300668954428493129078712197564988408824356639181304593314948076425606490705388687844217632849920 

noncomputable def Ns168p509 := BSN.cos_dyadic_bound_f 165327636 134217728 4 3 134217728 67108864 Ns168p506 Ns168p118 Ns168p507 Ns168p508 Ns168p121 Ns168p507 44634519 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 165327636) qz363 0 3 Ns168p506 Ns168p118 Ns168p507 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 165327636) qz364 0 3 Ns168p508 Ns168p121 Ns168p507 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p510 := nat_lit 2071608190337668175562684174336 

noncomputable def Ns168p511 := BSN.sin_dyadic_bound_f 37938216 134217728 2 1 134217728 67108864 Ns168p510 Ns168p394 Ns168p510 Ns168p510 Ns168p395 Ns168p510 37435034 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 37938216) qz361 0 1 Ns168p510 Ns168p394 Ns168p510 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 37938216) qz362 0 1 Ns168p510 Ns168p395 Ns168p510 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p512 := Ns168p454 85471 BSN.abs_quadSignPos (BSN.cos_quad_nat0 48 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 44634519 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 91 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 37435034 134217728) qz63 rfl rfl (Ns168p505 rfl rfl) (Ns168p487 rfl) RS169to186.d27 RS169to186.d29 RS169to186.d31 RS169to186.d33 RS169to186.d17 (Ns168p509 rfl rfl) (Ns168p511 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns168p513 := nat_lit 7247147021777612387869140218122176801545083336653461331150759169436452535873995669971583888176565755038881 

noncomputable def Ns168p514 := nat_lit 2322786562206488073878976757786338447739402519980198410471959511837765690086226022081837720915922081 

noncomputable def Ns168p515 := nat_lit 36205536781389765636724318948119162905556426938036595064697412114756674764706227578321884114831048387579041 

noncomputable def Ns168p516 := BSN.sin_dyadic_bound_f 190765913 134217728 4 3 134217728 67108864 Ns168p513 Ns168p144 Ns168p514 Ns168p515 Ns168p147 Ns168p514 132721029 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 190765913) qz361 0 3 Ns168p513 Ns168p144 Ns168p514 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 190765913) qz362 0 3 Ns168p515 Ns168p147 Ns168p514 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p517 := Ns168p452 Bool.true 19978718 85471 Bool.true 190765913 7074237752028440 1 Bool.false 132721029 Bool.false Bool.false 26945247 95242 BSN.abs_quadSignPos qz365 (BSN.sfrac_eq_quadSignPos_mul Bool.false 132721029 134217728) qz63 rfl (Ns168p512 rfl) (Ns168p487 rfl) RS169to186.d35 RS169to186.d37 RS169to186.d17 (Ns168p516 rfl rfl) rfl 

noncomputable def Ns168p518 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 8) 26945247 134217728 95242 134217728 26945247 134217728 95242 134217728 7233059665477632 26945247 67108864 47621 33554432 (Ns168p517 rfl rfl rfl rfl) 

noncomputable def Ns168p519 := @Enclosure.Real.IsNear.mulLit_ff qz668 (Zeta.RiemannSiegel.correction qz62) 2913135 8388608 1 8388608 32527554359923 70368744177664 405998279156813 4947802324992000000 94757157070294288605 590295810358705651712 

noncomputable abbrev qz672 := (@HPow.hPow Real Real Real qz7 qz61 qz9)

noncomputable def Ns168p520 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz672 1 1 0 1 2913135 8388608 1 8388608 2913135 8388608 1 8388608 

noncomputable def Ns168p521 := @Enclosure.Real.IsNear.sqrt_image qz61 1153551176301 16777216000 432013 16777216000 69558195 69558222 8388608 (@Enclosure.Real.IsNear.of_eq qz61 (@HMul.hMul Real Real Real qz5 qz60 qz3) Bool.false 1153551176301 16777216000 432013 16777216000 (BSN.t_div_two_pi_mk qz60 432013 1000 qz63) (@Enclosure.Real.IsNear.mulLit_ff qz60 qz3 432013 1000 0 1 2670177 16777216 1 16777216 1153551176301 16777216000 432013 16777216000 (Enclosure.Real.IsNear.const Bool.false 432013 1000) RS169to186.d40 rfl)) 

noncomputable abbrev qz907 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 432013 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz673 := qz907

noncomputable abbrev qz417 := qz673

noncomputable abbrev qz65 := qz417

noncomputable def Ns168p522 := @Enclosure.Real.IsNear.sqrt_image qz65 139116417 16777216 27 16777216 24155670 24155676 8388608 (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 139116417 16777216 27 16777216 139116417 16777216 27 16777216 (Ns168p521 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns168p523 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz65) 24155673 8388608 3 8388608 2913134 2913136 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz65) Bool.false 48311346 16777216 6 16777216 24155673 8388608 3 8388608 (Ns168p522 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns168p524 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz65)) Bool.false 5826270 16777216 2 16777216 2913135 8388608 1 8388608 (Ns168p523 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz66 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz410))

noncomputable abbrev qz674 := (@HMul.hMul Real Real Real qz890 qz906 qz906)

noncomputable abbrev qz418 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz674 qz667) qz641)

noncomputable abbrev qz67 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz418))

noncomputable def Ns168p525 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz62) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz66) qz67) Bool.false 32527554359923 

noncomputable def Ns168p526 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz66) qz67 64342579 16777216 2625 

noncomputable abbrev qz675 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz66))

noncomputable def Ns168p527 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz66) (@Neg.neg Real Real.instNeg qz675) Bool.true 64342579 16777216 2625 16777216 (BSN.inv_eq_neg_inv_neg qz66) 

noncomputable def Ns168p528 := @Enclosure.Real.IsNear.recentre' qz675 Bool.false 64342579 16777216 2625 16777216 64342579 16777216 

noncomputable def Ns168p529 := @Enclosure.Real.IsNear.recentre' qz66 Bool.true 2187315 8388608 401527216 37748736000000 2187315 8388608 25095451 2359296000000 

noncomputable abbrev qz68 := (@HMul.hMul Real Real Real qz342 qz340 qz410)

noncomputable def Ns168p530 := @Enclosure.Real.IsNear.cos_image qz68 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15389685) qz360) Bool.false 15389685 8388608 171 16777216 Bool.true 2187315 8388608 1 

noncomputable def Ns168p531 := nat_lit 728624036086268645386111997 

noncomputable def Ns168p532 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz62 884279719003555 140737488355328 1 500000000000000 4898689 16777216 27 16777216 4331811332405805839395 2361183241434822606848 Ns168p531 

noncomputable def Ns168p533 := @Enclosure.Real.IsNear.subLit_ff_p qz65 qz1 139116417 16777216 27 16777216 8 1 0 1 4898689 4898689 16777216 27 

noncomputable def Ns168p534 := @Ns168p533 16777216 (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 139116417 16777216 27 16777216 139116417 16777216 27 16777216 (Ns168p521 rfl rfl rfl rfl rfl rfl) rfl) qz371 

noncomputable def Ns168p535 := @Enclosure.Real.IsNear.recentre' qz68 Bool.false 4331811332405805839395 2361183241434822606848 Ns168p531 Ns168p163 15389685 8388608 171 16777216 (@Ns168p532 Ns168p163 RS169to186.d39 (Ns168p534 rfl rfl) rfl) 

noncomputable def Ns168p536 := nat_lit 27636638551580794482502360195446183494504845871816573525495315603283632869975212763293140625 

noncomputable def Ns168p537 := nat_lit 176504900653868918749139632482035140240451201080885199127721839275110685558515869140625 

noncomputable def Ns168p538 := nat_lit 166912740047539060981602108156122094345026267672293788029925315394613985217164571230774740625 

noncomputable def Ns168p539 := BSN.cos_dyadic_bound_t 15389685 8388608 4 3 8388608 2250000 Ns168p536 Ns168p187 Ns168p537 Ns168p538 Ns168p190 Ns168p537 2187315 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 15389685) (BSN.cosEvenQ 8388608) 0 3 Ns168p536 Ns168p187 Ns168p537 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 15389685) (BSN.cosOddQ 8388608) 0 3 Ns168p538 Ns168p190 Ns168p537 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p540 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz66) 2187315 8388608 25095451 2359296000000 32169977 32172602 8388608 (@Enclosure.Real.IsNear.neg qz66 Bool.true 2187315 8388608 25095451 2359296000000 (Ns168p529 (@Ns168p530 2250000 (Ns168p535 rfl) (Enclosure.sfrac_false_div 15389685 8388608) (Ns168p539 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns168p541 := Ns168p527 (@Enclosure.Real.IsNear.neg qz675 Bool.false 64342579 16777216 2625 16777216 (@Ns168p528 2625 16777216 (Ns168p540 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p542 := @Enclosure.Real.IsNear.recentre' qz67 Bool.true 1011074 8388608 

noncomputable abbrev qz69 := (@HMul.hMul Real Real Real qz342 qz340 qz418)

noncomputable def Ns168p543 := @Enclosure.Real.IsNear.cos_image qz69 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 28380665)) qz370) Bool.true 28380665 16777216 

noncomputable def Ns168p544 := nat_lit 67011951202902781840503070045 

noncomputable def Ns168p545 := nat_lit 19362907610015625198958955400928937 

noncomputable def Ns168p546 := @Enclosure.Real.IsNear.recentre' qz69 Bool.true Ns168p544 Ns168p178 Ns168p545 

noncomputable abbrev qz70 := qz418

noncomputable def Ns168p547 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz70 884279719003555 140737488355328 1 500000000000000 75781395595519 

noncomputable abbrev qz419 := (@HSub.hSub Real Real Real qz633 qz674 qz667)

noncomputable abbrev qz71 := qz419

noncomputable def Ns168p548 := @Enclosure.Real.IsNear.subLit_tf qz71 qz25 58189209551103 281474976710656 717514767 281474976710656 1 16 

noncomputable abbrev qz420 := qz674

noncomputable abbrev qz72 := qz420

noncomputable def Ns168p549 := @Enclosure.Real.IsNear.subLit_ff_n qz72 qz62 23997153918721 281474976710656 264529935 281474976710656 4898689 16777216 27 16777216 

noncomputable def Ns168p550 := @Enclosure.Real.IsNear.mulLit_ff qz62 qz62 4898689 16777216 27 16777216 4898689 16777216 27 16777216 23997153918721 281474976710656 

noncomputable def Ns168p551 := nat_lit 81674841042635096584640945030833930612804222202541110346776517851565589652172021627792609390625 

noncomputable def Ns168p552 := nat_lit 273067999479097999233603381328259034704452466532131374023176605585046097407668301025390625 

noncomputable def Ns168p553 := nat_lit 493890383086557501162644623338251376537889786031522999021359933515081311474586500613555834990625 

noncomputable def Ns168p554 := BSN.cos_dyadic_bound_t 28380665 16777216 4 3 8388608 2250000 Ns168p551 Ns168p169 Ns168p552 Ns168p553 Ns168p172 Ns168p552 1011074 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 28380665) qz642 0 3 Ns168p551 Ns168p169 Ns168p552 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 28380665) (BSN.cosOddQ 16777216) 0 3 Ns168p553 Ns168p172 Ns168p552 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p555 := @Ns168p542 622027216 37748736000000 505537 4194304 38876701 2359296000000 (@Ns168p543 269 16777216 Bool.true 1011074 8388608 1 2250000 (@Ns168p546 Ns168p181 28380665 16777216 269 16777216 (@Ns168p547 281474976710656 717514767 281474976710656 Ns168p544 Ns168p178 Ns168p545 Ns168p181 RS169to186.d39 (@Ns168p548 0 1 1212502329528304 75781395595519 281474976710656 717514767 281474976710656 (@Ns168p549 976252937508118069248 58189209551103 281474976710656 717514767 281474976710656 (@Ns168p550 264529935 281474976710656 (Ns168p534 rfl rfl) (Ns168p534 rfl rfl) rfl) (Ns168p534 rfl rfl) rfl rfl) qz375 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 28380665 16777216) (BSN.cos_neg_of_bound 28380665 16777216 Bool.true 1011074 8388608 1 2250000 (Ns168p554 rfl rfl)) rfl rfl) 

noncomputable def Ns168p556 := @Ns168p519 2370030593231387363011 Ns168p449 (Ns168p520 qz27 (@Enclosure.Real.IsNear.of_eq qz672 (@Inv.inv Real Real.instInv (Real.sqrt qz65)) Bool.false 2913135 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz61 (BSN.t_div_two_pi_nonneg qz60 432013 1000 qz63)) Ns168p524) rfl) (@Ns168p525 70368744177664 405998279156813 4947802324992000000 (BSN.correction_mk qz62 (BSN.cos_two_pi_p_ne_zero_mk qz60 432013 1000 8 qz63 rfl rfl (@BSN.floor_sqrt_eq_dec qz60 432013 1000 8 qz63 rfl rfl rfl))) (@Ns168p526 16777216 505537 4194304 38876701 2359296000000 32527554359923 70368744177664 405998279156813 4947802324992000000 Ns168p541 (Ns168p555 rfl) rfl)) 

noncomputable def Ns168p557 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz60) (hardyZApproximantRS₀ qz60) Bool.false 142255742048076756771 590295810358705651712 120179677852453403363011 Ns168p449 (@Eq.refl Real (hardyZApproximantRS₀ qz60)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz60) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz60) qz60 8) (@HMul.hMul Real Real Real qz5 qz668 (Zeta.RiemannSiegel.correction qz62))) Bool.false 142255742048076756771 590295810358705651712 120179677852453403363011 Ns168p449 (BSN.hardyZApproximantRS₀_eq qz60 8 (@BSN.floor_sqrt_eq_dec qz60 432013 1000 8 qz63 rfl rfl rfl)) (@Ns168p451 142255742048076756771 590295810358705651712 120179677852453403363011 Ns168p449 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz60) qz60 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 8)) Bool.false 26945247 67108864 47621 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz60) qz60 8) (Ns168p518 (Ns168p517 rfl rfl rfl rfl) rfl rfl)) (Ns168p556 rfl) rfl rfl)) 

theorem RS169to186.d46 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz60) Bool.false 142255742048076756771 590295810358705651712 120179677852453403363011 Ns168p449 := Ns168p557 

noncomputable def Ns168p558 := nat_lit 2594073385365405696000000 

noncomputable def Ns168p559 := nat_lit 10168385397004682722728214528 

noncomputable abbrev qz908 := (Enclosure.sfrac Bool.false 433498 1000)

noncomputable abbrev qz676 := qz908

noncomputable abbrev qz421 := qz676

noncomputable abbrev qz73 := qz421

noncomputable abbrev qz909 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 433498 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz677 := qz909

noncomputable abbrev qz422 := qz677

noncomputable abbrev qz74 := qz422

noncomputable abbrev qz910 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 433498 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz678 := qz910

noncomputable abbrev qz423 := qz678

noncomputable abbrev qz75 := qz423

noncomputable abbrev qz679 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz74 qz9))

noncomputable def Ns168p560 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz73) qz73 8) (@HMul.hMul Real Real Real qz5 qz679 (Zeta.RiemannSiegel.correction qz75)) 15912377 8388608 5973 4194304 92432012683922429163 590295810358705651712 56363619438276489061 Ns168p558 Ns168p559 

noncomputable def Ns168p561 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz73) qz73 Real.sin BSN.quadSignPos 7 8 433498 1000 127 134217728 67108864 2251799813685248 Bool.false 94029693123 1691 279097919 60 47453128 8 

noncomputable def Ns168p562 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz73) qz73 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 433498 1000 48 91 134217728 67108864 2251799813685248 Bool.false 94029693123 1691 

noncomputable def Ns168p563 := Ns168p562 240485871 61 54794152 8 261175631 61 50729528 8 Bool.true 215372420 63625 Bool.true 100672705 Bool.true 4007578 7074237752028440 1 Bool.false 98199203 Bool.false Bool.false 4006982 Bool.false Bool.true 173768271 

noncomputable def Ns168p564 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz73) qz73 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 433498 1000 63 1 134217728 67108864 2251799813685248 Bool.false 94029693123 1691 

noncomputable def Ns168p565 := Ns168p564 186065264 60 67108856 8 216015088 60 60023992 8 Bool.true 198410143 37366 Bool.false 88564319 Bool.false 176755791 7074237752028440 1 Bool.false 82275838 Bool.false Bool.false 129915977 Bool.true Bool.true 215372420 

noncomputable def Ns168p566 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz73) qz73 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 433498 1000 254 142 134217728 67108864 2251799813685248 Bool.false 94029693123 1691 

noncomputable def Ns168p567 := Ns168p566 93032624 60 94906264 8 147453232 60 77490640 16 Bool.true 134217696 1756 Bool.false 149743294 Bool.false 171334550 7074237752028440 1 Bool.false 58998322 Bool.true Bool.false 38926688 Bool.true Bool.true 198410143 

noncomputable def Ns168p568 := nat_lit 5888867240130665876091705488074480214466657935927824529 

noncomputable def Ns168p569 := nat_lit 8405753068084878154104417908623067506380455804928000 

noncomputable def Ns168p570 := nat_lit 7348153022590118388407814384640000 

noncomputable def Ns168p571 := nat_lit 19112469699586832016631019334052024320 

noncomputable abbrev qz424 := (@Eq.refl Real qz676)

noncomputable abbrev qz76 := qz424

noncomputable def Ns168p572 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz73 433498 1000 751683064016 16000000 866996 4000 2000 Ns168p570 Ns168p571 qz76 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns168p573 := nat_lit 120604001077876037142358128395765354792277154527801846353920 

noncomputable abbrev qz680 := (Real.log (Enclosure.sfrac Bool.false 751683064016 16000000))

noncomputable abbrev qz77 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 433498 4000) qz680) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 866996))))))

noncomputable abbrev qz681 := (Enclosure.sfrac Bool.false 433498 2000)

noncomputable abbrev qz425 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz77 qz681) (@HMul.hMul Real Real Real qz5 qz681 (Real.log Real.pi)))

noncomputable def Ns168p574 := @Enclosure.Real.IsNear.addLit_ft_p qz425 (Enclosure.sfrac Bool.true Ns168p570 Ns168p571) 6310229350776244823781 9007199254740992000 7736243323465567 614400000000000000000 Ns168p570 Ns168p571 0 1 Ns168p573 

noncomputable def Ns168p575 := nat_lit 42347232331005130830982309478400 

noncomputable abbrev qz426 := (@HSub.hSub Real Real Real qz12 qz77 qz681)

noncomputable abbrev qz427 := (@HMul.hMul Real Real Real qz5 qz681 (Real.log Real.pi))

noncomputable def Ns168p576 := @Enclosure.Real.IsNear.subLit_ff_p qz426 qz427 1709017427750446489953 1801439850948198400 7358301950891 1200000000000000000 8325494035989 33554432000 216749 33554432000 Ns168p575 6310229350776244823781 9007199254740992000 

noncomputable def Ns168p577 := nat_lit 17090174277504464899530000 

noncomputable abbrev qz428 := qz681

noncomputable def Ns168p578 := @Enclosure.Real.IsNear.subLit_ff_p qz77 qz428 10497388570018087724773 9007199254740992000 7358301950891 1200000000000000000 433498 2000 0 1 Ns168p577 1709017427750446489953 1801439850948198400 7358301950891 1200000000000000000 

noncomputable def Ns168p579 := nat_lit 23638017626148381868089191444674248704 

noncomputable def Ns168p580 := nat_lit 26009993850612275713409024 

noncomputable def Ns168p581 := nat_lit 6639852231893252169441506311756608742424188171530290778012232517317450279473291980283300450895134720 

noncomputable def Ns168p582 := nat_lit 71664548328288182408766743900503913903484309695980706133441805817131364317234602649749936326836224 

noncomputable def Ns168p583 := nat_lit 750650133360545893113038163198401493774595156593225921255067004836254760546683220645726126080 

noncomputable def Ns168p584 := BSN.log_dyadic_bound 227395064016 1275971064016 5 4 Ns168p581 67108864 18000000 Ns168p582 Ns168p583 24177553 1503366128032 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 227395064016) (BSN.artanhQ 1275971064016) 0 4 Ns168p582 Ns168p581 Ns168p583 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns168p585 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 433498 4000) qz680 433498 4000 0 1 48447388877369977 4503599627370496 100000027 1800000000000000 10500923091781065144773 9007199254740992000 21674905852223 3600000000000000000 (Enclosure.Real.IsNear.const Bool.false 433498 4000) (BSN.isNear_log_sfrac 751683064016 16000000 48447388877369977 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 751683064016) qz353)) Bool.false Ns168p580 Ns168p89 1000000270000000 18000000000000000000000 48447388877369977 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 751683064016 16000000 15 1503366128032 1048576000000 24177553 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns168p584 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p586 := BSN.arctan_dyadic_bound_f 1000 866996 1 0 8388608 2250000 0 1 1 0 1 1 9675 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 866996) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 866996) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz429 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 866996)))

noncomputable def Ns168p587 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz429 884279719003555 562949953421312 1 2000000000000000 9675 8388608 1 2250000 7412429384271622307840 883630440744355 562949953421312 8000000009 18000000000000000 qz16 (Ns168p586 rfl) rfl rfl 

noncomputable def Ns168p588 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 433498 4000) qz680) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz429)) 10500923091781065144773 9007199254740992000 21674905852223 3600000000000000000 883630440744355 2251799813685248 8000000009 72000000000000000 Ns168p579 10497388570018087724773 9007199254740992000 7358301950891 1200000000000000000 (Ns168p585 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz429) 1 4 0 1 883630440744355 562949953421312 8000000009 18000000000000000 883630440744355 2251799813685248 8000000009 72000000000000000 qz356 Ns168p587 rfl) 

noncomputable def Ns168p589 := @Ns168p574 Ns168p568 Ns168p569 7736243323465567 614400000000000000000 (@Ns168p576 7736243323465567 614400000000000000000 (Ns168p578 (Ns168p588 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 433498 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz428 (Real.log Real.pi) 433498 2000 0 1 38410761 33554432 1 33554432 8325494035989 33554432000 216749 33554432000 (Enclosure.Real.IsNear.const Bool.false 433498 2000) RS169to186.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns168p570 Ns168p571) 

noncomputable def Ns168p590 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz73) Bool.false Ns168p568 Ns168p569 7736243323465567 614400000000000000000 1469213955 2097152 53 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz73) (@HAdd.hAdd Real Real Real qz357 qz425 (Enclosure.sfrac Bool.true Ns168p570 Ns168p571)) Bool.false Ns168p568 Ns168p569 7736243323465567 614400000000000000000 Ns168p572 (Ns168p589 rfl rfl)) 

noncomputable abbrev qz682 := (BSN.cosEvenQ 34359738368)

noncomputable abbrev qz683 := (BSN.cosOddQ 34359738368)

noncomputable def Ns168p591 := BSN.cos_dyadic_bound_f 22173852 34359738368 1 0 16777216 4504395 0 1 1 0 1 1 16777212 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 22173852) qz682 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 22173852) qz683 0 0 rfl) rfl rfl 

noncomputable def Ns168p592 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz73) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1469213955) (@Nat.cast Real Real.instNatCast 2097152)) Bool.false 1469213955 2097152 53 4194304 Bool.true 16777212 16777216 1 2250000 (Ns168p590 rfl) (Enclosure.sfrac_false_div 1469213955 2097152) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1469213955) (@Nat.cast Real Real.instNatCast 2097152)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 195043271178085990400) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 16777212 16777216 111 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 1469213955 2097152 226375608064910080 72057594037927936 111 195043271178085990400 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777212 16777216 195043271178085990400 302231454903657293676544 22173852 34359738368 4504395 4500000 (Ns168p591 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p593 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz73) Bool.false Ns168p568 Ns168p569 7736243323465567 614400000000000000000 94029693123 134217728 1691 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz73) (@HAdd.hAdd Real Real Real qz357 qz425 (Enclosure.sfrac Bool.true Ns168p570 Ns168p571)) Bool.false Ns168p568 Ns168p569 7736243323465567 614400000000000000000 Ns168p572 (Ns168p589 rfl rfl)) 

noncomputable def Ns168p594 := Ns168p567 37366 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 254 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58998322 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 142 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 38926688 134217728) qz76 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz73) qz73 1) Bool.true 4194303 4194304 7715269 589824000000 134217696 134217728 1756 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz73) qz73 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz73)) Bool.true 4194303 4194304 7715269 589824000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz73) qz73) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz73)) Bool.true 16777212 16777216 123444304 9437184000000 4194303 4194304 7715269 589824000000 (Ns168p592 rfl rfl) rfl)) rfl) (Ns168p593 rfl) RS169to186.d7 

noncomputable def Ns168p595 := nat_lit 1057778422314271257028930568608959572794346087644679773854353702618277309219588669631353953637565157871616 

noncomputable def Ns168p596 := nat_lit 127106742355372380407261140270483428538935772986482502365238763551558692428375700388515295870324736 

noncomputable def Ns168p597 := nat_lit 6413246657535578131780229232827515353104011131478843501462224914891993295928164125368038786429015704473600 

noncomputable def Ns168p598 := BSN.cos_dyadic_bound_f 149743294 134217728 4 3 134217728 67108864 Ns168p595 Ns168p118 Ns168p596 Ns168p597 Ns168p121 Ns168p596 58998322 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 149743294) qz363 0 3 Ns168p595 Ns168p118 Ns168p596 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 149743294) qz364 0 3 Ns168p597 Ns168p121 Ns168p596 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p599 := nat_lit 1814139377508806564187519575376164112426993863665066292910406995322791512056364790111324556056040000000000 

noncomputable def Ns168p600 := nat_lit 639940180036829156129685800013116938358939324662712943469925210024728347254121337890625000000000000 

noncomputable def Ns168p601 := nat_lit 10994196557773606555766994048312300461025186049403708737887156158667944533544000027490602914239976000000000 

noncomputable def Ns168p602 := BSN.cos_dyadic_bound_f 171334550 134217728 4 3 134217728 67108864 Ns168p599 Ns168p118 Ns168p600 Ns168p601 Ns168p121 Ns168p600 38926688 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 171334550) qz363 0 3 Ns168p599 Ns168p118 Ns168p600 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 171334550) qz364 0 3 Ns168p601 Ns168p121 Ns168p600 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p603 := nat_lit 60378691196480888728308427955214758007256852705483884437571564920065 

noncomputable def Ns168p604 := nat_lit 3785038491593219004752093273794252791794329673494233604225424641 

noncomputable def Ns168p605 := nat_lit 158128539261796890981466760303119175514485994837748325720185352674561 

noncomputable def Ns168p606 := BSN.sin_dyadic_bound_f 88564319 134217728 3 2 134217728 67108864 Ns168p603 Ns168p112 Ns168p604 Ns168p605 Ns168p115 Ns168p604 82275838 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 88564319) qz361 0 2 Ns168p603 Ns168p112 Ns168p604 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 88564319) qz362 0 2 Ns168p605 Ns168p115 Ns168p604 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p607 := nat_lit 5339548973929919189575517673433483616829419764115857854142869348896353753903713673058938820710272196066881 

noncomputable def Ns168p608 := nat_lit 930001858479549057638489357451547085859747053529114554551353303536944230347567576737799096307990081 

noncomputable def Ns168p609 := nat_lit 26681341587301970446967564574822795853273981621702335959433937535512895249815115572148256550212167298367041 

noncomputable def Ns168p610 := BSN.sin_dyadic_bound_f 176755791 134217728 4 3 134217728 67108864 Ns168p607 Ns168p144 Ns168p608 Ns168p609 Ns168p147 Ns168p608 129915977 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 176755791) qz361 0 3 Ns168p607 Ns168p144 Ns168p608 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 176755791) qz362 0 3 Ns168p609 Ns168p147 Ns168p608 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p611 := Ns168p565 63625 BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 82275838 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 1 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 129915977 134217728) qz76 rfl rfl (Ns168p594 RS169to186.d9 RS169to186.d11 RS169to186.d13 RS169to186.d17 (Ns168p598 rfl rfl) (Ns168p602 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns168p593 rfl) RS169to186.d19 RS169to186.d21 RS169to186.d23 RS169to186.d25 RS169to186.d17 (Ns168p606 rfl rfl) (Ns168p610 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns168p612 := nat_lit 56011548812080579237842498996937183592219290340503377434614569690625 

noncomputable def Ns168p613 := nat_lit 10551006813222132798972667255062720960320187595024839134812890625 

noncomputable def Ns168p614 := nat_lit 168013544422615293447929551656301425334737230646320082625574083290625 

noncomputable def Ns168p615 := BSN.cos_dyadic_bound_f 100672705 134217728 3 2 134217728 67108864 Ns168p612 Ns168p124 Ns168p613 Ns168p614 Ns168p127 Ns168p613 98199203 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 100672705) qz363 0 2 Ns168p612 Ns168p124 Ns168p613 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 100672705) qz364 0 2 Ns168p614 Ns168p127 Ns168p613 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p616 := BSN.sin_dyadic_bound_f 4007578 134217728 1 0 134217728 67108864 0 1 1 0 1 1 4006982 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 4007578) qz361 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 4007578) qz362 0 0 rfl) rfl rfl 

noncomputable def Ns168p617 := Ns168p563 85764 BSN.abs_quadSignPos (BSN.cos_quad_nat0 48 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 98199203 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 91 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 4006982 134217728) qz76 rfl rfl (Ns168p611 rfl rfl) (Ns168p593 rfl) RS169to186.d27 RS169to186.d29 RS169to186.d31 RS169to186.d33 RS169to186.d17 (Ns168p615 rfl rfl) (Ns168p616 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns168p618 := nat_lit 6196533811189162622416736551289958908695897244461866973998627045057837560470686671082079346767678790434816 

noncomputable def Ns168p619 := nat_lit 1452810455918850566755597239316143716188853814887690257107813643547230224442194505778686854814498816 

noncomputable def Ns168p620 := nat_lit 30960584094618537661253711405004173268692385807010502523414901490690690044995953749202795243135740911026176 

noncomputable def Ns168p621 := BSN.sin_dyadic_bound_f 183449872 134217728 4 3 134217728 67108864 Ns168p618 Ns168p144 Ns168p619 Ns168p620 Ns168p147 Ns168p619 131434916 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 183449872) qz361 0 3 Ns168p618 Ns168p144 Ns168p619 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 183449872) qz362 0 3 Ns168p620 Ns168p147 Ns168p619 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p622 := Ns168p561 Bool.true 173768271 85764 Bool.true 183449872 7074237752028440 1 Bool.false 131434916 Bool.false Bool.true 127299016 95568 BSN.abs_quadSignPos qz365 (BSN.sfrac_eq_quadSignPos_mul Bool.false 131434916 134217728) qz76 rfl (Ns168p617 rfl) (Ns168p593 rfl) RS169to186.d35 RS169to186.d37 RS169to186.d17 (Ns168p621 rfl rfl) rfl 

noncomputable def Ns168p623 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz73) qz73 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz73) qz73 8) 127299016 134217728 95568 134217728 127299016 134217728 95568 134217728 34171569408311296 15912377 8388608 5973 4194304 (Ns168p622 rfl rfl rfl rfl) 

noncomputable def Ns168p624 := @Enclosure.Real.IsNear.mulLit_ff qz679 (Zeta.RiemannSiegel.correction qz75) 2910637 8388608 1 8388608 31756626705399 70368744177664 1236271942023983 19791209299968000000 92432012683922429163 590295810358705651712 

noncomputable abbrev qz684 := (@HPow.hPow Real Real Real qz7 qz74 qz9)

noncomputable def Ns168p625 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz684 1 1 0 1 2910637 8388608 1 8388608 2910637 8388608 1 8388608 

noncomputable def Ns168p626 := @Enclosure.Real.IsNear.sqrt_image qz74 578758194573 8388608000 216749 8388608000 69677642 69677669 8388608 (@Enclosure.Real.IsNear.of_eq qz74 (@HMul.hMul Real Real Real qz5 qz73 qz3) Bool.false 578758194573 8388608000 216749 8388608000 (BSN.t_div_two_pi_mk qz73 433498 1000 qz76) (@Enclosure.Real.IsNear.mulLit_ff qz73 qz3 433498 1000 0 1 2670177 16777216 1 16777216 578758194573 8388608000 216749 8388608000 (Enclosure.Real.IsNear.const Bool.false 433498 1000) RS169to186.d40 rfl)) 

noncomputable abbrev qz911 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 433498 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz685 := qz911

noncomputable abbrev qz430 := qz685

noncomputable abbrev qz78 := qz430

noncomputable def Ns168p627 := @Enclosure.Real.IsNear.sqrt_image qz78 139355311 16777216 27 16777216 24176402 24176407 8388608 (@Enclosure.Real.IsNear.recentre' qz78 Bool.false 139355311 16777216 27 16777216 139355311 16777216 27 16777216 (Ns168p626 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns168p628 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz78) 48352809 16777216 5 16777216 2910636 2910638 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz78) Bool.false 48352809 16777216 5 16777216 48352809 16777216 5 16777216 (Ns168p627 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns168p629 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz78)) Bool.false 5821274 16777216 2 16777216 2910637 8388608 1 8388608 (Ns168p628 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz79 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz423))

noncomputable abbrev qz686 := (@HMul.hMul Real Real Real qz890 qz910 qz910)

noncomputable abbrev qz431 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz686 qz678) qz641)

noncomputable abbrev qz80 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz431))

noncomputable def Ns168p630 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz75) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz79) qz80) Bool.false 31756626705399 

noncomputable def Ns168p631 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz79) qz80 48494283 16777216 1483 

noncomputable abbrev qz687 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz79))

noncomputable def Ns168p632 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz79) (@Neg.neg Real Real.instNeg qz687) Bool.true 48494283 16777216 1483 16777216 (BSN.inv_eq_neg_inv_neg qz79) 

noncomputable def Ns168p633 := @Enclosure.Real.IsNear.recentre' qz687 Bool.false 48494283 16777216 1483 16777216 48494283 16777216 

noncomputable def Ns168p634 := @Enclosure.Real.IsNear.recentre' qz79 Bool.true 2902146 8388608 199638608 18874368000000 1451073 4194304 12477413 1179648000000 

noncomputable abbrev qz81 := (@HMul.hMul Real Real Real qz342 qz340 qz423)

noncomputable def Ns168p635 := @Enclosure.Real.IsNear.cos_image qz81 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16140193) qz360) Bool.false 16140193 8388608 85 8388608 Bool.true 2902146 8388608 1 

noncomputable def Ns168p636 := nat_lit 145724807217664145844106649 

noncomputable def Ns168p637 := nat_lit 14411518807585587200000000000000 

noncomputable def Ns168p638 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz75 884279719003555 140737488355328 1 500000000000000 5137583 16777216 27 16777216 4543060451597441107565 2361183241434822606848 Ns168p636 

noncomputable def Ns168p639 := @Enclosure.Real.IsNear.subLit_ff_p qz78 qz1 139355311 16777216 27 16777216 8 1 0 1 5137583 5137583 16777216 27 

noncomputable def Ns168p640 := @Ns168p639 16777216 (@Enclosure.Real.IsNear.recentre' qz78 Bool.false 139355311 16777216 27 16777216 139355311 16777216 27 16777216 (Ns168p626 rfl rfl rfl rfl rfl rfl) rfl) qz371 

noncomputable def Ns168p641 := @Enclosure.Real.IsNear.recentre' qz81 Bool.false 4543060451597441107565 2361183241434822606848 Ns168p636 Ns168p637 16140193 8388608 85 8388608 (@Ns168p638 Ns168p637 RS169to186.d39 (Ns168p640 rfl rfl) rfl) 

noncomputable def Ns168p642 := nat_lit 33482072343853769417514234451863403536400688695098673770650375690096513591656763987219882881 

noncomputable def Ns168p643 := nat_lit 312539334526096259378848294828920578545894429134702682256303729226747512941535314224001 

noncomputable def Ns168p644 := nat_lit 202027255779459937936632326782104789369836153468943561762906483072436747646946687219484500865 

noncomputable def Ns168p645 := BSN.cos_dyadic_bound_t 16140193 8388608 4 3 8388608 2250000 Ns168p642 Ns168p187 Ns168p643 Ns168p644 Ns168p190 Ns168p643 2902146 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16140193) (BSN.cosEvenQ 8388608) 0 3 Ns168p642 Ns168p187 Ns168p643 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16140193) (BSN.cosOddQ 8388608) 0 3 Ns168p644 Ns168p190 Ns168p643 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p646 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz79) 1451073 4194304 12477413 1179648000000 24246400 24247883 8388608 (@Enclosure.Real.IsNear.neg qz79 Bool.true 1451073 4194304 12477413 1179648000000 (Ns168p634 (@Ns168p635 2250000 (Ns168p641 rfl) (Enclosure.sfrac_false_div 16140193 8388608) (Ns168p645 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns168p647 := Ns168p632 (@Enclosure.Real.IsNear.neg qz687 Bool.false 48494283 16777216 1483 16777216 (@Ns168p633 1483 16777216 (Ns168p646 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p648 := @Enclosure.Real.IsNear.recentre' qz80 Bool.true 1309706 8388608 

noncomputable abbrev qz82 := (@HMul.hMul Real Real Real qz342 qz340 qz431)

noncomputable def Ns168p649 := @Enclosure.Real.IsNear.cos_image qz82 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1811485)) qz671) Bool.true 1811485 1048576 

noncomputable def Ns168p650 := nat_lit 68435969685422920451662022525 

noncomputable def Ns168p651 := nat_lit 19711035430962939263698319607041941 

noncomputable def Ns168p652 := @Enclosure.Real.IsNear.recentre' qz82 Bool.true Ns168p650 Ns168p178 Ns168p651 

noncomputable abbrev qz83 := qz431

noncomputable def Ns168p653 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz83 884279719003555 140737488355328 1 500000000000000 77391766671455 

noncomputable abbrev qz432 := (@HSub.hSub Real Real Real qz633 qz686 qz678)

noncomputable abbrev qz84 := qz432

noncomputable def Ns168p654 := @Enclosure.Real.IsNear.subLit_tf qz84 qz25 59799580627039 281474976710656 730415043 281474976710656 1 16 

noncomputable abbrev qz433 := qz686

noncomputable abbrev qz85 := qz433

noncomputable def Ns168p655 := @Enclosure.Real.IsNear.subLit_ff_n qz85 qz75 26394759081889 281474976710656 277430211 281474976710656 5137583 16777216 27 16777216 

noncomputable def Ns168p656 := @Enclosure.Real.IsNear.mulLit_ff qz75 qz75 5137583 16777216 27 16777216 5137583 16777216 27 16777216 26394759081889 281474976710656 

noncomputable def Ns168p657 := nat_lit 315763705722308331064128748486219706385053959243823499151879074373851384500640625 

noncomputable def Ns168p658 := nat_lit 846322570984149739285326836131859157750990110577656481930582364989086940895641600 

noncomputable def Ns168p659 := nat_lit 1248581530882743983487415259315507088467594268944596124906295921445556640625 

noncomputable def Ns168p660 := nat_lit 1908891584540230916067815085627957435404510927008545205461732640308777526350240625 

noncomputable def Ns168p661 := nat_lit 77015353959557626274964742087999183355340100062566739855682995214006911621503385600 

noncomputable def Ns168p662 := BSN.cos_dyadic_bound_t 1811485 1048576 4 3 8388608 2250000 Ns168p657 Ns168p658 Ns168p659 Ns168p660 Ns168p661 Ns168p659 1309706 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 1811485) (BSN.cosEvenQ 1048576) 0 3 Ns168p657 Ns168p658 Ns168p659 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 1811485) (BSN.cosOddQ 1048576) 0 3 Ns168p660 Ns168p661 Ns168p659 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p663 := @Ns168p648 635527216 37748736000000 654853 4194304 39720451 2359296000000 (@Ns168p649 275 16777216 Bool.true 1309706 8388608 1 2250000 (@Ns168p652 Ns168p181 1811485 1048576 275 16777216 (@Ns168p653 281474976710656 730415043 281474976710656 Ns168p650 Ns168p178 Ns168p651 Ns168p181 RS169to186.d39 (@Ns168p654 0 1 1238268266743280 77391766671455 281474976710656 730415043 281474976710656 (@Ns168p655 1003270480889248743424 59799580627039 281474976710656 730415043 281474976710656 (@Ns168p656 277430211 281474976710656 (Ns168p640 rfl rfl) (Ns168p640 rfl rfl) rfl) (Ns168p640 rfl rfl) rfl rfl) qz375 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 1811485 1048576) (BSN.cos_neg_of_bound 1811485 1048576 Bool.true 1309706 8388608 1 2250000 (Ns168p662 rfl rfl)) rfl rfl) 

noncomputable def Ns168p664 := @Ns168p624 56363619438276489061 Ns168p558 (Ns168p625 qz27 (@Enclosure.Real.IsNear.of_eq qz684 (@Inv.inv Real Real.instInv (Real.sqrt qz78)) Bool.false 2910637 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz74 (BSN.t_div_two_pi_nonneg qz73 433498 1000 qz76)) Ns168p629) rfl) (@Ns168p630 70368744177664 1236271942023983 19791209299968000000 (BSN.correction_mk qz75 (BSN.cos_two_pi_p_ne_zero_mk qz73 433498 1000 8 qz76 rfl rfl (@BSN.floor_sqrt_eq_dec qz73 433498 1000 8 qz76 rfl rfl rfl))) (@Ns168p631 16777216 654853 4194304 39720451 2359296000000 31756626705399 70368744177664 1236271942023983 19791209299968000000 Ns168p647 (Ns168p663 rfl) rfl)) 

noncomputable def Ns168p665 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz73) (hardyZApproximantRS₀ qz73) Bool.true 1212165999055466976491 590295810358705651712 3750516530335428489061 Ns168p558 (@Eq.refl Real (hardyZApproximantRS₀ qz73)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz73) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz73) qz73 8) (@HMul.hMul Real Real Real qz5 qz679 (Zeta.RiemannSiegel.correction qz75))) Bool.true 1212165999055466976491 590295810358705651712 3750516530335428489061 Ns168p558 (BSN.hardyZApproximantRS₀_eq qz73 8 (@BSN.floor_sqrt_eq_dec qz73 433498 1000 8 qz76 rfl rfl rfl)) (@Ns168p560 1212165999055466976491 590295810358705651712 3750516530335428489061 Ns168p558 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz73) qz73 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz73) qz73 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz73) qz73 8)) Bool.true 15912377 8388608 5973 4194304 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz73) qz73 8) (Ns168p623 (Ns168p622 rfl rfl rfl rfl) rfl rfl)) (Ns168p664 rfl) rfl rfl)) 

theorem RS169to186.d47 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz73) Bool.true 1212165999055466976491 590295810358705651712 3750516530335428489061 Ns168p558 := Ns168p665 

noncomputable def Ns168p666 := nat_lit 115699117822182438478305820672 

noncomputable abbrev qz912 := (Enclosure.sfrac Bool.false 434981 1000)

noncomputable abbrev qz688 := qz912

noncomputable abbrev qz434 := qz688

noncomputable abbrev qz86 := qz434

noncomputable abbrev qz913 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 434981 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz689 := qz913

noncomputable abbrev qz435 := qz689

noncomputable abbrev qz87 := qz435

noncomputable abbrev qz914 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 434981 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz690 := qz914

noncomputable abbrev qz436 := qz690

noncomputable abbrev qz88 := qz436

noncomputable abbrev qz691 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz87 qz9))

noncomputable def Ns168p667 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz86) qz86 8) (@HMul.hMul Real Real Real qz5 qz691 (Zeta.RiemannSiegel.correction qz88)) 201134889 33554432 47949 33554432 90299978002335815503 590295810358705651712 1467961657957559638463 Ns168p449 Ns168p666 

noncomputable def Ns168p668 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz86) qz86 Real.sin BSN.quadSignPos 7 8 434981 1000 127 134217728 67108864 2251799813685248 Bool.false 94451242253 1697 279097919 60 47453128 8 

noncomputable def Ns168p669 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz86) qz86 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 434981 1000 48 90 134217728 67108864 2251799813685248 Bool.false 94451242253 1697 

noncomputable def Ns168p670 := Ns168p669 240485871 61 54794152 8 261175631 61 50729528 8 Bool.false 314888064 63845 Bool.true 35764122 Bool.true 180610623 7074237752028440 1 Bool.false 129480938 Bool.false Bool.false 29963449 Bool.true Bool.false 356423311 

noncomputable def Ns168p671 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz86) qz86 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 434981 1000 64 2 134217728 67108864 2251799813685248 Bool.false 94451242253 1697 

noncomputable def Ns168p672 := Ns168p671 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 301464572 37496 Bool.false 23349948 Bool.false 67125831 7074237752028440 1 Bool.false 132191742 Bool.false Bool.false 117779002 Bool.true Bool.false 314888064 

noncomputable def Ns168p673 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz86) qz86 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 434981 1000 256 143 134217728 67108864 2251799813685248 Bool.false 94451242253 1697 

noncomputable def Ns168p674 := Ns168p673 93032624 60 94906264 8 147453232 60 77490640 16 Bool.false 134217720 1764 Bool.false 11667614 Bool.false 163381823 7074237752028440 1 Bool.false 133710911 Bool.false Bool.false 125918298 Bool.false Bool.false 301464572 

noncomputable def Ns168p675 := nat_lit 772829181311934509338178461969556819984361481287871262717 

noncomputable def Ns168p676 := nat_lit 1098210826800083712778252379253066291187485178331136000 

noncomputable def Ns168p677 := nat_lit 7474706214764442799368799472480000 

noncomputable def Ns168p678 := nat_lit 19508143132897325827070964607888937280 

noncomputable abbrev qz437 := (@Eq.refl Real qz688)

noncomputable abbrev qz89 := qz437

noncomputable def Ns168p679 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz86 434981 1000 756834881444 16000000 869962 4000 2000 Ns168p677 Ns168p678 qz89 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns168p680 := nat_lit 247305338019819042988217107830258182394995674012118804069440 

noncomputable abbrev qz692 := (Real.log (Enclosure.sfrac Bool.false 756834881444 16000000))

noncomputable abbrev qz90 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 434981 4000) qz692) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 869962))))))

noncomputable abbrev qz693 := (Enclosure.sfrac Bool.false 434981 2000)

noncomputable abbrev qz438 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz90 qz693) (@HMul.hMul Real Real Real qz5 qz693 (Real.log Real.pi)))

noncomputable def Ns168p681 := @Enclosure.Real.IsNear.addLit_ft_p qz438 (Enclosure.sfrac Bool.true Ns168p677 Ns168p678) 12677038044441804714173 18014398509481984000 46574853184341269 3686400000000000000000 Ns168p677 Ns168p678 0 1 Ns168p680 

noncomputable def Ns168p682 := nat_lit 850741622047271028477994729472000 

noncomputable abbrev qz439 := (@HSub.hSub Real Real Real qz12 qz90 qz693)

noncomputable abbrev qz440 := (@HMul.hMul Real Real Real qz5 qz693 (Real.log Real.pi))

noncomputable def Ns168p683 := @Enclosure.Real.IsNear.subLit_ff_p qz439 qz440 17162044551837839175869 18014398509481984000 44298111745387 7200000000000000000 16707951230541 67108864000 434981 67108864000 Ns168p682 12677038044441804714173 18014398509481984000 

noncomputable def Ns168p684 := nat_lit 34324089103675678351738000 

noncomputable abbrev qz441 := qz693

noncomputable def Ns168p685 := @Enclosure.Real.IsNear.subLit_ff_p qz90 qz441 21080005090864330617021 18014398509481984000 44298111745387 7200000000000000000 434981 2000 0 1 Ns168p684 17162044551837839175869 18014398509481984000 44298111745387 7200000000000000000 

noncomputable def Ns168p686 := nat_lit 47467951536092379020282663243725406208 

noncomputable def Ns168p687 := nat_lit 26026508586474640341204992 

noncomputable def Ns168p688 := nat_lit 123803343395021229242637346985058724045576701602318559711404590188569713702570925913468325445723520133155215248180350702059520 

noncomputable def Ns168p689 := nat_lit 1387253461921822176416618771165466039603406399726606507458501405398630883113858392903149150908886261829189391750352369352704 

noncomputable def Ns168p690 := nat_lit 437055919362435939837076796465217686527551110006588247651723577765618813758940139872153413422124780021177429991096320 

noncomputable def Ns168p691 := BSN.log_dyadic_bound 232546881444 1281122881444 6 5 Ns168p688 67108864 18000000 Ns168p689 Ns168p690 24635929 1513669762888 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 232546881444) (BSN.artanhQ 1281122881444) 0 5 Ns168p689 Ns168p688 Ns168p690 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns168p692 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 434981 4000) qz692 434981 4000 0 1 48478149970014841 4503599627370496 100000027 1800000000000000 21087074152107025553021 18014398509481984000 43498111744487 7200000000000000000 (Enclosure.Real.IsNear.const Bool.false 434981 4000) (BSN.isNear_log_sfrac 756834881444 16000000 48478149970014841 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 756834881444) qz353)) Bool.false Ns168p687 Ns168p89 1000000270000000 18000000000000000000000 48478149970014841 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 756834881444 16000000 15 1513669762888 1048576000000 24635929 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns168p691 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p693 := BSN.arctan_dyadic_bound_f 1000 869962 1 0 8388608 2250000 0 1 1 0 1 1 9642 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 869962) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 869962) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz442 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 869962)))

noncomputable def Ns168p694 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz442 884279719003555 562949953421312 1 2000000000000000 9642 8388608 1 2250000 7412447961620085211136 883632655336867 562949953421312 8000000009 18000000000000000 qz16 (Ns168p693 rfl) rfl rfl 

noncomputable def Ns168p695 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 434981 4000) qz692) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz442)) 21087074152107025553021 18014398509481984000 43498111744487 7200000000000000000 883632655336867 2251799813685248 8000000009 72000000000000000 Ns168p686 21080005090864330617021 18014398509481984000 44298111745387 7200000000000000000 (Ns168p692 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz442) 1 4 0 1 883632655336867 562949953421312 8000000009 18000000000000000 883632655336867 2251799813685248 8000000009 72000000000000000 qz356 Ns168p694 rfl) 

noncomputable def Ns168p696 := @Ns168p681 Ns168p675 Ns168p676 46574853184341269 3686400000000000000000 (@Ns168p683 46574853184341269 3686400000000000000000 (Ns168p685 (Ns168p695 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 434981 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz441 (Real.log Real.pi) 434981 2000 0 1 38410761 33554432 1 33554432 16707951230541 67108864000 434981 67108864000 (Enclosure.Real.IsNear.const Bool.false 434981 2000) RS169to186.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns168p677 Ns168p678) 

noncomputable def Ns168p697 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz86) Bool.false Ns168p675 Ns168p676 46574853184341269 3686400000000000000000 11806405281 16777216 213 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz86) (@HAdd.hAdd Real Real Real qz357 qz438 (Enclosure.sfrac Bool.true Ns168p677 Ns168p678)) Bool.false Ns168p675 Ns168p676 46574853184341269 3686400000000000000000 Ns168p679 (Ns168p696 rfl rfl)) 

noncomputable def Ns168p698 := nat_lit 3797561855649716342095872 

noncomputable def Ns168p699 := nat_lit 856784290376892335900497739259725707927826755913916425631374576100993549063419667348302647735280264550505351491497689257667275428663296 

noncomputable def Ns168p700 := nat_lit 610239999926210852241890659693308777344207423726615520834165201938884840150484107507876978495301574526094210347756722258980048896 

noncomputable def Ns168p701 := nat_lit 4278600337118241432326761172535593401015316130863224506895114277152653809228320938096733238124915861596572823577911694621839223707078656 

noncomputable def Ns168p702 := BSN.sin_dyadic_bound_f 53966599802 34359738368 4 3 16777216 4504395 Ns168p699 Ns168p103 Ns168p700 Ns168p701 Ns168p106 Ns168p700 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53966599802) qz358 0 3 Ns168p699 Ns168p103 Ns168p700 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53966599802) qz359 0 3 Ns168p701 Ns168p106 Ns168p700 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p703 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz86) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11806405281) qz370) Bool.false 11806405281 16777216 213 16777216 Bool.false 16777215 16777216 1 2250000 (Ns168p697 rfl) (Enclosure.sfrac_false_div 11806405281 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11806405281) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns168p698) qz385) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 111 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q3 11806405281 16777216 226375608064910080 72057594037927936 111 Ns168p698 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns168p698 Ns168p89 53966599802 34359738368 4504395 4500000 (Ns168p702 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p704 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz86) Bool.false Ns168p675 Ns168p676 46574853184341269 3686400000000000000000 94451242253 134217728 1697 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz86) (@HAdd.hAdd Real Real Real qz357 qz438 (Enclosure.sfrac Bool.true Ns168p677 Ns168p678)) Bool.false Ns168p675 Ns168p676 46574853184341269 3686400000000000000000 Ns168p679 (Ns168p696 rfl rfl)) 

noncomputable def Ns168p705 := Ns168p674 37496 BSN.abs_quadSignPos (BSN.cos_quad_nat0 256 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133710911 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 143 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 125918298 134217728) qz89 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz86) qz86 1) Bool.false 16777215 16777216 31001701 2359296000000 134217720 134217728 1764 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz86) qz86 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz86)) Bool.false 16777215 16777216 31001701 2359296000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz86) qz86) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz86)) Bool.false 16777215 16777216 496027216 37748736000000 16777215 16777216 31001701 2359296000000 (Ns168p703 rfl rfl) rfl)) rfl) (Ns168p704 rfl) RS169to186.d7 

noncomputable def Ns168p706 := nat_lit 18532252621838260835477376016 

noncomputable def Ns168p707 := BSN.cos_dyadic_bound_f 11667614 134217728 2 1 134217728 67108864 Ns168p706 Ns168p130 Ns168p706 Ns168p706 Ns168p131 Ns168p706 133710911 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 11667614) qz363 0 1 Ns168p706 Ns168p130 Ns168p706 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 11667614) qz364 0 1 Ns168p706 Ns168p131 Ns168p706 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p708 := nat_lit 699763834901339333955726875590176609988577580789577233413655557942785 

noncomputable def Ns168p709 := nat_lit 507726580943243016056443162013590392826282612920286111892406382081 

noncomputable def Ns168p710 := nat_lit 1831892772181980624048526623331011975048365396885117052854605422374401 

noncomputable def Ns168p711 := BSN.sin_dyadic_bound_f 163381823 134217728 3 2 134217728 67108864 Ns168p708 Ns168p112 Ns168p709 Ns168p710 Ns168p115 Ns168p709 125918298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 163381823) qz361 0 2 Ns168p708 Ns168p112 Ns168p709 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 163381823) qz362 0 2 Ns168p710 Ns168p115 Ns168p709 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p712 := nat_lit 297264926478457676707220111616 

noncomputable def Ns168p713 := BSN.cos_dyadic_bound_f 23349948 134217728 2 1 134217728 67108864 Ns168p712 Ns168p130 Ns168p712 Ns168p712 Ns168p131 Ns168p712 132191742 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 23349948) qz363 0 1 Ns168p712 Ns168p130 Ns168p712 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 23349948) qz364 0 1 Ns168p712 Ns168p131 Ns168p712 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p714 := nat_lit 11069389952305243017560814875017297825649067895359311292114950755521 

noncomputable def Ns168p715 := nat_lit 412208935249247193282668668317212694774717503504604407363867841 

noncomputable def Ns168p716 := nat_lit 33207345439045230558295879287715259051557654251070924667530124530881 

noncomputable def Ns168p717 := BSN.cos_dyadic_bound_f 67125831 134217728 3 2 134217728 67108864 Ns168p714 Ns168p124 Ns168p715 Ns168p716 Ns168p127 Ns168p715 117779002 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 67125831) qz363 0 2 Ns168p714 Ns168p124 Ns168p715 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 67125831) qz364 0 2 Ns168p716 Ns168p127 Ns168p715 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p718 := Ns168p672 63845 BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 132191742 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 2 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 117779002 134217728) qz89 rfl rfl (Ns168p705 RS169to186.d9 RS169to186.d11 RS169to186.d13 RS169to186.d17 (Ns168p707 rfl rfl) (Ns168p711 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns168p704 rfl) RS169to186.d19 RS169to186.d21 RS169to186.d23 RS169to186.d25 RS169to186.d17 (Ns168p713 rfl rfl) (Ns168p717 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns168p719 := nat_lit 1636026261823209767147757021456 

noncomputable def Ns168p720 := BSN.cos_dyadic_bound_f 35764122 134217728 2 1 134217728 67108864 Ns168p719 Ns168p130 Ns168p719 Ns168p719 Ns168p131 Ns168p719 129480938 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 35764122) qz363 0 1 Ns168p719 Ns168p130 Ns168p719 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 35764122) qz364 0 1 Ns168p719 Ns168p131 Ns168p719 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p721 := nat_lit 2240912971351275678244501934352401057204323498663799526283193718476463815917905445195282908145376199660801 

noncomputable def Ns168p722 := nat_lit 1204812565297744403989557870388672032403466439341018714013445980558363155023687093927620657626174721 

noncomputable def Ns168p723 := nat_lit 13577211188076892145397853450810960868662870484244343068795042989633040257661490757096111408953498377868545 

noncomputable def Ns168p724 := BSN.cos_dyadic_bound_f 180610623 134217728 4 3 134217728 67108864 Ns168p721 Ns168p118 Ns168p722 Ns168p723 Ns168p121 Ns168p722 29963449 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 180610623) qz363 0 3 Ns168p721 Ns168p118 Ns168p722 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 180610623) qz364 0 3 Ns168p723 Ns168p121 Ns168p722 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p725 := Ns168p670 86060 BSN.abs_quadSignPos (BSN.cos_quad_nat0 48 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 129480938 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 90 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 29963449 134217728) qz89 rfl rfl (Ns168p718 rfl rfl) (Ns168p704 rfl) RS169to186.d27 RS169to186.d29 RS169to186.d31 RS169to186.d33 RS169to186.d17 (Ns168p720 rfl rfl) (Ns168p724 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns168p726 := nat_lit 5225230193098803379779675909945387677257164895086159018723911505437646237368325140643698237204219230683136 

noncomputable def Ns168p727 := nat_lit 871593690626383236289297487420252368505910428437708195364763731144698095515553717501524855788404736 

noncomputable def Ns168p728 := nat_lit 26110441955065466686274878089598688014531999591034981793453399809312137710509939624461795710870606258896896 

noncomputable def Ns168p729 := BSN.sin_dyadic_bound_f 175802956 134217728 4 3 134217728 67108864 Ns168p726 Ns168p144 Ns168p727 Ns168p728 Ns168p147 Ns168p727 129673405 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 175802956) qz361 0 3 Ns168p726 Ns168p144 Ns168p727 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 175802956) qz362 0 3 Ns168p728 Ns168p147 Ns168p727 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p730 := Ns168p668 Bool.false 356423311 86060 Bool.true 175802956 7074237752028440 1 Bool.false 129673405 Bool.false Bool.false 402269778 95898 BSN.abs_quadSignPos qz365 (BSN.sfrac_eq_quadSignPos_mul Bool.false 129673405 134217728) qz89 rfl (Ns168p725 rfl) (Ns168p704 rfl) RS169to186.d35 RS169to186.d37 RS169to186.d17 (Ns168p729 rfl rfl) rfl 

noncomputable def Ns168p731 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz86) qz86 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz86) qz86 8) 402269778 134217728 95898 134217728 402269778 134217728 95898 134217728 107983471292448768 201134889 33554432 47949 33554432 (Ns168p730 rfl rfl rfl rfl) 

noncomputable def Ns168p732 := @Enclosure.Real.IsNear.mulLit_ff qz691 (Zeta.RiemannSiegel.correction qz88) 2908153 8388608 1 8388608 31050628354951 70368744177664 125818230683893 2473901162496000000 90299978002335815503 590295810358705651712 

noncomputable abbrev qz694 := (@HPow.hPow Real Real Real qz7 qz87 qz9)

noncomputable def Ns168p733 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz694 1 1 0 1 2908153 8388608 1 8388608 2908153 8388608 1 8388608 

noncomputable def Ns168p734 := @Enclosure.Real.IsNear.sqrt_image qz87 1161476261637 16777216000 434981 16777216000 69796724 69796751 8388608 (@Enclosure.Real.IsNear.of_eq qz87 (@HMul.hMul Real Real Real qz5 qz86 qz3) Bool.false 1161476261637 16777216000 434981 16777216000 (BSN.t_div_two_pi_mk qz86 434981 1000 qz89) (@Enclosure.Real.IsNear.mulLit_ff qz86 qz3 434981 1000 0 1 2670177 16777216 1 16777216 1161476261637 16777216000 434981 16777216000 (Enclosure.Real.IsNear.const Bool.false 434981 1000) RS169to186.d40 rfl)) 

noncomputable abbrev qz915 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 434981 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz695 := qz915

noncomputable abbrev qz443 := qz695

noncomputable abbrev qz91 := qz443

noncomputable def Ns168p735 := @Enclosure.Real.IsNear.sqrt_image qz91 139593475 16777216 27 16777216 24197052 24197058 8388608 (@Enclosure.Real.IsNear.recentre' qz91 Bool.false 139593475 16777216 27 16777216 139593475 16777216 27 16777216 (Ns168p734 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns168p736 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz91) 24197055 8388608 3 8388608 2908152 2908154 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz91) Bool.false 48394110 16777216 6 16777216 24197055 8388608 3 8388608 (Ns168p735 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns168p737 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz91)) Bool.false 5816306 16777216 2 16777216 2908153 8388608 1 8388608 (Ns168p736 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz92 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz436))

noncomputable abbrev qz696 := (@HMul.hMul Real Real Real qz890 qz914 qz914)

noncomputable abbrev qz444 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz696 qz690) qz641)

noncomputable abbrev qz93 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz444))

noncomputable def Ns168p738 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz88) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz92) qz93) Bool.false 31050628354951 

noncomputable def Ns168p739 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz92) qz93 39184213 16777216 975 

noncomputable abbrev qz697 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz92))

noncomputable def Ns168p740 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz92) (@Neg.neg Real Real.instNeg qz697) Bool.true 39184213 16777216 975 16777216 (BSN.inv_eq_neg_inv_neg qz92) 

noncomputable def Ns168p741 := @Enclosure.Real.IsNear.recentre' qz697 Bool.false 39184213 16777216 975 16777216 39184213 16777216 

noncomputable def Ns168p742 := @Enclosure.Real.IsNear.recentre' qz92 Bool.true 7183377 16777216 401527216 37748736000000 7183377 16777216 25095451 2359296000000 

noncomputable abbrev qz94 := (@HMul.hMul Real Real Real qz342 qz340 qz436)

noncomputable def Ns168p743 := @Enclosure.Real.IsNear.cos_image qz94 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16888407) qz360) Bool.false 16888407 8388608 171 16777216 Bool.true 7183377 16777216 1 

noncomputable def Ns168p744 := nat_lit 728624036090366542402702333 

noncomputable def Ns168p745 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz88 884279719003555 140737488355328 1 500000000000000 5375747 16777216 27 16777216 4753664046594203780585 2361183241434822606848 Ns168p744 

noncomputable def Ns168p746 := @Enclosure.Real.IsNear.subLit_ff_p qz91 qz1 139593475 16777216 27 16777216 8 1 0 1 5375747 5375747 16777216 27 

noncomputable def Ns168p747 := @Ns168p746 16777216 (@Enclosure.Real.IsNear.recentre' qz91 Bool.false 139593475 16777216 27 16777216 139593475 16777216 27 16777216 (Ns168p734 rfl rfl rfl rfl rfl rfl) rfl) qz371 

noncomputable def Ns168p748 := @Enclosure.Real.IsNear.recentre' qz94 Bool.false 4753664046594203780585 2361183241434822606848 Ns168p744 Ns168p163 16888407 8388608 171 16777216 (@Ns168p745 Ns168p163 RS169to186.d39 (Ns168p747 rfl rfl) rfl) 

noncomputable def Ns168p749 := nat_lit 53418322296873011905609383426225207664081 

noncomputable def Ns168p750 := nat_lit 167255588988979673561517887044862711294853120 

noncomputable def Ns168p751 := nat_lit 1170789122922857714930625209314038979063971840 

noncomputable def Ns168p752 := BSN.sin_dyadic_bound_f 15202764253 34359738368 2 1 16777216 4504395 Ns168p749 Ns168p750 Ns168p749 Ns168p749 Ns168p751 Ns168p749 7183377 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 15202764253) qz358 0 1 Ns168p749 Ns168p750 Ns168p749 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 15202764253) qz359 0 1 Ns168p749 Ns168p751 Ns168p749 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p753 := @Ns168p743 2250000 (Ns168p748 rfl) (Enclosure.sfrac_false_div 16888407 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16888407) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 534899714288431623307264) qz636) 226375608064910080 72057594037927936 Bool.false 7183377 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 16888407 8388608 226375608064910080 72057594037927936 0 534899714288431623307264 Ns168p101 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 7183377 16777216 534899714288431623307264 Ns168p101 15202764253 34359738368 4504395 4500000 (Ns168p752 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p754 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz92) 7183377 16777216 25095451 2359296000000 19591619 19592594 8388608 (@Enclosure.Real.IsNear.neg qz92 Bool.true 7183377 16777216 25095451 2359296000000 (Ns168p742 (Ns168p753 rfl rfl) rfl)) 

noncomputable def Ns168p755 := Ns168p740 (@Enclosure.Real.IsNear.neg qz697 Bool.false 39184213 16777216 975 16777216 (@Ns168p741 975 16777216 (Ns168p754 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p756 := @Enclosure.Real.IsNear.recentre' qz93 Bool.true 1584854 8388608 

noncomputable abbrev qz95 := (@HMul.hMul Real Real Real qz342 qz340 qz444)

noncomputable def Ns168p757 := @Enclosure.Real.IsNear.cos_image qz95 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 14771231)) qz360) Bool.true 14771231 8388608 

noncomputable def Ns168p758 := nat_lit 69755166595672812204514578245 

noncomputable def Ns168p759 := nat_lit 20058099460816610570505106547253661 

noncomputable def Ns168p760 := @Enclosure.Real.IsNear.recentre' qz95 Bool.true Ns168p758 Ns168p178 Ns168p759 

noncomputable abbrev qz96 := qz444

noncomputable def Ns168p761 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz96 884279719003555 140737488355328 1 500000000000000 78883598816759 

noncomputable abbrev qz445 := (@HSub.hSub Real Real Real qz633 qz696 qz690)

noncomputable abbrev qz97 := qz445

noncomputable def Ns168p762 := @Enclosure.Real.IsNear.subLit_tf qz97 qz25 61291412772343 281474976710656 743275899 281474976710656 1 16 

noncomputable abbrev qz446 := qz696

noncomputable abbrev qz98 := qz446

noncomputable def Ns168p763 := @Enclosure.Real.IsNear.subLit_ff_n qz98 qz88 28898655808009 281474976710656 290291067 281474976710656 5375747 16777216 27 16777216 

noncomputable def Ns168p764 := @Enclosure.Real.IsNear.mulLit_ff qz88 qz88 5375747 16777216 27 16777216 5375747 16777216 27 16777216 28898655808009 281474976710656 

noncomputable def Ns168p765 := nat_lit 23431059075358087320664761570991175537840132113498157901741825921061480234860946671064602241 

noncomputable def Ns168p766 := nat_lit 107894741520300064978245755269605694782893667693727153588565545898236387244792319596161 

noncomputable def Ns168p767 := nat_lit 141608655357051345195761441408488897343330678948108306780758898850470688541985158092707616385 

noncomputable def Ns168p768 := BSN.cos_dyadic_bound_t 14771231 8388608 4 3 8388608 2250000 Ns168p765 Ns168p187 Ns168p766 Ns168p767 Ns168p190 Ns168p766 1584854 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 14771231) (BSN.cosEvenQ 8388608) 0 3 Ns168p765 Ns168p187 Ns168p766 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 14771231) (BSN.cosOddQ 8388608) 0 3 Ns168p767 Ns168p190 Ns168p766 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p769 := @Ns168p756 644527216 37748736000000 792427 4194304 40282951 2359296000000 (@Ns168p757 279 16777216 Bool.true 1584854 8388608 1 2250000 (@Ns168p760 Ns168p181 14771231 8388608 279 16777216 (@Ns168p761 281474976710656 743275899 281474976710656 Ns168p758 Ns168p178 Ns168p759 Ns168p181 RS169to186.d39 (@Ns168p762 0 1 1262137581068144 78883598816759 281474976710656 743275899 281474976710656 (@Ns168p763 1028299271026757337088 61291412772343 281474976710656 743275899 281474976710656 (@Ns168p764 290291067 281474976710656 (Ns168p747 rfl rfl) (Ns168p747 rfl rfl) rfl) (Ns168p747 rfl rfl) rfl rfl) qz375 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 14771231 8388608) (BSN.cos_neg_of_bound 14771231 8388608 Bool.true 1584854 8388608 1 2250000 (Ns168p768 rfl rfl)) rfl rfl) 

noncomputable def Ns168p770 := @Ns168p732 1467961657957559638463 Ns168p449 (Ns168p733 qz27 (@Enclosure.Real.IsNear.of_eq qz694 (@Inv.inv Real Real.instInv (Real.sqrt qz91)) Bool.false 2908153 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz87 (BSN.t_div_two_pi_nonneg qz86 434981 1000 qz89)) Ns168p737) rfl) (@Ns168p738 70368744177664 125818230683893 2473901162496000000 (BSN.correction_mk qz88 (BSN.cos_two_pi_p_ne_zero_mk qz86 434981 1000 8 qz89 rfl rfl (@BSN.floor_sqrt_eq_dec qz86 434981 1000 8 qz89 rfl rfl rfl))) (@Ns168p739 16777216 792427 4194304 40282951 2359296000000 31050628354951 70368744177664 125818230683893 2473901162496000000 Ns168p755 (Ns168p769 rfl) rfl)) 

noncomputable def Ns168p771 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz86) (hardyZApproximantRS₀ qz86) Bool.false 3448102409308625414321 590295810358705651712 120089048498478263638463 Ns168p449 (@Eq.refl Real (hardyZApproximantRS₀ qz86)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz86) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz86) qz86 8) (@HMul.hMul Real Real Real qz5 qz691 (Zeta.RiemannSiegel.correction qz88))) Bool.false 3448102409308625414321 590295810358705651712 120089048498478263638463 Ns168p449 (BSN.hardyZApproximantRS₀_eq qz86 8 (@BSN.floor_sqrt_eq_dec qz86 434981 1000 8 qz89 rfl rfl rfl)) (@Ns168p667 3448102409308625414321 590295810358705651712 120089048498478263638463 Ns168p449 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz86) qz86 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz86) qz86 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz86) qz86 8)) Bool.false 201134889 33554432 47949 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz86) qz86 8) (Ns168p731 (Ns168p730 rfl rfl rfl rfl) rfl rfl)) (Ns168p770 rfl) rfl rfl)) 

theorem RS169to186.d48 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz86) Bool.false 3448102409308625414321 590295810358705651712 120089048498478263638463 Ns168p449 := Ns168p771 

noncomputable def Ns168p772 := nat_lit 27248295128658930295543693312 

noncomputable abbrev qz916 := (Enclosure.sfrac Bool.false 436463 1000)

noncomputable abbrev qz698 := qz916

noncomputable abbrev qz447 := qz698

noncomputable abbrev qz99 := qz447

noncomputable abbrev qz917 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 436463 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz699 := qz917

noncomputable abbrev qz448 := qz699

noncomputable abbrev qz100 := qz448

noncomputable abbrev qz918 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 436463 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz700 := qz918

noncomputable abbrev qz449 := qz700

noncomputable abbrev qz101 := qz449

noncomputable abbrev qz701 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz100 qz9))

noncomputable def Ns168p773 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz99) qz99 8) (@HMul.hMul Real Real Real qz5 qz701 (Zeta.RiemannSiegel.correction qz101)) 41138147 33554432 96219 67108864 88352540392827226689 590295810358705651712 1249029786512979813547 Ns168p449 Ns168p772 

noncomputable def Ns168p774 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz99) qz99 Real.sin BSN.quadSignPos 7 8 436463 1000 127 134217728 67108864 2251799813685248 Bool.false 94872846008 1703 279097919 60 47453128 8 

noncomputable def Ns168p775 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz99) qz99 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 436463 1000 47 90 134217728 67108864 2251799813685248 Bool.false 94872846008 1703 

noncomputable def Ns168p776 := Ns168p775 240485871 61 54794152 8 261175631 61 50729528 8 Bool.true 157257407 64057 Bool.true 181389142 Bool.true 146069153 7074237752028440 1 Bool.false 131001985 Bool.false Bool.false 62275947 Bool.true Bool.true 127314170 

noncomputable def Ns168p777 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz99) qz99 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 436463 1000 64 2 134217728 67108864 2251799813685248 Bool.false 94872846008 1703 

noncomputable def Ns168p778 := Ns168p777 186065264 60 67108856 8 216015088 60 60023992 8 Bool.true 159160028 37618 Bool.false 169204982 Bool.false 168595225 7074237752028440 1 Bool.false 40959739 Bool.false Bool.false 41539984 Bool.true Bool.true 157257407 

noncomputable def Ns168p779 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz99) qz99 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 436463 1000 257 144 134217728 67108864 2251799813685248 Bool.false 94872846008 1703 

noncomputable def Ns168p780 := Ns168p779 93032624 60 94906264 8 147453232 60 77490640 16 Bool.true 134217704 1764 Bool.false 84568306 Bool.false 155631174 7074237752028440 1 Bool.false 79082669 Bool.true Bool.false 53654721 Bool.false Bool.true 159160028 

noncomputable def Ns168p781 := nat_lit 158456707343339700498723800191422287756712511301975046547 

noncomputable def Ns168p782 := nat_lit 224170562397130893549513734695062962013150758358220800 

noncomputable def Ns168p783 := nat_lit 7602909980027368861926866500640000 

noncomputable def Ns168p784 := nat_lit 19910345585317203425069874950909017920 

noncomputable abbrev qz450 := (@Eq.refl Real qz698)

noncomputable abbrev qz102 := qz450

noncomputable def Ns168p785 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz99 436463 1000 762000801476 16000000 872926 4000 2000 Ns168p783 Ns168p784 qz102 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns168p786 := nat_lit 50706146349868704159591616061255132082148003616632014895040 

noncomputable abbrev qz702 := (Real.log (Enclosure.sfrac Bool.false 762000801476 16000000))

noncomputable abbrev qz103 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 436463 4000) qz702) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 872926))))))

noncomputable abbrev qz703 := (Enclosure.sfrac Bool.false 436463 2000)

noncomputable abbrev qz451 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz103 qz703) (@HMul.hMul Real Real Real qz5 qz703 (Real.log Real.pi)))

noncomputable def Ns168p787 := @Enclosure.Real.IsNear.addLit_ft_p qz451 (Enclosure.sfrac Bool.true Ns168p783 Ns168p784) 2546724943821758213387 3602879701896396800 46732140296234687 3686400000000000000000 Ns168p783 Ns168p784 0 1 Ns168p786 

noncomputable def Ns168p788 := nat_lit 854539089501710060915355811840000 

noncomputable abbrev qz452 := (@HSub.hSub Real Real Real qz12 qz103 qz703)

noncomputable abbrev qz453 := (@HMul.hMul Real Real Real qz5 qz703 (Real.log Real.pi))

noncomputable def Ns168p789 := @Enclosure.Real.IsNear.subLit_ff_p qz452 qz453 17233911847138740396343 18014398509481984000 44446311785401 7200000000000000000 16764875978343 67108864000 436463 67108864000 Ns168p788 2546724943821758213387 3602879701896396800 

noncomputable def Ns168p790 := nat_lit 34467823694277480792686000 

noncomputable abbrev qz454 := qz703

noncomputable def Ns168p791 := @Enclosure.Real.IsNear.subLit_ff_p qz103 qz454 21165221055460757987639 18014398509481984000 44446311785401 7200000000000000000 436463 2000 0 1 Ns168p790 17233911847138740396343 18014398509481984000 44446311785401 7200000000000000000 

noncomputable def Ns168p792 := nat_lit 47659840829293622863216130001020649472 

noncomputable def Ns168p793 := nat_lit 26042956020544173544308736 

noncomputable def Ns168p794 := nat_lit 128887078685728571565595100373184919422441019290766249424069557311081224080579946690617782374408204540958539895096471867883520 

noncomputable def Ns168p795 := nat_lit 1498112027790917397000480918590624735782544943938118368737318401361558101247414688046273060042086666391494622521376195477504 

noncomputable def Ns168p796 := nat_lit 544449384771522603113481809666713827620652357630341721373554611361474838387126674179972714210063924349406519697080320 

noncomputable def Ns168p797 := BSN.log_dyadic_bound 237712801476 1286288801476 6 5 Ns168p794 67108864 18000000 Ns168p795 Ns168p796 25092437 1524001602952 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 237712801476) (BSN.artanhQ 1286288801476) 0 5 Ns168p795 Ns168p794 Ns168p796 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns168p798 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 436463 4000) qz702 436463 4000 0 1 48508785703301753 4503599627370496 100000027 1800000000000000 21172290134420193019639 18014398509481984000 43646311784501 7200000000000000000 (Enclosure.Real.IsNear.const Bool.false 436463 4000) (BSN.isNear_log_sfrac 762000801476 16000000 48508785703301753 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 762000801476) qz353)) Bool.false Ns168p793 Ns168p89 1000000270000000 18000000000000000000000 48508785703301753 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 762000801476 16000000 15 1524001602952 1048576000000 25092437 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns168p797 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p799 := BSN.arctan_dyadic_bound_f 1000 872926 1 0 8388608 2250000 0 1 1 0 1 1 9609 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 872926) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 872926) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz455 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 872926)))

noncomputable def Ns168p800 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz455 884279719003555 562949953421312 1 2000000000000000 9609 8388608 1 2250000 7412466538968548114432 883634869929379 562949953421312 8000000009 18000000000000000 qz16 (Ns168p799 rfl) rfl rfl 

noncomputable def Ns168p801 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 436463 4000) qz702) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz455)) 21172290134420193019639 18014398509481984000 43646311784501 7200000000000000000 883634869929379 2251799813685248 8000000009 72000000000000000 Ns168p792 21165221055460757987639 18014398509481984000 44446311785401 7200000000000000000 (Ns168p798 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz455) 1 4 0 1 883634869929379 562949953421312 8000000009 18000000000000000 883634869929379 2251799813685248 8000000009 72000000000000000 qz356 Ns168p800 rfl) 

noncomputable def Ns168p802 := @Ns168p787 Ns168p781 Ns168p782 46732140296234687 3686400000000000000000 (@Ns168p789 46732140296234687 3686400000000000000000 (Ns168p791 (Ns168p801 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 436463 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz454 (Real.log Real.pi) 436463 2000 0 1 38410761 33554432 1 33554432 16764875978343 67108864000 436463 67108864000 (Enclosure.Real.IsNear.const Bool.false 436463 2000) RS169to186.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns168p783 Ns168p784) 

noncomputable def Ns168p803 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz99) Bool.false Ns168p781 Ns168p782 46732140296234687 3686400000000000000000 11859105751 16777216 213 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz99) (@HAdd.hAdd Real Real Real qz357 qz451 (Enclosure.sfrac Bool.true Ns168p783 Ns168p784)) Bool.false Ns168p781 Ns168p782 46732140296234687 3686400000000000000000 Ns168p785 (Ns168p802 rfl rfl)) 

noncomputable def Ns168p804 := nat_lit 3796595054113039583281152 

noncomputable def Ns168p805 := nat_lit 855910375386431205578273793808670420658994029541469649135995126265854706289141490459949266093209603217292641321055203831283097914904576 

noncomputable def Ns168p806 := nat_lit 608378314189527160879682263402919400662543571752467422141280128362806131745905208663761235255108117962970007569510635374235160576 

noncomputable def Ns168p807 := nat_lit 4274241592393435594997586587262708229322061194101662117316122595860014947331385051851896498795181441891659217131125067785732040763969536 

noncomputable def Ns168p808 := BSN.sin_dyadic_bound_f 53952860726 34359738368 4 3 16777216 4504395 Ns168p805 Ns168p103 Ns168p806 Ns168p807 Ns168p106 Ns168p806 16777213 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53952860726) qz358 0 3 Ns168p805 Ns168p103 Ns168p806 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53952860726) qz359 0 3 Ns168p807 Ns168p106 Ns168p806 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p809 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz99) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11859105751) qz370) Bool.false 11859105751 16777216 213 16777216 Bool.true 16777213 16777216 1 2250000 (Ns168p803 rfl) (Enclosure.sfrac_false_div 11859105751 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11859105751) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns168p804) qz385) 226375608064910080 72057594037927936 Bool.false 16777213 16777216 112 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 11859105751 16777216 226375608064910080 72057594037927936 112 Ns168p804 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777213 16777216 Ns168p804 Ns168p89 53952860726 34359738368 4504395 4500000 (Ns168p808 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p810 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz99) Bool.false Ns168p781 Ns168p782 46732140296234687 3686400000000000000000 94872846008 134217728 1703 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz99) (@HAdd.hAdd Real Real Real qz357 qz451 (Enclosure.sfrac Bool.true Ns168p783 Ns168p784)) Bool.false Ns168p781 Ns168p782 46732140296234687 3686400000000000000000 Ns168p785 (Ns168p802 rfl rfl)) 

noncomputable def Ns168p811 := Ns168p780 37618 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 257 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 79082669 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 144 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 53654721 134217728) qz102 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz99) qz99 1) Bool.true 16777213 16777216 31001701 2359296000000 134217704 134217728 1764 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz99) qz99 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz99)) Bool.true 16777213 16777216 31001701 2359296000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz99) qz99) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz99)) Bool.true 16777213 16777216 496027216 37748736000000 16777213 16777216 31001701 2359296000000 (Ns168p809 rfl rfl) rfl)) rfl) (Ns168p810 rfl) RS169to186.d7 

noncomputable def Ns168p812 := nat_lit 50196620446086308225821022758049547228172209804065977591217151197440 

noncomputable def Ns168p813 := nat_lit 2616140415717149547400261398644765475878079001181751209386230016 

noncomputable def Ns168p814 := nat_lit 131463103607648217587406887752627198834442461168456599427420199239936 

noncomputable def Ns168p815 := BSN.sin_dyadic_bound_f 84568306 134217728 3 2 134217728 67108864 Ns168p812 Ns168p112 Ns168p813 Ns168p814 Ns168p115 Ns168p813 79082669 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 84568306) qz361 0 2 Ns168p812 Ns168p112 Ns168p813 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 84568306) qz362 0 2 Ns168p814 Ns168p115 Ns168p813 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p816 := nat_lit 1234406806808284331774231194234408994622102632780373703546974518484075161315154608844199589452445655699456 

noncomputable def Ns168p817 := nat_lit 201910601538249377351059465319429245647484340385416928254042997955338693149279411199120393978187776 

noncomputable def Ns168p818 := nat_lit 7483367148683418390076976392512156781367469800316279678849131779413026963926042887525188780845641113210880 

noncomputable def Ns168p819 := BSN.cos_dyadic_bound_f 155631174 134217728 4 3 134217728 67108864 Ns168p816 Ns168p118 Ns168p817 Ns168p818 Ns168p121 Ns168p817 53654721 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 155631174) qz363 0 3 Ns168p816 Ns168p118 Ns168p817 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 155631174) qz364 0 3 Ns168p818 Ns168p121 Ns168p817 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p820 := nat_lit 1725480201994284227820664106660776398765413285108862057434936006356212947835709082139679192284345747705856 

noncomputable def Ns168p821 := nat_lit 550754117784516982147038191659827737204028738924038925000688685674655493893577011320336371574706176 

noncomputable def Ns168p822 := nat_lit 10457433843328781559521872586167908203579941206135980903567258139890780168511061250760872131183601363783680 

noncomputable def Ns168p823 := BSN.cos_dyadic_bound_f 169204982 134217728 4 3 134217728 67108864 Ns168p820 Ns168p118 Ns168p821 Ns168p822 Ns168p121 Ns168p821 40959739 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 169204982) qz363 0 3 Ns168p820 Ns168p118 Ns168p821 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 169204982) qz364 0 3 Ns168p822 Ns168p121 Ns168p821 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p824 := nat_lit 1700705537900892002136880474619370632812531578544535758136592484276335063773147287398553038595334775390625 

noncomputable def Ns168p825 := nat_lit 527403785992887690607846244468783029185004786003597749783390106102930758189956359922885894775390625 

noncomputable def Ns168p826 := nat_lit 10307432583141244874204894499745680503952555560407277060320387172828991785975504452789262478189830775390625 

noncomputable def Ns168p827 := BSN.cos_dyadic_bound_f 168595225 134217728 4 3 134217728 67108864 Ns168p824 Ns168p118 Ns168p825 Ns168p826 Ns168p121 Ns168p825 41539984 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 168595225) qz363 0 3 Ns168p824 Ns168p118 Ns168p825 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 168595225) qz364 0 3 Ns168p826 Ns168p121 Ns168p825 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p828 := Ns168p778 64057 BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 40959739 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 2 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 41539984 134217728) qz102 rfl rfl (Ns168p811 RS169to186.d9 RS169to186.d11 RS169to186.d13 RS169to186.d17 (Ns168p815 rfl rfl) (Ns168p819 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns168p810 rfl) RS169to186.d19 RS169to186.d21 RS169to186.d23 RS169to186.d25 RS169to186.d17 (Ns168p823 rfl rfl) (Ns168p827 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns168p829 := nat_lit 5922460719309913479340675899578772696091823483557003312875478463986541130091547641107962544491835664961536 

noncomputable def Ns168p830 := nat_lit 1268631346952423777156712561566256481335241242421363076201000415707460309927319216806740197983195136 

noncomputable def Ns168p831 := nat_lit 29592127247533531083704382446142463925726368517025996486769079856205014630368615751684683919637474693943296 

noncomputable def Ns168p832 := BSN.sin_dyadic_bound_f 181389142 134217728 4 3 134217728 67108864 Ns168p829 Ns168p144 Ns168p830 Ns168p831 Ns168p147 Ns168p830 131001985 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 181389142) qz361 0 3 Ns168p829 Ns168p144 Ns168p830 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 181389142) qz362 0 3 Ns168p831 Ns168p147 Ns168p830 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p833 := nat_lit 957637966922660401581453348925164100318741030904876982402908431193714215981171522722408157650429033371521 

noncomputable def Ns168p834 := nat_lit 94341359766282623350697574881650807356120748110058824839861745616743843536757594191821844417927041 

noncomputable def Ns168p835 := nat_lit 5806438512602497153129181665325653981407799273898849619314807674433073579266061836836940160356704954406785 

noncomputable def Ns168p836 := BSN.cos_dyadic_bound_f 146069153 134217728 4 3 134217728 67108864 Ns168p833 Ns168p118 Ns168p834 Ns168p835 Ns168p121 Ns168p834 62275947 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 146069153) qz363 0 3 Ns168p833 Ns168p118 Ns168p834 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 146069153) qz364 0 3 Ns168p835 Ns168p121 Ns168p834 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p837 := Ns168p776 86348 BSN.abs_quadSignPos (BSN.cos_quad_nat3 47 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131001985 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 90 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 62275947 134217728) qz102 rfl rfl (Ns168p828 rfl rfl) (Ns168p810 rfl) RS169to186.d27 RS169to186.d29 RS169to186.d31 RS169to186.d33 RS169to186.d17 (Ns168p832 rfl rfl) (Ns168p836 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns168p838 := nat_lit 779060297003969969450486384575413702815257521702308484493995679628065 

noncomputable def Ns168p839 := nat_lit 629213022279765524041369888291721205653232463528992803655918500641 

noncomputable def Ns168p840 := nat_lit 2039377290117182680569492598830754053992712085231760994849783864310561 

noncomputable def Ns168p841 := BSN.sin_dyadic_bound_f 167822317 134217728 3 2 134217728 67108864 Ns168p838 Ns168p112 Ns168p839 Ns168p840 Ns168p115 Ns168p839 127386365 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 167822317) qz361 0 2 Ns168p838 Ns168p112 Ns168p839 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 167822317) qz362 0 2 Ns168p840 Ns168p115 Ns168p839 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p842 := Ns168p774 Bool.true 127314170 86348 Bool.true 167822317 7074237752028440 1 Bool.false 127386365 Bool.false Bool.true 82276294 96219 BSN.abs_quadSignPos qz365 (BSN.sfrac_eq_quadSignPos_mul Bool.false 127386365 134217728) qz102 rfl (Ns168p837 rfl) (Ns168p810 rfl) RS169to186.d35 RS169to186.d37 RS169to186.d17 (Ns168p841 rfl rfl) rfl 

noncomputable def Ns168p843 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz99) qz99 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz99) qz99 8) 82276294 134217728 96219 134217728 82276294 134217728 96219 134217728 22085874497880064 41138147 33554432 96219 67108864 (Ns168p842 rfl rfl rfl rfl) 

noncomputable def Ns168p844 := @Enclosure.Real.IsNear.mulLit_ff qz701 (Zeta.RiemannSiegel.correction qz101) 5811363 16777216 1 16777216 15203411040203 35184372088832 53640238627087 1236950581248000000 88352540392827226689 590295810358705651712 

noncomputable abbrev qz704 := (@HPow.hPow Real Real Real qz7 qz100 qz9)

noncomputable def Ns168p845 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz704 1 1 0 1 5811363 16777216 1 16777216 5811363 16777216 1 16777216 

noncomputable def Ns168p846 := @Enclosure.Real.IsNear.sqrt_image qz100 1165433463951 16777216000 436463 16777216000 69915523 69915550 8388608 (@Enclosure.Real.IsNear.of_eq qz100 (@HMul.hMul Real Real Real qz5 qz99 qz3) Bool.false 1165433463951 16777216000 436463 16777216000 (BSN.t_div_two_pi_mk qz99 436463 1000 qz102) (@Enclosure.Real.IsNear.mulLit_ff qz99 qz3 436463 1000 0 1 2670177 16777216 1 16777216 1165433463951 16777216000 436463 16777216000 (Enclosure.Real.IsNear.const Bool.false 436463 1000) RS169to186.d40 rfl)) 

noncomputable abbrev qz919 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 436463 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz705 := qz919

noncomputable abbrev qz456 := qz705

noncomputable abbrev qz104 := qz456

noncomputable def Ns168p847 := @Enclosure.Real.IsNear.sqrt_image qz104 139831073 16777216 27 16777216 24217636 24217642 8388608 (@Enclosure.Real.IsNear.recentre' qz104 Bool.false 139831073 16777216 27 16777216 139831073 16777216 27 16777216 (Ns168p846 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns168p848 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz104) 24217639 8388608 3 8388608 2905681 2905682 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz104) Bool.false 48435278 16777216 6 16777216 24217639 8388608 3 8388608 (Ns168p847 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns168p849 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz104)) Bool.false 5811363 16777216 1 16777216 5811363 16777216 1 16777216 (Ns168p848 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz105 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz449))

noncomputable abbrev qz706 := (@HMul.hMul Real Real Real qz890 qz918 qz918)

noncomputable abbrev qz457 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz706 qz700) qz641)

noncomputable abbrev qz106 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz457))

noncomputable def Ns168p850 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz101) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz105) qz106) Bool.false 15203411040203 

noncomputable def Ns168p851 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz105) qz106 8276447 4194304 87 

noncomputable abbrev qz707 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz105))

noncomputable def Ns168p852 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz105) (@Neg.neg Real Real.instNeg qz707) Bool.true 8276447 4194304 87 2097152 (BSN.inv_eq_neg_inv_neg qz105) 

noncomputable def Ns168p853 := @Enclosure.Real.IsNear.recentre' qz707 Bool.false 33105788 16777216 696 16777216 8276447 4194304 

noncomputable def Ns168p854 := @Enclosure.Real.IsNear.recentre' qz105 Bool.true 8502289 16777216 401527216 37748736000000 8502289 16777216 25095451 2359296000000 

noncomputable abbrev qz107 := (@HMul.hMul Real Real Real qz342 qz340 qz449)

noncomputable def Ns168p855 := @Enclosure.Real.IsNear.cos_image qz107 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17634843) qz360) Bool.false 17634843 8388608 171 16777216 Bool.true 8502289 16777216 1 

noncomputable def Ns168p856 := nat_lit 728624036092407493681892349 

noncomputable def Ns168p857 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz101 884279719003555 140737488355328 1 500000000000000 5613345 16777216 27 16777216 4963767139270010441475 2361183241434822606848 Ns168p856 

noncomputable def Ns168p858 := @Enclosure.Real.IsNear.subLit_ff_p qz104 qz1 139831073 16777216 27 16777216 8 1 0 1 5613345 5613345 16777216 27 

noncomputable def Ns168p859 := @Ns168p858 16777216 (@Enclosure.Real.IsNear.recentre' qz104 Bool.false 139831073 16777216 27 16777216 139831073 16777216 27 16777216 (Ns168p846 rfl rfl rfl rfl rfl rfl) rfl) qz371 

noncomputable def Ns168p860 := @Enclosure.Real.IsNear.recentre' qz107 Bool.false 4963767139270010441475 2361183241434822606848 Ns168p856 Ns168p163 17634843 8388608 171 16777216 (@Ns168p857 Ns168p163 RS169to186.d39 (Ns168p859 rfl rfl) rfl) 

noncomputable def Ns168p861 := nat_lit 111178009841113562212175824706711216414161 

noncomputable def Ns168p862 := BSN.sin_dyadic_bound_f 18260166109 34359738368 2 1 16777216 4504395 Ns168p861 Ns168p750 Ns168p861 Ns168p861 Ns168p751 Ns168p861 8502289 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 18260166109) qz358 0 1 Ns168p861 Ns168p750 Ns168p861 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 18260166109) qz359 0 1 Ns168p861 Ns168p751 Ns168p861 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p863 := @Ns168p855 2250000 (Ns168p860 rfl) (Enclosure.sfrac_false_div 17634843 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17634843) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 642472478815021176979456) qz636) 226375608064910080 72057594037927936 Bool.false 8502289 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 17634843 8388608 226375608064910080 72057594037927936 0 642472478815021176979456 Ns168p101 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8502289 16777216 642472478815021176979456 Ns168p101 18260166109 34359738368 4504395 4500000 (Ns168p862 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p864 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz105) 8502289 16777216 25095451 2359296000000 16552546 16553242 8388608 (@Enclosure.Real.IsNear.neg qz105 Bool.true 8502289 16777216 25095451 2359296000000 (Ns168p854 (Ns168p863 rfl rfl) rfl)) 

noncomputable def Ns168p865 := Ns168p852 (@Enclosure.Real.IsNear.neg qz707 Bool.false 8276447 4194304 87 2097152 (@Ns168p853 87 2097152 (Ns168p864 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p866 := @Enclosure.Real.IsNear.recentre' qz106 Bool.true 1836949 8388608 

noncomputable abbrev qz108 := (@HMul.hMul Real Real Real qz342 qz340 qz457)

noncomputable def Ns168p867 := @Enclosure.Real.IsNear.cos_image qz108 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 30057501)) qz370) Bool.true 30057501 16777216 

noncomputable def Ns168p868 := nat_lit 70971269348863872957771848605 

noncomputable def Ns168p869 := nat_lit 20404338688260478393638107735372009 

noncomputable def Ns168p870 := @Enclosure.Real.IsNear.recentre' qz108 Bool.true Ns168p868 Ns168p178 Ns168p869 

noncomputable abbrev qz109 := qz457

noncomputable def Ns168p871 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz109 884279719003555 140737488355328 1 500000000000000 80258845502911 

noncomputable abbrev qz458 := (@HSub.hSub Real Real Real qz633 qz706 qz700)

noncomputable abbrev qz110 := qz458

noncomputable def Ns168p872 := @Enclosure.Real.IsNear.subLit_tf qz110 qz25 62666659458495 281474976710656 756106191 281474976710656 1 16 

noncomputable abbrev qz459 := qz706

noncomputable abbrev qz111 := qz459

noncomputable def Ns168p873 := @Enclosure.Real.IsNear.subLit_ff_n qz111 qz101 31509642089025 281474976710656 303121359 281474976710656 5613345 16777216 27 16777216 

noncomputable def Ns168p874 := @Enclosure.Real.IsNear.mulLit_ff qz101 qz101 5613345 16777216 27 16777216 5613345 16777216 27 16777216 31509642089025 281474976710656 

noncomputable def Ns168p875 := nat_lit 102885400600289827344606364862425203233928355101704425753552309455556185679623042431557331508081 

noncomputable def Ns168p876 := nat_lit 543794039184665488338274902755658509526464148426284848918998597354731274522037918573190001 

noncomputable def Ns168p877 := nat_lit 621632508008711272008182621516111855699159664922129679168867424283103205059805117847511362362225 

noncomputable def Ns168p878 := BSN.cos_dyadic_bound_t 30057501 16777216 4 3 8388608 2250000 Ns168p875 Ns168p169 Ns168p876 Ns168p877 Ns168p172 Ns168p876 1836949 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 30057501) qz642 0 3 Ns168p875 Ns168p169 Ns168p876 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 30057501) (BSN.cosOddQ 16777216) 0 3 Ns168p877 Ns168p172 Ns168p876 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p879 := @Ns168p866 163944304 9437184000000 1836949 8388608 10246519 589824000000 (@Ns168p867 71 4194304 Bool.true 1836949 8388608 1 2250000 (@Ns168p870 Ns168p181 30057501 16777216 71 4194304 (@Ns168p871 281474976710656 756106191 281474976710656 Ns168p868 Ns168p178 Ns168p869 Ns168p181 RS169to186.d39 (@Ns168p872 0 1 1284141528046576 80258845502911 281474976710656 756106191 281474976710656 (@Ns168p873 1051372081733613649920 62666659458495 281474976710656 756106191 281474976710656 (@Ns168p874 303121359 281474976710656 (Ns168p859 rfl rfl) (Ns168p859 rfl rfl) rfl) (Ns168p859 rfl rfl) rfl rfl) qz375 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 30057501 16777216) (BSN.cos_neg_of_bound 30057501 16777216 Bool.true 1836949 8388608 1 2250000 (Ns168p878 rfl rfl)) rfl rfl) 

noncomputable def Ns168p880 := @Ns168p844 1249029786512979813547 Ns168p449 (Ns168p845 qz27 (@Enclosure.Real.IsNear.of_eq qz704 (@Inv.inv Real Real.instInv (Real.sqrt qz104)) Bool.false 5811363 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz100 (BSN.t_div_two_pi_nonneg qz99 436463 1000 qz102)) Ns168p849) rfl) (@Ns168p850 35184372088832 53640238627087 1236950581248000000 (BSN.correction_mk qz101 (BSN.cos_two_pi_p_ne_zero_mk qz99 436463 1000 8 qz102 rfl rfl (@BSN.floor_sqrt_eq_dec qz99 436463 1000 8 qz102 rfl rfl rfl))) (@Ns168p851 2097152 1836949 8388608 10246519 589824000000 15203411040203 35184372088832 53640238627087 1236950581248000000 Ns168p865 (Ns168p879 rfl) rfl)) 

noncomputable def Ns168p881 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz99) (hardyZApproximantRS₀ qz99) Bool.true 812062475939361163841 590295810358705651712 120267177763614291813547 Ns168p449 (@Eq.refl Real (hardyZApproximantRS₀ qz99)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz99) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz99) qz99 8) (@HMul.hMul Real Real Real qz5 qz701 (Zeta.RiemannSiegel.correction qz101))) Bool.true 812062475939361163841 590295810358705651712 120267177763614291813547 Ns168p449 (BSN.hardyZApproximantRS₀_eq qz99 8 (@BSN.floor_sqrt_eq_dec qz99 436463 1000 8 qz102 rfl rfl rfl)) (@Ns168p773 812062475939361163841 590295810358705651712 120267177763614291813547 Ns168p449 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz99) qz99 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz99) qz99 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz99) qz99 8)) Bool.true 41138147 33554432 96219 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz99) qz99 8) (Ns168p843 (Ns168p842 rfl rfl rfl rfl) rfl rfl)) (Ns168p880 rfl) rfl rfl)) 

theorem RS169to186.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz99) Bool.true 812062475939361163841 590295810358705651712 120267177763614291813547 Ns168p449 := Ns168p881 

noncomputable def Ns168p882 := nat_lit 27670116110564327424000000 

noncomputable def Ns168p883 := nat_lit 223971783257469181900095488 

noncomputable abbrev qz920 := (Enclosure.sfrac Bool.false 437944 1000)

noncomputable abbrev qz708 := qz920

noncomputable abbrev qz460 := qz708

noncomputable abbrev qz112 := qz460

noncomputable abbrev qz921 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 437944 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz709 := qz921

noncomputable abbrev qz461 := qz709

noncomputable abbrev qz113 := qz461

noncomputable abbrev qz922 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 437944 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz710 := qz922

noncomputable abbrev qz462 := qz710

noncomputable abbrev qz114 := qz462

noncomputable abbrev qz711 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz113 qz9))

noncomputable def Ns168p884 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz112) qz112 8) (@HMul.hMul Real Real Real qz5 qz711 (Zeta.RiemannSiegel.correction qz114)) 7301191 8388608 96545 67108864 5411460442909461003 36893488147419103232 367067840355944182001 Ns168p882 Ns168p883 

noncomputable def Ns168p885 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz112) qz112 Real.sin BSN.quadSignPos 7 8 437944 1000 127 134217728 67108864 2251799813685248 Bool.false 95294502620 1708 279097919 60 47453128 8 

noncomputable def Ns168p886 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz112) qz112 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 437944 1000 47 90 134217728 67108864 2251799813685248 Bool.false 95294502620 1708 

noncomputable def Ns168p887 := Ns168p886 240485871 61 54794152 8 261175631 61 50729528 8 Bool.false 7022444 64274 Bool.true 115892104 Bool.true 111213650 7074237752028440 1 Bool.false 102018587 Bool.false Bool.false 90718243 Bool.true Bool.false 14383083 

noncomputable def Ns168p888 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz112) qz112 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 437944 1000 65 3 134217728 67108864 2251799813685248 Bool.false 95294502620 1708 

noncomputable def Ns168p889 := Ns168p888 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 28392492 37746 Bool.false 104470224 Bool.false 59504778 7074237752028440 1 Bool.false 94236320 Bool.true Bool.false 57574519 Bool.false Bool.false 7022444 

noncomputable def Ns168p890 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz112) qz112 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 437944 1000 258 145 134217728 67108864 2251799813685248 Bool.false 95294502620 1708 

noncomputable def Ns168p891 := Ns168p890 93032624 60 94906264 8 147453232 60 77490640 16 Bool.false 134217704 1772 Bool.false 157614888 Bool.false 148080835 7074237752028440 1 Bool.false 51830615 Bool.true Bool.false 119815367 Bool.true Bool.false 28392492 

noncomputable def Ns168p892 := nat_lit 24784689794534649144783189960964231532773705134693707 

noncomputable def Ns168p893 := nat_lit 34908044660782388796539767934462182104709988352000 

noncomputable def Ns168p894 := nat_lit 7732778584965317695647379947520000 

noncomputable def Ns168p895 := nat_lit 20319156267669976686907331421076193280 

noncomputable abbrev qz463 := (@Eq.refl Real qz708)

noncomputable abbrev qz115 := qz463

noncomputable def Ns168p896 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz112 437944 1000 767180788544 16000000 875888 4000 2000 Ns168p894 Ns168p895 qz115 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns168p897 := nat_lit 32485788607492455327050222745635037554637150794145735639040 

noncomputable abbrev qz712 := (Real.log (Enclosure.sfrac Bool.false 767180788544 16000000))

noncomputable abbrev qz116 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 437944 4000) qz712) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 875888))))))

noncomputable abbrev qz713 := (Enclosure.sfrac Bool.false 437944 2000)

noncomputable abbrev qz464 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz116 qz713) (@HMul.hMul Real Real Real qz5 qz713 (Real.log Real.pi)))

noncomputable def Ns168p898 := @Enclosure.Real.IsNear.addLit_ft_p qz464 (Enclosure.sfrac Bool.true Ns168p894 Ns168p895) 1598777311036794375143 2251799813685248000 1953721719853069 153600000000000000000 Ns168p894 Ns168p895 0 1 Ns168p897 

noncomputable def Ns168p899 := nat_lit 13411516141581741589679570944000 

noncomputable abbrev qz465 := (@HSub.hSub Real Real Real qz12 qz116 qz713)

noncomputable abbrev qz466 := (@HMul.hMul Real Real Real qz5 qz713 (Real.log Real.pi))

noncomputable def Ns168p900 := @Enclosure.Real.IsNear.subLit_ff_p qz465 qz466 2163221990768509357031 2251799813685248000 3716200985449 600000000000000000 2102720289423 8388608000 54743 8388608000 Ns168p899 1598777311036794375143 2251799813685248000 

noncomputable def Ns168p901 := nat_lit 4326443981537018714062000 

noncomputable abbrev qz467 := qz713

noncomputable def Ns168p902 := @Enclosure.Real.IsNear.subLit_ff_p qz116 qz467 2656303099570795482087 2251799813685248000 3716200985449 600000000000000000 437944 2000 0 1 Ns168p901 2163221990768509357031 2251799813685248000 3716200985449 600000000000000000 

noncomputable def Ns168p903 := nat_lit 5981462824705064033199439912240152576 

noncomputable def Ns168p904 := nat_lit 26059336657224033588215808 

noncomputable def Ns168p905 := nat_lit 134172540273142621361884329271908177412236426150752019651994495322168241965198697171035088277469780691864864453519847477739520 

noncomputable def Ns168p906 := nat_lit 1616437587420867553871371850112122082971672472670607679038081570029836574391234697386760860663717480641175406993947391688704 

noncomputable def Ns168p907 := nat_lit 675426377212238505165584691085941849700832422107896129450184742107127201940120042839685201165923815073076249697976320 

noncomputable def Ns168p908 := BSN.log_dyadic_bound 242892788544 1291468788544 6 5 Ns168p905 67108864 18000000 Ns168p906 Ns168p907 25547091 1534361577088 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 242892788544) (BSN.artanhQ 1291468788544) 0 5 Ns168p906 Ns168p905 Ns168p907 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns168p909 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 437944 4000) qz712 437944 4000 0 1 48539297016754809 4503599627370496 100000027 1800000000000000 2657186736588208509087 2251799813685248000 5474301478061 900000000000000000 (Enclosure.Real.IsNear.const Bool.false 437944 4000) (BSN.isNear_log_sfrac 767180788544 16000000 48539297016754809 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 767180788544) qz353)) Bool.false Ns168p904 Ns168p89 1000000270000000 18000000000000000000000 48539297016754809 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 767180788544 16000000 15 1534361577088 1048576000000 25547091 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns168p908 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p910 := BSN.arctan_dyadic_bound_f 1000 875888 1 0 8388608 2250000 0 1 1 0 1 1 9577 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 875888) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 875888) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz468 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 875888)))

noncomputable def Ns168p911 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz468 884279719003555 562949953421312 1 2000000000000000 9577 8388608 1 2250000 7412484553367057596416 883637017413027 562949953421312 8000000009 18000000000000000 qz16 (Ns168p910 rfl) rfl rfl 

noncomputable def Ns168p912 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 437944 4000) qz712) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz468)) 2657186736588208509087 2251799813685248000 5474301478061 900000000000000000 883637017413027 2251799813685248 8000000009 72000000000000000 Ns168p903 2656303099570795482087 2251799813685248000 3716200985449 600000000000000000 (Ns168p909 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz468) 1 4 0 1 883637017413027 562949953421312 8000000009 18000000000000000 883637017413027 2251799813685248 8000000009 72000000000000000 qz356 Ns168p911 rfl) 

noncomputable def Ns168p913 := @Ns168p898 Ns168p892 Ns168p893 1953721719853069 153600000000000000000 (@Ns168p900 1953721719853069 153600000000000000000 (Ns168p902 (Ns168p912 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 437944 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz467 (Real.log Real.pi) 437944 2000 0 1 38410761 33554432 1 33554432 2102720289423 8388608000 54743 8388608000 (Enclosure.Real.IsNear.const Bool.false 437944 2000) RS169to186.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns168p894 Ns168p895) 

noncomputable def Ns168p914 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz112) Bool.false Ns168p892 Ns168p893 1953721719853069 153600000000000000000 11911812827 16777216 107 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz112) (@HAdd.hAdd Real Real Real qz357 qz464 (Enclosure.sfrac Bool.true Ns168p894 Ns168p895)) Bool.false Ns168p892 Ns168p893 1953721719853069 153600000000000000000 Ns168p896 (Ns168p913 rfl rfl)) 

noncomputable def Ns168p915 := nat_lit 3796580277508791928356864 

noncomputable def Ns168p916 := nat_lit 855897023678661595307888216950925244513086352597567116526880988357127359390900529947280532056948426384315471770398562067679032207609856 

noncomputable def Ns168p917 := nat_lit 608349900627973851365682332568651330196441476432489767381761715027009331856754977414506739102923803958127587446736733474901856256 

noncomputable def Ns168p918 := nat_lit 4274174999233967925988587928032141955037726664341018927813526710709204619532145791823676704509485173417794836150078678906950902767292416 

noncomputable def Ns168p919 := BSN.sin_dyadic_bound_f 53952650738 34359738368 4 3 16777216 4504395 Ns168p916 Ns168p103 Ns168p917 Ns168p918 Ns168p106 Ns168p917 16777213 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53952650738) qz358 0 3 Ns168p916 Ns168p103 Ns168p917 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53952650738) qz359 0 3 Ns168p918 Ns168p106 Ns168p917 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p920 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz112) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11911812827) qz370) Bool.false 11911812827 16777216 107 8388608 Bool.false 16777213 16777216 1 2250000 (Ns168p914 rfl) (Enclosure.sfrac_false_div 11911812827 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11911812827) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns168p915) qz385) 226375608064910080 72057594037927936 Bool.false 16777213 16777216 112 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q3 11911812827 16777216 226375608064910080 72057594037927936 112 Ns168p915 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777213 16777216 Ns168p915 Ns168p89 53952650738 34359738368 4504395 4500000 (Ns168p919 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p921 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz112) Bool.false Ns168p892 Ns168p893 1953721719853069 153600000000000000000 95294502620 134217728 1708 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz112) (@HAdd.hAdd Real Real Real qz357 qz464 (Enclosure.sfrac Bool.true Ns168p894 Ns168p895)) Bool.false Ns168p892 Ns168p893 1953721719853069 153600000000000000000 Ns168p896 (Ns168p913 rfl rfl)) 

noncomputable def Ns168p922 := Ns168p891 37746 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 258 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 51830615 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 145 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 119815367 134217728) qz115 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz112) qz112 1) Bool.false 16777213 16777216 15571163 1179648000000 134217704 134217728 1772 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz112) qz112 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz112)) Bool.false 16777213 16777216 15571163 1179648000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz112) qz112) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz112)) Bool.false 16777213 16777216 249138608 18874368000000 16777213 16777216 15571163 1179648000000 (Ns168p920 rfl rfl) rfl)) rfl) (Ns168p921 rfl) RS169to186.d7 

noncomputable def Ns168p923 := nat_lit 1298629162881450696610778203117128399749752312826153278893515987918320271275916468118918463780670077403136 

noncomputable def Ns168p924 := nat_lit 235053570502033828139114629259336529303539184506395563513754854892861824901990586182820386471673856 

noncomputable def Ns168p925 := nat_lit 7872410345260848379019065799342881307462682771395308518098293282164048807866505467416917347155861926051840 

noncomputable def Ns168p926 := BSN.cos_dyadic_bound_f 157614888 134217728 4 3 134217728 67108864 Ns168p923 Ns168p118 Ns168p924 Ns168p925 Ns168p121 Ns168p924 51830615 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 157614888) qz363 0 3 Ns168p923 Ns168p118 Ns168p924 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 157614888) qz364 0 3 Ns168p925 Ns168p121 Ns168p924 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p927 := nat_lit 472095084542552406764292922915057494398505446398472957992293648030625 

noncomputable def Ns168p928 := nat_lit 231201601074049250593938387442649916850438743281393071593375390625 

noncomputable def Ns168p929 := nat_lit 1236065180733517366548376993102624385464042125459259301197236946590625 

noncomputable def Ns168p930 := BSN.sin_dyadic_bound_f 148080835 134217728 3 2 134217728 67108864 Ns168p927 Ns168p112 Ns168p928 Ns168p929 Ns168p115 Ns168p928 119815367 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 148080835) qz361 0 2 Ns168p927 Ns168p112 Ns168p928 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 148080835) qz362 0 2 Ns168p929 Ns168p115 Ns168p928 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p931 := nat_lit 116907973863661937106330405540664187950709820325262125342273956741120 

noncomputable def Ns168p932 := nat_lit 14188621621176336715972263468993967371057742795260727355900952576 

noncomputable def Ns168p933 := nat_lit 306164578541251740257134726084694502018972578792113239480712713732096 

noncomputable def Ns168p934 := BSN.sin_dyadic_bound_f 104470224 134217728 3 2 134217728 67108864 Ns168p931 Ns168p112 Ns168p932 Ns168p933 Ns168p115 Ns168p932 94236320 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 104470224) qz361 0 2 Ns168p931 Ns168p112 Ns168p932 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 104470224) qz362 0 2 Ns168p933 Ns168p115 Ns168p932 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p935 := nat_lit 12537396392305197247086783952656 

noncomputable def Ns168p936 := BSN.sin_dyadic_bound_f 59504778 134217728 2 1 134217728 67108864 Ns168p935 Ns168p394 Ns168p935 Ns168p935 Ns168p395 Ns168p935 57574519 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 59504778) qz361 0 1 Ns168p935 Ns168p394 Ns168p935 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 59504778) qz362 0 1 Ns168p935 Ns168p395 Ns168p935 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p937 := Ns168p889 64274 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 65 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 94236320 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 3 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 57574519 134217728) qz115 rfl rfl (Ns168p922 RS169to186.d9 RS169to186.d11 RS169to186.d13 RS169to186.d17 (Ns168p926 rfl rfl) (Ns168p930 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns168p921 rfl) RS169to186.d19 RS169to186.d21 RS169to186.d23 RS169to186.d25 RS169to186.d17 (Ns168p934 rfl rfl) (Ns168p936 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns168p938 := nat_lit 177058399175293572474914634653529743143295014224342452374513647616000 

noncomputable def Ns168p939 := nat_lit 32540991376378361149414086882494832058841150417195655040111476736 

noncomputable def Ns168p940 := nat_lit 463671693377826172468629753666196716599582151582126201348899372793856 

noncomputable def Ns168p941 := BSN.sin_dyadic_bound_f 115892104 134217728 3 2 134217728 67108864 Ns168p938 Ns168p112 Ns168p939 Ns168p940 Ns168p115 Ns168p939 102018587 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 115892104) qz361 0 2 Ns168p938 Ns168p112 Ns168p939 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 115892104) qz362 0 2 Ns168p940 Ns168p115 Ns168p939 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p942 := nat_lit 83426310183224177927609206561521010058614908362609865331670500000000 

noncomputable def Ns168p943 := nat_lit 23402634786591069844656623037103121095801096841925039062500000000 

noncomputable def Ns168p944 := nat_lit 250232125280099351643138306438488823933653122894145745916886500000000 

noncomputable def Ns168p945 := BSN.cos_dyadic_bound_f 111213650 134217728 3 2 134217728 67108864 Ns168p942 Ns168p124 Ns168p943 Ns168p944 Ns168p127 Ns168p943 90718243 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 111213650) qz363 0 2 Ns168p942 Ns168p124 Ns168p943 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 111213650) qz364 0 2 Ns168p944 Ns168p127 Ns168p943 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p946 := Ns168p887 86640 BSN.abs_quadSignPos (BSN.cos_quad_nat3 47 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 102018587 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 90 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 90718243 134217728) qz115 rfl rfl (Ns168p937 rfl rfl) (Ns168p921 rfl) RS169to186.d27 RS169to186.d29 RS169to186.d31 RS169to186.d33 RS169to186.d17 (Ns168p941 rfl rfl) (Ns168p945 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns168p947 := nat_lit 635706070932181151318735645075128902119759514382083536771126684469985 

noncomputable def Ns168p948 := nat_lit 419080339254374191239625061602095307722061389032862185387009952481 

noncomputable def Ns168p949 := nat_lit 1664265960463586409525157772716077065529724914466070343243276633688801 

noncomputable def Ns168p950 := BSN.sin_dyadic_bound_f 159509723 134217728 3 2 134217728 67108864 Ns168p947 Ns168p112 Ns168p948 Ns168p949 Ns168p115 Ns168p948 124525606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 159509723) qz361 0 2 Ns168p947 Ns168p112 Ns168p948 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 159509723) qz362 0 2 Ns168p949 Ns168p115 Ns168p948 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p951 := Ns168p885 Bool.false 14383083 86640 Bool.true 159509723 7074237752028440 1 Bool.false 124525606 Bool.false Bool.false 58409528 96545 BSN.abs_quadSignPos qz365 (BSN.sfrac_eq_quadSignPos_mul Bool.false 124525606 134217728) qz115 rfl (Ns168p946 rfl) (Ns168p921 rfl) RS169to186.d35 RS169to186.d37 RS169to186.d17 (Ns168p950 rfl rfl) rfl 

noncomputable def Ns168p952 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz112) qz112 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz112) qz112 8) 58409528 134217728 96545 134217728 58409528 134217728 96545 134217728 15679188283424768 7301191 8388608 96545 67108864 (Ns168p951 rfl rfl rfl rfl) 

noncomputable def Ns168p953 := @Enclosure.Real.IsNear.mulLit_ff qz711 (Zeta.RiemannSiegel.correction qz114) 1451611 4194304 1 8388608 3727899859473 8796093022208 377859239102861 9895604649984000000 5411460442909461003 36893488147419103232 

noncomputable abbrev qz714 := (@HPow.hPow Real Real Real qz7 qz113 qz9)

noncomputable def Ns168p954 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz714 1 1 0 1 1451611 4194304 1 8388608 1451611 4194304 1 8388608 

noncomputable def Ns168p955 := @Enclosure.Real.IsNear.sqrt_image qz113 146173499511 2097152000 54743 2097152000 70034041 70034068 8388608 (@Enclosure.Real.IsNear.of_eq qz113 (@HMul.hMul Real Real Real qz5 qz112 qz3) Bool.false 146173499511 2097152000 54743 2097152000 (BSN.t_div_two_pi_mk qz112 437944 1000 qz115) (@Enclosure.Real.IsNear.mulLit_ff qz112 qz3 437944 1000 0 1 2670177 16777216 1 16777216 146173499511 2097152000 54743 2097152000 (Enclosure.Real.IsNear.const Bool.false 437944 1000) RS169to186.d40 rfl)) 

noncomputable abbrev qz923 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 437944 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz715 := qz923

noncomputable abbrev qz469 := qz715

noncomputable abbrev qz117 := qz469

noncomputable def Ns168p956 := @Enclosure.Real.IsNear.sqrt_image qz117 140068109 16777216 27 16777216 24238154 24238159 8388608 (@Enclosure.Real.IsNear.recentre' qz117 Bool.false 140068109 16777216 27 16777216 140068109 16777216 27 16777216 (Ns168p955 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns168p957 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz117) 48476313 16777216 5 16777216 2903221 2903223 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz117) Bool.false 48476313 16777216 5 16777216 48476313 16777216 5 16777216 (Ns168p956 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns168p958 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz117)) Bool.false 5806444 16777216 2 16777216 1451611 4194304 1 8388608 (Ns168p957 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz118 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz462))

noncomputable abbrev qz716 := (@HMul.hMul Real Real Real qz890 qz922 qz922)

noncomputable abbrev qz470 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz716 qz710) qz641)

noncomputable abbrev qz119 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz470))

noncomputable def Ns168p959 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz114) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz118) qz119) Bool.false 3727899859473 

noncomputable def Ns168p960 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz118) qz119 14433057 8388608 265 

noncomputable abbrev qz717 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz118))

noncomputable def Ns168p961 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz118) (@Neg.neg Real Real.instNeg qz717) Bool.true 14433057 8388608 265 8388608 (BSN.inv_eq_neg_inv_neg qz118) 

noncomputable def Ns168p962 := @Enclosure.Real.IsNear.recentre' qz717 Bool.false 28866114 16777216 530 16777216 14433057 8388608 

noncomputable def Ns168p963 := @Enclosure.Real.IsNear.recentre' qz118 Bool.true 9751052 16777216 401527216 37748736000000 2437763 4194304 25095451 2359296000000 

noncomputable abbrev qz120 := (@HMul.hMul Real Real Real qz342 qz340 qz462)

noncomputable def Ns168p964 := @Enclosure.Real.IsNear.cos_image qz120 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 36759027) qz370) Bool.false 36759027 16777216 171 16777216 Bool.true 9751052 16777216 1 

noncomputable def Ns168p965 := nat_lit 728624036094443617417841661 

noncomputable def Ns168p966 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz114 884279719003555 140737488355328 1 500000000000000 5850381 16777216 27 16777216 5173373266743737104455 2361183241434822606848 Ns168p965 

noncomputable def Ns168p967 := @Enclosure.Real.IsNear.subLit_ff_p qz117 qz1 140068109 16777216 27 16777216 8 1 0 1 5850381 5850381 16777216 27 

noncomputable def Ns168p968 := @Ns168p967 16777216 (@Enclosure.Real.IsNear.recentre' qz117 Bool.false 140068109 16777216 27 16777216 140068109 16777216 27 16777216 (Ns168p955 rfl rfl rfl rfl rfl rfl) rfl) qz371 

noncomputable def Ns168p969 := @Enclosure.Real.IsNear.recentre' qz120 Bool.false 5173373266743737104455 2361183241434822606848 Ns168p965 Ns168p163 36759027 16777216 171 16777216 (@Ns168p966 Ns168p163 RS169to186.d39 (Ns168p968 rfl rfl) rfl) 

noncomputable def Ns168p970 := nat_lit 1499581615954125614219264 

noncomputable def Ns168p971 := nat_lit 206234457227557389292991520741954704997841 

noncomputable def Ns168p972 := BSN.sin_dyadic_bound_f 21310336477 34359738368 2 1 16777216 4504395 Ns168p971 Ns168p750 Ns168p971 Ns168p971 Ns168p751 Ns168p971 9751052 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 21310336477) qz358 0 1 Ns168p971 Ns168p750 Ns168p971 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 21310336477) qz359 0 1 Ns168p971 Ns168p751 Ns168p971 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p973 := @Ns168p964 2250000 (Ns168p969 rfl) (Enclosure.sfrac_false_div 36759027 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 36759027) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns168p970) qz385) 226375608064910080 72057594037927936 Bool.false 9751052 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 36759027 16777216 226375608064910080 72057594037927936 0 Ns168p970 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 9751052 16777216 Ns168p970 Ns168p89 21310336477 34359738368 4504395 4500000 (Ns168p972 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p974 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz118) 2437763 4194304 25095451 2359296000000 14432792 14433322 8388608 (@Enclosure.Real.IsNear.neg qz118 Bool.true 2437763 4194304 25095451 2359296000000 (Ns168p963 (Ns168p973 rfl rfl) rfl)) 

noncomputable def Ns168p975 := Ns168p961 (@Enclosure.Real.IsNear.neg qz717 Bool.false 14433057 8388608 265 8388608 (@Ns168p962 265 8388608 (Ns168p974 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p976 := @Enclosure.Real.IsNear.recentre' qz119 Bool.true 2066312 8388608 

noncomputable abbrev qz121 := (@HMul.hMul Real Real Real qz342 qz340 qz470)

noncomputable def Ns168p977 := @Enclosure.Real.IsNear.cos_image qz121 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7632297)) qz405) Bool.true 7632297 4194304 

noncomputable def Ns168p978 := nat_lit 72085009411134244844249448805 

noncomputable def Ns168p979 := nat_lit 20749758942286838192107454333328737 

noncomputable def Ns168p980 := @Enclosure.Real.IsNear.recentre' qz121 Bool.true Ns168p978 Ns168p178 Ns168p979 

noncomputable abbrev qz122 := qz470

noncomputable def Ns168p981 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz122 884279719003555 140737488355328 1 500000000000000 81518333918551 

noncomputable abbrev qz471 := (@HSub.hSub Real Real Real qz633 qz716 qz710)

noncomputable abbrev qz123 := qz471

noncomputable def Ns168p982 := @Enclosure.Real.IsNear.subLit_tf qz123 qz25 63926147874135 281474976710656 768906135 281474976710656 1 16 

noncomputable abbrev qz472 := qz716

noncomputable abbrev qz124 := qz472

noncomputable def Ns168p983 := @Enclosure.Real.IsNear.subLit_ff_n qz124 qz114 34226957845161 281474976710656 315921303 281474976710656 5850381 16777216 27 16777216 

noncomputable def Ns168p984 := @Enclosure.Real.IsNear.mulLit_ff qz114 qz114 5850381 16777216 27 16777216 5850381 16777216 27 16777216 34226957845161 281474976710656 

noncomputable def Ns168p985 := nat_lit 6529106707563212677392037755318893174714864540918764113579933905075468823393586705946721 

noncomputable def Ns168p986 := nat_lit 39071775216426872367956937880993483164688842265220724090551741936672293515511814241 

noncomputable def Ns168p987 := nat_lit 39438495062249551407957351749045628207956804604729936268887740678085359690966487451916385 

noncomputable def Ns168p988 := BSN.cos_dyadic_bound_t 7632297 4194304 4 3 8388608 2250000 Ns168p985 Ns168p426 Ns168p986 Ns168p987 Ns168p429 Ns168p986 2066312 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 7632297) (BSN.cosEvenQ 4194304) 0 3 Ns168p985 Ns168p426 Ns168p986 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 7632297) (BSN.cosOddQ 4194304) 0 3 Ns168p987 Ns168p429 Ns168p986 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p989 := @Ns168p976 667027216 37748736000000 258289 1048576 41689201 2359296000000 (@Ns168p977 289 16777216 Bool.true 2066312 8388608 1 2250000 (@Ns168p980 Ns168p181 7632297 4194304 289 16777216 (@Ns168p981 281474976710656 768906135 281474976710656 Ns168p978 Ns168p178 Ns168p979 Ns168p181 RS169to186.d39 (@Ns168p982 0 1 1304293342696816 81518333918551 281474976710656 768906135 281474976710656 (@Ns168p983 1072502790932303708160 63926147874135 281474976710656 768906135 281474976710656 (@Ns168p984 315921303 281474976710656 (Ns168p968 rfl rfl) (Ns168p968 rfl rfl) rfl) (Ns168p968 rfl rfl) rfl rfl) qz375 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7632297 4194304) (BSN.cos_neg_of_bound 7632297 4194304 Bool.true 2066312 8388608 1 2250000 (Ns168p988 rfl rfl)) rfl rfl) 

noncomputable def Ns168p990 := @Ns168p953 367067840355944182001 Ns168p882 (Ns168p954 qz27 (@Enclosure.Real.IsNear.of_eq qz714 (@Inv.inv Real Real.instInv (Real.sqrt qz117)) Bool.false 1451611 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz113 (BSN.t_div_two_pi_nonneg qz112 437944 1000 qz115)) Ns168p958) rfl) (@Ns168p959 8796093022208 377859239102861 9895604649984000000 (BSN.correction_mk qz114 (BSN.cos_two_pi_p_ne_zero_mk qz112 437944 1000 8 qz115 rfl rfl (@BSN.floor_sqrt_eq_dec qz112 437944 1000 8 qz115 rfl rfl rfl))) (@Ns168p960 8388608 258289 1048576 41689201 2359296000000 3727899859473 8796093022208 377859239102861 9895604649984000000 Ns168p975 (Ns168p989 rfl) rfl)) 

noncomputable def Ns168p991 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz112) (hardyZApproximantRS₀ qz112) Bool.false 26699517161544463861 36893488147419103232 40174199129218664182001 Ns168p882 (@Eq.refl Real (hardyZApproximantRS₀ qz112)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz112) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz112) qz112 8) (@HMul.hMul Real Real Real qz5 qz711 (Zeta.RiemannSiegel.correction qz114))) Bool.false 26699517161544463861 36893488147419103232 40174199129218664182001 Ns168p882 (BSN.hardyZApproximantRS₀_eq qz112 8 (@BSN.floor_sqrt_eq_dec qz112 437944 1000 8 qz115 rfl rfl rfl)) (@Ns168p884 26699517161544463861 36893488147419103232 40174199129218664182001 Ns168p882 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz112) qz112 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz112) qz112 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz112) qz112 8)) Bool.false 7301191 8388608 96545 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz112) qz112 8) (Ns168p952 (Ns168p951 rfl rfl rfl rfl) rfl rfl)) (Ns168p990 rfl) rfl rfl)) 

theorem RS169to186.d50 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz112) Bool.false 26699517161544463861 36893488147419103232 40174199129218664182001 Ns168p882 := Ns168p991 

noncomputable def Ns168p992 := nat_lit 5669848223013476475850457088 

noncomputable abbrev qz924 := (Enclosure.sfrac Bool.false 439424 1000)

noncomputable abbrev qz718 := qz924

noncomputable abbrev qz473 := qz718

noncomputable abbrev qz125 := qz473

noncomputable abbrev qz925 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 439424 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz719 := qz925

noncomputable abbrev qz474 := qz719

noncomputable abbrev qz126 := qz474

noncomputable abbrev qz926 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 439424 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz720 := qz926

noncomputable abbrev qz475 := qz720

noncomputable abbrev qz127 := qz475

noncomputable abbrev qz721 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz126 qz9))

noncomputable def Ns168p993 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz125) qz125 8) (@HMul.hMul Real Real Real qz5 qz721 (Zeta.RiemannSiegel.correction qz127)) 16794733 16777216 48437 33554432 42493221760805168915 295147905179352825856 683629083214130699 55340232221128654848000 Ns168p992 

noncomputable def Ns168p994 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz125) qz125 Real.sin BSN.quadSignPos 7 8 439424 1000 127 134217728 67108864 2251799813685248 Bool.false 95716210360 1714 279097919 60 47453128 8 

noncomputable def Ns168p995 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz125) qz125 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 439424 1000 47 90 134217728 67108864 2251799813685248 Bool.false 95716210360 1714 

noncomputable def Ns168p996 := Ns168p995 240485871 61 54794152 8 261175631 61 50729528 8 Bool.true 87155233 64494 Bool.true 50103454 Bool.true 76045844 7074237752028440 1 Bool.false 48947859 Bool.false Bool.false 113244669 Bool.true Bool.true 109974813 

noncomputable def Ns168p997 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz125) qz125 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 439424 1000 66 3 134217728 67108864 2251799813685248 Bool.false 95716210360 1714 

noncomputable def Ns168p998 := Ns168p997 186065264 60 67108856 8 216015088 60 60023992 8 Bool.true 79017743 37876 Bool.false 39972659 Bool.false 161510188 7074237752028440 1 Bool.false 128309274 Bool.true Bool.false 125258135 Bool.false Bool.true 87155233 

noncomputable def Ns168p999 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz125) qz125 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 439424 1000 260 146 134217728 67108864 2251799813685248 Bool.false 95716210360 1714 

noncomputable def Ns168p1000 := Ns168p999 93032624 60 94906264 8 147453232 60 77490640 16 Bool.true 134217720 1780 Bool.false 19976916 Bool.false 140729078 7074237752028440 1 Bool.false 132733792 Bool.false Bool.false 66955863 Bool.true Bool.true 79017743 

noncomputable def Ns168p1001 := nat_lit 3175428155484956447201501757297817893526850402969483 

noncomputable def Ns168p1002 := nat_lit 4452733250194950373865867922001474641066983424000 

noncomputable def Ns168p1003 := nat_lit 7864326347417362906842288619520000 

noncomputable def Ns168p1004 := nat_lit 20734654973237544176475461209199738880 

noncomputable abbrev qz722 := (@Eq.refl Real qz924)

noncomputable abbrev qz476 := qz722

noncomputable abbrev qz128 := qz476

noncomputable def Ns168p1005 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz125 439424 1000 772374807104 16000000 878848 4000 2000 Ns168p1003 Ns168p1004 qz128 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns168p1006 := nat_lit 4162097191957242114475952383325395869403513360180160757760 

noncomputable abbrev qz723 := (Real.log (Enclosure.sfrac Bool.false 772374807104 16000000))

noncomputable abbrev qz129 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 439424 4000) qz723) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 878848))))))

noncomputable abbrev qz724 := (Enclosure.sfrac Bool.false 439424 2000)

noncomputable abbrev qz477 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz129 qz724) (@HMul.hMul Real Real Real qz5 qz724 (Real.log Real.pi)))

noncomputable def Ns168p1007 := @Enclosure.Real.IsNear.addLit_ft_p qz477 (Enclosure.sfrac Bool.true Ns168p1003 Ns168p1004) 200731548749684371627 281474976710656000 367549969727017 28800000000000000000 Ns168p1003 Ns168p1004 0 1 Ns168p1006 

noncomputable def Ns168p1008 := nat_lit 105241142230874519831576576000 

noncomputable abbrev qz478 := (@HSub.hSub Real Real Real qz12 qz129 qz724)

noncomputable abbrev qz479 := (@HMul.hMul Real Real Real qz5 qz724 (Real.log Real.pi))

noncomputable def Ns168p1009 := @Enclosure.Real.IsNear.subLit_ff_p qz478 qz479 271525571200736653483 281474976710656000 11185602966337 1800000000000000000 131864142513 524288000 3433 524288000 Ns168p1008 200731548749684371627 281474976710656000 

noncomputable abbrev qz480 := qz724

noncomputable def Ns168p1010 := @Enclosure.Real.IsNear.subLit_ff_p qz129 qz480 66673800256757660911 56294995342131200 11185602966337 1800000000000000000 439424 2000 0 1 108610228480294661393200 271525571200736653483 281474976710656000 11185602966337 1800000000000000000 

noncomputable def Ns168p1011 := nat_lit 75068025497927170552024941633470464 

noncomputable def Ns168p1012 := nat_lit 26075651000917378738421760 

noncomputable def Ns168p1013 := nat_lit 139667394942147164575176117431884780834481704960660214278637029678540700689417176648313872605860964730111877505643649192427520 

noncomputable def Ns168p1014 := nat_lit 1742663726921547061727112562226428048340299593972530616102170998922761643774636737150421865140250387835944035629913346146304 

noncomputable def Ns168p1015 := nat_lit 834581024018418276437121739550268103525623999545492781345489860941927181315299513085965668642967912386656249126584320 

noncomputable def Ns168p1016 := BSN.log_dyadic_bound 248086807104 1296662807104 6 5 Ns168p1013 67108864 18000000 Ns168p1014 Ns168p1015 25999905 1544749614208 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 248086807104) (BSN.artanhQ 1296662807104) 0 5 Ns168p1014 Ns168p1013 Ns168p1015 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns168p1017 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 439424 4000) qz723 439424 4000 0 1 48569684849898105 4503599627370496 100000027 1800000000000000 33347945617940038893 28147497671065600 343300092691 56250000000000000 (Enclosure.Real.IsNear.const Bool.false 439424 4000) (BSN.isNear_log_sfrac 772374807104 16000000 48569684849898105 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 772374807104) qz353)) Bool.false Ns168p1012 Ns168p89 1000000270000000 18000000000000000000000 48569684849898105 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 772374807104 16000000 15 1544749614208 1048576000000 25999905 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns168p1016 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p1018 := BSN.arctan_dyadic_bound_f 1000 878848 1 0 8388608 2250000 0 1 1 0 1 1 9545 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 878848) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 878848) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz481 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 878848)))

noncomputable def Ns168p1019 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz481 884279719003555 562949953421312 1 2000000000000000 9545 8388608 1 2250000 7412502567765567078400 883639164896675 562949953421312 8000000009 18000000000000000 qz16 (Ns168p1018 rfl) rfl rfl 

noncomputable def Ns168p1020 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 439424 4000) qz723) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz481)) 33347945617940038893 28147497671065600 343300092691 56250000000000000 883639164896675 2251799813685248 8000000009 72000000000000000 Ns168p1011 66673800256757660911 56294995342131200 11185602966337 1800000000000000000 (Ns168p1017 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz481) 1 4 0 1 883639164896675 562949953421312 8000000009 18000000000000000 883639164896675 2251799813685248 8000000009 72000000000000000 qz356 Ns168p1019 rfl) 

noncomputable def Ns168p1021 := @Ns168p1007 Ns168p1001 Ns168p1002 367549969727017 28800000000000000000 (@Ns168p1009 367549969727017 28800000000000000000 (Ns168p1010 (Ns168p1020 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 439424 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz480 (Real.log Real.pi) 439424 2000 0 1 38410761 33554432 1 33554432 131864142513 524288000 3433 524288000 (Enclosure.Real.IsNear.const Bool.false 439424 2000) RS169to186.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns168p1003 Ns168p1004) 

noncomputable def Ns168p1022 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz125) Bool.false Ns168p1001 Ns168p1002 367549969727017 28800000000000000000 11964526295 16777216 215 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz125) (@HAdd.hAdd Real Real Real qz357 qz477 (Enclosure.sfrac Bool.true Ns168p1003 Ns168p1004)) Bool.false Ns168p1001 Ns168p1002 367549969727017 28800000000000000000 Ns168p1005 (Ns168p1021 rfl rfl)) 

noncomputable def Ns168p1023 := nat_lit 3797486685186725144166400 

noncomputable def Ns168p1024 := nat_lit 856716317970288034025540983105796041059523686407648010648294272444252103756689289439651414872364259932821742395883001695656986274041856 

noncomputable def Ns168p1025 := nat_lit 610095063752953663743643347717154518546949999437108785170291483576589741269881947949600903221415930104789267803957959445598048256 

noncomputable def Ns168p1026 := nat_lit 4278261317845905452630347685347070649813433892364920727622955051438968085488816395950600088301992765574687727110337843513518725848764416 

noncomputable def Ns168p1027 := BSN.sin_dyadic_bound_f 53965531566 34359738368 4 3 16777216 4504395 Ns168p1024 Ns168p103 Ns168p1025 Ns168p1026 Ns168p106 Ns168p1025 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53965531566) qz358 0 3 Ns168p1024 Ns168p103 Ns168p1025 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53965531566) qz359 0 3 Ns168p1026 Ns168p106 Ns168p1025 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1028 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz125) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11964526295) qz370) Bool.false 11964526295 16777216 215 16777216 Bool.true 16777215 16777216 1 2250000 (Ns168p1022 rfl) (Enclosure.sfrac_false_div 11964526295 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11964526295) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns168p1023) qz385) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 113 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 11964526295 16777216 226375608064910080 72057594037927936 113 Ns168p1023 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns168p1023 Ns168p89 53965531566 34359738368 4504395 4500000 (Ns168p1027 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p1029 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz125) Bool.false Ns168p1001 Ns168p1002 367549969727017 28800000000000000000 95716210360 134217728 1714 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz125) (@HAdd.hAdd Real Real Real qz357 qz477 (Enclosure.sfrac Bool.true Ns168p1003 Ns168p1004)) Bool.false Ns168p1001 Ns168p1002 367549969727017 28800000000000000000 Ns168p1005 (Ns168p1021 rfl rfl)) 

noncomputable def Ns168p1030 := Ns168p1000 37876 BSN.abs_quadSignPos (BSN.cos_quad_nat0 260 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 132733792 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 146 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66955863 134217728) qz128 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz125) qz125 1) Bool.true 16777215 16777216 31282951 2359296000000 134217720 134217728 1780 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz125) qz125 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz125)) Bool.true 16777215 16777216 31282951 2359296000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz125) qz125) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz125)) Bool.true 16777215 16777216 500527216 37748736000000 16777215 16777216 31282951 2359296000000 (Ns168p1028 rfl rfl) rfl)) rfl) (Ns168p1029 rfl) RS169to186.d7 

noncomputable def Ns168p1031 := nat_lit 159262589906754715026002555136 

noncomputable def Ns168p1032 := BSN.cos_dyadic_bound_f 19976916 134217728 2 1 134217728 67108864 Ns168p1031 Ns168p130 Ns168p1031 Ns168p1031 Ns168p131 Ns168p1031 132733792 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 19976916) qz363 0 1 Ns168p1031 Ns168p130 Ns168p1031 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 19976916) qz364 0 1 Ns168p1031 Ns168p131 Ns168p1031 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1033 := nat_lit 213991495355522919291144572282028729106171195024288829670274805391616 

noncomputable def Ns168p1034 := nat_lit 153840519869922989855162255706680652670435927114555168494649467136 

noncomputable def Ns168p1035 := nat_lit 641666805026828911893723392334672826013172713218637378673835117240576 

noncomputable def Ns168p1036 := BSN.cos_dyadic_bound_f 140729078 134217728 3 2 134217728 67108864 Ns168p1033 Ns168p124 Ns168p1034 Ns168p1035 Ns168p127 Ns168p1034 66955863 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 140729078) qz363 0 2 Ns168p1033 Ns168p124 Ns168p1034 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 140729078) qz364 0 2 Ns168p1035 Ns168p127 Ns168p1034 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1037 := nat_lit 2553007877021140335469651938961 

noncomputable def Ns168p1038 := BSN.cos_dyadic_bound_f 39972659 134217728 2 1 134217728 67108864 Ns168p1037 Ns168p130 Ns168p1037 Ns168p1037 Ns168p131 Ns168p1037 128309274 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 39972659) qz363 0 1 Ns168p1037 Ns168p130 Ns168p1037 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 39972659) qz364 0 1 Ns168p1037 Ns168p131 Ns168p1037 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1039 := nat_lit 668223955498237901086283220228950736343656918382988549219114752737280 

noncomputable def Ns168p1040 := nat_lit 463019606204713159972150262389633866441517520521542095334392528896 

noncomputable def Ns168p1041 := nat_lit 1749360708847244014871739238270049664163910424541268465514759145455616 

noncomputable def Ns168p1042 := BSN.sin_dyadic_bound_f 161510188 134217728 3 2 134217728 67108864 Ns168p1039 Ns168p112 Ns168p1040 Ns168p1041 Ns168p115 Ns168p1040 125258135 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 161510188) qz361 0 2 Ns168p1039 Ns168p112 Ns168p1040 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 161510188) qz362 0 2 Ns168p1041 Ns168p115 Ns168p1040 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1043 := Ns168p998 64494 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 128309274 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 3 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 125258135 134217728) qz128 rfl rfl (Ns168p1030 RS169to186.d9 RS169to186.d11 RS169to186.d13 RS169to186.d17 (Ns168p1032 rfl rfl) (Ns168p1036 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns168p1029 rfl) RS169to186.d19 RS169to186.d21 RS169to186.d23 RS169to186.d25 RS169to186.d17 (Ns168p1038 rfl rfl) (Ns168p1042 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns168p1044 := nat_lit 6301887762514336716068733373456 

noncomputable def Ns168p1045 := BSN.sin_dyadic_bound_f 50103454 134217728 2 1 134217728 67108864 Ns168p1044 Ns168p394 Ns168p1044 Ns168p1044 Ns168p395 Ns168p1044 48947859 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 50103454) qz361 0 1 Ns168p1044 Ns168p394 Ns168p1044 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 50103454) qz362 0 1 Ns168p1044 Ns168p395 Ns168p1044 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1046 := nat_lit 18233808529702657644045877572366873130427490684523333262526602346496 

noncomputable def Ns168p1047 := nat_lit 1118417295324485511961625131554006258787616444551736183520034816 

noncomputable def Ns168p1048 := nat_lit 54699188754517323961113709466837511378764896820680896315212766969856 

noncomputable def Ns168p1049 := BSN.cos_dyadic_bound_f 76045844 134217728 3 2 134217728 67108864 Ns168p1046 Ns168p124 Ns168p1047 Ns168p1048 Ns168p127 Ns168p1047 113244669 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 76045844) qz363 0 2 Ns168p1046 Ns168p124 Ns168p1047 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 76045844) qz364 0 2 Ns168p1048 Ns168p127 Ns168p1047 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1050 := Ns168p996 86936 BSN.abs_quadSignPos (BSN.cos_quad_nat3 47 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 48947859 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 90 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 113244669 134217728) qz128 rfl rfl (Ns168p1043 rfl rfl) (Ns168p1029 rfl) RS169to186.d27 RS169to186.d29 RS169to186.d31 RS169to186.d33 RS169to186.d17 (Ns168p1045 rfl rfl) (Ns168p1049 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns168p1051 := nat_lit 508658638568138001012566319413272091992758164860925593075256508047425 

noncomputable def Ns168p1052 := nat_lit 268381021642594213979133332076788919795280261775347887564070608961 

noncomputable def Ns168p1053 := nat_lit 1331766674595797231067421763544731154110888549450025990045806168662081 

noncomputable def Ns168p1054 := BSN.sin_dyadic_bound_f 150866903 134217728 3 2 134217728 67108864 Ns168p1051 Ns168p112 Ns168p1052 Ns168p1053 Ns168p115 Ns168p1052 121045043 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 150866903) qz361 0 2 Ns168p1051 Ns168p112 Ns168p1052 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 150866903) qz362 0 2 Ns168p1053 Ns168p115 Ns168p1052 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1055 := Ns168p994 Bool.true 109974813 86936 Bool.true 150866903 7074237752028440 1 Bool.false 121045043 Bool.false Bool.true 67178932 96874 BSN.abs_quadSignPos qz365 (BSN.sfrac_eq_quadSignPos_mul Bool.false 121045043 134217728) qz128 rfl (Ns168p1050 rfl) (Ns168p1029 rfl) RS169to186.d35 RS169to186.d37 RS169to186.d17 (Ns168p1054 rfl rfl) rfl 

noncomputable def Ns168p1056 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz125) qz125 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz125) qz125 8) 67178932 134217728 96874 134217728 67178932 134217728 96874 134217728 18033207245012992 16794733 16777216 48437 33554432 (Ns168p1055 rfl rfl rfl rfl) 

noncomputable def Ns168p1057 := @Enclosure.Real.IsNear.mulLit_ff qz721 (Zeta.RiemannSiegel.correction qz127) 1450387 4194304 1 8388608 29297850684545 70368744177664 70417292935073 1979120929996800000 42493221760805168915 295147905179352825856 

noncomputable abbrev qz725 := (@HPow.hPow Real Real Real qz7 qz126 qz9)

noncomputable def Ns168p1058 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz725 1 1 0 1 1450387 4194304 1 8388608 1450387 4194304 1 8388608 

noncomputable def Ns168p1059 := @Enclosure.Real.IsNear.sqrt_image qz126 9166717641 131072000 3433 131072000 70152278 70152306 8388608 (@Enclosure.Real.IsNear.of_eq qz126 (@HMul.hMul Real Real Real qz5 qz125 qz3) Bool.false 9166717641 131072000 3433 131072000 (BSN.t_div_two_pi_mk qz125 439424 1000 qz128) (@Enclosure.Real.IsNear.mulLit_ff qz125 qz3 439424 1000 0 1 2670177 16777216 1 16777216 9166717641 131072000 3433 131072000 (Enclosure.Real.IsNear.const Bool.false 439424 1000) RS169to186.d40 rfl)) 

noncomputable abbrev qz927 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 439424 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz726 := qz927

noncomputable abbrev qz482 := qz726

noncomputable abbrev qz130 := qz482

noncomputable def Ns168p1060 := @Enclosure.Real.IsNear.sqrt_image qz130 17538073 2097152 7 4194304 24258605 24258611 8388608 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 140304584 16777216 28 16777216 17538073 2097152 7 4194304 (Ns168p1059 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns168p1061 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz130) 1516163 524288 3 8388608 2900773 2900775 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz130) Bool.false 48517216 16777216 6 16777216 1516163 524288 3 8388608 (Ns168p1060 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns168p1062 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz130)) Bool.false 5801548 16777216 2 16777216 1450387 4194304 1 8388608 (Ns168p1061 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz131 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz475))

noncomputable abbrev qz727 := (@HMul.hMul Real Real Real qz890 qz926 qz926)

noncomputable abbrev qz483 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz727 qz720) qz641)

noncomputable abbrev qz132 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz483))

noncomputable def Ns168p1063 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz127) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz131) qz132) Bool.false 29297850684545 

noncomputable def Ns168p1064 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz131) qz132 25775273 16777216 437 

noncomputable abbrev qz728 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz131))

noncomputable def Ns168p1065 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz131) (@Neg.neg Real Real.instNeg qz728) Bool.true 25775273 16777216 437 16777216 (BSN.inv_eq_neg_inv_neg qz131) 

noncomputable def Ns168p1066 := @Enclosure.Real.IsNear.recentre' qz728 Bool.false 25775273 16777216 437 16777216 25775273 16777216 

noncomputable def Ns168p1067 := @Enclosure.Real.IsNear.recentre' qz131 Bool.true 10920349 16777216 415027216 37748736000000 10920349 16777216 25939201 2359296000000 

noncomputable abbrev qz133 := (@HMul.hMul Real Real Real qz342 qz340 qz475)

noncomputable def Ns168p1068 := @Enclosure.Real.IsNear.cos_image qz133 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9561211) qz405) Bool.false 9561211 4194304 177 16777216 Bool.true 10920349 16777216 1 

noncomputable def Ns168p1069 := nat_lit 188902527876379741913913457 

noncomputable def Ns168p1070 := nat_lit 18014398509481984000000000000000 

noncomputable def Ns168p1071 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz127 884279719003555 140737488355328 1 500000000000000 760857 2097152 7 4194304 672810414161887846635 295147905179352825856 Ns168p1069 

noncomputable def Ns168p1072 := @Enclosure.Real.IsNear.subLit_ff_p qz130 qz1 17538073 2097152 7 4194304 8 1 0 1 760857 760857 2097152 7 

noncomputable def Ns168p1073 := @Ns168p1072 4194304 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 140304584 16777216 28 16777216 17538073 2097152 7 4194304 (Ns168p1059 rfl rfl rfl rfl rfl rfl) rfl) qz371 

noncomputable def Ns168p1074 := @Enclosure.Real.IsNear.recentre' qz133 Bool.false 672810414161887846635 295147905179352825856 Ns168p1069 Ns168p1070 9561211 4194304 177 16777216 (@Ns168p1071 Ns168p1070 RS169to186.d39 (Ns168p1073 rfl rfl) rfl) 

noncomputable def Ns168p1075 := nat_lit 1482681817497953503066381844490014570267407163308336397839228466841737088595657812542625 

noncomputable def Ns168p1076 := nat_lit 704955687610872565255254336748118540842396593755240389471857687246053587015266059818106880 

noncomputable def Ns168p1077 := nat_lit 123726030394868401476168299616879033158668471117603880598471988069431179421661988001 

noncomputable def Ns168p1078 := nat_lit 3883013965588286530619086272607801308456190440663833492819867506128627581555278246773921 

noncomputable def Ns168p1079 := nat_lit 12924187606199330363012996173715506582110604218846073806984057599510982428613211096665292800 

noncomputable def Ns168p1080 := BSN.sin_dyadic_bound_f 24353289693 34359738368 3 2 16777216 4504395 Ns168p1075 Ns168p1076 Ns168p1077 Ns168p1078 Ns168p1079 Ns168p1077 10920349 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 24353289693) qz358 0 2 Ns168p1075 Ns168p1076 Ns168p1077 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 24353289693) qz359 0 2 Ns168p1078 Ns168p1079 Ns168p1077 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1081 := @Ns168p1068 2250000 (Ns168p1074 rfl) (Enclosure.sfrac_false_div 9561211 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9561211) qz405) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 428427603088857389596672) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 10920349 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 9561211 4194304 226375608064910080 72057594037927936 0 428427603088857389596672 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 10920349 16777216 428427603088857389596672 604462909807314587353088 24353289693 34359738368 4504395 4500000 (Ns168p1080 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p1082 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz131) 10920349 16777216 25939201 2359296000000 12887418 12887855 8388608 (@Enclosure.Real.IsNear.neg qz131 Bool.true 10920349 16777216 25939201 2359296000000 (Ns168p1067 (Ns168p1081 rfl rfl) rfl)) 

noncomputable def Ns168p1083 := Ns168p1065 (@Enclosure.Real.IsNear.neg qz728 Bool.false 25775273 16777216 437 16777216 (@Ns168p1066 437 16777216 (Ns168p1082 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p1084 := @Enclosure.Real.IsNear.recentre' qz132 Bool.true 2273330 8388608 

noncomputable abbrev qz134 := (@HMul.hMul Real Real Real qz342 qz340 qz483)

noncomputable def Ns168p1085 := @Enclosure.Real.IsNear.cos_image qz134 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 30957825)) qz370) Bool.true 30957825 16777216 

noncomputable def Ns168p1086 := nat_lit 1142142150705185579714303245 

noncomputable def Ns168p1087 := nat_lit 618970019642690137449562112 

noncomputable def Ns168p1088 := nat_lit 1367227193159232572866779338188603 

noncomputable def Ns168p1089 := @Enclosure.Real.IsNear.recentre' qz134 Bool.true Ns168p1086 Ns168p1087 Ns168p1088 

noncomputable def Ns168p1090 := nat_lit 75557863725914323419136000000000000000 

noncomputable abbrev qz135 := qz483

noncomputable def Ns168p1091 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz135 884279719003555 140737488355328 1 500000000000000 1291607311759 

noncomputable abbrev qz484 := (@HSub.hSub Real Real Real qz633 qz727 qz720)

noncomputable abbrev qz136 := qz484

noncomputable def Ns168p1092 := @Enclosure.Real.IsNear.subLit_tf qz136 qz25 1016729404815 4398046511104 50664173 17592186044416 1 16 

noncomputable abbrev qz485 := qz727

noncomputable abbrev qz137 := qz485

noncomputable def Ns168p1093 := @Enclosure.Real.IsNear.subLit_ff_n qz137 qz127 578903374449 4398046511104 21304045 17592186044416 760857 2097152 7 4194304 

noncomputable def Ns168p1094 := @Enclosure.Real.IsNear.mulLit_ff qz127 qz127 760857 2097152 7 4194304 760857 2097152 7 4194304 578903374449 4398046511104 

noncomputable def Ns168p1095 := nat_lit 115866049318664542218355767826198513785641283677450356321266666134644671312436095636508212890625 

noncomputable def Ns168p1096 := nat_lit 774899339869571003839941670801055687606701474051709430552427563927864294111728668212890625 

noncomputable def Ns168p1097 := nat_lit 699705195400899965926293534560503046091000601500012832351130294958674399512661400769564212890625 

noncomputable def Ns168p1098 := BSN.cos_dyadic_bound_t 30957825 16777216 4 3 8388608 2250000 Ns168p1095 Ns168p169 Ns168p1096 Ns168p1097 Ns168p172 Ns168p1096 2273330 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 30957825) qz642 0 3 Ns168p1095 Ns168p169 Ns168p1096 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 30957825) (BSN.cosOddQ 16777216) 0 3 Ns168p1097 Ns168p172 Ns168p1096 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1099 := @Ns168p1084 43798576 2359296000000 1136665 4194304 2737411 147456000000 (@Ns168p1085 19 1048576 Bool.true 2273330 8388608 1 2250000 (@Ns168p1089 Ns168p1090 30957825 16777216 19 1048576 (@Ns168p1091 4398046511104 50664173 17592186044416 Ns168p1086 Ns168p1087 Ns168p1088 Ns168p1090 RS169to186.d39 (@Ns168p1092 0 1 20665716988144 1291607311759 4398046511104 50664173 17592186044416 (@Ns168p1093 2132236104766586880 1016729404815 4398046511104 50664173 17592186044416 (@Ns168p1094 21304045 17592186044416 (Ns168p1073 rfl rfl) (Ns168p1073 rfl rfl) rfl) (Ns168p1073 rfl rfl) rfl rfl) qz375 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 30957825 16777216) (BSN.cos_neg_of_bound 30957825 16777216 Bool.true 2273330 8388608 1 2250000 (Ns168p1098 rfl rfl)) rfl rfl) 

noncomputable def Ns168p1100 := @Ns168p1057 683629083214130699 55340232221128654848000 (Ns168p1058 qz27 (@Enclosure.Real.IsNear.of_eq qz725 (@Inv.inv Real Real.instInv (Real.sqrt qz130)) Bool.false 1450387 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz126 (BSN.t_div_two_pi_nonneg qz125 439424 1000 qz128)) Ns168p1062) rfl) (@Ns168p1063 70368744177664 70417292935073 1979120929996800000 (BSN.correction_mk qz127 (BSN.cos_two_pi_p_ne_zero_mk qz125 439424 1000 8 qz128 rfl rfl (@BSN.floor_sqrt_eq_dec qz125 439424 1000 8 qz128 rfl rfl rfl))) (@Ns168p1064 16777216 1136665 4194304 2737411 147456000000 29297850684545 70368744177664 70417292935073 1979120929996800000 Ns168p1083 (Ns168p1099 rfl) rfl)) 

noncomputable def Ns168p1101 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz125) (hardyZApproximantRS₀ qz125) Bool.true 337949289263098029843 295147905179352825856 80569196155093298699 55340232221128654848000 (@Eq.refl Real (hardyZApproximantRS₀ qz125)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz125) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz125) qz125 8) (@HMul.hMul Real Real Real qz5 qz721 (Zeta.RiemannSiegel.correction qz127))) Bool.true 337949289263098029843 295147905179352825856 80569196155093298699 55340232221128654848000 (BSN.hardyZApproximantRS₀_eq qz125 8 (@BSN.floor_sqrt_eq_dec qz125 439424 1000 8 qz128 rfl rfl rfl)) (@Ns168p993 337949289263098029843 295147905179352825856 80569196155093298699 55340232221128654848000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz125) qz125 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz125) qz125 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz125) qz125 8)) Bool.true 16794733 16777216 48437 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz125) qz125 8) (Ns168p1056 (Ns168p1055 rfl rfl rfl rfl) rfl rfl)) (Ns168p1100 rfl) rfl rfl)) 

theorem RS169to186.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz125) Bool.true 337949289263098029843 295147905179352825856 80569196155093298699 55340232221128654848000 := Ns168p1101 

noncomputable def Ns168p1102 := nat_lit 36893488147419103232000000 

noncomputable def Ns168p1103 := nat_lit 23414084566944952810353983488 

noncomputable abbrev qz928 := (Enclosure.sfrac Bool.false 440903 1000)

noncomputable abbrev qz729 := qz928

noncomputable abbrev qz486 := qz729

noncomputable abbrev qz138 := qz486

noncomputable abbrev qz929 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 440903 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz730 := qz929

noncomputable abbrev qz487 := qz730

noncomputable abbrev qz139 := qz487

noncomputable abbrev qz930 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 440903 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz731 := qz930

noncomputable abbrev qz488 := qz731

noncomputable abbrev qz140 := qz488

noncomputable abbrev qz732 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz139 qz9))

noncomputable def Ns168p1104 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz138) qz138 8) (@HMul.hMul Real Real Real qz5 qz732 (Zeta.RiemannSiegel.correction qz140)) 10509953 4194304 97199 67108864 334224778395339334239 2361183241434822606848 417401102287867704137 Ns168p1102 Ns168p1103 

noncomputable def Ns168p1105 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.sin BSN.quadSignPos 7 8 440903 1000 127 134217728 67108864 2251799813685248 Bool.false 96137967327 1719 279097919 60 47453128 8 

noncomputable def Ns168p1106 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 440903 1000 46 90 134217728 67108864 2251799813685248 Bool.false 96137967327 1719 

noncomputable def Ns168p1107 := Ns168p1106 240485871 61 54794152 8 261175631 61 50729528 8 Bool.false 181764456 64711 Bool.true 194853804 Bool.true 40567635 7074237752028440 1 Bool.false 15937219 Bool.true Bool.false 128133426 Bool.true Bool.false 126828236 

noncomputable def Ns168p1108 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 440903 1000 66 4 134217728 67108864 2251799813685248 Bool.false 96137967327 1719 

noncomputable def Ns168p1109 := Ns168p1108 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 138430154 38005 Bool.false 186539100 Bool.false 52952126 7074237752028440 1 Bool.false 24157247 Bool.true Bool.false 123907068 Bool.false Bool.false 181764456 

noncomputable def Ns168p1110 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 440903 1000 261 147 134217728 67108864 2251799813685248 Bool.false 96137967327 1719 

noncomputable def Ns168p1111 := Ns168p1110 93032624 60 94906264 8 147453232 60 77490640 16 Bool.false 134217704 1788 Bool.false 93309918 Bool.false 133574000 7074237752028440 1 Bool.false 85973040 Bool.true Bool.false 112591218 Bool.false Bool.false 138430154 

noncomputable def Ns168p1112 := nat_lit 170622901217351167643925351839007739581947566336043813659 

noncomputable def Ns168p1113 := nat_lit 238205765971735810477925509080823910216748640292044800 

noncomputable def Ns168p1114 := nat_lit 7997567636189885074522095076640000 

noncomputable def Ns168p1115 := nat_lit 21156922078423417808139595759870835520 

noncomputable abbrev qz733 := (@Eq.refl Real qz928)

noncomputable abbrev qz489 := qz733

noncomputable abbrev qz141 := qz489

noncomputable def Ns168p1116 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz138 440903 1000 777582821636 16000000 881806 4000 2000 Ns168p1114 Ns168p1115 qz141 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns168p1117 := nat_lit 54599328389552373646056112588482476666223221227534020370880 

noncomputable abbrev qz734 := (Real.log (Enclosure.sfrac Bool.false 777582821636 16000000))

noncomputable abbrev qz142 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 440903 4000) qz734) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 881806))))))

noncomputable abbrev qz735 := (Enclosure.sfrac Bool.false 440903 2000)

noncomputable abbrev qz490 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz142 qz735) (@HMul.hMul Real Real Real qz5 qz735 (Real.log Real.pi)))

noncomputable def Ns168p1118 := @Enclosure.Real.IsNear.addLit_ft_p qz490 (Enclosure.sfrac Bool.true Ns168p1114 Ns168p1115) 2580685271772534554819 3602879701896396800 47203364841988247 3686400000000000000000 Ns168p1114 Ns168p1115 0 1 Ns168p1117 

noncomputable def Ns168p1119 := nat_lit 865934284650930301873244078080000 

noncomputable abbrev qz491 := (@HSub.hSub Real Real Real qz12 qz142 qz735)

noncomputable abbrev qz492 := (@HMul.hMul Real Real Real qz5 qz735 (Real.log Real.pi))

noncomputable def Ns168p1120 := @Enclosure.Real.IsNear.subLit_ff_p qz491 qz492 17449493483933500654543 18014398509481984000 44890311905281 7200000000000000000 16935419757183 67108864000 440903 67108864000 Ns168p1119 2580685271772534554819 3602879701896396800 

noncomputable def Ns168p1121 := nat_lit 34898986967867001309086000 

noncomputable abbrev qz493 := qz735

noncomputable def Ns168p1122 := @Enclosure.Real.IsNear.subLit_ff_p qz142 qz493 21420794656946568250319 18014398509481984000 44890311905281 7200000000000000000 440903 2000 0 1 Ns168p1121 17449493483933500654543 18014398509481984000 44890311905281 7200000000000000000 

noncomputable def Ns168p1123 := nat_lit 48235341417502238234143383390741594112 

noncomputable def Ns168p1124 := nat_lit 26091899519998570241458176 

noncomputable def Ns168p1125 := nat_lit 145379586040090864154003476389519968855404352917251465753272767393257982086122563236273387807737541040940140792956288651755520 

noncomputable def Ns168p1126 := nat_lit 1877246328028509610362449125817055612044099097630861126983906406749590988967309445082788346195699493545511240729593883131904 

noncomputable def Ns168p1127 := nat_lit 1027294398555442737910250418416767584857625774425502969940642300129831072312302686837262051472078760307336338677432320 

noncomputable def Ns168p1128 := BSN.log_dyadic_bound 253294821636 1301870821636 6 5 Ns168p1125 67108864 18000000 Ns168p1126 Ns168p1127 26450892 1555165643272 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 253294821636) (BSN.artanhQ 1301870821636) 0 5 Ns168p1126 Ns168p1125 Ns168p1127 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns168p1129 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 440903 4000) qz734 440903 4000 0 1 48599950075146873 4503599627370496 100000027 1800000000000000 21427863787982481746319 18014398509481984000 44090311904381 7200000000000000000 (Enclosure.Real.IsNear.const Bool.false 440903 4000) (BSN.isNear_log_sfrac 777582821636 16000000 48599950075146873 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 777582821636) qz353)) Bool.false Ns168p1124 Ns168p89 1000000270000000 18000000000000000000000 48599950075146873 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 777582821636 16000000 15 1555165643272 1048576000000 26450892 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns168p1128 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p1130 := BSN.arctan_dyadic_bound_f 1000 881806 1 0 8388608 2250000 0 1 1 0 1 1 9512 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 881806) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 881806) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz494 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 881806)))

noncomputable def Ns168p1131 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz494 884279719003555 562949953421312 1 2000000000000000 9512 8388608 1 2250000 7412521145114029981696 883641379489187 562949953421312 8000000009 18000000000000000 qz16 (Ns168p1130 rfl) rfl rfl 

noncomputable def Ns168p1132 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 440903 4000) qz734) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz494)) 21427863787982481746319 18014398509481984000 44090311904381 7200000000000000000 883641379489187 2251799813685248 8000000009 72000000000000000 Ns168p1123 21420794656946568250319 18014398509481984000 44890311905281 7200000000000000000 (Ns168p1129 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz494) 1 4 0 1 883641379489187 562949953421312 8000000009 18000000000000000 883641379489187 2251799813685248 8000000009 72000000000000000 qz356 Ns168p1131 rfl) 

noncomputable def Ns168p1133 := @Ns168p1118 Ns168p1112 Ns168p1113 47203364841988247 3686400000000000000000 (@Ns168p1120 47203364841988247 3686400000000000000000 (Ns168p1122 (Ns168p1132 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 440903 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz493 (Real.log Real.pi) 440903 2000 0 1 38410761 33554432 1 33554432 16935419757183 67108864000 440903 67108864000 (Enclosure.Real.IsNear.const Bool.false 440903 2000) RS169to186.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns168p1114 Ns168p1115) 

noncomputable def Ns168p1134 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz138) Bool.false Ns168p1112 Ns168p1113 47203364841988247 3686400000000000000000 12017245915 16777216 27 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz138) (@HAdd.hAdd Real Real Real qz357 qz490 (Enclosure.sfrac Bool.true Ns168p1114 Ns168p1115)) Bool.false Ns168p1112 Ns168p1113 47203364841988247 3686400000000000000000 Ns168p1116 (Ns168p1133 rfl rfl)) 

noncomputable def Ns168p1135 := BSN.cos_dyadic_bound_f 18860871 34359738368 1 0 16777216 4504395 0 1 1 0 1 1 16777213 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 18860871) qz682 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 18860871) qz683 0 0 rfl) rfl rfl 

noncomputable def Ns168p1136 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz138) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12017245915) qz370) Bool.false 12017245915 16777216 27 2097152 Bool.false 16777213 16777216 1 2250000 (Ns168p1134 rfl) (Enclosure.sfrac_false_div 12017245915 16777216) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12017245915) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1327215865362592563200) qz385) 226375608064910080 72057594037927936 Bool.false 16777213 16777216 114 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q0 12017245915 16777216 226375608064910080 72057594037927936 114 1327215865362592563200 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777213 16777216 1327215865362592563200 Ns168p89 18860871 34359738368 4504395 4500000 (Ns168p1135 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p1137 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz138) Bool.false Ns168p1112 Ns168p1113 47203364841988247 3686400000000000000000 96137967327 134217728 1719 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz138) (@HAdd.hAdd Real Real Real qz357 qz490 (Enclosure.sfrac Bool.true Ns168p1114 Ns168p1115)) Bool.false Ns168p1112 Ns168p1113 47203364841988247 3686400000000000000000 Ns168p1116 (Ns168p1133 rfl rfl)) 

noncomputable def Ns168p1138 := Ns168p1111 38005 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 261 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 85973040 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 147 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 112591218 134217728) qz141 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 1) Bool.false 16777213 16777216 3927947 294912000000 134217704 134217728 1788 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz138)) Bool.false 16777213 16777216 3927947 294912000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz138) qz138) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz138)) Bool.false 16777213 16777216 62847152 4718592000000 16777213 16777216 3927947 294912000000 (Ns168p1136 rfl rfl) rfl)) rfl) (Ns168p1137 rfl) RS169to186.d7 

noncomputable def Ns168p1139 := nat_lit 74398828469129629936625480715589482850314810852940382264415291736320 

noncomputable def Ns168p1140 := nat_lit 5746752086658350803431432653759224513117687978028580423882014976 

noncomputable def Ns168p1141 := nat_lit 194844770296723012504146893840342559196850885500974669181353764618496 

noncomputable def Ns168p1142 := BSN.sin_dyadic_bound_f 93309918 134217728 3 2 134217728 67108864 Ns168p1139 Ns168p112 Ns168p1140 Ns168p1141 Ns168p115 Ns168p1140 85973040 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 93309918) qz361 0 2 Ns168p1139 Ns168p112 Ns168p1140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 93309918) qz362 0 2 Ns168p1141 Ns168p115 Ns168p1140 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1143 := nat_lit 312499914062455454936580676358806630342073870256459218944000000000000 

noncomputable def Ns168p1144 := nat_lit 101338728811304453480799764553608377835776000000000000000000000000 

noncomputable def Ns168p1145 := nat_lit 818288083650260270004456667035216284950840308576440811520000000000000 

noncomputable def Ns168p1146 := BSN.sin_dyadic_bound_f 133574000 134217728 3 2 134217728 67108864 Ns168p1143 Ns168p112 Ns168p1144 Ns168p1145 Ns168p115 Ns168p1144 112591218 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 133574000) qz361 0 2 Ns168p1143 Ns168p112 Ns168p1144 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 133574000) qz362 0 2 Ns168p1145 Ns168p115 Ns168p1144 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1147 := nat_lit 2550633475611490062047720547571077178155069943980164872243456963155866881346552929974819179888640000000000 

noncomputable def Ns168p1148 := nat_lit 1775164176008422840951402501865514401033142546077594931664728935211570553281000000000000000000000000 

noncomputable def Ns168p1149 := nat_lit 15450974215584617878682226829610311293528248942996780288604785011193236210281024372831237211324416000000000 

noncomputable def Ns168p1150 := BSN.cos_dyadic_bound_f 186539100 134217728 4 3 134217728 67108864 Ns168p1147 Ns168p118 Ns168p1148 Ns168p1149 Ns168p121 Ns168p1148 24157247 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 186539100) qz363 0 3 Ns168p1147 Ns168p118 Ns168p1148 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 186539100) qz364 0 3 Ns168p1149 Ns168p121 Ns168p1148 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1151 := nat_lit 4286360381704108455983089793596824583670703999032096594246275891456 

noncomputable def Ns168p1152 := nat_lit 61811205246100591280239207434955539572503642958353207348101376 

noncomputable def Ns168p1153 := nat_lit 12858957522701833166766708902375603839932966989810373076324131471616 

noncomputable def Ns168p1154 := BSN.cos_dyadic_bound_f 52952126 134217728 3 2 134217728 67108864 Ns168p1151 Ns168p124 Ns168p1152 Ns168p1153 Ns168p127 Ns168p1152 123907068 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 52952126) qz363 0 2 Ns168p1151 Ns168p124 Ns168p1152 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 52952126) qz364 0 2 Ns168p1153 Ns168p127 Ns168p1152 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1155 := Ns168p1109 64711 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 24157247 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 4 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 123907068 134217728) qz141 rfl rfl (Ns168p1138 RS169to186.d9 RS169to186.d11 RS169to186.d13 RS169to186.d17 (Ns168p1142 rfl rfl) (Ns168p1146 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns168p1137 rfl) RS169to186.d19 RS169to186.d21 RS169to186.d23 RS169to186.d25 RS169to186.d17 (Ns168p1150 rfl rfl) (Ns168p1154 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns168p1156 := nat_lit 3037998776387238416001094057052001444495682794940199711169439902715581544429402846840100188329035585028096 

noncomputable def Ns168p1157 := nat_lit 2995757558968109985907714438101804759177917323814429790573817370650555440795412477551078038480879616 

noncomputable def Ns168p1158 := nat_lit 18398107676740489318760801091727082756090709670939069347716434793717530289181319206844031700277293282754560 

noncomputable def Ns168p1159 := BSN.cos_dyadic_bound_f 194853804 134217728 4 3 134217728 67108864 Ns168p1156 Ns168p118 Ns168p1157 Ns168p1158 Ns168p121 Ns168p1157 15937219 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 194853804) qz363 0 3 Ns168p1156 Ns168p118 Ns168p1157 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 194853804) qz364 0 3 Ns168p1158 Ns168p121 Ns168p1157 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1160 := nat_lit 2708437138535627407971320900625 

noncomputable def Ns168p1161 := BSN.cos_dyadic_bound_f 40567635 134217728 2 1 134217728 67108864 Ns168p1160 Ns168p130 Ns168p1160 Ns168p1160 Ns168p131 Ns168p1160 128133426 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 40567635) qz363 0 1 Ns168p1160 Ns168p130 Ns168p1160 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 40567635) qz364 0 1 Ns168p1160 Ns168p131 Ns168p1160 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1162 := Ns168p1107 87228 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 46 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 15937219 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 90 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 128133426 134217728) qz141 rfl rfl (Ns168p1155 rfl rfl) (Ns168p1137 rfl) RS169to186.d27 RS169to186.d29 RS169to186.d31 RS169to186.d33 RS169to186.d17 (Ns168p1159 rfl rfl) (Ns168p1161 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns168p1163 := nat_lit 397995661913749823903794305675673841766654200625945827856464205431040 

noncomputable def Ns168p1164 := nat_lit 164344547022921311357050859197271473916617331563626029044692009216 

noncomputable def Ns168p1165 := nat_lit 1042103509078926713815359384902350193669181716435897964148476750971136 

noncomputable def Ns168p1166 := BSN.sin_dyadic_bound_f 141895758 134217728 3 2 134217728 67108864 Ns168p1163 Ns168p112 Ns168p1164 Ns168p1165 Ns168p115 Ns168p1164 116901770 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 141895758) qz361 0 2 Ns168p1163 Ns168p112 Ns168p1164 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 141895758) qz362 0 2 Ns168p1165 Ns168p115 Ns168p1164 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1167 := Ns168p1105 Bool.false 126828236 87228 Bool.true 141895758 7074237752028440 1 Bool.false 116901770 Bool.false Bool.false 168159248 97199 BSN.abs_quadSignPos qz365 (BSN.sfrac_eq_quadSignPos_mul Bool.false 116901770 134217728) qz141 rfl (Ns168p1162 rfl) (Ns168p1137 rfl) RS169to186.d35 RS169to186.d37 RS169to186.d17 (Ns168p1166 rfl rfl) rfl 

noncomputable def Ns168p1168 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 8) 168159248 134217728 97199 134217728 168159248 134217728 97199 134217728 45139904417497088 10509953 4194304 97199 67108864 (Ns168p1167 rfl rfl rfl rfl) 

noncomputable def Ns168p1169 := @Enclosure.Real.IsNear.mulLit_ff qz732 (Zeta.RiemannSiegel.correction qz140) 5796677 16777216 1 16777216 57657995847507 140737488355328 215554596668687 6597069766656000000 334224778395339334239 2361183241434822606848 

noncomputable abbrev qz736 := (@HPow.hPow Real Real Real qz7 qz139 qz9)

noncomputable def Ns168p1170 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz736 1 1 0 1 5796677 16777216 1 16777216 5796677 16777216 1 16777216 

noncomputable def Ns168p1171 := @Enclosure.Real.IsNear.sqrt_image qz139 1177289049831 16777216000 440903 16777216000 70270237 70270265 8388608 (@Enclosure.Real.IsNear.of_eq qz139 (@HMul.hMul Real Real Real qz5 qz138 qz3) Bool.false 1177289049831 16777216000 440903 16777216000 (BSN.t_div_two_pi_mk qz138 440903 1000 qz141) (@Enclosure.Real.IsNear.mulLit_ff qz138 qz3 440903 1000 0 1 2670177 16777216 1 16777216 1177289049831 16777216000 440903 16777216000 (Enclosure.Real.IsNear.const Bool.false 440903 1000) RS169to186.d40 rfl)) 

noncomputable abbrev qz931 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 440903 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz737 := qz931

noncomputable abbrev qz495 := qz737

noncomputable abbrev qz143 := qz495

noncomputable def Ns168p1172 := @Enclosure.Real.IsNear.sqrt_image qz143 70270251 8388608 7 4194304 24278992 24278998 8388608 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 140540502 16777216 28 16777216 70270251 8388608 7 4194304 (Ns168p1171 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns168p1173 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz143) 24278995 8388608 3 8388608 2898338 2898339 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz143) Bool.false 48557990 16777216 6 16777216 24278995 8388608 3 8388608 (Ns168p1172 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns168p1174 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 5796677 16777216 1 16777216 5796677 16777216 1 16777216 (Ns168p1173 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz144 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz488))

noncomputable abbrev qz738 := (@HMul.hMul Real Real Real qz890 qz930 qz930)

noncomputable abbrev qz496 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz738 qz731) qz641)

noncomputable abbrev qz145 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz496))

noncomputable def Ns168p1175 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz140) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz144) qz145) Bool.false 57657995847507 

noncomputable def Ns168p1176 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz144) qz145 23453111 16777216 361 

noncomputable abbrev qz739 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz144))

noncomputable def Ns168p1177 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz144) (@Neg.neg Real Real.instNeg qz739) Bool.true 23453111 16777216 361 16777216 (BSN.inv_eq_neg_inv_neg qz144) 

noncomputable def Ns168p1178 := @Enclosure.Real.IsNear.recentre' qz739 Bool.false 23453111 16777216 361 16777216 23453111 16777216 

noncomputable def Ns168p1179 := @Enclosure.Real.IsNear.recentre' qz144 Bool.true 12001605 16777216 415027216 37748736000000 12001605 16777216 25939201 2359296000000 

noncomputable abbrev qz146 := (@HMul.hMul Real Real Real qz342 qz340 qz488)

noncomputable def Ns168p1180 := @Enclosure.Real.IsNear.cos_image qz146 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4965895) (@Nat.cast Real Real.instNatCast 2097152)) Bool.false 4965895 2097152 177 16777216 Bool.true 12001605 16777216 1 

noncomputable def Ns168p1181 := nat_lit 188902527876886371961182321 

noncomputable def Ns168p1182 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz140 884279719003555 140737488355328 1 500000000000000 3161387 8388608 7 4194304 2795550408021491730785 1180591620717411303424 Ns168p1181 

noncomputable def Ns168p1183 := @Enclosure.Real.IsNear.subLit_ff_p qz143 qz1 70270251 8388608 7 4194304 8 1 0 1 3161387 3161387 8388608 7 

noncomputable def Ns168p1184 := @Ns168p1183 4194304 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 140540502 16777216 28 16777216 70270251 8388608 7 4194304 (Ns168p1171 rfl rfl rfl rfl rfl rfl) rfl) qz371 

noncomputable def Ns168p1185 := @Enclosure.Real.IsNear.recentre' qz146 Bool.false 2795550408021491730785 1180591620717411303424 Ns168p1181 Ns168p1070 4965895 2097152 177 16777216 (@Ns168p1182 Ns168p1070 RS169to186.d39 (Ns168p1184 rfl rfl) rfl) 

noncomputable def Ns168p1186 := nat_lit 2372184619927582084376579598255442002529433199265946780245313749307517227008098207663265 

noncomputable def Ns168p1187 := nat_lit 316678552148033495795100568819553531619194805701971611095458912095054336896138347681 

noncomputable def Ns168p1188 := nat_lit 6212351763106856261993087832605211681859227301725390756129286219471534077999568224650401 

noncomputable def Ns168p1189 := BSN.sin_dyadic_bound_f 27389072861 34359738368 3 2 16777216 4504395 Ns168p1186 Ns168p1076 Ns168p1187 Ns168p1188 Ns168p1079 Ns168p1187 12001605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 27389072861) qz358 0 2 Ns168p1186 Ns168p1076 Ns168p1187 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 27389072861) qz359 0 2 Ns168p1188 Ns168p1079 Ns168p1187 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1190 := @Ns168p1180 2250000 (Ns168p1185 rfl) (Enclosure.sfrac_false_div 4965895 2097152) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4965895) (@Nat.cast Real Real.instNatCast 2097152)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 240916832685409991393280) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 12001605 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 4965895 2097152 226375608064910080 72057594037927936 0 240916832685409991393280 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 12001605 16777216 240916832685409991393280 302231454903657293676544 27389072861 34359738368 4504395 4500000 (Ns168p1189 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p1191 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz144) 12001605 16777216 25939201 2359296000000 11726375 11726736 8388608 (@Enclosure.Real.IsNear.neg qz144 Bool.true 12001605 16777216 25939201 2359296000000 (Ns168p1179 (Ns168p1190 rfl rfl) rfl)) 

noncomputable def Ns168p1192 := Ns168p1177 (@Enclosure.Real.IsNear.neg qz739 Bool.false 23453111 16777216 361 16777216 (@Ns168p1178 361 16777216 (Ns168p1191 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p1193 := @Enclosure.Real.IsNear.recentre' qz145 Bool.true 2458437 8388608 

noncomputable abbrev qz147 := (@HMul.hMul Real Real Real qz342 qz340 qz496)

noncomputable def Ns168p1194 := @Enclosure.Real.IsNear.cos_image qz147 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15671857)) qz360) Bool.true 15671857 8388608 

noncomputable def Ns168p1195 := nat_lit 18502063132372120581608673205 

noncomputable def Ns168p1196 := nat_lit 9903520314283042199192993792 

noncomputable def Ns168p1197 := nat_lit 27790198928880274926942219571953 

noncomputable def Ns168p1198 := @Enclosure.Real.IsNear.recentre' qz147 Bool.true Ns168p1195 Ns168p1196 Ns168p1197 

noncomputable def Ns168p1199 := nat_lit 1511157274518286468382720000000000000 

noncomputable abbrev qz148 := qz496

noncomputable def Ns168p1200 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz148 884279719003555 140737488355328 1 500000000000000 20923315026631 

noncomputable abbrev qz497 := (@HSub.hSub Real Real Real qz633 qz738 qz731)

noncomputable abbrev qz149 := qz497

noncomputable def Ns168p1201 := @Enclosure.Real.IsNear.subLit_tf qz149 qz25 16525268515527 70368744177664 25744943 8796093022208 1 16 

noncomputable abbrev qz498 := qz738

noncomputable abbrev qz150 := qz498

noncomputable def Ns168p1202 := @Enclosure.Real.IsNear.subLit_ff_n qz150 qz140 9994367763769 70368744177664 11064879 8796093022208 3161387 8388608 7 4194304 

noncomputable def Ns168p1203 := @Enclosure.Real.IsNear.mulLit_ff qz140 qz140 3161387 8388608 7 4194304 3161387 8388608 7 4194304 9994367763769 70368744177664 

noncomputable def Ns168p1204 := nat_lit 29734989333118347010329730090384986071413220665407700533558872100216090213686105907424111681 

noncomputable def Ns168p1205 := nat_lit 219505558715477585386220395791229241954501205754504999407463665744403632260739651316801 

noncomputable def Ns168p1206 := nat_lit 179525394304148093741060533172307724089779003277256916055702694957601092129636092713642470465 

noncomputable def Ns168p1207 := BSN.cos_dyadic_bound_t 15671857 8388608 4 3 8388608 2250000 Ns168p1204 Ns168p187 Ns168p1205 Ns168p1206 Ns168p190 Ns168p1205 2458437 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 15671857) (BSN.cosEvenQ 8388608) 0 3 Ns168p1204 Ns168p187 Ns168p1205 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 15671857) (BSN.cosOddQ 8388608) 0 3 Ns168p1206 Ns168p190 Ns168p1205 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1208 := @Ns168p1193 712027216 37748736000000 2458437 8388608 44501701 2359296000000 (@Ns168p1194 309 16777216 Bool.true 2458437 8388608 1 2250000 (@Ns168p1198 Ns168p1199 15671857 8388608 309 16777216 (@Ns168p1200 70368744177664 25744943 8796093022208 Ns168p1195 Ns168p1196 Ns168p1197 Ns168p1199 RS169to186.d39 (@Ns168p1201 0 1 334773040426096 20923315026631 70368744177664 25744943 8796093022208 (@Ns168p1202 138623999671497916416 16525268515527 70368744177664 25744943 8796093022208 (@Ns168p1203 11064879 8796093022208 (Ns168p1184 rfl rfl) (Ns168p1184 rfl rfl) rfl) (Ns168p1184 rfl rfl) rfl rfl) qz375 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 15671857 8388608) (BSN.cos_neg_of_bound 15671857 8388608 Bool.true 2458437 8388608 1 2250000 (Ns168p1207 rfl rfl)) rfl rfl) 

noncomputable def Ns168p1209 := @Ns168p1169 417401102287867704137 Ns168p1102 (Ns168p1170 qz27 (@Enclosure.Real.IsNear.of_eq qz736 (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 5796677 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz139 (BSN.t_div_two_pi_nonneg qz138 440903 1000 qz141)) Ns168p1174) rfl) (@Ns168p1175 140737488355328 215554596668687 6597069766656000000 (BSN.correction_mk qz140 (BSN.cos_two_pi_p_ne_zero_mk qz138 440903 1000 8 qz141 rfl rfl (@BSN.floor_sqrt_eq_dec qz138 440903 1000 8 qz141 rfl rfl rfl))) (@Ns168p1176 16777216 2458437 8388608 44501701 2359296000000 57657995847507 140737488355328 215554596668687 6597069766656000000 Ns168p1192 (Ns168p1208 rfl) rfl)) 

noncomputable def Ns168p1210 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz138) (hardyZApproximantRS₀ qz138) Bool.false 5582352773414838984097 2361183241434822606848 53853116456387579704137 Ns168p1102 (@Eq.refl Real (hardyZApproximantRS₀ qz138)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz138) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz138) qz138 8) (@HMul.hMul Real Real Real qz5 qz732 (Zeta.RiemannSiegel.correction qz140))) Bool.false 5582352773414838984097 2361183241434822606848 53853116456387579704137 Ns168p1102 (BSN.hardyZApproximantRS₀_eq qz138 8 (@BSN.floor_sqrt_eq_dec qz138 440903 1000 8 qz141 rfl rfl rfl)) (@Ns168p1104 5582352773414838984097 2361183241434822606848 53853116456387579704137 Ns168p1102 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz138) qz138 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 8)) Bool.false 10509953 4194304 97199 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz138) qz138 8) (Ns168p1168 (Ns168p1167 rfl rfl rfl rfl) rfl rfl)) (Ns168p1209 rfl) rfl rfl)) 

theorem RS169to186.d52 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz138) Bool.false 5582352773414838984097 2361183241434822606848 53853116456387579704137 Ns168p1102 := Ns168p1210 

noncomputable def Ns168p1211 := nat_lit 27800613850823875590868697088 

noncomputable abbrev qz932 := (Enclosure.sfrac Bool.false 442380 1000)

noncomputable abbrev qz740 := qz932

noncomputable abbrev qz499 := qz740

noncomputable abbrev qz151 := qz499

noncomputable abbrev qz933 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 442380 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz741 := qz933

noncomputable abbrev qz500 := qz741

noncomputable abbrev qz152 := qz500

noncomputable abbrev qz934 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 442380 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz742 := qz934

noncomputable abbrev qz501 := qz742

noncomputable abbrev qz153 := qz501

noncomputable abbrev qz743 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz152 qz9))

noncomputable def Ns168p1212 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz151) qz151 8) (@HMul.hMul Real Real Real qz5 qz743 (Zeta.RiemannSiegel.correction qz153)) 84837059 67108864 48761 33554432 41144096931766186981 295147905179352825856 1695296834218849319699 Ns168p339 Ns168p1211 

noncomputable def Ns168p1213 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.sin BSN.quadSignPos 7 8 442380 1000 127 134217728 67108864 2251799813685248 Bool.false 96559486264 1726 279097919 60 47453128 8 

noncomputable def Ns168p1214 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 442380 1000 46 90 134217728 67108864 2251799813685248 Bool.false 96559486264 1726 

noncomputable def Ns168p1215 := Ns168p1214 240485871 61 54794152 8 261175631 61 50729528 8 Bool.true 42228104 64924 Bool.true 128532498 Bool.true 4805105 7074237752028440 1 Bool.false 77235626 Bool.true Bool.false 134131723 Bool.true Bool.true 124456434 

noncomputable def Ns168p1216 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 442380 1000 67 4 134217728 67108864 2251799813685248 Bool.false 96559486264 1726 

noncomputable def Ns168p1217 := Ns168p1216 186065264 60 67108856 8 216015088 60 60023992 8 Bool.true 119377376 38127 Bool.false 122410928 Bool.false 155416778 7074237752028440 1 Bool.false 106132606 Bool.false Bool.false 53851172 Bool.false Bool.true 42228104 

noncomputable def Ns168p1218 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 442380 1000 262 148 134217728 67108864 2251799813685248 Bool.false 96559486264 1726 

noncomputable def Ns168p1219 := Ns168p1218 93032624 60 94906264 8 147453232 60 77490640 16 Bool.true 134217712 1788 Bool.false 166590955 Bool.false 126475800 7074237752028440 1 Bool.false 43441143 Bool.true Bool.false 78908535 Bool.false Bool.true 119377376 

noncomputable def Ns168p1220 := nat_lit 1897183935279171635582812614628160121496961187 

noncomputable def Ns168p1221 := nat_lit 2637086497047922659386622938947508900986880 

noncomputable def Ns168p1222 := nat_lit 8132424953738951743064064000000000 

noncomputable def Ns168p1223 := nat_lit 21585745774638147790464796753920000000 

noncomputable abbrev qz935 := (@Eq.refl Real (Enclosure.sfrac Bool.false 442380 1000))

noncomputable abbrev qz744 := qz935

noncomputable abbrev qz502 := qz744

noncomputable abbrev qz154 := qz502

noncomputable def Ns168p1224 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz151 442380 1000 782801257600 16000000 884760 4000 2000 Ns168p1222 Ns168p1223 qz154 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns168p1225 := nat_lit 2797511543605255326964992169026099788754559087902720000000 

noncomputable abbrev qz745 := (Real.log (Enclosure.sfrac Bool.false 782801257600 16000000))

noncomputable abbrev qz155 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 442380 4000) qz745) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 884760))))))

noncomputable abbrev qz746 := (Enclosure.sfrac Bool.false 442380 2000)

noncomputable abbrev qz503 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz155 qz746) (@HMul.hMul Real Real Real qz5 qz746 (Real.log Real.pi)))

noncomputable def Ns168p1226 := @Enclosure.Real.IsNear.addLit_ft_p qz503 (Enclosure.sfrac Bool.true Ns168p1222 Ns168p1223) 129600016502538051891 180143985094819840 2368006064780471 184320000000000000000 Ns168p1222 Ns168p1223 0 1 Ns168p1225 

noncomputable def Ns168p1227 := nat_lit 2174327470466645444794515456000 

noncomputable abbrev qz504 := (@HSub.hSub Real Real Real qz12 qz155 qz746)

noncomputable abbrev qz505 := (@HMul.hMul Real Real Real qz5 qz746 (Real.log Real.pi))

noncomputable def Ns168p1228 := @Enclosure.Real.IsNear.subLit_ff_p qz504 qz505 876064892095391311359 900719925474099200 1125950298629 180000000000000000 849607622559 3355443200 22119 3355443200 Ns168p1227 129600016502538051891 180143985094819840 

noncomputable def Ns168p1229 := nat_lit 1752129784190782622718000 

noncomputable abbrev qz506 := qz746

noncomputable def Ns168p1230 := @Enclosure.Real.IsNear.subLit_ff_p qz155 qz506 1075295132411007313407 900719925474099200 1125950298629 180000000000000000 442380 2000 0 1 Ns168p1229 876064892095391311359 900719925474099200 1125950298629 180000000000000000 

noncomputable def Ns168p1231 := nat_lit 2421349378819760346365892932388519936 

noncomputable def Ns168p1232 := nat_lit 26108071766116472597774336 

noncomputable def Ns168p1233 := nat_lit 151313245878346590850683740549115798456691328395949549580472621132774701230629706227653000564144290660352000000000000000000000 

noncomputable def Ns168p1234 := nat_lit 2020564428793331752117181412686390856413765619553635455802397123337610993413294738400308548344448706150400000000000000000000 

noncomputable def Ns168p1235 := nat_lit 1259679356394243393106298826961816710123547286061082959140670361452396816879448258568819186860032000000000000000000000 

noncomputable def Ns168p1236 := BSN.log_dyadic_bound 258513257600 1307089257600 6 5 Ns168p1233 67108864 18000000 Ns168p1234 Ns168p1235 26899762 1565602515200 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 258513257600) (BSN.artanhQ 1307089257600) 0 5 Ns168p1234 Ns168p1233 Ns168p1235 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns168p1237 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 442380 4000) qz745 442380 4000 0 1 48630073230930553 4503599627370496 100000027 1800000000000000 1075648589794952901807 900719925474099200 737300199071 120000000000000000 (Enclosure.Real.IsNear.const Bool.false 442380 4000) (BSN.isNear_log_sfrac 782801257600 16000000 48630073230930553 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 782801257600) qz353)) Bool.false Ns168p1232 Ns168p89 1000000270000000 18000000000000000000000 48630073230930553 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 782801257600 16000000 15 1565602515200 1048576000000 26899762 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns168p1236 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p1238 := BSN.arctan_dyadic_bound_f 1000 884760 1 0 8388608 2250000 0 1 1 0 1 1 9481 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 884760) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 884760) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz747 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 884760)))

noncomputable def Ns168p1239 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz747 884279719003555 562949953421312 1 2000000000000000 9481 8388608 1 2250000 7412538596562586042368 883643459863971 562949953421312 8000000009 18000000000000000 qz16 (Ns168p1238 rfl) rfl rfl 

noncomputable def Ns168p1240 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 442380 4000) qz745) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz747)) 1075648589794952901807 900719925474099200 737300199071 120000000000000000 883643459863971 2251799813685248 8000000009 72000000000000000 Ns168p1231 1075295132411007313407 900719925474099200 1125950298629 180000000000000000 (Ns168p1237 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz747) 1 4 0 1 883643459863971 562949953421312 8000000009 18000000000000000 883643459863971 2251799813685248 8000000009 72000000000000000 qz356 Ns168p1239 rfl) 

noncomputable def Ns168p1241 := @Ns168p1226 Ns168p1220 Ns168p1221 2368006064780471 184320000000000000000 (@Ns168p1228 2368006064780471 184320000000000000000 (Ns168p1230 (Ns168p1240 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 442380 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz506 (Real.log Real.pi) 442380 2000 0 1 38410761 33554432 1 33554432 849607622559 3355443200 22119 3355443200 (Enclosure.Real.IsNear.const Bool.false 442380 2000) RS169to186.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns168p1222 Ns168p1223) 

noncomputable def Ns168p1242 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz151) Bool.false Ns168p1220 Ns168p1221 2368006064780471 184320000000000000000 12069935783 16777216 27 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz151) (@HAdd.hAdd Real Real Real qz357 qz503 (Enclosure.sfrac Bool.true Ns168p1222 Ns168p1223)) Bool.false Ns168p1220 Ns168p1221 2368006064780471 184320000000000000000 Ns168p1224 (Ns168p1241 rfl rfl)) 

noncomputable def Ns168p1243 := nat_lit 3796784978741044042530816 

noncomputable def Ns168p1244 := nat_lit 856081999808947897269915943384044388952744131651090983776670140427819741758054865338318742142936154496355936447217503756911636079262161 

noncomputable def Ns168p1245 := nat_lit 608743624074983795016357759208937330797843659532782374889448475953905903834406370596150105151417130208707575686134263022366570961 

noncomputable def Ns168p1246 := nat_lit 4275097588471516063432006039596486774124369733087625345709563605227666063544365639649485619216028096670056715183300445569702858453498321 

noncomputable def Ns168p1247 := BSN.sin_dyadic_bound_f 53955559717 34359738368 4 3 16777216 4504395 Ns168p1244 Ns168p103 Ns168p1245 Ns168p1246 Ns168p106 Ns168p1245 16777214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53955559717) qz358 0 3 Ns168p1244 Ns168p103 Ns168p1245 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53955559717) qz359 0 3 Ns168p1246 Ns168p106 Ns168p1245 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1248 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz151) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12069935783) qz370) Bool.false 12069935783 16777216 27 2097152 Bool.true 16777214 16777216 1 2250000 (Ns168p1242 rfl) (Enclosure.sfrac_false_div 12069935783 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12069935783) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns168p1243) qz385) 226375608064910080 72057594037927936 Bool.false 16777214 16777216 114 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 12069935783 16777216 226375608064910080 72057594037927936 114 Ns168p1243 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777214 16777216 Ns168p1243 Ns168p89 53955559717 34359738368 4504395 4500000 (Ns168p1247 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p1249 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz151) Bool.false Ns168p1220 Ns168p1221 2368006064780471 184320000000000000000 96559486264 134217728 1726 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz151) (@HAdd.hAdd Real Real Real qz357 qz503 (Enclosure.sfrac Bool.true Ns168p1222 Ns168p1223)) Bool.false Ns168p1220 Ns168p1221 2368006064780471 184320000000000000000 Ns168p1224 (Ns168p1241 rfl rfl)) 

noncomputable def Ns168p1250 := Ns168p1219 38127 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 262 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 43441143 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 148 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 78908535 134217728) qz154 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 1) Bool.true 8388607 8388608 3927947 294912000000 134217712 134217728 1788 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz151)) Bool.true 8388607 8388608 3927947 294912000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz151) qz151) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz151)) Bool.true 16777214 16777216 62847152 4718592000000 8388607 8388608 3927947 294912000000 (Ns168p1248 rfl rfl) rfl)) rfl) (Ns168p1249 rfl) RS169to186.d7 

noncomputable def Ns168p1251 := nat_lit 1621151804885279775003565282537314501283304100325613794160831512681043565434958227125639132729729723140625 

noncomputable def Ns168p1252 := nat_lit 456895640317626062344923012035553564227632307023489882536292939375456762659662031956145234619140625 

noncomputable def Ns168p1253 := nat_lit 9825735632419248873580092029140064177193597205414474997885234971236032134067089842384222441976364116740625 

noncomputable def Ns168p1254 := BSN.cos_dyadic_bound_f 166590955 134217728 4 3 134217728 67108864 Ns168p1251 Ns168p118 Ns168p1252 Ns168p1253 Ns168p121 Ns168p1252 43441143 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 166590955) qz363 0 3 Ns168p1251 Ns168p118 Ns168p1252 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 166590955) qz364 0 3 Ns168p1253 Ns168p121 Ns168p1252 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1255 := nat_lit 139566868697861617773434797128153737647585290342935019552768000000000 

noncomputable def Ns168p1256 := nat_lit 65472583941483344159663313513410757975652127132160000000000000000 

noncomputable def Ns168p1257 := nat_lit 418569660925701886631985064757434391426804566774540738658304000000000 

noncomputable def Ns168p1258 := BSN.cos_dyadic_bound_f 126475800 134217728 3 2 134217728 67108864 Ns168p1255 Ns168p124 Ns168p1256 Ns168p1257 Ns168p127 Ns168p1256 78908535 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 126475800) qz363 0 2 Ns168p1255 Ns168p124 Ns168p1256 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 126475800) qz364 0 2 Ns168p1257 Ns168p127 Ns168p1256 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1259 := nat_lit 220394846872756276049540568034623414009649804398006188525548994560000 

noncomputable def Ns168p1260 := nat_lit 50415203291508141944234127235446766173103191707754160302101364736 

noncomputable def Ns168p1261 := nat_lit 577142974337603995518982251503727741927659701589156034640710631161856 

noncomputable def Ns168p1262 := BSN.sin_dyadic_bound_f 122410928 134217728 3 2 134217728 67108864 Ns168p1259 Ns168p112 Ns168p1260 Ns168p1261 Ns168p115 Ns168p1260 106132606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 122410928) qz361 0 2 Ns168p1259 Ns168p112 Ns168p1260 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 122410928) qz362 0 2 Ns168p1261 Ns168p115 Ns168p1260 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1263 := nat_lit 1227611563481166842962722166212377828080179098382161668740548705148795507355850593899701115127554043088896 

noncomputable def Ns168p1264 := nat_lit 198597974340852168161300978235931814033868801791609754701672646369851013239268505073557042577084416 

noncomputable def Ns168p1265 := nat_lit 7442201547135088803048026468019288472894156541446477483578946110523397029908586294466252962019960838492160 

noncomputable def Ns168p1266 := BSN.cos_dyadic_bound_f 155416778 134217728 4 3 134217728 67108864 Ns168p1263 Ns168p118 Ns168p1264 Ns168p1265 Ns168p121 Ns168p1264 53851172 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 155416778) qz363 0 3 Ns168p1263 Ns168p118 Ns168p1264 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 155416778) qz364 0 3 Ns168p1265 Ns168p121 Ns168p1264 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1267 := Ns168p1217 64924 BSN.abs_quadSignPos (BSN.cos_quad_nat3 67 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 106132606 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 4 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 53851172 134217728) qz154 rfl rfl (Ns168p1250 RS169to186.d9 RS169to186.d11 RS169to186.d13 RS169to186.d17 (Ns168p1254 rfl rfl) (Ns168p1258 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns168p1249 rfl) RS169to186.d19 RS169to186.d21 RS169to186.d23 RS169to186.d25 RS169to186.d17 (Ns168p1262 rfl rfl) (Ns168p1266 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns168p1268 := nat_lit 148873694149374680070236605954948279773910719967982983797118829281536 

noncomputable def Ns168p1269 := nat_lit 74490962236539384241101220250218158577997553268342755441182720256 

noncomputable def Ns168p1270 := nat_lit 446472100523650961442227615424344403004576164797412265880474122404096 

noncomputable def Ns168p1271 := BSN.cos_dyadic_bound_f 128532498 134217728 3 2 134217728 67108864 Ns168p1268 Ns168p124 Ns168p1269 Ns168p1270 Ns168p127 Ns168p1269 77235626 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 128532498) qz363 0 2 Ns168p1268 Ns168p124 Ns168p1269 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 128532498) qz364 0 2 Ns168p1270 Ns168p127 Ns168p1269 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1272 := nat_lit 533103493871172603424050625 

noncomputable def Ns168p1273 := BSN.cos_dyadic_bound_f 4805105 134217728 2 1 134217728 67108864 Ns168p1272 Ns168p130 Ns168p1272 Ns168p1272 Ns168p131 Ns168p1272 134131723 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 4805105) qz363 0 1 Ns168p1272 Ns168p130 Ns168p1272 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 4805105) qz364 0 1 Ns168p1272 Ns168p131 Ns168p1272 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1274 := Ns168p1215 87517 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 46 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 77235626 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 90 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 134131723 134217728) qz154 rfl rfl (Ns168p1267 rfl rfl) (Ns168p1249 rfl) RS169to186.d27 RS169to186.d29 RS169to186.d31 RS169to186.d33 RS169to186.d17 (Ns168p1271 rfl rfl) (Ns168p1273 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns168p1275 := nat_lit 303522226584384311071271236350666474250852101313075371640520609628160 

noncomputable def Ns168p1276 := nat_lit 95601506524756298410824963460415251301571684351059013233023123456 

noncomputable def Ns168p1277 := nat_lit 794784381472347399751140473834714379297743434997676639703748130635776 

noncomputable def Ns168p1278 := BSN.sin_dyadic_bound_f 132604448 134217728 3 2 134217728 67108864 Ns168p1275 Ns168p112 Ns168p1276 Ns168p1277 Ns168p115 Ns168p1276 112060527 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 132604448) qz361 0 2 Ns168p1275 Ns168p112 Ns168p1276 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 132604448) qz362 0 2 Ns168p1277 Ns168p115 Ns168p1276 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1279 := Ns168p1213 Bool.true 124456434 87517 Bool.true 132604448 7074237752028440 1 Bool.false 112060527 Bool.false Bool.true 84837059 97522 BSN.abs_quadSignPos qz365 (BSN.sfrac_eq_quadSignPos_mul Bool.false 112060527 134217728) qz154 rfl (Ns168p1274 rfl) (Ns168p1249 rfl) RS169to186.d35 RS169to186.d37 RS169to186.d17 (Ns168p1278 rfl rfl) rfl 

noncomputable def Ns168p1280 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 8) 84837059 134217728 97522 134217728 84837059 134217728 97522 134217728 22773274618363904 84837059 67108864 48761 33554432 (Ns168p1279 rfl rfl rfl rfl) 

noncomputable def Ns168p1281 := @Enclosure.Real.IsNear.mulLit_ff qz743 (Zeta.RiemannSiegel.correction qz153) 723979 2097152 1 8388608 56830511564239 140737488355328 145662413971993 4947802324992000000 41144096931766186981 295147905179352825856 

noncomputable abbrev qz748 := (@HPow.hPow Real Real Real qz7 qz152 qz9)

noncomputable def Ns168p1282 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz748 1 1 0 1 723979 2097152 1 8388608 723979 2097152 1 8388608 

noncomputable def Ns168p1283 := @Enclosure.Real.IsNear.sqrt_image qz152 59061645063 838860800 22119 838860800 70387840 70387867 8388608 (@Enclosure.Real.IsNear.of_eq qz152 (@HMul.hMul Real Real Real qz5 qz151 qz3) Bool.false 59061645063 838860800 22119 838860800 (BSN.t_div_two_pi_mk qz151 442380 1000 qz154) (@Enclosure.Real.IsNear.mulLit_ff qz151 qz3 442380 1000 0 1 2670177 16777216 1 16777216 59061645063 838860800 22119 838860800 (Enclosure.Real.IsNear.const Bool.false 442380 1000) RS169to186.d40 rfl)) 

noncomputable abbrev qz936 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 442380 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz749 := qz936

noncomputable abbrev qz507 := qz749

noncomputable abbrev qz156 := qz507

noncomputable def Ns168p1284 := @Enclosure.Real.IsNear.sqrt_image qz156 140775707 16777216 27 16777216 24299300 24299306 8388608 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 140775707 16777216 27 16777216 140775707 16777216 27 16777216 (Ns168p1283 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns168p1285 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz156) 24299303 8388608 3 8388608 2895915 2895917 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz156) Bool.false 48598606 16777216 6 16777216 24299303 8388608 3 8388608 (Ns168p1284 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns168p1286 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz156)) Bool.false 5791832 16777216 2 16777216 723979 2097152 1 8388608 (Ns168p1285 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz157 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz501))

noncomputable abbrev qz750 := (@HMul.hMul Real Real Real qz890 qz934 qz934)

noncomputable abbrev qz508 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz750 qz742) qz641)

noncomputable abbrev qz158 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz508))

noncomputable def Ns168p1287 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz153) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz157) qz158) Bool.false 56830511564239 

noncomputable def Ns168p1288 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz157) qz158 21674597 16777216 297 

noncomputable abbrev qz751 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz157))

noncomputable def Ns168p1289 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz157) (@Neg.neg Real Real.instNeg qz751) Bool.true 21674597 16777216 297 16777216 (BSN.inv_eq_neg_inv_neg qz157) 

noncomputable def Ns168p1290 := @Enclosure.Real.IsNear.recentre' qz751 Bool.false 21674597 16777216 297 16777216 21674597 16777216 

noncomputable def Ns168p1291 := @Enclosure.Real.IsNear.recentre' qz157 Bool.true 12986400 16777216 199638608 18874368000000 405825 524288 12477413 1179648000000 

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz342 qz340 qz501)

noncomputable def Ns168p1292 := @Enclosure.Real.IsNear.cos_image qz159 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 41204997) qz370) Bool.false 41204997 16777216 85 8388608 Bool.true 12986400 16777216 1 

noncomputable def Ns168p1293 := nat_lit 728624036100521837955271677 

noncomputable def Ns168p1294 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz153 884279719003555 140737488355328 1 500000000000000 6557979 16777216 27 16777216 5799087827351214615345 2361183241434822606848 Ns168p1293 

noncomputable def Ns168p1295 := @Enclosure.Real.IsNear.subLit_ff_p qz156 qz1 140775707 16777216 27 16777216 8 1 0 1 6557979 6557979 16777216 27 

noncomputable def Ns168p1296 := @Ns168p1295 16777216 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 140775707 16777216 27 16777216 140775707 16777216 27 16777216 (Ns168p1283 rfl rfl rfl rfl rfl rfl) rfl) qz371 

noncomputable def Ns168p1297 := @Enclosure.Real.IsNear.recentre' qz159 Bool.false 5799087827351214615345 2361183241434822606848 Ns168p1293 Ns168p163 41204997 16777216 85 8388608 (@Ns168p1294 Ns168p163 RS169to186.d39 (Ns168p1296 rfl rfl) rfl) 

noncomputable def Ns168p1298 := nat_lit 2140313418683738545455104 

noncomputable def Ns168p1299 := nat_lit 3607942857282711362416010496242946548198850049601375734126621697784708071767424867124385 

noncomputable def Ns168p1300 := nat_lit 732454396158917342224129387123036602064836244665612264274098623323769903498722165921 

noncomputable def Ns168p1301 := nat_lit 9448188271479986749678331280676184614593645156940811169522803524998377893832829101819041 

noncomputable def Ns168p1302 := BSN.sin_dyadic_bound_f 30415683037 34359738368 3 2 16777216 4504395 Ns168p1299 Ns168p1076 Ns168p1300 Ns168p1301 Ns168p1079 Ns168p1300 12986400 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 30415683037) qz358 0 2 Ns168p1299 Ns168p1076 Ns168p1300 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 30415683037) qz359 0 2 Ns168p1301 Ns168p1079 Ns168p1300 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1303 := @Ns168p1292 2250000 (Ns168p1297 rfl) (Enclosure.sfrac_false_div 41204997 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 41204997) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns168p1298) qz385) 226375608064910080 72057594037927936 Bool.false 12986400 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 41204997 16777216 226375608064910080 72057594037927936 0 Ns168p1298 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 12986400 16777216 Ns168p1298 Ns168p89 30415683037 34359738368 4504395 4500000 (Ns168p1302 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p1304 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz157) 405825 524288 12477413 1179648000000 10837150 10837447 8388608 (@Enclosure.Real.IsNear.neg qz157 Bool.true 405825 524288 12477413 1179648000000 (Ns168p1291 (Ns168p1303 rfl rfl) rfl)) 

noncomputable def Ns168p1305 := Ns168p1289 (@Enclosure.Real.IsNear.neg qz751 Bool.false 21674597 16777216 297 16777216 (@Ns168p1290 297 16777216 (Ns168p1304 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p1306 := @Enclosure.Real.IsNear.recentre' qz158 Bool.true 2621987 8388608 

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz342 qz340 qz508)

noncomputable def Ns168p1307 := @Enclosure.Real.IsNear.cos_image qz160 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 31686937)) qz370) Bool.true 31686937 16777216 

noncomputable def Ns168p1308 := nat_lit 74818666223531586612566290645 

noncomputable def Ns168p1309 := nat_lit 21780904763626985480075007821718797 

noncomputable def Ns168p1310 := @Enclosure.Real.IsNear.recentre' qz160 Bool.true Ns168p1308 Ns168p178 Ns168p1309 

noncomputable abbrev qz161 := qz508

noncomputable def Ns168p1311 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz161 884279719003555 140737488355328 1 500000000000000 84609727686439 

noncomputable abbrev qz509 := (@HSub.hSub Real Real Real qz633 qz750 qz742)

noncomputable abbrev qz162 := qz509

noncomputable def Ns168p1312 := @Enclosure.Real.IsNear.subLit_tf qz162 qz25 67017541642023 281474976710656 807116427 281474976710656 1 16 

noncomputable abbrev qz510 := qz750

noncomputable abbrev qz163 := qz510

noncomputable def Ns168p1313 := @Enclosure.Real.IsNear.subLit_ff_n qz163 qz153 43007088564441 281474976710656 354131595 281474976710656 6557979 16777216 27 16777216 

noncomputable def Ns168p1314 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz153 6557979 16777216 27 16777216 6557979 16777216 27 16777216 43007088564441 281474976710656 

noncomputable def Ns168p1315 := nat_lit 127258392204390413630975820974571033457570008443457121786978519704377173803698912579312792787361 

noncomputable def Ns168p1316 := nat_lit 1024620697955262629385829173208545593165376664772152996246524319549281872981668651783051681 

noncomputable def Ns168p1317 := nat_lit 768160070201091556536510749077527703574759530071279590927303615438425980218008346213414580410785 

noncomputable def Ns168p1318 := BSN.cos_dyadic_bound_t 31686937 16777216 4 3 8388608 2250000 Ns168p1315 Ns168p169 Ns168p1316 Ns168p1317 Ns168p172 Ns168p1316 2621987 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 31686937) qz642 0 3 Ns168p1315 Ns168p169 Ns168p1316 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 31686937) (BSN.cosOddQ 16777216) 0 3 Ns168p1317 Ns168p172 Ns168p1316 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1319 := @Ns168p1306 698527216 37748736000000 2621987 8388608 43657951 2359296000000 (@Ns168p1307 303 16777216 Bool.true 2621987 8388608 1 2250000 (@Ns168p1310 Ns168p181 31686937 16777216 303 16777216 (@Ns168p1311 281474976710656 807116427 281474976710656 Ns168p1308 Ns168p178 Ns168p1309 Ns168p181 RS169to186.d39 (@Ns168p1312 0 1 1353755642983024 84609727686439 281474976710656 807116427 281474976710656 (@Ns168p1313 1124367771917214547968 67017541642023 281474976710656 807116427 281474976710656 (@Ns168p1314 354131595 281474976710656 (Ns168p1296 rfl rfl) (Ns168p1296 rfl rfl) rfl) (Ns168p1296 rfl rfl) rfl rfl) qz375 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 31686937 16777216) (BSN.cos_neg_of_bound 31686937 16777216 Bool.true 2621987 8388608 1 2250000 (Ns168p1318 rfl rfl)) rfl rfl) 

noncomputable def Ns168p1320 := @Ns168p1281 1695296834218849319699 Ns168p339 (Ns168p1282 qz27 (@Enclosure.Real.IsNear.of_eq qz748 (@Inv.inv Real Real.instInv (Real.sqrt qz156)) Bool.false 723979 2097152 1 8388608 (BSN.rpow_neg_quarter_mk qz152 (BSN.t_div_two_pi_nonneg qz151 442380 1000 qz154)) Ns168p1286) rfl) (@Ns168p1287 140737488355328 145662413971993 4947802324992000000 (BSN.correction_mk qz153 (BSN.cos_two_pi_p_ne_zero_mk qz151 442380 1000 8 qz154 rfl rfl (@BSN.floor_sqrt_eq_dec qz151 442380 1000 8 qz154 rfl rfl rfl))) (@Ns168p1288 16777216 2621987 8388608 43657951 2359296000000 56830511564239 140737488355328 145662413971993 4947802324992000000 Ns168p1305 (Ns168p1319 rfl) rfl)) 

noncomputable def Ns168p1321 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz151) (hardyZApproximantRS₀ qz151) Bool.true 414261428279040390117 295147905179352825856 242955086003153761319699 Ns168p339 (@Eq.refl Real (hardyZApproximantRS₀ qz151)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz151) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz151) qz151 8) (@HMul.hMul Real Real Real qz5 qz743 (Zeta.RiemannSiegel.correction qz153))) Bool.true 414261428279040390117 295147905179352825856 242955086003153761319699 Ns168p339 (BSN.hardyZApproximantRS₀_eq qz151 8 (@BSN.floor_sqrt_eq_dec qz151 442380 1000 8 qz154 rfl rfl rfl)) (@Ns168p1212 414261428279040390117 295147905179352825856 242955086003153761319699 Ns168p339 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz151) qz151 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 8)) Bool.true 84837059 67108864 48761 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz151) qz151 8) (Ns168p1280 (Ns168p1279 rfl rfl rfl rfl) rfl rfl)) (Ns168p1320 rfl) rfl rfl)) 

theorem RS169to186.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz151) Bool.true 414261428279040390117 295147905179352825856 242955086003153761319699 Ns168p339 := Ns168p1321 

noncomputable def Ns168p1322 := nat_lit 5534023222112865484800000 

noncomputable def Ns168p1323 := nat_lit 9842882120931894794125312 

noncomputable abbrev qz937 := (Enclosure.sfrac Bool.false 443857 1000)

noncomputable abbrev qz752 := qz937

noncomputable abbrev qz511 := qz752

noncomputable abbrev qz164 := qz511

noncomputable abbrev qz938 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 443857 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz753 := qz938

noncomputable abbrev qz512 := qz753

noncomputable abbrev qz165 := qz512

noncomputable abbrev qz939 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 443857 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz754 := qz939

noncomputable abbrev qz513 := qz754

noncomputable abbrev qz166 := qz513

noncomputable abbrev qz755 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz165 qz9))

noncomputable def Ns168p1324 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz164) qz164 8) (@HMul.hMul Real Real Real qz5 qz755 (Zeta.RiemannSiegel.correction qz166)) 36456521 16777216 1529 1048576 39636769299559807 288230376151711744 53505706485916033793 Ns168p1322 Ns168p1323 

noncomputable def Ns168p1325 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz164) qz164 Real.sin BSN.quadSignPos 7 8 443857 1000 127 134217728 67108864 2251799813685248 Bool.false 96981335951 1731 279097919 60 47453128 8 

noncomputable def Ns168p1326 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz164) qz164 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 443857 1000 46 89 134217728 67108864 2251799813685248 Bool.false 96981335951 1731 

noncomputable def Ns168p1327 := Ns168p1326 240485871 61 54794152 8 261175631 61 50729528 8 Bool.false 206609564 65150 Bool.true 61880443 Bool.true 179540539 7074237752028440 1 Bool.false 120203784 Bool.true Bool.false 130587340 Bool.true Bool.false 108179209 

noncomputable def Ns168p1328 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz164) qz164 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 443857 1000 68 5 134217728 67108864 2251799813685248 Bool.false 96981335951 1731 

noncomputable def Ns168p1329 := Ns168p1328 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 166551940 38264 Bool.false 58613506 Bool.false 47383465 7074237752028440 1 Bool.false 121621443 Bool.false Bool.false 46405321 Bool.true Bool.false 206609564 

noncomputable def Ns168p1330 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz164) qz164 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 443857 1000 264 149 134217728 67108864 2251799813685248 Bool.false 96981335951 1731 

noncomputable def Ns168p1331 := Ns168p1330 93032624 60 94906264 8 147453232 60 77490640 16 Bool.false 134217664 1804 Bool.false 29374029 Bool.false 119708349 7074237752028440 1 Bool.false 131016231 Bool.false Bool.false 104456846 Bool.true Bool.false 166551940 

noncomputable def Ns168p1332 := nat_lit 895778529522393456424044903435542597419319770049331983329 

noncomputable def Ns168p1333 := nat_lit 1239716465482641837257843407236354453679259982495744000 

noncomputable def Ns168p1334 := nat_lit 8269095370289673981282885307360000 

noncomputable def Ns168p1335 := nat_lit 22021788223771953547786555689149325120 

noncomputable abbrev qz756 := (@Eq.refl Real qz937)

noncomputable abbrev qz514 := qz756

noncomputable abbrev qz167 := qz514

noncomputable def Ns168p1336 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz164 443857 1000 788037145796 16000000 887714 4000 2000 Ns168p1334 Ns168p1335 qz167 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns168p1337 := nat_lit 286649129447165906055694369099373631174182326415786234665280 

noncomputable abbrev qz757 := (Real.log (Enclosure.sfrac Bool.false 788037145796 16000000))

noncomputable abbrev qz168 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 443857 4000) qz757) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 887714))))))

noncomputable abbrev qz758 := (Enclosure.sfrac Bool.false 443857 2000)

noncomputable abbrev qz515 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz168 qz758) (@HMul.hMul Real Real Real qz5 qz758 (Real.log Real.pi)))

noncomputable def Ns168p1338 := @Enclosure.Real.IsNear.addLit_ft_p qz515 (Enclosure.sfrac Bool.true Ns168p1334 Ns168p1335) 13016621334161896156169 18014398509481984000 15838959249743531 1228800000000000000000 Ns168p1334 Ns168p1335 0 1 Ns168p1337 

noncomputable def Ns168p1339 := nat_lit 873530670853769243126468182016000 

noncomputable abbrev qz516 := (@HSub.hSub Real Real Real qz12 qz168 qz758)

noncomputable abbrev qz517 := (@HMul.hMul Real Real Real qz5 qz758 (Real.log Real.pi))

noncomputable def Ns168p1340 := @Enclosure.Real.IsNear.subLit_ff_p qz516 qz517 17593146592399110351881 18014398509481984000 15061903995013 2400000000000000000 17048885145177 67108864000 443857 67108864000 Ns168p1339 13016621334161896156169 18014398509481984000 

noncomputable def Ns168p1341 := nat_lit 1407451727391928828150480 

noncomputable abbrev qz518 := qz758

noncomputable def Ns168p1342 := @Enclosure.Real.IsNear.subLit_ff_p qz168 qz518 863642201280427313521 720575940379279360 15061903995013 2400000000000000000 443857 2000 0 1 Ns168p1341 17593146592399110351881 18014398509481984000 15061903995013 2400000000000000000 

noncomputable def Ns168p1343 := nat_lit 1944749347933983676289690427308638208 

noncomputable def Ns168p1344 := nat_lit 26124190077125237565030400 

noncomputable def Ns168p1345 := nat_lit 157484929014595617040385167989540880369905153149290636334431714621730882717883465924846579726209880888857179579005503164907520 

noncomputable def Ns168p1346 := nat_lit 2173315399415890216949233545430246194672369052821775983037969300020648328452302130575368981890106180875363531627168927842304 

noncomputable def Ns168p1347 := nat_lit 1539367900004234109182803438861405050030642709230369179516262860315555267407735871034778144295378806388374226542264320 

noncomputable def Ns168p1348 := BSN.log_dyadic_bound 263749145796 1312325145796 6 5 Ns168p1345 67108864 18000000 Ns168p1346 Ns168p1347 27347135 1576074291592 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 263749145796) (BSN.artanhQ 1312325145796) 0 5 Ns168p1346 Ns168p1345 Ns168p1347 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns168p1349 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 443857 4000) qz757 443857 4000 0 1 48660095924744825 4503599627370496 100000027 1800000000000000 863924967874778551601 720575940379279360 44385711984139 7200000000000000000 (Enclosure.Real.IsNear.const Bool.false 443857 4000) (BSN.isNear_log_sfrac 788037145796 16000000 48660095924744825 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 788037145796) qz353)) Bool.false Ns168p1344 Ns168p89 1000000270000000 18000000000000000000000 48660095924744825 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 788037145796 16000000 15 1576074291592 1048576000000 27347135 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns168p1348 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p1350 := BSN.arctan_dyadic_bound_f 1000 887714 1 0 8388608 2250000 0 1 1 0 1 1 9449 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 887714) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 887714) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz759 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 887714)))

noncomputable def Ns168p1351 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz759 884279719003555 562949953421312 1 2000000000000000 9449 8388608 1 2250000 7412556610961095524352 883645607347619 562949953421312 8000000009 18000000000000000 qz16 (Ns168p1350 rfl) rfl rfl 

noncomputable def Ns168p1352 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 443857 4000) qz757) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz759)) 863924967874778551601 720575940379279360 44385711984139 7200000000000000000 883645607347619 2251799813685248 8000000009 72000000000000000 Ns168p1343 863642201280427313521 720575940379279360 15061903995013 2400000000000000000 (Ns168p1349 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz759) 1 4 0 1 883645607347619 562949953421312 8000000009 18000000000000000 883645607347619 2251799813685248 8000000009 72000000000000000 qz356 Ns168p1351 rfl) 

noncomputable def Ns168p1353 := @Ns168p1338 Ns168p1332 Ns168p1333 15838959249743531 1228800000000000000000 (@Ns168p1340 15838959249743531 1228800000000000000000 (Ns168p1342 (Ns168p1352 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 443857 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz518 (Real.log Real.pi) 443857 2000 0 1 38410761 33554432 1 33554432 17048885145177 67108864000 443857 67108864000 (Enclosure.Real.IsNear.const Bool.false 443857 2000) RS169to186.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns168p1334 Ns168p1335) 

noncomputable def Ns168p1354 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz164) Bool.false Ns168p1332 Ns168p1333 15838959249743531 1228800000000000000000 12122666993 16777216 109 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz164) (@HAdd.hAdd Real Real Real qz357 qz515 (Enclosure.sfrac Bool.true Ns168p1334 Ns168p1335)) Bool.false Ns168p1332 Ns168p1333 15838959249743531 1228800000000000000000 Ns168p1336 (Ns168p1353 rfl rfl)) 

noncomputable def Ns168p1355 := BSN.cos_dyadic_bound_f 32625343 34359738368 1 0 16777216 4504395 0 1 1 0 1 1 16777208 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 32625343) qz682 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 32625343) qz683 0 0 rfl) rfl rfl 

noncomputable def Ns168p1356 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz164) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12122666993) qz370) Bool.false 12122666993 16777216 109 8388608 Bool.false 16777208 16777216 1 2250000 (Ns168p1354 rfl) (Enclosure.sfrac_false_div 12122666993 16777216) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12122666993) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2295804449480660484096) qz385) 226375608064910080 72057594037927936 Bool.false 16777208 16777216 115 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q0 12122666993 16777216 226375608064910080 72057594037927936 115 2295804449480660484096 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777208 16777216 2295804449480660484096 Ns168p89 32625343 34359738368 4504395 4500000 (Ns168p1355 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p1357 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz164) Bool.false Ns168p1332 Ns168p1333 15838959249743531 1228800000000000000000 96981335951 134217728 1731 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz164) (@HAdd.hAdd Real Real Real qz357 qz515 (Enclosure.sfrac Bool.true Ns168p1334 Ns168p1335)) Bool.false Ns168p1332 Ns168p1333 15838959249743531 1228800000000000000000 Ns168p1336 (Ns168p1353 rfl rfl)) 

noncomputable def Ns168p1358 := Ns168p1331 38264 BSN.abs_quadSignPos (BSN.cos_quad_nat0 264 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131016231 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 149 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 104456846 134217728) qz167 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz164) qz164 1) Bool.false 2097151 2097152 15852413 1179648000000 134217664 134217728 1804 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz164) qz164 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz164)) Bool.false 2097151 2097152 15852413 1179648000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz164) qz164) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz164)) Bool.false 16777208 16777216 253638608 18874368000000 2097151 2097152 15852413 1179648000000 (Ns168p1356 rfl rfl) rfl)) rfl) (Ns168p1357 rfl) RS169to186.d7 

noncomputable def Ns168p1359 := nat_lit 744481786245562200895906651281 

noncomputable def Ns168p1360 := BSN.cos_dyadic_bound_f 29374029 134217728 2 1 134217728 67108864 Ns168p1359 Ns168p130 Ns168p1359 Ns168p1359 Ns168p131 Ns168p1359 131016231 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 29374029) qz363 0 1 Ns168p1359 Ns168p130 Ns168p1359 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 29374029) qz364 0 1 Ns168p1359 Ns168p131 Ns168p1359 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1361 := nat_lit 201562600066266469258406101088584917425246969993804732239800502691745 

noncomputable def Ns168p1362 := nat_lit 42169216209128104852702249481915331856216171693310324322411063201 

noncomputable def Ns168p1363 := nat_lit 527833773823502164459397318256656444624070095229604177245812651042721 

noncomputable def Ns168p1364 := BSN.sin_dyadic_bound_f 119708349 134217728 3 2 134217728 67108864 Ns168p1361 Ns168p112 Ns168p1362 Ns168p1363 Ns168p115 Ns168p1362 104456846 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 119708349) qz361 0 2 Ns168p1361 Ns168p112 Ns168p1362 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 119708349) qz362 0 2 Ns168p1363 Ns168p115 Ns168p1362 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1365 := nat_lit 6435006862394576334611717076842226165771993335095432077991355351296 

noncomputable def Ns168p1366 := nat_lit 139309777256750269378874771899387718250344347062181935399567616 

noncomputable def Ns168p1367 := nat_lit 19304741967629215503296393480982879721879479316592171870103266918656 

noncomputable def Ns168p1368 := BSN.cos_dyadic_bound_f 58613506 134217728 3 2 134217728 67108864 Ns168p1365 Ns168p124 Ns168p1366 Ns168p1367 Ns168p127 Ns168p1366 121621443 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 58613506) qz363 0 2 Ns168p1365 Ns168p124 Ns168p1366 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 58613506) qz364 0 2 Ns168p1367 Ns168p127 Ns168p1366 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1369 := nat_lit 5040890508928596878964768750625 

noncomputable def Ns168p1370 := BSN.sin_dyadic_bound_f 47383465 134217728 2 1 134217728 67108864 Ns168p1369 Ns168p394 Ns168p1369 Ns168p1369 Ns168p395 Ns168p1369 46405321 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 47383465) qz361 0 1 Ns168p1369 Ns168p394 Ns168p1369 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 47383465) qz362 0 1 Ns168p1369 Ns168p395 Ns168p1369 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1371 := Ns168p1329 65150 BSN.abs_quadSignPos (BSN.cos_quad_nat0 68 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 121621443 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 5 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 46405321 134217728) qz167 rfl rfl (Ns168p1358 RS169to186.d9 RS169to186.d11 RS169to186.d13 RS169to186.d17 (Ns168p1360 rfl rfl) (Ns168p1364 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns168p1357 rfl) RS169to186.d19 RS169to186.d21 RS169to186.d23 RS169to186.d25 RS169to186.d17 (Ns168p1368 rfl rfl) (Ns168p1370 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns168p1372 := nat_lit 7994184182620394488585415077725086051321797772940572142137477530081 

noncomputable def Ns168p1373 := nat_lit 214994481777043349881386570593181464927419889966366939824620001 

noncomputable def Ns168p1374 := nat_lit 23982122558897629379056482460034071791035538479041783692532783350241 

noncomputable def Ns168p1375 := BSN.cos_dyadic_bound_f 61880443 134217728 3 2 134217728 67108864 Ns168p1372 Ns168p124 Ns168p1373 Ns168p1374 Ns168p127 Ns168p1373 120203784 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 61880443) qz363 0 2 Ns168p1372 Ns168p124 Ns168p1373 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 61880443) qz364 0 2 Ns168p1374 Ns168p127 Ns168p1373 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1376 := nat_lit 5684443071922947454771361807766087309066883242326611071556269574101120890358859217482953382000272692304721 

noncomputable def Ns168p1377 := nat_lit 1121890048655000432534330086412412360371438889846291340835551131679065585802535269219804581444279121 

noncomputable def Ns168p1378 := nat_lit 28403626698856213138398856788642903330429082491022972470014452574050589246854323842783366189275837673593681 

noncomputable def Ns168p1379 := BSN.sin_dyadic_bound_f 179540539 134217728 4 3 134217728 67108864 Ns168p1376 Ns168p144 Ns168p1377 Ns168p1378 Ns168p147 Ns168p1377 130587340 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 179540539) qz361 0 3 Ns168p1376 Ns168p144 Ns168p1377 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 179540539) qz362 0 3 Ns168p1378 Ns168p147 Ns168p1377 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1380 := Ns168p1327 87818 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 46 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 120203784 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 89 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 130587340 134217728) qz167 rfl rfl (Ns168p1371 rfl rfl) (Ns168p1357 rfl) RS169to186.d27 RS169to186.d29 RS169to186.d31 RS169to186.d33 RS169to186.d17 (Ns168p1375 rfl rfl) (Ns168p1379 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns168p1381 := nat_lit 224540256908425905428172976828002106290836686563004173146032958902305 

noncomputable def Ns168p1382 := nat_lit 52329109595969997400481831263030195944513118923078591330450444321 

noncomputable def Ns168p1383 := nat_lit 587996901916055324697042730632246324730185919758183088139360829739041 

noncomputable def Ns168p1384 := BSN.sin_dyadic_bound_f 122982387 134217728 3 2 134217728 67108864 Ns168p1381 Ns168p112 Ns168p1382 Ns168p1383 Ns168p115 Ns168p1382 106481456 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 122982387) qz361 0 2 Ns168p1381 Ns168p112 Ns168p1382 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 122982387) qz362 0 2 Ns168p1383 Ns168p115 Ns168p1382 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1385 := Ns168p1325 Bool.false 108179209 87818 Bool.true 122982387 7074237752028440 1 Bool.false 106481456 Bool.false Bool.false 145826084 97856 BSN.abs_quadSignPos qz365 (BSN.sfrac_eq_quadSignPos_mul Bool.false 106481456 134217728) qz167 rfl (Ns168p1380 rfl) (Ns168p1357 rfl) RS169to186.d35 RS169to186.d37 RS169to186.d17 (Ns168p1384 rfl rfl) rfl 

noncomputable def Ns168p1386 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz164) qz164 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz164) qz164 8) 145826084 134217728 97856 134217728 145826084 134217728 97856 134217728 39144891355234304 36456521 16777216 1529 1048576 (Ns168p1385 rfl rfl rfl rfl) 

noncomputable def Ns168p1387 := @Enclosure.Real.IsNear.mulLit_ff qz755 (Zeta.RiemannSiegel.correction qz166) 45211 131072 1 8388608 876706317037 2199023255552 92003806094693 3298534883328000000 39636769299559807 288230376151711744 

noncomputable abbrev qz760 := (@HPow.hPow Real Real Real qz7 qz165 qz9)

noncomputable def Ns168p1388 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz760 1 1 0 1 45211 131072 1 8388608 45211 131072 1 8388608 

noncomputable def Ns168p1389 := @Enclosure.Real.IsNear.sqrt_image qz165 1185176752689 16777216000 443857 16777216000 70505246 70505273 8388608 (@Enclosure.Real.IsNear.of_eq qz165 (@HMul.hMul Real Real Real qz5 qz164 qz3) Bool.false 1185176752689 16777216000 443857 16777216000 (BSN.t_div_two_pi_mk qz164 443857 1000 qz167) (@Enclosure.Real.IsNear.mulLit_ff qz164 qz3 443857 1000 0 1 2670177 16777216 1 16777216 1185176752689 16777216000 443857 16777216000 (Enclosure.Real.IsNear.const Bool.false 443857 1000) RS169to186.d40 rfl)) 

noncomputable abbrev qz940 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 443857 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz761 := qz940

noncomputable abbrev qz519 := qz761

noncomputable abbrev qz169 := qz519

noncomputable def Ns168p1390 := @Enclosure.Real.IsNear.sqrt_image qz169 141010519 16777216 27 16777216 24319557 24319563 8388608 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 141010519 16777216 27 16777216 141010519 16777216 27 16777216 (Ns168p1389 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns168p1391 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz169) 3039945 1048576 3 8388608 2893503 2893505 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz169) Bool.false 48639120 16777216 6 16777216 3039945 1048576 3 8388608 (Ns168p1390 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns168p1392 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz169)) Bool.false 5787008 16777216 2 16777216 45211 131072 1 8388608 (Ns168p1391 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz170 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz513))

noncomputable abbrev qz762 := (@HMul.hMul Real Real Real qz890 qz939 qz939)

noncomputable abbrev qz520 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz762 qz754) qz641)

noncomputable abbrev qz171 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz520))

noncomputable def Ns168p1393 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz166) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz170) qz171) Bool.false 876706317037 

noncomputable def Ns168p1394 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz170) qz171 317111 262144 131 

noncomputable abbrev qz763 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz170))

noncomputable def Ns168p1395 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz170) (@Neg.neg Real Real.instNeg qz763) Bool.true 317111 262144 131 8388608 (BSN.inv_eq_neg_inv_neg qz170) 

noncomputable def Ns168p1396 := @Enclosure.Real.IsNear.recentre' qz763 Bool.false 20295104 16777216 262 16777216 317111 262144 

noncomputable def Ns168p1397 := @Enclosure.Real.IsNear.recentre' qz170 Bool.true 13869107 16777216 401527216 37748736000000 13869107 16777216 25095451 2359296000000 

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz342 qz340 qz513)

noncomputable def Ns168p1398 := @Enclosure.Real.IsNear.cos_image qz172 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10670091) qz405) Bool.false 10670091 4194304 171 16777216 Bool.true 13869107 16777216 1 

noncomputable def Ns168p1399 := nat_lit 728624036102538857676688381 

noncomputable def Ns168p1400 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz166 884279719003555 140737488355328 1 500000000000000 6792791 16777216 27 16777216 6006727316729877372005 2361183241434822606848 Ns168p1399 

noncomputable def Ns168p1401 := @Enclosure.Real.IsNear.subLit_ff_p qz169 qz1 141010519 16777216 27 16777216 8 1 0 1 6792791 6792791 16777216 27 

noncomputable def Ns168p1402 := @Ns168p1401 16777216 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 141010519 16777216 27 16777216 141010519 16777216 27 16777216 (Ns168p1389 rfl rfl rfl rfl rfl rfl) rfl) qz371 

noncomputable def Ns168p1403 := @Enclosure.Real.IsNear.recentre' qz172 Bool.false 6006727316729877372005 2361183241434822606848 Ns168p1399 Ns168p163 10670091 4194304 171 16777216 (@Ns168p1400 Ns168p163 RS169to186.d39 (Ns168p1402 rfl rfl) rfl) 

noncomputable def Ns168p1404 := nat_lit 5270251919468213709654466880239735931822235232868460664751986253693269268633878383494305 

noncomputable def Ns168p1405 := nat_lit 1562582023326607297306590198868791509072390218685181581944718252811498903744878412961 

noncomputable def Ns168p1406 := nat_lit 13800510846759935684899393064115425587567356025730001923217767787263534229149332629816481 

noncomputable def Ns168p1407 := BSN.sin_dyadic_bound_f 33437234653 34359738368 3 2 16777216 4504395 Ns168p1404 Ns168p1076 Ns168p1405 Ns168p1406 Ns168p1079 Ns168p1405 13869107 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 33437234653) qz358 0 2 Ns168p1404 Ns168p1076 Ns168p1405 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 33437234653) qz359 0 2 Ns168p1406 Ns168p1079 Ns168p1405 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1408 := @Ns168p1398 2250000 (Ns168p1403 rfl) (Enclosure.sfrac_false_div 10670091 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10670091) qz405) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 588234052842412448940032) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 13869107 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 10670091 4194304 226375608064910080 72057594037927936 0 588234052842412448940032 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 13869107 16777216 588234052842412448940032 604462909807314587353088 33437234653 34359738368 4504395 4500000 (Ns168p1407 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p1409 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz170) 13869107 16777216 25095451 2359296000000 10147421 10147683 8388608 (@Enclosure.Real.IsNear.neg qz170 Bool.true 13869107 16777216 25095451 2359296000000 (Ns168p1397 (Ns168p1408 rfl rfl) rfl)) 

noncomputable def Ns168p1410 := Ns168p1395 (@Enclosure.Real.IsNear.neg qz763 Bool.false 317111 262144 131 8388608 (@Ns168p1396 131 8388608 (Ns168p1409 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p1411 := @Enclosure.Real.IsNear.recentre' qz171 Bool.true 2764667 8388608 

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz342 qz340 qz520)

noncomputable def Ns168p1412 := @Enclosure.Real.IsNear.cos_image qz173 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 31988255)) qz370) Bool.true 31988255 16777216 

noncomputable def Ns168p1413 := nat_lit 75530131721355148100472921005 

noncomputable def Ns168p1414 := nat_lit 22123084097937113010908010517349797 

noncomputable def Ns168p1415 := @Enclosure.Real.IsNear.recentre' qz173 Bool.true Ns168p1413 Ns168p178 Ns168p1414 

noncomputable abbrev qz174 := qz520

noncomputable def Ns168p1416 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz174 884279719003555 140737488355328 1 500000000000000 85414298324591 

noncomputable abbrev qz521 := (@HSub.hSub Real Real Real qz633 qz762 qz754)

noncomputable abbrev qz175 := qz521

noncomputable def Ns168p1417 := @Enclosure.Real.IsNear.subLit_tf qz175 qz25 67822112280175 281474976710656 819796275 281474976710656 1 16 

noncomputable abbrev qz522 := qz762

noncomputable abbrev qz176 := qz522

noncomputable def Ns168p1418 := @Enclosure.Real.IsNear.subLit_ff_n qz176 qz166 46142009569681 281474976710656 366811443 281474976710656 6792791 16777216 27 16777216 

noncomputable def Ns168p1419 := @Enclosure.Real.IsNear.mulLit_ff qz166 qz166 6792791 16777216 27 16777216 6792791 16777216 27 16777216 46142009569681 281474976710656 

noncomputable def Ns168p1420 := nat_lit 132206803265181769097159417758737357545008618141529091853291169570107770956500277799539566890625 

noncomputable def Ns168p1421 := nat_lit 1147853844035555177509682536131498686604726104574903733329785661436421622466432324462890625 

noncomputable def Ns168p1422 := nat_lit 797875493675246556533906721155273328969540423185064249758019289585199424828195030338333960490625 

noncomputable def Ns168p1423 := BSN.cos_dyadic_bound_t 31988255 16777216 4 3 8388608 2250000 Ns168p1420 Ns168p169 Ns168p1421 Ns168p1422 Ns168p172 Ns168p1421 2764667 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 31988255) qz642 0 3 Ns168p1420 Ns168p169 Ns168p1421 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 31988255) (BSN.cosOddQ 16777216) 0 3 Ns168p1422 Ns168p172 Ns168p1421 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1424 := @Ns168p1411 177444304 9437184000000 2764667 8388608 11090269 589824000000 (@Ns168p1412 77 4194304 Bool.true 2764667 8388608 1 2250000 (@Ns168p1415 Ns168p181 31988255 16777216 77 4194304 (@Ns168p1416 281474976710656 819796275 281474976710656 Ns168p1413 Ns168p178 Ns168p1414 Ns168p181 RS169to186.d39 (@Ns168p1417 0 1 1366628773193456 85414298324591 281474976710656 819796275 281474976710656 (@Ns168p1418 1137866227300748492800 67822112280175 281474976710656 819796275 281474976710656 (@Ns168p1419 366811443 281474976710656 (Ns168p1402 rfl rfl) (Ns168p1402 rfl rfl) rfl) (Ns168p1402 rfl rfl) rfl rfl) qz375 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 31988255 16777216) (BSN.cos_neg_of_bound 31988255 16777216 Bool.true 2764667 8388608 1 2250000 (Ns168p1423 rfl rfl)) rfl rfl) 

noncomputable def Ns168p1425 := @Ns168p1387 53505706485916033793 Ns168p1322 (Ns168p1388 qz27 (@Enclosure.Real.IsNear.of_eq qz760 (@Inv.inv Real Real.instInv (Real.sqrt qz169)) Bool.false 45211 131072 1 8388608 (BSN.rpow_neg_quarter_mk qz165 (BSN.t_div_two_pi_nonneg qz164 443857 1000 qz167)) Ns168p1392) rfl) (@Ns168p1393 2199023255552 92003806094693 3298534883328000000 (BSN.correction_mk qz166 (BSN.cos_two_pi_p_ne_zero_mk qz164 443857 1000 8 qz167 rfl rfl (@BSN.floor_sqrt_eq_dec qz164 443857 1000 8 qz167 rfl rfl rfl))) (@Ns168p1394 8388608 2764667 8388608 11090269 589824000000 876706317037 2199023255552 92003806094693 3298534883328000000 Ns168p1410 (Ns168p1424 rfl) rfl)) 

noncomputable def Ns168p1426 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz164) (hardyZApproximantRS₀ qz164) Bool.false 586681492384189057 288230376151711744 8123041445059535233793 Ns168p1322 (@Eq.refl Real (hardyZApproximantRS₀ qz164)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz164) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz164) qz164 8) (@HMul.hMul Real Real Real qz5 qz755 (Zeta.RiemannSiegel.correction qz166))) Bool.false 586681492384189057 288230376151711744 8123041445059535233793 Ns168p1322 (BSN.hardyZApproximantRS₀_eq qz164 8 (@BSN.floor_sqrt_eq_dec qz164 443857 1000 8 qz167 rfl rfl rfl)) (@Ns168p1324 586681492384189057 288230376151711744 8123041445059535233793 Ns168p1322 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz164) qz164 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz164) qz164 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz164) qz164 8)) Bool.false 36456521 16777216 1529 1048576 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz164) qz164 8) (Ns168p1386 (Ns168p1385 rfl rfl rfl rfl) rfl rfl)) (Ns168p1425 rfl) rfl rfl)) 

theorem RS169to186.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz164) Bool.false 586681492384189057 288230376151711744 8123041445059535233793 Ns168p1322 := Ns168p1426 

noncomputable def Ns168p1427 := nat_lit 55340232221128654848000000 

noncomputable def Ns168p1428 := nat_lit 18457870880663599184384884736 

noncomputable abbrev qz941 := (Enclosure.sfrac Bool.false 446069 1000)

noncomputable abbrev qz764 := qz941

noncomputable abbrev qz523 := qz764

noncomputable abbrev qz177 := qz523

noncomputable abbrev qz942 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 446069 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz765 := qz942

noncomputable abbrev qz524 := qz765

noncomputable abbrev qz178 := qz524

noncomputable abbrev qz943 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 446069 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz766 := qz943

noncomputable abbrev qz525 := qz766

noncomputable abbrev qz179 := qz525

noncomputable abbrev qz767 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz178 qz9))

noncomputable def Ns168p1429 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz177) qz177 8) (@HMul.hMul Real Real Real qz5 qz767 (Zeta.RiemannSiegel.correction qz179)) 60269831 16777216 98335 67108864 39896757334469537775 295147905179352825856 502415536636814555381 Ns168p1427 Ns168p1428 

noncomputable def Ns168p1430 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz177) qz177 Real.sin BSN.quadSignPos 7 8 446069 1000 127 134217728 67108864 2251799813685248 Bool.false 97613727648 1740 279097919 60 47453128 8 

noncomputable def Ns168p1431 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz177) qz177 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 446069 1000 45 89 134217728 67108864 2251799813685248 Bool.false 97613727648 1740 

noncomputable def Ns168p1432 := Ns168p1431 240485871 61 54794152 8 261175631 61 50729528 8 Bool.true 182037784 65466 Bool.true 172272207 Bool.true 124869338 7074237752028440 1 Bool.false 128717675 Bool.true Bool.false 107619609 Bool.true Bool.true 275262934 

noncomputable def Ns168p1433 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz177) qz177 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 446069 1000 69 5 134217728 67108864 2251799813685248 Bool.false 97613727648 1740 

noncomputable def Ns168p1434 := Ns168p1433 186065264 60 67108856 8 216015088 60 60023992 8 Bool.true 89319031 38446 Bool.false 68600125 Bool.false 201949788 7074237752028440 1 Bool.false 65652112 Bool.true Bool.false 133924150 Bool.true Bool.true 182037784 

noncomputable def Ns168p1435 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz177) qz177 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 446069 1000 266 151 134217728 67108864 2251799813685248 Bool.false 97613727648 1740 

noncomputable def Ns168p1436 := Ns168p1435 93032624 60 94906264 8 147453232 60 77490640 16 Bool.false 33008 1804 Bool.false 34320133 Bool.false 4276068 7074237752028440 1 Bool.false 129853671 Bool.true Bool.false 4275344 Bool.false Bool.true 89319031 

noncomputable def Ns168p1437 := nat_lit 928917581070755532631312911216196102443020455095051310253 

noncomputable def Ns168p1438 := nat_lit 1277250753900487018920052803266831456419926125838336000 

noncomputable def Ns168p1439 := nat_lit 8477207868490928558546989447520000 

noncomputable def Ns168p1440 := nat_lit 22688531123202562492481121183850793280 

noncomputable abbrev qz526 := (@Eq.refl Real qz764)

noncomputable abbrev qz180 := qz526

noncomputable def Ns168p1441 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz177 446069 1000 795911211044 16000000 892138 4000 2000 Ns168p1439 Ns168p1440 qz180 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns168p1442 := nat_lit 297253625942641770442020131589182752781766545630416419280960 

noncomputable abbrev qz768 := (Real.log (Enclosure.sfrac Bool.false 795911211044 16000000))

noncomputable abbrev qz181 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 446069 4000) qz768) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 892138))))))

noncomputable abbrev qz769 := (Enclosure.sfrac Bool.false 446069 2000)

noncomputable abbrev qz527 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz181 qz769) (@HMul.hMul Real Real Real qz5 qz769 (Real.log Real.pi)))

noncomputable def Ns168p1443 := @Enclosure.Real.IsNear.addLit_ft_p qz527 (Enclosure.sfrac Bool.true Ns168p1439 Ns168p1440) 13101499477436606761357 18014398509481984000 47751640968871781 3686400000000000000000 Ns168p1439 Ns168p1440 0 1 Ns168p1442 

noncomputable def Ns168p1444 := nat_lit 879226746627364311769387368448000 

noncomputable abbrev qz528 := (@HSub.hSub Real Real Real qz12 qz181 qz769)

noncomputable abbrev qz529 := (@HMul.hMul Real Real Real qz5 qz769 (Real.log Real.pi))

noncomputable def Ns168p1445 := @Enclosure.Real.IsNear.subLit_ff_p qz528 qz529 17700832247713105496461 18014398509481984000 45406912044763 7200000000000000000 17133849748509 67108864000 446069 67108864000 Ns168p1444 13101499477436606761357 18014398509481984000 

noncomputable def Ns168p1446 := nat_lit 35401664495426210992922000 

noncomputable abbrev qz530 := qz769

noncomputable def Ns168p1447 := @Enclosure.Real.IsNear.subLit_ff_p qz181 qz530 21718664612076165056909 18014398509481984000 45406912044763 7200000000000000000 446069 2000 0 1 Ns168p1446 17700832247713105496461 18014398509481984000 45406912044763 7200000000000000000 

noncomputable def Ns168p1448 := nat_lit 48906084926965497505000788510933778432 

noncomputable def Ns168p1449 := nat_lit 26148229355187418779615232 

noncomputable def Ns168p1450 := nat_lit 167193420366214797001562755469477337335486405193054178391335554513049583610054821388104442910703275492882548497127206965739520 

noncomputable def Ns168p1451 := nat_lit 2420926370378324722676201107495424723618006478165707297928700601008112474299749476920754487774943113523323349860422809288704 

noncomputable def Ns168p1452 := nat_lit 2065858629001625497280218970169693921358765315233997368312356503204112398036021736117367507524815497055152555105976320 

noncomputable def Ns168p1453 := BSN.log_dyadic_bound 271623211044 1320199211044 6 5 Ns168p1450 67108864 18000000 Ns168p1451 Ns168p1452 28014359 1591822422088 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 271623211044) (BSN.artanhQ 1320199211044) 0 5 Ns168p1451 Ns168p1450 Ns168p1452 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns168p1454 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 446069 4000) qz768 446069 4000 0 1 48704872569418361 4503599627370496 100000027 1800000000000000 21725733802167878872909 18014398509481984000 44606912043863 7200000000000000000 (Enclosure.Real.IsNear.const Bool.false 446069 4000) (BSN.isNear_log_sfrac 795911211044 16000000 48704872569418361 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 795911211044) qz353)) Bool.false Ns168p1449 Ns168p89 1000000270000000 18000000000000000000000 48704872569418361 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 795911211044 16000000 15 1591822422088 1048576000000 28014359 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns168p1453 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p1455 := BSN.arctan_dyadic_bound_f 1000 892138 1 0 8388608 2250000 0 1 1 0 1 1 9402 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 892138) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 892138) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz770 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 892138)))

noncomputable def Ns168p1456 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz770 884279719003555 562949953421312 1 2000000000000000 9402 8388608 1 2250000 7412583069608906326016 883648761464227 562949953421312 8000000009 18000000000000000 qz16 (Ns168p1455 rfl) rfl rfl 

noncomputable def Ns168p1457 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 446069 4000) qz768) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz770)) 21725733802167878872909 18014398509481984000 44606912043863 7200000000000000000 883648761464227 2251799813685248 8000000009 72000000000000000 Ns168p1448 21718664612076165056909 18014398509481984000 45406912044763 7200000000000000000 (Ns168p1454 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz770) 1 4 0 1 883648761464227 562949953421312 8000000009 18000000000000000 883648761464227 2251799813685248 8000000009 72000000000000000 qz356 Ns168p1456 rfl) 

noncomputable def Ns168p1458 := @Ns168p1443 Ns168p1437 Ns168p1438 47751640968871781 3686400000000000000000 (@Ns168p1445 47751640968871781 3686400000000000000000 (Ns168p1447 (Ns168p1457 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 446069 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz530 (Real.log Real.pi) 446069 2000 0 1 38410761 33554432 1 33554432 17133849748509 67108864000 446069 67108864000 (Enclosure.Real.IsNear.const Bool.false 446069 2000) RS169to186.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns168p1439 Ns168p1440) 

noncomputable def Ns168p1459 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz177) Bool.false Ns168p1437 Ns168p1438 47751640968871781 3686400000000000000000 3050428989 4194304 109 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz177) (@HAdd.hAdd Real Real Real qz357 qz527 (Enclosure.sfrac Bool.true Ns168p1439 Ns168p1440)) Bool.false Ns168p1437 Ns168p1438 47751640968871781 3686400000000000000000 Ns168p1441 (Ns168p1458 rfl rfl)) 

noncomputable def Ns168p1460 := nat_lit 330406129951521115178867845039931704532368091274396711789160492956764520533017539173458407644769841388610304153377616805099295757481041 

noncomputable def Ns168p1461 := nat_lit 1296985566167364170939292694987530979374979352933922598450371085822004482258776525817524027815363891144507173707470555812298386676121600 

noncomputable def Ns168p1462 := nat_lit 612142429783509154120393031856605652856751052230515486201104905079602687503595107587758012499386631499823681110410525860734612561 

noncomputable def Ns168p1463 := nat_lit 1999632652333428199451204812886230792417767372390266435316209033352184466005347478017413817787868489446768765672085732963350369675162705 

noncomputable def Ns168p1464 := nat_lit 118025686521230139555475635243865319123123121116986956458983768809802407885548663849394686531198114094150152807379820578919153187527065600 

noncomputable def Ns168p1465 := BSN.cos_dyadic_bound_t 53980599931 34359738368 4 3 16777216 4504395 Ns168p1460 Ns168p1461 Ns168p1462 Ns168p1463 Ns168p1464 Ns168p1462 4126 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 53980599931) qz682 0 3 Ns168p1460 Ns168p1461 Ns168p1462 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 53980599931) qz683 0 3 Ns168p1463 Ns168p1464 Ns168p1462 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1466 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz177) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3050428989) qz405) Bool.false 3050428989 4194304 109 8388608 Bool.false 4126 16777216 1 2250000 (Ns168p1459 rfl) (Enclosure.sfrac_false_div 3050428989 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3050428989) qz405) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949636756780793953517568) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.true 4126 16777216 115 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 3050428989 4194304 226375608064910080 72057594037927936 115 949636756780793953517568 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.true 4126 16777216 949636756780793953517568 604462909807314587353088 53980599931 34359738368 4504395 4500000 (Ns168p1465 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p1467 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz177) Bool.false Ns168p1437 Ns168p1438 47751640968871781 3686400000000000000000 97613727648 134217728 1740 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz177) (@HAdd.hAdd Real Real Real qz357 qz527 (Enclosure.sfrac Bool.true Ns168p1439 Ns168p1440)) Bool.false Ns168p1437 Ns168p1438 47751640968871781 3686400000000000000000 Ns168p1441 (Ns168p1458 rfl rfl)) 

noncomputable def Ns168p1468 := Ns168p1436 38446 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 266 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 129853671 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 151 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 4275344 134217728) qz180 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz177) qz177 1) Bool.false 2063 8388608 15852413 1179648000000 33008 134217728 1804 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz177) qz177 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz177)) Bool.false 2063 8388608 15852413 1179648000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz177) qz177) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz177)) Bool.false 4126 16777216 253638608 18874368000000 2063 8388608 15852413 1179648000000 (Ns168p1466 rfl rfl) rfl)) rfl) (Ns168p1467 rfl) RS169to186.d7 

noncomputable def Ns168p1469 := nat_lit 1387381339153157746931920260721 

noncomputable def Ns168p1470 := BSN.cos_dyadic_bound_f 34320133 134217728 2 1 134217728 67108864 Ns168p1469 Ns168p130 Ns168p1469 Ns168p1469 Ns168p131 Ns168p1469 129853671 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 34320133) qz363 0 1 Ns168p1469 Ns168p130 Ns168p1469 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 34320133) qz364 0 1 Ns168p1469 Ns168p131 Ns168p1469 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1471 := BSN.sin_dyadic_bound_f 4276068 134217728 1 0 134217728 67108864 0 1 1 0 1 1 4275344 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 4276068) qz361 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 4276068) qz362 0 0 rfl) rfl rfl 

noncomputable def Ns168p1472 := nat_lit 21733553847105882793179481755244958323525705383798698390519775390625 

noncomputable def Ns168p1473 := nat_lit 490455101766906033808373493253612317104143524229526519775390625 

noncomputable def Ns168p1474 := nat_lit 56920418386541118039034381516176289760720583582338314646519775390625 

noncomputable def Ns168p1475 := BSN.sin_dyadic_bound_f 68600125 134217728 3 2 134217728 67108864 Ns168p1472 Ns168p112 Ns168p1473 Ns168p1474 Ns168p115 Ns168p1473 65652112 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 68600125) qz361 0 2 Ns168p1472 Ns168p112 Ns168p1473 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 68600125) qz362 0 2 Ns168p1474 Ns168p115 Ns168p1473 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1476 := nat_lit 9105156946278892296321907809198659399024792393374701345595720015388349982160871101995521478821403485536256 

noncomputable def Ns168p1477 := nat_lit 4601726669918333808661488231905585018865590597652767840371721518701081762961381186787542852442259456 

noncomputable def Ns168p1478 := nat_lit 45478146229221530054190789918387309080863464423319701803303893615501802673545152774609179278541711439036416 

noncomputable def Ns168p1479 := BSN.sin_dyadic_bound_f 201949788 134217728 4 3 134217728 67108864 Ns168p1476 Ns168p144 Ns168p1477 Ns168p1478 Ns168p147 Ns168p1477 133924150 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 201949788) qz361 0 3 Ns168p1476 Ns168p144 Ns168p1477 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 201949788) qz362 0 3 Ns168p1478 Ns168p147 Ns168p1477 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1480 := Ns168p1434 65466 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 69 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 65652112 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 5 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133924150 134217728) qz180 rfl rfl (Ns168p1468 RS169to186.d9 RS169to186.d11 RS169to186.d13 RS169to186.d17 (Ns168p1470 rfl rfl) (Ns168p1471 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns168p1467 rfl) RS169to186.d19 RS169to186.d21 RS169to186.d23 RS169to186.d25 RS169to186.d17 (Ns168p1475 rfl rfl) (Ns168p1479 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns168p1481 := nat_lit 4817577109235213080717673706638105883167086028674371209148014210562584756416639338238058515732768480769601 

noncomputable def Ns168p1482 := nat_lit 683254672943538536827424307866691026841824599864331083187811773525069580728193183190663600319182401 

noncomputable def Ns168p1483 := nat_lit 24074530245490601924350611194588027225949045169980928874639137148475756909158898468759227351396756018116161 

noncomputable def Ns168p1484 := BSN.sin_dyadic_bound_f 172272207 134217728 4 3 134217728 67108864 Ns168p1481 Ns168p144 Ns168p1482 Ns168p1483 Ns168p147 Ns168p1482 128717675 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 172272207) qz361 0 3 Ns168p1481 Ns168p144 Ns168p1482 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 172272207) qz362 0 3 Ns168p1483 Ns168p147 Ns168p1482 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1485 := nat_lit 238644888073030237109214545887333329590258563959878485145817349300480 

noncomputable def Ns168p1486 := nat_lit 59108028539911014974209752437476081795038856535657403991742423296 

noncomputable def Ns168p1487 := nat_lit 624926627192681241261794137724783759080151890317671634823058808054016 

noncomputable def Ns168p1488 := BSN.sin_dyadic_bound_f 124869338 134217728 3 2 134217728 67108864 Ns168p1485 Ns168p112 Ns168p1486 Ns168p1487 Ns168p115 Ns168p1486 107619609 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 124869338) qz361 0 2 Ns168p1485 Ns168p112 Ns168p1486 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 124869338) qz362 0 2 Ns168p1487 Ns168p115 Ns168p1486 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1489 := Ns168p1432 88247 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 45 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 128717675 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 89 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 107619609 134217728) qz180 rfl rfl (Ns168p1480 rfl rfl) (Ns168p1467 rfl) RS169to186.d27 RS169to186.d29 RS169to186.d31 RS169to186.d33 RS169to186.d17 (Ns168p1484 rfl rfl) (Ns168p1488 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns168p1490 := nat_lit 133308268807157938277006213249164027443316475987663809826361778519105 

noncomputable def Ns168p1491 := nat_lit 18448086681421574075313448683016110698720183030881749326036089921 

noncomputable def Ns168p1492 := nat_lit 349110835687929441510322908164228521981840461576117121951086313880641 

noncomputable def Ns168p1493 := BSN.sin_dyadic_bound_f 107955287 134217728 3 2 134217728 67108864 Ns168p1490 Ns168p112 Ns168p1491 Ns168p1492 Ns168p115 Ns168p1491 96685860 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 107955287) qz361 0 2 Ns168p1490 Ns168p112 Ns168p1491 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 107955287) qz362 0 2 Ns168p1492 Ns168p115 Ns168p1491 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1494 := Ns168p1430 Bool.true 275262934 88247 Bool.true 107955287 7074237752028440 1 Bool.false 96685860 Bool.false Bool.true 241079324 98335 BSN.abs_quadSignPos qz365 (BSN.sfrac_eq_quadSignPos_mul Bool.false 96685860 134217728) qz180 rfl (Ns168p1489 rfl) (Ns168p1467 rfl) RS169to186.d35 RS169to186.d37 RS169to186.d17 (Ns168p1493 rfl rfl) rfl 

noncomputable def Ns168p1495 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz177) qz177 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz177) qz177 8) 241079324 134217728 98335 134217728 241079324 134217728 98335 134217728 64714238270111744 60269831 16777216 98335 67108864 (Ns168p1494 rfl rfl rfl rfl) 

noncomputable def Ns168p1496 := @Enclosure.Real.IsNear.mulLit_ff qz767 (Zeta.RiemannSiegel.correction qz179) 1444955 4194304 1 8388608 27611072548605 70368744177664 172955844863521 6597069766656000000 39896757334469537775 295147905179352825856 

noncomputable abbrev qz771 := (@HPow.hPow Real Real Real qz7 qz178 qz9)

noncomputable def Ns168p1497 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz771 1 1 0 1 1444955 4194304 1 8388608 1444955 4194304 1 8388608 

noncomputable def Ns168p1498 := @Enclosure.Real.IsNear.sqrt_image qz178 1191083184213 16777216000 446069 16777216000 70680712 70680739 8388608 (@Enclosure.Real.IsNear.of_eq qz178 (@HMul.hMul Real Real Real qz5 qz177 qz3) Bool.false 1191083184213 16777216000 446069 16777216000 (BSN.t_div_two_pi_mk qz177 446069 1000 qz180) (@Enclosure.Real.IsNear.mulLit_ff qz177 qz3 446069 1000 0 1 2670177 16777216 1 16777216 1191083184213 16777216000 446069 16777216000 (Enclosure.Real.IsNear.const Bool.false 446069 1000) RS169to186.d40 rfl)) 

noncomputable abbrev qz944 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 446069 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz772 := qz944

noncomputable abbrev qz531 := qz772

noncomputable abbrev qz182 := qz531

noncomputable def Ns168p1499 := @Enclosure.Real.IsNear.sqrt_image qz182 141361451 16777216 27 16777216 24349800 24349806 8388608 (@Enclosure.Real.IsNear.recentre' qz182 Bool.false 141361451 16777216 27 16777216 141361451 16777216 27 16777216 (Ns168p1498 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns168p1500 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz182) 24349803 8388608 3 8388608 2889909 2889911 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz182) Bool.false 48699606 16777216 6 16777216 24349803 8388608 3 8388608 (Ns168p1499 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns168p1501 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz182)) Bool.false 5779820 16777216 2 16777216 1444955 4194304 1 8388608 (Ns168p1500 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz183 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz525))

noncomputable abbrev qz773 := (@HMul.hMul Real Real Real qz890 qz943 qz943)

noncomputable abbrev qz532 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz773 qz766) qz641)

noncomputable abbrev qz184 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz532))

noncomputable def Ns168p1502 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz179) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz183) qz184) Bool.false 27611072548605 

noncomputable def Ns168p1503 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz183) qz184 18781701 16777216 225 

noncomputable abbrev qz774 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz183))

noncomputable def Ns168p1504 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz183) (@Neg.neg Real Real.instNeg qz774) Bool.true 18781701 16777216 225 16777216 (BSN.inv_eq_neg_inv_neg qz183) 

noncomputable def Ns168p1505 := @Enclosure.Real.IsNear.recentre' qz774 Bool.false 18781701 16777216 225 16777216 18781701 16777216 

noncomputable def Ns168p1506 := @Enclosure.Real.IsNear.recentre' qz183 Bool.true 14986661 16777216 401527216 37748736000000 14986661 16777216 25095451 2359296000000 

noncomputable abbrev qz185 := (@HMul.hMul Real Real Real qz342 qz340 qz525)

noncomputable def Ns168p1507 := @Enclosure.Real.IsNear.cos_image qz185 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44885335) qz370) Bool.false 44885335 16777216 171 16777216 Bool.true 14986661 16777216 1 

noncomputable def Ns168p1508 := nat_lit 23058430092136939520000000000 

noncomputable def Ns168p1509 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz179 884279719003555 140737488355328 1 500000000000000 7143723 16777216 27 16777216 6317049367079232935265 2361183241434822606848 233159691553777068992937 

noncomputable def Ns168p1510 := @Enclosure.Real.IsNear.subLit_ff_p qz182 qz1 141361451 16777216 27 16777216 8 1 0 1 7143723 7143723 16777216 27 

noncomputable def Ns168p1511 := @Ns168p1510 16777216 (@Enclosure.Real.IsNear.recentre' qz182 Bool.false 141361451 16777216 27 16777216 141361451 16777216 27 16777216 (Ns168p1498 rfl rfl rfl rfl rfl rfl) rfl) qz371 

noncomputable def Ns168p1512 := @Enclosure.Real.IsNear.recentre' qz185 Bool.false 6317049367079232935265 2361183241434822606848 233159691553777068992937 Ns168p1508 44885335 16777216 171 16777216 (@Ns168p1509 Ns168p1508 RS169to186.d39 (Ns168p1511 rfl rfl) rfl) 

noncomputable def Ns168p1513 := nat_lit 2670706021736457793699840 

noncomputable def Ns168p1514 := nat_lit 8749435984278184685393695330956880326373261452041170759307341735240387407501915412808865 

noncomputable def Ns168p1515 := nat_lit 4304971500206750757486332955604327463473764455840404553154449445642190355467757470881 

noncomputable def Ns168p1516 := nat_lit 22908219528775863246233271803911327181751012946226943714623644959860451092405687807165601 

noncomputable def Ns168p1517 := BSN.sin_dyadic_bound_f 37953015261 34359738368 3 2 16777216 4504395 Ns168p1514 Ns168p1076 Ns168p1515 Ns168p1516 Ns168p1079 Ns168p1515 14986661 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 37953015261) qz358 0 2 Ns168p1514 Ns168p1076 Ns168p1515 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 37953015261) qz359 0 2 Ns168p1516 Ns168p1079 Ns168p1515 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1518 := @Ns168p1507 2250000 (Ns168p1512 rfl) (Enclosure.sfrac_false_div 44885335 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44885335) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns168p1513) qz385) 226375608064910080 72057594037927936 Bool.false 14986661 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 44885335 16777216 226375608064910080 72057594037927936 0 Ns168p1513 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 14986661 16777216 Ns168p1513 Ns168p89 37953015261 34359738368 4504395 4500000 (Ns168p1517 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p1519 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz183) 14986661 16777216 25095451 2359296000000 9390738 9390963 8388608 (@Enclosure.Real.IsNear.neg qz183 Bool.true 14986661 16777216 25095451 2359296000000 (Ns168p1506 (Ns168p1518 rfl rfl) rfl)) 

noncomputable def Ns168p1520 := Ns168p1504 (@Enclosure.Real.IsNear.neg qz774 Bool.false 18781701 16777216 225 16777216 (@Ns168p1505 225 16777216 (Ns168p1519 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p1521 := @Enclosure.Real.IsNear.recentre' qz184 Bool.true 2940210 8388608 

noncomputable abbrev qz186 := (@HMul.hMul Real Real Real qz342 qz340 qz532)

noncomputable def Ns168p1522 := @Enclosure.Real.IsNear.cos_image qz186 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16180799)) qz360) Bool.true 16180799 8388608 

noncomputable def Ns168p1523 := nat_lit 76411664190426663147736729525 

noncomputable def Ns168p1524 := nat_lit 22634479078379795086407906830681261 

noncomputable def Ns168p1525 := @Enclosure.Real.IsNear.recentre' qz186 Bool.true Ns168p1523 Ns168p178 Ns168p1524 

noncomputable abbrev qz187 := qz532

noncomputable def Ns168p1526 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz187 884279719003555 140737488355328 1 500000000000000 86411191558855 

noncomputable abbrev qz533 := (@HSub.hSub Real Real Real qz633 qz773 qz766)

noncomputable abbrev qz188 := qz533

noncomputable def Ns168p1527 := @Enclosure.Real.IsNear.subLit_tf qz188 qz25 68819005514439 281474976710656 838746603 281474976710656 1 16 

noncomputable abbrev qz534 := qz773

noncomputable abbrev qz189 := qz534

noncomputable def Ns168p1528 := @Enclosure.Real.IsNear.subLit_ff_n qz189 qz179 51032778300729 281474976710656 385761771 281474976710656 7143723 16777216 27 16777216 

noncomputable def Ns168p1529 := @Enclosure.Real.IsNear.mulLit_ff qz179 qz179 7143723 16777216 27 16777216 7143723 16777216 27 16777216 51032778300729 281474976710656 

noncomputable def Ns168p1530 := nat_lit 33823057713519094492018590475546992828094441693096152948797206198020678134863350800298497281 

noncomputable def Ns168p1531 := nat_lit 322106550325639525751781036461839420610085308157862996419018062730309115631254216070401 

noncomputable def Ns168p1532 := nat_lit 204073603280206487999909465473694837692417762947550611558868117216517125047101173085833745665 

noncomputable def Ns168p1533 := BSN.cos_dyadic_bound_t 16180799 8388608 4 3 8388608 2250000 Ns168p1530 Ns168p187 Ns168p1531 Ns168p1532 Ns168p190 Ns168p1531 2940210 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16180799) (BSN.cosEvenQ 8388608) 0 3 Ns168p1530 Ns168p187 Ns168p1531 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16180799) (BSN.cosOddQ 8388608) 0 3 Ns168p1532 Ns168p190 Ns168p1531 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1534 := @Ns168p1521 725527216 37748736000000 1470105 4194304 45345451 2359296000000 (@Ns168p1522 315 16777216 Bool.true 2940210 8388608 1 2250000 (@Ns168p1525 Ns168p181 16180799 8388608 315 16777216 (@Ns168p1526 281474976710656 838746603 281474976710656 Ns168p1523 Ns168p178 Ns168p1524 Ns168p181 RS169to186.d39 (@Ns168p1527 0 1 1382579064941680 86411191558855 281474976710656 838746603 281474976710656 (@Ns168p1528 1154591320420934221824 68819005514439 281474976710656 838746603 281474976710656 (@Ns168p1529 385761771 281474976710656 (Ns168p1511 rfl rfl) (Ns168p1511 rfl rfl) rfl) (Ns168p1511 rfl rfl) rfl rfl) qz375 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16180799 8388608) (BSN.cos_neg_of_bound 16180799 8388608 Bool.true 2940210 8388608 1 2250000 (Ns168p1533 rfl rfl)) rfl rfl) 

noncomputable def Ns168p1535 := @Ns168p1496 502415536636814555381 Ns168p1427 (Ns168p1497 qz27 (@Enclosure.Real.IsNear.of_eq qz771 (@Inv.inv Real Real.instInv (Real.sqrt qz182)) Bool.false 1444955 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz178 (BSN.t_div_two_pi_nonneg qz177 446069 1000 qz180)) Ns168p1501) rfl) (@Ns168p1502 70368744177664 172955844863521 6597069766656000000 (BSN.correction_mk qz179 (BSN.cos_two_pi_p_ne_zero_mk qz177 446069 1000 8 qz180 rfl rfl (@BSN.floor_sqrt_eq_dec qz177 446069 1000 8 qz180 rfl rfl rfl))) (@Ns168p1503 16777216 1470105 4194304 45345451 2359296000000 27611072548605 70368744177664 172955844863521 6597069766656000000 Ns168p1520 (Ns168p1534 rfl) rfl)) 

noncomputable def Ns168p1536 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz177) (hardyZApproximantRS₀ qz177) Bool.true 1100174837151980351471 295147905179352825856 81592772474651534555381 Ns168p1427 (@Eq.refl Real (hardyZApproximantRS₀ qz177)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz177) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz177) qz177 8) (@HMul.hMul Real Real Real qz5 qz767 (Zeta.RiemannSiegel.correction qz179))) Bool.true 1100174837151980351471 295147905179352825856 81592772474651534555381 Ns168p1427 (BSN.hardyZApproximantRS₀_eq qz177 8 (@BSN.floor_sqrt_eq_dec qz177 446069 1000 8 qz180 rfl rfl rfl)) (@Ns168p1429 1100174837151980351471 295147905179352825856 81592772474651534555381 Ns168p1427 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz177) qz177 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz177) qz177 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz177) qz177 8)) Bool.true 60269831 16777216 98335 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz177) qz177 8) (Ns168p1495 (Ns168p1494 rfl rfl rfl rfl) rfl rfl)) (Ns168p1535 rfl) rfl rfl)) 

theorem RS169to186.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz177) Bool.true 1100174837151980351471 295147905179352825856 81592772474651534555381 Ns168p1427 := Ns168p1536 

noncomputable def Ns168p1537 := nat_lit 3088109592282694892791005184 

noncomputable abbrev qz945 := (Enclosure.sfrac Bool.false 447174 1000)

noncomputable abbrev qz775 := qz945

noncomputable abbrev qz535 := qz775

noncomputable abbrev qz190 := qz535

noncomputable abbrev qz946 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 447174 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz776 := qz946

noncomputable abbrev qz536 := qz776

noncomputable abbrev qz191 := qz536

noncomputable abbrev qz947 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 447174 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz777 := qz947

noncomputable abbrev qz537 := qz777

noncomputable abbrev qz192 := qz537

noncomputable abbrev qz778 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz191 qz9))

noncomputable def Ns168p1538 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz190) qz190 8) (@HMul.hMul Real Real Real qz5 qz778 (Zeta.RiemannSiegel.correction qz192)) 14966443 33554432 24643 16777216 39613387201830564507 295147905179352825856 4899905771563094599 553402322211286548480000 Ns168p1537 

noncomputable def Ns168p1539 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz190) qz190 Real.sin BSN.quadSignPos 7 8 447174 1000 127 134217728 67108864 2251799813685248 Bool.false 97929913520 1744 279097919 60 47453128 8 

noncomputable def Ns168p1540 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz190) qz190 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 447174 1000 45 89 134217728 67108864 2251799813685248 Bool.false 97929913520 1744 

noncomputable def Ns168p1541 := Ns168p1540 240485871 61 54794152 8 261175631 61 50729528 8 Bool.false 74528696 65622 Bool.true 121823222 Bool.true 97282538 7074237752028440 1 Bool.false 105771831 Bool.true Bool.false 88985582 Bool.true Bool.true 2285854 

noncomputable def Ns168p1542 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz190) qz190 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 447174 1000 69 6 134217728 67108864 2251799813685248 Bool.false 97929913520 1744 

noncomputable def Ns168p1543 := Ns168p1542 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 192131742 38536 Bool.false 179183880 Bool.false 68610273 7074237752028440 1 Bool.false 130504488 Bool.true Bool.false 117059969 Bool.true Bool.false 74528696 

noncomputable def Ns168p1544 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz190) qz190 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 447174 1000 267 151 134217728 67108864 2251799813685248 Bool.false 97929913520 1744 

noncomputable def Ns168p1545 := Ns168p1544 93032624 60 94906264 8 147453232 60 77490640 16 Bool.false 94923368 1804 Bool.false 36876241 Bool.false 157526119 7074237752028440 1 Bool.false 36414041 Bool.false Bool.false 123771936 Bool.false Bool.false 192131742 

noncomputable def Ns168p1546 := nat_lit 821062429480598507383107811087301437680281919045748263 

noncomputable def Ns168p1547 := nat_lit 1125306148744953066898186154068581252236394364928000 

noncomputable def Ns168p1548 := nat_lit 8582727721997984406587162219520000 

noncomputable def Ns168p1549 := nat_lit 23027849553510754053794870257245818880 

noncomputable abbrev qz538 := (@Eq.refl Real qz775)

noncomputable abbrev qz193 := qz538

noncomputable def Ns168p1550 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz190 447174 1000 799859345104 16000000 894348 4000 2000 Ns168p1548 Ns168p1549 qz193 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns168p1551 := nat_lit 151338227001863916880854431739611400993229563318512319836160 

noncomputable abbrev qz779 := (Real.log (Enclosure.sfrac Bool.false 799859345104 16000000))

noncomputable abbrev qz194 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 447174 4000) qz779) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 894348))))))

noncomputable abbrev qz780 := (Enclosure.sfrac Bool.false 447174 2000)

noncomputable abbrev qz539 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz194 qz780) (@HMul.hMul Real Real Real qz5 qz780 (Real.log Real.pi)))

noncomputable def Ns168p1552 := @Enclosure.Real.IsNear.addLit_ft_p qz539 (Enclosure.sfrac Bool.true Ns168p1548 Ns168p1549) 6571968605081063363307 9007199254740992000 23934458223518963 1843200000000000000000 Ns168p1548 Ns168p1549 0 1 Ns168p1551 

noncomputable def Ns168p1553 := nat_lit 220518673665327395111776026624000 

noncomputable abbrev qz540 := (@HSub.hSub Real Real Real qz12 qz194 qz780)

noncomputable abbrev qz541 := (@HMul.hMul Real Real Real qz5 qz780 (Real.log Real.pi))

noncomputable def Ns168p1554 := @Enclosure.Real.IsNear.subLit_ff_p qz540 qz541 8877331712824061694699 9007199254740992000 22758706037299 3600000000000000000 8588146819707 33554432000 223587 33554432000 Ns168p1553 6571968605081063363307 9007199254740992000 

noncomputable def Ns168p1555 := nat_lit 17754663425648123389398000 

noncomputable abbrev qz542 := qz780

noncomputable def Ns168p1556 := @Enclosure.Real.IsNear.subLit_ff_p qz194 qz542 10891224372593835873003 9007199254740992000 22758706037299 3600000000000000000 447174 2000 0 1 Ns168p1555 8877331712824061694699 9007199254740992000 22758706037299 3600000000000000000 

noncomputable def Ns168p1557 := nat_lit 24524857013011031662652027992742559744 

noncomputable def Ns168p1558 := nat_lit 26160193509871100182396928 

noncomputable def Ns168p1559 := nat_lit 172261266047745926699479675124758200393497396665472932559698657763684008424669992192784336886897299943824638892628082446827520 

noncomputable def Ns168p1560 := nat_lit 2553615503577858765213918400782200637183834031400393640621960866339504271985360763469259780123464391823907088218581373026304 

noncomputable def Ns168p1561 := nat_lit 2386560066118479180365629824316060940336696400186269508267925709525767906253353407037490473925450848217405524876984320 

noncomputable def Ns168p1562 := BSN.log_dyadic_bound 275571345104 1324147345104 6 5 Ns168p1559 67108864 18000000 Ns168p1560 Ns168p1561 28346431 1599718690208 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 275571345104) (BSN.artanhQ 1324147345104) 0 5 Ns168p1560 Ns168p1559 Ns168p1561 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns168p1563 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 447174 4000) qz779 447174 4000 0 1 48727157544104569 4503599627370496 100000027 1800000000000000 10894758973813708269003 9007199254740992000 2484300670761 400000000000000000 (Enclosure.Real.IsNear.const Bool.false 447174 4000) (BSN.isNear_log_sfrac 799859345104 16000000 48727157544104569 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 799859345104) qz353)) Bool.false Ns168p1558 Ns168p89 1000000270000000 18000000000000000000000 48727157544104569 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 799859345104 16000000 15 1599718690208 1048576000000 28346431 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns168p1562 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p1564 := BSN.arctan_dyadic_bound_f 1000 894348 1 0 8388608 2250000 0 1 1 0 1 1 9379 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 894348) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 894348) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz781 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 894348)))

noncomputable def Ns168p1565 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz781 884279719003555 562949953421312 1 2000000000000000 9379 8388608 1 2250000 7412596017457835016192 883650304968099 562949953421312 8000000009 18000000000000000 qz16 (Ns168p1564 rfl) rfl rfl 

noncomputable def Ns168p1566 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 447174 4000) qz779) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz781)) 10894758973813708269003 9007199254740992000 2484300670761 400000000000000000 883650304968099 2251799813685248 8000000009 72000000000000000 Ns168p1557 10891224372593835873003 9007199254740992000 22758706037299 3600000000000000000 (Ns168p1563 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz781) 1 4 0 1 883650304968099 562949953421312 8000000009 18000000000000000 883650304968099 2251799813685248 8000000009 72000000000000000 qz356 Ns168p1565 rfl) 

noncomputable def Ns168p1567 := @Ns168p1552 Ns168p1546 Ns168p1547 23934458223518963 1843200000000000000000 (@Ns168p1554 23934458223518963 1843200000000000000000 (Ns168p1556 (Ns168p1566 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 447174 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz542 (Real.log Real.pi) 447174 2000 0 1 38410761 33554432 1 33554432 8588146819707 33554432000 223587 33554432000 (Enclosure.Real.IsNear.const Bool.false 447174 2000) RS169to186.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns168p1548 Ns168p1549) 

noncomputable def Ns168p1568 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz190) Bool.false Ns168p1546 Ns168p1547 23934458223518963 1843200000000000000000 6120619595 8388608 109 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz190) (@HAdd.hAdd Real Real Real qz357 qz539 (Enclosure.sfrac Bool.true Ns168p1548 Ns168p1549)) Bool.false Ns168p1546 Ns168p1547 23934458223518963 1843200000000000000000 Ns168p1550 (Ns168p1567 rfl rfl)) 

noncomputable def Ns168p1569 := nat_lit 1240986594234602153323967108596760583182014457306045038092643583880430591092699506775361 

noncomputable def Ns168p1570 := nat_lit 78328409734541396139472704083124282315821843750582265496873076360672620779474006646456320 

noncomputable def Ns168p1571 := nat_lit 280750349944451339954111317114889790208529002796340864629582372606591063287600092481 

noncomputable def Ns168p1572 := nat_lit 3722398282003917557291993103156051969965626313912542432548671586896078591151523320141121 

noncomputable def Ns168p1573 := nat_lit 3524778438054362826276271683740592704211982968776201947359288436230267935076330299090534400 

noncomputable def Ns168p1574 := BSN.cos_dyadic_bound_f 26979881527 34359738368 3 2 16777216 4504395 Ns168p1569 Ns168p1570 Ns168p1571 Ns168p1572 Ns168p1573 Ns168p1571 11865421 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 26979881527) qz682 0 2 Ns168p1569 Ns168p1570 Ns168p1571 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 26979881527) qz683 0 2 Ns168p1572 Ns168p1573 Ns168p1571 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1575 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz190) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6120619595) qz360) Bool.false 6120619595 8388608 109 8388608 Bool.false 11865421 16777216 1 2250000 (Ns168p1568 rfl) (Enclosure.sfrac_false_div 6120619595 8388608) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6120619595) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949270190563280163962880) qz636) 226375608064910080 72057594037927936 Bool.false 11865421 16777216 116 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q0 6120619595 8388608 226375608064910080 72057594037927936 116 949270190563280163962880 Ns168p101 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 11865421 16777216 949270190563280163962880 Ns168p101 26979881527 34359738368 4504395 4500000 (Ns168p1574 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p1576 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz190) Bool.false Ns168p1546 Ns168p1547 23934458223518963 1843200000000000000000 97929913520 134217728 1744 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz190) (@HAdd.hAdd Real Real Real qz357 qz539 (Enclosure.sfrac Bool.true Ns168p1548 Ns168p1549)) Bool.false Ns168p1546 Ns168p1547 23934458223518963 1843200000000000000000 Ns168p1550 (Ns168p1567 rfl rfl)) 

noncomputable def Ns168p1577 := Ns168p1545 38536 BSN.abs_quadSignPos (BSN.cos_quad_nat3 267 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 36414041 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 151 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 123771936 134217728) qz193 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz190) qz190 1) Bool.false 11865421 16777216 15852413 1179648000000 94923368 134217728 1804 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz190) qz190 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz190)) Bool.false 11865421 16777216 15852413 1179648000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz190) qz190) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz190)) Bool.false 11865421 16777216 253638608 18874368000000 11865421 16777216 15852413 1179648000000 (Ns168p1575 rfl rfl) rfl)) rfl) (Ns168p1576 rfl) RS169to186.d7 

noncomputable def Ns168p1578 := nat_lit 1849211469195059943942446986561 

noncomputable def Ns168p1579 := BSN.sin_dyadic_bound_f 36876241 134217728 2 1 134217728 67108864 Ns168p1578 Ns168p394 Ns168p1578 Ns168p1578 Ns168p395 Ns168p1578 36414041 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 36876241) qz361 0 1 Ns168p1578 Ns168p394 Ns168p1578 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 36876241) qz362 0 1 Ns168p1578 Ns168p395 Ns168p1578 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1580 := nat_lit 604649963116731850729485945725120068271728364937005338401728171772865 

noncomputable def Ns168p1581 := nat_lit 379158316913379782484251907018910069743233880855734243399294946241 

noncomputable def Ns168p1582 := nat_lit 1582993170887866517977012497621093372027323339027914221324736829492161 

noncomputable def Ns168p1583 := BSN.sin_dyadic_bound_f 157526119 134217728 3 2 134217728 67108864 Ns168p1580 Ns168p112 Ns168p1581 Ns168p1582 Ns168p115 Ns168p1581 123771936 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 157526119) qz361 0 2 Ns168p1580 Ns168p112 Ns168p1581 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 157526119) qz362 0 2 Ns168p1582 Ns168p115 Ns168p1581 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1584 := nat_lit 5639361409979042203961811028660944185225633023100980441584882823241731174024697740360641592559036006400000 

noncomputable def Ns168p1585 := nat_lit 1095436575406277820566897580741683739797595114498179954271739196961642733751933501177856000000000000 

noncomputable def Ns168p1586 := nat_lit 28178511790750121654040399886424292259727814808838101094878117413145863649682297544168692831100076032000000 

noncomputable def Ns168p1587 := BSN.sin_dyadic_bound_f 179183880 134217728 4 3 134217728 67108864 Ns168p1584 Ns168p144 Ns168p1585 Ns168p1586 Ns168p147 Ns168p1585 130504488 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 179183880) qz361 0 3 Ns168p1584 Ns168p144 Ns168p1585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 179183880) qz362 0 3 Ns168p1586 Ns168p147 Ns168p1585 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1588 := nat_lit 12081561098710757349045693157788883732519760206847638289362714146561 

noncomputable def Ns168p1589 := nat_lit 491035825614785028654027997651842323708502176839111146439489281 

noncomputable def Ns168p1590 := nat_lit 36243701224481042477079771417371347512911863616189236645795263461121 

noncomputable def Ns168p1591 := BSN.cos_dyadic_bound_f 68610273 134217728 3 2 134217728 67108864 Ns168p1588 Ns168p124 Ns168p1589 Ns168p1590 Ns168p127 Ns168p1589 117059969 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 68610273) qz363 0 2 Ns168p1588 Ns168p124 Ns168p1589 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 68610273) qz364 0 2 Ns168p1590 Ns168p127 Ns168p1589 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1592 := Ns168p1543 65622 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 69 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 130504488 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 6 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 117059969 134217728) qz193 rfl rfl (Ns168p1577 RS169to186.d9 RS169to186.d11 RS169to186.d13 RS169to186.d17 (Ns168p1579 rfl rfl) (Ns168p1583 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns168p1576 rfl) RS169to186.d19 RS169to186.d21 RS169to186.d23 RS169to186.d25 RS169to186.d17 (Ns168p1587 rfl rfl) (Ns168p1591 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns168p1593 := nat_lit 216191744919244167003476883303894277122351321815045565160091439980800 

noncomputable def Ns168p1594 := nat_lit 48511047544621123716964398501393559578895836918820196172673966336 

noncomputable def Ns168p1595 := nat_lit 566137933092472003189754847245958945747792392446298390339769442099456 

noncomputable def Ns168p1596 := BSN.sin_dyadic_bound_f 121823222 134217728 3 2 134217728 67108864 Ns168p1593 Ns168p112 Ns168p1594 Ns168p1595 Ns168p115 Ns168p1594 105771831 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 121823222) qz361 0 2 Ns168p1593 Ns168p112 Ns168p1594 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 121823222) qz362 0 2 Ns168p1595 Ns168p115 Ns168p1594 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1597 := nat_lit 87902357612557833342183019205799636918644726464062558437580881486080 

noncomputable def Ns168p1598 := nat_lit 8021935004951910451103342621133727917728637180559951292642058496 

noncomputable def Ns168p1599 := nat_lit 230207472519072022326891835365231499227440818183776270272523745321216 

noncomputable def Ns168p1600 := BSN.sin_dyadic_bound_f 97282538 134217728 3 2 134217728 67108864 Ns168p1597 Ns168p112 Ns168p1598 Ns168p1599 Ns168p115 Ns168p1598 88985582 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 97282538) qz361 0 2 Ns168p1597 Ns168p112 Ns168p1598 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 97282538) qz362 0 2 Ns168p1599 Ns168p115 Ns168p1598 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1601 := Ns168p1541 88459 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 45 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 105771831 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 89 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 88985582 134217728) qz193 rfl rfl (Ns168p1592 rfl rfl) (Ns168p1576 rfl) RS169to186.d27 RS169to186.d29 RS169to186.d31 RS169to186.d33 RS169to186.d17 (Ns168p1596 rfl rfl) (Ns168p1600 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns168p1602 := nat_lit 98823884830974406778092650638618656185077409221716557291543837330625 

noncomputable def Ns168p1603 := nat_lit 10138929172699965755544073719986874340866031288046233342687890625 

noncomputable def Ns168p1604 := nat_lit 258808044862462884474257489838930787450079431530029384719107603090625 

noncomputable def Ns168p1605 := BSN.sin_dyadic_bound_f 100172615 134217728 3 2 134217728 67108864 Ns168p1602 Ns168p112 Ns168p1603 Ns168p1604 Ns168p115 Ns168p1603 91128369 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 100172615) qz361 0 2 Ns168p1602 Ns168p112 Ns168p1603 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 100172615) qz362 0 2 Ns168p1604 Ns168p115 Ns168p1603 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1606 := Ns168p1539 Bool.true 2285854 88459 Bool.true 100172615 7074237752028440 1 Bool.false 91128369 Bool.false Bool.false 29932886 98572 BSN.abs_quadSignPos qz365 (BSN.sfrac_eq_quadSignPos_mul Bool.false 91128369 134217728) qz193 rfl (Ns168p1601 rfl) (Ns168p1576 rfl) RS169to186.d35 RS169to186.d37 RS169to186.d17 (Ns168p1605 rfl rfl) rfl 

noncomputable def Ns168p1607 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz190) qz190 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz190) qz190 8) 29932886 134217728 98572 134217728 29932886 134217728 98572 134217728 8035047902806016 14966443 33554432 24643 16777216 (Ns168p1606 rfl rfl rfl rfl) 

noncomputable def Ns168p1608 := @Enclosure.Real.IsNear.mulLit_ff qz778 (Zeta.RiemannSiegel.correction qz192) 2888123 8388608 1 8388608 13715962651809 35184372088832 5062997649953 197912092999680000 39613387201830564507 295147905179352825856 

noncomputable abbrev qz782 := (@HPow.hPow Real Real Real qz7 qz191 qz9)

noncomputable def Ns168p1609 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz782 1 1 0 1 2888123 8388608 1 8388608 2888123 8388608 1 8388608 

noncomputable def Ns168p1610 := @Enclosure.Real.IsNear.sqrt_image qz191 597016864899 8388608000 223587 8388608000 70768203 70768230 8388608 (@Enclosure.Real.IsNear.of_eq qz191 (@HMul.hMul Real Real Real qz5 qz190 qz3) Bool.false 597016864899 8388608000 223587 8388608000 (BSN.t_div_two_pi_mk qz190 447174 1000 qz193) (@Enclosure.Real.IsNear.mulLit_ff qz190 qz3 447174 1000 0 1 2670177 16777216 1 16777216 597016864899 8388608000 223587 8388608000 (Enclosure.Real.IsNear.const Bool.false 447174 1000) RS169to186.d40 rfl)) 

noncomputable abbrev qz948 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 447174 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz783 := qz948

noncomputable abbrev qz543 := qz783

noncomputable abbrev qz195 := qz543

noncomputable def Ns168p1611 := @Enclosure.Real.IsNear.sqrt_image qz195 141536433 16777216 27 16777216 24364866 24364872 8388608 (@Enclosure.Real.IsNear.recentre' qz195 Bool.false 141536433 16777216 27 16777216 141536433 16777216 27 16777216 (Ns168p1610 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns168p1612 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz195) 24364869 8388608 3 8388608 2888122 2888124 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz195) Bool.false 48729738 16777216 6 16777216 24364869 8388608 3 8388608 (Ns168p1611 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns168p1613 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz195)) Bool.false 5776246 16777216 2 16777216 2888123 8388608 1 8388608 (Ns168p1612 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz196 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz537))

noncomputable abbrev qz784 := (@HMul.hMul Real Real Real qz890 qz947 qz947)

noncomputable abbrev qz544 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz784 qz777) qz641)

noncomputable abbrev qz197 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz544))

noncomputable def Ns168p1614 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz192) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz196) qz197) Bool.false 13715962651809 

noncomputable def Ns168p1615 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz196) qz197 18220389 16777216 211 

noncomputable abbrev qz785 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz196))

noncomputable def Ns168p1616 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz196) (@Neg.neg Real Real.instNeg qz785) Bool.true 18220389 16777216 211 16777216 (BSN.inv_eq_neg_inv_neg qz196) 

noncomputable def Ns168p1617 := @Enclosure.Real.IsNear.recentre' qz785 Bool.false 18220389 16777216 211 16777216 18220389 16777216 

noncomputable def Ns168p1618 := @Enclosure.Real.IsNear.recentre' qz196 Bool.true 15448352 16777216 401527216 37748736000000 482761 524288 25095451 2359296000000 

noncomputable abbrev qz198 := (@HMul.hMul Real Real Real qz342 qz340 qz537)

noncomputable def Ns168p1619 := @Enclosure.Real.IsNear.cos_image qz198 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 45984779) qz370) Bool.false 45984779 16777216 171 16777216 Bool.true 15448352 16777216 1 

noncomputable def Ns168p1620 := nat_lit 728624036107056424537705469 

noncomputable def Ns168p1621 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz192 884279719003555 140737488355328 1 500000000000000 7318705 16777216 27 16777216 6471782400869912996275 2361183241434822606848 Ns168p1620 

noncomputable def Ns168p1622 := @Enclosure.Real.IsNear.subLit_ff_p qz195 qz1 141536433 16777216 27 16777216 8 1 0 1 7318705 7318705 16777216 27 

noncomputable def Ns168p1623 := @Ns168p1622 16777216 (@Enclosure.Real.IsNear.recentre' qz195 Bool.false 141536433 16777216 27 16777216 141536433 16777216 27 16777216 (Ns168p1610 rfl rfl rfl rfl rfl rfl) rfl) qz371 

noncomputable def Ns168p1624 := @Enclosure.Real.IsNear.recentre' qz198 Bool.false 6471782400869912996275 2361183241434822606848 Ns168p1620 Ns168p163 45984779 16777216 171 16777216 (@Ns168p1621 Ns168p163 RS169to186.d39 (Ns168p1623 rfl rfl) rfl) 

noncomputable def Ns168p1625 := nat_lit 2829152600575329077035008 

noncomputable def Ns168p1626 := nat_lit 11019366018366054222997358665353522717476692972694350638093786645944931188416823923426465 

noncomputable def Ns168p1627 := nat_lit 6826727729647884077429398864687293428232969339621698346305912994850140385217755858081 

noncomputable def Ns168p1628 := nat_lit 28849191536539283533629625096811637213555152025744864159589707832626014789991805337584801 

noncomputable def Ns168p1629 := BSN.sin_dyadic_bound_f 40204676573 34359738368 3 2 16777216 4504395 Ns168p1626 Ns168p1076 Ns168p1627 Ns168p1628 Ns168p1079 Ns168p1627 15448352 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 40204676573) qz358 0 2 Ns168p1626 Ns168p1076 Ns168p1627 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 40204676573) qz359 0 2 Ns168p1628 Ns168p1079 Ns168p1627 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1630 := @Ns168p1619 2250000 (Ns168p1624 rfl) (Enclosure.sfrac_false_div 45984779 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 45984779) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns168p1625) qz385) 226375608064910080 72057594037927936 Bool.false 15448352 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 45984779 16777216 226375608064910080 72057594037927936 0 Ns168p1625 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 15448352 16777216 Ns168p1625 Ns168p89 40204676573 34359738368 4504395 4500000 (Ns168p1629 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p1631 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz196) 482761 524288 25095451 2359296000000 9110089 9110300 8388608 (@Enclosure.Real.IsNear.neg qz196 Bool.true 482761 524288 25095451 2359296000000 (Ns168p1618 (Ns168p1630 rfl rfl) rfl)) 

noncomputable def Ns168p1632 := Ns168p1616 (@Enclosure.Real.IsNear.neg qz785 Bool.false 18220389 16777216 211 16777216 (@Ns168p1617 211 16777216 (Ns168p1631 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p1633 := @Enclosure.Real.IsNear.recentre' qz197 Bool.true 3011124 8388608 

noncomputable abbrev qz199 := (@HMul.hMul Real Real Real qz342 qz340 qz544)

noncomputable def Ns168p1634 := @Enclosure.Real.IsNear.cos_image qz199 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32513291)) qz370) Bool.true 32513291 16777216 

noncomputable def Ns168p1635 := nat_lit 76769838360248923864801945405 

noncomputable def Ns168p1636 := nat_lit 22889471260533443045802286523158409 

noncomputable def Ns168p1637 := @Enclosure.Real.IsNear.recentre' qz199 Bool.true Ns168p1635 Ns168p178 Ns168p1636 

noncomputable abbrev qz200 := qz544

noncomputable def Ns168p1638 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz200 884279719003555 140737488355328 1 500000000000000 86816237792671 

noncomputable abbrev qz545 := (@HSub.hSub Real Real Real qz633 qz784 qz777)

noncomputable abbrev qz201 := qz545

noncomputable def Ns168p1639 := @Enclosure.Real.IsNear.subLit_tf qz201 qz25 69224051748255 281474976710656 848195631 281474976710656 1 16 

noncomputable abbrev qz546 := qz784

noncomputable abbrev qz202 := qz546

noncomputable def Ns168p1640 := @Enclosure.Real.IsNear.subLit_ff_n qz202 qz192 53563442877025 281474976710656 395210799 281474976710656 7318705 16777216 27 16777216 

noncomputable def Ns168p1641 := @Enclosure.Real.IsNear.mulLit_ff qz192 qz192 7318705 16777216 27 16777216 7318705 16777216 27 16777216 53563442877025 281474976710656 

noncomputable def Ns168p1642 := nat_lit 141176975987869054812438645544495684310516464697130907337490219829941630429590765476879535663761 

noncomputable def Ns168p1643 := nat_lit 1395504280157300535181840247455739349698815418550201194123209204620857095639684793576680081 

noncomputable def Ns168p1644 := nat_lit 851712767999711971326980762482479750571410673859555871475847458838163069466388938720456503421585 

noncomputable def Ns168p1645 := BSN.cos_dyadic_bound_t 32513291 16777216 4 3 8388608 2250000 Ns168p1642 Ns168p169 Ns168p1643 Ns168p1644 Ns168p172 Ns168p1643 3011124 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32513291) qz642 0 3 Ns168p1642 Ns168p169 Ns168p1643 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32513291) (BSN.cosOddQ 16777216) 0 3 Ns168p1644 Ns168p172 Ns168p1643 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1646 := @Ns168p1633 366138608 18874368000000 752781 2097152 22883663 1179648000000 (@Ns168p1634 159 8388608 Bool.true 3011124 8388608 1 2250000 (@Ns168p1637 Ns168p181 32513291 16777216 159 8388608 (@Ns168p1638 281474976710656 848195631 281474976710656 Ns168p1635 Ns168p178 Ns168p1636 Ns168p181 RS169to186.d39 (@Ns168p1639 0 1 1389059804682736 86816237792671 281474976710656 848195631 281474976710656 (@Ns168p1640 1161386868575651758080 69224051748255 281474976710656 848195631 281474976710656 (@Ns168p1641 395210799 281474976710656 (Ns168p1623 rfl rfl) (Ns168p1623 rfl rfl) rfl) (Ns168p1623 rfl rfl) rfl rfl) qz375 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32513291 16777216) (BSN.cos_neg_of_bound 32513291 16777216 Bool.true 3011124 8388608 1 2250000 (Ns168p1645 rfl rfl)) rfl rfl) 

noncomputable def Ns168p1647 := @Ns168p1608 4899905771563094599 553402322211286548480000 (Ns168p1609 qz27 (@Enclosure.Real.IsNear.of_eq qz782 (@Inv.inv Real Real.instInv (Real.sqrt qz195)) Bool.false 2888123 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz191 (BSN.t_div_two_pi_nonneg qz190 447174 1000 qz193)) Ns168p1613) rfl) (@Ns168p1614 35184372088832 5062997649953 197912092999680000 (BSN.correction_mk qz192 (BSN.cos_two_pi_p_ne_zero_mk qz190 447174 1000 8 qz193 rfl rfl (@BSN.floor_sqrt_eq_dec qz190 447174 1000 8 qz193 rfl rfl rfl))) (@Ns168p1615 16777216 752781 2097152 22883663 1179648000000 13715962651809 35184372088832 5062997649953 197912092999680000 Ns168p1632 (Ns168p1646 rfl) rfl)) 

noncomputable def Ns168p1648 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz190) (hardyZApproximantRS₀ qz190) Bool.false 92032837637743201637 295147905179352825856 817757857070082134599 553402322211286548480000 (@Eq.refl Real (hardyZApproximantRS₀ qz190)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz190) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz190) qz190 8) (@HMul.hMul Real Real Real qz5 qz778 (Zeta.RiemannSiegel.correction qz192))) Bool.false 92032837637743201637 295147905179352825856 817757857070082134599 553402322211286548480000 (BSN.hardyZApproximantRS₀_eq qz190 8 (@BSN.floor_sqrt_eq_dec qz190 447174 1000 8 qz193 rfl rfl rfl)) (@Ns168p1538 92032837637743201637 295147905179352825856 817757857070082134599 553402322211286548480000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz190) qz190 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz190) qz190 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz190) qz190 8)) Bool.false 14966443 33554432 24643 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz190) qz190 8) (Ns168p1607 (Ns168p1606 rfl rfl rfl rfl) rfl rfl)) (Ns168p1647 rfl) rfl rfl)) 

theorem RS169to186.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz190) Bool.false 92032837637743201637 295147905179352825856 817757857070082134599 553402322211286548480000 := Ns168p1648 

noncomputable def Ns168p1649 := nat_lit 33204139332677192908800000 

noncomputable def Ns168p1650 := nat_lit 42067412921766839523546759168 

noncomputable abbrev qz949 := (Enclosure.sfrac Bool.false 447911 1000)

noncomputable abbrev qz786 := qz949

noncomputable abbrev qz547 := qz786

noncomputable abbrev qz203 := qz547

noncomputable abbrev qz950 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 447911 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz787 := qz950

noncomputable abbrev qz548 := qz787

noncomputable abbrev qz204 := qz548

noncomputable abbrev qz951 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 447911 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz788 := qz951

noncomputable abbrev qz549 := qz788

noncomputable abbrev qz205 := qz549

noncomputable abbrev qz789 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz204 qz9))

noncomputable def Ns168p1651 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz203) qz203 8) (@HMul.hMul Real Real Real qz5 qz789 (Zeta.RiemannSiegel.correction qz205)) 62295783 67108864 98749 67108864 78893798796113730723 590295810358705651712 300560478031034210767 Ns168p1649 Ns168p1650 

noncomputable def Ns168p1652 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz203) qz203 Real.sin BSN.quadSignPos 7 8 447911 1000 127 134217728 67108864 2251799813685248 Bool.false 98140901230 1747 279097919 60 47453128 8 

noncomputable def Ns168p1653 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz203) qz203 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 447911 1000 45 89 134217728 67108864 2251799813685248 Bool.false 98140901230 1747 

noncomputable def Ns168p1654 := Ns168p1653 240485871 61 54794152 8 261175631 61 50729528 8 Bool.true 31589667 65744 Bool.true 88073599 Bool.true 78781268 7074237752028440 1 Bool.false 81887581 Bool.true Bool.false 74334817 Bool.true Bool.true 93116046 

noncomputable def Ns168p1655 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz203) qz203 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 447911 1000 70 6 134217728 67108864 2251799813685248 Bool.false 98140901230 1747 

noncomputable def Ns168p1656 := Ns168p1655 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 69679230 38613 Bool.false 42212777 Bool.false 120394864 7074237752028440 1 Bool.false 127634102 Bool.true Bool.false 83744890 Bool.true Bool.true 31589667 

noncomputable def Ns168p1657 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz203) qz203 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 447911 1000 267 152 134217728 67108864 2251799813685248 Bool.false 98140901230 1747 

noncomputable def Ns168p1658 := Ns168p1657 93032624 60 94906264 8 147453232 60 77490640 16 Bool.true 95001528 1820 Bool.false 179298907 Bool.false 49012083 7074237752028440 1 Bool.false 130531309 Bool.false Bool.false 125367895 Bool.false Bool.false 69679230 

noncomputable def Ns168p1659 := nat_lit 957314036514044952754752855210046887701665643842883997479 

noncomputable def Ns168p1660 := nat_lit 1309224934271262116759795920972679808419407243247616000 

noncomputable def Ns168p1661 := nat_lit 8653688321600712986317798664480000 

noncomputable def Ns168p1662 := nat_lit 23256506663060998305777287970611407680 

noncomputable abbrev qz550 := (@Eq.refl Real qz786)

noncomputable abbrev qz206 := qz550

noncomputable def Ns168p1663 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz203 447911 1000 802498055684 16000000 895822 4000 2000 Ns168p1661 Ns168p1662 qz206 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns168p1664 := nat_lit 306340491684494384881520913667215004064533006029722879193280 

noncomputable abbrev qz790 := (Real.log (Enclosure.sfrac Bool.false 802498055684 16000000))

noncomputable abbrev qz207 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 447911 4000) qz790) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 895822))))))

noncomputable abbrev qz791 := (Enclosure.sfrac Bool.false 447911 2000)

noncomputable abbrev qz551 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz207 qz791) (@HMul.hMul Real Real Real qz5 qz791 (Real.log Real.pi)))

noncomputable def Ns168p1665 := @Enclosure.Real.IsNear.addLit_ft_p qz551 (Enclosure.sfrac Bool.true Ns168p1661 Ns168p1662) 13172255490204569498671 18014398509481984000 47947135476366839 3686400000000000000000 Ns168p1661 Ns168p1662 0 1 Ns168p1664 

noncomputable def Ns168p1666 := nat_lit 883975102265391786664860319744000 

noncomputable abbrev qz552 := (@HSub.hSub Real Real Real qz12 qz207 qz791)

noncomputable abbrev qz553 := (@HMul.hMul Real Real Real qz5 qz791 (Real.log Real.pi))

noncomputable def Ns168p1667 := @Enclosure.Real.IsNear.subLit_ff_p qz552 qz553 17790580772766946227247 18014398509481984000 45591112094497 7200000000000000000 17204602370271 67108864000 447911 67108864000 Ns168p1666 13172255490204569498671 18014398509481984000 

noncomputable def Ns168p1668 := nat_lit 35581161545533892454494000 

noncomputable abbrev qz554 := qz791

noncomputable def Ns168p1669 := @Enclosure.Real.IsNear.subLit_ff_p qz207 qz554 21825004398157238694959 18014398509481984000 45591112094497 7200000000000000000 447911 2000 0 1 Ns168p1668 17790580772766946227247 18014398509481984000 45591112094497 7200000000000000000 

noncomputable def Ns168p1670 := nat_lit 49145540837450188251733491743910264832 

noncomputable def Ns168p1671 := nat_lit 26168156774732216693424128 

noncomputable def Ns168p1672 := nat_lit 175724970347521694208375090380045729575607253435550732534604376778986231234837874808750625812605321559717490992884958515691520 

noncomputable def Ns168p1673 := nat_lit 2645620970625920001718416828971242592689129733408939002106196449173641364661163348602811288617990464104932441512170413359104 

noncomputable def Ns168p1674 := nat_lit 2625185762555824215571550567015440830414243163564629017028776233547513683517966616249324774316304786856389540519608320 

noncomputable def Ns168p1675 := BSN.log_dyadic_bound 278210055684 1326786055684 6 5 Ns168p1672 67108864 18000000 Ns168p1673 Ns168p1674 28567456 1604996111368 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 278210055684) (BSN.artanhQ 1326786055684) 0 5 Ns168p1673 Ns168p1672 Ns168p1674 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns168p1676 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 447911 4000) qz790 447911 4000 0 1 48741990280770169 4503599627370496 100000027 1800000000000000 21832073608650047166959 18014398509481984000 44791112093597 7200000000000000000 (Enclosure.Real.IsNear.const Bool.false 447911 4000) (BSN.isNear_log_sfrac 802498055684 16000000 48741990280770169 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 802498055684) qz353)) Bool.false Ns168p1671 Ns168p89 1000000270000000 18000000000000000000000 48741990280770169 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 802498055684 16000000 15 1604996111368 1048576000000 28567456 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns168p1675 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p1677 := BSN.arctan_dyadic_bound_f 1000 895822 1 0 8388608 2250000 0 1 1 0 1 1 9364 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 895822) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 895822) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz792 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 895822)))

noncomputable def Ns168p1678 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz792 884279719003555 562949953421312 1 2000000000000000 9364 8388608 1 2250000 7412604461707136335872 883651311601059 562949953421312 8000000009 18000000000000000 qz16 (Ns168p1677 rfl) rfl rfl 

noncomputable def Ns168p1679 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 447911 4000) qz790) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz792)) 21832073608650047166959 18014398509481984000 44791112093597 7200000000000000000 883651311601059 2251799813685248 8000000009 72000000000000000 Ns168p1670 21825004398157238694959 18014398509481984000 45591112094497 7200000000000000000 (Ns168p1676 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz792) 1 4 0 1 883651311601059 562949953421312 8000000009 18000000000000000 883651311601059 2251799813685248 8000000009 72000000000000000 qz356 Ns168p1678 rfl) 

noncomputable def Ns168p1680 := @Ns168p1665 Ns168p1659 Ns168p1660 47947135476366839 3686400000000000000000 (@Ns168p1667 47947135476366839 3686400000000000000000 (Ns168p1669 (Ns168p1679 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 447911 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz554 (Real.log Real.pi) 447911 2000 0 1 38410761 33554432 1 33554432 17204602370271 67108864000 447911 67108864000 (Enclosure.Real.IsNear.const Bool.false 447911 2000) RS169to186.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns168p1661 Ns168p1662) 

noncomputable def Ns168p1681 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz203) Bool.false Ns168p1659 Ns168p1660 47947135476366839 3686400000000000000000 12267612653 16777216 55 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz203) (@HAdd.hAdd Real Real Real qz357 qz551 (Enclosure.sfrac Bool.true Ns168p1661 Ns168p1662)) Bool.false Ns168p1659 Ns168p1660 47947135476366839 3686400000000000000000 Ns168p1663 (Ns168p1680 rfl rfl)) 

noncomputable def Ns168p1682 := nat_lit 1901404487946847928713216 

noncomputable def Ns168p1683 := nat_lit 2247061502291808202893765545632586651468822879644636869392368669250054317619268960258145 

noncomputable def Ns168p1684 := nat_lit 284156577224373090292531296131963477039464160881686814543853107772733042155519084641 

noncomputable def Ns168p1685 := nat_lit 5884701014401134403527959949796370432026948409475478593565989800147081645029833579300961 

noncomputable def Ns168p1686 := BSN.sin_dyadic_bound_f 27020582933 34359738368 3 2 16777216 4504395 Ns168p1683 Ns168p1076 Ns168p1684 Ns168p1685 Ns168p1079 Ns168p1684 11875191 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 27020582933) qz358 0 2 Ns168p1683 Ns168p1076 Ns168p1684 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 27020582933) qz359 0 2 Ns168p1685 Ns168p1079 Ns168p1684 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1687 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz203) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12267612653) qz370) Bool.false 12267612653 16777216 55 4194304 Bool.true 11875191 16777216 1 2250000 (Ns168p1681 rfl) (Enclosure.sfrac_false_div 12267612653 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12267612653) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns168p1682) qz385) 226375608064910080 72057594037927936 Bool.false 11875191 16777216 116 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 12267612653 16777216 226375608064910080 72057594037927936 116 Ns168p1682 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 11875191 16777216 Ns168p1682 Ns168p89 27020582933 34359738368 4504395 4500000 (Ns168p1686 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p1688 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz203) Bool.false Ns168p1659 Ns168p1660 47947135476366839 3686400000000000000000 98140901230 134217728 1747 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz203) (@HAdd.hAdd Real Real Real qz357 qz551 (Enclosure.sfrac Bool.true Ns168p1661 Ns168p1662)) Bool.false Ns168p1659 Ns168p1660 47947135476366839 3686400000000000000000 Ns168p1663 (Ns168p1680 rfl rfl)) 

noncomputable def Ns168p1689 := Ns168p1658 38613 BSN.abs_quadSignPos (BSN.cos_quad_nat3 267 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 130531309 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 152 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 125367895 134217728) qz206 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz203) qz203 1) Bool.true 11875191 16777216 7996519 589824000000 95001528 134217728 1820 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz203) qz203 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz203)) Bool.true 11875191 16777216 7996519 589824000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz203) qz203) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz203)) Bool.true 11875191 16777216 127944304 9437184000000 11875191 16777216 7996519 589824000000 (Ns168p1687 rfl rfl) rfl)) rfl) (Ns168p1688 rfl) RS169to186.d7 

noncomputable def Ns168p1690 := nat_lit 5653871355160098444098818029166338270970151842308078508403994829762931941502899315609447765712223824590801 

noncomputable def Ns168p1691 := nat_lit 1103905012915495187875309174338515081205037656700561120604284951396508804593306910073637138872219601 

noncomputable def Ns168p1692 := nat_lit 28250967336901094286676407359590817722914741624629902821081041294150334927173649703295945349957681176721361 

noncomputable def Ns168p1693 := BSN.sin_dyadic_bound_f 179298907 134217728 4 3 134217728 67108864 Ns168p1690 Ns168p144 Ns168p1691 Ns168p1692 Ns168p147 Ns168p1691 130531309 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 179298907) qz361 0 3 Ns168p1690 Ns168p144 Ns168p1691 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 179298907) qz362 0 3 Ns168p1692 Ns168p147 Ns168p1691 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1694 := nat_lit 3146053120547905377715317072545787349572742402071417399412230386721 

noncomputable def Ns168p1695 := nat_lit 33298546935380671244011787941149984239570260100518800828331041 

noncomputable def Ns168p1696 := nat_lit 9438092764549845371803463194061479748749748065694051160635034498081 

noncomputable def Ns168p1697 := BSN.cos_dyadic_bound_f 49012083 134217728 3 2 134217728 67108864 Ns168p1694 Ns168p124 Ns168p1695 Ns168p1696 Ns168p127 Ns168p1695 125367895 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 49012083) qz363 0 2 Ns168p1694 Ns168p124 Ns168p1695 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 49012083) qz364 0 2 Ns168p1696 Ns168p127 Ns168p1695 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1698 := nat_lit 3175233690507759492520911889441 

noncomputable def Ns168p1699 := BSN.cos_dyadic_bound_f 42212777 134217728 2 1 134217728 67108864 Ns168p1698 Ns168p130 Ns168p1698 Ns168p1698 Ns168p131 Ns168p1698 127634102 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 42212777) qz363 0 1 Ns168p1698 Ns168p130 Ns168p1698 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 42212777) qz364 0 1 Ns168p1698 Ns168p131 Ns168p1698 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1700 := nat_lit 114590335018528283555201365448055427534871876154450009920691855425536 

noncomputable def Ns168p1701 := nat_lit 44143186913621696410349318940660951333517116296144703989015904256 

noncomputable def Ns168p1702 := nat_lit 343682718681757607272783397706284960701948594230757740354097534468096 

noncomputable def Ns168p1703 := BSN.cos_dyadic_bound_f 120394864 134217728 3 2 134217728 67108864 Ns168p1700 Ns168p124 Ns168p1701 Ns168p1702 Ns168p127 Ns168p1701 83744890 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 120394864) qz363 0 2 Ns168p1700 Ns168p124 Ns168p1701 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 120394864) qz364 0 2 Ns168p1702 Ns168p127 Ns168p1701 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1704 := Ns168p1656 65744 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 70 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 127634102 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 6 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 83744890 134217728) qz206 rfl rfl (Ns168p1689 RS169to186.d9 RS169to186.d11 RS169to186.d13 RS169to186.d17 (Ns168p1693 rfl rfl) (Ns168p1697 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns168p1688 rfl) RS169to186.d19 RS169to186.d21 RS169to186.d23 RS169to186.d25 RS169to186.d17 (Ns168p1699 rfl rfl) (Ns168p1703 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns168p1705 := nat_lit 59051498152746211523301165161885633295364510651046315380474152735745 

noncomputable def Ns168p1706 := nat_lit 3620478294691882347742243168721367520789142139778856021434291201 

noncomputable def Ns168p1707 := nat_lit 154652823911382005227701945125522538321397202617847374515302363550721 

noncomputable def Ns168p1708 := BSN.sin_dyadic_bound_f 88073599 134217728 3 2 134217728 67108864 Ns168p1705 Ns168p112 Ns168p1706 Ns168p1707 Ns168p115 Ns168p1706 81887581 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 88073599) qz361 0 2 Ns168p1705 Ns168p112 Ns168p1706 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 88073599) qz362 0 2 Ns168p1707 Ns168p115 Ns168p1706 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1709 := nat_lit 37803345179438566205732739668367102637680598483862168266573646725120 

noncomputable def Ns168p1710 := nat_lit 1483828583111553130650804692484074991494516736890248123687960576 

noncomputable def Ns168p1711 := nat_lit 99006358795109302309945645447649818405843909668731666010730722820096 

noncomputable def Ns168p1712 := BSN.sin_dyadic_bound_f 78781268 134217728 3 2 134217728 67108864 Ns168p1709 Ns168p112 Ns168p1710 Ns168p1711 Ns168p115 Ns168p1710 74334817 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 78781268) qz361 0 2 Ns168p1709 Ns168p112 Ns168p1710 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 78781268) qz362 0 2 Ns168p1711 Ns168p115 Ns168p1710 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1713 := Ns168p1654 88619 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 45 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 81887581 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 89 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 74334817 134217728) qz206 rfl rfl (Ns168p1704 rfl rfl) (Ns168p1688 rfl) RS169to186.d27 RS169to186.d29 RS169to186.d31 RS169to186.d33 RS169to186.d17 (Ns168p1708 rfl rfl) (Ns168p1712 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns168p1714 := nat_lit 79534801910431736000341587886504676679446501498892275412518305792000 

noncomputable def Ns168p1715 := nat_lit 6567499443936910619361773617720000052069486397314111391699828736 

noncomputable def Ns168p1716 := nat_lit 208294800480602458336082334926416892255608915233407927042913763065856 

noncomputable def Ns168p1717 := BSN.sin_dyadic_bound_f 94880072 134217728 3 2 134217728 67108864 Ns168p1714 Ns168p112 Ns168p1715 Ns168p1716 Ns168p115 Ns168p1715 87172878 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 94880072) qz361 0 2 Ns168p1714 Ns168p112 Ns168p1715 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 94880072) qz362 0 2 Ns168p1716 Ns168p115 Ns168p1715 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1718 := Ns168p1652 Bool.true 93116046 88619 Bool.true 94880072 7074237752028440 1 Bool.false 87172878 Bool.false Bool.true 62295783 98749 BSN.abs_quadSignPos qz365 (BSN.sfrac_eq_quadSignPos_mul Bool.false 87172878 134217728) qz206 rfl (Ns168p1713 rfl) (Ns168p1688 rfl) RS169to186.d35 RS169to186.d37 RS169to186.d17 (Ns168p1717 rfl rfl) rfl 

noncomputable def Ns168p1719 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz203) qz203 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz203) qz203 8) 62295783 134217728 98749 134217728 62295783 134217728 98749 134217728 16722396916482048 62295783 67108864 98749 67108864 (Ns168p1718 rfl rfl rfl rfl) 

noncomputable def Ns168p1720 := @Enclosure.Real.IsNear.mulLit_ff qz789 (Zeta.RiemannSiegel.correction qz205) 5773869 16777216 1 16777216 13663939863567 35184372088832 519221737610491 19791209299968000000 78893798796113730723 590295810358705651712 

noncomputable abbrev qz793 := (@HPow.hPow Real Real Real qz7 qz204 qz9)

noncomputable def Ns168p1721 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz793 1 1 0 1 5773869 16777216 1 16777216 5773869 16777216 1 16777216 

noncomputable def Ns168p1722 := @Enclosure.Real.IsNear.sqrt_image qz204 1196001650247 16777216000 447911 16777216000 70826496 70826524 8388608 (@Enclosure.Real.IsNear.of_eq qz204 (@HMul.hMul Real Real Real qz5 qz203 qz3) Bool.false 1196001650247 16777216000 447911 16777216000 (BSN.t_div_two_pi_mk qz203 447911 1000 qz206) (@Enclosure.Real.IsNear.mulLit_ff qz203 qz3 447911 1000 0 1 2670177 16777216 1 16777216 1196001650247 16777216000 447911 16777216000 (Enclosure.Real.IsNear.const Bool.false 447911 1000) RS169to186.d40 rfl)) 

noncomputable abbrev qz952 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 447911 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz794 := qz952

noncomputable abbrev qz555 := qz794

noncomputable abbrev qz208 := qz555

noncomputable def Ns168p1723 := @Enclosure.Real.IsNear.sqrt_image qz208 35413255 4194304 7 4194304 24374899 24374905 8388608 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 141653020 16777216 28 16777216 35413255 4194304 7 4194304 (Ns168p1722 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns168p1724 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz208) 12187451 4194304 3 8388608 2886934 2886935 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz208) Bool.false 48749804 16777216 6 16777216 12187451 4194304 3 8388608 (Ns168p1723 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns168p1725 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz208)) Bool.false 5773869 16777216 1 16777216 5773869 16777216 1 16777216 (Ns168p1724 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz209 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz549))

noncomputable abbrev qz795 := (@HMul.hMul Real Real Real qz890 qz951 qz951)

noncomputable abbrev qz556 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz795 qz788) qz641)

noncomputable abbrev qz210 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz556))

noncomputable def Ns168p1726 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz205) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz209) qz210) Bool.false 13663939863567 

noncomputable def Ns168p1727 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz209) qz210 17906371 16777216 211 

noncomputable abbrev qz796 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz209))

noncomputable def Ns168p1728 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz209) (@Neg.neg Real Real.instNeg qz796) Bool.true 17906371 16777216 211 16777216 (BSN.inv_eq_neg_inv_neg qz209) 

noncomputable def Ns168p1729 := @Enclosure.Real.IsNear.recentre' qz796 Bool.false 17906371 16777216 211 16777216 17906371 16777216 

noncomputable def Ns168p1730 := @Enclosure.Real.IsNear.recentre' qz209 Bool.true 15719264 16777216 415027216 37748736000000 491227 524288 25939201 2359296000000 

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz342 qz340 qz549)

noncomputable def Ns168p1731 := @Enclosure.Real.IsNear.cos_image qz211 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46717317) qz370) Bool.false 46717317 16777216 177 16777216 Bool.true 15719264 16777216 1 

noncomputable def Ns168p1732 := nat_lit 37780505575855097234857597 

noncomputable def Ns168p1733 := nat_lit 3602879701896396800000000000000 

noncomputable def Ns168p1734 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz205 884279719003555 140737488355328 1 500000000000000 1858823 4194304 7 4194304 1643719480117345115765 590295810358705651712 Ns168p1732 

noncomputable def Ns168p1735 := @Enclosure.Real.IsNear.subLit_ff_p qz208 qz1 35413255 4194304 7 4194304 8 1 0 1 1858823 1858823 4194304 7 

noncomputable def Ns168p1736 := @Ns168p1735 4194304 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 141653020 16777216 28 16777216 35413255 4194304 7 4194304 (Ns168p1722 rfl rfl rfl rfl rfl rfl) rfl) qz371 

noncomputable def Ns168p1737 := @Enclosure.Real.IsNear.recentre' qz211 Bool.false 1643719480117345115765 590295810358705651712 Ns168p1732 Ns168p1733 46717317 16777216 177 16777216 (@Ns168p1734 Ns168p1733 RS169to186.d39 (Ns168p1736 rfl rfl) rfl) 

noncomputable def Ns168p1738 := nat_lit 2934722452218040385798144 

noncomputable def Ns168p1739 := nat_lit 12759736777431165692627759462184624312459621661129596319802530887944185672742733081887905 

noncomputable def Ns168p1740 := nat_lit 9151617768266218070594208819732168218187387264521715154388357076957756143490617984161 

noncomputable def Ns168p1741 := nat_lit 33403541321647288651434598443823021117421943818815907584470952128395888013903411356779681 

noncomputable def Ns168p1742 := BSN.sin_dyadic_bound_f 41704914397 34359738368 3 2 16777216 4504395 Ns168p1739 Ns168p1076 Ns168p1740 Ns168p1741 Ns168p1079 Ns168p1740 15719264 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 41704914397) qz358 0 2 Ns168p1739 Ns168p1076 Ns168p1740 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 41704914397) qz359 0 2 Ns168p1741 Ns168p1079 Ns168p1740 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1743 := @Ns168p1731 2250000 (Ns168p1737 rfl) (Enclosure.sfrac_false_div 46717317 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46717317) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns168p1738) qz385) 226375608064910080 72057594037927936 Bool.false 15719264 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 46717317 16777216 226375608064910080 72057594037927936 0 Ns168p1738 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 15719264 16777216 Ns168p1738 Ns168p89 41704914397 34359738368 4504395 4500000 (Ns168p1742 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p1744 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz209) 491227 524288 25939201 2359296000000 8953080 8953291 8388608 (@Enclosure.Real.IsNear.neg qz209 Bool.true 491227 524288 25939201 2359296000000 (Ns168p1730 (Ns168p1743 rfl rfl) rfl)) 

noncomputable def Ns168p1745 := Ns168p1728 (@Enclosure.Real.IsNear.neg qz796 Bool.false 17906371 16777216 211 16777216 (@Ns168p1729 211 16777216 (Ns168p1744 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p1746 := @Enclosure.Real.IsNear.recentre' qz210 Bool.true 3052308 8388608 

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz342 qz340 qz556)

noncomputable def Ns168p1747 := @Enclosure.Real.IsNear.cos_image qz212 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16300815)) qz360) Bool.true 16300815 8388608 

noncomputable def Ns168p1748 := nat_lit 4811151448394839927092701645 

noncomputable def Ns168p1749 := nat_lit 2475880078570760549798248448 

noncomputable def Ns168p1750 := nat_lit 1494588677692533041657163310865221 

noncomputable def Ns168p1751 := @Enclosure.Real.IsNear.recentre' qz212 Bool.true Ns168p1748 Ns168p1749 Ns168p1750 

noncomputable abbrev qz213 := qz556

noncomputable def Ns168p1752 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz213 884279719003555 140737488355328 1 500000000000000 5440757426639 

noncomputable abbrev qz557 := (@HSub.hSub Real Real Real qz633 qz795 qz788)

noncomputable abbrev qz214 := qz557

noncomputable def Ns168p1753 := @Enclosure.Real.IsNear.subLit_tf qz214 qz25 4341245798863 17592186044416 55383699 17592186044416 1 16 

noncomputable abbrev qz558 := qz795

noncomputable abbrev qz215 := qz558

noncomputable def Ns168p1754 := @Enclosure.Real.IsNear.subLit_ff_n qz215 qz205 3455222945329 17592186044416 26023571 17592186044416 1858823 4194304 7 4194304 

noncomputable def Ns168p1755 := @Enclosure.Real.IsNear.mulLit_ff qz205 qz205 1858823 4194304 7 4194304 1858823 4194304 7 4194304 3455222945329 17592186044416 

noncomputable def Ns168p1756 := nat_lit 34846327124403105367518497479928461674032307970547979416092727304625206822178046738961890625 

noncomputable def Ns168p1757 := nat_lit 351975004391226234581459620990099746713437722369640722933712097185051297813496337890625 

noncomputable def Ns168p1758 := nat_lit 210213200220599829001084396232220814731729820692114607089060880770871567930585895902123490625 

noncomputable def Ns168p1759 := BSN.cos_dyadic_bound_t 16300815 8388608 4 3 8388608 2250000 Ns168p1756 Ns168p187 Ns168p1757 Ns168p1758 Ns168p190 Ns168p1757 3052308 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16300815) (BSN.cosEvenQ 8388608) 0 3 Ns168p1756 Ns168p187 Ns168p1757 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16300815) (BSN.cosOddQ 8388608) 0 3 Ns168p1758 Ns168p190 Ns168p1757 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1760 := @Ns168p1746 766027216 37748736000000 763077 2097152 47876701 2359296000000 (@Ns168p1747 333 16777216 Bool.true 3052308 8388608 1 2250000 (@Ns168p1751 Ns168p1090 16300815 8388608 333 16777216 (@Ns168p1752 17592186044416 55383699 17592186044416 Ns168p1748 Ns168p1749 Ns168p1750 Ns168p1090 RS169to186.d39 (@Ns168p1753 0 1 87052118826224 5440757426639 17592186044416 55383699 17592186044416 (@Ns168p1754 18208504619154276352 4341245798863 17592186044416 55383699 17592186044416 (@Ns168p1755 26023571 17592186044416 (Ns168p1736 rfl rfl) (Ns168p1736 rfl rfl) rfl) (Ns168p1736 rfl rfl) rfl rfl) qz375 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16300815 8388608) (BSN.cos_neg_of_bound 16300815 8388608 Bool.true 3052308 8388608 1 2250000 (Ns168p1759 rfl rfl)) rfl rfl) 

noncomputable def Ns168p1761 := @Ns168p1720 300560478031034210767 Ns168p1649 (Ns168p1721 qz27 (@Enclosure.Real.IsNear.of_eq qz793 (@Inv.inv Real Real.instInv (Real.sqrt qz208)) Bool.false 5773869 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz204 (BSN.t_div_two_pi_nonneg qz203 447911 1000 qz206)) Ns168p1725) rfl) (@Ns168p1726 35184372088832 519221737610491 19791209299968000000 (BSN.correction_mk qz205 (BSN.cos_two_pi_p_ne_zero_mk qz203 447911 1000 8 qz206 rfl rfl (@BSN.floor_sqrt_eq_dec qz203 447911 1000 8 qz206 rfl rfl rfl))) (@Ns168p1727 16777216 763077 2097152 47876701 2359296000000 13663939863567 35184372088832 519221737610491 19791209299968000000 Ns168p1745 (Ns168p1760 rfl) rfl)) 

noncomputable def Ns168p1762 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz203) (hardyZApproximantRS₀ qz203) Bool.true 626853300955397479587 590295810358705651712 49159613657094535010767 Ns168p1649 (@Eq.refl Real (hardyZApproximantRS₀ qz203)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz203) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz203) qz203 8) (@HMul.hMul Real Real Real qz5 qz789 (Zeta.RiemannSiegel.correction qz205))) Bool.true 626853300955397479587 590295810358705651712 49159613657094535010767 Ns168p1649 (BSN.hardyZApproximantRS₀_eq qz203 8 (@BSN.floor_sqrt_eq_dec qz203 447911 1000 8 qz206 rfl rfl rfl)) (@Ns168p1651 626853300955397479587 590295810358705651712 49159613657094535010767 Ns168p1649 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz203) qz203 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz203) qz203 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz203) qz203 8)) Bool.true 62295783 67108864 98749 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz203) qz203 8) (Ns168p1719 (Ns168p1718 rfl rfl rfl rfl) rfl rfl)) (Ns168p1761 rfl) rfl rfl)) 

theorem RS169to186.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz203) Bool.true 626853300955397479587 590295810358705651712 49159613657094535010767 Ns168p1649 := Ns168p1762 

noncomputable def Ns168p1763 := nat_lit 6640827866535438581760000 

noncomputable def Ns168p1764 := nat_lit 51065306788898274463570722816 

noncomputable abbrev qz953 := (Enclosure.sfrac Bool.false 449750 1000)

noncomputable abbrev qz797 := qz953

noncomputable abbrev qz559 := qz797

noncomputable abbrev qz216 := qz559

noncomputable abbrev qz954 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 449750 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz798 := qz954

noncomputable abbrev qz560 := qz798

noncomputable abbrev qz217 := qz560

noncomputable abbrev qz955 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 449750 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz799 := qz955

noncomputable abbrev qz561 := qz799

noncomputable abbrev qz218 := qz561

noncomputable abbrev qz800 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz217 qz9))

noncomputable def Ns168p1765 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz216) qz216 8) (@HMul.hMul Real Real Real qz5 qz800 (Zeta.RiemannSiegel.correction qz218)) 52146309 67108864 12393 8388608 156435201582948223425 1180591620717411303424 58959169014775271207 Ns168p1763 Ns168p1764 

noncomputable def Ns168p1766 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz216) qz216 Real.sin BSN.quadSignPos 7 8 449750 1000 127 134217728 67108864 2251799813685248 Bool.false 98667723600 1754 279097919 60 47453128 8 

noncomputable def Ns168p1767 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz216) qz216 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 449750 1000 45 89 134217728 67108864 2251799813685248 Bool.false 98667723600 1754 

noncomputable def Ns168p1768 := Ns168p1767 240485871 61 54794152 8 261175631 61 50729528 8 Bool.false 38629780 66005 Bool.true 3504746 Bool.true 32260884 7074237752028440 1 Bool.false 3504347 Bool.true Bool.false 31951139 Bool.true Bool.false 25122742 

noncomputable def Ns168p1769 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz216) qz216 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 449750 1000 71 7 134217728 67108864 2251799813685248 Bool.false 98667723600 1754 

noncomputable def Ns168p1770 := Ns168p1769 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 13377104 38763 Bool.false 16032412 Bool.false 39136773 7074237752028440 1 Bool.false 15994312 Bool.false Bool.false 38584520 Bool.false Bool.false 38629780 

noncomputable def Ns168p1771 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz216) qz216 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 449750 1000 269 153 134217728 67108864 2251799813685248 Bool.false 98667723600 1754 

noncomputable def Ns168p1772 := Ns168p1771 93032624 60 94906264 8 147453232 60 77490640 16 Bool.false 134217672 1820 Bool.false 113376854 Bool.false 93839245 7074237752028440 1 Bool.false 100366337 Bool.true Bool.false 86378850 Bool.true Bool.false 13377104 

noncomputable def Ns168p1773 := nat_lit 80806461022069975410835832865200213944231 

noncomputable def Ns168p1774 := nat_lit 109921048245079635647483118606090240000 

noncomputable def Ns168p1775 := nat_lit 8832801228164268031250000000000000 

noncomputable def Ns168p1776 := nat_lit 23835327861839857119140625000000000000 

noncomputable abbrev qz801 := (@Eq.refl Real qz953)

noncomputable abbrev qz562 := qz801

noncomputable abbrev qz219 := qz562

noncomputable def Ns168p1777 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz216 449750 1000 809101250000 16000000 899500 4000 2000 Ns168p1775 Ns168p1776 qz219 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns168p1778 := nat_lit 1262600953469843365794309888518753342878609375000000000000 

noncomputable abbrev qz802 := (Real.log (Enclosure.sfrac Bool.false 809101250000 16000000))

noncomputable abbrev qz220 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 449750 4000) qz802) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 899500))))))

noncomputable abbrev qz803 := (Enclosure.sfrac Bool.false 449750 2000)

noncomputable abbrev qz563 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz220 qz803) (@HMul.hMul Real Real Real qz5 qz803 (Real.log Real.pi)))

noncomputable def Ns168p1779 := @Enclosure.Real.IsNear.addLit_ft_p qz563 (Enclosure.sfrac Bool.true Ns168p1775 Ns168p1776) 52971857457084201967 72057594037927936 962846231777971 73728000000000000000 Ns168p1775 Ns168p1776 0 1 Ns168p1778 

noncomputable def Ns168p1780 := nat_lit 14219524711659398185407741952 

noncomputable abbrev qz564 := (@HSub.hSub Real Real Real qz12 qz220 qz803)

noncomputable abbrev qz565 := (@HMul.hMul Real Real Real qz5 qz803 (Real.log Real.pi))

noncomputable def Ns168p1781 := @Enclosure.Real.IsNear.subLit_ff_p qz564 qz565 71521004906755488751 72057594037927936 915500242883 144000000000000000 69100959039 268435456 1799 268435456 Ns168p1780 52971857457084201967 72057594037927936 

noncomputable abbrev qz566 := qz803

noncomputable def Ns168p1782 := @Enclosure.Real.IsNear.subLit_ff_p qz220 qz566 87724956366034533359 72057594037927936 915500242883 144000000000000000 449750 2000 0 1 143042009813510977502000 71521004906755488751 72057594037927936 915500242883 144000000000000000 

noncomputable def Ns168p1783 := nat_lit 197539040400583072669250893782188032 

noncomputable def Ns168p1784 := nat_lit 26187970199163246605238272 

noncomputable def Ns168p1785 := nat_lit 184668996058397589883947688116632579816608895384450821484263741460617403984069824218750000000000000000000000000000000000000000 

noncomputable def Ns168p1786 := nat_lit 2888012975043312645063761156393578307893775827442315119959372085673523902893066406250000000000000000000000000000000000000000 

noncomputable def Ns168p1787 := nat_lit 3319202157275642281901514221616820990449178308536213292950965218544006347656250000000000000000000000000000000000000000 

noncomputable def Ns168p1788 := BSN.log_dyadic_bound 284813250000 1333389250000 6 5 Ns168p1785 67108864 18000000 Ns168p1786 Ns168p1787 29117389 1618202500000 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 284813250000) (BSN.artanhQ 1333389250000) 0 5 Ns168p1786 Ns168p1785 Ns168p1787 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns168p1789 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 449750 4000) qz802 449750 4000 0 1 48778895659676281 4503599627370496 100000027 1800000000000000 87753233291757629519 72057594037927936 179900048573 28800000000000000 (Enclosure.Real.IsNear.const Bool.false 449750 4000) (BSN.isNear_log_sfrac 809101250000 16000000 48778895659676281 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 809101250000) qz353)) Bool.false Ns168p1784 Ns168p89 1000000270000000 18000000000000000000000 48778895659676281 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 809101250000 16000000 15 1618202500000 1048576000000 29117389 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns168p1788 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p1790 := BSN.arctan_dyadic_bound_f 1000 899500 1 0 8388608 2250000 0 1 1 0 1 1 9325 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 899500) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 899500) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz804 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 899500)))

noncomputable def Ns168p1791 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz804 884279719003555 562949953421312 1 2000000000000000 9325 8388608 1 2250000 7412626416755319767040 883653928846755 562949953421312 8000000009 18000000000000000 qz16 (Ns168p1790 rfl) rfl rfl 

noncomputable def Ns168p1792 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 449750 4000) qz802) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz804)) 87753233291757629519 72057594037927936 179900048573 28800000000000000 883653928846755 2251799813685248 8000000009 72000000000000000 Ns168p1783 87724956366034533359 72057594037927936 915500242883 144000000000000000 (Ns168p1789 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz804) 1 4 0 1 883653928846755 562949953421312 8000000009 18000000000000000 883653928846755 2251799813685248 8000000009 72000000000000000 qz356 Ns168p1791 rfl) 

noncomputable def Ns168p1793 := @Ns168p1779 Ns168p1773 Ns168p1774 962846231777971 73728000000000000000 (@Ns168p1781 962846231777971 73728000000000000000 (Ns168p1782 (Ns168p1792 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 449750 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz566 (Real.log Real.pi) 449750 2000 0 1 38410761 33554432 1 33554432 69100959039 268435456 1799 268435456 (Enclosure.Real.IsNear.const Bool.false 449750 2000) RS169to186.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns168p1775 Ns168p1776) 

noncomputable def Ns168p1794 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz216) Bool.false Ns168p1773 Ns168p1774 962846231777971 73728000000000000000 6166732725 8388608 55 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz216) (@HAdd.hAdd Real Real Real qz357 qz563 (Enclosure.sfrac Bool.true Ns168p1775 Ns168p1776)) Bool.false Ns168p1773 Ns168p1774 962846231777971 73728000000000000000 Ns168p1777 (Ns168p1793 rfl rfl)) 

noncomputable def Ns168p1795 := nat_lit 1897943882825164201656320 

noncomputable def Ns168p1796 := nat_lit 855271465408831195994194299722183461945985348070819925907515563564530283291625637166826201846218877482435219874207518145273435097399296 

noncomputable def Ns168p1797 := nat_lit 607019649324579786993622168799926468273030761949994242693350986484566772516994915954969862486085971990757591286580595006317264896 

noncomputable def Ns168p1798 := nat_lit 4271054953413184343360283449514196257360112029990193680827026781393394417788458311215447110794734818963761729657870858723144456686534656 

noncomputable def Ns168p1799 := BSN.sin_dyadic_bound_f 53942809552 34359738368 4 3 16777216 4504395 Ns168p1796 Ns168p103 Ns168p1797 Ns168p1798 Ns168p106 Ns168p1797 16777209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53942809552) qz358 0 3 Ns168p1796 Ns168p103 Ns168p1797 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53942809552) qz359 0 3 Ns168p1798 Ns168p106 Ns168p1797 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1800 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz216) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6166732725) qz360) Bool.false 6166732725 8388608 55 4194304 Bool.false 16777209 16777216 1 2250000 (Ns168p1794 rfl) (Enclosure.sfrac_false_div 6166732725 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6166732725) qz360) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns168p1795) qz636) 226375608064910080 72057594037927936 Bool.false 16777209 16777216 116 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q3 6166732725 8388608 226375608064910080 72057594037927936 116 Ns168p1795 Ns168p101 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777209 16777216 Ns168p1795 Ns168p101 53942809552 34359738368 4504395 4500000 (Ns168p1799 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p1801 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz216) Bool.false Ns168p1773 Ns168p1774 962846231777971 73728000000000000000 98667723600 134217728 1754 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz216) (@HAdd.hAdd Real Real Real qz357 qz563 (Enclosure.sfrac Bool.true Ns168p1775 Ns168p1776)) Bool.false Ns168p1773 Ns168p1774 962846231777971 73728000000000000000 Ns168p1777 (Ns168p1793 rfl rfl)) 

noncomputable def Ns168p1802 := Ns168p1772 38763 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 269 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 100366337 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 153 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 86378850 134217728) qz219 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz216) qz216 1) Bool.false 16777209 16777216 7996519 589824000000 134217672 134217728 1820 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz216) qz216 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz216)) Bool.false 16777209 16777216 7996519 589824000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz216) qz216) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz216)) Bool.false 16777209 16777216 127944304 9437184000000 16777209 16777216 7996519 589824000000 (Ns168p1800 rfl rfl) rfl)) rfl) (Ns168p1801 rfl) RS169to186.d7 

noncomputable def Ns168p1803 := nat_lit 162178038813632859430836246929996507438037225146282330415557432992000 

noncomputable def Ns168p1804 := nat_lit 27302047352985309472439907967868861821865217452777959530654228736 

noncomputable def Ns168p1805 := nat_lit 424707803101895512770187172584709541323338284078673034391981741465856 

noncomputable def Ns168p1806 := BSN.sin_dyadic_bound_f 113376854 134217728 3 2 134217728 67108864 Ns168p1803 Ns168p112 Ns168p1804 Ns168p1805 Ns168p115 Ns168p1804 100366337 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 113376854) qz361 0 2 Ns168p1803 Ns168p112 Ns168p1804 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 113376854) qz362 0 2 Ns168p1805 Ns168p115 Ns168p1804 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1807 := nat_lit 76101576439216895665993542444447909442805780138490548375409973230625 

noncomputable def Ns168p1808 := nat_lit 6012790045690078233960658514675157008703185020394202260625390625 

noncomputable def Ns168p1809 := nat_lit 199303917585494085665223341526435050667429619015537464655747012590625 

noncomputable def Ns168p1810 := BSN.sin_dyadic_bound_f 93839245 134217728 3 2 134217728 67108864 Ns168p1807 Ns168p112 Ns168p1808 Ns168p1809 Ns168p115 Ns168p1808 86378850 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 93839245) qz361 0 2 Ns168p1807 Ns168p112 Ns168p1808 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 93839245) qz362 0 2 Ns168p1809 Ns168p115 Ns168p1808 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1811 := nat_lit 66068654014280292497360609536 

noncomputable def Ns168p1812 := BSN.sin_dyadic_bound_f 16032412 134217728 2 1 134217728 67108864 Ns168p1811 Ns168p394 Ns168p1811 Ns168p1811 Ns168p395 Ns168p1811 15994312 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 16032412) qz361 0 1 Ns168p1811 Ns168p394 Ns168p1811 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 16032412) qz362 0 1 Ns168p1811 Ns168p395 Ns168p1811 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1813 := nat_lit 2346065068583678547574511753841 

noncomputable def Ns168p1814 := BSN.sin_dyadic_bound_f 39136773 134217728 2 1 134217728 67108864 Ns168p1813 Ns168p394 Ns168p1813 Ns168p1813 Ns168p395 Ns168p1813 38584520 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 39136773) qz361 0 1 Ns168p1813 Ns168p394 Ns168p1813 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 39136773) qz362 0 1 Ns168p1813 Ns168p395 Ns168p1813 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1815 := Ns168p1770 66005 BSN.abs_quadSignPos (BSN.cos_quad_nat3 71 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 15994312 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 7 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 38584520 134217728) qz219 rfl rfl (Ns168p1802 RS169to186.d9 RS169to186.d11 RS169to186.d13 RS169to186.d17 (Ns168p1806 rfl rfl) (Ns168p1810 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns168p1801 rfl) RS169to186.d19 RS169to186.d21 RS169to186.d23 RS169to186.d25 RS169to186.d17 (Ns168p1812 rfl rfl) (Ns168p1814 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns168p1816 := BSN.sin_dyadic_bound_f 3504746 134217728 1 0 134217728 67108864 0 1 1 0 1 1 3504347 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 3504746) qz361 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 3504746) qz362 0 0 rfl) rfl rfl 

noncomputable def Ns168p1817 := nat_lit 1083191028508746667952973639936 

noncomputable def Ns168p1818 := BSN.sin_dyadic_bound_f 32260884 134217728 2 1 134217728 67108864 Ns168p1817 Ns168p394 Ns168p1817 Ns168p1817 Ns168p395 Ns168p1817 31951139 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 32260884) qz361 0 1 Ns168p1817 Ns168p394 Ns168p1817 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 32260884) qz362 0 1 Ns168p1817 Ns168p395 Ns168p1817 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1819 := Ns168p1768 88973 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 45 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 3504347 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 89 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 31951139 134217728) qz219 rfl rfl (Ns168p1815 rfl rfl) (Ns168p1801 rfl) RS169to186.d27 RS169to186.d29 RS169to186.d31 RS169to186.d33 RS169to186.d17 (Ns168p1816 rfl rfl) (Ns168p1818 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns168p1820 := nat_lit 42914492504822391409147512761576365684816746707211675081473737890625 

noncomputable def Ns168p1821 := nat_lit 1912170535202804396873449731829073656773605545085449371337890625 

noncomputable def Ns168p1822 := nat_lit 112392003522239744388267595456943710674313846014671867819163337890625 

noncomputable def Ns168p1823 := BSN.sin_dyadic_bound_f 81318775 134217728 3 2 134217728 67108864 Ns168p1820 Ns168p112 Ns168p1821 Ns168p1822 Ns168p115 Ns168p1821 76434198 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 81318775) qz361 0 2 Ns168p1820 Ns168p112 Ns168p1821 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 81318775) qz362 0 2 Ns168p1822 Ns168p115 Ns168p1821 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1824 := Ns168p1766 Bool.false 25122742 88973 Bool.true 81318775 7074237752028440 1 Bool.false 76434198 Bool.false Bool.false 52146309 99144 BSN.abs_quadSignPos qz365 (BSN.sfrac_eq_quadSignPos_mul Bool.false 76434198 134217728) qz219 rfl (Ns168p1819 rfl) (Ns168p1801 rfl) RS169to186.d35 RS169to186.d37 RS169to186.d17 (Ns168p1823 rfl rfl) rfl 

noncomputable def Ns168p1825 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz216) qz216 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz216) qz216 8) 52146309 134217728 99144 134217728 52146309 134217728 99144 134217728 13997918235131904 52146309 67108864 12393 8388608 (Ns168p1824 rfl rfl rfl rfl) 

noncomputable def Ns168p1826 := @Enclosure.Real.IsNear.mulLit_ff qz800 (Zeta.RiemannSiegel.correction qz218) 2883979 8388608 1 8388608 54242836575075 140737488355328 101689424092817 3958241859993600000 156435201582948223425 1180591620717411303424 

noncomputable abbrev qz805 := (@HPow.hPow Real Real Real qz7 qz217 qz9)

noncomputable def Ns168p1827 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz805 1 1 0 1 2883979 8388608 1 8388608 2883979 8388608 1 8388608 

noncomputable def Ns168p1828 := @Enclosure.Real.IsNear.sqrt_image qz217 4803648423 67108864 1799 67108864 70971744 70971772 8388608 (@Enclosure.Real.IsNear.of_eq qz217 (@HMul.hMul Real Real Real qz5 qz216 qz3) Bool.false 4803648423 67108864 1799 67108864 (BSN.t_div_two_pi_mk qz216 449750 1000 qz219) (@Enclosure.Real.IsNear.mulLit_ff qz216 qz3 449750 1000 0 1 2670177 16777216 1 16777216 4803648423 67108864 1799 67108864 (Enclosure.Real.IsNear.const Bool.false 449750 1000) RS169to186.d40 rfl)) 

noncomputable abbrev qz956 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 449750 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz806 := qz956

noncomputable abbrev qz567 := qz806

noncomputable abbrev qz221 := qz567

noncomputable def Ns168p1829 := @Enclosure.Real.IsNear.sqrt_image qz221 35485879 4194304 7 4194304 24399879 24399885 8388608 (@Enclosure.Real.IsNear.recentre' qz221 Bool.false 141943516 16777216 28 16777216 35485879 4194304 7 4194304 (Ns168p1828 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns168p1830 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz221) 12199941 4194304 3 8388608 2883978 2883980 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz221) Bool.false 48799764 16777216 6 16777216 12199941 4194304 3 8388608 (Ns168p1829 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns168p1831 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz221)) Bool.false 5767958 16777216 2 16777216 2883979 8388608 1 8388608 (Ns168p1830 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz222 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz561))

noncomputable abbrev qz807 := (@HMul.hMul Real Real Real qz890 qz955 qz955)

noncomputable abbrev qz568 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz807 qz799) qz641)

noncomputable abbrev qz223 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz568))

noncomputable def Ns168p1832 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz218) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz222) qz223) Bool.false 54242836575075 

noncomputable def Ns168p1833 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz222) qz223 17307723 16777216 197 

noncomputable abbrev qz808 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz222))

noncomputable def Ns168p1834 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz222) (@Neg.neg Real Real.instNeg qz808) Bool.true 17307723 16777216 197 16777216 (BSN.inv_eq_neg_inv_neg qz222) 

noncomputable def Ns168p1835 := @Enclosure.Real.IsNear.recentre' qz808 Bool.false 17307723 16777216 197 16777216 17307723 16777216 

noncomputable def Ns168p1836 := @Enclosure.Real.IsNear.recentre' qz222 Bool.true 16262970 16777216 415027216 37748736000000 8131485 8388608 25939201 2359296000000 

noncomputable abbrev qz224 := (@HMul.hMul Real Real Real qz342 qz340 qz561)

noncomputable def Ns168p1837 := @Enclosure.Real.IsNear.cos_image qz224 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 48542557) qz370) Bool.false 48542557 16777216 177 16777216 Bool.true 16262970 16777216 1 

noncomputable def Ns168p1838 := nat_lit 188902527879899321584097393 

noncomputable def Ns168p1839 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz218 884279719003555 140737488355328 1 500000000000000 1931447 4194304 7 4194304 1707939410430259294085 590295810358705651712 Ns168p1838 

noncomputable def Ns168p1840 := @Enclosure.Real.IsNear.subLit_ff_p qz221 qz1 35485879 4194304 7 4194304 8 1 0 1 1931447 1931447 4194304 7 

noncomputable def Ns168p1841 := @Ns168p1840 4194304 (@Enclosure.Real.IsNear.recentre' qz221 Bool.false 141943516 16777216 28 16777216 35485879 4194304 7 4194304 (Ns168p1828 rfl rfl rfl rfl rfl rfl) rfl) qz371 

noncomputable def Ns168p1842 := @Enclosure.Real.IsNear.recentre' qz224 Bool.false 1707939410430259294085 590295810358705651712 Ns168p1838 Ns168p1070 48542557 16777216 177 16777216 (@Ns168p1839 Ns168p1070 RS169to186.d39 (Ns168p1841 rfl rfl) rfl) 

noncomputable def Ns168p1843 := nat_lit 3197767258101615557607424 

noncomputable def Ns168p1844 := nat_lit 17992378254762513063218236949097241895388279803547195105338457492847207120465960351581345 

noncomputable def Ns168p1845 := nat_lit 18185967361744318859458483317635880899627280934863419148179841930080560572426594043041 

noncomputable def Ns168p1846 := nat_lit 47093451481982805315989592560359461156941336268729065454408430832427316788865015006643361 

noncomputable def Ns168p1847 := BSN.sin_dyadic_bound_f 45443005917 34359738368 3 2 16777216 4504395 Ns168p1844 Ns168p1076 Ns168p1845 Ns168p1846 Ns168p1079 Ns168p1845 16262970 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 45443005917) qz358 0 2 Ns168p1844 Ns168p1076 Ns168p1845 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 45443005917) qz359 0 2 Ns168p1846 Ns168p1079 Ns168p1845 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1848 := @Ns168p1837 2250000 (Ns168p1842 rfl) (Enclosure.sfrac_false_div 48542557 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 48542557) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns168p1843) qz385) 226375608064910080 72057594037927936 Bool.false 16262970 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 48542557 16777216 226375608064910080 72057594037927936 0 Ns168p1843 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16262970 16777216 Ns168p1843 Ns168p89 45443005917 34359738368 4504395 4500000 (Ns168p1847 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p1849 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz222) 8131485 8388608 25939201 2359296000000 8653763 8653960 8388608 (@Enclosure.Real.IsNear.neg qz222 Bool.true 8131485 8388608 25939201 2359296000000 (Ns168p1836 (Ns168p1848 rfl rfl) rfl)) 

noncomputable def Ns168p1850 := Ns168p1834 (@Enclosure.Real.IsNear.neg qz808 Bool.false 17307723 16777216 197 16777216 (@Ns168p1835 197 16777216 (Ns168p1849 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p1851 := @Enclosure.Real.IsNear.recentre' qz223 Bool.true 3134025 8388608 

noncomputable abbrev qz225 := (@HMul.hMul Real Real Real qz342 qz340 qz568)

noncomputable def Ns168p1852 := @Enclosure.Real.IsNear.cos_image qz225 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16388727)) qz360) Bool.true 16388727 8388608 

noncomputable def Ns168p1853 := nat_lit 4837098483718887894216044525 

noncomputable def Ns168p1854 := nat_lit 304405278411974979794607384009761 

noncomputable def Ns168p1855 := @Enclosure.Real.IsNear.recentre' qz225 Bool.true Ns168p1853 Ns168p1749 Ns168p1854 

noncomputable def Ns168p1856 := nat_lit 15111572745182864683827200000000000000 

noncomputable abbrev qz226 := qz568

noncomputable def Ns168p1857 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz226 884279719003555 140737488355328 1 500000000000000 5470099991855 

noncomputable abbrev qz569 := (@HSub.hSub Real Real Real qz633 qz807 qz799)

noncomputable abbrev qz227 := qz569

noncomputable def Ns168p1858 := @Enclosure.Real.IsNear.subLit_tf qz227 qz25 4370588364079 17592186044416 56400435 17592186044416 1 16 

noncomputable abbrev qz570 := qz807

noncomputable abbrev qz228 := qz570

noncomputable def Ns168p1859 := @Enclosure.Real.IsNear.subLit_ff_n qz228 qz218 3730487513809 17592186044416 27040307 17592186044416 1931447 4194304 7 4194304 

noncomputable def Ns168p1860 := @Enclosure.Real.IsNear.mulLit_ff qz218 qz218 1931447 4194304 7 4194304 1931447 4194304 7 4194304 3730487513809 17592186044416 

noncomputable def Ns168p1861 := nat_lit 35610681883875267735918928043600717891265819306505036424681723660734516061714247950732069601 

noncomputable def Ns168p1862 := nat_lit 375441823790761784627339020118134026023703820315785340126782099899311910900516687940321 

noncomputable def Ns168p1863 := nat_lit 214798017749203329486731601172018157456136667996450644799184541161798205375706627070748756705 

noncomputable def Ns168p1864 := BSN.cos_dyadic_bound_t 16388727 8388608 4 3 8388608 2250000 Ns168p1861 Ns168p187 Ns168p1862 Ns168p1863 Ns168p190 Ns168p1862 3134025 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16388727) (BSN.cosEvenQ 8388608) 0 3 Ns168p1861 Ns168p187 Ns168p1862 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16388727) (BSN.cosOddQ 8388608) 0 3 Ns168p1863 Ns168p190 Ns168p1862 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1865 := @Ns168p1851 779527216 37748736000000 3134025 8388608 48720451 2359296000000 (@Ns168p1852 339 16777216 Bool.true 3134025 8388608 1 2250000 (@Ns168p1855 Ns168p1856 16388727 8388608 339 16777216 (@Ns168p1857 17592186044416 56400435 17592186044416 Ns168p1853 Ns168p1749 Ns168p1854 Ns168p1856 RS169to186.d39 (@Ns168p1858 0 1 87521599869680 5470099991855 17592186044416 56400435 17592186044416 (@Ns168p1859 18331576257810006016 4370588364079 17592186044416 56400435 17592186044416 (@Ns168p1860 27040307 17592186044416 (Ns168p1841 rfl rfl) (Ns168p1841 rfl rfl) rfl) (Ns168p1841 rfl rfl) rfl rfl) qz375 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16388727 8388608) (BSN.cos_neg_of_bound 16388727 8388608 Bool.true 3134025 8388608 1 2250000 (Ns168p1864 rfl rfl)) rfl rfl) 

noncomputable def Ns168p1866 := @Ns168p1826 58959169014775271207 Ns168p1763 (Ns168p1827 qz27 (@Enclosure.Real.IsNear.of_eq qz805 (@Inv.inv Real Real.instInv (Real.sqrt qz221)) Bool.false 2883979 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz217 (BSN.t_div_two_pi_nonneg qz216 449750 1000 qz219)) Ns168p1831) rfl) (@Ns168p1832 140737488355328 101689424092817 3958241859993600000 (BSN.correction_mk qz218 (BSN.cos_two_pi_p_ne_zero_mk qz216 449750 1000 8 qz219 rfl rfl (@BSN.floor_sqrt_eq_dec qz216 449750 1000 8 qz219 rfl rfl rfl))) (@Ns168p1833 16777216 3134025 8388608 48720451 2359296000000 54242836575075 140737488355328 101689424092817 3958241859993600000 Ns168p1850 (Ns168p1865 rfl) rfl)) 

noncomputable def Ns168p1867 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz216) (hardyZApproximantRS₀ qz216) Bool.false 760932367874656237119 1180591620717411303424 9869857443194912231207 Ns168p1763 (@Eq.refl Real (hardyZApproximantRS₀ qz216)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz216) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz216) qz216 8) (@HMul.hMul Real Real Real qz5 qz800 (Zeta.RiemannSiegel.correction qz218))) Bool.false 760932367874656237119 1180591620717411303424 9869857443194912231207 Ns168p1763 (BSN.hardyZApproximantRS₀_eq qz216 8 (@BSN.floor_sqrt_eq_dec qz216 449750 1000 8 qz219 rfl rfl rfl)) (@Ns168p1765 760932367874656237119 1180591620717411303424 9869857443194912231207 Ns168p1763 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz216) qz216 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz216) qz216 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz216) qz216 8)) Bool.false 52146309 67108864 12393 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz216) qz216 8) (Ns168p1825 (Ns168p1824 rfl rfl rfl rfl) rfl rfl)) (Ns168p1866 rfl) rfl rfl)) 

theorem RS169to186.d58 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz216) Bool.false 760932367874656237119 1180591620717411303424 9869857443194912231207 Ns168p1763 := Ns168p1867 

noncomputable def Ns168p1868 := nat_lit 7378697629483820646400000 

noncomputable def Ns168p1869 := nat_lit 128276105187806153730592604160 

noncomputable abbrev qz957 := (Enclosure.sfrac Bool.false 451221 1000)

noncomputable abbrev qz809 := qz957

noncomputable abbrev qz571 := qz809

noncomputable abbrev qz229 := qz571

noncomputable abbrev qz958 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 451221 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz810 := qz958

noncomputable abbrev qz572 := qz810

noncomputable abbrev qz230 := qz572

noncomputable abbrev qz959 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 451221 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz811 := qz959

noncomputable abbrev qz573 := qz811

noncomputable abbrev qz231 := qz573

noncomputable abbrev qz812 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz230 qz9))

noncomputable def Ns168p1870 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz229) qz229 8) (@HMul.hMul Real Real Real qz5 qz812 (Zeta.RiemannSiegel.correction qz231)) 45478425 67108864 99461 67108864 311333093508417627465 2361183241434822606848 64898706477011957347 Ns168p1868 Ns168p1869 

noncomputable def Ns168p1871 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz229) qz229 Real.sin BSN.quadSignPos 7 8 451221 1000 127 134217728 67108864 2251799813685248 Bool.false 99089487497 1759 279097919 60 47453128 8 

noncomputable def Ns168p1872 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz229) qz229 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 451221 1000 44 88 134217728 67108864 2251799813685248 Bool.false 99089487497 1759 

noncomputable def Ns168p1873 := Ns168p1872 240485871 61 54794152 8 261175631 61 50729528 8 Bool.true 96493017 66214 Bool.true 146324279 Bool.true 205515054 7074237752028440 1 Bool.false 62049834 Bool.false Bool.false 5312272 Bool.false Bool.true 69153432 

noncomputable def Ns168p1874 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz229) qz229 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 451221 1000 71 7 134217728 67108864 2251799813685248 Bool.false 99089487497 1759 

noncomputable def Ns168p1875 := Ns168p1874 186065264 60 67108856 8 216015088 60 60023992 8 Bool.true 212126327 38883 Bool.false 164094306 Bool.false 143142475 7074237752028440 1 Bool.false 126163177 Bool.false Bool.false 117509240 Bool.false Bool.true 96493017 

noncomputable def Ns168p1876 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz229) qz229 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 451221 1000 270 154 134217728 67108864 2251799813685248 Bool.false 99089487497 1759 

noncomputable def Ns168p1877 := Ns168p1876 93032624 60 94906264 8 147453232 60 77490640 16 Bool.true 134217720 1820 Bool.false 187461047 Bool.false 87870724 7074237752028440 1 Bool.false 23249793 Bool.true Bool.false 106466602 Bool.true Bool.true 212126327 

noncomputable def Ns168p1878 := nat_lit 112247037336100382145841283268923977945244482830621590373 

noncomputable def Ns168p1879 := nat_lit 152039764323378458698018053497179627988315080228864000 

noncomputable def Ns168p1880 := nat_lit 8978196508701659500433721648480000 

noncomputable def Ns168p1881 := nat_lit 24306918769497196711209640822108764480 

noncomputable abbrev qz813 := (@Eq.refl Real qz957)

noncomputable abbrev qz574 := qz813

noncomputable abbrev qz232 := qz574

noncomputable def Ns168p1882 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz229 451221 1000 814402563364 16000000 902442 4000 2000 Ns168p1880 Ns168p1881 qz232 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns168p1883 := nat_lit 323271467527969100580022895814501056482304110552190180274240 

noncomputable abbrev qz814 := (Real.log (Enclosure.sfrac Bool.false 814402563364 16000000))

noncomputable abbrev qz233 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 451221 4000) qz814) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 902442))))))

noncomputable abbrev qz815 := (Enclosure.sfrac Bool.false 451221 2000)

noncomputable abbrev qz575 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz233 qz815) (@HMul.hMul Real Real Real qz5 qz815 (Real.log Real.pi)))

noncomputable def Ns168p1884 := @Enclosure.Real.IsNear.addLit_ft_p qz575 (Enclosure.sfrac Bool.true Ns168p1880 Ns168p1881) 13299572534485660503213 18014398509481984000 48298431252593029 3686400000000000000000 Ns168p1880 Ns168p1881 0 1 Ns168p1883 

noncomputable def Ns168p1885 := nat_lit 892519204474933500660292780032000 

noncomputable abbrev qz576 := (@HSub.hSub Real Real Real qz12 qz233 qz815)

noncomputable abbrev qz577 := (@HMul.hMul Real Real Real qz5 qz815 (Real.log Real.pi))

noncomputable def Ns168p1886 := @Enclosure.Real.IsNear.subLit_ff_p qz576 qz577 17952026598625809304749 18014398509481984000 45922112183867 7200000000000000000 17331741989181 67108864000 451221 67108864000 Ns168p1885 13299572534485660503213 18014398509481984000 

noncomputable def Ns168p1887 := nat_lit 35904053197251618609498000 

noncomputable abbrev qz578 := qz815

noncomputable def Ns168p1888 := @Enclosure.Real.IsNear.subLit_ff_p qz233 qz578 22016264053549294455981 18014398509481984000 45922112183867 7200000000000000000 451221 2000 0 1 Ns168p1887 17952026598625809304749 18014398509481984000 45922112183867 7200000000000000000 

noncomputable def Ns168p1889 := nat_lit 49576219293827524152426499458925068288 

noncomputable def Ns168p1890 := nat_lit 26203760540032747943493632 

noncomputable def Ns168p1891 := nat_lit 192143861117751808455698121992966065909829153955799438771229049347357003129451653567230025469431377094822294759968571019755520 

noncomputable def Ns168p1892 := nat_lit 3095758038132741920492858827226653337884323684788794907125375451071472256712083953378754993432604496559341495415284148731904 

noncomputable def Ns168p1893 := nat_lit 3991417085758921635995615243452423556866054554305764896608258522630104441665203159909896522072694857177710648565432320 

noncomputable def Ns168p1894 := BSN.log_dyadic_bound 290114563364 1338690563364 6 5 Ns168p1891 67108864 18000000 Ns168p1892 Ns168p1893 29555659 1628805126728 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 290114563364) (BSN.artanhQ 1338690563364) 0 5 Ns168p1892 Ns168p1891 Ns168p1893 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns168p1895 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 451221 4000) qz814 451221 4000 0 1 48808307461501561 4503599627370496 100000027 1800000000000000 22023333301086195855981 18014398509481984000 15040704060989 2400000000000000000 (Enclosure.Real.IsNear.const Bool.false 451221 4000) (BSN.isNear_log_sfrac 814402563364 16000000 48808307461501561 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 814402563364) qz353)) Bool.false Ns168p1890 Ns168p89 1000000270000000 18000000000000000000000 48808307461501561 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 814402563364 16000000 15 1628805126728 1048576000000 29555659 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns168p1894 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p1896 := BSN.arctan_dyadic_bound_f 1000 902442 1 0 8388608 2250000 0 1 1 0 1 1 9295 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 902442) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 902442) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz816 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 902442)))

noncomputable def Ns168p1897 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz816 884279719003555 562949953421312 1 2000000000000000 9295 8388608 1 2250000 7412643305253922406400 883655942112675 562949953421312 8000000009 18000000000000000 qz16 (Ns168p1896 rfl) rfl rfl 

noncomputable def Ns168p1898 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 451221 4000) qz814) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz816)) 22023333301086195855981 18014398509481984000 15040704060989 2400000000000000000 883655942112675 2251799813685248 8000000009 72000000000000000 Ns168p1889 22016264053549294455981 18014398509481984000 45922112183867 7200000000000000000 (Ns168p1895 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz816) 1 4 0 1 883655942112675 562949953421312 8000000009 18000000000000000 883655942112675 2251799813685248 8000000009 72000000000000000 qz356 Ns168p1897 rfl) 

noncomputable def Ns168p1899 := @Ns168p1884 Ns168p1878 Ns168p1879 48298431252593029 3686400000000000000000 (@Ns168p1886 48298431252593029 3686400000000000000000 (Ns168p1888 (Ns168p1898 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 451221 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz578 (Real.log Real.pi) 451221 2000 0 1 38410761 33554432 1 33554432 17331741989181 67108864000 451221 67108864000 (Enclosure.Real.IsNear.const Bool.false 451221 2000) RS169to186.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns168p1880 Ns168p1881) 

noncomputable def Ns168p1900 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz229) Bool.false Ns168p1878 Ns168p1879 48298431252593029 3686400000000000000000 12386185937 16777216 55 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz229) (@HAdd.hAdd Real Real Real qz357 qz575 (Enclosure.sfrac Bool.true Ns168p1880 Ns168p1881)) Bool.false Ns168p1878 Ns168p1879 48298431252593029 3686400000000000000000 Ns168p1882 (Ns168p1899 rfl rfl)) 

noncomputable def Ns168p1901 := nat_lit 3797805717833366051487744 

noncomputable def Ns168p1902 := nat_lit 857004829227606061248417725001364830201246513977544332013131173547939304257901941973201697864848207963667598546295754535673968235380736 

noncomputable def Ns168p1903 := nat_lit 610710408147708271981407931576774197077521343126822966436397720063553207218416450042199778199478003772606581983036357344583745536 

noncomputable def Ns168p1904 := nat_lit 4279700296547340135582632419796563445042806646065075552908999680873543121117872549011893238848950798874054908714007189514773203722960896 

noncomputable def Ns168p1905 := BSN.sin_dyadic_bound_f 53970065292 34359738368 4 3 16777216 4504395 Ns168p1902 Ns168p103 Ns168p1903 Ns168p1904 Ns168p106 Ns168p1903 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53970065292) qz358 0 3 Ns168p1902 Ns168p103 Ns168p1903 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53970065292) qz359 0 3 Ns168p1904 Ns168p106 Ns168p1903 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1906 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz229) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12386185937) qz370) Bool.false 12386185937 16777216 55 4194304 Bool.true 16777215 16777216 1 2250000 (Ns168p1900 rfl) (Enclosure.sfrac_false_div 12386185937 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12386185937) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns168p1901) qz385) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 117 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 12386185937 16777216 226375608064910080 72057594037927936 117 Ns168p1901 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns168p1901 Ns168p89 53970065292 34359738368 4504395 4500000 (Ns168p1905 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p1907 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz229) Bool.false Ns168p1878 Ns168p1879 48298431252593029 3686400000000000000000 99089487497 134217728 1759 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz229) (@HAdd.hAdd Real Real Real qz357 qz575 (Enclosure.sfrac Bool.true Ns168p1880 Ns168p1881)) Bool.false Ns168p1878 Ns168p1879 48298431252593029 3686400000000000000000 Ns168p1882 (Ns168p1899 rfl rfl)) 

noncomputable def Ns168p1908 := Ns168p1877 38883 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 270 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 23249793 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 154 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 106466602 134217728) qz232 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz229) qz229 1) Bool.true 16777215 16777216 7996519 589824000000 134217720 134217728 1820 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz229) qz229 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz229)) Bool.true 16777215 16777216 7996519 589824000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz229) qz229) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz229)) Bool.true 16777215 16777216 127944304 9437184000000 16777215 16777216 7996519 589824000000 (Ns168p1906 rfl rfl) rfl)) rfl) (Ns168p1907 rfl) RS169to186.d7 

noncomputable def Ns168p1909 := nat_lit 2601548216282120283330478463901239660013304785508014928618478635454299131389737781137567653885668777802721 

noncomputable def Ns168p1910 := nat_lit 1883356171904688777586118085166089462724366197252896000655119170987504107484267529981298961854774241 

noncomputable def Ns168p1911 := nat_lit 15758936779327330662375623166998535794826421740372339079916883029567972479853943432790835484982445014793185 

noncomputable def Ns168p1912 := BSN.cos_dyadic_bound_f 187461047 134217728 4 3 134217728 67108864 Ns168p1909 Ns168p118 Ns168p1910 Ns168p1911 Ns168p121 Ns168p1910 23249793 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 187461047) qz363 0 3 Ns168p1909 Ns168p118 Ns168p1910 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 187461047) qz364 0 3 Ns168p1911 Ns168p121 Ns168p1910 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1913 := nat_lit 32506717787758525276396808963723098572049152426378670152254352326656 

noncomputable def Ns168p1914 := nat_lit 3554296368703835823369539533362734796334794438722080121857048576 

noncomputable def Ns168p1915 := nat_lit 97513044770538168157543687812102570246554787690258566296519342882816 

noncomputable def Ns168p1916 := BSN.cos_dyadic_bound_f 87870724 134217728 3 2 134217728 67108864 Ns168p1913 Ns168p124 Ns168p1914 Ns168p1915 Ns168p127 Ns168p1914 106466602 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 87870724) qz363 0 2 Ns168p1913 Ns168p124 Ns168p1914 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 87870724) qz364 0 2 Ns168p1915 Ns168p127 Ns168p1914 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1917 := nat_lit 712059232546418268191389832644714213032291300564603037371250119901440 

noncomputable def Ns168p1918 := nat_lit 525712243894803861608060603698869028987657702165707958199785718016 

noncomputable def Ns168p1919 := nat_lit 1864065884464789591391988892139691436656687674722834904039998280007936 

noncomputable def Ns168p1920 := BSN.sin_dyadic_bound_f 164094306 134217728 3 2 134217728 67108864 Ns168p1917 Ns168p112 Ns168p1918 Ns168p1919 Ns168p115 Ns168p1918 126163177 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 164094306) qz361 0 2 Ns168p1917 Ns168p112 Ns168p1918 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 164094306) qz362 0 2 Ns168p1919 Ns168p115 Ns168p1918 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1921 := nat_lit 412174541497804722232885505093067431802823543977564540761111550390625 

noncomputable def Ns168p1922 := nat_lit 176257731692900163512684949296179285402899021557604126129150390625 

noncomputable def Ns168p1923 := nat_lit 1079219381881033386535679594849649459688171254858718628646321150390625 

noncomputable def Ns168p1924 := BSN.sin_dyadic_bound_f 143142475 134217728 3 2 134217728 67108864 Ns168p1921 Ns168p112 Ns168p1922 Ns168p1923 Ns168p115 Ns168p1922 117509240 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 143142475) qz361 0 2 Ns168p1921 Ns168p112 Ns168p1922 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 143142475) qz362 0 2 Ns168p1923 Ns168p115 Ns168p1922 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1925 := Ns168p1875 66214 BSN.abs_quadSignPos (BSN.cos_quad_nat3 71 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 126163177 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 7 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 117509240 134217728) qz232 rfl rfl (Ns168p1908 RS169to186.d9 RS169to186.d11 RS169to186.d13 RS169to186.d17 (Ns168p1912 rfl rfl) (Ns168p1916 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns168p1907 rfl) RS169to186.d19 RS169to186.d21 RS169to186.d23 RS169to186.d25 RS169to186.d17 (Ns168p1920 rfl rfl) (Ns168p1924 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns168p1926 := nat_lit 964351637215243163033599156371625760778757523797459967857804442481630293732700812576052355988946220247521 

noncomputable def Ns168p1927 := nat_lit 96337797718841025280804796555809981049837427937673158946979738995747942218463792169024612812483041 

noncomputable def Ns168p1928 := nat_lit 5847122674097830469283219544277312584881057262022107329674489078702865922574054317134046481438642561378785 

noncomputable def Ns168p1929 := BSN.cos_dyadic_bound_f 146324279 134217728 4 3 134217728 67108864 Ns168p1926 Ns168p118 Ns168p1927 Ns168p1928 Ns168p121 Ns168p1927 62049834 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 146324279) qz363 0 3 Ns168p1926 Ns168p118 Ns168p1927 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 146324279) qz364 0 3 Ns168p1928 Ns168p121 Ns168p1927 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1930 := nat_lit 3761826241177989098359173700712373777155780268497983225676970885741019528581949827793241080368779608068096 

noncomputable def Ns168p1931 := nat_lit 5677062479728062375501053209826898515195688795168508053276451648167845974950498097861107980571119616 

noncomputable def Ns168p1932 := nat_lit 22772096276429721304206791449540659761170936013395207559503883890195233805106795215526266125074918301634560 

noncomputable def Ns168p1933 := BSN.cos_dyadic_bound_f 205515054 134217728 4 3 134217728 67108864 Ns168p1930 Ns168p118 Ns168p1931 Ns168p1932 Ns168p121 Ns168p1931 5312272 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 205515054) qz363 0 3 Ns168p1930 Ns168p118 Ns168p1931 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 205515054) qz364 0 3 Ns168p1932 Ns168p121 Ns168p1931 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1934 := Ns168p1873 89257 BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 62049834 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 88 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 5312272 134217728) qz232 rfl rfl (Ns168p1925 rfl rfl) (Ns168p1907 rfl) RS169to186.d27 RS169to186.d29 RS169to186.d31 RS169to186.d33 RS169to186.d17 (Ns168p1929 rfl rfl) (Ns168p1933 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns168p1935 := nat_lit 23708291865165275095593441322398615916401900885977092585982440671265 

noncomputable def Ns168p1936 := nat_lit 583628525899644490277961550694387069006576230773879518522411041 

noncomputable def Ns168p1937 := nat_lit 62092200438771882968808086763771441249607539292233037158352594044961 

noncomputable def Ns168p1938 := BSN.sin_dyadic_bound_f 70107917 134217728 3 2 134217728 67108864 Ns168p1935 Ns168p112 Ns168p1936 Ns168p1937 Ns168p115 Ns168p1936 66963040 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 70107917) qz361 0 2 Ns168p1935 Ns168p112 Ns168p1936 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 70107917) qz362 0 2 Ns168p1937 Ns168p115 Ns168p1936 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1939 := Ns168p1871 Bool.true 69153432 89257 Bool.true 70107917 7074237752028440 1 Bool.false 66963040 Bool.false Bool.true 45478425 99461 BSN.abs_quadSignPos qz365 (BSN.sfrac_eq_quadSignPos_mul Bool.false 66963040 134217728) qz232 rfl (Ns168p1934 rfl) (Ns168p1907 rfl) RS169to186.d35 RS169to186.d37 RS169to186.d17 (Ns168p1938 rfl rfl) rfl 

noncomputable def Ns168p1940 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz229) qz229 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz229) qz229 8) 45478425 134217728 99461 134217728 45478425 134217728 99461 134217728 12208021753036800 45478425 67108864 99461 67108864 (Ns168p1939 rfl rfl rfl rfl) 

noncomputable def Ns168p1941 := @Enclosure.Real.IsNear.mulLit_ff qz812 (Zeta.RiemannSiegel.correction qz231) 5763251 16777216 1 16777216 54020394653715 140737488355328 33694462472083 1319413953331200000 311333093508417627465 2361183241434822606848 

noncomputable abbrev qz817 := (@HPow.hPow Real Real Real qz7 qz230 qz9)

noncomputable def Ns168p1942 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz817 1 1 0 1 5763251 16777216 1 16777216 5763251 16777216 1 16777216 

noncomputable def Ns168p1943 := @Enclosure.Real.IsNear.sqrt_image qz230 1204839936117 16777216000 451221 16777216000 71087713 71087741 8388608 (@Enclosure.Real.IsNear.of_eq qz230 (@HMul.hMul Real Real Real qz5 qz229 qz3) Bool.false 1204839936117 16777216000 451221 16777216000 (BSN.t_div_two_pi_mk qz229 451221 1000 qz232) (@Enclosure.Real.IsNear.mulLit_ff qz229 qz3 451221 1000 0 1 2670177 16777216 1 16777216 1204839936117 16777216000 451221 16777216000 (Enclosure.Real.IsNear.const Bool.false 451221 1000) RS169to186.d40 rfl)) 

noncomputable abbrev qz960 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 451221 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz818 := qz960

noncomputable abbrev qz579 := qz818

noncomputable abbrev qz234 := qz579

noncomputable def Ns168p1944 := @Enclosure.Real.IsNear.sqrt_image qz234 71087727 8388608 7 4194304 24419806 24419812 8388608 (@Enclosure.Real.IsNear.recentre' qz234 Bool.false 142175454 16777216 28 16777216 71087727 8388608 7 4194304 (Ns168p1943 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns168p1945 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz234) 24419809 8388608 3 8388608 2881625 2881626 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz234) Bool.false 48839618 16777216 6 16777216 24419809 8388608 3 8388608 (Ns168p1944 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns168p1946 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz234)) Bool.false 5763251 16777216 1 16777216 5763251 16777216 1 16777216 (Ns168p1945 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz235 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz573))

noncomputable abbrev qz819 := (@HMul.hMul Real Real Real qz890 qz959 qz959)

noncomputable abbrev qz580 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz819 qz811) qz641)

noncomputable abbrev qz236 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz580))

noncomputable def Ns168p1947 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz231) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz235) qz236) Bool.false 54020394653715 

noncomputable def Ns168p1948 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz235) qz236 16998049 16777216 191 

noncomputable abbrev qz820 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz235))

noncomputable def Ns168p1949 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz235) (@Neg.neg Real Real.instNeg qz820) Bool.true 16998049 16777216 191 16777216 (BSN.inv_eq_neg_inv_neg qz235) 

noncomputable def Ns168p1950 := @Enclosure.Real.IsNear.recentre' qz820 Bool.false 16998049 16777216 191 16777216 16998049 16777216 

noncomputable def Ns168p1951 := @Enclosure.Real.IsNear.recentre' qz235 Bool.true 16559252 16777216 415027216 37748736000000 4139813 4194304 25939201 2359296000000 

noncomputable abbrev qz237 := (@HMul.hMul Real Real Real qz342 qz340 qz573)

noncomputable def Ns168p1952 := @Enclosure.Real.IsNear.cos_image qz237 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49999867) qz370) Bool.false 49999867 16777216 177 16777216 Bool.true 16559252 16777216 1 

noncomputable def Ns168p1953 := nat_lit 188902527880397404646447217 

noncomputable def Ns168p1954 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz231 884279719003555 140737488355328 1 500000000000000 3978863 8388608 7 4194304 3518427855593641857965 1180591620717411303424 Ns168p1953 

noncomputable def Ns168p1955 := @Enclosure.Real.IsNear.subLit_ff_p qz234 qz1 71087727 8388608 7 4194304 8 1 0 1 3978863 3978863 8388608 7 

noncomputable def Ns168p1956 := @Ns168p1955 4194304 (@Enclosure.Real.IsNear.recentre' qz234 Bool.false 142175454 16777216 28 16777216 71087727 8388608 7 4194304 (Ns168p1943 rfl rfl rfl rfl rfl rfl) rfl) qz371 

noncomputable def Ns168p1957 := @Enclosure.Real.IsNear.recentre' qz237 Bool.false 3518427855593641857965 1180591620717411303424 Ns168p1953 Ns168p1070 49999867 16777216 177 16777216 (@Ns168p1954 Ns168p1070 RS169to186.d39 (Ns168p1956 rfl rfl) rfl) 

noncomputable def Ns168p1958 := nat_lit 3407787762836441078431744 

noncomputable def Ns168p1959 := nat_lit 23212316930936574405872906727521131101334869076684502520244880520744182185155589761516705 

noncomputable def Ns168p1960 := nat_lit 30251151324448239890119288417447534455322146188944311300797352697373834638512135193761 

noncomputable def Ns168p1961 := nat_lit 60745185336022873912702181628927094971520802202248739620440062792819967133611810680325281 

noncomputable def Ns168p1962 := BSN.sin_dyadic_bound_f 48427576797 34359738368 3 2 16777216 4504395 Ns168p1959 Ns168p1076 Ns168p1960 Ns168p1961 Ns168p1079 Ns168p1960 16559252 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 48427576797) qz358 0 2 Ns168p1959 Ns168p1076 Ns168p1960 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 48427576797) qz359 0 2 Ns168p1961 Ns168p1079 Ns168p1960 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1963 := @Ns168p1952 2250000 (Ns168p1957 rfl) (Enclosure.sfrac_false_div 49999867 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49999867) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns168p1958) qz385) 226375608064910080 72057594037927936 Bool.false 16559252 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 49999867 16777216 226375608064910080 72057594037927936 0 Ns168p1958 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16559252 16777216 Ns168p1958 Ns168p89 48427576797 34359738368 4504395 4500000 (Ns168p1962 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p1964 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz235) 4139813 4194304 25939201 2359296000000 8498929 8499120 8388608 (@Enclosure.Real.IsNear.neg qz235 Bool.true 4139813 4194304 25939201 2359296000000 (Ns168p1951 (Ns168p1963 rfl rfl) rfl)) 

noncomputable def Ns168p1965 := Ns168p1949 (@Enclosure.Real.IsNear.neg qz820 Bool.false 16998049 16777216 191 16777216 (@Ns168p1950 191 16777216 (Ns168p1964 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p1966 := @Enclosure.Real.IsNear.recentre' qz236 Bool.true 3178035 8388608 

noncomputable abbrev qz238 := (@HMul.hMul Real Real Real qz342 qz340 qz580)

noncomputable def Ns168p1967 := @Enclosure.Real.IsNear.cos_image qz238 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32872455)) qz370) Bool.true 32872455 16777216 

noncomputable def Ns168p1968 := nat_lit 19404472977068394770074843645 

noncomputable def Ns168p1969 := nat_lit 771966614656895544967567440694539 

noncomputable def Ns168p1970 := @Enclosure.Real.IsNear.recentre' qz238 Bool.true Ns168p1968 Ns168p1196 Ns168p1969 

noncomputable def Ns168p1971 := nat_lit 37778931862957161709568000000000000000 

noncomputable abbrev qz239 := qz580

noncomputable def Ns168p1972 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz239 884279719003555 140737488355328 1 500000000000000 21943817731039 

noncomputable abbrev qz581 := (@HSub.hSub Real Real Real qz633 qz819 qz811)

noncomputable abbrev qz240 := qz581

noncomputable def Ns168p1973 := @Enclosure.Real.IsNear.subLit_tf qz240 qz25 17545771219935 70368744177664 28606109 8796093022208 1 16 

noncomputable abbrev qz582 := qz819

noncomputable abbrev qz241 := qz582

noncomputable def Ns168p1974 := @Enclosure.Real.IsNear.subLit_ff_n qz241 qz231 15831350772769 70368744177664 13926045 8796093022208 3978863 8388608 7 4194304 

noncomputable def Ns168p1975 := @Enclosure.Real.IsNear.mulLit_ff qz231 qz231 3978863 8388608 7 4194304 3978863 8388608 7 4194304 15831350772769 70368744177664 

noncomputable def Ns168p1976 := nat_lit 147574564373499348685016581749412367083056141448859247842324104409461054839780958206443969390625 

noncomputable def Ns168p1977 := nat_lit 1592156207246526141114346845955096093273586187386786058989978190799505633680075801025390625 

noncomputable def Ns168p1978 := nat_lit 890087089910863535893077495856809414857876724686960044500516900974094665512562456071363418990625 

noncomputable def Ns168p1979 := BSN.cos_dyadic_bound_t 32872455 16777216 4 3 8388608 2250000 Ns168p1976 Ns168p169 Ns168p1977 Ns168p1978 Ns168p172 Ns168p1977 3178035 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32872455) qz642 0 3 Ns168p1976 Ns168p169 Ns168p1977 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32872455) (BSN.cosOddQ 16777216) 0 3 Ns168p1978 Ns168p172 Ns168p1977 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p1980 := @Ns168p1966 98847152 4718592000000 3178035 8388608 6177947 294912000000 (@Ns168p1967 43 2097152 Bool.true 3178035 8388608 1 2250000 (@Ns168p1970 Ns168p1971 32872455 16777216 43 2097152 (@Ns168p1972 70368744177664 28606109 8796093022208 Ns168p1968 Ns168p1196 Ns168p1969 Ns168p1971 RS169to186.d39 (@Ns168p1973 0 1 351101083696624 21943817731039 70368744177664 28606109 8796093022208 (@Ns168p1974 147184596821716500480 17545771219935 70368744177664 28606109 8796093022208 (@Ns168p1975 13926045 8796093022208 (Ns168p1956 rfl rfl) (Ns168p1956 rfl rfl) rfl) (Ns168p1956 rfl rfl) rfl rfl) qz375 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32872455 16777216) (BSN.cos_neg_of_bound 32872455 16777216 Bool.true 3178035 8388608 1 2250000 (Ns168p1979 rfl rfl)) rfl rfl) 

noncomputable def Ns168p1981 := @Ns168p1941 64898706477011957347 Ns168p1868 (Ns168p1942 qz27 (@Enclosure.Real.IsNear.of_eq qz817 (@Inv.inv Real Real.instInv (Real.sqrt qz234)) Bool.false 5763251 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz230 (BSN.t_div_two_pi_nonneg qz229 451221 1000 qz232)) Ns168p1946) rfl) (@Ns168p1947 140737488355328 33694462472083 1319413953331200000 (BSN.correction_mk qz231 (BSN.cos_two_pi_p_ne_zero_mk qz229 451221 1000 8 qz232 rfl rfl (@BSN.floor_sqrt_eq_dec qz229 451221 1000 8 qz232 rfl rfl rfl))) (@Ns168p1948 16777216 3178035 8388608 6177947 294912000000 54020394653715 140737488355328 33694462472083 1319413953331200000 Ns168p1965 (Ns168p1980 rfl) rfl)) 

noncomputable def Ns168p1982 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz229) (hardyZApproximantRS₀ qz229) Bool.true 1911462920722457077065 2361183241434822606848 11000751307499885557347 Ns168p1868 (@Eq.refl Real (hardyZApproximantRS₀ qz229)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz229) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz229) qz229 8) (@HMul.hMul Real Real Real qz5 qz812 (Zeta.RiemannSiegel.correction qz231))) Bool.true 1911462920722457077065 2361183241434822606848 11000751307499885557347 Ns168p1868 (BSN.hardyZApproximantRS₀_eq qz229 8 (@BSN.floor_sqrt_eq_dec qz229 451221 1000 8 qz232 rfl rfl rfl)) (@Ns168p1870 1911462920722457077065 2361183241434822606848 11000751307499885557347 Ns168p1868 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz229) qz229 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz229) qz229 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz229) qz229 8)) Bool.true 45478425 67108864 99461 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz229) qz229 8) (Ns168p1940 (Ns168p1939 rfl rfl rfl rfl) rfl rfl)) (Ns168p1981 rfl) rfl rfl)) 

theorem RS169to186.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz229) Bool.true 1911462920722457077065 2361183241434822606848 11000751307499885557347 Ns168p1868 := Ns168p1982 

noncomputable def Ns168p1983 := nat_lit 8237745868251468187400404992 

noncomputable abbrev qz961 := (Enclosure.sfrac Bool.false 452691 1000)

noncomputable abbrev qz821 := qz961

noncomputable abbrev qz583 := qz821

noncomputable abbrev qz242 := qz583

noncomputable abbrev qz962 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 452691 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz822 := qz962

noncomputable abbrev qz584 := qz822

noncomputable abbrev qz243 := qz584

noncomputable abbrev qz963 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 452691 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz823 := qz963

noncomputable abbrev qz585 := qz823

noncomputable abbrev qz244 := qz585

noncomputable abbrev qz824 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz243 qz9))

noncomputable def Ns168p1984 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz242) qz242 8) (@HMul.hMul Real Real Real qz5 qz824 (Zeta.RiemannSiegel.correction qz244)) 227694813 33554432 24947 16777216 4849136364246635307 36893488147419103232 8134663346595199177 922337203685477580800000 Ns168p1983 

noncomputable def Ns168p1985 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz242) qz242 Real.sin BSN.quadSignPos 7 8 452691 1000 127 134217728 67108864 2251799813685248 Bool.false 99511286155 1765 279097919 60 47453128 8 

noncomputable def Ns168p1986 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz242) qz242 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 452691 1000 44 88 134217728 67108864 2251799813685248 Bool.false 99511286155 1765 

noncomputable def Ns168p1987 := Ns168p1986 240485871 61 54794152 8 261175631 61 50729528 8 Bool.false 373496950 66432 Bool.true 78039852 Bool.true 167644574 7074237752028440 1 Bool.false 112161918 Bool.false Bool.false 42442909 Bool.false Bool.false 435328766 

noncomputable def Ns168p1988 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz242) qz242 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 452691 1000 72 8 134217728 67108864 2251799813685248 Bool.false 99511286155 1765 

noncomputable def Ns168p1989 := Ns168p1988 186065264 60 67108856 8 216015088 60 60023992 8 Bool.false 266887181 39012 Bool.false 101548311 Bool.false 36570240 7074237752028440 1 Bool.false 97600226 Bool.false Bool.false 129266336 Bool.false Bool.false 373496950 

noncomputable def Ns168p1990 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz242) qz242 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 452691 1000 272 155 134217728 67108864 2251799813685248 Bool.false 99511286155 1765 

noncomputable def Ns168p1991 := Ns168p1990 93032624 60 94906264 8 147453232 60 77490640 16 Bool.false 134217656 1828 Bool.false 50844319 Bool.false 82084417 7074237752028440 1 Bool.false 124701930 Bool.false Bool.false 77062313 Bool.false Bool.false 266887181 

noncomputable def Ns168p1992 := nat_lit 114946294009051596838063449713707285545934051691612691891 

noncomputable def Ns168p1993 := nat_lit 155035986569310803406921429606199967448044608159744000 

noncomputable def Ns168p1994 := nat_lit 9125399388629125278866382936480000 

noncomputable def Ns168p1995 := nat_lit 24785931158600455693315695996684406080 

noncomputable abbrev qz964 := (@Eq.refl Real (Enclosure.sfrac Bool.false 452691 1000))

noncomputable abbrev qz825 := qz964

noncomputable abbrev qz586 := qz825

noncomputable abbrev qz245 := qz586

noncomputable def Ns168p1996 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz242 452691 1000 819717565924 16000000 905382 4000 2000 Ns168p1994 Ns168p1995 qz245 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns168p1997 := nat_lit 331045326746068598893622735175476982372290068871844552646080 

noncomputable abbrev qz826 := (Real.log (Enclosure.sfrac Bool.false 819717565924 16000000))

noncomputable abbrev qz246 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 452691 4000) qz826) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 905382))))))

noncomputable abbrev qz827 := (Enclosure.sfrac Bool.false 452691 2000)

noncomputable abbrev qz587 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz246 qz827) (@HMul.hMul Real Real Real qz5 qz827 (Real.log Real.pi)))

noncomputable def Ns168p1998 := @Enclosure.Real.IsNear.addLit_ft_p qz587 (Enclosure.sfrac Bool.true Ns168p1994 Ns168p1995) 13356185370497184784251 18014398509481984000 48454444784633059 3686400000000000000000 Ns168p1994 Ns168p1995 0 1 Ns168p1997 

noncomputable def Ns168p1999 := nat_lit 896318427587485186069169700864000 

noncomputable abbrev qz588 := (@HSub.hSub Real Real Real qz12 qz246 qz827)

noncomputable abbrev qz589 := (@HMul.hMul Real Real Real qz5 qz827 (Real.log Real.pi))

noncomputable def Ns168p2000 := @Enclosure.Real.IsNear.subLit_ff_p qz588 qz589 18023796325549516349307 18014398509481984000 46069112223557 7200000000000000000 17388205807851 67108864000 452691 67108864000 Ns168p1999 13356185370497184784251 18014398509481984000 

noncomputable def Ns168p2001 := nat_lit 36047592651099032698614000 

noncomputable abbrev qz590 := qz827

noncomputable def Ns168p2002 := @Enclosure.Real.IsNear.subLit_ff_p qz246 qz590 22101274363377470758779 18014398509481984000 46069112223557 7200000000000000000 452691 2000 0 1 Ns168p2001 18023796325549516349307 18014398509481984000 46069112223557 7200000000000000000 

noncomputable def Ns168p2003 := nat_lit 49767645493659936757987205390838792192 

noncomputable def Ns168p2004 := nat_lit 26219488803284985606832128 

noncomputable def Ns168p2005 := nat_lit 199910297884343878559853876547801473156744058211803707491156390922999355913558749122065384138098082141470263422435738407403520 

noncomputable def Ns168p2006 := nat_lit 3316420987175185819046785596141293664548715928493671627120815056961715387417361550670682586946527748776941379735991436181504 

noncomputable def Ns168p2007 := nat_lit 4785985429745730334992573311315061153360364215269393295426485318654237402812497375673577979135627074152350924873400320 

noncomputable def Ns168p2008 := BSN.log_dyadic_bound 295429565924 1344005565924 6 5 Ns168p2005 67108864 18000000 Ns168p2006 Ns168p2007 29992206 1639435131848 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 295429565924) (BSN.artanhQ 1344005565924) 0 5 Ns168p2006 Ns168p2005 Ns168p2007 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns168p2009 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 452691 4000) qz826 452691 4000 0 1 48837603634754169 4503599627370496 100000027 1800000000000000 22108343627020499518779 18014398509481984000 5029901358073 800000000000000000 (Enclosure.Real.IsNear.const Bool.false 452691 4000) (BSN.isNear_log_sfrac 819717565924 16000000 48837603634754169 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 819717565924) qz353)) Bool.false Ns168p2004 Ns168p89 1000000270000000 18000000000000000000000 48837603634754169 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 819717565924 16000000 15 1639435131848 1048576000000 29992206 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns168p2008 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p2010 := BSN.arctan_dyadic_bound_f 1000 905382 1 0 8388608 2250000 0 1 1 0 1 1 9265 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 905382) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 905382) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz828 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 905382)))

noncomputable def Ns168p2011 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz828 884279719003555 562949953421312 1 2000000000000000 9265 8388608 1 2250000 7412660193752525045760 883657955378595 562949953421312 8000000009 18000000000000000 qz16 (Ns168p2010 rfl) rfl rfl 

noncomputable def Ns168p2012 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 452691 4000) qz826) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz828)) 22108343627020499518779 18014398509481984000 5029901358073 800000000000000000 883657955378595 2251799813685248 8000000009 72000000000000000 Ns168p2003 22101274363377470758779 18014398509481984000 46069112223557 7200000000000000000 (Ns168p2009 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz828) 1 4 0 1 883657955378595 562949953421312 8000000009 18000000000000000 883657955378595 2251799813685248 8000000009 72000000000000000 qz356 Ns168p2011 rfl) 

noncomputable def Ns168p2013 := @Ns168p1998 Ns168p1992 Ns168p1993 48454444784633059 3686400000000000000000 (@Ns168p2000 48454444784633059 3686400000000000000000 (Ns168p2002 (Ns168p2012 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 452691 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz590 (Real.log Real.pi) 452691 2000 0 1 38410761 33554432 1 33554432 17388205807851 67108864000 452691 67108864000 (Enclosure.Real.IsNear.const Bool.false 452691 2000) RS169to186.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns168p1994 Ns168p1995) 

noncomputable def Ns168p2014 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz242) Bool.false Ns168p1992 Ns168p1993 48454444784633059 3686400000000000000000 12438910769 16777216 221 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz242) (@HAdd.hAdd Real Real Real qz357 qz587 (Enclosure.sfrac Bool.true Ns168p1994 Ns168p1995)) Bool.false Ns168p1992 Ns168p1993 48454444784633059 3686400000000000000000 Ns168p1996 (Ns168p2013 rfl rfl)) 

noncomputable def Ns168p2015 := BSN.cos_dyadic_bound_f 34068774 34359738368 1 0 16777216 4504395 0 1 1 0 1 1 16777207 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 34068774) qz682 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 34068774) qz683 0 0 rfl) rfl rfl 

noncomputable def Ns168p2016 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz242) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12438910769) qz370) Bool.false 12438910769 16777216 221 16777216 Bool.false 16777207 16777216 1 2250000 (Ns168p2014 rfl) (Enclosure.sfrac_false_div 12438910769 16777216) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12438910769) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2397376872254860689408) qz385) 226375608064910080 72057594037927936 Bool.false 16777207 16777216 118 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q0 12438910769 16777216 226375608064910080 72057594037927936 118 2397376872254860689408 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777207 16777216 2397376872254860689408 Ns168p89 34068774 34359738368 4504395 4500000 (Ns168p2015 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p2017 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz242) Bool.false Ns168p1992 Ns168p1993 48454444784633059 3686400000000000000000 99511286155 134217728 1765 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz242) (@HAdd.hAdd Real Real Real qz357 qz587 (Enclosure.sfrac Bool.true Ns168p1994 Ns168p1995)) Bool.false Ns168p1992 Ns168p1993 48454444784633059 3686400000000000000000 Ns168p1996 (Ns168p2013 rfl rfl)) 

noncomputable def Ns168p2018 := Ns168p1991 39012 BSN.abs_quadSignPos (BSN.cos_quad_nat0 272 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 124701930 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 155 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 77062313 134217728) qz245 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz242) qz242 1) Bool.false 16777207 16777216 32126701 2359296000000 134217656 134217728 1828 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz242) qz242 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz242)) Bool.false 16777207 16777216 32126701 2359296000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz242) qz242) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz242)) Bool.false 16777207 16777216 514027216 37748736000000 16777207 16777216 32126701 2359296000000 (Ns168p2016 rfl rfl) rfl)) rfl) (Ns168p2017 rfl) RS169to186.d7 

noncomputable def Ns168p2019 := nat_lit 3643542807657467338423947446132141947459112546880284220119274904321 

noncomputable def Ns168p2020 := nat_lit 44662134875295442618433240586023248120491636676783572808784641 

noncomputable def Ns168p2021 := nat_lit 10930539098702651424386605471915253795881096657367499093212207143681 

noncomputable def Ns168p2022 := BSN.cos_dyadic_bound_f 50844319 134217728 3 2 134217728 67108864 Ns168p2019 Ns168p124 Ns168p2020 Ns168p2021 Ns168p127 Ns168p2020 124701930 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 50844319) qz363 0 2 Ns168p2019 Ns168p124 Ns168p2020 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 50844319) qz364 0 2 Ns168p2021 Ns168p127 Ns168p2020 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p2023 := nat_lit 44553751804471697002498356568129490338057172951479903163095442379265 

noncomputable def Ns168p2024 := nat_lit 2061036788766522258934113842811451571884457758946665093995287041 

noncomputable def Ns168p2025 := nat_lit 116685060666434536827647897684593637106652401941313832731288261480961 

noncomputable def Ns168p2026 := BSN.sin_dyadic_bound_f 82084417 134217728 3 2 134217728 67108864 Ns168p2023 Ns168p112 Ns168p2024 Ns168p2025 Ns168p115 Ns168p2024 77062313 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 82084417) qz361 0 2 Ns168p2023 Ns168p112 Ns168p2024 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 82084417) qz362 0 2 Ns168p2025 Ns168p115 Ns168p2024 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p2027 := nat_lit 57986157546853613424286396164747429757886690310650835728210992170561 

noncomputable def Ns168p2028 := nat_lit 11307891565343070481611232077354314865800559894625928599937353281 

noncomputable def Ns168p2029 := nat_lit 173935856857430154131895966030087580643928469812163255327433101805121 

noncomputable def Ns168p2030 := BSN.cos_dyadic_bound_f 101548311 134217728 3 2 134217728 67108864 Ns168p2027 Ns168p124 Ns168p2028 Ns168p2029 Ns168p127 Ns168p2028 97600226 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 101548311) qz363 0 2 Ns168p2027 Ns168p124 Ns168p2028 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 101548311) qz364 0 2 Ns168p2029 Ns168p127 Ns168p2028 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p2031 := nat_lit 1788591827351222611618037760000 

noncomputable def Ns168p2032 := BSN.cos_dyadic_bound_f 36570240 134217728 2 1 134217728 67108864 Ns168p2031 Ns168p130 Ns168p2031 Ns168p2031 Ns168p131 Ns168p2031 129266336 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 36570240) qz363 0 1 Ns168p2031 Ns168p130 Ns168p2031 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 36570240) qz364 0 1 Ns168p2031 Ns168p131 Ns168p2031 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p2033 := Ns168p1989 66432 BSN.abs_quadSignPos (BSN.cos_quad_nat0 72 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 97600226 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 8 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 129266336 134217728) qz245 rfl rfl (Ns168p2018 RS169to186.d9 RS169to186.d11 RS169to186.d13 RS169to186.d17 (Ns168p2022 rfl rfl) (Ns168p2026 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns168p2017 rfl) RS169to186.d19 RS169to186.d21 RS169to186.d23 RS169to186.d25 RS169to186.d17 (Ns168p2030 rfl rfl) (Ns168p2032 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns168p2034 := nat_lit 20222931322930888788018513127055891129285980380137387623555688103936 

noncomputable def Ns168p2035 := nat_lit 1375724579744977961654759106165459128838819760528081604701126656 

noncomputable def Ns168p2036 := nat_lit 60666042519633176408132229862955342469600263500891106707457662058496 

noncomputable def Ns168p2037 := BSN.cos_dyadic_bound_f 78039852 134217728 3 2 134217728 67108864 Ns168p2034 Ns168p124 Ns168p2035 Ns168p2036 Ns168p127 Ns168p2035 112161918 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 78039852) qz363 0 2 Ns168p2034 Ns168p124 Ns168p2035 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 78039852) qz364 0 2 Ns168p2036 Ns168p127 Ns168p2035 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p2038 := nat_lit 1662614915950177162329740473711679317787242257864470466677083630405441630338234985038564053478328726982656 

noncomputable def Ns168p2039 := nat_lit 492803766992679184422649074977621764375089241885831662687190114424285309280982401984322443187326976 

noncomputable def Ns168p2040 := nat_lit 10076799829768908404600232761992979336216377394696844685834229054309588728337534013373151785619672835297280 

noncomputable def Ns168p2041 := BSN.cos_dyadic_bound_f 167644574 134217728 4 3 134217728 67108864 Ns168p2038 Ns168p118 Ns168p2039 Ns168p2040 Ns168p121 Ns168p2039 42442909 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 167644574) qz363 0 3 Ns168p2038 Ns168p118 Ns168p2039 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 167644574) qz364 0 3 Ns168p2040 Ns168p121 Ns168p2039 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p2042 := Ns168p1987 89550 BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 112161918 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 88 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 42442909 134217728) qz245 rfl rfl (Ns168p2033 rfl rfl) (Ns168p2017 rfl) RS169to186.d27 RS169to186.d29 RS169to186.d31 RS169to186.d33 RS169to186.d17 (Ns168p2037 rfl rfl) (Ns168p2041 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns168p2043 := nat_lit 11778564435930663518617600000000 

noncomputable def Ns168p2044 := BSN.sin_dyadic_bound_f 58583200 134217728 2 1 134217728 67108864 Ns168p2043 Ns168p394 Ns168p2043 Ns168p2043 Ns168p395 Ns168p2043 56740687 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 58583200) qz361 0 1 Ns168p2043 Ns168p394 Ns168p2043 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 58583200) qz362 0 1 Ns168p2043 Ns168p395 Ns168p2043 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p2045 := Ns168p1985 Bool.false 435328766 89550 Bool.true 58583200 7074237752028440 1 Bool.false 56740687 Bool.false Bool.false 455389626 99788 BSN.abs_quadSignPos qz365 (BSN.sfrac_eq_quadSignPos_mul Bool.false 56740687 134217728) qz245 rfl (Ns168p2042 rfl) (Ns168p2017 rfl) RS169to186.d35 RS169to186.d37 RS169to186.d17 (Ns168p2044 rfl rfl) rfl 

noncomputable def Ns168p2046 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz242) qz242 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz242) qz242 8) 455389626 134217728 99788 134217728 455389626 134217728 99788 134217728 122242721912979456 227694813 33554432 24947 16777216 (Ns168p2045 rfl rfl rfl rfl) 

noncomputable def Ns168p2047 := @Enclosure.Real.IsNear.mulLit_ff qz824 (Zeta.RiemannSiegel.correction qz244) 2879283 8388608 1 8388608 1684147186729 4398046511104 11242461204837 439804651110400000 4849136364246635307 36893488147419103232 

noncomputable abbrev qz829 := (@HPow.hPow Real Real Real qz7 qz243 qz9)

noncomputable def Ns168p2048 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz829 1 1 0 1 2879283 8388608 1 8388608 2879283 8388608 1 8388608 

noncomputable def Ns168p2049 := @Enclosure.Real.IsNear.sqrt_image qz243 1208765096307 16777216000 452691 16777216000 71203415 71203443 8388608 (@Enclosure.Real.IsNear.of_eq qz243 (@HMul.hMul Real Real Real qz5 qz242 qz3) Bool.false 1208765096307 16777216000 452691 16777216000 (BSN.t_div_two_pi_mk qz242 452691 1000 qz245) (@Enclosure.Real.IsNear.mulLit_ff qz242 qz3 452691 1000 0 1 2670177 16777216 1 16777216 1208765096307 16777216000 452691 16777216000 (Enclosure.Real.IsNear.const Bool.false 452691 1000) RS169to186.d40 rfl)) 

noncomputable abbrev qz965 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 452691 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz830 := qz965

noncomputable abbrev qz591 := qz830

noncomputable abbrev qz247 := qz591

noncomputable def Ns168p2050 := @Enclosure.Real.IsNear.sqrt_image qz247 71203429 8388608 7 4194304 24439671 24439677 8388608 (@Enclosure.Real.IsNear.recentre' qz247 Bool.false 142406858 16777216 28 16777216 71203429 8388608 7 4194304 (Ns168p2049 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns168p2051 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz247) 12219837 4194304 3 8388608 2879282 2879284 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz247) Bool.false 48879348 16777216 6 16777216 12219837 4194304 3 8388608 (Ns168p2050 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns168p2052 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz247)) Bool.false 5758566 16777216 2 16777216 2879283 8388608 1 8388608 (Ns168p2051 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz248 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz585))

noncomputable abbrev qz831 := (@HMul.hMul Real Real Real qz890 qz963 qz963)

noncomputable abbrev qz592 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz831 qz823) qz641)

noncomputable abbrev qz249 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz592))

noncomputable def Ns168p2053 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz244) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz248) qz249) Bool.false 1684147186729 

noncomputable def Ns168p2054 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz248) qz249 16824143 16777216 187 

noncomputable abbrev qz832 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz248))

noncomputable def Ns168p2055 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz248) (@Neg.neg Real Real.instNeg qz832) Bool.true 16824143 16777216 187 16777216 (BSN.inv_eq_neg_inv_neg qz248) 

noncomputable def Ns168p2056 := @Enclosure.Real.IsNear.recentre' qz832 Bool.false 16824143 16777216 187 16777216 16824143 16777216 

noncomputable def Ns168p2057 := @Enclosure.Real.IsNear.recentre' qz248 Bool.true 16730420 16777216 415027216 37748736000000 4182605 4194304 25939201 2359296000000 

noncomputable abbrev qz250 := (@HMul.hMul Real Real Real qz342 qz340 qz585)

noncomputable def Ns168p2058 := @Enclosure.Real.IsNear.cos_image qz250 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51453821) qz370) Bool.false 51453821 16777216 177 16777216 Bool.true 16730420 16777216 1 

noncomputable def Ns168p2059 := nat_lit 188902527880894340952529009 

noncomputable def Ns168p2060 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz244 884279719003555 140737488355328 1 500000000000000 4094565 8388608 7 4194304 3620740787641791178575 1180591620717411303424 Ns168p2059 

noncomputable def Ns168p2061 := @Enclosure.Real.IsNear.subLit_ff_p qz247 qz1 71203429 8388608 7 4194304 8 1 0 1 4094565 4094565 8388608 7 

noncomputable def Ns168p2062 := @Ns168p2061 4194304 (@Enclosure.Real.IsNear.recentre' qz247 Bool.false 142406858 16777216 28 16777216 71203429 8388608 7 4194304 (Ns168p2049 rfl rfl rfl rfl rfl rfl) rfl) qz371 

noncomputable def Ns168p2063 := @Enclosure.Real.IsNear.recentre' qz250 Bool.false 3620740787641791178575 1180591620717411303424 Ns168p2059 Ns168p1070 51453821 16777216 177 16777216 (@Ns168p2060 Ns168p1070 RS169to186.d39 (Ns168p2062 rfl rfl) rfl) 

noncomputable def Ns168p2064 := nat_lit 3617324617000084026949632 

noncomputable def Ns168p2065 := nat_lit 29480226971357560764919170070772429559658033886441296688861033320295993720100459815650465 

noncomputable def Ns168p2066 := nat_lit 48759749604989978228286874104482074665938770238583641549794572364633121341861874386081 

noncomputable def Ns168p2067 := nat_lit 77131173901814103943371076198711011202026187884102832098793515102661053737138189815792801 

noncomputable def Ns168p2068 := BSN.sin_dyadic_bound_f 51405274589 34359738368 3 2 16777216 4504395 Ns168p2065 Ns168p1076 Ns168p2066 Ns168p2067 Ns168p1079 Ns168p2066 16730420 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 51405274589) qz358 0 2 Ns168p2065 Ns168p1076 Ns168p2066 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 51405274589) qz359 0 2 Ns168p2067 Ns168p1079 Ns168p2066 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p2069 := @Ns168p2058 2250000 (Ns168p2063 rfl) (Enclosure.sfrac_false_div 51453821 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51453821) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns168p2064) qz385) 226375608064910080 72057594037927936 Bool.false 16730420 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 51453821 16777216 226375608064910080 72057594037927936 0 Ns168p2064 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16730420 16777216 Ns168p2064 Ns168p89 51405274589 34359738368 4504395 4500000 (Ns168p2068 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p2070 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz248) 4182605 4194304 25939201 2359296000000 8411978 8412165 8388608 (@Enclosure.Real.IsNear.neg qz248 Bool.true 4182605 4194304 25939201 2359296000000 (Ns168p2057 (Ns168p2069 rfl rfl) rfl)) 

noncomputable def Ns168p2071 := Ns168p2055 (@Enclosure.Real.IsNear.neg qz832 Bool.false 16824143 16777216 187 16777216 (@Ns168p2056 187 16777216 (Ns168p2070 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p2072 := @Enclosure.Real.IsNear.recentre' qz249 Bool.true 3203296 8388608 

noncomputable abbrev qz251 := (@HMul.hMul Real Real Real qz342 qz340 qz592)

noncomputable def Ns168p2073 := @Enclosure.Real.IsNear.cos_image qz251 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8231771)) qz405) Bool.true 8231771 4194304 

noncomputable def Ns168p2074 := nat_lit 19436719966991330472944703445 

noncomputable def Ns168p2075 := nat_lit 391447407398177475289597007432299 

noncomputable def Ns168p2076 := @Enclosure.Real.IsNear.recentre' qz251 Bool.true Ns168p2074 Ns168p1196 Ns168p2075 

noncomputable def Ns168p2077 := nat_lit 18889465931478580854784000000000000000 

noncomputable abbrev qz252 := qz592

noncomputable def Ns168p2078 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz252 884279719003555 140737488355328 1 500000000000000 21980284687399 

noncomputable abbrev qz593 := (@HSub.hSub Real Real Real qz633 qz831 qz823)

noncomputable abbrev qz253 := qz593

noncomputable def Ns168p2079 := @Enclosure.Real.IsNear.subLit_tf qz253 qz25 17582238176295 70368744177664 14505533 4398046511104 1 16 

noncomputable abbrev qz594 := qz831

noncomputable abbrev qz254 := qz594

noncomputable def Ns168p2080 := @Enclosure.Real.IsNear.subLit_ff_n qz254 qz244 16765462539225 70368744177664 7165501 4398046511104 4094565 8388608 7 4194304 

noncomputable def Ns168p2081 := @Enclosure.Real.IsNear.mulLit_ff qz244 qz244 4094565 8388608 7 4194304 4094565 8388608 7 4194304 16765462539225 70368744177664 

noncomputable def Ns168p2082 := nat_lit 8855261135739580641588927335622490473252186192360047617336128097438908221907420763143121 

noncomputable def Ns168p2083 := nat_lit 96809808976379498691360692473363896094635489302285341275220157394320372769957362641 

noncomputable def Ns168p2084 := nat_lit 53407909995589249531620497081411892330183768415771766730465952415785992483998812015967185 

noncomputable def Ns168p2085 := BSN.cos_dyadic_bound_t 8231771 4194304 4 3 8388608 2250000 Ns168p2082 Ns168p426 Ns168p2083 Ns168p2084 Ns168p429 Ns168p2083 3203296 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 8231771) (BSN.cosEvenQ 4194304) 0 3 Ns168p2082 Ns168p426 Ns168p2083 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 8231771) (BSN.cosOddQ 4194304) 0 3 Ns168p2084 Ns168p429 Ns168p2083 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p2086 := @Ns168p2072 802027216 37748736000000 100103 262144 50126701 2359296000000 (@Ns168p2073 349 16777216 Bool.true 3203296 8388608 1 2250000 (@Ns168p2076 Ns168p2077 8231771 4194304 349 16777216 (@Ns168p2078 70368744177664 14505533 4398046511104 Ns168p2074 Ns168p1196 Ns168p2075 Ns168p2077 RS169to186.d39 (@Ns168p2079 0 1 351684554998384 21980284687399 70368744177664 14505533 4398046511104 (@Ns168p2080 147490503823573647360 17582238176295 70368744177664 14505533 4398046511104 (@Ns168p2081 7165501 4398046511104 (Ns168p2062 rfl rfl) (Ns168p2062 rfl rfl) rfl) (Ns168p2062 rfl rfl) rfl rfl) qz375 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8231771 4194304) (BSN.cos_neg_of_bound 8231771 4194304 Bool.true 3203296 8388608 1 2250000 (Ns168p2085 rfl rfl)) rfl rfl) 

noncomputable def Ns168p2087 := @Ns168p2047 8134663346595199177 922337203685477580800000 (Ns168p2048 qz27 (@Enclosure.Real.IsNear.of_eq qz829 (@Inv.inv Real Real.instInv (Real.sqrt qz247)) Bool.false 2879283 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz243 (BSN.t_div_two_pi_nonneg qz242 452691 1000 qz245)) Ns168p2052) rfl) (@Ns168p2053 4398046511104 11242461204837 439804651110400000 (BSN.correction_mk qz244 (BSN.cos_two_pi_p_ne_zero_mk qz242 452691 1000 8 qz245 rfl rfl (@BSN.floor_sqrt_eq_dec qz242 452691 1000 8 qz245 rfl rfl rfl))) (@Ns168p2054 16777216 100103 262144 50126701 2359296000000 1684147186729 4398046511104 11242461204837 439804651110400000 Ns168p2071 (Ns168p2086 rfl) rfl)) 

noncomputable def Ns168p2088 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz242) (hardyZApproximantRS₀ qz242) Bool.false 245503958113535290581 36893488147419103232 1379610492252988799177 922337203685477580800000 (@Eq.refl Real (hardyZApproximantRS₀ qz242)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz242) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz242) qz242 8) (@HMul.hMul Real Real Real qz5 qz824 (Zeta.RiemannSiegel.correction qz244))) Bool.false 245503958113535290581 36893488147419103232 1379610492252988799177 922337203685477580800000 (BSN.hardyZApproximantRS₀_eq qz242 8 (@BSN.floor_sqrt_eq_dec qz242 452691 1000 8 qz245 rfl rfl rfl)) (@Ns168p1984 245503958113535290581 36893488147419103232 1379610492252988799177 922337203685477580800000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz242) qz242 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz242) qz242 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz242) qz242 8)) Bool.false 227694813 33554432 24947 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz242) qz242 8) (Ns168p2046 (Ns168p2045 rfl rfl rfl rfl) rfl rfl)) (Ns168p2087 rfl) rfl rfl)) 

theorem RS169to186.d60 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz242) Bool.false 245503958113535290581 36893488147419103232 1379610492252988799177 922337203685477580800000 := Ns168p2088 

noncomputable def Ns168p2089 := nat_lit 6432173487392806690600517632 

noncomputable abbrev qz966 := (Enclosure.sfrac Bool.false 454159 1000)

noncomputable abbrev qz833 := qz966

noncomputable abbrev qz595 := qz833

noncomputable abbrev qz255 := qz595

noncomputable abbrev qz967 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 454159 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz834 := qz967

noncomputable abbrev qz596 := qz834

noncomputable abbrev qz256 := qz596

noncomputable abbrev qz968 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 454159 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz835 := qz968

noncomputable abbrev qz597 := qz835

noncomputable abbrev qz257 := qz597

noncomputable abbrev qz836 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz256 qz9))

noncomputable def Ns168p2090 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz255) qz255 8) (@HMul.hMul Real Real Real qz5 qz836 (Zeta.RiemannSiegel.correction qz257)) 34778261 67108864 50057 33554432 19368649235776282791 147573952589676412928 1308925416801214079 147573952589676412928000 Ns168p2089 

noncomputable def Ns168p2091 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz255) qz255 Real.sin BSN.quadSignPos 7 8 454159 1000 127 134217728 67108864 2251799813685248 Bool.false 99932830475 1771 279097919 60 47453128 8 

noncomputable def Ns168p2092 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz255) qz255 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 454159 1000 44 88 134217728 67108864 2251799813685248 Bool.false 99932830475 1771 

noncomputable def Ns168p2093 := Ns168p2092 240485871 61 54794152 8 261175631 61 50729528 8 Bool.true 134522948 66650 Bool.true 9528790 Bool.true 129506080 7074237752028440 1 Bool.false 133879621 Bool.false Bool.false 76437370 Bool.false Bool.true 50976221 

noncomputable def Ns168p2094 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz255) qz255 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 454159 1000 73 8 134217728 67108864 2251799813685248 Bool.false 99932830475 1771 

noncomputable def Ns168p2095 := Ns168p2094 186065264 60 67108856 8 216015088 60 60023992 8 Bool.true 145075463 39141 Bool.false 39120110 Bool.false 141004410 7074237752028440 1 Bool.false 38568560 Bool.true Bool.false 66717098 Bool.false Bool.true 134522948 

noncomputable def Ns168p2096 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz255) qz255 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 454159 1000 273 156 134217728 67108864 2251799813685248 Bool.false 99932830475 1771 

noncomputable def Ns168p2097 := Ns168p2096 93032624 60 94906264 8 147453232 60 77490640 16 Bool.true 134217720 1836 Bool.false 124988033 Bool.false 76338678 7074237752028440 1 Bool.false 107690494 Bool.true Bool.false 113087219 Bool.false Bool.true 145075463 

noncomputable def Ns168p2098 := nat_lit 1059277407687923438438187454748063349457064528121589049791 

noncomputable def Ns168p2099 := nat_lit 1422693686398748389042812827373023766996595922436096000 

noncomputable def Ns168p2100 := nat_lit 9274322541723626034831843903520000 

noncomputable def Ns168p2101 := nat_lit 25272116602059717909917197207168438080 

noncomputable def Ns168p2102 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz255 454159 1000 825042589124 16000000 908318 4000 2000 Ns168p2100 Ns168p2101 (@Eq.refl Real qz255) rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns168p2103 := nat_lit 338968770460135500300219985519380271826260648998908495933120 

noncomputable abbrev qz837 := (Real.log (Enclosure.sfrac Bool.false 825042589124 16000000))

noncomputable abbrev qz258 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 454159 4000) qz837) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 908318))))))

noncomputable abbrev qz838 := (Enclosure.sfrac Bool.false 454159 2000)

noncomputable abbrev qz598 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz258 qz838) (@HMul.hMul Real Real Real qz5 qz838 (Real.log Real.pi)))

noncomputable def Ns168p2104 := @Enclosure.Real.IsNear.addLit_ft_p qz598 (Enclosure.sfrac Bool.true Ns168p2100 Ns168p2101) 13412764069941461175639 18014398509481984000 5401138450373799 409600000000000000000 Ns168p2100 Ns168p2101 0 1 Ns168p2103 

noncomputable def Ns168p2105 := nat_lit 900115359833788005997237764096000 

noncomputable abbrev qz599 := (@HSub.hSub Real Real Real qz12 qz258 qz838)

noncomputable abbrev qz600 := (@HMul.hMul Real Real Real qz5 qz838 (Real.log Real.pi))

noncomputable def Ns168p2106 := @Enclosure.Real.IsNear.subLit_ff_p qz599 qz600 18095511294285686820183 18014398509481984000 5135101362577 800000000000000000 17444592804999 67108864000 454159 67108864000 Ns168p2105 13412764069941461175639 18014398509481984000 

noncomputable def Ns168p2107 := nat_lit 36191022588571373640366000 

noncomputable abbrev qz601 := qz838

noncomputable def Ns168p2108 := @Enclosure.Real.IsNear.subLit_ff_p qz258 qz601 22186211900619601005911 18014398509481984000 5135101362577 800000000000000000 454159 2000 0 1 Ns168p2107 18095511294285686820183 18014398509481984000 5135101362577 800000000000000000 

noncomputable def Ns168p2109 := nat_lit 49958907824196649461720782044741500928 

noncomputable def Ns168p2110 := nat_lit 26235144756741606209486848 

noncomputable def Ns168p2111 := nat_lit 207973572624665683199690194527594740856878809447753709701533065682512133340720082482087137145730438571913389671742309814763520 

noncomputable def Ns168p2112 := nat_lit 3550544147471439469191024545983692754379718721913860855276412237323483867843116295783592985416821016269258382775075292053504 

noncomputable def Ns168p2113 := nat_lit 5722086738950500790947465715751606242462353729359577405217987868784896649068788301947224175466997573862172453183160320 

noncomputable def Ns168p2114 := BSN.log_dyadic_bound 300754589124 1349330589124 6 5 Ns168p2111 67108864 18000000 Ns168p2112 Ns168p2113 30426746 1650085178248 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 300754589124) (BSN.artanhQ 1349330589124) 0 5 Ns168p2112 Ns168p2111 Ns168p2113 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns168p2115 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 454159 4000) qz837 454159 4000 0 1 48866765120516729 4503599627370496 100000027 1800000000000000 22193281180368757125911 18014398509481984000 45415912262293 7200000000000000000 (Enclosure.Real.IsNear.const Bool.false 454159 4000) (BSN.isNear_log_sfrac 825042589124 16000000 48866765120516729 4503599627370496 100000027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 825042589124) qz353)) Bool.false Ns168p2110 Ns168p89 1000000270000000 18000000000000000000000 48866765120516729 4503599627370496 100000027 1800000000000000 (BSN.log_rat_reduce_isNear 825042589124 16000000 15 1650085178248 1048576000000 30426746 67108864 24973259072661432 36028797018963968 18000000 1000000000000000 rfl rfl rfl rfl (Ns168p2114 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p2116 := BSN.arctan_dyadic_bound_f 1000 908318 1 0 8388608 2250000 0 1 1 0 1 1 9235 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 908318) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 908318) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz839 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 908318)))

noncomputable def Ns168p2117 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz839 884279719003555 562949953421312 1 2000000000000000 9235 8388608 1 2250000 7412677082251127685120 883659968644515 562949953421312 8000000009 18000000000000000 qz16 (Ns168p2116 rfl) rfl rfl 

noncomputable def Ns168p2118 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 454159 4000) qz837) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz839)) 22193281180368757125911 18014398509481984000 45415912262293 7200000000000000000 883659968644515 2251799813685248 8000000009 72000000000000000 Ns168p2109 22186211900619601005911 18014398509481984000 5135101362577 800000000000000000 (Ns168p2115 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz839) 1 4 0 1 883659968644515 562949953421312 8000000009 18000000000000000 883659968644515 2251799813685248 8000000009 72000000000000000 qz356 Ns168p2117 rfl) 

noncomputable def Ns168p2119 := @Ns168p2104 Ns168p2098 Ns168p2099 5401138450373799 409600000000000000000 (@Ns168p2106 5401138450373799 409600000000000000000 (Ns168p2108 (Ns168p2118 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 454159 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz601 (Real.log Real.pi) 454159 2000 0 1 38410761 33554432 1 33554432 17444592804999 67108864000 454159 67108864000 (Enclosure.Real.IsNear.const Bool.false 454159 2000) RS169to186.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns168p2100 Ns168p2101) 

noncomputable def Ns168p2120 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz255) Bool.false Ns168p2098 Ns168p2099 5401138450373799 409600000000000000000 12491603809 16777216 111 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz255) (@HAdd.hAdd Real Real Real qz357 qz598 (Enclosure.sfrac Bool.true Ns168p2100 Ns168p2101)) Bool.false Ns168p2098 Ns168p2099 5401138450373799 409600000000000000000 Ns168p2102 (Ns168p2119 rfl rfl)) 

noncomputable def Ns168p2121 := nat_lit 3798312273124512925483008 

noncomputable def Ns168p2122 := nat_lit 857463073390863937500826548120023451419154255766386188076804060700206756791037509023979467088142452898342333516784728880538215174373376 

noncomputable def Ns168p2123 := nat_lit 611688611895388051221923761944960104481303093462814793506316398583448333498430349048312270210007538462962761564511019586474213376 

noncomputable def Ns168p2124 := nat_lit 4281985832600757662060411377129428832349782403599607400092094235768950381980152096903158874139945650538676502772321928123774311476494336 

noncomputable def Ns168p2125 := BSN.sin_dyadic_bound_f 53977263876 34359738368 4 3 16777216 4504395 Ns168p2122 Ns168p103 Ns168p2123 Ns168p2124 Ns168p106 Ns168p2123 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53977263876) qz358 0 3 Ns168p2122 Ns168p103 Ns168p2123 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53977263876) qz359 0 3 Ns168p2124 Ns168p106 Ns168p2123 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p2126 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz255) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12491603809) qz370) Bool.false 12491603809 16777216 111 8388608 Bool.true 16777215 16777216 1 2250000 (Ns168p2120 rfl) (Enclosure.sfrac_false_div 12491603809 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12491603809) qz370) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns168p2121) qz385) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 118 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q1 12491603809 16777216 226375608064910080 72057594037927936 118 Ns168p2121 Ns168p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns168p2121 Ns168p89 53977263876 34359738368 4504395 4500000 (Ns168p2125 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p2127 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz255) Bool.false Ns168p2098 Ns168p2099 5401138450373799 409600000000000000000 99932830475 134217728 1771 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz255) (@HAdd.hAdd Real Real Real qz357 qz598 (Enclosure.sfrac Bool.true Ns168p2100 Ns168p2101)) Bool.false Ns168p2098 Ns168p2099 5401138450373799 409600000000000000000 Ns168p2102 (Ns168p2119 rfl rfl)) 

noncomputable def Ns168p2128 := Ns168p2097 39141 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 273 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 107690494 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 156 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 113087219 134217728) (@Eq.refl Real qz255) rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz255) qz255 1) Bool.true 16777215 16777216 16133663 1179648000000 134217720 134217728 1836 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz255) qz255 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz255)) Bool.true 16777215 16777216 16133663 1179648000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz255) qz255) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz255)) Bool.true 16777215 16777216 258138608 18874368000000 16777215 16777216 16133663 1179648000000 (Ns168p2126 rfl rfl) rfl)) rfl) (Ns168p2127 rfl) RS169to186.d7 

noncomputable def Ns168p2129 := nat_lit 239553787620077192617356242846488501189922928063222910068830683812865 

noncomputable def Ns168p2130 := nat_lit 59559009586665378621248530173995846125675629945673866039890826241 

noncomputable def Ns168p2131 := nat_lit 627306348227538046241974805072902462222737527240909863920968158172161 

noncomputable def Ns168p2132 := BSN.sin_dyadic_bound_f 124988033 134217728 3 2 134217728 67108864 Ns168p2129 Ns168p112 Ns168p2130 Ns168p2131 Ns168p115 Ns168p2130 107690494 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 124988033) qz361 0 2 Ns168p2129 Ns168p112 Ns168p2130 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 124988033) qz362 0 2 Ns168p2131 Ns168p115 Ns168p2130 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p2133 := nat_lit 18516308354252603464002564829086227016289706814142294843185350697216 

noncomputable def Ns168p2134 := nat_lit 1153339265986793131566099996370453902037380636292693190711828736 

noncomputable def Ns168p2135 := nat_lit 55546618384225836805744562287265940141065045681154299143174628434176 

noncomputable def Ns168p2136 := BSN.cos_dyadic_bound_f 76338678 134217728 3 2 134217728 67108864 Ns168p2133 Ns168p124 Ns168p2134 Ns168p2135 Ns168p127 Ns168p2134 113087219 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 76338678) qz363 0 2 Ns168p2133 Ns168p124 Ns168p2134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 76338678) qz364 0 2 Ns168p2135 Ns168p127 Ns168p2134 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p2137 := nat_lit 2342072146314937709715026410000 

noncomputable def Ns168p2138 := BSN.sin_dyadic_bound_f 39120110 134217728 2 1 134217728 67108864 Ns168p2137 Ns168p394 Ns168p2137 Ns168p2137 Ns168p395 Ns168p2137 38568560 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 39120110) qz361 0 1 Ns168p2137 Ns168p394 Ns168p2137 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 39120110) qz362 0 1 Ns168p2137 Ns168p395 Ns168p2137 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p2139 := nat_lit 831477271241628160034883498867915815497111426082620016846834690408459941133619536577700783364057664000000 

noncomputable def Ns168p2140 := nat_lit 61772097513348401594819253733196123587500194216534128006551891095610463407263290462881000000000000 

noncomputable def Ns168p2141 := nat_lit 5041858576470899163258376401991502698593251008118657074838360573999269322830809595453228052318438361600000 

noncomputable def Ns168p2142 := BSN.cos_dyadic_bound_f 141004410 134217728 4 3 134217728 67108864 Ns168p2139 Ns168p118 Ns168p2140 Ns168p2141 Ns168p121 Ns168p2140 66717098 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 141004410) qz363 0 3 Ns168p2139 Ns168p118 Ns168p2140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 141004410) qz364 0 3 Ns168p2141 Ns168p121 Ns168p2140 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p2143 := Ns168p2095 66650 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 73 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 38568560 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 8 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66717098 134217728) (@Eq.refl Real qz255) rfl rfl (Ns168p2128 RS169to186.d9 RS169to186.d11 RS169to186.d13 RS169to186.d17 (Ns168p2132 rfl rfl) (Ns168p2136 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns168p2127 rfl) RS169to186.d19 RS169to186.d21 RS169to186.d23 RS169to186.d25 RS169to186.d17 (Ns168p2138 rfl rfl) (Ns168p2142 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns168p2144 := nat_lit 8244247542391068378268810000 

noncomputable def Ns168p2145 := BSN.cos_dyadic_bound_f 9528790 134217728 2 1 134217728 67108864 Ns168p2144 Ns168p130 Ns168p2144 Ns168p2144 Ns168p131 Ns168p2144 133879621 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 9528790) qz363 0 1 Ns168p2144 Ns168p130 Ns168p2144 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 9528790) qz364 0 1 Ns168p2144 Ns168p131 Ns168p2144 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p2146 := nat_lit 153438189003908136719395180626736014400187001539808700878605516800000 

noncomputable def Ns168p2147 := nat_lit 79126373889405827698315279906528438608494181637644982681600000000 

noncomputable def Ns168p2148 := nat_lit 460156314263945598502788911320394986323344016256150812670453350400000 

noncomputable def Ns168p2149 := BSN.cos_dyadic_bound_f 129506080 134217728 3 2 134217728 67108864 Ns168p2146 Ns168p124 Ns168p2147 Ns168p2148 Ns168p127 Ns168p2147 76437370 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 129506080) qz363 0 2 Ns168p2146 Ns168p124 Ns168p2147 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 129506080) qz364 0 2 Ns168p2148 Ns168p127 Ns168p2147 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p2150 := Ns168p2093 89843 BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133879621 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 88 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 76437370 134217728) (@Eq.refl Real qz255) rfl rfl (Ns168p2143 rfl rfl) (Ns168p2127 rfl) RS169to186.d27 RS169to186.d29 RS169to186.d31 RS169to186.d33 RS169to186.d17 (Ns168p2145 rfl rfl) (Ns168p2149 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns168p2151 := nat_lit 4778573960295225283730712890625 

noncomputable def Ns168p2152 := BSN.sin_dyadic_bound_f 46754625 134217728 2 1 134217728 67108864 Ns168p2151 Ns168p394 Ns168p2151 Ns168p2151 Ns168p395 Ns168p2151 45814755 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 46754625) qz361 0 1 Ns168p2151 Ns168p394 Ns168p2151 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 46754625) qz362 0 1 Ns168p2151 Ns168p395 Ns168p2151 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p2153 := Ns168p2091 Bool.true 50976221 89843 Bool.true 46754625 7074237752028440 1 Bool.false 45814755 Bool.false Bool.true 34778261 100114 BSN.abs_quadSignPos qz365 (BSN.sfrac_eq_quadSignPos_mul Bool.false 45814755 134217728) (@Eq.refl Real qz255) rfl (Ns168p2150 rfl) (Ns168p2127 rfl) RS169to186.d35 RS169to186.d37 RS169to186.d17 (Ns168p2152 rfl rfl) rfl 

noncomputable def Ns168p2154 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz255) qz255 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz255) qz255 8) 34778261 134217728 100114 134217728 34778261 134217728 100114 134217728 9335718350422016 34778261 67108864 50057 33554432 (Ns168p2153 rfl rfl rfl rfl) 

noncomputable def Ns168p2155 := @Enclosure.Real.IsNear.mulLit_ff qz836 (Zeta.RiemannSiegel.correction qz257) 1438477 4194304 1 8388608 13464691639683 35184372088832 6789433990007 263882790666240000 19368649235776282791 147573952589676412928 

noncomputable abbrev qz840 := (@HPow.hPow Real Real Real qz7 qz256 qz9)

noncomputable def Ns168p2156 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz840 1 1 0 1 1438477 4194304 1 8388608 1438477 4194304 1 8388608 

noncomputable def Ns168p2157 := @Enclosure.Real.IsNear.sqrt_image qz256 1212684916143 16777216000 454159 16777216000 71318772 71318800 8388608 (@Enclosure.Real.IsNear.of_eq qz256 (@HMul.hMul Real Real Real qz5 qz255 qz3) Bool.false 1212684916143 16777216000 454159 16777216000 (BSN.t_div_two_pi_mk qz255 454159 1000 (@Eq.refl Real qz255)) (@Enclosure.Real.IsNear.mulLit_ff qz255 qz3 454159 1000 0 1 2670177 16777216 1 16777216 1212684916143 16777216000 454159 16777216000 (Enclosure.Real.IsNear.const Bool.false 454159 1000) RS169to186.d40 rfl)) 

noncomputable abbrev qz969 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 454159 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz841 := qz969

noncomputable abbrev qz602 := qz841

noncomputable abbrev qz259 := qz602

noncomputable def Ns168p2158 := @Enclosure.Real.IsNear.sqrt_image qz259 35659393 4194304 7 4194304 24459460 24459466 8388608 (@Enclosure.Real.IsNear.recentre' qz259 Bool.false 142637572 16777216 28 16777216 35659393 4194304 7 4194304 (Ns168p2157 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns168p2159 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz259) 24459463 8388608 3 8388608 2876953 2876955 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz259) Bool.false 48918926 16777216 6 16777216 24459463 8388608 3 8388608 (Ns168p2158 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns168p2160 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz259)) Bool.false 5753908 16777216 2 16777216 1438477 4194304 1 8388608 (Ns168p2159 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz260 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz597))

noncomputable abbrev qz842 := (@HMul.hMul Real Real Real qz890 qz968 qz968)

noncomputable abbrev qz603 := (@HSub.hSub Real Real Real qz633 (@HSub.hSub Real Real Real qz633 qz842 qz835) qz641)

noncomputable abbrev qz261 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz603))

noncomputable def Ns168p2161 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz257) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz260) qz261) Bool.false 13464691639683 

noncomputable def Ns168p2162 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz260) qz261 4194591 4194304 93 

noncomputable abbrev qz843 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz260))

noncomputable def Ns168p2163 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz260) (@Neg.neg Real Real.instNeg qz843) Bool.true 4194591 4194304 93 8388608 (BSN.inv_eq_neg_inv_neg qz260) 

noncomputable def Ns168p2164 := @Enclosure.Real.IsNear.recentre' qz843 Bool.false 16778364 16777216 186 16777216 4194591 4194304 

noncomputable def Ns168p2165 := @Enclosure.Real.IsNear.recentre' qz260 Bool.true 16776068 16777216 415027216 37748736000000 4194017 4194304 25939201 2359296000000 

noncomputable abbrev qz262 := (@HMul.hMul Real Real Real qz342 qz340 qz597)

noncomputable def Ns168p2166 := @Enclosure.Real.IsNear.cos_image qz262 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3306465) qz671) Bool.false 3306465 1048576 177 16777216 Bool.true 16776068 16777216 1 

noncomputable def Ns168p2167 := nat_lit 188902527881389795494893681 

noncomputable def Ns168p2168 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz257 884279719003555 140737488355328 1 500000000000000 2104961 4194304 7 4194304 1861374321593442136355 590295810358705651712 Ns168p2167 

noncomputable def Ns168p2169 := @Enclosure.Real.IsNear.subLit_ff_p qz259 qz1 35659393 4194304 7 4194304 8 1 0 1 2104961 2104961 4194304 7 

noncomputable def Ns168p2170 := @Ns168p2169 4194304 (@Enclosure.Real.IsNear.recentre' qz259 Bool.false 142637572 16777216 28 16777216 35659393 4194304 7 4194304 (Ns168p2157 rfl rfl rfl rfl rfl rfl) rfl) qz371 

noncomputable def Ns168p2171 := @Enclosure.Real.IsNear.recentre' qz262 Bool.false 1861374321593442136355 590295810358705651712 Ns168p2167 Ns168p1070 3306465 1048576 177 16777216 (@Ns168p2168 Ns168p1070 RS169to186.d39 (Ns168p2170 rfl rfl) rfl) 

noncomputable def Ns168p2172 := BSN.cos_dyadic_bound_f 401943483 34359738368 1 0 16777216 4504395 0 1 1 0 1 1 16776068 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 401943483) qz682 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 401943483) qz683 0 0 rfl) rfl rfl 

noncomputable def Ns168p2173 := @Ns168p2166 2250000 (Ns168p2171 rfl) (Enclosure.sfrac_false_div 3306465 1048576) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3306465) qz671) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1767766136692481720320) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false 16776068 16777216 0 1000000000000000 4500000 2250000 (BSN.sin_reduce_arg_pos_rat_q2 3306465 1048576 226375608064910080 72057594037927936 0 1767766136692481720320 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16776068 16777216 1767766136692481720320 151115727451828646838272 401943483 34359738368 4504395 4500000 (Ns168p2172 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns168p2174 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz260) 4194017 4194304 25939201 2359296000000 8389089 8389275 8388608 (@Enclosure.Real.IsNear.neg qz260 Bool.true 4194017 4194304 25939201 2359296000000 (Ns168p2165 (Ns168p2173 rfl rfl) rfl)) 

noncomputable def Ns168p2175 := Ns168p2163 (@Enclosure.Real.IsNear.neg qz843 Bool.false 4194591 4194304 93 8388608 (@Ns168p2164 93 8388608 (Ns168p2174 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns168p2176 := @Enclosure.Real.IsNear.recentre' qz261 Bool.true 3210013 8388608 

noncomputable abbrev qz263 := (@HMul.hMul Real Real Real qz342 qz340 qz603)

noncomputable def Ns168p2177 := @Enclosure.Real.IsNear.cos_image qz263 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32941621)) qz370) Bool.true 32941621 16777216 

noncomputable def Ns168p2178 := nat_lit 4861325242451909812279108445 

noncomputable def Ns168p2179 := nat_lit 317516171699891679577034128939877 

noncomputable def Ns168p2180 := @Enclosure.Real.IsNear.recentre' qz263 Bool.true Ns168p2178 Ns168p1749 Ns168p2179 

noncomputable abbrev qz264 := qz603

noncomputable def Ns168p2181 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz264 884279719003555 140737488355328 1 500000000000000 5497497158399 

noncomputable abbrev qz604 := (@HSub.hSub Real Real Real qz633 qz842 qz835)

noncomputable abbrev qz265 := qz604

noncomputable def Ns168p2182 := @Enclosure.Real.IsNear.subLit_tf qz265 qz25 4397985530623 17592186044416 58829631 17592186044416 1 16 

noncomputable abbrev qz605 := qz842

noncomputable abbrev qz266 := qz605

noncomputable def Ns168p2183 := @Enclosure.Real.IsNear.subLit_ff_n qz266 qz257 4430860811521 17592186044416 29469503 17592186044416 2104961 4194304 7 4194304 

noncomputable def Ns168p2184 := @Enclosure.Real.IsNear.mulLit_ff qz257 qz257 2104961 4194304 7 4194304 2104961 4194304 7 4194304 4430860811521 17592186044416 

noncomputable def Ns168p2185 := nat_lit 148831473758586876779423415065210873241751752253219570951609081585878498308507679567259678008721 

noncomputable def Ns168p2186 := nat_lit 1632824825755218606920095423316081764547881942203395535433843624488962750558746854727869841 

noncomputable def Ns168p2187 := nat_lit 897624117958881591990262969523755521707421281568642534640038840395404717825599980393329986889105 

noncomputable def Ns168p2188 := BSN.cos_dyadic_bound_t 32941621 16777216 4 3 8388608 2250000 Ns168p2185 Ns168p169 Ns168p2186 Ns168p2187 Ns168p172 Ns168p2186 3210013 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32941621) qz642 0 3 Ns168p2185 Ns168p169 Ns168p2186 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32941621) (BSN.cosOddQ 16777216) 0 3 Ns168p2187 Ns168p172 Ns168p2186 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns168p2189 := @Ns168p2176 811027216 37748736000000 3210013 8388608 50689201 2359296000000 (@Ns168p2177 353 16777216 Bool.true 3210013 8388608 1 2250000 (@Ns168p2180 Ns168p1856 32941621 16777216 353 16777216 (@Ns168p2181 17592186044416 58829631 17592186044416 Ns168p2178 Ns168p1749 Ns168p2179 Ns168p1856 RS169to186.d39 (@Ns168p2182 0 1 87959954534384 5497497158399 17592186044416 58829631 17592186044416 (@Ns168p2183 18446488303034171392 4397985530623 17592186044416 58829631 17592186044416 (@Ns168p2184 29469503 17592186044416 (Ns168p2170 rfl rfl) (Ns168p2170 rfl rfl) rfl) (Ns168p2170 rfl rfl) rfl rfl) qz375 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32941621 16777216) (BSN.cos_neg_of_bound 32941621 16777216 Bool.true 3210013 8388608 1 2250000 (Ns168p2188 rfl rfl)) rfl rfl) 

noncomputable def Ns168p2190 := @Ns168p2155 1308925416801214079 147573952589676412928000 (Ns168p2156 qz27 (@Enclosure.Real.IsNear.of_eq qz840 (@Inv.inv Real Real.instInv (Real.sqrt qz259)) Bool.false 1438477 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz256 (BSN.t_div_two_pi_nonneg qz255 454159 1000 (@Eq.refl Real qz255))) Ns168p2160) rfl) (@Ns168p2161 35184372088832 6789433990007 263882790666240000 (BSN.correction_mk qz257 (BSN.cos_two_pi_p_ne_zero_mk qz255 454159 1000 8 (@Eq.refl Real qz255) rfl rfl (@BSN.floor_sqrt_eq_dec qz255 454159 1000 8 (@Eq.refl Real qz255) rfl rfl rfl))) (@Ns168p2162 8388608 3210013 8388608 50689201 2359296000000 13464691639683 35184372088832 6789433990007 263882790666240000 Ns168p2175 (Ns168p2189 rfl) rfl)) 

noncomputable def Ns168p2191 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz255) (hardyZApproximantRS₀ qz255) Bool.true 95846853962433437863 147573952589676412928 221461939623134142079 147573952589676412928000 (@Eq.refl Real (hardyZApproximantRS₀ qz255)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz255) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz255) qz255 8) (@HMul.hMul Real Real Real qz5 qz836 (Zeta.RiemannSiegel.correction qz257))) Bool.true 95846853962433437863 147573952589676412928 221461939623134142079 147573952589676412928000 (BSN.hardyZApproximantRS₀_eq qz255 8 (@BSN.floor_sqrt_eq_dec qz255 454159 1000 8 (@Eq.refl Real qz255) rfl rfl rfl)) (@Ns168p2090 95846853962433437863 147573952589676412928 221461939623134142079 147573952589676412928000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz255) qz255 8) (@HAdd.hAdd Real Real Real qz357 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz255) qz255 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz255) qz255 8)) Bool.true 34778261 67108864 50057 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz255) qz255 8) (Ns168p2154 (Ns168p2153 rfl rfl rfl rfl) rfl rfl)) (Ns168p2190 rfl) rfl rfl)) 

theorem RS169to186.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz255) Bool.true 95846853962433437863 147573952589676412928 221461939623134142079 147573952589676412928000 := Ns168p2191 

noncomputable def RS169to186.d62 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz267 := (RS169to186.d3 qz341 qz376 (@Enclosure.dec_le_dec qz341 qz376 427552 1000 429040 1000 (@Eq.refl Real qz341) qz379 rfl rfl rfl))

noncomputable abbrev qz844 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz267)

noncomputable def Ns168p2192 := @Enclosure.Real.IsNear.of_eq qz844 (hardyZApproximantRS₀ qz4) Bool.true 541630627858275095367 590295810358705651712 9750986410832685573409 Ns168p67 

noncomputable abbrev qz268 := (@Enclosure.dec_le_dec qz341 qz376 427552 1000 429040 1000 (@Eq.refl Real qz341) qz379 rfl rfl rfl)

noncomputable def Ns168p2193 := @Enclosure.Real.IsNear.neg_val qz844 541630627858275095367 590295810358705651712 9750986410832685573409 Ns168p67 (Ns168p2192 (RS169to186.d4 qz4 qz28 qz268) RS169to186.d41) rfl 

noncomputable abbrev qz845 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz267)

noncomputable def Ns168p2194 := @Enclosure.Real.IsNear.of_eq qz845 (hardyZApproximantRS₀ qz28) Bool.false 1917233629809203895193 590295810358705651712 24850208172787053724639 Ns168p195 

noncomputable def Ns168p2195 := @Enclosure.Real.IsNear.pos_val qz845 1917233629809203895193 590295810358705651712 24850208172787053724639 Ns168p195 (Ns168p2194 (RS169to186.d42 qz4 qz28 qz268) RS169to186.d43) rfl 

noncomputable def Ns168p2196 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz844 qz4 qz4 427552 1000 427552 1000 

noncomputable def Ns168p2197 := @Enclosure.norm_gt_of_isNear qz844 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 541630627858275095367 590295810358705651712 9750986410832685573409 

noncomputable def Ns168p2198 := @Ns168p2197 Ns168p67 46626811 536870912 1421 2684354560 (Ns168p2192 (RS169to186.d4 qz4 qz28 qz268) RS169to186.d41) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2199 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz845 qz4 qz28 427552 1000 429040 1000 

noncomputable def Ns168p2200 := @Enclosure.norm_gt_of_isNear qz845 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1917233629809203895193 590295810358705651712 24850208172787053724639 

noncomputable def Ns168p2201 := @Ns168p2200 Ns168p195 46626811 536870912 1421 2684354560 (Ns168p2194 (RS169to186.d42 qz4 qz28 qz268) RS169to186.d43) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2202 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz267 (@BSN.thirtyTwoPi_le_dec qz4 427552 1000 qz11 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz844 qz845 (Ns168p2193 rfl rfl) (Ns168p2195 rfl rfl)) (Ns168p2196 qz11 qz11 rfl rfl rfl rfl (Ns168p2198 rfl)) (Ns168p2199 qz11 qz31 rfl rfl rfl rfl (Ns168p2201 rfl)) 

noncomputable abbrev qz269 := (RS169to186.d3 qz376 qz394 (@Enclosure.dec_le_dec qz376 qz394 429040 1000 430527 1000 qz379 qz397 rfl rfl rfl))

noncomputable abbrev qz846 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz269)

noncomputable def Ns168p2203 := @Enclosure.Real.IsNear.of_eq qz846 (hardyZApproximantRS₀ qz28) Bool.false 1917233629809203895193 590295810358705651712 24850208172787053724639 Ns168p195 

noncomputable abbrev qz270 := (@Enclosure.dec_le_dec qz376 qz394 429040 1000 430527 1000 qz379 qz397 rfl rfl rfl)

noncomputable def Ns168p2204 := @Enclosure.Real.IsNear.pos_val qz846 1917233629809203895193 590295810358705651712 24850208172787053724639 Ns168p195 (Ns168p2203 (RS169to186.d4 qz28 qz47 qz270) RS169to186.d43) rfl 

noncomputable abbrev qz847 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz269)

noncomputable def Ns168p2205 := @Enclosure.Real.IsNear.of_eq qz847 (hardyZApproximantRS₀ qz47) Bool.true 121386930367574799209 295147905179352825856 241922172363345289857067 Ns168p339 

noncomputable def Ns168p2206 := @Enclosure.Real.IsNear.neg_val qz847 121386930367574799209 295147905179352825856 241922172363345289857067 Ns168p339 (Ns168p2205 (RS169to186.d42 qz28 qz47 qz270) RS169to186.d45) rfl 

noncomputable def Ns168p2207 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz846 qz4 qz28 427552 1000 429040 1000 

noncomputable def Ns168p2208 := @Enclosure.norm_gt_of_isNear qz846 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1917233629809203895193 590295810358705651712 24850208172787053724639 

noncomputable def Ns168p2209 := @Ns168p2208 Ns168p195 46626811 536870912 1421 2684354560 (Ns168p2203 (RS169to186.d4 qz28 qz47 qz270) RS169to186.d43) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2210 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz847 qz4 qz47 427552 1000 430527 1000 

noncomputable def Ns168p2211 := @Enclosure.norm_gt_of_isNear qz847 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 121386930367574799209 295147905179352825856 241922172363345289857067 

noncomputable def Ns168p2212 := @Ns168p2211 Ns168p339 46626811 536870912 1421 2684354560 (Ns168p2205 (RS169to186.d42 qz28 qz47 qz270) RS169to186.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2213 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz269 (@BSN.thirtyTwoPi_le_dec qz28 429040 1000 qz31 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz846 qz847 (Ns168p2204 rfl rfl) (Ns168p2206 rfl rfl)) (Ns168p2207 qz11 qz31 rfl rfl rfl rfl (Ns168p2209 rfl)) (Ns168p2210 qz11 qz50 rfl rfl rfl rfl (Ns168p2212 rfl)) 

noncomputable abbrev qz271 := (RS169to186.d3 qz394 qz408 (@Enclosure.dec_le_dec qz394 qz408 430527 1000 432013 1000 qz397 qz411 rfl rfl rfl))

noncomputable abbrev qz848 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz271)

noncomputable def Ns168p2214 := @Enclosure.Real.IsNear.of_eq qz848 (hardyZApproximantRS₀ qz47) Bool.true 121386930367574799209 295147905179352825856 241922172363345289857067 Ns168p339 

noncomputable abbrev qz272 := (@Enclosure.dec_le_dec qz394 qz408 430527 1000 432013 1000 qz397 qz411 rfl rfl rfl)

noncomputable def Ns168p2215 := @Enclosure.Real.IsNear.neg_val qz848 121386930367574799209 295147905179352825856 241922172363345289857067 Ns168p339 (Ns168p2214 (RS169to186.d4 qz47 qz60 qz272) RS169to186.d45) rfl 

noncomputable abbrev qz849 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz271)

noncomputable def Ns168p2216 := @Enclosure.Real.IsNear.of_eq qz849 (hardyZApproximantRS₀ qz60) Bool.false 142255742048076756771 590295810358705651712 120179677852453403363011 Ns168p449 

noncomputable def Ns168p2217 := @Enclosure.Real.IsNear.pos_val qz849 142255742048076756771 590295810358705651712 120179677852453403363011 Ns168p449 (Ns168p2216 (RS169to186.d42 qz47 qz60 qz272) RS169to186.d46) rfl 

noncomputable def Ns168p2218 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz848 qz4 qz47 427552 1000 430527 1000 

noncomputable def Ns168p2219 := @Enclosure.norm_gt_of_isNear qz848 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 121386930367574799209 295147905179352825856 241922172363345289857067 

noncomputable def Ns168p2220 := @Ns168p2219 Ns168p339 46626811 536870912 1421 2684354560 (Ns168p2214 (RS169to186.d4 qz47 qz60 qz272) RS169to186.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2221 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz849 qz4 qz60 427552 1000 432013 1000 

noncomputable def Ns168p2222 := @Enclosure.norm_gt_of_isNear qz849 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 142255742048076756771 590295810358705651712 120179677852453403363011 

noncomputable def Ns168p2223 := @Ns168p2222 Ns168p449 46626811 536870912 1421 2684354560 (Ns168p2216 (RS169to186.d42 qz47 qz60 qz272) RS169to186.d46) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2224 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz271 (@BSN.thirtyTwoPi_le_dec qz47 430527 1000 qz50 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz848 qz849 (Ns168p2215 rfl rfl) (Ns168p2217 rfl rfl)) (Ns168p2218 qz11 qz50 rfl rfl rfl rfl (Ns168p2220 rfl)) (Ns168p2221 qz11 qz63 rfl rfl rfl rfl (Ns168p2223 rfl)) 

noncomputable abbrev qz273 := (RS169to186.d3 qz408 qz421 (@Enclosure.dec_le_dec qz408 qz421 432013 1000 433498 1000 qz411 qz424 rfl rfl rfl))

noncomputable abbrev qz850 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz273)

noncomputable def Ns168p2225 := @Enclosure.Real.IsNear.of_eq qz850 (hardyZApproximantRS₀ qz60) Bool.false 142255742048076756771 590295810358705651712 120179677852453403363011 Ns168p449 

noncomputable abbrev qz274 := (@Enclosure.dec_le_dec qz408 qz421 432013 1000 433498 1000 qz411 qz424 rfl rfl rfl)

noncomputable def Ns168p2226 := @Enclosure.Real.IsNear.pos_val qz850 142255742048076756771 590295810358705651712 120179677852453403363011 Ns168p449 (Ns168p2225 (RS169to186.d4 qz60 qz73 qz274) RS169to186.d46) rfl 

noncomputable abbrev qz851 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz273)

noncomputable def Ns168p2227 := @Enclosure.Real.IsNear.of_eq qz851 (hardyZApproximantRS₀ qz73) Bool.true 1212165999055466976491 590295810358705651712 3750516530335428489061 Ns168p558 

noncomputable def Ns168p2228 := @Enclosure.Real.IsNear.neg_val qz851 1212165999055466976491 590295810358705651712 3750516530335428489061 Ns168p558 (Ns168p2227 (RS169to186.d42 qz60 qz73 qz274) RS169to186.d47) rfl 

noncomputable def Ns168p2229 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz850 qz4 qz60 427552 1000 432013 1000 

noncomputable def Ns168p2230 := @Enclosure.norm_gt_of_isNear qz850 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 142255742048076756771 590295810358705651712 120179677852453403363011 

noncomputable def Ns168p2231 := @Ns168p2230 Ns168p449 46626811 536870912 1421 2684354560 (Ns168p2225 (RS169to186.d4 qz60 qz73 qz274) RS169to186.d46) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2232 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz851 qz4 qz73 427552 1000 433498 1000 

noncomputable def Ns168p2233 := @Enclosure.norm_gt_of_isNear qz851 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1212165999055466976491 590295810358705651712 3750516530335428489061 

noncomputable def Ns168p2234 := @Ns168p2233 Ns168p558 46626811 536870912 1421 2684354560 (Ns168p2227 (RS169to186.d42 qz60 qz73 qz274) RS169to186.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2235 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz273 (@BSN.thirtyTwoPi_le_dec qz60 432013 1000 qz63 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz850 qz851 (Ns168p2226 rfl rfl) (Ns168p2228 rfl rfl)) (Ns168p2229 qz11 qz63 rfl rfl rfl rfl (Ns168p2231 rfl)) (Ns168p2232 qz11 qz76 rfl rfl rfl rfl (Ns168p2234 rfl)) 

noncomputable abbrev qz275 := (RS169to186.d3 qz421 qz434 (@Enclosure.dec_le_dec qz421 qz434 433498 1000 434981 1000 qz424 qz437 rfl rfl rfl))

noncomputable abbrev qz852 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz275)

noncomputable def Ns168p2236 := @Enclosure.Real.IsNear.of_eq qz852 (hardyZApproximantRS₀ qz73) Bool.true 1212165999055466976491 590295810358705651712 3750516530335428489061 Ns168p558 

noncomputable abbrev qz276 := (@Enclosure.dec_le_dec qz421 qz434 433498 1000 434981 1000 qz424 qz437 rfl rfl rfl)

noncomputable def Ns168p2237 := @Enclosure.Real.IsNear.neg_val qz852 1212165999055466976491 590295810358705651712 3750516530335428489061 Ns168p558 (Ns168p2236 (RS169to186.d4 qz73 qz86 qz276) RS169to186.d47) rfl 

noncomputable abbrev qz853 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz275)

noncomputable def Ns168p2238 := @Enclosure.Real.IsNear.of_eq qz853 (hardyZApproximantRS₀ qz86) Bool.false 3448102409308625414321 590295810358705651712 120089048498478263638463 Ns168p449 

noncomputable def Ns168p2239 := @Enclosure.Real.IsNear.pos_val qz853 3448102409308625414321 590295810358705651712 120089048498478263638463 Ns168p449 (Ns168p2238 (RS169to186.d42 qz73 qz86 qz276) RS169to186.d48) rfl 

noncomputable def Ns168p2240 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz852 qz4 qz73 427552 1000 433498 1000 

noncomputable def Ns168p2241 := @Enclosure.norm_gt_of_isNear qz852 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1212165999055466976491 590295810358705651712 3750516530335428489061 

noncomputable def Ns168p2242 := @Ns168p2241 Ns168p558 46626811 536870912 1421 2684354560 (Ns168p2236 (RS169to186.d4 qz73 qz86 qz276) RS169to186.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2243 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz853 qz4 qz86 427552 1000 434981 1000 

noncomputable def Ns168p2244 := @Enclosure.norm_gt_of_isNear qz853 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 3448102409308625414321 590295810358705651712 120089048498478263638463 

noncomputable def Ns168p2245 := @Ns168p2244 Ns168p449 46626811 536870912 1421 2684354560 (Ns168p2238 (RS169to186.d42 qz73 qz86 qz276) RS169to186.d48) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2246 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz275 (@BSN.thirtyTwoPi_le_dec qz73 433498 1000 qz76 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz852 qz853 (Ns168p2237 rfl rfl) (Ns168p2239 rfl rfl)) (Ns168p2240 qz11 qz76 rfl rfl rfl rfl (Ns168p2242 rfl)) (Ns168p2243 qz11 qz89 rfl rfl rfl rfl (Ns168p2245 rfl)) 

noncomputable abbrev qz277 := (RS169to186.d3 qz434 qz447 (@Enclosure.dec_le_dec qz434 qz447 434981 1000 436463 1000 qz437 qz450 rfl rfl rfl))

noncomputable abbrev qz854 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz277)

noncomputable def Ns168p2247 := @Enclosure.Real.IsNear.of_eq qz854 (hardyZApproximantRS₀ qz86) Bool.false 3448102409308625414321 590295810358705651712 120089048498478263638463 Ns168p449 

noncomputable abbrev qz278 := (@Enclosure.dec_le_dec qz434 qz447 434981 1000 436463 1000 qz437 qz450 rfl rfl rfl)

noncomputable def Ns168p2248 := @Enclosure.Real.IsNear.pos_val qz854 3448102409308625414321 590295810358705651712 120089048498478263638463 Ns168p449 (Ns168p2247 (RS169to186.d4 qz86 qz99 qz278) RS169to186.d48) rfl 

noncomputable abbrev qz855 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz277)

noncomputable def Ns168p2249 := @Enclosure.Real.IsNear.of_eq qz855 (hardyZApproximantRS₀ qz99) Bool.true 812062475939361163841 590295810358705651712 120267177763614291813547 Ns168p449 

noncomputable def Ns168p2250 := @Enclosure.Real.IsNear.neg_val qz855 812062475939361163841 590295810358705651712 120267177763614291813547 Ns168p449 (Ns168p2249 (RS169to186.d42 qz86 qz99 qz278) RS169to186.d49) rfl 

noncomputable def Ns168p2251 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz854 qz4 qz86 427552 1000 434981 1000 

noncomputable def Ns168p2252 := @Enclosure.norm_gt_of_isNear qz854 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 3448102409308625414321 590295810358705651712 120089048498478263638463 

noncomputable def Ns168p2253 := @Ns168p2252 Ns168p449 46626811 536870912 1421 2684354560 (Ns168p2247 (RS169to186.d4 qz86 qz99 qz278) RS169to186.d48) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2254 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz855 qz4 qz99 427552 1000 436463 1000 

noncomputable def Ns168p2255 := @Enclosure.norm_gt_of_isNear qz855 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 812062475939361163841 590295810358705651712 120267177763614291813547 

noncomputable def Ns168p2256 := @Ns168p2255 Ns168p449 46626811 536870912 1421 2684354560 (Ns168p2249 (RS169to186.d42 qz86 qz99 qz278) RS169to186.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2257 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz277 (@BSN.thirtyTwoPi_le_dec qz86 434981 1000 qz89 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz854 qz855 (Ns168p2248 rfl rfl) (Ns168p2250 rfl rfl)) (Ns168p2251 qz11 qz89 rfl rfl rfl rfl (Ns168p2253 rfl)) (Ns168p2254 qz11 qz102 rfl rfl rfl rfl (Ns168p2256 rfl)) 

noncomputable abbrev qz606 := (@Enclosure.dec_le_dec qz698 qz708 436463 1000 437944 1000 (@Eq.refl Real qz698) (@Eq.refl Real qz708) rfl rfl rfl)

noncomputable abbrev qz279 := (RS169to186.d3 qz447 qz460 qz606)

noncomputable abbrev qz856 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz279)

noncomputable def Ns168p2258 := @Enclosure.Real.IsNear.of_eq qz856 (hardyZApproximantRS₀ qz99) Bool.true 812062475939361163841 590295810358705651712 120267177763614291813547 Ns168p449 

noncomputable abbrev qz280 := qz606

noncomputable def Ns168p2259 := @Enclosure.Real.IsNear.neg_val qz856 812062475939361163841 590295810358705651712 120267177763614291813547 Ns168p449 (Ns168p2258 (RS169to186.d4 qz99 qz112 qz280) RS169to186.d49) rfl 

noncomputable abbrev qz857 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz279)

noncomputable def Ns168p2260 := @Enclosure.Real.IsNear.of_eq qz857 (hardyZApproximantRS₀ qz112) Bool.false 26699517161544463861 36893488147419103232 40174199129218664182001 Ns168p882 

noncomputable def Ns168p2261 := @Enclosure.Real.IsNear.pos_val qz857 26699517161544463861 36893488147419103232 40174199129218664182001 Ns168p882 (Ns168p2260 (RS169to186.d42 qz99 qz112 qz280) RS169to186.d50) rfl 

noncomputable def Ns168p2262 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz856 qz4 qz99 427552 1000 436463 1000 

noncomputable def Ns168p2263 := @Enclosure.norm_gt_of_isNear qz856 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 812062475939361163841 590295810358705651712 120267177763614291813547 

noncomputable def Ns168p2264 := @Ns168p2263 Ns168p449 46626811 536870912 1421 2684354560 (Ns168p2258 (RS169to186.d4 qz99 qz112 qz280) RS169to186.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2265 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz857 qz4 qz112 427552 1000 437944 1000 

noncomputable def Ns168p2266 := @Enclosure.norm_gt_of_isNear qz857 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 26699517161544463861 36893488147419103232 40174199129218664182001 

noncomputable def Ns168p2267 := @Ns168p2266 Ns168p882 46626811 536870912 1421 2684354560 (Ns168p2260 (RS169to186.d42 qz99 qz112 qz280) RS169to186.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2268 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz279 (@BSN.thirtyTwoPi_le_dec qz99 436463 1000 qz102 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz856 qz857 (Ns168p2259 rfl rfl) (Ns168p2261 rfl rfl)) (Ns168p2262 qz11 qz102 rfl rfl rfl rfl (Ns168p2264 rfl)) (Ns168p2265 qz11 qz115 rfl rfl rfl rfl (Ns168p2267 rfl)) 

noncomputable abbrev qz607 := (@Enclosure.dec_le_dec qz708 qz718 437944 1000 439424 1000 (@Eq.refl Real qz708) qz722 rfl rfl rfl)

noncomputable abbrev qz281 := (RS169to186.d3 qz460 qz473 qz607)

noncomputable abbrev qz858 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz281)

noncomputable def Ns168p2269 := @Enclosure.Real.IsNear.of_eq qz858 (hardyZApproximantRS₀ qz112) Bool.false 26699517161544463861 36893488147419103232 40174199129218664182001 Ns168p882 

noncomputable abbrev qz282 := qz607

noncomputable def Ns168p2270 := @Enclosure.Real.IsNear.pos_val qz858 26699517161544463861 36893488147419103232 40174199129218664182001 Ns168p882 (Ns168p2269 (RS169to186.d4 qz112 qz125 qz282) RS169to186.d50) rfl 

noncomputable abbrev qz859 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz281)

noncomputable def Ns168p2271 := @Enclosure.Real.IsNear.of_eq qz859 (hardyZApproximantRS₀ qz125) Bool.true 337949289263098029843 295147905179352825856 80569196155093298699 55340232221128654848000 

noncomputable def Ns168p2272 := @Enclosure.Real.IsNear.neg_val qz859 337949289263098029843 295147905179352825856 80569196155093298699 55340232221128654848000 (Ns168p2271 (RS169to186.d42 qz112 qz125 qz282) RS169to186.d51) rfl 

noncomputable def Ns168p2273 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz858 qz4 qz112 427552 1000 437944 1000 

noncomputable def Ns168p2274 := @Enclosure.norm_gt_of_isNear qz858 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 26699517161544463861 36893488147419103232 40174199129218664182001 

noncomputable def Ns168p2275 := @Ns168p2274 Ns168p882 46626811 536870912 1421 2684354560 (Ns168p2269 (RS169to186.d4 qz112 qz125 qz282) RS169to186.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2276 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz859 qz4 qz125 427552 1000 439424 1000 

noncomputable def Ns168p2277 := @Enclosure.norm_gt_of_isNear qz859 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 337949289263098029843 295147905179352825856 80569196155093298699 

noncomputable def Ns168p2278 := @Ns168p2277 55340232221128654848000 46626811 536870912 1421 2684354560 (Ns168p2271 (RS169to186.d42 qz112 qz125 qz282) RS169to186.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2279 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz281 (@BSN.thirtyTwoPi_le_dec qz112 437944 1000 qz115 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz858 qz859 (Ns168p2270 rfl rfl) (Ns168p2272 rfl rfl)) (Ns168p2273 qz11 qz115 rfl rfl rfl rfl (Ns168p2275 rfl)) (Ns168p2276 qz11 qz128 rfl rfl rfl rfl (Ns168p2278 rfl)) 

noncomputable abbrev qz608 := (@Enclosure.dec_le_dec qz718 qz729 439424 1000 440903 1000 qz722 qz733 rfl rfl rfl)

noncomputable abbrev qz283 := (RS169to186.d3 qz473 qz486 qz608)

noncomputable abbrev qz860 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz283)

noncomputable def Ns168p2280 := @Enclosure.Real.IsNear.of_eq qz860 (hardyZApproximantRS₀ qz125) Bool.true 337949289263098029843 295147905179352825856 80569196155093298699 55340232221128654848000 

noncomputable abbrev qz284 := qz608

noncomputable def Ns168p2281 := @Enclosure.Real.IsNear.neg_val qz860 337949289263098029843 295147905179352825856 80569196155093298699 55340232221128654848000 (Ns168p2280 (RS169to186.d4 qz125 qz138 qz284) RS169to186.d51) rfl 

noncomputable abbrev qz861 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz283)

noncomputable def Ns168p2282 := @Enclosure.Real.IsNear.of_eq qz861 (hardyZApproximantRS₀ qz138) Bool.false 5582352773414838984097 2361183241434822606848 53853116456387579704137 Ns168p1102 

noncomputable def Ns168p2283 := @Enclosure.Real.IsNear.pos_val qz861 5582352773414838984097 2361183241434822606848 53853116456387579704137 Ns168p1102 (Ns168p2282 (RS169to186.d42 qz125 qz138 qz284) RS169to186.d52) rfl 

noncomputable def Ns168p2284 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz860 qz4 qz125 427552 1000 439424 1000 

noncomputable def Ns168p2285 := @Enclosure.norm_gt_of_isNear qz860 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 337949289263098029843 295147905179352825856 80569196155093298699 

noncomputable def Ns168p2286 := @Ns168p2285 55340232221128654848000 46626811 536870912 1421 2684354560 (Ns168p2280 (RS169to186.d4 qz125 qz138 qz284) RS169to186.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2287 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz861 qz4 qz138 427552 1000 440903 1000 

noncomputable def Ns168p2288 := @Enclosure.norm_gt_of_isNear qz861 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 5582352773414838984097 2361183241434822606848 53853116456387579704137 

noncomputable def Ns168p2289 := @Ns168p2288 Ns168p1102 46626811 536870912 1421 2684354560 (Ns168p2282 (RS169to186.d42 qz125 qz138 qz284) RS169to186.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2290 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz283 (@BSN.thirtyTwoPi_le_dec qz125 439424 1000 qz128 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz860 qz861 (Ns168p2281 rfl rfl) (Ns168p2283 rfl rfl)) (Ns168p2284 qz11 qz128 rfl rfl rfl rfl (Ns168p2286 rfl)) (Ns168p2287 qz11 qz141 rfl rfl rfl rfl (Ns168p2289 rfl)) 

noncomputable abbrev qz862 := (@Enclosure.dec_le_dec qz928 qz932 440903 1000 442380 1000 (@Eq.refl Real qz928) qz935 rfl rfl rfl)

noncomputable abbrev qz609 := qz862

noncomputable abbrev qz285 := (RS169to186.d3 qz486 qz499 qz609)

noncomputable abbrev qz863 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz285)

noncomputable def Ns168p2291 := @Enclosure.Real.IsNear.of_eq qz863 (hardyZApproximantRS₀ qz138) Bool.false 5582352773414838984097 2361183241434822606848 53853116456387579704137 Ns168p1102 

noncomputable abbrev qz286 := qz609

noncomputable def Ns168p2292 := @Enclosure.Real.IsNear.pos_val qz863 5582352773414838984097 2361183241434822606848 53853116456387579704137 Ns168p1102 (Ns168p2291 (RS169to186.d4 qz138 qz151 qz286) RS169to186.d52) rfl 

noncomputable abbrev qz864 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz285)

noncomputable def Ns168p2293 := @Enclosure.Real.IsNear.of_eq qz864 (hardyZApproximantRS₀ qz151) Bool.true 414261428279040390117 295147905179352825856 242955086003153761319699 Ns168p339 

noncomputable def Ns168p2294 := @Enclosure.Real.IsNear.neg_val qz864 414261428279040390117 295147905179352825856 242955086003153761319699 Ns168p339 (Ns168p2293 (RS169to186.d42 qz138 qz151 qz286) RS169to186.d53) rfl 

noncomputable def Ns168p2295 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz863 qz4 qz138 427552 1000 440903 1000 

noncomputable def Ns168p2296 := @Enclosure.norm_gt_of_isNear qz863 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 5582352773414838984097 2361183241434822606848 53853116456387579704137 

noncomputable def Ns168p2297 := @Ns168p2296 Ns168p1102 46626811 536870912 1421 2684354560 (Ns168p2291 (RS169to186.d4 qz138 qz151 qz286) RS169to186.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2298 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz864 qz4 qz151 427552 1000 442380 1000 

noncomputable def Ns168p2299 := @Enclosure.norm_gt_of_isNear qz864 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 414261428279040390117 295147905179352825856 242955086003153761319699 

noncomputable def Ns168p2300 := @Ns168p2299 Ns168p339 46626811 536870912 1421 2684354560 (Ns168p2293 (RS169to186.d42 qz138 qz151 qz286) RS169to186.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2301 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz285 (@BSN.thirtyTwoPi_le_dec qz138 440903 1000 qz141 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz863 qz864 (Ns168p2292 rfl rfl) (Ns168p2294 rfl rfl)) (Ns168p2295 qz11 qz141 rfl rfl rfl rfl (Ns168p2297 rfl)) (Ns168p2298 qz11 qz154 rfl rfl rfl rfl (Ns168p2300 rfl)) 

noncomputable abbrev qz865 := (@Enclosure.dec_le_dec qz932 qz937 442380 1000 443857 1000 qz935 (@Eq.refl Real qz937) rfl rfl rfl)

noncomputable abbrev qz610 := qz865

noncomputable abbrev qz287 := (RS169to186.d3 qz499 qz511 qz610)

noncomputable abbrev qz866 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz287)

noncomputable def Ns168p2302 := @Enclosure.Real.IsNear.of_eq qz866 (hardyZApproximantRS₀ qz151) Bool.true 414261428279040390117 295147905179352825856 242955086003153761319699 Ns168p339 

noncomputable abbrev qz288 := qz610

noncomputable def Ns168p2303 := @Enclosure.Real.IsNear.neg_val qz866 414261428279040390117 295147905179352825856 242955086003153761319699 Ns168p339 (Ns168p2302 (RS169to186.d4 qz151 qz164 qz288) RS169to186.d53) rfl 

noncomputable abbrev qz867 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz287)

noncomputable def Ns168p2304 := @Enclosure.Real.IsNear.of_eq qz867 (hardyZApproximantRS₀ qz164) Bool.false 586681492384189057 288230376151711744 8123041445059535233793 Ns168p1322 

noncomputable def Ns168p2305 := @Enclosure.Real.IsNear.pos_val qz867 586681492384189057 288230376151711744 8123041445059535233793 Ns168p1322 (Ns168p2304 (RS169to186.d42 qz151 qz164 qz288) RS169to186.d54) rfl 

noncomputable def Ns168p2306 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz866 qz4 qz151 427552 1000 442380 1000 

noncomputable def Ns168p2307 := @Enclosure.norm_gt_of_isNear qz866 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 414261428279040390117 295147905179352825856 242955086003153761319699 

noncomputable def Ns168p2308 := @Ns168p2307 Ns168p339 46626811 536870912 1421 2684354560 (Ns168p2302 (RS169to186.d4 qz151 qz164 qz288) RS169to186.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2309 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz867 qz4 qz164 427552 1000 443857 1000 

noncomputable def Ns168p2310 := @Enclosure.norm_gt_of_isNear qz867 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 586681492384189057 288230376151711744 8123041445059535233793 

noncomputable def Ns168p2311 := @Ns168p2310 Ns168p1322 46626811 536870912 1421 2684354560 (Ns168p2304 (RS169to186.d42 qz151 qz164 qz288) RS169to186.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2312 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz287 (@BSN.thirtyTwoPi_le_dec qz151 442380 1000 qz154 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz866 qz867 (Ns168p2303 rfl rfl) (Ns168p2305 rfl rfl)) (Ns168p2306 qz11 qz154 rfl rfl rfl rfl (Ns168p2308 rfl)) (Ns168p2309 qz11 qz167 rfl rfl rfl rfl (Ns168p2311 rfl)) 

noncomputable abbrev qz289 := (RS169to186.d3 qz511 qz523 (@Enclosure.dec_le_dec qz511 qz523 443857 1000 446069 1000 qz514 qz526 rfl rfl rfl))

noncomputable abbrev qz868 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz289)

noncomputable def Ns168p2313 := @Enclosure.Real.IsNear.of_eq qz868 (hardyZApproximantRS₀ qz164) Bool.false 586681492384189057 288230376151711744 8123041445059535233793 Ns168p1322 

noncomputable abbrev qz290 := (@Enclosure.dec_le_dec qz511 qz523 443857 1000 446069 1000 qz514 qz526 rfl rfl rfl)

noncomputable def Ns168p2314 := @Enclosure.Real.IsNear.pos_val qz868 586681492384189057 288230376151711744 8123041445059535233793 Ns168p1322 (Ns168p2313 (RS169to186.d4 qz164 qz177 qz290) RS169to186.d54) rfl 

noncomputable abbrev qz869 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz289)

noncomputable def Ns168p2315 := @Enclosure.Real.IsNear.of_eq qz869 (hardyZApproximantRS₀ qz177) Bool.true 1100174837151980351471 295147905179352825856 81592772474651534555381 Ns168p1427 

noncomputable def Ns168p2316 := @Enclosure.Real.IsNear.neg_val qz869 1100174837151980351471 295147905179352825856 81592772474651534555381 Ns168p1427 (Ns168p2315 (RS169to186.d42 qz164 qz177 qz290) RS169to186.d55) rfl 

noncomputable def Ns168p2317 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz868 qz4 qz164 427552 1000 443857 1000 

noncomputable def Ns168p2318 := @Enclosure.norm_gt_of_isNear qz868 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 586681492384189057 288230376151711744 8123041445059535233793 

noncomputable def Ns168p2319 := @Ns168p2318 Ns168p1322 46626811 536870912 1421 2684354560 (Ns168p2313 (RS169to186.d4 qz164 qz177 qz290) RS169to186.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2320 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz869 qz4 qz177 427552 1000 446069 1000 

noncomputable def Ns168p2321 := @Enclosure.norm_gt_of_isNear qz869 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1100174837151980351471 295147905179352825856 81592772474651534555381 

noncomputable def Ns168p2322 := @Ns168p2321 Ns168p1427 46626811 536870912 1421 2684354560 (Ns168p2315 (RS169to186.d42 qz164 qz177 qz290) RS169to186.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2323 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz289 (@BSN.thirtyTwoPi_le_dec qz164 443857 1000 qz167 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz868 qz869 (Ns168p2314 rfl rfl) (Ns168p2316 rfl rfl)) (Ns168p2317 qz11 qz167 rfl rfl rfl rfl (Ns168p2319 rfl)) (Ns168p2320 qz11 qz180 rfl rfl rfl rfl (Ns168p2322 rfl)) 

noncomputable abbrev qz291 := (RS169to186.d3 qz523 qz535 (@Enclosure.dec_le_dec qz523 qz535 446069 1000 447174 1000 qz526 qz538 rfl rfl rfl))

noncomputable abbrev qz870 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz291)

noncomputable def Ns168p2324 := @Enclosure.Real.IsNear.of_eq qz870 (hardyZApproximantRS₀ qz177) Bool.true 1100174837151980351471 295147905179352825856 81592772474651534555381 Ns168p1427 

noncomputable abbrev qz292 := (@Enclosure.dec_le_dec qz523 qz535 446069 1000 447174 1000 qz526 qz538 rfl rfl rfl)

noncomputable def Ns168p2325 := @Enclosure.Real.IsNear.neg_val qz870 1100174837151980351471 295147905179352825856 81592772474651534555381 Ns168p1427 (Ns168p2324 (RS169to186.d4 qz177 qz190 qz292) RS169to186.d55) rfl 

noncomputable abbrev qz871 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz291)

noncomputable def Ns168p2326 := @Enclosure.Real.IsNear.of_eq qz871 (hardyZApproximantRS₀ qz190) Bool.false 92032837637743201637 295147905179352825856 817757857070082134599 553402322211286548480000 

noncomputable def Ns168p2327 := @Enclosure.Real.IsNear.pos_val qz871 92032837637743201637 295147905179352825856 817757857070082134599 553402322211286548480000 (Ns168p2326 (RS169to186.d42 qz177 qz190 qz292) RS169to186.d56) rfl 

noncomputable def Ns168p2328 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz870 qz4 qz177 427552 1000 446069 1000 

noncomputable def Ns168p2329 := @Enclosure.norm_gt_of_isNear qz870 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1100174837151980351471 295147905179352825856 81592772474651534555381 

noncomputable def Ns168p2330 := @Ns168p2329 Ns168p1427 46626811 536870912 1421 2684354560 (Ns168p2324 (RS169to186.d4 qz177 qz190 qz292) RS169to186.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2331 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz871 qz4 qz190 427552 1000 447174 1000 

noncomputable def Ns168p2332 := @Enclosure.norm_gt_of_isNear qz871 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 92032837637743201637 295147905179352825856 817757857070082134599 

noncomputable def Ns168p2333 := @Ns168p2332 553402322211286548480000 46626811 536870912 1421 2684354560 (Ns168p2326 (RS169to186.d42 qz177 qz190 qz292) RS169to186.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2334 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz291 (@BSN.thirtyTwoPi_le_dec qz177 446069 1000 qz180 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz870 qz871 (Ns168p2325 rfl rfl) (Ns168p2327 rfl rfl)) (Ns168p2328 qz11 qz180 rfl rfl rfl rfl (Ns168p2330 rfl)) (Ns168p2331 qz11 qz193 rfl rfl rfl rfl (Ns168p2333 rfl)) 

noncomputable abbrev qz611 := (@Enclosure.dec_le_dec qz775 qz786 447174 1000 447911 1000 (@Eq.refl Real qz775) (@Eq.refl Real qz786) rfl rfl rfl)

noncomputable abbrev qz293 := (RS169to186.d3 qz535 qz547 qz611)

noncomputable abbrev qz872 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz293)

noncomputable def Ns168p2335 := @Enclosure.Real.IsNear.of_eq qz872 (hardyZApproximantRS₀ qz190) Bool.false 92032837637743201637 295147905179352825856 817757857070082134599 553402322211286548480000 

noncomputable abbrev qz294 := qz611

noncomputable def Ns168p2336 := @Enclosure.Real.IsNear.pos_val qz872 92032837637743201637 295147905179352825856 817757857070082134599 553402322211286548480000 (Ns168p2335 (RS169to186.d4 qz190 qz203 qz294) RS169to186.d56) rfl 

noncomputable abbrev qz873 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz293)

noncomputable def Ns168p2337 := @Enclosure.Real.IsNear.of_eq qz873 (hardyZApproximantRS₀ qz203) Bool.true 626853300955397479587 590295810358705651712 49159613657094535010767 Ns168p1649 

noncomputable def Ns168p2338 := @Enclosure.Real.IsNear.neg_val qz873 626853300955397479587 590295810358705651712 49159613657094535010767 Ns168p1649 (Ns168p2337 (RS169to186.d42 qz190 qz203 qz294) RS169to186.d57) rfl 

noncomputable def Ns168p2339 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz872 qz4 qz190 427552 1000 447174 1000 

noncomputable def Ns168p2340 := @Enclosure.norm_gt_of_isNear qz872 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 92032837637743201637 295147905179352825856 817757857070082134599 

noncomputable def Ns168p2341 := @Ns168p2340 553402322211286548480000 46626811 536870912 1421 2684354560 (Ns168p2335 (RS169to186.d4 qz190 qz203 qz294) RS169to186.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2342 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz873 qz4 qz203 427552 1000 447911 1000 

noncomputable def Ns168p2343 := @Enclosure.norm_gt_of_isNear qz873 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 626853300955397479587 590295810358705651712 49159613657094535010767 

noncomputable def Ns168p2344 := @Ns168p2343 Ns168p1649 46626811 536870912 1421 2684354560 (Ns168p2337 (RS169to186.d42 qz190 qz203 qz294) RS169to186.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2345 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz293 (@BSN.thirtyTwoPi_le_dec qz190 447174 1000 qz193 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz872 qz873 (Ns168p2336 rfl rfl) (Ns168p2338 rfl rfl)) (Ns168p2339 qz11 qz193 rfl rfl rfl rfl (Ns168p2341 rfl)) (Ns168p2342 qz11 qz206 rfl rfl rfl rfl (Ns168p2344 rfl)) 

noncomputable abbrev qz612 := (@Enclosure.dec_le_dec qz786 qz797 447911 1000 449750 1000 (@Eq.refl Real qz786) qz801 rfl rfl rfl)

noncomputable abbrev qz295 := (RS169to186.d3 qz547 qz559 qz612)

noncomputable abbrev qz874 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz295)

noncomputable def Ns168p2346 := @Enclosure.Real.IsNear.of_eq qz874 (hardyZApproximantRS₀ qz203) Bool.true 626853300955397479587 590295810358705651712 49159613657094535010767 Ns168p1649 

noncomputable abbrev qz296 := qz612

noncomputable def Ns168p2347 := @Enclosure.Real.IsNear.neg_val qz874 626853300955397479587 590295810358705651712 49159613657094535010767 Ns168p1649 (Ns168p2346 (RS169to186.d4 qz203 qz216 qz296) RS169to186.d57) rfl 

noncomputable abbrev qz875 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz295)

noncomputable def Ns168p2348 := @Enclosure.Real.IsNear.of_eq qz875 (hardyZApproximantRS₀ qz216) Bool.false 760932367874656237119 1180591620717411303424 9869857443194912231207 Ns168p1763 

noncomputable def Ns168p2349 := @Enclosure.Real.IsNear.pos_val qz875 760932367874656237119 1180591620717411303424 9869857443194912231207 Ns168p1763 (Ns168p2348 (RS169to186.d42 qz203 qz216 qz296) RS169to186.d58) rfl 

noncomputable def Ns168p2350 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz874 qz4 qz203 427552 1000 447911 1000 

noncomputable def Ns168p2351 := @Enclosure.norm_gt_of_isNear qz874 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 626853300955397479587 590295810358705651712 49159613657094535010767 

noncomputable def Ns168p2352 := @Ns168p2351 Ns168p1649 46626811 536870912 1421 2684354560 (Ns168p2346 (RS169to186.d4 qz203 qz216 qz296) RS169to186.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2353 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz875 qz4 qz216 427552 1000 449750 1000 

noncomputable def Ns168p2354 := @Enclosure.norm_gt_of_isNear qz875 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 760932367874656237119 1180591620717411303424 9869857443194912231207 

noncomputable def Ns168p2355 := @Ns168p2354 Ns168p1763 46626811 536870912 1421 2684354560 (Ns168p2348 (RS169to186.d42 qz203 qz216 qz296) RS169to186.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2356 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz295 (@BSN.thirtyTwoPi_le_dec qz203 447911 1000 qz206 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz874 qz875 (Ns168p2347 rfl rfl) (Ns168p2349 rfl rfl)) (Ns168p2350 qz11 qz206 rfl rfl rfl rfl (Ns168p2352 rfl)) (Ns168p2353 qz11 qz219 rfl rfl rfl rfl (Ns168p2355 rfl)) 

noncomputable abbrev qz613 := (@Enclosure.dec_le_dec qz797 qz809 449750 1000 451221 1000 qz801 qz813 rfl rfl rfl)

noncomputable abbrev qz297 := (RS169to186.d3 qz559 qz571 qz613)

noncomputable abbrev qz876 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz297)

noncomputable def Ns168p2357 := @Enclosure.Real.IsNear.of_eq qz876 (hardyZApproximantRS₀ qz216) Bool.false 760932367874656237119 1180591620717411303424 9869857443194912231207 Ns168p1763 

noncomputable abbrev qz298 := qz613

noncomputable def Ns168p2358 := @Enclosure.Real.IsNear.pos_val qz876 760932367874656237119 1180591620717411303424 9869857443194912231207 Ns168p1763 (Ns168p2357 (RS169to186.d4 qz216 qz229 qz298) RS169to186.d58) rfl 

noncomputable abbrev qz877 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz297)

noncomputable def Ns168p2359 := @Enclosure.Real.IsNear.of_eq qz877 (hardyZApproximantRS₀ qz229) Bool.true 1911462920722457077065 2361183241434822606848 11000751307499885557347 Ns168p1868 

noncomputable def Ns168p2360 := @Enclosure.Real.IsNear.neg_val qz877 1911462920722457077065 2361183241434822606848 11000751307499885557347 Ns168p1868 (Ns168p2359 (RS169to186.d42 qz216 qz229 qz298) RS169to186.d59) rfl 

noncomputable def Ns168p2361 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz876 qz4 qz216 427552 1000 449750 1000 

noncomputable def Ns168p2362 := @Enclosure.norm_gt_of_isNear qz876 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 760932367874656237119 1180591620717411303424 9869857443194912231207 

noncomputable def Ns168p2363 := @Ns168p2362 Ns168p1763 46626811 536870912 1421 2684354560 (Ns168p2357 (RS169to186.d4 qz216 qz229 qz298) RS169to186.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2364 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz877 qz4 qz229 427552 1000 451221 1000 

noncomputable def Ns168p2365 := @Enclosure.norm_gt_of_isNear qz877 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1911462920722457077065 2361183241434822606848 11000751307499885557347 

noncomputable def Ns168p2366 := @Ns168p2365 Ns168p1868 46626811 536870912 1421 2684354560 (Ns168p2359 (RS169to186.d42 qz216 qz229 qz298) RS169to186.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2367 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz297 (@BSN.thirtyTwoPi_le_dec qz216 449750 1000 qz219 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz876 qz877 (Ns168p2358 rfl rfl) (Ns168p2360 rfl rfl)) (Ns168p2361 qz11 qz219 rfl rfl rfl rfl (Ns168p2363 rfl)) (Ns168p2364 qz11 qz232 rfl rfl rfl rfl (Ns168p2366 rfl)) 

noncomputable abbrev qz878 := (@Enclosure.dec_le_dec qz957 qz961 451221 1000 452691 1000 (@Eq.refl Real qz957) qz964 rfl rfl rfl)

noncomputable abbrev qz614 := qz878

noncomputable abbrev qz299 := (RS169to186.d3 qz571 qz583 qz614)

noncomputable abbrev qz879 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz299)

noncomputable def Ns168p2368 := @Enclosure.Real.IsNear.of_eq qz879 (hardyZApproximantRS₀ qz229) Bool.true 1911462920722457077065 2361183241434822606848 11000751307499885557347 Ns168p1868 

noncomputable abbrev qz300 := qz614

noncomputable def Ns168p2369 := @Enclosure.Real.IsNear.neg_val qz879 1911462920722457077065 2361183241434822606848 11000751307499885557347 Ns168p1868 (Ns168p2368 (RS169to186.d4 qz229 qz242 qz300) RS169to186.d59) rfl 

noncomputable abbrev qz880 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz299)

noncomputable def Ns168p2370 := @Enclosure.Real.IsNear.of_eq qz880 (hardyZApproximantRS₀ qz242) Bool.false 245503958113535290581 36893488147419103232 1379610492252988799177 922337203685477580800000 

noncomputable def Ns168p2371 := @Enclosure.Real.IsNear.pos_val qz880 245503958113535290581 36893488147419103232 1379610492252988799177 922337203685477580800000 (Ns168p2370 (RS169to186.d42 qz229 qz242 qz300) RS169to186.d60) rfl 

noncomputable def Ns168p2372 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz879 qz4 qz229 427552 1000 451221 1000 

noncomputable def Ns168p2373 := @Enclosure.norm_gt_of_isNear qz879 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1911462920722457077065 2361183241434822606848 11000751307499885557347 

noncomputable def Ns168p2374 := @Ns168p2373 Ns168p1868 46626811 536870912 1421 2684354560 (Ns168p2368 (RS169to186.d4 qz229 qz242 qz300) RS169to186.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2375 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz880 qz4 qz242 427552 1000 452691 1000 

noncomputable def Ns168p2376 := @Enclosure.norm_gt_of_isNear qz880 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 245503958113535290581 36893488147419103232 1379610492252988799177 

noncomputable def Ns168p2377 := @Ns168p2376 922337203685477580800000 46626811 536870912 1421 2684354560 (Ns168p2370 (RS169to186.d42 qz229 qz242 qz300) RS169to186.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2378 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz299 (@BSN.thirtyTwoPi_le_dec qz229 451221 1000 qz232 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz879 qz880 (Ns168p2369 rfl rfl) (Ns168p2371 rfl rfl)) (Ns168p2372 qz11 qz232 rfl rfl rfl rfl (Ns168p2374 rfl)) (Ns168p2375 qz11 qz245 rfl rfl rfl rfl (Ns168p2377 rfl)) 

noncomputable abbrev qz970 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 452691 1000) (Enclosure.sfrac Bool.false 454159 1000) 452691 1000 454159 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 452691 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 454159 1000)) rfl rfl rfl)

noncomputable abbrev qz881 := qz970

noncomputable abbrev qz615 := qz881

noncomputable abbrev qz301 := (RS169to186.d3 qz583 qz595 qz615)

noncomputable abbrev qz882 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz301)

noncomputable def Ns168p2379 := @Enclosure.Real.IsNear.of_eq qz882 (hardyZApproximantRS₀ qz242) Bool.false 245503958113535290581 36893488147419103232 1379610492252988799177 922337203685477580800000 

noncomputable abbrev qz302 := qz615

noncomputable def Ns168p2380 := @Enclosure.Real.IsNear.pos_val qz882 245503958113535290581 36893488147419103232 1379610492252988799177 922337203685477580800000 (Ns168p2379 (RS169to186.d4 qz242 qz255 qz302) RS169to186.d60) rfl 

noncomputable abbrev qz883 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz301)

noncomputable def Ns168p2381 := @Enclosure.Real.IsNear.of_eq qz883 (hardyZApproximantRS₀ qz255) Bool.true 95846853962433437863 147573952589676412928 221461939623134142079 147573952589676412928000 

noncomputable def Ns168p2382 := @Enclosure.Real.IsNear.neg_val qz883 95846853962433437863 147573952589676412928 221461939623134142079 147573952589676412928000 (Ns168p2381 (RS169to186.d42 qz242 qz255 qz302) RS169to186.d61) rfl 

noncomputable def Ns168p2383 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz882 qz4 qz242 427552 1000 452691 1000 

noncomputable def Ns168p2384 := @Enclosure.norm_gt_of_isNear qz882 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 245503958113535290581 36893488147419103232 1379610492252988799177 

noncomputable def Ns168p2385 := @Ns168p2384 922337203685477580800000 46626811 536870912 1421 2684354560 (Ns168p2379 (RS169to186.d4 qz242 qz255 qz302) RS169to186.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2386 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz883 qz4 qz255 427552 1000 454159 1000 

noncomputable def Ns168p2387 := @Enclosure.norm_gt_of_isNear qz883 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 95846853962433437863 147573952589676412928 221461939623134142079 

noncomputable def Ns168p2388 := @Ns168p2387 147573952589676412928000 46626811 536870912 1421 2684354560 (Ns168p2381 (RS169to186.d42 qz242 qz255 qz302) RS169to186.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 46626811 536870912 1421 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS169to186.d44) rfl rfl rfl rfl 

noncomputable def Ns168p2389 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz301 (@BSN.thirtyTwoPi_le_dec qz242 452691 1000 qz245 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz882 qz883 (Ns168p2380 rfl rfl) (Ns168p2382 rfl rfl)) (Ns168p2383 qz11 qz245 rfl rfl rfl rfl (Ns168p2385 rfl)) (Ns168p2386 qz11 (@Eq.refl Real qz255) rfl rfl rfl rfl (Ns168p2388 rfl)) 

noncomputable def Ns168p2390 := @List.cons RS169to186.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz299 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz299) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz299) Ns168p2378)) (@List.cons RS169to186.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz301 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz301) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz301) Ns168p2389)) (@List.nil RS169to186.d0)) 

noncomputable def Ns168p2391 := @List.cons RS169to186.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz295 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz295) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz295) Ns168p2356)) (@List.cons RS169to186.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz297 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz297) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz297) Ns168p2367)) Ns168p2390) 

noncomputable def Ns168p2392 := @List.cons RS169to186.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz291 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz291) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz291) Ns168p2334)) (@List.cons RS169to186.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz293 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz293) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz293) Ns168p2345)) Ns168p2391) 

noncomputable def Ns168p2393 := @List.cons RS169to186.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz287 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz287) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz287) Ns168p2312)) (@List.cons RS169to186.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz289 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz289) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz289) Ns168p2323)) Ns168p2392) 

noncomputable def Ns168p2394 := @List.cons RS169to186.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz283 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz283) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz283) Ns168p2290)) (@List.cons RS169to186.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz285 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz285) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz285) Ns168p2301)) Ns168p2393) 

noncomputable def Ns168p2395 := @List.cons RS169to186.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz279 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz279) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz279) Ns168p2268)) (@List.cons RS169to186.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz281 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz281) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz281) Ns168p2279)) Ns168p2394) 

noncomputable def Ns168p2396 := @List.cons RS169to186.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz275 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz275) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz275) Ns168p2246)) (@List.cons RS169to186.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz277 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz277) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz277) Ns168p2257)) Ns168p2395) 

noncomputable def Ns168p2397 := @List.cons RS169to186.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz271 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz271) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz271) Ns168p2224)) (@List.cons RS169to186.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz273 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz273) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz273) Ns168p2235)) Ns168p2396) 

noncomputable def Ns168p2398 := @List.cons RS169to186.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz267 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz267) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz267) Ns168p2202)) (@List.cons RS169to186.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz269 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz269) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz269) Ns168p2213)) Ns168p2397) 

noncomputable abbrev qz884 := (RS169to186.d2 qz957 qz961 (@Enclosure.dec_le_dec qz957 qz961 451221 1000 452691 1000 (@Eq.refl Real qz957) qz964 rfl rfl rfl))

noncomputable abbrev qz885 := (@List.cons RS169to186.d1 (RS169to186.d2 qz961 qz966 qz970) (@List.nil RS169to186.d1))

noncomputable abbrev qz616 := (@List.cons RS169to186.d1 (RS169to186.d2 qz797 qz809 (@Enclosure.dec_le_dec qz797 qz809 449750 1000 451221 1000 qz801 qz813 rfl rfl rfl)) (@List.cons RS169to186.d1 qz884 qz885))

noncomputable abbrev qz303 := (@List.cons RS169to186.d1 (RS169to186.d2 qz535 qz547 qz611) (@List.cons RS169to186.d1 (RS169to186.d2 qz547 qz559 qz612) qz616))

noncomputable def Ns168p2399 := @List.cons RS169to186.d1 (RS169to186.d2 qz164 qz177 qz290) (@List.cons RS169to186.d1 (RS169to186.d2 qz177 qz190 qz292) qz303) 

noncomputable abbrev qz886 := (RS169to186.d2 qz928 qz932 (@Enclosure.dec_le_dec qz928 qz932 440903 1000 442380 1000 (@Eq.refl Real qz928) qz935 rfl rfl rfl))

noncomputable abbrev qz887 := (RS169to186.d2 qz932 qz937 (@Enclosure.dec_le_dec qz932 qz937 442380 1000 443857 1000 qz935 (@Eq.refl Real qz937) rfl rfl rfl))

noncomputable abbrev qz617 := (@List.cons RS169to186.d1 (RS169to186.d2 qz718 qz729 (@Enclosure.dec_le_dec qz718 qz729 439424 1000 440903 1000 qz722 qz733 rfl rfl rfl)) (@List.cons RS169to186.d1 qz886 (@List.cons RS169to186.d1 qz887 Ns168p2399)))

noncomputable abbrev qz304 := (@List.cons RS169to186.d1 (RS169to186.d2 qz447 qz460 qz606) (@List.cons RS169to186.d1 (RS169to186.d2 qz460 qz473 qz607) qz617))

noncomputable def Ns168p2400 := @List.cons RS169to186.d1 (RS169to186.d2 qz73 qz86 qz276) (@List.cons RS169to186.d1 (RS169to186.d2 qz86 qz99 qz278) qz304) 

noncomputable def Ns168p2401 := @List.IsChain.cons_cons RS169to186.d1 RS169to186.d62 (RS169to186.d2 qz60 qz73 qz274) (RS169to186.d2 qz73 qz86 qz276) (@List.cons RS169to186.d1 (RS169to186.d2 qz86 qz99 qz278) qz304) 

noncomputable def Ns168p2402 := @List.IsChain.cons_cons RS169to186.d1 RS169to186.d62 (RS169to186.d2 qz73 qz86 qz276) (RS169to186.d2 qz86 qz99 qz278) qz304 (@Enclosure.dec_le_dec qz86 qz86 434981 1000 434981 1000 qz89 qz89 rfl rfl rfl) 

noncomputable abbrev qz618 := qz887

noncomputable abbrev qz305 := qz618

noncomputable def Ns168p2403 := @List.IsChain.cons_cons RS169to186.d1 RS169to186.d62 qz305 (RS169to186.d2 qz164 qz177 qz290) (@List.cons RS169to186.d1 (RS169to186.d2 qz177 qz190 qz292) qz303) 

noncomputable def Ns168p2404 := @List.IsChain.cons_cons RS169to186.d1 RS169to186.d62 (RS169to186.d2 qz164 qz177 qz290) (RS169to186.d2 qz177 qz190 qz292) qz303 (@Enclosure.dec_le_dec qz177 qz177 446069 1000 446069 1000 qz180 qz180 rfl rfl rfl) 

noncomputable abbrev qz306 := qz616

noncomputable abbrev qz619 := (@List.cons RS169to186.d1 qz884 qz885)

noncomputable abbrev qz307 := qz619

noncomputable abbrev qz620 := qz884

noncomputable abbrev qz308 := qz620

noncomputable abbrev qz621 := qz885

noncomputable abbrev qz309 := qz621

noncomputable abbrev qz888 := (RS169to186.d2 qz961 qz966 qz970)

noncomputable abbrev qz622 := qz888

noncomputable abbrev qz310 := qz622

noncomputable def Ns168p2405 := @List.IsChain.cons_cons RS169to186.d1 RS169to186.d62 (RS169to186.d2 qz190 qz203 qz294) (RS169to186.d2 qz203 qz216 qz296) qz306 (@Enclosure.dec_le_dec qz203 qz203 447911 1000 447911 1000 qz206 qz206 rfl rfl rfl) (@List.IsChain.cons_cons RS169to186.d1 RS169to186.d62 (RS169to186.d2 qz203 qz216 qz296) (RS169to186.d2 qz216 qz229 qz298) qz307 (@Enclosure.dec_le_dec qz216 qz216 449750 1000 449750 1000 qz219 qz219 rfl rfl rfl) (@List.IsChain.cons_cons RS169to186.d1 RS169to186.d62 (RS169to186.d2 qz216 qz229 qz298) qz308 qz309 (@Enclosure.dec_le_dec qz229 qz229 451221 1000 451221 1000 qz232 qz232 rfl rfl rfl) (@List.IsChain.cons_cons RS169to186.d1 RS169to186.d62 qz308 qz310 (@List.nil RS169to186.d1) (@Enclosure.dec_le_dec qz242 qz242 452691 1000 452691 1000 qz245 qz245 rfl rfl rfl) (@List.IsChain.singleton RS169to186.d1 RS169to186.d62 qz310)))) 

noncomputable abbrev qz311 := (@List.cons RS169to186.d1 (RS169to186.d2 qz547 qz559 qz612) qz616)

noncomputable def Ns168p2406 := @List.IsChain.cons_cons RS169to186.d1 RS169to186.d62 (RS169to186.d2 qz177 qz190 qz292) (RS169to186.d2 qz190 qz203 qz294) qz311 (@Enclosure.dec_le_dec qz190 qz190 447174 1000 447174 1000 qz193 qz193 rfl rfl rfl) Ns168p2405 

noncomputable abbrev qz312 := qz617

noncomputable abbrev qz623 := (@List.cons RS169to186.d1 qz886 (@List.cons RS169to186.d1 qz887 Ns168p2399))

noncomputable abbrev qz313 := qz623

noncomputable abbrev qz624 := qz886

noncomputable abbrev qz314 := qz624

noncomputable def Ns168p2407 := @List.IsChain.cons_cons RS169to186.d1 RS169to186.d62 (RS169to186.d2 qz99 qz112 qz280) (RS169to186.d2 qz112 qz125 qz282) qz312 (@Enclosure.dec_le_dec qz112 qz112 437944 1000 437944 1000 qz115 qz115 rfl rfl rfl) (@List.IsChain.cons_cons RS169to186.d1 RS169to186.d62 (RS169to186.d2 qz112 qz125 qz282) (RS169to186.d2 qz125 qz138 qz284) qz313 (@Enclosure.dec_le_dec qz125 qz125 439424 1000 439424 1000 qz128 qz128 rfl rfl rfl) (@List.IsChain.cons_cons RS169to186.d1 RS169to186.d62 (RS169to186.d2 qz125 qz138 qz284) qz314 (@List.cons RS169to186.d1 qz305 Ns168p2399) (@Enclosure.dec_le_dec qz138 qz138 440903 1000 440903 1000 qz141 qz141 rfl rfl rfl) (@List.IsChain.cons_cons RS169to186.d1 RS169to186.d62 qz314 qz305 Ns168p2399 (@Enclosure.dec_le_dec qz151 qz151 442380 1000 442380 1000 qz154 qz154 rfl rfl rfl) (Ns168p2403 (@Enclosure.dec_le_dec qz164 qz164 443857 1000 443857 1000 qz167 qz167 rfl rfl rfl) (Ns168p2404 Ns168p2406))))) 

noncomputable abbrev qz315 := (@List.cons RS169to186.d1 (RS169to186.d2 qz460 qz473 qz607) qz617)

noncomputable def Ns168p2408 := @List.IsChain.cons_cons RS169to186.d1 RS169to186.d62 (RS169to186.d2 qz86 qz99 qz278) (RS169to186.d2 qz99 qz112 qz280) qz315 (@Enclosure.dec_le_dec qz99 qz99 436463 1000 436463 1000 qz102 qz102 rfl rfl rfl) Ns168p2407 

noncomputable def Ns168p2409 := Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns168p2398 (@List.IsChain.cons_cons RS169to186.d1 RS169to186.d62 (RS169to186.d2 qz4 qz28 qz268) (RS169to186.d2 qz28 qz47 qz270) (@List.cons RS169to186.d1 (RS169to186.d2 qz47 qz60 qz272) (@List.cons RS169to186.d1 (RS169to186.d2 qz60 qz73 qz274) Ns168p2400)) (@Enclosure.dec_le_dec qz28 qz28 429040 1000 429040 1000 qz31 qz31 rfl rfl rfl) (@List.IsChain.cons_cons RS169to186.d1 RS169to186.d62 (RS169to186.d2 qz28 qz47 qz270) (RS169to186.d2 qz47 qz60 qz272) (@List.cons RS169to186.d1 (RS169to186.d2 qz60 qz73 qz274) Ns168p2400) (@Enclosure.dec_le_dec qz47 qz47 430527 1000 430527 1000 qz50 qz50 rfl rfl rfl) (@List.IsChain.cons_cons RS169to186.d1 RS169to186.d62 (RS169to186.d2 qz47 qz60 qz272) (RS169to186.d2 qz60 qz73 qz274) Ns168p2400 (@Enclosure.dec_le_dec qz60 qz60 432013 1000 432013 1000 qz63 qz63 rfl rfl rfl) (Ns168p2401 (@Enclosure.dec_le_dec qz73 qz73 433498 1000 433498 1000 qz76 qz76 rfl rfl rfl) (Ns168p2402 Ns168p2408))))) 

noncomputable abbrev qz625 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz626 := (Zeta.Certificates.CertifiedZeroIntervals.intervals Ns168p2409)

theorem RS169to186.d63 : Zeta.Certificates.BatchSpec 18 427552 1000 454159 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz625 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 18) (And (@Eq (Option Real) (@Option.map qz625 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz625 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz625 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz625 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz255)))) Ns168p2409 (@And.intro (@Eq Nat (@List.length qz625 qz626) 18) (And (@Eq (Option Real) (@Option.map qz625 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz625 qz626)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz625 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz625 qz626)) (@Option.some Real qz255))) (@Eq.refl Nat 18) (@And.intro (@Eq (Option Real) (@Option.map qz625 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz625 qz626)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz625 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz625 qz626)) (@Option.some Real qz255)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz255))))

theorem solution : Zeta.Certificates.BatchSpec 18 427552 1000 454159 1000 := RS169to186.d63
#print axioms solution
#check solution
