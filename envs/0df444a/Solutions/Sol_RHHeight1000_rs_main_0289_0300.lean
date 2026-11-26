-- Prove2me | solution 1 for RHHeight1000.rs_main_0289_0300
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:13:34.978616+00:00
-- url     : https://prove2.me/submissions/2d847050-e8f8-40d0-a4d9-d1dca793adc7

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

noncomputable def RS289to300.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS289to300.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS289to300.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS289to300.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS289to300.d2 a b h 

theorem RS289to300.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS289to300.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS289to300.d3 a b h)) 

noncomputable def Ns288p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns288p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns288p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns288p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns288p0 Ns288p1 Ns288p2 Ns288p1 153643044 134217728 1 64000000 153643044 134217728 1 64000000 76821522 67108864 2 67108864 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns288p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns288p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns288p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns288p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns288p8 := nat_lit 167537954069964697925743468333314178468718661948561187618563575975392713740913527107727581163208035826476740967700482432525301063254420572874757592895482956004842597348203117269212172556829666669574421653274845612596416189641484794702002223261246862056663160605878293700340502480877986491439034432953223334258717026053687371824342493299510132312376251152844516906794910572262907940062760396663270105627554083664899640691826599584783763757814813433640133591539937449421955686657622469485188711283992428713614179785896055117030632677201478317872225272595773536303110412989181984739022579128493081560758017763072115692678596043664844667144619713966763611484179303468167142547433165016751768184247559143333542643815355903304572487929375 

noncomputable def Ns288p9 := nat_lit 17907736863639440849562382641391758203535690054199171304015283257442503423240620144819838407313611418261944516207295868563739563278604805791797182761045687776939279949642059267526948014748996956777332184087524644234759874591635243045607722412471722018588244283882362848653445974523544951031470230725674276297342086185092985546835544820091590454230569790847977790484558207349923322458845585052164126500435851662252152223728079705692133047658564669873831757357628115566356048471439549797170528303905720944834637690907185213991407615774042056720704508980680095051114888612186461088301140868302968264130481206655302741383410655080008578156649725227045954510069588220729495895148666460653631514375880874422615237249871322129146554264800 

noncomputable def Ns288p10 := nat_lit 55164646516618494962085419356369025784335016154267579706247610053041231157772817011486486467101704279863254798704146668052276438579475100451766223896220272709675360577301802978530276301158911649961092601279696986330335403118086533522541958716560166657634553390183479955483588238249446822384543398154260439705049143284278540285021213103458182619368483938376641172730818250587232036579805400979202432024046862170503602539341971086573372247299262086029843105216008583038025403798224342134620653974939981235680083776396058604459065501719125356177784467570909658245422960948263734871602033841948787585406240093531041217463298165642337705122589129757920995868559518021463265498464182174549661735402095023640043996665674913376875 

noncomputable def Ns288p11 := BSN.log_dyadic_bound Ns288p6 Ns288p7 15 14 Ns288p8 134217728 64000000 Ns288p9 Ns288p10 153643044 Ns288p4 Ns288p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns288p6) (BSN.artanhQ Ns288p7) 0 14 Ns288p9 Ns288p8 Ns288p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns288p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns288p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns288p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns288p15 := nat_lit 167537954069966963268140139327979112712430526945422964221951926912223381190141639739514890494967825643602350173964944759828460064784215684919760383437959917620844610857567326816719640593037578236900835917107172977527392439886629774248115214831425484905681376157923696414882114961796820014026232307332015059110330001516939277521159573995394989771587717775443426002499543257897301982481613760098955890450106043861450716722534643739571053080256776912576113428445260435254713579381797931690799491102381747484553243404562568585572234105168360737285205910186933811836504830286397217473365026331067977496463917110493303316865058355012304571237619413071097245713770677768486493924969821719264401216877841676972336093778875903304572487929375 

noncomputable def Ns288p16 := nat_lit 17907736863639702486765313263906285882628955290251965205176678923530777959693011244026517850256414903756943142851250712732214241881959351517241344993825585048584379523049477943740273636414656012170312373198803997844271825165684859407921203335666024680974464565759223251918458072775203410604089667122984485578465112081892102496937045858735135721609691262763214794451343726045584198128451069547586972080574568545086657023793200560105564573365716615162566961587407171758966967827997201380802107846920231945878242774600967607639551032178207663699700360114112068650063802902647517702890145150192721997537569966984346993833704449560383184487996362781528900358997452380059737141488304159449328022742959995775545894292303322129146554264800 

noncomputable def Ns288p17 := nat_lit 55164646516619937449385584700664297411818070214438189962773666351465523500358685366424500506990751111492356556545320273548942244833046464529601272738875466881799996765940232256588350019911833156887888425998391295014189841212513610526066550079316346993943774342801096070086869790972589246312728227659319758310961510342377923950694747797317942483020440897997204711883064182772445608288320382376665481938194224815739627075458138172195220395246294556718284728034954178416253903237031389214179719385823921869528509431462690683227358218086518156757026652846493301460983550768858152506145788622699720737745394141184245149692548799188169247529408201840608223422296381897323845616153036586108326210125693898345963996665674913376875 

noncomputable def Ns288p18 := BSN.log_dyadic_bound Ns288p13 Ns288p14 15 14 Ns288p15 134217728 64000000 Ns288p16 Ns288p17 153643044 Ns288p12 Ns288p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns288p13) (BSN.artanhQ Ns288p14) 0 14 Ns288p16 Ns288p15 Ns288p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns288p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 76821522 67108864 2 67108864 38410761 33554432 1 33554432 (Ns288p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns288p0 Ns288p1 153643044 134217728 1 64000000 Bool.false (BSN.logfrac_isNear Ns288p4 Ns288p5 1 Ns288p0 Ns288p1 153643044 134217728 64000000 rfl rfl rfl (Ns288p11 rfl))) (BSN.isNear_log_sfrac Ns288p2 Ns288p1 153643044 134217728 1 64000000 Bool.false (BSN.logfrac_isNear Ns288p12 Ns288p5 1 Ns288p2 Ns288p1 153643044 134217728 64000000 rfl rfl rfl (Ns288p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS289to300.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 33554432 := Ns288p19 

noncomputable def Ns288p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 8388608 4000000 385100712855 135135 5814539 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz316 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz0 := qz316

theorem RS289to300.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 5814539 8388608 1 4000000 := BSN.isNear_log_sfrac 2 1 5814539 8388608 1 4000000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 5814539 8388608 4000000 rfl rfl rfl (Ns288p20 rfl)) 

theorem RS289to300.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 93032624 134217728 34 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 5814539 8388608 1 4000000 93032624 134217728 34 134217728 RS289to300.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz578 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz319 := qz578

noncomputable def Ns288p21 := @Enclosure.Real.IsNear.inv_image qz317 23726567 16777216 1 16777216 5931641 5931642 8388608 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 23726567 16777216 1 16777216 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 23726567 16777216 1 16777216 23726567 16777216 1 16777216 (BSN.sqrt_enclosure 2 1 11863283 11863284 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS289to300.d8 : Enclosure.Real.IsNear qz320 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 11863283 16777216 1 16777216 (Ns288p21 rfl rfl) rfl 

theorem RS289to300.d9 : Enclosure.Real.IsNear qz320 Bool.false 94906264 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 94906264 134217728 8 134217728 RS289to300.d8 rfl 

noncomputable def Ns288p22 := BSN.log_dyadic_bound 1 2 12 11 1326382131865190400 8388608 4000000 130797573554866995 13749310575 9215827 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 1) (BSN.artanhQ 2) 0 11 130797573554866995 1326382131865190400 13749310575 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS289to300.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 9215827 8388608 1 4000000 := BSN.isNear_log_sfrac 3 1 9215827 8388608 1 4000000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 9215827 8388608 4000000 rfl rfl rfl (Ns288p22 rfl)) 

theorem RS289to300.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 147453232 134217728 34 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 9215827 8388608 1 4000000 147453232 134217728 34 134217728 RS289to300.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns288p23 := @Enclosure.Real.IsNear.inv_image qz321 29058991 16777216 1 16777216 4843164 4843166 8388608 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 29058991 16777216 1 16777216 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 29058991 16777216 1 16777216 29058991 16777216 1 16777216 (BSN.sqrt_enclosure 3 1 14529495 14529496 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS289to300.d12 : Enclosure.Real.IsNear qz323 Bool.false 4843165 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 9686330 16777216 2 16777216 4843165 8388608 1 8388608 (Ns288p23 rfl rfl) rfl 

theorem RS289to300.d13 : Enclosure.Real.IsNear qz323 Bool.false 77490640 134217728 16 134217728 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 4843165 8388608 1 8388608 77490640 134217728 16 134217728 RS289to300.d12 rfl 

noncomputable def Ns288p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns288p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns288p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns288p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns288p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns288p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns288p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns288p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns288p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns288p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns288p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns288p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns288p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns288p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns288p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns288p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns288p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns288p25 Ns288p26 Ns288p27 Ns288p28 200200021673987500790625 Ns288p29 Ns288p30 Ns288p31 Ns288p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns288p32 Ns288p33 151412625 Ns288p34 Ns288p35 1322214852783825 Ns288p27 Ns288p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns288p32 Ns288p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns288p34 Ns288p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns288p36 Ns288p37 1267389585 Ns288p38 Ns288p39 1927077560082675 Ns288p29 Ns288p30 Ns288p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns288p36 Ns288p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns288p38 Ns288p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS289to300.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns288p24 Ns288p25 1 Ns288p26 := Ns288p40 rfl rfl rfl 

noncomputable def Ns288p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns288p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns288p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns288p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns288p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns288p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns288p25 Ns288p26 Ns288p42 Ns288p43 9945 Ns288p44 Ns288p45 65835 Ns288p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns288p42 Ns288p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns288p44 Ns288p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS289to300.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns288p41 Ns288p25 1 Ns288p26 := Ns288p46 rfl 

noncomputable def Ns288p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns288p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS289to300.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns288p47 Ns288p25 1 Ns288p48 := BSN.pi_combine Ns288p24 Ns288p41 Ns288p25 Ns288p26 Ns288p48 Ns288p47 rfl rfl rfl rfl RS289to300.d14 RS289to300.d15 

theorem RS289to300.d17 : Enclosure.Real.IsNear Real.pi Bool.false 7074237752028440 2251799813685248 1 2251799813685248 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns288p47 Ns288p25 1 Ns288p48 7074237752028440 2251799813685248 1 2251799813685248 RS289to300.d16 rfl 

noncomputable def Ns288p49 := nat_lit 147443727375074537121690809726715087890625 

noncomputable def Ns288p50 := nat_lit 22889945643899497138335355216896171420000 

noncomputable def Ns288p51 := nat_lit 355592320898650075318906513310625 

noncomputable def Ns288p52 := BSN.log_dyadic_bound 3 5 17 16 Ns288p49 8388608 4000000 Ns288p50 Ns288p51 11629079 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 3) (BSN.artanhQ 5) 0 16 Ns288p50 Ns288p49 Ns288p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS289to300.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 11629079 8388608 1 4000000 := BSN.isNear_log_sfrac 4 1 11629079 8388608 1 4000000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 11629079 8388608 4000000 rfl rfl rfl (Ns288p52 rfl)) 

theorem RS289to300.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 186065264 134217728 34 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 11629079 8388608 1 4000000 186065264 134217728 34 134217728 RS289to300.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns288p53 := @Enclosure.Real.IsNear.inv_image qz325 33554433 16777216 1 16777216 4194303 4194304 8388608 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 33554433 16777216 1 16777216 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 33554433 16777216 1 16777216 33554433 16777216 1 16777216 (BSN.sqrt_enclosure 4 1 16777216 16777217 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS289to300.d20 : Enclosure.Real.IsNear qz327 Bool.false 8388607 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 8388607 16777216 1 16777216 8388607 16777216 1 16777216 (Ns288p53 rfl rfl) rfl 

theorem RS289to300.d21 : Enclosure.Real.IsNear qz327 Bool.false 67108856 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 8388607 16777216 1 16777216 67108856 134217728 8 134217728 RS289to300.d20 rfl 

noncomputable def Ns288p54 := nat_lit 159424323765613091421820433543167414255940625 

noncomputable def Ns288p55 := nat_lit 33013339099500162583200499609923570567289500 

noncomputable def Ns288p56 := nat_lit 351657888879851162997374110924800000 

noncomputable def Ns288p57 := nat_lit 2289063575687431840984260 

noncomputable def Ns288p58 := nat_lit 3325435793429257756623375 

noncomputable def Ns288p59 := BSN.log_dyadic_bound 2 3 21 20 Ns288p54 8388608 4000000 Ns288p55 Ns288p56 13500943 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 20 10 9927050056596826020 47940881637414340575 686533194547200 Ns288p57 Ns288p58 512222703392784384000 Ns288p55 Ns288p54 Ns288p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 10 20 Ns288p57 Ns288p58 512222703392784384000 rfl rfl rfl rfl)) rfl rfl 

theorem RS289to300.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 13500943 8388608 1 4000000 := BSN.isNear_log_sfrac 5 1 13500943 8388608 1 4000000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 13500943 8388608 4000000 rfl rfl rfl (Ns288p59 rfl rfl)) 

theorem RS289to300.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 216015088 134217728 34 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 13500943 8388608 1 4000000 216015088 134217728 34 134217728 RS289to300.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns288p60 := @Enclosure.Real.IsNear.inv_image qz328 37514995 16777216 1 16777216 3751499 3751500 8388608 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 37514995 16777216 1 16777216 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 37514995 16777216 1 16777216 37514995 16777216 1 16777216 (BSN.sqrt_enclosure 5 1 18757497 18757498 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS289to300.d24 : Enclosure.Real.IsNear qz329 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 7502999 16777216 1 16777216 (Ns288p60 rfl rfl) rfl 

theorem RS289to300.d25 : Enclosure.Real.IsNear qz329 Bool.false 60023992 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 60023992 134217728 8 134217728 RS289to300.d24 rfl 

noncomputable def Ns288p61 := BSN.log_dyadic_bound 2 10 5 4 94500000000 8388608 4000000 1291130880 26880 3401287 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz578)

theorem RS289to300.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683410914551 2251799813685248 125000001 500000000000000 := BSN.isNear_log_sfrac 6 1 4034683410914551 2251799813685248 125000001 500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 541526040612241437360128 302231454903657293676544 1000000008000000 4000000000000000000000 4034683410914551 2251799813685248 125000001 500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 3401287 8388608 24973259072661432 36028797018963968 4000000 1000000000000000 rfl rfl rfl rfl (Ns288p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS289to300.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 240485871 134217728 35 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683410914551 2251799813685248 125000001 500000000000000 240485871 134217728 35 134217728 RS289to300.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns288p62 := @Enclosure.Real.IsNear.inv_image qz331 41095619 16777216 1 16777216 3424634 3424635 8388608 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 41095619 16777216 1 16777216 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 41095619 16777216 1 16777216 41095619 16777216 1 16777216 (BSN.sqrt_enclosure 6 1 20547809 20547810 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS289to300.d28 : Enclosure.Real.IsNear qz332 Bool.false 6849269 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 6849269 16777216 1 16777216 6849269 16777216 1 16777216 (Ns288p62 rfl rfl) rfl 

theorem RS289to300.d29 : Enclosure.Real.IsNear qz332 Bool.false 54794152 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 6849269 16777216 1 16777216 54794152 134217728 8 134217728 RS289to300.d28 rfl 

noncomputable def Ns288p63 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 8388608 4000000 11010900719820672 5524329195 4694397 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz578)

theorem RS289to300.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 125000001 500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 125000001 500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 588115238325433934020608 302231454903657293676544 1000000008000000 4000000000000000000000 4381799983422711 2251799813685248 125000001 500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 4694397 8388608 24973259072661432 36028797018963968 4000000 1000000000000000 rfl rfl rfl rfl (Ns288p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS289to300.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 261175631 134217728 35 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 125000001 500000000000000 261175631 134217728 35 134217728 RS289to300.d30 rfl 

noncomputable abbrev qz334 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns288p64 := @Enclosure.Real.IsNear.inv_image qz334 44388341 16777216 1 16777216 3170595 3170596 8388608 (@Enclosure.Real.IsNear.of_eq qz334 (Real.sqrt qz333) Bool.false 44388341 16777216 1 16777216 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 44388341 16777216 1 16777216 44388341 16777216 1 16777216 (BSN.sqrt_enclosure 7 1 22194170 22194171 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS289to300.d32 : Enclosure.Real.IsNear qz335 Bool.false 6341191 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 6341191 16777216 1 16777216 6341191 16777216 1 16777216 (Ns288p64 rfl rfl) rfl 

theorem RS289to300.d33 : Enclosure.Real.IsNear qz335 Bool.false 50729528 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 6341191 16777216 1 16777216 50729528 134217728 8 134217728 RS289to300.d32 rfl 

noncomputable def Ns288p65 := BSN.log_dyadic_bound 0 16 1 0 1 8388608 4000000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz578)

theorem RS289to300.d34 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 250000003 1000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 250000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false 628472642529000809299968 302231454903657293676544 1000000012000000 4000000000000000000000 9364972152248037 4503599627370496 250000003 1000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 8388608 24973259072661432 36028797018963968 4000000 1000000000000000 rfl rfl rfl rfl (Ns288p65 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS289to300.d35 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 279097919 134217728 34 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 250000003 1000000000000000 279097919 134217728 34 134217728 RS289to300.d34 rfl 

noncomputable abbrev qz337 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns288p66 := @Enclosure.Real.IsNear.inv_image qz337 47453133 16777216 1 16777216 2965820 2965821 8388608 (@Enclosure.Real.IsNear.of_eq qz337 (Real.sqrt qz336) Bool.false 47453133 16777216 1 16777216 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 47453133 16777216 1 16777216 47453133 16777216 1 16777216 (BSN.sqrt_enclosure 8 1 23726566 23726567 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz338 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS289to300.d36 : Enclosure.Real.IsNear qz338 Bool.false 5931641 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 5931641 16777216 1 16777216 5931641 16777216 1 16777216 (Ns288p66 rfl rfl) rfl 

theorem RS289to300.d37 : Enclosure.Real.IsNear qz338 Bool.false 47453128 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 5931641 16777216 1 16777216 47453128 134217728 8 134217728 RS289to300.d36 rfl 

noncomputable def Ns288p67 := BSN.log_dyadic_bound 1 17 3 2 1252815 8388608 4000000 1448 3 988035 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz707 := (Enclosure.sfrac Bool.false 9 1)

noncomputable abbrev qz579 := qz707

noncomputable abbrev qz339 := qz579

noncomputable abbrev qz1 := qz339

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz578)

theorem RS289to300.d38 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 9895419403785957 4503599627370496 250000003 1000000000000000 := BSN.isNear_log_sfrac 9 1 9895419403785957 4503599627370496 250000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz340) Bool.false 664070354991632873422848 302231454903657293676544 1000000012000000 4000000000000000000000 9895419403785957 4503599627370496 250000003 1000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 988035 8388608 24973259072661432 36028797018963968 4000000 1000000000000000 rfl rfl rfl rfl (Ns288p67 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS289to300.d39 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 294906479 134217728 34 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 9895419403785957 4503599627370496 250000003 1000000000000000 294906479 134217728 34 134217728 RS289to300.d38 rfl 

noncomputable abbrev qz341 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns288p68 := @Enclosure.Real.IsNear.inv_image qz341 50331649 16777216 1 16777216 2796202 2796203 8388608 (@Enclosure.Real.IsNear.of_eq qz341 (Real.sqrt qz340) Bool.false 50331649 16777216 1 16777216 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz340) Bool.false 50331649 16777216 1 16777216 50331649 16777216 1 16777216 (BSN.sqrt_enclosure 9 1 25165824 25165825 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz342 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS289to300.d40 : Enclosure.Real.IsNear qz342 Bool.false 5592405 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz342 Bool.false 5592405 16777216 1 16777216 5592405 16777216 1 16777216 (Ns288p68 rfl rfl) rfl 

theorem RS289to300.d41 : Enclosure.Real.IsNear qz342 Bool.false 44739240 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz342 Bool.false 5592405 16777216 1 16777216 44739240 134217728 8 134217728 RS289to300.d40 rfl 

theorem RS289to300.d42 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz708 := (@instHMul Real Real.instMul)

noncomputable abbrev qz580 := qz708

noncomputable abbrev qz343 := (@HMul.hMul Real Real Real qz580 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz2 := qz343

theorem RS289to300.d43 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS289to300.d42 rfl 

noncomputable abbrev qz344 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz580 (Enclosure.sfrac Bool.false 2 1) Real.pi))

noncomputable abbrev qz3 := qz344

theorem RS289to300.d44 : Enclosure.Real.IsNear qz3 Bool.false 2670177 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 2670177 16777216 1 16777216 2670177 16777216 1 16777216 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 1335088 1335089 8388608 RS289to300.d43 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns288p69 := nat_lit 1844674407370955161600000 

noncomputable def Ns288p70 := nat_lit 2054269781720935522705080320 

noncomputable abbrev qz709 := (Enclosure.sfrac Bool.false 598981 1000)

noncomputable abbrev qz581 := qz709

noncomputable abbrev qz345 := qz581

noncomputable abbrev qz4 := qz345

noncomputable abbrev qz346 := qz580

noncomputable abbrev qz5 := qz346

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 9)

noncomputable abbrev qz347 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz710 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 598981 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz582 := qz710

noncomputable abbrev qz348 := qz582

noncomputable abbrev qz349 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz7 := (@HPow.hPow Real Real Real qz347 qz348 qz349)

noncomputable abbrev qz711 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 598981 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz583 := qz711

noncomputable abbrev qz350 := qz583

noncomputable abbrev qz8 := qz350

noncomputable def Ns288p71 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8)) 30601505 16777216 84685 67108864 12142821687486012375 73786976294838206464 252629172356869951443 Ns288p69 Ns288p70 

noncomputable def Ns288p72 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 598981 1000 114 159 134217728 67108864 2251799813685248 Bool.false 142941975371 1836 

noncomputable def Ns288p73 := Ns288p72 279097919 34 47453128 8 294906479 34 44739240 8 Bool.true 161379252 69416 Bool.true 197901838 Bool.true 179636779 7074237752028440 1 Bool.false 12906900 Bool.true Bool.false 130609539 Bool.false Bool.true 122406020 

noncomputable def Ns288p74 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 598981 1000 5 64 134217728 67108864 2251799813685248 Bool.false 142941975371 1836 

noncomputable def Ns288p75 := Ns288p74 240485871 35 54794152 8 261175631 35 50729528 8 Bool.true 192007602 51470 Bool.true 50348555 Bool.true 4227556 7074237752028440 1 Bool.false 49175998 Bool.true Bool.false 134151154 Bool.false Bool.true 161379252 

noncomputable def Ns288p76 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 598981 1000 149 64 134217728 67108864 2251799813685248 Bool.false 142941975371 1836 

noncomputable def Ns288p77 := Ns288p76 186065264 34 67108856 8 216015088 34 60023992 8 Bool.true 208899316 30420 Bool.false 78939069 Bool.false 60004241 7074237752028440 1 Bool.false 74466154 Bool.true Bool.false 121026705 Bool.false Bool.true 192007602 

noncomputable def Ns288p78 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 598981 1000 413 259 134217728 67108864 2251799813685248 Bool.false 142941975371 1836 

noncomputable def Ns288p79 := Ns288p78 93032624 34 94906264 8 147453232 34 77490640 16 Bool.true 134217680 1874 Bool.false 144942277 Bool.false 15654053 7074237752028440 1 Bool.false 118368306 Bool.true Bool.false 15618586 Bool.false Bool.true 208899316 

noncomputable def Ns288p80 := nat_lit 498392360121514751131582051868556467052665414039011527607 

noncomputable def Ns288p81 := nat_lit 467973735875208525792264034257081008134654783389696000 

noncomputable def Ns288p82 := nat_lit 37008990315856602839347945072480000 

noncomputable def Ns288p83 := nat_lit 133006135421058083293321497608610857280 

noncomputable abbrev qz351 := (@Eq.refl Real qz581)

noncomputable abbrev qz9 := qz351

noncomputable def Ns288p84 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 598981 1000 1435113953444 16000000 1197962 4000 2000 Ns288p82 Ns288p83 qz9 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns288p85 := nat_lit 159485555238884720362106256597938069456852932492483688834240 

noncomputable abbrev qz712 := (@instHSub Real Real.instSub)

noncomputable abbrev qz584 := qz712

noncomputable abbrev qz352 := qz584

noncomputable abbrev qz585 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz713 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz714 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz586 := (@HSub.hSub Real Real Real qz712 qz713 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz714 (@Nat.cast Real Real.instNatCast 1197962))))

noncomputable abbrev qz353 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz580 (Enclosure.sfrac Bool.false 598981 4000) (Real.log (Enclosure.sfrac Bool.false 1435113953444 16000000))) (@HMul.hMul Real Real Real qz580 qz585 qz586))

noncomputable abbrev qz587 := (Enclosure.sfrac Bool.false 598981 2000)

noncomputable abbrev qz10 := (@HSub.hSub Real Real Real qz352 (@HSub.hSub Real Real Real qz352 qz353 qz587) (@HMul.hMul Real Real Real qz346 qz587 (Real.log Real.pi)))

noncomputable def Ns288p86 := @Enclosure.Real.IsNear.addLit_ft_p qz10 (Enclosure.sfrac Bool.true Ns288p82 Ns288p83) 1199084511420614118583 1125899906842624000 27991150369998977 2048000000000000000000 Ns288p82 Ns288p83 0 1 Ns288p85 

noncomputable def Ns288p87 := nat_lit 80469199401432439680466419712000 

noncomputable abbrev qz11 := (@HSub.hSub Real Real Real qz352 qz353 qz587)

noncomputable def Ns288p88 := @Enclosure.Real.IsNear.subLit_ff_p qz11 (@HMul.hMul Real Real Real qz5 qz587 (Real.log Real.pi)) 1585083222112371936439 1125899906842624000 4742041458549 1000000000000000000 23007316034541 67108864000 598981 67108864000 Ns288p87 1199084511420614118583 1125899906842624000 

noncomputable def Ns288p89 := nat_lit 3170166444224743872878000 

noncomputable abbrev qz12 := qz353

noncomputable def Ns288p90 := @Enclosure.Real.IsNear.subLit_ff_p qz12 qz587 1922279548162622819511 1125899906842624000 4742041458549 1000000000000000000 598981 2000 0 1 Ns288p89 1585083222112371936439 1125899906842624000 4742041458549 1000000000000000000 

noncomputable def Ns288p91 := nat_lit 4328588728403556774383743513267273728 

noncomputable def Ns288p92 := nat_lit 27573581667099267460759552 

noncomputable def Ns288p93 := nat_lit 2417851639229258349412352 

noncomputable def Ns288p94 := nat_lit 1368393029418793946487327141761867729647174769407827968482629495816049187945092745476161489229482885120 

noncomputable def Ns288p95 := nat_lit 11211267992876665279757176782011128699916771064172135077821707170680762595720574198133186261854715904 

noncomputable def Ns288p96 := nat_lit 52327072994498809016253240868854460315812322370834999059787856556200393329939588043435311431680 

noncomputable def Ns288p97 := BSN.log_dyadic_bound 386537953444 2483689953444 5 4 Ns288p94 67108864 32000000 Ns288p95 Ns288p96 21059513 2870227906888 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 386537953444) (BSN.artanhQ 2483689953444) 0 4 Ns288p95 Ns288p94 Ns288p96 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz354 := (Real.log (Enclosure.sfrac Bool.false 1435113953444 16000000))

noncomputable abbrev qz355 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns288p98 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 598981 4000) qz354 598981 4000 0 1 3209987383696631 281474976710656 976563 31250000000000 1922721453073991733011 1125899906842624000 584942682303 125000000000000000 (Enclosure.Real.IsNear.const Bool.false 598981 4000) (BSN.isNear_log_sfrac 1435113953444 16000000 3209987383696631 281474976710656 976563 31250000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1435113953444) qz355)) Bool.false Ns288p92 Ns288p93 1000000512000000 32000000000000000000000 3209987383696631 281474976710656 976563 31250000000000 (BSN.log_rat_reduce_isNear 1435113953444 16000000 16 2870227906888 2097152000000 21059513 67108864 24973259072661432 36028797018963968 32000000 1000000000000000 rfl rfl rfl rfl (Ns288p97 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns288p99 := BSN.arctan_dyadic_bound_f 1000 1197962 1 0 8388608 4000000 0 1 1 0 1 1 7002 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1197962) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1197962) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz588 := qz713

noncomputable abbrev qz356 := qz588

noncomputable abbrev qz13 := qz356

noncomputable abbrev qz589 := qz714

noncomputable abbrev qz357 := qz589

noncomputable abbrev qz14 := qz357

noncomputable abbrev qz715 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz590 := qz715

noncomputable abbrev qz358 := qz590

noncomputable abbrev qz15 := (@Enclosure.Real.IsNear.mulLit_ff qz358 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz359 := (@Nat.cast Real Real.instNatCast 1197962)

noncomputable def Ns288p100 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz359)) 884279719003555 562949953421312 1 2000000000000000 7002 8388608 1 4000000 7413934149497117474816 883809822737827 562949953421312 500000001 2000000000000000 qz15 (Ns288p99 rfl) rfl rfl 

noncomputable abbrev qz360 := (@HMul.hMul Real Real Real qz580 qz585 qz586)

noncomputable abbrev qz16 := qz360

noncomputable abbrev qz361 := qz585

noncomputable abbrev qz17 := qz361

noncomputable abbrev qz362 := qz586

noncomputable abbrev qz18 := qz362

noncomputable abbrev qz363 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns288p101 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 598981 4000) qz354) qz16 1922721453073991733011 1125899906842624000 584942682303 125000000000000000 883809822737827 2251799813685248 500000001 8000000000000000 Ns288p91 1922279548162622819511 1125899906842624000 4742041458549 1000000000000000000 (Ns288p98 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz18 1 4 0 1 883809822737827 562949953421312 500000001 2000000000000000 883809822737827 2251799813685248 500000001 8000000000000000 qz363 Ns288p100 rfl) 

noncomputable def Ns288p102 := @Ns288p86 Ns288p80 Ns288p81 27991150369998977 2048000000000000000000 (@Ns288p88 27991150369998977 2048000000000000000000 (Ns288p90 (Ns288p101 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 598981 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz587 (Real.log Real.pi) 598981 2000 0 1 38410761 33554432 1 33554432 23007316034541 67108864000 598981 67108864000 (Enclosure.Real.IsNear.const Bool.false 598981 2000) RS289to300.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns288p82 Ns288p83) 

noncomputable abbrev qz364 := (@instHAdd Real Real.instAdd)

noncomputable def Ns288p103 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns288p80 Ns288p81 27991150369998977 2048000000000000000000 17867746921 16777216 115 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz364 qz10 (Enclosure.sfrac Bool.true Ns288p82 Ns288p83)) Bool.false Ns288p80 Ns288p81 27991150369998977 2048000000000000000000 Ns288p84 (Ns288p102 rfl rfl)) 

noncomputable def Ns288p104 := BSN.cos_dyadic_bound_f 27439544 34359738368 1 0 16777216 8007813 0 1 1 0 1 1 16777210 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 27439544) (BSN.cosEvenQ 34359738368) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 27439544) (BSN.cosOddQ 34359738368) 0 0 rfl) rfl rfl 

noncomputable abbrev qz365 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable abbrev qz366 := (@Nat.cast Real Real.instNatCast Ns288p93)

noncomputable def Ns288p105 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17867746921) qz365) Bool.false 17867746921 16777216 115 8388608 Bool.true 16777210 16777216 1 4000000 (Ns288p103 rfl) (Enclosure.sfrac_false_div 17867746921 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17867746921) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1930886272213971894272) qz366) 226375608064910080 72057594037927936 Bool.false 16777210 16777216 169 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q2 17867746921 16777216 226375608064910080 72057594037927936 169 1930886272213971894272 Ns288p93 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777210 16777216 1930886272213971894272 Ns288p93 27439544 34359738368 8007813 8000000 (Ns288p104 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p106 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns288p80 Ns288p81 27991150369998977 2048000000000000000000 142941975371 134217728 1836 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz364 qz10 (Enclosure.sfrac Bool.true Ns288p82 Ns288p83)) Bool.false Ns288p80 Ns288p81 27991150369998977 2048000000000000000000 Ns288p84 (Ns288p102 rfl rfl)) 

noncomputable def Ns288p107 := Ns288p79 30420 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 413 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 118368306 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 259 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 15618586 134217728) qz9 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 8388605 8388608 1829643 131072000000 134217680 134217728 1874 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 8388605 8388608 1829643 131072000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 16777210 16777216 468388608 33554432000000 8388605 8388608 1829643 131072000000 (Ns288p105 rfl rfl) rfl)) rfl) (Ns288p106 rfl) RS289to300.d7 

noncomputable def Ns288p108 := nat_lit 433308204005698841330200620919968476702182242682731675114363294933985 

noncomputable def Ns288p109 := nat_lit 38215724400686031908940493885850326479880652218951261491964367528263680 

noncomputable def Ns288p110 := nat_lit 194787299830822948832204959947538531849456791380146219696968000481 

noncomputable def Ns288p111 := nat_lit 1134539450100913728233368532474288090882721038887777007610489729016801 

noncomputable def Ns288p112 := nat_lit 700621614012577251663909054573922652131145290680773127352680071351500800 

noncomputable abbrev qz367 := (BSN.sinEvenQ 134217728)

noncomputable abbrev qz368 := (BSN.sinOddQ 134217728)

noncomputable def Ns288p113 := BSN.sin_dyadic_bound_f 144942277 134217728 3 2 134217728 67108864 Ns288p108 Ns288p109 Ns288p110 Ns288p111 Ns288p112 Ns288p110 118368306 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 144942277) qz367 0 2 Ns288p108 Ns288p109 Ns288p110 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 144942277) qz368 0 2 Ns288p111 Ns288p112 Ns288p110 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p114 := nat_lit 60049196348059307495554122481 

noncomputable def Ns288p115 := nat_lit 38942226439011207213978722469150720 

noncomputable def Ns288p116 := nat_lit 272595585073078450497851057284055040 

noncomputable def Ns288p117 := BSN.sin_dyadic_bound_f 15654053 134217728 2 1 134217728 67108864 Ns288p114 Ns288p115 Ns288p114 Ns288p114 Ns288p116 Ns288p114 15618586 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 15654053) qz367 0 1 Ns288p114 Ns288p115 Ns288p114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 15654053) qz368 0 1 Ns288p114 Ns288p116 Ns288p114 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p118 := nat_lit 38107152915162367324246949057234686355707827327142921184753871196065 

noncomputable def Ns288p119 := nat_lit 1507773133468476746511150011393963187549958128360646482586996641 

noncomputable def Ns288p120 := nat_lit 99802006954637727363057181859405731181693038305547447770526426566561 

noncomputable def Ns288p121 := BSN.sin_dyadic_bound_f 78939069 134217728 3 2 134217728 67108864 Ns288p118 Ns288p109 Ns288p119 Ns288p120 Ns288p112 Ns288p119 74466154 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 78939069) qz367 0 2 Ns288p118 Ns288p109 Ns288p119 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 78939069) qz368 0 2 Ns288p120 Ns288p112 Ns288p119 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p122 := nat_lit 7067843536081012885869410084767398860654794875538379504744519145601 

noncomputable def Ns288p123 := nat_lit 4246191600076225767660054876205591831097850246550140165773818614251520 

noncomputable def Ns288p124 := nat_lit 168056600185842570798161823763645307139457319117084084650350721 

noncomputable def Ns288p125 := nat_lit 21203194495042666972466633930654669291350105711976904346064256735361 

noncomputable def Ns288p126 := nat_lit 191078622003430159544702469429251632399403261094756307459821837641318400 

noncomputable abbrev qz369 := (BSN.cosEvenQ 134217728)

noncomputable abbrev qz370 := (BSN.cosOddQ 134217728)

noncomputable def Ns288p127 := BSN.cos_dyadic_bound_f 60004241 134217728 3 2 134217728 67108864 Ns288p122 Ns288p123 Ns288p124 Ns288p125 Ns288p126 Ns288p124 121026705 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 60004241) qz369 0 2 Ns288p122 Ns288p123 Ns288p124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 60004241) qz370 0 2 Ns288p125 Ns288p126 Ns288p124 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p128 := Ns288p77 51470 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 149 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 74466154 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 121026705 134217728) qz9 rfl rfl (Ns288p107 RS289to300.d9 RS289to300.d11 RS289to300.d13 RS289to300.d17 (Ns288p113 rfl rfl) (Ns288p117 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns288p106 rfl) RS289to300.d19 RS289to300.d21 RS289to300.d23 RS289to300.d25 RS289to300.d17 (Ns288p121 rfl rfl) (Ns288p127 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns288p129 := nat_lit 6426108342810719789435273400625 

noncomputable def Ns288p130 := BSN.sin_dyadic_bound_f 50348555 134217728 2 1 134217728 67108864 Ns288p129 Ns288p115 Ns288p129 Ns288p129 Ns288p116 Ns288p129 49175998 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 50348555) qz367 0 1 Ns288p129 Ns288p115 Ns288p129 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 50348555) qz368 0 1 Ns288p129 Ns288p116 Ns288p129 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p131 := nat_lit 319416595633990497776394496 

noncomputable def Ns288p132 := nat_lit 7788445287802241442795744493830144 

noncomputable def Ns288p133 := nat_lit 116826679317033621641936167407452160 

noncomputable def Ns288p134 := BSN.cos_dyadic_bound_f 4227556 134217728 2 1 134217728 67108864 Ns288p131 Ns288p132 Ns288p131 Ns288p131 Ns288p133 Ns288p131 134151154 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 4227556) qz369 0 1 Ns288p131 Ns288p132 Ns288p131 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 4227556) qz370 0 1 Ns288p131 Ns288p133 Ns288p131 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p135 := Ns288p75 69416 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 5 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 49175998 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 134151154 134217728) qz9 rfl rfl (Ns288p128 rfl rfl) (Ns288p106 rfl) RS289to300.d27 RS289to300.d29 RS289to300.d31 RS289to300.d33 RS289to300.d17 (Ns288p130 rfl rfl) (Ns288p134 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p136 := nat_lit 3233141880893241731551204324763046384213940935880349951569295544068720184751375879872045702385061507239936 

noncomputable def Ns288p137 := nat_lit 16370259324565974446773555668639125346849261288577159159185037526614652227207809159774062022111344040345600 

noncomputable def Ns288p138 := nat_lit 3609091830412808585393604322092495024405447678293584336936154057800712844875967279228690767427014656 

noncomputable def Ns288p139 := nat_lit 19577688684197514972585301050223905940914032459132118072214643436743064807408436431496071244472262194237440 

noncomputable def Ns288p140 := nat_lit 1489693598535503674656393565846160406563282777260521483485838414921933352675910633539439644012132307671449600 

noncomputable def Ns288p141 := BSN.cos_dyadic_bound_f 197901838 134217728 4 3 134217728 67108864 Ns288p136 Ns288p137 Ns288p138 Ns288p139 Ns288p140 Ns288p138 12906900 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 197901838) qz369 0 3 Ns288p136 Ns288p137 Ns288p138 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 197901838) qz370 0 3 Ns288p139 Ns288p140 Ns288p138 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p142 := nat_lit 5696654050136311031453755351042402930284807926494188935963329928682258666186020243840659853932443307361041 

noncomputable def Ns288p143 := nat_lit 212813371219357667808056223692308629509040396751503069069405487845990478953701519077062806287447472524492800 

noncomputable def Ns288p144 := nat_lit 1129127829272032346255117093925369605621122581260785134769441198138906213561188830630477480955233041 

noncomputable def Ns288p145 := nat_lit 28464601717167958941395170629863244349336100071597067633311298952197840770862130016987296970159792803824401 

noncomputable def Ns288p146 := nat_lit 7448467992677518373281967829230802032816413886302607417429192074609666763379553167697198220060661538357248000 

noncomputable def Ns288p147 := BSN.sin_dyadic_bound_f 179636779 134217728 4 3 134217728 67108864 Ns288p142 Ns288p143 Ns288p144 Ns288p145 Ns288p146 Ns288p144 130609539 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 179636779) qz367 0 3 Ns288p142 Ns288p143 Ns288p144 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 179636779) qz368 0 3 Ns288p145 Ns288p146 Ns288p144 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz371 := (BSN.cos_quad_nat3 159 rfl)

noncomputable def Ns288p148 := Ns288p73 84685 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 114 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 12906900 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 130609539 134217728) qz9 rfl rfl (Ns288p135 rfl) (Ns288p106 rfl) RS289to300.d35 RS289to300.d37 RS289to300.d39 RS289to300.d41 RS289to300.d17 (Ns288p141 rfl rfl) (Ns288p147 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p149 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) 122406020 134217728 84685 134217728 122406020 134217728 84685 134217728 32858115795845120 30601505 16777216 84685 67108864 (Ns288p148 rfl) 

noncomputable def Ns288p150 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8) 5369225 16777216 1 16777216 2261559477855 4398046511104 94081580238911 219902325555200000 12142821687486012375 73786976294838206464 

noncomputable def Ns288p151 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz7 1 1 0 1 5369225 16777216 1 16777216 5369225 16777216 1 16777216 

noncomputable abbrev qz19 := qz348

noncomputable abbrev qz20 := (@Enclosure.Real.IsNear.of_eq qz348 (@HMul.hMul Real Real Real qz346 qz345 qz344) Bool.false 1599385289637 16777216000 598981 16777216000 (BSN.t_div_two_pi_mk qz345 598981 1000 qz351) (@Enclosure.Real.IsNear.mulLit_ff qz345 qz344 598981 1000 0 1 2670177 16777216 1 16777216 1599385289637 16777216000 598981 16777216000 (Enclosure.Real.IsNear.const Bool.false 598981 1000) RS289to300.d44 rfl))

noncomputable def Ns288p152 := @Enclosure.Real.IsNear.sqrt_image qz19 1599385289637 16777216000 598981 16777216000 81904246 81904278 8388608 qz20 

noncomputable abbrev qz716 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 598981 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz591 := qz716

noncomputable abbrev qz372 := qz591

noncomputable abbrev qz21 := qz372

noncomputable def Ns288p153 := @Enclosure.Real.IsNear.sqrt_image qz21 40952131 4194304 1 524288 26211879 26211885 8388608 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 163808524 16777216 32 16777216 40952131 4194304 1 524288 (Ns288p152 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz592 := (Real.sqrt qz716)

noncomputable abbrev qz373 := qz592

noncomputable abbrev qz22 := qz373

noncomputable def Ns288p154 := @Enclosure.Real.IsNear.inv_image qz22 13105941 4194304 3 8388608 2684612 2684613 8388608 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 52423764 16777216 6 16777216 13105941 4194304 3 8388608 (Ns288p153 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns288p155 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz22) Bool.false 5369225 16777216 1 16777216 5369225 16777216 1 16777216 (Ns288p154 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz23 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz350))

noncomputable abbrev qz593 := (@HMul.hMul Real Real Real qz708 qz711 qz711)

noncomputable abbrev qz594 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz374 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz593 qz583) qz594)

noncomputable abbrev qz24 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz374))

noncomputable def Ns288p156 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz8) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz23) qz24) Bool.false 2261559477855 

noncomputable def Ns288p157 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz23) qz24 6076635 524288 6925 

noncomputable def Ns288p158 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz23) Bool.false 194452320 16777216 27700 16777216 6076635 524288 6925 

noncomputable def Ns288p159 := @Enclosure.Real.IsNear.recentre' qz23 Bool.false 1447527 16777216 412388608 33554432000000 1447527 16777216 1610893 131072000000 

noncomputable abbrev qz25 := (@HMul.hMul Real Real Real qz346 qz343 qz350)

noncomputable def Ns288p160 := @Enclosure.Real.IsNear.cos_image qz25 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 80510097) qz365) Bool.false 80510097 16777216 101 8388608 Bool.false 1447527 16777216 1 

noncomputable def Ns288p161 := nat_lit 26986075412483664645461447 

noncomputable def Ns288p162 := nat_lit 2251799813685248000000000000000 

noncomputable def Ns288p163 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz8 884279719003555 140737488355328 1 500000000000000 3203395 4194304 1 524288 2832697230457393069225 590295810358705651712 Ns288p161 

noncomputable def Ns288p164 := @Enclosure.Real.IsNear.subLit_ff_p qz21 qz1 40952131 4194304 1 524288 9 1 0 1 3203395 3203395 4194304 1 

noncomputable abbrev qz375 := (Enclosure.Real.IsNear.const Bool.false 9 1)

noncomputable def Ns288p165 := @Ns288p164 524288 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 163808524 16777216 32 16777216 40952131 4194304 1 524288 (Ns288p152 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns288p166 := @Enclosure.Real.IsNear.recentre' qz25 Bool.false 2832697230457393069225 590295810358705651712 Ns288p161 Ns288p162 80510097 16777216 101 8388608 (@Ns288p163 Ns288p162 RS289to300.d43 (Ns288p165 rfl rfl) rfl) 

noncomputable def Ns288p167 := nat_lit 77622562803464754695461421366583544801 

noncomputable def Ns288p168 := nat_lit 167255588988979673561517887044862711294853120 

noncomputable def Ns288p169 := nat_lit 1170789122922857714930625209314038979063971840 

noncomputable abbrev qz376 := (BSN.sinEvenQ 34359738368)

noncomputable abbrev qz377 := (BSN.sinOddQ 34359738368)

noncomputable def Ns288p170 := BSN.sin_dyadic_bound_f 2968226201 34359738368 2 1 16777216 8007813 Ns288p167 Ns288p168 Ns288p167 Ns288p167 Ns288p169 Ns288p167 1447527 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 2968226201) qz376 0 1 Ns288p167 Ns288p168 Ns288p167 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 2968226201) qz377 0 1 Ns288p167 Ns288p169 Ns288p167 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p171 := @Ns288p160 4000000 (Ns288p166 rfl) (Enclosure.sfrac_false_div 80510097 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 80510097) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 208870350251384314527744) qz366) 226375608064910080 72057594037927936 Bool.false 1447527 16777216 0 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q3 80510097 16777216 226375608064910080 72057594037927936 0 208870350251384314527744 Ns288p93 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1447527 16777216 208870350251384314527744 Ns288p93 2968226201 34359738368 8007813 8000000 (Ns288p170 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p172 := @Enclosure.Real.IsNear.inv_image qz23 1447527 16777216 1610893 131072000000 97212310 97240010 8388608 (Ns288p159 (Ns288p171 rfl rfl) rfl) rfl 

noncomputable def Ns288p173 := @Enclosure.Real.IsNear.recentre' qz24 Bool.false 372173 8388608 

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz346 qz343 qz374)

noncomputable def Ns288p174 := @Enclosure.Real.IsNear.cos_image qz26 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 25608997)) qz365) Bool.true 25608997 16777216 

noncomputable def Ns288p175 := nat_lit 3779221013186207547613419205 

noncomputable def Ns288p176 := nat_lit 2475880078570760549798248448 

noncomputable def Ns288p177 := nat_lit 143041068997778294797916794384689 

noncomputable def Ns288p178 := @Enclosure.Real.IsNear.recentre' qz26 Bool.true Ns288p175 Ns288p176 Ns288p177 

noncomputable def Ns288p179 := nat_lit 4722366482869645213696000000000000000 

noncomputable abbrev qz27 := qz374

noncomputable def Ns288p180 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz27 884279719003555 140737488355328 1 500000000000000 4273784563831 

noncomputable abbrev qz378 := (@HSub.hSub Real Real Real qz584 qz593 qz583)

noncomputable abbrev qz28 := qz378

noncomputable abbrev qz379 := qz594

noncomputable abbrev qz29 := qz379

noncomputable def Ns288p181 := @Enclosure.Real.IsNear.subLit_tf qz28 qz29 3174272936055 17592186044416 5300551 1099511627776 1 16 

noncomputable abbrev qz380 := qz593

noncomputable abbrev qz30 := qz380

noncomputable def Ns288p182 := @Enclosure.Real.IsNear.subLit_ff_n qz30 qz8 10261739526025 17592186044416 3203399 1099511627776 3203395 4194304 1 524288 

noncomputable def Ns288p183 := @Enclosure.Real.IsNear.mulLit_ff qz8 qz8 3203395 4194304 1 524288 3203395 4194304 1 524288 10261739526025 17592186044416 

noncomputable def Ns288p184 := nat_lit 54057616473243610592530430463909462879393186009442743080538373713095769296499361408022516986321 

noncomputable def Ns288p185 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600 

noncomputable def Ns288p186 := nat_lit 79562941528436316622448692940963959636806501402399266879531440422709943564908364464255441 

noncomputable def Ns288p187 := nat_lit 327244937739901227599476514647770683946518593798528234076405718404588360419590411245595625124305 

noncomputable def Ns288p188 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600 

noncomputable abbrev qz595 := (BSN.cosEvenQ 16777216)

noncomputable def Ns288p189 := BSN.cos_dyadic_bound_f 25608997 16777216 4 3 8388608 4000000 Ns288p184 Ns288p185 Ns288p186 Ns288p187 Ns288p188 Ns288p186 372173 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 25608997) qz595 0 3 Ns288p184 Ns288p185 Ns288p186 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 25608997) (BSN.cosOddQ 16777216) 0 3 Ns288p187 Ns288p188 Ns288p186 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz381 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns288p190 := @Ns288p173 2052777216 67108864000000 372173 8388608 8018661 262144000000 (@Ns288p174 509 16777216 Bool.false 372173 8388608 1 4000000 (@Ns288p178 Ns288p179 25608997 16777216 509 16777216 (@Ns288p180 17592186044416 5300551 1099511627776 Ns288p175 Ns288p176 Ns288p177 Ns288p179 RS289to300.d43 (@Ns288p181 0 1 68380553021296 4273784563831 17592186044416 5300551 1099511627776 (@Ns288p182 13313865672787230720 3174272936055 17592186044416 5300551 1099511627776 (@Ns288p183 3203399 1099511627776 (Ns288p165 rfl rfl) (Ns288p165 rfl rfl) rfl) (Ns288p165 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 25608997 16777216) (BSN.cos_neg_of_bound 25608997 16777216 Bool.false 372173 8388608 1 4000000 (Ns288p189 rfl rfl)) rfl rfl) 

noncomputable abbrev qz31 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 9) (Enclosure.sfrac Bool.true 1 1) Bool.true 1 1 0 1 (BSN.neg_one_pow_odd_mk 9 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1))

noncomputable def Ns288p191 := @Ns288p150 252629172356869951443 Ns288p69 (Ns288p151 qz31 (@Enclosure.Real.IsNear.of_eq qz7 (@Inv.inv Real Real.instInv qz22) Bool.false 5369225 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz19 (BSN.t_div_two_pi_nonneg qz4 598981 1000 qz9)) Ns288p155) rfl) (@Ns288p156 4398046511104 94081580238911 219902325555200000 (BSN.correction_mk qz8 (BSN.cos_two_pi_p_ne_zero_mk qz4 598981 1000 9 qz9 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 598981 1000 9 qz9 rfl rfl rfl))) (@Ns288p157 4194304 372173 8388608 8018661 262144000000 2261559477855 4398046511104 94081580238911 219902325555200000 (@Ns288p158 4194304 (Ns288p172 rfl rfl rfl rfl rfl) rfl) (Ns288p190 rfl) rfl)) 

noncomputable abbrev qz32 := qz352

noncomputable def Ns288p192 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 122444020612295599145 73786976294838206464 2580432727312133951443 Ns288p69 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8))) Bool.true 122444020612295599145 73786976294838206464 2580432727312133951443 Ns288p69 (BSN.hardyZApproximantRS₀_eq qz4 9 (@BSN.floor_sqrt_eq_dec qz4 598981 1000 9 qz9 rfl rfl rfl)) (@Ns288p71 122444020612295599145 73786976294838206464 2580432727312133951443 Ns288p69 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9)) Bool.true 30601505 16777216 84685 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (Ns288p149 (Ns288p148 rfl) rfl rfl)) (Ns288p191 rfl) rfl rfl)) 

theorem RS289to300.d45 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 122444020612295599145 73786976294838206464 2580432727312133951443 Ns288p69 := Ns288p192 

theorem RS289to300.d46 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS289to300.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS289to300.d3 a b h)) 

noncomputable def Ns288p193 := nat_lit 9223372036854775808000000 

noncomputable def Ns288p194 := nat_lit 39481663441656390080786333696 

noncomputable abbrev qz717 := (Enclosure.sfrac Bool.false 600359 1000)

noncomputable abbrev qz596 := qz717

noncomputable abbrev qz382 := qz596

noncomputable abbrev qz33 := qz382

noncomputable abbrev qz718 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 600359 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz597 := qz718

noncomputable abbrev qz383 := qz597

noncomputable abbrev qz34 := (@HPow.hPow Real Real Real qz347 qz383 qz349)

noncomputable abbrev qz719 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 600359 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz598 := qz719

noncomputable abbrev qz384 := qz598

noncomputable abbrev qz35 := qz384

noncomputable def Ns288p195 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz33) qz33 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz34) (Zeta.RiemannSiegel.correction qz35)) 256236255 67108864 84879 67108864 24853147484811460529 147573952589676412928 705586798230361887499 Ns288p193 Ns288p194 

noncomputable def Ns288p196 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 600359 1000 114 159 134217728 67108864 2251799813685248 Bool.false 143363527498 1839 

noncomputable def Ns288p197 := Ns288p196 279097919 34 47453128 8 294906479 34 44739240 8 Bool.false 231372553 69575 Bool.true 160946643 Bool.true 164465780 7074237752028440 1 Bool.false 48741656 Bool.true Bool.false 126289443 Bool.false Bool.false 256236255 

noncomputable def Ns288p198 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 600359 1000 4 63 134217728 67108864 2251799813685248 Bool.false 143363527498 1839 

noncomputable def Ns288p199 := Ns288p198 240485871 35 54794152 8 261175631 35 50729528 8 Bool.false 169199027 51589 Bool.true 171014673 Bool.true 153404163 7074237752028440 1 Bool.false 39232705 Bool.false Bool.false 122119540 Bool.false Bool.false 231372553 

noncomputable def Ns288p200 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 600359 1000 150 64 134217728 67108864 2251799813685248 Bool.false 143363527498 1839 

noncomputable def Ns288p201 := Ns288p200 186065264 34 67108856 8 216015088 34 60023992 8 Bool.false 222289641 30492 Bool.false 33264548 Bool.false 183887576 7074237752028440 1 Bool.false 130116638 Bool.true Bool.false 26760586 Bool.false Bool.false 169199027 

noncomputable def Ns288p202 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 600359 1000 415 260 134217728 67108864 2251799813685248 Bool.false 143363527498 1839 

noncomputable def Ns288p203 := Ns288p202 93032624 34 94906264 8 147453232 34 77490640 16 Bool.false 134217720 1882 Bool.false 16638020 Bool.false 23186913 7074237752028440 1 Bool.false 16595440 Bool.false Bool.false 132219865 Bool.false Bool.false 222289641 

noncomputable def Ns288p204 := nat_lit 101360359146250842521200536656706361054533391807129732297 

noncomputable def Ns288p205 := nat_lit 94894129289957749424330575450941446491021373551411200 

noncomputable def Ns288p206 := nat_lit 37436662845722919110557647583520000 

noncomputable def Ns288p207 := nat_lit 134852668466518465243567810959662902080 

noncomputable abbrev qz599 := (@Eq.refl Real qz717)

noncomputable abbrev qz385 := qz599

noncomputable abbrev qz36 := qz385

noncomputable def Ns288p208 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz33 600359 1000 1441724715524 16000000 1200718 4000 2000 Ns288p206 Ns288p207 qz36 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns288p209 := nat_lit 32435314926800269606784171730146035537450685378281514335040 

noncomputable abbrev qz600 := (@HSub.hSub Real Real Real qz712 qz713 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz714 (@Nat.cast Real Real.instNatCast 1200718))))

noncomputable abbrev qz386 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz580 (Enclosure.sfrac Bool.false 600359 4000) (Real.log (Enclosure.sfrac Bool.false 1441724715524 16000000))) (@HMul.hMul Real Real Real qz580 qz585 qz600))

noncomputable abbrev qz601 := (Enclosure.sfrac Bool.false 600359 2000)

noncomputable abbrev qz37 := (@HSub.hSub Real Real Real qz352 (@HSub.hSub Real Real Real qz352 qz386 qz601) (@HMul.hMul Real Real Real qz346 qz601 (Real.log Real.pi)))

noncomputable def Ns288p210 := @Enclosure.Real.IsNear.addLit_ft_p qz37 (Enclosure.sfrac Bool.true Ns288p206 Ns288p207) 240524149248410530113 225179981368524800 28055251603943803 2048000000000000000000 Ns288p206 Ns288p207 0 1 Ns288p209 

noncomputable def Ns288p211 := nat_lit 80706512103136422407606108160000 

noncomputable abbrev qz38 := (@HSub.hSub Real Real Real qz352 qz386 qz601)

noncomputable def Ns288p212 := @Enclosure.Real.IsNear.subLit_ff_p qz38 (@HMul.hMul Real Real Real qz5 qz601 (Real.log Real.pi)) 1589507475457491924549 1125899906842624000 4752807089061 1000000000000000000 23060246063199 67108864000 600359 67108864000 Ns288p211 240524149248410530113 225179981368524800 

noncomputable def Ns288p213 := nat_lit 3179014950914983849098000 

noncomputable abbrev qz39 := qz386

noncomputable def Ns288p214 := @Enclosure.Real.IsNear.subLit_ff_p qz39 qz601 1927479546543557375557 1125899906842624000 4752807089061 1000000000000000000 600359 2000 0 1 Ns288p213 1589507475457491924549 1125899906842624000 4752807089061 1000000000000000000 

noncomputable def Ns288p215 := nat_lit 4340298083788908798943902975326683136 

noncomputable def Ns288p216 := nat_lit 27584693776762247384662016 

noncomputable def Ns288p217 := nat_lit 1397803602469731854691423048465651464544813212288232871317595671686774896453805417532215037919084216320 

noncomputable def Ns288p218 := nat_lit 11789559064944847890502288969808950544404936252826838141942517273093133019037696337450053256039890944 

noncomputable def Ns288p219 := nat_lit 59929987603590168908390250330148594984495287107688461270715242653804901288039682280885800468480 

noncomputable def Ns288p220 := BSN.log_dyadic_bound 393148715524 2490300715524 5 4 Ns288p217 67108864 32000000 Ns288p218 Ns288p219 21367936 2883449431048 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 393148715524) (BSN.artanhQ 2490300715524) 0 4 Ns288p218 Ns288p217 Ns288p219 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz387 := (Real.log (Enclosure.sfrac Bool.false 1441724715524 16000000))

noncomputable def Ns288p221 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 600359 4000) qz387 600359 4000 0 1 3211281003519223 281474976710656 976563 31250000000000 1927921451991797201057 1125899906842624000 586288386117 125000000000000000 (Enclosure.Real.IsNear.const Bool.false 600359 4000) (BSN.isNear_log_sfrac 1441724715524 16000000 3211281003519223 281474976710656 976563 31250000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1441724715524) qz355)) Bool.false Ns288p216 Ns288p93 1000000512000000 32000000000000000000000 3211281003519223 281474976710656 976563 31250000000000 (BSN.log_rat_reduce_isNear 1441724715524 16000000 16 2883449431048 2097152000000 21367936 67108864 24973259072661432 36028797018963968 32000000 1000000000000000 rfl rfl rfl rfl (Ns288p220 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns288p222 := BSN.arctan_dyadic_bound_f 1000 1200718 1 0 8388608 4000000 0 1 1 0 1 1 6986 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1200718) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1200718) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz388 := (@Nat.cast Real Real.instNatCast 1200718)

noncomputable def Ns288p223 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz388)) 884279719003555 562949953421312 1 2000000000000000 6986 8388608 1 4000000 7413943156696372215808 883810896479651 562949953421312 500000001 2000000000000000 qz15 (Ns288p222 rfl) rfl rfl 

noncomputable abbrev qz389 := (@HMul.hMul Real Real Real qz580 qz585 qz600)

noncomputable abbrev qz40 := qz389

noncomputable abbrev qz390 := qz600

noncomputable abbrev qz41 := qz390

noncomputable def Ns288p224 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 600359 4000) qz387) qz40 1927921451991797201057 1125899906842624000 586288386117 125000000000000000 883810896479651 2251799813685248 500000001 8000000000000000 Ns288p215 1927479546543557375557 1125899906842624000 4752807089061 1000000000000000000 (Ns288p221 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz41 1 4 0 1 883810896479651 562949953421312 500000001 2000000000000000 883810896479651 2251799813685248 500000001 8000000000000000 qz363 Ns288p223 rfl) 

noncomputable def Ns288p225 := @Ns288p210 Ns288p204 Ns288p205 28055251603943803 2048000000000000000000 (@Ns288p212 28055251603943803 2048000000000000000000 (Ns288p214 (Ns288p224 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 600359 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz601 (Real.log Real.pi) 600359 2000 0 1 38410761 33554432 1 33554432 23060246063199 67108864000 600359 67108864000 (Enclosure.Real.IsNear.const Bool.false 600359 2000) RS289to300.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns288p206 Ns288p207) 

noncomputable def Ns288p226 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz33) Bool.false Ns288p204 Ns288p205 28055251603943803 2048000000000000000000 17920440937 16777216 231 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz33) (@HAdd.hAdd Real Real Real qz364 qz37 (Enclosure.sfrac Bool.true Ns288p206 Ns288p207)) Bool.false Ns288p204 Ns288p205 28055251603943803 2048000000000000000000 Ns288p208 (Ns288p225 rfl rfl)) 

noncomputable def Ns288p227 := nat_lit 3797986438948034072018944 

noncomputable def Ns288p228 := nat_lit 857168293503875079262200427533387188297959804241400123859401660966894365656948526138233222153633977559803972579751669912120945322561536 

noncomputable def Ns288p229 := nat_lit 16860812360175734222210805034837902731874731588140993779854824115686058269364094835627812361599730584878593258197117225559879026789580800 

noncomputable def Ns288p230 := nat_lit 611059232238779256692221943699288503684322627093053668019969188364403856478269130035943621053586852945003023325769862886029070336 

noncomputable def Ns288p231 := nat_lit 4280515590414095748359382765243401302680699984061095709470560555310350969377790575272184945263177243233154826480901899130408589277597696 

noncomputable def Ns288p232 := nat_lit 590128432606150697777378176219326595615615605584934782294918844049012039427743319246973432655990570470750764036899102894595765937635328000 

noncomputable def Ns288p233 := BSN.sin_dyadic_bound_f 53972633494 34359738368 4 3 16777216 8007813 Ns288p228 Ns288p229 Ns288p230 Ns288p231 Ns288p232 Ns288p230 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53972633494) qz376 0 3 Ns288p228 Ns288p229 Ns288p230 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53972633494) qz377 0 3 Ns288p231 Ns288p232 Ns288p230 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p234 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz33) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17920440937) qz365) Bool.false 17920440937 16777216 231 16777216 Bool.false 16777215 16777216 1 4000000 (Ns288p226 rfl) (Enclosure.sfrac_false_div 17920440937 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17920440937) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns288p227) qz366) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 169 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q3 17920440937 16777216 226375608064910080 72057594037927936 169 Ns288p227 Ns288p93 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns288p227 Ns288p93 53972633494 34359738368 8007813 8000000 (Ns288p233 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p235 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz33) Bool.false Ns288p204 Ns288p205 28055251603943803 2048000000000000000000 143363527498 134217728 1839 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz33) (@HAdd.hAdd Real Real Real qz364 qz37 (Enclosure.sfrac Bool.true Ns288p206 Ns288p207)) Bool.false Ns288p204 Ns288p205 28055251603943803 2048000000000000000000 Ns288p208 (Ns288p225 rfl rfl)) 

noncomputable def Ns288p236 := Ns288p203 30492 BSN.abs_quadSignPos (BSN.cos_quad_nat3 415 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 16595440 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 260 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 132219865 134217728) qz36 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 1) Bool.false 16777215 16777216 3674911 262144000000 134217720 134217728 1882 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz33)) Bool.false 16777215 16777216 3674911 262144000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz33) qz33) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz33)) Bool.false 16777215 16777216 940777216 67108864000000 16777215 16777216 3674911 262144000000 (Ns288p234 rfl rfl) rfl)) rfl) (Ns288p235 rfl) RS289to300.d7 

noncomputable def Ns288p237 := nat_lit 76631366152634797598016160000 

noncomputable def Ns288p238 := BSN.sin_dyadic_bound_f 16638020 134217728 2 1 134217728 67108864 Ns288p237 Ns288p115 Ns288p237 Ns288p237 Ns288p116 Ns288p237 16595440 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 16638020) qz367 0 1 Ns288p237 Ns288p115 Ns288p237 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 16638020) qz368 0 1 Ns288p237 Ns288p116 Ns288p237 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p239 := nat_lit 289049172226359874591387045761 

noncomputable def Ns288p240 := BSN.cos_dyadic_bound_f 23186913 134217728 2 1 134217728 67108864 Ns288p239 Ns288p132 Ns288p239 Ns288p239 Ns288p133 Ns288p239 132219865 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 23186913) qz369 0 1 Ns288p239 Ns288p132 Ns288p239 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 23186913) qz370 0 1 Ns288p239 Ns288p133 Ns288p239 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p241 := nat_lit 1224408980924087016812151644416 

noncomputable def Ns288p242 := BSN.cos_dyadic_bound_f 33264548 134217728 2 1 134217728 67108864 Ns288p241 Ns288p132 Ns288p241 Ns288p241 Ns288p133 Ns288p241 130116638 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 33264548) qz369 0 1 Ns288p241 Ns288p132 Ns288p241 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 33264548) qz370 0 1 Ns288p241 Ns288p133 Ns288p241 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p243 := nat_lit 2408377158770864315489322977600686675654624562042838101572634948608516926131007026383509741092538161299456 

noncomputable def Ns288p244 := nat_lit 1494956844139656118510993175133542066212223771057568366754371062289258620997546538563271874131787776 

noncomputable def Ns288p245 := nat_lit 14590427764807460731983275499804075814476664997109040370359487770814317123690089481939950030101272204410880 

noncomputable def Ns288p246 := BSN.cos_dyadic_bound_f 183887576 134217728 4 3 134217728 67108864 Ns288p243 Ns288p137 Ns288p244 Ns288p245 Ns288p140 Ns288p244 26760586 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 183887576) qz369 0 3 Ns288p243 Ns288p137 Ns288p244 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 183887576) qz370 0 3 Ns288p245 Ns288p140 Ns288p244 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p247 := Ns288p201 51589 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 150 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 130116638 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 26760586 134217728) qz36 rfl rfl (Ns288p236 RS289to300.d9 RS289to300.d11 RS289to300.d13 RS289to300.d17 (Ns288p238 rfl rfl) (Ns288p240 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns288p235 rfl) RS289to300.d19 RS289to300.d21 RS289to300.d23 RS289to300.d25 RS289to300.d17 (Ns288p242 rfl rfl) (Ns288p246 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns288p248 := nat_lit 1800608301386832673920448018845610096585897720105732823011795521536725795587790602088557140047635250232001 

noncomputable def Ns288p249 := nat_lit 625749471803975764165042642728018721548816456733868713251984729842664455161267779419122776945801921 

noncomputable def Ns288p250 := nat_lit 10912279918131096207192331090433176092114678755237672929588065871827749033202313856881381964772998892042945 

noncomputable def Ns288p251 := BSN.cos_dyadic_bound_f 171014673 134217728 4 3 134217728 67108864 Ns288p248 Ns288p137 Ns288p249 Ns288p250 Ns288p140 Ns288p249 39232705 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 171014673) qz369 0 3 Ns288p248 Ns288p137 Ns288p249 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 171014673) qz370 0 3 Ns288p250 Ns288p140 Ns288p249 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p252 := nat_lit 543769586162231617055736336326192924590825187202656555134778291724705 

noncomputable def Ns288p253 := nat_lit 306688268365036596318149637066253321300736442516919964588747465121 

noncomputable def Ns288p254 := nat_lit 1423661897038015604466222924299064678074817155100025488267466125287841 

noncomputable def Ns288p255 := BSN.sin_dyadic_bound_f 153404163 134217728 3 2 134217728 67108864 Ns288p252 Ns288p109 Ns288p253 Ns288p254 Ns288p112 Ns288p253 122119540 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 153404163) qz367 0 2 Ns288p252 Ns288p109 Ns288p253 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 153404163) qz368 0 2 Ns288p254 Ns288p112 Ns288p253 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p256 := Ns288p199 69575 BSN.abs_quadSignPos (BSN.cos_quad_nat0 4 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 39232705 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 122119540 134217728) qz36 rfl rfl (Ns288p247 rfl rfl) (Ns288p235 rfl) RS289to300.d27 RS289to300.d29 RS289to300.d31 RS289to300.d33 RS289to300.d17 (Ns288p251 rfl rfl) (Ns288p255 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p257 := nat_lit 1412104248861366897405248382455531229774227419840882024968901163808504594163106876311670931445368009650481 

noncomputable def Ns288p258 := nat_lit 302122501598893229284622636971481884739151483494992268631625824110052951811826186182069779812970801 

noncomputable def Ns288p259 := nat_lit 8559743710362685932984178969696521718734536324140266885941306311482229002073189941308310273245316716032305 

noncomputable def Ns288p260 := BSN.cos_dyadic_bound_f 160946643 134217728 4 3 134217728 67108864 Ns288p257 Ns288p137 Ns288p258 Ns288p259 Ns288p140 Ns288p258 48741656 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 160946643) qz369 0 3 Ns288p257 Ns288p137 Ns288p258 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 160946643) qz370 0 3 Ns288p259 Ns288p140 Ns288p258 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p261 := nat_lit 718533772273843585357634537406121832247591677916626204027625840640000 

noncomputable def Ns288p262 := nat_lit 535308812011998183004575376331685869245052494640952434713600000000 

noncomputable def Ns288p263 := nat_lit 1881007475021570916973702094978163021622057642885554706606626611200000 

noncomputable def Ns288p264 := BSN.sin_dyadic_bound_f 164465780 134217728 3 2 134217728 67108864 Ns288p261 Ns288p109 Ns288p262 Ns288p263 Ns288p112 Ns288p262 126289443 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 164465780) qz367 0 2 Ns288p261 Ns288p109 Ns288p262 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 164465780) qz368 0 2 Ns288p263 Ns288p112 Ns288p262 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p265 := Ns288p197 84879 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 114 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 48741656 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 126289443 134217728) qz36 rfl rfl (Ns288p256 rfl) (Ns288p235 rfl) RS289to300.d35 RS289to300.d37 RS289to300.d39 RS289to300.d41 RS289to300.d17 (Ns288p260 rfl rfl) (Ns288p264 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p266 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 9) 256236255 134217728 84879 134217728 256236255 134217728 84879 134217728 68782895954657280 256236255 67108864 84879 67108864 (Ns288p265 rfl) 

noncomputable def Ns288p267 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz34) (Zeta.RiemannSiegel.correction qz35) 5366141 16777216 1 16777216 4631474924869 8796093022208 262869425016169 1099511627776000000 24853147484811460529 147573952589676412928 

noncomputable def Ns288p268 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz34 1 1 0 1 5366141 16777216 1 16777216 5366141 16777216 1 16777216 

noncomputable abbrev qz42 := qz383

noncomputable def Ns288p269 := @Enclosure.Real.IsNear.sqrt_image qz42 1603064793543 16777216000 600359 16777216000 81998405 81998437 8388608 (@Enclosure.Real.IsNear.of_eq qz42 (@HMul.hMul Real Real Real qz5 qz33 qz3) Bool.false 1603064793543 16777216000 600359 16777216000 (BSN.t_div_two_pi_mk qz33 600359 1000 qz36) (@Enclosure.Real.IsNear.mulLit_ff qz33 qz3 600359 1000 0 1 2670177 16777216 1 16777216 1603064793543 16777216000 600359 16777216000 (Enclosure.Real.IsNear.const Bool.false 600359 1000) RS289to300.d44 rfl)) 

noncomputable abbrev qz720 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 600359 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz602 := qz720

noncomputable abbrev qz391 := qz602

noncomputable abbrev qz43 := qz391

noncomputable def Ns288p270 := @Enclosure.Real.IsNear.sqrt_image qz43 81998421 8388608 1 524288 26226941 26226947 8388608 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 163996842 16777216 32 16777216 81998421 8388608 1 524288 (Ns288p269 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns288p271 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz43) 102449 32768 3 8388608 2683070 2683071 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz43) Bool.false 52453888 16777216 6 16777216 102449 32768 3 8388608 (Ns288p270 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns288p272 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz43)) Bool.false 5366141 16777216 1 16777216 5366141 16777216 1 16777216 (Ns288p271 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz44 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz384))

noncomputable abbrev qz603 := (@HMul.hMul Real Real Real qz708 qz719 qz719)

noncomputable abbrev qz392 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz603 qz598) qz594)

noncomputable abbrev qz45 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz392))

noncomputable def Ns288p273 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz35) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz44) qz45) Bool.false 4631474924869 

noncomputable def Ns288p274 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz44) qz45 53680211 8388608 2111 

noncomputable def Ns288p275 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz44) Bool.false 107360422 16777216 8444 16777216 53680211 8388608 2111 

noncomputable def Ns288p276 := @Enclosure.Real.IsNear.recentre' qz44 Bool.false 2621776 16777216 412388608 33554432000000 163861 1048576 1610893 131072000000 

noncomputable abbrev qz46 := (@HMul.hMul Real Real Real qz346 qz343 qz384)

noncomputable abbrev qz393 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable def Ns288p277 := @Enclosure.Real.IsNear.cos_image qz46 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40846667) qz393) Bool.false 40846667 8388608 101 8388608 Bool.false 2621776 16777216 1 

noncomputable def Ns288p278 := nat_lit 5397215082506843174732891 

noncomputable def Ns288p279 := nat_lit 450359962737049600000000000000 

noncomputable def Ns288p280 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz35 884279719003555 140737488355328 1 500000000000000 6500949 8388608 1 524288 5748657354976441873695 1180591620717411303424 Ns288p278 

noncomputable def Ns288p281 := @Enclosure.Real.IsNear.subLit_ff_p qz43 qz1 81998421 8388608 1 524288 9 1 0 1 6500949 6500949 8388608 1 

noncomputable def Ns288p282 := @Ns288p281 524288 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 163996842 16777216 32 16777216 81998421 8388608 1 524288 (Ns288p269 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns288p283 := @Enclosure.Real.IsNear.recentre' qz46 Bool.false 5748657354976441873695 1180591620717411303424 Ns288p278 Ns288p279 40846667 8388608 101 8388608 (@Ns288p280 Ns288p279 RS289to300.d43 (Ns288p282 rfl rfl) rfl) 

noncomputable def Ns288p284 := nat_lit 1208925819614629174706176 

noncomputable def Ns288p285 := nat_lit 844961678885164647610539181309869059041 

noncomputable def Ns288p286 := BSN.sin_dyadic_bound_f 5391495577 34359738368 2 1 16777216 8007813 Ns288p285 Ns288p168 Ns288p285 Ns288p285 Ns288p169 Ns288p285 2621776 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 5391495577) qz376 0 1 Ns288p285 Ns288p168 Ns288p285 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 5391495577) qz377 0 1 Ns288p285 Ns288p169 Ns288p285 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz394 := (@Nat.cast Real Real.instNatCast Ns288p284)

noncomputable def Ns288p287 := @Ns288p277 4000000 (Ns288p283 rfl) (Enclosure.sfrac_false_div 40846667 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40846667) qz393) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 189696386522347894472704) qz394) 226375608064910080 72057594037927936 Bool.false 2621776 16777216 0 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q3 40846667 8388608 226375608064910080 72057594037927936 0 189696386522347894472704 Ns288p284 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2621776 16777216 189696386522347894472704 Ns288p284 5391495577 34359738368 8007813 8000000 (Ns288p286 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p288 := @Enclosure.Real.IsNear.inv_image qz44 163861 1048576 1610893 131072000000 53675989 53684433 8388608 (Ns288p276 (Ns288p287 rfl rfl) rfl) rfl 

noncomputable def Ns288p289 := @Enclosure.Real.IsNear.recentre' qz45 Bool.false 690232 8388608 

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz346 qz343 qz392)

noncomputable def Ns288p290 := @Enclosure.Real.IsNear.cos_image qz47 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 24971561)) qz365) Bool.true 24971561 16777216 

noncomputable def Ns288p291 := nat_lit 14740608127041085845980204725 

noncomputable def Ns288p292 := nat_lit 9903520314283042199192993792 

noncomputable def Ns288p293 := nat_lit 288623119869882544060616699660107 

noncomputable def Ns288p294 := @Enclosure.Real.IsNear.recentre' qz47 Bool.true Ns288p291 Ns288p292 Ns288p293 

noncomputable def Ns288p295 := nat_lit 9444732965739290427392000000000000000 

noncomputable abbrev qz48 := qz392

noncomputable def Ns288p296 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz48 884279719003555 140737488355328 1 500000000000000 16669621399495 

noncomputable abbrev qz395 := (@HSub.hSub Real Real Real qz584 qz603 qz598)

noncomputable abbrev qz49 := qz395

noncomputable def Ns288p297 := @Enclosure.Real.IsNear.subLit_tf qz49 qz29 12271574888391 70368744177664 10695261 2199023255552 1 16 

noncomputable abbrev qz396 := qz603

noncomputable abbrev qz50 := qz396

noncomputable def Ns288p298 := @Enclosure.Real.IsNear.subLit_ff_n qz50 qz35 42262337900601 70368744177664 6500957 2199023255552 6500949 8388608 1 524288 

noncomputable def Ns288p299 := @Enclosure.Real.IsNear.mulLit_ff qz35 qz35 6500949 8388608 1 524288 6500949 8388608 1 524288 42262337900601 70368744177664 

noncomputable def Ns288p300 := nat_lit 48857932460844383919988723494425446295711479611328458772992613969178761161534704296464937480801 

noncomputable def Ns288p301 := nat_lit 58796069848409358247000764605662563545983093438991546930619512768335746212847784772596321 

noncomputable def Ns288p302 := nat_lit 295828892833174481334263074241603136072200520854109110132755916918160675223564521148371905376865 

noncomputable def Ns288p303 := BSN.cos_dyadic_bound_f 24971561 16777216 4 3 8388608 4000000 Ns288p300 Ns288p185 Ns288p301 Ns288p302 Ns288p188 Ns288p301 690232 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 24971561) qz595 0 3 Ns288p300 Ns288p185 Ns288p301 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 24971561) (BSN.cosOddQ 16777216) 0 3 Ns288p302 Ns288p188 Ns288p301 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p304 := @Ns288p289 1036388608 33554432000000 86279 1048576 4048393 131072000000 (@Ns288p290 257 8388608 Bool.false 690232 8388608 1 4000000 (@Ns288p294 Ns288p295 24971561 16777216 257 8388608 (@Ns288p296 70368744177664 10695261 2199023255552 Ns288p291 Ns288p292 Ns288p293 Ns288p295 RS289to300.d43 (@Ns288p297 0 1 266713942391920 16669621399495 70368744177664 10695261 2199023255552 (@Ns288p298 102941431281355849728 12271574888391 70368744177664 10695261 2199023255552 (@Ns288p299 6500957 2199023255552 (Ns288p282 rfl rfl) (Ns288p282 rfl rfl) rfl) (Ns288p282 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 24971561 16777216) (BSN.cos_neg_of_bound 24971561 16777216 Bool.false 690232 8388608 1 4000000 (Ns288p303 rfl rfl)) rfl rfl) 

noncomputable def Ns288p305 := @Ns288p267 705586798230361887499 Ns288p193 (Ns288p268 qz31 (@Enclosure.Real.IsNear.of_eq qz34 (@Inv.inv Real Real.instInv (Real.sqrt qz43)) Bool.false 5366141 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz42 (BSN.t_div_two_pi_nonneg qz33 600359 1000 qz36)) Ns288p272) rfl) (@Ns288p273 8796093022208 262869425016169 1099511627776000000 (BSN.correction_mk qz35 (BSN.cos_two_pi_p_ne_zero_mk qz33 600359 1000 9 qz36 rfl rfl (@BSN.floor_sqrt_eq_dec qz33 600359 1000 9 qz36 rfl rfl rfl))) (@Ns288p274 4194304 86279 1048576 4048393 131072000000 4631474924869 8796093022208 262869425016169 1099511627776000000 (@Ns288p275 4194304 (Ns288p288 rfl rfl rfl rfl rfl) rfl) (Ns288p304 rfl) rfl)) 

noncomputable def Ns288p306 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz33) (hardyZApproximantRS₀ qz33) Bool.false 588322631145363898289 147573952589676412928 12371267729980249887499 Ns288p193 (@Eq.refl Real (hardyZApproximantRS₀ qz33)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz33) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz33) qz33 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz34) (Zeta.RiemannSiegel.correction qz35))) Bool.false 588322631145363898289 147573952589676412928 12371267729980249887499 Ns288p193 (BSN.hardyZApproximantRS₀_eq qz33 9 (@BSN.floor_sqrt_eq_dec qz33 600359 1000 9 qz36 rfl rfl rfl)) (@Ns288p195 588322631145363898289 147573952589676412928 12371267729980249887499 Ns288p193 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz33) qz33 9) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 9)) Bool.false 256236255 67108864 84879 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz33) qz33 9) (Ns288p266 (Ns288p265 rfl) rfl rfl)) (Ns288p305 rfl) rfl rfl)) 

theorem RS289to300.d47 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz33) Bool.false 588322631145363898289 147573952589676412928 12371267729980249887499 Ns288p193 := Ns288p306 

noncomputable abbrev qz604 := (@HMul.hMul Real Real Real qz708 (Real.sqrt qz716) qz710)

noncomputable abbrev qz397 := qz604

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv qz397)

noncomputable abbrev qz398 := (@HMul.hMul Real Real Real qz580 (@HMul.hMul Real Real Real qz580 qz604 qz604) qz604)

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz346 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz398))

noncomputable abbrev qz399 := (@HMul.hMul Real Real Real qz580 qz592 qz592)

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz346 qz399 qz373))

noncomputable abbrev qz605 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz51)

noncomputable def Ns288p307 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz364 (@HAdd.hAdd Real Real Real qz364 qz605 qz52) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz53)) Bool.false 

noncomputable def Ns288p308 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz364 qz605 qz52) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz53) 11264601 536870912 

noncomputable def Ns288p309 := @Enclosure.Real.IsNear.addLit_ff qz605 qz52 1408075 67108864 25 67108864 

noncomputable def Ns288p310 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz51 25 4 0 1 56323 16777216 1 16777216 1408075 

noncomputable def Ns288p311 := @Enclosure.Real.IsNear.recentre' qz51 Bool.false 56323 16777216 1 16777216 56323 16777216 1 16777216 

noncomputable def Ns288p312 := @Enclosure.Real.IsNear.mulLit_ff qz22 qz19 13105941 4194304 3 8388608 1599385289637 16777216000 598981 16777216000 20961449242250433417 70368744177664000 1281161059881 

noncomputable def Ns288p313 := @Enclosure.Real.IsNear.sqrt_image qz19 1599385289637 16777216000 598981 16777216000 81904246 81904278 8388608 qz20 

noncomputable def Ns288p314 := @Enclosure.Real.IsNear.sqrt_image qz21 40952131 4194304 1 524288 26211879 26211885 8388608 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 163808524 16777216 32 16777216 40952131 4194304 1 524288 (Ns288p313 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz400 := (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 52423764 16777216 6 16777216 13105941 4194304 3 8388608 (Ns288p314 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns288p315 := @Ns288p312 8796093022208000 qz400 

noncomputable def Ns288p316 := Ns288p315 qz20 

noncomputable abbrev qz54 := qz397

noncomputable def Ns288p317 := @Enclosure.Real.IsNear.inv_image qz54 20961449242250433417 70368744177664000 1281161059881 8796093022208000 28161 28162 8388608 (Ns288p316 rfl) rfl rfl 

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv qz398)

noncomputable def Ns288p318 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz55 1 32 0 1 1 

noncomputable def Ns288p319 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 1 16777216 1 16777216 

noncomputable def Ns288p320 := nat_lit 9210090918342846832091481933176872428957520937842443322713 

noncomputable def Ns288p321 := nat_lit 348449143727040986586495598010130648530944000000000 

noncomputable def Ns288p322 := nat_lit 1688759514054040240797457469456700091031651534852739 

noncomputable def Ns288p323 := nat_lit 43556142965880123323311949751266331066368000000000 

noncomputable abbrev qz56 := qz398

noncomputable def Ns288p324 := @Enclosure.Real.IsNear.inv_image qz56 Ns288p320 Ns288p321 Ns288p322 Ns288p323 0 1 

noncomputable def Ns288p325 := nat_lit 439382354335441269281954956724350295889 

noncomputable def Ns288p326 := nat_lit 4951760157141521099596496896000000 

noncomputable def Ns288p327 := nat_lit 26854999093337995023784411380021 

noncomputable def Ns288p328 := nat_lit 309485009821345068724781056000000 

noncomputable abbrev qz401 := (@HMul.hMul Real Real Real qz580 qz604 qz604)

noncomputable abbrev qz57 := qz401

noncomputable def Ns288p329 := @Enclosure.Real.IsNear.mulLit_ff qz57 qz54 Ns288p325 Ns288p326 Ns288p327 Ns288p328 20961449242250433417 70368744177664000 1281161059881 

noncomputable def Ns288p330 := @Enclosure.Real.IsNear.mulLit_ff qz54 qz54 20961449242250433417 70368744177664000 1281161059881 8796093022208000 20961449242250433417 70368744177664000 1281161059881 8796093022208000 Ns288p325 

noncomputable def Ns288p331 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz53 13 10 0 1 549915 16777216 1 

noncomputable def Ns288p332 := @Enclosure.Real.IsNear.recentre' qz53 Bool.false 549915 16777216 1 16777216 549915 16777216 

noncomputable abbrev qz58 := qz399

noncomputable def Ns288p333 := @Enclosure.Real.IsNear.mulLit_ff qz58 qz22 171765689495481 17592186044416 157271301 70368744177664 13105941 4194304 3 8388608 2251150992352093752621 

noncomputable def Ns288p334 := @Enclosure.Real.IsNear.mulLit_ff qz22 qz22 13105941 4194304 3 8388608 13105941 4194304 3 8388608 171765689495481 17592186044416 157271301 

noncomputable def Ns288p335 := @Ns288p334 70368744177664 qz400 

noncomputable def Ns288p336 := Ns288p335 qz400 

noncomputable def Ns288p337 := @Ns288p333 73786976294838206464 6183565529558157 590295810358705651712 (Ns288p336 rfl) qz400 

noncomputable abbrev qz59 := (@HMul.hMul Real Real Real qz346 qz399 qz373)

noncomputable def Ns288p338 := @Enclosure.Real.IsNear.inv_image qz59 2251150992352093752621 73786976294838206464 6183565529558157 590295810358705651712 274957 274958 8388608 (Ns288p337 rfl) 

noncomputable def Ns288p339 := @Ns288p308 201 536870912 1429779 33554432 13 167772160 1145584043950080 34141065 536870912 1213 2684354560 (@Ns288p309 1 536870912 1 536870912 755954576523264 11264601 536870912 201 536870912 (@Ns288p310 67108864 25 67108864 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns288p311 (Ns288p317 rfl rfl rfl rfl) rfl) rfl) (@Ns288p318 16777216 1 16777216 1 536870912 1 536870912 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns288p319 1 16777216 1 16777216 (@Ns288p324 8388608 (@Ns288p329 8796093022208000 Ns288p320 Ns288p321 Ns288p322 Ns288p323 (@Ns288p330 Ns288p326 Ns288p327 Ns288p328 (Ns288p316 rfl) (Ns288p316 rfl) rfl) (Ns288p316 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns288p331 16777216 1429779 33554432 13 167772160 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns288p332 1 16777216 (Ns288p338 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS289to300.d48 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 := @Ns288p307 34141065 536870912 1213 2684354560 (BSN.hardyZErrorBoundRS₀_mk qz4 598981 1000 qz9 rfl rfl) (Ns288p339 rfl rfl) 

noncomputable def Ns288p340 := nat_lit 4611686018427387904000000 

noncomputable def Ns288p341 := nat_lit 7934479412704117500411904 

noncomputable abbrev qz721 := (Enclosure.sfrac Bool.false 601737 1000)

noncomputable abbrev qz606 := qz721

noncomputable abbrev qz402 := qz606

noncomputable abbrev qz60 := qz402

noncomputable abbrev qz722 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 601737 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz607 := qz722

noncomputable abbrev qz403 := qz607

noncomputable abbrev qz61 := (@HPow.hPow Real Real Real qz347 qz403 qz349)

noncomputable abbrev qz723 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 601737 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz608 := qz723

noncomputable abbrev qz404 := qz608

noncomputable abbrev qz62 := qz404

noncomputable def Ns288p342 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz60) qz60 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz61) (Zeta.RiemannSiegel.correction qz62)) 610963 1048576 21267 16777216 3181265532304469379 18446744073709551616 239744484472984339849 Ns288p340 Ns288p341 

noncomputable def Ns288p343 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 601737 1000 114 159 134217728 67108864 2251799813685248 Bool.false 143785291917 1843 

noncomputable def Ns288p344 := Ns288p343 279097919 34 47453128 8 294906479 34 44739240 8 Bool.true 50525513 69729 Bool.true 123779157 Bool.true 149082489 7074237752028440 1 Bool.false 81073840 Bool.true Bool.false 120263435 Bool.false Bool.true 39101632 

noncomputable def Ns288p345 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 601737 1000 4 63 134217728 67108864 2251799813685248 Bool.false 143785291917 1843 

noncomputable def Ns288p346 := Ns288p345 240485871 35 54794152 8 261175631 35 50729528 8 Bool.true 127702064 51702 Bool.true 80639784 Bool.true 91539763 7074237752028440 1 Bool.false 110713005 Bool.false Bool.false 84606270 Bool.false Bool.true 50525513 

noncomputable def Ns288p347 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 601737 1000 150 65 134217728 67108864 2251799813685248 Bool.false 143785291917 1843 

noncomputable def Ns288p348 := Ns288p347 186065264 34 67108856 8 216015088 34 60023992 8 Bool.true 81858942 30557 Bool.false 198631033 Bool.false 97154490 7074237752028440 1 Bool.false 12180897 Bool.true Bool.false 88889682 Bool.true Bool.true 127702064 

noncomputable def Ns288p349 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 601737 1000 416 261 134217728 67108864 2251799813685248 Bool.false 143785291917 1843 

noncomputable def Ns288p350 := Ns288p349 93032624 34 94906264 8 147453232 34 77490640 16 Bool.true 134217680 1882 Bool.false 99374769 Bool.false 30932064 7074237752028440 1 Bool.false 99079388 Bool.false Bool.false 30658976 Bool.true Bool.true 81858942 

noncomputable def Ns288p351 := nat_lit 57259237751386414642450636199552167739078791578712242867 

noncomputable def Ns288p352 := nat_lit 53449171994826728786460763460379242260357307170816000 

noncomputable def Ns288p353 := nat_lit 37868279986010523014947829979360000 

noncomputable def Ns288p354 := nat_lit 136720515215938735047457973662236889920 

noncomputable abbrev qz609 := (@Eq.refl Real qz721)

noncomputable abbrev qz405 := qz609

noncomputable abbrev qz63 := qz405

noncomputable def Ns288p355 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz60 601737 1000 1448350668676 16000000 1203474 4000 2000 Ns288p353 Ns288p354 qz63 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns288p356 := nat_lit 164906604723992874170257832254710243088546919746691259456960 

noncomputable abbrev qz610 := (@HSub.hSub Real Real Real qz712 qz713 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz714 (@Nat.cast Real Real.instNatCast 1203474))))

noncomputable abbrev qz406 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz580 (Enclosure.sfrac Bool.false 601737 4000) (Real.log (Enclosure.sfrac Bool.false 1448350668676 16000000))) (@HMul.hMul Real Real Real qz580 qz585 qz610))

noncomputable abbrev qz611 := (Enclosure.sfrac Bool.false 601737 2000)

noncomputable abbrev qz64 := (@HSub.hSub Real Real Real qz352 (@HSub.hSub Real Real Real qz352 qz406 qz611) (@HMul.hMul Real Real Real qz346 qz611 (Real.log Real.pi)))

noncomputable def Ns288p357 := @Enclosure.Real.IsNear.addLit_ft_p qz64 (Enclosure.sfrac Bool.true Ns288p353 Ns288p354) 1206158761905112670163 1125899906842624000 28119352837888629 2048000000000000000000 Ns288p353 Ns288p354 0 1 Ns288p356 

noncomputable def Ns288p358 := nat_lit 3237757772603943483465824993280 

noncomputable abbrev qz65 := (@HSub.hSub Real Real Real qz352 qz406 qz611)

noncomputable def Ns288p359 := @Enclosure.Real.IsNear.subLit_ff_p qz65 (@HMul.hMul Real Real Real qz5 qz611 (Real.log Real.pi)) 63757340385769336011 45035996273704960 4763572719573 1000000000000000000 23113176091857 67108864000 601737 67108864000 Ns288p358 1206158761905112670163 1125899906842624000 

noncomputable def Ns288p360 := nat_lit 3187867019288466800550000 

noncomputable abbrev qz66 := qz406

noncomputable def Ns288p361 := @Enclosure.Real.IsNear.subLit_ff_p qz66 qz611 1932681325766113419219 1125899906842624000 4763572719573 1000000000000000000 601737 2000 0 1 Ns288p360 63757340385769336011 45035996273704960 4763572719573 1000000000000000000 

noncomputable def Ns288p362 := nat_lit 4352011449273092292252712494339981312 

noncomputable def Ns288p363 := nat_lit 27595780414065734901039104 

noncomputable def Ns288p364 := nat_lit 1427835290236476870266817740918960766291424811700651318682286182700713141579067457481689599392464568320 

noncomputable def Ns288p365 := nat_lit 12391602604596850322636771730104837274874108581823547468629987151463987190505671560958203080062009344 

noncomputable def Ns288p366 := nat_lit 68503297160133787067210321648125293758938085094163619740410947444935066284202635756490149396480 

noncomputable def Ns288p367 := BSN.log_dyadic_bound 399774668676 2496926668676 5 4 Ns288p364 67108864 32000000 Ns288p365 Ns288p366 21675652 2896701337352 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 399774668676) (BSN.artanhQ 2496926668676) 0 4 Ns288p365 Ns288p364 Ns288p366 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz407 := (Real.log (Enclosure.sfrac Bool.false 1448350668676 16000000))

noncomputable def Ns288p368 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 601737 4000) qz407 601737 4000 0 1 3212571657968887 281474976710656 976563 31250000000000 1933123231751224156719 1125899906842624000 587634089931 125000000000000000 (Enclosure.Real.IsNear.const Bool.false 601737 4000) (BSN.isNear_log_sfrac 1448350668676 16000000 3212571657968887 281474976710656 976563 31250000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1448350668676) qz355)) Bool.false Ns288p363 Ns288p93 1000000512000000 32000000000000000000000 3212571657968887 281474976710656 976563 31250000000000 (BSN.log_rat_reduce_isNear 1448350668676 16000000 16 2896701337352 2097152000000 21675652 67108864 24973259072661432 36028797018963968 32000000 1000000000000000 rfl rfl rfl rfl (Ns288p367 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns288p369 := BSN.arctan_dyadic_bound_f 1000 1203474 1 0 8388608 4000000 0 1 1 0 1 1 6970 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1203474) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1203474) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz408 := (@Nat.cast Real Real.instNatCast 1203474)

noncomputable def Ns288p370 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz408)) 884279719003555 562949953421312 1 2000000000000000 6970 8388608 1 4000000 7413952163895626956800 883811970221475 562949953421312 500000001 2000000000000000 qz15 (Ns288p369 rfl) rfl rfl 

noncomputable abbrev qz409 := (@HMul.hMul Real Real Real qz580 qz585 qz610)

noncomputable abbrev qz67 := qz409

noncomputable abbrev qz410 := qz610

noncomputable abbrev qz68 := qz410

noncomputable def Ns288p371 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 601737 4000) qz407) qz67 1933123231751224156719 1125899906842624000 587634089931 125000000000000000 883811970221475 2251799813685248 500000001 8000000000000000 Ns288p362 1932681325766113419219 1125899906842624000 4763572719573 1000000000000000000 (Ns288p368 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz68 1 4 0 1 883811970221475 562949953421312 500000001 2000000000000000 883811970221475 2251799813685248 500000001 8000000000000000 qz363 Ns288p370 rfl) 

noncomputable def Ns288p372 := @Ns288p357 Ns288p351 Ns288p352 28119352837888629 2048000000000000000000 (@Ns288p359 28119352837888629 2048000000000000000000 (Ns288p361 (Ns288p371 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 601737 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz611 (Real.log Real.pi) 601737 2000 0 1 38410761 33554432 1 33554432 23113176091857 67108864000 601737 67108864000 (Enclosure.Real.IsNear.const Bool.false 601737 2000) RS289to300.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns288p353 Ns288p354) 

noncomputable def Ns288p373 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz60) Bool.false Ns288p351 Ns288p352 28119352837888629 2048000000000000000000 17973161489 16777216 231 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz60) (@HAdd.hAdd Real Real Real qz364 qz64 (Enclosure.sfrac Bool.true Ns288p353 Ns288p354)) Bool.false Ns288p351 Ns288p352 28119352837888629 2048000000000000000000 Ns288p355 (Ns288p372 rfl rfl)) 

noncomputable def Ns288p374 := BSN.cos_dyadic_bound_f 27871535 34359738368 1 0 16777216 8007813 0 1 1 0 1 1 16777210 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 27871535) (BSN.cosEvenQ 34359738368) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 27871535) (BSN.cosOddQ 34359738368) 0 0 rfl) rfl rfl 

noncomputable def Ns288p375 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz60) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17973161489) qz365) Bool.false 17973161489 16777216 231 16777216 Bool.true 16777210 16777216 1 4000000 (Ns288p373 rfl) (Enclosure.sfrac_false_div 17973161489 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17973161489) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1961284981958218088448) qz366) 226375608064910080 72057594037927936 Bool.false 16777210 16777216 170 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q2 17973161489 16777216 226375608064910080 72057594037927936 170 1961284981958218088448 Ns288p93 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777210 16777216 1961284981958218088448 Ns288p93 27871535 34359738368 8007813 8000000 (Ns288p374 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p376 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz60) Bool.false Ns288p351 Ns288p352 28119352837888629 2048000000000000000000 143785291917 134217728 1843 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz60) (@HAdd.hAdd Real Real Real qz364 qz64 (Enclosure.sfrac Bool.true Ns288p353 Ns288p354)) Bool.false Ns288p351 Ns288p352 28119352837888629 2048000000000000000000 Ns288p355 (Ns288p372 rfl rfl)) 

noncomputable def Ns288p377 := Ns288p350 30557 BSN.abs_quadSignPos (BSN.cos_quad_nat0 416 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 99079388 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 261 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 30658976 134217728) qz63 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 1) Bool.true 8388605 8388608 3674911 262144000000 134217680 134217728 1882 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz60)) Bool.true 8388605 8388608 3674911 262144000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz60) qz60) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz60)) Bool.true 16777210 16777216 940777216 67108864000000 8388605 8388608 3674911 262144000000 (Ns288p375 rfl rfl) rfl)) rfl) (Ns288p376 rfl) RS289to300.d7 

noncomputable def Ns288p378 := nat_lit 53177880105753992348358835350970136037955607149231058915212014350721 

noncomputable def Ns288p379 := nat_lit 9510624980455777288356074449299671804033191353786163775099335041 

noncomputable def Ns288p380 := nat_lit 159514619067301065490499793904011808770258755064985604418085844382081 

noncomputable def Ns288p381 := BSN.cos_dyadic_bound_f 99374769 134217728 3 2 134217728 67108864 Ns288p378 Ns288p123 Ns288p379 Ns288p380 Ns288p126 Ns288p379 99079388 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 99374769) qz369 0 2 Ns288p378 Ns288p123 Ns288p379 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 99374769) qz370 0 2 Ns288p380 Ns288p126 Ns288p379 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p382 := nat_lit 915452047458071143065993609216 

noncomputable def Ns288p383 := BSN.sin_dyadic_bound_f 30932064 134217728 2 1 134217728 67108864 Ns288p382 Ns288p115 Ns288p382 Ns288p382 Ns288p116 Ns288p382 30658976 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 30932064) qz367 0 1 Ns288p382 Ns288p115 Ns288p382 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 30932064) qz368 0 1 Ns288p382 Ns288p116 Ns288p382 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p384 := nat_lit 3281194155271758403299822352992714850646500715783687176766940332950472173315001187520274596205393674167841 

noncomputable def Ns288p385 := nat_lit 3771943808847655588698186863402039537401430022851135872569690281121727876050857013905382182677308961 

noncomputable def Ns288p386 := nat_lit 19868109513503257261581392505291563515834136440355704608446641173293861219140550758221597110211706194683425 

noncomputable def Ns288p387 := BSN.cos_dyadic_bound_f 198631033 134217728 4 3 134217728 67108864 Ns288p384 Ns288p137 Ns288p385 Ns288p386 Ns288p140 Ns288p385 12180897 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 198631033) qz369 0 3 Ns288p384 Ns288p137 Ns288p385 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 198631033) qz370 0 3 Ns288p386 Ns288p140 Ns288p385 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p388 := nat_lit 87440423226286059387787628668894293985244732662322115197750689440000 

noncomputable def Ns288p389 := nat_lit 7937852245756920186741068719445752843936210128758044640100000000 

noncomputable def Ns288p390 := nat_lit 228997780498541787192474780021558333980560307870635169636120215200000 

noncomputable def Ns288p391 := BSN.sin_dyadic_bound_f 97154490 134217728 3 2 134217728 67108864 Ns288p388 Ns288p109 Ns288p389 Ns288p390 Ns288p112 Ns288p389 88889682 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 97154490) qz367 0 2 Ns288p388 Ns288p109 Ns288p389 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 97154490) qz368 0 2 Ns288p390 Ns288p112 Ns288p389 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p392 := Ns288p348 51702 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 150 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 12180897 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 65 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 88889682 134217728) qz63 rfl rfl (Ns288p377 RS289to300.d9 RS289to300.d11 RS289to300.d13 RS289to300.d17 (Ns288p381 rfl rfl) (Ns288p383 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns288p376 rfl) RS289to300.d19 RS289to300.d21 RS289to300.d23 RS289to300.d25 RS289to300.d17 (Ns288p387 rfl rfl) (Ns288p391 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns288p393 := nat_lit 23055785344547814245507888439767427838769073827202096351532365643776 

noncomputable def Ns288p394 := nat_lit 1788112530109296676202092051199500919467798760692681396658896896 

noncomputable def Ns288p395 := nat_lit 69163779808583224143171261135199884514468285884084903691803779137536 

noncomputable def Ns288p396 := BSN.cos_dyadic_bound_f 80639784 134217728 3 2 134217728 67108864 Ns288p393 Ns288p123 Ns288p394 Ns288p395 Ns288p126 Ns288p394 110713005 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 80639784) qz369 0 2 Ns288p393 Ns288p123 Ns288p394 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 80639784) qz370 0 2 Ns288p395 Ns288p126 Ns288p394 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p397 := nat_lit 68911471947259086089512760633471094955392921578672172740987352489505 

noncomputable def Ns288p398 := nat_lit 4930355892561003798972274323701478799122804186154810946926386721 

noncomputable def Ns288p399 := nat_lit 180474444047566793371144608453043065346068595784982868437243280465441 

noncomputable def Ns288p400 := BSN.sin_dyadic_bound_f 91539763 134217728 3 2 134217728 67108864 Ns288p397 Ns288p109 Ns288p398 Ns288p399 Ns288p112 Ns288p398 84606270 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 91539763) qz367 0 2 Ns288p397 Ns288p109 Ns288p398 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 91539763) qz368 0 2 Ns288p399 Ns288p112 Ns288p398 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p401 := Ns288p346 69729 BSN.abs_quadSignPos (BSN.cos_quad_nat0 4 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 110713005 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 84606270 134217728) qz63 rfl rfl (Ns288p392 rfl rfl) (Ns288p376 rfl) RS289to300.d27 RS289to300.d29 RS289to300.d31 RS289to300.d33 RS289to300.d17 (Ns288p396 rfl rfl) (Ns288p400 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p402 := nat_lit 128034157686902680822666967987053905906473019315784884312756626768481 

noncomputable def Ns288p403 := nat_lit 55103624347764550421344775097953539159899670059521653630393762401 

noncomputable def Ns288p404 := nat_lit 383992265812012513367158214410965810641099258607235609631009092780641 

noncomputable def Ns288p405 := BSN.cos_dyadic_bound_f 123779157 134217728 3 2 134217728 67108864 Ns288p402 Ns288p123 Ns288p403 Ns288p404 Ns288p126 Ns288p403 81073840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 123779157) qz369 0 2 Ns288p402 Ns288p123 Ns288p403 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 123779157) qz370 0 2 Ns288p404 Ns288p126 Ns288p403 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p406 := nat_lit 485005219994938994557376471331128255993421489655870904440058550805185 

noncomputable def Ns288p407 := nat_lit 244013064461167780926170624005464214005442248643967963598424498881 

noncomputable def Ns288p408 := nat_lit 1269856697882379285528772196285517537921999852124714515878136850539201 

noncomputable def Ns288p409 := BSN.sin_dyadic_bound_f 149082489 134217728 3 2 134217728 67108864 Ns288p406 Ns288p109 Ns288p407 Ns288p408 Ns288p112 Ns288p407 120263435 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 149082489) qz367 0 2 Ns288p406 Ns288p109 Ns288p407 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 149082489) qz368 0 2 Ns288p408 Ns288p112 Ns288p407 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p410 := Ns288p344 85068 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 114 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 81073840 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 120263435 134217728) qz63 rfl rfl (Ns288p401 rfl) (Ns288p376 rfl) RS289to300.d35 RS289to300.d37 RS289to300.d39 RS289to300.d41 RS289to300.d17 (Ns288p405 rfl rfl) (Ns288p409 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p411 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 9) 39101632 134217728 85068 134217728 39101632 134217728 85068 134217728 10496264416264192 610963 1048576 21267 16777216 (Ns288p410 rfl) 

noncomputable def Ns288p412 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz61) (Zeta.RiemannSiegel.correction qz62) 2681533 8388608 1 8388608 1186360761663 2199023255552 178590235501447 1099511627776000000 3181265532304469379 18446744073709551616 

noncomputable def Ns288p413 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz61 1 1 0 1 2681533 8388608 1 8388608 2681533 8388608 1 8388608 

noncomputable abbrev qz69 := qz403

noncomputable def Ns288p414 := @Enclosure.Real.IsNear.sqrt_image qz69 1606744297449 16777216000 601737 16777216000 82092457 82092488 8388608 (@Enclosure.Real.IsNear.of_eq qz69 (@HMul.hMul Real Real Real qz5 qz60 qz3) Bool.false 1606744297449 16777216000 601737 16777216000 (BSN.t_div_two_pi_mk qz60 601737 1000 qz63) (@Enclosure.Real.IsNear.mulLit_ff qz60 qz3 601737 1000 0 1 2670177 16777216 1 16777216 1606744297449 16777216000 601737 16777216000 (Enclosure.Real.IsNear.const Bool.false 601737 1000) RS289to300.d44 rfl)) 

noncomputable abbrev qz724 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 601737 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz612 := qz724

noncomputable abbrev qz411 := qz612

noncomputable abbrev qz70 := qz411

noncomputable def Ns288p415 := @Enclosure.Real.IsNear.sqrt_image qz70 164184945 16777216 31 16777216 26241978 26241984 8388608 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 164184945 16777216 31 16777216 164184945 16777216 31 16777216 (Ns288p414 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns288p416 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz70) 26241981 8388608 3 8388608 2681532 2681534 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz70) Bool.false 52483962 16777216 6 16777216 26241981 8388608 3 8388608 (Ns288p415 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns288p417 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz70)) Bool.false 5363066 16777216 2 16777216 2681533 8388608 1 8388608 (Ns288p416 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz71 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz404))

noncomputable abbrev qz613 := (@HMul.hMul Real Real Real qz708 qz723 qz723)

noncomputable abbrev qz412 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz613 qz608) qz594)

noncomputable abbrev qz72 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz412))

noncomputable def Ns288p418 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz62) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz71) qz72) Bool.false 1186360761663 

noncomputable def Ns288p419 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz71) qz72 74431317 16777216 3941 

noncomputable def Ns288p420 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz71) Bool.false 74431317 16777216 3941 16777216 74431317 16777216 3941 

noncomputable def Ns288p421 := @Enclosure.Real.IsNear.recentre' qz71 Bool.false 3781674 16777216 200194304 16777216000000 1890837 8388608 782009 65536000000 

noncomputable abbrev qz73 := (@HMul.hMul Real Real Real qz346 qz343 qz404)

noncomputable abbrev qz413 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable def Ns288p422 := @Enclosure.Real.IsNear.cos_image qz73 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20718805) qz413) Bool.false 20718805 4194304 49 4194304 Bool.false 3781674 16777216 1 

noncomputable def Ns288p423 := nat_lit 836568337793666654968652569 

noncomputable def Ns288p424 := nat_lit 72057594037927936000000000000000 

noncomputable def Ns288p425 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz62 884279719003555 140737488355328 1 500000000000000 13190001 16777216 31 16777216 11663650377936609453555 2361183241434822606848 Ns288p423 

noncomputable def Ns288p426 := @Enclosure.Real.IsNear.subLit_ff_p qz70 qz1 164184945 16777216 31 16777216 9 1 0 1 13190001 13190001 16777216 31 

noncomputable def Ns288p427 := @Ns288p426 16777216 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 164184945 16777216 31 16777216 164184945 16777216 31 16777216 (Ns288p414 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns288p428 := @Enclosure.Real.IsNear.recentre' qz73 Bool.false 11663650377936609453555 2361183241434822606848 Ns288p423 Ns288p424 20718805 4194304 49 4194304 (@Ns288p425 Ns288p424 RS289to300.d43 (Ns288p427 rfl rfl) rfl) 

noncomputable def Ns288p429 := nat_lit 3724333101963917037855283211161460550625 

noncomputable def Ns288p430 := BSN.sin_dyadic_bound_f 7811998105 34359738368 2 1 16777216 8007813 Ns288p429 Ns288p168 Ns288p429 Ns288p429 Ns288p169 Ns288p429 3781674 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 7811998105) qz376 0 1 Ns288p429 Ns288p168 Ns288p429 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 7811998105) qz377 0 1 Ns288p429 Ns288p169 Ns288p429 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz414 := (@Nat.cast Real Real.instNatCast 604462909807314587353088)

noncomputable def Ns288p431 := @Ns288p422 4000000 (Ns288p428 rfl) (Enclosure.sfrac_false_div 20718805 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20718805) qz413) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 137430124054729195520000) qz414) 226375608064910080 72057594037927936 Bool.false 3781674 16777216 0 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q3 20718805 4194304 226375608064910080 72057594037927936 0 137430124054729195520000 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 3781674 16777216 137430124054729195520000 604462909807314587353088 7811998105 34359738368 8007813 8000000 (Ns288p430 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p432 := @Enclosure.Real.IsNear.inv_image qz71 1890837 8388608 782009 65536000000 37213688 37217629 8388608 (Ns288p421 (Ns288p431 rfl rfl) rfl) rfl 

noncomputable def Ns288p433 := @Enclosure.Real.IsNear.recentre' qz72 Bool.false 1020096 8388608 

noncomputable abbrev qz74 := (@HMul.hMul Real Real Real qz346 qz343 qz412)

noncomputable def Ns288p434 := @Enclosure.Real.IsNear.cos_image qz74 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 24308335)) qz365) Bool.true 24308335 16777216 

noncomputable def Ns288p435 := nat_lit 57396434922504316701426198205 

noncomputable def Ns288p436 := nat_lit 39614081257132168796771975168 

noncomputable def Ns288p437 := nat_lit 1444159522213806561122849206804993 

noncomputable def Ns288p438 := @Enclosure.Real.IsNear.recentre' qz74 Bool.true Ns288p435 Ns288p436 Ns288p437 

noncomputable def Ns288p439 := nat_lit 48357032784585166988247040000000000000 

noncomputable abbrev qz75 := qz412

noncomputable def Ns288p440 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz75 884279719003555 140737488355328 1 500000000000000 64907555481631 

noncomputable abbrev qz415 := (@HSub.hSub Real Real Real qz584 qz613 qz608)

noncomputable abbrev qz76 := qz415

noncomputable def Ns288p441 := @Enclosure.Real.IsNear.subLit_tf qz76 qz29 47315369437215 281474976710656 1337874719 281474976710656 1 16 

noncomputable abbrev qz416 := qz613

noncomputable abbrev qz77 := qz416

noncomputable def Ns288p442 := @Enclosure.Real.IsNear.subLit_ff_n qz77 qz62 173976126380001 281474976710656 817781023 281474976710656 13190001 16777216 31 16777216 

noncomputable def Ns288p443 := @Enclosure.Real.IsNear.mulLit_ff qz62 qz62 13190001 16777216 31 16777216 13190001 16777216 31 16777216 173976126380001 281474976710656 

noncomputable def Ns288p444 := nat_lit 43857504231636305991740825094936486166890843730566391180901989927680024197450802111659071890625 

noncomputable def Ns288p445 := nat_lit 42565971920917120862509303625096280497492295906773659075853071849379145629086465087890625 

noncomputable def Ns288p446 := nat_lit 265604559331590701825167018566181578844879990888766855476390744502952073828827530624554457490625 

noncomputable def Ns288p447 := BSN.cos_dyadic_bound_f 24308335 16777216 4 3 8388608 4000000 Ns288p444 Ns288p185 Ns288p445 Ns288p446 Ns288p188 Ns288p445 1020096 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 24308335) qz595 0 3 Ns288p444 Ns288p185 Ns288p445 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 24308335) (BSN.cosOddQ 16777216) 0 3 Ns288p446 Ns288p188 Ns288p445 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p448 := @Ns288p433 1012388608 33554432000000 15939 131072 3954643 131072000000 (@Ns288p434 251 8388608 Bool.false 1020096 8388608 1 4000000 (@Ns288p438 Ns288p439 24308335 16777216 251 8388608 (@Ns288p440 281474976710656 1337874719 281474976710656 Ns288p435 Ns288p436 Ns288p437 Ns288p439 RS289to300.d43 (@Ns288p441 0 1 1038520887706096 64907555481631 281474976710656 1337874719 281474976710656 (@Ns288p442 793820173167954493440 47315369437215 281474976710656 1337874719 281474976710656 (@Ns288p443 817781023 281474976710656 (Ns288p427 rfl rfl) (Ns288p427 rfl rfl) rfl) (Ns288p427 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 24308335 16777216) (BSN.cos_neg_of_bound 24308335 16777216 Bool.false 1020096 8388608 1 4000000 (Ns288p447 rfl rfl)) rfl rfl) 

noncomputable def Ns288p449 := @Ns288p412 239744484472984339849 Ns288p340 (Ns288p413 qz31 (@Enclosure.Real.IsNear.of_eq qz61 (@Inv.inv Real Real.instInv (Real.sqrt qz70)) Bool.false 2681533 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz69 (BSN.t_div_two_pi_nonneg qz60 601737 1000 qz63)) Ns288p417) rfl) (@Ns288p418 2199023255552 178590235501447 1099511627776000000 (BSN.correction_mk qz62 (BSN.cos_two_pi_p_ne_zero_mk qz60 601737 1000 9 qz63 rfl rfl (@BSN.floor_sqrt_eq_dec qz60 601737 1000 9 qz63 rfl rfl rfl))) (@Ns288p419 16777216 15939 131072 3954643 131072000000 1186360761663 2199023255552 178590235501447 1099511627776000000 (@Ns288p420 16777216 (Ns288p432 rfl rfl rfl rfl rfl) rfl) (Ns288p448 rfl) rfl)) 

noncomputable def Ns288p450 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz60) (hardyZApproximantRS₀ qz60) Bool.true 7566909229950063229 18446744073709551616 6085572931451032339849 Ns288p340 (@Eq.refl Real (hardyZApproximantRS₀ qz60)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz60) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz60) qz60 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz61) (Zeta.RiemannSiegel.correction qz62))) Bool.true 7566909229950063229 18446744073709551616 6085572931451032339849 Ns288p340 (BSN.hardyZApproximantRS₀_eq qz60 9 (@BSN.floor_sqrt_eq_dec qz60 601737 1000 9 qz63 rfl rfl rfl)) (@Ns288p342 7566909229950063229 18446744073709551616 6085572931451032339849 Ns288p340 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz60) qz60 9) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 9)) Bool.true 610963 1048576 21267 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz60) qz60 9) (Ns288p411 (Ns288p410 rfl) rfl rfl)) (Ns288p449 rfl) rfl rfl)) 

theorem RS289to300.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz60) Bool.true 7566909229950063229 18446744073709551616 6085572931451032339849 Ns288p340 := Ns288p450 

noncomputable def Ns288p451 := nat_lit 18446744073709551616000000 

noncomputable def Ns288p452 := nat_lit 13433414384152862760001077248 

noncomputable abbrev qz725 := (Enclosure.sfrac Bool.false 603114 1000)

noncomputable abbrev qz614 := qz725

noncomputable abbrev qz417 := qz614

noncomputable abbrev qz78 := qz417

noncomputable abbrev qz726 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 603114 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz615 := qz726

noncomputable abbrev qz418 := qz615

noncomputable abbrev qz79 := (@HPow.hPow Real Real Real qz347 qz418 qz349)

noncomputable abbrev qz727 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 603114 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz616 := qz727

noncomputable abbrev qz419 := qz616

noncomputable abbrev qz80 := qz419

noncomputable def Ns288p453 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz78) qz78 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz79) (Zeta.RiemannSiegel.correction qz80)) 8413983 16777216 85269 67108864 208612475245840325891 1180591620717411303424 767489180141954728741 Ns288p451 Ns288p452 

noncomputable def Ns288p454 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 603114 1000 114 159 134217728 67108864 2251799813685248 Bool.false 144206961633 1848 

noncomputable def Ns288p455 := Ns288p454 279097919 34 47453128 8 294906479 34 44739240 8 Bool.false 34089335 69895 Bool.true 86427275 Bool.true 133498995 7074237752028440 1 Bool.false 107339361 Bool.true Bool.false 112550373 Bool.false Bool.false 33655932 

noncomputable def Ns288p456 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 603114 1000 3 63 134217728 67108864 2251799813685248 Bool.false 144206961633 1848 

noncomputable def Ns288p457 := Ns288p456 240485871 35 54794152 8 261175631 35 50729528 8 Bool.true 31620074 51826 Bool.true 200947826 Bool.true 29508891 7074237752028440 1 Bool.false 133854184 Bool.false Bool.false 29271732 Bool.false Bool.false 34089335 

noncomputable def Ns288p458 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 603114 1000 151 66 134217728 67108864 2251799813685248 Bool.false 144206961633 1848 

noncomputable def Ns288p459 := Ns288p458 186065264 34 67108856 8 216015088 34 60023992 8 Bool.true 32811015 30632 Bool.false 153260166 Bool.false 10542716 7074237752028440 1 Bool.false 122059723 Bool.false Bool.false 133803879 Bool.true Bool.true 31620074 

noncomputable def Ns288p460 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 603114 1000 417 262 134217728 67108864 2251799813685248 Bool.false 144206961633 1848 

noncomputable def Ns288p461 := Ns288p460 93032624 34 94906264 8 147453232 34 77490640 16 Bool.false 134217672 1890 Bool.false 182109848 Bool.false 38729965 7074237752028440 1 Bool.false 131156912 Bool.true Bool.false 128668421 Bool.true Bool.true 32811015 

noncomputable def Ns288p462 := nat_lit 90969018121311267073762056464580855600659929146941173 

noncomputable def Ns288p463 := nat_lit 84667583259285292017731148197593820236787325337600 

noncomputable def Ns288p464 := nat_lit 38303551412149944270822521195520000 

noncomputable def Ns288p465 := nat_lit 138608493095228846534078972359265095680 

noncomputable abbrev qz617 := (@Eq.refl Real qz725)

noncomputable abbrev qz420 := qz617

noncomputable abbrev qz81 := qz420

noncomputable def Ns288p466 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz78 603114 1000 1454986987984 16000000 1206228 4000 2000 Ns288p464 Ns288p465 qz81 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns288p467 := nat_lit 16767409420120092747035822247551543304313638140364197007360 

noncomputable abbrev qz618 := (@HSub.hSub Real Real Real qz712 qz713 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz714 (@Nat.cast Real Real.instNatCast 1206228))))

noncomputable abbrev qz421 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz580 (Enclosure.sfrac Bool.false 603114 4000) (Real.log (Enclosure.sfrac Bool.false 1454986987984 16000000))) (@HMul.hMul Real Real Real qz580 qz585 qz618))

noncomputable abbrev qz619 := (Enclosure.sfrac Bool.false 603114 2000)

noncomputable abbrev qz82 := (@HSub.hSub Real Real Real qz352 (@HSub.hSub Real Real Real qz352 qz421 qz619) (@HMul.hMul Real Real Real qz346 qz619 (Real.log Real.pi)))

noncomputable def Ns288p468 := @Enclosure.Real.IsNear.addLit_ft_p qz82 (Enclosure.sfrac Bool.true Ns288p464 Ns288p465) 120969598314562110577 112589990684262400 14091703777123569 1024000000000000000000 Ns288p464 Ns288p465 0 1 Ns288p467 

noncomputable def Ns288p469 := nat_lit 20295330803566444745662136320000 

noncomputable abbrev qz83 := (@HSub.hSub Real Real Real qz352 qz421 qz619)

noncomputable def Ns288p470 := @Enclosure.Real.IsNear.subLit_ff_p qz83 (@HMul.hMul Real Real Real qz5 qz619 (Real.log Real.pi)) 799179052491394635317 562949953421312000 4774330537581 1000000000000000000 11583033854877 33554432000 301557 33554432000 Ns288p469 120969598314562110577 112589990684262400 

noncomputable def Ns288p471 := nat_lit 1598358104982789270634000 

noncomputable abbrev qz84 := qz421

noncomputable def Ns288p472 := @Enclosure.Real.IsNear.subLit_ff_p qz84 qz619 968940551595265218101 562949953421312000 4774330537581 1000000000000000000 603114 2000 0 1 Ns288p471 799179052491394635317 562949953421312000 4774330537581 1000000000000000000 

noncomputable def Ns288p473 := nat_lit 2181860153554299644904788315286274048 

noncomputable def Ns288p474 := nat_lit 27606833652674385837817856 

noncomputable def Ns288p475 := nat_lit 1458478354170978391975540516525941340659064999049170304893592908259281344213675995950732424711472414720 

noncomputable def Ns288p476 := nat_lit 13017734205885398712370686488684005651786362482371344860323511369714670377146697846498726082169012224 

noncomputable def Ns288p477 := nat_lit 78147093382253277491749762686051979539968668884330549685216175053627757874055987751456688046080 

noncomputable def Ns288p478 := BSN.log_dyadic_bound 406410987984 2503562987984 5 4 Ns288p475 67108864 32000000 Ns288p476 Ns288p477 21982441 2909973975968 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 406410987984) (BSN.artanhQ 2503562987984) 0 4 Ns288p476 Ns288p475 Ns288p477 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz422 := (Real.log (Enclosure.sfrac Bool.false 1454986987984 16000000))

noncomputable def Ns288p479 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 603114 4000) qz422 603114 4000 0 1 3213858424298743 281474976710656 976563 31250000000000 969161504856256042851 562949953421312000 294489408591 62500000000000000 (Enclosure.Real.IsNear.const Bool.false 603114 4000) (BSN.isNear_log_sfrac 1454986987984 16000000 3213858424298743 281474976710656 976563 31250000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1454986987984) qz355)) Bool.false Ns288p474 Ns288p93 1000000512000000 32000000000000000000000 3213858424298743 281474976710656 976563 31250000000000 (BSN.log_rat_reduce_isNear 1454986987984 16000000 16 2909973975968 2097152000000 21982441 67108864 24973259072661432 36028797018963968 32000000 1000000000000000 rfl rfl rfl rfl (Ns288p478 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns288p480 := BSN.arctan_dyadic_bound_f 1000 1206228 1 0 8388608 4000000 0 1 1 0 1 1 6954 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1206228) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1206228) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz423 := (@Nat.cast Real Real.instNatCast 1206228)

noncomputable def Ns288p481 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz423)) 884279719003555 562949953421312 1 2000000000000000 6954 8388608 1 4000000 7413961171094881697792 883813043963299 562949953421312 500000001 2000000000000000 qz15 (Ns288p480 rfl) rfl rfl 

noncomputable abbrev qz424 := (@HMul.hMul Real Real Real qz580 qz585 qz618)

noncomputable abbrev qz85 := qz424

noncomputable abbrev qz425 := qz618

noncomputable abbrev qz86 := qz425

noncomputable def Ns288p482 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 603114 4000) qz422) qz85 969161504856256042851 562949953421312000 294489408591 62500000000000000 883813043963299 2251799813685248 500000001 8000000000000000 Ns288p473 968940551595265218101 562949953421312000 4774330537581 1000000000000000000 (Ns288p479 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz86 1 4 0 1 883813043963299 562949953421312 500000001 2000000000000000 883813043963299 2251799813685248 500000001 8000000000000000 qz363 Ns288p481 rfl) 

noncomputable def Ns288p483 := @Ns288p468 Ns288p462 Ns288p463 14091703777123569 1024000000000000000000 (@Ns288p470 14091703777123569 1024000000000000000000 (Ns288p472 (Ns288p482 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 603114 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz619 (Real.log Real.pi) 603114 2000 0 1 38410761 33554432 1 33554432 11583033854877 33554432000 301557 33554432000 (Enclosure.Real.IsNear.const Bool.false 603114 2000) RS289to300.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns288p464 Ns288p465) 

noncomputable def Ns288p484 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz78) Bool.false Ns288p462 Ns288p463 14091703777123569 1024000000000000000000 4506467551 4194304 29 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz78) (@HAdd.hAdd Real Real Real qz364 qz82 (Enclosure.sfrac Bool.true Ns288p464 Ns288p465)) Bool.false Ns288p462 Ns288p463 14091703777123569 1024000000000000000000 Ns288p466 (Ns288p483 rfl rfl)) 

noncomputable def Ns288p485 := BSN.cos_dyadic_bound_f 31018219 34359738368 1 0 16777216 8007813 0 1 1 0 1 1 16777209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 31018219) (BSN.cosEvenQ 34359738368) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 31018219) (BSN.cosOddQ 34359738368) 0 0 rfl) rfl rfl 

noncomputable def Ns288p486 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz78) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4506467551) qz413) Bool.false 4506467551 4194304 29 2097152 Bool.false 16777209 16777216 1 4000000 (Ns288p484 rfl) (Enclosure.sfrac_false_div 4506467551 4194304) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4506467551) qz413) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 545678292741722734592) qz414) 226375608064910080 72057594037927936 Bool.false 16777209 16777216 171 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q0 4506467551 4194304 226375608064910080 72057594037927936 171 545678292741722734592 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777209 16777216 545678292741722734592 604462909807314587353088 31018219 34359738368 8007813 8000000 (Ns288p485 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p487 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz78) Bool.false Ns288p462 Ns288p463 14091703777123569 1024000000000000000000 144206961633 134217728 1848 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz78) (@HAdd.hAdd Real Real Real qz364 qz82 (Enclosure.sfrac Bool.true Ns288p464 Ns288p465)) Bool.false Ns288p462 Ns288p463 14091703777123569 1024000000000000000000 Ns288p466 (Ns288p483 rfl rfl)) 

noncomputable def Ns288p488 := Ns288p461 30632 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 417 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 131156912 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 262 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 128668421 134217728) qz81 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 1) Bool.false 16777209 16777216 461317 32768000000 134217672 134217728 1890 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz78)) Bool.false 16777209 16777216 461317 32768000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz78) qz78) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz78)) Bool.false 16777209 16777216 118097152 8388608000000 16777209 16777216 461317 32768000000 (Ns288p486 rfl rfl) rfl)) rfl) (Ns288p487 rfl) RS289to300.d7 

noncomputable def Ns288p489 := nat_lit 6017255109936204043980949880860182786755876244152926465325589387840426391081149180286370940480245356036096 

noncomputable def Ns288p490 := nat_lit 1330458040801920411959677649439800889184478470958500487329380650009045655609737440898815955876970496 

noncomputable def Ns288p491 := nat_lit 30065448800296509055015109631594519137286841810968044457910572365948832058823124914781328975447101125165056 

noncomputable def Ns288p492 := BSN.sin_dyadic_bound_f 182109848 134217728 4 3 134217728 67108864 Ns288p489 Ns288p143 Ns288p490 Ns288p491 Ns288p146 Ns288p490 131156912 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 182109848) qz367 0 3 Ns288p489 Ns288p143 Ns288p490 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 182109848) qz368 0 3 Ns288p491 Ns288p146 Ns288p490 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p493 := nat_lit 2250030566807488708172806500625 

noncomputable def Ns288p494 := BSN.cos_dyadic_bound_f 38729965 134217728 2 1 134217728 67108864 Ns288p493 Ns288p132 Ns288p493 Ns288p493 Ns288p133 Ns288p493 128668421 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 38729965) qz369 0 1 Ns288p493 Ns288p132 Ns288p493 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 38729965) qz370 0 1 Ns288p493 Ns288p133 Ns288p493 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p495 := nat_lit 541729616922168434868996579592224472091952707541628505326485792334080 

noncomputable def Ns288p496 := nat_lit 304392770113693704675452484730986262057460136885943209975864074496 

noncomputable def Ns288p497 := nat_lit 1418322836977876111039802213956737734864164060482640272562739961897216 

noncomputable def Ns288p498 := BSN.sin_dyadic_bound_f 153260166 134217728 3 2 134217728 67108864 Ns288p495 Ns288p109 Ns288p496 Ns288p497 Ns288p112 Ns288p496 122059723 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 153260166) qz367 0 2 Ns288p495 Ns288p109 Ns288p496 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 153260166) qz368 0 2 Ns288p497 Ns288p112 Ns288p496 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p499 := nat_lit 12354069225272732055517102336 

noncomputable def Ns288p500 := BSN.cos_dyadic_bound_f 10542716 134217728 2 1 134217728 67108864 Ns288p499 Ns288p132 Ns288p499 Ns288p499 Ns288p133 Ns288p499 133803879 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 10542716) qz369 0 1 Ns288p499 Ns288p132 Ns288p499 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 10542716) qz370 0 1 Ns288p499 Ns288p133 Ns288p499 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p501 := Ns288p459 51826 BSN.abs_quadSignPos (BSN.cos_quad_nat3 151 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 122059723 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133803879 134217728) qz81 rfl rfl (Ns288p488 RS289to300.d9 RS289to300.d11 RS289to300.d13 RS289to300.d17 (Ns288p492 rfl rfl) (Ns288p494 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns288p487 rfl) RS289to300.d19 RS289to300.d21 RS289to300.d23 RS289to300.d25 RS289to300.d17 (Ns288p498 rfl rfl) (Ns288p500 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns288p502 := nat_lit 8925500806385203132633631381058627300556130776750245789331749646546399563635042900239478205066128741502976 

noncomputable def Ns288p503 := nat_lit 4335106233205032053974366304140797568360568069930257976015821040471735722226863262350453620220235776 

noncomputable def Ns288p504 := nat_lit 44581724212414093705802905446897147864292539888551794838818151151907517313991184363618833802773565950529536 

noncomputable def Ns288p505 := BSN.sin_dyadic_bound_f 200947826 134217728 4 3 134217728 67108864 Ns288p502 Ns288p143 Ns288p503 Ns288p504 Ns288p146 Ns288p503 133854184 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 200947826) qz367 0 3 Ns288p502 Ns288p143 Ns288p503 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 200947826) qz368 0 3 Ns288p504 Ns288p146 Ns288p503 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p506 := nat_lit 758248487686394124436264114161 

noncomputable def Ns288p507 := BSN.sin_dyadic_bound_f 29508891 134217728 2 1 134217728 67108864 Ns288p506 Ns288p115 Ns288p506 Ns288p506 Ns288p116 Ns288p506 29271732 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 29508891) qz367 0 1 Ns288p506 Ns288p115 Ns288p506 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 29508891) qz368 0 1 Ns288p506 Ns288p116 Ns288p506 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p508 := Ns288p457 69895 BSN.abs_quadSignPos (BSN.cos_quad_nat3 3 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133854184 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 29271732 134217728) qz81 rfl rfl (Ns288p501 rfl rfl) (Ns288p487 rfl) RS289to300.d27 RS289to300.d29 RS289to300.d31 RS289to300.d33 RS289to300.d17 (Ns288p505 rfl rfl) (Ns288p507 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p509 := nat_lit 30422614791667722008887635881068719488767230704851733720952150390625 

noncomputable def Ns288p510 := nat_lit 3113196699668651435308705824147094522060697403669360504150390625 

noncomputable def Ns288p511 := nat_lit 91261617981603828723792290231557864277257570719747862441848150390625 

noncomputable def Ns288p512 := BSN.cos_dyadic_bound_f 86427275 134217728 3 2 134217728 67108864 Ns288p509 Ns288p123 Ns288p510 Ns288p511 Ns288p126 Ns288p510 107339361 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 86427275) qz369 0 2 Ns288p509 Ns288p123 Ns288p510 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 86427275) qz370 0 2 Ns288p511 Ns288p126 Ns288p510 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p513 := nat_lit 311798373387630910627082176454912089968176862360246457457978421230625 

noncomputable def Ns288p514 := nat_lit 100884389506289206539301491910723658226472284252823904500625390625 

noncomputable def Ns288p515 := nat_lit 816451450813166011974627783537866683041429874864236149877894852590625 

noncomputable def Ns288p516 := BSN.sin_dyadic_bound_f 133498995 134217728 3 2 134217728 67108864 Ns288p513 Ns288p109 Ns288p514 Ns288p515 Ns288p112 Ns288p514 112550373 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 133498995) qz367 0 2 Ns288p513 Ns288p109 Ns288p514 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 133498995) qz368 0 2 Ns288p515 Ns288p112 Ns288p514 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p517 := Ns288p455 85269 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 114 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 107339361 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 112550373 134217728) qz81 rfl rfl (Ns288p508 rfl) (Ns288p487 rfl) RS289to300.d35 RS289to300.d37 RS289to300.d39 RS289to300.d41 RS289to300.d17 (Ns288p512 rfl rfl) (Ns288p516 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p518 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 9) 33655932 134217728 85269 134217728 33655932 134217728 85269 134217728 9034445453524992 8413983 16777216 85269 67108864 (Ns288p517 rfl) 

noncomputable def Ns288p519 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz79) (Zeta.RiemannSiegel.correction qz80) 5360003 16777216 1 16777216 38920216135297 70368744177664 143074716318279 1099511627776000000 208612475245840325891 1180591620717411303424 

noncomputable def Ns288p520 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz79 1 1 0 1 5360003 16777216 1 16777216 5360003 16777216 1 16777216 

noncomputable abbrev qz87 := qz418

noncomputable def Ns288p521 := @Enclosure.Real.IsNear.sqrt_image qz87 805210565589 8388608000 301557 8388608000 82186332 82186364 8388608 (@Enclosure.Real.IsNear.of_eq qz87 (@HMul.hMul Real Real Real qz5 qz78 qz3) Bool.false 805210565589 8388608000 301557 8388608000 (BSN.t_div_two_pi_mk qz78 603114 1000 qz81) (@Enclosure.Real.IsNear.mulLit_ff qz78 qz3 603114 1000 0 1 2670177 16777216 1 16777216 805210565589 8388608000 301557 8388608000 (Enclosure.Real.IsNear.const Bool.false 603114 1000) RS289to300.d44 rfl)) 

noncomputable abbrev qz728 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 603114 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz620 := qz728

noncomputable abbrev qz426 := qz620

noncomputable abbrev qz88 := qz426

noncomputable def Ns288p522 := @Enclosure.Real.IsNear.sqrt_image qz88 20546587 2097152 1 524288 26256978 26256984 8388608 (@Enclosure.Real.IsNear.recentre' qz88 Bool.false 164372696 16777216 32 16777216 20546587 2097152 1 524288 (Ns288p521 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns288p523 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz88) 26256981 8388608 3 8388608 2680001 2680002 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz88) Bool.false 52513962 16777216 6 16777216 26256981 8388608 3 8388608 (Ns288p522 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns288p524 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz88)) Bool.false 5360003 16777216 1 16777216 5360003 16777216 1 16777216 (Ns288p523 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz89 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz419))

noncomputable abbrev qz621 := (@HMul.hMul Real Real Real qz708 qz727 qz727)

noncomputable abbrev qz427 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz621 qz616) qz594)

noncomputable abbrev qz90 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz427))

noncomputable def Ns288p525 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz80) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz89) qz90) Bool.false 38920216135297 

noncomputable def Ns288p526 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz89) qz90 28601129 8388608 1199 

noncomputable def Ns288p527 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz89) Bool.false 57202258 16777216 2398 16777216 28601129 8388608 1199 

noncomputable def Ns288p528 := @Enclosure.Real.IsNear.recentre' qz89 Bool.false 4920697 16777216 412388608 33554432000000 4920697 16777216 1610893 131072000000 

noncomputable abbrev qz91 := (@HMul.hMul Real Real Real qz346 qz343 qz419)

noncomputable def Ns288p529 := @Enclosure.Real.IsNear.cos_image qz91 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 42027447) qz393) Bool.false 42027447 8388608 101 8388608 Bool.false 4920697 16777216 1 

noncomputable def Ns288p530 := nat_lit 26986075412635108413543879 

noncomputable def Ns288p531 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz80 884279719003555 140737488355328 1 500000000000000 1672219 2097152 1 524288 1478709347432405738545 295147905179352825856 Ns288p530 

noncomputable def Ns288p532 := @Enclosure.Real.IsNear.subLit_ff_p qz88 qz1 20546587 2097152 1 524288 9 1 0 1 1672219 1672219 2097152 1 

noncomputable def Ns288p533 := @Ns288p532 524288 (@Enclosure.Real.IsNear.recentre' qz88 Bool.false 164372696 16777216 32 16777216 20546587 2097152 1 524288 (Ns288p521 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns288p534 := @Enclosure.Real.IsNear.recentre' qz91 Bool.false 1478709347432405738545 295147905179352825856 Ns288p530 Ns288p162 42027447 8388608 101 8388608 (@Ns288p531 Ns288p162 RS289to300.d43 (Ns288p533 rfl rfl) rfl) 

noncomputable def Ns288p535 := nat_lit 10943540756307066403190783135096554744801 

noncomputable def Ns288p536 := BSN.sin_dyadic_bound_f 10227970457 34359738368 2 1 16777216 8007813 Ns288p535 Ns288p168 Ns288p535 Ns288p535 Ns288p169 Ns288p535 4920697 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 10227970457) qz376 0 1 Ns288p535 Ns288p168 Ns288p535 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 10227970457) qz377 0 1 Ns288p535 Ns288p169 Ns288p535 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p537 := @Ns288p529 4000000 (Ns288p534 rfl) (Enclosure.sfrac_false_div 42027447 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 42027447) qz393) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 359864718298556991012864) qz394) 226375608064910080 72057594037927936 Bool.false 4920697 16777216 0 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q3 42027447 8388608 226375608064910080 72057594037927936 0 359864718298556991012864 Ns288p284 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 4920697 16777216 359864718298556991012864 Ns288p284 10227970457 34359738368 8007813 8000000 (Ns288p536 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p538 := @Enclosure.Real.IsNear.inv_image qz89 4920697 16777216 1610893 131072000000 28599930 28602328 8388608 (Ns288p528 (Ns288p537 rfl rfl) rfl) rfl 

noncomputable def Ns288p539 := @Enclosure.Real.IsNear.recentre' qz90 Bool.false 1360793 8388608 

noncomputable abbrev qz92 := (@HMul.hMul Real Real Real qz346 qz343 qz427)

noncomputable def Ns288p540 := @Enclosure.Real.IsNear.cos_image qz92 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 23619923)) qz365) Bool.true 23619923 16777216 

noncomputable def Ns288p541 := nat_lit 871421357445220127392328405 

noncomputable def Ns288p542 := nat_lit 618970019642690137449562112 

noncomputable def Ns288p543 := nat_lit 73423633015758940225512275973003 

noncomputable def Ns288p544 := @Enclosure.Real.IsNear.recentre' qz92 Bool.true Ns288p541 Ns288p542 Ns288p543 

noncomputable def Ns288p545 := nat_lit 2361183241434822606848000000000000000 

noncomputable abbrev qz93 := qz427

noncomputable def Ns288p546 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz93 884279719003555 140737488355328 1 500000000000000 985458943271 

noncomputable abbrev qz428 := (@HSub.hSub Real Real Real qz584 qz621 qz616)

noncomputable abbrev qz94 := qz428

noncomputable def Ns288p547 := @Enclosure.Real.IsNear.subLit_tf qz94 qz29 710581036327 4398046511104 2720797 549755813888 1 16 

noncomputable abbrev qz429 := qz621

noncomputable abbrev qz95 := qz429

noncomputable def Ns288p548 := @Enclosure.Real.IsNear.subLit_ff_n qz95 qz80 2796316383961 4398046511104 1672221 549755813888 1672219 2097152 1 524288 

noncomputable def Ns288p549 := @Enclosure.Real.IsNear.mulLit_ff qz80 qz80 1672219 2097152 1 524288 1672219 2097152 1 524288 2796316383961 4398046511104 

noncomputable def Ns288p550 := nat_lit 39085306155443939956062819924098507660583864591356830403657989874743137118742290721922539204401 

noncomputable def Ns288p551 := nat_lit 30153777781189378428970149277972299828475437969675205226412560314085219443240212836527921 

noncomputable def Ns288p552 := nat_lit 236748578188613145537531175004857552049811431114509540626700732223831849491252619615830323638065 

noncomputable def Ns288p553 := BSN.cos_dyadic_bound_f 23619923 16777216 4 3 8388608 4000000 Ns288p550 Ns288p185 Ns288p551 Ns288p552 Ns288p188 Ns288p551 1360793 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 23619923) qz595 0 3 Ns288p550 Ns288p185 Ns288p551 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 23619923) (BSN.cosOddQ 16777216) 0 3 Ns288p552 Ns288p188 Ns288p551 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p554 := @Ns288p539 1052388608 33554432000000 1360793 8388608 4110893 131072000000 (@Ns288p540 261 8388608 Bool.false 1360793 8388608 1 4000000 (@Ns288p544 Ns288p545 23619923 16777216 261 8388608 (@Ns288p546 4398046511104 2720797 549755813888 Ns288p541 Ns288p542 Ns288p543 Ns288p545 RS289to300.d43 (@Ns288p547 0 1 15767343092336 985458943271 4398046511104 2720797 549755813888 (@Ns288p548 1490196441495240704 710581036327 4398046511104 2720797 549755813888 (@Ns288p549 1672221 549755813888 (Ns288p533 rfl rfl) (Ns288p533 rfl rfl) rfl) (Ns288p533 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 23619923 16777216) (BSN.cos_neg_of_bound 23619923 16777216 Bool.false 1360793 8388608 1 4000000 (Ns288p553 rfl rfl)) rfl rfl) 

noncomputable def Ns288p555 := @Ns288p519 767489180141954728741 Ns288p451 (Ns288p520 qz31 (@Enclosure.Real.IsNear.of_eq qz79 (@Inv.inv Real Real.instInv (Real.sqrt qz88)) Bool.false 5360003 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz87 (BSN.t_div_two_pi_nonneg qz78 603114 1000 qz81)) Ns288p524) rfl) (@Ns288p525 70368744177664 143074716318279 1099511627776000000 (BSN.correction_mk qz80 (BSN.cos_two_pi_p_ne_zero_mk qz78 603114 1000 9 qz81 rfl rfl (@BSN.floor_sqrt_eq_dec qz78 603114 1000 9 qz81 rfl rfl rfl))) (@Ns288p526 8388608 1360793 8388608 4110893 131072000000 38920216135297 70368744177664 143074716318279 1099511627776000000 (@Ns288p527 8388608 (Ns288p538 rfl rfl rfl rfl rfl) rfl) (Ns288p554 rfl) rfl)) 

noncomputable def Ns288p556 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz78) (hardyZApproximantRS₀ qz78) Bool.false 800693892488054201603 1180591620717411303424 24206053427349890728741 Ns288p451 (@Eq.refl Real (hardyZApproximantRS₀ qz78)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz78) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz78) qz78 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz79) (Zeta.RiemannSiegel.correction qz80))) Bool.false 800693892488054201603 1180591620717411303424 24206053427349890728741 Ns288p451 (BSN.hardyZApproximantRS₀_eq qz78 9 (@BSN.floor_sqrt_eq_dec qz78 603114 1000 9 qz81 rfl rfl rfl)) (@Ns288p453 800693892488054201603 1180591620717411303424 24206053427349890728741 Ns288p451 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz78) qz78 9) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 9)) Bool.false 8413983 16777216 85269 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz78) qz78 9) (Ns288p518 (Ns288p517 rfl) rfl rfl)) (Ns288p555 rfl) rfl rfl)) 

theorem RS289to300.d50 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz78) Bool.false 800693892488054201603 1180591620717411303424 24206053427349890728741 Ns288p451 := Ns288p556 

noncomputable def Ns288p557 := nat_lit 30963734019969086373041799168 

noncomputable abbrev qz729 := (Enclosure.sfrac Bool.false 604490 1000)

noncomputable abbrev qz622 := qz729

noncomputable abbrev qz430 := qz622

noncomputable abbrev qz96 := qz430

noncomputable abbrev qz730 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 604490 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz623 := qz730

noncomputable abbrev qz431 := qz623

noncomputable abbrev qz97 := (@HPow.hPow Real Real Real qz347 qz431 qz349)

noncomputable abbrev qz731 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 604490 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz624 := qz731

noncomputable abbrev qz432 := qz624

noncomputable abbrev qz98 := qz432

noncomputable def Ns288p558 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz97) (Zeta.RiemannSiegel.correction qz98)) 38384007 67108864 42729 33554432 213863000479182215325 1180591620717411303424 634086133225827935819 Ns288p451 Ns288p557 

noncomputable def Ns288p559 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 604490 1000 114 159 134217728 67108864 2251799813685248 Bool.false 144628536084 1852 

noncomputable def Ns288p560 := Ns288p559 279097919 34 47453128 8 294906479 34 44739240 8 Bool.true 28442640 70049 Bool.true 48891561 Bool.true 117715859 7074237752028440 1 Bool.false 125410884 Bool.true Bool.false 103194224 Bool.false Bool.true 38384007 

noncomputable def Ns288p561 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 604490 1000 3 62 134217728 67108864 2251799813685248 Bool.false 144628536084 1852 

noncomputable def Ns288p562 := Ns288p561 240485871 35 54794152 8 261175631 35 50729528 8 Bool.true 56334232 51939 Bool.true 110281934 Bool.true 178140822 7074237752028440 1 Bool.false 98285002 Bool.false Bool.false 32365709 Bool.true Bool.true 28442640 

noncomputable def Ns288p563 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 604490 1000 152 66 134217728 67108864 2251799813685248 Bool.false 144628536084 1852 

noncomputable def Ns288p564 := Ns288p563 186065264 34 67108856 8 216015088 34 60023992 8 Bool.true 70690287 30697 Bool.false 107980100 Bool.false 134880406 7074237752028440 1 Bool.false 93074781 Bool.false Bool.false 71959641 Bool.true Bool.true 56334232 

noncomputable def Ns288p565 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 604490 1000 419 263 134217728 67108864 2251799813685248 Bool.false 144628536084 1852 

noncomputable def Ns288p566 := Ns288p565 93032624 34 94906264 8 147453232 34 77490640 16 Bool.true 134217720 1890 Bool.false 54013980 Bool.false 46580055 7074237752028440 1 Bool.false 52567774 Bool.false Bool.false 45650632 Bool.false Bool.true 70690287 

noncomputable def Ns288p567 := nat_lit 53274823076174024279025574451682598180124324422757 

noncomputable def Ns288p568 := nat_lit 49439937003207831279584139575547481367878041600 

noncomputable def Ns288p569 := nat_lit 38742495743590722867403952000000000 

noncomputable def Ns288p570 := nat_lit 140516752376265206065636845026880000000 

noncomputable abbrev qz625 := (@Eq.refl Real qz729)

noncomputable abbrev qz433 := qz625

noncomputable abbrev qz99 := qz433

noncomputable def Ns288p571 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz96 604490 1000 1461633640400 16000000 1208980 4000 2000 Ns288p569 Ns288p570 qz99 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns288p572 := nat_lit 17047943384375687769288183824538431417639783815282240000000 

noncomputable abbrev qz626 := (@HSub.hSub Real Real Real qz712 qz713 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz714 (@Nat.cast Real Real.instNatCast 1208980))))

noncomputable abbrev qz434 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz580 (Enclosure.sfrac Bool.false 604490 4000) (Real.log (Enclosure.sfrac Bool.false 1461633640400 16000000))) (@HMul.hMul Real Real Real qz580 qz585 qz626))

noncomputable abbrev qz627 := (Enclosure.sfrac Bool.false 604490 2000)

noncomputable abbrev qz100 := (@HSub.hSub Real Real Real qz352 (@HSub.hSub Real Real Real qz352 qz434 qz627) (@HMul.hMul Real Real Real qz346 qz627 (Real.log Real.pi)))

noncomputable def Ns288p573 := @Enclosure.Real.IsNear.addLit_ft_p qz100 (Enclosure.sfrac Bool.true Ns288p569 Ns288p570) 121323240525394499073 112589990684262400 2824741575301933 204800000000000000000 Ns288p569 Ns288p570 0 1 Ns288p572 

noncomputable def Ns288p574 := nat_lit 814186484845798798463808307200 

noncomputable abbrev qz101 := (@HSub.hSub Real Real Real qz352 qz434 qz627)

noncomputable def Ns288p575 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (@HMul.hMul Real Real Real qz5 qz627 (Real.log Real.pi)) 160278125676352656897 112589990684262400 957016108617 200000000000000000 2321892091689 6710886400 60449 6710886400 Ns288p574 121323240525394499073 112589990684262400 

noncomputable abbrev qz102 := qz434

noncomputable def Ns288p576 := @Enclosure.Real.IsNear.subLit_ff_p qz102 qz627 38861577482143509197 22517998136852480 957016108617 200000000000000000 604490 2000 0 1 64111250270541062758800 160278125676352656897 112589990684262400 957016108617 200000000000000000 

noncomputable def Ns288p577 := nat_lit 87508492933805583095452255551225856 

noncomputable def Ns288p578 := nat_lit 27617853708760982308782080 

noncomputable def Ns288p579 := nat_lit 1489744372786251499526372221782581505508973509113393074699398217731264756786657325875200000000000000000 

noncomputable def Ns288p580 := nat_lit 13668720584204447498646638603750869583734541790956567025601017778564684904978149539840000000000000000 

noncomputable def Ns288p581 := nat_lit 88976348224676712922524859753457278498309609189762334757753372142759080168652800000000000000000 

noncomputable def Ns288p582 := BSN.log_dyadic_bound 413057640400 2510209640400 5 4 Ns288p579 67108864 32000000 Ns288p580 Ns288p581 22288309 2923267280800 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 413057640400) (BSN.artanhQ 2510209640400) 0 4 Ns288p580 Ns288p579 Ns288p581 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz435 := (Real.log (Enclosure.sfrac Bool.false 1461633640400 16000000))

noncomputable def Ns288p583 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 604490 4000) qz435 604490 4000 0 1 3215141327674615 281474976710656 976563 31250000000000 38870415623320560427 22517998136852480 59032256787 12500000000000000 (Enclosure.Real.IsNear.const Bool.false 604490 4000) (BSN.isNear_log_sfrac 1461633640400 16000000 3215141327674615 281474976710656 976563 31250000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1461633640400) qz355)) Bool.false Ns288p578 Ns288p93 1000000512000000 32000000000000000000000 3215141327674615 281474976710656 976563 31250000000000 (BSN.log_rat_reduce_isNear 1461633640400 16000000 16 2923267280800 2097152000000 22288309 67108864 24973259072661432 36028797018963968 32000000 1000000000000000 rfl rfl rfl rfl (Ns288p582 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns288p584 := BSN.arctan_dyadic_bound_f 1000 1208980 1 0 8388608 4000000 0 1 1 0 1 1 6938 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1208980) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1208980) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz436 := (@Nat.cast Real Real.instNatCast 1208980)

noncomputable def Ns288p585 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz436)) 884279719003555 562949953421312 1 2000000000000000 6938 8388608 1 4000000 7413970178294136438784 883814117705123 562949953421312 500000001 2000000000000000 qz15 (Ns288p584 rfl) rfl rfl 

noncomputable abbrev qz437 := (@HMul.hMul Real Real Real qz580 qz585 qz626)

noncomputable abbrev qz103 := qz437

noncomputable abbrev qz438 := qz626

noncomputable abbrev qz104 := qz438

noncomputable def Ns288p586 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 604490 4000) qz435) qz103 38870415623320560427 22517998136852480 59032256787 12500000000000000 883814117705123 2251799813685248 500000001 8000000000000000 Ns288p577 38861577482143509197 22517998136852480 957016108617 200000000000000000 (Ns288p583 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz104 1 4 0 1 883814117705123 562949953421312 500000001 2000000000000000 883814117705123 2251799813685248 500000001 8000000000000000 qz363 Ns288p585 rfl) 

noncomputable def Ns288p587 := @Ns288p573 Ns288p567 Ns288p568 2824741575301933 204800000000000000000 (@Ns288p575 2824741575301933 204800000000000000000 (Ns288p576 (Ns288p586 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 604490 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz627 (Real.log Real.pi) 604490 2000 0 1 38410761 33554432 1 33554432 2321892091689 6710886400 60449 6710886400 (Enclosure.Real.IsNear.const Bool.false 604490 2000) RS289to300.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns288p569 Ns288p570) 

noncomputable def Ns288p588 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz96) Bool.false Ns288p567 Ns288p568 2824741575301933 204800000000000000000 9039283505 8388608 29 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz96) (@HAdd.hAdd Real Real Real qz364 qz100 (Enclosure.sfrac Bool.true Ns288p569 Ns288p570)) Bool.false Ns288p567 Ns288p568 2824741575301933 204800000000000000000 Ns288p571 (Ns288p587 rfl rfl)) 

noncomputable def Ns288p589 := nat_lit 1899320173610759314472960 

noncomputable def Ns288p590 := nat_lit 857759956773080300789171966611534789377802728623850532918959478117004465329519741817991445845733872954855932876875907655999034993725921 

noncomputable def Ns288p591 := nat_lit 612322918465886670860734423137806924197953645372797515274256047201371093655038616814392590276567303705016250695115788209178071521 

noncomputable def Ns288p592 := nat_lit 4283466564901875085706237701439354710342298644025192462841812762812614398818519620818146474122501354776461350062115798482141864357581281 

noncomputable def Ns288p593 := BSN.sin_dyadic_bound_f 53981926089 34359738368 4 3 16777216 8007813 Ns288p590 Ns288p229 Ns288p591 Ns288p592 Ns288p232 Ns288p591 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53981926089) qz376 0 3 Ns288p590 Ns288p229 Ns288p591 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53981926089) qz377 0 3 Ns288p592 Ns288p232 Ns288p591 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p594 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz96) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9039283505) qz393) Bool.false 9039283505 8388608 29 2097152 Bool.true 16777215 16777216 1 4000000 (Ns288p588 rfl) (Enclosure.sfrac_false_div 9039283505 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9039283505) qz393) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns288p589) qz394) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 171 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q1 9039283505 8388608 226375608064910080 72057594037927936 171 Ns288p589 Ns288p284 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns288p589 Ns288p284 53981926089 34359738368 8007813 8000000 (Ns288p593 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p595 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz96) Bool.false Ns288p567 Ns288p568 2824741575301933 204800000000000000000 144628536084 134217728 1852 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz96) (@HAdd.hAdd Real Real Real qz364 qz100 (Enclosure.sfrac Bool.true Ns288p569 Ns288p570)) Bool.false Ns288p567 Ns288p568 2824741575301933 204800000000000000000 Ns288p571 (Ns288p587 rfl rfl)) 

noncomputable def Ns288p596 := Ns288p566 30697 BSN.abs_quadSignPos (BSN.cos_quad_nat3 419 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 52567774 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 263 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 45650632 134217728) qz99 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 1) Bool.true 16777215 16777216 461317 32768000000 134217720 134217728 1890 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz96)) Bool.true 16777215 16777216 461317 32768000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz96) qz96) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz96)) Bool.true 16777215 16777216 118097152 8388608000000 16777215 16777216 461317 32768000000 (Ns288p594 rfl rfl) rfl)) rfl) (Ns288p595 rfl) RS289to300.d7 

noncomputable def Ns288p597 := nat_lit 8511864806895444064021952160000 

noncomputable def Ns288p598 := BSN.sin_dyadic_bound_f 54013980 134217728 2 1 134217728 67108864 Ns288p597 Ns288p115 Ns288p597 Ns288p597 Ns288p116 Ns288p597 52567774 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 54013980) qz367 0 1 Ns288p597 Ns288p115 Ns288p597 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 54013980) qz368 0 1 Ns288p597 Ns288p116 Ns288p597 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p599 := nat_lit 4707604702393168660658999150625 

noncomputable def Ns288p600 := BSN.sin_dyadic_bound_f 46580055 134217728 2 1 134217728 67108864 Ns288p599 Ns288p115 Ns288p599 Ns288p599 Ns288p116 Ns288p599 45650632 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 46580055) qz367 0 1 Ns288p599 Ns288p115 Ns288p599 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 46580055) qz368 0 1 Ns288p599 Ns288p116 Ns288p599 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p601 := nat_lit 74136485955510525483610146895480934680649641192790422484608000000000 

noncomputable def Ns288p602 := nat_lit 18482035609683813126734165295571562358562657584010000000000000000 

noncomputable def Ns288p603 := nat_lit 222372493795312208824576972355851660917231798263203247453824000000000 

noncomputable def Ns288p604 := BSN.cos_dyadic_bound_f 107980100 134217728 3 2 134217728 67108864 Ns288p601 Ns288p123 Ns288p602 Ns288p603 Ns288p126 Ns288p602 93074781 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 107980100) qz369 0 2 Ns288p601 Ns288p123 Ns288p602 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 107980100) qz370 0 2 Ns288p603 Ns288p126 Ns288p602 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p605 := nat_lit 180554303195578273107423710113359887083407571526684792074433098506496 

noncomputable def Ns288p606 := nat_lit 109544585483111849565569002202952174462745438522273234259513794816 

noncomputable def Ns288p607 := nat_lit 541443820415768595623139992335673756901297223703009829754780267929856 

noncomputable def Ns288p608 := BSN.cos_dyadic_bound_f 134880406 134217728 3 2 134217728 67108864 Ns288p605 Ns288p123 Ns288p606 Ns288p607 Ns288p126 Ns288p606 71959641 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 134880406) qz369 0 2 Ns288p605 Ns288p123 Ns288p606 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 134880406) qz370 0 2 Ns288p607 Ns288p126 Ns288p606 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p609 := Ns288p564 51939 BSN.abs_quadSignPos (BSN.cos_quad_nat0 152 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 93074781 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 71959641 134217728) qz99 rfl rfl (Ns288p596 RS289to300.d9 RS289to300.d11 RS289to300.d13 RS289to300.d17 (Ns288p598 rfl rfl) (Ns288p600 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns288p595 rfl) RS289to300.d19 RS289to300.d21 RS289to300.d23 RS289to300.d25 RS289to300.d17 (Ns288p604 rfl rfl) (Ns288p608 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns288p610 := nat_lit 145179156550986945995639108052412979171859612175024189126060594151680 

noncomputable def Ns288p611 := nat_lit 21879378900705190952744146415428013752970026511176655908495933696 

noncomputable def Ns288p612 := nat_lit 380195700543888478727036078185932823904032270891664304553925896028416 

noncomputable def Ns288p613 := BSN.sin_dyadic_bound_f 110281934 134217728 3 2 134217728 67108864 Ns288p610 Ns288p109 Ns288p611 Ns288p612 Ns288p112 Ns288p611 98285002 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 110281934) qz367 0 2 Ns288p610 Ns288p109 Ns288p611 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 110281934) qz368 0 2 Ns288p612 Ns288p112 Ns288p611 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p614 := nat_lit 2120607412247937867298646892555624663568743365448386703927992593795895574391982027606577410222334412394496 

noncomputable def Ns288p615 := nat_lit 1021319028686481718264129358784930011607992638166217434236574556603437928818737121124332630464598016 

noncomputable def Ns288p616 := nat_lit 12849199828032644808311714274294860894724342162394778964898750047116649390074483130348610770211784952975360 

noncomputable def Ns288p617 := BSN.cos_dyadic_bound_f 178140822 134217728 4 3 134217728 67108864 Ns288p614 Ns288p137 Ns288p615 Ns288p616 Ns288p140 Ns288p615 32365709 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 178140822) qz369 0 3 Ns288p614 Ns288p137 Ns288p615 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 178140822) qz370 0 3 Ns288p616 Ns288p140 Ns288p615 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p618 := Ns288p562 70049 BSN.abs_quadSignPos (BSN.cos_quad_nat3 3 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 98285002 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 62 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 32365709 134217728) qz99 rfl rfl (Ns288p609 rfl rfl) (Ns288p595 rfl) RS289to300.d27 RS289to300.d29 RS289to300.d31 RS289to300.d33 RS289to300.d17 (Ns288p613 rfl rfl) (Ns288p617 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p619 := nat_lit 3115221842765907599001361447335355881911755312964739454899259626561 

noncomputable def Ns288p620 := nat_lit 32649101078017170932775009175572958998158089059039161781769281 

noncomputable def Ns288p621 := nat_lit 9345600230095566762662218791987716499817269622716100286374215341121 

noncomputable def Ns288p622 := BSN.cos_dyadic_bound_f 48891561 134217728 3 2 134217728 67108864 Ns288p619 Ns288p123 Ns288p620 Ns288p621 Ns288p126 Ns288p620 125410884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 48891561) qz369 0 2 Ns288p619 Ns288p123 Ns288p620 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 48891561) qz370 0 2 Ns288p621 Ns288p126 Ns288p620 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p623 := nat_lit 188471719142494442320315767982069774921412365734634020655629090787105 

noncomputable def Ns288p624 := nat_lit 36870566375190144032013174109082527335102940665825665843075845921 

noncomputable def Ns288p625 := nat_lit 493556712075258945843822799575910895940394600734392050639092162596641 

noncomputable def Ns288p626 := BSN.sin_dyadic_bound_f 117715859 134217728 3 2 134217728 67108864 Ns288p623 Ns288p109 Ns288p624 Ns288p625 Ns288p112 Ns288p624 103194224 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 117715859) qz367 0 2 Ns288p623 Ns288p109 Ns288p624 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 117715859) qz368 0 2 Ns288p625 Ns288p112 Ns288p624 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p627 := Ns288p560 85458 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 114 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 125410884 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 103194224 134217728) qz99 rfl rfl (Ns288p618 rfl) (Ns288p595 rfl) RS289to300.d35 RS289to300.d37 RS289to300.d39 RS289to300.d41 RS289to300.d17 (Ns288p622 rfl rfl) (Ns288p626 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p628 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 9) 38384007 134217728 85458 134217728 38384007 134217728 85458 134217728 10303628422152192 38384007 67108864 42729 33554432 (Ns288p627 rfl) 

noncomputable def Ns288p629 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz97) (Zeta.RiemannSiegel.correction qz98) 2678475 8388608 1 8388608 79845061267767 140737488355328 236268144326669 2199023255552000000 213863000479182215325 1180591620717411303424 

noncomputable def Ns288p630 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz97 1 1 0 1 2678475 8388608 1 8388608 2678475 8388608 1 8388608 

noncomputable abbrev qz105 := qz431

noncomputable def Ns288p631 := @Enclosure.Real.IsNear.sqrt_image qz105 161409529473 1677721600 60449 1677721600 82280032 82280064 8388608 (@Enclosure.Real.IsNear.of_eq qz105 (@HMul.hMul Real Real Real qz5 qz96 qz3) Bool.false 161409529473 1677721600 60449 1677721600 (BSN.t_div_two_pi_mk qz96 604490 1000 qz99) (@Enclosure.Real.IsNear.mulLit_ff qz96 qz3 604490 1000 0 1 2670177 16777216 1 16777216 161409529473 1677721600 60449 1677721600 (Enclosure.Real.IsNear.const Bool.false 604490 1000) RS289to300.d44 rfl)) 

noncomputable abbrev qz732 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 604490 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz628 := qz732

noncomputable abbrev qz439 := qz628

noncomputable abbrev qz106 := qz439

noncomputable def Ns288p632 := @Enclosure.Real.IsNear.sqrt_image qz106 5142503 524288 1 524288 26271941 26271948 8388608 (@Enclosure.Real.IsNear.recentre' qz106 Bool.false 164560096 16777216 32 16777216 5142503 524288 1 524288 (Ns288p631 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns288p633 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz106) 52543889 16777216 7 16777216 2678474 2678476 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz106) Bool.false 52543889 16777216 7 16777216 52543889 16777216 7 16777216 (Ns288p632 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns288p634 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz106)) Bool.false 5356950 16777216 2 16777216 2678475 8388608 1 8388608 (Ns288p633 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz107 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz432))

noncomputable abbrev qz629 := (@HMul.hMul Real Real Real qz708 qz731 qz731)

noncomputable abbrev qz440 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz629 qz624) qz594)

noncomputable abbrev qz108 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz440))

noncomputable def Ns288p635 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz98) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz107) qz108) Bool.false 79845061267767 

noncomputable def Ns288p636 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz107) qz108 46653213 16777216 1595 

noncomputable def Ns288p637 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz107) Bool.false 46653213 16777216 1595 16777216 46653213 16777216 1595 

noncomputable def Ns288p638 := @Enclosure.Real.IsNear.recentre' qz107 Bool.false 6033346 16777216 412388608 33554432000000 3016673 8388608 1610893 131072000000 

noncomputable abbrev qz109 := (@HMul.hMul Real Real Real qz346 qz343 qz432)

noncomputable def Ns288p639 := @Enclosure.Real.IsNear.cos_image qz109 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 85232363) qz365) Bool.false 85232363 16777216 101 8388608 Bool.false 6033346 16777216 1 

noncomputable def Ns288p640 := nat_lit 26986075412685413217998279 

noncomputable def Ns288p641 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz98 884279719003555 140737488355328 1 500000000000000 423911 524288 1 524288 374855899962516003605 73786976294838206464 Ns288p640 

noncomputable def Ns288p642 := @Enclosure.Real.IsNear.subLit_ff_p qz106 qz1 5142503 524288 1 524288 9 1 0 1 423911 423911 524288 1 

noncomputable def Ns288p643 := @Ns288p642 524288 (@Enclosure.Real.IsNear.recentre' qz106 Bool.false 164560096 16777216 32 16777216 5142503 524288 1 524288 (Ns288p631 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns288p644 := @Enclosure.Real.IsNear.recentre' qz109 Bool.false 374855899962516003605 73786976294838206464 Ns288p640 Ns288p162 85232363 16777216 101 8388608 (@Ns288p641 Ns288p162 RS289to300.d43 (Ns288p643 rfl rfl) rfl) 

noncomputable def Ns288p645 := nat_lit 25521696482600773088340107293048335895521 

noncomputable def Ns288p646 := BSN.sin_dyadic_bound_f 12639426969 34359738368 2 1 16777216 8007813 Ns288p645 Ns288p168 Ns288p645 Ns288p645 Ns288p169 Ns288p645 6033346 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 12639426969) qz376 0 1 Ns288p645 Ns288p168 Ns288p645 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 12639426969) qz377 0 1 Ns288p645 Ns288p169 Ns288p645 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p647 := @Ns288p639 4000000 (Ns288p644 rfl) (Enclosure.sfrac_false_div 85232363 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 85232363) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 889420602985603919773696) qz366) 226375608064910080 72057594037927936 Bool.false 6033346 16777216 0 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q3 85232363 16777216 226375608064910080 72057594037927936 0 889420602985603919773696 Ns288p93 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 6033346 16777216 889420602985603919773696 Ns288p93 12639426969 34359738368 8007813 8000000 (Ns288p646 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p648 := @Enclosure.Real.IsNear.inv_image qz107 3016673 8388608 1610893 131072000000 23325809 23327404 8388608 (Ns288p638 (Ns288p647 rfl rfl) rfl) rfl 

noncomputable def Ns288p649 := @Enclosure.Real.IsNear.recentre' qz108 Bool.false 1711459 8388608 

noncomputable abbrev qz110 := (@HMul.hMul Real Real Real qz346 qz343 qz440)

noncomputable def Ns288p650 := @Enclosure.Real.IsNear.cos_image qz110 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 5726617)) qz413) Bool.true 5726617 4194304 

noncomputable def Ns288p651 := nat_lit 52818720565082822624808205 

noncomputable def Ns288p652 := nat_lit 38685626227668133590597632 

noncomputable def Ns288p653 := nat_lit 37027890916091917778056540742889 

noncomputable def Ns288p654 := @Enclosure.Real.IsNear.recentre' qz110 Bool.true Ns288p651 Ns288p652 Ns288p653 

noncomputable def Ns288p655 := nat_lit 1180591620717411303424000000000000000 

noncomputable abbrev qz111 := qz440

noncomputable def Ns288p656 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz111 884279719003555 140737488355328 1 500000000000000 59730783631 

noncomputable abbrev qz441 := (@HSub.hSub Real Real Real qz584 qz629 qz624)

noncomputable abbrev qz112 := qz441

noncomputable def Ns288p657 := @Enclosure.Real.IsNear.subLit_tf qz112 qz29 42550914447 274877906944 1372111 274877906944 1 16 

noncomputable abbrev qz442 := qz629

noncomputable abbrev qz113 := qz442

noncomputable def Ns288p658 := @Enclosure.Real.IsNear.subLit_ff_n qz113 qz98 179700535921 274877906944 847823 274877906944 423911 524288 1 524288 

noncomputable def Ns288p659 := @Enclosure.Real.IsNear.mulLit_ff qz98 qz98 423911 524288 1 524288 423911 524288 1 524288 179700535921 274877906944 

noncomputable def Ns288p660 := nat_lit 2060132530844147081752568255780726440435565075544373519191581039801065613368318416654241 

noncomputable def Ns288p661 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600 

noncomputable def Ns288p662 := nat_lit 1243877631793311770067575817459424757790507414336147975397897261352218420363923361 

noncomputable def Ns288p663 := nat_lit 12480932176529377149700110588694543846691935981602548666887433616813480595446895016939425 

noncomputable def Ns288p664 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600 

noncomputable def Ns288p665 := BSN.cos_dyadic_bound_f 5726617 4194304 4 3 8388608 4000000 Ns288p660 Ns288p661 Ns288p662 Ns288p663 Ns288p664 Ns288p662 1711459 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 5726617) (BSN.cosEvenQ 4194304) 0 3 Ns288p660 Ns288p661 Ns288p662 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 5726617) (BSN.cosOddQ 4194304) 0 3 Ns288p663 Ns288p664 Ns288p662 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p666 := @Ns288p649 2124777216 67108864000000 1711459 8388608 8299911 262144000000 (@Ns288p650 527 16777216 Bool.false 1711459 8388608 1 4000000 (@Ns288p654 Ns288p655 5726617 4194304 527 16777216 (@Ns288p656 274877906944 1372111 274877906944 Ns288p651 Ns288p652 Ns288p653 Ns288p655 RS289to300.d43 (@Ns288p657 0 1 955692538096 59730783631 274877906944 1372111 274877906944 (@Ns288p658 22308933833588736 42550914447 274877906944 1372111 274877906944 (@Ns288p659 847823 274877906944 (Ns288p643 rfl rfl) (Ns288p643 rfl rfl) rfl) (Ns288p643 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 5726617 4194304) (BSN.cos_neg_of_bound 5726617 4194304 Bool.false 1711459 8388608 1 4000000 (Ns288p665 rfl rfl)) rfl rfl) 

noncomputable def Ns288p667 := @Ns288p629 634086133225827935819 Ns288p451 (Ns288p630 qz31 (@Enclosure.Real.IsNear.of_eq qz97 (@Inv.inv Real Real.instInv (Real.sqrt qz106)) Bool.false 2678475 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz105 (BSN.t_div_two_pi_nonneg qz96 604490 1000 qz99)) Ns288p634) rfl) (@Ns288p635 140737488355328 236268144326669 2199023255552000000 (BSN.correction_mk qz98 (BSN.cos_two_pi_p_ne_zero_mk qz96 604490 1000 9 qz99 rfl rfl (@BSN.floor_sqrt_eq_dec qz96 604490 1000 9 qz99 rfl rfl rfl))) (@Ns288p636 16777216 1711459 8388608 8299911 262144000000 79845061267767 140737488355328 236268144326669 2199023255552000000 (@Ns288p637 16777216 (Ns288p648 rfl rfl rfl rfl rfl) rfl) (Ns288p666 rfl) rfl)) 

noncomputable def Ns288p668 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz96) (hardyZApproximantRS₀ qz96) Bool.true 461395591794983839587 1180591620717411303424 24124602304846179935819 Ns288p451 (@Eq.refl Real (hardyZApproximantRS₀ qz96)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz96) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz97) (Zeta.RiemannSiegel.correction qz98))) Bool.true 461395591794983839587 1180591620717411303424 24124602304846179935819 Ns288p451 (BSN.hardyZApproximantRS₀_eq qz96 9 (@BSN.floor_sqrt_eq_dec qz96 604490 1000 9 qz99 rfl rfl rfl)) (@Ns288p558 461395591794983839587 1180591620717411303424 24124602304846179935819 Ns288p451 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 9) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 9)) Bool.true 38384007 67108864 42729 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz96) qz96 9) (Ns288p628 (Ns288p627 rfl) rfl rfl)) (Ns288p667 rfl) rfl rfl)) 

theorem RS289to300.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz96) Bool.true 461395591794983839587 1180591620717411303424 24124602304846179935819 Ns288p451 := Ns288p668 

noncomputable def Ns288p669 := nat_lit 2001488179174431547142963200 

noncomputable abbrev qz733 := (Enclosure.sfrac Bool.false 605865 1000)

noncomputable abbrev qz630 := qz733

noncomputable abbrev qz443 := qz630

noncomputable abbrev qz114 := qz443

noncomputable abbrev qz734 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 605865 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz631 := qz734

noncomputable abbrev qz444 := qz631

noncomputable abbrev qz115 := (@HPow.hPow Real Real Real qz347 qz444 qz349)

noncomputable abbrev qz735 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 605865 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz632 := qz735

noncomputable abbrev qz445 := qz632

noncomputable abbrev qz116 := qz445

noncomputable def Ns288p670 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz115) (Zeta.RiemannSiegel.correction qz116)) 102266425 33554432 21415 16777216 3427434261626577825 18446744073709551616 2722067129820945741 92233720368547758080000 Ns288p669 

noncomputable def Ns288p671 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 605865 1000 114 159 134217728 67108864 2251799813685248 Bool.false 145050013820 1857 

noncomputable def Ns288p672 := Ns288p671 279097919 34 47453128 8 294906479 34 44739240 8 Bool.false 221065343 70215 Bool.true 11173463 Bool.true 101734532 7074237752028440 1 Bool.false 133752907 Bool.true Bool.false 92268894 Bool.false Bool.false 204532850 

noncomputable def Ns288p673 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 605865 1000 3 62 134217728 67108864 2251799813685248 Bool.false 145050013820 1857 

noncomputable def Ns288p674 := Ns288p673 240485871 35 54794152 8 261175631 35 50729528 8 Bool.false 246140490 52063 Bool.true 19472271 Bool.true 115779579 7074237752028440 1 Bool.false 19404033 Bool.false Bool.false 87301360 Bool.true Bool.false 221065343 

noncomputable def Ns288p675 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 605865 1000 153 67 134217728 67108864 2251799813685248 Bool.false 145050013820 1857 

noncomputable def Ns288p676 := Ns288p675 186065264 34 67108856 8 216015088 34 60023992 8 Bool.false 255177974 30772 Bool.false 62789384 Bool.false 48508681 7074237752028440 1 Bool.false 60524040 Bool.true Bool.false 47459499 Bool.false Bool.false 246140490 

noncomputable def Ns288p677 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 605865 1000 420 264 134217728 67108864 2251799813685248 Bool.false 145050013820 1857 

noncomputable def Ns288p678 := Ns288p677 93032624 34 94906264 8 147453232 34 77490640 16 Bool.false 134217648 1898 Bool.false 136743144 Bool.false 54480883 7074237752028440 1 Bool.false 70380372 Bool.false Bool.false 123311436 Bool.false Bool.false 255177974 

noncomputable def Ns288p679 := nat_lit 770324515556452792520518314541438048512453648920319 

noncomputable def Ns288p680 := nat_lit 712796942084425165299793663988400640194982707200 

noncomputable def Ns288p681 := nat_lit 39185131611722408834791639500000000 

noncomputable def Ns288p682 := nat_lit 142445443857215947318598358604005000000 

noncomputable abbrev qz633 := (@Eq.refl Real qz733)

noncomputable abbrev qz446 := qz633

noncomputable abbrev qz117 := qz446

noncomputable def Ns288p683 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz114 605865 1000 1468290592900 16000000 1211730 4000 2000 Ns288p681 Ns288p682 qz117 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns288p684 := nat_lit 34664603200040375663423324154364712183060414201414355000000 

noncomputable abbrev qz634 := (@HSub.hSub Real Real Real qz712 qz713 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz714 (@Nat.cast Real Real.instNatCast 1211730))))

noncomputable abbrev qz447 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz580 (Enclosure.sfrac Bool.false 605865 4000) (Real.log (Enclosure.sfrac Bool.false 1468290592900 16000000))) (@HMul.hMul Real Real Real qz580 qz585 qz634))

noncomputable abbrev qz635 := (Enclosure.sfrac Bool.false 605865 2000)

noncomputable abbrev qz118 := (@HSub.hSub Real Real Real qz352 (@HSub.hSub Real Real Real qz352 qz447 qz635) (@HMul.hMul Real Real Real qz346 qz635 (Real.log Real.pi)))

noncomputable def Ns288p685 := @Enclosure.Real.IsNear.addLit_ft_p qz118 (Enclosure.sfrac Bool.true Ns288p681 Ns288p682) 243353603211729226071 225179981368524800 5662275486841041 409600000000000000000 Ns288p681 Ns288p682 0 1 Ns288p684 

noncomputable def Ns288p686 := nat_lit 3266236772369179967444798668800 

noncomputable abbrev qz119 := (@HSub.hSub Real Real Real qz352 qz447 qz635)

noncomputable def Ns288p687 := @Enclosure.Real.IsNear.subLit_ff_p qz119 (@HMul.hMul Real Real Real qz5 qz635 (Real.log Real.pi)) 321440590563001420119 225179981368524800 959164547217 200000000000000000 4654347142653 13421772800 121173 13421772800 Ns288p686 243353603211729226071 225179981368524800 

noncomputable abbrev qz120 := qz447

noncomputable def Ns288p688 := @Enclosure.Real.IsNear.subLit_ff_p qz120 qz635 77930985053784411819 45035996273704960 959164547217 200000000000000000 605865 2000 0 1 128576236225200568047600 321440590563001420119 225179981368524800 959164547217 200000000000000000 

noncomputable def Ns288p689 := nat_lit 175484977624419585122474850477146112 

noncomputable def Ns288p690 := nat_lit 27628840690411915370823680 

noncomputable def Ns288p691 := nat_lit 1521645124204489878763576920140668502329076614510809845024355603599884659129843578841450000000000000000 

noncomputable def Ns288p692 := nat_lit 14345348799212355521922283859396792316208799035663213157757098186427028272625058541840000000000000000 

noncomputable def Ns288p693 := nat_lit 101116459188407228506530015474353710838794980858566756539131755181681788685649050000000000000000 

noncomputable def Ns288p694 := BSN.log_dyadic_bound 419714592900 2516866592900 5 4 Ns288p691 67108864 32000000 Ns288p692 Ns288p693 22593259 2936581185800 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 419714592900) (BSN.artanhQ 2516866592900) 0 4 Ns288p692 Ns288p691 Ns288p693 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz448 := (Real.log (Enclosure.sfrac Bool.false 1468290592900 16000000))

noncomputable def Ns288p695 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 605865 4000) qz448 605865 4000 0 1 3216420380679415 281474976710656 976563 31250000000000 77948661357613350759 45035996273704960 118333068399 25000000000000000 (Enclosure.Real.IsNear.const Bool.false 605865 4000) (BSN.isNear_log_sfrac 1468290592900 16000000 3216420380679415 281474976710656 976563 31250000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1468290592900) qz355)) Bool.false Ns288p690 Ns288p93 1000000512000000 32000000000000000000000 3216420380679415 281474976710656 976563 31250000000000 (BSN.log_rat_reduce_isNear 1468290592900 16000000 16 2936581185800 2097152000000 22593259 67108864 24973259072661432 36028797018963968 32000000 1000000000000000 rfl rfl rfl rfl (Ns288p694 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns288p696 := BSN.arctan_dyadic_bound_f 1000 1211730 1 0 8388608 4000000 0 1 1 0 1 1 6922 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1211730) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1211730) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz449 := (@Nat.cast Real Real.instNatCast 1211730)

noncomputable def Ns288p697 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz449)) 884279719003555 562949953421312 1 2000000000000000 6922 8388608 1 4000000 7413979185493391179776 883815191446947 562949953421312 500000001 2000000000000000 qz15 (Ns288p696 rfl) rfl rfl 

noncomputable abbrev qz450 := (@HMul.hMul Real Real Real qz580 qz585 qz634)

noncomputable abbrev qz121 := qz450

noncomputable abbrev qz451 := qz634

noncomputable abbrev qz122 := qz451

noncomputable def Ns288p698 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 605865 4000) qz448) qz121 77948661357613350759 45035996273704960 118333068399 25000000000000000 883815191446947 2251799813685248 500000001 8000000000000000 Ns288p689 77930985053784411819 45035996273704960 959164547217 200000000000000000 (Ns288p695 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz122 1 4 0 1 883815191446947 562949953421312 500000001 2000000000000000 883815191446947 2251799813685248 500000001 8000000000000000 qz363 Ns288p697 rfl) 

noncomputable def Ns288p699 := @Ns288p685 Ns288p679 Ns288p680 5662275486841041 409600000000000000000 (@Ns288p687 5662275486841041 409600000000000000000 (Ns288p688 (Ns288p698 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 605865 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz635 (Real.log Real.pi) 605865 2000 0 1 38410761 33554432 1 33554432 4654347142653 13421772800 121173 13421772800 (Enclosure.Real.IsNear.const Bool.false 605865 2000) RS289to300.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns288p681 Ns288p682) 

noncomputable def Ns288p700 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz114) Bool.false Ns288p679 Ns288p680 5662275486841041 409600000000000000000 18131251727 16777216 233 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz114) (@HAdd.hAdd Real Real Real qz364 qz118 (Enclosure.sfrac Bool.true Ns288p681 Ns288p682)) Bool.false Ns288p679 Ns288p680 5662275486841041 409600000000000000000 Ns288p683 (Ns288p699 rfl rfl)) 

noncomputable def Ns288p701 := nat_lit 3795403299127082912579584 

noncomputable def Ns288p702 := nat_lit 854834042817001413945018292375802044847737121248117661162918311574580306408260775559879677140670679469960338944660041869453719833518161 

noncomputable def Ns288p703 := nat_lit 606090619735577163217678691500280139888526554878793298279119439256784251541725959082151968566705584527402975458975817094518906961 

noncomputable def Ns288p704 := nat_lit 4268873253180181526039771144584575212992953584460797310335292237851741062097805680670903516863507496762366079249727623493282812369674321 

noncomputable def Ns288p705 := BSN.sin_dyadic_bound_f 53935924869 34359738368 4 3 16777216 8007813 Ns288p702 Ns288p229 Ns288p703 Ns288p704 Ns288p232 Ns288p703 16777206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53935924869) qz376 0 3 Ns288p702 Ns288p229 Ns288p703 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53935924869) qz377 0 3 Ns288p704 Ns288p232 Ns288p703 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p706 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz114) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18131251727) qz365) Bool.false 18131251727 16777216 233 16777216 Bool.false 16777206 16777216 1 4000000 (Ns288p700 rfl) (Enclosure.sfrac_false_div 18131251727 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18131251727) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns288p701) qz366) 226375608064910080 72057594037927936 Bool.false 16777206 16777216 171 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q3 18131251727 16777216 226375608064910080 72057594037927936 171 Ns288p701 Ns288p93 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777206 16777216 Ns288p701 Ns288p93 53935924869 34359738368 8007813 8000000 (Ns288p705 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p707 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz114) Bool.false Ns288p679 Ns288p680 5662275486841041 409600000000000000000 145050013820 134217728 1857 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz114) (@HAdd.hAdd Real Real Real qz364 qz118 (Enclosure.sfrac Bool.true Ns288p681 Ns288p682)) Bool.false Ns288p679 Ns288p680 5662275486841041 409600000000000000000 Ns288p683 (Ns288p699 rfl rfl)) 

noncomputable def Ns288p708 := Ns288p678 30772 BSN.abs_quadSignPos (BSN.cos_quad_nat0 420 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 70380372 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 264 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 123311436 134217728) qz117 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 1) Bool.false 8388603 8388608 3706161 262144000000 134217648 134217728 1898 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz114)) Bool.false 8388603 8388608 3706161 262144000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz114) qz114) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz114)) Bool.false 16777206 16777216 948777216 67108864000000 8388603 8388608 3706161 262144000000 (Ns288p706 rfl rfl) rfl)) rfl) (Ns288p707 rfl) RS289to300.d7 

noncomputable def Ns288p709 := nat_lit 190743386516391150266748533699609140119573173205271939303095555588096 

noncomputable def Ns288p710 := nat_lit 122248767094138699066262063453085475818202077648565231980606652416 

noncomputable def Ns288p711 := nat_lit 571985662014985173402113076971921249407083115460518687445325453459456 

noncomputable def Ns288p712 := BSN.cos_dyadic_bound_f 136743144 134217728 3 2 134217728 67108864 Ns288p709 Ns288p123 Ns288p710 Ns288p711 Ns288p126 Ns288p710 70380372 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 136743144) qz369 0 2 Ns288p709 Ns288p123 Ns288p710 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 136743144) qz370 0 2 Ns288p711 Ns288p126 Ns288p710 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p713 := nat_lit 4803218934239756052301632026468472962640323230939083766854807359521 

noncomputable def Ns288p714 := nat_lit 77616329752995923435802802211812918672989451451830893841911841 

noncomputable def Ns288p715 := nat_lit 14409501570059762165058024473800995262083623713914347638776738254881 

noncomputable def Ns288p716 := BSN.cos_dyadic_bound_f 54480883 134217728 3 2 134217728 67108864 Ns288p713 Ns288p123 Ns288p714 Ns288p715 Ns288p126 Ns288p714 123311436 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 54480883) qz369 0 2 Ns288p713 Ns288p123 Ns288p714 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 54480883) qz370 0 2 Ns288p715 Ns288p126 Ns288p714 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p717 := nat_lit 15543359419384679950273507495936 

noncomputable def Ns288p718 := BSN.sin_dyadic_bound_f 62789384 134217728 2 1 134217728 67108864 Ns288p717 Ns288p115 Ns288p717 Ns288p717 Ns288p116 Ns288p717 60524040 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 62789384) qz367 0 1 Ns288p717 Ns288p115 Ns288p717 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 62789384) qz368 0 1 Ns288p717 Ns288p116 Ns288p717 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p719 := nat_lit 5537042583373406981130331977121 

noncomputable def Ns288p720 := BSN.sin_dyadic_bound_f 48508681 134217728 2 1 134217728 67108864 Ns288p719 Ns288p115 Ns288p719 Ns288p719 Ns288p116 Ns288p719 47459499 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 48508681) qz367 0 1 Ns288p719 Ns288p115 Ns288p719 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 48508681) qz368 0 1 Ns288p719 Ns288p116 Ns288p719 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p721 := Ns288p676 52063 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 153 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 60524040 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 67 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 47459499 134217728) qz117 rfl rfl (Ns288p708 RS289to300.d9 RS289to300.d11 RS289to300.d13 RS289to300.d17 (Ns288p712 rfl rfl) (Ns288p716 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns288p707 rfl) RS289to300.d19 RS289to300.d21 RS289to300.d23 RS289to300.d25 RS289to300.d17 (Ns288p718 rfl rfl) (Ns288p720 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns288p722 := nat_lit 143769386801583787738634348481 

noncomputable def Ns288p723 := BSN.sin_dyadic_bound_f 19472271 134217728 2 1 134217728 67108864 Ns288p722 Ns288p115 Ns288p722 Ns288p722 Ns288p116 Ns288p722 19404033 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 19472271) qz367 0 1 Ns288p722 Ns288p115 Ns288p722 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 19472271) qz368 0 1 Ns288p722 Ns288p116 Ns288p722 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p724 := nat_lit 97998582705869832793648078567695134153092004060617007387838205507041 

noncomputable def Ns288p725 := nat_lit 32289084262783478117758674312683249081167750905825559763984430561 

noncomputable def Ns288p726 := nat_lit 293931169949083931424708718354460035961113676680039371043986647660001 

noncomputable def Ns288p727 := BSN.cos_dyadic_bound_f 115779579 134217728 3 2 134217728 67108864 Ns288p724 Ns288p123 Ns288p725 Ns288p726 Ns288p126 Ns288p725 87301360 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 115779579) qz369 0 2 Ns288p724 Ns288p123 Ns288p725 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 115779579) qz370 0 2 Ns288p726 Ns288p126 Ns288p725 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p728 := Ns288p674 70215 BSN.abs_quadSignPos (BSN.cos_quad_nat3 3 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 19404033 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 62 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 87301360 134217728) qz117 rfl rfl (Ns288p721 rfl rfl) (Ns288p707 rfl) RS289to300.d27 RS289to300.d29 RS289to300.d31 RS289to300.d33 RS289to300.d17 (Ns288p723 rfl rfl) (Ns288p727 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p729 := nat_lit 15586592484341092320998192161 

noncomputable def Ns288p730 := BSN.cos_dyadic_bound_f 11173463 134217728 2 1 134217728 67108864 Ns288p729 Ns288p132 Ns288p729 Ns288p729 Ns288p133 Ns288p729 133752907 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 11173463) qz369 0 1 Ns288p729 Ns288p132 Ns288p729 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 11173463) qz370 0 1 Ns288p729 Ns288p133 Ns288p729 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p731 := nat_lit 105133782233930068358490737147899930027943856585701884626538472734720 

noncomputable def Ns288p732 := nat_lit 11474853052399707040647376767967514125554219115902488933553995776 

noncomputable def Ns288p733 := nat_lit 275331803707732008079886120586875488383649679464936331896946436407296 

noncomputable def Ns288p734 := BSN.sin_dyadic_bound_f 101734532 134217728 3 2 134217728 67108864 Ns288p731 Ns288p109 Ns288p732 Ns288p733 Ns288p112 Ns288p732 92268894 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 101734532) qz367 0 2 Ns288p731 Ns288p109 Ns288p732 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 101734532) qz368 0 2 Ns288p733 Ns288p112 Ns288p732 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p735 := Ns288p672 85660 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 114 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133752907 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 92268894 134217728) qz117 rfl rfl (Ns288p728 rfl) (Ns288p707 rfl) RS289to300.d35 RS289to300.d37 RS289to300.d39 RS289to300.d41 RS289to300.d17 (Ns288p730 rfl rfl) (Ns288p734 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p736 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 9) 204532850 134217728 85660 134217728 204532850 134217728 85660 134217728 54903868856729600 102266425 33554432 21415 16777216 (Ns288p735 rfl) 

noncomputable def Ns288p737 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz115) (Zeta.RiemannSiegel.correction qz116) 1338477 4194304 1 8388608 2560697166725 4398046511104 5072303021351 54975581388800000 3427434261626577825 18446744073709551616 

noncomputable def Ns288p738 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz115 1 1 0 1 1338477 4194304 1 8388608 1338477 4194304 1 8388608 

noncomputable abbrev qz123 := qz444

noncomputable def Ns288p739 := @Enclosure.Real.IsNear.sqrt_image qz123 323553357621 3355443200 121173 3355443200 82373558 82373590 8388608 (@Enclosure.Real.IsNear.of_eq qz123 (@HMul.hMul Real Real Real qz5 qz114 qz3) Bool.false 323553357621 3355443200 121173 3355443200 (BSN.t_div_two_pi_mk qz114 605865 1000 qz117) (@Enclosure.Real.IsNear.mulLit_ff qz114 qz3 605865 1000 0 1 2670177 16777216 1 16777216 323553357621 3355443200 121173 3355443200 (Enclosure.Real.IsNear.const Bool.false 605865 1000) RS289to300.d44 rfl)) 

noncomputable abbrev qz736 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 605865 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz636 := qz736

noncomputable abbrev qz452 := qz636

noncomputable abbrev qz124 := qz452

noncomputable def Ns288p740 := @Enclosure.Real.IsNear.sqrt_image qz124 41186787 4194304 1 524288 26286869 26286875 8388608 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 164747148 16777216 32 16777216 41186787 4194304 1 524288 (Ns288p739 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns288p741 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz124) 3285859 1048576 3 8388608 2676953 2676955 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz124) Bool.false 52573744 16777216 6 16777216 3285859 1048576 3 8388608 (Ns288p740 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns288p742 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz124)) Bool.false 5353908 16777216 2 16777216 1338477 4194304 1 8388608 (Ns288p741 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz125 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz445))

noncomputable abbrev qz637 := (@HMul.hMul Real Real Real qz708 qz735 qz735)

noncomputable abbrev qz453 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz637 qz632) qz594)

noncomputable abbrev qz126 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz453))

noncomputable def Ns288p743 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz116) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz125) qz126) Bool.false 2560697166725 

noncomputable def Ns288p744 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz125) qz126 4945579 2097152 287 

noncomputable def Ns288p745 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz125) Bool.false 39564632 16777216 1148 16777216 4945579 2097152 287 

noncomputable def Ns288p746 := @Enclosure.Real.IsNear.recentre' qz125 Bool.false 7114308 16777216 412388608 33554432000000 1778577 4194304 1610893 131072000000 

noncomputable abbrev qz127 := (@HMul.hMul Real Real Real qz346 qz343 qz445)

noncomputable def Ns288p747 := @Enclosure.Real.IsNear.cos_image qz127 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43203823) qz393) Bool.false 43203823 8388608 101 8388608 Bool.false 7114308 16777216 1 

noncomputable def Ns288p748 := nat_lit 26986075412735624606913991 

noncomputable def Ns288p749 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz116 884279719003555 140737488355328 1 500000000000000 3438051 4194304 1 524288 3040198772199891271305 590295810358705651712 Ns288p748 

noncomputable def Ns288p750 := @Enclosure.Real.IsNear.subLit_ff_p qz124 qz1 41186787 4194304 1 524288 9 1 0 1 3438051 3438051 4194304 1 

noncomputable def Ns288p751 := @Ns288p750 524288 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 164747148 16777216 32 16777216 41186787 4194304 1 524288 (Ns288p739 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns288p752 := @Enclosure.Real.IsNear.recentre' qz127 Bool.false 3040198772199891271305 590295810358705651712 Ns288p748 Ns288p162 43203823 8388608 101 8388608 (@Ns288p749 Ns288p162 RS289to300.d43 (Ns288p751 rfl rfl) rfl) 

noncomputable def Ns288p753 := nat_lit 51254401783536168372967768342823331392481 

noncomputable def Ns288p754 := BSN.sin_dyadic_bound_f 15046406553 34359738368 2 1 16777216 8007813 Ns288p753 Ns288p168 Ns288p753 Ns288p753 Ns288p169 Ns288p753 7114308 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 15046406553) qz376 0 1 Ns288p753 Ns288p168 Ns288p753 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 15046406553) qz377 0 1 Ns288p753 Ns288p169 Ns288p753 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p755 := @Ns288p747 4000000 (Ns288p752 rfl) (Enclosure.sfrac_false_div 43203823 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43203823) qz393) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 529398366786480018292736) qz394) 226375608064910080 72057594037927936 Bool.false 7114308 16777216 0 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q3 43203823 8388608 226375608064910080 72057594037927936 0 529398366786480018292736 Ns288p284 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 7114308 16777216 529398366786480018292736 Ns288p284 15046406553 34359738368 8007813 8000000 (Ns288p754 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p756 := @Enclosure.Real.IsNear.inv_image qz125 1778577 4194304 1610893 131072000000 19781742 19782890 8388608 (Ns288p746 (Ns288p755 rfl rfl) rfl) rfl 

noncomputable def Ns288p757 := @Enclosure.Real.IsNear.recentre' qz126 Bool.false 2071100 8388608 

noncomputable abbrev qz128 := (@HMul.hMul Real Real Real qz346 qz343 qz453)

noncomputable def Ns288p758 := @Enclosure.Real.IsNear.cos_image qz128 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 22168107)) qz365) Bool.true 22168107 16777216 

noncomputable def Ns288p759 := nat_lit 3271435275323387012378963845 

noncomputable def Ns288p760 := nat_lit 149373513508654643426250472790417 

noncomputable def Ns288p761 := @Enclosure.Real.IsNear.recentre' qz128 Bool.true Ns288p759 Ns288p176 Ns288p760 

noncomputable abbrev qz129 := qz453

noncomputable def Ns288p762 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz129 884279719003555 140737488355328 1 500000000000000 3699548010679 

noncomputable abbrev qz454 := (@HSub.hSub Real Real Real qz584 qz637 qz632)

noncomputable abbrev qz130 := qz454

noncomputable def Ns288p763 := @Enclosure.Real.IsNear.subLit_tf qz130 qz29 2600036382903 17592186044416 5535207 1099511627776 1 16 

noncomputable abbrev qz455 := qz637

noncomputable abbrev qz131 := qz455

noncomputable def Ns288p764 := @Enclosure.Real.IsNear.subLit_ff_n qz131 qz116 11820194678601 17592186044416 3438055 1099511627776 3438051 4194304 1 524288 

noncomputable def Ns288p765 := @Enclosure.Real.IsNear.mulLit_ff qz116 qz116 3438051 4194304 1 524288 3438051 4194304 1 524288 11820194678601 17592186044416 

noncomputable def Ns288p766 := nat_lit 32202571850652194180317023823187415391269238918788131458563681 

noncomputable def Ns288p767 := nat_lit 253092741970790968397859029543733109897246971520789871559966720 

noncomputable def Ns288p768 := nat_lit 58321525085847118216088097367083529801172565410701795311201 

noncomputable def Ns288p769 := nat_lit 96491072501784888304518895274828079114205371625542990785068641 

noncomputable def Ns288p770 := nat_lit 11389173388685593577903656329467989945376113718435544220198502400 

noncomputable def Ns288p771 := BSN.cos_dyadic_bound_f 22168107 16777216 3 2 8388608 4000000 Ns288p766 Ns288p767 Ns288p768 Ns288p769 Ns288p770 Ns288p768 2071100 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 22168107) qz595 0 2 Ns288p766 Ns288p767 Ns288p768 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 22168107) (BSN.cosOddQ 16777216) 0 2 Ns288p769 Ns288p770 Ns288p768 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p772 := @Ns288p757 536194304 16777216000000 517775 2097152 2094509 65536000000 (@Ns288p758 133 4194304 Bool.false 2071100 8388608 1 4000000 (@Ns288p761 Ns288p179 22168107 16777216 133 4194304 (@Ns288p762 17592186044416 5535207 1099511627776 Ns288p759 Ns288p176 Ns288p760 Ns288p179 RS289to300.d43 (@Ns288p763 0 1 59192768170864 3699548010679 17592186044416 5535207 1099511627776 (@Ns288p764 10905343000955584512 2600036382903 17592186044416 5535207 1099511627776 (@Ns288p765 3438055 1099511627776 (Ns288p751 rfl rfl) (Ns288p751 rfl rfl) rfl) (Ns288p751 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 22168107 16777216) (BSN.cos_neg_of_bound 22168107 16777216 Bool.false 2071100 8388608 1 4000000 (Ns288p771 rfl rfl)) rfl rfl) 

noncomputable def Ns288p773 := @Ns288p737 2722067129820945741 92233720368547758080000 (Ns288p738 qz31 (@Enclosure.Real.IsNear.of_eq qz115 (@Inv.inv Real Real.instInv (Real.sqrt qz124)) Bool.false 1338477 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz123 (BSN.t_div_two_pi_nonneg qz114 605865 1000 qz117)) Ns288p742) rfl) (@Ns288p743 4398046511104 5072303021351 54975581388800000 (BSN.correction_mk qz116 (BSN.cos_two_pi_p_ne_zero_mk qz114 605865 1000 9 qz117 rfl rfl (@BSN.floor_sqrt_eq_dec qz114 605865 1000 9 qz117 rfl rfl rfl))) (@Ns288p744 4194304 517775 2097152 2094509 65536000000 2560697166725 4398046511104 5072303021351 54975581388800000 (@Ns288p745 4194304 (Ns288p756 rfl rfl rfl rfl rfl) rfl) (Ns288p772 rfl) rfl)) 

noncomputable def Ns288p774 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz114) (hardyZApproximantRS₀ qz114) Bool.false 59648995970917688225 18446744073709551616 120452274673936145741 92233720368547758080000 (@Eq.refl Real (hardyZApproximantRS₀ qz114)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz114) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz115) (Zeta.RiemannSiegel.correction qz116))) Bool.false 59648995970917688225 18446744073709551616 120452274673936145741 92233720368547758080000 (BSN.hardyZApproximantRS₀_eq qz114 9 (@BSN.floor_sqrt_eq_dec qz114 605865 1000 9 qz117 rfl rfl rfl)) (@Ns288p670 59648995970917688225 18446744073709551616 120452274673936145741 92233720368547758080000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 9) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 9)) Bool.false 102266425 33554432 21415 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz114) qz114 9) (Ns288p736 (Ns288p735 rfl) rfl rfl)) (Ns288p773 rfl) rfl rfl)) 

theorem RS289to300.d52 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz114) Bool.false 59648995970917688225 18446744073709551616 120452274673936145741 92233720368547758080000 := Ns288p774 

noncomputable def Ns288p775 := nat_lit 209163252322380018597595447296 

noncomputable abbrev qz737 := (Enclosure.sfrac Bool.false 607240 1000)

noncomputable abbrev qz638 := qz737

noncomputable abbrev qz456 := qz638

noncomputable abbrev qz132 := qz456

noncomputable abbrev qz738 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 607240 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz639 := qz738

noncomputable abbrev qz457 := qz639

noncomputable abbrev qz133 := (@HPow.hPow Real Real Real qz347 qz457 qz349)

noncomputable abbrev qz739 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 607240 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz640 := qz739

noncomputable abbrev qz458 := qz640

noncomputable abbrev qz134 := qz458

noncomputable def Ns288p776 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz132) qz132 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz133) (Zeta.RiemannSiegel.correction qz134)) 183565833 33554432 10731 8388608 225097893697966483803 1180591620717411303424 479846663729628988461 Ns288p451 Ns288p775 

noncomputable def Ns288p777 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 607240 1000 113 159 134217728 67108864 2251799813685248 Bool.false 145471701368 1861 

noncomputable def Ns288p778 := Ns288p777 279097919 34 47453128 8 294906479 34 44739240 8 Bool.true 347240999 70369 Bool.true 184074268 Bool.true 85543392 7074237752028440 1 Bool.false 131559981 Bool.true Bool.false 79868424 Bool.false Bool.true 367131666 

noncomputable def Ns288p779 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 607240 1000 2 62 134217728 67108864 2251799813685248 Bool.false 145471701368 1861 

noncomputable def Ns288p780 := Ns288p779 240485871 35 54794152 8 261175631 35 50729528 8 Bool.true 272600672 52176 Bool.true 139281509 Bool.true 53208524 7074237752028440 1 Bool.false 68206528 Bool.true Bool.false 123808290 Bool.true Bool.true 347240999 

noncomputable def Ns288p781 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 607240 1000 154 67 134217728 67108864 2251799813685248 Bool.false 145471701368 1861 

noncomputable def Ns288p782 := Ns288p781 186065264 34 67108856 8 216015088 34 60023992 8 Bool.true 263759116 30837 Bool.false 17808480 Bool.false 173175483 7074237752028440 1 Bool.false 133038014 Bool.true Bool.false 128970687 Bool.false Bool.true 272600672 

noncomputable def Ns288p783 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 607240 1000 422 265 134217728 67108864 2251799813685248 Bool.false 145471701368 1861 

noncomputable def Ns288p784 := Ns288p783 93032624 34 94906264 8 147453232 34 77490640 16 Bool.true 134217680 1898 Bool.false 8853406 Bool.false 62591523 7074237752028440 1 Bool.false 133925835 Bool.true Bool.false 60347372 Bool.true Bool.true 263759116 

noncomputable def Ns288p785 := nat_lit 430193724854194037509149985748709317175310974599 

noncomputable def Ns288p786 := nat_lit 396913102730323155262647502696602850767667200 

noncomputable def Ns288p787 := nat_lit 39631803985520194860669952000000000 

noncomputable def Ns288p788 := nat_lit 144396145598993154731087089274880000000 

noncomputable abbrev qz641 := (@Eq.refl Real qz737)

noncomputable abbrev qz459 := qz641

noncomputable abbrev qz135 := qz459

noncomputable def Ns288p789 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz132 607240 1000 1474962670400 16000000 1214480 4000 2000 Ns288p787 Ns288p788 qz135 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns288p790 := nat_lit 8810367485013893888187391708133566815750368759787520000000 

noncomputable abbrev qz642 := (@HSub.hSub Real Real Real qz712 qz713 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz714 (@Nat.cast Real Real.instNatCast 1214480))))

noncomputable abbrev qz460 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz580 (Enclosure.sfrac Bool.false 607240 4000) (Real.log (Enclosure.sfrac Bool.false 1474962670400 16000000))) (@HMul.hMul Real Real Real qz580 qz585 qz642))

noncomputable abbrev qz643 := (Enclosure.sfrac Bool.false 607240 2000)

noncomputable abbrev qz136 := (@HSub.hSub Real Real Real qz352 (@HSub.hSub Real Real Real qz352 qz460 qz643) (@HMul.hMul Real Real Real qz346 qz643 (Real.log Real.pi)))

noncomputable def Ns288p791 := @Enclosure.Real.IsNear.addLit_ft_p qz136 (Enclosure.sfrac Bool.true Ns288p787 Ns288p788) 61015269344887191979 56294995342131200 709383477884777 51200000000000000000 Ns288p787 Ns288p788 0 1 Ns288p790 

noncomputable def Ns288p792 := nat_lit 102366635309735091546515046400 

noncomputable abbrev qz137 := (@HSub.hSub Real Real Real qz352 qz460 qz643)

noncomputable def Ns288p793 := @Enclosure.Real.IsNear.subLit_ff_p qz137 (@HMul.hMul Real Real Real qz5 qz643 (Real.log Real.pi)) 80581320445044210091 56294995342131200 961312985817 200000000000000000 583113762741 1677721600 15181 1677721600 Ns288p792 61015269344887191979 56294995342131200 

noncomputable abbrev qz138 := qz460

noncomputable def Ns288p794 := @Enclosure.Real.IsNear.subLit_ff_p qz138 qz643 19534721386164417007 11258999068426240 961312985817 200000000000000000 607240 2000 0 1 32232528178017684036400 80581320445044210091 56294995342131200 961312985817 200000000000000000 

noncomputable def Ns288p795 := nat_lit 21994140988879131882021507058106368 

noncomputable def Ns288p796 := nat_lit 27639802812192905347727360 

noncomputable def Ns288p797 := nat_lit 1554216524480999127741967836824473004987372512503436716981914781046390490456554418995200000000000000000 

noncomputable def Ns288p798 := nat_lit 15048948434207541680197840692661547527879905334886188857785771504466806662355579043840000000000000000 

noncomputable def Ns288p799 := nat_lit 114714483595592627501588532612662108625745840739653499285120034897908017712332800000000000000000 

noncomputable def Ns288p800 := BSN.log_dyadic_bound 426386670400 2523538670400 5 4 Ns288p797 67108864 32000000 Ns288p798 Ns288p799 22897519 2949925340800 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 426386670400) (BSN.artanhQ 2523538670400) 0 4 Ns288p798 Ns288p797 Ns288p799 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz461 := (Real.log (Enclosure.sfrac Bool.false 1474962670400 16000000))

noncomputable def Ns288p801 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 607240 4000) qz461 607240 4000 0 1 3217696539614455 281474976710656 976563 31250000000000 9769570233577408271 5629499534213120 14825202903 3125000000000000 (Enclosure.Real.IsNear.const Bool.false 607240 4000) (BSN.isNear_log_sfrac 1474962670400 16000000 3217696539614455 281474976710656 976563 31250000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1474962670400) qz355)) Bool.false Ns288p796 Ns288p93 1000000512000000 32000000000000000000000 3217696539614455 281474976710656 976563 31250000000000 (BSN.log_rat_reduce_isNear 1474962670400 16000000 16 2949925340800 2097152000000 22897519 67108864 24973259072661432 36028797018963968 32000000 1000000000000000 rfl rfl rfl rfl (Ns288p800 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns288p802 := BSN.arctan_dyadic_bound_f 1000 1214480 1 0 8388608 4000000 0 1 1 0 1 1 6907 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1214480) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1214480) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz462 := (@Nat.cast Real Real.instNatCast 1214480)

noncomputable def Ns288p803 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz462)) 884279719003555 562949953421312 1 2000000000000000 6907 8388608 1 4000000 7413987629742692499456 883816198079907 562949953421312 500000001 2000000000000000 qz15 (Ns288p802 rfl) rfl rfl 

noncomputable abbrev qz463 := (@HMul.hMul Real Real Real qz580 qz585 qz642)

noncomputable abbrev qz139 := qz463

noncomputable abbrev qz464 := qz642

noncomputable abbrev qz140 := qz464

noncomputable def Ns288p804 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 607240 4000) qz461) qz139 9769570233577408271 5629499534213120 14825202903 3125000000000000 883816198079907 2251799813685248 500000001 8000000000000000 Ns288p795 19534721386164417007 11258999068426240 961312985817 200000000000000000 (Ns288p801 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz140 1 4 0 1 883816198079907 562949953421312 500000001 2000000000000000 883816198079907 2251799813685248 500000001 8000000000000000 qz363 Ns288p803 rfl) 

noncomputable def Ns288p805 := @Ns288p791 Ns288p785 Ns288p786 709383477884777 51200000000000000000 (@Ns288p793 709383477884777 51200000000000000000 (Ns288p794 (Ns288p804 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 607240 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz643 (Real.log Real.pi) 607240 2000 0 1 38410761 33554432 1 33554432 583113762741 1677721600 15181 1677721600 (Enclosure.Real.IsNear.const Bool.false 607240 2000) RS289to300.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns288p787 Ns288p788) 

noncomputable def Ns288p806 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz132) Bool.false Ns288p785 Ns288p786 709383477884777 51200000000000000000 18183962671 16777216 233 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz132) (@HAdd.hAdd Real Real Real qz364 qz136 (Enclosure.sfrac Bool.true Ns288p787 Ns288p788)) Bool.false Ns288p785 Ns288p786 709383477884777 51200000000000000000 Ns288p789 (Ns288p805 rfl rfl)) 

noncomputable def Ns288p807 := nat_lit 3795945960070312668168192 

noncomputable def Ns288p808 := nat_lit 855324020249437549469535186746703996506612311153185167898584856427020903152788188823236827095211516535643890622983916873973001079290625 

noncomputable def Ns288p809 := nat_lit 607131332791409863842872295348137185876356984550208874927378108625187258073582144743022197538659561174203531027651900605712890625 

noncomputable def Ns288p810 := nat_lit 4271317077110191557494479447099306090050658756573120112567418404907823356572149295406873426289928095239740239955134425469361718544890625 

noncomputable def Ns288p811 := BSN.sin_dyadic_bound_f 53943636545 34359738368 4 3 16777216 8007813 Ns288p808 Ns288p229 Ns288p809 Ns288p810 Ns288p232 Ns288p809 16777210 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53943636545) qz376 0 3 Ns288p808 Ns288p229 Ns288p809 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53943636545) qz377 0 3 Ns288p810 Ns288p232 Ns288p809 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p812 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz132) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18183962671) qz365) Bool.false 18183962671 16777216 233 16777216 Bool.true 16777210 16777216 1 4000000 (Ns288p806 rfl) (Enclosure.sfrac_false_div 18183962671 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18183962671) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns288p807) qz366) 226375608064910080 72057594037927936 Bool.false 16777210 16777216 172 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q1 18183962671 16777216 226375608064910080 72057594037927936 172 Ns288p807 Ns288p93 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777210 16777216 Ns288p807 Ns288p93 53943636545 34359738368 8007813 8000000 (Ns288p811 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p813 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz132) Bool.false Ns288p785 Ns288p786 709383477884777 51200000000000000000 145471701368 134217728 1861 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz132) (@HAdd.hAdd Real Real Real qz364 qz136 (Enclosure.sfrac Bool.true Ns288p787 Ns288p788)) Bool.false Ns288p785 Ns288p786 709383477884777 51200000000000000000 Ns288p789 (Ns288p805 rfl rfl)) 

noncomputable def Ns288p814 := Ns288p784 30837 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 422 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133925835 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 265 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 60347372 134217728) qz135 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 1) Bool.true 8388605 8388608 3706161 262144000000 134217680 134217728 1898 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz132)) Bool.true 8388605 8388608 3706161 262144000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz132) qz132) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz132)) Bool.true 16777210 16777216 948777216 67108864000000 8388605 8388608 3706161 262144000000 (Ns288p812 rfl rfl) rfl)) rfl) (Ns288p813 rfl) RS289to300.d7 

noncomputable def Ns288p815 := nat_lit 6143862991086740877922298896 

noncomputable def Ns288p816 := BSN.cos_dyadic_bound_f 8853406 134217728 2 1 134217728 67108864 Ns288p815 Ns288p132 Ns288p815 Ns288p815 Ns288p133 Ns288p815 133925835 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 8853406) qz369 0 1 Ns288p815 Ns288p132 Ns288p815 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 8853406) qz370 0 1 Ns288p815 Ns288p133 Ns288p815 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p817 := nat_lit 15348363507187552379907724901841 

noncomputable def Ns288p818 := BSN.sin_dyadic_bound_f 62591523 134217728 2 1 134217728 67108864 Ns288p817 Ns288p115 Ns288p817 Ns288p817 Ns288p116 Ns288p817 60347372 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 62591523) qz367 0 1 Ns288p817 Ns288p115 Ns288p817 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 62591523) qz368 0 1 Ns288p817 Ns288p116 Ns288p817 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p819 := nat_lit 100579022735809760776028160000 

noncomputable def Ns288p820 := BSN.cos_dyadic_bound_f 17808480 134217728 2 1 134217728 67108864 Ns288p819 Ns288p132 Ns288p819 Ns288p819 Ns288p133 Ns288p819 133038014 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 17808480) qz369 0 1 Ns288p819 Ns288p132 Ns288p819 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 17808480) qz370 0 1 Ns288p819 Ns288p133 Ns288p819 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p821 := nat_lit 4919507981232978997604047746751930044544508784099805177673549368255561034408190357183911932954506413518161 

noncomputable def Ns288p822 := nat_lit 727506522058602306434084926447537911997796076945546303386879065379908761570333421560010463862631761 

noncomputable def Ns288p823 := nat_lit 24583613948540778850004472908555496134231224097156010872262268155740966006693502088409623562554757082819921 

noncomputable def Ns288p824 := BSN.sin_dyadic_bound_f 173175483 134217728 4 3 134217728 67108864 Ns288p821 Ns288p143 Ns288p822 Ns288p823 Ns288p146 Ns288p822 128970687 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 173175483) qz367 0 3 Ns288p821 Ns288p143 Ns288p822 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 173175483) qz368 0 3 Ns288p823 Ns288p146 Ns288p822 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p825 := Ns288p782 52176 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 154 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133038014 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 67 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 128970687 134217728) qz135 rfl rfl (Ns288p814 RS289to300.d9 RS289to300.d11 RS289to300.d13 RS289to300.d17 (Ns288p816 rfl rfl) (Ns288p818 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns288p813 rfl) RS289to300.d19 RS289to300.d21 RS289to300.d23 RS289to300.d25 RS289to300.d17 (Ns288p820 rfl rfl) (Ns288p824 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns288p826 := nat_lit 205315788861297607704457487668879311189275090212901914072003698789601 

noncomputable def Ns288p827 := nat_lit 141627538406738575849354494115342470888821945325779543121120234721 

noncomputable def Ns288p828 := nat_lit 615664111507079345961673754018407248626047626748054183129768855899361 

noncomputable def Ns288p829 := BSN.cos_dyadic_bound_f 139281509 134217728 3 2 134217728 67108864 Ns288p826 Ns288p123 Ns288p827 Ns288p828 Ns288p126 Ns288p827 68206528 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 139281509) qz369 0 2 Ns288p826 Ns288p123 Ns288p827 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 139281509) qz370 0 2 Ns288p828 Ns288p126 Ns288p827 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p830 := nat_lit 4369985999416169387877337705730222417116279872660843168131941728256 

noncomputable def Ns288p831 := nat_lit 64246532708043120369415531722361291019383449013796495834546176 

noncomputable def Ns288p832 := nat_lit 13109829505183092077391274286127222528766800851084501911404156092416 

noncomputable def Ns288p833 := BSN.cos_dyadic_bound_f 53208524 134217728 3 2 134217728 67108864 Ns288p830 Ns288p123 Ns288p831 Ns288p832 Ns288p126 Ns288p831 123808290 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 53208524) qz369 0 2 Ns288p830 Ns288p123 Ns288p831 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 53208524) qz370 0 2 Ns288p832 Ns288p126 Ns288p831 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p834 := Ns288p780 70369 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 2 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 68206528 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 62 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 123808290 134217728) qz135 rfl rfl (Ns288p825 rfl rfl) (Ns288p813 rfl) RS289to300.d27 RS289to300.d29 RS289to300.d31 RS289to300.d33 RS289to300.d17 (Ns288p829 rfl rfl) (Ns288p833 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p835 := nat_lit 6281427530466872415462090225881602526432093666673241729322202916937319967660838618983203279621884924133376 

noncomputable def Ns288p836 := nat_lit 1513271961433194987584609052445056661409264535059773261286052288377379983967096751395158757449138176 

noncomputable def Ns288p837 := nat_lit 31384444043787180642918638474458651383860800160167102423984347064218865222942091305883984440059218347687936 

noncomputable def Ns288p838 := BSN.sin_dyadic_bound_f 184074268 134217728 4 3 134217728 67108864 Ns288p835 Ns288p143 Ns288p836 Ns288p837 Ns288p146 Ns288p836 131559981 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 184074268) qz367 0 3 Ns288p835 Ns288p143 Ns288p836 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 184074268) qz368 0 3 Ns288p837 Ns288p146 Ns288p836 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p839 := nat_lit 52552197866676254280044995828072889101983127427305565965382414499840 

noncomputable def Ns288p840 := nat_lit 2867422816176861671425460094467977980176270114314207075359522816 

noncomputable def Ns288p841 := nat_lit 137632066204354474862173633566704618540845048348472354526450979700736 

noncomputable def Ns288p842 := BSN.sin_dyadic_bound_f 85543392 134217728 3 2 134217728 67108864 Ns288p839 Ns288p109 Ns288p840 Ns288p841 Ns288p112 Ns288p840 79868424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 85543392) qz367 0 2 Ns288p839 Ns288p109 Ns288p840 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 85543392) qz368 0 2 Ns288p841 Ns288p112 Ns288p840 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p843 := Ns288p778 85848 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 113 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 131559981 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 79868424 134217728) qz135 rfl rfl (Ns288p834 rfl) (Ns288p813 rfl) RS289to300.d35 RS289to300.d37 RS289to300.d39 RS289to300.d41 RS289to300.d17 (Ns288p838 rfl rfl) (Ns288p842 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p844 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 9) 367131666 134217728 85848 134217728 367131666 134217728 85848 134217728 98551156174749696 183565833 33554432 10731 8388608 (Ns288p843 rfl) 

noncomputable def Ns288p845 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz133) (Zeta.RiemannSiegel.correction qz134) 2675437 8388608 1 8388608 84135000636519 140737488355328 178861201173297 2199023255552000000 225097893697966483803 1180591620717411303424 

noncomputable def Ns288p846 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz133 1 1 0 1 2675437 8388608 1 8388608 2675437 8388608 1 8388608 

noncomputable abbrev qz141 := qz457

noncomputable def Ns288p847 := @Enclosure.Real.IsNear.sqrt_image qz141 40535957037 419430400 15181 419430400 82466978 82467010 8388608 (@Enclosure.Real.IsNear.of_eq qz141 (@HMul.hMul Real Real Real qz5 qz132 qz3) Bool.false 40535957037 419430400 15181 419430400 (BSN.t_div_two_pi_mk qz132 607240 1000 qz135) (@Enclosure.Real.IsNear.mulLit_ff qz132 qz3 607240 1000 0 1 2670177 16777216 1 16777216 40535957037 419430400 15181 419430400 (Enclosure.Real.IsNear.const Bool.false 607240 1000) RS289to300.d44 rfl)) 

noncomputable abbrev qz740 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 607240 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz644 := qz740

noncomputable abbrev qz465 := qz644

noncomputable abbrev qz142 := qz465

noncomputable def Ns288p848 := @Enclosure.Real.IsNear.sqrt_image qz142 41233497 4194304 1 524288 26301770 26301776 8388608 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 164933988 16777216 32 16777216 41233497 4194304 1 524288 (Ns288p847 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns288p849 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz142) 26301773 8388608 3 8388608 2675436 2675438 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz142) Bool.false 52603546 16777216 6 16777216 26301773 8388608 3 8388608 (Ns288p848 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns288p850 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz142)) Bool.false 5350874 16777216 2 16777216 2675437 8388608 1 8388608 (Ns288p849 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz143 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz458))

noncomputable abbrev qz645 := (@HMul.hMul Real Real Real qz708 qz739 qz739)

noncomputable abbrev qz466 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz645 qz640) qz594)

noncomputable abbrev qz144 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz466))

noncomputable def Ns288p851 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz134) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz143) qz144) Bool.false 84135000636519 

noncomputable def Ns288p852 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz143) qz144 34497831 16777216 873 

noncomputable def Ns288p853 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz143) Bool.false 34497831 16777216 873 16777216 34497831 16777216 873 

noncomputable def Ns288p854 := @Enclosure.Real.IsNear.recentre' qz143 Bool.false 8159208 16777216 412388608 33554432000000 1019901 2097152 1610893 131072000000 

noncomputable abbrev qz145 := (@HMul.hMul Real Real Real qz346 qz343 qz458)

noncomputable def Ns288p855 := @Enclosure.Real.IsNear.cos_image qz145 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21895399) qz413) Bool.false 21895399 4194304 101 8388608 Bool.false 8159208 16777216 1 

noncomputable def Ns288p856 := nat_lit 26986075412785779087513031 

noncomputable def Ns288p857 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz134 884279719003555 140737488355328 1 500000000000000 3484761 4194304 1 524288 3081503477874547325355 590295810358705651712 Ns288p856 

noncomputable def Ns288p858 := @Enclosure.Real.IsNear.subLit_ff_p qz142 qz1 41233497 4194304 1 524288 9 1 0 1 3484761 3484761 4194304 1 

noncomputable def Ns288p859 := @Ns288p858 524288 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 164933988 16777216 32 16777216 41233497 4194304 1 524288 (Ns288p847 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns288p860 := @Enclosure.Real.IsNear.recentre' qz145 Bool.false 3081503477874547325355 590295810358705651712 Ns288p856 Ns288p162 21895399 4194304 101 8388608 (@Ns288p857 Ns288p162 RS289to300.d43 (Ns288p859 rfl rfl) rfl) 

noncomputable def Ns288p861 := nat_lit 92735719348842834536439531454077750029281 

noncomputable def Ns288p862 := BSN.sin_dyadic_bound_f 17450656153 34359738368 2 1 16777216 8007813 Ns288p861 Ns288p168 Ns288p861 Ns288p861 Ns288p169 Ns288p861 8159208 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 17450656153) qz376 0 1 Ns288p861 Ns288p168 Ns288p861 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 17450656153) qz377 0 1 Ns288p861 Ns288p169 Ns288p861 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p863 := @Ns288p855 4000000 (Ns288p860 rfl) (Enclosure.sfrac_false_div 21895399 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21895399) qz413) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 306995189653652759379968) qz414) 226375608064910080 72057594037927936 Bool.false 8159208 16777216 0 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q3 21895399 4194304 226375608064910080 72057594037927936 0 306995189653652759379968 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8159208 16777216 306995189653652759379968 604462909807314587353088 17450656153 34359738368 8007813 8000000 (Ns288p862 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p864 := @Enclosure.Real.IsNear.inv_image qz143 1019901 2097152 1610893 131072000000 17248479 17249352 8388608 (Ns288p854 (Ns288p863 rfl rfl) rfl) rfl 

noncomputable def Ns288p865 := @Enclosure.Real.IsNear.recentre' qz144 Bool.false 2438849 8388608 

noncomputable abbrev qz146 := (@HMul.hMul Real Real Real qz346 qz343 qz466)

noncomputable def Ns288p866 := @Enclosure.Real.IsNear.cos_image qz146 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 21404421)) qz365) Bool.true 21404421 16777216 

noncomputable def Ns288p867 := nat_lit 3158735055452442571655106445 

noncomputable def Ns288p868 := nat_lit 150634033090942667338686252522827 

noncomputable def Ns288p869 := @Enclosure.Real.IsNear.recentre' qz146 Bool.true Ns288p867 Ns288p176 Ns288p868 

noncomputable abbrev qz147 := qz466

noncomputable def Ns288p870 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz147 884279719003555 140737488355328 1 500000000000000 3572099401999 

noncomputable abbrev qz467 := (@HSub.hSub Real Real Real qz584 qz645 qz640)

noncomputable abbrev qz148 := qz467

noncomputable def Ns288p871 := @Enclosure.Real.IsNear.subLit_tf qz148 qz29 2472587774223 17592186044416 5581917 1099511627776 1 16 

noncomputable abbrev qz468 := qz645

noncomputable abbrev qz149 := qz468

noncomputable def Ns288p872 := @Enclosure.Real.IsNear.subLit_ff_n qz149 qz134 12143559227121 17592186044416 3484765 1099511627776 3484761 4194304 1 524288 

noncomputable def Ns288p873 := @Enclosure.Real.IsNear.mulLit_ff qz134 qz134 3484761 4194304 1 524288 3484761 4194304 1 524288 12143559227121 17592186044416 

noncomputable def Ns288p874 := nat_lit 27982540164087512722635777688956545685469125848275090655145441 

noncomputable def Ns288p875 := nat_lit 44058314186062042378347751667740734777396582192442094382561 

noncomputable def Ns288p876 := nat_lit 83859503863890414083150637563534155586852584380440387776671201 

noncomputable def Ns288p877 := BSN.cos_dyadic_bound_f 21404421 16777216 3 2 8388608 4000000 Ns288p874 Ns288p767 Ns288p875 Ns288p876 Ns288p770 Ns288p875 2438849 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 21404421) qz595 0 2 Ns288p874 Ns288p767 Ns288p875 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 21404421) (BSN.cosOddQ 16777216) 0 2 Ns288p876 Ns288p770 Ns288p875 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p878 := @Ns288p865 270097152 8388608000000 2438849 8388608 1055067 32768000000 (@Ns288p866 67 2097152 Bool.false 2438849 8388608 1 4000000 (@Ns288p869 Ns288p179 21404421 16777216 67 2097152 (@Ns288p870 17592186044416 5581917 1099511627776 Ns288p867 Ns288p176 Ns288p868 Ns288p179 RS289to300.d43 (@Ns288p871 0 1 57153590431984 3572099401999 17592186044416 5581917 1099511627776 (@Ns288p872 10370784791774625792 2472587774223 17592186044416 5581917 1099511627776 (@Ns288p873 3484765 1099511627776 (Ns288p859 rfl rfl) (Ns288p859 rfl rfl) rfl) (Ns288p859 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 21404421 16777216) (BSN.cos_neg_of_bound 21404421 16777216 Bool.false 2438849 8388608 1 4000000 (Ns288p877 rfl rfl)) rfl rfl) 

noncomputable def Ns288p879 := @Ns288p845 479846663729628988461 Ns288p451 (Ns288p846 qz31 (@Enclosure.Real.IsNear.of_eq qz133 (@Inv.inv Real Real.instInv (Real.sqrt qz142)) Bool.false 2675437 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz141 (BSN.t_div_two_pi_nonneg qz132 607240 1000 qz135)) Ns288p850) rfl) (@Ns288p851 140737488355328 178861201173297 2199023255552000000 (BSN.correction_mk qz134 (BSN.cos_two_pi_p_ne_zero_mk qz132 607240 1000 9 qz135 rfl rfl (@BSN.floor_sqrt_eq_dec qz132 607240 1000 9 qz135 rfl rfl rfl))) (@Ns288p852 16777216 2438849 8388608 1055067 32768000000 84135000636519 140737488355328 178861201173297 2199023255552000000 (@Ns288p853 16777216 (Ns288p864 rfl rfl rfl rfl rfl) rfl) (Ns288p878 rfl) rfl)) 

noncomputable def Ns288p880 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz132) (hardyZApproximantRS₀ qz132) Bool.true 6233550677370429593253 1180591620717411303424 24077565219058140988461 Ns288p451 (@Eq.refl Real (hardyZApproximantRS₀ qz132)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz132) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz132) qz132 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz133) (Zeta.RiemannSiegel.correction qz134))) Bool.true 6233550677370429593253 1180591620717411303424 24077565219058140988461 Ns288p451 (BSN.hardyZApproximantRS₀_eq qz132 9 (@BSN.floor_sqrt_eq_dec qz132 607240 1000 9 qz135 rfl rfl rfl)) (@Ns288p776 6233550677370429593253 1180591620717411303424 24077565219058140988461 Ns288p451 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz132) qz132 9) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 9)) Bool.true 183565833 33554432 10731 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz132) qz132 9) (Ns288p844 (Ns288p843 rfl) rfl rfl)) (Ns288p879 rfl) rfl rfl)) 

theorem RS289to300.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz132) Bool.true 6233550677370429593253 1180591620717411303424 24077565219058140988461 Ns288p451 := Ns288p880 

noncomputable def Ns288p881 := nat_lit 488955302523313533847863296 

noncomputable abbrev qz741 := (Enclosure.sfrac Bool.false 608615 1000)

noncomputable abbrev qz646 := qz741

noncomputable abbrev qz469 := qz646

noncomputable abbrev qz150 := qz469

noncomputable abbrev qz742 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 608615 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz647 := qz742

noncomputable abbrev qz470 := qz647

noncomputable abbrev qz151 := (@HPow.hPow Real Real Real qz347 qz470 qz349)

noncomputable abbrev qz743 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 608615 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz648 := qz743

noncomputable abbrev qz471 := qz648

noncomputable abbrev qz152 := qz471

noncomputable def Ns288p882 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz150) qz150 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz151) (Zeta.RiemannSiegel.correction qz152)) 19938281 33554432 86045 67108864 3610817660290234725 18446744073709551616 21627818460583561651 922337203685477580800000 Ns288p881 

noncomputable def Ns288p883 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 608615 1000 113 159 134217728 67108864 2251799813685248 Bool.false 145893597602 1865 

noncomputable def Ns288p884 := Ns288p883 279097919 34 47453128 8 294906479 34 44739240 8 Bool.false 59848971 70531 Bool.true 145937673 Bool.true 69143567 7074237752028440 1 Bool.false 118834289 Bool.true Bool.false 66125564 Bool.false Bool.false 39876562 

noncomputable def Ns288p885 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 608615 1000 2 61 134217728 67108864 2251799813685248 Bool.false 145893597602 1865 

noncomputable def Ns288p886 := Ns288p885 240485871 35 54794152 8 261175631 35 50729528 8 Bool.false 161769256 52297 Bool.true 48053348 Bool.true 201257496 7074237752028440 1 Bool.false 125707065 Bool.true Bool.false 133876605 Bool.true Bool.false 59848971 

noncomputable def Ns288p887 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 608615 1000 154 68 134217728 67108864 2251799813685248 Bool.false 145893597602 1865 

noncomputable def Ns288p888 := Ns288p887 186065264 34 67108856 8 216015088 34 60023992 8 Bool.false 127371280 30910 Bool.false 183864976 Bool.false 87222257 7074237752028440 1 Bool.false 26782732 Bool.true Bool.false 106860217 Bool.false Bool.false 161769256 

noncomputable def Ns288p889 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 608615 1000 423 266 134217728 67108864 2251799813685248 Bool.false 145893597602 1865 

noncomputable def Ns288p890 := Ns288p889 93032624 34 94906264 8 147453232 34 77490640 16 Bool.false 134217664 1906 Bool.false 92001067 Bool.false 70910848 7074237752028440 1 Bool.false 84963879 Bool.false Bool.false 115917359 Bool.true Bool.false 127371280 

noncomputable def Ns288p891 := nat_lit 7165316912083850318161862777609231741774498619823873 

noncomputable def Ns288p892 := nat_lit 6591876354718911679534855821417951632068234444800 

noncomputable def Ns288p893 := nat_lit 40082540409681700031523264500000000 

noncomputable def Ns288p894 := nat_lit 146369058089821628233170432352005000000 

noncomputable abbrev qz649 := (@Eq.refl Real qz741)

noncomputable abbrev qz472 := qz649

noncomputable abbrev qz153 := qz472

noncomputable def Ns288p895 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz150 608615 1000 1481649872900 16000000 1217230 4000 2000 Ns288p893 Ns288p894 qz153 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns288p896 := nat_lit 35826584560419251590809313888046158708872493099119365000000 

noncomputable abbrev qz650 := (@HSub.hSub Real Real Real qz712 qz713 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz714 (@Nat.cast Real Real.instNatCast 1217230))))

noncomputable abbrev qz473 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz580 (Enclosure.sfrac Bool.false 608615 4000) (Real.log (Enclosure.sfrac Bool.false 1481649872900 16000000))) (@HMul.hMul Real Real Real qz580 qz585 qz650))

noncomputable abbrev qz651 := (Enclosure.sfrac Bool.false 608615 2000)

noncomputable abbrev qz154 := (@HSub.hSub Real Real Real qz352 (@HSub.hSub Real Real Real qz352 qz473 qz651) (@HMul.hMul Real Real Real qz346 qz651 (Real.log Real.pi)))

noncomputable def Ns288p897 := @Enclosure.Real.IsNear.addLit_ft_p qz154 (Enclosure.sfrac Bool.true Ns288p893 Ns288p894) 244768901663761564673 225179981368524800 5687860159315391 409600000000000000000 Ns288p893 Ns288p894 0 1 Ns288p896 

noncomputable def Ns288p898 := nat_lit 3285232586636549714413512294400 

noncomputable abbrev qz155 := (@HSub.hSub Real Real Real qz352 qz473 qz651)

noncomputable def Ns288p899 := @Enclosure.Real.IsNear.subLit_ff_p qz155 (@HMul.hMul Real Real Real qz5 qz651 (Real.log Real.pi)) 323210323113745515521 225179981368524800 963461424417 200000000000000000 4675473061203 13421772800 121723 13421772800 Ns288p898 244768901663761564673 225179981368524800 

noncomputable abbrev qz156 := qz473

noncomputable def Ns288p900 := @Enclosure.Real.IsNear.subLit_ff_p qz156 qz651 391734280294047876097 225179981368524800 963461424417 200000000000000000 608615 2000 0 1 646420646227491031042000 323210323113745515521 225179981368524800 963461424417 200000000000000000 

noncomputable def Ns288p901 := nat_lit 882107179380261724511207488860717056 

noncomputable def Ns288p902 := nat_lit 27650740110132749258457088 

noncomputable def Ns288p903 := nat_lit 1587472267234242113650683067530196758538629972932486082600347383404385988431001111961450000000000000000 

noncomputable def Ns288p904 := nat_lit 15780410347481258344570442531420909228862073088606661799136905257020878239974136045840000000000000000 

noncomputable def Ns288p905 := nat_lit 129922739489518223143499392859751553595148348909706057220154454254104457389329050000000000000000 

noncomputable def Ns288p906 := BSN.log_dyadic_bound 433073872900 2530225872900 5 4 Ns288p903 67108864 32000000 Ns288p904 Ns288p905 23201090 2963299745800 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 433073872900) (BSN.artanhQ 2530225872900) 0 4 Ns288p904 Ns288p903 Ns288p905 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz474 := (Real.log (Enclosure.sfrac Bool.false 1481649872900 16000000))

noncomputable def Ns288p907 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 608615 4000) qz474 608615 4000 0 1 3218969808674039 281474976710656 976563 31250000000000 391822662021230049197 225179981368524800 118870178049 25000000000000000 (Enclosure.Real.IsNear.const Bool.false 608615 4000) (BSN.isNear_log_sfrac 1481649872900 16000000 3218969808674039 281474976710656 976563 31250000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1481649872900) qz355)) Bool.false Ns288p902 Ns288p93 1000000512000000 32000000000000000000000 3218969808674039 281474976710656 976563 31250000000000 (BSN.log_rat_reduce_isNear 1481649872900 16000000 16 2963299745800 2097152000000 23201090 67108864 24973259072661432 36028797018963968 32000000 1000000000000000 rfl rfl rfl rfl (Ns288p906 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns288p908 := BSN.arctan_dyadic_bound_f 1000 1217230 1 0 8388608 4000000 0 1 1 0 1 1 6891 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1217230) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1217230) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz475 := (@Nat.cast Real Real.instNatCast 1217230)

noncomputable def Ns288p909 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz475)) 884279719003555 562949953421312 1 2000000000000000 6891 8388608 1 4000000 7413996636941947240448 883817271821731 562949953421312 500000001 2000000000000000 qz15 (Ns288p908 rfl) rfl rfl 

noncomputable abbrev qz476 := (@HMul.hMul Real Real Real qz580 qz585 qz650)

noncomputable abbrev qz157 := qz476

noncomputable abbrev qz477 := qz650

noncomputable abbrev qz158 := qz477

noncomputable def Ns288p910 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 608615 4000) qz474) qz157 391822662021230049197 225179981368524800 118870178049 25000000000000000 883817271821731 2251799813685248 500000001 8000000000000000 Ns288p901 391734280294047876097 225179981368524800 963461424417 200000000000000000 (Ns288p907 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz158 1 4 0 1 883817271821731 562949953421312 500000001 2000000000000000 883817271821731 2251799813685248 500000001 8000000000000000 qz363 Ns288p909 rfl) 

noncomputable def Ns288p911 := @Ns288p897 Ns288p891 Ns288p892 5687860159315391 409600000000000000000 (@Ns288p899 5687860159315391 409600000000000000000 (Ns288p900 (Ns288p910 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 608615 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz651 (Real.log Real.pi) 608615 2000 0 1 38410761 33554432 1 33554432 4675473061203 13421772800 121723 13421772800 (Enclosure.Real.IsNear.const Bool.false 608615 2000) RS289to300.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns288p893 Ns288p894) 

noncomputable def Ns288p912 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz150) Bool.false Ns288p891 Ns288p892 5687860159315391 409600000000000000000 4559174925 4194304 117 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz150) (@HAdd.hAdd Real Real Real qz364 qz154 (Enclosure.sfrac Bool.true Ns288p893 Ns288p894)) Bool.false Ns288p891 Ns288p892 5687860159315391 409600000000000000000 Ns288p895 (Ns288p911 rfl rfl)) 

noncomputable def Ns288p913 := BSN.cos_dyadic_bound_f 32619483 34359738368 1 0 16777216 8007813 0 1 1 0 1 1 16777208 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 32619483) (BSN.cosEvenQ 34359738368) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 32619483) (BSN.cosOddQ 34359738368) 0 0 rfl) rfl rfl 

noncomputable def Ns288p914 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz150) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4559174925) qz413) Bool.false 4559174925 4194304 117 8388608 Bool.false 16777208 16777216 1 4000000 (Ns288p912 rfl) (Enclosure.sfrac_false_div 4559174925 4194304) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4559174925) qz413) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 573848014540672860160) qz414) 226375608064910080 72057594037927936 Bool.false 16777208 16777216 173 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q0 4559174925 4194304 226375608064910080 72057594037927936 173 573848014540672860160 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777208 16777216 573848014540672860160 604462909807314587353088 32619483 34359738368 8007813 8000000 (Ns288p913 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p915 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz150) Bool.false Ns288p891 Ns288p892 5687860159315391 409600000000000000000 145893597602 134217728 1865 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz150) (@HAdd.hAdd Real Real Real qz364 qz154 (Enclosure.sfrac Bool.true Ns288p893 Ns288p894)) Bool.false Ns288p891 Ns288p892 5687860159315391 409600000000000000000 Ns288p895 (Ns288p911 rfl rfl)) 

noncomputable def Ns288p916 := Ns288p890 30910 BSN.abs_quadSignPos (BSN.cos_quad_nat3 423 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 84963879 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 266 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 115917359 134217728) qz153 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 1) Bool.false 2097151 2097152 1860893 131072000000 134217664 134217728 1906 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz150)) Bool.false 2097151 2097152 1860893 131072000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz150) qz150) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz150)) Bool.false 16777208 16777216 476388608 33554432000000 2097151 2097152 1860893 131072000000 (Ns288p914 rfl rfl) rfl)) rfl) (Ns288p915 rfl) RS289to300.d7 

noncomputable def Ns288p917 := nat_lit 70311195066737170470797049049709331731542723004489316207060841748065 

noncomputable def Ns288p918 := nat_lit 5132664928564077794684624109847538048373037848237318658980140641 

noncomputable def Ns288p919 := nat_lit 184140058002998723678515162881632306140057384855241539169235284350561 

noncomputable def Ns288p920 := BSN.sin_dyadic_bound_f 92001067 134217728 3 2 134217728 67108864 Ns288p917 Ns288p109 Ns288p918 Ns288p919 Ns288p112 Ns288p918 84963879 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 92001067) qz367 0 2 Ns288p917 Ns288p109 Ns288p918 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 92001067) qz368 0 2 Ns288p919 Ns288p112 Ns288p918 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p921 := nat_lit 13785409458518426450878837170467145501376346002887973989257247195136 

noncomputable def Ns288p922 := nat_lit 639295182779039449942490207026977558979041231341737837494009856 

noncomputable def Ns288p923 := nat_lit 41354949785189721273736626530987382549011079926201238492096753565696 

noncomputable def Ns288p924 := BSN.cos_dyadic_bound_f 70910848 134217728 3 2 134217728 67108864 Ns288p921 Ns288p123 Ns288p922 Ns288p923 Ns288p126 Ns288p922 115917359 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 70910848) qz369 0 2 Ns288p921 Ns288p123 Ns288p922 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 70910848) qz370 0 2 Ns288p923 Ns288p126 Ns288p922 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p925 := nat_lit 2407190929709244440196921237134823197460602684270054333839769625776543187404964207919234936682807616864256 

noncomputable def Ns288p926 := nat_lit 1492753550352256036854300803995595011984451764633458534207463398497581858709168225289774717862936576 

noncomputable def Ns288p927 := nat_lit 14583251354840526837037466439552811841435309151707310987144258669163851637373071637314035406815650885140480 

noncomputable def Ns288p928 := BSN.cos_dyadic_bound_f 183864976 134217728 4 3 134217728 67108864 Ns288p925 Ns288p137 Ns288p926 Ns288p927 Ns288p140 Ns288p926 26782732 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 183864976) qz369 0 3 Ns288p925 Ns288p137 Ns288p926 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 183864976) qz370 0 3 Ns288p927 Ns288p140 Ns288p926 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p929 := nat_lit 31557616744758355516250015959121658672497457150837377901833717930881 

noncomputable def Ns288p930 := nat_lit 3349797574427030752037394710641666735857803822704763251081468801 

noncomputable def Ns288p931 := nat_lit 94666150639126212487245973087943692684020655844866724178998990855041 

noncomputable def Ns288p932 := BSN.cos_dyadic_bound_f 87222257 134217728 3 2 134217728 67108864 Ns288p929 Ns288p123 Ns288p930 Ns288p931 Ns288p126 Ns288p930 106860217 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 87222257) qz369 0 2 Ns288p929 Ns288p123 Ns288p930 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 87222257) qz370 0 2 Ns288p931 Ns288p126 Ns288p930 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p933 := Ns288p888 52297 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 154 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 26782732 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 68 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 106860217 134217728) qz153 rfl rfl (Ns288p916 RS289to300.d9 RS289to300.d11 RS289to300.d13 RS289to300.d17 (Ns288p920 rfl rfl) (Ns288p924 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns288p915 rfl) RS289to300.d19 RS289to300.d21 RS289to300.d23 RS289to300.d25 RS289to300.d17 (Ns288p928 rfl rfl) (Ns288p932 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns288p934 := nat_lit 2907017637654891017453326767835367952411578177509524133932800475136 

noncomputable def Ns288p935 := nat_lit 28430808608317151679850448582786487588742931133113479012089856 

noncomputable def Ns288p936 := nat_lit 8720996051347456418056620602608938284259557046666306174840377245696 

noncomputable def Ns288p937 := BSN.cos_dyadic_bound_f 48053348 134217728 3 2 134217728 67108864 Ns288p934 Ns288p123 Ns288p935 Ns288p936 Ns288p126 Ns288p935 125707065 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 48053348) qz369 0 2 Ns288p934 Ns288p123 Ns288p935 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 48053348) qz370 0 2 Ns288p936 Ns288p126 Ns288p935 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p938 := nat_lit 8980738667534065355772836123217714905302656103199404128851621310870150911141021518415480776158057873801216 

noncomputable def Ns288p939 := nat_lit 4415956431542734036831988822139437186134756406832970317931963632068901791272068475241584016769417216 

noncomputable def Ns288p940 := nat_lit 44857345965411963226181403871327099831060224736515869894840139607364208204406141510720367381169434919960576 

noncomputable def Ns288p941 := BSN.sin_dyadic_bound_f 201257496 134217728 4 3 134217728 67108864 Ns288p938 Ns288p143 Ns288p939 Ns288p940 Ns288p146 Ns288p939 133876605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 201257496) qz367 0 3 Ns288p938 Ns288p143 Ns288p939 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 201257496) qz368 0 3 Ns288p940 Ns288p146 Ns288p939 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p942 := Ns288p886 70531 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 2 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 125707065 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133876605 134217728) qz153 rfl rfl (Ns288p933 rfl rfl) (Ns288p915 rfl) RS289to300.d27 RS289to300.d29 RS289to300.d31 RS289to300.d33 RS289to300.d17 (Ns288p937 rfl rfl) (Ns288p941 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p943 := nat_lit 445339974461773094369367382919597673276284088288561596164691992395585 

noncomputable def Ns288p944 := nat_lit 205749759672623168065699154754988075596789648368788431418848591681 

noncomputable def Ns288p945 := nat_lit 1166033481122316714409570109015057258839301619420302332494753272840001 

noncomputable def Ns288p946 := BSN.sin_dyadic_bound_f 145937673 134217728 3 2 134217728 67108864 Ns288p943 Ns288p109 Ns288p944 Ns288p945 Ns288p112 Ns288p944 118834289 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 145937673) qz367 0 2 Ns288p943 Ns288p109 Ns288p944 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 145937673) qz368 0 2 Ns288p945 Ns288p112 Ns288p944 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p947 := nat_lit 22430479348696634369464583565827959598186753126377928529893616008065 

noncomputable def Ns288p948 := nat_lit 522413320956920326030572429043769905467282551638673795411360641 

noncomputable def Ns288p949 := nat_lit 58745647720257255001403193174188109034451692111620493058814518770561 

noncomputable def Ns288p950 := BSN.sin_dyadic_bound_f 69143567 134217728 3 2 134217728 67108864 Ns288p947 Ns288p109 Ns288p948 Ns288p949 Ns288p112 Ns288p948 66125564 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 69143567) qz367 0 2 Ns288p947 Ns288p109 Ns288p948 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 69143567) qz368 0 2 Ns288p949 Ns288p112 Ns288p948 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p951 := Ns288p884 86045 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 113 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 118834289 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 66125564 134217728) qz153 rfl rfl (Ns288p942 rfl) (Ns288p915 rfl) RS289to300.d35 RS289to300.d37 RS289to300.d39 RS289to300.d41 RS289to300.d17 (Ns288p946 rfl rfl) (Ns288p950 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p952 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 9) 39876562 134217728 86045 134217728 39876562 134217728 86045 134217728 10704283104182272 19938281 33554432 86045 67108864 (Ns288p951 rfl) 

noncomputable def Ns288p953 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz151) (Zeta.RiemannSiegel.correction qz152) 2673925 8388608 1 8388608 1350381054177 2199023255552 16126324668577 219902325555200000 3610817660290234725 18446744073709551616 

noncomputable def Ns288p954 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz151 1 1 0 1 2673925 8388608 1 8388608 2673925 8388608 1 8388608 

noncomputable abbrev qz159 := qz470

noncomputable def Ns288p955 := @Enclosure.Real.IsNear.sqrt_image qz159 325021954971 3355443200 121723 3355443200 82560292 82560324 8388608 (@Enclosure.Real.IsNear.of_eq qz159 (@HMul.hMul Real Real Real qz5 qz150 qz3) Bool.false 325021954971 3355443200 121723 3355443200 (BSN.t_div_two_pi_mk qz150 608615 1000 qz153) (@Enclosure.Real.IsNear.mulLit_ff qz150 qz3 608615 1000 0 1 2670177 16777216 1 16777216 325021954971 3355443200 121723 3355443200 (Enclosure.Real.IsNear.const Bool.false 608615 1000) RS289to300.d44 rfl)) 

noncomputable abbrev qz744 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 608615 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz652 := qz744

noncomputable abbrev qz478 := qz652

noncomputable abbrev qz160 := qz478

noncomputable def Ns288p956 := @Enclosure.Real.IsNear.sqrt_image qz160 20640077 2097152 1 524288 26316647 26316653 8388608 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 165120616 16777216 32 16777216 20640077 2097152 1 524288 (Ns288p955 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns288p957 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz160) 13158325 4194304 3 8388608 2673924 2673926 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz160) Bool.false 52633300 16777216 6 16777216 13158325 4194304 3 8388608 (Ns288p956 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns288p958 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz160)) Bool.false 5347850 16777216 2 16777216 2673925 8388608 1 8388608 (Ns288p957 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz161 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz471))

noncomputable abbrev qz653 := (@HMul.hMul Real Real Real qz708 qz743 qz743)

noncomputable abbrev qz479 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz653 qz648) qz594)

noncomputable abbrev qz162 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz479))

noncomputable def Ns288p959 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz152) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz161) qz162) Bool.false 1350381054177 

noncomputable def Ns288p960 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz161) qz162 1919903 1048576 173 

noncomputable def Ns288p961 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz161) Bool.false 30718448 16777216 692 16777216 1919903 1048576 173 

noncomputable def Ns288p962 := @Enclosure.Real.IsNear.recentre' qz161 Bool.false 9163060 16777216 412388608 33554432000000 2290765 4194304 1610893 131072000000 

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz346 qz343 qz471)

noncomputable def Ns288p963 := @Enclosure.Real.IsNear.cos_image qz163 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44377107) qz393) Bool.false 44377107 8388608 101 8388608 Bool.false 9163060 16777216 1 

noncomputable def Ns288p964 := nat_lit 26986075412835876659795399 

noncomputable def Ns288p965 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz152 884279719003555 140737488355328 1 500000000000000 1765709 2097152 1 524288 1561380658362048095495 295147905179352825856 Ns288p964 

noncomputable def Ns288p966 := @Enclosure.Real.IsNear.subLit_ff_p qz160 qz1 20640077 2097152 1 524288 9 1 0 1 1765709 1765709 2097152 1 

noncomputable def Ns288p967 := @Ns288p966 524288 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 165120616 16777216 32 16777216 20640077 2097152 1 524288 (Ns288p955 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns288p968 := @Enclosure.Real.IsNear.recentre' qz163 Bool.false 1561380658362048095495 295147905179352825856 Ns288p964 Ns288p162 44377107 8388608 101 8388608 (@Ns288p965 Ns288p162 RS289to300.d43 (Ns288p967 rfl rfl) rfl) 

noncomputable def Ns288p969 := nat_lit 155321875566466313711763646346078798769121 

noncomputable def Ns288p970 := BSN.sin_dyadic_bound_f 19852177817 34359738368 2 1 16777216 8007813 Ns288p969 Ns288p168 Ns288p969 Ns288p969 Ns288p169 Ns288p969 9163060 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 19852177817) qz376 0 1 Ns288p969 Ns288p168 Ns288p969 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 19852177817) qz377 0 1 Ns288p969 Ns288p169 Ns288p969 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p971 := @Ns288p963 4000000 (Ns288p968 rfl) (Enclosure.sfrac_false_div 44377107 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44377107) qz393) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 698486411112872499216384) qz394) 226375608064910080 72057594037927936 Bool.false 9163060 16777216 0 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q3 44377107 8388608 226375608064910080 72057594037927936 0 698486411112872499216384 Ns288p284 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 9163060 16777216 698486411112872499216384 Ns288p284 19852177817 34359738368 8007813 8000000 (Ns288p970 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p972 := @Enclosure.Real.IsNear.inv_image qz161 2290765 4194304 1610893 131072000000 15358878 15359570 8388608 (Ns288p962 (Ns288p971 rfl rfl) rfl) rfl 

noncomputable def Ns288p973 := @Enclosure.Real.IsNear.recentre' qz162 Bool.false 2813436 8388608 

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz346 qz343 qz479)

noncomputable def Ns288p974 := @Enclosure.Real.IsNear.cos_image qz164 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 10307749)) qz393) Bool.true 10307749 8388608 

noncomputable def Ns288p975 := nat_lit 760577647862217966610335205 

noncomputable def Ns288p976 := nat_lit 75946561205615875412047958708073 

noncomputable def Ns288p977 := @Enclosure.Real.IsNear.recentre' qz164 Bool.true Ns288p975 Ns288p542 Ns288p976 

noncomputable abbrev qz165 := qz479

noncomputable def Ns288p978 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz165 884279719003555 140737488355328 1 500000000000000 860109795031 

noncomputable abbrev qz480 := (@HSub.hSub Real Real Real qz584 qz653 qz648)

noncomputable abbrev qz166 := qz480

noncomputable def Ns288p979 := @Enclosure.Real.IsNear.subLit_tf qz166 qz29 585231888087 4398046511104 2814287 549755813888 1 16 

noncomputable abbrev qz481 := qz653

noncomputable abbrev qz167 := qz481

noncomputable def Ns288p980 := @Enclosure.Real.IsNear.subLit_ff_n qz167 qz152 3117728272681 4398046511104 1765711 549755813888 1765709 2097152 1 524288 

noncomputable def Ns288p981 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz152 1765709 2097152 1 524288 1765709 2097152 1 524288 3117728272681 4398046511104 

noncomputable def Ns288p982 := nat_lit 94040118684361449861625756865211670394507710129473126893281 

noncomputable def Ns288p983 := nat_lit 988643523323402220304136834155207460536120982503085435781120 

noncomputable def Ns288p984 := nat_lit 127441442148247263577042031593121619929242635485611788001 

noncomputable def Ns288p985 := nat_lit 281865473168787855057723186532448767943664645117448157103841 

noncomputable def Ns288p986 := nat_lit 44488958549553099913686157536984335724125444212638844610150400 

noncomputable def Ns288p987 := BSN.cos_dyadic_bound_f 10307749 8388608 3 2 8388608 4000000 Ns288p982 Ns288p983 Ns288p984 Ns288p985 Ns288p986 Ns288p984 2813436 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 10307749) (BSN.cosEvenQ 8388608) 0 2 Ns288p982 Ns288p983 Ns288p984 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 10307749) (BSN.cosOddQ 8388608) 0 2 Ns288p985 Ns288p986 Ns288p984 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p988 := @Ns288p973 2180777216 67108864000000 703359 2097152 8518661 262144000000 (@Ns288p974 541 16777216 Bool.false 2813436 8388608 1 4000000 (@Ns288p977 Ns288p545 10307749 8388608 541 16777216 (@Ns288p978 4398046511104 2814287 549755813888 Ns288p975 Ns288p542 Ns288p976 Ns288p545 RS289to300.d43 (@Ns288p979 0 1 13761756720496 860109795031 4398046511104 2814287 549755813888 (@Ns288p980 1227320224565428224 585231888087 4398046511104 2814287 549755813888 (@Ns288p981 1765711 549755813888 (Ns288p967 rfl rfl) (Ns288p967 rfl rfl) rfl) (Ns288p967 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 10307749 8388608) (BSN.cos_neg_of_bound 10307749 8388608 Bool.false 2813436 8388608 1 4000000 (Ns288p987 rfl rfl)) rfl rfl) 

noncomputable def Ns288p989 := @Ns288p953 21627818460583561651 922337203685477580800000 (Ns288p954 qz31 (@Enclosure.Real.IsNear.of_eq qz151 (@Inv.inv Real Real.instInv (Real.sqrt qz160)) Bool.false 2673925 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz159 (BSN.t_div_two_pi_nonneg qz150 608615 1000 qz153)) Ns288p958) rfl) (@Ns288p959 2199023255552 16126324668577 219902325555200000 (BSN.correction_mk qz152 (BSN.cos_two_pi_p_ne_zero_mk qz150 608615 1000 9 qz153 rfl rfl (@BSN.floor_sqrt_eq_dec qz150 608615 1000 9 qz153 rfl rfl rfl))) (@Ns288p960 4194304 703359 2097152 8518661 262144000000 1350381054177 2199023255552 16126324668577 219902325555200000 (@Ns288p961 4194304 (Ns288p972 rfl rfl rfl rfl rfl) rfl) (Ns288p988 rfl) rfl)) 

noncomputable def Ns288p990 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz150) (hardyZApproximantRS₀ qz150) Bool.false 14572003558972881253 18446744073709551616 1204221293610407561651 922337203685477580800000 (@Eq.refl Real (hardyZApproximantRS₀ qz150)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz150) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz150) qz150 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz151) (Zeta.RiemannSiegel.correction qz152))) Bool.false 14572003558972881253 18446744073709551616 1204221293610407561651 922337203685477580800000 (BSN.hardyZApproximantRS₀_eq qz150 9 (@BSN.floor_sqrt_eq_dec qz150 608615 1000 9 qz153 rfl rfl rfl)) (@Ns288p882 14572003558972881253 18446744073709551616 1204221293610407561651 922337203685477580800000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz150) qz150 9) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 9)) Bool.false 19938281 33554432 86045 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz150) qz150 9) (Ns288p952 (Ns288p951 rfl) rfl rfl)) (Ns288p989 rfl) rfl rfl)) 

theorem RS289to300.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz150) Bool.false 14572003558972881253 18446744073709551616 1204221293610407561651 922337203685477580800000 := Ns288p990 

noncomputable def Ns288p991 := nat_lit 31852955704039539144524824576 

noncomputable abbrev qz745 := (Enclosure.sfrac Bool.false 609988 1000)

noncomputable abbrev qz654 := qz745

noncomputable abbrev qz482 := qz654

noncomputable abbrev qz168 := qz482

noncomputable abbrev qz746 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 609988 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz655 := qz746

noncomputable abbrev qz483 := qz655

noncomputable abbrev qz169 := (@HPow.hPow Real Real Real qz347 qz483 qz349)

noncomputable abbrev qz747 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 609988 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz656 := qz747

noncomputable abbrev qz484 := qz656

noncomputable abbrev qz170 := qz484

noncomputable def Ns288p992 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz169) (Zeta.RiemannSiegel.correction qz170)) 60706401 33554432 86235 67108864 118666245586156844773 590295810358705651712 39662930568774853967 Ns288p69 Ns288p991 

noncomputable def Ns288p993 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 609988 1000 113 159 134217728 67108864 2251799813685248 Bool.false 146315088226 1869 

noncomputable def Ns288p994 := Ns288p993 279097919 34 47453128 8 294906479 34 44739240 8 Bool.true 104380002 70686 Bool.true 107648491 Bool.true 52559539 7074237752028440 1 Bool.false 96472816 Bool.true Bool.false 51226468 Bool.false Bool.true 121412802 

noncomputable def Ns288p995 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 609988 1000 1 61 134217728 67108864 2251799813685248 Bool.false 146315088226 1869 

noncomputable def Ns288p996 := Ns288p995 240485871 35 54794152 8 261175631 35 50729528 8 Bool.true 8893098 52411 Bool.true 167578539 Bool.true 138361014 7074237752028440 1 Bool.false 127309373 Bool.true Bool.false 115124786 Bool.true Bool.true 104380002 

noncomputable def Ns288p997 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 609988 1000 155 69 134217728 67108864 2251799813685248 Bool.false 146315088226 1869 

noncomputable def Ns288p998 := Ns288p997 186065264 34 67108856 8 216015088 34 60023992 8 Bool.true 66054849 30975 Bool.false 139059278 Bool.false 1295451 7074237752028440 1 Bool.false 115482185 Bool.false Bool.false 1295430 Bool.true Bool.true 8893098 

noncomputable def Ns288p999 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 609988 1000 424 267 134217728 67108864 2251799813685248 Bool.false 146315088226 1869 

noncomputable def Ns288p1000 := Ns288p999 93032624 34 94906264 8 147453232 34 77490640 16 Bool.true 134217720 1906 Bool.false 174929185 Bool.false 79119471 7074237752028440 1 Bool.false 35473006 Bool.false Bool.false 74616177 Bool.false Bool.true 66054849 

noncomputable def Ns288p1001 := nat_lit 54268801926132396541751922171267202211487727349443 

noncomputable def Ns288p1002 := nat_lit 49781846726203722431713580555021310602143334400 

noncomputable def Ns288p1003 := nat_lit 40536704000819018809672072560640000 

noncomputable def Ns288p1004 := nat_lit 148361464518915779685120524630014033920 

noncomputable abbrev qz657 := (@Eq.refl Real qz745)

noncomputable abbrev qz485 := qz657

noncomputable abbrev qz171 := qz485

noncomputable def Ns288p1005 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz168 609988 1000 1488342440576 16000000 1219976 4000 2000 Ns288p1003 Ns288p1004 qz171 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns288p1006 := nat_lit 569049632484962038361640635426586778261129551931695431680 

noncomputable abbrev qz658 := (@HSub.hSub Real Real Real qz712 qz713 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz714 (@Nat.cast Real Real.instNatCast 1219976))))

noncomputable abbrev qz486 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz580 (Enclosure.sfrac Bool.false 609988 4000) (Real.log (Enclosure.sfrac Bool.false 1488342440576 16000000))) (@HMul.hMul Real Real Real qz580 qz585 qz658))

noncomputable abbrev qz659 := (Enclosure.sfrac Bool.false 609988 2000)

noncomputable abbrev qz172 := (@HSub.hSub Real Real Real qz352 (@HSub.hSub Real Real Real qz352 qz486 qz659) (@HMul.hMul Real Real Real qz346 qz659 (Real.log Real.pi)))

noncomputable def Ns288p1007 := @Enclosure.Real.IsNear.addLit_ft_p qz172 (Enclosure.sfrac Bool.true Ns288p1003 Ns288p1004) 3835563210137070679 3518437208883200 7125792360647549 512000000000000000000 Ns288p1003 Ns288p1004 0 1 Ns288p1006 

noncomputable def Ns288p1008 := nat_lit 321750362290615121944248320000 

noncomputable abbrev qz173 := (@HSub.hSub Real Real Real qz352 qz486 qz659)

noncomputable def Ns288p1009 := @Enclosure.Real.IsNear.subLit_ff_p qz173 (@HMul.hMul Real Real Real qz5 qz659 (Real.log Real.pi)) 25319877045145214387 17592186044416000 4828033690077 1000000000000000000 5857525820217 16777216000 152497 16777216000 Ns288p1008 3835563210137070679 3518437208883200 

noncomputable abbrev qz174 := qz486

noncomputable def Ns288p1010 := @Enclosure.Real.IsNear.subLit_ff_p qz174 qz659 30685388235575827891 17592186044416000 4828033690077 1000000000000000000 609988 2000 0 1 50639754090290428774000 25319877045145214387 17592186044416000 4828033690077 1000000000000000000 

noncomputable def Ns288p1011 := nat_lit 1105557624187666401758813588698431488 

noncomputable def Ns288p1012 := nat_lit 27661636875675946834722816 

noncomputable def Ns288p1013 := nat_lit 114786165097669761610965536465559609206665215013585889194733459422863236314057885864244459996549674296146349905923573567476203520 

noncomputable def Ns288p1014 := nat_lit 1170924240000044839870126201016315199595179725866603527256705328585915612943295484685949254223526507581355397663839690113941504 

noncomputable def Ns288p1015 := nat_lit 255654035772039258308460879094183354774616989184018710266527843461099651419217125204594869571942115250288353299734200320 

noncomputable def Ns288p1016 := BSN.log_dyadic_bound 439766440576 2536918440576 6 5 Ns288p1013 67108864 32000000 Ns288p1014 Ns288p1015 23503536 2976684881152 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 439766440576) (BSN.artanhQ 2536918440576) 0 5 Ns288p1014 Ns288p1013 Ns288p1015 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz487 := (Real.log (Enclosure.sfrac Bool.false 1488342440576 16000000))

noncomputable def Ns288p1017 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 609988 4000) qz487 609988 4000 0 1 3220238359141623 281474976710656 976563 31250000000000 491076689054020082631 281474976710656000 148922927811 31250000000000000 (Enclosure.Real.IsNear.const Bool.false 609988 4000) (BSN.isNear_log_sfrac 1488342440576 16000000 3220238359141623 281474976710656 976563 31250000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1488342440576) qz355)) Bool.false Ns288p1012 Ns288p93 1000000512000000 32000000000000000000000 3220238359141623 281474976710656 976563 31250000000000 (BSN.log_rat_reduce_isNear 1488342440576 16000000 16 2976684881152 2097152000000 23503536 67108864 24973259072661432 36028797018963968 32000000 1000000000000000 rfl rfl rfl rfl (Ns288p1016 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns288p1018 := BSN.arctan_dyadic_bound_f 1000 1219976 1 0 8388608 4000000 0 1 1 0 1 1 6876 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1219976) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1219976) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz488 := (@Nat.cast Real Real.instNatCast 1219976)

noncomputable def Ns288p1019 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz488)) 884279719003555 562949953421312 1 2000000000000000 6876 8388608 1 4000000 7414005081191248560128 883818278454691 562949953421312 500000001 2000000000000000 qz15 (Ns288p1018 rfl) rfl rfl 

noncomputable abbrev qz489 := (@HMul.hMul Real Real Real qz580 qz585 qz658)

noncomputable abbrev qz175 := qz489

noncomputable abbrev qz490 := qz658

noncomputable abbrev qz176 := qz490

noncomputable def Ns288p1020 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 609988 4000) qz487) qz175 491076689054020082631 281474976710656000 148922927811 31250000000000000 883818278454691 2251799813685248 500000001 8000000000000000 Ns288p1011 30685388235575827891 17592186044416000 4828033690077 1000000000000000000 (Ns288p1017 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz176 1 4 0 1 883818278454691 562949953421312 500000001 2000000000000000 883818278454691 2251799813685248 500000001 8000000000000000 qz363 Ns288p1019 rfl) 

noncomputable def Ns288p1021 := @Ns288p1007 Ns288p1001 Ns288p1002 7125792360647549 512000000000000000000 (@Ns288p1009 7125792360647549 512000000000000000000 (Ns288p1010 (Ns288p1020 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 609988 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz659 (Real.log Real.pi) 609988 2000 0 1 38410761 33554432 1 33554432 5857525820217 16777216000 152497 16777216000 (Enclosure.Real.IsNear.const Bool.false 609988 2000) RS289to300.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns288p1003 Ns288p1004) 

noncomputable def Ns288p1022 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz168) Bool.false Ns288p1001 Ns288p1002 7125792360647549 512000000000000000000 4572346507 4194304 117 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz168) (@HAdd.hAdd Real Real Real qz364 qz172 (Enclosure.sfrac Bool.true Ns288p1003 Ns288p1004)) Bool.false Ns288p1001 Ns288p1002 7125792360647549 512000000000000000000 Ns288p1005 (Ns288p1021 rfl rfl)) 

noncomputable def Ns288p1023 := nat_lit 856495983345948360943756216889280658535498510741633407877681082621126234161410510643158109650479164595665388755340484412084846944321536 

noncomputable def Ns288p1024 := nat_lit 609625406186554800458309446167736738585686480465505831921259094569531946201782702491479706919655488155969129614894181750287630336 

noncomputable def Ns288p1025 := nat_lit 4277162376101412273199223853802219891986410829345797131963701172327320887836544501765992592207461413222395689093028302084290552262557696 

noncomputable def Ns288p1026 := BSN.sin_dyadic_bound_f 53962068408 34359738368 4 3 16777216 8007813 Ns288p1023 Ns288p229 Ns288p1024 Ns288p1025 Ns288p232 Ns288p1024 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53962068408) qz376 0 3 Ns288p1023 Ns288p229 Ns288p1024 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53962068408) qz377 0 3 Ns288p1025 Ns288p232 Ns288p1024 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1027 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz168) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4572346507) qz413) Bool.false 4572346507 4194304 117 8388608 Bool.true 16777215 16777216 1 4000000 (Ns288p1022 rfl) (Enclosure.sfrac_false_div 4572346507 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4572346507) qz413) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949310746792013902905344) qz414) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 173 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q1 4572346507 4194304 226375608064910080 72057594037927936 173 949310746792013902905344 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 949310746792013902905344 604462909807314587353088 53962068408 34359738368 8007813 8000000 (Ns288p1026 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p1028 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz168) Bool.false Ns288p1001 Ns288p1002 7125792360647549 512000000000000000000 146315088226 134217728 1869 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz168) (@HAdd.hAdd Real Real Real qz364 qz172 (Enclosure.sfrac Bool.true Ns288p1003 Ns288p1004)) Bool.false Ns288p1001 Ns288p1002 7125792360647549 512000000000000000000 Ns288p1005 (Ns288p1021 rfl rfl)) 

noncomputable def Ns288p1029 := Ns288p1000 30975 BSN.abs_quadSignPos (BSN.cos_quad_nat0 424 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 35473006 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 267 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 74616177 134217728) qz171 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 1) Bool.true 16777215 16777216 1860893 131072000000 134217720 134217728 1906 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz168)) Bool.true 16777215 16777216 1860893 131072000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz168) qz168) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz168)) Bool.true 16777215 16777216 476388608 33554432000000 16777215 16777216 1860893 131072000000 (Ns288p1027 rfl rfl) rfl)) rfl) (Ns288p1028 rfl) RS289to300.d7 

noncomputable def Ns288p1030 := nat_lit 1971511545356779647440285076065454711267259264070040830171425362302468622011654352441820261543234666890625 

noncomputable def Ns288p1031 := nat_lit 821007780907405638389622724394104145099534552086858100584112073808206403688977746899760761962890625 

noncomputable def Ns288p1032 := nat_lit 11946827814180962213112620976686699535757567880598432503627622339484235151227954082530618789871248900490625 

noncomputable def Ns288p1033 := BSN.cos_dyadic_bound_f 174929185 134217728 4 3 134217728 67108864 Ns288p1030 Ns288p137 Ns288p1031 Ns288p1032 Ns288p140 Ns288p1031 35473006 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 174929185) qz369 0 3 Ns288p1030 Ns288p137 Ns288p1031 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 174929185) qz370 0 3 Ns288p1032 Ns288p140 Ns288p1031 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1034 := nat_lit 38456712857805706466518797221995840053437020321707312326694792247425 

noncomputable def Ns288p1035 := nat_lit 1535560736606680735306678238777938882718815535793450509094008961 

noncomputable def Ns288p1036 := nat_lit 100717476100679487072073020007126321572239222760270723840519256062081 

noncomputable def Ns288p1037 := BSN.sin_dyadic_bound_f 79119471 134217728 3 2 134217728 67108864 Ns288p1034 Ns288p109 Ns288p1035 Ns288p1036 Ns288p112 Ns288p1035 74616177 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 79119471) qz367 0 2 Ns288p1034 Ns288p109 Ns288p1035 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 79119471) qz368 0 2 Ns288p1036 Ns288p112 Ns288p1035 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1038 := nat_lit 367101918678916656762925098636000146964303041535977242457650495340800 

noncomputable def Ns288p1039 := nat_lit 139829808051028444509823775078708821471072782889017016667168686336 

noncomputable def Ns288p1040 := nat_lit 961231014946032435945121257934634856338411943326691512219242548019456 

noncomputable def Ns288p1041 := BSN.sin_dyadic_bound_f 139059278 134217728 3 2 134217728 67108864 Ns288p1038 Ns288p109 Ns288p1039 Ns288p1040 Ns288p112 Ns288p1039 115482185 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 139059278) qz367 0 2 Ns288p1038 Ns288p109 Ns288p1039 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 139059278) qz368 0 2 Ns288p1040 Ns288p112 Ns288p1039 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1042 := BSN.sin_dyadic_bound_f 1295451 134217728 1 0 134217728 67108864 0 1 1 0 1 1 1295430 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1295451) qz367 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1295451) qz368 0 0 rfl) rfl rfl 

noncomputable def Ns288p1043 := Ns288p998 52411 BSN.abs_quadSignPos (BSN.cos_quad_nat3 155 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 115482185 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 69 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 1295430 134217728) qz171 rfl rfl (Ns288p1029 RS289to300.d9 RS289to300.d11 RS289to300.d13 RS289to300.d17 (Ns288p1033 rfl rfl) (Ns288p1037 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns288p1028 rfl) RS289to300.d19 RS289to300.d21 RS289to300.d23 RS289to300.d25 RS289to300.d17 (Ns288p1041 rfl rfl) (Ns288p1042 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns288p1044 := nat_lit 774539884666313558471912315922101799025768068197532588643795379429985 

noncomputable def Ns288p1045 := nat_lit 621938151229835577459338319803221201240322357499806026582286672481 

noncomputable def Ns288p1046 := nat_lit 2027549893309782443158169517754394734551193942414728522404997529608801 

noncomputable def Ns288p1047 := BSN.sin_dyadic_bound_f 167578539 134217728 3 2 134217728 67108864 Ns288p1044 Ns288p109 Ns288p1045 Ns288p1046 Ns288p112 Ns288p1045 127309373 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 167578539) qz367 0 2 Ns288p1044 Ns288p109 Ns288p1045 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 167578539) qz368 0 2 Ns288p1046 Ns288p112 Ns288p1045 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1048 := nat_lit 359781162369158508948854397866310733046615589567440704970286990024960 

noncomputable def Ns288p1049 := nat_lit 134310476286532627109352372179068796825666368553425209405659341056 

noncomputable def Ns288p1050 := nat_lit 942066541624284565850727328666333427546275465222782015059332953989376 

noncomputable def Ns288p1051 := BSN.sin_dyadic_bound_f 138361014 134217728 3 2 134217728 67108864 Ns288p1048 Ns288p109 Ns288p1049 Ns288p1050 Ns288p112 Ns288p1049 115124786 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 138361014) qz367 0 2 Ns288p1048 Ns288p109 Ns288p1049 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 138361014) qz368 0 2 Ns288p1050 Ns288p112 Ns288p1049 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1052 := Ns288p996 70686 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 1 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 127309373 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 115124786 134217728) qz171 rfl rfl (Ns288p1043 rfl rfl) (Ns288p1028 rfl) RS289to300.d27 RS289to300.d29 RS289to300.d31 RS289to300.d33 RS289to300.d17 (Ns288p1047 rfl rfl) (Ns288p1051 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p1053 := nat_lit 131799125381274906534443442909587331331416645999430244864341265553505 

noncomputable def Ns288p1054 := nat_lit 18032816801210221451830122719042782631234747930137763224718874721 

noncomputable def Ns288p1055 := nat_lit 345158989533279938660239387421659798505640645168525656361387103033441 

noncomputable def Ns288p1056 := BSN.sin_dyadic_bound_f 107648491 134217728 3 2 134217728 67108864 Ns288p1053 Ns288p109 Ns288p1054 Ns288p1055 Ns288p112 Ns288p1054 96472816 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 107648491) qz367 0 2 Ns288p1053 Ns288p109 Ns288p1054 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 107648491) qz368 0 2 Ns288p1055 Ns288p112 Ns288p1054 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1057 := nat_lit 7631434647932597020127431735441 

noncomputable def Ns288p1058 := BSN.sin_dyadic_bound_f 52559539 134217728 2 1 134217728 67108864 Ns288p1057 Ns288p115 Ns288p1057 Ns288p1057 Ns288p116 Ns288p1057 51226468 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 52559539) qz367 0 1 Ns288p1057 Ns288p115 Ns288p1057 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 52559539) qz368 0 1 Ns288p1057 Ns288p116 Ns288p1057 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1059 := Ns288p994 86235 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 113 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 96472816 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 51226468 134217728) qz171 rfl rfl (Ns288p1052 rfl) (Ns288p1028 rfl) RS289to300.d35 RS289to300.d37 RS289to300.d39 RS289to300.d41 RS289to300.d17 (Ns288p1056 rfl rfl) (Ns288p1058 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p1060 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 9) 121412802 134217728 86235 134217728 121412802 134217728 86235 134217728 32591500869107712 60706401 33554432 86235 67108864 (Ns288p1059 rfl) 

noncomputable def Ns288p1061 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz169) (Zeta.RiemannSiegel.correction qz170) 2672419 8388608 1 8388608 44404056993367 70368744177664 73948271399463 1099511627776000000 118666245586156844773 590295810358705651712 

noncomputable def Ns288p1062 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz169 1 1 0 1 2672419 8388608 1 8388608 2672419 8388608 1 8388608 

noncomputable abbrev qz177 := qz483

noncomputable def Ns288p1063 := @Enclosure.Real.IsNear.sqrt_image qz177 407193981969 4194304000 152497 4194304000 82653365 82653397 8388608 (@Enclosure.Real.IsNear.of_eq qz177 (@HMul.hMul Real Real Real qz5 qz168 qz3) Bool.false 407193981969 4194304000 152497 4194304000 (BSN.t_div_two_pi_mk qz168 609988 1000 qz171) (@Enclosure.Real.IsNear.mulLit_ff qz168 qz3 609988 1000 0 1 2670177 16777216 1 16777216 407193981969 4194304000 152497 4194304000 (Enclosure.Real.IsNear.const Bool.false 609988 1000) RS289to300.d44 rfl)) 

noncomputable abbrev qz748 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 609988 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz660 := qz748

noncomputable abbrev qz491 := qz660

noncomputable abbrev qz178 := qz491

noncomputable def Ns288p1064 := @Enclosure.Real.IsNear.sqrt_image qz178 82653381 8388608 1 524288 26331476 26331483 8388608 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 165306762 16777216 32 16777216 82653381 8388608 1 524288 (Ns288p1063 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns288p1065 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz178) 52662959 16777216 7 16777216 2672418 2672420 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz178) Bool.false 52662959 16777216 7 16777216 52662959 16777216 7 16777216 (Ns288p1064 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns288p1066 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz178)) Bool.false 5344838 16777216 2 16777216 2672419 8388608 1 8388608 (Ns288p1065 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz179 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz484))

noncomputable abbrev qz661 := (@HMul.hMul Real Real Real qz708 qz747 qz747)

noncomputable abbrev qz492 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz661 qz656) qz594)

noncomputable abbrev qz180 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz492))

noncomputable def Ns288p1067 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz170) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz179) qz180) Bool.false 44404056993367 

noncomputable def Ns288p1068 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz179) qz180 13907207 8388608 71 

noncomputable def Ns288p1069 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz179) Bool.false 27814414 16777216 568 16777216 13907207 8388608 71 

noncomputable def Ns288p1070 := @Enclosure.Real.IsNear.recentre' qz179 Bool.false 10119752 16777216 412388608 33554432000000 1264969 2097152 1610893 131072000000 

noncomputable abbrev qz181 := (@HMul.hMul Real Real Real qz346 qz343 qz484)

noncomputable def Ns288p1071 := @Enclosure.Real.IsNear.cos_image qz181 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 22480951) qz413) Bool.false 22480951 4194304 101 8388608 Bool.false 10119752 16777216 1 

noncomputable def Ns288p1072 := nat_lit 90071992547409920000000000000 

noncomputable def Ns288p1073 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz170 884279719003555 140737488355328 1 500000000000000 7155909 8388608 1 524288 6327825199735010256495 1180591620717411303424 1079443016515433793847519 

noncomputable def Ns288p1074 := @Enclosure.Real.IsNear.subLit_ff_p qz178 qz1 82653381 8388608 1 524288 9 1 0 1 7155909 7155909 8388608 1 

noncomputable def Ns288p1075 := @Ns288p1074 524288 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 165306762 16777216 32 16777216 82653381 8388608 1 524288 (Ns288p1063 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns288p1076 := @Enclosure.Real.IsNear.recentre' qz181 Bool.false 6327825199735010256495 1180591620717411303424 1079443016515433793847519 Ns288p1072 22480951 4194304 101 8388608 (@Ns288p1073 Ns288p1072 RS289to300.d43 (Ns288p1075 rfl rfl) rfl) 

noncomputable def Ns288p1077 := nat_lit 1032597662484526745860266732054677574878240712951494388644734679830460464941605565979585 

noncomputable def Ns288p1078 := nat_lit 704955687610872565255254336748118540842396593755240389471857687246053587015266059818106880 

noncomputable def Ns288p1079 := nat_lit 60013565907656321262497397665583516841214908703330142838449162483456154286180752321 

noncomputable def Ns288p1080 := nat_lit 2704325284543243367018654540546982703749077995496965626219233339007185145835360761109441 

noncomputable def Ns288p1081 := nat_lit 12924187606199330363012996173715506582110604218846073806984057599510982428613211096665292800 

noncomputable def Ns288p1082 := BSN.sin_dyadic_bound_f 22247498137 34359738368 3 2 16777216 8007813 Ns288p1077 Ns288p1078 Ns288p1079 Ns288p1080 Ns288p1081 Ns288p1079 10119752 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 22247498137) qz376 0 2 Ns288p1077 Ns288p1078 Ns288p1079 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 22247498137) qz377 0 2 Ns288p1080 Ns288p1081 Ns288p1079 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1083 := @Ns288p1071 4000000 (Ns288p1076 rfl) (Enclosure.sfrac_false_div 22480951 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 22480951) qz413) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 391382126261846316941312) qz414) 226375608064910080 72057594037927936 Bool.false 10119752 16777216 0 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q3 22480951 4194304 226375608064910080 72057594037927936 0 391382126261846316941312 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 10119752 16777216 391382126261846316941312 604462909807314587353088 22247498137 34359738368 8007813 8000000 (Ns288p1082 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p1084 := @Enclosure.Real.IsNear.inv_image qz179 1264969 2097152 1610893 131072000000 13906923 13907491 8388608 (Ns288p1070 (Ns288p1083 rfl rfl) rfl) rfl 

noncomputable def Ns288p1085 := @Enclosure.Real.IsNear.recentre' qz180 Bool.false 3192881 8388608 

noncomputable abbrev qz182 := (@HMul.hMul Real Real Real qz346 qz343 qz492)

noncomputable def Ns288p1086 := @Enclosure.Real.IsNear.cos_image qz182 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 19802625)) qz365) Bool.true 19802625 16777216 

noncomputable def Ns288p1087 := nat_lit 11689407128891757963294104725 

noncomputable def Ns288p1088 := nat_lit 306297919818863797404685649166427 

noncomputable def Ns288p1089 := @Enclosure.Real.IsNear.recentre' qz182 Bool.true Ns288p1087 Ns288p292 Ns288p1088 

noncomputable abbrev qz183 := qz492

noncomputable def Ns288p1090 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz183 884279719003555 140737488355328 1 500000000000000 13219128379495 

noncomputable abbrev qz493 := (@HSub.hSub Real Real Real qz584 qz661 qz656)

noncomputable abbrev qz184 := qz493

noncomputable def Ns288p1091 := @Enclosure.Real.IsNear.subLit_tf qz184 qz29 8821081868391 70368744177664 11350221 2199023255552 1 16 

noncomputable abbrev qz494 := qz661

noncomputable abbrev qz185 := qz494

noncomputable def Ns288p1092 := @Enclosure.Real.IsNear.subLit_ff_n qz185 qz170 51207033616281 70368744177664 7155917 2199023255552 7155909 8388608 1 524288 

noncomputable def Ns288p1093 := @Enclosure.Real.IsNear.mulLit_ff qz170 qz170 7155909 8388608 1 524288 7155909 8388608 1 524288 51207033616281 70368744177664 

noncomputable def Ns288p1094 := nat_lit 20491859913649461608246506872347575453852846710664918212890625 

noncomputable def Ns288p1095 := nat_lit 23647329722386381736747423234136625724706709384918212890625 

noncomputable def Ns288p1096 := nat_lit 61428285081503612061266025770574453110109126713224918212890625 

noncomputable def Ns288p1097 := BSN.cos_dyadic_bound_f 19802625 16777216 3 2 8388608 4000000 Ns288p1094 Ns288p767 Ns288p1095 Ns288p1096 Ns288p770 Ns288p1095 3192881 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 19802625) qz595 0 2 Ns288p1094 Ns288p767 Ns288p1095 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 19802625) (BSN.cosOddQ 16777216) 0 2 Ns288p1096 Ns288p770 Ns288p1095 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1098 := @Ns288p1085 1100388608 33554432000000 3192881 8388608 4298393 131072000000 (@Ns288p1086 273 8388608 Bool.false 3192881 8388608 1 4000000 (@Ns288p1089 Ns288p295 19802625 16777216 273 8388608 (@Ns288p1090 70368744177664 11350221 2199023255552 Ns288p1087 Ns288p292 Ns288p1088 Ns288p295 RS289to300.d43 (@Ns288p1091 0 1 211506054071920 13219128379495 70368744177664 11350221 2199023255552 (@Ns288p1092 73996597929839689728 8821081868391 70368744177664 11350221 2199023255552 (@Ns288p1093 7155917 2199023255552 (Ns288p1075 rfl rfl) (Ns288p1075 rfl rfl) rfl) (Ns288p1075 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 19802625 16777216) (BSN.cos_neg_of_bound 19802625 16777216 Bool.false 3192881 8388608 1 4000000 (Ns288p1097 rfl rfl)) rfl rfl) 

noncomputable def Ns288p1099 := @Ns288p1061 39662930568774853967 Ns288p69 (Ns288p1062 qz31 (@Enclosure.Real.IsNear.of_eq qz169 (@Inv.inv Real Real.instInv (Real.sqrt qz178)) Bool.false 2672419 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz177 (BSN.t_div_two_pi_nonneg qz168 609988 1000 qz171)) Ns288p1066) rfl) (@Ns288p1067 70368744177664 73948271399463 1099511627776000000 (BSN.correction_mk qz170 (BSN.cos_two_pi_p_ne_zero_mk qz168 609988 1000 9 qz171 rfl rfl (@BSN.floor_sqrt_eq_dec qz168 609988 1000 9 qz171 rfl rfl rfl))) (@Ns288p1068 2097152 3192881 8388608 4298393 131072000000 44404056993367 70368744177664 73948271399463 1099511627776000000 (@Ns288p1069 2097152 (Ns288p1084 rfl rfl rfl rfl rfl) rfl) (Ns288p1098 rfl) rfl)) 

noncomputable def Ns288p1100 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz168) (hardyZApproximantRS₀ qz168) Bool.true 949292054892764662043 590295810358705651712 2410072561100358853967 Ns288p69 (@Eq.refl Real (hardyZApproximantRS₀ qz168)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz168) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz169) (Zeta.RiemannSiegel.correction qz170))) Bool.true 949292054892764662043 590295810358705651712 2410072561100358853967 Ns288p69 (BSN.hardyZApproximantRS₀_eq qz168 9 (@BSN.floor_sqrt_eq_dec qz168 609988 1000 9 qz171 rfl rfl rfl)) (@Ns288p992 949292054892764662043 590295810358705651712 2410072561100358853967 Ns288p69 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 9) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 9)) Bool.true 60706401 33554432 86235 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz168) qz168 9) (Ns288p1060 (Ns288p1059 rfl) rfl rfl)) (Ns288p1099 rfl) rfl rfl)) 

theorem RS289to300.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz168) Bool.true 949292054892764662043 590295810358705651712 2410072561100358853967 Ns288p69 := Ns288p1100 

noncomputable def Ns288p1101 := nat_lit 32588424395732000961403551744 

noncomputable abbrev qz749 := (Enclosure.sfrac Bool.false 611361 1000)

noncomputable abbrev qz662 := qz749

noncomputable abbrev qz495 := qz662

noncomputable abbrev qz186 := qz495

noncomputable abbrev qz750 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 611361 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz663 := qz750

noncomputable abbrev qz496 := qz663

noncomputable abbrev qz187 := (@HPow.hPow Real Real Real qz347 qz496 qz349)

noncomputable abbrev qz751 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 611361 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz664 := qz751

noncomputable abbrev qz497 := qz664

noncomputable abbrev qz188 := qz497

noncomputable def Ns288p1102 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz186) qz186 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz187) (Zeta.RiemannSiegel.correction qz188)) 41346869 67108864 86435 67108864 121914459073271682419 590295810358705651712 183987412192858122373 Ns288p193 Ns288p1101 

noncomputable def Ns288p1103 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz186) qz186 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 611361 1000 113 159 134217728 67108864 2251799813685248 Bool.false 146736786546 1874 

noncomputable def Ns288p1104 := Ns288p1103 279097919 34 47453128 8 294906479 34 44739240 8 Bool.false 52946275 70850 Bool.true 69151614 Bool.true 35767814 7074237752028440 1 Bool.false 66132566 Bool.true Bool.false 35345958 Bool.false Bool.false 41346869 

noncomputable def Ns288p1105 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz186) qz186 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 611361 1000 1 61 134217728 67108864 2251799813685248 Bool.false 146736786546 1874 

noncomputable def Ns288p1106 := Ns288p1105 240485871 35 54794152 8 261175631 35 50729528 8 Bool.false 109341885 52534 Bool.true 76067320 Bool.true 75256835 7074237752028440 1 Bool.false 72060074 Bool.true Bool.false 71374997 Bool.true Bool.false 52946275 

noncomputable def Ns288p1107 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz186) qz186 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 611361 1000 156 69 134217728 67108864 2251799813685248 Bool.false 146736786546 1874 

noncomputable def Ns288p1108 := Ns288p1107 186065264 34 67108856 8 216015088 34 60023992 8 Bool.false 106714669 31050 Bool.false 94461276 Bool.false 126405056 7074237752028440 1 Bool.false 102326822 Bool.false Bool.false 108530219 Bool.true Bool.false 109341885 

noncomputable def Ns288p1109 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz186) qz186 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 611361 1000 426 268 134217728 67108864 2251799813685248 Bool.false 146736786546 1874 

noncomputable def Ns288p1110 := Ns288p1109 93032624 34 94906264 8 147453232 34 77490640 16 Bool.false 134217720 1914 Bool.false 47236284 Bool.false 87535789 7074237752028440 1 Bool.false 125991054 Bool.true Bool.false 106670216 Bool.false Bool.false 106714669 

noncomputable def Ns288p1111 := nat_lit 64271163215106100409648392860481593229135038991906661963 

noncomputable def Ns288p1112 := nat_lit 58787777118779730616838669766109765911237533630464000 

noncomputable def Ns288p1113 := nat_lit 40994975091309501027819750144480000 

noncomputable def Ns288p1114 := nat_lit 150376420739637971891951345894252623680 

noncomputable abbrev qz665 := (@Eq.refl Real qz749)

noncomputable abbrev qz498 := qz665

noncomputable abbrev qz189 := qz498

noncomputable def Ns288p1115 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz186 611361 1000 1495050089284 16000000 1222722 4000 2000 Ns288p1113 Ns288p1114 qz189 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns288p1116 := nat_lit 185100950059505569179787371438186988499908912296691186453440 

noncomputable abbrev qz666 := (@HSub.hSub Real Real Real qz712 qz713 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz714 (@Nat.cast Real Real.instNatCast 1222722))))

noncomputable abbrev qz499 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz580 (Enclosure.sfrac Bool.false 611361 4000) (Real.log (Enclosure.sfrac Bool.false 1495050089284 16000000))) (@HMul.hMul Real Real Real qz580 qz585 qz666))

noncomputable abbrev qz667 := (Enclosure.sfrac Bool.false 611361 2000)

noncomputable abbrev qz190 := (@HSub.hSub Real Real Real qz352 (@HSub.hSub Real Real Real qz352 qz499 qz667) (@HMul.hMul Real Real Real qz346 qz667 (Real.log Real.pi)))

noncomputable def Ns288p1117 := @Enclosure.Real.IsNear.addLit_ft_p qz190 (Enclosure.sfrac Bool.true Ns288p1113 Ns288p1114) 1230917688460137186683 1125899906842624000 28567038088603437 2048000000000000000000 Ns288p1113 Ns288p1114 0 1 Ns288p1116 

noncomputable def Ns288p1118 := nat_lit 82605487750065715882452058112000 

noncomputable abbrev qz191 := (@HSub.hSub Real Real Real qz352 qz499 qz667)

noncomputable def Ns288p1119 := @Enclosure.Real.IsNear.subLit_ff_p qz191 (@HMul.hMul Real Real Real qz5 qz667 (Real.log Real.pi)) 1624894388501079639419 1125899906842624000 4838760258069 1000000000000000000 23482841255721 67108864000 611361 67108864000 Ns288p1118 1230917688460137186683 1125899906842624000 

noncomputable def Ns288p1120 := nat_lit 3249788777002159278838000 

noncomputable abbrev qz192 := qz499

noncomputable def Ns288p1121 := @Enclosure.Real.IsNear.subLit_ff_p qz192 qz667 1969060034974686365051 1125899906842624000 4838760258069 1000000000000000000 611361 2000 0 1 Ns288p1120 1624894388501079639419 1125899906842624000 4838760258069 1000000000000000000 

noncomputable def Ns288p1122 := nat_lit 4433929019891066667401825417741467648 

noncomputable def Ns288p1123 := nat_lit 27672509177665968534454272 

noncomputable def Ns288p1124 := nat_lit 117857493715750915593553205545021991928427460463607817478684660763336193028630096441176104321583400240404240343973495344353771520 

noncomputable def Ns288p1125 := nat_lit 1233259814792453938957300224336414314848208394737032281630035498698642811163937372952340274921189141757033258922100731600175104 

noncomputable def Ns288p1126 := nat_lit 297436600821323102051330693101931363011839100442928485623225428710012405035134747840405814705927184921255753741704888320 

noncomputable def Ns288p1127 := BSN.log_dyadic_bound 446474089284 2543626089284 6 5 Ns288p1124 67108864 32000000 Ns288p1125 Ns288p1126 23805303 2990100178568 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 446474089284) (BSN.artanhQ 2543626089284) 0 5 Ns288p1125 Ns288p1124 Ns288p1126 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz500 := (Real.log (Enclosure.sfrac Bool.false 1495050089284 16000000))

noncomputable def Ns288p1128 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 611361 4000) qz500 611361 4000 0 1 3221504061676791 281474976710656 976563 31250000000000 1969501944650784622551 1125899906842624000 597032532243 125000000000000000 (Enclosure.Real.IsNear.const Bool.false 611361 4000) (BSN.isNear_log_sfrac 1495050089284 16000000 3221504061676791 281474976710656 976563 31250000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1495050089284) qz355)) Bool.false Ns288p1123 Ns288p93 1000000512000000 32000000000000000000000 3221504061676791 281474976710656 976563 31250000000000 (BSN.log_rat_reduce_isNear 1495050089284 16000000 16 2990100178568 2097152000000 23805303 67108864 24973259072661432 36028797018963968 32000000 1000000000000000 rfl rfl rfl rfl (Ns288p1127 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns288p1129 := BSN.arctan_dyadic_bound_f 1000 1222722 1 0 8388608 4000000 0 1 1 0 1 1 6860 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1222722) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1222722) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz501 := (@Nat.cast Real Real.instNatCast 1222722)

noncomputable def Ns288p1130 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz501)) 884279719003555 562949953421312 1 2000000000000000 6860 8388608 1 4000000 7414014088390503301120 883819352196515 562949953421312 500000001 2000000000000000 qz15 (Ns288p1129 rfl) rfl rfl 

noncomputable abbrev qz502 := (@HMul.hMul Real Real Real qz580 qz585 qz666)

noncomputable abbrev qz193 := qz502

noncomputable abbrev qz503 := qz666

noncomputable abbrev qz194 := qz503

noncomputable def Ns288p1131 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 611361 4000) qz500) qz193 1969501944650784622551 1125899906842624000 597032532243 125000000000000000 883819352196515 2251799813685248 500000001 8000000000000000 Ns288p1122 1969060034974686365051 1125899906842624000 4838760258069 1000000000000000000 (Ns288p1128 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz194 1 4 0 1 883819352196515 562949953421312 500000001 2000000000000000 883819352196515 2251799813685248 500000001 8000000000000000 qz363 Ns288p1130 rfl) 

noncomputable def Ns288p1132 := @Ns288p1117 Ns288p1111 Ns288p1112 28567038088603437 2048000000000000000000 (@Ns288p1119 28567038088603437 2048000000000000000000 (Ns288p1121 (Ns288p1131 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 611361 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz667 (Real.log Real.pi) 611361 2000 0 1 38410761 33554432 1 33554432 23482841255721 67108864000 611361 67108864000 (Enclosure.Real.IsNear.const Bool.false 611361 2000) RS289to300.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns288p1113 Ns288p1114) 

noncomputable def Ns288p1133 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz186) Bool.false Ns288p1111 Ns288p1112 28567038088603437 2048000000000000000000 9171049159 8388608 235 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz186) (@HAdd.hAdd Real Real Real qz364 qz190 (Enclosure.sfrac Bool.true Ns288p1113 Ns288p1114)) Bool.false Ns288p1111 Ns288p1112 28567038088603437 2048000000000000000000 Ns288p1115 (Ns288p1132 rfl rfl)) 

noncomputable def Ns288p1134 := nat_lit 1898989813577217734606848 

noncomputable def Ns288p1135 := nat_lit 857162131698231784010351219367163323985814386485483054335983219570861351775626906904799896965183799427164026213926781003417866140123136 

noncomputable def Ns288p1136 := nat_lit 611046080868877918862339930444752059375868832084084354685879943478349590519250969955213465356390011351584723869197184342410919936 

noncomputable def Ns288p1137 := nat_lit 4280484857820262748220730595473610564181321482332516443813957651169555168331753420063563654944398447631927554636324809465578607708471296 

noncomputable def Ns288p1138 := BSN.sin_dyadic_bound_f 53972536692 34359738368 4 3 16777216 8007813 Ns288p1135 Ns288p229 Ns288p1136 Ns288p1137 Ns288p232 Ns288p1136 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53972536692) qz376 0 3 Ns288p1135 Ns288p229 Ns288p1136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53972536692) qz377 0 3 Ns288p1137 Ns288p232 Ns288p1136 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1139 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz186) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9171049159) qz393) Bool.false 9171049159 8388608 235 16777216 Bool.false 16777215 16777216 1 4000000 (Ns288p1133 rfl) (Enclosure.sfrac_false_div 9171049159 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9171049159) qz393) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns288p1134) qz394) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 173 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q3 9171049159 8388608 226375608064910080 72057594037927936 173 Ns288p1134 Ns288p284 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns288p1134 Ns288p284 53972536692 34359738368 8007813 8000000 (Ns288p1138 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p1140 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz186) Bool.false Ns288p1111 Ns288p1112 28567038088603437 2048000000000000000000 146736786546 134217728 1874 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz186) (@HAdd.hAdd Real Real Real qz364 qz190 (Enclosure.sfrac Bool.true Ns288p1113 Ns288p1114)) Bool.false Ns288p1111 Ns288p1112 28567038088603437 2048000000000000000000 Ns288p1115 (Ns288p1132 rfl rfl)) 

noncomputable def Ns288p1141 := Ns288p1110 31050 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 426 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 125991054 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 268 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 106670216 134217728) qz189 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 1) Bool.false 16777215 16777216 3737411 262144000000 134217720 134217728 1914 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz186)) Bool.false 16777215 16777216 3737411 262144000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz186) qz186) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz186)) Bool.false 16777215 16777216 956777216 67108864000000 16777215 16777216 3737411 262144000000 (Ns288p1139 rfl rfl) rfl)) rfl) (Ns288p1140 rfl) RS289to300.d7 

noncomputable def Ns288p1142 := nat_lit 2714286455442847514294260066472786430067809095878429440352704331776 

noncomputable def Ns288p1143 := nat_lit 24785963195396805659636415168167013255723436409164516410064896 

noncomputable def Ns288p1144 := nat_lit 8142809794402151749271460926588022956176915840762469992025292865536 

noncomputable def Ns288p1145 := BSN.cos_dyadic_bound_f 47236284 134217728 3 2 134217728 67108864 Ns288p1142 Ns288p123 Ns288p1143 Ns288p1144 Ns288p126 Ns288p1143 125991054 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 47236284) qz369 0 2 Ns288p1142 Ns288p123 Ns288p1143 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 47236284) qz370 0 2 Ns288p1144 Ns288p126 Ns288p1143 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1146 := nat_lit 32013870544956169598925514158819238569280956624612364701936988649761 

noncomputable def Ns288p1147 := nat_lit 3447348621729079515060473803089829934071602349232386570237704481 

noncomputable def Ns288p1148 := nat_lit 96034716937625050637746421528851536047974726669138629332670490540321 

noncomputable def Ns288p1149 := BSN.cos_dyadic_bound_f 87535789 134217728 3 2 134217728 67108864 Ns288p1146 Ns288p123 Ns288p1147 Ns288p1148 Ns288p126 Ns288p1147 106670216 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 87535789) qz369 0 2 Ns288p1146 Ns288p123 Ns288p1147 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 87535789) qz370 0 2 Ns288p1148 Ns288p126 Ns288p1147 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1150 := nat_lit 43413766253905167783364361192305650363389410317917802415223598022656 

noncomputable def Ns288p1151 := nat_lit 6339141739772267028999359004153714329379837366617499745428504576 

noncomputable def Ns288p1152 := nat_lit 130228620478235958816035084858908643661509471279020172246179937058816 

noncomputable def Ns288p1153 := BSN.cos_dyadic_bound_f 94461276 134217728 3 2 134217728 67108864 Ns288p1150 Ns288p123 Ns288p1151 Ns288p1152 Ns288p126 Ns288p1151 102326822 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 94461276) qz369 0 2 Ns288p1150 Ns288p123 Ns288p1151 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 94461276) qz370 0 2 Ns288p1152 Ns288p126 Ns288p1151 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1154 := nat_lit 250606349518849275753528097759134802044795383772338682774706129469440 

noncomputable def Ns288p1155 := nat_lit 65180181134306676640931243231015788573643113666498142013296214016 

noncomputable def Ns288p1156 := nat_lit 656244433208483035211345414975359979792963916267331743608589764263936 

noncomputable def Ns288p1157 := BSN.sin_dyadic_bound_f 126405056 134217728 3 2 134217728 67108864 Ns288p1154 Ns288p109 Ns288p1155 Ns288p1156 Ns288p112 Ns288p1155 108530219 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 126405056) qz367 0 2 Ns288p1154 Ns288p109 Ns288p1155 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 126405056) qz368 0 2 Ns288p1156 Ns288p112 Ns288p1155 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1158 := Ns288p1108 52534 BSN.abs_quadSignPos (BSN.cos_quad_nat0 156 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 102326822 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 69 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 108530219 134217728) qz189 rfl rfl (Ns288p1141 RS289to300.d9 RS289to300.d11 RS289to300.d13 RS289to300.d17 (Ns288p1145 rfl rfl) (Ns288p1149 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns288p1140 rfl) RS289to300.d19 RS289to300.d21 RS289to300.d23 RS289to300.d25 RS289to300.d17 (Ns288p1153 rfl rfl) (Ns288p1157 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns288p1159 := nat_lit 32857052149147696624169734487120747364619342023926274162625085440000 

noncomputable def Ns288p1160 := nat_lit 1120946599566711499078614249806706893841928340666063257600000000 

noncomputable def Ns288p1161 := nat_lit 86052369334225621244684129709864175096174913607255353942553395200000 

noncomputable def Ns288p1162 := BSN.sin_dyadic_bound_f 76067320 134217728 3 2 134217728 67108864 Ns288p1159 Ns288p109 Ns288p1160 Ns288p1161 Ns288p112 Ns288p1160 72060074 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 76067320) qz367 0 2 Ns288p1159 Ns288p109 Ns288p1160 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 76067320) qz368 0 2 Ns288p1161 Ns288p112 Ns288p1160 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1163 := nat_lit 31478882929004622232216736687744576162443151216480968919690184030625 

noncomputable def Ns288p1164 := nat_lit 1028886804690153249343228510184651228025069533910188748375390625 

noncomputable def Ns288p1165 := nat_lit 82443027568756893217211564193171686228220022121061921150738826590625 

noncomputable def Ns288p1166 := BSN.sin_dyadic_bound_f 75256835 134217728 3 2 134217728 67108864 Ns288p1163 Ns288p109 Ns288p1164 Ns288p1165 Ns288p112 Ns288p1164 71374997 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 75256835) qz367 0 2 Ns288p1163 Ns288p109 Ns288p1164 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 75256835) qz368 0 2 Ns288p1165 Ns288p112 Ns288p1164 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1167 := Ns288p1106 70850 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 1 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 72060074 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 71374997 134217728) qz189 rfl rfl (Ns288p1158 rfl rfl) (Ns288p1140 rfl) RS289to300.d27 RS289to300.d29 RS289to300.d31 RS289to300.d33 RS289to300.d17 (Ns288p1162 rfl rfl) (Ns288p1166 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p1168 := nat_lit 22440923344803671530167030811518874555231819037986142607560364130560 

noncomputable def Ns288p1169 := nat_lit 522899911157384454158888793538323744985639955876825186385920256 

noncomputable def Ns288p1170 := nat_lit 58773000255582027766083109162597990358591454063368477683784900280576 

noncomputable def Ns288p1171 := BSN.sin_dyadic_bound_f 69151614 134217728 3 2 134217728 67108864 Ns288p1168 Ns288p109 Ns288p1169 Ns288p1170 Ns288p112 Ns288p1169 66132566 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 69151614) qz367 0 2 Ns288p1168 Ns288p109 Ns288p1169 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 69151614) qz368 0 2 Ns288p1170 Ns288p112 Ns288p1169 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1172 := nat_lit 1636701927154720779412103251216 

noncomputable def Ns288p1173 := BSN.sin_dyadic_bound_f 35767814 134217728 2 1 134217728 67108864 Ns288p1172 Ns288p115 Ns288p1172 Ns288p1172 Ns288p116 Ns288p1172 35345958 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 35767814) qz367 0 1 Ns288p1172 Ns288p115 Ns288p1172 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 35767814) qz368 0 1 Ns288p1172 Ns288p116 Ns288p1172 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1174 := Ns288p1104 86435 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 113 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66132566 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 35345958 134217728) qz189 rfl rfl (Ns288p1167 rfl) (Ns288p1140 rfl) RS289to300.d35 RS289to300.d37 RS289to300.d39 RS289to300.d41 RS289to300.d17 (Ns288p1171 rfl rfl) (Ns288p1173 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p1175 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 9) 41346869 134217728 86435 134217728 41346869 134217728 86435 134217728 11098965634187264 41346869 67108864 86435 67108864 (Ns288p1174 rfl) 

noncomputable def Ns288p1176 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz187) (Zeta.RiemannSiegel.correction qz188) 2670917 8388608 1 8388608 45645169458007 70368744177664 68618432471561 1099511627776000000 121914459073271682419 590295810358705651712 

noncomputable def Ns288p1177 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz187 1 1 0 1 2670917 8388608 1 8388608 2670917 8388608 1 8388608 

noncomputable abbrev qz195 := qz496

noncomputable def Ns288p1178 := @Enclosure.Real.IsNear.sqrt_image qz195 1632442080897 16777216000 611361 16777216000 82746333 82746365 8388608 (@Enclosure.Real.IsNear.of_eq qz195 (@HMul.hMul Real Real Real qz5 qz186 qz3) Bool.false 1632442080897 16777216000 611361 16777216000 (BSN.t_div_two_pi_mk qz186 611361 1000 qz189) (@Enclosure.Real.IsNear.mulLit_ff qz186 qz3 611361 1000 0 1 2670177 16777216 1 16777216 1632442080897 16777216000 611361 16777216000 (Enclosure.Real.IsNear.const Bool.false 611361 1000) RS289to300.d44 rfl)) 

noncomputable abbrev qz752 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 611361 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz668 := qz752

noncomputable abbrev qz504 := qz668

noncomputable abbrev qz196 := qz504

noncomputable def Ns288p1179 := @Enclosure.Real.IsNear.sqrt_image qz196 82746349 8388608 1 524288 26346281 26346287 8388608 (@Enclosure.Real.IsNear.recentre' qz196 Bool.false 165492698 16777216 32 16777216 82746349 8388608 1 524288 (Ns288p1178 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns288p1180 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz196) 6586571 2097152 3 8388608 2670916 2670918 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz196) Bool.false 52692568 16777216 6 16777216 6586571 2097152 3 8388608 (Ns288p1179 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns288p1181 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz196)) Bool.false 5341834 16777216 2 16777216 2670917 8388608 1 8388608 (Ns288p1180 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz197 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz497))

noncomputable abbrev qz669 := (@HMul.hMul Real Real Real qz708 qz751 qz751)

noncomputable abbrev qz505 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz669 qz664) qz594)

noncomputable abbrev qz198 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz505))

noncomputable def Ns288p1182 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz188) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz197) qz198) Bool.false 45645169458007 

noncomputable def Ns288p1183 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz197) qz198 12763813 8388608 239 

noncomputable def Ns288p1184 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz197) Bool.false 25527626 16777216 478 16777216 12763813 8388608 239 

noncomputable def Ns288p1185 := @Enclosure.Real.IsNear.recentre' qz197 Bool.false 11026289 16777216 412388608 33554432000000 11026289 16777216 1610893 131072000000 

noncomputable abbrev qz199 := (@HMul.hMul Real Real Real qz346 qz343 qz497)

noncomputable def Ns288p1186 := @Enclosure.Real.IsNear.cos_image qz199 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 45546037) qz393) Bool.false 45546037 8388608 101 8388608 Bool.false 11026289 16777216 1 

noncomputable def Ns288p1187 := nat_lit 26986075412935756661134791 

noncomputable def Ns288p1188 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz188 884279719003555 140737488355328 1 500000000000000 7248877 8388608 1 524288 6410034916651332757735 1180591620717411303424 Ns288p1187 

noncomputable def Ns288p1189 := @Enclosure.Real.IsNear.subLit_ff_p qz196 qz1 82746349 8388608 1 524288 9 1 0 1 7248877 7248877 8388608 1 

noncomputable def Ns288p1190 := @Ns288p1189 524288 (@Enclosure.Real.IsNear.recentre' qz196 Bool.false 165492698 16777216 32 16777216 82746349 8388608 1 524288 (Ns288p1178 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns288p1191 := @Enclosure.Real.IsNear.recentre' qz199 Bool.false 6410034916651332757735 1180591620717411303424 Ns288p1187 Ns288p162 45546037 8388608 101 8388608 (@Ns288p1188 Ns288p162 RS289to300.d43 (Ns288p1190 rfl rfl) rfl) 

noncomputable def Ns288p1192 := nat_lit 1553782008437519712643312524611860531401728646092372716709054826558451163615791934266305 

noncomputable def Ns288p1193 := nat_lit 135875719596358446196028606696044320129863519957290611989546113783864999396718336961 

noncomputable def Ns288p1194 := nat_lit 4069209080457014667057691613382126843819555246447711978009065280611722028042336569580481 

noncomputable def Ns288p1195 := BSN.sin_dyadic_bound_f 24640115097 34359738368 3 2 16777216 8007813 Ns288p1192 Ns288p1078 Ns288p1193 Ns288p1194 Ns288p1081 Ns288p1193 11026289 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 24640115097) qz376 0 2 Ns288p1192 Ns288p1078 Ns288p1193 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 24640115097) qz377 0 2 Ns288p1194 Ns288p1081 Ns288p1193 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1196 := @Ns288p1186 4000000 (Ns288p1191 rfl) (Enclosure.sfrac_false_div 45546037 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 45546037) qz393) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 866946977910382703673344) qz394) 226375608064910080 72057594037927936 Bool.false 11026289 16777216 0 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q3 45546037 8388608 226375608064910080 72057594037927936 0 866946977910382703673344 Ns288p284 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 11026289 16777216 866946977910382703673344 Ns288p284 24640115097 34359738368 8007813 8000000 (Ns288p1195 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p1197 := @Enclosure.Real.IsNear.inv_image qz197 11026289 16777216 1610893 131072000000 12763574 12764052 8388608 (Ns288p1185 (Ns288p1196 rfl rfl) rfl) rfl 

noncomputable def Ns288p1198 := @Enclosure.Real.IsNear.recentre' qz198 Bool.false 3576139 8388608 

noncomputable abbrev qz200 := (@HMul.hMul Real Real Real qz346 qz343 qz505)

noncomputable def Ns288p1199 := @Enclosure.Real.IsNear.cos_image qz200 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 2370595)) (@Nat.cast Real Real.instNatCast 2097152)) Bool.true 2370595 2097152 

noncomputable def Ns288p1200 := nat_lit 11194818838593550690429044005 

noncomputable def Ns288p1201 := nat_lit 308806761277341665041050244895859 

noncomputable def Ns288p1202 := @Enclosure.Real.IsNear.recentre' qz200 Bool.true Ns288p1200 Ns288p292 Ns288p1201 

noncomputable abbrev qz201 := qz505

noncomputable def Ns288p1203 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz201 884279719003555 140737488355328 1 500000000000000 12659816343191 

noncomputable abbrev qz506 := (@HSub.hSub Real Real Real qz584 qz669 qz664)

noncomputable abbrev qz202 := qz506

noncomputable def Ns288p1204 := @Enclosure.Real.IsNear.subLit_tf qz202 qz29 8261769832087 70368744177664 11443189 2199023255552 1 16 

noncomputable abbrev qz507 := qz669

noncomputable abbrev qz203 := qz507

noncomputable def Ns288p1205 := @Enclosure.Real.IsNear.subLit_ff_n qz203 qz188 52546217761129 70368744177664 7248885 2199023255552 7248877 8388608 1 524288 

noncomputable def Ns288p1206 := @Enclosure.Real.IsNear.mulLit_ff qz188 qz188 7248877 8388608 1 524288 7248877 8388608 1 524288 52546217761129 70368744177664 

noncomputable def Ns288p1207 := nat_lit 1027259672381575762074823726246222676330311725488190625 

noncomputable def Ns288p1208 := nat_lit 15085502980398593449464978548510856026246963233994833920 

noncomputable def Ns288p1209 := nat_lit 997375997669197799972883498071860204718875875390625 

noncomputable def Ns288p1210 := nat_lit 3079784265149388890624525411742524308581497424713790625 

noncomputable def Ns288p1211 := nat_lit 678847634117936705225924034682988521181113345529767526400 

noncomputable def Ns288p1212 := BSN.cos_dyadic_bound_f 2370595 2097152 3 2 8388608 4000000 Ns288p1207 Ns288p1208 Ns288p1209 Ns288p1210 Ns288p1211 Ns288p1209 3576139 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2370595) (BSN.cosEvenQ 2097152) 0 2 Ns288p1207 Ns288p1208 Ns288p1209 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2370595) (BSN.cosOddQ 2097152) 0 2 Ns288p1210 Ns288p1211 Ns288p1209 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1213 := @Ns288p1198 1108388608 33554432000000 3576139 8388608 4329643 131072000000 (@Ns288p1199 275 8388608 Bool.false 3576139 8388608 1 4000000 (@Ns288p1202 Ns288p295 2370595 2097152 275 8388608 (@Ns288p1203 70368744177664 11443189 2199023255552 Ns288p1200 Ns288p292 Ns288p1201 Ns288p295 RS289to300.d43 (@Ns288p1204 0 1 202557061491056 12659816343191 70368744177664 11443189 2199023255552 (@Ns288p1205 69304748507603664896 8261769832087 70368744177664 11443189 2199023255552 (@Ns288p1206 7248885 2199023255552 (Ns288p1190 rfl rfl) (Ns288p1190 rfl rfl) rfl) (Ns288p1190 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 2370595 2097152) (BSN.cos_neg_of_bound 2370595 2097152 Bool.false 3576139 8388608 1 4000000 (Ns288p1212 rfl rfl)) rfl rfl) 

noncomputable def Ns288p1214 := @Ns288p1176 183987412192858122373 Ns288p193 (Ns288p1177 qz31 (@Enclosure.Real.IsNear.of_eq qz187 (@Inv.inv Real Real.instInv (Real.sqrt qz196)) Bool.false 2670917 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz195 (BSN.t_div_two_pi_nonneg qz186 611361 1000 qz189)) Ns288p1181) rfl) (@Ns288p1182 70368744177664 68618432471561 1099511627776000000 (BSN.correction_mk qz188 (BSN.cos_two_pi_p_ne_zero_mk qz186 611361 1000 9 qz189 rfl rfl (@BSN.floor_sqrt_eq_dec qz186 611361 1000 9 qz189 rfl rfl rfl))) (@Ns288p1183 8388608 3576139 8388608 4329643 131072000000 45645169458007 70368744177664 68618432471561 1099511627776000000 (@Ns288p1184 8388608 (Ns288p1197 rfl rfl rfl rfl rfl) rfl) (Ns288p1213 rfl) rfl)) 

noncomputable def Ns288p1215 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz186) (hardyZApproximantRS₀ qz186) Bool.false 485605364974319949171 590295810358705651712 12063523355545178122373 Ns288p193 (@Eq.refl Real (hardyZApproximantRS₀ qz186)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz186) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz186) qz186 9) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz187) (Zeta.RiemannSiegel.correction qz188))) Bool.false 485605364974319949171 590295810358705651712 12063523355545178122373 Ns288p193 (BSN.hardyZApproximantRS₀_eq qz186 9 (@BSN.floor_sqrt_eq_dec qz186 611361 1000 9 qz189 rfl rfl rfl)) (@Ns288p1102 485605364974319949171 590295810358705651712 12063523355545178122373 Ns288p193 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz186) qz186 9) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 9)) Bool.false 41346869 67108864 86435 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz186) qz186 9) (Ns288p1175 (Ns288p1174 rfl) rfl rfl)) (Ns288p1214 rfl) rfl rfl)) 

theorem RS289to300.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz186) Bool.false 485605364974319949171 590295810358705651712 12063523355545178122373 Ns288p193 := Ns288p1215 

noncomputable def Ns288p1216 := nat_lit 2305843009213693952000000 

noncomputable def Ns288p1217 := nat_lit 407515396973864761222496256 

noncomputable abbrev qz753 := (Enclosure.sfrac Bool.false 612733 1000)

noncomputable abbrev qz670 := qz753

noncomputable abbrev qz508 := qz670

noncomputable abbrev qz204 := qz508

noncomputable abbrev qz205 := qz347

noncomputable abbrev qz754 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 612733 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz671 := qz754

noncomputable abbrev qz509 := qz671

noncomputable abbrev qz206 := qz509

noncomputable abbrev qz207 := qz349

noncomputable abbrev qz755 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 612733 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz672 := qz755

noncomputable abbrev qz510 := qz672

noncomputable abbrev qz208 := qz510

noncomputable abbrev qz673 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz205 qz206 qz207))

noncomputable def Ns288p1218 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 9) (@HMul.hMul Real Real Real qz5 qz673 (Zeta.RiemannSiegel.correction qz208)) 23871921 8388608 86631 67108864 3915288479441145885 18446744073709551616 43175693036846263599 Ns288p1216 Ns288p1217 

noncomputable def Ns288p1219 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 612733 1000 113 159 134217728 67108864 2251799813685248 Bool.false 147158384132 1878 

noncomputable def Ns288p1220 := Ns288p1219 279097919 34 47453128 8 294906479 34 44739240 8 Bool.true 186532923 71012 Bool.true 30476373 Bool.true 18781917 7074237752028440 1 Bool.false 30215157 Bool.true Bool.false 18720678 Bool.false Bool.true 190975368 

noncomputable def Ns288p1221 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 612733 1000 0 61 134217728 67108864 2251799813685248 Bool.false 147158384132 1878 

noncomputable def Ns288p1222 := Ns288p1221 240485871 35 54794152 8 261175631 35 50729528 8 Bool.true 188354034 52655 Bool.true 195245063 Bool.true 11992215 7074237752028440 1 Bool.false 15548661 Bool.false Bool.false 11976265 Bool.true Bool.true 186532923 

noncomputable def Ns288p1223 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 612733 1000 157 70 134217728 67108864 2251799813685248 Bool.false 147158384132 1878 

noncomputable def Ns288p1224 := Ns288p1223 186065264 34 67108856 8 216015088 34 60023992 8 Bool.true 106680388 31123 Bool.false 49948606 Bool.false 40801227 7074237752028440 1 Bool.false 48803643 Bool.true Bool.false 128063699 Bool.true Bool.true 188354034 

noncomputable def Ns288p1225 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 612733 1000 427 269 134217728 67108864 2251799813685248 Bool.false 147158384132 1878 

noncomputable def Ns288p1226 := Ns288p1225 93032624 34 94906264 8 147453232 34 77490640 16 Bool.true 134217712 1922 Bool.false 130364395 Bool.false 95998827 7074237752028440 1 Bool.false 110812103 Bool.false Bool.false 88020509 Bool.true Bool.true 106680388 

noncomputable def Ns288p1227 := nat_lit 587957469976415142541389235651166419347422688038755249519 

noncomputable def Ns288p1228 := nat_lit 536254296660247943592126008570391336118129476501504000 

noncomputable def Ns288p1229 := nat_lit 41457043182813107568589849068640000 

noncomputable def Ns288p1230 := nat_lit 152412638004832372073487365631305958720 

noncomputable abbrev qz756 := (@Eq.refl Real (Enclosure.sfrac Bool.false 612733 1000))

noncomputable abbrev qz674 := qz756

noncomputable abbrev qz511 := qz674

noncomputable abbrev qz209 := qz511

noncomputable def Ns288p1231 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz204 612733 1000 1501767917156 16000000 1225466 4000 2000 Ns288p1229 Ns288p1230 qz209 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns288p1232 := nat_lit 188146390392452845613244555408373254191175260172401679846080 

noncomputable abbrev qz675 := (@HSub.hSub Real Real Real qz712 qz713 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz714 (@Nat.cast Real Real.instNatCast 1225466))))

noncomputable abbrev qz512 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz580 (Enclosure.sfrac Bool.false 612733 4000) (Real.log (Enclosure.sfrac Bool.false 1501767917156 16000000))) (@HMul.hMul Real Real Real qz580 qz585 qz675))

noncomputable abbrev qz676 := (Enclosure.sfrac Bool.false 612733 2000)

noncomputable abbrev qz210 := (@HSub.hSub Real Real Real qz352 (@HSub.hSub Real Real Real qz352 qz512 qz676) (@HMul.hMul Real Real Real qz346 qz676 (Real.log Real.pi)))

noncomputable def Ns288p1233 := @Enclosure.Real.IsNear.addLit_ft_p qz210 (Enclosure.sfrac Bool.true Ns288p1229 Ns288p1230) 1234454304655290859839 1125899906842624000 28630860217030361 2048000000000000000000 Ns288p1229 Ns288p1230 0 1 Ns288p1232 

noncomputable def Ns288p1234 := nat_lit 82842826045326481193378512896000 

noncomputable abbrev qz211 := (@HSub.hSub Real Real Real qz352 qz512 qz676)

noncomputable def Ns288p1235 := @Enclosure.Real.IsNear.subLit_ff_p qz211 (@HMul.hMul Real Real Real qz5 qz676 (Real.log Real.pi)) 1629315156666110640447 1125899906842624000 4849479013557 1000000000000000000 23535540819813 67108864000 612733 67108864000 Ns288p1234 1234454304655290859839 1125899906842624000 

noncomputable def Ns288p1236 := nat_lit 3258630313332221280894000 

noncomputable abbrev qz212 := qz512

noncomputable def Ns288p1237 := @Enclosure.Real.IsNear.subLit_ff_p qz212 qz676 1974253170475811406143 1125899906842624000 4849479013557 1000000000000000000 612733 2000 0 1 Ns288p1236 1629315156666110640447 1125899906842624000 4849479013557 1000000000000000000 

noncomputable def Ns288p1238 := nat_lit 4445622921444942281938283265695678464 

noncomputable def Ns288p1239 := nat_lit 27683349161825064223506432 

noncomputable def Ns288p1240 := nat_lit 121007416586289648110709355601428806275837977508916825598103463436199918458491769121328653176852154232132083800846204238451179520 

noncomputable def Ns288p1241 := nat_lit 1298360836463448747116512398000469660881789153108490713408872677463400890658729766902684361466467397834050958068907670795976704 

noncomputable def Ns288p1242 := nat_lit 345345151521076791318721183264030823695418031922966835314345157349448648400720276015023979894968514440916745283641016320 

noncomputable def Ns288p1243 := BSN.log_dyadic_bound 453191917156 2550343917156 6 5 Ns288p1240 67108864 32000000 Ns288p1241 Ns288p1242 24106173 3003535834312 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 453191917156) (BSN.artanhQ 2550343917156) 0 5 Ns288p1241 Ns288p1240 Ns288p1242 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz513 := (Real.log (Enclosure.sfrac Bool.false 1501767917156 16000000))

noncomputable def Ns288p1244 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 612733 4000) qz513 612733 4000 0 1 3222766001921271 281474976710656 976563 31250000000000 1974695080655226143643 1125899906842624000 598372376679 125000000000000000 (Enclosure.Real.IsNear.const Bool.false 612733 4000) (BSN.isNear_log_sfrac 1501767917156 16000000 3222766001921271 281474976710656 976563 31250000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1501767917156) qz355)) Bool.false Ns288p1239 Ns288p93 1000000512000000 32000000000000000000000 3222766001921271 281474976710656 976563 31250000000000 (BSN.log_rat_reduce_isNear 1501767917156 16000000 16 3003535834312 2097152000000 24106173 67108864 24973259072661432 36028797018963968 32000000 1000000000000000 rfl rfl rfl rfl (Ns288p1243 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns288p1245 := BSN.arctan_dyadic_bound_f 1000 1225466 1 0 8388608 4000000 0 1 1 0 1 1 6845 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1225466) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1225466) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns288p1246 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1225466))) 884279719003555 562949953421312 1 2000000000000000 6845 8388608 1 4000000 7414022532639804620800 883820358829475 562949953421312 500000001 2000000000000000 qz15 (Ns288p1245 rfl) rfl rfl 

noncomputable abbrev qz514 := (@HMul.hMul Real Real Real qz580 qz585 qz675)

noncomputable abbrev qz213 := qz514

noncomputable abbrev qz515 := qz675

noncomputable abbrev qz214 := qz515

noncomputable def Ns288p1247 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 612733 4000) qz513) qz213 1974695080655226143643 1125899906842624000 598372376679 125000000000000000 883820358829475 2251799813685248 500000001 8000000000000000 Ns288p1238 1974253170475811406143 1125899906842624000 4849479013557 1000000000000000000 (Ns288p1244 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz214 1 4 0 1 883820358829475 562949953421312 500000001 2000000000000000 883820358829475 2251799813685248 500000001 8000000000000000 qz363 Ns288p1246 rfl) 

noncomputable def Ns288p1248 := @Ns288p1233 Ns288p1227 Ns288p1228 28630860217030361 2048000000000000000000 (@Ns288p1235 28630860217030361 2048000000000000000000 (Ns288p1237 (Ns288p1247 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 612733 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz676 (Real.log Real.pi) 612733 2000 0 1 38410761 33554432 1 33554432 23535540819813 67108864000 612733 67108864000 (Enclosure.Real.IsNear.const Bool.false 612733 2000) RS289to300.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns288p1229 Ns288p1230) 

noncomputable def Ns288p1249 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz204) Bool.false Ns288p1227 Ns288p1228 28630860217030361 2048000000000000000000 287418719 262144 59 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz204) (@HAdd.hAdd Real Real Real qz364 qz210 (Enclosure.sfrac Bool.true Ns288p1229 Ns288p1230)) Bool.false Ns288p1227 Ns288p1228 28630860217030361 2048000000000000000000 Ns288p1231 (Ns288p1248 rfl rfl)) 

noncomputable def Ns288p1250 := nat_lit 856187368572042821717434132235149979323126421680702402931000787935196413474286363731327984469741186057002387212290063952748373606400000 

noncomputable def Ns288p1251 := nat_lit 608967978260793971106652937111862603229688635511758621932744627356557214248800535882942230454583485265645404092891136000000000000 

noncomputable def Ns288p1252 := nat_lit 4275623126798675689213889054265111944074128115860225806179539772945156037821320561049623128945121887185590351200150141879852204032000000 

noncomputable def Ns288p1253 := BSN.sin_dyadic_bound_f 53957216560 34359738368 4 3 16777216 8007813 Ns288p1250 Ns288p229 Ns288p1251 Ns288p1252 Ns288p232 Ns288p1251 16777214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53957216560) qz376 0 3 Ns288p1250 Ns288p229 Ns288p1251 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53957216560) qz377 0 3 Ns288p1252 Ns288p232 Ns288p1251 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1254 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz204) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 287418719) (@Nat.cast Real Real.instNatCast 262144)) Bool.false 287418719 262144 59 4194304 Bool.true 16777214 16777216 1 4000000 (Ns288p1249 rfl) (Enclosure.sfrac_false_div 287418719 262144) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 287418719) (@Nat.cast Real Real.instNatCast 262144)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 59326587010821314838528) (@Nat.cast Real Real.instNatCast 37778931862957161709568)) 226375608064910080 72057594037927936 Bool.false 16777214 16777216 174 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q1 287418719 262144 226375608064910080 72057594037927936 174 59326587010821314838528 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777214 16777216 59326587010821314838528 37778931862957161709568 53957216560 34359738368 8007813 8000000 (Ns288p1253 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p1255 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz204) Bool.false Ns288p1227 Ns288p1228 28630860217030361 2048000000000000000000 147158384132 134217728 1878 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz204) (@HAdd.hAdd Real Real Real qz364 qz210 (Enclosure.sfrac Bool.true Ns288p1229 Ns288p1230)) Bool.false Ns288p1227 Ns288p1228 28630860217030361 2048000000000000000000 Ns288p1231 (Ns288p1248 rfl rfl)) 

noncomputable def Ns288p1256 := Ns288p1226 31123 BSN.abs_quadSignPos (BSN.cos_quad_nat3 427 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 110812103 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 269 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 88020509 134217728) qz209 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 1) Bool.true 8388607 8388608 938259 65536000000 134217712 134217728 1922 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz204)) Bool.true 8388607 8388608 938259 65536000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz204) qz204) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz204)) Bool.true 16777214 16777216 240194304 16777216000000 8388607 8388608 938259 65536000000 (Ns288p1254 rfl rfl) rfl)) rfl) (Ns288p1255 rfl) RS289to300.d7 

noncomputable def Ns288p1257 := nat_lit 283520909748321828779216558939087949046323684089324588775446993430625 

noncomputable def Ns288p1258 := nat_lit 83420338532833863159728837560535048200514987270466005792250390625 

noncomputable def Ns288p1259 := nat_lit 742419702126075439595689521960608524090904053111697930402507053590625 

noncomputable def Ns288p1260 := BSN.sin_dyadic_bound_f 130364395 134217728 3 2 134217728 67108864 Ns288p1257 Ns288p109 Ns288p1258 Ns288p1259 Ns288p112 Ns288p1258 110812103 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 130364395) qz367 0 2 Ns288p1257 Ns288p109 Ns288p1258 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 130364395) qz368 0 2 Ns288p1259 Ns288p112 Ns288p1258 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1261 := nat_lit 83353263611092829543091334130405593998911453900586297514790160063585 

noncomputable def Ns288p1262 := nat_lit 7213190661680678362484753769659546343174572200647937159683267681 

noncomputable def Ns288p1263 := nat_lit 218294488101314689609795185502101868826879144241782111116668074876001 

noncomputable def Ns288p1264 := BSN.sin_dyadic_bound_f 95998827 134217728 3 2 134217728 67108864 Ns288p1261 Ns288p109 Ns288p1262 Ns288p1263 Ns288p112 Ns288p1262 88020509 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 95998827) qz367 0 2 Ns288p1261 Ns288p109 Ns288p1262 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 95998827) qz368 0 2 Ns288p1263 Ns288p112 Ns288p1262 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1265 := nat_lit 6224342593005677839893562951696 

noncomputable def Ns288p1266 := BSN.sin_dyadic_bound_f 49948606 134217728 2 1 134217728 67108864 Ns288p1265 Ns288p115 Ns288p1265 Ns288p1265 Ns288p116 Ns288p1265 48803643 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 49948606) qz367 0 1 Ns288p1265 Ns288p115 Ns288p1265 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 49948606) qz368 0 1 Ns288p1265 Ns288p116 Ns288p1265 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1267 := nat_lit 2771359682804580246388963169841 

noncomputable def Ns288p1268 := BSN.cos_dyadic_bound_f 40801227 134217728 2 1 134217728 67108864 Ns288p1267 Ns288p132 Ns288p1267 Ns288p1267 Ns288p133 Ns288p1267 128063699 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 40801227) qz369 0 1 Ns288p1267 Ns288p132 Ns288p1267 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 40801227) qz370 0 1 Ns288p1267 Ns288p133 Ns288p1267 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1269 := Ns288p1224 52655 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 157 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 48803643 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 70 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 128063699 134217728) qz209 rfl rfl (Ns288p1256 RS289to300.d9 RS289to300.d11 RS289to300.d13 RS289to300.d17 (Ns288p1260 rfl rfl) (Ns288p1264 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns288p1255 rfl) RS289to300.d19 RS289to300.d21 RS289to300.d23 RS289to300.d25 RS289to300.d17 (Ns288p1266 rfl rfl) (Ns288p1268 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns288p1270 := nat_lit 3062538222733119709207986188621476791415222630615160786097921231967260013455790566610695261817414911612961 

noncomputable def Ns288p1271 := nat_lit 3068744510087766862868527159271576035317108790305070768368388479132307032792018972305263880309659681 

noncomputable def Ns288p1272 := nat_lit 18546455762505979373651779743641726534260370872718879414918019390691998364750785879283258652409355972728865 

noncomputable def Ns288p1273 := BSN.cos_dyadic_bound_f 195245063 134217728 4 3 134217728 67108864 Ns288p1270 Ns288p137 Ns288p1271 Ns288p1272 Ns288p140 Ns288p1271 15548661 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 195245063) qz369 0 3 Ns288p1270 Ns288p137 Ns288p1271 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 195245063) qz370 0 3 Ns288p1272 Ns288p140 Ns288p1271 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1274 := nat_lit 20682242421134738956508750625 

noncomputable def Ns288p1275 := BSN.sin_dyadic_bound_f 11992215 134217728 2 1 134217728 67108864 Ns288p1274 Ns288p115 Ns288p1274 Ns288p1274 Ns288p116 Ns288p1274 11976265 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 11992215) qz367 0 1 Ns288p1274 Ns288p115 Ns288p1274 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 11992215) qz368 0 1 Ns288p1274 Ns288p116 Ns288p1274 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1276 := Ns288p1222 71012 BSN.abs_quadSignPos (BSN.cos_quad_nat0 0 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 15548661 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 11976265 134217728) qz209 rfl rfl (Ns288p1269 rfl rfl) (Ns288p1255 rfl) RS289to300.d27 RS289to300.d29 RS289to300.d31 RS289to300.d33 RS289to300.d17 (Ns288p1273 rfl rfl) (Ns288p1275 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p1277 := nat_lit 862686736637074730027523646641 

noncomputable def Ns288p1278 := BSN.sin_dyadic_bound_f 30476373 134217728 2 1 134217728 67108864 Ns288p1277 Ns288p115 Ns288p1277 Ns288p1277 Ns288p116 Ns288p1277 30215157 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 30476373) qz367 0 1 Ns288p1277 Ns288p115 Ns288p1277 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 30476373) qz368 0 1 Ns288p1277 Ns288p116 Ns288p1277 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1279 := nat_lit 124439904178783081567849722321 

noncomputable def Ns288p1280 := BSN.sin_dyadic_bound_f 18781917 134217728 2 1 134217728 67108864 Ns288p1279 Ns288p115 Ns288p1279 Ns288p1279 Ns288p116 Ns288p1279 18720678 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 18781917) qz367 0 1 Ns288p1279 Ns288p115 Ns288p1279 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 18781917) qz368 0 1 Ns288p1279 Ns288p116 Ns288p1279 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1281 := Ns288p1220 86631 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 113 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 30215157 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 18720678 134217728) qz209 rfl rfl (Ns288p1276 rfl) (Ns288p1255 rfl) RS289to300.d35 RS289to300.d37 RS289to300.d39 RS289to300.d41 RS289to300.d17 (Ns288p1278 rfl rfl) (Ns288p1280 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p1282 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 9) 190975368 134217728 86631 134217728 190975368 134217728 86631 134217728 51264559993847808 23871921 8388608 86631 67108864 (Ns288p1281 rfl) 

noncomputable def Ns288p1283 := @Enclosure.Real.IsNear.mulLit_tf qz673 (Zeta.RiemannSiegel.correction qz208) 2669421 8388608 1 8388608 1466718243185 2199023255552 32210982944209 549755813888000000 3915288479441145885 18446744073709551616 

noncomputable abbrev qz677 := (@HPow.hPow Real Real Real qz205 qz206 qz207)

noncomputable def Ns288p1284 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz677 1 1 0 1 2669421 8388608 1 8388608 2669421 8388608 1 8388608 

noncomputable def Ns288p1285 := @Enclosure.Real.IsNear.sqrt_image qz206 1636105563741 16777216000 612733 16777216000 82839130 82839162 8388608 (@Enclosure.Real.IsNear.of_eq qz206 (@HMul.hMul Real Real Real qz5 qz204 qz3) Bool.false 1636105563741 16777216000 612733 16777216000 (BSN.t_div_two_pi_mk qz204 612733 1000 qz209) (@Enclosure.Real.IsNear.mulLit_ff qz204 qz3 612733 1000 0 1 2670177 16777216 1 16777216 1636105563741 16777216000 612733 16777216000 (Enclosure.Real.IsNear.const Bool.false 612733 1000) RS289to300.d44 rfl)) 

noncomputable abbrev qz757 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 612733 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz678 := qz757

noncomputable abbrev qz516 := qz678

noncomputable abbrev qz215 := qz516

noncomputable def Ns288p1286 := @Enclosure.Real.IsNear.sqrt_image qz215 41419573 4194304 1 524288 26361050 26361056 8388608 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 165678292 16777216 32 16777216 41419573 4194304 1 524288 (Ns288p1285 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns288p1287 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz215) 26361053 8388608 3 8388608 2669420 2669422 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz215) Bool.false 52722106 16777216 6 16777216 26361053 8388608 3 8388608 (Ns288p1286 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns288p1288 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 5338842 16777216 2 16777216 2669421 8388608 1 8388608 (Ns288p1287 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz216 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz510))

noncomputable abbrev qz679 := (@HMul.hMul Real Real Real qz708 qz755 qz755)

noncomputable abbrev qz517 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz679 qz672) qz594)

noncomputable abbrev qz217 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz517))

noncomputable def Ns288p1289 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz208) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz216) qz217) Bool.false 1466718243185 

noncomputable def Ns288p1290 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz216) qz217 740545 524288 103 

noncomputable def Ns288p1291 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz216) Bool.false 23697440 16777216 412 16777216 740545 524288 103 

noncomputable def Ns288p1292 := @Enclosure.Real.IsNear.recentre' qz216 Bool.false 11877864 16777216 412388608 33554432000000 1484733 2097152 1610893 131072000000 

noncomputable abbrev qz218 := (@HMul.hMul Real Real Real qz346 qz343 qz510)

noncomputable def Ns288p1293 := @Enclosure.Real.IsNear.cos_image qz218 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23064549) qz413) Bool.false 23064549 4194304 101 8388608 Bool.false 11877864 16777216 1 

noncomputable def Ns288p1294 := nat_lit 5397215082597115334231131 

noncomputable def Ns288p1295 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz208 884279719003555 140737488355328 1 500000000000000 3670837 4194304 1 524288 3246046710867852825535 590295810358705651712 Ns288p1294 

noncomputable def Ns288p1296 := @Enclosure.Real.IsNear.subLit_ff_p qz215 qz1 41419573 4194304 1 524288 9 1 0 1 3670837 3670837 4194304 1 

noncomputable def Ns288p1297 := @Ns288p1296 524288 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 165678292 16777216 32 16777216 41419573 4194304 1 524288 (Ns288p1285 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns288p1298 := @Enclosure.Real.IsNear.recentre' qz218 Bool.false 3246046710867852825535 590295810358705651712 Ns288p1294 Ns288p279 23064549 4194304 101 8388608 (@Ns288p1295 Ns288p279 RS289to300.d43 (Ns288p1297 rfl rfl) rfl) 

noncomputable def Ns288p1299 := nat_lit 2249640939025622700128771821326436767585412280437551584006285959011808281045264785824705 

noncomputable def Ns288p1300 := nat_lit 284809244464222680994316611148502630700170133853246376057660142818574590988129229761 

noncomputable def Ns288p1301 := nat_lit 5891455625337974520758506828960713006083517601881634606836179395275886853399807944121281 

noncomputable def Ns288p1302 := BSN.sin_dyadic_bound_f 27028332953 34359738368 3 2 16777216 8007813 Ns288p1299 Ns288p1078 Ns288p1300 Ns288p1301 Ns288p1081 Ns288p1300 11877864 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 27028332953) qz376 0 2 Ns288p1299 Ns288p1078 Ns288p1300 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 27028332953) qz377 0 2 Ns288p1301 Ns288p1081 Ns288p1300 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1303 := @Ns288p1293 4000000 (Ns288p1298 rfl) (Enclosure.sfrac_false_div 23064549 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23064549) qz413) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 475487461792539652128768) qz414) 226375608064910080 72057594037927936 Bool.false 11877864 16777216 0 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q3 23064549 4194304 226375608064910080 72057594037927936 0 475487461792539652128768 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 11877864 16777216 475487461792539652128768 604462909807314587353088 27028332953 34359738368 8007813 8000000 (Ns288p1302 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p1304 := @Enclosure.Real.IsNear.inv_image qz216 1484733 2097152 1610893 131072000000 11848514 11848926 8388608 (Ns288p1292 (Ns288p1303 rfl rfl) rfl) rfl 

noncomputable def Ns288p1305 := @Enclosure.Real.IsNear.recentre' qz217 Bool.false 3961186 8388608 

noncomputable abbrev qz219 := (@HMul.hMul Real Real Real qz346 qz343 qz517)

noncomputable def Ns288p1306 := @Enclosure.Real.IsNear.cos_image qz219 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 18102613)) qz365) Bool.true 18102613 16777216 

noncomputable def Ns288p1307 := nat_lit 2671474166848764953805073525 

noncomputable def Ns288p1308 := nat_lit 155655494058460117447974572928591 

noncomputable def Ns288p1309 := @Enclosure.Real.IsNear.recentre' qz219 Bool.true Ns288p1307 Ns288p176 Ns288p1308 

noncomputable abbrev qz220 := qz517

noncomputable def Ns288p1310 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz220 884279719003555 140737488355328 1 500000000000000 3021073659655 

noncomputable abbrev qz518 := (@HSub.hSub Real Real Real qz584 qz679 qz672)

noncomputable abbrev qz221 := qz518

noncomputable def Ns288p1311 := @Enclosure.Real.IsNear.subLit_tf qz221 qz29 1921562031879 17592186044416 5767993 1099511627776 1 16 

noncomputable abbrev qz519 := qz679

noncomputable abbrev qz222 := qz519

noncomputable def Ns288p1312 := @Enclosure.Real.IsNear.subLit_ff_n qz222 qz208 13475044280569 17592186044416 3670841 1099511627776 3670837 4194304 1 524288 

noncomputable def Ns288p1313 := @Enclosure.Real.IsNear.mulLit_ff qz208 qz208 3670837 4194304 1 524288 3670837 4194304 1 524288 13475044280569 17592186044416 

noncomputable def Ns288p1314 := nat_lit 14305537816495929220865330922117614770240121456817671401941601 

noncomputable def Ns288p1315 := nat_lit 11532677216082021216962411516808321389574284254174902004321 

noncomputable def Ns288p1316 := nat_lit 42893548095055623620162067943319227667941215801944664401816161 

noncomputable def Ns288p1317 := BSN.cos_dyadic_bound_f 18102613 16777216 3 2 8388608 4000000 Ns288p1314 Ns288p767 Ns288p1315 Ns288p1316 Ns288p770 Ns288p1315 3961186 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 18102613) qz595 0 2 Ns288p1314 Ns288p767 Ns288p1315 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 18102613) (BSN.cosOddQ 16777216) 0 2 Ns288p1316 Ns288p770 Ns288p1315 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1318 := @Ns288p1305 1116388608 33554432000000 1980593 4194304 4360893 131072000000 (@Ns288p1306 277 8388608 Bool.false 3961186 8388608 1 4000000 (@Ns288p1309 Ns288p179 18102613 16777216 277 8388608 (@Ns288p1310 17592186044416 5767993 1099511627776 Ns288p1307 Ns288p176 Ns288p1308 Ns288p179 RS289to300.d43 (@Ns288p1311 0 1 48337178554480 3021073659655 17592186044416 5767993 1099511627776 (@Ns288p1312 8059615316558217216 1921562031879 17592186044416 5767993 1099511627776 (@Ns288p1313 3670841 1099511627776 (Ns288p1297 rfl rfl) (Ns288p1297 rfl rfl) rfl) (Ns288p1297 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 18102613 16777216) (BSN.cos_neg_of_bound 18102613 16777216 Bool.false 3961186 8388608 1 4000000 (Ns288p1317 rfl rfl)) rfl rfl) 

noncomputable def Ns288p1319 := @Ns288p1283 43175693036846263599 Ns288p1216 (Ns288p1284 qz31 (@Enclosure.Real.IsNear.of_eq qz677 (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 2669421 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz206 (BSN.t_div_two_pi_nonneg qz204 612733 1000 qz209)) Ns288p1288) rfl) (@Ns288p1289 2199023255552 32210982944209 549755813888000000 (BSN.correction_mk qz208 (BSN.cos_two_pi_p_ne_zero_mk qz204 612733 1000 9 qz209 rfl rfl (@BSN.floor_sqrt_eq_dec qz204 612733 1000 9 qz209 rfl rfl rfl))) (@Ns288p1290 4194304 1980593 4194304 4360893 131072000000 1466718243185 2199023255552 32210982944209 549755813888000000 (@Ns288p1291 4194304 (Ns288p1304 rfl rfl rfl rfl rfl) rfl) (Ns288p1318 rfl) rfl)) 

noncomputable def Ns288p1320 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz204) (hardyZApproximantRS₀ qz204) Bool.true 48579620954259009507 18446744073709551616 3019794187595054263599 Ns288p1216 (@Eq.refl Real (hardyZApproximantRS₀ qz204)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz204) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 9) (@HMul.hMul Real Real Real qz5 qz673 (Zeta.RiemannSiegel.correction qz208))) Bool.true 48579620954259009507 18446744073709551616 3019794187595054263599 Ns288p1216 (BSN.hardyZApproximantRS₀_eq qz204 9 (@BSN.floor_sqrt_eq_dec qz204 612733 1000 9 qz209 rfl rfl rfl)) (@Ns288p1218 48579620954259009507 18446744073709551616 3019794187595054263599 Ns288p1216 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 9) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 9)) Bool.true 23871921 8388608 86631 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz204) qz204 9) (Ns288p1282 (Ns288p1281 rfl) rfl rfl)) (Ns288p1319 rfl) rfl rfl)) 

theorem RS289to300.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz204) Bool.true 48579620954259009507 18446744073709551616 3019794187595054263599 Ns288p1216 := Ns288p1320 

noncomputable def Ns288p1321 := nat_lit 9874591921787865137034559488 

noncomputable abbrev qz758 := (Enclosure.sfrac Bool.false 614105 1000)

noncomputable abbrev qz680 := qz758

noncomputable abbrev qz520 := qz680

noncomputable abbrev qz223 := qz520

noncomputable abbrev qz759 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 614105 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz681 := qz759

noncomputable abbrev qz521 := qz681

noncomputable abbrev qz224 := qz521

noncomputable abbrev qz760 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 614105 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz682 := qz760

noncomputable abbrev qz522 := qz682

noncomputable abbrev qz225 := qz522

noncomputable abbrev qz683 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz205 qz224 qz207))

noncomputable def Ns288p1322 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (@HMul.hMul Real Real Real qz5 qz683 (Zeta.RiemannSiegel.correction qz225)) 52270731 67108864 21705 16777216 32198332896324038205 147573952589676412928 163323107728402240977 Ns288p193 Ns288p1321 

noncomputable def Ns288p1323 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 614105 1000 112 159 134217728 67108864 2251799813685248 Bool.false 147580187861 1882 

noncomputable def Ns288p1324 := Ns288p1323 279097919 34 47453128 8 294906479 34 44739240 8 Bool.false 48771107 71166 Bool.true 202423703 Bool.true 1589878 7074237752028440 1 Bool.false 8399518 Bool.false Bool.false 1589840 Bool.false Bool.false 52270731 

noncomputable def Ns288p1325 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 614105 1000 0 60 134217728 67108864 2251799813685248 Bool.false 147580187861 1882 

noncomputable def Ns288p1326 := Ns288p1325 240485871 35 54794152 8 261175631 35 50729528 8 Bool.true 9538257 52768 Bool.true 103387949 Bool.true 159350166 7074237752028440 1 Bool.false 96328281 Bool.false Bool.false 50225658 Bool.false Bool.false 48771107 

noncomputable def Ns288p1327 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 614105 1000 158 70 134217728 67108864 2251799813685248 Bool.false 147580187861 1882 

noncomputable def Ns288p1328 := Ns288p1327 186065264 34 67108856 8 216015088 34 60023992 8 Bool.false 77090495 31188 Bool.false 5642079 Bool.false 166232255 7074237752028440 1 Bool.false 134099158 Bool.true Bool.false 43780379 Bool.true Bool.true 9538257 

noncomputable def Ns288p1329 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 614105 1000 429 270 134217728 67108864 2251799813685248 Bool.false 147580187861 1882 

noncomputable def Ns288p1330 := Ns288p1329 93032624 34 94906264 8 147453232 34 77490640 16 Bool.false 134217696 1922 Bool.false 2869936 Bool.false 104668007 7074237752028440 1 Bool.false 2869717 Bool.true Bool.false 95432544 Bool.true Bool.false 77090495 

noncomputable def Ns288p1331 := nat_lit 7649395257463470142348884794600688300957363938810599 

noncomputable def Ns288p1332 := nat_lit 6956790521176727652510627556812296315708060467200 

noncomputable def Ns288p1333 := nat_lit 41923268413609968645845151500000000 

noncomputable def Ns288p1334 := nat_lit 154471780282088914149310533581445000000 

noncomputable abbrev qz761 := (@Eq.refl Real (Enclosure.sfrac Bool.false 614105 1000))

noncomputable abbrev qz684 := qz761

noncomputable abbrev qz523 := qz684

noncomputable abbrev qz226 := qz523

noncomputable def Ns288p1335 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz223 614105 1000 1508500804100 16000000 1228210 4000 2000 Ns288p1333 Ns288p1334 qz226 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns288p1336 := nat_lit 38246976287317350711744423973003441504786819694052995000000 

noncomputable abbrev qz685 := (@HSub.hSub Real Real Real qz712 qz713 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz714 (@Nat.cast Real Real.instNatCast 1228210))))

noncomputable abbrev qz524 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz580 (Enclosure.sfrac Bool.false 614105 4000) (Real.log (Enclosure.sfrac Bool.false 1508500804100 16000000))) (@HMul.hMul Real Real Real qz580 qz585 qz685))

noncomputable abbrev qz686 := (Enclosure.sfrac Bool.false 614105 2000)

noncomputable abbrev qz227 := (@HSub.hSub Real Real Real qz352 (@HSub.hSub Real Real Real qz352 qz524 qz686) (@HMul.hMul Real Real Real qz346 qz686 (Real.log Real.pi)))

noncomputable def Ns288p1337 := @Enclosure.Real.IsNear.addLit_ft_p qz227 (Enclosure.sfrac Bool.true Ns288p1333 Ns288p1334) 247598530021168594791 225179981368524800 5738936469091457 409600000000000000000 Ns288p1333 Ns288p1334 0 1 Ns288p1336 

noncomputable def Ns288p1338 := nat_lit 3323211215558104069780065484800 

noncomputable abbrev qz228 := (@HSub.hSub Real Real Real qz352 qz524 qz686)

noncomputable def Ns288p1339 := @Enclosure.Real.IsNear.subLit_ff_p qz228 (@HMul.hMul Real Real Real qz5 qz686 (Real.log Real.pi)) 326747530817308016487 225179981368524800 972039553809 200000000000000000 4717648076781 13421772800 122821 13421772800 Ns288p1338 247598530021168594791 225179981368524800 

noncomputable abbrev qz229 := qz524

noncomputable def Ns288p1340 := @Enclosure.Real.IsNear.subLit_ff_p qz229 qz686 395889607046466977639 225179981368524800 972039553809 200000000000000000 614105 2000 0 1 653495061634616032974000 326747530817308016487 225179981368524800 972039553809 200000000000000000 

noncomputable def Ns288p1341 := nat_lit 891464143387160384007552785000169472 

noncomputable def Ns288p1342 := nat_lit 27694164898603766149808128 

noncomputable def Ns288p1343 := nat_lit 124240222399282607210086398540578134400935637965641442661831619326634096155219240762797316580109690902380839500000000000000000000 

noncomputable def Ns288p1344 := nat_lit 1366382140813920331609185833508912291629447530150134810474587108810219468860984907073523170086447313406872900000000000000000000 

noncomputable def Ns288p1345 := nat_lit 400221236068786553650881301540474013908711885521947042813473437582579242965680948812592264324361894500000000000000000000 

noncomputable def Ns288p1346 := BSN.log_dyadic_bound 459924804100 2557076804100 6 5 Ns288p1343 67108864 32000000 Ns288p1344 Ns288p1345 24406370 3017001608200 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 459924804100) (BSN.artanhQ 2557076804100) 0 5 Ns288p1344 Ns288p1343 Ns288p1345 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz525 := (Real.log (Enclosure.sfrac Bool.false 1508500804100 16000000))

noncomputable def Ns288p1347 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 614105 4000) qz525 614105 4000 0 1 3224025119399159 281474976710656 976563 31250000000000 395977989189724107539 225179981368524800 119942444223 25000000000000000 (Enclosure.Real.IsNear.const Bool.false 614105 4000) (BSN.isNear_log_sfrac 1508500804100 16000000 3224025119399159 281474976710656 976563 31250000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1508500804100) qz355)) Bool.false Ns288p1342 Ns288p93 1000000512000000 32000000000000000000000 3224025119399159 281474976710656 976563 31250000000000 (BSN.log_rat_reduce_isNear 1508500804100 16000000 16 3017001608200 2097152000000 24406370 67108864 24973259072661432 36028797018963968 32000000 1000000000000000 rfl rfl rfl rfl (Ns288p1346 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns288p1348 := BSN.arctan_dyadic_bound_f 1000 1228210 1 0 8388608 4000000 0 1 1 0 1 1 6829 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1228210) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1228210) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns288p1349 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1228210))) 884279719003555 562949953421312 1 2000000000000000 6829 8388608 1 4000000 7414031539839059361792 883821432571299 562949953421312 500000001 2000000000000000 qz15 (Ns288p1348 rfl) rfl rfl 

noncomputable abbrev qz526 := (@HMul.hMul Real Real Real qz580 qz585 qz685)

noncomputable abbrev qz230 := qz526

noncomputable abbrev qz527 := qz685

noncomputable abbrev qz231 := qz527

noncomputable def Ns288p1350 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 614105 4000) qz525) qz230 395977989189724107539 225179981368524800 119942444223 25000000000000000 883821432571299 2251799813685248 500000001 8000000000000000 Ns288p1341 395889607046466977639 225179981368524800 972039553809 200000000000000000 (Ns288p1347 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz231 1 4 0 1 883821432571299 562949953421312 500000001 2000000000000000 883821432571299 2251799813685248 500000001 8000000000000000 qz363 Ns288p1349 rfl) 

noncomputable def Ns288p1351 := @Ns288p1337 Ns288p1331 Ns288p1332 5738936469091457 409600000000000000000 (@Ns288p1339 5738936469091457 409600000000000000000 (Ns288p1340 (Ns288p1350 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 614105 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz686 (Real.log Real.pi) 614105 2000 0 1 38410761 33554432 1 33554432 4717648076781 13421772800 122821 13421772800 (Enclosure.Real.IsNear.const Bool.false 614105 2000) RS289to300.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns288p1333 Ns288p1334) 

noncomputable def Ns288p1352 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns288p1331 Ns288p1332 5738936469091457 409600000000000000000 9223761741 8388608 59 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz364 qz227 (Enclosure.sfrac Bool.true Ns288p1333 Ns288p1334)) Bool.false Ns288p1331 Ns288p1332 5738936469091457 409600000000000000000 Ns288p1335 (Ns288p1351 rfl rfl)) 

noncomputable def Ns288p1353 := BSN.cos_dyadic_bound_f 22518474 34359738368 1 0 16777216 8007813 0 1 1 0 1 1 16777212 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 22518474) (BSN.cosEvenQ 34359738368) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 22518474) (BSN.cosOddQ 34359738368) 0 0 rfl) rfl rfl 

noncomputable def Ns288p1354 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz223) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9223761741) qz393) Bool.false 9223761741 8388608 59 4194304 Bool.false 16777212 16777216 1 4000000 (Ns288p1352 rfl) (Enclosure.sfrac_false_div 9223761741 8388608) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9223761741) qz393) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 792298380346525745152) qz394) 226375608064910080 72057594037927936 Bool.false 16777212 16777216 175 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q0 9223761741 8388608 226375608064910080 72057594037927936 175 792298380346525745152 Ns288p284 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777212 16777216 792298380346525745152 Ns288p284 22518474 34359738368 8007813 8000000 (Ns288p1353 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p1355 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns288p1331 Ns288p1332 5738936469091457 409600000000000000000 147580187861 134217728 1882 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz364 qz227 (Enclosure.sfrac Bool.true Ns288p1333 Ns288p1334)) Bool.false Ns288p1331 Ns288p1332 5738936469091457 409600000000000000000 Ns288p1335 (Ns288p1351 rfl rfl)) 

noncomputable def Ns288p1356 := Ns288p1330 31188 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 429 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 2869717 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 270 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 95432544 134217728) qz226 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) Bool.false 4194303 4194304 938259 65536000000 134217696 134217728 1922 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 4194303 4194304 938259 65536000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz223) qz223) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 16777212 16777216 240194304 16777216000000 4194303 4194304 938259 65536000000 (Ns288p1354 rfl rfl) rfl)) rfl) (Ns288p1355 rfl) RS289to300.d7 

noncomputable def Ns288p1357 := BSN.sin_dyadic_bound_f 2869936 134217728 1 0 134217728 67108864 0 1 1 0 1 1 2869717 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 2869936) qz367 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 2869936) qz368 0 0 rfl) rfl rfl 

noncomputable def Ns288p1358 := nat_lit 65448580154698171473837169256500768992412243687709506816604755538881 

noncomputable def Ns288p1359 := nat_lit 14404946120760961554310984399356789615925069636745847907323556801 

noncomputable def Ns288p1360 := nat_lit 196316930571852992498402885800703593398004880923855028753999619503041 

noncomputable def Ns288p1361 := BSN.cos_dyadic_bound_f 104668007 134217728 3 2 134217728 67108864 Ns288p1358 Ns288p123 Ns288p1359 Ns288p1360 Ns288p126 Ns288p1359 95432544 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 104668007) qz369 0 2 Ns288p1358 Ns288p123 Ns288p1359 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 104668007) qz370 0 2 Ns288p1360 Ns288p126 Ns288p1359 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1362 := nat_lit 1013343418788789348087102081 

noncomputable def Ns288p1363 := BSN.cos_dyadic_bound_f 5642079 134217728 2 1 134217728 67108864 Ns288p1362 Ns288p132 Ns288p1362 Ns288p1362 Ns288p133 Ns288p1362 134099158 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 5642079) qz369 0 1 Ns288p1362 Ns288p132 Ns288p1362 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 5642079) qz370 0 1 Ns288p1362 Ns288p133 Ns288p1362 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1364 := nat_lit 1607214848460646825431940337419509603025439226361685345345151267969433756159230314346925219081278976890625 

noncomputable def Ns288p1365 := nat_lit 445229113784805801852605138710106936537657468900255731053903700108892530182946186724114355712890625 

noncomputable def Ns288p1366 := nat_lit 9741342956462450900778566743530275095174675190568135313801178133057402280235456900534873809256738714490625 

noncomputable def Ns288p1367 := BSN.cos_dyadic_bound_f 166232255 134217728 4 3 134217728 67108864 Ns288p1364 Ns288p137 Ns288p1365 Ns288p1366 Ns288p140 Ns288p1365 43780379 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 166232255) qz369 0 3 Ns288p1364 Ns288p137 Ns288p1365 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 166232255) qz370 0 3 Ns288p1366 Ns288p140 Ns288p1365 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1368 := Ns288p1328 52768 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 158 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 134099158 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 70 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 43780379 134217728) qz226 rfl rfl (Ns288p1356 RS289to300.d9 RS289to300.d11 RS289to300.d13 RS289to300.d17 (Ns288p1357 rfl rfl) (Ns288p1361 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns288p1355 rfl) RS289to300.d19 RS289to300.d21 RS289to300.d23 RS289to300.d25 RS289to300.d17 (Ns288p1363 rfl rfl) (Ns288p1367 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns288p1369 := nat_lit 62304512040931582991543117099948037821504153828900359790435876232481 

noncomputable def Ns288p1370 := nat_lit 13054473451361292015552514674867754634000202047715505611503066401 

noncomputable def Ns288p1371 := nat_lit 186887427175892026390598246270494377955244461082605648360084622564641 

noncomputable def Ns288p1372 := BSN.cos_dyadic_bound_f 103387949 134217728 3 2 134217728 67108864 Ns288p1369 Ns288p123 Ns288p1370 Ns288p1371 Ns288p126 Ns288p1370 96328281 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 103387949) qz369 0 2 Ns288p1369 Ns288p123 Ns288p1370 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 103387949) qz370 0 2 Ns288p1371 Ns288p126 Ns288p1370 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1373 := nat_lit 1356838860034438759378116844270974651004726106804166496472028039777915984810278849383578801343399452020736 

noncomputable def Ns288p1374 := nat_lit 268058907183428528913075951773168165905340811934363244457523897327839457689248669317354508739219456 

noncomputable def Ns288p1375 := nat_lit 8225005338246172273386896413594045750099732174111140273440793509661755138362260449107535222729876434391040 

noncomputable def Ns288p1376 := BSN.cos_dyadic_bound_f 159350166 134217728 4 3 134217728 67108864 Ns288p1373 Ns288p137 Ns288p1374 Ns288p1375 Ns288p140 Ns288p1374 50225658 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 159350166) qz369 0 3 Ns288p1373 Ns288p137 Ns288p1374 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 159350166) qz370 0 3 Ns288p1375 Ns288p140 Ns288p1374 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1377 := Ns288p1326 71166 BSN.abs_quadSignPos (BSN.cos_quad_nat0 0 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 96328281 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 50225658 134217728) qz226 rfl rfl (Ns288p1368 rfl rfl) (Ns288p1355 rfl) RS289to300.d27 RS289to300.d29 RS289to300.d31 RS289to300.d33 RS289to300.d17 (Ns288p1372 rfl rfl) (Ns288p1376 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p1378 := nat_lit 3539861195365744746147402194211184602497924871162816669655675662862758056562503854309519233771641464506721 

noncomputable def Ns288p1379 := nat_lit 4732998680062424975151294615486666582504926230099742286611017969912788029502857447110242115500198241 

noncomputable def Ns288p1380 := nat_lit 21431179192628073209582655687336040019039823137696506886255008637858993145270997890207594112352887375481185 

noncomputable def Ns288p1381 := BSN.cos_dyadic_bound_f 202423703 134217728 4 3 134217728 67108864 Ns288p1378 Ns288p137 Ns288p1379 Ns288p1380 Ns288p140 Ns288p1379 8399518 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 202423703) qz369 0 3 Ns288p1378 Ns288p137 Ns288p1379 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 202423703) qz370 0 3 Ns288p1380 Ns288p140 Ns288p1379 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1382 := BSN.sin_dyadic_bound_f 1589878 134217728 1 0 134217728 67108864 0 1 1 0 1 1 1589840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1589878) qz367 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1589878) qz368 0 0 rfl) rfl rfl 

noncomputable def Ns288p1383 := Ns288p1324 86820 BSN.abs_quadSignPos (BSN.cos_quad_nat0 112 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 8399518 134217728) BSN.abs_quadSignPos qz371 (BSN.sfrac_eq_quadSignPos_mul Bool.false 1589840 134217728) qz226 rfl rfl (Ns288p1377 rfl) (Ns288p1355 rfl) RS289to300.d35 RS289to300.d37 RS289to300.d39 RS289to300.d41 RS289to300.d17 (Ns288p1381 rfl rfl) (Ns288p1382 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p1384 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) 52270731 134217728 86820 134217728 52270731 134217728 86820 134217728 14031317511438336 52270731 67108864 21705 16777216 (Ns288p1383 rfl) 

noncomputable def Ns288p1385 := @Enclosure.Real.IsNear.mulLit_tf qz683 (Zeta.RiemannSiegel.correction qz225) 5335857 16777216 1 16777216 6034332047565 8796093022208 61075823972613 1099511627776000000 32198332896324038205 147573952589676412928 

noncomputable abbrev qz687 := (@HPow.hPow Real Real Real qz205 qz224 qz207)

noncomputable def Ns288p1386 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz687 1 1 0 1 5335857 16777216 1 16777216 5335857 16777216 1 16777216 

noncomputable def Ns288p1387 := @Enclosure.Real.IsNear.sqrt_image qz224 327953809317 3355443200 122821 3355443200 82931823 82931855 8388608 (@Enclosure.Real.IsNear.of_eq qz224 (@HMul.hMul Real Real Real qz5 qz223 qz3) Bool.false 327953809317 3355443200 122821 3355443200 (BSN.t_div_two_pi_mk qz223 614105 1000 qz226) (@Enclosure.Real.IsNear.mulLit_ff qz223 qz3 614105 1000 0 1 2670177 16777216 1 16777216 327953809317 3355443200 122821 3355443200 (Enclosure.Real.IsNear.const Bool.false 614105 1000) RS289to300.d44 rfl)) 

noncomputable abbrev qz762 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 614105 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz688 := qz762

noncomputable abbrev qz528 := qz688

noncomputable abbrev qz232 := qz528

noncomputable def Ns288p1388 := @Enclosure.Real.IsNear.sqrt_image qz232 82931839 8388608 1 524288 26375794 26375800 8388608 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 165863678 16777216 32 16777216 82931839 8388608 1 524288 (Ns288p1387 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns288p1389 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz232) 26375797 8388608 3 8388608 2667928 2667929 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz232) Bool.false 52751594 16777216 6 16777216 26375797 8388608 3 8388608 (Ns288p1388 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns288p1390 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 5335857 16777216 1 16777216 5335857 16777216 1 16777216 (Ns288p1389 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz233 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz522))

noncomputable abbrev qz689 := (@HMul.hMul Real Real Real qz708 qz760 qz760)

noncomputable abbrev qz529 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz689 qz682) qz594)

noncomputable abbrev qz234 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz529))

noncomputable def Ns288p1391 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz225) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz233) qz234) Bool.false 6034332047565 

noncomputable def Ns288p1392 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz233) qz234 2776715 2097152 181 

noncomputable def Ns288p1393 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz233) Bool.false 22213720 16777216 362 16777216 2776715 2097152 181 

noncomputable def Ns288p1394 := @Enclosure.Real.IsNear.recentre' qz233 Bool.false 12671222 16777216 412388608 33554432000000 6335611 8388608 1610893 131072000000 

noncomputable abbrev qz235 := (@HMul.hMul Real Real Real qz346 qz343 qz522)

noncomputable def Ns288p1395 := @Enclosure.Real.IsNear.cos_image qz235 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 93423011) qz365) Bool.false 93423011 16777216 101 8388608 Bool.false 12671222 16777216 1 

noncomputable def Ns288p1396 := nat_lit 26986075413035340846601671 

noncomputable def Ns288p1397 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz225 884279719003555 140737488355328 1 500000000000000 7434367 8388608 1 524288 6574059961729302174685 1180591620717411303424 Ns288p1396 

noncomputable def Ns288p1398 := @Enclosure.Real.IsNear.subLit_ff_p qz232 qz1 82931839 8388608 1 524288 9 1 0 1 7434367 7434367 8388608 1 

noncomputable def Ns288p1399 := @Ns288p1398 524288 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 165863678 16777216 32 16777216 82931839 8388608 1 524288 (Ns288p1387 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns288p1400 := @Enclosure.Real.IsNear.recentre' qz235 Bool.false 6574059961729302174685 1180591620717411303424 Ns288p1396 Ns288p162 93423011 16777216 101 8388608 (@Ns288p1397 Ns288p162 RS289to300.d43 (Ns288p1399 rfl rfl) rfl) 

noncomputable def Ns288p1401 := nat_lit 2069817379968736666058752 

noncomputable def Ns288p1402 := nat_lit 3155492963445574814298437501826520087274031421414900178118811933564619451206567994006465 

noncomputable def Ns288p1403 := nat_lit 560296397670854877359907516768177272872219771267244172582315615633058581918698118081 

noncomputable def Ns288p1404 := nat_lit 8263479186285038367646848844994689846323527271695067785460326553101073610694095425444801 

noncomputable def Ns288p1405 := BSN.sin_dyadic_bound_f 29413874073 34359738368 3 2 16777216 8007813 Ns288p1402 Ns288p1078 Ns288p1403 Ns288p1404 Ns288p1081 Ns288p1403 12671222 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 29413874073) qz376 0 2 Ns288p1402 Ns288p1078 Ns288p1403 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 29413874073) qz377 0 2 Ns288p1404 Ns288p1081 Ns288p1403 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1406 := @Ns288p1395 4000000 (Ns288p1400 rfl) (Enclosure.sfrac_false_div 93423011 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 93423011) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns288p1401) qz366) 226375608064910080 72057594037927936 Bool.false 12671222 16777216 0 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q3 93423011 16777216 226375608064910080 72057594037927936 0 Ns288p1401 Ns288p93 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 12671222 16777216 Ns288p1401 Ns288p93 29413874073 34359738368 8007813 8000000 (Ns288p1405 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p1407 := @Enclosure.Real.IsNear.inv_image qz233 6335611 8388608 1610893 131072000000 11106679 11107041 8388608 (Ns288p1394 (Ns288p1406 rfl rfl) rfl) rfl 

noncomputable def Ns288p1408 := @Enclosure.Real.IsNear.recentre' qz234 Bool.false 4346382 8388608 

noncomputable abbrev qz236 := (@HMul.hMul Real Real Real qz346 qz343 qz529)

noncomputable def Ns288p1409 := @Enclosure.Real.IsNear.cos_image qz236 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 17215675)) qz365) Bool.true 17215675 16777216 

noncomputable def Ns288p1410 := nat_lit 10162340884944141591596563805 

noncomputable def Ns288p1411 := nat_lit 313812408404651821933094286756849 

noncomputable def Ns288p1412 := @Enclosure.Real.IsNear.recentre' qz236 Bool.true Ns288p1410 Ns288p292 Ns288p1411 

noncomputable abbrev qz237 := qz529

noncomputable def Ns288p1413 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz237 884279719003555 140737488355328 1 500000000000000 11492224311551 

noncomputable abbrev qz530 := (@HSub.hSub Real Real Real qz584 qz689 qz682)

noncomputable abbrev qz238 := qz530

noncomputable def Ns288p1414 := @Enclosure.Real.IsNear.subLit_tf qz238 qz29 7094177800447 70368744177664 11628679 2199023255552 1 16 

noncomputable abbrev qz531 := qz689

noncomputable abbrev qz239 := qz531

noncomputable def Ns288p1415 := @Enclosure.Real.IsNear.subLit_ff_n qz239 qz225 55269812690689 70368744177664 7434375 2199023255552 7434367 8388608 1 524288 

noncomputable def Ns288p1416 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz225 7434367 8388608 1 524288 7434367 8388608 1 524288 55269812690689 70368744177664 

noncomputable def Ns288p1417 := nat_lit 11699615864415767592868121775127631929060484149671563400390625 

noncomputable def Ns288p1418 := nat_lit 7716003982342541256622840889203916197204367505035400390625 

noncomputable def Ns288p1419 := nat_lit 35083415585282617696091119643604487954787043714004619400390625 

noncomputable def Ns288p1420 := BSN.cos_dyadic_bound_f 17215675 16777216 3 2 8388608 4000000 Ns288p1417 Ns288p767 Ns288p1418 Ns288p1419 Ns288p770 Ns288p1418 4346382 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 17215675) qz595 0 2 Ns288p1417 Ns288p767 Ns288p1418 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 17215675) (BSN.cosOddQ 16777216) 0 2 Ns288p1419 Ns288p770 Ns288p1418 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1421 := @Ns288p1408 1124388608 33554432000000 2173191 4194304 4392143 131072000000 (@Ns288p1409 279 8388608 Bool.false 4346382 8388608 1 4000000 (@Ns288p1412 Ns288p295 17215675 16777216 279 8388608 (@Ns288p1413 70368744177664 11628679 2199023255552 Ns288p1410 Ns288p292 Ns288p1411 Ns288p295 RS289to300.d43 (@Ns288p1414 0 1 183875588984816 11492224311551 70368744177664 11628679 2199023255552 (@Ns288p1415 59510276650252107776 7094177800447 70368744177664 11628679 2199023255552 (@Ns288p1416 7434375 2199023255552 (Ns288p1399 rfl rfl) (Ns288p1399 rfl rfl) rfl) (Ns288p1399 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 17215675 16777216) (BSN.cos_neg_of_bound 17215675 16777216 Bool.false 4346382 8388608 1 4000000 (Ns288p1420 rfl rfl)) rfl rfl) 

noncomputable def Ns288p1422 := @Ns288p1385 163323107728402240977 Ns288p193 (Ns288p1386 qz31 (@Enclosure.Real.IsNear.of_eq qz687 (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 5335857 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz224 (BSN.t_div_two_pi_nonneg qz223 614105 1000 qz226)) Ns288p1390) rfl) (@Ns288p1391 8796093022208 61075823972613 1099511627776000000 (BSN.correction_mk qz225 (BSN.cos_two_pi_p_ne_zero_mk qz223 614105 1000 9 qz226 rfl rfl (@BSN.floor_sqrt_eq_dec qz223 614105 1000 9 qz226 rfl rfl rfl))) (@Ns288p1392 8388608 2173191 4194304 4392143 131072000000 6034332047565 8796093022208 61075823972613 1099511627776000000 (@Ns288p1393 8388608 (Ns288p1407 rfl rfl rfl rfl rfl) rfl) (Ns288p1421 rfl) rfl)) 

noncomputable def Ns288p1423 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (hardyZApproximantRS₀ qz223) Bool.false 147142885950026886717 147573952589676412928 12095773048167442240977 Ns288p193 (@Eq.refl Real (hardyZApproximantRS₀ qz223)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (@HMul.hMul Real Real Real qz5 qz683 (Zeta.RiemannSiegel.correction qz225))) Bool.false 147142885950026886717 147573952589676412928 12095773048167442240977 Ns288p193 (BSN.hardyZApproximantRS₀_eq qz223 9 (@BSN.floor_sqrt_eq_dec qz223 614105 1000 9 qz226 rfl rfl rfl)) (@Ns288p1322 147142885950026886717 147573952589676412928 12095773048167442240977 Ns288p193 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 9)) Bool.false 52270731 67108864 21705 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (Ns288p1384 (Ns288p1383 rfl) rfl rfl)) (Ns288p1422 rfl) rfl rfl)) 

theorem RS289to300.d58 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz223) Bool.false 147142885950026886717 147573952589676412928 12095773048167442240977 Ns288p193 := Ns288p1423 

noncomputable def Ns288p1424 := nat_lit 21307981892576854419433324544 

noncomputable abbrev qz763 := (Enclosure.sfrac Bool.false 615476 1000)

noncomputable abbrev qz690 := qz763

noncomputable abbrev qz532 := qz690

noncomputable abbrev qz240 := qz532

noncomputable abbrev qz764 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 615476 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz691 := qz764

noncomputable abbrev qz533 := qz691

noncomputable abbrev qz241 := qz533

noncomputable abbrev qz765 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 615476 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz692 := qz765

noncomputable abbrev qz534 := qz692

noncomputable abbrev qz242 := qz534

noncomputable abbrev qz693 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz205 qz241 qz207))

noncomputable def Ns288p1425 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (@HMul.hMul Real Real Real qz5 qz693 (Zeta.RiemannSiegel.correction qz242)) 33103449 67108864 87017 67108864 264848360622962028913 1180591620717411303424 322180504286298576191 Ns288p451 Ns288p1424 

noncomputable def Ns288p1426 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 615476 1000 112 158 134217728 67108864 2251799813685248 Bool.false 148001889639 1886 

noncomputable def Ns288p1427 := Ns288p1426 279097919 34 47453128 8 294906479 34 44739240 8 Bool.true 44283874 71328 Bool.true 163365172 Bool.true 195033596 7074237752028440 1 Bool.false 46480451 Bool.false Bool.false 15758684 Bool.true Bool.true 33103449 

noncomputable def Ns288p1428 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 615476 1000 0 60 134217728 67108864 2251799813685248 Bool.false 148001889639 1886 

noncomputable def Ns288p1429 := Ns288p1428 240485871 35 54794152 8 261175631 35 50729528 8 Bool.true 137247056 52889 Bool.true 11392300 Bool.true 95720178 7074237752028440 1 Bool.false 133734533 Bool.false Bool.false 101507682 Bool.false Bool.true 44283874 

noncomputable def Ns288p1430 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 615476 1000 158 71 134217728 67108864 2251799813685248 Bool.false 148001889639 1886 

noncomputable def Ns288p1431 := Ns288p1430 186065264 34 67108856 8 216015088 34 60023992 8 Bool.true 152267651 31261 Bool.false 172248380 Bool.false 80948633 7074237752028440 1 Bool.false 38051240 Bool.true Bool.false 76129648 Bool.false Bool.true 137247056 

noncomputable def Ns288p1432 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 615476 1000 430 271 134217728 67108864 2251799813685248 Bool.false 148001889639 1886 

noncomputable def Ns288p1433 := Ns288p1432 93032624 34 94906264 8 147453232 34 77490640 16 Bool.true 134217656 1930 Bool.false 86195272 Bool.false 113382690 7074237752028440 1 Bool.false 107478483 Bool.true Bool.false 100370212 Bool.false Bool.true 152267651 

noncomputable def Ns288p1434 := nat_lit 1158503494345200749909320965677535304792887182642701 

noncomputable def Ns288p1435 := nat_lit 1050606227187316692106206975869742145477804032000 

noncomputable def Ns288p1436 := nat_lit 42393334375984504764472389140480000 

noncomputable def Ns288p1437 := nat_lit 156552527425783379689783897380492410880 

noncomputable abbrev qz766 := (@Eq.refl Real (Enclosure.sfrac Bool.false 615476 1000))

noncomputable abbrev qz694 := qz766

noncomputable abbrev qz535 := qz694

noncomputable abbrev qz243 := qz535

noncomputable def Ns288p1438 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz240 615476 1000 1515243826304 16000000 1230952 4000 2000 Ns288p1436 Ns288p1437 qz243 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns288p1439 := nat_lit 12147789600865132215369161409062872597585064704267528437760 

noncomputable abbrev qz695 := (@HSub.hSub Real Real Real qz712 qz713 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz714 (@Nat.cast Real Real.instNatCast 1230952))))

noncomputable abbrev qz536 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz580 (Enclosure.sfrac Bool.false 615476 4000) (Real.log (Enclosure.sfrac Bool.false 1515243826304 16000000))) (@HMul.hMul Real Real Real qz580 qz585 qz695))

noncomputable abbrev qz696 := (Enclosure.sfrac Bool.false 615476 2000)

noncomputable abbrev qz244 := (@HSub.hSub Real Real Real qz352 (@HSub.hSub Real Real Real qz352 qz536 qz696) (@HMul.hMul Real Real Real qz346 qz696 (Real.log Real.pi)))

noncomputable def Ns288p1440 := @Enclosure.Real.IsNear.addLit_ft_p qz244 (Enclosure.sfrac Bool.true Ns288p1436 Ns288p1437) 77595633770842310077 70368744177664000 7189614489074473 512000000000000000000 Ns288p1436 Ns288p1437 0 1 Ns288p1439 

noncomputable def Ns288p1441 := nat_lit 1301838708430315938100805632000 

noncomputable abbrev qz245 := (@HSub.hSub Real Real Real qz352 qz536 qz696)

noncomputable def Ns288p1442 := @Enclosure.Real.IsNear.subLit_ff_p qz245 (@HMul.hMul Real Real Real qz5 qz696 (Real.log Real.pi)) 102384915741151086013 70368744177664000 4870908712029 1000000000000000000 5910225384309 16777216000 153869 16777216000 Ns288p1441 77595633770842310077 70368744177664000 

noncomputable abbrev qz246 := qz536

noncomputable def Ns288p1443 := @Enclosure.Real.IsNear.subLit_ff_p qz246 qz696 24808010467379410009 14073748835532800 4870908712029 1000000000000000000 615476 2000 0 1 40953966296460434405200 102384915741151086013 70368744177664000 4870908712029 1000000000000000000 

noncomputable def Ns288p1444 := nat_lit 223450693393386550460269337067388928 

noncomputable def Ns288p1445 := nat_lit 27704948641810715236106240 

noncomputable def Ns288p1446 := nat_lit 127555594224698098667565172151380056077138850872967730892486212401994673238409492545678242277215340984005056066959598580945387520 

noncomputable def Ns288p1447 := nat_lit 1437385147147709748431848995188575409576837064188220206144490700685676022385016629013118552437970381999761497173598490071138304 

noncomputable def Ns288p1448 := nat_lit 462924759938076090358779303750112608794049149976846280612359590931672949567900386782992852345909001625985713858485944320 

noncomputable def Ns288p1449 := BSN.log_dyadic_bound 466667826304 2563819826304 6 5 Ns288p1446 67108864 32000000 Ns288p1447 Ns288p1448 24705679 3030487652608 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 466667826304) (BSN.artanhQ 2563819826304) 0 5 Ns288p1447 Ns288p1446 Ns288p1448 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz537 := (Real.log (Enclosure.sfrac Bool.false 1515243826304 16000000))

noncomputable def Ns288p1450 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 615476 4000) qz537 615476 4000 0 1 3225280512335095 281474976710656 976563 31250000000000 99254137430497746511 56294995342131200 150262772247 31250000000000000 (Enclosure.Real.IsNear.const Bool.false 615476 4000) (BSN.isNear_log_sfrac 1515243826304 16000000 3225280512335095 281474976710656 976563 31250000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1515243826304) qz355)) Bool.false Ns288p1445 Ns288p93 1000000512000000 32000000000000000000000 3225280512335095 281474976710656 976563 31250000000000 (BSN.log_rat_reduce_isNear 1515243826304 16000000 16 3030487652608 2097152000000 24705679 67108864 24973259072661432 36028797018963968 32000000 1000000000000000 rfl rfl rfl rfl (Ns288p1449 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns288p1451 := BSN.arctan_dyadic_bound_f 1000 1230952 1 0 8388608 4000000 0 1 1 0 1 1 6814 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1230952) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1230952) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns288p1452 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1230952))) 884279719003555 562949953421312 1 2000000000000000 6814 8388608 1 4000000 7414039984088360681472 883822439204259 562949953421312 500000001 2000000000000000 qz15 (Ns288p1451 rfl) rfl rfl 

noncomputable abbrev qz538 := (@HMul.hMul Real Real Real qz580 qz585 qz695)

noncomputable abbrev qz247 := qz538

noncomputable abbrev qz539 := qz695

noncomputable abbrev qz248 := qz539

noncomputable def Ns288p1453 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 615476 4000) qz537) qz247 99254137430497746511 56294995342131200 150262772247 31250000000000000 883822439204259 2251799813685248 500000001 8000000000000000 Ns288p1444 24808010467379410009 14073748835532800 4870908712029 1000000000000000000 (Ns288p1450 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz248 1 4 0 1 883822439204259 562949953421312 500000001 2000000000000000 883822439204259 2251799813685248 500000001 8000000000000000 qz363 Ns288p1452 rfl) 

noncomputable def Ns288p1454 := @Ns288p1440 Ns288p1434 Ns288p1435 7189614489074473 512000000000000000000 (@Ns288p1442 7189614489074473 512000000000000000000 (Ns288p1443 (Ns288p1453 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 615476 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz696 (Real.log Real.pi) 615476 2000 0 1 38410761 33554432 1 33554432 5910225384309 16777216000 153869 16777216000 (Enclosure.Real.IsNear.const Bool.false 615476 2000) RS289to300.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns288p1436 Ns288p1437) 

noncomputable def Ns288p1455 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns288p1434 Ns288p1435 7189614489074473 512000000000000000000 4625059051 4194304 237 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz364 qz244 (Enclosure.sfrac Bool.true Ns288p1436 Ns288p1437)) Bool.false Ns288p1434 Ns288p1435 7189614489074473 512000000000000000000 Ns288p1438 (Ns288p1454 rfl rfl)) 

noncomputable def Ns288p1456 := BSN.cos_dyadic_bound_f 33871494 34359738368 1 0 16777216 8007813 0 1 1 0 1 1 16777207 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 33871494) (BSN.cosEvenQ 34359738368) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 33871494) (BSN.cosOddQ 34359738368) 0 0 rfl) rfl rfl 

noncomputable def Ns288p1457 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz240) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4625059051) qz413) Bool.false 4625059051 4194304 237 16777216 Bool.true 16777207 16777216 1 4000000 (Ns288p1455 rfl) (Enclosure.sfrac_false_div 4625059051 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4625059051) qz413) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 595873627080419704832) qz414) 226375608064910080 72057594037927936 Bool.false 16777207 16777216 175 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q2 4625059051 4194304 226375608064910080 72057594037927936 175 595873627080419704832 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777207 16777216 595873627080419704832 604462909807314587353088 33871494 34359738368 8007813 8000000 (Ns288p1456 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p1458 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns288p1434 Ns288p1435 7189614489074473 512000000000000000000 148001889639 134217728 1886 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz364 qz244 (Enclosure.sfrac Bool.true Ns288p1436 Ns288p1437)) Bool.false Ns288p1434 Ns288p1435 7189614489074473 512000000000000000000 Ns288p1438 (Ns288p1454 rfl rfl)) 

noncomputable def Ns288p1459 := Ns288p1433 31261 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 430 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 107478483 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 271 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 100370212 134217728) qz243 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) Bool.true 16777207 16777216 3768661 262144000000 134217656 134217728 1930 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 16777207 16777216 3768661 262144000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz240) qz240) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 16777207 16777216 964777216 67108864000000 16777207 16777216 3768661 262144000000 (Ns288p1457 rfl rfl) rfl)) rfl) (Ns288p1458 rfl) RS289to300.d7 

noncomputable def Ns288p1460 := nat_lit 30097232305957475657844990356245147935958573045281930453799734870016 

noncomputable def Ns288p1461 := nat_lit 3046965632792167642494216819443707730112363818462480441892929536 

noncomputable def Ns288p1462 := nat_lit 90285602986606842638249982635096556392415494408208866400515418750976 

noncomputable def Ns288p1463 := BSN.cos_dyadic_bound_f 86195272 134217728 3 2 134217728 67108864 Ns288p1460 Ns288p123 Ns288p1461 Ns288p1462 Ns288p126 Ns288p1461 107478483 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 86195272) qz369 0 2 Ns288p1460 Ns288p123 Ns288p1461 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 86195272) qz370 0 2 Ns288p1462 Ns288p126 Ns288p1461 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1464 := nat_lit 162211439052286888067562577376100001471696016098642278915018222240000 

noncomputable def Ns288p1465 := nat_lit 27313292220096701691200231459629428327699652798767954704100000000 

noncomputable def Ns288p1466 := nat_lit 424795261711442645517068616562660603827625671296674629993622039200000 

noncomputable def Ns288p1467 := BSN.sin_dyadic_bound_f 113382690 134217728 3 2 134217728 67108864 Ns288p1464 Ns288p109 Ns288p1465 Ns288p1466 Ns288p112 Ns288p1465 100370212 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 113382690) qz367 0 2 Ns288p1464 Ns288p109 Ns288p1465 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 113382690) qz368 0 2 Ns288p1466 Ns288p112 Ns288p1465 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1468 := nat_lit 1853216623606194981663790515532754965246221101278141943103958041625762734532288374516371928090148864000000 

noncomputable def Ns288p1469 := nat_lit 682121522272824997461773848898464077144671291449422183146508122485914423355682870726656000000000000 

noncomputable def Ns288p1470 := nat_lit 11230761582408497519828875580857841860415986309971732527787905768340937506367720815278706640895711641600000 

noncomputable def Ns288p1471 := BSN.cos_dyadic_bound_f 172248380 134217728 4 3 134217728 67108864 Ns288p1468 Ns288p137 Ns288p1469 Ns288p1470 Ns288p140 Ns288p1469 38051240 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 172248380) qz369 0 3 Ns288p1468 Ns288p137 Ns288p1469 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 172248380) qz370 0 3 Ns288p1470 Ns288p140 Ns288p1469 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1472 := nat_lit 42138434470953865201323213143810618652711927959538508143895878089665 

noncomputable def Ns288p1473 := nat_lit 1843640130696403636496910899139619933618773823618449774819195841 

noncomputable def Ns288p1474 := nat_lit 110359581530381852778530277520905394229591095212600710505806163917761 

noncomputable def Ns288p1475 := BSN.sin_dyadic_bound_f 80948633 134217728 3 2 134217728 67108864 Ns288p1472 Ns288p109 Ns288p1473 Ns288p1474 Ns288p112 Ns288p1473 76129648 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 80948633) qz367 0 2 Ns288p1472 Ns288p109 Ns288p1473 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 80948633) qz368 0 2 Ns288p1474 Ns288p112 Ns288p1473 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1476 := Ns288p1431 52889 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 158 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 38051240 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 71 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 76129648 134217728) qz243 rfl rfl (Ns288p1459 RS289to300.d9 RS289to300.d11 RS289to300.d13 RS289to300.d17 (Ns288p1463 rfl rfl) (Ns288p1467 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns288p1458 rfl) RS289to300.d19 RS289to300.d21 RS289to300.d23 RS289to300.d25 RS289to300.d17 (Ns288p1471 rfl rfl) (Ns288p1475 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns288p1477 := nat_lit 16844016255956010504100000000 

noncomputable def Ns288p1478 := BSN.cos_dyadic_bound_f 11392300 134217728 2 1 134217728 67108864 Ns288p1477 Ns288p132 Ns288p1477 Ns288p1477 Ns288p133 Ns288p1477 133734533 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 11392300) qz369 0 1 Ns288p1477 Ns288p132 Ns288p1477 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 11392300) qz370 0 1 Ns288p1477 Ns288p133 Ns288p1477 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1479 := nat_lit 45775138951516764382665644973765140105460762508247557059269923881216 

noncomputable def Ns288p1480 := nat_lit 7047384718744891738174893669142788722136726483449156031800852736 

noncomputable def Ns288p1481 := nat_lit 137311322085112803364520585133957134738938014071775772865746169938176 

noncomputable def Ns288p1482 := BSN.cos_dyadic_bound_f 95720178 134217728 3 2 134217728 67108864 Ns288p1479 Ns288p123 Ns288p1480 Ns288p1481 Ns288p126 Ns288p1480 101507682 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 95720178) qz369 0 2 Ns288p1479 Ns288p123 Ns288p1480 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 95720178) qz370 0 2 Ns288p1481 Ns288p126 Ns288p1480 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1483 := Ns288p1429 71328 BSN.abs_quadSignPos (BSN.cos_quad_nat0 0 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133734533 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 101507682 134217728) qz243 rfl rfl (Ns288p1476 rfl rfl) (Ns288p1458 rfl) RS289to300.d27 RS289to300.d29 RS289to300.d31 RS289to300.d33 RS289to300.d17 (Ns288p1478 rfl rfl) (Ns288p1482 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p1484 := nat_lit 1499028178578593251614093517998491233600441845034610267799578144545122851543400681079577078786524337668096 

noncomputable def Ns288p1485 := nat_lit 361338046393389168268847477666503180409835470984004636537654797610875368246033365681827597428719616 

noncomputable def Ns288p1486 := nat_lit 9086192194729869130508106053603877281477955599932177575198614112969486067733856314116973324915161232834560 

noncomputable def Ns288p1487 := BSN.cos_dyadic_bound_f 163365172 134217728 4 3 134217728 67108864 Ns288p1484 Ns288p137 Ns288p1485 Ns288p1486 Ns288p140 Ns288p1485 46480451 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 163365172) qz369 0 3 Ns288p1484 Ns288p137 Ns288p1485 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 163365172) qz370 0 3 Ns288p1486 Ns288p140 Ns288p1485 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1488 := nat_lit 3049256717855787171231685510383397967623190445673227287400597766512553612354772606990624808244279452368896 

noncomputable def Ns288p1489 := nat_lit 3029096711327744613614229623787955796533433156489245088997153500586429386050066329940073903256764416 

noncomputable def Ns288p1490 := nat_lit 18466165725278508925236899013259335004577350020653719938664087500504363527694640219962134367534978338652160 

noncomputable def Ns288p1491 := BSN.cos_dyadic_bound_f 195033596 134217728 4 3 134217728 67108864 Ns288p1488 Ns288p137 Ns288p1489 Ns288p1490 Ns288p140 Ns288p1489 15758684 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 195033596) qz369 0 3 Ns288p1488 Ns288p137 Ns288p1489 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 195033596) qz370 0 3 Ns288p1490 Ns288p140 Ns288p1489 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1492 := Ns288p1427 87017 BSN.abs_quadSignPos (BSN.cos_quad_nat0 112 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 46480451 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 158 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 15758684 134217728) qz243 rfl rfl (Ns288p1483 rfl) (Ns288p1458 rfl) RS289to300.d35 RS289to300.d37 RS289to300.d39 RS289to300.d41 RS289to300.d17 (Ns288p1487 rfl rfl) (Ns288p1491 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns288p1493 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) 33103449 134217728 87017 134217728 33103449 134217728 87017 134217728 8886139427487744 33103449 67108864 87017 67108864 (Ns288p1492 rfl) 

noncomputable def Ns288p1494 := @Enclosure.Real.IsNear.mulLit_tf qz693 (Zeta.RiemannSiegel.correction qz242) 5332883 16777216 1 16777216 49663261058411 70368744177664 60268424333299 1099511627776000000 264848360622962028913 1180591620717411303424 

noncomputable abbrev qz697 := (@HPow.hPow Real Real Real qz205 qz241 qz207)

noncomputable def Ns288p1495 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz697 1 1 0 1 5332883 16777216 1 16777216 5332883 16777216 1 16777216 

noncomputable def Ns288p1496 := @Enclosure.Real.IsNear.sqrt_image qz241 410857464813 4194304000 153869 4194304000 83024344 83024377 8388608 (@Enclosure.Real.IsNear.of_eq qz241 (@HMul.hMul Real Real Real qz5 qz240 qz3) Bool.false 410857464813 4194304000 153869 4194304000 (BSN.t_div_two_pi_mk qz240 615476 1000 qz243) (@Enclosure.Real.IsNear.mulLit_ff qz240 qz3 615476 1000 0 1 2670177 16777216 1 16777216 410857464813 4194304000 153869 4194304000 (Enclosure.Real.IsNear.const Bool.false 615476 1000) RS289to300.d44 rfl)) 

noncomputable abbrev qz767 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 615476 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz698 := qz767

noncomputable abbrev qz540 := qz698

noncomputable abbrev qz249 := qz540

noncomputable def Ns288p1497 := @Enclosure.Real.IsNear.sqrt_image qz249 166048721 16777216 33 16777216 26390503 26390509 8388608 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 166048721 16777216 33 16777216 166048721 16777216 33 16777216 (Ns288p1496 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns288p1498 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz249) 13195253 4194304 3 8388608 2666441 2666442 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz249) Bool.false 52781012 16777216 6 16777216 13195253 4194304 3 8388608 (Ns288p1497 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns288p1499 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 5332883 16777216 1 16777216 5332883 16777216 1 16777216 (Ns288p1498 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz534))

noncomputable abbrev qz699 := (@HMul.hMul Real Real Real qz708 qz765 qz765)

noncomputable abbrev qz541 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz699 qz692) qz594)

noncomputable abbrev qz251 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz541))

noncomputable def Ns288p1500 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz242) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz250) qz251) Bool.false 49663261058411 

noncomputable def Ns288p1501 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz250) qz251 10501051 8388608 167 

noncomputable def Ns288p1502 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz250) Bool.false 21002102 16777216 334 16777216 10501051 8388608 167 

noncomputable def Ns288p1503 := @Enclosure.Real.IsNear.recentre' qz250 Bool.false 13402229 16777216 53048576 4194304000000 13402229 16777216 207221 16384000000 

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz346 qz343 qz534)

noncomputable def Ns288p1504 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47292835) qz393) Bool.false 47292835 8388608 13 1048576 Bool.false 13402229 16777216 1 

noncomputable def Ns288p1505 := nat_lit 178108097725552891962625979 

noncomputable def Ns288p1506 := nat_lit 14411518807585587200000000000000 

noncomputable def Ns288p1507 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz242 884279719003555 140737488355328 1 500000000000000 15053777 16777216 33 16777216 13311749695502179177235 2361183241434822606848 Ns288p1505 

noncomputable def Ns288p1508 := @Enclosure.Real.IsNear.subLit_ff_p qz249 qz1 166048721 16777216 33 16777216 9 1 0 1 15053777 15053777 16777216 33 

noncomputable def Ns288p1509 := @Ns288p1508 16777216 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 166048721 16777216 33 16777216 166048721 16777216 33 16777216 (Ns288p1496 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns288p1510 := @Enclosure.Real.IsNear.recentre' qz252 Bool.false 13311749695502179177235 2361183241434822606848 Ns288p1505 Ns288p1506 47292835 8388608 13 1048576 (@Ns288p1507 Ns288p1506 RS289to300.d43 (Ns288p1509 rfl rfl) rfl) 

noncomputable def Ns288p1511 := nat_lit 4308457076780386526864803958633866341903826720008784015431120291879616058808882194930625 

noncomputable def Ns288p1512 := nat_lit 1044408992070044728377256983721374865116409602345589900399935353905905574064187890625 

noncomputable def Ns288p1513 := nat_lit 11282363300818613212228542427972196288537929127333493847242762773873622973570016111090625 

noncomputable def Ns288p1514 := BSN.sin_dyadic_bound_f 31794999705 34359738368 3 2 16777216 8007813 Ns288p1511 Ns288p1078 Ns288p1512 Ns288p1513 Ns288p1081 Ns288p1512 13402229 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 31794999705) qz376 0 2 Ns288p1511 Ns288p1078 Ns288p1512 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 31794999705) qz377 0 2 Ns288p1513 Ns288p1081 Ns288p1512 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1515 := @Ns288p1504 4000000 (Ns288p1510 rfl) (Enclosure.sfrac_false_div 47292835 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47292835) qz393) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1118687100210911589171200) qz394) 226375608064910080 72057594037927936 Bool.false 13402229 16777216 0 1000000000000000 8000000 4000000 (BSN.sin_reduce_arg_pos_rat_q3 47292835 8388608 226375608064910080 72057594037927936 0 1118687100210911589171200 Ns288p284 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 13402229 16777216 1118687100210911589171200 Ns288p284 31794999705 34359738368 8007813 8000000 (Ns288p1514 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns288p1516 := @Enclosure.Real.IsNear.inv_image qz250 13402229 16777216 207221 16384000000 10500884 10501218 8388608 (Ns288p1503 (Ns288p1515 rfl rfl) rfl) rfl 

noncomputable def Ns288p1517 := @Enclosure.Real.IsNear.recentre' qz251 Bool.false 4729361 8388608 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz346 qz343 qz541)

noncomputable def Ns288p1518 := @Enclosure.Real.IsNear.cos_image qz253 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16304707)) qz365) Bool.true 16304707 16777216 

noncomputable def Ns288p1519 := nat_lit 38498401915481022399526610045 

noncomputable def Ns288p1520 := nat_lit 41752815367147733431810945626249781 

noncomputable def Ns288p1521 := @Enclosure.Real.IsNear.recentre' qz253 Bool.true Ns288p1519 Ns288p436 Ns288p1520 

noncomputable def Ns288p1522 := nat_lit 1208925819614629174706176000000000000000 

noncomputable abbrev qz254 := qz541

noncomputable def Ns288p1523 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz254 884279719003555 140737488355328 1 500000000000000 43536452423519 

noncomputable abbrev qz542 := (@HSub.hSub Real Real Real qz584 qz699 qz692)

noncomputable abbrev qz255 := qz542

noncomputable def Ns288p1524 := @Enclosure.Real.IsNear.subLit_tf qz255 qz29 25944266379103 281474976710656 1547198499 281474976710656 1 16 

noncomputable abbrev qz543 := qz699

noncomputable abbrev qz256 := qz543

noncomputable def Ns288p1525 := @Enclosure.Real.IsNear.subLit_ff_n qz256 qz242 226616201965729 281474976710656 993550371 281474976710656 15053777 16777216 33 16777216 

noncomputable def Ns288p1526 := @Enclosure.Real.IsNear.mulLit_ff qz242 qz242 15053777 16777216 33 16777216 15053777 16777216 33 16777216 226616201965729 281474976710656 

noncomputable def Ns288p1527 := nat_lit 9411771900487602045250662423579020248164358642823472306610081 

noncomputable def Ns288p1528 := nat_lit 4994637695863610568450256880212614190709668799999093661601 

noncomputable def Ns288p1529 := nat_lit 28225326426071078914615086756976635516111656590870418732507041 

noncomputable def Ns288p1530 := BSN.cos_dyadic_bound_f 16304707 16777216 3 2 8388608 4000000 Ns288p1527 Ns288p767 Ns288p1528 Ns288p1529 Ns288p770 Ns288p1528 4729361 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 16304707) qz595 0 2 Ns288p1527 Ns288p767 Ns288p1528 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 16304707) (BSN.cosOddQ 16777216) 0 2 Ns288p1529 Ns288p770 Ns288p1528 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns288p1531 := @Ns288p1517 584194304 16777216000000 4729361 8388608 2282009 65536000000 (@Ns288p1518 145 4194304 Bool.false 4729361 8388608 1 4000000 (@Ns288p1521 Ns288p1522 16304707 16777216 145 4194304 (@Ns288p1523 281474976710656 1547198499 281474976710656 Ns288p1519 Ns288p436 Ns288p1520 Ns288p1522 RS289to300.d43 (@Ns288p1524 0 1 696583238776304 43536452423519 281474976710656 1547198499 281474976710656 (@Ns288p1525 435272561003748917248 25944266379103 281474976710656 1547198499 281474976710656 (@Ns288p1526 993550371 281474976710656 (Ns288p1509 rfl rfl) (Ns288p1509 rfl rfl) rfl) (Ns288p1509 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16304707 16777216) (BSN.cos_neg_of_bound 16304707 16777216 Bool.false 4729361 8388608 1 4000000 (Ns288p1530 rfl rfl)) rfl rfl) 

noncomputable def Ns288p1532 := @Ns288p1494 322180504286298576191 Ns288p451 (Ns288p1495 qz31 (@Enclosure.Real.IsNear.of_eq qz697 (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 5332883 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz241 (BSN.t_div_two_pi_nonneg qz240 615476 1000 qz243)) Ns288p1499) rfl) (@Ns288p1500 70368744177664 60268424333299 1099511627776000000 (BSN.correction_mk qz242 (BSN.cos_two_pi_p_ne_zero_mk qz240 615476 1000 9 qz243 rfl rfl (@BSN.floor_sqrt_eq_dec qz240 615476 1000 9 qz243 rfl rfl rfl))) (@Ns288p1501 8388608 4729361 8388608 2282009 65536000000 49663261058411 70368744177664 60268424333299 1099511627776000000 (@Ns288p1502 8388608 (Ns288p1516 rfl rfl rfl rfl rfl) rfl) (Ns288p1531 rfl) rfl)) 

noncomputable def Ns288p1533 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (hardyZApproximantRS₀ qz240) Bool.true 317513672896874761871 1180591620717411303424 24241231332832346576191 Ns288p451 (@Eq.refl Real (hardyZApproximantRS₀ qz240)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (@HMul.hMul Real Real Real qz5 qz693 (Zeta.RiemannSiegel.correction qz242))) Bool.true 317513672896874761871 1180591620717411303424 24241231332832346576191 Ns288p451 (BSN.hardyZApproximantRS₀_eq qz240 9 (@BSN.floor_sqrt_eq_dec qz240 615476 1000 9 qz243 rfl rfl rfl)) (@Ns288p1425 317513672896874761871 1180591620717411303424 24241231332832346576191 Ns288p451 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 9)) Bool.true 33103449 67108864 87017 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (Ns288p1493 (Ns288p1492 rfl) rfl rfl)) (Ns288p1532 rfl) rfl rfl)) 

theorem RS289to300.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz240) Bool.true 317513672896874761871 1180591620717411303424 24241231332832346576191 Ns288p451 := Ns288p1533 

noncomputable def RS289to300.d60 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz544 := (RS289to300.d3 qz581 qz596 (@Enclosure.dec_le_dec qz581 qz596 598981 1000 600359 1000 (@Eq.refl Real qz581) qz599 rfl rfl rfl))

noncomputable abbrev qz257 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz544)

noncomputable def Ns288p1534 := @Enclosure.Real.IsNear.of_eq qz257 (hardyZApproximantRS₀ qz4) Bool.true 122444020612295599145 73786976294838206464 2580432727312133951443 Ns288p69 

noncomputable abbrev qz545 := (@Enclosure.dec_le_dec qz581 qz596 598981 1000 600359 1000 (@Eq.refl Real qz581) qz599 rfl rfl rfl)

noncomputable abbrev qz258 := qz545

noncomputable def Ns288p1535 := @Enclosure.Real.IsNear.neg_val qz257 122444020612295599145 73786976294838206464 2580432727312133951443 Ns288p69 (Ns288p1534 (RS289to300.d4 qz4 qz33 qz258) RS289to300.d45) rfl 

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz544)

noncomputable def Ns288p1536 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantRS₀ qz33) Bool.false 588322631145363898289 147573952589676412928 12371267729980249887499 Ns288p193 

noncomputable def Ns288p1537 := @Enclosure.Real.IsNear.pos_val qz259 588322631145363898289 147573952589676412928 12371267729980249887499 Ns288p193 (Ns288p1536 (RS289to300.d46 qz4 qz33 qz258) RS289to300.d47) rfl 

noncomputable def Ns288p1538 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz257 qz4 qz4 598981 1000 598981 1000 

noncomputable def Ns288p1539 := @Enclosure.norm_gt_of_isNear qz257 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 122444020612295599145 73786976294838206464 2580432727312133951443 

noncomputable def Ns288p1540 := @Ns288p1539 Ns288p69 34141065 536870912 1213 2684354560 (Ns288p1534 (RS289to300.d4 qz4 qz33 qz258) RS289to300.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable def Ns288p1541 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz259 qz4 qz33 598981 1000 600359 1000 

noncomputable def Ns288p1542 := @Enclosure.norm_gt_of_isNear qz259 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 588322631145363898289 147573952589676412928 12371267729980249887499 

noncomputable def Ns288p1543 := @Ns288p1542 Ns288p193 34141065 536870912 1213 2684354560 (Ns288p1536 (RS289to300.d46 qz4 qz33 qz258) RS289to300.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable abbrev qz260 := qz544

noncomputable def Ns288p1544 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz260 (@BSN.thirtyTwoPi_le_dec qz4 598981 1000 qz9 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz257 qz259 (Ns288p1535 rfl rfl) (Ns288p1537 rfl rfl)) (Ns288p1538 qz9 qz9 rfl rfl rfl rfl (Ns288p1540 rfl)) (Ns288p1541 qz9 qz36 rfl rfl rfl rfl (Ns288p1543 rfl)) 

noncomputable abbrev qz546 := (RS289to300.d3 qz596 qz606 (@Enclosure.dec_le_dec qz596 qz606 600359 1000 601737 1000 qz599 qz609 rfl rfl rfl))

noncomputable abbrev qz261 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz546)

noncomputable def Ns288p1545 := @Enclosure.Real.IsNear.of_eq qz261 (hardyZApproximantRS₀ qz33) Bool.false 588322631145363898289 147573952589676412928 12371267729980249887499 Ns288p193 

noncomputable abbrev qz547 := (@Enclosure.dec_le_dec qz596 qz606 600359 1000 601737 1000 qz599 qz609 rfl rfl rfl)

noncomputable abbrev qz262 := qz547

noncomputable def Ns288p1546 := @Enclosure.Real.IsNear.pos_val qz261 588322631145363898289 147573952589676412928 12371267729980249887499 Ns288p193 (Ns288p1545 (RS289to300.d4 qz33 qz60 qz262) RS289to300.d47) rfl 

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz546)

noncomputable def Ns288p1547 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantRS₀ qz60) Bool.true 7566909229950063229 18446744073709551616 6085572931451032339849 Ns288p340 

noncomputable def Ns288p1548 := @Enclosure.Real.IsNear.neg_val qz263 7566909229950063229 18446744073709551616 6085572931451032339849 Ns288p340 (Ns288p1547 (RS289to300.d46 qz33 qz60 qz262) RS289to300.d49) rfl 

noncomputable def Ns288p1549 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz261 qz4 qz33 598981 1000 600359 1000 

noncomputable def Ns288p1550 := @Enclosure.norm_gt_of_isNear qz261 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 588322631145363898289 147573952589676412928 12371267729980249887499 

noncomputable def Ns288p1551 := @Ns288p1550 Ns288p193 34141065 536870912 1213 2684354560 (Ns288p1545 (RS289to300.d4 qz33 qz60 qz262) RS289to300.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable def Ns288p1552 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz263 qz4 qz60 598981 1000 601737 1000 

noncomputable def Ns288p1553 := @Enclosure.norm_gt_of_isNear qz263 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 7566909229950063229 18446744073709551616 6085572931451032339849 

noncomputable def Ns288p1554 := @Ns288p1553 Ns288p340 34141065 536870912 1213 2684354560 (Ns288p1547 (RS289to300.d46 qz33 qz60 qz262) RS289to300.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable abbrev qz264 := qz546

noncomputable def Ns288p1555 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz264 (@BSN.thirtyTwoPi_le_dec qz33 600359 1000 qz36 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz261 qz263 (Ns288p1546 rfl rfl) (Ns288p1548 rfl rfl)) (Ns288p1549 qz9 qz36 rfl rfl rfl rfl (Ns288p1551 rfl)) (Ns288p1552 qz9 qz63 rfl rfl rfl rfl (Ns288p1554 rfl)) 

noncomputable abbrev qz548 := (RS289to300.d3 qz606 qz614 (@Enclosure.dec_le_dec qz606 qz614 601737 1000 603114 1000 qz609 qz617 rfl rfl rfl))

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz548)

noncomputable def Ns288p1556 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantRS₀ qz60) Bool.true 7566909229950063229 18446744073709551616 6085572931451032339849 Ns288p340 

noncomputable abbrev qz549 := (@Enclosure.dec_le_dec qz606 qz614 601737 1000 603114 1000 qz609 qz617 rfl rfl rfl)

noncomputable abbrev qz266 := qz549

noncomputable def Ns288p1557 := @Enclosure.Real.IsNear.neg_val qz265 7566909229950063229 18446744073709551616 6085572931451032339849 Ns288p340 (Ns288p1556 (RS289to300.d4 qz60 qz78 qz266) RS289to300.d49) rfl 

noncomputable abbrev qz267 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz548)

noncomputable def Ns288p1558 := @Enclosure.Real.IsNear.of_eq qz267 (hardyZApproximantRS₀ qz78) Bool.false 800693892488054201603 1180591620717411303424 24206053427349890728741 Ns288p451 

noncomputable def Ns288p1559 := @Enclosure.Real.IsNear.pos_val qz267 800693892488054201603 1180591620717411303424 24206053427349890728741 Ns288p451 (Ns288p1558 (RS289to300.d46 qz60 qz78 qz266) RS289to300.d50) rfl 

noncomputable def Ns288p1560 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz265 qz4 qz60 598981 1000 601737 1000 

noncomputable def Ns288p1561 := @Enclosure.norm_gt_of_isNear qz265 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 7566909229950063229 18446744073709551616 6085572931451032339849 

noncomputable def Ns288p1562 := @Ns288p1561 Ns288p340 34141065 536870912 1213 2684354560 (Ns288p1556 (RS289to300.d4 qz60 qz78 qz266) RS289to300.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable def Ns288p1563 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz267 qz4 qz78 598981 1000 603114 1000 

noncomputable def Ns288p1564 := @Enclosure.norm_gt_of_isNear qz267 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 800693892488054201603 1180591620717411303424 24206053427349890728741 

noncomputable def Ns288p1565 := @Ns288p1564 Ns288p451 34141065 536870912 1213 2684354560 (Ns288p1558 (RS289to300.d46 qz60 qz78 qz266) RS289to300.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable abbrev qz268 := qz548

noncomputable def Ns288p1566 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz60 601737 1000 qz63 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz265 qz267 (Ns288p1557 rfl rfl) (Ns288p1559 rfl rfl)) (Ns288p1560 qz9 qz63 rfl rfl rfl rfl (Ns288p1562 rfl)) (Ns288p1563 qz9 qz81 rfl rfl rfl rfl (Ns288p1565 rfl)) 

noncomputable abbrev qz550 := (RS289to300.d3 qz614 qz622 (@Enclosure.dec_le_dec qz614 qz622 603114 1000 604490 1000 qz617 qz625 rfl rfl rfl))

noncomputable abbrev qz269 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz550)

noncomputable def Ns288p1567 := @Enclosure.Real.IsNear.of_eq qz269 (hardyZApproximantRS₀ qz78) Bool.false 800693892488054201603 1180591620717411303424 24206053427349890728741 Ns288p451 

noncomputable abbrev qz551 := (@Enclosure.dec_le_dec qz614 qz622 603114 1000 604490 1000 qz617 qz625 rfl rfl rfl)

noncomputable abbrev qz270 := qz551

noncomputable def Ns288p1568 := @Enclosure.Real.IsNear.pos_val qz269 800693892488054201603 1180591620717411303424 24206053427349890728741 Ns288p451 (Ns288p1567 (RS289to300.d4 qz78 qz96 qz270) RS289to300.d50) rfl 

noncomputable abbrev qz271 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz550)

noncomputable def Ns288p1569 := @Enclosure.Real.IsNear.of_eq qz271 (hardyZApproximantRS₀ qz96) Bool.true 461395591794983839587 1180591620717411303424 24124602304846179935819 Ns288p451 

noncomputable def Ns288p1570 := @Enclosure.Real.IsNear.neg_val qz271 461395591794983839587 1180591620717411303424 24124602304846179935819 Ns288p451 (Ns288p1569 (RS289to300.d46 qz78 qz96 qz270) RS289to300.d51) rfl 

noncomputable def Ns288p1571 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz269 qz4 qz78 598981 1000 603114 1000 

noncomputable def Ns288p1572 := @Enclosure.norm_gt_of_isNear qz269 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 800693892488054201603 1180591620717411303424 24206053427349890728741 

noncomputable def Ns288p1573 := @Ns288p1572 Ns288p451 34141065 536870912 1213 2684354560 (Ns288p1567 (RS289to300.d4 qz78 qz96 qz270) RS289to300.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable def Ns288p1574 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz271 qz4 qz96 598981 1000 604490 1000 

noncomputable def Ns288p1575 := @Enclosure.norm_gt_of_isNear qz271 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 461395591794983839587 1180591620717411303424 24124602304846179935819 

noncomputable def Ns288p1576 := @Ns288p1575 Ns288p451 34141065 536870912 1213 2684354560 (Ns288p1569 (RS289to300.d46 qz78 qz96 qz270) RS289to300.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable abbrev qz272 := qz550

noncomputable def Ns288p1577 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz78 603114 1000 qz81 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz269 qz271 (Ns288p1568 rfl rfl) (Ns288p1570 rfl rfl)) (Ns288p1571 qz9 qz81 rfl rfl rfl rfl (Ns288p1573 rfl)) (Ns288p1574 qz9 qz99 rfl rfl rfl rfl (Ns288p1576 rfl)) 

noncomputable abbrev qz552 := (RS289to300.d3 qz622 qz630 (@Enclosure.dec_le_dec qz622 qz630 604490 1000 605865 1000 qz625 qz633 rfl rfl rfl))

noncomputable abbrev qz273 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz552)

noncomputable def Ns288p1578 := @Enclosure.Real.IsNear.of_eq qz273 (hardyZApproximantRS₀ qz96) Bool.true 461395591794983839587 1180591620717411303424 24124602304846179935819 Ns288p451 

noncomputable abbrev qz553 := (@Enclosure.dec_le_dec qz622 qz630 604490 1000 605865 1000 qz625 qz633 rfl rfl rfl)

noncomputable abbrev qz274 := qz553

noncomputable def Ns288p1579 := @Enclosure.Real.IsNear.neg_val qz273 461395591794983839587 1180591620717411303424 24124602304846179935819 Ns288p451 (Ns288p1578 (RS289to300.d4 qz96 qz114 qz274) RS289to300.d51) rfl 

noncomputable abbrev qz275 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz552)

noncomputable def Ns288p1580 := @Enclosure.Real.IsNear.of_eq qz275 (hardyZApproximantRS₀ qz114) Bool.false 59648995970917688225 18446744073709551616 120452274673936145741 92233720368547758080000 

noncomputable def Ns288p1581 := @Enclosure.Real.IsNear.pos_val qz275 59648995970917688225 18446744073709551616 120452274673936145741 92233720368547758080000 (Ns288p1580 (RS289to300.d46 qz96 qz114 qz274) RS289to300.d52) rfl 

noncomputable def Ns288p1582 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz273 qz4 qz96 598981 1000 604490 1000 

noncomputable def Ns288p1583 := @Enclosure.norm_gt_of_isNear qz273 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 461395591794983839587 1180591620717411303424 24124602304846179935819 

noncomputable def Ns288p1584 := @Ns288p1583 Ns288p451 34141065 536870912 1213 2684354560 (Ns288p1578 (RS289to300.d4 qz96 qz114 qz274) RS289to300.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable def Ns288p1585 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz275 qz4 qz114 598981 1000 605865 1000 

noncomputable def Ns288p1586 := @Enclosure.norm_gt_of_isNear qz275 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 59648995970917688225 18446744073709551616 120452274673936145741 

noncomputable def Ns288p1587 := @Ns288p1586 92233720368547758080000 34141065 536870912 1213 2684354560 (Ns288p1580 (RS289to300.d46 qz96 qz114 qz274) RS289to300.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable abbrev qz276 := qz552

noncomputable def Ns288p1588 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz96 604490 1000 qz99 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz273 qz275 (Ns288p1579 rfl rfl) (Ns288p1581 rfl rfl)) (Ns288p1582 qz9 qz99 rfl rfl rfl rfl (Ns288p1584 rfl)) (Ns288p1585 qz9 qz117 rfl rfl rfl rfl (Ns288p1587 rfl)) 

noncomputable abbrev qz554 := (RS289to300.d3 qz630 qz638 (@Enclosure.dec_le_dec qz630 qz638 605865 1000 607240 1000 qz633 qz641 rfl rfl rfl))

noncomputable abbrev qz277 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz554)

noncomputable def Ns288p1589 := @Enclosure.Real.IsNear.of_eq qz277 (hardyZApproximantRS₀ qz114) Bool.false 59648995970917688225 18446744073709551616 120452274673936145741 92233720368547758080000 

noncomputable abbrev qz555 := (@Enclosure.dec_le_dec qz630 qz638 605865 1000 607240 1000 qz633 qz641 rfl rfl rfl)

noncomputable abbrev qz278 := qz555

noncomputable def Ns288p1590 := @Enclosure.Real.IsNear.pos_val qz277 59648995970917688225 18446744073709551616 120452274673936145741 92233720368547758080000 (Ns288p1589 (RS289to300.d4 qz114 qz132 qz278) RS289to300.d52) rfl 

noncomputable abbrev qz279 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz554)

noncomputable def Ns288p1591 := @Enclosure.Real.IsNear.of_eq qz279 (hardyZApproximantRS₀ qz132) Bool.true 6233550677370429593253 1180591620717411303424 24077565219058140988461 Ns288p451 

noncomputable def Ns288p1592 := @Enclosure.Real.IsNear.neg_val qz279 6233550677370429593253 1180591620717411303424 24077565219058140988461 Ns288p451 (Ns288p1591 (RS289to300.d46 qz114 qz132 qz278) RS289to300.d53) rfl 

noncomputable def Ns288p1593 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz277 qz4 qz114 598981 1000 605865 1000 

noncomputable def Ns288p1594 := @Enclosure.norm_gt_of_isNear qz277 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 59648995970917688225 18446744073709551616 120452274673936145741 

noncomputable def Ns288p1595 := @Ns288p1594 92233720368547758080000 34141065 536870912 1213 2684354560 (Ns288p1589 (RS289to300.d4 qz114 qz132 qz278) RS289to300.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable def Ns288p1596 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz279 qz4 qz132 598981 1000 607240 1000 

noncomputable def Ns288p1597 := @Enclosure.norm_gt_of_isNear qz279 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 6233550677370429593253 1180591620717411303424 24077565219058140988461 

noncomputable def Ns288p1598 := @Ns288p1597 Ns288p451 34141065 536870912 1213 2684354560 (Ns288p1591 (RS289to300.d46 qz114 qz132 qz278) RS289to300.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable abbrev qz280 := qz554

noncomputable def Ns288p1599 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz114 605865 1000 qz117 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz277 qz279 (Ns288p1590 rfl rfl) (Ns288p1592 rfl rfl)) (Ns288p1593 qz9 qz117 rfl rfl rfl rfl (Ns288p1595 rfl)) (Ns288p1596 qz9 qz135 rfl rfl rfl rfl (Ns288p1598 rfl)) 

noncomputable abbrev qz556 := (RS289to300.d3 qz638 qz646 (@Enclosure.dec_le_dec qz638 qz646 607240 1000 608615 1000 qz641 qz649 rfl rfl rfl))

noncomputable abbrev qz281 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz556)

noncomputable def Ns288p1600 := @Enclosure.Real.IsNear.of_eq qz281 (hardyZApproximantRS₀ qz132) Bool.true 6233550677370429593253 1180591620717411303424 24077565219058140988461 Ns288p451 

noncomputable abbrev qz557 := (@Enclosure.dec_le_dec qz638 qz646 607240 1000 608615 1000 qz641 qz649 rfl rfl rfl)

noncomputable abbrev qz282 := qz557

noncomputable def Ns288p1601 := @Enclosure.Real.IsNear.neg_val qz281 6233550677370429593253 1180591620717411303424 24077565219058140988461 Ns288p451 (Ns288p1600 (RS289to300.d4 qz132 qz150 qz282) RS289to300.d53) rfl 

noncomputable abbrev qz283 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz556)

noncomputable def Ns288p1602 := @Enclosure.Real.IsNear.of_eq qz283 (hardyZApproximantRS₀ qz150) Bool.false 14572003558972881253 18446744073709551616 1204221293610407561651 922337203685477580800000 

noncomputable def Ns288p1603 := @Enclosure.Real.IsNear.pos_val qz283 14572003558972881253 18446744073709551616 1204221293610407561651 922337203685477580800000 (Ns288p1602 (RS289to300.d46 qz132 qz150 qz282) RS289to300.d54) rfl 

noncomputable def Ns288p1604 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz281 qz4 qz132 598981 1000 607240 1000 

noncomputable def Ns288p1605 := @Enclosure.norm_gt_of_isNear qz281 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 6233550677370429593253 1180591620717411303424 24077565219058140988461 

noncomputable def Ns288p1606 := @Ns288p1605 Ns288p451 34141065 536870912 1213 2684354560 (Ns288p1600 (RS289to300.d4 qz132 qz150 qz282) RS289to300.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable def Ns288p1607 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz283 qz4 qz150 598981 1000 608615 1000 

noncomputable def Ns288p1608 := @Enclosure.norm_gt_of_isNear qz283 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 14572003558972881253 18446744073709551616 1204221293610407561651 

noncomputable def Ns288p1609 := @Ns288p1608 922337203685477580800000 34141065 536870912 1213 2684354560 (Ns288p1602 (RS289to300.d46 qz132 qz150 qz282) RS289to300.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable abbrev qz284 := qz556

noncomputable def Ns288p1610 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz132 607240 1000 qz135 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz281 qz283 (Ns288p1601 rfl rfl) (Ns288p1603 rfl rfl)) (Ns288p1604 qz9 qz135 rfl rfl rfl rfl (Ns288p1606 rfl)) (Ns288p1607 qz9 qz153 rfl rfl rfl rfl (Ns288p1609 rfl)) 

noncomputable abbrev qz558 := (RS289to300.d3 qz646 qz654 (@Enclosure.dec_le_dec qz646 qz654 608615 1000 609988 1000 qz649 qz657 rfl rfl rfl))

noncomputable abbrev qz285 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz558)

noncomputable def Ns288p1611 := @Enclosure.Real.IsNear.of_eq qz285 (hardyZApproximantRS₀ qz150) Bool.false 14572003558972881253 18446744073709551616 1204221293610407561651 922337203685477580800000 

noncomputable abbrev qz559 := (@Enclosure.dec_le_dec qz646 qz654 608615 1000 609988 1000 qz649 qz657 rfl rfl rfl)

noncomputable abbrev qz286 := qz559

noncomputable def Ns288p1612 := @Enclosure.Real.IsNear.pos_val qz285 14572003558972881253 18446744073709551616 1204221293610407561651 922337203685477580800000 (Ns288p1611 (RS289to300.d4 qz150 qz168 qz286) RS289to300.d54) rfl 

noncomputable abbrev qz287 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz558)

noncomputable def Ns288p1613 := @Enclosure.Real.IsNear.of_eq qz287 (hardyZApproximantRS₀ qz168) Bool.true 949292054892764662043 590295810358705651712 2410072561100358853967 Ns288p69 

noncomputable def Ns288p1614 := @Enclosure.Real.IsNear.neg_val qz287 949292054892764662043 590295810358705651712 2410072561100358853967 Ns288p69 (Ns288p1613 (RS289to300.d46 qz150 qz168 qz286) RS289to300.d55) rfl 

noncomputable def Ns288p1615 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz285 qz4 qz150 598981 1000 608615 1000 

noncomputable def Ns288p1616 := @Enclosure.norm_gt_of_isNear qz285 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 14572003558972881253 18446744073709551616 1204221293610407561651 

noncomputable def Ns288p1617 := @Ns288p1616 922337203685477580800000 34141065 536870912 1213 2684354560 (Ns288p1611 (RS289to300.d4 qz150 qz168 qz286) RS289to300.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable def Ns288p1618 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz287 qz4 qz168 598981 1000 609988 1000 

noncomputable def Ns288p1619 := @Enclosure.norm_gt_of_isNear qz287 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 949292054892764662043 590295810358705651712 2410072561100358853967 

noncomputable def Ns288p1620 := @Ns288p1619 Ns288p69 34141065 536870912 1213 2684354560 (Ns288p1613 (RS289to300.d46 qz150 qz168 qz286) RS289to300.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable abbrev qz288 := qz558

noncomputable def Ns288p1621 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz150 608615 1000 qz153 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz285 qz287 (Ns288p1612 rfl rfl) (Ns288p1614 rfl rfl)) (Ns288p1615 qz9 qz153 rfl rfl rfl rfl (Ns288p1617 rfl)) (Ns288p1618 qz9 qz171 rfl rfl rfl rfl (Ns288p1620 rfl)) 

noncomputable abbrev qz700 := (@Enclosure.dec_le_dec qz745 qz749 609988 1000 611361 1000 (@Eq.refl Real qz745) (@Eq.refl Real qz749) rfl rfl rfl)

noncomputable abbrev qz560 := (RS289to300.d3 qz654 qz662 qz700)

noncomputable abbrev qz289 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz560)

noncomputable def Ns288p1622 := @Enclosure.Real.IsNear.of_eq qz289 (hardyZApproximantRS₀ qz168) Bool.true 949292054892764662043 590295810358705651712 2410072561100358853967 Ns288p69 

noncomputable abbrev qz561 := qz700

noncomputable abbrev qz290 := qz561

noncomputable def Ns288p1623 := @Enclosure.Real.IsNear.neg_val qz289 949292054892764662043 590295810358705651712 2410072561100358853967 Ns288p69 (Ns288p1622 (RS289to300.d4 qz168 qz186 qz290) RS289to300.d55) rfl 

noncomputable abbrev qz291 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz560)

noncomputable def Ns288p1624 := @Enclosure.Real.IsNear.of_eq qz291 (hardyZApproximantRS₀ qz186) Bool.false 485605364974319949171 590295810358705651712 12063523355545178122373 Ns288p193 

noncomputable def Ns288p1625 := @Enclosure.Real.IsNear.pos_val qz291 485605364974319949171 590295810358705651712 12063523355545178122373 Ns288p193 (Ns288p1624 (RS289to300.d46 qz168 qz186 qz290) RS289to300.d56) rfl 

noncomputable def Ns288p1626 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz289 qz4 qz168 598981 1000 609988 1000 

noncomputable def Ns288p1627 := @Enclosure.norm_gt_of_isNear qz289 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 949292054892764662043 590295810358705651712 2410072561100358853967 

noncomputable def Ns288p1628 := @Ns288p1627 Ns288p69 34141065 536870912 1213 2684354560 (Ns288p1622 (RS289to300.d4 qz168 qz186 qz290) RS289to300.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable def Ns288p1629 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz291 qz4 qz186 598981 1000 611361 1000 

noncomputable def Ns288p1630 := @Enclosure.norm_gt_of_isNear qz291 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 485605364974319949171 590295810358705651712 12063523355545178122373 

noncomputable def Ns288p1631 := @Ns288p1630 Ns288p193 34141065 536870912 1213 2684354560 (Ns288p1624 (RS289to300.d46 qz168 qz186 qz290) RS289to300.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable abbrev qz292 := qz560

noncomputable def Ns288p1632 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz168 609988 1000 qz171 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz289 qz291 (Ns288p1623 rfl rfl) (Ns288p1625 rfl rfl)) (Ns288p1626 qz9 qz171 rfl rfl rfl rfl (Ns288p1628 rfl)) (Ns288p1629 qz9 qz189 rfl rfl rfl rfl (Ns288p1631 rfl)) 

noncomputable abbrev qz701 := (@Enclosure.dec_le_dec qz749 qz753 611361 1000 612733 1000 (@Eq.refl Real qz749) qz756 rfl rfl rfl)

noncomputable abbrev qz562 := (RS289to300.d3 qz662 qz670 qz701)

noncomputable abbrev qz293 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz562)

noncomputable def Ns288p1633 := @Enclosure.Real.IsNear.of_eq qz293 (hardyZApproximantRS₀ qz186) Bool.false 485605364974319949171 590295810358705651712 12063523355545178122373 Ns288p193 

noncomputable abbrev qz563 := qz701

noncomputable abbrev qz294 := qz563

noncomputable def Ns288p1634 := @Enclosure.Real.IsNear.pos_val qz293 485605364974319949171 590295810358705651712 12063523355545178122373 Ns288p193 (Ns288p1633 (RS289to300.d4 qz186 qz204 qz294) RS289to300.d56) rfl 

noncomputable abbrev qz295 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz562)

noncomputable def Ns288p1635 := @Enclosure.Real.IsNear.of_eq qz295 (hardyZApproximantRS₀ qz204) Bool.true 48579620954259009507 18446744073709551616 3019794187595054263599 Ns288p1216 

noncomputable def Ns288p1636 := @Enclosure.Real.IsNear.neg_val qz295 48579620954259009507 18446744073709551616 3019794187595054263599 Ns288p1216 (Ns288p1635 (RS289to300.d46 qz186 qz204 qz294) RS289to300.d57) rfl 

noncomputable def Ns288p1637 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz293 qz4 qz186 598981 1000 611361 1000 

noncomputable def Ns288p1638 := @Enclosure.norm_gt_of_isNear qz293 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 485605364974319949171 590295810358705651712 12063523355545178122373 

noncomputable def Ns288p1639 := @Ns288p1638 Ns288p193 34141065 536870912 1213 2684354560 (Ns288p1633 (RS289to300.d4 qz186 qz204 qz294) RS289to300.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable def Ns288p1640 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz295 qz4 qz204 598981 1000 612733 1000 

noncomputable def Ns288p1641 := @Enclosure.norm_gt_of_isNear qz295 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 48579620954259009507 18446744073709551616 3019794187595054263599 

noncomputable def Ns288p1642 := @Ns288p1641 Ns288p1216 34141065 536870912 1213 2684354560 (Ns288p1635 (RS289to300.d46 qz186 qz204 qz294) RS289to300.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable abbrev qz296 := qz562

noncomputable def Ns288p1643 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz186 611361 1000 qz189 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz293 qz295 (Ns288p1634 rfl rfl) (Ns288p1636 rfl rfl)) (Ns288p1637 qz9 qz189 rfl rfl rfl rfl (Ns288p1639 rfl)) (Ns288p1640 qz9 qz209 rfl rfl rfl rfl (Ns288p1642 rfl)) 

noncomputable abbrev qz702 := (@Enclosure.dec_le_dec qz753 qz758 612733 1000 614105 1000 qz756 qz761 rfl rfl rfl)

noncomputable abbrev qz564 := (RS289to300.d3 qz670 qz680 qz702)

noncomputable abbrev qz297 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz564)

noncomputable def Ns288p1644 := @Enclosure.Real.IsNear.of_eq qz297 (hardyZApproximantRS₀ qz204) Bool.true 48579620954259009507 18446744073709551616 3019794187595054263599 Ns288p1216 

noncomputable abbrev qz565 := qz702

noncomputable abbrev qz298 := qz565

noncomputable def Ns288p1645 := @Enclosure.Real.IsNear.neg_val qz297 48579620954259009507 18446744073709551616 3019794187595054263599 Ns288p1216 (Ns288p1644 (RS289to300.d4 qz204 qz223 qz298) RS289to300.d57) rfl 

noncomputable abbrev qz299 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz564)

noncomputable def Ns288p1646 := @Enclosure.Real.IsNear.of_eq qz299 (hardyZApproximantRS₀ qz223) Bool.false 147142885950026886717 147573952589676412928 12095773048167442240977 Ns288p193 

noncomputable def Ns288p1647 := @Enclosure.Real.IsNear.pos_val qz299 147142885950026886717 147573952589676412928 12095773048167442240977 Ns288p193 (Ns288p1646 (RS289to300.d46 qz204 qz223 qz298) RS289to300.d58) rfl 

noncomputable def Ns288p1648 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz297 qz4 qz204 598981 1000 612733 1000 

noncomputable def Ns288p1649 := @Enclosure.norm_gt_of_isNear qz297 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 48579620954259009507 18446744073709551616 3019794187595054263599 

noncomputable def Ns288p1650 := @Ns288p1649 Ns288p1216 34141065 536870912 1213 2684354560 (Ns288p1644 (RS289to300.d4 qz204 qz223 qz298) RS289to300.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable def Ns288p1651 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz299 qz4 qz223 598981 1000 614105 1000 

noncomputable def Ns288p1652 := @Enclosure.norm_gt_of_isNear qz299 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 147142885950026886717 147573952589676412928 12095773048167442240977 

noncomputable def Ns288p1653 := @Ns288p1652 Ns288p193 34141065 536870912 1213 2684354560 (Ns288p1646 (RS289to300.d46 qz204 qz223 qz298) RS289to300.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable abbrev qz300 := qz564

noncomputable def Ns288p1654 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz204 612733 1000 qz209 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz297 qz299 (Ns288p1645 rfl rfl) (Ns288p1647 rfl rfl)) (Ns288p1648 qz9 qz209 rfl rfl rfl rfl (Ns288p1650 rfl)) (Ns288p1651 qz9 qz226 rfl rfl rfl rfl (Ns288p1653 rfl)) 

noncomputable abbrev qz768 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 614105 1000) (Enclosure.sfrac Bool.false 615476 1000) 614105 1000 615476 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 614105 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 615476 1000)) rfl rfl rfl)

noncomputable abbrev qz703 := qz768

noncomputable abbrev qz566 := (RS289to300.d3 qz680 qz690 qz703)

noncomputable abbrev qz301 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz566)

noncomputable def Ns288p1655 := @Enclosure.Real.IsNear.of_eq qz301 (hardyZApproximantRS₀ qz223) Bool.false 147142885950026886717 147573952589676412928 12095773048167442240977 Ns288p193 

noncomputable abbrev qz567 := qz703

noncomputable abbrev qz302 := qz567

noncomputable def Ns288p1656 := @Enclosure.Real.IsNear.pos_val qz301 147142885950026886717 147573952589676412928 12095773048167442240977 Ns288p193 (Ns288p1655 (RS289to300.d4 qz223 qz240 qz302) RS289to300.d58) rfl 

noncomputable abbrev qz303 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz566)

noncomputable def Ns288p1657 := @Enclosure.Real.IsNear.of_eq qz303 (hardyZApproximantRS₀ qz240) Bool.true 317513672896874761871 1180591620717411303424 24241231332832346576191 Ns288p451 

noncomputable def Ns288p1658 := @Enclosure.Real.IsNear.neg_val qz303 317513672896874761871 1180591620717411303424 24241231332832346576191 Ns288p451 (Ns288p1657 (RS289to300.d46 qz223 qz240 qz302) RS289to300.d59) rfl 

noncomputable def Ns288p1659 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz301 qz4 qz223 598981 1000 614105 1000 

noncomputable def Ns288p1660 := @Enclosure.norm_gt_of_isNear qz301 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 147142885950026886717 147573952589676412928 12095773048167442240977 

noncomputable def Ns288p1661 := @Ns288p1660 Ns288p193 34141065 536870912 1213 2684354560 (Ns288p1655 (RS289to300.d4 qz223 qz240 qz302) RS289to300.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable def Ns288p1662 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz303 qz4 qz240 598981 1000 615476 1000 

noncomputable def Ns288p1663 := @Enclosure.norm_gt_of_isNear qz303 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 317513672896874761871 1180591620717411303424 24241231332832346576191 

noncomputable def Ns288p1664 := @Ns288p1663 Ns288p451 34141065 536870912 1213 2684354560 (Ns288p1657 (RS289to300.d46 qz223 qz240 qz302) RS289to300.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 34141065 536870912 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS289to300.d48) rfl rfl rfl rfl 

noncomputable abbrev qz304 := qz566

noncomputable def Ns288p1665 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz223 614105 1000 qz226 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz301 qz303 (Ns288p1656 rfl rfl) (Ns288p1658 rfl rfl)) (Ns288p1659 qz9 qz226 rfl rfl rfl rfl (Ns288p1661 rfl)) (Ns288p1662 qz9 qz243 rfl rfl rfl rfl (Ns288p1664 rfl)) 

noncomputable def Ns288p1666 := @List.cons RS289to300.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns288p1654)) (@List.cons RS289to300.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns288p1665)) (@List.nil RS289to300.d0)) 

noncomputable def Ns288p1667 := @List.cons RS289to300.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns288p1632)) (@List.cons RS289to300.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns288p1643)) Ns288p1666) 

noncomputable def Ns288p1668 := @List.cons RS289to300.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns288p1610)) (@List.cons RS289to300.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns288p1621)) Ns288p1667) 

noncomputable def Ns288p1669 := @List.cons RS289to300.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns288p1588)) (@List.cons RS289to300.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns288p1599)) Ns288p1668) 

noncomputable def Ns288p1670 := @List.cons RS289to300.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns288p1566)) (@List.cons RS289to300.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns288p1577)) Ns288p1669) 

noncomputable def Ns288p1671 := @List.cons RS289to300.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz260 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz260) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz260) Ns288p1544)) (@List.cons RS289to300.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz264 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz264) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz264) Ns288p1555)) Ns288p1670) 

noncomputable abbrev qz568 := (RS289to300.d2 qz654 qz662 qz700)

noncomputable abbrev qz704 := (RS289to300.d2 qz753 qz758 (@Enclosure.dec_le_dec qz753 qz758 612733 1000 614105 1000 qz756 qz761 rfl rfl rfl))

noncomputable abbrev qz705 := (@List.cons RS289to300.d1 (RS289to300.d2 qz758 qz763 qz768) (@List.nil RS289to300.d1))

noncomputable abbrev qz569 := (@List.cons RS289to300.d1 (RS289to300.d2 qz662 qz670 qz701) (@List.cons RS289to300.d1 qz704 qz705))

noncomputable abbrev qz305 := (@List.cons RS289to300.d1 (RS289to300.d2 qz469 qz482 qz559) (@List.cons RS289to300.d1 qz568 qz569))

noncomputable def Ns288p1672 := @List.cons RS289to300.d1 (RS289to300.d2 qz114 qz132 qz278) (@List.cons RS289to300.d1 (RS289to300.d2 qz132 qz150 qz282) qz305) 

noncomputable abbrev qz306 := (RS289to300.d2 qz430 qz443 qz553)

noncomputable def Ns288p1673 := @List.IsChain.cons_cons RS289to300.d1 RS289to300.d60 qz306 (RS289to300.d2 qz114 qz132 qz278) (@List.cons RS289to300.d1 (RS289to300.d2 qz132 qz150 qz282) qz305) 

noncomputable def Ns288p1674 := @List.IsChain.cons_cons RS289to300.d1 RS289to300.d60 (RS289to300.d2 qz114 qz132 qz278) (RS289to300.d2 qz132 qz150 qz282) qz305 (@Enclosure.dec_le_dec qz132 qz132 607240 1000 607240 1000 qz135 qz135 rfl rfl rfl) 

noncomputable abbrev qz307 := (RS289to300.d2 qz469 qz482 qz559)

noncomputable abbrev qz308 := qz568

noncomputable abbrev qz309 := qz569

noncomputable abbrev qz570 := (RS289to300.d2 qz662 qz670 qz701)

noncomputable abbrev qz310 := qz570

noncomputable abbrev qz571 := (@List.cons RS289to300.d1 qz704 qz705)

noncomputable abbrev qz311 := qz571

noncomputable abbrev qz572 := qz704

noncomputable abbrev qz312 := qz572

noncomputable abbrev qz573 := qz705

noncomputable abbrev qz313 := qz573

noncomputable abbrev qz706 := (RS289to300.d2 qz758 qz763 qz768)

noncomputable abbrev qz574 := qz706

noncomputable abbrev qz314 := qz574

noncomputable def Ns288p1675 := @List.IsChain.cons_cons RS289to300.d1 RS289to300.d60 qz307 qz308 qz309 (@Enclosure.dec_le_dec qz168 qz168 609988 1000 609988 1000 qz171 qz171 rfl rfl rfl) (@List.IsChain.cons_cons RS289to300.d1 RS289to300.d60 qz308 qz310 qz311 (@Enclosure.dec_le_dec qz186 qz186 611361 1000 611361 1000 qz189 qz189 rfl rfl rfl) (@List.IsChain.cons_cons RS289to300.d1 RS289to300.d60 qz310 qz312 qz313 (@Enclosure.dec_le_dec qz204 qz204 612733 1000 612733 1000 qz209 qz209 rfl rfl rfl) (@List.IsChain.cons_cons RS289to300.d1 RS289to300.d60 qz312 qz314 (@List.nil RS289to300.d1) (@Enclosure.dec_le_dec qz223 qz223 614105 1000 614105 1000 qz226 qz226 rfl rfl rfl) (@List.IsChain.singleton RS289to300.d1 RS289to300.d60 qz314)))) 

noncomputable abbrev qz315 := (@List.cons RS289to300.d1 qz568 qz569)

noncomputable def Ns288p1676 := @List.IsChain.cons_cons RS289to300.d1 RS289to300.d60 (RS289to300.d2 qz132 qz150 qz282) qz307 qz315 (@Enclosure.dec_le_dec qz150 qz150 608615 1000 608615 1000 qz153 qz153 rfl rfl rfl) Ns288p1675 

noncomputable def Ns288p1677 := @List.IsChain.cons_cons RS289to300.d1 RS289to300.d60 (RS289to300.d2 qz4 qz33 qz258) (RS289to300.d2 qz33 qz60 qz262) (@List.cons RS289to300.d1 (RS289to300.d2 qz60 qz78 qz266) (@List.cons RS289to300.d1 (RS289to300.d2 qz78 qz96 qz270) (@List.cons RS289to300.d1 qz306 Ns288p1672))) (@Enclosure.dec_le_dec qz33 qz33 600359 1000 600359 1000 qz36 qz36 rfl rfl rfl) (@List.IsChain.cons_cons RS289to300.d1 RS289to300.d60 (RS289to300.d2 qz33 qz60 qz262) (RS289to300.d2 qz60 qz78 qz266) (@List.cons RS289to300.d1 (RS289to300.d2 qz78 qz96 qz270) (@List.cons RS289to300.d1 qz306 Ns288p1672)) (@Enclosure.dec_le_dec qz60 qz60 601737 1000 601737 1000 qz63 qz63 rfl rfl rfl) (@List.IsChain.cons_cons RS289to300.d1 RS289to300.d60 (RS289to300.d2 qz60 qz78 qz266) (RS289to300.d2 qz78 qz96 qz270) (@List.cons RS289to300.d1 qz306 Ns288p1672) (@Enclosure.dec_le_dec qz78 qz78 603114 1000 603114 1000 qz81 qz81 rfl rfl rfl) (@List.IsChain.cons_cons RS289to300.d1 RS289to300.d60 (RS289to300.d2 qz78 qz96 qz270) qz306 Ns288p1672 (@Enclosure.dec_le_dec qz96 qz96 604490 1000 604490 1000 qz99 qz99 rfl rfl rfl) (Ns288p1673 (@Enclosure.dec_le_dec qz114 qz114 605865 1000 605865 1000 qz117 qz117 rfl rfl rfl) (Ns288p1674 Ns288p1676))))) 

noncomputable abbrev qz575 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz576 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns288p1671 Ns288p1677)

noncomputable abbrev qz577 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns288p1671 Ns288p1677))

theorem RS289to300.d61 : Zeta.Certificates.BatchSpec 12 598981 1000 615476 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz575 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz575 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz575 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz575 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz575 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz240)))) qz576 (@And.intro (@Eq Nat (@List.length qz575 qz577) 12) (And (@Eq (Option Real) (@Option.map qz575 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz575 qz577)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz575 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz575 qz577)) (@Option.some Real qz240))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz575 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz575 qz577)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz575 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz575 qz577)) (@Option.some Real qz240)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz240))))

theorem solution : Zeta.Certificates.BatchSpec 12 598981 1000 615476 1000 := RS289to300.d61
#print axioms solution
#check solution
