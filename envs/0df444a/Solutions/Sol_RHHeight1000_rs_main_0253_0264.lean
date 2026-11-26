-- Prove2me | solution 1 for RHHeight1000.rs_main_0253_0264
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:08:52.689962+00:00
-- url     : https://prove2.me/submissions/efec0e97-7bad-48bb-94ba-f5911d851121

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

noncomputable def RS253to264.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS253to264.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS253to264.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS253to264.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS253to264.d2 a b h 

theorem RS253to264.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS253to264.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS253to264.d3 a b h)) 

noncomputable def Ns252p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns252p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns252p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns252p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns252p0 Ns252p1 Ns252p2 Ns252p1 153643044 134217728 1 51840000 153643044 134217728 1 51840000 76821522 67108864 2 67108864 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns252p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns252p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns252p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns252p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns252p8 := nat_lit 167537954069964697925743468333314178468718661948561187618563575975392713740913527107727581163208035826476740967700482432525301063254420572874757592895482956004842597348203117269212172556829666669574421653274845612596416189641484794702002223261246862056663160605878293700340502480877986491439034432953223334258717026053687371824342493299510132312376251152844516906794910572262907940062760396663270105627554083664899640691826599584783763757814813433640133591539937449421955686657622469485188711283992428713614179785896055117030632677201478317872225272595773536303110412989181984739022579128493081560758017763072115692678596043664844667144619713966763611484179303468167142547433165016751768184247559143333542643815355903304572487929375 

noncomputable def Ns252p9 := nat_lit 17907736863639440849562382641391758203535690054199171304015283257442503423240620144819838407313611418261944516207295868563739563278604805791797182761045687776939279949642059267526948014748996956777332184087524644234759874591635243045607722412471722018588244283882362848653445974523544951031470230725674276297342086185092985546835544820091590454230569790847977790484558207349923322458845585052164126500435851662252152223728079705692133047658564669873831757357628115566356048471439549797170528303905720944834637690907185213991407615774042056720704508980680095051114888612186461088301140868302968264130481206655302741383410655080008578156649725227045954510069588220729495895148666460653631514375880874422615237249871322129146554264800 

noncomputable def Ns252p10 := nat_lit 55164646516618494962085419356369025784335016154267579706247610053041231157772817011486486467101704279863254798704146668052276438579475100451766223896220272709675360577301802978530276301158911649961092601279696986330335403118086533522541958716560166657634553390183479955483588238249446822384543398154260439705049143284278540285021213103458182619368483938376641172730818250587232036579805400979202432024046862170503602539341971086573372247299262086029843105216008583038025403798224342134620653974939981235680083776396058604459065501719125356177784467570909658245422960948263734871602033841948787585406240093531041217463298165642337705122589129757920995868559518021463265498464182174549661735402095023640043996665674913376875 

noncomputable def Ns252p11 := BSN.log_dyadic_bound Ns252p6 Ns252p7 15 14 Ns252p8 134217728 51840000 Ns252p9 Ns252p10 153643044 Ns252p4 Ns252p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns252p6) (BSN.artanhQ Ns252p7) 0 14 Ns252p9 Ns252p8 Ns252p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns252p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns252p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns252p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns252p15 := nat_lit 167537954069966963268140139327979112712430526945422964221951926912223381190141639739514890494967825643602350173964944759828460064784215684919760383437959917620844610857567326816719640593037578236900835917107172977527392439886629774248115214831425484905681376157923696414882114961796820014026232307332015059110330001516939277521159573995394989771587717775443426002499543257897301982481613760098955890450106043861450716722534643739571053080256776912576113428445260435254713579381797931690799491102381747484553243404562568585572234105168360737285205910186933811836504830286397217473365026331067977496463917110493303316865058355012304571237619413071097245713770677768486493924969821719264401216877841676972336093778875903304572487929375 

noncomputable def Ns252p16 := nat_lit 17907736863639702486765313263906285882628955290251965205176678923530777959693011244026517850256414903756943142851250712732214241881959351517241344993825585048584379523049477943740273636414656012170312373198803997844271825165684859407921203335666024680974464565759223251918458072775203410604089667122984485578465112081892102496937045858735135721609691262763214794451343726045584198128451069547586972080574568545086657023793200560105564573365716615162566961587407171758966967827997201380802107846920231945878242774600967607639551032178207663699700360114112068650063802902647517702890145150192721997537569966984346993833704449560383184487996362781528900358997452380059737141488304159449328022742959995775545894292303322129146554264800 

noncomputable def Ns252p17 := nat_lit 55164646516619937449385584700664297411818070214438189962773666351465523500358685366424500506990751111492356556545320273548942244833046464529601272738875466881799996765940232256588350019911833156887888425998391295014189841212513610526066550079316346993943774342801096070086869790972589246312728227659319758310961510342377923950694747797317942483020440897997204711883064182772445608288320382376665481938194224815739627075458138172195220395246294556718284728034954178416253903237031389214179719385823921869528509431462690683227358218086518156757026652846493301460983550768858152506145788622699720737745394141184245149692548799188169247529408201840608223422296381897323845616153036586108326210125693898345963996665674913376875 

noncomputable def Ns252p18 := BSN.log_dyadic_bound Ns252p13 Ns252p14 15 14 Ns252p15 134217728 51840000 Ns252p16 Ns252p17 153643044 Ns252p12 Ns252p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns252p13) (BSN.artanhQ Ns252p14) 0 14 Ns252p16 Ns252p15 Ns252p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns252p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 76821522 67108864 2 67108864 38410761 33554432 1 33554432 (Ns252p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns252p0 Ns252p1 153643044 134217728 1 51840000 Bool.false (BSN.logfrac_isNear Ns252p4 Ns252p5 1 Ns252p0 Ns252p1 153643044 134217728 51840000 rfl rfl rfl (Ns252p11 rfl))) (BSN.isNear_log_sfrac Ns252p2 Ns252p1 153643044 134217728 1 51840000 Bool.false (BSN.logfrac_isNear Ns252p12 Ns252p5 1 Ns252p2 Ns252p1 153643044 134217728 51840000 rfl rfl rfl (Ns252p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS253to264.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 33554432 := Ns252p19 

noncomputable def Ns252p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 8388608 3240000 385100712855 135135 5814539 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz579 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz316 := qz579

noncomputable abbrev qz0 := qz316

theorem RS253to264.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 5814539 8388608 1 3240000 := BSN.isNear_log_sfrac 2 1 5814539 8388608 1 3240000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 5814539 8388608 3240000 rfl rfl rfl (Ns252p20 rfl)) 

theorem RS253to264.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 93032624 134217728 42 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 5814539 8388608 1 3240000 93032624 134217728 42 134217728 RS253to264.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz580 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz319 := qz580

noncomputable def Ns252p21 := @Enclosure.Real.IsNear.inv_image qz317 23726567 16777216 1 16777216 5931641 5931642 8388608 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 23726567 16777216 1 16777216 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 23726567 16777216 1 16777216 23726567 16777216 1 16777216 (BSN.sqrt_enclosure 2 1 11863283 11863284 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS253to264.d8 : Enclosure.Real.IsNear qz320 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 11863283 16777216 1 16777216 (Ns252p21 rfl rfl) rfl 

theorem RS253to264.d9 : Enclosure.Real.IsNear qz320 Bool.false 94906264 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 94906264 134217728 8 134217728 RS253to264.d8 rfl 

noncomputable def Ns252p22 := BSN.log_dyadic_bound 1 2 12 11 1326382131865190400 8388608 3240000 130797573554866995 13749310575 9215827 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 1) (BSN.artanhQ 2) 0 11 130797573554866995 1326382131865190400 13749310575 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS253to264.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 9215827 8388608 1 3240000 := BSN.isNear_log_sfrac 3 1 9215827 8388608 1 3240000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 9215827 8388608 3240000 rfl rfl rfl (Ns252p22 rfl)) 

theorem RS253to264.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 147453232 134217728 42 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 9215827 8388608 1 3240000 147453232 134217728 42 134217728 RS253to264.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns252p23 := @Enclosure.Real.IsNear.inv_image qz321 29058991 16777216 1 16777216 4843164 4843166 8388608 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 29058991 16777216 1 16777216 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 29058991 16777216 1 16777216 29058991 16777216 1 16777216 (BSN.sqrt_enclosure 3 1 14529495 14529496 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS253to264.d12 : Enclosure.Real.IsNear qz323 Bool.false 4843165 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 9686330 16777216 2 16777216 4843165 8388608 1 8388608 (Ns252p23 rfl rfl) rfl 

theorem RS253to264.d13 : Enclosure.Real.IsNear qz323 Bool.false 77490640 134217728 16 134217728 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 4843165 8388608 1 8388608 77490640 134217728 16 134217728 RS253to264.d12 rfl 

noncomputable def Ns252p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns252p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns252p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns252p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns252p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns252p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns252p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns252p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns252p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns252p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns252p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns252p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns252p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns252p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns252p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns252p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns252p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns252p25 Ns252p26 Ns252p27 Ns252p28 200200021673987500790625 Ns252p29 Ns252p30 Ns252p31 Ns252p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns252p32 Ns252p33 151412625 Ns252p34 Ns252p35 1322214852783825 Ns252p27 Ns252p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns252p32 Ns252p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns252p34 Ns252p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns252p36 Ns252p37 1267389585 Ns252p38 Ns252p39 1927077560082675 Ns252p29 Ns252p30 Ns252p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns252p36 Ns252p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns252p38 Ns252p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS253to264.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns252p24 Ns252p25 1 Ns252p26 := Ns252p40 rfl rfl rfl 

noncomputable def Ns252p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns252p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns252p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns252p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns252p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns252p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns252p25 Ns252p26 Ns252p42 Ns252p43 9945 Ns252p44 Ns252p45 65835 Ns252p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns252p42 Ns252p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns252p44 Ns252p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS253to264.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns252p41 Ns252p25 1 Ns252p26 := Ns252p46 rfl 

noncomputable def Ns252p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns252p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS253to264.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns252p47 Ns252p25 1 Ns252p48 := BSN.pi_combine Ns252p24 Ns252p41 Ns252p25 Ns252p26 Ns252p48 Ns252p47 rfl rfl rfl rfl RS253to264.d14 RS253to264.d15 

theorem RS253to264.d17 : Enclosure.Real.IsNear Real.pi Bool.false 7074237752028440 2251799813685248 1 2251799813685248 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns252p47 Ns252p25 1 Ns252p48 7074237752028440 2251799813685248 1 2251799813685248 RS253to264.d16 rfl 

noncomputable def Ns252p49 := nat_lit 147443727375074537121690809726715087890625 

noncomputable def Ns252p50 := nat_lit 22889945643899497138335355216896171420000 

noncomputable def Ns252p51 := nat_lit 355592320898650075318906513310625 

noncomputable def Ns252p52 := BSN.log_dyadic_bound 3 5 17 16 Ns252p49 8388608 3240000 Ns252p50 Ns252p51 11629079 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 3) (BSN.artanhQ 5) 0 16 Ns252p50 Ns252p49 Ns252p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS253to264.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 11629079 8388608 1 3240000 := BSN.isNear_log_sfrac 4 1 11629079 8388608 1 3240000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 11629079 8388608 3240000 rfl rfl rfl (Ns252p52 rfl)) 

theorem RS253to264.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 186065264 134217728 42 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 11629079 8388608 1 3240000 186065264 134217728 42 134217728 RS253to264.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns252p53 := @Enclosure.Real.IsNear.inv_image qz325 33554433 16777216 1 16777216 4194303 4194304 8388608 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 33554433 16777216 1 16777216 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 33554433 16777216 1 16777216 33554433 16777216 1 16777216 (BSN.sqrt_enclosure 4 1 16777216 16777217 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS253to264.d20 : Enclosure.Real.IsNear qz327 Bool.false 8388607 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 8388607 16777216 1 16777216 8388607 16777216 1 16777216 (Ns252p53 rfl rfl) rfl 

theorem RS253to264.d21 : Enclosure.Real.IsNear qz327 Bool.false 67108856 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 8388607 16777216 1 16777216 67108856 134217728 8 134217728 RS253to264.d20 rfl 

noncomputable def Ns252p54 := nat_lit 159424323765613091421820433543167414255940625 

noncomputable def Ns252p55 := nat_lit 33013339099500162583200499609923570567289500 

noncomputable def Ns252p56 := nat_lit 351657888879851162997374110924800000 

noncomputable def Ns252p57 := nat_lit 2289063575687431840984260 

noncomputable def Ns252p58 := nat_lit 3325435793429257756623375 

noncomputable def Ns252p59 := BSN.log_dyadic_bound 2 3 21 20 Ns252p54 8388608 3240000 Ns252p55 Ns252p56 13500943 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 20 10 9927050056596826020 47940881637414340575 686533194547200 Ns252p57 Ns252p58 512222703392784384000 Ns252p55 Ns252p54 Ns252p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 10 20 Ns252p57 Ns252p58 512222703392784384000 rfl rfl rfl rfl)) rfl rfl 

theorem RS253to264.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 13500943 8388608 1 3240000 := BSN.isNear_log_sfrac 5 1 13500943 8388608 1 3240000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 13500943 8388608 3240000 rfl rfl rfl (Ns252p59 rfl rfl)) 

theorem RS253to264.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 216015088 134217728 42 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 13500943 8388608 1 3240000 216015088 134217728 42 134217728 RS253to264.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns252p60 := @Enclosure.Real.IsNear.inv_image qz328 37514995 16777216 1 16777216 3751499 3751500 8388608 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 37514995 16777216 1 16777216 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 37514995 16777216 1 16777216 37514995 16777216 1 16777216 (BSN.sqrt_enclosure 5 1 18757497 18757498 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS253to264.d24 : Enclosure.Real.IsNear qz329 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 7502999 16777216 1 16777216 (Ns252p60 rfl rfl) rfl 

theorem RS253to264.d25 : Enclosure.Real.IsNear qz329 Bool.false 60023992 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 60023992 134217728 8 134217728 RS253to264.d24 rfl 

noncomputable def Ns252p61 := BSN.log_dyadic_bound 2 10 5 4 94500000000 8388608 3240000 1291130880 26880 3401287 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz580)

theorem RS253to264.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683410914551 2251799813685248 12500000081 40500000000000000 := BSN.isNear_log_sfrac 6 1 4034683410914551 2251799813685248 12500000081 40500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 541526040612241437360128 302231454903657293676544 1000000006480000 3240000000000000000000 4034683410914551 2251799813685248 12500000081 40500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 3401287 8388608 24973259072661432 36028797018963968 3240000 1000000000000000 rfl rfl rfl rfl (Ns252p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS253to264.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 240485871 134217728 42 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683410914551 2251799813685248 12500000081 40500000000000000 240485871 134217728 42 134217728 RS253to264.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns252p62 := @Enclosure.Real.IsNear.inv_image qz331 41095619 16777216 1 16777216 3424634 3424635 8388608 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 41095619 16777216 1 16777216 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 41095619 16777216 1 16777216 41095619 16777216 1 16777216 (BSN.sqrt_enclosure 6 1 20547809 20547810 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS253to264.d28 : Enclosure.Real.IsNear qz332 Bool.false 6849269 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 6849269 16777216 1 16777216 6849269 16777216 1 16777216 (Ns252p62 rfl rfl) rfl 

theorem RS253to264.d29 : Enclosure.Real.IsNear qz332 Bool.false 54794152 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 6849269 16777216 1 16777216 54794152 134217728 8 134217728 RS253to264.d28 rfl 

noncomputable def Ns252p63 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 8388608 3240000 11010900719820672 5524329195 4694397 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz580)

theorem RS253to264.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 12500000081 40500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 12500000081 40500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 588115238325433934020608 302231454903657293676544 1000000006480000 3240000000000000000000 4381799983422711 2251799813685248 12500000081 40500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 4694397 8388608 24973259072661432 36028797018963968 3240000 1000000000000000 rfl rfl rfl rfl (Ns252p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS253to264.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 261175631 134217728 42 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 12500000081 40500000000000000 261175631 134217728 42 134217728 RS253to264.d30 rfl 

noncomputable abbrev qz334 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns252p64 := @Enclosure.Real.IsNear.inv_image qz334 44388341 16777216 1 16777216 3170595 3170596 8388608 (@Enclosure.Real.IsNear.of_eq qz334 (Real.sqrt qz333) Bool.false 44388341 16777216 1 16777216 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 44388341 16777216 1 16777216 44388341 16777216 1 16777216 (BSN.sqrt_enclosure 7 1 22194170 22194171 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS253to264.d32 : Enclosure.Real.IsNear qz335 Bool.false 6341191 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 6341191 16777216 1 16777216 6341191 16777216 1 16777216 (Ns252p64 rfl rfl) rfl 

theorem RS253to264.d33 : Enclosure.Real.IsNear qz335 Bool.false 50729528 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 6341191 16777216 1 16777216 50729528 134217728 8 134217728 RS253to264.d32 rfl 

noncomputable def Ns252p65 := BSN.log_dyadic_bound 0 16 1 0 1 8388608 3240000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz580)

theorem RS253to264.d34 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 25000000243 81000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 25000000243 81000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false 628472642529000809299968 302231454903657293676544 1000000009720000 3240000000000000000000 9364972152248037 4503599627370496 25000000243 81000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 8388608 24973259072661432 36028797018963968 3240000 1000000000000000 rfl rfl rfl rfl (Ns252p65 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS253to264.d35 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 279097919 134217728 42 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 25000000243 81000000000000000 279097919 134217728 42 134217728 RS253to264.d34 rfl 

noncomputable abbrev qz337 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns252p66 := @Enclosure.Real.IsNear.inv_image qz337 47453133 16777216 1 16777216 2965820 2965821 8388608 (@Enclosure.Real.IsNear.of_eq qz337 (Real.sqrt qz336) Bool.false 47453133 16777216 1 16777216 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 47453133 16777216 1 16777216 47453133 16777216 1 16777216 (BSN.sqrt_enclosure 8 1 23726566 23726567 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz338 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS253to264.d36 : Enclosure.Real.IsNear qz338 Bool.false 5931641 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 5931641 16777216 1 16777216 5931641 16777216 1 16777216 (Ns252p66 rfl rfl) rfl 

theorem RS253to264.d37 : Enclosure.Real.IsNear qz338 Bool.false 47453128 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 5931641 16777216 1 16777216 47453128 134217728 8 134217728 RS253to264.d36 rfl 

noncomputable def Ns252p67 := BSN.log_dyadic_bound 1 17 3 2 1252815 8388608 3240000 1448 3 988035 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz734 := (Enclosure.sfrac Bool.false 9 1)

noncomputable abbrev qz581 := qz734

noncomputable abbrev qz339 := qz581

noncomputable abbrev qz1 := qz339

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz580)

theorem RS253to264.d38 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 9895419403785957 4503599627370496 25000000243 81000000000000000 := BSN.isNear_log_sfrac 9 1 9895419403785957 4503599627370496 25000000243 81000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz340) Bool.false 664070354991632873422848 302231454903657293676544 1000000009720000 3240000000000000000000 9895419403785957 4503599627370496 25000000243 81000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 988035 8388608 24973259072661432 36028797018963968 3240000 1000000000000000 rfl rfl rfl rfl (Ns252p67 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS253to264.d39 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 294906479 134217728 42 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 9895419403785957 4503599627370496 25000000243 81000000000000000 294906479 134217728 42 134217728 RS253to264.d38 rfl 

noncomputable abbrev qz341 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns252p68 := @Enclosure.Real.IsNear.inv_image qz341 50331649 16777216 1 16777216 2796202 2796203 8388608 (@Enclosure.Real.IsNear.of_eq qz341 (Real.sqrt qz340) Bool.false 50331649 16777216 1 16777216 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz340) Bool.false 50331649 16777216 1 16777216 50331649 16777216 1 16777216 (BSN.sqrt_enclosure 9 1 25165824 25165825 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz342 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS253to264.d40 : Enclosure.Real.IsNear qz342 Bool.false 5592405 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz342 Bool.false 5592405 16777216 1 16777216 5592405 16777216 1 16777216 (Ns252p68 rfl rfl) rfl 

theorem RS253to264.d41 : Enclosure.Real.IsNear qz342 Bool.false 44739240 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz342 Bool.false 5592405 16777216 1 16777216 44739240 134217728 8 134217728 RS253to264.d40 rfl 

theorem RS253to264.d42 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz735 := (@instHMul Real Real.instMul)

noncomputable abbrev qz582 := (@HMul.hMul Real Real Real qz735 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz343 := qz582

noncomputable abbrev qz2 := qz343

theorem RS253to264.d43 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS253to264.d42 rfl 

noncomputable abbrev qz344 := (@Inv.inv Real Real.instInv qz582)

noncomputable abbrev qz3 := qz344

theorem RS253to264.d44 : Enclosure.Real.IsNear qz3 Bool.false 2670177 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 2670177 16777216 1 16777216 2670177 16777216 1 16777216 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 1335088 1335089 8388608 RS253to264.d43 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns252p69 := nat_lit 29883725399409473617920000 

noncomputable def Ns252p70 := nat_lit 18535391291991780304869130240 

noncomputable abbrev qz736 := (Enclosure.sfrac Bool.false 548874 1000)

noncomputable abbrev qz583 := qz736

noncomputable abbrev qz345 := qz583

noncomputable abbrev qz4 := qz345

noncomputable abbrev qz584 := qz735

noncomputable abbrev qz346 := qz584

noncomputable abbrev qz5 := qz346

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 9)

noncomputable abbrev qz7 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz737 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 548874 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz585 := qz737

noncomputable abbrev qz347 := qz585

noncomputable abbrev qz8 := qz347

noncomputable abbrev qz9 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz738 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 548874 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz586 := qz738

noncomputable abbrev qz348 := qz586

noncomputable abbrev qz10 := qz348

noncomputable abbrev qz587 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz8 qz9))

noncomputable def Ns252p71 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (@HMul.hMul Real Real Real qz5 qz587 (Zeta.RiemannSiegel.correction qz10)) 33732965 16777216 94099 67108864 82077778487507992365 590295810358705651712 433011210172049578897 Ns252p69 Ns252p70 

noncomputable def Ns252p72 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 548874 1000 120 161 134217728 67108864 2251799813685248 Bool.false 127762055282 1819 

noncomputable def Ns252p73 := Ns252p72 279097919 42 47453128 8 294906479 42 44739240 8 Bool.true 120672718 76995 Bool.true 128090215 Bool.true 161020497 7074237752028440 1 Bool.false 77596921 Bool.false Bool.false 125081386 Bool.true Bool.true 134931860 

noncomputable def Ns252p74 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 548874 1000 20 73 134217728 67108864 2251799813685248 Bool.false 127762055282 1819 

noncomputable def Ns252p75 := Ns252p74 240485871 42 54794152 8 261175631 42 50729528 8 Bool.true 124421695 57421 Bool.true 17812394 Bool.true 199961875 7074237752028440 1 Bool.false 133037496 Bool.false Bool.false 133778055 Bool.true Bool.true 120672718 

noncomputable def Ns252p76 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 548874 1000 121 43 134217728 67108864 2251799813685248 Bool.false 127762055282 1819 

noncomputable def Ns252p77 := Ns252p76 186065264 42 67108856 8 216015088 42 60023992 8 Bool.true 120260536 33842 Bool.false 125395159 Bool.false 131355163 7074237752028440 1 Bool.false 107932989 Bool.true Bool.false 111368104 Bool.false Bool.true 124421695 

noncomputable def Ns252p78 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 548874 1000 363 222 134217728 67108864 2251799813685248 Bool.false 127762055282 1819 

noncomputable def Ns252p79 := Ns252p78 93032624 42 94906264 8 147453232 42 77490640 16 Bool.true 134217648 1866 Bool.false 168043586 Bool.false 24835483 7074237752028440 1 Bool.false 127455885 Bool.false Bool.false 131926513 Bool.true Bool.true 120260536 

noncomputable def Ns252p80 := nat_lit 45787702277186514743580927052678575110152631552796229 

noncomputable def Ns252p81 := nat_lit 48101303289276098636956409809811099844368505241600 

noncomputable def Ns252p82 := nat_lit 23911424232963014699627688299520000 

noncomputable def Ns252p83 := nat_lit 78746184881944807372312004788600442880 

noncomputable abbrev qz349 := (@Eq.refl Real qz583)

noncomputable abbrev qz11 := qz349

noncomputable def Ns252p84 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 548874 1000 1205051671504 16000000 1097748 4000 2000 Ns252p82 Ns252p83 qz11 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns252p85 := nat_lit 8439589283731018397536836474349714964303333047811400929280 

noncomputable abbrev qz739 := (@instHSub Real Real.instSub)

noncomputable abbrev qz588 := qz739

noncomputable abbrev qz350 := qz588

noncomputable abbrev qz589 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz740 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz741 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz590 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1097748))))

noncomputable abbrev qz351 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 548874 4000) (Real.log (Enclosure.sfrac Bool.false 1205051671504 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz590))

noncomputable abbrev qz591 := (Enclosure.sfrac Bool.false 548874 2000)

noncomputable abbrev qz12 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz351 qz591) (@HMul.hMul Real Real Real qz346 qz591 (Real.log Real.pi)))

noncomputable def Ns252p86 := @Enclosure.Real.IsNear.addLit_ft_p qz12 (Enclosure.sfrac Bool.true Ns252p82 Ns252p83) 107174614091724821281 112589990684262400 1123886741732728849 82944000000000000000000 Ns252p82 Ns252p83 0 1 Ns252p85 

noncomputable def Ns252p87 := nat_lit 17980916503335111391927336960000 

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz350 qz351 qz591)

noncomputable def Ns252p88 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (@HMul.hMul Real Real Real qz5 qz591 (Real.log Real.pi)) 712727308182548471717 562949953421312000 435057990345301 81000000000000000000 10541334016557 33554432000 274437 33554432000 Ns252p87 107174614091724821281 112589990684262400 

noncomputable def Ns252p89 := nat_lit 1425454616365096943434000 

noncomputable abbrev qz14 := qz351

noncomputable def Ns252p90 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz591 867221604549633073061 562949953421312000 435057990345301 81000000000000000000 548874 2000 0 1 Ns252p89 712727308182548471717 562949953421312000 435057990345301 81000000000000000000 

noncomputable def Ns252p91 := nat_lit 1952809447548685573211802101641904128 

noncomputable def Ns252p92 := nat_lit 27151130259051453691723776 

noncomputable def Ns252p93 := nat_lit 2417851639229258349412352 

noncomputable def Ns252p94 := nat_lit 13755687418178569511816673806614745867096718904749511881169592310902638510080 

noncomputable def Ns252p95 := nat_lit 22169151745926196259469608393878508788096150934283169911346859983100706816 

noncomputable def Ns252p96 := nat_lit 220177128214567092901161187574106825689726141239950990480143485501440 

noncomputable def Ns252p97 := BSN.log_dyadic_bound 156475671504 2253627671504 4 3 Ns252p94 67108864 25920000 Ns252p95 Ns252p96 9334131 2410103343008 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 156475671504) (BSN.artanhQ 2253627671504) 0 3 Ns252p95 Ns252p94 Ns252p96 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz352 := (Real.log (Enclosure.sfrac Bool.false 1205051671504 16000000))

noncomputable abbrev qz353 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns252p98 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 548874 4000) qz352 548874 4000 0 1 3160807567072503 281474976710656 195312581 5062500000000000 867442546284676505811 562949953421312000 5955666532433 1125000000000000000 (Enclosure.Real.IsNear.const Bool.false 548874 4000) (BSN.isNear_log_sfrac 1205051671504 16000000 3160807567072503 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1205051671504) qz353)) Bool.false Ns252p92 Ns252p93 1000000414720000 25920000000000000000000 3160807567072503 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1205051671504 16000000 16 2410103343008 2097152000000 9334131 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns252p97 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p99 := BSN.arctan_dyadic_bound_f 1000 1097748 1 0 8388608 3240000 0 1 1 0 1 1 7641 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1097748) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1097748) 0 0 rfl) rfl rfl rfl 

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

noncomputable abbrev qz357 := (@Nat.cast Real Real.instNatCast 1097748)

noncomputable def Ns252p100 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 qz357)) 884279719003555 562949953421312 1 2000000000000000 7641 8388608 1 3240000 7413574424476881256448 883766940173731 562949953421312 50000000081 162000000000000000 qz17 (Ns252p99 rfl) rfl rfl 

noncomputable abbrev qz358 := (@HMul.hMul Real Real Real qz584 qz589 qz590)

noncomputable abbrev qz18 := qz358

noncomputable abbrev qz359 := qz589

noncomputable abbrev qz19 := qz359

noncomputable abbrev qz360 := qz590

noncomputable abbrev qz20 := qz360

noncomputable abbrev qz361 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns252p101 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 548874 4000) qz352) qz18 867442546284676505811 562949953421312000 5955666532433 1125000000000000000 883766940173731 2251799813685248 50000000081 648000000000000000 Ns252p91 867221604549633073061 562949953421312000 435057990345301 81000000000000000000 (Ns252p98 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz20 1 4 0 1 883766940173731 562949953421312 50000000081 162000000000000000 883766940173731 2251799813685248 50000000081 648000000000000000 qz361 Ns252p100 rfl) 

noncomputable def Ns252p102 := @Ns252p86 Ns252p80 Ns252p81 1123886741732728849 82944000000000000000000 (@Ns252p88 1123886741732728849 82944000000000000000000 (Ns252p90 (Ns252p101 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 548874 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz591 (Real.log Real.pi) 548874 2000 0 1 38410761 33554432 1 33554432 10541334016557 33554432000 274437 33554432000 (Enclosure.Real.IsNear.const Bool.false 548874 2000) RS253to264.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns252p82 Ns252p83) 

noncomputable abbrev qz362 := (@instHAdd Real Real.instAdd)

noncomputable def Ns252p103 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns252p80 Ns252p81 1123886741732728849 82944000000000000000000 7985128455 8388608 57 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz362 qz12 (Enclosure.sfrac Bool.true Ns252p82 Ns252p83)) Bool.false Ns252p80 Ns252p81 1123886741732728849 82944000000000000000000 Ns252p84 (Ns252p102 rfl rfl)) 

noncomputable def Ns252p104 := nat_lit 1897665827201046083010560 

noncomputable def Ns252p105 := nat_lit 1208925819614629174706176 

noncomputable def Ns252p106 := nat_lit 854769369398734312921280684588850349925409102529696185035750737431467029415560652346223068683388200429519321493640391779688739499933696 

noncomputable def Ns252p107 := nat_lit 16860812360175734222210805034837902731874731588140993779854824115686058269364094835627812361599730584878593258197117225559879026789580800 

noncomputable def Ns252p108 := nat_lit 605953342000942837785379445736040135471537552969865835721431678148449498220425768387372448669423901743986506061968975727790391296 

noncomputable def Ns252p109 := nat_lit 4268550686132728575591869008600187210756255828917807709267711870013340427391674528409171239889235871334348366362560515218503999795757056 

noncomputable def Ns252p110 := nat_lit 590128432606150697777378176219326595615615605584934782294918844049012039427743319246973432655990570470750764036899102894595765937635328000 

noncomputable abbrev qz363 := (BSN.sinEvenQ 34359738368)

noncomputable abbrev qz364 := (BSN.sinOddQ 34359738368)

noncomputable def Ns252p111 := BSN.sin_dyadic_bound_f 53934906736 34359738368 4 3 16777216 6486329 Ns252p106 Ns252p107 Ns252p108 Ns252p109 Ns252p110 Ns252p108 16777206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53934906736) qz363 0 3 Ns252p106 Ns252p107 Ns252p108 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53934906736) qz364 0 3 Ns252p109 Ns252p110 Ns252p108 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz365 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable abbrev qz366 := (@Nat.cast Real Real.instNatCast Ns252p105)

noncomputable def Ns252p112 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7985128455) qz365) Bool.false 7985128455 8388608 57 4194304 Bool.true 16777206 16777216 1 3240000 (Ns252p103 rfl) (Enclosure.sfrac_false_div 7985128455 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7985128455) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns252p104) qz366) 226375608064910080 72057594037927936 Bool.false 16777206 16777216 151 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 7985128455 8388608 226375608064910080 72057594037927936 151 Ns252p104 Ns252p105 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777206 16777216 Ns252p104 Ns252p105 53934906736 34359738368 6486329 6480000 (Ns252p111 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p113 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns252p80 Ns252p81 1123886741732728849 82944000000000000000000 127762055282 134217728 1819 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz362 qz12 (Enclosure.sfrac Bool.true Ns252p82 Ns252p83)) Bool.false Ns252p80 Ns252p81 1123886741732728849 82944000000000000000000 Ns252p84 (Ns252p102 rfl rfl)) 

noncomputable def Ns252p114 := Ns252p79 33842 BSN.abs_quadSignPos (BSN.cos_quad_nat3 363 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 127455885 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 222 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 131926513 134217728) qz11 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 8388603 8388608 2951161 212336640000 134217648 134217728 1866 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 8388603 8388608 2951161 212336640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 16777206 16777216 188874304 13589544960000 8388603 8388608 2951161 212336640000 (Ns252p112 rfl rfl) rfl)) rfl) (Ns252p113 rfl) RS253to264.d7 

noncomputable def Ns252p115 := nat_lit 783180448717097377320088424508374891070144733242839640168447573295360 

noncomputable def Ns252p116 := nat_lit 38215724400686031908940493885850326479880652218951261491964367528263680 

noncomputable def Ns252p117 := nat_lit 635880526916682820984591885316259273716794045237969214986533273856 

noncomputable def Ns252p118 := nat_lit 2050157368644056596985304153517136485407218539562766155045479733330176 

noncomputable def Ns252p119 := nat_lit 700621614012577251663909054573922652131145290680773127352680071351500800 

noncomputable abbrev qz367 := (BSN.sinEvenQ 134217728)

noncomputable abbrev qz368 := (BSN.sinOddQ 134217728)

noncomputable def Ns252p120 := BSN.sin_dyadic_bound_f 168043586 134217728 3 2 134217728 67108864 Ns252p115 Ns252p116 Ns252p117 Ns252p118 Ns252p119 Ns252p117 127455885 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 168043586) qz367 0 2 Ns252p115 Ns252p116 Ns252p117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 168043586) qz368 0 2 Ns252p118 Ns252p119 Ns252p117 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p121 := nat_lit 380443739865759585303406337521 

noncomputable def Ns252p122 := nat_lit 7788445287802241442795744493830144 

noncomputable def Ns252p123 := nat_lit 116826679317033621641936167407452160 

noncomputable abbrev qz369 := (BSN.cosEvenQ 134217728)

noncomputable abbrev qz370 := (BSN.cosOddQ 134217728)

noncomputable def Ns252p124 := BSN.cos_dyadic_bound_f 24835483 134217728 2 1 134217728 67108864 Ns252p121 Ns252p122 Ns252p121 Ns252p121 Ns252p123 Ns252p121 131926513 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 24835483) qz369 0 1 Ns252p121 Ns252p122 Ns252p121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 24835483) qz370 0 1 Ns252p121 Ns252p123 Ns252p121 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p125 := nat_lit 242691074192397457224076573355025786178340360787775517981638630307905 

noncomputable def Ns252p126 := nat_lit 61128841288909300473074056351450362181940893238444209086808979521 

noncomputable def Ns252p127 := nat_lit 635520509522763677671815572219546139404501612045597446946722531506241 

noncomputable def Ns252p128 := BSN.sin_dyadic_bound_f 125395159 134217728 3 2 134217728 67108864 Ns252p125 Ns252p116 Ns252p126 Ns252p127 Ns252p119 Ns252p126 107932989 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 125395159) qz367 0 2 Ns252p125 Ns252p116 Ns252p126 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 125395159) qz368 0 2 Ns252p127 Ns252p119 Ns252p126 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p129 := nat_lit 292241332617698189969757708182438077273801121509610969645877485332705 

noncomputable def Ns252p130 := nat_lit 88629271886933151176678774672727643406979592952189122153960401121 

noncomputable def Ns252p131 := nat_lit 765250471368059272437936517699772452865867827469915661922382239983841 

noncomputable def Ns252p132 := BSN.sin_dyadic_bound_f 131355163 134217728 3 2 134217728 67108864 Ns252p129 Ns252p116 Ns252p130 Ns252p131 Ns252p119 Ns252p130 111368104 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 131355163) qz367 0 2 Ns252p129 Ns252p116 Ns252p130 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 131355163) qz368 0 2 Ns252p131 Ns252p119 Ns252p130 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p133 := Ns252p77 57421 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 121 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 107932989 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 43 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 111368104 134217728) qz11 rfl rfl (Ns252p114 RS253to264.d9 RS253to264.d11 RS253to264.d13 RS253to264.d17 (Ns252p120 rfl rfl) (Ns252p124 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns252p113 rfl) RS253to264.d19 RS253to264.d21 RS253to264.d23 RS253to264.d25 RS253to264.d17 (Ns252p128 rfl rfl) (Ns252p132 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns252p134 := nat_lit 100667474101834347171486247696 

noncomputable def Ns252p135 := BSN.cos_dyadic_bound_f 17812394 134217728 2 1 134217728 67108864 Ns252p134 Ns252p122 Ns252p134 Ns252p134 Ns252p123 Ns252p134 133037496 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 17812394) qz369 0 1 Ns252p134 Ns252p122 Ns252p134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 17812394) qz370 0 1 Ns252p134 Ns252p123 Ns252p134 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p136 := nat_lit 8751330864773774179709953254530546358236200698283109435394281513254324101302329867665844907907867431640625 

noncomputable def Ns252p137 := nat_lit 212813371219357667808056223692308629509040396751503069069405487845990478953701519077062806287447472524492800 

noncomputable def Ns252p138 := nat_lit 4086640217200698906790613262587266903584120237877795998128959518854941279641934670507907867431640625 

noncomputable def Ns252p139 := nat_lit 43712641221891307466703181906717023710283802488181850271407776334864663422746530770590542507907867431640625 

noncomputable def Ns252p140 := nat_lit 7448467992677518373281967829230802032816413886302607417429192074609666763379553167697198220060661538357248000 

noncomputable def Ns252p141 := BSN.sin_dyadic_bound_f 199961875 134217728 4 3 134217728 67108864 Ns252p136 Ns252p137 Ns252p138 Ns252p139 Ns252p140 Ns252p138 133778055 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 199961875) qz367 0 3 Ns252p136 Ns252p137 Ns252p138 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 199961875) qz368 0 3 Ns252p139 Ns252p140 Ns252p138 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p142 := Ns252p75 76995 BSN.abs_quadSignPos (BSN.cos_quad_nat0 20 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133037496 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 73 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133778055 134217728) qz11 rfl rfl (Ns252p133 rfl rfl) (Ns252p113 rfl) RS253to264.d27 RS253to264.d29 RS253to264.d31 RS253to264.d33 RS253to264.d17 (Ns252p135 rfl rfl) (Ns252p141 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p143 := nat_lit 146834130483055506045783924428791692794214103280934718677085896690625 

noncomputable def Ns252p144 := nat_lit 4246191600076225767660054876205591831097850246550140165773818614251520 

noncomputable def Ns252p145 := nat_lit 72464889940699533473360228336003782365125020192701031752187890625 

noncomputable def Ns252p146 := nat_lit 440357461669285119070405052829703070817912059802418753967753314290625 

noncomputable def Ns252p147 := nat_lit 191078622003430159544702469429251632399403261094756307459821837641318400 

noncomputable def Ns252p148 := BSN.cos_dyadic_bound_f 128090215 134217728 3 2 134217728 67108864 Ns252p143 Ns252p144 Ns252p145 Ns252p146 Ns252p147 Ns252p145 77596921 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 128090215) qz369 0 2 Ns252p143 Ns252p144 Ns252p145 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 128090215) qz370 0 2 Ns252p146 Ns252p147 Ns252p145 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p149 := nat_lit 660151125865587859758487335805054396692772065115527341588491659972225 

noncomputable def Ns252p150 := nat_lit 451907243198655238916192091012851479012288921344127221126928338561 

noncomputable def Ns252p151 := nat_lit 1728235575063741809933031092294454993705525988477538260088034558807681 

noncomputable def Ns252p152 := BSN.sin_dyadic_bound_f 161020497 134217728 3 2 134217728 67108864 Ns252p149 Ns252p116 Ns252p150 Ns252p151 Ns252p119 Ns252p150 125081386 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 161020497) qz367 0 2 Ns252p149 Ns252p116 Ns252p150 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 161020497) qz368 0 2 Ns252p151 Ns252p119 Ns252p150 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz371 := (BSN.cos_quad_nat1 161 rfl)

noncomputable def Ns252p153 := Ns252p73 94099 BSN.abs_quadSignPos (BSN.cos_quad_nat0 120 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 77596921 134217728) BSN.abs_quadSignNeg qz371 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 125081386 134217728) qz11 rfl rfl (Ns252p142 rfl) (Ns252p113 rfl) RS253to264.d35 RS253to264.d37 RS253to264.d39 RS253to264.d41 RS253to264.d17 (Ns252p148 rfl rfl) (Ns252p152 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p154 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) 134931860 134217728 94099 134217728 134931860 134217728 94099 134217728 36220495368028160 33732965 16777216 94099 67108864 (Ns252p153 rfl) 

noncomputable def Ns252p155 := @Enclosure.Real.IsNear.mulLit_tf qz587 (Zeta.RiemannSiegel.correction qz10) 1371945 4194304 1 8388608 59825851974757 140737488355328 314514584066159 7124835347988480000 82077778487507992365 590295810358705651712 

noncomputable abbrev qz595 := (@HPow.hPow Real Real Real qz7 qz8 qz9)

noncomputable def Ns252p156 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz595 1 1 0 1 1371945 4194304 1 8388608 1371945 4194304 1 8388608 

noncomputable abbrev qz21 := (@Enclosure.Real.IsNear.of_eq qz347 (@HMul.hMul Real Real Real qz346 qz345 qz344) Bool.false 732795365349 8388608000 274437 8388608000 (BSN.t_div_two_pi_mk qz345 548874 1000 qz349) (@Enclosure.Real.IsNear.mulLit_ff qz345 qz344 548874 1000 0 1 2670177 16777216 1 16777216 732795365349 8388608000 274437 8388608000 (Enclosure.Real.IsNear.const Bool.false 548874 1000) RS253to264.d44 rfl))

noncomputable def Ns252p157 := @Enclosure.Real.IsNear.sqrt_image qz8 732795365349 8388608000 274437 8388608000 78403639 78403670 8388608 qz21 

noncomputable abbrev qz743 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 548874 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz596 := qz743

noncomputable abbrev qz372 := qz596

noncomputable abbrev qz22 := qz372

noncomputable def Ns252p158 := @Enclosure.Real.IsNear.sqrt_image qz22 156807309 16777216 31 16777216 25645611 25645617 8388608 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 156807309 16777216 31 16777216 156807309 16777216 31 16777216 (Ns252p157 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz597 := (Real.sqrt qz743)

noncomputable abbrev qz373 := qz597

noncomputable abbrev qz23 := qz373

noncomputable def Ns252p159 := @Enclosure.Real.IsNear.inv_image qz23 12822807 4194304 3 8388608 2743889 2743891 8388608 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 51291228 16777216 6 16777216 12822807 4194304 3 8388608 (Ns252p158 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns252p160 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz23) Bool.false 5487780 16777216 2 16777216 1371945 4194304 1 8388608 (Ns252p159 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz374 := (@HMul.hMul Real Real Real qz584 qz582 qz586)

noncomputable abbrev qz24 := (Real.cos qz374)

noncomputable abbrev qz598 := (@HMul.hMul Real Real Real qz735 qz738 qz738)

noncomputable abbrev qz599 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz375 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz598 qz586) qz599)

noncomputable abbrev qz25 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz375))

noncomputable def Ns252p161 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz10) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz24) qz25) Bool.false 59825851974757 

noncomputable def Ns252p162 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz24) qz25 29456251 16777216 621 

noncomputable abbrev qz26 := (@Neg.neg Real Real.instNeg (Real.cos qz374))

noncomputable def Ns252p163 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz24) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz26)) Bool.true 29456251 16777216 621 16777216 (BSN.inv_eq_neg_inv_neg qz24) 

noncomputable def Ns252p164 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz26) Bool.false 29456251 16777216 621 16777216 29456251 16777216 

noncomputable def Ns252p165 := @Enclosure.Real.IsNear.recentre' qz24 Bool.true 9555696 16777216 162954304 13589544960000 597231 1048576 2546161 212336640000 

noncomputable abbrev qz27 := qz374

noncomputable def Ns252p166 := @Enclosure.Real.IsNear.cos_image qz27 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18260083) qz365) Bool.false 18260083 8388608 49 4194304 Bool.true 9555696 16777216 1 

noncomputable def Ns252p167 := nat_lit 836568337730293244285068057 

noncomputable def Ns252p168 := nat_lit 72057594037927936000000000000000 

noncomputable def Ns252p169 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz10 884279719003555 140737488355328 1 500000000000000 5812365 16777216 31 16777216 5139756488946097957575 2361183241434822606848 Ns252p167 

noncomputable def Ns252p170 := @Enclosure.Real.IsNear.subLit_ff_p qz22 qz1 156807309 16777216 31 16777216 9 1 0 1 5812365 5812365 16777216 31 

noncomputable abbrev qz376 := (Enclosure.Real.IsNear.const Bool.false 9 1)

noncomputable def Ns252p171 := @Ns252p170 16777216 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 156807309 16777216 31 16777216 156807309 16777216 31 16777216 (Ns252p157 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns252p172 := @Enclosure.Real.IsNear.recentre' qz27 Bool.false 5139756488946097957575 2361183241434822606848 Ns252p167 Ns252p168 18260083 8388608 49 4194304 (@Ns252p169 Ns252p168 RS253to264.d43 (Ns252p171 rfl rfl) rfl) 

noncomputable def Ns252p173 := nat_lit 187939808794350110923808059064654952488401 

noncomputable def Ns252p174 := nat_lit 167255588988979673561517887044862711294853120 

noncomputable def Ns252p175 := nat_lit 1170789122922857714930625209314038979063971840 

noncomputable def Ns252p176 := BSN.sin_dyadic_bound_f 20821149149 34359738368 2 1 16777216 6486329 Ns252p173 Ns252p174 Ns252p173 Ns252p173 Ns252p175 Ns252p173 9555696 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 20821149149) qz363 0 1 Ns252p173 Ns252p174 Ns252p173 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 20821149149) qz364 0 1 Ns252p173 Ns252p175 Ns252p173 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p177 := @Ns252p166 3240000 (Ns252p172 rfl) (Enclosure.sfrac_false_div 18260083 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18260083) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 732579059007569302388736) qz366) 226375608064910080 72057594037927936 Bool.false 9555696 16777216 0 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 18260083 8388608 226375608064910080 72057594037927936 0 732579059007569302388736 Ns252p105 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 9555696 16777216 732579059007569302388736 Ns252p105 20821149149 34359738368 6486329 6480000 (Ns252p176 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p178 := @Enclosure.Real.IsNear.inv_image qz26 597231 1048576 2546161 212336640000 14727815 14728436 8388608 (@Enclosure.Real.IsNear.neg qz24 Bool.true 597231 1048576 2546161 212336640000 (Ns252p165 (Ns252p177 rfl rfl) rfl)) 

noncomputable def Ns252p179 := Ns252p163 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz26) Bool.false 29456251 16777216 621 16777216 (@Ns252p164 621 16777216 (Ns252p178 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p180 := @Enclosure.Real.IsNear.recentre' qz25 Bool.true 2031007 8388608 

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz346 qz343 qz375)

noncomputable abbrev qz377 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable def Ns252p181 := @Enclosure.Real.IsNear.cos_image qz28 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7614093)) qz377) Bool.true 7614093 4194304 

noncomputable def Ns252p182 := nat_lit 71913077409591553356706095205 

noncomputable def Ns252p183 := nat_lit 39614081257132168796771975168 

noncomputable def Ns252p184 := nat_lit 23760194686424538702040968911636881 

noncomputable def Ns252p185 := @Enclosure.Real.IsNear.recentre' qz28 Bool.true Ns252p182 Ns252p183 Ns252p184 

noncomputable def Ns252p186 := nat_lit 1208925819614629174706176000000000000000 

noncomputable abbrev qz29 := qz375

noncomputable def Ns252p187 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz29 884279719003555 140737488355328 1 500000000000000 81323902227031 

noncomputable abbrev qz378 := (@HSub.hSub Real Real Real qz588 qz598 qz586)

noncomputable abbrev qz30 := qz378

noncomputable abbrev qz379 := qz599

noncomputable abbrev qz31 := qz379

noncomputable def Ns252p188 := @Enclosure.Real.IsNear.subLit_tf qz30 qz31 63731716182615 281474976710656 880461287 281474976710656 1 16 

noncomputable abbrev qz380 := qz598

noncomputable abbrev qz32 := qz380

noncomputable def Ns252p189 := @Enclosure.Real.IsNear.subLit_ff_n qz32 qz10 33783586893225 281474976710656 360367591 281474976710656 5812365 16777216 31 16777216 

noncomputable def Ns252p190 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz10 5812365 16777216 31 16777216 5812365 16777216 31 16777216 33783586893225 281474976710656 

noncomputable def Ns252p191 := nat_lit 6466638848700626044203585817228022310825805090492438334296946808520312464295858650511281 

noncomputable def Ns252p192 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600 

noncomputable def Ns252p193 := nat_lit 37968035313777335990748198491416487808185660279155175791375189232117431203978311601 

noncomputable def Ns252p194 := nat_lit 39062768904876552678337969986609114114760972763416424150378094094446684242755955597277105 

noncomputable def Ns252p195 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600 

noncomputable def Ns252p196 := BSN.cos_dyadic_bound_t 7614093 4194304 4 3 8388608 3240000 Ns252p191 Ns252p192 Ns252p193 Ns252p194 Ns252p195 Ns252p193 2031007 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 7614093) (BSN.cosEvenQ 4194304) 0 3 Ns252p191 Ns252p192 Ns252p193 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 7614093) (BSN.cosOddQ 4194304) 0 3 Ns252p194 Ns252p195 Ns252p193 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz381 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns252p197 := @Ns252p180 1089217216 54358179840000 2031007 8388608 17019019 849346560000 (@Ns252p181 331 16777216 Bool.true 2031007 8388608 1 3240000 (@Ns252p185 Ns252p186 7614093 4194304 331 16777216 (@Ns252p187 281474976710656 880461287 281474976710656 Ns252p182 Ns252p183 Ns252p184 Ns252p186 RS253to264.d43 (@Ns252p188 0 1 1301182435632496 81323902227031 281474976710656 880461287 281474976710656 (@Ns252p189 1069240768446427299840 63731716182615 281474976710656 880461287 281474976710656 (@Ns252p190 360367591 281474976710656 (Ns252p171 rfl rfl) (Ns252p171 rfl rfl) rfl) (Ns252p171 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7614093 4194304) (BSN.cos_neg_of_bound 7614093 4194304 Bool.true 2031007 8388608 1 3240000 (Ns252p196 rfl rfl)) rfl rfl) 

noncomputable abbrev qz33 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 9) (Enclosure.sfrac Bool.true 1 1) Bool.true 1 1 0 1 (BSN.neg_one_pow_odd_mk 9 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1))

noncomputable def Ns252p198 := @Ns252p155 433011210172049578897 Ns252p69 (Ns252p156 qz33 (@Enclosure.Real.IsNear.of_eq qz595 (@Inv.inv Real Real.instInv qz23) Bool.false 1371945 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz8 (BSN.t_div_two_pi_nonneg qz4 548874 1000 qz11)) Ns252p160) rfl) (@Ns252p161 140737488355328 314514584066159 7124835347988480000 (BSN.correction_mk qz10 (BSN.cos_two_pi_p_ne_zero_mk qz4 548874 1000 9 qz11 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 548874 1000 9 qz11 rfl rfl rfl))) (@Ns252p162 16777216 2031007 8388608 17019019 849346560000 59825851974757 140737488355328 314514584066159 7124835347988480000 Ns252p179 (Ns252p197 rfl) rfl)) 

noncomputable abbrev qz34 := qz350

noncomputable def Ns252p199 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 1104795413732038754515 590295810358705651712 42335503798320048298897 Ns252p69 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (@HMul.hMul Real Real Real qz5 qz587 (Zeta.RiemannSiegel.correction qz10))) Bool.true 1104795413732038754515 590295810358705651712 42335503798320048298897 Ns252p69 (BSN.hardyZApproximantRS₀_eq qz4 9 (@BSN.floor_sqrt_eq_dec qz4 548874 1000 9 qz11 rfl rfl rfl)) (@Ns252p71 1104795413732038754515 590295810358705651712 42335503798320048298897 Ns252p69 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 9)) Bool.true 33732965 16777216 94099 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 9) (Ns252p154 (Ns252p153 rfl) rfl rfl)) (Ns252p198 rfl) rfl rfl)) 

theorem RS253to264.d45 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 1104795413732038754515 590295810358705651712 42335503798320048298897 Ns252p69 := Ns252p199 

theorem RS253to264.d46 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS253to264.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS253to264.d3 a b h)) 

noncomputable def Ns252p200 := nat_lit 19922483599606315745280000 

noncomputable def Ns252p201 := nat_lit 156062348598532000642037186560 

noncomputable abbrev qz744 := (Enclosure.sfrac Bool.false 550280 1000)

noncomputable abbrev qz600 := qz744

noncomputable abbrev qz382 := qz600

noncomputable abbrev qz35 := qz382

noncomputable abbrev qz745 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 550280 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz601 := qz745

noncomputable abbrev qz383 := qz601

noncomputable abbrev qz36 := qz383

noncomputable abbrev qz746 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 550280 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz602 := qz746

noncomputable abbrev qz384 := qz602

noncomputable abbrev qz37 := qz384

noncomputable abbrev qz603 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz36 qz9))

noncomputable def Ns252p202 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) (@HMul.hMul Real Real Real qz5 qz603 (Zeta.RiemannSiegel.correction qz37)) 123007277 67108864 23587 16777216 161543310956156994683 1180591620717411303424 254481703302600164039 Ns252p200 Ns252p201 

noncomputable def Ns252p203 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 550280 1000 120 161 134217728 67108864 2251799813685248 Bool.false 128183942294 1825 

noncomputable def Ns252p204 := Ns252p203 279097919 42 47453128 8 294906479 42 44739240 8 Bool.false 128553985 77200 Bool.true 98614877 Bool.true 153771994 7074237752028440 1 Bool.false 99590408 Bool.false Bool.false 122271698 Bool.true Bool.false 123007277 

noncomputable def Ns252p205 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 550280 1000 19 73 134217728 67108864 2251799813685248 Bool.false 128183942294 1825 

noncomputable def Ns252p206 := Ns252p205 240485871 42 54794152 8 261175631 42 50729528 8 Bool.false 125043282 57575 Bool.true 144877231 Bool.true 145287800 7074237752028440 1 Bool.false 118337629 Bool.false Bool.false 118530798 Bool.true Bool.false 128553985 

noncomputable def Ns252p207 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 550280 1000 122 44 134217728 67108864 2251799813685248 Bool.false 128183942294 1825 

noncomputable def Ns252p208 := Ns252p207 186065264 42 67108856 8 216015088 42 60023992 8 Bool.false 124438879 33934 Bool.false 74845695 Bool.false 38696247 7074237752028440 1 Bool.false 113884318 Bool.true Bool.false 128678012 Bool.false Bool.false 125043282 

noncomputable def Ns252p209 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 550280 1000 365 223 134217728 67108864 2251799813685248 Bool.false 128183942294 1825 

noncomputable def Ns252p210 := Ns252p209 93032624 42 94906264 8 147453232 42 77490640 16 Bool.false 134217696 1874 Bool.false 37469300 Bool.false 28574537 7074237752028440 1 Bool.false 36984499 Bool.true Bool.false 28359168 Bool.false Bool.false 124438879 

noncomputable def Ns252p211 := nat_lit 209922752189500461538275621606989747712372201127 

noncomputable def Ns252p212 := nat_lit 219804090512361904223516481967120081276108800 

noncomputable def Ns252p213 := nat_lit 24219255497398245358705664000000000 

noncomputable def Ns252p214 := nat_lit 79964262299604126100718160875520000000 

noncomputable abbrev qz604 := (@Eq.refl Real qz744)

noncomputable abbrev qz385 := qz604

noncomputable abbrev qz38 := qz385

noncomputable def Ns252p215 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz35 550280 1000 1211233313600 16000000 1100560 4000 2000 Ns252p213 Ns252p214 qz38 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns252p216 := nat_lit 4299217964840969452303884730511150033149382679080960000000 

noncomputable abbrev qz605 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1100560))))

noncomputable abbrev qz386 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 550280 4000) (Real.log (Enclosure.sfrac Bool.false 1211233313600 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz605))

noncomputable abbrev qz606 := (Enclosure.sfrac Bool.false 550280 2000)

noncomputable abbrev qz39 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz386 qz606) (@HMul.hMul Real Real Real qz346 qz606 (Real.log Real.pi)))

noncomputable def Ns252p217 := @Enclosure.Real.IsNear.addLit_ft_p qz39 (Enclosure.sfrac Bool.true Ns252p213 Ns252p214) 53764259240657419723 56294995342131200 56337465232518889 4147200000000000000000 Ns252p213 Ns252p214 0 1 Ns252p216 

noncomputable def Ns252p218 := nat_lit 90201459036050551269543116800 

noncomputable abbrev qz40 := (@HSub.hSub Real Real Real qz350 qz386 qz606)

noncomputable def Ns252p219 := @Enclosure.Real.IsNear.subLit_ff_p qz40 (@HMul.hMul Real Real Real qz5 qz606 (Real.log Real.pi)) 71494986135121558987 56294995342131200 87231285660169 16200000000000000000 528416839077 1677721600 13757 1677721600 Ns252p218 53764259240657419723 56294995342131200 

noncomputable abbrev qz41 := qz386

noncomputable def Ns252p220 := @Enclosure.Real.IsNear.subLit_ff_p qz41 qz606 17396798230711107471 11258999068426240 87231285660169 16200000000000000000 550280 2000 0 1 28597994454048623594800 71494986135121558987 56294995342131200 87231285660169 16200000000000000000 

noncomputable def Ns252p221 := nat_lit 19587053507317561927109513947643904 

noncomputable def Ns252p222 := nat_lit 27163501575170246406307840 

noncomputable def Ns252p223 := nat_lit 13983634512370741218957978082174796517616958293778970388495073280000000000000 

noncomputable def Ns252p224 := nat_lit 24224527513944614780189527257172754901225509265448418678931456000000000000 

noncomputable def Ns252p225 := nat_lit 277800377219638001034056526660642976800840794894279639040000000000000 

noncomputable def Ns252p226 := BSN.log_dyadic_bound 162657313600 2259809313600 4 3 Ns252p223 67108864 25920000 Ns252p224 Ns252p225 9677504 2422466627200 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 162657313600) (BSN.artanhQ 2259809313600) 0 3 Ns252p224 Ns252p223 Ns252p225 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz387 := (Real.log (Enclosure.sfrac Bool.false 1211233313600 16000000))

noncomputable def Ns252p227 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 550280 4000) qz387 550280 4000 0 1 3162247777819895 281474976710656 195312581 5062500000000000 8700608535893659103 5629499534213120 2686915176817 506250000000000000 (Enclosure.Real.IsNear.const Bool.false 550280 4000) (BSN.isNear_log_sfrac 1211233313600 16000000 3162247777819895 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1211233313600) qz353)) Bool.false Ns252p222 Ns252p93 1000000414720000 25920000000000000000000 3162247777819895 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1211233313600 16000000 16 2422466627200 2097152000000 9677504 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns252p226 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p228 := BSN.arctan_dyadic_bound_f 1000 1100560 1 0 8388608 3240000 0 1 1 0 1 1 7622 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1100560) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1100560) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz388 := (@Nat.cast Real Real.instNatCast 1100560)

noncomputable def Ns252p229 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 qz388)) 884279719003555 562949953421312 1 2000000000000000 7622 8388608 1 3240000 7413585120525996261376 883768215242147 562949953421312 50000000081 162000000000000000 qz17 (Ns252p228 rfl) rfl rfl 

noncomputable abbrev qz389 := (@HMul.hMul Real Real Real qz584 qz589 qz605)

noncomputable abbrev qz42 := qz389

noncomputable abbrev qz390 := qz605

noncomputable abbrev qz43 := qz390

noncomputable def Ns252p230 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 550280 4000) qz387) qz42 8700608535893659103 5629499534213120 2686915176817 506250000000000000 883768215242147 2251799813685248 50000000081 648000000000000000 Ns252p221 17396798230711107471 11258999068426240 87231285660169 16200000000000000000 (Ns252p227 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz43 1 4 0 1 883768215242147 562949953421312 50000000081 162000000000000000 883768215242147 2251799813685248 50000000081 648000000000000000 qz361 Ns252p229 rfl) 

noncomputable def Ns252p231 := @Ns252p217 Ns252p211 Ns252p212 56337465232518889 4147200000000000000000 (@Ns252p219 56337465232518889 4147200000000000000000 (Ns252p220 (Ns252p230 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 550280 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz606 (Real.log Real.pi) 550280 2000 0 1 38410761 33554432 1 33554432 528416839077 1677721600 13757 1677721600 (Enclosure.Real.IsNear.const Bool.false 550280 2000) RS253to264.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns252p213 Ns252p214) 

noncomputable def Ns252p232 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns252p211 Ns252p212 56337465232518889 4147200000000000000000 8011496393 8388608 229 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz362 qz39 (Enclosure.sfrac Bool.true Ns252p213 Ns252p214)) Bool.false Ns252p211 Ns252p212 56337465232518889 4147200000000000000000 Ns252p215 (Ns252p231 rfl rfl)) 

noncomputable def Ns252p233 := BSN.cos_dyadic_bound_f 21528330 34359738368 1 0 16777216 6486329 0 1 1 0 1 1 16777212 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 21528330) (BSN.cosEvenQ 34359738368) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 21528330) (BSN.cosOddQ 34359738368) 0 0 rfl) rfl rfl 

noncomputable def Ns252p234 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz35) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8011496393) qz365) Bool.false 8011496393 8388608 229 16777216 Bool.false 16777212 16777216 1 3240000 (Ns252p232 rfl) (Enclosure.sfrac_false_div 8011496393 8388608) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8011496393) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 757460789045363736576) qz366) 226375608064910080 72057594037927936 Bool.false 16777212 16777216 152 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q0 8011496393 8388608 226375608064910080 72057594037927936 152 757460789045363736576 Ns252p105 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777212 16777216 757460789045363736576 Ns252p105 21528330 34359738368 6486329 6480000 (Ns252p233 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p235 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns252p211 Ns252p212 56337465232518889 4147200000000000000000 128183942294 134217728 1825 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz362 qz39 (Enclosure.sfrac Bool.true Ns252p213 Ns252p214)) Bool.false Ns252p211 Ns252p212 56337465232518889 4147200000000000000000 Ns252p215 (Ns252p231 rfl rfl)) 

noncomputable def Ns252p236 := Ns252p210 33934 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 365 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 36984499 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 223 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 28359168 134217728) qz38 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) Bool.false 4194303 4194304 11855269 849346560000 134217696 134217728 1874 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 4194303 4194304 11855269 849346560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz35) qz35) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 16777212 16777216 758737216 54358179840000 4194303 4194304 11855269 849346560000 (Ns252p234 rfl rfl) rfl)) rfl) (Ns252p235 rfl) RS253to264.d7 

noncomputable def Ns252p237 := nat_lit 1971071229170096837400100000000 

noncomputable def Ns252p238 := nat_lit 38942226439011207213978722469150720 

noncomputable def Ns252p239 := nat_lit 272595585073078450497851057284055040 

noncomputable def Ns252p240 := BSN.sin_dyadic_bound_f 37469300 134217728 2 1 134217728 67108864 Ns252p237 Ns252p238 Ns252p237 Ns252p237 Ns252p239 Ns252p237 36984499 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 37469300) qz367 0 1 Ns252p237 Ns252p238 Ns252p237 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 37469300) qz368 0 1 Ns252p237 Ns252p239 Ns252p237 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p241 := nat_lit 666679051077559839249291968161 

noncomputable def Ns252p242 := BSN.sin_dyadic_bound_f 28574537 134217728 2 1 134217728 67108864 Ns252p241 Ns252p238 Ns252p241 Ns252p241 Ns252p239 Ns252p241 28359168 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 28574537) qz367 0 1 Ns252p241 Ns252p238 Ns252p241 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 28574537) qz368 0 1 Ns252p241 Ns252p239 Ns252p241 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p243 := nat_lit 17109649487832309425382511113306284603715834001556916877439633690625 

noncomputable def Ns252p244 := nat_lit 984769533372352872830187142787952536175009900708747535812890625 

noncomputable def Ns252p245 := nat_lit 51326978924430183570401872965633277906075151984869333137247275290625 

noncomputable def Ns252p246 := BSN.cos_dyadic_bound_f 74845695 134217728 3 2 134217728 67108864 Ns252p243 Ns252p144 Ns252p244 Ns252p245 Ns252p147 Ns252p244 113884318 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 74845695) qz369 0 2 Ns252p243 Ns252p144 Ns252p244 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 74845695) qz370 0 2 Ns252p245 Ns252p147 Ns252p244 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p247 := nat_lit 2242205358089444084844798930081 

noncomputable def Ns252p248 := BSN.cos_dyadic_bound_f 38696247 134217728 2 1 134217728 67108864 Ns252p247 Ns252p122 Ns252p247 Ns252p247 Ns252p123 Ns252p247 128678012 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 38696247) qz369 0 1 Ns252p247 Ns252p122 Ns252p247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 38696247) qz370 0 1 Ns252p247 Ns252p123 Ns252p247 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p249 := Ns252p208 57575 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 122 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 113884318 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 128678012 134217728) qz38 rfl rfl (Ns252p236 RS253to264.d9 RS253to264.d11 RS253to264.d13 RS253to264.d17 (Ns252p240 rfl rfl) (Ns252p242 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns252p235 rfl) RS253to264.d19 RS253to264.d21 RS253to264.d23 RS253to264.d25 RS253to264.d17 (Ns252p246 rfl rfl) (Ns252p248 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns252p250 := nat_lit 432530552718111430740050386388321376107672152450552966704209602971265 

noncomputable def Ns252p251 := nat_lit 194089076961770664043175444464116070654470160578569859765985511041 

noncomputable def Ns252p252 := nat_lit 1132503874803782308958347775535518844739034114253368656833308793144961 

noncomputable def Ns252p253 := BSN.sin_dyadic_bound_f 144877231 134217728 3 2 134217728 67108864 Ns252p250 Ns252p116 Ns252p251 Ns252p252 Ns252p119 Ns252p251 118337629 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 144877231) qz367 0 2 Ns252p250 Ns252p116 Ns252p251 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 144877231) qz368 0 2 Ns252p252 Ns252p119 Ns252p251 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p254 := nat_lit 437456679033838952507771777496007426817799518502954444056166400000000 

noncomputable def Ns252p255 := nat_lit 198533217322425491239127442955084524716804979919360000000000000000 

noncomputable def Ns252p256 := nat_lit 1145398438927246662915491306153330266720885816587868389670912000000000 

noncomputable def Ns252p257 := BSN.sin_dyadic_bound_f 145287800 134217728 3 2 134217728 67108864 Ns252p254 Ns252p116 Ns252p255 Ns252p256 Ns252p119 Ns252p255 118530798 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 145287800) qz367 0 2 Ns252p254 Ns252p116 Ns252p255 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 145287800) qz368 0 2 Ns252p256 Ns252p119 Ns252p255 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p258 := Ns252p206 77200 BSN.abs_quadSignPos (BSN.cos_quad_nat3 19 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 118337629 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 73 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 118530798 134217728) qz38 rfl rfl (Ns252p249 rfl rfl) (Ns252p235 rfl) RS253to264.d27 RS253to264.d29 RS253to264.d31 RS253to264.d33 RS253to264.d17 (Ns252p253 rfl rfl) (Ns252p257 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p259 := nat_lit 51569615441850017405022391107053298083038074400742429146562948864161 

noncomputable def Ns252p260 := nat_lit 8944158751291518116443882620801932931307289571992494106965022881 

noncomputable def Ns252p261 := nat_lit 154690958008047469178834285555918290383251608623083302451474916546721 

noncomputable def Ns252p262 := BSN.cos_dyadic_bound_f 98614877 134217728 3 2 134217728 67108864 Ns252p259 Ns252p144 Ns252p260 Ns252p261 Ns252p147 Ns252p260 99590408 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 98614877) qz369 0 2 Ns252p259 Ns252p144 Ns252p260 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 98614877) qz370 0 2 Ns252p261 Ns252p147 Ns252p260 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p263 := nat_lit 549006736318564650220363878201228345904252216460274375695651906986240 

noncomputable def Ns252p264 := nat_lit 312620870498220199748052667133986895993489405331973531943564943616 

noncomputable def Ns252p265 := nat_lit 1437368637520196013110884738589762070012861584073038264913084460769536 

noncomputable def Ns252p266 := BSN.sin_dyadic_bound_f 153771994 134217728 3 2 134217728 67108864 Ns252p263 Ns252p116 Ns252p264 Ns252p265 Ns252p119 Ns252p264 122271698 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 153771994) qz367 0 2 Ns252p263 Ns252p116 Ns252p264 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 153771994) qz368 0 2 Ns252p265 Ns252p119 Ns252p264 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p267 := Ns252p204 94348 BSN.abs_quadSignPos (BSN.cos_quad_nat0 120 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 99590408 134217728) BSN.abs_quadSignNeg qz371 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 122271698 134217728) qz38 rfl rfl (Ns252p258 rfl) (Ns252p235 rfl) RS253to264.d35 RS253to264.d37 RS253to264.d39 RS253to264.d41 RS253to264.d17 (Ns252p262 rfl rfl) (Ns252p266 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p268 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) 123007277 134217728 94348 134217728 123007277 134217728 94348 134217728 33019514492813312 123007277 67108864 23587 16777216 (Ns252p267 rfl) 

noncomputable def Ns252p269 := @Enclosure.Real.IsNear.mulLit_tf qz603 (Zeta.RiemannSiegel.correction qz37) 5484271 16777216 1 16777216 29455749169973 70368744177664 23155729469231 593736278999040000 161543310956156994683 1180591620717411303424 

noncomputable abbrev qz607 := (@HPow.hPow Real Real Real qz7 qz36 qz9)

noncomputable def Ns252p270 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz607 1 1 0 1 5484271 16777216 1 16777216 5484271 16777216 1 16777216 

noncomputable def Ns252p271 := @Enclosure.Real.IsNear.sqrt_image qz36 36733624989 419430400 13757 419430400 78503995 78504025 8388608 (@Enclosure.Real.IsNear.of_eq qz36 (@HMul.hMul Real Real Real qz5 qz35 qz3) Bool.false 36733624989 419430400 13757 419430400 (BSN.t_div_two_pi_mk qz35 550280 1000 qz38) (@Enclosure.Real.IsNear.mulLit_ff qz35 qz3 550280 1000 0 1 2670177 16777216 1 16777216 36733624989 419430400 13757 419430400 (Enclosure.Real.IsNear.const Bool.false 550280 1000) RS253to264.d44 rfl)) 

noncomputable abbrev qz747 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 550280 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz608 := qz747

noncomputable abbrev qz391 := qz608

noncomputable abbrev qz44 := qz391

noncomputable def Ns252p272 := @Enclosure.Real.IsNear.sqrt_image qz44 39252005 4194304 15 8388608 25662019 25662025 8388608 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 157008020 16777216 30 16777216 39252005 4194304 15 8388608 (Ns252p271 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns252p273 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz44) 12831011 4194304 3 8388608 2742135 2742136 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz44) Bool.false 51324044 16777216 6 16777216 12831011 4194304 3 8388608 (Ns252p272 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns252p274 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 5484271 16777216 1 16777216 5484271 16777216 1 16777216 (Ns252p273 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz392 := (@HMul.hMul Real Real Real qz584 qz582 qz602)

noncomputable abbrev qz45 := (Real.cos qz392)

noncomputable abbrev qz609 := (@HMul.hMul Real Real Real qz735 qz746 qz746)

noncomputable abbrev qz393 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz609 qz602) qz599)

noncomputable abbrev qz46 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz393))

noncomputable def Ns252p275 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz37) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz45) qz46) Bool.false 29455749169973 

noncomputable def Ns252p276 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz45) qz46 26643983 16777216 493 

noncomputable abbrev qz47 := (@Neg.neg Real Real.instNeg (Real.cos qz392))

noncomputable def Ns252p277 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz45) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz47)) Bool.true 26643983 16777216 493 16777216 (BSN.inv_eq_neg_inv_neg qz45) 

noncomputable def Ns252p278 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz47) Bool.false 26643983 16777216 493 16777216 26643983 16777216 

noncomputable def Ns252p279 := @Enclosure.Real.IsNear.recentre' qz45 Bool.true 10564298 16777216 316188608 27179089920000 5282149 8388608 4940447 424673280000 

noncomputable abbrev qz48 := qz392

noncomputable def Ns252p280 := @Enclosure.Real.IsNear.cos_image qz48 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18890635) qz365) Bool.false 18890635 8388608 95 8388608 Bool.true 10564298 16777216 1 

noncomputable def Ns252p281 := nat_lit 404791131161486646595897001 

noncomputable def Ns252p282 := nat_lit 36028797018963968000000000000000 

noncomputable def Ns252p283 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz37 884279719003555 140737488355328 1 500000000000000 1503269 4194304 15 8388608 1329310288906755121295 590295810358705651712 Ns252p281 

noncomputable def Ns252p284 := @Enclosure.Real.IsNear.subLit_ff_p qz44 qz1 39252005 4194304 15 8388608 9 1 0 1 1503269 1503269 4194304 15 

noncomputable def Ns252p285 := @Ns252p284 8388608 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 157008020 16777216 30 16777216 39252005 4194304 15 8388608 (Ns252p271 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns252p286 := @Enclosure.Real.IsNear.recentre' qz48 Bool.false 1329310288906755121295 590295810358705651712 Ns252p281 Ns252p282 18890635 8388608 95 8388608 (@Ns252p283 Ns252p282 RS253to264.d43 (Ns252p285 rfl rfl) rfl) 

noncomputable def Ns252p287 := nat_lit 1264632376084266781358009547693503668589432596382962919168043013535666724872193303348385 

noncomputable def Ns252p288 := nat_lit 704955687610872565255254336748118540842396593755240389471857687246053587015266059818106880 

noncomputable def Ns252p289 := nat_lit 90012828058813080263605481240888646327677363090069016418118172617180140670108533921 

noncomputable def Ns252p290 := nat_lit 3311986678499079682379122025560976740878269131938947533699245225075842178247040380667041 

noncomputable def Ns252p291 := nat_lit 12924187606199330363012996173715506582110604218846073806984057599510982428613211096665292800 

noncomputable def Ns252p292 := BSN.sin_dyadic_bound_f 23403890141 34359738368 3 2 16777216 6486329 Ns252p287 Ns252p288 Ns252p289 Ns252p290 Ns252p291 Ns252p289 10564298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 23403890141) qz363 0 2 Ns252p287 Ns252p288 Ns252p289 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 23403890141) qz364 0 2 Ns252p290 Ns252p291 Ns252p289 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p293 := @Ns252p280 3240000 (Ns252p286 rfl) (Enclosure.sfrac_false_div 18890635 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18890635) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 823451179079176374190080) qz366) 226375608064910080 72057594037927936 Bool.false 10564298 16777216 0 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 18890635 8388608 226375608064910080 72057594037927936 0 823451179079176374190080 Ns252p105 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 10564298 16777216 823451179079176374190080 Ns252p105 23403890141 34359738368 6486329 6480000 (Ns252p292 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p294 := @Enclosure.Real.IsNear.inv_image qz47 5282149 8388608 4940447 424673280000 13321745 13322238 8388608 (@Enclosure.Real.IsNear.neg qz45 Bool.true 5282149 8388608 4940447 424673280000 (Ns252p279 (Ns252p293 rfl rfl) rfl)) 

noncomputable def Ns252p295 := Ns252p277 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz47) Bool.false 26643983 16777216 493 16777216 (@Ns252p278 493 16777216 (Ns252p294 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p296 := @Enclosure.Real.IsNear.recentre' qz46 Bool.true 2211062 8388608 

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz346 qz343 qz393)

noncomputable def Ns252p297 := @Enclosure.Real.IsNear.cos_image qz49 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15414293)) qz365) Bool.true 15414293 8388608 

noncomputable def Ns252p298 := nat_lit 4549496346559092406614834005 

noncomputable def Ns252p299 := nat_lit 2475880078570760549798248448 

noncomputable def Ns252p300 := nat_lit 5829680028662089387878739753680283 

noncomputable def Ns252p301 := @Enclosure.Real.IsNear.recentre' qz49 Bool.true Ns252p298 Ns252p299 Ns252p300 

noncomputable def Ns252p302 := nat_lit 302231454903657293676544000000000000000 

noncomputable abbrev qz50 := qz393

noncomputable def Ns252p303 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz50 884279719003555 140737488355328 1 500000000000000 5144861121191 

noncomputable abbrev qz394 := (@HSub.hSub Real Real Real qz588 qz609 qz602)

noncomputable abbrev qz51 := qz394

noncomputable def Ns252p304 := @Enclosure.Real.IsNear.subLit_tf qz51 qz31 4045349493415 17592186044416 216025485 70368744177664 1 16 

noncomputable abbrev qz395 := qz609

noncomputable abbrev qz52 := qz395

noncomputable def Ns252p305 := @Enclosure.Real.IsNear.subLit_ff_n qz52 qz37 2259817686361 17592186044416 90196365 70368744177664 1503269 4194304 15 8388608 

noncomputable def Ns252p306 := @Enclosure.Real.IsNear.mulLit_ff qz37 qz37 1503269 4194304 15 8388608 1503269 4194304 15 8388608 2259817686361 17592186044416 

noncomputable def Ns252p307 := nat_lit 27815022796098794943176575050775760969247529793165260833352235877547778209762751789452235281 

noncomputable def Ns252p308 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600 

noncomputable def Ns252p309 := nat_lit 179921606124725764091854972740444990774766928960070627250877811276801707604382234448401 

noncomputable def Ns252p310 := nat_lit 167985290163977453226787425600817414546217653652004842724139037344706925743171985469744091665 

noncomputable def Ns252p311 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600 

noncomputable def Ns252p312 := BSN.cos_dyadic_bound_t 15414293 8388608 4 3 8388608 3240000 Ns252p307 Ns252p308 Ns252p309 Ns252p310 Ns252p311 Ns252p309 2211062 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 15414293) (BSN.cosEvenQ 8388608) 0 3 Ns252p307 Ns252p308 Ns252p309 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 15414293) (BSN.cosOddQ 8388608) 0 3 Ns252p310 Ns252p311 Ns252p309 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p313 := @Ns252p296 1069777216 54358179840000 1105531 4194304 16715269 849346560000 (@Ns252p297 325 16777216 Bool.true 2211062 8388608 1 3240000 (@Ns252p301 Ns252p302 15414293 8388608 325 16777216 (@Ns252p303 17592186044416 216025485 70368744177664 Ns252p298 Ns252p299 Ns252p300 Ns252p302 RS253to264.d43 (@Ns252p304 0 1 82317777939056 5144861121191 17592186044416 216025485 70368744177664 (@Ns252p305 16967425561628508160 4045349493415 17592186044416 216025485 70368744177664 (@Ns252p306 90196365 70368744177664 (Ns252p285 rfl rfl) (Ns252p285 rfl rfl) rfl) (Ns252p285 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 15414293 8388608) (BSN.cos_neg_of_bound 15414293 8388608 Bool.true 2211062 8388608 1 3240000 (Ns252p312 rfl rfl)) rfl rfl) 

noncomputable def Ns252p314 := @Ns252p269 254481703302600164039 Ns252p200 (Ns252p270 qz33 (@Enclosure.Real.IsNear.of_eq qz607 (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 5484271 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz36 (BSN.t_div_two_pi_nonneg qz35 550280 1000 qz38)) Ns252p274) rfl) (@Ns252p275 70368744177664 23155729469231 593736278999040000 (BSN.correction_mk qz37 (BSN.cos_two_pi_p_ne_zero_mk qz35 550280 1000 9 qz38 rfl rfl (@BSN.floor_sqrt_eq_dec qz35 550280 1000 9 qz38 rfl rfl rfl))) (@Ns252p276 16777216 1105531 4194304 16715269 849346560000 29455749169973 70368744177664 23155729469231 593736278999040000 Ns252p295 (Ns252p313 rfl) rfl)) 

noncomputable def Ns252p315 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (hardyZApproximantRS₀ qz35) Bool.false 2325510212757170209915 1180591620717411303424 28263396928803313124039 Ns252p200 (@Eq.refl Real (hardyZApproximantRS₀ qz35)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) (@HMul.hMul Real Real Real qz5 qz603 (Zeta.RiemannSiegel.correction qz37))) Bool.false 2325510212757170209915 1180591620717411303424 28263396928803313124039 Ns252p200 (BSN.hardyZApproximantRS₀_eq qz35 9 (@BSN.floor_sqrt_eq_dec qz35 550280 1000 9 qz38 rfl rfl rfl)) (@Ns252p202 2325510212757170209915 1180591620717411303424 28263396928803313124039 Ns252p200 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 9)) Bool.false 123007277 67108864 23587 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz35) qz35 9) (Ns252p268 (Ns252p267 rfl) rfl rfl)) (Ns252p314 rfl) rfl rfl)) 

theorem RS253to264.d47 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz35) Bool.false 2325510212757170209915 1180591620717411303424 28263396928803313124039 Ns252p200 := Ns252p315 

noncomputable abbrev qz610 := (@HMul.hMul Real Real Real qz735 (Real.sqrt qz743) qz737)

noncomputable abbrev qz396 := qz610

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv qz396)

noncomputable abbrev qz397 := (@HMul.hMul Real Real Real qz584 (@HMul.hMul Real Real Real qz584 qz610 qz610) qz610)

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz346 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz397))

noncomputable abbrev qz398 := (@HMul.hMul Real Real Real qz584 qz597 qz597)

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz346 qz398 qz373))

noncomputable abbrev qz611 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz53)

noncomputable def Ns252p316 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz362 (@HAdd.hAdd Real Real Real qz362 qz611 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55)) Bool.false 

noncomputable def Ns252p317 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz362 qz611 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55) 12564201 536870912 

noncomputable def Ns252p318 := @Enclosure.Real.IsNear.addLit_ff qz611 qz54 1570525 67108864 25 67108864 

noncomputable def Ns252p319 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz53 25 4 0 1 62821 16777216 1 16777216 1570525 

noncomputable def Ns252p320 := @Enclosure.Real.IsNear.recentre' qz53 Bool.false 62821 16777216 1 16777216 62821 16777216 1 16777216 

noncomputable def Ns252p321 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz8 12822807 4194304 3 8388608 732795365349 8388608000 274437 8388608000 9396493540364714643 35184372088832000 2309123072169 

noncomputable def Ns252p322 := @Enclosure.Real.IsNear.sqrt_image qz8 732795365349 8388608000 274437 8388608000 78403639 78403670 8388608 qz21 

noncomputable def Ns252p323 := @Enclosure.Real.IsNear.sqrt_image qz22 156807309 16777216 31 16777216 25645611 25645617 8388608 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 156807309 16777216 31 16777216 156807309 16777216 31 16777216 (Ns252p322 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz399 := (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 51291228 16777216 6 16777216 12822807 4194304 3 8388608 (Ns252p323 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns252p324 := @Ns252p321 17592186044416000 qz399 

noncomputable def Ns252p325 := Ns252p324 qz21 

noncomputable abbrev qz56 := qz396

noncomputable def Ns252p326 := @Enclosure.Real.IsNear.inv_image qz56 9396493540364714643 35184372088832000 2309123072169 17592186044416000 31410 31411 8388608 (Ns252p325 rfl) rfl rfl 

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv qz397)

noncomputable def Ns252p327 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz57 1 32 0 1 1 

noncomputable def Ns252p328 := @Enclosure.Real.IsNear.recentre' qz57 Bool.false 1 16777216 1 16777216 

noncomputable def Ns252p329 := nat_lit 829654854363074431139469427587342367677861463260665605707 

noncomputable def Ns252p330 := nat_lit 43556142965880123323311949751266331066368000000000 

noncomputable def Ns252p331 := nat_lit 611646067597727702358599528201942793163687338842217 

noncomputable def Ns252p332 := nat_lit 21778071482940061661655974875633165533184000000000 

noncomputable abbrev qz58 := qz397

noncomputable def Ns252p333 := @Enclosure.Real.IsNear.inv_image qz58 Ns252p329 Ns252p330 Ns252p331 Ns252p332 0 1 

noncomputable def Ns252p334 := nat_lit 88294090854115809173918829210818617449 

noncomputable def Ns252p335 := nat_lit 1237940039285380274899124224000000 

noncomputable def Ns252p336 := nat_lit 5424416340898123927092490608807 

noncomputable def Ns252p337 := nat_lit 77371252455336267181195264000000 

noncomputable abbrev qz400 := (@HMul.hMul Real Real Real qz584 qz610 qz610)

noncomputable abbrev qz59 := qz400

noncomputable def Ns252p338 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz56 Ns252p334 Ns252p335 Ns252p336 Ns252p337 9396493540364714643 35184372088832000 2309123072169 

noncomputable def Ns252p339 := @Enclosure.Real.IsNear.mulLit_ff qz56 qz56 9396493540364714643 35184372088832000 2309123072169 17592186044416000 9396493540364714643 35184372088832000 2309123072169 17592186044416000 Ns252p334 

noncomputable def Ns252p340 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz55 13 10 0 1 587151 16777216 1 

noncomputable def Ns252p341 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 587151 16777216 1 16777216 587151 16777216 

noncomputable abbrev qz60 := qz398

noncomputable def Ns252p342 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz23 164424379359249 17592186044416 153873693 70368744177664 12822807 4194304 3 8388608 2108382082618433591943 

noncomputable def Ns252p343 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz23 12822807 4194304 3 8388608 12822807 4194304 3 8388608 164424379359249 17592186044416 153873693 

noncomputable def Ns252p344 := @Ns252p343 70368744177664 qz399 

noncomputable def Ns252p345 := Ns252p344 qz399 

noncomputable def Ns252p346 := @Ns252p342 73786976294838206464 5919278349364569 590295810358705651712 (Ns252p345 rfl) qz399 

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz346 qz398 qz373)

noncomputable def Ns252p347 := @Enclosure.Real.IsNear.inv_image qz61 2108382082618433591943 73786976294838206464 5919278349364569 590295810358705651712 293575 293576 8388608 (Ns252p346 rfl) 

noncomputable def Ns252p348 := @Ns252p317 201 536870912 7632963 167772160 13 167772160 6205838947516416 184948413 2684354560 1213 2684354560 (@Ns252p318 1 536870912 1 536870912 843169256177664 12564201 536870912 201 536870912 (@Ns252p319 67108864 25 67108864 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns252p320 (Ns252p326 rfl rfl rfl rfl) rfl) rfl) (@Ns252p327 16777216 1 16777216 1 536870912 1 536870912 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns252p328 1 16777216 1 16777216 (@Ns252p333 8388608 (@Ns252p338 17592186044416000 Ns252p329 Ns252p330 Ns252p331 Ns252p332 (@Ns252p339 Ns252p335 Ns252p336 Ns252p337 (Ns252p325 rfl) (Ns252p325 rfl) rfl) (Ns252p325 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns252p340 16777216 7632963 167772160 13 167772160 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns252p341 1 16777216 (Ns252p347 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS253to264.d48 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 := @Ns252p316 184948413 2684354560 1213 2684354560 (BSN.hardyZErrorBoundRS₀_mk qz4 548874 1000 qz11 rfl rfl) (Ns252p348 rfl rfl) 

noncomputable def Ns252p349 := nat_lit 2991226215744427883447189504 

noncomputable abbrev qz748 := (Enclosure.sfrac Bool.false 551684 1000)

noncomputable abbrev qz612 := qz748

noncomputable abbrev qz401 := qz612

noncomputable abbrev qz62 := qz401

noncomputable abbrev qz749 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 551684 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz613 := qz749

noncomputable abbrev qz402 := qz613

noncomputable abbrev qz63 := qz402

noncomputable abbrev qz750 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 551684 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz614 := qz750

noncomputable abbrev qz403 := qz614

noncomputable abbrev qz64 := qz403

noncomputable abbrev qz615 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz63 qz9))

noncomputable def Ns252p350 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (@HMul.hMul Real Real Real qz5 qz615 (Zeta.RiemannSiegel.correction qz64)) 22531153 16777216 94589 67108864 19895141653318261905 147573952589676412928 14137324310425775251 1195349015976378944716800 Ns252p349 

noncomputable def Ns252p351 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 551684 1000 120 161 134217728 67108864 2251799813685248 Bool.false 128605469967 1829 

noncomputable def Ns252p352 := Ns252p351 279097919 42 47453128 8 294906479 42 44739240 8 Bool.true 91787932 77397 Bool.true 68940682 Bool.true 146293018 7074237752028440 1 Bool.false 116897974 Bool.false Bool.false 118999058 Bool.true Bool.true 90124612 

noncomputable def Ns252p353 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 551684 1000 19 73 134217728 67108864 2251799813685248 Bool.false 128605469967 1829 

noncomputable def Ns252p354 := Ns252p353 240485871 42 54794152 8 261175631 42 50729528 8 Bool.true 84181958 57722 Bool.true 60991721 Bool.true 90450713 7074237752028440 1 Bool.false 58914146 Bool.false Bool.false 83758067 Bool.true Bool.true 91787932 

noncomputable def Ns252p355 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 551684 1000 123 44 134217728 67108864 2251799813685248 Bool.false 128605469967 1829 

noncomputable def Ns252p356 := Ns252p355 186065264 42 67108856 8 216015088 42 60023992 8 Bool.true 119728113 34022 Bool.false 24309024 Bool.false 156938736 7074237752028440 1 Bool.false 24176339 Bool.false Bool.false 52453656 Bool.false Bool.true 84181958 

noncomputable def Ns252p357 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 551684 1000 366 224 134217728 67108864 2251799813685248 Bool.false 128605469967 1829 

noncomputable def Ns252p358 := Ns252p357 93032624 42 94906264 8 147453232 42 77490640 16 Bool.true 134217720 1882 Bool.false 117550455 Bool.false 32249158 7074237752028440 1 Bool.false 85948727 Bool.true Bool.false 130361999 Bool.false Bool.true 119728113 

noncomputable def Ns252p359 := nat_lit 65264249493164063148617049060505443386523174913649 

noncomputable def Ns252p360 := nat_lit 68112338369725820474136678364324345795313664000 

noncomputable def Ns252p361 := nat_lit 24529804363363895829490307563520000 

noncomputable def Ns252p362 := nat_lit 81196234666974330513640258746533806080 

noncomputable abbrev qz616 := (@Eq.refl Real qz748)

noncomputable abbrev qz404 := qz616

noncomputable abbrev qz65 := qz404

noncomputable def Ns252p363 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz62 551684 1000 1217421943424 16000000 1103368 4000 2000 Ns252p361 Ns252p362 qz65 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns252p364 := nat_lit 684345256765440006801242708356685558044669246582544138240 

noncomputable abbrev qz617 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1103368))))

noncomputable abbrev qz405 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 551684 4000) (Real.log (Enclosure.sfrac Bool.false 1217421943424 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz617))

noncomputable abbrev qz618 := (Enclosure.sfrac Bool.false 551684 2000)

noncomputable abbrev qz66 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz405 qz618) (@HMul.hMul Real Real Real qz346 qz618 (Real.log Real.pi)))

noncomputable def Ns252p365 := @Enclosure.Real.IsNear.addLit_ft_p qz66 (Enclosure.sfrac Bool.true Ns252p361 Ns252p362) 8428290737110140253 8796093022208000 564803897821767517 41472000000000000000000 Ns252p361 Ns252p362 0 1 Ns252p364 

noncomputable def Ns252p366 := nat_lit 141403254207296038814875648000 

noncomputable abbrev qz67 := (@HSub.hSub Real Real Real qz350 qz405 qz618)

noncomputable def Ns252p367 := @Enclosure.Real.IsNear.subLit_ff_p qz67 (@HMul.hMul Real Real Real qz5 qz618 (Real.log Real.pi)) 11205785358043333981 8796093022208000 437253303755741 81000000000000000000 5297650567881 16777216000 137921 16777216000 Ns252p366 8428290737110140253 8796093022208000 

noncomputable abbrev qz68 := qz405

noncomputable def Ns252p368 := @Enclosure.Real.IsNear.subLit_ff_p qz68 qz618 13632117249475233117 8796093022208000 437253303755741 81000000000000000000 551684 2000 0 1 22411570716086667962000 11205785358043333981 8796093022208000 437253303755741 81000000000000000000 

noncomputable def Ns252p369 := nat_lit 982297570640121131582733173246656512 

noncomputable def Ns252p370 := nat_lit 27175823820067499291967488 

noncomputable def Ns252p371 := nat_lit 14214983741255931177327048269959692114637989628858288394893068487732211220480 

noncomputable def Ns252p372 := nat_lit 26395958101763397677473494884482558828864876780768813430433067187249872896 

noncomputable def Ns252p373 := nat_lit 347564206915494964028842659104012102654212638423715599524613995888640 

noncomputable def Ns252p374 := BSN.log_dyadic_bound 168845943424 2265997943424 4 3 Ns252p371 67108864 25920000 Ns252p372 Ns252p373 10019515 2434843886848 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 168845943424) (BSN.artanhQ 2265997943424) 0 3 Ns252p372 Ns252p371 Ns252p373 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz406 := (Real.log (Enclosure.sfrac Bool.false 1217421943424 16000000))

noncomputable def Ns252p375 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 551684 4000) qz406 551684 4000 0 1 3163682275925239 281474976710656 195312581 5062500000000000 436338223177884888119 281474976710656000 26937706484101 5062500000000000000 (Enclosure.Real.IsNear.const Bool.false 551684 4000) (BSN.isNear_log_sfrac 1217421943424 16000000 3163682275925239 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1217421943424) qz353)) Bool.false Ns252p370 Ns252p93 1000000414720000 25920000000000000000000 3163682275925239 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1217421943424 16000000 16 2434843886848 2097152000000 10019515 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns252p374 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p376 := BSN.arctan_dyadic_bound_f 1000 1103368 1 0 8388608 3240000 0 1 1 0 1 1 7602 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1103368) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1103368) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz407 := (@Nat.cast Real Real.instNatCast 1103368)

noncomputable def Ns252p377 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 qz407)) 884279719003555 562949953421312 1 2000000000000000 7602 8388608 1 3240000 7413596379525064687616 883769557419427 562949953421312 50000000081 162000000000000000 qz17 (Ns252p376 rfl) rfl rfl 

noncomputable abbrev qz408 := (@HMul.hMul Real Real Real qz584 qz589 qz617)

noncomputable abbrev qz69 := qz408

noncomputable abbrev qz409 := qz617

noncomputable abbrev qz70 := qz409

noncomputable def Ns252p378 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 551684 4000) qz406) qz69 436338223177884888119 281474976710656000 26937706484101 5062500000000000000 883769557419427 2251799813685248 50000000081 648000000000000000 Ns252p369 13632117249475233117 8796093022208000 437253303755741 81000000000000000000 (Ns252p375 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz70 1 4 0 1 883769557419427 562949953421312 50000000081 162000000000000000 883769557419427 2251799813685248 50000000081 648000000000000000 qz361 Ns252p377 rfl) 

noncomputable def Ns252p379 := @Ns252p365 Ns252p359 Ns252p360 564803897821767517 41472000000000000000000 (@Ns252p367 564803897821767517 41472000000000000000000 (Ns252p368 (Ns252p378 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 551684 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz618 (Real.log Real.pi) 551684 2000 0 1 38410761 33554432 1 33554432 5297650567881 16777216000 137921 16777216000 (Enclosure.Real.IsNear.const Bool.false 551684 2000) RS253to264.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns252p361 Ns252p362) 

noncomputable def Ns252p380 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns252p359 Ns252p360 564803897821767517 41472000000000000000000 16075683745 16777216 115 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz362 qz66 (Enclosure.sfrac Bool.true Ns252p361 Ns252p362)) Bool.false Ns252p359 Ns252p360 564803897821767517 41472000000000000000000 Ns252p363 (Ns252p379 rfl rfl)) 

noncomputable def Ns252p381 := nat_lit 3797129914123962936197120 

noncomputable def Ns252p382 := nat_lit 856393765192574172678311215243778254745594376185482935170601069163061211517962691499649683384714113656123202410369171665263881078439936 

noncomputable def Ns252p383 := nat_lit 609407603260192995968038619257199526716845894372505072418816908006406753364872529047774735603837010722194874801466054960255860736 

noncomputable def Ns252p384 := nat_lit 4276652552244131051222120542913629323827699772725223403292647612620995926408721427543916317091928108810026977245031396725387575580164096 

noncomputable def Ns252p385 := BSN.sin_dyadic_bound_f 53960461544 34359738368 4 3 16777216 6486329 Ns252p382 Ns252p107 Ns252p383 Ns252p384 Ns252p110 Ns252p383 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53960461544) qz363 0 3 Ns252p382 Ns252p107 Ns252p383 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53960461544) qz364 0 3 Ns252p384 Ns252p110 Ns252p383 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz410 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable abbrev qz411 := (@Nat.cast Real Real.instNatCast Ns252p93)

noncomputable def Ns252p386 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz62) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16075683745) qz410) Bool.false 16075683745 16777216 115 8388608 Bool.true 16777215 16777216 1 3240000 (Ns252p380 rfl) (Enclosure.sfrac_false_div 16075683745 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16075683745) qz410) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns252p381) qz411) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 152 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 16075683745 16777216 226375608064910080 72057594037927936 152 Ns252p381 Ns252p93 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns252p381 Ns252p93 53960461544 34359738368 6486329 6480000 (Ns252p385 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p387 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns252p359 Ns252p360 564803897821767517 41472000000000000000000 128605469967 134217728 1829 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz362 qz66 (Enclosure.sfrac Bool.true Ns252p361 Ns252p362)) Bool.false Ns252p359 Ns252p360 564803897821767517 41472000000000000000000 Ns252p363 (Ns252p379 rfl rfl)) 

noncomputable def Ns252p388 := Ns252p358 34022 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 366 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 85948727 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 224 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 130361999 134217728) qz65 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) Bool.true 16777215 16777216 5952947 424673280000 134217720 134217728 1882 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 16777215 16777216 5952947 424673280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz62) qz62) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 16777215 16777216 380988608 27179089920000 16777215 16777216 5952947 424673280000 (Ns252p386 rfl rfl) rfl)) rfl) (Ns252p387 rfl) RS253to264.d7 

noncomputable def Ns252p389 := nat_lit 104135341589610608306219415381078760306144078145166745145607254690625 

noncomputable def Ns252p390 := nat_lit 36458140631678264805160131470422382946895422952684516652937890625 

noncomputable def Ns252p391 := nat_lit 312333108487568468389047925880295436152538443589594866403515888290625 

noncomputable def Ns252p392 := BSN.cos_dyadic_bound_f 117550455 134217728 3 2 134217728 67108864 Ns252p389 Ns252p144 Ns252p390 Ns252p391 Ns252p147 Ns252p390 85948727 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 117550455) qz369 0 2 Ns252p389 Ns252p144 Ns252p390 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 117550455) qz370 0 2 Ns252p391 Ns252p147 Ns252p390 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p393 := nat_lit 1081617038821749215750877953296 

noncomputable def Ns252p394 := BSN.cos_dyadic_bound_f 32249158 134217728 2 1 134217728 67108864 Ns252p393 Ns252p122 Ns252p393 Ns252p393 Ns252p123 Ns252p393 130361999 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 32249158) qz369 0 1 Ns252p393 Ns252p122 Ns252p393 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 32249158) qz370 0 1 Ns252p393 Ns252p123 Ns252p393 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p395 := nat_lit 349196666829236628102526795776 

noncomputable def Ns252p396 := BSN.sin_dyadic_bound_f 24309024 134217728 2 1 134217728 67108864 Ns252p395 Ns252p238 Ns252p395 Ns252p395 Ns252p239 Ns252p395 24176339 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 24309024) qz367 0 1 Ns252p395 Ns252p238 Ns252p395 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 24309024) qz368 0 1 Ns252p395 Ns252p239 Ns252p395 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p397 := nat_lit 1276463577826201772404178083699043055030922034108604981221866261571516245234292779902078830167642525925376 

noncomputable def Ns252p398 := nat_lit 16370259324565974446773555668639125346849261288577159159185037526614652227207809159774062022111344040345600 

noncomputable def Ns252p399 := nat_lit 223234752543106153592635799823945522121518183942229348651280108149852666768626981376258581039415296 

noncomputable def Ns252p400 := nat_lit 7738139967129700634128542705935085641761216031266855282933167457688652833938570004876283590457967320760320 

noncomputable def Ns252p401 := nat_lit 1489693598535503674656393565846160406563282777260521483485838414921933352675910633539439644012132307671449600 

noncomputable def Ns252p402 := BSN.cos_dyadic_bound_f 156938736 134217728 4 3 134217728 67108864 Ns252p397 Ns252p398 Ns252p399 Ns252p400 Ns252p401 Ns252p399 52453656 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 156938736) qz369 0 3 Ns252p397 Ns252p398 Ns252p399 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 156938736) qz370 0 3 Ns252p400 Ns252p401 Ns252p399 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p403 := Ns252p356 57722 BSN.abs_quadSignPos (BSN.cos_quad_nat3 123 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 24176339 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 52453656 134217728) qz65 rfl rfl (Ns252p388 RS253to264.d9 RS253to264.d11 RS253to264.d13 RS253to264.d17 (Ns252p392 rfl rfl) (Ns252p394 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns252p387 rfl) RS253to264.d19 RS253to264.d21 RS253to264.d23 RS253to264.d25 RS253to264.d17 (Ns252p396 rfl rfl) (Ns252p402 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns252p404 := nat_lit 13838325827330687135984051669281 

noncomputable def Ns252p405 := BSN.sin_dyadic_bound_f 60991721 134217728 2 1 134217728 67108864 Ns252p404 Ns252p238 Ns252p404 Ns252p404 Ns252p239 Ns252p404 58914146 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 60991721) qz367 0 1 Ns252p404 Ns252p238 Ns252p404 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 60991721) qz368 0 1 Ns252p404 Ns252p239 Ns252p404 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p406 := nat_lit 65689947967469330177625995248617324969859170080705204988584434567105 

noncomputable def Ns252p407 := nat_lit 4480185097755372545831801550594592232939969064323686550632105921 

noncomputable def Ns252p408 := nat_lit 172037848186547117957279593210534888438396875975742822334734400456641 

noncomputable def Ns252p409 := BSN.sin_dyadic_bound_f 90450713 134217728 3 2 134217728 67108864 Ns252p406 Ns252p116 Ns252p407 Ns252p408 Ns252p119 Ns252p407 83758067 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 90450713) qz367 0 2 Ns252p406 Ns252p116 Ns252p407 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 90450713) qz368 0 2 Ns252p408 Ns252p119 Ns252p407 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p410 := Ns252p354 77397 BSN.abs_quadSignPos (BSN.cos_quad_nat3 19 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 58914146 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 73 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 83758067 134217728) qz65 rfl rfl (Ns252p403 rfl rfl) (Ns252p387 rfl) RS253to264.d27 RS253to264.d29 RS253to264.d31 RS253to264.d33 RS253to264.d17 (Ns252p405 rfl rfl) (Ns252p409 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p411 := nat_lit 12315983800520905576080585335231901625401827802922888091737481011456 

noncomputable def Ns252p412 := nat_lit 510275366169347395827679403715109695036511077006707697260421376 

noncomputable def Ns252p413 := nat_lit 36946930850830378033450100646888274656815410386614650859817922191616 

noncomputable def Ns252p414 := BSN.cos_dyadic_bound_f 68940682 134217728 3 2 134217728 67108864 Ns252p411 Ns252p144 Ns252p412 Ns252p413 Ns252p147 Ns252p412 116897974 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 68940682) qz369 0 2 Ns252p411 Ns252p144 Ns252p412 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 68940682) qz370 0 2 Ns252p413 Ns252p147 Ns252p412 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p415 := nat_lit 449695322874275752805322506109832522354545190634574095010514524709120 

noncomputable def Ns252p416 := nat_lit 209791938250952199886880062018453692944310134675627521649078968576 

noncomputable def Ns252p417 := nat_lit 1177433801532601620452218281615817204949518044777266851897249055908096 

noncomputable def Ns252p418 := BSN.sin_dyadic_bound_f 146293018 134217728 3 2 134217728 67108864 Ns252p415 Ns252p116 Ns252p416 Ns252p417 Ns252p119 Ns252p416 118999058 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 146293018) qz367 0 2 Ns252p415 Ns252p116 Ns252p416 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 146293018) qz368 0 2 Ns252p417 Ns252p119 Ns252p416 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p419 := Ns252p352 94589 BSN.abs_quadSignPos (BSN.cos_quad_nat0 120 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 116897974 134217728) BSN.abs_quadSignNeg qz371 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 118999058 134217728) qz65 rfl rfl (Ns252p410 rfl) (Ns252p387 rfl) RS253to264.d35 RS253to264.d37 RS253to264.d39 RS253to264.d41 RS253to264.d17 (Ns252p414 rfl rfl) (Ns252p418 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p420 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) 90124612 134217728 94589 134217728 90124612 134217728 94589 134217728 24192641319043072 22531153 16777216 94589 67108864 (Ns252p419 rfl) 

noncomputable def Ns252p421 := @Enclosure.Real.IsNear.mulLit_tf qz615 (Zeta.RiemannSiegel.correction qz64) 2740389 8388608 1 8388608 7259969899645 17592186044416 51374142199609 1424967069597696000 19895141653318261905 147573952589676412928 

noncomputable abbrev qz619 := (@HPow.hPow Real Real Real qz7 qz63 qz9)

noncomputable def Ns252p422 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz619 1 1 0 1 2740389 8388608 1 8388608 2740389 8388608 1 8388608 

noncomputable def Ns252p423 := @Enclosure.Real.IsNear.sqrt_image qz63 368273482017 4194304000 137921 4194304000 78604080 78604110 8388608 (@Enclosure.Real.IsNear.of_eq qz63 (@HMul.hMul Real Real Real qz5 qz62 qz3) Bool.false 368273482017 4194304000 137921 4194304000 (BSN.t_div_two_pi_mk qz62 551684 1000 qz65) (@Enclosure.Real.IsNear.mulLit_ff qz62 qz3 551684 1000 0 1 2670177 16777216 1 16777216 368273482017 4194304000 137921 4194304000 (Enclosure.Real.IsNear.const Bool.false 551684 1000) RS253to264.d44 rfl)) 

noncomputable abbrev qz751 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 551684 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz620 := qz751

noncomputable abbrev qz412 := qz620

noncomputable abbrev qz71 := qz412

noncomputable def Ns252p424 := @Enclosure.Real.IsNear.sqrt_image qz71 78604095 8388608 15 8388608 25678372 25678378 8388608 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 157208190 16777216 30 16777216 78604095 8388608 15 8388608 (Ns252p423 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns252p425 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz71) 25678375 8388608 3 8388608 2740388 2740390 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz71) Bool.false 51356750 16777216 6 16777216 25678375 8388608 3 8388608 (Ns252p424 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns252p426 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 5480778 16777216 2 16777216 2740389 8388608 1 8388608 (Ns252p425 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz413 := (@HMul.hMul Real Real Real qz584 qz582 qz614)

noncomputable abbrev qz72 := (Real.cos qz413)

noncomputable abbrev qz621 := (@HMul.hMul Real Real Real qz735 qz750 qz750)

noncomputable abbrev qz414 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz621 qz614) qz599)

noncomputable abbrev qz73 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz414))

noncomputable def Ns252p427 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz64) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz72) qz73) Bool.false 7259969899645 

noncomputable def Ns252p428 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz72) qz73 12226597 8388608 13 

noncomputable abbrev qz74 := (@Neg.neg Real Real.instNeg (Real.cos qz413))

noncomputable def Ns252p429 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz72) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz74)) Bool.true 12226597 8388608 13 524288 (BSN.inv_eq_neg_inv_neg qz72) 

noncomputable def Ns252p430 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz74) Bool.false 24453194 16777216 416 16777216 12226597 8388608 

noncomputable def Ns252p431 := @Enclosure.Real.IsNear.recentre' qz72 Bool.true 11510765 16777216 316188608 27179089920000 11510765 16777216 4940447 424673280000 

noncomputable abbrev qz75 := qz413

noncomputable def Ns252p432 := @Enclosure.Real.IsNear.cos_image qz75 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39038975) qz410) Bool.false 39038975 16777216 95 8388608 Bool.true 11510765 16777216 1 

noncomputable def Ns252p433 := nat_lit 404791131162346370199537321 

noncomputable def Ns252p434 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz64 884279719003555 140737488355328 1 500000000000000 3106623 8388608 15 8388608 2747123713489981044765 1180591620717411303424 Ns252p433 

noncomputable def Ns252p435 := @Enclosure.Real.IsNear.subLit_ff_p qz71 qz1 78604095 8388608 15 8388608 9 1 0 1 3106623 3106623 8388608 15 

noncomputable def Ns252p436 := @Ns252p435 8388608 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 157208190 16777216 30 16777216 78604095 8388608 15 8388608 (Ns252p423 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns252p437 := @Enclosure.Real.IsNear.recentre' qz75 Bool.false 2747123713489981044765 1180591620717411303424 Ns252p433 Ns252p282 39038975 16777216 95 8388608 (@Ns252p434 Ns252p282 RS253to264.d43 (Ns252p436 rfl rfl) rfl) 

noncomputable def Ns252p438 := nat_lit 1828156750777297057873920 

noncomputable def Ns252p439 := nat_lit 1920271500502759158469543694164769583084360713374994507931926929101806064258595702621345 

noncomputable def Ns252p440 := nat_lit 207524339143466517592065040952314084807926850929373581983674456604377023549814523041 

noncomputable def Ns252p441 := nat_lit 5028946509529565516867941569889045161464589034413957106403263627098799272162955711923361 

noncomputable def Ns252p442 := BSN.sin_dyadic_bound_f 25979669981 34359738368 3 2 16777216 6486329 Ns252p439 Ns252p288 Ns252p440 Ns252p441 Ns252p291 Ns252p440 11510765 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 25979669981) qz363 0 2 Ns252p439 Ns252p288 Ns252p440 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 25979669981) qz364 0 2 Ns252p441 Ns252p291 Ns252p440 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p443 := @Ns252p432 3240000 (Ns252p437 rfl) (Enclosure.sfrac_false_div 39038975 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39038975) qz410) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns252p438) qz411) 226375608064910080 72057594037927936 Bool.false 11510765 16777216 0 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 39038975 16777216 226375608064910080 72057594037927936 0 Ns252p438 Ns252p93 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 11510765 16777216 Ns252p438 Ns252p93 25979669981 34359738368 6486329 6480000 (Ns252p442 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p444 := @Enclosure.Real.IsNear.inv_image qz74 11510765 16777216 4940447 424673280000 12226389 12226805 8388608 (@Enclosure.Real.IsNear.neg qz72 Bool.true 11510765 16777216 4940447 424673280000 (Ns252p431 (Ns252p443 rfl rfl) rfl)) 

noncomputable def Ns252p445 := Ns252p429 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz74) Bool.false 12226597 8388608 13 524288 (@Ns252p430 13 524288 (Ns252p444 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p446 := @Enclosure.Real.IsNear.recentre' qz73 Bool.true 2375140 8388608 

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz346 qz343 qz414)

noncomputable def Ns252p447 := @Enclosure.Real.IsNear.cos_image qz76 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1948109)) (@Nat.cast Real Real.instNatCast 1048576)) Bool.true 1948109 1048576 

noncomputable def Ns252p448 := nat_lit 18399369580801988083856033245 

noncomputable def Ns252p449 := nat_lit 9903520314283042199192993792 

noncomputable def Ns252p450 := nat_lit 5910707069383470842054889890769173 

noncomputable def Ns252p451 := @Enclosure.Real.IsNear.recentre' qz76 Bool.true Ns252p448 Ns252p449 Ns252p450 

noncomputable abbrev qz77 := qz414

noncomputable def Ns252p452 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz77 884279719003555 140737488355328 1 500000000000000 20807182597759 

noncomputable abbrev qz415 := (@HSub.hSub Real Real Real qz588 qz621 qz614)

noncomputable abbrev qz78 := qz415

noncomputable def Ns252p453 := @Enclosure.Real.IsNear.subLit_tf qz78 qz31 16409136086655 70368744177664 219028035 70368744177664 1 16 

noncomputable abbrev qz416 := qz621

noncomputable abbrev qz79 := qz416

noncomputable def Ns252p454 := @Enclosure.Real.IsNear.subLit_ff_n qz79 qz64 9651106464129 70368744177664 93198915 70368744177664 3106623 8388608 15 8388608 

noncomputable def Ns252p455 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz64 3106623 8388608 15 8388608 3106623 8388608 15 8388608 9651106464129 70368744177664 

noncomputable def Ns252p456 := nat_lit 423106871826700922055231827486929422519163129081637412900805330477433242991594161 

noncomputable def Ns252p457 := nat_lit 846322570984149739285326836131859157750990110577656481930582364989086940895641600 

noncomputable def Ns252p458 := nat_lit 2987851665951877255103286704916968793024714784318287314926419094200723311281 

noncomputable def Ns252p459 := nat_lit 2554783385359138189911723086551073433365182865540588624596912893150524633918868145 

noncomputable def Ns252p460 := nat_lit 77015353959557626274964742087999183355340100062566739855682995214006911621503385600 

noncomputable def Ns252p461 := BSN.cos_dyadic_bound_t 1948109 1048576 4 3 8388608 3240000 Ns252p456 Ns252p457 Ns252p458 Ns252p459 Ns252p460 Ns252p458 2375140 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 1948109) (BSN.cosEvenQ 1048576) 0 3 Ns252p456 Ns252p457 Ns252p458 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 1948109) (BSN.cosOddQ 1048576) 0 3 Ns252p459 Ns252p460 Ns252p458 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p462 := @Ns252p446 1082737216 54358179840000 593785 2097152 16917769 849346560000 (@Ns252p447 329 16777216 Bool.true 2375140 8388608 1 3240000 (@Ns252p451 Ns252p302 1948109 1048576 329 16777216 (@Ns252p452 70368744177664 219028035 70368744177664 Ns252p448 Ns252p449 Ns252p450 Ns252p302 RS253to264.d43 (@Ns252p453 0 1 332914921564144 20807182597759 70368744177664 219028035 70368744177664 (@Ns252p454 137649810249602826240 16409136086655 70368744177664 219028035 70368744177664 (@Ns252p455 93198915 70368744177664 (Ns252p436 rfl rfl) (Ns252p436 rfl rfl) rfl) (Ns252p436 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 1948109 1048576) (BSN.cos_neg_of_bound 1948109 1048576 Bool.true 2375140 8388608 1 3240000 (Ns252p461 rfl rfl)) rfl rfl) 

noncomputable def Ns252p463 := @Ns252p421 14137324310425775251 1195349015976378944716800 (Ns252p422 qz33 (@Enclosure.Real.IsNear.of_eq qz619 (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 2740389 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz63 (BSN.t_div_two_pi_nonneg qz62 551684 1000 qz65)) Ns252p426) rfl) (@Ns252p427 17592186044416 51374142199609 1424967069597696000 (BSN.correction_mk qz64 (BSN.cos_two_pi_p_ne_zero_mk qz62 551684 1000 9 qz65 rfl rfl (@BSN.floor_sqrt_eq_dec qz62 551684 1000 9 qz65 rfl rfl rfl))) (@Ns252p428 524288 593785 2097152 16917769 849346560000 7259969899645 17592186044416 51374142199609 1424967069597696000 Ns252p445 (Ns252p462 rfl) rfl)) 

noncomputable def Ns252p464 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (hardyZApproximantRS₀ qz62) Bool.true 178290976032282583919 147573952589676412928 1698964951137631612051 1195349015976378944716800 (@Eq.refl Real (hardyZApproximantRS₀ qz62)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (@HMul.hMul Real Real Real qz5 qz615 (Zeta.RiemannSiegel.correction qz64))) Bool.true 178290976032282583919 147573952589676412928 1698964951137631612051 1195349015976378944716800 (BSN.hardyZApproximantRS₀_eq qz62 9 (@BSN.floor_sqrt_eq_dec qz62 551684 1000 9 qz65 rfl rfl rfl)) (@Ns252p350 178290976032282583919 147573952589676412928 1698964951137631612051 1195349015976378944716800 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 9)) Bool.true 22531153 16777216 94589 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz62) qz62 9) (Ns252p420 (Ns252p419 rfl) rfl rfl)) (Ns252p463 rfl) rfl rfl)) 

theorem RS253to264.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz62) Bool.true 178290976032282583919 147573952589676412928 1698964951137631612051 1195349015976378944716800 := Ns252p464 

noncomputable def Ns252p465 := nat_lit 6640827866535438581760000 

noncomputable def Ns252p466 := nat_lit 141367634076917434665958113280 

noncomputable abbrev qz752 := (Enclosure.sfrac Bool.false 553088 1000)

noncomputable abbrev qz622 := qz752

noncomputable abbrev qz417 := qz622

noncomputable abbrev qz80 := qz417

noncomputable abbrev qz753 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 553088 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz623 := qz753

noncomputable abbrev qz418 := qz623

noncomputable abbrev qz81 := qz418

noncomputable abbrev qz754 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 553088 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz624 := qz754

noncomputable abbrev qz419 := qz624

noncomputable abbrev qz82 := qz419

noncomputable abbrev qz625 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz81 qz9))

noncomputable def Ns252p467 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) (@HMul.hMul Real Real Real qz5 qz625 (Zeta.RiemannSiegel.correction qz82)) 115280845 33554432 47411 33554432 156999660751067203125 1180591620717411303424 75776301661768843823 Ns252p465 Ns252p466 

noncomputable def Ns252p468 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 553088 1000 120 161 134217728 67108864 2251799813685248 Bool.false 129027237233 1833 

noncomputable def Ns252p469 := Ns252p468 279097919 42 47453128 8 294906479 42 44739240 8 Bool.false 223511976 77587 Bool.true 39026894 Bool.true 138574448 7074237752028440 1 Bool.false 128583608 Bool.false Bool.false 115234361 Bool.true Bool.false 230561690 

noncomputable def Ns252p470 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 553088 1000 18 73 134217728 67108864 2251799813685248 Bool.false 129027237233 1833 

noncomputable def Ns252p471 := Ns252p470 240485871 42 54794152 8 261175631 42 50729528 8 Bool.false 246125325 57863 Bool.true 187695332 Bool.true 35374033 7074237752028440 1 Bool.false 23019014 Bool.true Bool.false 34965925 Bool.true Bool.false 223511976 

noncomputable def Ns252p472 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 553088 1000 123 45 134217728 67108864 2251799813685248 Bool.false 129027237233 1833 

noncomputable def Ns252p473 := Ns252p472 186065264 42 67108856 8 216015088 42 60023992 8 Bool.false 208054825 34103 Bool.false 184840659 Bool.false 64592105 7074237752028440 1 Bool.false 131709595 Bool.false Bool.false 62127559 Bool.true Bool.false 246125325 

noncomputable def Ns252p474 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 553088 1000 367 225 134217728 67108864 2251799813685248 Bool.false 129027237233 1833 

noncomputable def Ns252p475 := Ns252p474 93032624 42 94906264 8 147453232 42 77490640 16 Bool.false 134217712 1882 Bool.false 197871203 Bool.false 36163372 7074237752028440 1 Bool.false 133592748 Bool.false Bool.false 35727399 Bool.true Bool.false 208054825 

noncomputable def Ns252p476 := nat_lit 3404006218155424299532001620128713868496927789997461 

noncomputable def Ns252p477 := nat_lit 3540942133583529380618409000290428159161217843200 

noncomputable def Ns252p478 := nat_lit 24843530676160981341723180400640000 

noncomputable def Ns252p479 := nat_lit 82443983610335955876354337676671057920 

noncomputable abbrev qz626 := (@Eq.refl Real qz752)

noncomputable abbrev qz420 := qz626

noncomputable abbrev qz83 := qz420

noncomputable def Ns252p480 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz80 553088 1000 1223626342976 16000000 1106176 4000 2000 Ns252p478 Ns252p479 qz83 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns252p481 := nat_lit 4461699030260677737882585163535107841716293192905472081920 

noncomputable abbrev qz627 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1106176))))

noncomputable abbrev qz421 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 553088 4000) (Real.log (Enclosure.sfrac Bool.false 1223626342976 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz627))

noncomputable abbrev qz628 := (Enclosure.sfrac Bool.false 553088 2000)

noncomputable abbrev qz84 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz421 qz628) (@HMul.hMul Real Real Real qz346 qz628 (Real.log Real.pi)))

noncomputable def Ns252p482 := @Enclosure.Real.IsNear.addLit_ft_p qz84 (Enclosure.sfrac Bool.true Ns252p478 Ns252p479) 54117962687428419701 56294995342131200 17694785728698317 1296000000000000000000 Ns252p478 Ns252p479 0 1 Ns252p481 

noncomputable def Ns252p483 := nat_lit 141866992107332356540989440000 

noncomputable abbrev qz85 := (@HSub.hSub Real Real Real qz350 qz421 qz628)

noncomputable def Ns252p484 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (@HMul.hMul Real Real Real qz5 qz628 (Real.log Real.pi)) 359695834704545800777 281474976710656000 438350179210637 81000000000000000000 165972898281 524288000 4321 524288000 Ns252p483 54117962687428419701 56294995342131200 

noncomputable abbrev qz86 := qz421

noncomputable def Ns252p485 := @Enclosure.Real.IsNear.subLit_ff_p qz86 qz628 437536050664017453641 281474976710656000 438350179210637 81000000000000000000 553088 2000 0 1 719391669409091601554000 359695834704545800777 281474976710656000 438350179210637 81000000000000000000 

noncomputable def Ns252p486 := nat_lit 30788862417681679111967393787674624 

noncomputable def Ns252p487 := nat_lit 27188114719911345678974976 

noncomputable def Ns252p488 := nat_lit 14450115519942843695135398566026537555013914135111143351783079368339205652480 

noncomputable def Ns252p489 := nat_lit 28690118246435179866963414478317519090142699693012377057983697587898679296 

noncomputable def Ns252p490 := nat_lit 431587696122818272631113374752381490652543851797107266974779063664640 

noncomputable def Ns252p491 := BSN.log_dyadic_bound 175050342976 2272202342976 4 3 Ns252p488 67108864 25920000 Ns252p489 Ns252p490 10360656 2447252685952 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 175050342976) (BSN.artanhQ 2272202342976) 0 3 Ns252p489 Ns252p488 Ns252p490 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz422 := (Real.log (Enclosure.sfrac Bool.false 1223626342976 16000000))

noncomputable def Ns252p492 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 553088 4000) qz422 553088 4000 0 1 3165113124986103 281474976710656 195312581 5062500000000000 13676453813064951063 8796093022208000 843945662501 158203125000000000 (Enclosure.Real.IsNear.const Bool.false 553088 4000) (BSN.isNear_log_sfrac 1223626342976 16000000 3165113124986103 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1223626342976) qz353)) Bool.false Ns252p487 Ns252p93 1000000414720000 25920000000000000000000 3165113124986103 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1223626342976 16000000 16 2447252685952 2097152000000 10360656 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns252p491 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p493 := BSN.arctan_dyadic_bound_f 1000 1106176 1 0 8388608 3240000 0 1 1 0 1 1 7583 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1106176) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1106176) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz423 := (@Nat.cast Real Real.instNatCast 1106176)

noncomputable def Ns252p494 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 qz423)) 884279719003555 562949953421312 1 2000000000000000 7583 8388608 1 3240000 7413607075574179692544 883770832487843 562949953421312 50000000081 162000000000000000 qz17 (Ns252p493 rfl) rfl rfl 

noncomputable abbrev qz424 := (@HMul.hMul Real Real Real qz584 qz589 qz627)

noncomputable abbrev qz87 := qz424

noncomputable abbrev qz425 := qz627

noncomputable abbrev qz88 := qz425

noncomputable def Ns252p495 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 553088 4000) qz422) qz87 13676453813064951063 8796093022208000 843945662501 158203125000000000 883770832487843 2251799813685248 50000000081 648000000000000000 Ns252p486 437536050664017453641 281474976710656000 438350179210637 81000000000000000000 (Ns252p492 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz88 1 4 0 1 883770832487843 562949953421312 50000000081 162000000000000000 883770832487843 2251799813685248 50000000081 648000000000000000 qz361 Ns252p494 rfl) 

noncomputable def Ns252p496 := @Ns252p482 Ns252p476 Ns252p477 17694785728698317 1296000000000000000000 (@Ns252p484 17694785728698317 1296000000000000000000 (Ns252p485 (Ns252p495 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 553088 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz628 (Real.log Real.pi) 553088 2000 0 1 38410761 33554432 1 33554432 165972898281 524288000 4321 524288000 (Enclosure.Real.IsNear.const Bool.false 553088 2000) RS253to264.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns252p478 Ns252p479) 

noncomputable def Ns252p497 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns252p476 Ns252p477 17694785728698317 1296000000000000000000 8064202327 8388608 115 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz362 qz84 (Enclosure.sfrac Bool.true Ns252p478 Ns252p479)) Bool.false Ns252p476 Ns252p477 17694785728698317 1296000000000000000000 Ns252p480 (Ns252p496 rfl rfl)) 

noncomputable def Ns252p498 := BSN.cos_dyadic_bound_f 16430722 34359738368 1 0 16777216 6486329 0 1 1 0 1 1 16777214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 16430722) (BSN.cosEvenQ 34359738368) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 16430722) (BSN.cosOddQ 34359738368) 0 0 rfl) rfl rfl 

noncomputable def Ns252p499 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz80) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8064202327) qz365) Bool.false 8064202327 8388608 115 8388608 Bool.false 16777214 16777216 1 3240000 (Ns252p497 rfl) (Enclosure.sfrac_false_div 8064202327 8388608) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8064202327) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 578104640015081406464) qz366) 226375608064910080 72057594037927936 Bool.false 16777214 16777216 153 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q0 8064202327 8388608 226375608064910080 72057594037927936 153 578104640015081406464 Ns252p105 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777214 16777216 578104640015081406464 Ns252p105 16430722 34359738368 6486329 6480000 (Ns252p498 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p500 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns252p476 Ns252p477 17694785728698317 1296000000000000000000 129027237233 134217728 1833 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz362 qz84 (Enclosure.sfrac Bool.true Ns252p478 Ns252p479)) Bool.false Ns252p476 Ns252p477 17694785728698317 1296000000000000000000 Ns252p480 (Ns252p496 rfl rfl)) 

noncomputable def Ns252p501 := Ns252p475 34103 BSN.abs_quadSignPos (BSN.cos_quad_nat3 367 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133592748 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 225 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 35727399 134217728) qz83 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) Bool.false 8388607 8388608 5952947 424673280000 134217712 134217728 1882 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 8388607 8388608 5952947 424673280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz80) qz80) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 16777214 16777216 380988608 27179089920000 8388607 8388608 5952947 424673280000 (Ns252p499 rfl rfl) rfl)) rfl) (Ns252p500 rfl) RS253to264.d7 

noncomputable def Ns252p502 := nat_lit 8390475610516317826179060179295975103259335963398147634749038313938451670386899644444105302528564292560241 

noncomputable def Ns252p503 := nat_lit 3602393331163717675082314386200459400453151121300044980763609670877954764734976130786859939163088241 

noncomputable def Ns252p504 := nat_lit 41911915014513760118137337363100030762647588648996161205948758434782745296184814598611217125794512645727601 

noncomputable def Ns252p505 := BSN.sin_dyadic_bound_f 197871203 134217728 4 3 134217728 67108864 Ns252p502 Ns252p137 Ns252p503 Ns252p504 Ns252p140 Ns252p503 133592748 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 197871203) qz367 0 3 Ns252p502 Ns252p137 Ns252p503 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 197871203) qz368 0 3 Ns252p504 Ns252p140 Ns252p503 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p506 := nat_lit 1710313309378588427164447027456 

noncomputable def Ns252p507 := BSN.sin_dyadic_bound_f 36163372 134217728 2 1 134217728 67108864 Ns252p506 Ns252p238 Ns252p506 Ns252p506 Ns252p239 Ns252p506 35727399 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 36163372) qz367 0 1 Ns252p506 Ns252p238 Ns252p506 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 36163372) qz368 0 1 Ns252p506 Ns252p239 Ns252p506 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p508 := nat_lit 6386818375388502614821616304673799471994135757542122496715952000006689720419904970311442001722129051570481 

noncomputable def Ns252p509 := nat_lit 1590633403771185823904159473699871230813822601456709607532276275201607184772095817490031734170341681 

noncomputable def Ns252p510 := nat_lit 31910631180010003946922630112975692060830609423213517636616327023212735617787266169915478455089926733582641 

noncomputable def Ns252p511 := BSN.sin_dyadic_bound_f 184840659 134217728 4 3 134217728 67108864 Ns252p508 Ns252p137 Ns252p509 Ns252p510 Ns252p140 Ns252p509 131709595 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 184840659) qz367 0 3 Ns252p508 Ns252p137 Ns252p509 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 184840659) qz368 0 3 Ns252p510 Ns252p140 Ns252p509 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p512 := nat_lit 17082316887653911333067383484499542959323359663303297259453228930625 

noncomputable def Ns252p513 := nat_lit 302995029671991676067618482157274633830513691462262724437890625 

noncomputable def Ns252p514 := nat_lit 44738910809045536933415228219956262639296883048389125349395081090625 

noncomputable def Ns252p515 := BSN.sin_dyadic_bound_f 64592105 134217728 3 2 134217728 67108864 Ns252p512 Ns252p116 Ns252p513 Ns252p514 Ns252p119 Ns252p513 62127559 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 64592105) qz367 0 2 Ns252p512 Ns252p116 Ns252p513 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 64592105) qz368 0 2 Ns252p514 Ns252p119 Ns252p513 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p516 := Ns252p473 57863 BSN.abs_quadSignPos (BSN.cos_quad_nat3 123 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131709595 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 45 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 62127559 134217728) qz83 rfl rfl (Ns252p501 RS253to264.d9 RS253to264.d11 RS253to264.d13 RS253to264.d17 (Ns252p505 rfl rfl) (Ns252p507 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns252p500 rfl) RS253to264.d19 RS253to264.d21 RS253to264.d23 RS253to264.d25 RS253to264.d17 (Ns252p511 rfl rfl) (Ns252p515 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns252p517 := nat_lit 2614607679724649153575403228743408129147546040236841197331369837566479715967459143237893770344365562003456 

noncomputable def Ns252p518 := nat_lit 1911796498046431987975264594438039296733322274456241445054996453030790735743184365948816255956811776 

noncomputable def Ns252p519 := nat_lit 15837925250872531694488396463862294600616433323270301964825231817686971587313765701340024582443497297018880 

noncomputable def Ns252p520 := BSN.cos_dyadic_bound_f 187695332 134217728 4 3 134217728 67108864 Ns252p517 Ns252p398 Ns252p518 Ns252p519 Ns252p401 Ns252p518 23019014 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 187695332) qz369 0 3 Ns252p517 Ns252p398 Ns252p518 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 187695332) qz370 0 3 Ns252p519 Ns252p401 Ns252p518 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p521 := nat_lit 1565807274953818263522726937921 

noncomputable def Ns252p522 := BSN.sin_dyadic_bound_f 35374033 134217728 2 1 134217728 67108864 Ns252p521 Ns252p238 Ns252p521 Ns252p521 Ns252p239 Ns252p521 34965925 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 35374033) qz367 0 1 Ns252p521 Ns252p238 Ns252p521 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 35374033) qz368 0 1 Ns252p521 Ns252p239 Ns252p521 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p523 := Ns252p471 77587 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 18 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 23019014 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 73 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 34965925 134217728) qz83 rfl rfl (Ns252p516 rfl rfl) (Ns252p500 rfl) RS253to264.d27 RS253to264.d29 RS253to264.d31 RS253to264.d33 RS253to264.d17 (Ns252p520 rfl rfl) (Ns252p522 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p524 := nat_lit 2319828904498364440723264519696 

noncomputable def Ns252p525 := BSN.cos_dyadic_bound_f 39026894 134217728 2 1 134217728 67108864 Ns252p524 Ns252p122 Ns252p524 Ns252p524 Ns252p123 Ns252p524 128583608 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 39026894) qz369 0 1 Ns252p524 Ns252p122 Ns252p524 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 39026894) qz370 0 1 Ns252p524 Ns252p123 Ns252p524 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p526 := nat_lit 362007116215193489527239408573326086528065058502780194256968650588160 

noncomputable def Ns252p527 := nat_lit 135976938329805389581536843468807663088748653046310899609245843456 

noncomputable def Ns252p528 := nat_lit 947893722663448978131066438993095014214217179211873148264121972555776 

noncomputable def Ns252p529 := BSN.sin_dyadic_bound_f 138574448 134217728 3 2 134217728 67108864 Ns252p526 Ns252p116 Ns252p527 Ns252p528 Ns252p119 Ns252p527 115234361 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 138574448) qz367 0 2 Ns252p526 Ns252p116 Ns252p527 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 138574448) qz368 0 2 Ns252p528 Ns252p119 Ns252p527 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p530 := Ns252p469 94822 BSN.abs_quadSignPos (BSN.cos_quad_nat0 120 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 128583608 134217728) BSN.abs_quadSignNeg qz371 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 115234361 134217728) qz83 rfl rfl (Ns252p523 rfl) (Ns252p500 rfl) RS253to264.d35 RS253to264.d37 RS253to264.d39 RS253to264.d41 RS253to264.d17 (Ns252p525 rfl rfl) (Ns252p529 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p531 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) 230561690 134217728 94822 134217728 230561690 134217728 94822 134217728 61890932391280640 115280845 33554432 47411 33554432 (Ns252p530 rfl) 

noncomputable def Ns252p532 := @Enclosure.Real.IsNear.mulLit_tf qz625 (Zeta.RiemannSiegel.correction qz82) 5477297 16777216 1 16777216 28663711453125 70368744177664 41415530952403 1187472557998080000 156999660751067203125 1180591620717411303424 

noncomputable abbrev qz629 := (@HPow.hPow Real Real Real qz7 qz81 qz9)

noncomputable def Ns252p533 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz629 1 1 0 1 5477297 16777216 1 16777216 5477297 16777216 1 16777216 

noncomputable def Ns252p534 := @Enclosure.Real.IsNear.sqrt_image qz81 11537834817 131072000 4321 131072000 78704037 78704068 8388608 (@Enclosure.Real.IsNear.of_eq qz81 (@HMul.hMul Real Real Real qz5 qz80 qz3) Bool.false 11537834817 131072000 4321 131072000 (BSN.t_div_two_pi_mk qz80 553088 1000 qz83) (@Enclosure.Real.IsNear.mulLit_ff qz80 qz3 553088 1000 0 1 2670177 16777216 1 16777216 11537834817 131072000 4321 131072000 (Enclosure.Real.IsNear.const Bool.false 553088 1000) RS253to264.d44 rfl)) 

noncomputable abbrev qz755 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 553088 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz630 := qz755

noncomputable abbrev qz426 := qz630

noncomputable abbrev qz89 := qz426

noncomputable def Ns252p535 := @Enclosure.Real.IsNear.sqrt_image qz89 157408105 16777216 31 16777216 25694694 25694700 8388608 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 157408105 16777216 31 16777216 157408105 16777216 31 16777216 (Ns252p534 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns252p536 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz89) 25694697 8388608 3 8388608 2738648 2738649 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz89) Bool.false 51389394 16777216 6 16777216 25694697 8388608 3 8388608 (Ns252p535 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns252p537 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 5477297 16777216 1 16777216 5477297 16777216 1 16777216 (Ns252p536 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz427 := (@HMul.hMul Real Real Real qz584 qz582 qz624)

noncomputable abbrev qz90 := (Real.cos qz427)

noncomputable abbrev qz631 := (@HMul.hMul Real Real Real qz735 qz754 qz754)

noncomputable abbrev qz428 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz631 qz624) qz599)

noncomputable abbrev qz91 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz428))

noncomputable def Ns252p538 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz82) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz90) qz91) Bool.false 28663711453125 

noncomputable def Ns252p539 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz90) qz91 22715175 16777216 369 

noncomputable abbrev qz92 := (@Neg.neg Real Real.instNeg (Real.cos qz427))

noncomputable def Ns252p540 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz90) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz92)) Bool.true 22715175 16777216 369 16777216 (BSN.inv_eq_neg_inv_neg qz90) 

noncomputable def Ns252p541 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz92) Bool.false 22715175 16777216 369 16777216 22715175 16777216 

noncomputable def Ns252p542 := @Enclosure.Real.IsNear.recentre' qz90 Bool.true 12391495 16777216 162954304 13589544960000 12391495 16777216 2546161 212336640000 

noncomputable abbrev qz93 := qz427

noncomputable def Ns252p543 := @Enclosure.Real.IsNear.cos_image qz93 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20147539) qz365) Bool.false 20147539 8388608 49 4194304 Bool.true 12391495 16777216 1 

noncomputable def Ns252p544 := nat_lit 836568337735454042628203289 

noncomputable def Ns252p545 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz82 884279719003555 140737488355328 1 500000000000000 6413161 16777216 31 16777216 5671028207004557787355 2361183241434822606848 Ns252p544 

noncomputable def Ns252p546 := @Enclosure.Real.IsNear.subLit_ff_p qz89 qz1 157408105 16777216 31 16777216 9 1 0 1 6413161 6413161 16777216 31 

noncomputable def Ns252p547 := @Ns252p546 16777216 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 157408105 16777216 31 16777216 157408105 16777216 31 16777216 (Ns252p534 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns252p548 := @Enclosure.Real.IsNear.recentre' qz93 Bool.false 5671028207004557787355 2361183241434822606848 Ns252p544 Ns252p168 20147539 8388608 49 4194304 (@Ns252p545 Ns252p168 RS253to264.d43 (Ns252p547 rfl rfl) rfl) 

noncomputable def Ns252p549 := nat_lit 2801599629603988286206266029497059746989101278605359970071689100162800170735152675390625 

noncomputable def Ns252p550 := nat_lit 441685187838499147630333783222549313722440605005169717643729818111703003082275390625 

noncomputable def Ns252p551 := nat_lit 7336807730087278417634533346367081876558762254415458218263953033101819594682314275390625 

noncomputable def Ns252p552 := BSN.sin_dyadic_bound_f 28552168925 34359738368 3 2 16777216 6486329 Ns252p549 Ns252p288 Ns252p550 Ns252p551 Ns252p291 Ns252p550 12391495 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 28552168925) qz363 0 2 Ns252p549 Ns252p288 Ns252p550 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 28552168925) qz364 0 2 Ns252p551 Ns252p291 Ns252p550 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p553 := @Ns252p543 3240000 (Ns252p548 rfl) (Enclosure.sfrac_false_div 20147539 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20147539) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1004590135432471923130368) qz366) 226375608064910080 72057594037927936 Bool.false 12391495 16777216 0 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 20147539 8388608 226375608064910080 72057594037927936 0 1004590135432471923130368 Ns252p105 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 12391495 16777216 1004590135432471923130368 Ns252p105 28552168925 34359738368 6486329 6480000 (Ns252p552 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p554 := @Enclosure.Real.IsNear.inv_image qz92 12391495 16777216 2546161 212336640000 11357403 11357772 8388608 (@Enclosure.Real.IsNear.neg qz90 Bool.true 12391495 16777216 2546161 212336640000 (Ns252p542 (Ns252p553 rfl rfl) rfl)) 

noncomputable def Ns252p555 := Ns252p540 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz92) Bool.false 22715175 16777216 369 16777216 (@Ns252p541 369 16777216 (Ns252p554 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p556 := @Enclosure.Real.IsNear.recentre' qz91 Bool.true 2523750 8388608 

noncomputable abbrev qz94 := (@HMul.hMul Real Real Real qz346 qz343 qz428)

noncomputable def Ns252p557 := @Enclosure.Real.IsNear.cos_image qz94 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 31480513)) qz410) Bool.true 31480513 16777216 

noncomputable def Ns252p558 := nat_lit 74331261575961064379317423405 

noncomputable def Ns252p559 := nat_lit 4953081701691610937783004637407669 

noncomputable def Ns252p560 := @Enclosure.Real.IsNear.recentre' qz94 Bool.true Ns252p558 Ns252p183 Ns252p559 

noncomputable def Ns252p561 := nat_lit 241785163922925834941235200000000000000 

noncomputable abbrev qz95 := qz428

noncomputable def Ns252p562 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz95 884279719003555 140737488355328 1 500000000000000 84058539372271 

noncomputable abbrev qz429 := (@HSub.hSub Real Real Real qz588 qz631 qz624)

noncomputable abbrev qz96 := qz429

noncomputable def Ns252p563 := @Enclosure.Real.IsNear.subLit_tf qz96 qz31 66466353327855 281474976710656 917710639 281474976710656 1 16 

noncomputable abbrev qz430 := qz631

noncomputable abbrev qz97 := qz430

noncomputable def Ns252p564 := @Enclosure.Real.IsNear.subLit_ff_n qz97 qz82 41128634011921 281474976710656 397616943 281474976710656 6413161 16777216 31 16777216 

noncomputable def Ns252p565 := @Enclosure.Real.IsNear.mulLit_ff qz82 qz82 6413161 16777216 31 16777216 6413161 16777216 31 16777216 41128634011921 281474976710656 

noncomputable def Ns252p566 := nat_lit 123950466489553032697918041854851378400348157976660120250049306589369531474615315644377925116161 

noncomputable def Ns252p567 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600 

noncomputable def Ns252p568 := nat_lit 947330698641333881684535853497742946833515859916969457367442085365191676045111426294964481 

noncomputable def Ns252p569 := nat_lit 748289476575031939954877676582615271640904974912648169619958431946743240460351527218300702384385 

noncomputable def Ns252p570 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600 

noncomputable def Ns252p571 := BSN.cos_dyadic_bound_t 31480513 16777216 4 3 8388608 3240000 Ns252p566 Ns252p567 Ns252p568 Ns252p569 Ns252p570 Ns252p568 2523750 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 31480513) (BSN.cosEvenQ 16777216) 0 3 Ns252p566 Ns252p567 Ns252p568 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 31480513) (BSN.cosOddQ 16777216) 0 3 Ns252p569 Ns252p570 Ns252p568 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p572 := @Ns252p556 1134577216 54358179840000 1261875 4194304 17727769 849346560000 (@Ns252p557 345 16777216 Bool.true 2523750 8388608 1 3240000 (@Ns252p560 Ns252p561 31480513 16777216 345 16777216 (@Ns252p562 281474976710656 917710639 281474976710656 Ns252p558 Ns252p183 Ns252p559 Ns252p561 RS253to264.d43 (@Ns252p563 0 1 1344936629956336 84058539372271 281474976710656 917710639 281474976710656 (@Ns252p564 1115120366513742151680 66466353327855 281474976710656 917710639 281474976710656 (@Ns252p565 397616943 281474976710656 (Ns252p547 rfl rfl) (Ns252p547 rfl rfl) rfl) (Ns252p547 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 31480513 16777216) (BSN.cos_neg_of_bound 31480513 16777216 Bool.true 2523750 8388608 1 3240000 (Ns252p571 rfl rfl)) rfl rfl) 

noncomputable def Ns252p573 := @Ns252p532 75776301661768843823 Ns252p465 (Ns252p533 qz33 (@Enclosure.Real.IsNear.of_eq qz629 (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 5477297 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz81 (BSN.t_div_two_pi_nonneg qz80 553088 1000 qz83)) Ns252p537) rfl) (@Ns252p538 70368744177664 41415530952403 1187472557998080000 (BSN.correction_mk qz82 (BSN.cos_two_pi_p_ne_zero_mk qz80 553088 1000 9 qz83 rfl rfl (@BSN.floor_sqrt_eq_dec qz80 553088 1000 9 qz83 rfl rfl rfl))) (@Ns252p539 16777216 1261875 4194304 17727769 849346560000 28663711453125 70368744177664 41415530952403 1187472557998080000 Ns252p555 (Ns252p572 rfl) rfl)) 

noncomputable def Ns252p574 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (hardyZApproximantRS₀ qz80) Bool.false 4213083805946035226165 1180591620717411303424 9458986542869597323823 Ns252p465 (@Eq.refl Real (hardyZApproximantRS₀ qz80)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) (@HMul.hMul Real Real Real qz5 qz625 (Zeta.RiemannSiegel.correction qz82))) Bool.false 4213083805946035226165 1180591620717411303424 9458986542869597323823 Ns252p465 (BSN.hardyZApproximantRS₀_eq qz80 9 (@BSN.floor_sqrt_eq_dec qz80 553088 1000 9 qz83 rfl rfl rfl)) (@Ns252p467 4213083805946035226165 1180591620717411303424 9458986542869597323823 Ns252p465 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 9)) Bool.false 115280845 33554432 47411 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz80) qz80 9) (Ns252p531 (Ns252p530 rfl) rfl rfl)) (Ns252p573 rfl) rfl rfl)) 

theorem RS253to264.d50 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz80) Bool.false 4213083805946035226165 1180591620717411303424 9458986542869597323823 Ns252p465 := Ns252p574 

noncomputable def Ns252p575 := nat_lit 683056277341668672666549092352 

noncomputable abbrev qz756 := (Enclosure.sfrac Bool.false 554491 1000)

noncomputable abbrev qz632 := qz756

noncomputable abbrev qz431 := qz632

noncomputable abbrev qz98 := qz431

noncomputable abbrev qz757 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 554491 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz633 := qz757

noncomputable abbrev qz432 := qz633

noncomputable abbrev qz99 := qz432

noncomputable abbrev qz758 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 554491 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz634 := qz758

noncomputable abbrev qz433 := qz634

noncomputable abbrev qz100 := qz433

noncomputable abbrev qz635 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz99 qz9))

noncomputable def Ns252p576 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) (@HMul.hMul Real Real Real qz5 qz635 (Zeta.RiemannSiegel.correction qz100)) 298099439 67108864 23767 16777216 310109888110362015655 2361183241434822606848 5726760796721467909 531266229322835086540800 Ns252p575 

noncomputable def Ns252p577 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 554491 1000 120 161 134217728 67108864 2251799813685248 Bool.false 129448942998 1838 

noncomputable def Ns252p578 := Ns252p577 279097919 42 47453128 8 294906479 42 44739240 8 Bool.true 308462547 77789 Bool.true 8895510 Bool.true 130622473 7074237752028440 1 Bool.false 133923053 Bool.false Bool.false 110957514 Bool.true Bool.true 298099439 

noncomputable def Ns252p579 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 554491 1000 18 72 134217728 67108864 2251799813685248 Bool.false 129448942998 1838 

noncomputable def Ns252p580 := Ns252p579 240485871 42 54794152 8 261175631 42 50729528 8 Bool.true 276632464 58014 Bool.true 103391244 Bool.true 190926393 7074237752028440 1 Bool.false 96325986 Bool.true Bool.false 19829465 Bool.false Bool.true 308462547 

noncomputable def Ns252p581 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 554491 1000 124 45 134217728 67108864 2251799813685248 Bool.false 129448942998 1838 

noncomputable def Ns252p582 := Ns252p581 186065264 42 67108856 8 216015088 42 60023992 8 Bool.true 253942460 34193 Bool.false 134668144 Bool.false 183228701 7074237752028440 1 Bool.false 72138728 Bool.false Bool.false 131389933 Bool.true Bool.true 276632464 

noncomputable def Ns252p583 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 554491 1000 369 226 134217728 67108864 2251799813685248 Bool.false 129448942998 1838 

noncomputable def Ns252p584 := Ns252p583 93032624 42 94906264 8 147453232 42 77490640 16 Bool.true 134217680 1890 Bool.false 67394768 Bool.false 40163538 7074237752028440 1 Bool.false 64598164 Bool.true Bool.false 128253134 Bool.true Bool.true 253942460 

noncomputable def Ns252p585 := nat_lit 284052742360684917388611414512874555364222722656801736529 

noncomputable def Ns252p586 := nat_lit 294516995107529843386608130126503580634057231302656000 

noncomputable def Ns252p587 := nat_lit 25160231879245876280034934456480000 

noncomputable def Ns252p588 := nat_lit 83706764572619318694992253462744310080 

noncomputable abbrev qz636 := (@Eq.refl Real qz756)

noncomputable abbrev qz434 := qz636

noncomputable abbrev qz101 := qz434

noncomputable def Ns252p589 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz98 554491 1000 1229842076324 16000000 1108982 4000 2000 Ns252p587 Ns252p588 qz101 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns252p590 := nat_lit 90896877555419173564355652644119857716551271250176555689280 

noncomputable abbrev qz637 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1108982))))

noncomputable abbrev qz435 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 554491 4000) (Real.log (Enclosure.sfrac Bool.false 1229842076324 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz637))

noncomputable abbrev qz638 := (Enclosure.sfrac Bool.false 554491 2000)

noncomputable abbrev qz102 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz435 qz638) (@HMul.hMul Real Real Real qz346 qz638 (Real.log Real.pi)))

noncomputable def Ns252p591 := @Enclosure.Real.IsNear.addLit_ft_p qz102 (Enclosure.sfrac Bool.true Ns252p587 Ns252p588) 1085896777248687212241 1125899906842624000 84097980864266941 6144000000000000000000 Ns252p587 Ns252p588 0 1 Ns252p590 

noncomputable def Ns252p592 := nat_lit 72873299142420444304820404224000 

noncomputable abbrev qz103 := (@HSub.hSub Real Real Real qz350 qz435 qz638)

noncomputable def Ns252p593 := @Enclosure.Real.IsNear.subLit_ff_p qz103 (@HMul.hMul Real Real Real qz5 qz638 (Real.log Real.pi)) 1443224991482834011857 1125899906842624000 16275787904267 3000000000000000000 21298421277651 67108864000 554491 67108864000 Ns252p592 1085896777248687212241 1125899906842624000 

noncomputable def Ns252p594 := nat_lit 2886449982965668023714000 

noncomputable abbrev qz104 := qz435

noncomputable def Ns252p595 := @Enclosure.Real.IsNear.subLit_ff_p qz104 qz638 1755375674105370724049 1125899906842624000 16275787904267 3000000000000000000 554491 2000 0 1 Ns252p594 1443224991482834011857 1125899906842624000 16275787904267 3000000000000000000 

noncomputable def Ns252p596 := nat_lit 3952754615898090408638569880750129152 

noncomputable def Ns252p597 := nat_lit 27200365735876892072869888 

noncomputable def Ns252p598 := nat_lit 14688917928812394786716782436689657784253803552514810910861523586217166868480 

noncomputable def Ns252p599 := nat_lit 31109167934103234457261146959659574357500811070721999562428755758219882496 

noncomputable def Ns252p600 := nat_lit 532096575489906684776292024677568373432824527573895459997608989552640 

noncomputable def Ns252p601 := BSN.log_dyadic_bound 181266076324 2278418076324 4 3 Ns252p598 67108864 25920000 Ns252p599 Ns252p600 10700690 2459684152648 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 181266076324) (BSN.artanhQ 2278418076324) 0 3 Ns252p599 Ns252p598 Ns252p600 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz436 := (Real.log (Enclosure.sfrac Bool.false 1229842076324 16000000))

noncomputable def Ns252p602 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 554491 4000) qz436 554491 4000 0 1 3166539330952439 281474976710656 195312581 5062500000000000 1755817560159148853549 1125899906842624000 108299068351271 20250000000000000000 (Enclosure.Real.IsNear.const Bool.false 554491 4000) (BSN.isNear_log_sfrac 1229842076324 16000000 3166539330952439 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1229842076324) qz353)) Bool.false Ns252p597 Ns252p93 1000000414720000 25920000000000000000000 3166539330952439 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1229842076324 16000000 16 2459684152648 2097152000000 10700690 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns252p601 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p603 := BSN.arctan_dyadic_bound_f 1000 1108982 1 0 8388608 3240000 0 1 1 0 1 1 7564 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1108982) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1108982) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns252p604 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1108982))) 884279719003555 562949953421312 1 2000000000000000 7564 8388608 1 3240000 7413617771623294697472 883772107556259 562949953421312 50000000081 162000000000000000 qz17 (Ns252p603 rfl) rfl rfl 

noncomputable abbrev qz437 := (@HMul.hMul Real Real Real qz584 qz589 qz637)

noncomputable abbrev qz105 := qz437

noncomputable abbrev qz438 := qz637

noncomputable abbrev qz106 := qz438

noncomputable def Ns252p605 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 554491 4000) qz436) qz105 1755817560159148853549 1125899906842624000 108299068351271 20250000000000000000 883772107556259 2251799813685248 50000000081 648000000000000000 Ns252p596 1755375674105370724049 1125899906842624000 16275787904267 3000000000000000000 (Ns252p602 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz106 1 4 0 1 883772107556259 562949953421312 50000000081 162000000000000000 883772107556259 2251799813685248 50000000081 648000000000000000 qz361 Ns252p604 rfl) 

noncomputable def Ns252p606 := @Ns252p591 Ns252p585 Ns252p586 84097980864266941 6144000000000000000000 (@Ns252p593 84097980864266941 6144000000000000000000 (Ns252p595 (Ns252p605 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 554491 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz638 (Real.log Real.pi) 554491 2000 0 1 38410761 33554432 1 33554432 21298421277651 67108864000 554491 67108864000 (Enclosure.Real.IsNear.const Bool.false 554491 2000) RS253to264.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns252p587 Ns252p588) 

noncomputable def Ns252p607 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns252p585 Ns252p586 84097980864266941 6144000000000000000000 8090558937 8388608 231 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz362 qz102 (Enclosure.sfrac Bool.true Ns252p587 Ns252p588)) Bool.false Ns252p585 Ns252p586 84097980864266941 6144000000000000000000 Ns252p589 (Ns252p606 rfl rfl)) 

noncomputable def Ns252p608 := BSN.cos_dyadic_bound_f 28803645 34359738368 1 0 16777216 6486329 0 1 1 0 1 1 16777210 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 28803645) (BSN.cosEvenQ 34359738368) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 28803645) (BSN.cosOddQ 34359738368) 0 0 rfl) rfl rfl 

noncomputable def Ns252p609 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz98) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8090558937) qz365) Bool.false 8090558937 8388608 231 16777216 Bool.true 16777210 16777216 1 3240000 (Ns252p607 rfl) (Enclosure.sfrac_false_div 8090558937 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8090558937) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1013438195660283183104) qz366) 226375608064910080 72057594037927936 Bool.false 16777210 16777216 153 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q2 8090558937 8388608 226375608064910080 72057594037927936 153 1013438195660283183104 Ns252p105 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777210 16777216 1013438195660283183104 Ns252p105 28803645 34359738368 6486329 6480000 (Ns252p608 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p610 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns252p585 Ns252p586 84097980864266941 6144000000000000000000 129448942998 134217728 1838 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz362 qz102 (Enclosure.sfrac Bool.true Ns252p587 Ns252p588)) Bool.false Ns252p585 Ns252p586 84097980864266941 6144000000000000000000 Ns252p589 (Ns252p606 rfl rfl)) 

noncomputable def Ns252p611 := Ns252p584 34193 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 369 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 64598164 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 226 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 128253134 134217728) qz101 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) Bool.true 8388605 8388608 11956519 849346560000 134217680 134217728 1890 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 8388605 8388608 11956519 849346560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz98) qz98) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 16777210 16777216 765217216 54358179840000 8388605 8388608 11956519 849346560000 (Ns252p609 rfl rfl) rfl)) rfl) (Ns252p610 rfl) RS253to264.d7 

noncomputable def Ns252p612 := nat_lit 20245811029776996892700138733899671237177378044986561714568948613120 

noncomputable def Ns252p613 := nat_lit 425607684866210540748288406094789008200551916370463794005016576 

noncomputable def Ns252p614 := nat_lit 53024054094116637044767723264698795010403665414719252311061714436096 

noncomputable def Ns252p615 := BSN.sin_dyadic_bound_f 67394768 134217728 3 2 134217728 67108864 Ns252p612 Ns252p116 Ns252p613 Ns252p614 Ns252p119 Ns252p613 64598164 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 67394768) qz367 0 2 Ns252p612 Ns252p116 Ns252p613 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 67394768) qz368 0 2 Ns252p614 Ns252p119 Ns252p613 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p616 := nat_lit 2602123177422109745483122373136 

noncomputable def Ns252p617 := BSN.cos_dyadic_bound_f 40163538 134217728 2 1 134217728 67108864 Ns252p616 Ns252p122 Ns252p616 Ns252p616 Ns252p123 Ns252p616 128253134 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 40163538) qz369 0 1 Ns252p616 Ns252p122 Ns252p616 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 40163538) qz370 0 1 Ns252p616 Ns252p123 Ns252p616 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p618 := nat_lit 179419742670130218004468550663413189440405043936320650140833437188096 

noncomputable def Ns252p619 := nat_lit 108173030715582723032350548336932542255130057065017231419864252416 

noncomputable def Ns252p620 := nat_lit 538042881948959488567340950893565703236704871694831915959660583059456 

noncomputable def Ns252p621 := BSN.cos_dyadic_bound_f 134668144 134217728 3 2 134217728 67108864 Ns252p618 Ns252p144 Ns252p619 Ns252p620 Ns252p147 Ns252p619 72138728 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 134668144) qz369 0 2 Ns252p618 Ns252p144 Ns252p619 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 134668144) qz370 0 2 Ns252p620 Ns252p147 Ns252p619 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p622 := nat_lit 6166670891496935547265650559123603234030024826775292389676682070223813779760203045121302259481651857311601 

noncomputable def Ns252p623 := nat_lit 1431930805170319250980978102542175580667917099396088101931371531813813089748234179092733399602284401 

noncomputable def Ns252p624 := nat_lit 30811481635927346235499397546273268057860421899870743709593333065419482500508223795962881898414323744098161 

noncomputable def Ns252p625 := BSN.sin_dyadic_bound_f 183228701 134217728 4 3 134217728 67108864 Ns252p622 Ns252p137 Ns252p623 Ns252p624 Ns252p140 Ns252p623 131389933 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 183228701) qz367 0 3 Ns252p622 Ns252p137 Ns252p623 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 183228701) qz368 0 3 Ns252p624 Ns252p140 Ns252p623 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p626 := Ns252p582 58014 BSN.abs_quadSignPos (BSN.cos_quad_nat0 124 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 72138728 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 45 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 131389933 134217728) qz101 rfl rfl (Ns252p611 RS253to264.d9 RS253to264.d11 RS253to264.d13 RS253to264.d17 (Ns252p615 rfl rfl) (Ns252p617 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns252p610 rfl) RS253to264.d19 RS253to264.d21 RS253to264.d23 RS253to264.d25 RS253to264.d17 (Ns252p621 rfl rfl) (Ns252p625 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns252p627 := nat_lit 62312456727155734256362580674340661655513939044284216671744305463296 

noncomputable def Ns252p628 := nat_lit 13057802217534403775883118656236069294679371304671218346837999616 

noncomputable def Ns252p629 := nat_lit 186911254577032133961535975785709512827952458390243307578539240390656 

noncomputable def Ns252p630 := BSN.cos_dyadic_bound_f 103391244 134217728 3 2 134217728 67108864 Ns252p627 Ns252p144 Ns252p628 Ns252p629 Ns252p147 Ns252p628 96325986 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 103391244) qz369 0 2 Ns252p627 Ns252p144 Ns252p628 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 103391244) qz370 0 2 Ns252p629 Ns252p147 Ns252p628 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p631 := nat_lit 2799795132653017042151482647548172657465014316882197851282944871232986910672565838462496147347632645704481 

noncomputable def Ns252p632 := nat_lit 2346343621747882186631444591196897922900309005672841378282156289810701799981847238542198753625344801 

noncomputable def Ns252p633 := nat_lit 16957879610492411428902515587072346235863367323952863571425862431095729837296166307397229583383053322390305 

noncomputable def Ns252p634 := BSN.cos_dyadic_bound_f 190926393 134217728 4 3 134217728 67108864 Ns252p631 Ns252p398 Ns252p632 Ns252p633 Ns252p401 Ns252p632 19829465 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 190926393) qz369 0 3 Ns252p631 Ns252p398 Ns252p632 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 190926393) qz370 0 3 Ns252p633 Ns252p401 Ns252p632 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p635 := Ns252p580 77789 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 18 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 96325986 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 72 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 19829465 134217728) qz101 rfl rfl (Ns252p626 rfl rfl) (Ns252p610 rfl) RS253to264.d27 RS253to264.d29 RS253to264.d31 RS253to264.d33 RS253to264.d17 (Ns252p630 rfl rfl) (Ns252p634 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p636 := nat_lit 6261572434827061405232010000 

noncomputable def Ns252p637 := BSN.cos_dyadic_bound_f 8895510 134217728 2 1 134217728 67108864 Ns252p636 Ns252p122 Ns252p636 Ns252p636 Ns252p123 Ns252p636 133923053 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 8895510) qz369 0 1 Ns252p636 Ns252p122 Ns252p636 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 8895510) qz370 0 1 Ns252p636 Ns252p123 Ns252p636 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p638 := nat_lit 285773360365724875793320005450658853119145981433018969243162077361985 

noncomputable def Ns252p639 := nat_lit 84750684396980496619504066636600512561960865605662466577933596481 

noncomputable def Ns252p640 := nat_lit 748316823659303372940358912453361547815520109970735751643345929172801 

noncomputable def Ns252p641 := BSN.sin_dyadic_bound_f 130622473 134217728 3 2 134217728 67108864 Ns252p638 Ns252p116 Ns252p639 Ns252p640 Ns252p119 Ns252p639 110957514 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 130622473) qz367 0 2 Ns252p638 Ns252p116 Ns252p639 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 130622473) qz368 0 2 Ns252p640 Ns252p119 Ns252p639 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p642 := Ns252p578 95068 BSN.abs_quadSignPos (BSN.cos_quad_nat0 120 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133923053 134217728) BSN.abs_quadSignNeg qz371 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 110957514 134217728) qz101 rfl rfl (Ns252p635 rfl) (Ns252p610 rfl) RS253to264.d35 RS253to264.d37 RS253to264.d39 RS253to264.d41 RS253to264.d17 (Ns252p637 rfl rfl) (Ns252p641 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p643 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) 298099439 134217728 95068 134217728 298099439 134217728 95068 134217728 80020458841309184 298099439 67108864 23767 16777216 (Ns252p642 rfl) 

noncomputable def Ns252p644 := @Enclosure.Real.IsNear.mulLit_tf qz635 (Zeta.RiemannSiegel.correction qz100) 5473829 16777216 1 16777216 56653192511195 140737488355328 15658178537897 474989023199232000 310109888110362015655 2361183241434822606848 

noncomputable abbrev qz639 := (@HPow.hPow Real Real Real qz7 qz99 qz9)

noncomputable def Ns252p645 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz639 1 1 0 1 5473829 16777216 1 16777216 5473829 16777216 1 16777216 

noncomputable def Ns252p646 := @Enclosure.Real.IsNear.sqrt_image qz99 1480589114907 16777216000 554491 16777216000 78803797 78803828 8388608 (@Enclosure.Real.IsNear.of_eq qz99 (@HMul.hMul Real Real Real qz5 qz98 qz3) Bool.false 1480589114907 16777216000 554491 16777216000 (BSN.t_div_two_pi_mk qz98 554491 1000 qz101) (@Enclosure.Real.IsNear.mulLit_ff qz98 qz3 554491 1000 0 1 2670177 16777216 1 16777216 1480589114907 16777216000 554491 16777216000 (Enclosure.Real.IsNear.const Bool.false 554491 1000) RS253to264.d44 rfl)) 

noncomputable abbrev qz759 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 554491 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz640 := qz759

noncomputable abbrev qz439 := qz640

noncomputable abbrev qz107 := qz439

noncomputable def Ns252p647 := @Enclosure.Real.IsNear.sqrt_image qz107 157607625 16777216 31 16777216 25710973 25710979 8388608 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 157607625 16777216 31 16777216 157607625 16777216 31 16777216 (Ns252p646 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns252p648 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz107) 200867 65536 3 8388608 2736914 2736915 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz107) Bool.false 51421952 16777216 6 16777216 200867 65536 3 8388608 (Ns252p647 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns252p649 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 5473829 16777216 1 16777216 5473829 16777216 1 16777216 (Ns252p648 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz440 := (@HMul.hMul Real Real Real qz584 qz582 qz634)

noncomputable abbrev qz108 := (Real.cos qz440)

noncomputable abbrev qz641 := (@HMul.hMul Real Real Real qz735 qz758 qz758)

noncomputable abbrev qz441 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz641 qz634) qz599)

noncomputable abbrev qz109 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz441))

noncomputable def Ns252p650 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz100) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz108) qz109) Bool.false 56653192511195 

noncomputable def Ns252p651 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz108) qz109 21321815 16777216 325 

noncomputable abbrev qz110 := (@Neg.neg Real Real.instNeg (Real.cos qz440))

noncomputable def Ns252p652 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz108) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz110)) Bool.true 21321815 16777216 325 16777216 (BSN.inv_eq_neg_inv_neg qz108) 

noncomputable def Ns252p653 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz110) Bool.false 21321815 16777216 325 16777216 21321815 16777216 

noncomputable def Ns252p654 := @Enclosure.Real.IsNear.recentre' qz108 Bool.true 13201267 16777216 648577216 54358179840000 13201267 16777216 10134019 849346560000 

noncomputable abbrev qz111 := qz440

noncomputable def Ns252p655 := @Enclosure.Real.IsNear.cos_image qz111 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10387175) qz377) Bool.false 10387175 4194304 195 16777216 Bool.true 13201267 16777216 1 

noncomputable def Ns252p656 := nat_lit 836568337737167906377999129 

noncomputable def Ns252p657 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz100 884279719003555 140737488355328 1 500000000000000 6612681 16777216 31 16777216 5847459696540147080955 2361183241434822606848 Ns252p656 

noncomputable def Ns252p658 := @Enclosure.Real.IsNear.subLit_ff_p qz107 qz1 157607625 16777216 31 16777216 9 1 0 1 6612681 6612681 16777216 31 

noncomputable def Ns252p659 := @Ns252p658 16777216 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 157607625 16777216 31 16777216 157607625 16777216 31 16777216 (Ns252p646 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns252p660 := @Enclosure.Real.IsNear.recentre' qz111 Bool.false 5847459696540147080955 2361183241434822606848 Ns252p656 Ns252p168 10387175 4194304 195 16777216 (@Ns252p657 Ns252p168 RS253to264.d43 (Ns252p659 rfl rfl) rfl) 

noncomputable def Ns252p661 := nat_lit 3953785381692145313374360665430861228152892796172412266897503897625161966823140303504545 

noncomputable def Ns252p662 := nat_lit 879570333514437891232938660123070918951089610422711170567316352650580170143188321441 

noncomputable def Ns252p663 := nat_lit 10353728123891833397489900794488246816055465082987062023788734553018751830927992775705761 

noncomputable def Ns252p664 := BSN.sin_dyadic_bound_f 31119586781 34359738368 3 2 16777216 6486329 Ns252p661 Ns252p288 Ns252p662 Ns252p663 Ns252p291 Ns252p662 13201267 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 31119586781) qz363 0 2 Ns252p661 Ns252p288 Ns252p662 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 31119586781) qz364 0 2 Ns252p663 Ns252p291 Ns252p662 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz642 := (@Nat.cast Real Real.instNatCast 604462909807314587353088)

noncomputable def Ns252p665 := @Ns252p655 3240000 (Ns252p660 rfl) (Enclosure.sfrac_false_div 10387175 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10387175) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 547461560292743609057280) qz642) 226375608064910080 72057594037927936 Bool.false 13201267 16777216 0 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 10387175 4194304 226375608064910080 72057594037927936 0 547461560292743609057280 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 13201267 16777216 547461560292743609057280 604462909807314587353088 31119586781 34359738368 6486329 6480000 (Ns252p664 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p666 := @Enclosure.Real.IsNear.inv_image qz110 13201267 16777216 10134019 849346560000 10660745 10661070 8388608 (@Enclosure.Real.IsNear.neg qz108 Bool.true 13201267 16777216 10134019 849346560000 (Ns252p654 (Ns252p665 rfl rfl) rfl)) 

noncomputable def Ns252p667 := Ns252p652 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz110) Bool.false 21321815 16777216 325 16777216 (@Ns252p653 325 16777216 (Ns252p666 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p668 := @Enclosure.Real.IsNear.recentre' qz109 Bool.true 2657053 8388608 

noncomputable abbrev qz112 := (@HMul.hMul Real Real Real qz346 qz343 qz441)

noncomputable def Ns252p669 := @Enclosure.Real.IsNear.cos_image qz112 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15880411)) qz365) Bool.true 15880411 8388608 

noncomputable def Ns252p670 := nat_lit 74993122078586146130006829805 

noncomputable def Ns252p671 := nat_lit 5019846547586491409135379833772917 

noncomputable def Ns252p672 := @Enclosure.Real.IsNear.recentre' qz112 Bool.true Ns252p670 Ns252p183 Ns252p671 

noncomputable abbrev qz113 := qz441

noncomputable def Ns252p673 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz113 884279719003555 140737488355328 1 500000000000000 84807013512751 

noncomputable abbrev qz442 := (@HSub.hSub Real Real Real qz588 qz641 qz634)

noncomputable abbrev qz114 := qz442

noncomputable def Ns252p674 := @Enclosure.Real.IsNear.subLit_tf qz114 qz31 67214827468335 281474976710656 930080879 281474976710656 1 16 

noncomputable abbrev qz443 := qz641

noncomputable abbrev qz115 := qz443

noncomputable def Ns252p675 := @Enclosure.Real.IsNear.subLit_ff_n qz115 qz100 43727550007761 281474976710656 409987183 281474976710656 6612681 16777216 31 16777216 

noncomputable def Ns252p676 := @Enclosure.Real.IsNear.mulLit_ff qz100 qz100 6612681 16777216 31 16777216 6612681 16777216 31 16777216 43727550007761 281474976710656 

noncomputable def Ns252p677 := nat_lit 31361945673298017832363335875968961049222633089290595815410640131736340458248371401925902801 

noncomputable def Ns252p678 := nat_lit 257241396291879266150844299504296431824816054815024822442268177306945464775442410029521 

noncomputable def Ns252p679 := nat_lit 189298826433035765396788242327519069185638769953941366346777910989206375614754442213602673105 

noncomputable def Ns252p680 := BSN.cos_dyadic_bound_t 15880411 8388608 4 3 8388608 3240000 Ns252p677 Ns252p308 Ns252p678 Ns252p679 Ns252p311 Ns252p678 2657053 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 15880411) (BSN.cosEvenQ 8388608) 0 3 Ns252p677 Ns252p308 Ns252p678 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 15880411) (BSN.cosOddQ 8388608) 0 3 Ns252p679 Ns252p311 Ns252p678 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p681 := @Ns252p668 1147537216 54358179840000 2657053 8388608 17930269 849346560000 (@Ns252p669 349 16777216 Bool.true 2657053 8388608 1 3240000 (@Ns252p672 Ns252p561 15880411 8388608 349 16777216 (@Ns252p673 281474976710656 930080879 281474976710656 Ns252p670 Ns252p183 Ns252p671 Ns252p561 RS253to264.d43 (@Ns252p674 0 1 1356912216204016 84807013512751 281474976710656 930080879 281474976710656 (@Ns252p675 1127677678838989455360 67214827468335 281474976710656 930080879 281474976710656 (@Ns252p676 409987183 281474976710656 (Ns252p659 rfl rfl) (Ns252p659 rfl rfl) rfl) (Ns252p659 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 15880411 8388608) (BSN.cos_neg_of_bound 15880411 8388608 Bool.true 2657053 8388608 1 3240000 (Ns252p680 rfl rfl)) rfl rfl) 

noncomputable def Ns252p682 := @Ns252p644 5726760796721467909 531266229322835086540800 (Ns252p645 qz33 (@Enclosure.Real.IsNear.of_eq qz639 (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 5473829 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz99 (BSN.t_div_two_pi_nonneg qz98 554491 1000 qz101)) Ns252p649) rfl) (@Ns252p650 140737488355328 15658178537897 474989023199232000 (BSN.correction_mk qz100 (BSN.cos_two_pi_p_ne_zero_mk qz98 554491 1000 9 qz101 rfl rfl (@BSN.floor_sqrt_eq_dec qz98 554491 1000 9 qz101 rfl rfl rfl))) (@Ns252p651 16777216 2657053 8388608 17930269 849346560000 56653192511195 140737488355328 15658178537897 474989023199232000 Ns252p667 (Ns252p681 rfl) rfl)) 

noncomputable def Ns252p683 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (hardyZApproximantRS₀ qz98) Bool.true 10178331693137715349593 2361183241434822606848 758331035088464597509 531266229322835086540800 (@Eq.refl Real (hardyZApproximantRS₀ qz98)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) (@HMul.hMul Real Real Real qz5 qz635 (Zeta.RiemannSiegel.correction qz100))) Bool.true 10178331693137715349593 2361183241434822606848 758331035088464597509 531266229322835086540800 (BSN.hardyZApproximantRS₀_eq qz98 9 (@BSN.floor_sqrt_eq_dec qz98 554491 1000 9 qz101 rfl rfl rfl)) (@Ns252p576 10178331693137715349593 2361183241434822606848 758331035088464597509 531266229322835086540800 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 9)) Bool.true 298099439 67108864 23767 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz98) qz98 9) (Ns252p643 (Ns252p642 rfl) rfl rfl)) (Ns252p682 rfl) rfl rfl)) 

theorem RS253to264.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz98) Bool.true 10178331693137715349593 2361183241434822606848 758331035088464597509 531266229322835086540800 := Ns252p683 

noncomputable def Ns252p684 := nat_lit 7470931349852368404480000 

noncomputable def Ns252p685 := nat_lit 53105200937675489009467392 

noncomputable abbrev qz760 := (Enclosure.sfrac Bool.false 555893 1000)

noncomputable abbrev qz643 := qz760

noncomputable abbrev qz444 := qz643

noncomputable abbrev qz116 := qz444

noncomputable abbrev qz761 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 555893 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz644 := qz761

noncomputable abbrev qz445 := qz644

noncomputable abbrev qz117 := qz445

noncomputable abbrev qz762 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 555893 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz645 := qz762

noncomputable abbrev qz446 := qz645

noncomputable abbrev qz118 := qz446

noncomputable abbrev qz646 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz117 qz9))

noncomputable def Ns252p686 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) (@HMul.hMul Real Real Real qz5 qz646 (Zeta.RiemannSiegel.correction qz118)) 894711 4194304 11913 8388608 4791305366470812735 36893488147419103232 74587797692229150473 Ns252p684 Ns252p685 

noncomputable def Ns252p687 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 555893 1000 119 161 134217728 67108864 2251799813685248 Bool.false 129870586369 1843 

noncomputable def Ns252p688 := Ns252p687 279097919 42 47453128 8 294906479 42 44739240 8 Bool.false 2850154 77981 Bool.true 189376135 Bool.true 122437986 7074237752028440 1 Bool.false 132506947 Bool.false Bool.false 106149167 Bool.true Bool.false 14315376 

noncomputable def Ns252p689 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 555893 1000 18 72 134217728 67108864 2251799813685248 Bool.false 129870586369 1843 

noncomputable def Ns252p690 := Ns252p689 240485871 42 54794152 8 261175631 42 50729528 8 Bool.false 30085614 58156 Bool.true 18909064 Bool.true 135451256 7074237752028440 1 Bool.false 132887942 Bool.true Bool.false 71477121 Bool.false Bool.false 2850154 

noncomputable def Ns252p691 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 555893 1000 125 46 134217728 67108864 2251799813685248 Bool.false 129870586369 1843 

noncomputable def Ns252p692 := Ns252p691 186065264 42 67108856 8 216015088 42 60023992 8 Bool.false 116342446 34275 Bool.false 84619301 Bool.false 91190205 7074237752028440 1 Bool.false 79123867 Bool.true Bool.false 104412977 Bool.true Bool.false 30085614 

noncomputable def Ns252p693 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 555893 1000 370 227 134217728 67108864 2251799813685248 Bool.false 129870586369 1843 

noncomputable def Ns252p694 := Ns252p693 93032624 42 94906264 8 147453232 42 77490640 16 Bool.false 134217688 1890 Bool.false 147777686 Bool.false 44248764 7074237752028440 1 Bool.false 60757456 Bool.true Bool.false 43451555 Bool.false Bool.false 116342446 

noncomputable def Ns252p695 := nat_lit 289328687459072779219967244043031997034327627707029696231 

noncomputable def Ns252p696 := nat_lit 299013349839212603842679132707930724079041180073984000 

noncomputable def Ns252p697 := nat_lit 25479925502469707420331854092640000 

noncomputable def Ns252p698 := nat_lit 84984705449418414628632698596655565120 

noncomputable abbrev qz647 := (@Eq.refl Real qz760)

noncomputable abbrev qz447 := qz647

noncomputable abbrev qz119 := qz447

noncomputable def Ns252p699 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz116 555893 1000 1236069109796 16000000 1111786 4000 2000 Ns252p697 Ns252p698 qz119 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns252p700 := nat_lit 92585179986903289350389518093770239050984840866249502793920 

noncomputable abbrev qz648 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1111786))))

noncomputable abbrev qz448 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 555893 4000) (Real.log (Enclosure.sfrac Bool.false 1236069109796 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz648))

noncomputable abbrev qz649 := (Enclosure.sfrac Bool.false 555893 2000)

noncomputable abbrev qz120 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz448 qz649) (@HMul.hMul Real Real Real qz346 qz649 (Real.log Real.pi)))

noncomputable def Ns252p701 := @Enclosure.Real.IsNear.addLit_ft_p qz120 (Enclosure.sfrac Bool.true Ns252p697 Ns252p698) 1089433777350141273991 1125899906842624000 2276354321472538561 165888000000000000000000 Ns252p697 Ns252p698 0 1 Ns252p700 

noncomputable def Ns252p702 := nat_lit 73110663201196911137048756224000 

noncomputable abbrev qz121 := (@HSub.hSub Real Real Real qz350 qz448 qz649)

noncomputable def Ns252p703 := @Enclosure.Real.IsNear.subLit_ff_p qz121 (@HMul.hMul Real Real Real qz5 qz649 (Real.log Real.pi)) 1447665476323186042759 1125899906842624000 440541586369457 81000000000000000000 21352273164573 67108864000 555893 67108864000 Ns252p702 1089433777350141273991 1125899906842624000 

noncomputable abbrev qz122 := qz448

noncomputable def Ns252p704 := @Enclosure.Real.IsNear.subLit_ff_p qz122 qz649 14084843318243355475 9007199254740992 440541586369457 81000000000000000000 555893 2000 0 1 23162647621170976684144 1447665476323186042759 1125899906842624000 440541586369457 81000000000000000000 

noncomputable def Ns252p705 := nat_lit 31716247559806298061237149027532800 

noncomputable def Ns252p706 := nat_lit 27212577120165717606400000 

noncomputable def Ns252p707 := nat_lit 14931443133819720042922526408342753265080543783475964569136820598857294254080 

noncomputable def Ns252p708 := nat_lit 33656852357949614015196704224848813377508968580760466380381989403520495616 

noncomputable def Ns252p709 := nat_lit 651633095819021047921847343536417591649215317709852620948016504893440 

noncomputable def Ns252p710 := BSN.log_dyadic_bound 187493109796 2284645109796 4 3 Ns252p707 67108864 25920000 Ns252p708 Ns252p709 11039624 2472138219592 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 187493109796) (BSN.artanhQ 2284645109796) 0 3 Ns252p708 Ns252p707 Ns252p709 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz449 := (Real.log (Enclosure.sfrac Bool.false 1236069109796 16000000))

noncomputable def Ns252p711 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 555893 4000) qz449 555893 4000 0 1 3167960923184375 281474976710656 195312581 5062500000000000 14088378411773854175 9007199254740992 108572896589833 20250000000000000000 (Enclosure.Real.IsNear.const Bool.false 555893 4000) (BSN.isNear_log_sfrac 1236069109796 16000000 3167960923184375 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1236069109796) qz353)) Bool.false Ns252p706 Ns252p93 1000000414720000 25920000000000000000000 3167960923184375 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1236069109796 16000000 16 2472138219592 2097152000000 11039624 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns252p710 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p712 := BSN.arctan_dyadic_bound_f 1000 1111786 1 0 8388608 3240000 0 1 1 0 1 1 7545 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1111786) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1111786) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns252p713 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1111786))) 884279719003555 562949953421312 1 2000000000000000 7545 8388608 1 3240000 7413628467672409702400 883773382624675 562949953421312 50000000081 162000000000000000 qz17 (Ns252p712 rfl) rfl rfl 

noncomputable abbrev qz450 := (@HMul.hMul Real Real Real qz584 qz589 qz648)

noncomputable abbrev qz123 := qz450

noncomputable abbrev qz451 := qz648

noncomputable abbrev qz124 := qz451

noncomputable def Ns252p714 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 555893 4000) qz449) qz123 14088378411773854175 9007199254740992 108572896589833 20250000000000000000 883773382624675 2251799813685248 50000000081 648000000000000000 Ns252p705 14084843318243355475 9007199254740992 440541586369457 81000000000000000000 (Ns252p711 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz124 1 4 0 1 883773382624675 562949953421312 50000000081 162000000000000000 883773382624675 2251799813685248 50000000081 648000000000000000 qz361 Ns252p713 rfl) 

noncomputable def Ns252p715 := @Ns252p701 Ns252p695 Ns252p696 2276354321472538561 165888000000000000000000 (@Ns252p703 2276354321472538561 165888000000000000000000 (Ns252p704 (Ns252p714 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 555893 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz649 (Real.log Real.pi) 555893 2000 0 1 38410761 33554432 1 33554432 21352273164573 67108864000 555893 67108864000 (Enclosure.Real.IsNear.const Bool.false 555893 2000) RS253to264.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns252p697 Ns252p698) 

noncomputable def Ns252p716 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns252p695 Ns252p696 2276354321472538561 165888000000000000000000 253653489 262144 231 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz362 qz120 (Enclosure.sfrac Bool.true Ns252p697 Ns252p698)) Bool.false Ns252p695 Ns252p696 2276354321472538561 165888000000000000000000 Ns252p699 (Ns252p715 rfl rfl)) 

noncomputable def Ns252p717 := BSN.cos_dyadic_bound_f 25206265 34359738368 1 0 16777216 6486329 0 1 1 0 1 1 16777211 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 25206265) (BSN.cosEvenQ 34359738368) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 25206265) (BSN.cosOddQ 34359738368) 0 0 rfl) rfl rfl 

noncomputable def Ns252p718 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz116) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 253653489) (@Nat.cast Real Real.instNatCast 262144)) Bool.false 253653489 262144 231 16777216 Bool.false 16777211 16777216 1 3240000 (Ns252p716 rfl) (Enclosure.sfrac_false_div 253653489 262144) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 253653489) (@Nat.cast Real Real.instNatCast 262144)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 27714582281178841088) (@Nat.cast Real Real.instNatCast 37778931862957161709568)) 226375608064910080 72057594037927936 Bool.false 16777211 16777216 154 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q0 253653489 262144 226375608064910080 72057594037927936 154 27714582281178841088 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777211 16777216 27714582281178841088 37778931862957161709568 25206265 34359738368 6486329 6480000 (Ns252p717 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p719 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns252p695 Ns252p696 2276354321472538561 165888000000000000000000 129870586369 134217728 1843 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz362 qz120 (Enclosure.sfrac Bool.true Ns252p697 Ns252p698)) Bool.false Ns252p695 Ns252p696 2276354321472538561 165888000000000000000000 Ns252p699 (Ns252p715 rfl rfl)) 

noncomputable def Ns252p720 := Ns252p694 34275 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 370 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 60757456 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 227 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 43451555 134217728) qz119 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) Bool.false 16777211 16777216 11956519 849346560000 134217688 134217728 1890 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 16777211 16777216 11956519 849346560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz116) qz116) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 16777211 16777216 765217216 54358179840000 16777211 16777216 11956519 849346560000 (Ns252p718 rfl rfl) rfl)) rfl) (Ns252p719 rfl) RS253to264.d7 

noncomputable def Ns252p721 := nat_lit 1003275057514493862051915625337085297423957365577319933970349280361581301503738491685856669345345732939776 

noncomputable def Ns252p722 := nat_lit 108469176174763305424384357990917076565177433635803588329106649001016656832310730032862082316701696 

noncomputable def Ns252p723 := nat_lit 6082988415490173114213436372798079483515361638821471779925221288217389728962529963288530518025655891333120 

noncomputable def Ns252p724 := BSN.cos_dyadic_bound_f 147777686 134217728 4 3 134217728 67108864 Ns252p721 Ns252p398 Ns252p722 Ns252p723 Ns252p401 Ns252p722 60757456 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 147777686) qz369 0 3 Ns252p721 Ns252p398 Ns252p722 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 147777686) qz370 0 3 Ns252p723 Ns252p401 Ns252p722 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p725 := nat_lit 3833580402604611279224543068416 

noncomputable def Ns252p726 := BSN.sin_dyadic_bound_f 44248764 134217728 2 1 134217728 67108864 Ns252p725 Ns252p238 Ns252p725 Ns252p725 Ns252p239 Ns252p725 43451555 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 44248764) qz367 0 1 Ns252p725 Ns252p238 Ns252p725 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 44248764) qz368 0 1 Ns252p725 Ns252p239 Ns252p725 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p727 := nat_lit 50317811322292694999722992022257123207507278131982817447902730949345 

noncomputable def Ns252p728 := nat_lit 2628787421702410327496014998668043915744498751319756472978674401 

noncomputable def Ns252p729 := nat_lit 131780487807321921096839509367342241091417380204833813710217567965921 

noncomputable def Ns252p730 := BSN.sin_dyadic_bound_f 84619301 134217728 3 2 134217728 67108864 Ns252p727 Ns252p116 Ns252p728 Ns252p729 Ns252p119 Ns252p728 79123867 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 84619301) qz367 0 2 Ns252p727 Ns252p116 Ns252p728 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 84619301) qz368 0 2 Ns252p729 Ns252p119 Ns252p728 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p731 := nat_lit 37704801816404610133198222476641823222204306139998284626118332190625 

noncomputable def Ns252p732 := nat_lit 4781735352438179502531533006711861384918954732663660411375390625 

noncomputable def Ns252p733 := nat_lit 113104841978508954040589604363912045943843080510529526557532245790625 

noncomputable def Ns252p734 := BSN.cos_dyadic_bound_f 91190205 134217728 3 2 134217728 67108864 Ns252p731 Ns252p144 Ns252p732 Ns252p733 Ns252p147 Ns252p732 104412977 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 91190205) qz369 0 2 Ns252p731 Ns252p144 Ns252p732 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 91190205) qz370 0 2 Ns252p733 Ns252p147 Ns252p732 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p735 := Ns252p692 58156 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 125 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 79123867 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 46 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 104412977 134217728) qz119 rfl rfl (Ns252p720 RS253to264.d9 RS253to264.d11 RS253to264.d13 RS253to264.d17 (Ns252p724 rfl rfl) (Ns252p726 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns252p719 rfl) RS253to264.d19 RS253to264.d21 RS253to264.d23 RS253to264.d25 RS253to264.d17 (Ns252p730 rfl rfl) (Ns252p734 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns252p736 := nat_lit 127843934247041574357396361216 

noncomputable def Ns252p737 := BSN.cos_dyadic_bound_f 18909064 134217728 2 1 134217728 67108864 Ns252p736 Ns252p122 Ns252p736 Ns252p736 Ns252p123 Ns252p736 132887942 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 18909064) qz369 0 1 Ns252p736 Ns252p122 Ns252p736 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 18909064) qz370 0 1 Ns252p736 Ns252p123 Ns252p736 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p738 := nat_lit 183632277383211289661111450000524544728667706776449350696215611703296 

noncomputable def Ns252p739 := nat_lit 113308970011891812109398500858490745377426821725762883454150639616 

noncomputable def Ns252p740 := nat_lit 550670214209610085359115552999856652695248266685896526321738533830656 

noncomputable def Ns252p741 := BSN.cos_dyadic_bound_f 135451256 134217728 3 2 134217728 67108864 Ns252p738 Ns252p144 Ns252p739 Ns252p740 Ns252p147 Ns252p739 71477121 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 135451256) qz369 0 2 Ns252p738 Ns252p144 Ns252p739 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 135451256) qz370 0 2 Ns252p740 Ns252p147 Ns252p739 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p742 := Ns252p690 77981 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 18 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132887942 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 72 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 71477121 134217728) qz119 rfl rfl (Ns252p735 rfl rfl) (Ns252p719 rfl) RS253to264.d27 RS253to264.d29 RS253to264.d31 RS253to264.d33 RS253to264.d17 (Ns252p737 rfl rfl) (Ns252p741 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p743 := nat_lit 7037980936532032730942774813696385492099911947525678923873209250083007399694942836580014645046893167790625 

noncomputable def Ns252p744 := nat_lit 2127663703456967827328966210010074704098173765992360968394971699264142387303021893451443926025390625 

noncomputable def Ns252p745 := nat_lit 35161422397785509123812540541342863583074186051238022174681457235259675824258746904290232624475337737390625 

noncomputable def Ns252p746 := BSN.sin_dyadic_bound_f 189376135 134217728 4 3 134217728 67108864 Ns252p743 Ns252p137 Ns252p744 Ns252p745 Ns252p140 Ns252p744 132506947 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 189376135) qz367 0 3 Ns252p743 Ns252p137 Ns252p744 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 189376135) qz368 0 3 Ns252p745 Ns252p140 Ns252p744 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p747 := nat_lit 220589822508017456319389989805334606214760019873434021643744601800960 

noncomputable def Ns252p748 := nat_lit 50504423456405187189952757114974134601668469665658577783405773056 

noncomputable def Ns252p749 := nat_lit 577653480359211539104856716454833058154064017384297085655300823941376 

noncomputable def Ns252p750 := BSN.sin_dyadic_bound_f 122437986 134217728 3 2 134217728 67108864 Ns252p747 Ns252p116 Ns252p748 Ns252p749 Ns252p119 Ns252p748 106149167 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 122437986) qz367 0 2 Ns252p747 Ns252p116 Ns252p748 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 122437986) qz368 0 2 Ns252p749 Ns252p119 Ns252p748 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz650 := (BSN.cos_quad_nat3 119 rfl)

noncomputable def Ns252p751 := Ns252p688 95304 BSN.abs_quadSignPos qz650 (BSN.sfrac_eq_quadSignPos_mul Bool.false 132506947 134217728) BSN.abs_quadSignNeg qz371 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 106149167 134217728) qz119 rfl rfl (Ns252p742 rfl) (Ns252p719 rfl) RS253to264.d35 RS253to264.d37 RS253to264.d39 RS253to264.d41 RS253to264.d17 (Ns252p746 rfl rfl) (Ns252p750 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p752 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) 14315376 134217728 95304 134217728 14315376 134217728 95304 134217728 3842754484371456 894711 4194304 11913 8388608 (Ns252p751 rfl) 

noncomputable def Ns252p753 := @Enclosure.Real.IsNear.mulLit_tf qz646 (Zeta.RiemannSiegel.correction qz118) 2735187 8388608 1 8388608 1751728626405 4398046511104 108560102845409 3562417673994240000 4791305366470812735 36893488147419103232 

noncomputable abbrev qz651 := (@HPow.hPow Real Real Real qz7 qz117 qz9)

noncomputable def Ns252p754 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz651 1 1 0 1 2735187 8388608 1 8388608 2735187 8388608 1 8388608 

noncomputable def Ns252p755 := @Enclosure.Real.IsNear.sqrt_image qz117 1484332703061 16777216000 555893 16777216000 78903360 78903390 8388608 (@Enclosure.Real.IsNear.of_eq qz117 (@HMul.hMul Real Real Real qz5 qz116 qz3) Bool.false 1484332703061 16777216000 555893 16777216000 (BSN.t_div_two_pi_mk qz116 555893 1000 qz119) (@Enclosure.Real.IsNear.mulLit_ff qz116 qz3 555893 1000 0 1 2670177 16777216 1 16777216 1484332703061 16777216000 555893 16777216000 (Enclosure.Real.IsNear.const Bool.false 555893 1000) RS253to264.d44 rfl)) 

noncomputable abbrev qz763 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 555893 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz652 := qz763

noncomputable abbrev qz452 := qz652

noncomputable abbrev qz125 := qz452

noncomputable def Ns252p756 := @Enclosure.Real.IsNear.sqrt_image qz125 78903375 8388608 15 8388608 25727210 25727216 8388608 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 157806750 16777216 30 16777216 78903375 8388608 15 8388608 (Ns252p755 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns252p757 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz125) 25727213 8388608 3 8388608 2735186 2735188 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz125) Bool.false 51454426 16777216 6 16777216 25727213 8388608 3 8388608 (Ns252p756 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns252p758 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 5470374 16777216 2 16777216 2735187 8388608 1 8388608 (Ns252p757 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz453 := (@HMul.hMul Real Real Real qz584 qz582 qz645)

noncomputable abbrev qz126 := (Real.cos qz453)

noncomputable abbrev qz653 := (@HMul.hMul Real Real Real qz735 qz762 qz762)

noncomputable abbrev qz454 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz653 qz645) qz599)

noncomputable abbrev qz127 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz454))

noncomputable def Ns252p759 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz118) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz126) qz127) Bool.false 1751728626405 

noncomputable def Ns252p760 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz126) qz127 1262357 1048576 141 

noncomputable abbrev qz128 := (@Neg.neg Real Real.instNeg (Real.cos qz453))

noncomputable def Ns252p761 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz126) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz128)) Bool.true 1262357 1048576 141 8388608 (BSN.inv_eq_neg_inv_neg qz126) 

noncomputable def Ns252p762 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz128) Bool.false 20197712 16777216 282 16777216 1262357 1048576 

noncomputable def Ns252p763 := @Enclosure.Real.IsNear.recentre' qz126 Bool.true 13935983 16777216 629137216 54358179840000 13935983 16777216 9830269 849346560000 

noncomputable abbrev qz129 := qz453

noncomputable def Ns252p764 := @Enclosure.Real.IsNear.cos_image qz129 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 42799839) qz410) Bool.false 42799839 16777216 189 16777216 Bool.true 13935983 16777216 1 

noncomputable def Ns252p765 := nat_lit 404791131164917165824231081 

noncomputable def Ns252p766 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz118 884279719003555 140737488355328 1 500000000000000 3405903 8388608 15 8388608 3011770947793364985165 1180591620717411303424 Ns252p765 

noncomputable def Ns252p767 := @Enclosure.Real.IsNear.subLit_ff_p qz125 qz1 78903375 8388608 15 8388608 9 1 0 1 3405903 3405903 8388608 15 

noncomputable def Ns252p768 := @Ns252p767 8388608 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 157806750 16777216 30 16777216 78903375 8388608 15 8388608 (Ns252p755 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns252p769 := @Enclosure.Real.IsNear.recentre' qz129 Bool.false 3011770947793364985165 1180591620717411303424 Ns252p765 Ns252p282 42799839 16777216 189 16777216 (@Ns252p766 Ns252p282 RS253to264.d43 (Ns252p768 rfl rfl) rfl) 

noncomputable def Ns252p770 := nat_lit 2370154373465012676067328 

noncomputable def Ns252p771 := nat_lit 5426266328029134957217620792567917429243446084877552577942035046717394740919419603436705 

noncomputable def Ns252p772 := nat_lit 1656436011293069318337298186294691093361198346327418723659252949387480813543799833761 

noncomputable def Ns252p773 := nat_lit 14208968057962783728102175021566735195772154948785250454771786331865596971567028047365281 

noncomputable def Ns252p774 := BSN.sin_dyadic_bound_f 33681919453 34359738368 3 2 16777216 6486329 Ns252p771 Ns252p288 Ns252p772 Ns252p773 Ns252p291 Ns252p772 13935983 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 33681919453) qz363 0 2 Ns252p771 Ns252p288 Ns252p772 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 33681919453) qz364 0 2 Ns252p773 Ns252p291 Ns252p772 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p775 := @Ns252p764 3240000 (Ns252p769 rfl) (Enclosure.sfrac_false_div 42799839 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 42799839) qz410) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns252p770) qz411) 226375608064910080 72057594037927936 Bool.false 13935983 16777216 0 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 42799839 16777216 226375608064910080 72057594037927936 0 Ns252p770 Ns252p93 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 13935983 16777216 Ns252p770 Ns252p93 33681919453 34359738368 6486329 6480000 (Ns252p774 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p776 := @Enclosure.Real.IsNear.inv_image qz128 13935983 16777216 9830269 849346560000 10098715 10098997 8388608 (@Enclosure.Real.IsNear.neg qz126 Bool.true 13935983 16777216 9830269 849346560000 (Ns252p763 (Ns252p775 rfl rfl) rfl)) 

noncomputable def Ns252p777 := Ns252p761 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz128) Bool.false 1262357 1048576 141 8388608 (@Ns252p762 141 8388608 (Ns252p776 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p778 := @Enclosure.Real.IsNear.recentre' qz127 Bool.true 2775330 8388608 

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz346 qz343 qz454)

noncomputable def Ns252p779 := @Enclosure.Real.IsNear.cos_image qz130 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1000339)) (@Nat.cast Real Real.instNatCast 524288)) Bool.true 1000339 524288 

noncomputable def Ns252p780 := nat_lit 18895869493428349233529546045 

noncomputable def Ns252p781 := nat_lit 6152998848840854923166745662730293 

noncomputable def Ns252p782 := @Enclosure.Real.IsNear.recentre' qz130 Bool.true Ns252p780 Ns252p449 Ns252p781 

noncomputable abbrev qz131 := qz454

noncomputable def Ns252p783 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz131 884279719003555 140737488355328 1 500000000000000 21368656418719 

noncomputable abbrev qz455 := (@HSub.hSub Real Real Real qz588 qz653 qz645)

noncomputable abbrev qz132 := qz455

noncomputable def Ns252p784 := @Enclosure.Real.IsNear.subLit_tf qz132 qz31 16970609907615 70368744177664 228006435 70368744177664 1 16 

noncomputable abbrev qz456 := qz653

noncomputable abbrev qz133 := qz456

noncomputable def Ns252p785 := @Enclosure.Real.IsNear.subLit_ff_n qz133 qz118 11600175245409 70368744177664 102177315 70368744177664 3405903 8388608 15 8388608 

noncomputable def Ns252p786 := @Enclosure.Real.IsNear.mulLit_ff qz118 qz118 3405903 8388608 15 8388608 3405903 8388608 15 8388608 11600175245409 70368744177664 

noncomputable def Ns252p787 := nat_lit 114997974524737088637423406352891993927514279591200729241415684513533194238001 

noncomputable def Ns252p788 := nat_lit 206621721431677182442706747102504677185300319965248164533833585202413803929600 

noncomputable def Ns252p789 := nat_lit 1004075593363349111219145628445891320183782136214370917087859561415145521 

noncomputable def Ns252p790 := nat_lit 694009029884678859815787649801955997432745782393161153603195896522602811324465 

noncomputable def Ns252p791 := nat_lit 18802576650282623602286313986327925623862329116837582972578856253419656157593600 

noncomputable def Ns252p792 := BSN.cos_dyadic_bound_t 1000339 524288 4 3 8388608 3240000 Ns252p787 Ns252p788 Ns252p789 Ns252p790 Ns252p791 Ns252p789 2775330 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 1000339) (BSN.cosEvenQ 524288) 0 3 Ns252p787 Ns252p788 Ns252p789 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 1000339) (BSN.cosOddQ 524288) 0 3 Ns252p790 Ns252p791 Ns252p789 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p793 := @Ns252p778 562428608 27179089920000 1387665 4194304 8787947 424673280000 (@Ns252p779 171 8388608 Bool.true 2775330 8388608 1 3240000 (@Ns252p782 Ns252p302 1000339 524288 171 8388608 (@Ns252p783 70368744177664 228006435 70368744177664 Ns252p780 Ns252p449 Ns252p781 Ns252p302 RS253to264.d43 (@Ns252p784 0 1 341898502699504 21368656418719 70368744177664 228006435 70368744177664 (@Ns252p785 142359794035898449920 16970609907615 70368744177664 228006435 70368744177664 (@Ns252p786 102177315 70368744177664 (Ns252p768 rfl rfl) (Ns252p768 rfl rfl) rfl) (Ns252p768 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 1000339 524288) (BSN.cos_neg_of_bound 1000339 524288 Bool.true 2775330 8388608 1 3240000 (Ns252p792 rfl rfl)) rfl rfl) 

noncomputable def Ns252p794 := @Ns252p753 74587797692229150473 Ns252p684 (Ns252p754 qz33 (@Enclosure.Real.IsNear.of_eq qz651 (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 2735187 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz117 (BSN.t_div_two_pi_nonneg qz116 555893 1000 qz119)) Ns252p758) rfl) (@Ns252p759 4398046511104 108560102845409 3562417673994240000 (BSN.correction_mk qz118 (BSN.cos_two_pi_p_ne_zero_mk qz116 555893 1000 9 qz119 rfl rfl (@BSN.floor_sqrt_eq_dec qz116 555893 1000 9 qz119 rfl rfl rfl))) (@Ns252p760 8388608 1387665 4194304 8787947 424673280000 1751728626405 4398046511104 108560102845409 3562417673994240000 Ns252p777 (Ns252p793 rfl) rfl)) 

noncomputable def Ns252p795 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (hardyZApproximantRS₀ qz116) Bool.false 12661266550463554623 36893488147419103232 10684358235265574430473 Ns252p684 (@Eq.refl Real (hardyZApproximantRS₀ qz116)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) (@HMul.hMul Real Real Real qz5 qz646 (Zeta.RiemannSiegel.correction qz118))) Bool.false 12661266550463554623 36893488147419103232 10684358235265574430473 Ns252p684 (BSN.hardyZApproximantRS₀_eq qz116 9 (@BSN.floor_sqrt_eq_dec qz116 555893 1000 9 qz119 rfl rfl rfl)) (@Ns252p686 12661266550463554623 36893488147419103232 10684358235265574430473 Ns252p684 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 9)) Bool.false 894711 4194304 11913 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz116) qz116 9) (Ns252p752 (Ns252p751 rfl) rfl rfl)) (Ns252p794 rfl) rfl rfl)) 

theorem RS253to264.d52 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz116) Bool.false 12661266550463554623 36893488147419103232 10684358235265574430473 Ns252p684 := Ns252p795 

noncomputable def Ns252p796 := nat_lit 2988372539940947361792000 

noncomputable def Ns252p797 := nat_lit 2973427783050334206211129344 

noncomputable abbrev qz764 := (Enclosure.sfrac Bool.false 557294 1000)

noncomputable abbrev qz654 := qz764

noncomputable abbrev qz457 := qz654

noncomputable abbrev qz134 := qz457

noncomputable abbrev qz765 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 557294 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz655 := qz765

noncomputable abbrev qz458 := qz655

noncomputable abbrev qz135 := qz458

noncomputable abbrev qz766 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 557294 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz656 := qz766

noncomputable abbrev qz459 := qz656

noncomputable abbrev qz136 := qz459

noncomputable abbrev qz657 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz135 qz9))

noncomputable def Ns252p798 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) (@HMul.hMul Real Real Real qz5 qz657 (Zeta.RiemannSiegel.correction qz136)) 14388645 33554432 23887 16777216 37948806496531812393 295147905179352825856 29691856767751807379 Ns252p796 Ns252p797 

noncomputable def Ns252p799 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 557294 1000 119 161 134217728 67108864 2251799813685248 Bool.false 130292165917 1848 

noncomputable def Ns252p800 := Ns252p799 279097919 42 47453128 8 294906479 42 44739240 8 Bool.true 39113278 78182 Bool.true 158812772 Bool.true 114022415 7074237752028440 1 Bool.false 124263890 Bool.false Bool.false 100793787 Bool.true Bool.true 28777290 

noncomputable def Ns252p801 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 557294 1000 17 72 134217728 67108864 2251799813685248 Bool.false 130292165917 1848 

noncomputable def Ns252p802 := Ns252p801 240485871 42 54794152 8 261175631 42 50729528 8 Bool.true 32792037 58307 Bool.true 145078935 Bool.true 79778767 7074237752028440 1 Bool.false 118432667 Bool.true Bool.false 111197468 Bool.false Bool.true 39113278 

noncomputable def Ns252p803 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 557294 1000 126 46 134217728 67108864 2251799813685248 Bool.false 130292165917 1848 

noncomputable def Ns252p804 := Ns252p803 186065264 42 67108856 8 216015088 42 60023992 8 Bool.false 32398728 34365 Bool.false 34692700 Bool.false 210132615 7074237752028440 1 Bool.false 129758938 Bool.true Bool.false 696096 Bool.true Bool.true 32792037 

noncomputable def Ns252p805 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 557294 1000 372 228 134217728 67108864 2251799813685248 Bool.false 130292165917 1848 

noncomputable def Ns252p806 := Ns252p805 93032624 42 94906264 8 147453232 42 77490640 16 Bool.true 134217720 1898 Bool.false 17361100 Bool.false 48417620 7074237752028440 1 Bool.false 133096461 Bool.false Bool.false 125578952 Bool.false Bool.false 32398728 

noncomputable def Ns252p807 := nat_lit 2302226223679561279976484064701569284364431521618650431 

noncomputable def Ns252p808 := nat_lit 2371589810546674643234265521762197739552146194432000 

noncomputable def Ns252p809 := nat_lit 25802629099662460085603886187520000 

noncomputable def Ns252p810 := nat_lit 86277934698834529380629301950182625280 

noncomputable abbrev qz658 := (@Eq.refl Real qz764)

noncomputable abbrev qz460 := qz658

noncomputable abbrev qz137 := qz460

noncomputable def Ns252p811 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz134 557294 1000 1242307409744 16000000 1114588 4000 2000 Ns252p809 Ns252p810 qz137 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns252p812 := nat_lit 47149593060957415013918393645088138943783557562749960826880 

noncomputable abbrev qz659 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1114588))))

noncomputable abbrev qz461 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 557294 4000) (Real.log (Enclosure.sfrac Bool.false 1242307409744 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz659))

noncomputable abbrev qz660 := (Enclosure.sfrac Bool.false 557294 2000)

noncomputable abbrev qz138 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz461 qz660) (@HMul.hMul Real Real Real qz346 qz660 (Real.log Real.pi)))

noncomputable def Ns252p813 := @Enclosure.Real.IsNear.addLit_ft_p qz138 (Enclosure.sfrac Bool.true Ns252p809 Ns252p810) 546485121035044631971 562949953421312000 1141029543842689019 82944000000000000000000 Ns252p809 Ns252p810 0 1 Ns252p812 

noncomputable def Ns252p814 := nat_lit 18336997832782174720435945472000 

noncomputable abbrev qz139 := (@HSub.hSub Real Real Real qz350 qz461 qz660)

noncomputable def Ns252p815 := @Enclosure.Real.IsNear.subLit_ff_p qz139 (@HMul.hMul Real Real Real qz5 qz660 (Real.log Real.pi)) 726052390678198990243 562949953421312000 441636118073381 81000000000000000000 10703043320367 33554432000 278647 33554432000 Ns252p814 546485121035044631971 562949953421312000 

noncomputable def Ns252p816 := nat_lit 1452104781356397980486000 

noncomputable abbrev qz140 := qz461

noncomputable def Ns252p817 := @Enclosure.Real.IsNear.subLit_ff_p qz140 qz660 882916706349187315107 562949953421312000 441636118073381 81000000000000000000 557294 2000 0 1 Ns252p816 726052390678198990243 562949953421312000 441636118073381 81000000000000000000 

noncomputable def Ns252p818 := nat_lit 1988151674856692816052282584293441536 

noncomputable def Ns252p819 := nat_lit 27224749052921807374385152 

noncomputable def Ns252p820 := nat_lit 15177743948334864262627537306092425731791326908889674994031643193426973818880 

noncomputable def Ns252p821 := nat_lit 36336999529100236284190401030236070983005872555946071889717282479670296576 

noncomputable def Ns252p822 := nat_lit 793033423329602259736234974939791588235567640301926929007516676259840 

noncomputable def Ns252p823 := BSN.log_dyadic_bound 193731409744 2290883409744 4 3 Ns252p820 67108864 25920000 Ns252p821 Ns252p822 11377463 2484614819488 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 193731409744) (BSN.artanhQ 2290883409744) 0 3 Ns252p821 Ns252p820 Ns252p822 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz462 := (Real.log (Enclosure.sfrac Bool.false 1242307409744 16000000))

noncomputable def Ns252p824 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 557294 4000) qz462 557294 4000 0 1 3169377922653431 281474976710656 195312581 5062500000000000 883137650013610587857 562949953421312000 54423264757907 10125000000000000000 (Enclosure.Real.IsNear.const Bool.false 557294 4000) (BSN.isNear_log_sfrac 1242307409744 16000000 3169377922653431 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1242307409744) qz353)) Bool.false Ns252p819 Ns252p93 1000000414720000 25920000000000000000000 3169377922653431 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1242307409744 16000000 16 2484614819488 2097152000000 11377463 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns252p823 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p825 := BSN.arctan_dyadic_bound_f 1000 1114588 1 0 8388608 3240000 0 1 1 0 1 1 7526 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1114588) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1114588) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns252p826 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1114588))) 884279719003555 562949953421312 1 2000000000000000 7526 8388608 1 3240000 7413639163721524707328 883774657693091 562949953421312 50000000081 162000000000000000 qz17 (Ns252p825 rfl) rfl rfl 

noncomputable abbrev qz463 := (@HMul.hMul Real Real Real qz584 qz589 qz659)

noncomputable abbrev qz141 := qz463

noncomputable abbrev qz464 := qz659

noncomputable abbrev qz142 := qz464

noncomputable def Ns252p827 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 557294 4000) qz462) qz141 883137650013610587857 562949953421312000 54423264757907 10125000000000000000 883774657693091 2251799813685248 50000000081 648000000000000000 Ns252p818 882916706349187315107 562949953421312000 441636118073381 81000000000000000000 (Ns252p824 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz142 1 4 0 1 883774657693091 562949953421312 50000000081 162000000000000000 883774657693091 2251799813685248 50000000081 648000000000000000 qz361 Ns252p826 rfl) 

noncomputable def Ns252p828 := @Ns252p813 Ns252p807 Ns252p808 1141029543842689019 82944000000000000000000 (@Ns252p815 1141029543842689019 82944000000000000000000 (Ns252p817 (Ns252p827 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 557294 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz660 (Real.log Real.pi) 557294 2000 0 1 38410761 33554432 1 33554432 10703043320367 33554432000 278647 33554432000 (Enclosure.Real.IsNear.const Bool.false 557294 2000) RS253to264.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns252p809 Ns252p810) 

noncomputable def Ns252p829 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns252p807 Ns252p808 1141029543842689019 82944000000000000000000 16286520739 16777216 29 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz362 qz138 (Enclosure.sfrac Bool.true Ns252p809 Ns252p810)) Bool.false Ns252p807 Ns252p808 1141029543842689019 82944000000000000000000 Ns252p811 (Ns252p828 rfl rfl)) 

noncomputable def Ns252p830 := nat_lit 3798323168691351504027648 

noncomputable def Ns252p831 := nat_lit 857472931831526961596211044367960688665419447061993319258971919329992167893421838141085158293254509866565927327465382700183497141671521 

noncomputable def Ns252p832 := nat_lit 611709667938694394670715461091587774140699804209761430774449893791560666349036756285932260872207843955152718323136492811093825121 

noncomputable def Ns252p833 := nat_lit 4282035002471652939508863589244920372242385428921510660174867611178513675529860044146924377156938813502101361515951503358074181955638881 

noncomputable def Ns252p834 := BSN.sin_dyadic_bound_f 53977418711 34359738368 4 3 16777216 6486329 Ns252p831 Ns252p107 Ns252p832 Ns252p833 Ns252p110 Ns252p832 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53977418711) qz363 0 3 Ns252p831 Ns252p107 Ns252p832 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53977418711) qz364 0 3 Ns252p833 Ns252p110 Ns252p832 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p835 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz134) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16286520739) qz410) Bool.false 16286520739 16777216 29 2097152 Bool.true 16777215 16777216 1 3240000 (Ns252p829 rfl) (Enclosure.sfrac_false_div 16286520739 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16286520739) qz410) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns252p830) qz411) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 154 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 16286520739 16777216 226375608064910080 72057594037927936 154 Ns252p830 Ns252p93 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns252p830 Ns252p93 53977418711 34359738368 6486329 6480000 (Ns252p834 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p836 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns252p807 Ns252p808 1141029543842689019 82944000000000000000000 130292165917 134217728 1848 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz362 qz138 (Enclosure.sfrac Bool.true Ns252p809 Ns252p810)) Bool.false Ns252p807 Ns252p808 1141029543842689019 82944000000000000000000 Ns252p811 (Ns252p828 rfl rfl)) 

noncomputable def Ns252p837 := Ns252p806 34365 BSN.abs_quadSignPos (BSN.cos_quad_nat0 372 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133096461 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 228 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 125578952 134217728) qz137 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) Bool.true 16777215 16777216 1500893 106168320000 134217720 134217728 1898 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 16777215 16777216 1500893 106168320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz134) qz134) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 16777215 16777216 96057152 6794772480000 16777215 16777216 1500893 106168320000 (Ns252p835 rfl rfl) rfl)) rfl) (Ns252p836 rfl) RS253to264.d7 

noncomputable def Ns252p838 := nat_lit 90846657807722122104100000000 

noncomputable def Ns252p839 := BSN.cos_dyadic_bound_f 17361100 134217728 2 1 134217728 67108864 Ns252p838 Ns252p122 Ns252p838 Ns252p838 Ns252p123 Ns252p838 133096461 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 17361100) qz369 0 1 Ns252p838 Ns252p122 Ns252p838 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 17361100) qz370 0 1 Ns252p838 Ns252p123 Ns252p838 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p840 := nat_lit 2996173382804244179108758872170109972480281665779060160016588800000 

noncomputable def Ns252p841 := nat_lit 30201429586040982202312272748016301138756834638905369600000000 

noncomputable def Ns252p842 := nat_lit 8988459745553560455361871991964833884838567483667902669310566400000 

noncomputable def Ns252p843 := BSN.cos_dyadic_bound_f 48417620 134217728 3 2 134217728 67108864 Ns252p840 Ns252p144 Ns252p841 Ns252p842 Ns252p147 Ns252p841 125578952 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 48417620) qz369 0 2 Ns252p840 Ns252p144 Ns252p841 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 48417620) qz370 0 2 Ns252p842 Ns252p147 Ns252p841 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p844 := nat_lit 1448613080890143880224100000000 

noncomputable def Ns252p845 := BSN.cos_dyadic_bound_f 34692700 134217728 2 1 134217728 67108864 Ns252p844 Ns252p122 Ns252p844 Ns252p844 Ns252p123 Ns252p844 129758938 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 34692700) qz369 0 1 Ns252p844 Ns252p122 Ns252p844 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 34692700) qz370 0 1 Ns252p844 Ns252p123 Ns252p844 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p846 := nat_lit 4112726163629124819238416418475109509459839081178884792737199592369874363585655110609885680780435849390625 

noncomputable def Ns252p847 := nat_lit 7411763987893631455875930838533203342033652884063592418240516376156446643281783299547193926025390625 

noncomputable def Ns252p848 := nat_lit 24891227400751906504078983848801140856735489225503343759374540165249742026821499001490129560863603490990625 

noncomputable def Ns252p849 := BSN.cos_dyadic_bound_f 210132615 134217728 4 3 134217728 67108864 Ns252p846 Ns252p398 Ns252p847 Ns252p848 Ns252p401 Ns252p847 696096 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 210132615) qz369 0 3 Ns252p846 Ns252p398 Ns252p847 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 210132615) qz370 0 3 Ns252p848 Ns252p401 Ns252p847 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p850 := Ns252p804 58307 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 126 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 129758938 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 46 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 696096 134217728) qz137 rfl rfl (Ns252p837 RS253to264.d9 RS253to264.d11 RS253to264.d13 RS253to264.d17 (Ns252p839 rfl rfl) (Ns252p843 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns252p836 rfl) RS253to264.d19 RS253to264.d21 RS253to264.d23 RS253to264.d25 RS253to264.d17 (Ns252p845 rfl rfl) (Ns252p849 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns252p851 := nat_lit 434945423727801663088317627444037525251402381745629818887469296130625 

noncomputable def Ns252p852 := nat_lit 196261390152384372234324729657063886509725373837782706430437890625 

noncomputable def Ns252p853 := nat_lit 1138825019893519542914357260410177319842180968252340734609151257090625 

noncomputable def Ns252p854 := BSN.sin_dyadic_bound_f 145078935 134217728 3 2 134217728 67108864 Ns252p851 Ns252p116 Ns252p852 Ns252p853 Ns252p119 Ns252p852 118432667 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 145078935) qz367 0 2 Ns252p851 Ns252p116 Ns252p852 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 145078935) qz368 0 2 Ns252p853 Ns252p119 Ns252p852 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p855 := nat_lit 22086676022082294401897935761948433219228956541051111359189382389121 

noncomputable def Ns252p856 := nat_lit 1640962132448481405966705734001752045466262881191581849850797441 

noncomputable def Ns252p857 := nat_lit 66256746141981986242881873874377296153595937097390950913868445572481 

noncomputable def Ns252p858 := BSN.cos_dyadic_bound_f 79778767 134217728 3 2 134217728 67108864 Ns252p855 Ns252p144 Ns252p856 Ns252p857 Ns252p147 Ns252p856 111197468 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 79778767) qz369 0 2 Ns252p855 Ns252p144 Ns252p856 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 79778767) qz370 0 2 Ns252p857 Ns252p147 Ns252p856 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p859 := Ns252p802 78182 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 17 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 118432667 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 72 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 111197468 134217728) qz137 rfl rfl (Ns252p850 rfl rfl) (Ns252p836 rfl) RS253to264.d27 RS253to264.d29 RS253to264.d31 RS253to264.d33 RS253to264.d17 (Ns252p854 rfl rfl) (Ns252p858 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p860 := nat_lit 624661082176708614594491620725209612825969010715144402991784199782400 

noncomputable def Ns252p861 := nat_lit 404653601187037399115308707738525702626934941745415473826627649536 

noncomputable def Ns252p862 := nat_lit 1635361966537076882434624697324924706263760942919695144687525030854656 

noncomputable def Ns252p863 := BSN.sin_dyadic_bound_f 158812772 134217728 3 2 134217728 67108864 Ns252p860 Ns252p116 Ns252p861 Ns252p862 Ns252p119 Ns252p861 124263890 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 158812772) qz367 0 2 Ns252p860 Ns252p116 Ns252p861 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 158812772) qz368 0 2 Ns252p862 Ns252p119 Ns252p861 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p864 := nat_lit 165904076165522653171830811256566041295713962049293709654832243530625 

noncomputable def Ns252p865 := nat_lit 28570765795883089819564135872725864552158169100661270050562890625 

noncomputable def Ns252p866 := nat_lit 434464418241270757114134735166259980565214025474368168944478774090625 

noncomputable def Ns252p867 := BSN.sin_dyadic_bound_f 114022415 134217728 3 2 134217728 67108864 Ns252p864 Ns252p116 Ns252p865 Ns252p866 Ns252p119 Ns252p865 100793787 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 114022415) qz367 0 2 Ns252p864 Ns252p116 Ns252p865 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 114022415) qz368 0 2 Ns252p866 Ns252p119 Ns252p865 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p868 := Ns252p800 95548 BSN.abs_quadSignPos qz650 (BSN.sfrac_eq_quadSignPos_mul Bool.false 124263890 134217728) BSN.abs_quadSignNeg qz371 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 100793787 134217728) qz137 rfl rfl (Ns252p859 rfl) (Ns252p836 rfl) RS253to264.d35 RS253to264.d37 RS253to264.d39 RS253to264.d41 RS253to264.d17 (Ns252p863 rfl rfl) (Ns252p867 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p869 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) 28777290 134217728 95548 134217728 28777290 134217728 95548 134217728 7724844963594240 14388645 33554432 23887 16777216 (Ns252p868 rfl) 

noncomputable def Ns252p870 := @Enclosure.Real.IsNear.mulLit_tf qz657 (Zeta.RiemannSiegel.correction qz136) 5466933 16777216 1 16777216 6941516659621 17592186044416 5418315624731 178120883699712000 37948806496531812393 295147905179352825856 

noncomputable abbrev qz661 := (@HPow.hPow Real Real Real qz7 qz135 qz9)

noncomputable def Ns252p871 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz661 1 1 0 1 5466933 16777216 1 16777216 5466933 16777216 1 16777216 

noncomputable def Ns252p872 := @Enclosure.Real.IsNear.sqrt_image qz135 744036810519 8388608000 278647 8388608000 79002726 79002757 8388608 (@Enclosure.Real.IsNear.of_eq qz135 (@HMul.hMul Real Real Real qz5 qz134 qz3) Bool.false 744036810519 8388608000 278647 8388608000 (BSN.t_div_two_pi_mk qz134 557294 1000 qz137) (@Enclosure.Real.IsNear.mulLit_ff qz134 qz3 557294 1000 0 1 2670177 16777216 1 16777216 744036810519 8388608000 278647 8388608000 (Enclosure.Real.IsNear.const Bool.false 557294 1000) RS253to264.d44 rfl)) 

noncomputable abbrev qz767 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 557294 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz662 := qz767

noncomputable abbrev qz465 := qz662

noncomputable abbrev qz143 := qz465

noncomputable def Ns252p873 := @Enclosure.Real.IsNear.sqrt_image qz143 158005483 16777216 31 16777216 25743404 25743411 8388608 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 158005483 16777216 31 16777216 158005483 16777216 31 16777216 (Ns252p872 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns252p874 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz143) 51486815 16777216 7 16777216 2733466 2733467 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz143) Bool.false 51486815 16777216 7 16777216 51486815 16777216 7 16777216 (Ns252p873 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns252p875 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 5466933 16777216 1 16777216 5466933 16777216 1 16777216 (Ns252p874 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz466 := (@HMul.hMul Real Real Real qz584 qz582 qz656)

noncomputable abbrev qz144 := (Real.cos qz466)

noncomputable abbrev qz663 := (@HMul.hMul Real Real Real qz735 qz766 qz766)

noncomputable abbrev qz467 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz663 qz656) qz599)

noncomputable abbrev qz145 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz467))

noncomputable def Ns252p876 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz136) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz144) qz145) Bool.false 6941516659621 

noncomputable def Ns252p877 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz144) qz145 19289653 16777216 267 

noncomputable abbrev qz146 := (@Neg.neg Real Real.instNeg (Real.cos qz466))

noncomputable def Ns252p878 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz144) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz146)) Bool.true 19289653 16777216 267 16777216 (BSN.inv_eq_neg_inv_neg qz144) 

noncomputable def Ns252p879 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz146) Bool.false 19289653 16777216 267 16777216 19289653 16777216 

noncomputable def Ns252p880 := @Enclosure.Real.IsNear.recentre' qz144 Bool.true 14592018 16777216 162954304 13589544960000 7296009 8388608 2546161 212336640000 

noncomputable abbrev qz147 := qz466

noncomputable def Ns252p881 := @Enclosure.Real.IsNear.cos_image qz147 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44048515) qz410) Bool.false 44048515 16777216 49 4194304 Bool.true 14592018 16777216 1 

noncomputable def Ns252p882 := nat_lit 167313667548117096114980613 

noncomputable def Ns252p883 := nat_lit 14411518807585587200000000000000 

noncomputable def Ns252p884 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz136 884279719003555 140737488355328 1 500000000000000 7010539 16777216 31 16777216 6199277456983463466145 2361183241434822606848 Ns252p882 

noncomputable def Ns252p885 := @Enclosure.Real.IsNear.subLit_ff_p qz143 qz1 158005483 16777216 31 16777216 9 1 0 1 7010539 7010539 16777216 31 

noncomputable def Ns252p886 := @Ns252p885 16777216 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 158005483 16777216 31 16777216 158005483 16777216 31 16777216 (Ns252p872 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns252p887 := @Enclosure.Real.IsNear.recentre' qz147 Bool.false 6199277456983463466145 2361183241434822606848 Ns252p882 Ns252p883 44048515 16777216 49 4194304 (@Ns252p884 Ns252p883 RS253to264.d43 (Ns252p886 rfl rfl) rfl) 

noncomputable def Ns252p888 := nat_lit 2550107550050820082892800 

noncomputable def Ns252p889 := nat_lit 7272331073461666899828544109388123889371383043463953878150956657972376228143258762200225 

noncomputable def Ns252p890 := nat_lit 2974606838883894260745090508613122601114518384223123863069688398687615283346925143201 

noncomputable def Ns252p891 := nat_lit 19041765352755696527890694901859712749856579703116851289855154608710729220392639831721121 

noncomputable def Ns252p892 := BSN.sin_dyadic_bound_f 36239207901 34359738368 3 2 16777216 6486329 Ns252p889 Ns252p288 Ns252p890 Ns252p891 Ns252p291 Ns252p890 14592018 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 36239207901) qz363 0 2 Ns252p889 Ns252p288 Ns252p890 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 36239207901) qz364 0 2 Ns252p891 Ns252p291 Ns252p890 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p893 := @Ns252p881 3240000 (Ns252p887 rfl) (Enclosure.sfrac_false_div 44048515 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44048515) qz410) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns252p888) qz411) 226375608064910080 72057594037927936 Bool.false 14592018 16777216 0 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 44048515 16777216 226375608064910080 72057594037927936 0 Ns252p888 Ns252p93 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 14592018 16777216 Ns252p888 Ns252p93 36239207901 34359738368 6486329 6480000 (Ns252p892 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p894 := @Enclosure.Real.IsNear.inv_image qz146 7296009 8388608 2546161 212336640000 9644693 9644960 8388608 (@Enclosure.Real.IsNear.neg qz144 Bool.true 7296009 8388608 2546161 212336640000 (Ns252p880 (Ns252p893 rfl rfl) rfl)) 

noncomputable def Ns252p895 := Ns252p878 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz146) Bool.false 19289653 16777216 267 16777216 (@Ns252p879 267 16777216 (Ns252p894 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p896 := @Enclosure.Real.IsNear.recentre' qz145 Bool.true 2878856 8388608 

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz346 qz343 qz467)

noncomputable def Ns252p897 := @Enclosure.Real.IsNear.cos_image qz148 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32230769)) qz410) Bool.true 32230769 16777216 

noncomputable def Ns252p898 := nat_lit 76102753887753324235630549045 

noncomputable def Ns252p899 := nat_lit 25764903549328905702899199517499373 

noncomputable def Ns252p900 := @Enclosure.Real.IsNear.recentre' qz148 Bool.true Ns252p898 Ns252p183 Ns252p899 

noncomputable abbrev qz149 := qz467

noncomputable def Ns252p901 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz149 884279719003555 140737488355328 1 500000000000000 86061856053319 

noncomputable abbrev qz468 := (@HSub.hSub Real Real Real qz588 qz663 qz656)

noncomputable abbrev qz150 := qz468

noncomputable def Ns252p902 := @Enclosure.Real.IsNear.subLit_tf qz150 qz31 68469670008903 281474976710656 954748075 281474976710656 1 16 

noncomputable abbrev qz469 := qz663

noncomputable abbrev qz151 := qz469

noncomputable def Ns252p903 := @Enclosure.Real.IsNear.subLit_ff_n qz151 qz136 49147657070521 281474976710656 434654379 281474976710656 7010539 16777216 31 16777216 

noncomputable def Ns252p904 := @Enclosure.Real.IsNear.mulLit_ff qz136 qz136 7010539 16777216 31 16777216 7010539 16777216 31 16777216 49147657070521 281474976710656 

noncomputable def Ns252p905 := nat_lit 136294542273822671366416920085213607578953582005226486153885811916055976296553244469161167045441 

noncomputable def Ns252p906 := nat_lit 1256747443930177193898886457691452687358967210691895388385372349561658181128296978746852161 

noncomputable def Ns252p907 := nat_lit 822413959190691297710444955409419243768102288324698024681185749680545646775927086568478310286145 

noncomputable def Ns252p908 := BSN.cos_dyadic_bound_t 32230769 16777216 4 3 8388608 3240000 Ns252p905 Ns252p567 Ns252p906 Ns252p907 Ns252p570 Ns252p906 2878856 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32230769) (BSN.cosEvenQ 16777216) 0 3 Ns252p905 Ns252p567 Ns252p906 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32230769) (BSN.cosOddQ 16777216) 0 3 Ns252p907 Ns252p570 Ns252p906 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p909 := @Ns252p896 1179937216 54358179840000 359857 1048576 18436519 849346560000 (@Ns252p897 359 16777216 Bool.true 2878856 8388608 1 3240000 (@Ns252p900 Ns252p186 32230769 16777216 359 16777216 (@Ns252p901 281474976710656 954748075 281474976710656 Ns252p898 Ns252p183 Ns252p899 Ns252p186 RS253to264.d43 (@Ns252p902 0 1 1376989696853104 86061856053319 281474976710656 954748075 281474976710656 (@Ns252p903 1148730443188087554048 68469670008903 281474976710656 954748075 281474976710656 (@Ns252p904 434654379 281474976710656 (Ns252p886 rfl rfl) (Ns252p886 rfl rfl) rfl) (Ns252p886 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32230769 16777216) (BSN.cos_neg_of_bound 32230769 16777216 Bool.true 2878856 8388608 1 3240000 (Ns252p908 rfl rfl)) rfl rfl) 

noncomputable def Ns252p910 := @Ns252p870 29691856767751807379 Ns252p796 (Ns252p871 qz33 (@Enclosure.Real.IsNear.of_eq qz661 (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 5466933 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz135 (BSN.t_div_two_pi_nonneg qz134 557294 1000 qz137)) Ns252p875) rfl) (@Ns252p876 17592186044416 5418315624731 178120883699712000 (BSN.correction_mk qz136 (BSN.cos_two_pi_p_ne_zero_mk qz134 557294 1000 9 qz137 rfl rfl (@BSN.floor_sqrt_eq_dec qz134 557294 1000 9 qz137 rfl rfl rfl))) (@Ns252p877 16777216 359857 1048576 18436519 849346560000 6941516659621 17592186044416 5418315624731 178120883699712000 Ns252p895 (Ns252p909 rfl) rfl)) 

noncomputable def Ns252p911 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (hardyZApproximantRS₀ qz134) Bool.true 88615053386996215767 295147905179352825856 4284465405702772351379 Ns252p796 (@Eq.refl Real (hardyZApproximantRS₀ qz134)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) (@HMul.hMul Real Real Real qz5 qz657 (Zeta.RiemannSiegel.correction qz136))) Bool.true 88615053386996215767 295147905179352825856 4284465405702772351379 Ns252p796 (BSN.hardyZApproximantRS₀_eq qz134 9 (@BSN.floor_sqrt_eq_dec qz134 557294 1000 9 qz137 rfl rfl rfl)) (@Ns252p798 88615053386996215767 295147905179352825856 4284465405702772351379 Ns252p796 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 9)) Bool.true 14388645 33554432 23887 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz134) qz134 9) (Ns252p869 (Ns252p868 rfl) rfl rfl)) (Ns252p910 rfl) rfl rfl)) 

theorem RS253to264.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz134) Bool.true 88615053386996215767 295147905179352825856 4284465405702772351379 Ns252p796 := Ns252p911 

noncomputable def Ns252p912 := nat_lit 1992248359960631574528000 

noncomputable def Ns252p913 := nat_lit 36000564190880655324431253504 

noncomputable abbrev qz768 := (Enclosure.sfrac Bool.false 558694 1000)

noncomputable abbrev qz664 := qz768

noncomputable abbrev qz470 := qz664

noncomputable abbrev qz152 := qz470

noncomputable abbrev qz769 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 558694 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz665 := qz769

noncomputable abbrev qz471 := qz665

noncomputable abbrev qz153 := qz471

noncomputable abbrev qz770 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 558694 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz666 := qz770

noncomputable abbrev qz472 := qz666

noncomputable abbrev qz154 := qz472

noncomputable abbrev qz667 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz153 qz9))

noncomputable def Ns252p914 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (@HMul.hMul Real Real Real qz5 qz667 (Zeta.RiemannSiegel.correction qz154)) 28355341 16777216 47895 33554432 150471103411662171995 1180591620717411303424 18553056036855119173 Ns252p912 Ns252p913 

noncomputable def Ns252p915 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 558694 1000 119 161 134217728 67108864 2251799813685248 Bool.false 130713680510 1852 

noncomputable def Ns252p916 := Ns252p915 279097919 42 47453128 8 294906479 42 44739240 8 Bool.false 106340469 78380 Bool.true 128035265 Bool.true 105376892 7074237752028440 1 Bool.false 109481308 Bool.false Bool.false 94879770 Bool.true Bool.false 113421364 

noncomputable def Ns252p917 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 558694 1000 17 72 134217728 67108864 2251799813685248 Bool.false 130713680510 1852 

noncomputable def Ns252p918 := Ns252p917 240485871 42 54794152 8 261175631 42 50729528 8 Bool.false 80190927 58455 Bool.true 60244562 Bool.true 23910058 7074237752028440 1 Bool.false 58241904 Bool.true Bool.false 132093639 Bool.false Bool.false 106340469 

noncomputable def Ns252p919 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 558694 1000 126 47 134217728 67108864 2251799813685248 Bool.false 130713680510 1852 

noncomputable def Ns252p920 := Ns252p919 186065264 42 67108856 8 216015088 42 60023992 8 Bool.false 41387217 34454 Bool.false 195715924 Bool.false 118397370 7074237752028440 1 Bool.false 15080875 Bool.true Bool.false 103628664 Bool.false Bool.false 80190927 

noncomputable def Ns252p921 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 558694 1000 373 229 134217728 67108864 2251799813685248 Bool.false 130713680510 1852 

noncomputable def Ns252p922 := Ns252p921 93032624 42 94906264 8 147453232 42 77490640 16 Bool.false 134217672 1906 Bool.false 97801305 Bool.false 52668974 7074237752028440 1 Bool.false 89373278 Bool.true Bool.false 51327602 Bool.true Bool.false 41387217 

noncomputable def Ns252p923 := nat_lit 2344706951234121612928327514991133620535169743991313131 

noncomputable def Ns252p924 := nat_lit 2407561615516059297046691379257504882025018949632000 

noncomputable def Ns252p925 := nat_lit 26128360248250403536457520747520000 

noncomputable def Ns252p926 := nat_lit 87586581340149106728738529609745633280 

noncomputable abbrev qz668 := (@Eq.refl Real qz768)

noncomputable abbrev qz473 := qz668

noncomputable abbrev qz155 := qz473

noncomputable def Ns252p927 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz152 558694 1000 1248556942544 16000000 1117388 4000 2000 Ns252p925 Ns252p926 qz155 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns252p928 := nat_lit 48019598361274810632772147507018416548560276356942092922880 

noncomputable abbrev qz669 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1117388))))

noncomputable abbrev qz474 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 558694 4000) (Real.log (Enclosure.sfrac Bool.false 1248556942544 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz669))

noncomputable abbrev qz670 := (Enclosure.sfrac Bool.false 558694 2000)

noncomputable abbrev qz156 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz474 qz670) (@HMul.hMul Real Real Real qz346 qz670 (Real.log Real.pi)))

noncomputable def Ns252p929 := @Enclosure.Real.IsNear.addLit_ft_p qz156 (Enclosure.sfrac Bool.true Ns252p925 Ns252p926) 548253080957072632071 562949953421312000 127097765665206991 9216000000000000000000 Ns252p925 Ns252p926 0 1 Ns252p928 

noncomputable def Ns252p930 := nat_lit 18396320723764588551887388672000 

noncomputable abbrev qz157 := (@HSub.hSub Real Real Real qz350 qz474 qz670)

noncomputable def Ns252p931 := @Enclosure.Real.IsNear.subLit_ff_p qz157 (@HMul.hMul Real Real Real qz5 qz670 (Real.log Real.pi)) 728271448544041953543 562949953421312000 49192207614109 9000000000000000000 10729930853067 33554432000 279347 33554432000 Ns252p930 548253080957072632071 562949953421312000 

noncomputable def Ns252p932 := nat_lit 1456542897088083907086000 

noncomputable abbrev qz158 := qz474

noncomputable def Ns252p933 := @Enclosure.Real.IsNear.subLit_ff_p qz158 qz670 885529829182425196807 562949953421312000 49192207614109 9000000000000000000 558694 2000 0 1 Ns252p932 728271448544041953543 562949953421312000 49192207614109 9000000000000000000 

noncomputable def Ns252p934 := nat_lit 1994035904365714545444089298352603136 

noncomputable def Ns252p935 := nat_lit 27236881750317943490609152 

noncomputable def Ns252p936 := nat_lit 15427873839685262056091619372313612887013588452242266010332425140000658554880 

noncomputable def Ns252p937 := nat_lit 39153521686769921945665382576979907513691212316102543474923484347971403776 

noncomputable def Ns252p938 := nat_lit 959451275997776304498988841532176565802126793734326853349964345507840 

noncomputable def Ns252p939 := BSN.log_dyadic_bound 199980942544 2297132942544 4 3 Ns252p936 67108864 25920000 Ns252p937 Ns252p938 11714213 2497113885088 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 199980942544) (BSN.artanhQ 2297132942544) 0 3 Ns252p937 Ns252p936 Ns252p938 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz475 := (Real.log (Enclosure.sfrac Bool.false 1248556942544 16000000))

noncomputable def Ns252p940 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 558694 4000) qz475 558694 4000 0 1 3170790354525431 281474976710656 195312581 5062500000000000 885750773165615573557 562949953421312000 54559983564607 10125000000000000000 (Enclosure.Real.IsNear.const Bool.false 558694 4000) (BSN.isNear_log_sfrac 1248556942544 16000000 3170790354525431 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1248556942544) qz353)) Bool.false Ns252p935 Ns252p93 1000000414720000 25920000000000000000000 3170790354525431 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1248556942544 16000000 16 2497113885088 2097152000000 11714213 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns252p939 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p941 := BSN.arctan_dyadic_bound_f 1000 1117388 1 0 8388608 3240000 0 1 1 0 1 1 7507 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1117388) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1117388) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns252p942 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1117388))) 884279719003555 562949953421312 1 2000000000000000 7507 8388608 1 3240000 7413649859770639712256 883775932761507 562949953421312 50000000081 162000000000000000 qz17 (Ns252p941 rfl) rfl rfl 

noncomputable abbrev qz476 := (@HMul.hMul Real Real Real qz584 qz589 qz669)

noncomputable abbrev qz159 := qz476

noncomputable abbrev qz477 := qz669

noncomputable abbrev qz160 := qz477

noncomputable def Ns252p943 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 558694 4000) qz475) qz159 885750773165615573557 562949953421312000 54559983564607 10125000000000000000 883775932761507 2251799813685248 50000000081 648000000000000000 Ns252p934 885529829182425196807 562949953421312000 49192207614109 9000000000000000000 (Ns252p940 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz160 1 4 0 1 883775932761507 562949953421312 50000000081 162000000000000000 883775932761507 2251799813685248 50000000081 648000000000000000 qz361 Ns252p942 rfl) 

noncomputable def Ns252p944 := @Ns252p929 Ns252p923 Ns252p924 127097765665206991 9216000000000000000000 (@Ns252p931 127097765665206991 9216000000000000000000 (Ns252p933 (Ns252p943 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 558694 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz670 (Real.log Real.pi) 558694 2000 0 1 38410761 33554432 1 33554432 10729930853067 33554432000 279347 33554432000 (Enclosure.Real.IsNear.const Bool.false 558694 2000) RS253to264.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns252p925 Ns252p926) 

noncomputable def Ns252p945 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns252p923 Ns252p924 127097765665206991 9216000000000000000000 16339210063 16777216 233 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz362 qz156 (Enclosure.sfrac Bool.true Ns252p925 Ns252p926)) Bool.false Ns252p923 Ns252p924 127097765665206991 9216000000000000000000 Ns252p927 (Ns252p944 rfl rfl)) 

noncomputable def Ns252p946 := nat_lit 3795750059268381255663616 

noncomputable def Ns252p947 := nat_lit 855147113839210674766421481407822083088361496321558406809944908324069753313063331140131024911953523086708223395350206930195455085955121 

noncomputable def Ns252p948 := nat_lit 606755446192031368709435301404480422279624205455315255309056909056151919600394089957813267780517721838007928226731703102121756721 

noncomputable def Ns252p949 := nat_lit 4270434734588378006510428985572162886631367488439207697610665331873358034617069004760813506165464191351439585887960694830806502526994481 

noncomputable def Ns252p950 := BSN.sin_dyadic_bound_f 53940852627 34359738368 4 3 16777216 6486329 Ns252p947 Ns252p107 Ns252p948 Ns252p949 Ns252p110 Ns252p948 16777209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53940852627) qz363 0 3 Ns252p947 Ns252p107 Ns252p948 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53940852627) qz364 0 3 Ns252p949 Ns252p110 Ns252p948 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p951 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz152) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16339210063) qz410) Bool.false 16339210063 16777216 233 16777216 Bool.false 16777209 16777216 1 3240000 (Ns252p945 rfl) (Enclosure.sfrac_false_div 16339210063 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16339210063) qz410) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns252p946) qz411) 226375608064910080 72057594037927936 Bool.false 16777209 16777216 154 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q3 16339210063 16777216 226375608064910080 72057594037927936 154 Ns252p946 Ns252p93 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777209 16777216 Ns252p946 Ns252p93 53940852627 34359738368 6486329 6480000 (Ns252p950 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p952 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns252p923 Ns252p924 127097765665206991 9216000000000000000000 130713680510 134217728 1852 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz362 qz156 (Enclosure.sfrac Bool.true Ns252p925 Ns252p926)) Bool.false Ns252p923 Ns252p924 127097765665206991 9216000000000000000000 Ns252p927 (Ns252p944 rfl rfl)) 

noncomputable def Ns252p953 := Ns252p922 34454 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 373 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 89373278 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 229 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 51327602 134217728) qz155 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) Bool.false 16777209 16777216 12057769 849346560000 134217672 134217728 1906 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 16777209 16777216 12057769 849346560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz152) qz152) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 16777209 16777216 771697216 54358179840000 16777209 16777216 12057769 849346560000 (Ns252p951 rfl rfl) rfl)) rfl) (Ns252p952 rfl) RS253to264.d7 

noncomputable def Ns252p954 := nat_lit 89792570682118891158469320086806869854510493661992022721717969330625 

noncomputable def Ns252p955 := nat_lit 8370611741026720490682074546447205566769441220717008215187890625 

noncomputable def Ns252p956 := nat_lit 235157466034159243105672829249514220809943190019431279591198663090625 

noncomputable def Ns252p957 := BSN.sin_dyadic_bound_f 97801305 134217728 3 2 134217728 67108864 Ns252p954 Ns252p116 Ns252p955 Ns252p956 Ns252p119 Ns252p955 89373278 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 97801305) qz367 0 2 Ns252p954 Ns252p116 Ns252p955 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 97801305) qz368 0 2 Ns252p956 Ns252p119 Ns252p955 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p958 := nat_lit 7695191522069490988724575080976 

noncomputable def Ns252p959 := BSN.sin_dyadic_bound_f 52668974 134217728 2 1 134217728 67108864 Ns252p958 Ns252p238 Ns252p958 Ns252p958 Ns252p239 Ns252p958 51327602 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 52668974) qz367 0 1 Ns252p958 Ns252p238 Ns252p958 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 52668974) qz368 0 1 Ns252p958 Ns252p239 Ns252p958 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p960 := nat_lit 3092267880259221834951115793551005173519837892584947888793371304516502944563924669960876067833912760467456 

noncomputable def Ns252p961 := nat_lit 3158740510678828297900575843790569447529237110369836664190369306957826521118775332054206215960395776 

noncomputable def Ns252p962 := nat_lit 18726174571297576346770494437582898423641494174275283444895847260757903809278773201177177089398172161146880 

noncomputable def Ns252p963 := BSN.cos_dyadic_bound_f 195715924 134217728 4 3 134217728 67108864 Ns252p960 Ns252p398 Ns252p961 Ns252p962 Ns252p401 Ns252p961 15080875 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 195715924) qz369 0 3 Ns252p960 Ns252p398 Ns252p961 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 195715924) qz370 0 3 Ns252p962 Ns252p401 Ns252p961 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p964 := nat_lit 192875246290544169312401742964278508008767506020301787084026887840000 

noncomputable def Ns252p965 := nat_lit 38613257652930216388952790254060862115789583174237077472100000000 

noncomputable def Ns252p966 := nat_lit 505086937867606175467851022293651422436679808823270201380353687200000 

noncomputable def Ns252p967 := BSN.sin_dyadic_bound_f 118397370 134217728 3 2 134217728 67108864 Ns252p964 Ns252p116 Ns252p965 Ns252p966 Ns252p119 Ns252p965 103628664 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 118397370) qz367 0 2 Ns252p964 Ns252p116 Ns252p965 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 118397370) qz368 0 2 Ns252p966 Ns252p119 Ns252p965 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p968 := Ns252p920 58455 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 126 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 15080875 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 47 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 103628664 134217728) qz155 rfl rfl (Ns252p953 RS253to264.d9 RS253to264.d11 RS253to264.d13 RS253to264.d17 (Ns252p957 rfl rfl) (Ns252p959 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns252p952 rfl) RS253to264.d19 RS253to264.d21 RS253to264.d23 RS253to264.d25 RS253to264.d17 (Ns252p963 rfl rfl) (Ns252p967 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns252p969 := nat_lit 13172596990503472019265005560336 

noncomputable def Ns252p970 := BSN.sin_dyadic_bound_f 60244562 134217728 2 1 134217728 67108864 Ns252p969 Ns252p238 Ns252p969 Ns252p969 Ns252p239 Ns252p969 58241904 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 60244562) qz367 0 1 Ns252p969 Ns252p238 Ns252p969 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 60244562) qz368 0 1 Ns252p969 Ns252p239 Ns252p969 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p971 := nat_lit 326830454915642243270922996496 

noncomputable def Ns252p972 := BSN.cos_dyadic_bound_f 23910058 134217728 2 1 134217728 67108864 Ns252p971 Ns252p122 Ns252p971 Ns252p971 Ns252p123 Ns252p971 132093639 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 23910058) qz369 0 1 Ns252p971 Ns252p122 Ns252p971 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 23910058) qz370 0 1 Ns252p971 Ns252p123 Ns252p971 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p973 := Ns252p918 78380 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 17 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58241904 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 72 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 132093639 134217728) qz155 rfl rfl (Ns252p968 rfl rfl) (Ns252p952 rfl) RS253to264.d27 RS253to264.d29 RS253to264.d31 RS253to264.d33 RS253to264.d17 (Ns252p970 rfl rfl) (Ns252p972 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p974 := nat_lit 263790194613635496951030467783494064931732233980836658761752019930625 

noncomputable def Ns252p975 := nat_lit 72216566709190624338990363170195004819504613530545283938812890625 

noncomputable def Ns252p976 := nat_lit 690762159070563802432340478844970806718162367242189413916306736090625 

noncomputable def Ns252p977 := BSN.sin_dyadic_bound_f 128035265 134217728 3 2 134217728 67108864 Ns252p974 Ns252p116 Ns252p975 Ns252p976 Ns252p119 Ns252p975 109481308 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 128035265) qz367 0 2 Ns252p974 Ns252p116 Ns252p975 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 128035265) qz368 0 2 Ns252p976 Ns252p119 Ns252p975 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p978 := nat_lit 121020077043082667318599013370461821245696623251518391609709826211840 

noncomputable def Ns252p979 := nat_lit 15204182793197615420508891030070349063483982188528873552247586816 

noncomputable def Ns252p980 := nat_lit 316932728340694189695173734908589417935483610639957216992060191604736 

noncomputable def Ns252p981 := BSN.sin_dyadic_bound_f 105376892 134217728 3 2 134217728 67108864 Ns252p978 Ns252p116 Ns252p979 Ns252p980 Ns252p119 Ns252p979 94879770 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 105376892) qz367 0 2 Ns252p978 Ns252p116 Ns252p979 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 105376892) qz368 0 2 Ns252p980 Ns252p119 Ns252p979 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p982 := Ns252p916 95790 BSN.abs_quadSignPos qz650 (BSN.sfrac_eq_quadSignPos_mul Bool.false 109481308 134217728) BSN.abs_quadSignNeg qz371 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 94879770 134217728) qz155 rfl rfl (Ns252p973 rfl) (Ns252p952 rfl) RS253to264.d35 RS253to264.d37 RS253to264.d39 RS253to264.d41 RS253to264.d17 (Ns252p977 rfl rfl) (Ns252p981 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p983 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) 113421364 134217728 95790 134217728 113421364 134217728 95790 134217728 30446315565481984 28355341 16777216 47895 33554432 (Ns252p982 rfl) 

noncomputable def Ns252p984 := @Enclosure.Real.IsNear.mulLit_tf qz667 (Zeta.RiemannSiegel.correction qz154) 5463505 16777216 1 16777216 27541130357099 70368744177664 13549234048157 474989023199232000 150471103411662171995 1180591620717411303424 

noncomputable abbrev qz671 := (@HPow.hPow Real Real Real qz7 qz153 qz9)

noncomputable def Ns252p985 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz671 1 1 0 1 5463505 16777216 1 16777216 5463505 16777216 1 16777216 

noncomputable def Ns252p986 := @Enclosure.Real.IsNear.sqrt_image qz153 745905934419 8388608000 279347 8388608000 79101897 79101927 8388608 (@Enclosure.Real.IsNear.of_eq qz153 (@HMul.hMul Real Real Real qz5 qz152 qz3) Bool.false 745905934419 8388608000 279347 8388608000 (BSN.t_div_two_pi_mk qz152 558694 1000 qz155) (@Enclosure.Real.IsNear.mulLit_ff qz152 qz3 558694 1000 0 1 2670177 16777216 1 16777216 745905934419 8388608000 279347 8388608000 (Enclosure.Real.IsNear.const Bool.false 558694 1000) RS253to264.d44 rfl)) 

noncomputable abbrev qz771 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 558694 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz672 := qz771

noncomputable abbrev qz478 := qz672

noncomputable abbrev qz161 := qz478

noncomputable def Ns252p987 := @Enclosure.Real.IsNear.sqrt_image qz161 9887739 1048576 15 8388608 25759557 25759563 8388608 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 158203824 16777216 30 16777216 9887739 1048576 15 8388608 (Ns252p986 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns252p988 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz161) 3219945 1048576 3 8388608 2731752 2731753 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz161) Bool.false 51519120 16777216 6 16777216 3219945 1048576 3 8388608 (Ns252p987 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns252p989 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 5463505 16777216 1 16777216 5463505 16777216 1 16777216 (Ns252p988 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz479 := (@HMul.hMul Real Real Real qz584 qz582 qz666)

noncomputable abbrev qz162 := (Real.cos qz479)

noncomputable abbrev qz673 := (@HMul.hMul Real Real Real qz735 qz770 qz770)

noncomputable abbrev qz480 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz673 qz666) qz599)

noncomputable abbrev qz163 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz480))

noncomputable def Ns252p990 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz154) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz162) qz163) Bool.false 27541130357099 

noncomputable def Ns252p991 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz162) qz163 18559351 16777216 239 

noncomputable abbrev qz164 := (@Neg.neg Real Real.instNeg (Real.cos qz479))

noncomputable def Ns252p992 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz162) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz164)) Bool.true 18559351 16777216 239 16777216 (BSN.inv_eq_neg_inv_neg qz162) 

noncomputable def Ns252p993 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz164) Bool.false 18559351 16777216 239 16777216 18559351 16777216 

noncomputable def Ns252p994 := @Enclosure.Real.IsNear.recentre' qz162 Bool.true 15166208 16777216 316188608 27179089920000 59243 65536 4940447 424673280000 

noncomputable abbrev qz165 := qz479

noncomputable def Ns252p995 := @Enclosure.Real.IsNear.cos_image qz165 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5661841) (@Nat.cast Real Real.instNatCast 2097152)) Bool.false 5661841 2097152 95 8388608 Bool.true 15166208 16777216 1 

noncomputable def Ns252p996 := nat_lit 80958226233324517133664597 

noncomputable def Ns252p997 := nat_lit 7205759403792793600000000000000 

noncomputable def Ns252p998 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz154 884279719003555 140737488355328 1 500000000000000 450555 1048576 15 8388608 398416648795646723025 147573952589676412928 Ns252p996 

noncomputable def Ns252p999 := @Enclosure.Real.IsNear.subLit_ff_p qz161 qz1 9887739 1048576 15 8388608 9 1 0 1 450555 450555 1048576 15 

noncomputable def Ns252p1000 := @Ns252p999 8388608 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 158203824 16777216 30 16777216 9887739 1048576 15 8388608 (Ns252p986 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns252p1001 := @Enclosure.Real.IsNear.recentre' qz165 Bool.false 398416648795646723025 147573952589676412928 Ns252p996 Ns252p997 5661841 2097152 95 8388608 (@Ns252p998 Ns252p997 RS253to264.d43 (Ns252p1000 rfl rfl) rfl) 

noncomputable def Ns252p1002 := nat_lit 9549015186088919705642539241504685875168404293488353788532043502378356874627082275390625 

noncomputable def Ns252p1003 := nat_lit 5127294922148559303308519198615317293556417517241434379838610733261168003082275390625 

noncomputable def Ns252p1004 := nat_lit 25001024152739882514001293744285942968870538949822535695254660945994226113923082275390625 

noncomputable def Ns252p1005 := BSN.sin_dyadic_bound_f 38791452125 34359738368 3 2 16777216 6486329 Ns252p1002 Ns252p288 Ns252p1003 Ns252p1004 Ns252p291 Ns252p1003 15166208 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 38791452125) qz363 0 2 Ns252p1002 Ns252p288 Ns252p1003 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 38791452125) qz364 0 2 Ns252p1004 Ns252p291 Ns252p1003 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1006 := @Ns252p995 3240000 (Ns252p1001 rfl) (Enclosure.sfrac_false_div 5661841 2097152) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5661841) (@Nat.cast Real Real.instNatCast 2097152)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 341213221366049582088192) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 15166208 16777216 0 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 5661841 2097152 226375608064910080 72057594037927936 0 341213221366049582088192 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 15166208 16777216 341213221366049582088192 302231454903657293676544 38791452125 34359738368 6486329 6480000 (Ns252p1005 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p1007 := @Enclosure.Real.IsNear.inv_image qz164 59243 65536 4940447 424673280000 9279556 9279795 8388608 (@Enclosure.Real.IsNear.neg qz162 Bool.true 59243 65536 4940447 424673280000 (Ns252p994 (Ns252p1006 rfl rfl) rfl)) 

noncomputable def Ns252p1008 := Ns252p992 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz164) Bool.false 18559351 16777216 239 16777216 (@Ns252p993 239 16777216 (Ns252p1007 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p1009 := @Enclosure.Real.IsNear.recentre' qz163 Bool.true 2967898 8388608 

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz346 qz343 qz480)

noncomputable def Ns252p1010 := @Enclosure.Real.IsNear.cos_image qz166 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32420763)) qz410) Bool.true 32420763 16777216 

noncomputable def Ns252p1011 := nat_lit 299028762307602863873930005 

noncomputable def Ns252p1012 := nat_lit 154742504910672534362390528 

noncomputable def Ns252p1013 := nat_lit 6313730882447766773224149426835223 

noncomputable def Ns252p1014 := @Enclosure.Real.IsNear.recentre' qz166 Bool.true Ns252p1011 Ns252p1012 Ns252p1013 

noncomputable abbrev qz167 := qz480

noncomputable def Ns252p1015 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz167 884279719003555 140737488355328 1 500000000000000 338160828391 

noncomputable abbrev qz481 := (@HSub.hSub Real Real Real qz588 qz673 qz666)

noncomputable abbrev qz168 := qz481

noncomputable def Ns252p1016 := @Enclosure.Real.IsNear.subLit_tf qz168 qz31 269441351655 1099511627776 233962545 70368744177664 1 16 

noncomputable abbrev qz482 := qz673

noncomputable abbrev qz169 := qz482

noncomputable def Ns252p1017 := @Enclosure.Real.IsNear.subLit_ff_n qz169 qz154 202999808025 1099511627776 108133425 70368744177664 450555 1048576 15 8388608 

noncomputable def Ns252p1018 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz154 450555 1048576 15 8388608 450555 1048576 15 8388608 202999808025 1099511627776 

noncomputable def Ns252p1019 := nat_lit 139563545290653140530516371879601967968608910191641055947129808895092585690921620274323443582161 

noncomputable def Ns252p1020 := nat_lit 1348586405393265618503659312440544909362378108944266769361010304771487782671546893856310481 

noncomputable def Ns252p1021 := nat_lit 842032016818317549182489272394241853160033495021128204503098756992173034094952037759998990386385 

noncomputable def Ns252p1022 := BSN.cos_dyadic_bound_t 32420763 16777216 4 3 8388608 3240000 Ns252p1019 Ns252p567 Ns252p1020 Ns252p1021 Ns252p570 Ns252p1020 2967898 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32420763) (BSN.cosEvenQ 16777216) 0 3 Ns252p1019 Ns252p567 Ns252p1020 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32420763) (BSN.cosOddQ 16777216) 0 3 Ns252p1021 Ns252p570 Ns252p1020 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1023 := @Ns252p1009 1154017216 54358179840000 1483949 4194304 18031519 849346560000 (@Ns252p1010 351 16777216 Bool.true 2967898 8388608 1 3240000 (@Ns252p1014 Ns252p302 32420763 16777216 351 16777216 (@Ns252p1015 1099511627776 233962545 70368744177664 Ns252p1011 Ns252p1012 Ns252p1013 Ns252p302 RS253to264.d43 (@Ns252p1016 0 1 5410573254256 338160828391 1099511627776 233962545 70368744177664 (@Ns252p1017 282529734752993280 269441351655 1099511627776 233962545 70368744177664 (@Ns252p1018 108133425 70368744177664 (Ns252p1000 rfl rfl) (Ns252p1000 rfl rfl) rfl) (Ns252p1000 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32420763 16777216) (BSN.cos_neg_of_bound 32420763 16777216 Bool.true 2967898 8388608 1 3240000 (Ns252p1022 rfl rfl)) rfl rfl) 

noncomputable def Ns252p1024 := @Ns252p984 18553056036855119173 Ns252p912 (Ns252p985 qz33 (@Enclosure.Real.IsNear.of_eq qz671 (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 5463505 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz153 (BSN.t_div_two_pi_nonneg qz152 558694 1000 qz155)) Ns252p989) rfl) (@Ns252p990 70368744177664 13549234048157 474989023199232000 (BSN.correction_mk qz154 (BSN.cos_two_pi_p_ne_zero_mk qz152 558694 1000 9 qz155 rfl rfl (@BSN.floor_sqrt_eq_dec qz152 558694 1000 9 qz155 rfl rfl rfl))) (@Ns252p991 16777216 1483949 4194304 18031519 849346560000 27541130357099 70368744177664 13549234048157 474989023199232000 Ns252p1008 (Ns252p1023 rfl) rfl)) 

noncomputable def Ns252p1025 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (hardyZApproximantRS₀ qz152) Bool.false 2145800840311089475419 1180591620717411303424 2862252964302757199173 Ns252p912 (@Eq.refl Real (hardyZApproximantRS₀ qz152)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (@HMul.hMul Real Real Real qz5 qz667 (Zeta.RiemannSiegel.correction qz154))) Bool.false 2145800840311089475419 1180591620717411303424 2862252964302757199173 Ns252p912 (BSN.hardyZApproximantRS₀_eq qz152 9 (@BSN.floor_sqrt_eq_dec qz152 558694 1000 9 qz155 rfl rfl rfl)) (@Ns252p914 2145800840311089475419 1180591620717411303424 2862252964302757199173 Ns252p912 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 9)) Bool.false 28355341 16777216 47895 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz152) qz152 9) (Ns252p983 (Ns252p982 rfl) rfl rfl)) (Ns252p1024 rfl) rfl rfl)) 

theorem RS253to264.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz152) Bool.false 2145800840311089475419 1180591620717411303424 2862252964302757199173 Ns252p912 := Ns252p1025 

noncomputable def Ns252p1026 := nat_lit 90812880676982588350398464 

noncomputable abbrev qz772 := (Enclosure.sfrac Bool.false 560094 1000)

noncomputable abbrev qz674 := qz772

noncomputable abbrev qz483 := qz674

noncomputable abbrev qz170 := qz483

noncomputable abbrev qz773 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 560094 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz675 := qz773

noncomputable abbrev qz484 := qz675

noncomputable abbrev qz171 := qz484

noncomputable abbrev qz774 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 560094 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz676 := qz774

noncomputable abbrev qz485 := qz676

noncomputable abbrev qz172 := qz485

noncomputable abbrev qz677 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz171 qz9))

noncomputable def Ns252p1027 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) (@HMul.hMul Real Real Real qz5 qz677 (Zeta.RiemannSiegel.correction qz172)) 11968265 16777216 48013 33554432 1166753772120781841 9223372036854775808 195823779721217953 20752587082923245568000 Ns252p1026 

noncomputable def Ns252p1028 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 560094 1000 119 161 134217728 67108864 2251799813685248 Bool.false 131135430753 1857 

noncomputable def Ns252p1029 := Ns252p1028 279097919 42 47453128 8 294906479 42 44739240 8 Bool.true 49800215 78573 Bool.true 97022109 Bool.true 96495720 7074237752028440 1 Bool.false 88790451 Bool.false Bool.false 88395025 Bool.true Bool.true 47873060 

noncomputable def Ns252p1030 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 560094 1000 16 71 134217728 67108864 2251799813685248 Bool.false 131135430753 1857 

noncomputable def Ns252p1031 := Ns252p1030 240485871 42 54794152 8 261175631 42 50729528 8 Bool.true 109154605 58598 Bool.true 186003252 Bool.true 178634412 7074237752028440 1 Bool.false 24684150 Bool.false Bool.false 130375042 Bool.false Bool.true 49800215 

noncomputable def Ns252p1032 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 560094 1000 127 48 134217728 67108864 2251799813685248 Bool.false 131135430753 1857 

noncomputable def Ns252p1033 := Ns252p1032 186065264 42 67108856 8 216015088 42 60023992 8 Bool.true 227442796 34536 Bool.false 146146083 Bool.false 26897776 7074237752028440 1 Bool.false 118931027 Bool.false Bool.false 131531524 Bool.false Bool.true 109154605 

noncomputable def Ns252p1034 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 560094 1000 374 230 134217728 67108864 2251799813685248 Bool.false 131135430753 1857 

noncomputable def Ns252p1035 := Ns252p1034 93032624 42 94906264 8 147453232 42 77490640 16 Bool.true 134217720 1906 Bool.false 178477160 Bool.false 57155978 7074237752028440 1 Bool.false 32039196 Bool.true Bool.false 122230730 Bool.true Bool.true 227442796 

noncomputable def Ns252p1036 := nat_lit 10612715677827643674499779849998146680107011512932183 

noncomputable def Ns252p1037 := nat_lit 10862164237389153228258458862722357426076432465920 

noncomputable def Ns252p1038 := nat_lit 26457372734735383302120499307520000 

noncomputable def Ns252p1039 := nat_lit 88911727413235329599343576559932641280 

noncomputable abbrev qz678 := (@Eq.refl Real qz772)

noncomputable abbrev qz486 := qz678

noncomputable abbrev qz173 := qz486

noncomputable def Ns252p1040 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz170 560094 1000 1254822155344 16000000 1120188 4000 2000 Ns252p1038 Ns252p1039 qz173 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns252p1041 := nat_lit 1956135753737191282083799421951658396077324362063659970560 

noncomputable abbrev qz679 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1120188))))

noncomputable abbrev qz487 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 560094 4000) (Real.log (Enclosure.sfrac Bool.false 1254822155344 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz679))

noncomputable abbrev qz680 := (Enclosure.sfrac Bool.false 560094 2000)

noncomputable abbrev qz174 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz487 qz680) (@HMul.hMul Real Real Real qz346 qz680 (Real.log Real.pi)))

noncomputable def Ns252p1042 := @Enclosure.Real.IsNear.addLit_ft_p qz174 (Enclosure.sfrac Bool.true Ns252p1038 Ns252p1039) 22000881170745000227 22517998136852480 1146730238131036819 82944000000000000000000 Ns252p1038 Ns252p1039 0 1 Ns252p1041 

noncomputable def Ns252p1043 := nat_lit 18455676779596087486421401600000 

noncomputable abbrev qz175 := (@HSub.hSub Real Real Real qz350 qz487 qz680)

noncomputable def Ns252p1044 := @Enclosure.Real.IsNear.subLit_ff_p qz175 (@HMul.hMul Real Real Real qz5 qz680 (Real.log Real.pi)) 730491494799409290347 562949953421312000 443823618980581 81000000000000000000 10756818385767 33554432000 280047 33554432000 Ns252p1043 22000881170745000227 22517998136852480 

noncomputable def Ns252p1045 := nat_lit 1460982989598818580694000 

noncomputable abbrev qz176 := qz487

noncomputable def Ns252p1046 := @Enclosure.Real.IsNear.subLit_ff_p qz176 qz680 888143940405187452011 562949953421312000 443823618980581 81000000000000000000 560094 2000 0 1 Ns252p1045 730491494799409290347 562949953421312000 443823618980581 81000000000000000000 

noncomputable def Ns252p1047 := nat_lit 1999922359530083107543090165058633728 

noncomputable def Ns252p1048 := nat_lit 27248984111466989639172096 

noncomputable def Ns252p1049 := nat_lit 15682069970696038828629428191939649086388154099108331230571632080553120890880 

noncomputable def Ns252p1050 := nat_lit 42112582252265101184496108574560077713408333298063859480995278106684030976 

noncomputable def Ns252p1051 := nat_lit 1154533206307241294316872834028575234646420324402763618894980411555840 

noncomputable def Ns252p1052 := BSN.log_dyadic_bound 206246155344 2303398155344 4 3 Ns252p1049 67108864 25920000 Ns252p1050 Ns252p1051 12050121 2509644310688 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 206246155344) (BSN.artanhQ 2303398155344) 0 3 Ns252p1050 Ns252p1049 Ns252p1051 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz488 := (Real.log (Enclosure.sfrac Bool.false 1254822155344 16000000))

noncomputable def Ns252p1053 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 560094 4000) qz488 560094 4000 0 1 3172199254793463 281474976710656 195312581 5062500000000000 888364884707144932761 562949953421312000 18232234123769 3375000000000000000 (Enclosure.Real.IsNear.const Bool.false 560094 4000) (BSN.isNear_log_sfrac 1254822155344 16000000 3172199254793463 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1254822155344) qz353)) Bool.false Ns252p1048 Ns252p93 1000000414720000 25920000000000000000000 3172199254793463 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1254822155344 16000000 16 2509644310688 2097152000000 12050121 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns252p1052 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p1054 := BSN.arctan_dyadic_bound_f 1000 1120188 1 0 8388608 3240000 0 1 1 0 1 1 7488 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1120188) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1120188) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns252p1055 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1120188))) 884279719003555 562949953421312 1 2000000000000000 7488 8388608 1 3240000 7413660555819754717184 883777207829923 562949953421312 50000000081 162000000000000000 qz17 (Ns252p1054 rfl) rfl rfl 

noncomputable abbrev qz489 := (@HMul.hMul Real Real Real qz584 qz589 qz679)

noncomputable abbrev qz177 := qz489

noncomputable abbrev qz490 := qz679

noncomputable abbrev qz178 := qz490

noncomputable def Ns252p1056 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 560094 4000) qz488) qz177 888364884707144932761 562949953421312000 18232234123769 3375000000000000000 883777207829923 2251799813685248 50000000081 648000000000000000 Ns252p1047 888143940405187452011 562949953421312000 443823618980581 81000000000000000000 (Ns252p1053 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz178 1 4 0 1 883777207829923 562949953421312 50000000081 162000000000000000 883777207829923 2251799813685248 50000000081 648000000000000000 qz361 Ns252p1055 rfl) 

noncomputable def Ns252p1057 := @Ns252p1042 Ns252p1036 Ns252p1037 1146730238131036819 82944000000000000000000 (@Ns252p1044 1146730238131036819 82944000000000000000000 (Ns252p1046 (Ns252p1056 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 560094 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz680 (Real.log Real.pi) 560094 2000 0 1 38410761 33554432 1 33554432 10756818385767 33554432000 280047 33554432000 (Enclosure.Real.IsNear.const Bool.false 560094 2000) RS253to264.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns252p1038 Ns252p1039) 

noncomputable def Ns252p1058 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns252p1036 Ns252p1037 1146730238131036819 82944000000000000000000 4097982211 4194304 233 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz362 qz174 (Enclosure.sfrac Bool.true Ns252p1038 Ns252p1039)) Bool.false Ns252p1036 Ns252p1037 1146730238131036819 82944000000000000000000 Ns252p1040 (Ns252p1057 rfl rfl)) 

noncomputable def Ns252p1059 := nat_lit 856657966489696264903411200594386896201367085579776321568227960511795416596717555745295133792553708710724602052857512652329567065893441 

noncomputable def Ns252p1060 := nat_lit 609970660354806766557888930886578949927373533683883362695416898521149803211180175227020356241603506779014102062401703441222232641 

noncomputable def Ns252p1061 := nat_lit 4277970283864848666312368383886499326209373469840158221663967196699343369662084109069093673288750269857026024232850472350233036537883201 

noncomputable def Ns252p1062 := BSN.sin_dyadic_bound_f 53964614479 34359738368 4 3 16777216 6486329 Ns252p1059 Ns252p107 Ns252p1060 Ns252p1061 Ns252p110 Ns252p1060 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53964614479) qz363 0 3 Ns252p1059 Ns252p107 Ns252p1060 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53964614479) qz364 0 3 Ns252p1061 Ns252p110 Ns252p1060 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1063 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz170) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4097982211) qz377) Bool.false 4097982211 4194304 233 16777216 Bool.true 16777215 16777216 1 3240000 (Ns252p1058 rfl) (Enclosure.sfrac_false_div 4097982211 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4097982211) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949355537735140373430272) qz642) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 155 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 4097982211 4194304 226375608064910080 72057594037927936 155 949355537735140373430272 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 949355537735140373430272 604462909807314587353088 53964614479 34359738368 6486329 6480000 (Ns252p1062 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p1064 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns252p1036 Ns252p1037 1146730238131036819 82944000000000000000000 131135430753 134217728 1857 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz362 qz174 (Enclosure.sfrac Bool.true Ns252p1038 Ns252p1039)) Bool.false Ns252p1036 Ns252p1037 1146730238131036819 82944000000000000000000 Ns252p1040 (Ns252p1057 rfl rfl)) 

noncomputable def Ns252p1065 := Ns252p1035 34536 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 374 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 32039196 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 230 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 122230730 134217728) qz173 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) Bool.true 16777215 16777216 12057769 849346560000 134217720 134217728 1906 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 16777215 16777216 12057769 849346560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz170) qz170) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 16777215 16777216 771697216 54358179840000 16777215 16777216 12057769 849346560000 (Ns252p1063 rfl rfl) rfl)) rfl) (Ns252p1064 rfl) RS253to264.d7 

noncomputable def Ns252p1066 := nat_lit 2136697891537888597748430971356973149331253127042974016528193073265037678975278902400506863565144064000000 

noncomputable def Ns252p1067 := nat_lit 1044700397516093973480657677267430983595437734067212263443653548611504175804961370669056000000000000 

noncomputable def Ns252p1068 := nat_lit 12946574849765178617972490160297721964030815389099603711356279594595712276700093459739182041453402521600000 

noncomputable def Ns252p1069 := BSN.cos_dyadic_bound_f 178477160 134217728 4 3 134217728 67108864 Ns252p1066 Ns252p398 Ns252p1067 Ns252p1068 Ns252p401 Ns252p1067 32039196 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 178477160) qz369 0 3 Ns252p1066 Ns252p398 Ns252p1067 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 178477160) qz370 0 3 Ns252p1068 Ns252p401 Ns252p1067 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1070 := nat_lit 5818405112483202060674901678101662383224059571413880611741062390016 

noncomputable def Ns252p1071 := nat_lit 113892016707562421140870727228726632769282204164603060135649536 

noncomputable def Ns252p1072 := nat_lit 17454987553416191057182423292850529696406640149833312629102915870976 

noncomputable def Ns252p1073 := BSN.cos_dyadic_bound_f 57155978 134217728 3 2 134217728 67108864 Ns252p1070 Ns252p144 Ns252p1071 Ns252p1072 Ns252p147 Ns252p1071 122230730 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 57155978) qz369 0 2 Ns252p1070 Ns252p144 Ns252p1071 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 57155978) qz370 0 2 Ns252p1072 Ns252p147 Ns252p1071 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1074 := nat_lit 447890529814769347185003565038507107872654326375033521643758007983265 

noncomputable def Ns252p1075 := nat_lit 208112151609606239869304763996940701512514086848532691185364475041 

noncomputable def Ns252p1076 := nat_lit 1172709682221789880143792367387714045197360117698761598995542287948961 

noncomputable def Ns252p1077 := BSN.sin_dyadic_bound_f 146146083 134217728 3 2 134217728 67108864 Ns252p1074 Ns252p116 Ns252p1075 Ns252p1076 Ns252p119 Ns252p1075 118931027 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 146146083) qz367 0 2 Ns252p1074 Ns252p116 Ns252p1075 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 146146083) qz368 0 2 Ns252p1076 Ns252p119 Ns252p1075 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1078 := nat_lit 523438291963766884837034622976 

noncomputable def Ns252p1079 := BSN.cos_dyadic_bound_f 26897776 134217728 2 1 134217728 67108864 Ns252p1078 Ns252p122 Ns252p1078 Ns252p1078 Ns252p123 Ns252p1078 131531524 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 26897776) qz369 0 1 Ns252p1078 Ns252p122 Ns252p1078 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 26897776) qz370 0 1 Ns252p1078 Ns252p123 Ns252p1078 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1080 := Ns252p1033 58598 BSN.abs_quadSignPos (BSN.cos_quad_nat3 127 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 118931027 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 48 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131531524 134217728) qz173 rfl rfl (Ns252p1065 RS253to264.d9 RS253to264.d11 RS253to264.d13 RS253to264.d17 (Ns252p1069 rfl rfl) (Ns252p1073 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns252p1064 rfl) RS253to264.d19 RS253to264.d21 RS253to264.d23 RS253to264.d25 RS253to264.d17 (Ns252p1077 rfl rfl) (Ns252p1079 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns252p1081 := nat_lit 2521387982246527760450314280038251481202520950195738200757334010210800093779900140931140249153063329202176 

noncomputable def Ns252p1082 := nat_lit 1714930197008318827740992599143653670162763157636554738773353971233197161004322966901170061071876096 

noncomputable def Ns252p1083 := nat_lit 15274071943632247002152198572420913024626730246299204492279976648460092555098925933852710436915954759761920 

noncomputable def Ns252p1084 := BSN.cos_dyadic_bound_f 186003252 134217728 4 3 134217728 67108864 Ns252p1081 Ns252p398 Ns252p1082 Ns252p1083 Ns252p401 Ns252p1082 24684150 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 186003252) qz369 0 3 Ns252p1081 Ns252p398 Ns252p1082 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 186003252) qz370 0 3 Ns252p1083 Ns252p401 Ns252p1082 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1085 := nat_lit 5570435053214525183557452501620588445644716522905504021860581761018626864570814901647861301916708640915456 

noncomputable def Ns252p1086 := nat_lit 1055799610206144995241126577896173089265936032307363476878107520335124952035464565816003363556294656 

noncomputable def Ns252p1087 := nat_lit 27834324091296291754120871669114226049533556820010238141501656802019555327540181231684078495108350519279616 

noncomputable def Ns252p1088 := BSN.sin_dyadic_bound_f 178634412 134217728 4 3 134217728 67108864 Ns252p1085 Ns252p137 Ns252p1086 Ns252p1087 Ns252p140 Ns252p1086 130375042 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 178634412) qz367 0 3 Ns252p1085 Ns252p137 Ns252p1086 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 178634412) qz368 0 3 Ns252p1087 Ns252p140 Ns252p1086 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1089 := Ns252p1031 78573 BSN.abs_quadSignPos (BSN.cos_quad_nat0 16 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 24684150 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 71 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 130375042 134217728) qz173 rfl rfl (Ns252p1080 rfl rfl) (Ns252p1064 rfl) RS253to264.d27 RS253to264.d29 RS253to264.d31 RS253to264.d33 RS253to264.d17 (Ns252p1084 rfl rfl) (Ns252p1088 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p1090 := nat_lit 86964774334964586187674108182325091035497258051568912271293863187105 

noncomputable def Ns252p1091 := nat_lit 7851735954319528603898271246201060263549446747040216621166645921 

noncomputable def Ns252p1092 := nat_lit 227752172828600256016644924228833770043018500554613847978859181396641 

noncomputable def Ns252p1093 := BSN.sin_dyadic_bound_f 97022109 134217728 3 2 134217728 67108864 Ns252p1090 Ns252p116 Ns252p1091 Ns252p1092 Ns252p119 Ns252p1091 88790451 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 97022109) qz367 0 2 Ns252p1090 Ns252p116 Ns252p1091 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 97022109) qz368 0 2 Ns252p1092 Ns252p119 Ns252p1091 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1094 := nat_lit 85092619047500105869586270871993173121901595637691226113588592640000 

noncomputable def Ns252p1095 := nat_lit 7517343708640188994967394420542982465558202308488075673600000000 

noncomputable def Ns252p1096 := nat_lit 222849450377448193161972190788063145728607561009263278174974771200000 

noncomputable def Ns252p1097 := BSN.sin_dyadic_bound_f 96495720 134217728 3 2 134217728 67108864 Ns252p1094 Ns252p116 Ns252p1095 Ns252p1096 Ns252p119 Ns252p1095 88395025 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 96495720) qz367 0 2 Ns252p1094 Ns252p116 Ns252p1095 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 96495720) qz368 0 2 Ns252p1096 Ns252p119 Ns252p1095 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1098 := Ns252p1029 96026 BSN.abs_quadSignPos qz650 (BSN.sfrac_eq_quadSignPos_mul Bool.false 88790451 134217728) BSN.abs_quadSignNeg qz371 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 88395025 134217728) qz173 rfl rfl (Ns252p1089 rfl) (Ns252p1064 rfl) RS253to264.d35 RS253to264.d37 RS253to264.d39 RS253to264.d41 RS253to264.d17 (Ns252p1093 rfl rfl) (Ns252p1097 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p1099 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) 47873060 134217728 96026 134217728 47873060 134217728 96026 134217728 12850826691215360 11968265 16777216 48013 33554432 (Ns252p1098 rfl) 

noncomputable def Ns252p1100 := @Enclosure.Real.IsNear.mulLit_tf qz677 (Zeta.RiemannSiegel.correction qz172) 682511 2097152 1 8388608 1709501784031 4398046511104 2141307395677 74217034874880000 1166753772120781841 9223372036854775808 

noncomputable abbrev qz681 := (@HPow.hPow Real Real Real qz7 qz171 qz9)

noncomputable def Ns252p1101 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz681 1 1 0 1 682511 2097152 1 8388608 682511 2097152 1 8388608 

noncomputable def Ns252p1102 := @Enclosure.Real.IsNear.sqrt_image qz171 747775058319 8388608000 280047 8388608000 79200943 79200974 8388608 (@Enclosure.Real.IsNear.of_eq qz171 (@HMul.hMul Real Real Real qz5 qz170 qz3) Bool.false 747775058319 8388608000 280047 8388608000 (BSN.t_div_two_pi_mk qz170 560094 1000 qz173) (@Enclosure.Real.IsNear.mulLit_ff qz170 qz3 560094 1000 0 1 2670177 16777216 1 16777216 747775058319 8388608000 280047 8388608000 (Enclosure.Real.IsNear.const Bool.false 560094 1000) RS253to264.d44 rfl)) 

noncomputable abbrev qz775 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 560094 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz682 := qz775

noncomputable abbrev qz491 := qz682

noncomputable abbrev qz179 := qz491

noncomputable def Ns252p1103 := @Enclosure.Real.IsNear.sqrt_image qz179 158401917 16777216 31 16777216 25775679 25775685 8388608 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 158401917 16777216 31 16777216 158401917 16777216 31 16777216 (Ns252p1102 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns252p1104 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz179) 12887841 4194304 3 8388608 2730043 2730045 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz179) Bool.false 51551364 16777216 6 16777216 12887841 4194304 3 8388608 (Ns252p1103 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns252p1105 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 5460088 16777216 2 16777216 682511 2097152 1 8388608 (Ns252p1104 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz492 := (@HMul.hMul Real Real Real qz584 qz582 qz676)

noncomputable abbrev qz180 := (Real.cos qz492)

noncomputable abbrev qz683 := (@HMul.hMul Real Real Real qz735 qz774 qz774)

noncomputable abbrev qz493 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz683 qz676) qz599)

noncomputable abbrev qz181 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz493))

noncomputable def Ns252p1106 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz172) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz180) qz181) Bool.false 1709501784031 

noncomputable def Ns252p1107 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz180) qz181 2247313 2097152 29 

noncomputable abbrev qz182 := (@Neg.neg Real Real.instNeg (Real.cos qz492))

noncomputable def Ns252p1108 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz180) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz182)) Bool.true 2247313 2097152 29 2097152 (BSN.inv_eq_neg_inv_neg qz180) 

noncomputable def Ns252p1109 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz182) Bool.false 17978504 16777216 232 16777216 2247313 2097152 

noncomputable def Ns252p1110 := @Enclosure.Real.IsNear.recentre' qz180 Bool.true 15656196 16777216 162954304 13589544960000 3914049 4194304 2546161 212336640000 

noncomputable abbrev qz183 := qz492

noncomputable def Ns252p1111 := @Enclosure.Real.IsNear.cos_image qz183 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46539383) qz410) Bool.false 46539383 16777216 49 4194304 Bool.true 15656196 16777216 1 

noncomputable def Ns252p1112 := nat_lit 836568337743990822704947993 

noncomputable def Ns252p1113 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz172 884279719003555 140737488355328 1 500000000000000 7406973 16777216 31 16777216 6549836003106918789015 2361183241434822606848 Ns252p1112 

noncomputable def Ns252p1114 := @Enclosure.Real.IsNear.subLit_ff_p qz179 qz1 158401917 16777216 31 16777216 9 1 0 1 7406973 7406973 16777216 31 

noncomputable def Ns252p1115 := @Ns252p1114 16777216 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 158401917 16777216 31 16777216 158401917 16777216 31 16777216 (Ns252p1102 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns252p1116 := @Enclosure.Real.IsNear.recentre' qz183 Bool.false 6549836003106918789015 2361183241434822606848 Ns252p1112 Ns252p168 46539383 16777216 49 4194304 (@Ns252p1113 Ns252p168 RS253to264.d43 (Ns252p1115 rfl rfl) rfl) 

noncomputable def Ns252p1117 := nat_lit 2909079460342951047069696 

noncomputable def Ns252p1118 := nat_lit 12319275498849950861088632419061446939950580560179235849074344549528222363221233402430625 

noncomputable def Ns252p1119 := nat_lit 8531124255653914527723723863126048004097357361499149901442365885767859859843875390625 

noncomputable def Ns252p1120 := nat_lit 32250956867240717345996770306525395050721077174265095266782852846854101082949197398590625 

noncomputable def Ns252p1121 := BSN.sin_dyadic_bound_f 41340505565 34359738368 3 2 16777216 6486329 Ns252p1118 Ns252p288 Ns252p1119 Ns252p1120 Ns252p291 Ns252p1119 15656196 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 41340505565) qz363 0 2 Ns252p1118 Ns252p288 Ns252p1119 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 41340505565) qz364 0 2 Ns252p1120 Ns252p291 Ns252p1119 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1122 := @Ns252p1111 3240000 (Ns252p1116 rfl) (Enclosure.sfrac_false_div 46539383 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46539383) qz410) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns252p1117) qz411) 226375608064910080 72057594037927936 Bool.false 15656196 16777216 0 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 46539383 16777216 226375608064910080 72057594037927936 0 Ns252p1117 Ns252p93 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 15656196 16777216 Ns252p1117 Ns252p93 41340505565 34359738368 6486329 6480000 (Ns252p1121 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p1123 := @Enclosure.Real.IsNear.inv_image qz182 3914049 4194304 2546161 212336640000 8989136 8989368 8388608 (@Enclosure.Real.IsNear.neg qz180 Bool.true 3914049 4194304 2546161 212336640000 (Ns252p1110 (Ns252p1122 rfl rfl) rfl)) 

noncomputable def Ns252p1124 := Ns252p1108 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz182) Bool.false 2247313 2097152 29 2097152 (@Ns252p1109 29 2097152 (Ns252p1123 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p1125 := @Enclosure.Real.IsNear.recentre' qz181 Bool.true 3042748 8388608 

noncomputable abbrev qz184 := (@HMul.hMul Real Real Real qz346 qz343 qz493)

noncomputable def Ns252p1126 := @Enclosure.Real.IsNear.cos_image qz184 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8145277)) qz377) Bool.true 8145277 4194304 

noncomputable def Ns252p1127 := nat_lit 76929968291275026254828179525 

noncomputable def Ns252p1128 := nat_lit 26428191814096897263535251218628721 

noncomputable def Ns252p1129 := @Enclosure.Real.IsNear.recentre' qz184 Bool.true Ns252p1127 Ns252p183 Ns252p1128 

noncomputable abbrev qz185 := qz493

noncomputable def Ns252p1130 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz185 884279719003555 140737488355328 1 500000000000000 86997322948855 

noncomputable abbrev qz494 := (@HSub.hSub Real Real Real qz588 qz683 qz676)

noncomputable abbrev qz186 := qz494

noncomputable def Ns252p1131 := @Enclosure.Real.IsNear.subLit_tf qz186 qz31 69405136904439 281474976710656 979326983 281474976710656 1 16 

noncomputable abbrev qz495 := qz683

noncomputable abbrev qz187 := qz495

noncomputable def Ns252p1132 := @Enclosure.Real.IsNear.subLit_ff_n qz187 qz172 54863249022729 281474976710656 459233287 281474976710656 7406973 16777216 31 16777216 

noncomputable def Ns252p1133 := @Enclosure.Real.IsNear.mulLit_ff qz172 qz172 7406973 16777216 31 16777216 7406973 16777216 31 16777216 54863249022729 281474976710656 

noncomputable def Ns252p1134 := nat_lit 8485823334354760036906419074516459579952722403086649357068972720160316603145980355401201 

noncomputable def Ns252p1135 := nat_lit 85284537313095216307270476260688814723187546356234864968676905744725140478679963121 

noncomputable def Ns252p1136 := nat_lit 51192117154125907793675724765325085634428548380672987933335955774018806313006705072002545 

noncomputable def Ns252p1137 := BSN.cos_dyadic_bound_t 8145277 4194304 4 3 8388608 3240000 Ns252p1134 Ns252p192 Ns252p1135 Ns252p1136 Ns252p195 Ns252p1135 3042748 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 8145277) (BSN.cosEvenQ 4194304) 0 3 Ns252p1134 Ns252p192 Ns252p1135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 8145277) (BSN.cosOddQ 4194304) 0 3 Ns252p1136 Ns252p195 Ns252p1135 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1138 := @Ns252p1125 75568576 3397386240000 760687 2097152 1180759 53084160000 (@Ns252p1126 23 1048576 Bool.true 3042748 8388608 1 3240000 (@Ns252p1129 Ns252p186 8145277 4194304 23 1048576 (@Ns252p1130 281474976710656 979326983 281474976710656 Ns252p1127 Ns252p183 Ns252p1128 Ns252p186 RS253to264.d43 (@Ns252p1131 0 1 1391957167181680 86997322948855 281474976710656 979326983 281474976710656 (@Ns252p1132 1164424973355344461824 69405136904439 281474976710656 979326983 281474976710656 (@Ns252p1133 459233287 281474976710656 (Ns252p1115 rfl rfl) (Ns252p1115 rfl rfl) rfl) (Ns252p1115 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8145277 4194304) (BSN.cos_neg_of_bound 8145277 4194304 Bool.true 3042748 8388608 1 3240000 (Ns252p1137 rfl rfl)) rfl rfl) 

noncomputable def Ns252p1139 := @Ns252p1100 195823779721217953 20752587082923245568000 (Ns252p1101 qz33 (@Enclosure.Real.IsNear.of_eq qz681 (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 682511 2097152 1 8388608 (BSN.rpow_neg_quarter_mk qz171 (BSN.t_div_two_pi_nonneg qz170 560094 1000 qz173)) Ns252p1105) rfl) (@Ns252p1106 4398046511104 2141307395677 74217034874880000 (BSN.correction_mk qz172 (BSN.cos_two_pi_p_ne_zero_mk qz170 560094 1000 9 qz173 rfl rfl (@BSN.floor_sqrt_eq_dec qz170 560094 1000 9 qz173 rfl rfl rfl))) (@Ns252p1107 2097152 760687 2097152 1180759 53084160000 1709501784031 4398046511104 2141307395677 74217034874880000 Ns252p1124 (Ns252p1138 rfl) rfl)) 

noncomputable def Ns252p1140 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (hardyZApproximantRS₀ qz170) Bool.true 5412869493781482479 9223372036854775808 29890677908451329953 20752587082923245568000 (@Eq.refl Real (hardyZApproximantRS₀ qz170)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) (@HMul.hMul Real Real Real qz5 qz677 (Zeta.RiemannSiegel.correction qz172))) Bool.true 5412869493781482479 9223372036854775808 29890677908451329953 20752587082923245568000 (BSN.hardyZApproximantRS₀_eq qz170 9 (@BSN.floor_sqrt_eq_dec qz170 560094 1000 9 qz173 rfl rfl rfl)) (@Ns252p1027 5412869493781482479 9223372036854775808 29890677908451329953 20752587082923245568000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 9)) Bool.true 11968265 16777216 48013 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz170) qz170 9) (Ns252p1099 (Ns252p1098 rfl) rfl rfl)) (Ns252p1139 rfl) rfl rfl)) 

theorem RS253to264.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz170) Bool.true 5412869493781482479 9223372036854775808 29890677908451329953 20752587082923245568000 := Ns252p1140 

noncomputable def Ns252p1141 := nat_lit 14941862699704736808960000 

noncomputable def Ns252p1142 := nat_lit 123789331132494346976306921472 

noncomputable abbrev qz776 := (Enclosure.sfrac Bool.false 561493 1000)

noncomputable abbrev qz684 := qz776

noncomputable abbrev qz496 := qz684

noncomputable abbrev qz188 := qz496

noncomputable abbrev qz777 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 561493 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz685 := qz777

noncomputable abbrev qz497 := qz685

noncomputable abbrev qz189 := qz497

noncomputable abbrev qz778 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 561493 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz686 := qz778

noncomputable abbrev qz498 := qz686

noncomputable abbrev qz190 := qz498

noncomputable abbrev qz687 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz189 qz9))

noncomputable def Ns252p1143 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (@HMul.hMul Real Real Real qz5 qz687 (Zeta.RiemannSiegel.correction qz190)) 410978271 67108864 96267 67108864 37103226372778083489 295147905179352825856 138512587027753423931 Ns252p1141 Ns252p1142 

noncomputable def Ns252p1144 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 561493 1000 119 161 134217728 67108864 2251799813685248 Bool.false 131557114229 1861 

noncomputable def Ns252p1145 := Ns252p1144 279097919 42 47453128 8 294906479 42 44739240 8 Bool.false 415750274 78770 Bool.true 65796622 Bool.true 87386408 7074237752028440 1 Bool.false 63192748 Bool.false Bool.false 81342037 Bool.true Bool.false 410978271 

noncomputable def Ns252p1146 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 561493 1000 16 71 134217728 67108864 2251799813685248 Bool.false 131557114229 1861 

noncomputable def Ns252p1147 := Ns252p1146 240485871 42 54794152 8 261175631 42 50729528 8 Bool.false 335587862 58746 Bool.true 100759510 Bool.true 122335644 7074237752028440 1 Bool.false 98140009 Bool.false Bool.false 106086505 Bool.false Bool.false 415750274 

noncomputable def Ns252p1148 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 561493 1000 128 48 134217728 67108864 2251799813685248 Bool.false 131557114229 1861 

noncomputable def Ns252p1149 := Ns252p1148 186065264 42 67108856 8 216015088 42 60023992 8 Bool.false 257425463 34625 Bool.false 96695540 Bool.false 146376144 7074237752028440 1 Bool.false 100866891 Bool.false Bool.false 62003840 Bool.false Bool.false 335587862 

noncomputable def Ns252p1150 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 561493 1000 376 231 134217728 67108864 2251799813685248 Bool.false 131557114229 1861 

noncomputable def Ns252p1151 := Ns252p1150 93032624 42 94906264 8 147453232 42 77490640 16 Bool.false 134217720 1914 Bool.false 48350567 Bool.false 61723668 7074237752028440 1 Bool.false 125602603 Bool.false Bool.false 59570932 Bool.false Bool.false 257425463 

noncomputable def Ns252p1152 := nat_lit 62250644943525479681227517726423491158094205973654317147 

noncomputable def Ns252p1153 := nat_lit 63509603260830110400650083853393297425393355902156800 

noncomputable def Ns252p1154 := nat_lit 26789452732288542496546907532640000 

noncomputable def Ns252p1155 := nat_lit 90252574495977612515176366306083789120 

noncomputable abbrev qz688 := (@Eq.refl Real qz776)

noncomputable abbrev qz499 := qz688

noncomputable abbrev qz191 := qz499

noncomputable def Ns252p1156 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz188 561493 1000 1261098556196 16000000 1122986 4000 2000 Ns252p1154 Ns252p1155 qz191 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns252p1157 := nat_lit 19920206381928153497992805672455517170590145911569381487040 

noncomputable abbrev qz689 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1122986))))

noncomputable abbrev qz500 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 561493 4000) (Real.log (Enclosure.sfrac Bool.false 1261098556196 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz689))

noncomputable abbrev qz690 := (Enclosure.sfrac Bool.false 561493 2000)

noncomputable abbrev qz192 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz500 qz690) (@HMul.hMul Real Real Real qz346 qz690 (Real.log Real.pi)))

noncomputable def Ns252p1158 := @Enclosure.Real.IsNear.addLit_ft_p qz192 (Enclosure.sfrac Bool.true Ns252p1154 Ns252p1155) 220716279016111911867 225179981368524800 255461899847325529 18432000000000000000000 Ns252p1154 Ns252p1155 0 1 Ns252p1157 

noncomputable def Ns252p1159 := nat_lit 74060093755391540511312445440000 

noncomputable abbrev qz193 := (@HSub.hSub Real Real Real qz350 qz500 qz690)

noncomputable def Ns252p1160 := @Enclosure.Real.IsNear.subLit_ff_p qz193 (@HMul.hMul Real Real Real qz5 qz690 (Real.log Real.pi)) 1465421877604124033703 1125899906842624000 49435176464873 9000000000000000000 21567373426173 67108864000 561493 67108864000 Ns252p1159 220716279016111911867 225179981368524800 

noncomputable def Ns252p1161 := nat_lit 2930843755208248067406000 

noncomputable abbrev qz194 := qz500

noncomputable def Ns252p1162 := @Enclosure.Real.IsNear.subLit_ff_p qz194 qz690 1781514335800516772519 1125899906842624000 49435176464873 9000000000000000000 561493 2000 0 1 Ns252p1161 1465421877604124033703 1125899906842624000 49435176464873 9000000000000000000 

noncomputable def Ns252p1163 := nat_lit 4011613649433202009240280256282099712 

noncomputable def Ns252p1164 := nat_lit 27261047633572849344577536 

noncomputable def Ns252p1165 := nat_lit 15940210040891989206546617539061425743952658090742916069124083063030112686080 

noncomputable def Ns252p1166 := nat_lit 45216313577909139289423552020802351415088272824323995991329379252950102016 

noncomputable def Ns252p1167 := nat_lit 1382042646499772036570754059198834385467517595726936735148909764669440 

noncomputable def Ns252p1168 := BSN.log_dyadic_bound 212522556196 2309674556196 4 3 Ns252p1165 67108864 25920000 Ns252p1166 Ns252p1167 12384951 2522197112392 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 212522556196) (BSN.artanhQ 2309674556196) 0 3 Ns252p1166 Ns252p1165 Ns252p1167 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz501 := (Real.log (Enclosure.sfrac Bool.false 1261098556196 16000000))

noncomputable def Ns252p1169 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 561493 4000) qz501 561493 4000 0 1 3173603633601783 281474976710656 195312581 5062500000000000 1781956225041965942019 1125899906842624000 109666647043433 20250000000000000000 (Enclosure.Real.IsNear.const Bool.false 561493 4000) (BSN.isNear_log_sfrac 1261098556196 16000000 3173603633601783 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1261098556196) qz353)) Bool.false Ns252p1164 Ns252p93 1000000414720000 25920000000000000000000 3173603633601783 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1261098556196 16000000 16 2522197112392 2097152000000 12384951 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns252p1168 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p1170 := BSN.arctan_dyadic_bound_f 1000 1122986 1 0 8388608 3240000 0 1 1 0 1 1 7469 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1122986) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1122986) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns252p1171 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1122986))) 884279719003555 562949953421312 1 2000000000000000 7469 8388608 1 3240000 7413671251868869722112 883778482898339 562949953421312 50000000081 162000000000000000 qz17 (Ns252p1170 rfl) rfl rfl 

noncomputable abbrev qz502 := (@HMul.hMul Real Real Real qz584 qz589 qz689)

noncomputable abbrev qz195 := qz502

noncomputable abbrev qz503 := qz689

noncomputable abbrev qz196 := qz503

noncomputable def Ns252p1172 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 561493 4000) qz501) qz195 1781956225041965942019 1125899906842624000 109666647043433 20250000000000000000 883778482898339 2251799813685248 50000000081 648000000000000000 Ns252p1163 1781514335800516772519 1125899906842624000 49435176464873 9000000000000000000 (Ns252p1169 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz196 1 4 0 1 883778482898339 562949953421312 50000000081 162000000000000000 883778482898339 2251799813685248 50000000081 648000000000000000 qz361 Ns252p1171 rfl) 

noncomputable def Ns252p1173 := @Ns252p1158 Ns252p1152 Ns252p1153 255461899847325529 18432000000000000000000 (@Ns252p1160 255461899847325529 18432000000000000000000 (Ns252p1162 (Ns252p1172 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 561493 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz690 (Real.log Real.pi) 561493 2000 0 1 38410761 33554432 1 33554432 21567373426173 67108864000 561493 67108864000 (Enclosure.Real.IsNear.const Bool.false 561493 2000) RS253to264.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns252p1154 Ns252p1155) 

noncomputable def Ns252p1174 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz188) Bool.false Ns252p1152 Ns252p1153 255461899847325529 18432000000000000000000 8222319639 8388608 117 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz188) (@HAdd.hAdd Real Real Real qz362 qz192 (Enclosure.sfrac Bool.true Ns252p1154 Ns252p1155)) Bool.false Ns252p1152 Ns252p1153 255461899847325529 18432000000000000000000 Ns252p1156 (Ns252p1173 rfl rfl)) 

noncomputable def Ns252p1175 := nat_lit 1898945656568936281407488 

noncomputable def Ns252p1176 := nat_lit 857082248237658014875764652395346284367366853214626389321426260075909316900307912482571741760729851565406269978847799721388609869140625 

noncomputable def Ns252p1177 := nat_lit 610875599687639151544279670879983440267860681086118863929176191095966610516658219270183419085902295039338511214315891265869140625 

noncomputable def Ns252p1178 := nat_lit 4280086431385749962498367362612683630631229878525472235183523677475739069391732072433131479758128713940819821444890358943377985869140625 

noncomputable def Ns252p1179 := BSN.sin_dyadic_bound_f 53971281675 34359738368 4 3 16777216 6486329 Ns252p1176 Ns252p107 Ns252p1177 Ns252p1178 Ns252p110 Ns252p1177 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53971281675) qz363 0 3 Ns252p1176 Ns252p107 Ns252p1177 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53971281675) qz364 0 3 Ns252p1178 Ns252p110 Ns252p1177 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1180 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz188) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8222319639) qz365) Bool.false 8222319639 8388608 117 8388608 Bool.false 16777215 16777216 1 3240000 (Ns252p1174 rfl) (Enclosure.sfrac_false_div 8222319639 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8222319639) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns252p1175) qz366) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 155 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q3 8222319639 8388608 226375608064910080 72057594037927936 155 Ns252p1175 Ns252p105 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns252p1175 Ns252p105 53971281675 34359738368 6486329 6480000 (Ns252p1179 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p1181 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz188) Bool.false Ns252p1152 Ns252p1153 255461899847325529 18432000000000000000000 131557114229 134217728 1861 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz188) (@HAdd.hAdd Real Real Real qz362 qz192 (Enclosure.sfrac Bool.true Ns252p1154 Ns252p1155)) Bool.false Ns252p1152 Ns252p1153 255461899847325529 18432000000000000000000 Ns252p1156 (Ns252p1173 rfl rfl)) 

noncomputable def Ns252p1182 := Ns252p1151 34625 BSN.abs_quadSignPos (BSN.cos_quad_nat0 376 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 125602603 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 231 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 59570932 134217728) qz191 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 1) Bool.false 16777215 16777216 6054197 424673280000 134217720 134217728 1914 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz188)) Bool.false 16777215 16777216 6054197 424673280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz188) qz188) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz188)) Bool.false 16777215 16777216 387468608 27179089920000 16777215 16777216 6054197 424673280000 (Ns252p1180 rfl rfl) rfl)) rfl) (Ns252p1181 rfl) RS253to264.d7 

noncomputable def Ns252p1183 := nat_lit 2979610200424955993631030879913314489693420717838197100530179728321 

noncomputable def Ns252p1184 := nat_lit 29868442093514482951007839040731676676450453006994814418248641 

noncomputable def Ns252p1185 := nat_lit 8938770864390680951927190624061862005726909252608577311961702687681 

noncomputable def Ns252p1186 := BSN.cos_dyadic_bound_f 48350567 134217728 3 2 134217728 67108864 Ns252p1183 Ns252p144 Ns252p1184 Ns252p1185 Ns252p147 Ns252p1184 125602603 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 48350567) qz369 0 2 Ns252p1183 Ns252p144 Ns252p1184 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 48350567) qz370 0 2 Ns252p1185 Ns252p147 Ns252p1184 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1187 := nat_lit 14514661313920284047421611602176 

noncomputable def Ns252p1188 := BSN.sin_dyadic_bound_f 61723668 134217728 2 1 134217728 67108864 Ns252p1187 Ns252p238 Ns252p1187 Ns252p1187 Ns252p239 Ns252p1187 59570932 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 61723668) qz367 0 1 Ns252p1187 Ns252p238 Ns252p1187 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 61723668) qz368 0 1 Ns252p1187 Ns252p239 Ns252p1187 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1189 := nat_lit 47669897770660657463187804578591426472464598360903772611031244800000 

noncomputable def Ns252p1190 := nat_lit 7642783276469768083748938018074810354725926747479564313600000000 

noncomputable def Ns252p1191 := nat_lit 142994407745429032853395915859738129796684343229216358704466534400000 

noncomputable def Ns252p1192 := BSN.cos_dyadic_bound_f 96695540 134217728 3 2 134217728 67108864 Ns252p1189 Ns252p144 Ns252p1190 Ns252p1191 Ns252p147 Ns252p1190 100866891 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 96695540) qz369 0 2 Ns252p1189 Ns252p144 Ns252p1190 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 96695540) qz370 0 2 Ns252p1191 Ns252p147 Ns252p1190 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1193 := nat_lit 965720782768338687432436253348582007233396706584245490312784413582576851739208515837405662185117676732416 

noncomputable def Ns252p1194 := nat_lit 96748363525163438869297208360490908553011437631507966759007157566053095088583980152175091605569536 

noncomputable def Ns252p1195 := nat_lit 5855419518497102139689332821094340455877904980329118726048997998141439609437250124439450203865627177779200 

noncomputable def Ns252p1196 := BSN.cos_dyadic_bound_f 146376144 134217728 4 3 134217728 67108864 Ns252p1193 Ns252p398 Ns252p1194 Ns252p1195 Ns252p401 Ns252p1194 62003840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 146376144) qz369 0 3 Ns252p1193 Ns252p398 Ns252p1194 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 146376144) qz370 0 3 Ns252p1195 Ns252p401 Ns252p1194 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1197 := Ns252p1149 58746 BSN.abs_quadSignPos (BSN.cos_quad_nat0 128 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 100866891 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 48 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 62003840 134217728) qz191 rfl rfl (Ns252p1182 RS253to264.d9 RS253to264.d11 RS253to264.d13 RS253to264.d17 (Ns252p1186 rfl rfl) (Ns252p1188 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns252p1181 rfl) RS253to264.d19 RS253to264.d21 RS253to264.d23 RS253to264.d25 RS253to264.d17 (Ns252p1192 rfl rfl) (Ns252p1196 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns252p1198 := nat_lit 56205019121068757370158843863922731871277530639228503752296240800000 

noncomputable def Ns252p1199 := nat_lit 10624007647251457728590275892066660980705291743604637760100000000 

noncomputable def Ns252p1200 := nat_lit 168593809347911769195019351039984062291871181334198301981368522400000 

noncomputable def Ns252p1201 := BSN.cos_dyadic_bound_f 100759510 134217728 3 2 134217728 67108864 Ns252p1198 Ns252p144 Ns252p1199 Ns252p1200 Ns252p147 Ns252p1199 98140009 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 100759510) qz369 0 2 Ns252p1198 Ns252p144 Ns252p1199 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 100759510) qz370 0 2 Ns252p1200 Ns252p147 Ns252p1199 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1202 := nat_lit 219853042696728909855573034726823613979204582819740742973046709616640 

noncomputable def Ns252p1203 := nat_lit 50167689550352581043567658804513956006411588723004459071182012416 

noncomputable def Ns252p1204 := nat_lit 575724364136922764490525505217902156873906383860436129138530897166336 

noncomputable def Ns252p1205 := BSN.sin_dyadic_bound_f 122335644 134217728 3 2 134217728 67108864 Ns252p1202 Ns252p116 Ns252p1203 Ns252p1204 Ns252p119 Ns252p1203 106086505 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 122335644) qz367 0 2 Ns252p1202 Ns252p116 Ns252p1203 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 122335644) qz368 0 2 Ns252p1204 Ns252p119 Ns252p1203 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1206 := Ns252p1147 78770 BSN.abs_quadSignPos (BSN.cos_quad_nat0 16 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 98140009 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 71 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 106086505 134217728) qz191 rfl rfl (Ns252p1197 rfl rfl) (Ns252p1181 rfl) RS253to264.d27 RS253to264.d29 RS253to264.d31 RS253to264.d33 RS253to264.d17 (Ns252p1201 rfl rfl) (Ns252p1205 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p1207 := nat_lit 18392637130478121266018279918276802512838410485892035853626731577600 

noncomputable def Ns252p1208 := nat_lit 351260067124885765912255932867677843740284791729457127463239936 

noncomputable def Ns252p1209 := nat_lit 48170623777810210643569732323976506531401209859102055733673166029056 

noncomputable def Ns252p1210 := BSN.sin_dyadic_bound_f 65796622 134217728 3 2 134217728 67108864 Ns252p1207 Ns252p116 Ns252p1208 Ns252p1209 Ns252p119 Ns252p1208 63192748 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 65796622) qz367 0 2 Ns252p1207 Ns252p116 Ns252p1208 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 65796622) qz368 0 2 Ns252p1209 Ns252p119 Ns252p1208 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1211 := nat_lit 57229859189493606078267085287349319818816944710697791528271861514240 

noncomputable def Ns252p1212 := nat_lit 3400565191627417131966380912560384182650857147132999004235759616 

noncomputable def Ns252p1213 := nat_lit 149882220771696809624866801612056454141558182378351238670895636545536 

noncomputable def Ns252p1214 := BSN.sin_dyadic_bound_f 87386408 134217728 3 2 134217728 67108864 Ns252p1211 Ns252p116 Ns252p1212 Ns252p1213 Ns252p119 Ns252p1212 81342037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 87386408) qz367 0 2 Ns252p1211 Ns252p116 Ns252p1212 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 87386408) qz368 0 2 Ns252p1213 Ns252p119 Ns252p1212 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1215 := Ns252p1145 96267 BSN.abs_quadSignPos qz650 (BSN.sfrac_eq_quadSignPos_mul Bool.false 63192748 134217728) BSN.abs_quadSignNeg qz371 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 81342037 134217728) qz191 rfl rfl (Ns252p1206 rfl) (Ns252p1181 rfl) RS253to264.d35 RS253to264.d37 RS253to264.d39 RS253to264.d41 RS253to264.d17 (Ns252p1210 rfl rfl) (Ns252p1214 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p1216 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) 410978271 134217728 96267 134217728 410978271 134217728 96267 134217728 110321139581976576 410978271 67108864 96267 67108864 (Ns252p1215 rfl) 

noncomputable def Ns252p1217 := @Enclosure.Real.IsNear.mulLit_tf qz687 (Zeta.RiemannSiegel.correction qz190) 1364171 4194304 1 8388608 27198369099459 70368744177664 101031379346309 3562417673994240000 37103226372778083489 295147905179352825856 

noncomputable abbrev qz691 := (@HPow.hPow Real Real Real qz7 qz189 qz9)

noncomputable def Ns252p1218 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz691 1 1 0 1 1364171 4194304 1 8388608 1364171 4194304 1 8388608 

noncomputable def Ns252p1219 := @Enclosure.Real.IsNear.sqrt_image qz189 1499285694261 16777216000 561493 16777216000 79299795 79299826 8388608 (@Enclosure.Real.IsNear.of_eq qz189 (@HMul.hMul Real Real Real qz5 qz188 qz3) Bool.false 1499285694261 16777216000 561493 16777216000 (BSN.t_div_two_pi_mk qz188 561493 1000 qz191) (@Enclosure.Real.IsNear.mulLit_ff qz188 qz3 561493 1000 0 1 2670177 16777216 1 16777216 1499285694261 16777216000 561493 16777216000 (Enclosure.Real.IsNear.const Bool.false 561493 1000) RS253to264.d44 rfl)) 

noncomputable abbrev qz779 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 561493 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz692 := qz779

noncomputable abbrev qz504 := qz692

noncomputable abbrev qz197 := qz504

noncomputable def Ns252p1220 := @Enclosure.Real.IsNear.sqrt_image qz197 158599621 16777216 31 16777216 25791760 25791766 8388608 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 158599621 16777216 31 16777216 158599621 16777216 31 16777216 (Ns252p1219 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns252p1221 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz197) 25791763 8388608 3 8388608 2728341 2728343 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz197) Bool.false 51583526 16777216 6 16777216 25791763 8388608 3 8388608 (Ns252p1220 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns252p1222 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz197)) Bool.false 5456684 16777216 2 16777216 1364171 4194304 1 8388608 (Ns252p1221 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz505 := (@HMul.hMul Real Real Real qz584 qz582 qz686)

noncomputable abbrev qz198 := (Real.cos qz505)

noncomputable abbrev qz693 := (@HMul.hMul Real Real Real qz735 qz778 qz778)

noncomputable abbrev qz506 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz693 qz686) qz599)

noncomputable abbrev qz199 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz506))

noncomputable def Ns252p1223 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz190) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz198) qz199) Bool.false 27198369099459 

noncomputable def Ns252p1224 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz198) qz199 17527173 16777216 221 

noncomputable abbrev qz200 := (@Neg.neg Real Real.instNeg (Real.cos qz505))

noncomputable def Ns252p1225 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz198) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz200)) Bool.true 17527173 16777216 221 16777216 (BSN.inv_eq_neg_inv_neg qz198) 

noncomputable def Ns252p1226 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz200) Bool.false 17527173 16777216 221 16777216 17527173 16777216 

noncomputable def Ns252p1227 := @Enclosure.Real.IsNear.recentre' qz198 Bool.true 16059348 16777216 162954304 13589544960000 4014837 4194304 2546161 212336640000 

noncomputable abbrev qz201 := qz505

noncomputable def Ns252p1228 := @Enclosure.Real.IsNear.cos_image qz201 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23890797) qz365) Bool.false 23890797 8388608 49 4194304 Bool.true 16059348 16777216 1 

noncomputable def Ns252p1229 := nat_lit 836568337745689087133524761 

noncomputable def Ns252p1230 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz190 884279719003555 140737488355328 1 500000000000000 7604677 16777216 31 16777216 6724661640672797626735 2361183241434822606848 Ns252p1229 

noncomputable def Ns252p1231 := @Enclosure.Real.IsNear.subLit_ff_p qz197 qz1 158599621 16777216 31 16777216 9 1 0 1 7604677 7604677 16777216 31 

noncomputable def Ns252p1232 := @Ns252p1231 16777216 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 158599621 16777216 31 16777216 158599621 16777216 31 16777216 (Ns252p1219 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns252p1233 := @Enclosure.Real.IsNear.recentre' qz201 Bool.false 6724661640672797626735 2361183241434822606848 Ns252p1229 Ns252p168 23890797 8388608 49 4194304 (@Ns252p1230 Ns252p168 RS253to264.d43 (Ns252p1232 rfl rfl) rfl) 

noncomputable def Ns252p1234 := nat_lit 1544050466118924022841344 

noncomputable def Ns252p1235 := nat_lit 15646237545769584459539998074231627851868417606287343392087895440692277194685974108734625 

noncomputable def Ns252p1236 := nat_lit 13756041819256636103905550053911172956779935777762562634412681733396048680343022372001 

noncomputable def Ns252p1237 := nat_lit 40955969504546305697484147875281264379630116691874283782631629431387608573933186343797921 

noncomputable def Ns252p1238 := BSN.sin_dyadic_bound_f 43884553693 34359738368 3 2 16777216 6486329 Ns252p1235 Ns252p288 Ns252p1236 Ns252p1237 Ns252p291 Ns252p1236 16059348 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 43884553693) qz363 0 2 Ns252p1235 Ns252p288 Ns252p1236 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 43884553693) qz364 0 2 Ns252p1237 Ns252p291 Ns252p1236 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1239 := @Ns252p1228 3240000 (Ns252p1233 rfl) (Enclosure.sfrac_false_div 23890797 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23890797) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns252p1234) qz366) 226375608064910080 72057594037927936 Bool.false 16059348 16777216 0 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 23890797 8388608 226375608064910080 72057594037927936 0 Ns252p1234 Ns252p105 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16059348 16777216 Ns252p1234 Ns252p105 43884553693 34359738368 6486329 6480000 (Ns252p1238 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p1240 := @Enclosure.Real.IsNear.inv_image qz200 4014837 4194304 2546161 212336640000 8763476 8763697 8388608 (@Enclosure.Real.IsNear.neg qz198 Bool.true 4014837 4194304 2546161 212336640000 (Ns252p1227 (Ns252p1239 rfl rfl) rfl)) 

noncomputable def Ns252p1241 := Ns252p1225 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz200) Bool.false 17527173 16777216 221 16777216 (@Ns252p1226 221 16777216 (Ns252p1240 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p1242 := @Enclosure.Real.IsNear.recentre' qz199 Bool.true 3103566 8388608 

noncomputable abbrev qz202 := (@HMul.hMul Real Real Real qz346 qz343 qz506)

noncomputable def Ns252p1243 := @Enclosure.Real.IsNear.cos_image qz202 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16355917)) qz365) Bool.true 16355917 8388608 

noncomputable def Ns252p1244 := nat_lit 77238634492889664690826129045 

noncomputable def Ns252p1245 := nat_lit 1070359105094616543486192670664361 

noncomputable def Ns252p1246 := @Enclosure.Real.IsNear.recentre' qz202 Bool.true Ns252p1244 Ns252p183 Ns252p1245 

noncomputable def Ns252p1247 := nat_lit 48357032784585166988247040000000000000 

noncomputable abbrev qz203 := qz506

noncomputable def Ns252p1248 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz203 884279719003555 140737488355328 1 500000000000000 87346382409319 

noncomputable abbrev qz507 := (@HSub.hSub Real Real Real qz588 qz693 qz686)

noncomputable abbrev qz204 := qz507

noncomputable def Ns252p1249 := @Enclosure.Real.IsNear.subLit_tf qz204 qz31 69754196364903 281474976710656 991584631 281474976710656 1 16 

noncomputable abbrev qz508 := qz693

noncomputable abbrev qz205 := qz508

noncomputable def Ns252p1250 := @Enclosure.Real.IsNear.subLit_ff_n qz205 qz190 57831112274329 281474976710656 471490935 281474976710656 7604677 16777216 31 16777216 

noncomputable def Ns252p1251 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz190 7604677 16777216 31 16777216 7604677 16777216 31 16777216 57831112274329 281474976710656 

noncomputable def Ns252p1252 := nat_lit 35323938059349467651070702779449465247987465682727189871557462044930031420353293054933592241 

noncomputable def Ns252p1253 := nat_lit 366520926843865956645105988278734664808420498595105241341495644268337899826395951786161 

noncomputable def Ns252p1254 := nat_lit 213078176485421455402862188475188646895509183934894296687759599633561699375499602209143646385 

noncomputable def Ns252p1255 := BSN.cos_dyadic_bound_t 16355917 8388608 4 3 8388608 3240000 Ns252p1252 Ns252p308 Ns252p1253 Ns252p1254 Ns252p311 Ns252p1253 3103566 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16355917) (BSN.cosEvenQ 8388608) 0 3 Ns252p1252 Ns252p308 Ns252p1253 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16355917) (BSN.cosOddQ 8388608) 0 3 Ns252p1254 Ns252p311 Ns252p1253 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1256 := @Ns252p1242 305514304 13589544960000 1551783 4194304 4773661 212336640000 (@Ns252p1243 93 4194304 Bool.true 3103566 8388608 1 3240000 (@Ns252p1246 Ns252p1247 16355917 8388608 93 4194304 (@Ns252p1248 281474976710656 991584631 281474976710656 Ns252p1244 Ns252p183 Ns252p1245 Ns252p1247 RS253to264.d43 (@Ns252p1249 0 1 1397542118549104 87346382409319 281474976710656 991584631 281474976710656 (@Ns252p1250 1170281219320392450048 69754196364903 281474976710656 991584631 281474976710656 (@Ns252p1251 471490935 281474976710656 (Ns252p1232 rfl rfl) (Ns252p1232 rfl rfl) rfl) (Ns252p1232 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16355917 8388608) (BSN.cos_neg_of_bound 16355917 8388608 Bool.true 3103566 8388608 1 3240000 (Ns252p1255 rfl rfl)) rfl rfl) 

noncomputable def Ns252p1257 := @Ns252p1217 138512587027753423931 Ns252p1141 (Ns252p1218 qz33 (@Enclosure.Real.IsNear.of_eq qz691 (@Inv.inv Real Real.instInv (Real.sqrt qz197)) Bool.false 1364171 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz189 (BSN.t_div_two_pi_nonneg qz188 561493 1000 qz191)) Ns252p1222) rfl) (@Ns252p1223 70368744177664 101031379346309 3562417673994240000 (BSN.correction_mk qz190 (BSN.cos_two_pi_p_ne_zero_mk qz188 561493 1000 9 qz191 rfl rfl (@BSN.floor_sqrt_eq_dec qz188 561493 1000 9 qz191 rfl rfl rfl))) (@Ns252p1224 16777216 1551783 4194304 4773661 212336640000 27198369099459 70368744177664 101031379346309 3562417673994240000 Ns252p1241 (Ns252p1256 rfl) rfl)) 

noncomputable def Ns252p1258 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz188) (hardyZApproximantRS₀ qz188) Bool.false 1844604777283882304673 295147905179352825856 21572466475927972303931 Ns252p1141 (@Eq.refl Real (hardyZApproximantRS₀ qz188)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz188) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (@HMul.hMul Real Real Real qz5 qz687 (Zeta.RiemannSiegel.correction qz190))) Bool.false 1844604777283882304673 295147905179352825856 21572466475927972303931 Ns252p1141 (BSN.hardyZApproximantRS₀_eq qz188 9 (@BSN.floor_sqrt_eq_dec qz188 561493 1000 9 qz191 rfl rfl rfl)) (@Ns252p1143 1844604777283882304673 295147905179352825856 21572466475927972303931 Ns252p1141 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 9)) Bool.false 410978271 67108864 96267 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz188) qz188 9) (Ns252p1216 (Ns252p1215 rfl) rfl rfl)) (Ns252p1257 rfl) rfl rfl)) 

theorem RS253to264.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz188) Bool.false 1844604777283882304673 295147905179352825856 21572466475927972303931 Ns252p1141 := Ns252p1258 

noncomputable def Ns252p1259 := nat_lit 59767450798818947235840000 

noncomputable def Ns252p1260 := nat_lit 8622446574464269810940248064 

noncomputable abbrev qz780 := (Enclosure.sfrac Bool.false 562891 1000)

noncomputable abbrev qz694 := qz780

noncomputable abbrev qz509 := qz694

noncomputable abbrev qz206 := qz509

noncomputable abbrev qz781 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 562891 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz695 := qz781

noncomputable abbrev qz510 := qz695

noncomputable abbrev qz207 := qz510

noncomputable abbrev qz782 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 562891 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz696 := qz782

noncomputable abbrev qz511 := qz696

noncomputable abbrev qz208 := qz511

noncomputable abbrev qz697 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz207 qz9))

noncomputable def Ns252p1261 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) (@HMul.hMul Real Real Real qz5 qz697 (Zeta.RiemannSiegel.correction qz208)) 125250191 67108864 48251 33554432 9229575094233272415 73786976294838206464 548379980750877263443 Ns252p1259 Ns252p1260 

noncomputable def Ns252p1262 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 562891 1000 119 161 134217728 67108864 2251799813685248 Bool.false 131978729866 1866 

noncomputable def Ns252p1263 := Ns252p1262 279097919 42 47453128 8 294906479 42 44739240 8 Bool.true 112691029 78962 Bool.true 34359875 Bool.true 78050029 7074237752028440 1 Bool.false 33985798 Bool.false Bool.false 73724869 Bool.true Bool.true 125250191 

noncomputable def Ns252p1264 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 562891 1000 16 71 134217728 67108864 2251799813685248 Bool.false 131978729866 1866 

noncomputable def Ns252p1265 := Ns252p1264 240485871 42 54794152 8 261175631 42 50729528 8 Bool.true 191027801 58888 Bool.true 15343120 Bool.true 65843539 7074237752028440 1 Bool.false 133341707 Bool.false Bool.false 63234136 Bool.false Bool.true 112691029 

noncomputable def Ns252p1266 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 562891 1000 129 49 134217728 67108864 2251799813685248 Bool.false 131978729866 1866 

noncomputable def Ns252p1267 := Ns252p1266 186065264 42 67108856 8 216015088 42 60023992 8 Bool.true 143849180 34707 Bool.false 47363224 Bool.false 55173974 7074237752028440 1 Bool.false 46386328 Bool.true Bool.false 53633119 Bool.true Bool.true 191027801 

noncomputable def Ns252p1268 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 562891 1000 377 232 134217728 67108864 2251799813685248 Bool.false 131978729866 1866 

noncomputable def Ns252p1269 := Ns252p1268 93032624 42 94906264 8 147453232 42 77490640 16 Bool.true 134217720 1914 Bool.false 129077881 Bool.false 66370973 7074237752028440 1 Bool.false 110081128 Bool.true Bool.false 118139119 Bool.false Bool.true 143849180 

noncomputable def Ns252p1270 := nat_lit 316944493739312061269702876887439105472963908836336854433 

noncomputable def Ns252p1271 := nat_lit 322321406600353238668492101492651128179365098029056000 

noncomputable def Ns252p1272 := nat_lit 27124617934962152440084132216480000 

noncomputable def Ns252p1273 := nat_lit 91609253615943441294715541258895862080 

noncomputable abbrev qz783 := (@Eq.refl Real (Enclosure.sfrac Bool.false 562891 1000))

noncomputable abbrev qz698 := qz783

noncomputable abbrev qz512 := qz698

noncomputable abbrev qz209 := qz512

noncomputable def Ns252p1274 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz206 562891 1000 1267386111524 16000000 1125782 4000 2000 Ns252p1272 Ns252p1273 qz209 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns252p1275 := nat_lit 101422237996579859606304920603980513751348450827627793418560 

noncomputable abbrev qz699 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1125782))))

noncomputable abbrev qz513 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 562891 4000) (Real.log (Enclosure.sfrac Bool.false 1267386111524 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz699))

noncomputable abbrev qz700 := (Enclosure.sfrac Bool.false 562891 2000)

noncomputable abbrev qz210 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz513 qz700) (@HMul.hMul Real Real Real qz346 qz700 (Real.log Real.pi)))

noncomputable def Ns252p1276 := @Enclosure.Real.IsNear.addLit_ft_p qz210 (Enclosure.sfrac Bool.true Ns252p1272 Ns252p1273) 1107118162553541341057 1125899906842624000 768283216355098069 55296000000000000000000 Ns252p1272 Ns252p1273 0 1 Ns252p1275 

noncomputable def Ns252p1277 := nat_lit 74297442202735498575371829248000 

noncomputable abbrev qz211 := (@HSub.hSub Real Real Real qz350 qz513 qz700)

noncomputable def Ns252p1278 := @Enclosure.Real.IsNear.subLit_ff_p qz211 (@HMul.hMul Real Real Real qz5 qz700 (Real.log Real.pi)) 1469859552113467699073 1125899906842624000 148669592045603 27000000000000000000 21621071670051 67108864000 562891 67108864000 Ns252p1277 1107118162553541341057 1125899906842624000 

noncomputable abbrev qz212 := qz513

noncomputable def Ns252p1279 := @Enclosure.Real.IsNear.subLit_ff_p qz212 qz700 357347802868948686413 225179981368524800 148669592045603 27000000000000000000 562891 2000 0 1 587943820845387079629200 1469859552113467699073 1125899906842624000 148669592045603 27000000000000000000 

noncomputable def Ns252p1280 := nat_lit 804675715921131382791730390236135424 

noncomputable def Ns252p1281 := nat_lit 27273072532808304720609280 

noncomputable def Ns252p1282 := nat_lit 16202349651926580824869366287894109275733549158116667075875821179283228692480 

noncomputable def Ns252p1283 := nat_lit 48468898752643653924271036488485140739651087191680624462046681943461687296 

noncomputable def Ns252p1284 := nat_lit 1646249226716976014875859453739888675292262174126541393456366998384640 

noncomputable def Ns252p1285 := BSN.log_dyadic_bound 218810111524 2315962111524 4 3 Ns252p1282 67108864 25920000 Ns252p1283 Ns252p1284 12718709 2534772223048 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 218810111524) (BSN.artanhQ 2315962111524) 0 3 Ns252p1283 Ns252p1282 Ns252p1284 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz514 := (Real.log (Enclosure.sfrac Bool.false 1267386111524 16000000))

noncomputable def Ns252p1286 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 562891 4000) qz514 562891 4000 0 1 3175003516116215 281474976710656 195312581 5062500000000000 357436180838034475513 225179981368524800 109939694031671 20250000000000000000 (Enclosure.Real.IsNear.const Bool.false 562891 4000) (BSN.isNear_log_sfrac 1267386111524 16000000 3175003516116215 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1267386111524) qz353)) Bool.false Ns252p1281 Ns252p93 1000000414720000 25920000000000000000000 3175003516116215 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1267386111524 16000000 16 2534772223048 2097152000000 12718709 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns252p1285 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p1287 := BSN.arctan_dyadic_bound_f 1000 1125782 1 0 8388608 3240000 0 1 1 0 1 1 7451 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1125782) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1125782) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns252p1288 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1125782))) 884279719003555 562949953421312 1 2000000000000000 7451 8388608 1 3240000 7413681384968031305728 883779690857891 562949953421312 50000000081 162000000000000000 qz17 (Ns252p1287 rfl) rfl rfl 

noncomputable abbrev qz515 := (@HMul.hMul Real Real Real qz584 qz589 qz699)

noncomputable abbrev qz213 := qz515

noncomputable abbrev qz516 := qz699

noncomputable abbrev qz214 := qz516

noncomputable def Ns252p1289 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 562891 4000) qz514) qz213 357436180838034475513 225179981368524800 109939694031671 20250000000000000000 883779690857891 2251799813685248 50000000081 648000000000000000 Ns252p1280 357347802868948686413 225179981368524800 148669592045603 27000000000000000000 (Ns252p1286 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz214 1 4 0 1 883779690857891 562949953421312 50000000081 162000000000000000 883779690857891 2251799813685248 50000000081 648000000000000000 qz361 Ns252p1288 rfl) 

noncomputable def Ns252p1290 := @Ns252p1276 Ns252p1270 Ns252p1271 768283216355098069 55296000000000000000000 (@Ns252p1278 768283216355098069 55296000000000000000000 (Ns252p1279 (Ns252p1289 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 562891 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz700 (Real.log Real.pi) 562891 2000 0 1 38410761 33554432 1 33554432 21621071670051 67108864000 562891 67108864000 (Enclosure.Real.IsNear.const Bool.false 562891 2000) RS253to264.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns252p1272 Ns252p1273) 

noncomputable def Ns252p1291 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns252p1270 Ns252p1271 768283216355098069 55296000000000000000000 16497341233 16777216 117 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz362 qz210 (Enclosure.sfrac Bool.true Ns252p1272 Ns252p1273)) Bool.false Ns252p1270 Ns252p1271 768283216355098069 55296000000000000000000 Ns252p1274 (Ns252p1290 rfl rfl)) 

noncomputable def Ns252p1292 := nat_lit 3797138522655488449970176 

noncomputable def Ns252p1293 := nat_lit 856401546956800191057477073007978275655943956596632463906131849373446998465107388374449205002459537862133384015296017130608297554415616 

noncomputable def Ns252p1294 := nat_lit 609424182554853501923185993701130021669755259172171896486349445075834429992016172696416275219728050237606967694441035292730658816 

noncomputable def Ns252p1295 := nat_lit 4276691364622009651754923400769652053534496660081084472254941694223041801371699792333195916832880614659326989441330515708073876183781376 

noncomputable def Ns252p1296 := BSN.sin_dyadic_bound_f 53960583878 34359738368 4 3 16777216 6486329 Ns252p1293 Ns252p107 Ns252p1294 Ns252p1295 Ns252p110 Ns252p1294 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53960583878) qz363 0 3 Ns252p1293 Ns252p107 Ns252p1294 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53960583878) qz364 0 3 Ns252p1295 Ns252p110 Ns252p1294 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1297 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz206) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16497341233) qz410) Bool.false 16497341233 16777216 117 8388608 Bool.true 16777215 16777216 1 3240000 (Ns252p1291 rfl) (Enclosure.sfrac_false_div 16497341233 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16497341233) qz410) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns252p1292) qz411) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 156 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 16497341233 16777216 226375608064910080 72057594037927936 156 Ns252p1292 Ns252p93 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns252p1292 Ns252p93 53960583878 34359738368 6486329 6480000 (Ns252p1296 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p1298 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns252p1270 Ns252p1271 768283216355098069 55296000000000000000000 131978729866 134217728 1866 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz362 qz210 (Enclosure.sfrac Bool.true Ns252p1272 Ns252p1273)) Bool.false Ns252p1270 Ns252p1271 768283216355098069 55296000000000000000000 Ns252p1274 (Ns252p1290 rfl rfl)) 

noncomputable def Ns252p1299 := Ns252p1269 34707 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 377 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 110081128 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 232 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 118139119 134217728) qz209 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) Bool.true 16777215 16777216 6054197 424673280000 134217720 134217728 1914 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.true 16777215 16777216 6054197 424673280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz206) qz206) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.true 16777215 16777216 387468608 27179089920000 16777215 16777216 6054197 424673280000 (Ns252p1297 rfl rfl) rfl)) rfl) (Ns252p1298 rfl) RS253to264.d7 

noncomputable def Ns252p1300 := nat_lit 272490558263662787021864640345297728187133049865871436252226205788865 

noncomputable def Ns252p1301 := nat_lit 77057447266053039985390602429467038750693795570660082607589698241 

noncomputable def Ns252p1302 := nat_lit 713540988156876546802050092309941579570228293027310788145894441364161 

noncomputable def Ns252p1303 := BSN.sin_dyadic_bound_f 129077881 134217728 3 2 134217728 67108864 Ns252p1300 Ns252p116 Ns252p1301 Ns252p1302 Ns252p119 Ns252p1301 110081128 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 129077881) qz367 0 2 Ns252p1300 Ns252p116 Ns252p1301 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 129077881) qz368 0 2 Ns252p1302 Ns252p119 Ns252p1301 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1304 := nat_lit 10579789059720906316941108593733977537228405363620419311674574297761 

noncomputable def Ns252p1305 := nat_lit 376552448272630344654256497208409108140195241282668515511032481 

noncomputable def Ns252p1306 := nat_lit 31738614074266173690134017268207515793468935700378692597992700828321 

noncomputable def Ns252p1307 := BSN.cos_dyadic_bound_f 66370973 134217728 3 2 134217728 67108864 Ns252p1304 Ns252p144 Ns252p1305 Ns252p1306 Ns252p147 Ns252p1305 118139119 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 66370973) qz369 0 2 Ns252p1304 Ns252p144 Ns252p1305 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 66370973) qz370 0 2 Ns252p1306 Ns252p147 Ns252p1305 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1308 := nat_lit 5032282670324574484725937278976 

noncomputable def Ns252p1309 := BSN.sin_dyadic_bound_f 47363224 134217728 2 1 134217728 67108864 Ns252p1308 Ns252p238 Ns252p1308 Ns252p1308 Ns252p239 Ns252p1308 46386328 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 47363224) qz367 0 1 Ns252p1308 Ns252p238 Ns252p1308 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 47363224) qz368 0 1 Ns252p1308 Ns252p239 Ns252p1308 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1310 := nat_lit 9266955201552979292264503560976 

noncomputable def Ns252p1311 := BSN.sin_dyadic_bound_f 55173974 134217728 2 1 134217728 67108864 Ns252p1310 Ns252p238 Ns252p1310 Ns252p1310 Ns252p239 Ns252p1310 53633119 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 55173974) qz367 0 1 Ns252p1310 Ns252p238 Ns252p1310 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 55173974) qz368 0 1 Ns252p1310 Ns252p239 Ns252p1310 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1312 := Ns252p1267 58888 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 129 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 46386328 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 53633119 134217728) qz209 rfl rfl (Ns252p1299 RS253to264.d9 RS253to264.d11 RS253to264.d13 RS253to264.d17 (Ns252p1303 rfl rfl) (Ns252p1307 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns252p1298 rfl) RS253to264.d19 RS253to264.d21 RS253to264.d23 RS253to264.d25 RS253to264.d17 (Ns252p1309 rfl rfl) (Ns252p1311 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns252p1313 := nat_lit 55418494920634659284623360000 

noncomputable def Ns252p1314 := BSN.cos_dyadic_bound_f 15343120 134217728 2 1 134217728 67108864 Ns252p1313 Ns252p122 Ns252p1313 Ns252p1313 Ns252p123 Ns252p1313 133341707 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 15343120) qz369 0 1 Ns252p1313 Ns252p122 Ns252p1313 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 15343120) qz370 0 1 Ns252p1313 Ns252p123 Ns252p1313 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1315 := nat_lit 18445154557258145845909489521842575650458127285935575549754919069985 

noncomputable def Ns252p1316 := nat_lit 353268833690741358494535205271621646380696696431976298022152481 

noncomputable def Ns252p1317 := nat_lit 48308166167088216015182529024017258363772383668513236573447037888801 

noncomputable def Ns252p1318 := BSN.sin_dyadic_bound_f 65843539 134217728 3 2 134217728 67108864 Ns252p1315 Ns252p116 Ns252p1316 Ns252p1317 Ns252p119 Ns252p1316 63234136 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 65843539) qz367 0 2 Ns252p1315 Ns252p116 Ns252p1316 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 65843539) qz368 0 2 Ns252p1317 Ns252p119 Ns252p1316 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1319 := Ns252p1265 78962 BSN.abs_quadSignPos (BSN.cos_quad_nat0 16 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133341707 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 71 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 63234136 134217728) qz209 rfl rfl (Ns252p1312 rfl rfl) (Ns252p1298 rfl) RS253to264.d27 RS253to264.d29 RS253to264.d31 RS253to264.d33 RS253to264.d17 (Ns252p1314 rfl rfl) (Ns252p1318 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p1320 := nat_lit 1393818744849913881562744140625 

noncomputable def Ns252p1321 := BSN.sin_dyadic_bound_f 34359875 134217728 2 1 134217728 67108864 Ns252p1320 Ns252p238 Ns252p1320 Ns252p1320 Ns252p239 Ns252p1320 33985798 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 34359875) qz367 0 1 Ns252p1320 Ns252p238 Ns252p1320 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 34359875) qz368 0 1 Ns252p1320 Ns252p239 Ns252p1320 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1322 := nat_lit 36419167691523867465405771742867164716113193362304638735862819099425 

noncomputable def Ns252p1323 := nat_lit 1377160475962281778269888262289593472554083783383754137586012961 

noncomputable def Ns252p1324 := nat_lit 95381304741791904429374108078894105390864704575148575372941767906081 

noncomputable def Ns252p1325 := BSN.sin_dyadic_bound_f 78050029 134217728 3 2 134217728 67108864 Ns252p1322 Ns252p116 Ns252p1323 Ns252p1324 Ns252p119 Ns252p1323 73724869 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 78050029) qz367 0 2 Ns252p1322 Ns252p116 Ns252p1323 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 78050029) qz368 0 2 Ns252p1324 Ns252p119 Ns252p1323 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1326 := Ns252p1263 96502 BSN.abs_quadSignPos qz650 (BSN.sfrac_eq_quadSignPos_mul Bool.false 33985798 134217728) BSN.abs_quadSignNeg qz371 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 73724869 134217728) qz209 rfl rfl (Ns252p1319 rfl) (Ns252p1298 rfl) RS253to264.d35 RS253to264.d37 RS253to264.d39 RS253to264.d41 RS253to264.d17 (Ns252p1321 rfl rfl) (Ns252p1325 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p1327 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) 125250191 134217728 96502 134217728 125250191 134217728 96502 134217728 33621592135172096 125250191 67108864 48251 33554432 (Ns252p1326 rfl) 

noncomputable def Ns252p1328 := @Enclosure.Real.IsNear.mulLit_tf qz697 (Zeta.RiemannSiegel.correction qz208) 1363323 4194304 1 8388608 6769910794605 17592186044416 200113240503469 7124835347988480000 9229575094233272415 73786976294838206464 

noncomputable abbrev qz701 := (@HPow.hPow Real Real Real qz7 qz207 qz9)

noncomputable def Ns252p1329 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz701 1 1 0 1 1363323 4194304 1 8388608 1363323 4194304 1 8388608 

noncomputable def Ns252p1330 := @Enclosure.Real.IsNear.sqrt_image qz207 1503018601707 16777216000 562891 16777216000 79398454 79398485 8388608 (@Enclosure.Real.IsNear.of_eq qz207 (@HMul.hMul Real Real Real qz5 qz206 qz3) Bool.false 1503018601707 16777216000 562891 16777216000 (BSN.t_div_two_pi_mk qz206 562891 1000 qz209) (@Enclosure.Real.IsNear.mulLit_ff qz206 qz3 562891 1000 0 1 2670177 16777216 1 16777216 1503018601707 16777216000 562891 16777216000 (Enclosure.Real.IsNear.const Bool.false 562891 1000) RS253to264.d44 rfl)) 

noncomputable abbrev qz784 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 562891 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz702 := qz784

noncomputable abbrev qz517 := qz702

noncomputable abbrev qz215 := qz517

noncomputable def Ns252p1331 := @Enclosure.Real.IsNear.sqrt_image qz215 158796939 16777216 31 16777216 25807799 25807805 8388608 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 158796939 16777216 31 16777216 158796939 16777216 31 16777216 (Ns252p1330 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns252p1332 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz215) 12903901 4194304 3 8388608 2726645 2726647 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz215) Bool.false 51615604 16777216 6 16777216 12903901 4194304 3 8388608 (Ns252p1331 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns252p1333 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 5453292 16777216 2 16777216 1363323 4194304 1 8388608 (Ns252p1332 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz216 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz511))

noncomputable abbrev qz703 := (@HMul.hMul Real Real Real qz735 qz782 qz782)

noncomputable abbrev qz518 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz703 qz696) qz599)

noncomputable abbrev qz217 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz518))

noncomputable def Ns252p1334 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz208) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz216) qz217) Bool.false 6769910794605 

noncomputable def Ns252p1335 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz216) qz217 8595195 8388608 53 

noncomputable abbrev qz704 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz216))

noncomputable def Ns252p1336 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz216) (@Neg.neg Real Real.instNeg qz704) Bool.true 8595195 8388608 53 4194304 (BSN.inv_eq_neg_inv_neg qz216) 

noncomputable def Ns252p1337 := @Enclosure.Real.IsNear.recentre' qz704 Bool.false 17190390 16777216 212 16777216 8595195 8388608 

noncomputable def Ns252p1338 := @Enclosure.Real.IsNear.recentre' qz216 Bool.true 16373973 16777216 162954304 13589544960000 16373973 16777216 2546161 212336640000 

noncomputable abbrev qz218 := (@HMul.hMul Real Real Real qz346 qz343 qz511)

noncomputable def Ns252p1339 := @Enclosure.Real.IsNear.cos_image qz218 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12255345) qz377) Bool.false 12255345 4194304 49 4194304 Bool.true 16373973 16777216 1 

noncomputable def Ns252p1340 := nat_lit 836568337747384035847349017 

noncomputable def Ns252p1341 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz208 884279719003555 140737488355328 1 500000000000000 7801995 16777216 31 16777216 6899145946267141092225 2361183241434822606848 Ns252p1340 

noncomputable def Ns252p1342 := @Enclosure.Real.IsNear.subLit_ff_p qz215 qz1 158796939 16777216 31 16777216 9 1 0 1 7801995 7801995 16777216 31 

noncomputable def Ns252p1343 := @Ns252p1342 16777216 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 158796939 16777216 31 16777216 158796939 16777216 31 16777216 (Ns252p1330 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns252p1344 := @Enclosure.Real.IsNear.recentre' qz218 Bool.false 6899145946267141092225 2361183241434822606848 Ns252p1340 Ns252p168 12255345 4194304 49 4194304 (@Ns252p1341 Ns252p168 RS253to264.d43 (Ns252p1343 rfl rfl) rfl) 

noncomputable def Ns252p1345 := nat_lit 19598195683058866768205840964798606236012141947260604597603047266271522437901613881427105 

noncomputable def Ns252p1346 := nat_lit 21573130736889113816945327103455901384378911061489461533687706560530745934603448550561 

noncomputable def Ns252p1347 := nat_lit 51293679815389687732454529140114563920647567815392505294096296077232175653467249820370081 

noncomputable def Ns252p1348 := BSN.sin_dyadic_bound_f 46423635421 34359738368 3 2 16777216 6486329 Ns252p1345 Ns252p288 Ns252p1346 Ns252p1347 Ns252p291 Ns252p1346 16373973 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 46423635421) qz363 0 2 Ns252p1345 Ns252p288 Ns252p1346 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 46423635421) qz364 0 2 Ns252p1347 Ns252p291 Ns252p1346 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1349 := @Ns252p1339 3240000 (Ns252p1344 rfl) (Enclosure.sfrac_false_div 12255345 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12255345) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 816693231200415273451520) qz642) 226375608064910080 72057594037927936 Bool.false 16373973 16777216 0 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 12255345 4194304 226375608064910080 72057594037927936 0 816693231200415273451520 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16373973 16777216 816693231200415273451520 604462909807314587353088 46423635421 34359738368 6486329 6480000 (Ns252p1348 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p1350 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz216) 16373973 16777216 2546161 212336640000 8595089 8595301 8388608 (@Enclosure.Real.IsNear.neg qz216 Bool.true 16373973 16777216 2546161 212336640000 (Ns252p1338 (Ns252p1349 rfl rfl) rfl)) 

noncomputable def Ns252p1351 := Ns252p1336 (@Enclosure.Real.IsNear.neg qz704 Bool.false 8595195 8388608 53 4194304 (@Ns252p1337 53 4194304 (Ns252p1350 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p1352 := @Enclosure.Real.IsNear.recentre' qz217 Bool.true 3150556 8388608 

noncomputable abbrev qz219 := (@HMul.hMul Real Real Real qz346 qz343 qz518)

noncomputable def Ns252p1353 := @Enclosure.Real.IsNear.cos_image qz219 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32813113)) qz410) Bool.true 32813113 16777216 

noncomputable def Ns252p1354 := nat_lit 77477772911016158561392655605 

noncomputable def Ns252p1355 := nat_lit 27089117609876565272534484192015661 

noncomputable def Ns252p1356 := @Enclosure.Real.IsNear.recentre' qz219 Bool.true Ns252p1354 Ns252p183 Ns252p1355 

noncomputable abbrev qz220 := qz518

noncomputable def Ns252p1357 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz220 884279719003555 140737488355328 1 500000000000000 87616815410311 

noncomputable abbrev qz519 := (@HSub.hSub Real Real Real qz588 qz703 qz696)

noncomputable abbrev qz221 := qz519

noncomputable def Ns252p1358 := @Enclosure.Real.IsNear.subLit_tf qz221 qz31 70024629365895 281474976710656 1003818347 281474976710656 1 16 

noncomputable abbrev qz520 := qz703

noncomputable abbrev qz222 := qz520

noncomputable def Ns252p1359 := @Enclosure.Real.IsNear.subLit_ff_n qz222 qz208 60871125980025 281474976710656 483724651 281474976710656 7801995 16777216 31 16777216 

noncomputable def Ns252p1360 := @Enclosure.Real.IsNear.mulLit_ff qz208 qz208 7801995 16777216 31 16777216 7801995 16777216 31 16777216 60871125980025 281474976710656 

noncomputable def Ns252p1361 := nat_lit 146502630279780962647659232066063713058097996004199722030114992169013222085073432565899646198561 

noncomputable def Ns252p1362 := nat_lit 1558006300009807191153104752802522199524133128378914038927600670455025937157373929845678881 

noncomputable def Ns252p1363 := nat_lit 883658684613087964986279932540771161971449565803131884900851786487378671435296275237180933137185 

noncomputable def Ns252p1364 := BSN.cos_dyadic_bound_t 32813113 16777216 4 3 8388608 3240000 Ns252p1361 Ns252p567 Ns252p1362 Ns252p1363 Ns252p570 Ns252p1362 3150556 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32813113) (BSN.cosEvenQ 16777216) 0 3 Ns252p1361 Ns252p567 Ns252p1362 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32813113) (BSN.cosOddQ 16777216) 0 3 Ns252p1363 Ns252p570 Ns252p1362 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1365 := @Ns252p1352 1238257216 54358179840000 787639 2097152 19347769 849346560000 (@Ns252p1353 377 16777216 Bool.true 3150556 8388608 1 3240000 (@Ns252p1356 Ns252p186 32813113 16777216 377 16777216 (@Ns252p1357 281474976710656 1003818347 281474976710656 Ns252p1354 Ns252p183 Ns252p1355 Ns252p186 RS253to264.d43 (@Ns252p1358 0 1 1401869046564976 87616815410311 281474976710656 1003818347 281474976710656 (@Ns252p1359 1174818332191563448320 70024629365895 281474976710656 1003818347 281474976710656 (@Ns252p1360 483724651 281474976710656 (Ns252p1343 rfl rfl) (Ns252p1343 rfl rfl) rfl) (Ns252p1343 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32813113 16777216) (BSN.cos_neg_of_bound 32813113 16777216 Bool.true 3150556 8388608 1 3240000 (Ns252p1364 rfl rfl)) rfl rfl) 

noncomputable def Ns252p1366 := @Ns252p1328 548379980750877263443 Ns252p1259 (Ns252p1329 qz33 (@Enclosure.Real.IsNear.of_eq qz701 (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 1363323 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz207 (BSN.t_div_two_pi_nonneg qz206 562891 1000 qz209)) Ns252p1333) rfl) (@Ns252p1334 17592186044416 200113240503469 7124835347988480000 (BSN.correction_mk qz208 (BSN.cos_two_pi_p_ne_zero_mk qz206 562891 1000 9 qz209 rfl rfl (@BSN.floor_sqrt_eq_dec qz206 562891 1000 9 qz209 rfl rfl rfl))) (@Ns252p1335 4194304 787639 2097152 19347769 849346560000 6769910794605 17592186044416 200113240503469 7124835347988480000 Ns252p1351 (Ns252p1365 rfl) rfl)) 

noncomputable def Ns252p1367 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (hardyZApproximantRS₀ qz206) Bool.true 128484466291431632801 73786976294838206464 86493487574698914383443 Ns252p1259 (@Eq.refl Real (hardyZApproximantRS₀ qz206)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) (@HMul.hMul Real Real Real qz5 qz697 (Zeta.RiemannSiegel.correction qz208))) Bool.true 128484466291431632801 73786976294838206464 86493487574698914383443 Ns252p1259 (BSN.hardyZApproximantRS₀_eq qz206 9 (@BSN.floor_sqrt_eq_dec qz206 562891 1000 9 qz209 rfl rfl rfl)) (@Ns252p1261 128484466291431632801 73786976294838206464 86493487574698914383443 Ns252p1259 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 9)) Bool.true 125250191 67108864 48251 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz206) qz206 9) (Ns252p1327 (Ns252p1326 rfl) rfl rfl)) (Ns252p1366 rfl) rfl rfl)) 

theorem RS253to264.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz206) Bool.true 128484466291431632801 73786976294838206464 86493487574698914383443 Ns252p1259 := Ns252p1367 

noncomputable def Ns252p1368 := nat_lit 143459712560970285956726784 

noncomputable abbrev qz785 := (Enclosure.sfrac Bool.false 564289 1000)

noncomputable abbrev qz705 := qz785

noncomputable abbrev qz521 := qz705

noncomputable abbrev qz223 := qz521

noncomputable abbrev qz786 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 564289 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz706 := qz786

noncomputable abbrev qz522 := qz706

noncomputable abbrev qz224 := qz522

noncomputable abbrev qz787 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 564289 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz707 := qz787

noncomputable abbrev qz523 := qz707

noncomputable abbrev qz225 := qz523

noncomputable abbrev qz708 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz224 qz9))

noncomputable def Ns252p1369 := @Enclosure.Real.IsNear.subLit_tt_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (@HMul.hMul Real Real Real qz5 qz708 (Zeta.RiemannSiegel.correction qz225)) 292983 33554432 48373 33554432 4597570818628834995 36893488147419103232 7574275844202444139 830103483316929822720000 Ns252p1368 

noncomputable def Ns252p1370 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 564289 1000 119 161 134217728 67108864 2251799813685248 Bool.false 132400578758 1871 

noncomputable def Ns252p1371 := Ns252p1370 279097919 42 47453128 8 294906479 42 44739240 8 Bool.false 20312302 79162 Bool.true 2689874 Bool.true 68480394 7074237752028440 1 Bool.false 2689693 Bool.false Bool.false 65547656 Bool.true Bool.true 585966 

noncomputable def Ns252p1372 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 564289 1000 15 71 134217728 67108864 2251799813685248 Bool.false 132400578758 1871 

noncomputable def Ns252p1373 := Ns252p1372 240485871 42 54794152 8 261175631 42 50729528 8 Bool.true 30578338 59038 Bool.true 140522190 Bool.true 9118179 7074237752028440 1 Bool.false 116220816 Bool.false Bool.false 9111166 Bool.false Bool.false 20312302 

noncomputable def Ns252p1374 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 564289 1000 129 49 134217728 67108864 2251799813685248 Bool.false 132400578758 1871 

noncomputable def Ns252p1375 := Ns252p1374 186065264 42 67108856 8 216015088 42 60023992 8 Bool.false 94426911 34796 Bool.false 209092877 Bool.false 175033773 7074237752028440 1 Bool.false 134206503 Bool.true Bool.false 129472820 Bool.true Bool.true 30578338 

noncomputable def Ns252p1376 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 564289 1000 378 233 134217728 67108864 2251799813685248 Bool.false 132400578758 1871 

noncomputable def Ns252p1377 := Ns252p1376 93032624 42 94906264 8 147453232 42 77490640 16 Bool.false 134217648 1922 Bool.false 210038451 Bool.false 71251532 7074237752028440 1 Bool.false 790258 Bool.true Bool.false 67951714 Bool.true Bool.false 94426911 

noncomputable def Ns252p1378 := nat_lit 322725158379466761514046313578848402448082800647281865411 

noncomputable def Ns252p1379 := nat_lit 327154442467421330489763073827884801640704325451776000 

noncomputable def Ns252p1380 := nat_lit 27463129400780656575093385815520000 

noncomputable def Ns252p1381 := nat_lit 92982885026748741236634451134899791680 

noncomputable abbrev qz788 := (@Eq.refl Real (Enclosure.sfrac Bool.false 564289 1000))

noncomputable abbrev qz709 := qz788

noncomputable abbrev qz524 := qz709

noncomputable abbrev qz226 := qz524

noncomputable def Ns252p1382 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz223 564289 1000 1273689302084 16000000 1128578 4000 2000 Ns252p1380 Ns252p1381 qz226 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns252p1383 := nat_lit 103272050681429363684494820345231488783386496207130196931520 

noncomputable abbrev qz710 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1128578))))

noncomputable abbrev qz525 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 564289 4000) (Real.log (Enclosure.sfrac Bool.false 1273689302084 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz710))

noncomputable abbrev qz711 := (Enclosure.sfrac Bool.false 564289 2000)

noncomputable abbrev qz227 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz525 qz711) (@HMul.hMul Real Real Real qz346 qz711 (Real.log Real.pi)))

noncomputable def Ns252p1384 := @Enclosure.Real.IsNear.addLit_ft_p qz227 (Enclosure.sfrac Bool.true Ns252p1380 Ns252p1381) 1110656886721201691739 1125899906842624000 770180733168219551 55296000000000000000000 Ns252p1380 Ns252p1381 0 1 Ns252p1383 

noncomputable def Ns252p1385 := nat_lit 74534921961636530247482474496000 

noncomputable abbrev qz228 := (@HSub.hSub Real Real Real qz350 qz525 qz711)

noncomputable def Ns252p1386 := @Enclosure.Real.IsNear.subLit_ff_p qz228 (@HMul.hMul Real Real Real qz5 qz711 (Real.log Real.pi)) 1474299183317489933403 1125899906842624000 149033654696587 27000000000000000000 21674769913929 67108864000 564289 67108864000 Ns252p1385 1110656886721201691739 1125899906842624000 

noncomputable def Ns252p1387 := nat_lit 2948598366634979866806000 

noncomputable abbrev qz229 := qz525

noncomputable def Ns252p1388 := @Enclosure.Real.IsNear.subLit_ff_p qz229 qz711 1791965649583648660571 1125899906842624000 149033654696587 27000000000000000000 564289 2000 0 1 Ns252p1387 1474299183317489933403 1125899906842624000 149033654696587 27000000000000000000 

noncomputable def Ns252p1389 := nat_lit 4035147915862824459177374350581956608 

noncomputable def Ns252p1390 := nat_lit 27285067636228625413439488 

noncomputable def Ns252p1391 := nat_lit 16468737171318257888884931720851362670762600587906715304040983850601503559680 

noncomputable def Ns252p1392 := nat_lit 51877105852381645986981905333866307365099872693702034997420144011704692736 

noncomputable def Ns252p1393 := nat_lit 1952082688191251344263571854601170018592627135529540618425759894794240 

noncomputable def Ns252p1394 := BSN.log_dyadic_bound 225113302084 2322265302084 4 3 Ns252p1391 67108864 25920000 Ns252p1392 Ns252p1393 13051640 2547378604168 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 225113302084) (BSN.artanhQ 2322265302084) 0 3 Ns252p1392 Ns252p1391 Ns252p1393 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz526 := (Real.log (Enclosure.sfrac Bool.false 1273689302084 16000000))

noncomputable def Ns252p1395 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 564289 4000) qz526 564289 4000 0 1 3176399929941239 281474976710656 195312581 5062500000000000 1792407540066611814071 1125899906842624000 110212741019909 20250000000000000000 (Enclosure.Real.IsNear.const Bool.false 564289 4000) (BSN.isNear_log_sfrac 1273689302084 16000000 3176399929941239 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1273689302084) qz353)) Bool.false Ns252p1390 Ns252p93 1000000414720000 25920000000000000000000 3176399929941239 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1273689302084 16000000 16 2547378604168 2097152000000 13051640 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns252p1394 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p1396 := BSN.arctan_dyadic_bound_f 1000 1128578 1 0 8388608 3240000 0 1 1 0 1 1 7432 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1128578) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1128578) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns252p1397 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1128578))) 884279719003555 562949953421312 1 2000000000000000 7432 8388608 1 3240000 7413692081017146310656 883780965926307 562949953421312 50000000081 162000000000000000 qz17 (Ns252p1396 rfl) rfl rfl 

noncomputable abbrev qz527 := (@HMul.hMul Real Real Real qz584 qz589 qz710)

noncomputable abbrev qz230 := qz527

noncomputable abbrev qz528 := qz710

noncomputable abbrev qz231 := qz528

noncomputable def Ns252p1398 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 564289 4000) qz526) qz230 1792407540066611814071 1125899906842624000 110212741019909 20250000000000000000 883780965926307 2251799813685248 50000000081 648000000000000000 Ns252p1389 1791965649583648660571 1125899906842624000 149033654696587 27000000000000000000 (Ns252p1395 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz231 1 4 0 1 883780965926307 562949953421312 50000000081 162000000000000000 883780965926307 2251799813685248 50000000081 648000000000000000 qz361 Ns252p1397 rfl) 

noncomputable def Ns252p1399 := @Ns252p1384 Ns252p1378 Ns252p1379 770180733168219551 55296000000000000000000 (@Ns252p1386 770180733168219551 55296000000000000000000 (Ns252p1388 (Ns252p1398 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 564289 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz711 (Real.log Real.pi) 564289 2000 0 1 38410761 33554432 1 33554432 21674769913929 67108864000 564289 67108864000 (Enclosure.Real.IsNear.const Bool.false 564289 2000) RS253to264.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns252p1380 Ns252p1381) 

noncomputable def Ns252p1400 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns252p1378 Ns252p1379 770180733168219551 55296000000000000000000 2068759043 2097152 235 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz362 qz227 (Enclosure.sfrac Bool.true Ns252p1380 Ns252p1381)) Bool.false Ns252p1378 Ns252p1379 770180733168219551 55296000000000000000000 Ns252p1382 (Ns252p1399 rfl rfl)) 

noncomputable def Ns252p1401 := BSN.cos_dyadic_bound_f 37446752 34359738368 1 0 16777216 6486329 0 1 1 0 1 1 16777206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 37446752) (BSN.cosEvenQ 34359738368) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 37446752) (BSN.cosOddQ 34359738368) 0 0 rfl) rfl rfl 

noncomputable def Ns252p1402 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz223) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2068759043) (@Nat.cast Real Real.instNatCast 2097152)) Bool.false 2068759043 2097152 235 16777216 Bool.false 16777206 16777216 1 3240000 (Ns252p1400 rfl) (Enclosure.sfrac_false_div 2068759043 2097152) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2068759043) (@Nat.cast Real Real.instNatCast 2097152)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 329385120038194774016) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 16777206 16777216 157 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q0 2068759043 2097152 226375608064910080 72057594037927936 157 329385120038194774016 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777206 16777216 329385120038194774016 302231454903657293676544 37446752 34359738368 6486329 6480000 (Ns252p1401 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p1403 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns252p1378 Ns252p1379 770180733168219551 55296000000000000000000 132400578758 134217728 1871 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz362 qz227 (Enclosure.sfrac Bool.true Ns252p1380 Ns252p1381)) Bool.false Ns252p1378 Ns252p1379 770180733168219551 55296000000000000000000 Ns252p1382 (Ns252p1399 rfl rfl)) 

noncomputable def Ns252p1404 := Ns252p1377 34796 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 378 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 790258 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 233 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 67951714 134217728) qz226 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) Bool.false 8388603 8388608 12159019 849346560000 134217648 134217728 1922 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 8388603 8388608 12159019 849346560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz223) qz223) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 16777206 16777216 778177216 54358179840000 8388603 8388608 12159019 849346560000 (Ns252p1402 rfl rfl) rfl)) rfl) (Ns252p1403 rfl) RS253to264.d7 

noncomputable def Ns252p1405 := nat_lit 4105332955601954308783244447019019101495544679741393732828896529719804858156936935146889418577997473148081 

noncomputable def Ns252p1406 := nat_lit 7372006021700529926884938922518940484026866247382443712309732980319697115197088107303338736436276401 

noncomputable def Ns252p1407 := nat_lit 24846587633204027510218317107757326155516820083312647284740117760765621124254097332921621577450643136867505 

noncomputable def Ns252p1408 := BSN.cos_dyadic_bound_f 210038451 134217728 4 3 134217728 67108864 Ns252p1405 Ns252p398 Ns252p1406 Ns252p1407 Ns252p401 Ns252p1406 790258 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 210038451) qz369 0 3 Ns252p1405 Ns252p398 Ns252p1406 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 210038451) qz370 0 3 Ns252p1407 Ns252p401 Ns252p1406 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1409 := nat_lit 25293536228255519274052001852866849204052525303942929406861387038720 

noncomputable def Ns252p1410 := nat_lit 664283787807627028965979231610037342524567326105874309044043776 

noncomputable def Ns252p1411 := nat_lit 66243900328822290512089298029228664997773478877513024650041370935296 

noncomputable def Ns252p1412 := BSN.sin_dyadic_bound_f 71251532 134217728 3 2 134217728 67108864 Ns252p1409 Ns252p116 Ns252p1410 Ns252p1411 Ns252p119 Ns252p1410 67951714 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 71251532) qz367 0 2 Ns252p1409 Ns252p116 Ns252p1410 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 71251532) qz368 0 2 Ns252p1411 Ns252p119 Ns252p1410 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1413 := nat_lit 10465993383019244499374351493284719061717020620542328784127908634184235155083101165966424277671331342118321 

noncomputable def Ns252p1414 := nat_lit 6983463372767136548857257689328170677660629598005000000033376476659705013287659322465264130592140721 

noncomputable def Ns252p1415 := nat_lit 52267052549418873605776116178554909180405219671242356940992872075040294441195274933533548207454614782799281 

noncomputable def Ns252p1416 := BSN.sin_dyadic_bound_f 209092877 134217728 4 3 134217728 67108864 Ns252p1413 Ns252p137 Ns252p1414 Ns252p1415 Ns252p140 Ns252p1414 134206503 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 209092877) qz367 0 3 Ns252p1413 Ns252p137 Ns252p1414 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 209092877) qz368 0 3 Ns252p1415 Ns252p140 Ns252p1414 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1417 := nat_lit 5134294875630214115828515031783904720370025360638919261857529831913920718620884248509426610805049519919921 

noncomputable def Ns252p1418 := nat_lit 826917634587405057708157608222603003876360178359126361872687537413741108663774591519806077031830321 

noncomputable def Ns252p1419 := nat_lit 25656306927073881368836292803267194302880301555705255562053212714836662412099521043277419233651887262552881 

noncomputable def Ns252p1420 := BSN.sin_dyadic_bound_f 175033773 134217728 4 3 134217728 67108864 Ns252p1417 Ns252p137 Ns252p1418 Ns252p1419 Ns252p140 Ns252p1418 129472820 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 175033773) qz367 0 3 Ns252p1417 Ns252p137 Ns252p1418 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 175033773) qz368 0 3 Ns252p1419 Ns252p140 Ns252p1418 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1421 := Ns252p1375 59038 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 129 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 134206503 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 129472820 134217728) qz226 rfl rfl (Ns252p1404 RS253to264.d9 RS253to264.d11 RS253to264.d13 RS253to264.d17 (Ns252p1408 rfl rfl) (Ns252p1412 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns252p1403 rfl) RS253to264.d19 RS253to264.d21 RS253to264.d23 RS253to264.d25 RS253to264.d17 (Ns252p1416 rfl rfl) (Ns252p1420 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns252p1422 := nat_lit 382801369998701449598006220417849648286517092146583742650430190240000 

noncomputable def Ns252p1423 := nat_lit 152040495489833659864937012738548363414472521953265488944100000000 

noncomputable def Ns252p1424 := nat_lit 1002328855861044065878806393549934286257254666776937848530931479200000 

noncomputable def Ns252p1425 := BSN.sin_dyadic_bound_f 140522190 134217728 3 2 134217728 67108864 Ns252p1422 Ns252p116 Ns252p1423 Ns252p1424 Ns252p119 Ns252p1423 116220816 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 140522190) qz367 0 2 Ns252p1422 Ns252p116 Ns252p1423 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 140522190) qz368 0 2 Ns252p1424 Ns252p119 Ns252p1423 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1426 := nat_lit 6912457187952097429614633681 

noncomputable def Ns252p1427 := BSN.sin_dyadic_bound_f 9118179 134217728 2 1 134217728 67108864 Ns252p1426 Ns252p238 Ns252p1426 Ns252p1426 Ns252p239 Ns252p1426 9111166 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 9118179) qz367 0 1 Ns252p1426 Ns252p238 Ns252p1426 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 9118179) qz368 0 1 Ns252p1426 Ns252p239 Ns252p1426 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1428 := Ns252p1373 79162 BSN.abs_quadSignPos (BSN.cos_quad_nat3 15 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 116220816 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 71 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 9111166 134217728) qz226 rfl rfl (Ns252p1421 rfl rfl) (Ns252p1403 rfl) RS253to264.d27 RS253to264.d29 RS253to264.d31 RS253to264.d33 RS253to264.d17 (Ns252p1425 rfl rfl) (Ns252p1427 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p1429 := BSN.sin_dyadic_bound_f 2689874 134217728 1 0 134217728 67108864 0 1 1 0 1 1 2689693 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 2689874) qz367 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 2689874) qz368 0 0 rfl) rfl rfl 

noncomputable def Ns252p1430 := nat_lit 21582216883175209765910944312667495509261524955247157798817924112640 

noncomputable def Ns252p1431 := nat_lit 483648675775735902657418118891741410384995934544954480114524416 

noncomputable def Ns252p1432 := nat_lit 56524070691412388671638646903841425419115751556039007165841044398336 

noncomputable def Ns252p1433 := BSN.sin_dyadic_bound_f 68480394 134217728 3 2 134217728 67108864 Ns252p1430 Ns252p116 Ns252p1431 Ns252p1432 Ns252p119 Ns252p1431 65547656 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 68480394) qz367 0 2 Ns252p1430 Ns252p116 Ns252p1431 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 68480394) qz368 0 2 Ns252p1432 Ns252p119 Ns252p1431 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1434 := Ns252p1371 96746 BSN.abs_quadSignPos qz650 (BSN.sfrac_eq_quadSignPos_mul Bool.false 2689693 134217728) BSN.abs_quadSignNeg qz371 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 65547656 134217728) qz226 rfl rfl (Ns252p1428 rfl) (Ns252p1403 rfl) RS253to264.d35 RS253to264.d37 RS253to264.d39 RS253to264.d41 RS253to264.d17 (Ns252p1429 rfl rfl) (Ns252p1433 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p1435 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) 585966 134217728 96746 134217728 585966 134217728 96746 134217728 157294050410496 292983 33554432 48373 33554432 (Ns252p1434 rfl) 

noncomputable def Ns252p1436 := @Enclosure.Real.IsNear.mulLit_tf qz708 (Zeta.RiemannSiegel.correction qz225) 681239 2097152 1 8388608 6748836779205 17592186044416 12445484962859 445302209249280000 4597570818628834995 36893488147419103232 

noncomputable abbrev qz712 := (@HPow.hPow Real Real Real qz7 qz224 qz9)

noncomputable def Ns252p1437 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz712 1 1 0 1 681239 2097152 1 8388608 681239 2097152 1 8388608 

noncomputable def Ns252p1438 := @Enclosure.Real.IsNear.sqrt_image qz224 1506751509153 16777216000 564289 16777216000 79496990 79497021 8388608 (@Enclosure.Real.IsNear.of_eq qz224 (@HMul.hMul Real Real Real qz5 qz223 qz3) Bool.false 1506751509153 16777216000 564289 16777216000 (BSN.t_div_two_pi_mk qz223 564289 1000 qz226) (@Enclosure.Real.IsNear.mulLit_ff qz223 qz3 564289 1000 0 1 2670177 16777216 1 16777216 1506751509153 16777216000 564289 16777216000 (Enclosure.Real.IsNear.const Bool.false 564289 1000) RS253to264.d44 rfl)) 

noncomputable abbrev qz789 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 564289 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz713 := qz789

noncomputable abbrev qz529 := qz713

noncomputable abbrev qz232 := qz529

noncomputable def Ns252p1439 := @Enclosure.Real.IsNear.sqrt_image qz232 158994011 16777216 31 16777216 25823808 25823814 8388608 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 158994011 16777216 31 16777216 158994011 16777216 31 16777216 (Ns252p1438 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns252p1440 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz232) 25823811 8388608 3 8388608 2724955 2724957 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz232) Bool.false 51647622 16777216 6 16777216 25823811 8388608 3 8388608 (Ns252p1439 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns252p1441 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 5449912 16777216 2 16777216 681239 2097152 1 8388608 (Ns252p1440 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz233 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz523))

noncomputable abbrev qz714 := (@HMul.hMul Real Real Real qz735 qz787 qz787)

noncomputable abbrev qz530 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz714 qz707) qz599)

noncomputable abbrev qz234 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz530))

noncomputable def Ns252p1442 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz225) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz233) qz234) Bool.false 6748836779205 

noncomputable def Ns252p1443 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz233) qz234 16957345 16777216 207 

noncomputable abbrev qz715 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz233))

noncomputable def Ns252p1444 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz233) (@Neg.neg Real Real.instNeg qz715) Bool.true 16957345 16777216 207 16777216 (BSN.inv_eq_neg_inv_neg qz233) 

noncomputable def Ns252p1445 := @Enclosure.Real.IsNear.recentre' qz715 Bool.false 16957345 16777216 207 16777216 16957345 16777216 

noncomputable def Ns252p1446 := @Enclosure.Real.IsNear.recentre' qz233 Bool.true 16599000 16777216 162954304 13589544960000 2074875 2097152 2546161 212336640000 

noncomputable abbrev qz235 := (@HMul.hMul Real Real Real qz346 qz343 qz523)

noncomputable def Ns252p1447 := @Enclosure.Real.IsNear.cos_image qz235 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12564905) qz377) Bool.false 12564905 4194304 49 4194304 Bool.true 16599000 16777216 1 

noncomputable def Ns252p1448 := nat_lit 836568337749076871437263641 

noncomputable def Ns252p1449 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz225 884279719003555 140737488355328 1 500000000000000 7999067 16777216 31 16777216 7073412719050609683185 2361183241434822606848 Ns252p1448 

noncomputable def Ns252p1450 := @Enclosure.Real.IsNear.subLit_ff_p qz232 qz1 158994011 16777216 31 16777216 9 1 0 1 7999067 7999067 16777216 31 

noncomputable def Ns252p1451 := @Ns252p1450 16777216 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 158994011 16777216 31 16777216 158994011 16777216 31 16777216 (Ns252p1438 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns252p1452 := @Enclosure.Real.IsNear.recentre' qz235 Bool.false 7073412719050609683185 2361183241434822606848 Ns252p1448 Ns252p168 12564905 4194304 49 4194304 (@Ns252p1449 Ns252p168 RS253to264.d43 (Ns252p1451 rfl rfl) rfl) 

noncomputable def Ns252p1453 := nat_lit 24250601896397241560487110945456504011029532319152682339226416633204884989270428223079585 

noncomputable def Ns252p1454 := nat_lit 33014095733758709603248262825248425936071420496827223503931624954848669650532735452321 

noncomputable def Ns252p1455 := nat_lit 63460029764138118557156221955430917815466564250309781098015201884657324744845497107809441 

noncomputable def Ns252p1456 := BSN.sin_dyadic_bound_f 48959550941 34359738368 3 2 16777216 6486329 Ns252p1453 Ns252p288 Ns252p1454 Ns252p1455 Ns252p291 Ns252p1454 16599000 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 48959550941) qz363 0 2 Ns252p1453 Ns252p288 Ns252p1454 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 48959550941) qz364 0 2 Ns252p1455 Ns252p291 Ns252p1454 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1457 := @Ns252p1447 3240000 (Ns252p1452 rfl) (Enclosure.sfrac_false_div 12564905 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12564905) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 861305528821177217187840) qz642) 226375608064910080 72057594037927936 Bool.false 16599000 16777216 0 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 12564905 4194304 226375608064910080 72057594037927936 0 861305528821177217187840 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16599000 16777216 861305528821177217187840 604462909807314587353088 48959550941 34359738368 6486329 6480000 (Ns252p1456 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p1458 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz233) 2074875 2097152 2546161 212336640000 8478569 8478776 8388608 (@Enclosure.Real.IsNear.neg qz233 Bool.true 2074875 2097152 2546161 212336640000 (Ns252p1446 (Ns252p1457 rfl rfl) rfl)) 

noncomputable def Ns252p1459 := Ns252p1444 (@Enclosure.Real.IsNear.neg qz715 Bool.false 16957345 16777216 207 16777216 (@Ns252p1445 207 16777216 (Ns252p1458 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p1460 := @Enclosure.Real.IsNear.recentre' qz234 Bool.true 3183912 8388608 

noncomputable abbrev qz236 := (@HMul.hMul Real Real Real qz346 qz343 qz530)

noncomputable def Ns252p1461 := @Enclosure.Real.IsNear.cos_image qz236 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16442579)) qz365) Bool.true 16442579 8388608 

noncomputable def Ns252p1462 := nat_lit 77647884118335832560332623445 

noncomputable def Ns252p1463 := nat_lit 5483769200152981536915053469819689 

noncomputable def Ns252p1464 := @Enclosure.Real.IsNear.recentre' qz236 Bool.true Ns252p1462 Ns252p183 Ns252p1463 

noncomputable abbrev qz237 := qz530

noncomputable def Ns252p1465 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz237 884279719003555 140737488355328 1 500000000000000 87809188031399 

noncomputable abbrev qz531 := (@HSub.hSub Real Real Real qz588 qz714 qz707)

noncomputable abbrev qz238 := qz531

noncomputable def Ns252p1466 := @Enclosure.Real.IsNear.subLit_tf qz238 qz31 70217001986983 281474976710656 1016036811 281474976710656 1 16 

noncomputable abbrev qz532 := qz714

noncomputable abbrev qz239 := qz532

noncomputable def Ns252p1467 := @Enclosure.Real.IsNear.subLit_ff_n qz239 qz225 63985072870489 281474976710656 495943115 281474976710656 7999067 16777216 31 16777216 

noncomputable def Ns252p1468 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz225 7999067 16777216 31 16777216 7999067 16777216 31 16777216 63985072870489 281474976710656 

noncomputable def Ns252p1469 := nat_lit 36085156308889591660819325529192475314105284552753219851011414871825402089730757245641891121 

noncomputable def Ns252p1470 := nat_lit 390516371836871565672168411387403649450619456408930166991950626357280569554764481371441 

noncomputable def Ns252p1471 := nat_lit 217643493315787599107267156207242381193675715730455245707140520252787925702222822545059159345 

noncomputable def Ns252p1472 := BSN.cos_dyadic_bound_t 16442579 8388608 4 3 8388608 3240000 Ns252p1469 Ns252p308 Ns252p1470 Ns252p1471 Ns252p311 Ns252p1470 3183912 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16442579) (BSN.cosEvenQ 8388608) 0 3 Ns252p1469 Ns252p308 Ns252p1470 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16442579) (BSN.cosOddQ 8388608) 0 3 Ns252p1471 Ns252p311 Ns252p1470 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1473 := @Ns252p1460 1251217216 54358179840000 397989 1048576 19550269 849346560000 (@Ns252p1461 381 16777216 Bool.true 3183912 8388608 1 3240000 (@Ns252p1464 Ns252p561 16442579 8388608 381 16777216 (@Ns252p1465 281474976710656 1016036811 281474976710656 Ns252p1462 Ns252p183 Ns252p1463 Ns252p561 RS253to264.d43 (@Ns252p1466 0 1 1404947008502384 87809188031399 281474976710656 1016036811 281474976710656 (@Ns252p1467 1178045809208042979328 70217001986983 281474976710656 1016036811 281474976710656 (@Ns252p1468 495943115 281474976710656 (Ns252p1451 rfl rfl) (Ns252p1451 rfl rfl) rfl) (Ns252p1451 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16442579 8388608) (BSN.cos_neg_of_bound 16442579 8388608 Bool.true 3183912 8388608 1 3240000 (Ns252p1472 rfl rfl)) rfl rfl) 

noncomputable def Ns252p1474 := @Ns252p1436 7574275844202444139 830103483316929822720000 (Ns252p1437 qz33 (@Enclosure.Real.IsNear.of_eq qz712 (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 681239 2097152 1 8388608 (BSN.rpow_neg_quarter_mk qz224 (BSN.t_div_two_pi_nonneg qz223 564289 1000 qz226)) Ns252p1441) rfl) (@Ns252p1442 17592186044416 12445484962859 445302209249280000 (BSN.correction_mk qz225 (BSN.cos_two_pi_p_ne_zero_mk qz223 564289 1000 9 qz226 rfl rfl (@BSN.floor_sqrt_eq_dec qz223 564289 1000 9 qz226 rfl rfl rfl))) (@Ns252p1443 16777216 397989 1048576 19550269 849346560000 6748836779205 17592186044416 12445484962859 445302209249280000 Ns252p1459 (Ns252p1473 rfl) rfl)) 

noncomputable def Ns252p1475 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (hardyZApproximantRS₀ qz223) Bool.false 4275432603388139187 36893488147419103232 1204274485178392524139 830103483316929822720000 (@Eq.refl Real (hardyZApproximantRS₀ qz223)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (@HMul.hMul Real Real Real qz5 qz708 (Zeta.RiemannSiegel.correction qz225))) Bool.false 4275432603388139187 36893488147419103232 1204274485178392524139 830103483316929822720000 (BSN.hardyZApproximantRS₀_eq qz223 9 (@BSN.floor_sqrt_eq_dec qz223 564289 1000 9 qz226 rfl rfl rfl)) (@Ns252p1369 4275432603388139187 36893488147419103232 1204274485178392524139 830103483316929822720000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 9)) Bool.true 292983 33554432 48373 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz223) qz223 9) (Ns252p1435 (Ns252p1434 rfl) rfl rfl)) (Ns252p1474 rfl) rfl rfl)) 

theorem RS253to264.d58 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz223) Bool.false 4275432603388139187 36893488147419103232 1204274485178392524139 830103483316929822720000 := Ns252p1475 

noncomputable def Ns252p1476 := nat_lit 7793529976150073153943502848 

noncomputable abbrev qz790 := (Enclosure.sfrac Bool.false 565685 1000)

noncomputable abbrev qz716 := qz790

noncomputable abbrev qz533 := qz716

noncomputable abbrev qz240 := qz533

noncomputable abbrev qz791 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 565685 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz717 := qz791

noncomputable abbrev qz534 := qz717

noncomputable abbrev qz241 := qz534

noncomputable abbrev qz792 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 565685 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz718 := qz792

noncomputable abbrev qz535 := qz718

noncomputable abbrev qz242 := qz535

noncomputable abbrev qz719 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz241 qz9))

noncomputable def Ns252p1477 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (@HMul.hMul Real Real Real qz5 qz719 (Zeta.RiemannSiegel.correction qz242)) 109793155 33554432 48493 33554432 9172408258033506521 73786976294838206464 1224471895235505203 138350580552821637120000 Ns252p1476 

noncomputable def Ns252p1478 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 565685 1000 118 161 134217728 67108864 2251799813685248 Bool.false 132822055894 1875 

noncomputable def Ns252p1479 := Ns252p1478 279097919 42 47453128 8 294906479 42 44739240 8 Bool.true 190408706 79359 Bool.true 181662147 Bool.true 58692703 7074237752028440 1 Bool.false 28937554 Bool.true Bool.false 56839905 Bool.true Bool.true 219586310 

noncomputable def Ns252p1480 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 565685 1000 15 70 134217728 67108864 2251799813685248 Bool.false 132822055894 1875 

noncomputable def Ns252p1481 := Ns252p1480 240485871 42 54794152 8 261175631 42 50729528 8 Bool.true 194478308 59186 Bool.true 54763330 Bool.true 163070938 7074237752028440 1 Bool.false 53256435 Bool.false Bool.false 46756366 Bool.true Bool.true 190408706 

noncomputable def Ns252p1482 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 565685 1000 130 50 134217728 67108864 2251799813685248 Bool.false 132822055894 1875 

noncomputable def Ns252p1483 := Ns252p1482 186065264 42 67108856 8 216015088 42 60023992 8 Bool.true 121049770 34885 Bool.false 159994190 Bool.false 84125132 7074237752028440 1 Bool.false 49627850 Bool.true Bool.false 108705586 Bool.true Bool.true 194478308 

noncomputable def Ns252p1484 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 565685 1000 380 234 134217728 67108864 2251799813685248 Bool.false 132822055894 1875 

noncomputable def Ns252p1485 := Ns252p1484 93032624 42 94906264 8 147453232 42 77490640 16 Bool.true 134217720 1930 Bool.false 79984615 Bool.false 76055242 7074237752028440 1 Bool.false 111082060 Bool.false Bool.false 113239624 Bool.true Bool.true 121049770 

noncomputable def Ns252p1486 := nat_lit 4205925472980114241276954996219607006119122081264163 

noncomputable def Ns252p1487 := nat_lit 4250120639367006628148282740907861219128167628800 

noncomputable def Ns252p1488 := nat_lit 27804520601481057255448185500000000 

noncomputable def Ns252p1489 := nat_lit 94371635825196845196411626697405000000 

noncomputable abbrev qz793 := (@Eq.refl Real (Enclosure.sfrac Bool.false 565685 1000))

noncomputable abbrev qz720 := qz793

noncomputable abbrev qz536 := qz720

noncomputable abbrev qz243 := qz536

noncomputable def Ns252p1490 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz240 565685 1000 1279999076900 16000000 1131370 4000 2000 Ns252p1488 Ns252p1489 qz243 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns252p1491 := nat_lit 21029627364900571206384774981098035030595610406320815000000 

noncomputable abbrev qz721 := (@HSub.hSub Real Real Real qz739 qz740 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz741 (@Nat.cast Real Real.instNatCast 1131370))))

noncomputable abbrev qz537 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 565685 4000) (Real.log (Enclosure.sfrac Bool.false 1279999076900 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz721))

noncomputable abbrev qz722 := (Enclosure.sfrac Bool.false 565685 2000)

noncomputable abbrev qz244 := (@HSub.hSub Real Real Real qz350 (@HSub.hSub Real Real Real qz350 qz537 qz722) (@HMul.hMul Real Real Real qz346 qz722 (Real.log Real.pi)))

noncomputable def Ns252p1492 := @Enclosure.Real.IsNear.addLit_ft_p qz244 (Enclosure.sfrac Bool.true Ns252p1488 Ns252p1489) 222838498475059548123 225179981368524800 463245321219007949 33177600000000000000000 Ns252p1488 Ns252p1489 0 1 Ns252p1491 

noncomputable def Ns252p1493 := nat_lit 598177539525079144275514490880 

noncomputable abbrev qz245 := (@HSub.hSub Real Real Real qz350 qz537 qz722)

noncomputable def Ns252p1494 := @Enclosure.Real.IsNear.subLit_ff_p qz245 (@HMul.hMul Real Real Real qz5 qz722 (Real.log Real.pi)) 59149376286267192927 45035996273704960 89638317908413 16200000000000000000 4345678267257 13421772800 113137 13421772800 Ns252p1493 222838498475059548123 225179981368524800 

noncomputable abbrev qz246 := qz537

noncomputable def Ns252p1495 := @Enclosure.Real.IsNear.subLit_ff_p qz246 qz722 359437350311562940379 225179981368524800 89638317908413 16200000000000000000 565685 2000 0 1 591493762862671929270000 59149376286267192927 45035996273704960 89638317908413 16200000000000000000 

noncomputable def Ns252p1496 := nat_lit 809380958463096646309460230895828992 

noncomputable def Ns252p1497 := nat_lit 27297015938241618472075264 

noncomputable def Ns252p1498 := nat_lit 16739048512926043661078791815645057217510664603433352211666282505000000000000 

noncomputable def Ns252p1499 := nat_lit 55440427073565590382883721341495317391623714237918878000080551000000000000 

noncomputable def Ns252p1500 := nat_lit 2304258721360351438787008086014749505033674023392051983215000000000000 

noncomputable def Ns252p1501 := BSN.log_dyadic_bound 231423076900 2328575076900 4 3 Ns252p1498 67108864 25920000 Ns252p1499 Ns252p1500 13383272 2559998153800 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 231423076900) (BSN.artanhQ 2328575076900) 0 3 Ns252p1499 Ns252p1498 Ns252p1500 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz538 := (Real.log (Enclosure.sfrac Bool.false 1279999076900 16000000))

noncomputable def Ns252p1502 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 565685 4000) qz538 565685 4000 0 1 3177790895365367 281474976710656 195312581 5062500000000000 359525728528951526279 225179981368524800 22097079476597 4050000000000000000 (Enclosure.Real.IsNear.const Bool.false 565685 4000) (BSN.isNear_log_sfrac 1279999076900 16000000 3177790895365367 281474976710656 195312581 5062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1279999076900) qz353)) Bool.false Ns252p1497 Ns252p93 1000000414720000 25920000000000000000000 3177790895365367 281474976710656 195312581 5062500000000000 (BSN.log_rat_reduce_isNear 1279999076900 16000000 16 2559998153800 2097152000000 13383272 67108864 24973259072661432 36028797018963968 25920000 1000000000000000 rfl rfl rfl rfl (Ns252p1501 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p1503 := BSN.arctan_dyadic_bound_f 1000 1131370 1 0 8388608 3240000 0 1 1 0 1 1 7414 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1131370) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1131370) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns252p1504 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1131370))) 884279719003555 562949953421312 1 2000000000000000 7414 8388608 1 3240000 7413702214116307894272 883782173885859 562949953421312 50000000081 162000000000000000 qz17 (Ns252p1503 rfl) rfl rfl 

noncomputable abbrev qz539 := (@HMul.hMul Real Real Real qz584 qz589 qz721)

noncomputable abbrev qz247 := qz539

noncomputable abbrev qz540 := qz721

noncomputable abbrev qz248 := qz540

noncomputable def Ns252p1505 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 565685 4000) qz538) qz247 359525728528951526279 225179981368524800 22097079476597 4050000000000000000 883782173885859 2251799813685248 50000000081 648000000000000000 Ns252p1496 359437350311562940379 225179981368524800 89638317908413 16200000000000000000 (Ns252p1502 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz248 1 4 0 1 883782173885859 562949953421312 50000000081 162000000000000000 883782173885859 2251799813685248 50000000081 648000000000000000 qz361 Ns252p1504 rfl) 

noncomputable def Ns252p1506 := @Ns252p1492 Ns252p1486 Ns252p1487 463245321219007949 33177600000000000000000 (@Ns252p1494 463245321219007949 33177600000000000000000 (Ns252p1495 (Ns252p1505 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 565685 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz722 (Real.log Real.pi) 565685 2000 0 1 38410761 33554432 1 33554432 4345678267257 13421772800 113137 13421772800 (Enclosure.Real.IsNear.const Bool.false 565685 2000) RS253to264.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns252p1488 Ns252p1489) 

noncomputable def Ns252p1507 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns252p1486 Ns252p1487 463245321219007949 33177600000000000000000 8301378493 8388608 59 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz362 qz244 (Enclosure.sfrac Bool.true Ns252p1488 Ns252p1489)) Bool.false Ns252p1486 Ns252p1487 463245321219007949 33177600000000000000000 Ns252p1490 (Ns252p1506 rfl rfl)) 

noncomputable def Ns252p1508 := nat_lit 1898669848931551292686336 

noncomputable def Ns252p1509 := nat_lit 856583417258112139254841273081336858584486022077598600456699468457927961620185592250015571262254667793602401335652308828465000000000000 

noncomputable def Ns252p1510 := nat_lit 609811748451738667880568072449452908657969480323093671700807365100670751194388670656054151219422020971775054931640625000000000000 

noncomputable def Ns252p1511 := nat_lit 4277598461871755019203673164401163774164450944659988620065731328358972522100510367472993510331263966183242592538041817579825000000000000 

noncomputable def Ns252p1512 := BSN.sin_dyadic_bound_f 53963442750 34359738368 4 3 16777216 6486329 Ns252p1509 Ns252p107 Ns252p1510 Ns252p1511 Ns252p110 Ns252p1510 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53963442750) qz363 0 3 Ns252p1509 Ns252p107 Ns252p1510 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53963442750) qz364 0 3 Ns252p1511 Ns252p110 Ns252p1510 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1513 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz240) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8301378493) qz365) Bool.false 8301378493 8388608 59 4194304 Bool.true 16777215 16777216 1 3240000 (Ns252p1507 rfl) (Enclosure.sfrac_false_div 8301378493 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8301378493) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns252p1508) qz366) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 157 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 8301378493 8388608 226375608064910080 72057594037927936 157 Ns252p1508 Ns252p105 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns252p1508 Ns252p105 53963442750 34359738368 6486329 6480000 (Ns252p1512 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p1514 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns252p1486 Ns252p1487 463245321219007949 33177600000000000000000 132822055894 134217728 1875 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz362 qz244 (Enclosure.sfrac Bool.true Ns252p1488 Ns252p1489)) Bool.false Ns252p1486 Ns252p1487 463245321219007949 33177600000000000000000 Ns252p1490 (Ns252p1506 rfl rfl)) 

noncomputable def Ns252p1515 := Ns252p1485 34885 BSN.abs_quadSignPos (BSN.cos_quad_nat0 380 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 111082060 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 234 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 113239624 134217728) qz243 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) Bool.true 16777215 16777216 3052411 212336640000 134217720 134217728 1930 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 16777215 16777216 3052411 212336640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz240) qz240) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 16777215 16777216 195354304 13589544960000 16777215 16777216 3052411 212336640000 (Ns252p1513 rfl rfl) rfl)) rfl) (Ns252p1514 rfl) RS253to264.d7 

noncomputable def Ns252p1516 := nat_lit 22315532280990633858125616296209364296417535611019283429749208690625 

noncomputable def Ns252p1517 := nat_lit 1675142162022869540933048031533190770530610978934351570187890625 

noncomputable def Ns252p1518 := nat_lit 66943246558647855835294982792565026507711545611099981586107250290625 

noncomputable def Ns252p1519 := BSN.cos_dyadic_bound_f 79984615 134217728 3 2 134217728 67108864 Ns252p1516 Ns252p144 Ns252p1517 Ns252p1518 Ns252p147 Ns252p1517 111082060 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 79984615) qz369 0 2 Ns252p1516 Ns252p144 Ns252p1517 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 79984615) qz370 0 2 Ns252p1518 Ns252p147 Ns252p1517 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1520 := nat_lit 18242824334396592055316270627031107494322164449235086468999678320896 

noncomputable def Ns252p1521 := nat_lit 1119523515752460595131148850739595801070189558901353117591593216 

noncomputable def Ns252p1522 := nat_lit 54726233956158271244758549583391843291364352968587456700763851776256 

noncomputable def Ns252p1523 := BSN.cos_dyadic_bound_f 76055242 134217728 3 2 134217728 67108864 Ns252p1520 Ns252p144 Ns252p1521 Ns252p1522 Ns252p147 Ns252p1521 113239624 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 76055242) qz369 0 2 Ns252p1520 Ns252p144 Ns252p1521 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 76055242) qz370 0 2 Ns252p1522 Ns252p147 Ns252p1521 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1524 := nat_lit 1378933705801126019723110171017193376526632501187174807121526487531786252137595432059579085255882304000000 

noncomputable def Ns252p1525 := nat_lit 281352348482637673917071381926290957440506692404526874279571291208380866260060971649361000000000000 

noncomputable def Ns252p1526 := nat_lit 8358834754431363771981033601044634476462551452597134202907913712273284352632153695550867559056265177600000 

noncomputable def Ns252p1527 := BSN.cos_dyadic_bound_f 159994190 134217728 4 3 134217728 67108864 Ns252p1524 Ns252p398 Ns252p1525 Ns252p1526 Ns252p401 Ns252p1525 49627850 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 159994190) qz369 0 3 Ns252p1524 Ns252p398 Ns252p1525 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 159994190) qz370 0 3 Ns252p1526 Ns252p401 Ns252p1525 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1528 := nat_lit 27308116262726252990816522627007856993678276260115158667106420064256 

noncomputable def Ns252p1529 := nat_lit 2508453584663858446401399000585670279965958351767794163269042176 

noncomputable def Ns252p1530 := nat_lit 81919331881009431255556765083022399640474896863641940412992722108416 

noncomputable def Ns252p1531 := BSN.cos_dyadic_bound_f 84125132 134217728 3 2 134217728 67108864 Ns252p1528 Ns252p144 Ns252p1529 Ns252p1530 Ns252p147 Ns252p1529 108705586 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 84125132) qz369 0 2 Ns252p1528 Ns252p144 Ns252p1529 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 84125132) qz370 0 2 Ns252p1530 Ns252p147 Ns252p1529 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1532 := Ns252p1483 59186 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 130 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 49627850 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 50 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 108705586 134217728) qz243 rfl rfl (Ns252p1515 RS253to264.d9 RS253to264.d11 RS253to264.d13 RS253to264.d17 (Ns252p1519 rfl rfl) (Ns252p1523 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns252p1514 rfl) RS253to264.d19 RS253to264.d21 RS253to264.d23 RS253to264.d25 RS253to264.d17 (Ns252p1527 rfl rfl) (Ns252p1531 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns252p1533 := nat_lit 8994134832005878285948183210000 

noncomputable def Ns252p1534 := BSN.sin_dyadic_bound_f 54763330 134217728 2 1 134217728 67108864 Ns252p1533 Ns252p238 Ns252p1533 Ns252p1533 Ns252p239 Ns252p1533 53256435 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 54763330) qz367 0 1 Ns252p1533 Ns252p238 Ns252p1533 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 54763330) qz368 0 1 Ns252p1533 Ns252p239 Ns252p1533 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1535 := nat_lit 1488243875007247061646295411195942155623531435610779073019999745602369167861926490668701047240685762318336 

noncomputable def Ns252p1536 := nat_lit 353605353696917438103316711125367169928418209602189534945606732798893403422713290968694739123245056 

noncomputable def Ns252p1537 := nat_lit 9020880719167459920151190591689914853833149292608022107742466040698159046105725060663821508672990306570240 

noncomputable def Ns252p1538 := BSN.cos_dyadic_bound_f 163070938 134217728 4 3 134217728 67108864 Ns252p1535 Ns252p398 Ns252p1536 Ns252p1537 Ns252p401 Ns252p1536 46756366 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 163070938) qz369 0 3 Ns252p1535 Ns252p398 Ns252p1536 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 163070938) qz370 0 3 Ns252p1537 Ns252p401 Ns252p1536 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1539 := Ns252p1481 79359 BSN.abs_quadSignPos (BSN.cos_quad_nat3 15 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 53256435 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 70 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 46756366 134217728) qz243 rfl rfl (Ns252p1532 rfl rfl) (Ns252p1514 rfl) RS253to264.d27 RS253to264.d29 RS253to264.d31 RS253to264.d33 RS253to264.d17 (Ns252p1534 rfl rfl) (Ns252p1538 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p1540 := nat_lit 2293662336063898791345297565055494961540301290667116501910590756855867754247874449894375725285333219054321 

noncomputable def Ns252p1541 := nat_lit 1291734657219934543231685742415139737532003345338214854015535240401748607853651731789407804164313841 

noncomputable def Ns252p1542 := nat_lit 13896384313821398282073357180533094337812331243953984926556671941339495748766680305882405969066437603398385 

noncomputable def Ns252p1543 := BSN.cos_dyadic_bound_f 181662147 134217728 4 3 134217728 67108864 Ns252p1540 Ns252p398 Ns252p1541 Ns252p1542 Ns252p401 Ns252p1541 28937554 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 181662147) qz369 0 3 Ns252p1540 Ns252p398 Ns252p1541 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 181662147) qz370 0 3 Ns252p1542 Ns252p401 Ns252p1541 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1544 := nat_lit 11866877053484789544974032471681 

noncomputable def Ns252p1545 := BSN.sin_dyadic_bound_f 58692703 134217728 2 1 134217728 67108864 Ns252p1544 Ns252p238 Ns252p1544 Ns252p1544 Ns252p239 Ns252p1544 56839905 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 58692703) qz367 0 1 Ns252p1544 Ns252p238 Ns252p1544 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 58692703) qz368 0 1 Ns252p1544 Ns252p239 Ns252p1544 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1546 := Ns252p1479 96986 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 118 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 28937554 134217728) BSN.abs_quadSignNeg qz371 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 56839905 134217728) qz243 rfl rfl (Ns252p1539 rfl) (Ns252p1514 rfl) RS253to264.d35 RS253to264.d37 RS253to264.d39 RS253to264.d41 RS253to264.d17 (Ns252p1543 rfl rfl) (Ns252p1545 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns252p1547 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) 219586310 134217728 96986 134217728 219586310 134217728 96986 134217728 58944751256207360 109793155 33554432 48493 33554432 (Ns252p1546 rfl) 

noncomputable def Ns252p1548 := @Enclosure.Real.IsNear.mulLit_tf qz719 (Zeta.RiemannSiegel.correction qz242) 2723273 8388608 1 8388608 3368155986577 8796093022208 1509682292093 55662776156160000 9172408258033506521 73786976294838206464 

noncomputable abbrev qz723 := (@HPow.hPow Real Real Real qz7 qz241 qz9)

noncomputable def Ns252p1549 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz723 1 1 0 1 2723273 8388608 1 8388608 2723273 8388608 1 8388608 

noncomputable def Ns252p1550 := @Enclosure.Real.IsNear.sqrt_image qz241 302095815249 3355443200 113137 3355443200 79595264 79595294 8388608 (@Enclosure.Real.IsNear.of_eq qz241 (@HMul.hMul Real Real Real qz5 qz240 qz3) Bool.false 302095815249 3355443200 113137 3355443200 (BSN.t_div_two_pi_mk qz240 565685 1000 qz243) (@Enclosure.Real.IsNear.mulLit_ff qz240 qz3 565685 1000 0 1 2670177 16777216 1 16777216 302095815249 3355443200 113137 3355443200 (Enclosure.Real.IsNear.const Bool.false 565685 1000) RS253to264.d44 rfl)) 

noncomputable abbrev qz794 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 565685 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz724 := qz794

noncomputable abbrev qz541 := qz724

noncomputable abbrev qz249 := qz541

noncomputable def Ns252p1551 := @Enclosure.Real.IsNear.sqrt_image qz249 79595279 8388608 15 8388608 25839765 25839771 8388608 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 159190558 16777216 30 16777216 79595279 8388608 15 8388608 (Ns252p1550 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns252p1552 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz249) 3229971 1048576 3 8388608 2723272 2723274 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz249) Bool.false 51679536 16777216 6 16777216 3229971 1048576 3 8388608 (Ns252p1551 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns252p1553 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 5446546 16777216 2 16777216 2723273 8388608 1 8388608 (Ns252p1552 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz535))

noncomputable abbrev qz725 := (@HMul.hMul Real Real Real qz735 qz792 qz792)

noncomputable abbrev qz542 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz725 qz718) qz599)

noncomputable abbrev qz251 := (Real.cos (@HMul.hMul Real Real Real qz346 qz343 qz542))

noncomputable def Ns252p1554 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz242) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz250) qz251) Bool.false 3368155986577 

noncomputable def Ns252p1555 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz250) qz251 1051321 1048576 49 

noncomputable abbrev qz726 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz250))

noncomputable def Ns252p1556 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz250) (@Neg.neg Real Real.instNeg qz726) Bool.true 1051321 1048576 49 4194304 (BSN.inv_eq_neg_inv_neg qz250) 

noncomputable def Ns252p1557 := @Enclosure.Real.IsNear.recentre' qz726 Bool.false 16821136 16777216 196 16777216 1051321 1048576 

noncomputable def Ns252p1558 := @Enclosure.Real.IsNear.recentre' qz250 Bool.true 16733411 16777216 629137216 54358179840000 16733411 16777216 9830269 849346560000 

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz346 qz343 qz535)

noncomputable def Ns252p1559 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51494561) qz410) Bool.false 51494561 16777216 189 16777216 Bool.true 16733411 16777216 1 

noncomputable def Ns252p1560 := nat_lit 404791131170860575928174249 

noncomputable def Ns252p1561 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz242 884279719003555 140737488355328 1 500000000000000 4097807 8388608 15 8388608 3623607622490800703885 1180591620717411303424 Ns252p1560 

noncomputable def Ns252p1562 := @Enclosure.Real.IsNear.subLit_ff_p qz249 qz1 79595279 8388608 15 8388608 9 1 0 1 4097807 4097807 8388608 15 

noncomputable def Ns252p1563 := @Ns252p1562 8388608 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 159190558 16777216 30 16777216 79595279 8388608 15 8388608 (Ns252p1550 rfl rfl rfl rfl rfl rfl) rfl) qz376 

noncomputable def Ns252p1564 := @Enclosure.Real.IsNear.recentre' qz252 Bool.false 3623607622490800703885 1180591620717411303424 Ns252p1560 Ns252p282 51494561 16777216 189 16777216 (@Ns252p1561 Ns252p282 RS253to264.d43 (Ns252p1563 rfl rfl) rfl) 

noncomputable def Ns252p1565 := nat_lit 3623195869762294395174912 

noncomputable def Ns252p1566 := nat_lit 29672409411645344241469166555930028951308025106835969104431870390002623753991959182132385 

noncomputable def Ns252p1567 := nat_lit 49396490723930145237700121220345472166332490639627395686588521384091161810664872821921 

noncomputable def Ns252p1568 := nat_lit 77633477950280014682986778878793326012775527437820522347162326748718343188952149968635041 

noncomputable def Ns252p1569 := BSN.sin_dyadic_bound_f 51488710109 34359738368 3 2 16777216 6486329 Ns252p1566 Ns252p288 Ns252p1567 Ns252p1568 Ns252p291 Ns252p1567 16733411 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 51488710109) qz363 0 2 Ns252p1566 Ns252p288 Ns252p1567 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 51488710109) qz364 0 2 Ns252p1568 Ns252p291 Ns252p1567 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1570 := @Ns252p1559 3240000 (Ns252p1564 rfl) (Enclosure.sfrac_false_div 51494561 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51494561) qz410) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns252p1565) qz411) 226375608064910080 72057594037927936 Bool.false 16733411 16777216 0 1000000000000000 6480000 3240000 (BSN.sin_reduce_arg_pos_rat_q1 51494561 16777216 226375608064910080 72057594037927936 0 Ns252p1565 Ns252p93 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16733411 16777216 Ns252p1565 Ns252p93 51488710109 34359738368 6486329 6480000 (Ns252p1569 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns252p1571 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz250) 16733411 16777216 9830269 849346560000 8410470 8410666 8388608 (@Enclosure.Real.IsNear.neg qz250 Bool.true 16733411 16777216 9830269 849346560000 (Ns252p1558 (Ns252p1570 rfl rfl) rfl)) 

noncomputable def Ns252p1572 := Ns252p1556 (@Enclosure.Real.IsNear.neg qz726 Bool.false 1051321 1048576 49 4194304 (@Ns252p1557 49 4194304 (Ns252p1571 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns252p1573 := @Enclosure.Real.IsNear.recentre' qz251 Bool.true 3203737 8388608 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz346 qz343 qz542)

noncomputable def Ns252p1574 := @Enclosure.Real.IsNear.cos_image qz253 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32928037)) qz410) Bool.true 32928037 16777216 

noncomputable def Ns252p1575 := nat_lit 19437282543194760706153436605 

noncomputable def Ns252p1576 := nat_lit 6713152054440690571679301632502197 

noncomputable def Ns252p1577 := @Enclosure.Real.IsNear.recentre' qz253 Bool.true Ns252p1575 Ns252p449 Ns252p1576 

noncomputable abbrev qz254 := qz542

noncomputable def Ns252p1578 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz254 884279719003555 140737488355328 1 500000000000000 21980920884511 

noncomputable abbrev qz543 := (@HSub.hSub Real Real Real qz588 qz725 qz718)

noncomputable abbrev qz255 := qz543

noncomputable def Ns252p1579 := @Enclosure.Real.IsNear.subLit_tf qz255 qz31 17582874373407 70368744177664 248763555 70368744177664 1 16 

noncomputable abbrev qz544 := qz725

noncomputable abbrev qz256 := qz544

noncomputable def Ns252p1580 := @Enclosure.Real.IsNear.subLit_ff_n qz256 qz242 16792022209249 70368744177664 122934435 70368744177664 4097807 8388608 15 8388608 

noncomputable def Ns252p1581 := @Enclosure.Real.IsNear.mulLit_ff qz242 qz242 4097807 8388608 15 8388608 4097807 8388608 15 8388608 16792022209249 70368744177664 

noncomputable def Ns252p1582 := nat_lit 148583980222465667379026625619923368339255348828826302970283796038953707441587665285382870890961 

noncomputable def Ns252p1583 := nat_lit 1624763271161619378195904953115837732134190889113958541855861795389521985973280715847203281 

noncomputable def Ns252p1584 := nat_lit 896140086456564988088899013106420347524663273493946402403225602391430737319008494849976085739985 

noncomputable def Ns252p1585 := BSN.cos_dyadic_bound_t 32928037 16777216 4 3 8388608 3240000 Ns252p1582 Ns252p567 Ns252p1583 Ns252p1584 Ns252p570 Ns252p1583 3203737 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32928037) (BSN.cosEvenQ 16777216) 0 3 Ns252p1582 Ns252p567 Ns252p1583 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32928037) (BSN.cosOddQ 16777216) 0 3 Ns252p1584 Ns252p570 Ns252p1583 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns252p1586 := @Ns252p1573 614268608 27179089920000 3203737 8388608 9597947 424673280000 (@Ns252p1574 187 8388608 Bool.true 3203737 8388608 1 3240000 (@Ns252p1577 Ns252p302 32928037 16777216 187 8388608 (@Ns252p1578 70368744177664 248763555 70368744177664 Ns252p1575 Ns252p449 Ns252p1576 Ns252p302 RS253to264.d43 (@Ns252p1579 0 1 351694734152176 21980920884511 70368744177664 248763555 70368744177664 (@Ns252p1580 147495840631756947456 17582874373407 70368744177664 248763555 70368744177664 (@Ns252p1581 122934435 70368744177664 (Ns252p1563 rfl rfl) (Ns252p1563 rfl rfl) rfl) (Ns252p1563 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32928037 16777216) (BSN.cos_neg_of_bound 32928037 16777216 Bool.true 3203737 8388608 1 3240000 (Ns252p1585 rfl rfl)) rfl rfl) 

noncomputable def Ns252p1587 := @Ns252p1548 1224471895235505203 138350580552821637120000 (Ns252p1549 qz33 (@Enclosure.Real.IsNear.of_eq qz723 (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 2723273 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz241 (BSN.t_div_two_pi_nonneg qz240 565685 1000 qz243)) Ns252p1553) rfl) (@Ns252p1554 8796093022208 1509682292093 55662776156160000 (BSN.correction_mk qz242 (BSN.cos_two_pi_p_ne_zero_mk qz240 565685 1000 9 qz243 rfl rfl (@BSN.floor_sqrt_eq_dec qz240 565685 1000 9 qz243 rfl rfl rfl))) (@Ns252p1555 4194304 3203737 8388608 9597947 424673280000 3368155986577 8796093022208 1509682292093 55662776156160000 Ns252p1572 (Ns252p1586 rfl) rfl)) 

noncomputable def Ns252p1588 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (hardyZApproximantRS₀ qz240) Bool.true 232265292887391840039 73786976294838206464 201169287016766385203 138350580552821637120000 (@Eq.refl Real (hardyZApproximantRS₀ qz240)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (@HMul.hMul Real Real Real qz5 qz719 (Zeta.RiemannSiegel.correction qz242))) Bool.true 232265292887391840039 73786976294838206464 201169287016766385203 138350580552821637120000 (BSN.hardyZApproximantRS₀_eq qz240 9 (@BSN.floor_sqrt_eq_dec qz240 565685 1000 9 qz243 rfl rfl rfl)) (@Ns252p1477 232265292887391840039 73786976294838206464 201169287016766385203 138350580552821637120000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (@HAdd.hAdd Real Real Real qz362 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 9)) Bool.true 109793155 33554432 48493 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz240) qz240 9) (Ns252p1547 (Ns252p1546 rfl) rfl rfl)) (Ns252p1587 rfl) rfl rfl)) 

theorem RS253to264.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz240) Bool.true 232265292887391840039 73786976294838206464 201169287016766385203 138350580552821637120000 := Ns252p1588 

noncomputable def RS253to264.d60 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz545 := (RS253to264.d3 qz583 qz600 (@Enclosure.dec_le_dec qz583 qz600 548874 1000 550280 1000 (@Eq.refl Real qz583) qz604 rfl rfl rfl))

noncomputable abbrev qz257 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz545)

noncomputable def Ns252p1589 := @Enclosure.Real.IsNear.of_eq qz257 (hardyZApproximantRS₀ qz4) Bool.true 1104795413732038754515 590295810358705651712 42335503798320048298897 Ns252p69 

noncomputable abbrev qz546 := (@Enclosure.dec_le_dec qz583 qz600 548874 1000 550280 1000 (@Eq.refl Real qz583) qz604 rfl rfl rfl)

noncomputable abbrev qz258 := qz546

noncomputable def Ns252p1590 := @Enclosure.Real.IsNear.neg_val qz257 1104795413732038754515 590295810358705651712 42335503798320048298897 Ns252p69 (Ns252p1589 (RS253to264.d4 qz4 qz35 qz258) RS253to264.d45) rfl 

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz545)

noncomputable def Ns252p1591 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantRS₀ qz35) Bool.false 2325510212757170209915 1180591620717411303424 28263396928803313124039 Ns252p200 

noncomputable def Ns252p1592 := @Enclosure.Real.IsNear.pos_val qz259 2325510212757170209915 1180591620717411303424 28263396928803313124039 Ns252p200 (Ns252p1591 (RS253to264.d46 qz4 qz35 qz258) RS253to264.d47) rfl 

noncomputable def Ns252p1593 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz257 qz4 qz4 548874 1000 548874 1000 

noncomputable def Ns252p1594 := @Enclosure.norm_gt_of_isNear qz257 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1104795413732038754515 590295810358705651712 42335503798320048298897 

noncomputable def Ns252p1595 := @Ns252p1594 Ns252p69 184948413 2684354560 1213 2684354560 (Ns252p1589 (RS253to264.d4 qz4 qz35 qz258) RS253to264.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable def Ns252p1596 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz259 qz4 qz35 548874 1000 550280 1000 

noncomputable def Ns252p1597 := @Enclosure.norm_gt_of_isNear qz259 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2325510212757170209915 1180591620717411303424 28263396928803313124039 

noncomputable def Ns252p1598 := @Ns252p1597 Ns252p200 184948413 2684354560 1213 2684354560 (Ns252p1591 (RS253to264.d46 qz4 qz35 qz258) RS253to264.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable abbrev qz260 := qz545

noncomputable def Ns252p1599 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz260 (@BSN.thirtyTwoPi_le_dec qz4 548874 1000 qz11 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz257 qz259 (Ns252p1590 rfl rfl) (Ns252p1592 rfl rfl)) (Ns252p1593 qz11 qz11 rfl rfl rfl rfl (Ns252p1595 rfl)) (Ns252p1596 qz11 qz38 rfl rfl rfl rfl (Ns252p1598 rfl)) 

noncomputable abbrev qz547 := (RS253to264.d3 qz600 qz612 (@Enclosure.dec_le_dec qz600 qz612 550280 1000 551684 1000 qz604 qz616 rfl rfl rfl))

noncomputable abbrev qz261 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz547)

noncomputable def Ns252p1600 := @Enclosure.Real.IsNear.of_eq qz261 (hardyZApproximantRS₀ qz35) Bool.false 2325510212757170209915 1180591620717411303424 28263396928803313124039 Ns252p200 

noncomputable abbrev qz548 := (@Enclosure.dec_le_dec qz600 qz612 550280 1000 551684 1000 qz604 qz616 rfl rfl rfl)

noncomputable abbrev qz262 := qz548

noncomputable def Ns252p1601 := @Enclosure.Real.IsNear.pos_val qz261 2325510212757170209915 1180591620717411303424 28263396928803313124039 Ns252p200 (Ns252p1600 (RS253to264.d4 qz35 qz62 qz262) RS253to264.d47) rfl 

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz547)

noncomputable def Ns252p1602 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantRS₀ qz62) Bool.true 178290976032282583919 147573952589676412928 1698964951137631612051 1195349015976378944716800 

noncomputable def Ns252p1603 := @Enclosure.Real.IsNear.neg_val qz263 178290976032282583919 147573952589676412928 1698964951137631612051 1195349015976378944716800 (Ns252p1602 (RS253to264.d46 qz35 qz62 qz262) RS253to264.d49) rfl 

noncomputable def Ns252p1604 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz261 qz4 qz35 548874 1000 550280 1000 

noncomputable def Ns252p1605 := @Enclosure.norm_gt_of_isNear qz261 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2325510212757170209915 1180591620717411303424 28263396928803313124039 

noncomputable def Ns252p1606 := @Ns252p1605 Ns252p200 184948413 2684354560 1213 2684354560 (Ns252p1600 (RS253to264.d4 qz35 qz62 qz262) RS253to264.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable def Ns252p1607 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz263 qz4 qz62 548874 1000 551684 1000 

noncomputable def Ns252p1608 := @Enclosure.norm_gt_of_isNear qz263 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 178290976032282583919 147573952589676412928 1698964951137631612051 

noncomputable def Ns252p1609 := @Ns252p1608 1195349015976378944716800 184948413 2684354560 1213 2684354560 (Ns252p1602 (RS253to264.d46 qz35 qz62 qz262) RS253to264.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable abbrev qz264 := qz547

noncomputable def Ns252p1610 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz264 (@BSN.thirtyTwoPi_le_dec qz35 550280 1000 qz38 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz261 qz263 (Ns252p1601 rfl rfl) (Ns252p1603 rfl rfl)) (Ns252p1604 qz11 qz38 rfl rfl rfl rfl (Ns252p1606 rfl)) (Ns252p1607 qz11 qz65 rfl rfl rfl rfl (Ns252p1609 rfl)) 

noncomputable abbrev qz549 := (RS253to264.d3 qz612 qz622 (@Enclosure.dec_le_dec qz612 qz622 551684 1000 553088 1000 qz616 qz626 rfl rfl rfl))

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz549)

noncomputable def Ns252p1611 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantRS₀ qz62) Bool.true 178290976032282583919 147573952589676412928 1698964951137631612051 1195349015976378944716800 

noncomputable abbrev qz550 := (@Enclosure.dec_le_dec qz612 qz622 551684 1000 553088 1000 qz616 qz626 rfl rfl rfl)

noncomputable abbrev qz266 := qz550

noncomputable def Ns252p1612 := @Enclosure.Real.IsNear.neg_val qz265 178290976032282583919 147573952589676412928 1698964951137631612051 1195349015976378944716800 (Ns252p1611 (RS253to264.d4 qz62 qz80 qz266) RS253to264.d49) rfl 

noncomputable abbrev qz267 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz549)

noncomputable def Ns252p1613 := @Enclosure.Real.IsNear.of_eq qz267 (hardyZApproximantRS₀ qz80) Bool.false 4213083805946035226165 1180591620717411303424 9458986542869597323823 Ns252p465 

noncomputable def Ns252p1614 := @Enclosure.Real.IsNear.pos_val qz267 4213083805946035226165 1180591620717411303424 9458986542869597323823 Ns252p465 (Ns252p1613 (RS253to264.d46 qz62 qz80 qz266) RS253to264.d50) rfl 

noncomputable def Ns252p1615 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz265 qz4 qz62 548874 1000 551684 1000 

noncomputable def Ns252p1616 := @Enclosure.norm_gt_of_isNear qz265 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 178290976032282583919 147573952589676412928 1698964951137631612051 

noncomputable def Ns252p1617 := @Ns252p1616 1195349015976378944716800 184948413 2684354560 1213 2684354560 (Ns252p1611 (RS253to264.d4 qz62 qz80 qz266) RS253to264.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable def Ns252p1618 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz267 qz4 qz80 548874 1000 553088 1000 

noncomputable def Ns252p1619 := @Enclosure.norm_gt_of_isNear qz267 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 4213083805946035226165 1180591620717411303424 9458986542869597323823 

noncomputable def Ns252p1620 := @Ns252p1619 Ns252p465 184948413 2684354560 1213 2684354560 (Ns252p1613 (RS253to264.d46 qz62 qz80 qz266) RS253to264.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable abbrev qz268 := qz549

noncomputable def Ns252p1621 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz62 551684 1000 qz65 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz265 qz267 (Ns252p1612 rfl rfl) (Ns252p1614 rfl rfl)) (Ns252p1615 qz11 qz65 rfl rfl rfl rfl (Ns252p1617 rfl)) (Ns252p1618 qz11 qz83 rfl rfl rfl rfl (Ns252p1620 rfl)) 

noncomputable abbrev qz551 := (RS253to264.d3 qz622 qz632 (@Enclosure.dec_le_dec qz622 qz632 553088 1000 554491 1000 qz626 qz636 rfl rfl rfl))

noncomputable abbrev qz269 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz551)

noncomputable def Ns252p1622 := @Enclosure.Real.IsNear.of_eq qz269 (hardyZApproximantRS₀ qz80) Bool.false 4213083805946035226165 1180591620717411303424 9458986542869597323823 Ns252p465 

noncomputable abbrev qz552 := (@Enclosure.dec_le_dec qz622 qz632 553088 1000 554491 1000 qz626 qz636 rfl rfl rfl)

noncomputable abbrev qz270 := qz552

noncomputable def Ns252p1623 := @Enclosure.Real.IsNear.pos_val qz269 4213083805946035226165 1180591620717411303424 9458986542869597323823 Ns252p465 (Ns252p1622 (RS253to264.d4 qz80 qz98 qz270) RS253to264.d50) rfl 

noncomputable abbrev qz271 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz551)

noncomputable def Ns252p1624 := @Enclosure.Real.IsNear.of_eq qz271 (hardyZApproximantRS₀ qz98) Bool.true 10178331693137715349593 2361183241434822606848 758331035088464597509 531266229322835086540800 

noncomputable def Ns252p1625 := @Enclosure.Real.IsNear.neg_val qz271 10178331693137715349593 2361183241434822606848 758331035088464597509 531266229322835086540800 (Ns252p1624 (RS253to264.d46 qz80 qz98 qz270) RS253to264.d51) rfl 

noncomputable def Ns252p1626 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz269 qz4 qz80 548874 1000 553088 1000 

noncomputable def Ns252p1627 := @Enclosure.norm_gt_of_isNear qz269 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 4213083805946035226165 1180591620717411303424 9458986542869597323823 

noncomputable def Ns252p1628 := @Ns252p1627 Ns252p465 184948413 2684354560 1213 2684354560 (Ns252p1622 (RS253to264.d4 qz80 qz98 qz270) RS253to264.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable def Ns252p1629 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz271 qz4 qz98 548874 1000 554491 1000 

noncomputable def Ns252p1630 := @Enclosure.norm_gt_of_isNear qz271 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 10178331693137715349593 2361183241434822606848 758331035088464597509 

noncomputable def Ns252p1631 := @Ns252p1630 531266229322835086540800 184948413 2684354560 1213 2684354560 (Ns252p1624 (RS253to264.d46 qz80 qz98 qz270) RS253to264.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable abbrev qz272 := qz551

noncomputable def Ns252p1632 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz80 553088 1000 qz83 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz269 qz271 (Ns252p1623 rfl rfl) (Ns252p1625 rfl rfl)) (Ns252p1626 qz11 qz83 rfl rfl rfl rfl (Ns252p1628 rfl)) (Ns252p1629 qz11 qz101 rfl rfl rfl rfl (Ns252p1631 rfl)) 

noncomputable abbrev qz553 := (RS253to264.d3 qz632 qz643 (@Enclosure.dec_le_dec qz632 qz643 554491 1000 555893 1000 qz636 qz647 rfl rfl rfl))

noncomputable abbrev qz273 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz553)

noncomputable def Ns252p1633 := @Enclosure.Real.IsNear.of_eq qz273 (hardyZApproximantRS₀ qz98) Bool.true 10178331693137715349593 2361183241434822606848 758331035088464597509 531266229322835086540800 

noncomputable abbrev qz554 := (@Enclosure.dec_le_dec qz632 qz643 554491 1000 555893 1000 qz636 qz647 rfl rfl rfl)

noncomputable abbrev qz274 := qz554

noncomputable def Ns252p1634 := @Enclosure.Real.IsNear.neg_val qz273 10178331693137715349593 2361183241434822606848 758331035088464597509 531266229322835086540800 (Ns252p1633 (RS253to264.d4 qz98 qz116 qz274) RS253to264.d51) rfl 

noncomputable abbrev qz275 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz553)

noncomputable def Ns252p1635 := @Enclosure.Real.IsNear.of_eq qz275 (hardyZApproximantRS₀ qz116) Bool.false 12661266550463554623 36893488147419103232 10684358235265574430473 Ns252p684 

noncomputable def Ns252p1636 := @Enclosure.Real.IsNear.pos_val qz275 12661266550463554623 36893488147419103232 10684358235265574430473 Ns252p684 (Ns252p1635 (RS253to264.d46 qz98 qz116 qz274) RS253to264.d52) rfl 

noncomputable def Ns252p1637 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz273 qz4 qz98 548874 1000 554491 1000 

noncomputable def Ns252p1638 := @Enclosure.norm_gt_of_isNear qz273 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 10178331693137715349593 2361183241434822606848 758331035088464597509 

noncomputable def Ns252p1639 := @Ns252p1638 531266229322835086540800 184948413 2684354560 1213 2684354560 (Ns252p1633 (RS253to264.d4 qz98 qz116 qz274) RS253to264.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable def Ns252p1640 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz275 qz4 qz116 548874 1000 555893 1000 

noncomputable def Ns252p1641 := @Enclosure.norm_gt_of_isNear qz275 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 12661266550463554623 36893488147419103232 10684358235265574430473 

noncomputable def Ns252p1642 := @Ns252p1641 Ns252p684 184948413 2684354560 1213 2684354560 (Ns252p1635 (RS253to264.d46 qz98 qz116 qz274) RS253to264.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable abbrev qz276 := qz553

noncomputable def Ns252p1643 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz98 554491 1000 qz101 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz273 qz275 (Ns252p1634 rfl rfl) (Ns252p1636 rfl rfl)) (Ns252p1637 qz11 qz101 rfl rfl rfl rfl (Ns252p1639 rfl)) (Ns252p1640 qz11 qz119 rfl rfl rfl rfl (Ns252p1642 rfl)) 

noncomputable abbrev qz555 := (RS253to264.d3 qz643 qz654 (@Enclosure.dec_le_dec qz643 qz654 555893 1000 557294 1000 qz647 qz658 rfl rfl rfl))

noncomputable abbrev qz277 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz555)

noncomputable def Ns252p1644 := @Enclosure.Real.IsNear.of_eq qz277 (hardyZApproximantRS₀ qz116) Bool.false 12661266550463554623 36893488147419103232 10684358235265574430473 Ns252p684 

noncomputable abbrev qz556 := (@Enclosure.dec_le_dec qz643 qz654 555893 1000 557294 1000 qz647 qz658 rfl rfl rfl)

noncomputable abbrev qz278 := qz556

noncomputable def Ns252p1645 := @Enclosure.Real.IsNear.pos_val qz277 12661266550463554623 36893488147419103232 10684358235265574430473 Ns252p684 (Ns252p1644 (RS253to264.d4 qz116 qz134 qz278) RS253to264.d52) rfl 

noncomputable abbrev qz279 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz555)

noncomputable def Ns252p1646 := @Enclosure.Real.IsNear.of_eq qz279 (hardyZApproximantRS₀ qz134) Bool.true 88615053386996215767 295147905179352825856 4284465405702772351379 Ns252p796 

noncomputable def Ns252p1647 := @Enclosure.Real.IsNear.neg_val qz279 88615053386996215767 295147905179352825856 4284465405702772351379 Ns252p796 (Ns252p1646 (RS253to264.d46 qz116 qz134 qz278) RS253to264.d53) rfl 

noncomputable def Ns252p1648 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz277 qz4 qz116 548874 1000 555893 1000 

noncomputable def Ns252p1649 := @Enclosure.norm_gt_of_isNear qz277 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 12661266550463554623 36893488147419103232 10684358235265574430473 

noncomputable def Ns252p1650 := @Ns252p1649 Ns252p684 184948413 2684354560 1213 2684354560 (Ns252p1644 (RS253to264.d4 qz116 qz134 qz278) RS253to264.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable def Ns252p1651 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz279 qz4 qz134 548874 1000 557294 1000 

noncomputable def Ns252p1652 := @Enclosure.norm_gt_of_isNear qz279 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 88615053386996215767 295147905179352825856 4284465405702772351379 

noncomputable def Ns252p1653 := @Ns252p1652 Ns252p796 184948413 2684354560 1213 2684354560 (Ns252p1646 (RS253to264.d46 qz116 qz134 qz278) RS253to264.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable abbrev qz280 := qz555

noncomputable def Ns252p1654 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz116 555893 1000 qz119 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz277 qz279 (Ns252p1645 rfl rfl) (Ns252p1647 rfl rfl)) (Ns252p1648 qz11 qz119 rfl rfl rfl rfl (Ns252p1650 rfl)) (Ns252p1651 qz11 qz137 rfl rfl rfl rfl (Ns252p1653 rfl)) 

noncomputable abbrev qz557 := (RS253to264.d3 qz654 qz664 (@Enclosure.dec_le_dec qz654 qz664 557294 1000 558694 1000 qz658 qz668 rfl rfl rfl))

noncomputable abbrev qz281 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz557)

noncomputable def Ns252p1655 := @Enclosure.Real.IsNear.of_eq qz281 (hardyZApproximantRS₀ qz134) Bool.true 88615053386996215767 295147905179352825856 4284465405702772351379 Ns252p796 

noncomputable abbrev qz558 := (@Enclosure.dec_le_dec qz654 qz664 557294 1000 558694 1000 qz658 qz668 rfl rfl rfl)

noncomputable abbrev qz282 := qz558

noncomputable def Ns252p1656 := @Enclosure.Real.IsNear.neg_val qz281 88615053386996215767 295147905179352825856 4284465405702772351379 Ns252p796 (Ns252p1655 (RS253to264.d4 qz134 qz152 qz282) RS253to264.d53) rfl 

noncomputable abbrev qz283 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz557)

noncomputable def Ns252p1657 := @Enclosure.Real.IsNear.of_eq qz283 (hardyZApproximantRS₀ qz152) Bool.false 2145800840311089475419 1180591620717411303424 2862252964302757199173 Ns252p912 

noncomputable def Ns252p1658 := @Enclosure.Real.IsNear.pos_val qz283 2145800840311089475419 1180591620717411303424 2862252964302757199173 Ns252p912 (Ns252p1657 (RS253to264.d46 qz134 qz152 qz282) RS253to264.d54) rfl 

noncomputable def Ns252p1659 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz281 qz4 qz134 548874 1000 557294 1000 

noncomputable def Ns252p1660 := @Enclosure.norm_gt_of_isNear qz281 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 88615053386996215767 295147905179352825856 4284465405702772351379 

noncomputable def Ns252p1661 := @Ns252p1660 Ns252p796 184948413 2684354560 1213 2684354560 (Ns252p1655 (RS253to264.d4 qz134 qz152 qz282) RS253to264.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable def Ns252p1662 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz283 qz4 qz152 548874 1000 558694 1000 

noncomputable def Ns252p1663 := @Enclosure.norm_gt_of_isNear qz283 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2145800840311089475419 1180591620717411303424 2862252964302757199173 

noncomputable def Ns252p1664 := @Ns252p1663 Ns252p912 184948413 2684354560 1213 2684354560 (Ns252p1657 (RS253to264.d46 qz134 qz152 qz282) RS253to264.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable abbrev qz284 := qz557

noncomputable def Ns252p1665 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz134 557294 1000 qz137 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz281 qz283 (Ns252p1656 rfl rfl) (Ns252p1658 rfl rfl)) (Ns252p1659 qz11 qz137 rfl rfl rfl rfl (Ns252p1661 rfl)) (Ns252p1662 qz11 qz155 rfl rfl rfl rfl (Ns252p1664 rfl)) 

noncomputable abbrev qz559 := (RS253to264.d3 qz664 qz674 (@Enclosure.dec_le_dec qz664 qz674 558694 1000 560094 1000 qz668 qz678 rfl rfl rfl))

noncomputable abbrev qz285 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz559)

noncomputable def Ns252p1666 := @Enclosure.Real.IsNear.of_eq qz285 (hardyZApproximantRS₀ qz152) Bool.false 2145800840311089475419 1180591620717411303424 2862252964302757199173 Ns252p912 

noncomputable abbrev qz560 := (@Enclosure.dec_le_dec qz664 qz674 558694 1000 560094 1000 qz668 qz678 rfl rfl rfl)

noncomputable abbrev qz286 := qz560

noncomputable def Ns252p1667 := @Enclosure.Real.IsNear.pos_val qz285 2145800840311089475419 1180591620717411303424 2862252964302757199173 Ns252p912 (Ns252p1666 (RS253to264.d4 qz152 qz170 qz286) RS253to264.d54) rfl 

noncomputable abbrev qz287 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz559)

noncomputable def Ns252p1668 := @Enclosure.Real.IsNear.of_eq qz287 (hardyZApproximantRS₀ qz170) Bool.true 5412869493781482479 9223372036854775808 29890677908451329953 20752587082923245568000 

noncomputable def Ns252p1669 := @Enclosure.Real.IsNear.neg_val qz287 5412869493781482479 9223372036854775808 29890677908451329953 20752587082923245568000 (Ns252p1668 (RS253to264.d46 qz152 qz170 qz286) RS253to264.d55) rfl 

noncomputable def Ns252p1670 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz285 qz4 qz152 548874 1000 558694 1000 

noncomputable def Ns252p1671 := @Enclosure.norm_gt_of_isNear qz285 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2145800840311089475419 1180591620717411303424 2862252964302757199173 

noncomputable def Ns252p1672 := @Ns252p1671 Ns252p912 184948413 2684354560 1213 2684354560 (Ns252p1666 (RS253to264.d4 qz152 qz170 qz286) RS253to264.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable def Ns252p1673 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz287 qz4 qz170 548874 1000 560094 1000 

noncomputable def Ns252p1674 := @Enclosure.norm_gt_of_isNear qz287 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 5412869493781482479 9223372036854775808 29890677908451329953 

noncomputable def Ns252p1675 := @Ns252p1674 20752587082923245568000 184948413 2684354560 1213 2684354560 (Ns252p1668 (RS253to264.d46 qz152 qz170 qz286) RS253to264.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable abbrev qz288 := qz559

noncomputable def Ns252p1676 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz152 558694 1000 qz155 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz285 qz287 (Ns252p1667 rfl rfl) (Ns252p1669 rfl rfl)) (Ns252p1670 qz11 qz155 rfl rfl rfl rfl (Ns252p1672 rfl)) (Ns252p1673 qz11 qz173 rfl rfl rfl rfl (Ns252p1675 rfl)) 

noncomputable abbrev qz727 := (@Enclosure.dec_le_dec qz772 qz776 560094 1000 561493 1000 (@Eq.refl Real qz772) (@Eq.refl Real qz776) rfl rfl rfl)

noncomputable abbrev qz561 := (RS253to264.d3 qz674 qz684 qz727)

noncomputable abbrev qz289 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz561)

noncomputable def Ns252p1677 := @Enclosure.Real.IsNear.of_eq qz289 (hardyZApproximantRS₀ qz170) Bool.true 5412869493781482479 9223372036854775808 29890677908451329953 20752587082923245568000 

noncomputable abbrev qz562 := qz727

noncomputable abbrev qz290 := qz562

noncomputable def Ns252p1678 := @Enclosure.Real.IsNear.neg_val qz289 5412869493781482479 9223372036854775808 29890677908451329953 20752587082923245568000 (Ns252p1677 (RS253to264.d4 qz170 qz188 qz290) RS253to264.d55) rfl 

noncomputable abbrev qz291 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz561)

noncomputable def Ns252p1679 := @Enclosure.Real.IsNear.of_eq qz291 (hardyZApproximantRS₀ qz188) Bool.false 1844604777283882304673 295147905179352825856 21572466475927972303931 Ns252p1141 

noncomputable def Ns252p1680 := @Enclosure.Real.IsNear.pos_val qz291 1844604777283882304673 295147905179352825856 21572466475927972303931 Ns252p1141 (Ns252p1679 (RS253to264.d46 qz170 qz188 qz290) RS253to264.d56) rfl 

noncomputable def Ns252p1681 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz289 qz4 qz170 548874 1000 560094 1000 

noncomputable def Ns252p1682 := @Enclosure.norm_gt_of_isNear qz289 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 5412869493781482479 9223372036854775808 29890677908451329953 

noncomputable def Ns252p1683 := @Ns252p1682 20752587082923245568000 184948413 2684354560 1213 2684354560 (Ns252p1677 (RS253to264.d4 qz170 qz188 qz290) RS253to264.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable def Ns252p1684 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz291 qz4 qz188 548874 1000 561493 1000 

noncomputable def Ns252p1685 := @Enclosure.norm_gt_of_isNear qz291 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1844604777283882304673 295147905179352825856 21572466475927972303931 

noncomputable def Ns252p1686 := @Ns252p1685 Ns252p1141 184948413 2684354560 1213 2684354560 (Ns252p1679 (RS253to264.d46 qz170 qz188 qz290) RS253to264.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable abbrev qz292 := qz561

noncomputable def Ns252p1687 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz170 560094 1000 qz173 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz289 qz291 (Ns252p1678 rfl rfl) (Ns252p1680 rfl rfl)) (Ns252p1681 qz11 qz173 rfl rfl rfl rfl (Ns252p1683 rfl)) (Ns252p1684 qz11 qz191 rfl rfl rfl rfl (Ns252p1686 rfl)) 

noncomputable abbrev qz728 := (@Enclosure.dec_le_dec qz776 qz780 561493 1000 562891 1000 (@Eq.refl Real qz776) qz783 rfl rfl rfl)

noncomputable abbrev qz563 := (RS253to264.d3 qz684 qz694 qz728)

noncomputable abbrev qz293 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz563)

noncomputable def Ns252p1688 := @Enclosure.Real.IsNear.of_eq qz293 (hardyZApproximantRS₀ qz188) Bool.false 1844604777283882304673 295147905179352825856 21572466475927972303931 Ns252p1141 

noncomputable abbrev qz564 := qz728

noncomputable abbrev qz294 := qz564

noncomputable def Ns252p1689 := @Enclosure.Real.IsNear.pos_val qz293 1844604777283882304673 295147905179352825856 21572466475927972303931 Ns252p1141 (Ns252p1688 (RS253to264.d4 qz188 qz206 qz294) RS253to264.d56) rfl 

noncomputable abbrev qz295 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz563)

noncomputable def Ns252p1690 := @Enclosure.Real.IsNear.of_eq qz295 (hardyZApproximantRS₀ qz206) Bool.true 128484466291431632801 73786976294838206464 86493487574698914383443 Ns252p1259 

noncomputable def Ns252p1691 := @Enclosure.Real.IsNear.neg_val qz295 128484466291431632801 73786976294838206464 86493487574698914383443 Ns252p1259 (Ns252p1690 (RS253to264.d46 qz188 qz206 qz294) RS253to264.d57) rfl 

noncomputable def Ns252p1692 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz293 qz4 qz188 548874 1000 561493 1000 

noncomputable def Ns252p1693 := @Enclosure.norm_gt_of_isNear qz293 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1844604777283882304673 295147905179352825856 21572466475927972303931 

noncomputable def Ns252p1694 := @Ns252p1693 Ns252p1141 184948413 2684354560 1213 2684354560 (Ns252p1688 (RS253to264.d4 qz188 qz206 qz294) RS253to264.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable def Ns252p1695 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz295 qz4 qz206 548874 1000 562891 1000 

noncomputable def Ns252p1696 := @Enclosure.norm_gt_of_isNear qz295 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 128484466291431632801 73786976294838206464 86493487574698914383443 

noncomputable def Ns252p1697 := @Ns252p1696 Ns252p1259 184948413 2684354560 1213 2684354560 (Ns252p1690 (RS253to264.d46 qz188 qz206 qz294) RS253to264.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable abbrev qz296 := qz563

noncomputable def Ns252p1698 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz188 561493 1000 qz191 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz293 qz295 (Ns252p1689 rfl rfl) (Ns252p1691 rfl rfl)) (Ns252p1692 qz11 qz191 rfl rfl rfl rfl (Ns252p1694 rfl)) (Ns252p1695 qz11 qz209 rfl rfl rfl rfl (Ns252p1697 rfl)) 

noncomputable abbrev qz729 := (@Enclosure.dec_le_dec qz780 qz785 562891 1000 564289 1000 qz783 qz788 rfl rfl rfl)

noncomputable abbrev qz565 := (RS253to264.d3 qz694 qz705 qz729)

noncomputable abbrev qz297 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz565)

noncomputable def Ns252p1699 := @Enclosure.Real.IsNear.of_eq qz297 (hardyZApproximantRS₀ qz206) Bool.true 128484466291431632801 73786976294838206464 86493487574698914383443 Ns252p1259 

noncomputable abbrev qz566 := qz729

noncomputable abbrev qz298 := qz566

noncomputable def Ns252p1700 := @Enclosure.Real.IsNear.neg_val qz297 128484466291431632801 73786976294838206464 86493487574698914383443 Ns252p1259 (Ns252p1699 (RS253to264.d4 qz206 qz223 qz298) RS253to264.d57) rfl 

noncomputable abbrev qz299 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz565)

noncomputable def Ns252p1701 := @Enclosure.Real.IsNear.of_eq qz299 (hardyZApproximantRS₀ qz223) Bool.false 4275432603388139187 36893488147419103232 1204274485178392524139 830103483316929822720000 

noncomputable def Ns252p1702 := @Enclosure.Real.IsNear.pos_val qz299 4275432603388139187 36893488147419103232 1204274485178392524139 830103483316929822720000 (Ns252p1701 (RS253to264.d46 qz206 qz223 qz298) RS253to264.d58) rfl 

noncomputable def Ns252p1703 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz297 qz4 qz206 548874 1000 562891 1000 

noncomputable def Ns252p1704 := @Enclosure.norm_gt_of_isNear qz297 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 128484466291431632801 73786976294838206464 86493487574698914383443 

noncomputable def Ns252p1705 := @Ns252p1704 Ns252p1259 184948413 2684354560 1213 2684354560 (Ns252p1699 (RS253to264.d4 qz206 qz223 qz298) RS253to264.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable def Ns252p1706 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz299 qz4 qz223 548874 1000 564289 1000 

noncomputable def Ns252p1707 := @Enclosure.norm_gt_of_isNear qz299 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 4275432603388139187 36893488147419103232 1204274485178392524139 

noncomputable def Ns252p1708 := @Ns252p1707 830103483316929822720000 184948413 2684354560 1213 2684354560 (Ns252p1701 (RS253to264.d46 qz206 qz223 qz298) RS253to264.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable abbrev qz300 := qz565

noncomputable def Ns252p1709 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz206 562891 1000 qz209 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz297 qz299 (Ns252p1700 rfl rfl) (Ns252p1702 rfl rfl)) (Ns252p1703 qz11 qz209 rfl rfl rfl rfl (Ns252p1705 rfl)) (Ns252p1706 qz11 qz226 rfl rfl rfl rfl (Ns252p1708 rfl)) 

noncomputable abbrev qz795 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 564289 1000) (Enclosure.sfrac Bool.false 565685 1000) 564289 1000 565685 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 564289 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 565685 1000)) rfl rfl rfl)

noncomputable abbrev qz730 := qz795

noncomputable abbrev qz567 := (RS253to264.d3 qz705 qz716 qz730)

noncomputable abbrev qz301 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz567)

noncomputable def Ns252p1710 := @Enclosure.Real.IsNear.of_eq qz301 (hardyZApproximantRS₀ qz223) Bool.false 4275432603388139187 36893488147419103232 1204274485178392524139 830103483316929822720000 

noncomputable abbrev qz568 := qz730

noncomputable abbrev qz302 := qz568

noncomputable def Ns252p1711 := @Enclosure.Real.IsNear.pos_val qz301 4275432603388139187 36893488147419103232 1204274485178392524139 830103483316929822720000 (Ns252p1710 (RS253to264.d4 qz223 qz240 qz302) RS253to264.d58) rfl 

noncomputable abbrev qz303 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz567)

noncomputable def Ns252p1712 := @Enclosure.Real.IsNear.of_eq qz303 (hardyZApproximantRS₀ qz240) Bool.true 232265292887391840039 73786976294838206464 201169287016766385203 138350580552821637120000 

noncomputable def Ns252p1713 := @Enclosure.Real.IsNear.neg_val qz303 232265292887391840039 73786976294838206464 201169287016766385203 138350580552821637120000 (Ns252p1712 (RS253to264.d46 qz223 qz240 qz302) RS253to264.d59) rfl 

noncomputable def Ns252p1714 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz301 qz4 qz223 548874 1000 564289 1000 

noncomputable def Ns252p1715 := @Enclosure.norm_gt_of_isNear qz301 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 4275432603388139187 36893488147419103232 1204274485178392524139 

noncomputable def Ns252p1716 := @Ns252p1715 830103483316929822720000 184948413 2684354560 1213 2684354560 (Ns252p1710 (RS253to264.d4 qz223 qz240 qz302) RS253to264.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable def Ns252p1717 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz303 qz4 qz240 548874 1000 565685 1000 

noncomputable def Ns252p1718 := @Enclosure.norm_gt_of_isNear qz303 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 232265292887391840039 73786976294838206464 201169287016766385203 

noncomputable def Ns252p1719 := @Ns252p1718 138350580552821637120000 184948413 2684354560 1213 2684354560 (Ns252p1712 (RS253to264.d46 qz223 qz240 qz302) RS253to264.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 184948413 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS253to264.d48) rfl rfl rfl rfl 

noncomputable abbrev qz304 := qz567

noncomputable def Ns252p1720 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz223 564289 1000 qz226 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz301 qz303 (Ns252p1711 rfl rfl) (Ns252p1713 rfl rfl)) (Ns252p1714 qz11 qz226 rfl rfl rfl rfl (Ns252p1716 rfl)) (Ns252p1717 qz11 qz243 rfl rfl rfl rfl (Ns252p1719 rfl)) 

noncomputable def Ns252p1721 := @List.cons RS253to264.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns252p1709)) (@List.cons RS253to264.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns252p1720)) (@List.nil RS253to264.d0)) 

noncomputable def Ns252p1722 := @List.cons RS253to264.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns252p1687)) (@List.cons RS253to264.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns252p1698)) Ns252p1721) 

noncomputable def Ns252p1723 := @List.cons RS253to264.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns252p1665)) (@List.cons RS253to264.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns252p1676)) Ns252p1722) 

noncomputable def Ns252p1724 := @List.cons RS253to264.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns252p1643)) (@List.cons RS253to264.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns252p1654)) Ns252p1723) 

noncomputable def Ns252p1725 := @List.cons RS253to264.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns252p1621)) (@List.cons RS253to264.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns252p1632)) Ns252p1724) 

noncomputable def Ns252p1726 := @List.cons RS253to264.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz260 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz260) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz260) Ns252p1599)) (@List.cons RS253to264.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz264 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz264) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz264) Ns252p1610)) Ns252p1725) 

noncomputable abbrev qz569 := (RS253to264.d2 qz674 qz684 qz727)

noncomputable abbrev qz731 := (RS253to264.d2 qz780 qz785 (@Enclosure.dec_le_dec qz780 qz785 562891 1000 564289 1000 qz783 qz788 rfl rfl rfl))

noncomputable abbrev qz732 := (@List.cons RS253to264.d1 (RS253to264.d2 qz785 qz790 qz795) (@List.nil RS253to264.d1))

noncomputable abbrev qz570 := (@List.cons RS253to264.d1 (RS253to264.d2 qz684 qz694 qz728) (@List.cons RS253to264.d1 qz731 qz732))

noncomputable abbrev qz305 := (@List.cons RS253to264.d1 (RS253to264.d2 qz470 qz483 qz560) (@List.cons RS253to264.d1 qz569 qz570))

noncomputable def Ns252p1727 := @List.cons RS253to264.d1 (RS253to264.d2 qz116 qz134 qz278) (@List.cons RS253to264.d1 (RS253to264.d2 qz134 qz152 qz282) qz305) 

noncomputable abbrev qz306 := (RS253to264.d2 qz431 qz444 qz554)

noncomputable def Ns252p1728 := @List.IsChain.cons_cons RS253to264.d1 RS253to264.d60 qz306 (RS253to264.d2 qz116 qz134 qz278) (@List.cons RS253to264.d1 (RS253to264.d2 qz134 qz152 qz282) qz305) 

noncomputable def Ns252p1729 := @List.IsChain.cons_cons RS253to264.d1 RS253to264.d60 (RS253to264.d2 qz116 qz134 qz278) (RS253to264.d2 qz134 qz152 qz282) qz305 (@Enclosure.dec_le_dec qz134 qz134 557294 1000 557294 1000 qz137 qz137 rfl rfl rfl) 

noncomputable abbrev qz307 := (RS253to264.d2 qz470 qz483 qz560)

noncomputable abbrev qz308 := qz569

noncomputable abbrev qz309 := qz570

noncomputable abbrev qz571 := (RS253to264.d2 qz684 qz694 qz728)

noncomputable abbrev qz310 := qz571

noncomputable abbrev qz572 := (@List.cons RS253to264.d1 qz731 qz732)

noncomputable abbrev qz311 := qz572

noncomputable abbrev qz573 := qz731

noncomputable abbrev qz312 := qz573

noncomputable abbrev qz574 := qz732

noncomputable abbrev qz313 := qz574

noncomputable abbrev qz733 := (RS253to264.d2 qz785 qz790 qz795)

noncomputable abbrev qz575 := qz733

noncomputable abbrev qz314 := qz575

noncomputable def Ns252p1730 := @List.IsChain.cons_cons RS253to264.d1 RS253to264.d60 qz307 qz308 qz309 (@Enclosure.dec_le_dec qz170 qz170 560094 1000 560094 1000 qz173 qz173 rfl rfl rfl) (@List.IsChain.cons_cons RS253to264.d1 RS253to264.d60 qz308 qz310 qz311 (@Enclosure.dec_le_dec qz188 qz188 561493 1000 561493 1000 qz191 qz191 rfl rfl rfl) (@List.IsChain.cons_cons RS253to264.d1 RS253to264.d60 qz310 qz312 qz313 (@Enclosure.dec_le_dec qz206 qz206 562891 1000 562891 1000 qz209 qz209 rfl rfl rfl) (@List.IsChain.cons_cons RS253to264.d1 RS253to264.d60 qz312 qz314 (@List.nil RS253to264.d1) (@Enclosure.dec_le_dec qz223 qz223 564289 1000 564289 1000 qz226 qz226 rfl rfl rfl) (@List.IsChain.singleton RS253to264.d1 RS253to264.d60 qz314)))) 

noncomputable abbrev qz315 := (@List.cons RS253to264.d1 qz569 qz570)

noncomputable def Ns252p1731 := @List.IsChain.cons_cons RS253to264.d1 RS253to264.d60 (RS253to264.d2 qz134 qz152 qz282) qz307 qz315 (@Enclosure.dec_le_dec qz152 qz152 558694 1000 558694 1000 qz155 qz155 rfl rfl rfl) Ns252p1730 

noncomputable def Ns252p1732 := @List.IsChain.cons_cons RS253to264.d1 RS253to264.d60 (RS253to264.d2 qz4 qz35 qz258) (RS253to264.d2 qz35 qz62 qz262) (@List.cons RS253to264.d1 (RS253to264.d2 qz62 qz80 qz266) (@List.cons RS253to264.d1 (RS253to264.d2 qz80 qz98 qz270) (@List.cons RS253to264.d1 qz306 Ns252p1727))) (@Enclosure.dec_le_dec qz35 qz35 550280 1000 550280 1000 qz38 qz38 rfl rfl rfl) (@List.IsChain.cons_cons RS253to264.d1 RS253to264.d60 (RS253to264.d2 qz35 qz62 qz262) (RS253to264.d2 qz62 qz80 qz266) (@List.cons RS253to264.d1 (RS253to264.d2 qz80 qz98 qz270) (@List.cons RS253to264.d1 qz306 Ns252p1727)) (@Enclosure.dec_le_dec qz62 qz62 551684 1000 551684 1000 qz65 qz65 rfl rfl rfl) (@List.IsChain.cons_cons RS253to264.d1 RS253to264.d60 (RS253to264.d2 qz62 qz80 qz266) (RS253to264.d2 qz80 qz98 qz270) (@List.cons RS253to264.d1 qz306 Ns252p1727) (@Enclosure.dec_le_dec qz80 qz80 553088 1000 553088 1000 qz83 qz83 rfl rfl rfl) (@List.IsChain.cons_cons RS253to264.d1 RS253to264.d60 (RS253to264.d2 qz80 qz98 qz270) qz306 Ns252p1727 (@Enclosure.dec_le_dec qz98 qz98 554491 1000 554491 1000 qz101 qz101 rfl rfl rfl) (Ns252p1728 (@Enclosure.dec_le_dec qz116 qz116 555893 1000 555893 1000 qz119 qz119 rfl rfl rfl) (Ns252p1729 Ns252p1731))))) 

noncomputable abbrev qz576 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz577 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns252p1726 Ns252p1732)

noncomputable abbrev qz578 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns252p1726 Ns252p1732))

theorem RS253to264.d61 : Zeta.Certificates.BatchSpec 12 548874 1000 565685 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz576 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz576 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz576 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz240)))) qz577 (@And.intro (@Eq Nat (@List.length qz576 qz578) 12) (And (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz576 qz578)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz576 qz578)) (@Option.some Real qz240))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz576 qz578)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz576 qz578)) (@Option.some Real qz240)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz240))))

theorem solution : Zeta.Certificates.BatchSpec 12 548874 1000 565685 1000 := RS253to264.d61
#print axioms solution
#check solution
