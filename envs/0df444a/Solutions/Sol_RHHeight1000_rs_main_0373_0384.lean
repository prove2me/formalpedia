-- Prove2me | solution 1 for RHHeight1000.rs_main_0373_0384
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T09:02:32.809465+00:00
-- url     : https://prove2.me/submissions/6fd92674-00cb-498a-86de-05334308bc56

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

noncomputable def RS373to384.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS373to384.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS373to384.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS373to384.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS373to384.d2 a b h 

theorem RS373to384.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS373to384.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS373to384.d3 a b h)) 

noncomputable def Ns372p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns372p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns372p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns372p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns372p0 Ns372p1 Ns372p2 Ns372p1 307286088 268435456 1 92160000 307286088 268435456 1 92160000 153643044 134217728 2 134217728 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns372p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns372p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns372p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns372p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns372p8 := nat_lit 167537954069964697925743468333314178468718661948561187618563575975392713740913527107727581163208035826476740967700482432525301063254420572874757592895482956004842597348203117269212172556829666669574421653274845612596416189641484794702002223261246862056663160605878293700340502480877986491439034432953223334258717026053687371824342493299510132312376251152844516906794910572262907940062760396663270105627554083664899640691826599584783763757814813433640133591539937449421955686657622469485188711283992428713614179785896055117030632677201478317872225272595773536303110412989181984739022579128493081560758017763072115692678596043664844667144619713966763611484179303468167142547433165016751768184247559143333542643815355903304572487929375 

noncomputable def Ns372p9 := nat_lit 17907736863639440849562382641391758203535690054199171304015283257442503423240620144819838407313611418261944516207295868563739563278604805791797182761045687776939279949642059267526948014748996956777332184087524644234759874591635243045607722412471722018588244283882362848653445974523544951031470230725674276297342086185092985546835544820091590454230569790847977790484558207349923322458845585052164126500435851662252152223728079705692133047658564669873831757357628115566356048471439549797170528303905720944834637690907185213991407615774042056720704508980680095051114888612186461088301140868302968264130481206655302741383410655080008578156649725227045954510069588220729495895148666460653631514375880874422615237249871322129146554264800 

noncomputable def Ns372p10 := nat_lit 55164646516618494962085419356369025784335016154267579706247610053041231157772817011486486467101704279863254798704146668052276438579475100451766223896220272709675360577301802978530276301158911649961092601279696986330335403118086533522541958716560166657634553390183479955483588238249446822384543398154260439705049143284278540285021213103458182619368483938376641172730818250587232036579805400979202432024046862170503602539341971086573372247299262086029843105216008583038025403798224342134620653974939981235680083776396058604459065501719125356177784467570909658245422960948263734871602033841948787585406240093531041217463298165642337705122589129757920995868559518021463265498464182174549661735402095023640043996665674913376875 

noncomputable def Ns372p11 := BSN.log_dyadic_bound Ns372p6 Ns372p7 15 14 Ns372p8 268435456 92160000 Ns372p9 Ns372p10 307286088 Ns372p4 Ns372p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns372p6) (BSN.artanhQ Ns372p7) 0 14 Ns372p9 Ns372p8 Ns372p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns372p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns372p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns372p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns372p15 := nat_lit 167537954069966963268140139327979112712430526945422964221951926912223381190141639739514890494967825643602350173964944759828460064784215684919760383437959917620844610857567326816719640593037578236900835917107172977527392439886629774248115214831425484905681376157923696414882114961796820014026232307332015059110330001516939277521159573995394989771587717775443426002499543257897301982481613760098955890450106043861450716722534643739571053080256776912576113428445260435254713579381797931690799491102381747484553243404562568585572234105168360737285205910186933811836504830286397217473365026331067977496463917110493303316865058355012304571237619413071097245713770677768486493924969821719264401216877841676972336093778875903304572487929375 

noncomputable def Ns372p16 := nat_lit 17907736863639702486765313263906285882628955290251965205176678923530777959693011244026517850256414903756943142851250712732214241881959351517241344993825585048584379523049477943740273636414656012170312373198803997844271825165684859407921203335666024680974464565759223251918458072775203410604089667122984485578465112081892102496937045858735135721609691262763214794451343726045584198128451069547586972080574568545086657023793200560105564573365716615162566961587407171758966967827997201380802107846920231945878242774600967607639551032178207663699700360114112068650063802902647517702890145150192721997537569966984346993833704449560383184487996362781528900358997452380059737141488304159449328022742959995775545894292303322129146554264800 

noncomputable def Ns372p17 := nat_lit 55164646516619937449385584700664297411818070214438189962773666351465523500358685366424500506990751111492356556545320273548942244833046464529601272738875466881799996765940232256588350019911833156887888425998391295014189841212513610526066550079316346993943774342801096070086869790972589246312728227659319758310961510342377923950694747797317942483020440897997204711883064182772445608288320382376665481938194224815739627075458138172195220395246294556718284728034954178416253903237031389214179719385823921869528509431462690683227358218086518156757026652846493301460983550768858152506145788622699720737745394141184245149692548799188169247529408201840608223422296381897323845616153036586108326210125693898345963996665674913376875 

noncomputable def Ns372p18 := BSN.log_dyadic_bound Ns372p13 Ns372p14 15 14 Ns372p15 268435456 92160000 Ns372p16 Ns372p17 307286088 Ns372p12 Ns372p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns372p13) (BSN.artanhQ Ns372p14) 0 14 Ns372p16 Ns372p15 Ns372p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns372p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 153643044 134217728 2 134217728 38410761 33554432 1 67108864 (Ns372p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns372p0 Ns372p1 307286088 268435456 1 92160000 Bool.false (BSN.logfrac_isNear Ns372p4 Ns372p5 1 Ns372p0 Ns372p1 307286088 268435456 92160000 rfl rfl rfl (Ns372p11 rfl))) (BSN.isNear_log_sfrac Ns372p2 Ns372p1 307286088 268435456 1 92160000 Bool.false (BSN.logfrac_isNear Ns372p12 Ns372p5 1 Ns372p2 Ns372p1 307286088 268435456 92160000 rfl rfl rfl (Ns372p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS373to384.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 67108864 := Ns372p19 

noncomputable def Ns372p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 16777216 5760000 385100712855 135135 11629079 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz579 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz316 := qz579

noncomputable abbrev qz0 := qz316

theorem RS373to384.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 11629079 16777216 1 5760000 := BSN.isNear_log_sfrac 2 1 11629079 16777216 1 5760000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 11629079 16777216 5760000 rfl rfl rfl (Ns372p20 rfl)) 

theorem RS373to384.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 186065264 268435456 47 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 11629079 16777216 1 5760000 186065264 268435456 47 268435456 RS373to384.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz580 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz319 := qz580

noncomputable def Ns372p21 := @Enclosure.Real.IsNear.inv_image qz317 47453133 33554432 1 33554432 11863282 11863284 16777216 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 47453133 33554432 1 33554432 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 47453133 33554432 1 33554432 47453133 33554432 1 33554432 (BSN.sqrt_enclosure 2 1 23726566 23726567 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS373to384.d8 : Enclosure.Real.IsNear qz320 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 23726566 33554432 2 33554432 11863283 16777216 1 16777216 (Ns372p21 rfl rfl) rfl 

theorem RS373to384.d9 : Enclosure.Real.IsNear qz320 Bool.false 189812528 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 189812528 268435456 16 268435456 RS373to384.d8 rfl 

noncomputable def Ns372p22 := BSN.log_dyadic_bound 1 2 13 12 132638213186519040000 16777216 5760000 13079757671720842725 316234143225 18431655 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS373to384.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 18431655 16777216 1 5760000 := BSN.isNear_log_sfrac 3 1 18431655 16777216 1 5760000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 18431655 16777216 5760000 rfl rfl rfl (Ns372p22 rfl)) 

theorem RS373to384.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 294906480 268435456 47 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 18431655 16777216 1 5760000 294906480 268435456 47 268435456 RS373to384.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns372p23 := @Enclosure.Real.IsNear.inv_image qz321 58117981 33554432 1 33554432 9686330 9686331 16777216 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 58117981 33554432 1 33554432 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 58117981 33554432 1 33554432 58117981 33554432 1 33554432 (BSN.sqrt_enclosure 3 1 29058990 29058991 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS373to384.d12 : Enclosure.Real.IsNear qz323 Bool.false 19372661 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 19372661 33554432 1 33554432 19372661 33554432 1 33554432 (Ns372p23 rfl rfl) rfl 

theorem RS373to384.d13 : Enclosure.Real.IsNear qz323 Bool.false 154981288 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 19372661 33554432 1 33554432 154981288 268435456 8 268435456 RS373to384.d12 rfl 

noncomputable def Ns372p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns372p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns372p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns372p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns372p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns372p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns372p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns372p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns372p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns372p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns372p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns372p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns372p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns372p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns372p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns372p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns372p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns372p25 Ns372p26 Ns372p27 Ns372p28 200200021673987500790625 Ns372p29 Ns372p30 Ns372p31 Ns372p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns372p32 Ns372p33 151412625 Ns372p34 Ns372p35 1322214852783825 Ns372p27 Ns372p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns372p32 Ns372p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns372p34 Ns372p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns372p36 Ns372p37 1267389585 Ns372p38 Ns372p39 1927077560082675 Ns372p29 Ns372p30 Ns372p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns372p36 Ns372p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns372p38 Ns372p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS373to384.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns372p24 Ns372p25 1 Ns372p26 := Ns372p40 rfl rfl rfl 

noncomputable def Ns372p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns372p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns372p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns372p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns372p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns372p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns372p25 Ns372p26 Ns372p42 Ns372p43 9945 Ns372p44 Ns372p45 65835 Ns372p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns372p42 Ns372p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns372p44 Ns372p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS373to384.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns372p41 Ns372p25 1 Ns372p26 := Ns372p46 rfl 

noncomputable def Ns372p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns372p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS373to384.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns372p47 Ns372p25 1 Ns372p48 := BSN.pi_combine Ns372p24 Ns372p41 Ns372p25 Ns372p26 Ns372p48 Ns372p47 rfl rfl rfl rfl RS373to384.d14 RS373to384.d15 

theorem RS373to384.d17 : Enclosure.Real.IsNear Real.pi Bool.false 14148475504056880 4503599627370496 1 4503599627370496 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns372p47 Ns372p25 1 Ns372p48 14148475504056880 4503599627370496 1 4503599627370496 RS373to384.d16 rfl 

noncomputable def Ns372p49 := nat_lit 147443727375074537121690809726715087890625 

noncomputable def Ns372p50 := nat_lit 22889945643899497138335355216896171420000 

noncomputable def Ns372p51 := nat_lit 355592320898650075318906513310625 

noncomputable def Ns372p52 := BSN.log_dyadic_bound 3 5 17 16 Ns372p49 16777216 5760000 Ns372p50 Ns372p51 23258159 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 3) (BSN.artanhQ 5) 0 16 Ns372p50 Ns372p49 Ns372p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS373to384.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 23258159 16777216 1 5760000 := BSN.isNear_log_sfrac 4 1 23258159 16777216 1 5760000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 23258159 16777216 5760000 rfl rfl rfl (Ns372p52 rfl)) 

theorem RS373to384.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 372130544 268435456 47 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 23258159 16777216 1 5760000 372130544 268435456 47 268435456 RS373to384.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns372p53 := @Enclosure.Real.IsNear.inv_image qz325 67108865 33554432 1 33554432 8388607 8388608 16777216 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 67108865 33554432 1 33554432 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 67108865 33554432 1 33554432 67108865 33554432 1 33554432 (BSN.sqrt_enclosure 4 1 33554432 33554433 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS373to384.d20 : Enclosure.Real.IsNear qz327 Bool.false 16777215 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 16777215 33554432 1 33554432 16777215 33554432 1 33554432 (Ns372p53 rfl rfl) rfl 

theorem RS373to384.d21 : Enclosure.Real.IsNear qz327 Bool.false 134217720 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 16777215 33554432 1 33554432 134217720 268435456 8 268435456 RS373to384.d20 rfl 

noncomputable def Ns372p54 := nat_lit 61697213297292266380244507781205789317049021875 

noncomputable def Ns372p55 := nat_lit 12776162289178456695994184080609776001208236500 

noncomputable def Ns372p56 := nat_lit 57671893776295590731569354191667200000 

noncomputable def Ns372p57 := nat_lit 885951608314392539099884620 

noncomputable def Ns372p58 := nat_lit 1286943652057122751813246125 

noncomputable def Ns372p59 := BSN.log_dyadic_bound 2 3 22 21 Ns372p54 16777216 5760000 Ns372p55 Ns372p56 27001887 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 21 10 9927050056596826020 47940881637414340575 686533194547200 Ns372p57 Ns372p58 84004523356416638976000 Ns372p55 Ns372p54 Ns372p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 10 21 Ns372p57 Ns372p58 84004523356416638976000 rfl rfl rfl rfl)) rfl rfl 

theorem RS373to384.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 5760000 := BSN.isNear_log_sfrac 5 1 27001887 16777216 1 5760000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 27001887 16777216 5760000 rfl rfl rfl (Ns372p59 rfl rfl)) 

theorem RS373to384.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 432030192 268435456 47 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 5760000 432030192 268435456 47 268435456 RS373to384.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns372p60 := @Enclosure.Real.IsNear.inv_image qz328 75029991 33554432 1 33554432 7502998 7503000 16777216 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 75029991 33554432 1 33554432 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 75029991 33554432 1 33554432 75029991 33554432 1 33554432 (BSN.sqrt_enclosure 5 1 37514995 37514996 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS373to384.d24 : Enclosure.Real.IsNear qz329 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 15005998 33554432 2 33554432 7502999 16777216 1 16777216 (Ns372p60 rfl rfl) rfl 

theorem RS373to384.d25 : Enclosure.Real.IsNear qz329 Bool.false 120047984 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 120047984 268435456 16 268435456 RS373to384.d24 rfl 

noncomputable def Ns372p61 := BSN.log_dyadic_bound 2 10 5 4 94500000000 16777216 5760000 1291130880 26880 6802575 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz580)

theorem RS373to384.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 781250009 4500000000000000 := BSN.isNear_log_sfrac 6 1 4034683545132279 2251799813685248 781250009 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 1083052117253279893684224 604462909807314587353088 1000000011520000 5760000000000000000000 4034683545132279 2251799813685248 781250009 4500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 6802575 16777216 24973259072661432 36028797018963968 5760000 1000000000000000 rfl rfl rfl rfl (Ns372p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS373to384.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 480971758 268435456 48 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 781250009 4500000000000000 480971758 268435456 48 268435456 RS373to384.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns372p62 := @Enclosure.Real.IsNear.inv_image qz331 82191237 33554432 1 33554432 6849269 6849270 16777216 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 82191237 33554432 1 33554432 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 82191237 33554432 1 33554432 82191237 33554432 1 33554432 (BSN.sqrt_enclosure 6 1 41095618 41095619 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS373to384.d28 : Enclosure.Real.IsNear qz332 Bool.false 13698539 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 13698539 33554432 1 33554432 13698539 33554432 1 33554432 (Ns372p62 rfl rfl) rfl 

theorem RS373to384.d29 : Enclosure.Real.IsNear qz332 Bool.false 109588312 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 13698539 33554432 1 33554432 109588312 268435456 8 268435456 RS373to384.d28 rfl 

noncomputable def Ns372p63 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 16777216 5760000 11010900719820672 5524329195 9388794 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz580)

theorem RS373to384.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 781250009 4500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 781250009 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 1176230476650867868041216 604462909807314587353088 1000000011520000 5760000000000000000000 4381799983422711 2251799813685248 781250009 4500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 9388794 16777216 24973259072661432 36028797018963968 5760000 1000000000000000 rfl rfl rfl rfl (Ns372p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS373to384.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 522351262 268435456 48 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 781250009 4500000000000000 522351262 268435456 48 268435456 RS373to384.d30 rfl 

noncomputable abbrev qz334 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns372p64 := @Enclosure.Real.IsNear.inv_image qz334 88776683 33554432 1 33554432 6341191 6341192 16777216 (@Enclosure.Real.IsNear.of_eq qz334 (Real.sqrt qz333) Bool.false 88776683 33554432 1 33554432 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 88776683 33554432 1 33554432 88776683 33554432 1 33554432 (BSN.sqrt_enclosure 7 1 44388341 44388342 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS373to384.d32 : Enclosure.Real.IsNear qz335 Bool.false 12682383 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 12682383 33554432 1 33554432 12682383 33554432 1 33554432 (Ns372p64 rfl rfl) rfl 

theorem RS373to384.d33 : Enclosure.Real.IsNear qz335 Bool.false 101459064 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 12682383 33554432 1 33554432 101459064 268435456 8 268435456 RS373to384.d32 rfl 

noncomputable def Ns372p65 := nat_lit 1256945285058001618599936 

noncomputable def Ns372p66 := BSN.log_dyadic_bound 0 16 1 0 1 16777216 5760000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz580)

theorem RS373to384.d34 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 1562500027 9000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1562500027 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false Ns372p65 604462909807314587353088 1000000017280000 5760000000000000000000 9364972152248037 4503599627370496 1562500027 9000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 16777216 24973259072661432 36028797018963968 5760000 1000000000000000 rfl rfl rfl rfl (Ns372p66 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS373to384.d35 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 558195838 268435456 48 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 1562500027 9000000000000000 558195838 268435456 48 268435456 RS373to384.d34 rfl 

noncomputable abbrev qz337 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns372p67 := @Enclosure.Real.IsNear.inv_image qz337 94906265 33554432 1 33554432 5931641 5931642 16777216 (@Enclosure.Real.IsNear.of_eq qz337 (Real.sqrt qz336) Bool.false 94906265 33554432 1 33554432 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 94906265 33554432 1 33554432 94906265 33554432 1 33554432 (BSN.sqrt_enclosure 8 1 47453132 47453133 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz338 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS373to384.d36 : Enclosure.Real.IsNear qz338 Bool.false 11863283 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 11863283 33554432 1 33554432 11863283 33554432 1 33554432 (Ns372p67 rfl rfl) rfl 

theorem RS373to384.d37 : Enclosure.Real.IsNear qz338 Bool.false 94906264 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 11863283 33554432 1 33554432 94906264 268435456 8 268435456 RS373to384.d36 rfl 

noncomputable def Ns372p68 := nat_lit 1328140746012062765809664 

noncomputable def Ns372p69 := BSN.log_dyadic_bound 1 17 3 2 1252815 16777216 5760000 1448 3 1976071 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz580)

theorem RS373to384.d38 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 1562500027 9000000000000000 := BSN.isNear_log_sfrac 9 1 9895419672221413 4503599627370496 1562500027 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false Ns372p68 604462909807314587353088 1000000017280000 5760000000000000000000 9895419672221413 4503599627370496 1562500027 9000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 1976071 16777216 24973259072661432 36028797018963968 5760000 1000000000000000 rfl rfl rfl rfl (Ns372p69 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS373to384.d39 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 589812974 268435456 48 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 1562500027 9000000000000000 589812974 268435456 48 268435456 RS373to384.d38 rfl 

noncomputable abbrev qz340 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns372p70 := @Enclosure.Real.IsNear.inv_image qz340 100663297 33554432 1 33554432 5592405 5592406 16777216 (@Enclosure.Real.IsNear.of_eq qz340 (Real.sqrt qz339) Bool.false 100663297 33554432 1 33554432 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 100663297 33554432 1 33554432 100663297 33554432 1 33554432 (BSN.sqrt_enclosure 9 1 50331648 50331649 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz341 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS373to384.d40 : Enclosure.Real.IsNear qz341 Bool.false 11184811 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 11184811 33554432 1 33554432 11184811 33554432 1 33554432 (Ns372p70 rfl rfl) rfl 

theorem RS373to384.d41 : Enclosure.Real.IsNear qz341 Bool.false 89478488 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 11184811 33554432 1 33554432 89478488 268435456 8 268435456 RS373to384.d40 rfl 

noncomputable def Ns372p71 := nat_lit 1391827265235416537628672 

noncomputable def Ns372p72 := BSN.log_dyadic_bound 2 18 4 3 3571283520 16777216 5760000 14806464 960 3743727 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 18) 0 3 14806464 3571283520 960 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz732 := (Enclosure.sfrac Bool.false 10 1)

noncomputable abbrev qz581 := qz732

noncomputable abbrev qz342 := qz581

noncomputable abbrev qz1 := qz342

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10) qz580)

theorem RS373to384.d42 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 10369921216632549 4503599627370496 1562500027 9000000000000000 := BSN.isNear_log_sfrac 10 1 10369921216632549 4503599627370496 1562500027 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false Ns372p71 604462909807314587353088 1000000017280000 5760000000000000000000 10369921216632549 4503599627370496 1562500027 9000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 3743727 16777216 24973259072661432 36028797018963968 5760000 1000000000000000 rfl rfl rfl rfl (Ns372p72 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS373to384.d43 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 618095470 268435456 48 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 10369921216632549 4503599627370496 1562500027 9000000000000000 618095470 268435456 48 268435456 RS373to384.d42 rfl 

noncomputable abbrev qz344 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10))

noncomputable def Ns372p73 := @Enclosure.Real.IsNear.inv_image qz344 106108431 33554432 1 33554432 5305421 5305422 16777216 (@Enclosure.Real.IsNear.of_eq qz344 (Real.sqrt qz343) Bool.false 106108431 33554432 1 33554432 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz343) Bool.false 106108431 33554432 1 33554432 106108431 33554432 1 33554432 (BSN.sqrt_enclosure 10 1 53054215 53054216 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz345 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

theorem RS373to384.d44 : Enclosure.Real.IsNear qz345 Bool.false 10610843 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz345 Bool.false 10610843 33554432 1 33554432 10610843 33554432 1 33554432 (Ns372p73 rfl rfl) rfl 

theorem RS373to384.d45 : Enclosure.Real.IsNear qz345 Bool.false 84886744 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz345 Bool.false 10610843 33554432 1 33554432 84886744 268435456 8 268435456 RS373to384.d44 rfl 

theorem RS373to384.d46 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz733 := (@instHMul Real Real.instMul)

noncomputable abbrev qz582 := (@HMul.hMul Real Real Real qz733 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz346 := qz582

noncomputable abbrev qz2 := qz346

theorem RS373to384.d47 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS373to384.d46 rfl 

noncomputable abbrev qz347 := (@Inv.inv Real Real.instInv qz582)

noncomputable abbrev qz3 := qz347

theorem RS373to384.d48 : Enclosure.Real.IsNear qz3 Bool.false 5340353 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 5340353 33554432 1 33554432 5340353 33554432 1 33554432 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 2670176 2670177 16777216 RS373to384.d47 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns372p74 := nat_lit 2656331146614175432704000 

noncomputable def Ns372p75 := nat_lit 109455461985247221499106951168 

noncomputable abbrev qz734 := (Enclosure.sfrac Bool.false 712564 1000)

noncomputable abbrev qz583 := qz734

noncomputable abbrev qz348 := qz583

noncomputable abbrev qz4 := qz348

noncomputable abbrev qz584 := qz733

noncomputable abbrev qz349 := qz584

noncomputable abbrev qz5 := qz349

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 10)

noncomputable abbrev qz7 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz735 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 712564 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz585 := qz735

noncomputable abbrev qz350 := qz585

noncomputable abbrev qz8 := qz350

noncomputable abbrev qz9 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz736 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 712564 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz586 := qz736

noncomputable abbrev qz351 := qz586

noncomputable abbrev qz10 := qz351

noncomputable abbrev qz587 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz8 qz9))

noncomputable def Ns372p76 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HMul.hMul Real Real Real qz5 qz587 (Zeta.RiemannSiegel.correction qz10)) 28969991 134217728 74265 67108864 305861269917559500725 2361183241434822606848 24331570601686135801 Ns372p74 Ns372p75 

noncomputable def Ns372p77 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos BSN.quadSignNeg 9 10 712564 1000 198 268435456 134217728 4503599627370496 Bool.false 356721960697 2476 618095470 48 84886744 8 

noncomputable def Ns372p78 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 712564 1000 97 150 268435456 134217728 4503599627370496 Bool.false 356721960697 2476 

noncomputable def Ns372p79 := Ns372p78 558195838 48 94906264 8 589812974 48 89478488 8 Bool.false 108296122 111707 Bool.true 127527869 Bool.true 308917068 14148475504056880 1 Bool.false 122784553 Bool.true Bool.false 109455051 Bool.true Bool.false 28400209 

noncomputable def Ns372p80 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 712564 1000 33 36 268435456 134217728 4503599627370496 Bool.false 356721960697 2476 

noncomputable def Ns372p81 := Ns372p80 480971758 48 109588312 8 522351262 48 101459064 8 Bool.false 100068794 82850 Bool.false 84105796 Bool.true 307076541 14148475504056880 1 Bool.false 82736444 Bool.true Bool.false 111133037 Bool.false Bool.false 108296122 

noncomputable def Ns372p82 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 712564 1000 217 115 268435456 134217728 4503599627370496 Bool.false 356721960697 2476 

noncomputable def Ns372p83 := Ns372p82 372130544 47 134217720 8 432030192 47 120047984 16 Bool.false 8853652 48754 Bool.false 55469808 Bool.false 382194714 14148475504056880 1 Bool.false 55075884 Bool.true Bool.false 265539968 Bool.false Bool.false 100068794 

noncomputable def Ns372p84 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 712564 1000 531 347 268435456 134217728 4503599627370496 Bool.false 356721960697 2476 

noncomputable def Ns372p85 := Ns372p84 186065264 47 189812528 16 294906480 47 154981288 8 Bool.true 268435360 2527 Bool.false 238457510 Bool.false 267092073 14148475504056880 1 Bool.false 208310051 Bool.false Bool.false 225151988 Bool.false Bool.false 8853652 

noncomputable def Ns372p86 := nat_lit 134482644044424400307257412540879162825402901359633 

noncomputable def Ns372p87 := nat_lit 101199011710837384899290463376401703546996654080 

noncomputable def Ns372p88 := nat_lit 88178187015873848590046532075520000 

noncomputable def Ns372p89 := nat_lit 376995696540316138041356442035740999680 

noncomputable abbrev qz352 := (@Eq.refl Real qz583)

noncomputable abbrev qz11 := qz352

noncomputable def Ns372p90 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 712564 1000 2030990816384 16000000 1425128 4000 2000 Ns372p88 Ns372p89 qz11 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns372p91 := nat_lit 1410152729615263599765827486124649090388096726960785326080 

noncomputable abbrev qz737 := (@instHSub Real Real.instSub)

noncomputable abbrev qz588 := qz737

noncomputable abbrev qz353 := qz588

noncomputable abbrev qz589 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz738 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz739 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz590 := (@HSub.hSub Real Real Real qz737 qz738 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz739 (@Nat.cast Real Real.instNatCast 1425128))))

noncomputable abbrev qz354 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 712564 4000) (Real.log (Enclosure.sfrac Bool.false 2030990816384 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz590))

noncomputable abbrev qz591 := (Enclosure.sfrac Bool.false 712564 2000)

noncomputable abbrev qz12 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz354 qz591) (@HMul.hMul Real Real Real qz349 qz591 (Real.log Real.pi)))

noncomputable def Ns372p92 := @Enclosure.Real.IsNear.addLit_ft_p qz12 (Enclosure.sfrac Bool.true Ns372p88 Ns372p89) 3740501524966326481 2814749767106560 28318704410667307 3072000000000000000000 Ns372p88 Ns372p89 0 1 Ns372p91 

noncomputable def Ns372p93 := nat_lit 1568880050817236302456422400000 

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz353 qz354 qz591)

noncomputable def Ns372p94 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (@HMul.hMul Real Real Real qz5 qz591 (Real.log Real.pi)) 122212194841708647529 70368744177664000 11727938238643 3000000000000000000 6842531375301 16777216000 178141 33554432000 Ns372p93 3740501524966326481 2814749767106560 

noncomputable abbrev qz14 := qz354

noncomputable def Ns372p95 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz591 147283311754815132777 70368744177664000 11727938238643 3000000000000000000 712564 2000 0 1 244424389683417295058000 122212194841708647529 70368744177664000 11727938238643 3000000000000000000 

noncomputable def Ns372p96 := nat_lit 1326610135873756050600729323224694784 

noncomputable def Ns372p97 := nat_lit 56826503969950067685588992 

noncomputable def Ns372p98 := nat_lit 4835703278458516698824704 

noncomputable def Ns372p99 := nat_lit 2254977053360755402095980718287251163665024619228242858576613143340480635098594269528692143745715433850847492155765394036884088055135639402607864056371559188530495553207330251199360177538446595151574650060800 

noncomputable def Ns372p100 := nat_lit 81534385020586831675699534769485732523950307948505017389710982050522375953940730232756592765250233844142385592280804605789175723653123642194457778019672089501464250358599338023436061066475131051455681658880 

noncomputable def Ns372p101 := nat_lit 1526080925875632044946016978662289473096707811048563268372374020790318719401482294618861230776785689503255443776263957877565719979870523764168113403378909010805772804936614408128337093147473897062400 

noncomputable def Ns372p102 := BSN.log_dyadic_bound 982414816384 3079566816384 9 8 Ns372p99 134217728 46080000 Ns372p100 Ns372p101 88730092 4061981632768 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 982414816384) (BSN.artanhQ 3079566816384) 0 8 Ns372p100 Ns372p99 Ns372p101 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz355 := (Real.log (Enclosure.sfrac Bool.false 2030990816384 16000000))

noncomputable abbrev qz356 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns372p103 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 712564 4000) qz355 712564 4000 0 1 3307737873980663 281474976710656 48828161 2250000000000000 589243732608789287483 281474976710656000 8698297428701 2250000000000000000 (Enclosure.Real.IsNear.const Bool.false 712564 4000) (BSN.isNear_log_sfrac 2030990816384 16000000 3307737873980663 281474976710656 48828161 2250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2030990816384) qz356)) Bool.false Ns372p97 Ns372p98 1000000737280000 46080000000000000000000 3307737873980663 281474976710656 48828161 2250000000000000 (BSN.log_rat_reduce_isNear 2030990816384 16000000 16 4061981632768 2097152000000 88730092 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns372p102 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p104 := BSN.arctan_dyadic_bound_f 1000 1425128 1 0 16777216 5760000 0 1 1 0 1 1 11772 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1425128) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1425128) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz592 := qz738

noncomputable abbrev qz357 := qz592

noncomputable abbrev qz15 := qz357

noncomputable abbrev qz593 := qz739

noncomputable abbrev qz358 := qz593

noncomputable abbrev qz16 := qz358

noncomputable abbrev qz740 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz594 := qz740

noncomputable abbrev qz359 := qz594

noncomputable abbrev qz17 := (@Enclosure.Real.IsNear.mulLit_ff qz359 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def Ns372p105 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1425128))) 884279719003555 562949953421312 1 2000000000000000 11772 16777216 1 5760000 14829124803290271318016 883884716230051 562949953421312 3125000009 18000000000000000 qz17 (Ns372p104 rfl) rfl rfl 

noncomputable abbrev qz360 := (@HMul.hMul Real Real Real qz584 qz589 qz590)

noncomputable abbrev qz18 := qz360

noncomputable abbrev qz361 := qz589

noncomputable abbrev qz19 := qz361

noncomputable abbrev qz362 := qz590

noncomputable abbrev qz20 := qz362

noncomputable abbrev qz363 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns372p106 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 712564 4000) qz355) qz18 589243732608789287483 281474976710656000 8698297428701 2250000000000000000 883884716230051 2251799813685248 3125000009 72000000000000000 Ns372p96 147283311754815132777 70368744177664000 11727938238643 3000000000000000000 (Ns372p103 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz20 1 4 0 1 883884716230051 562949953421312 3125000009 18000000000000000 883884716230051 2251799813685248 3125000009 72000000000000000 qz363 Ns372p105 rfl) 

noncomputable def Ns372p107 := @Ns372p92 Ns372p86 Ns372p87 28318704410667307 3072000000000000000000 (@Ns372p94 28318704410667307 3072000000000000000000 (Ns372p95 (Ns372p106 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 712564 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz591 (Real.log Real.pi) 712564 2000 0 1 38410761 33554432 1 67108864 6842531375301 16777216000 178141 33554432000 (Enclosure.Real.IsNear.const Bool.false 712564 2000) RS373to384.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns372p88 Ns372p89) 

noncomputable abbrev qz364 := (@instHAdd Real Real.instAdd)

noncomputable def Ns372p108 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns372p86 Ns372p87 28318704410667307 3072000000000000000000 44590245087 33554432 155 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz364 qz12 (Enclosure.sfrac Bool.true Ns372p88 Ns372p89)) Bool.false Ns372p86 Ns372p87 28318704410667307 3072000000000000000000 Ns372p90 (Ns372p107 rfl rfl)) 

noncomputable def Ns372p109 := nat_lit 7591876616101328442097664 

noncomputable def Ns372p110 := nat_lit 3503378881177961842801142531269134658584637462604027099283114648124883985222052198929766553316050732422177494540033309886897174920072754401 

noncomputable def Ns372p111 := nat_lit 69061887427279807374175457422696049589758900585025510522285359577850094671315332446731519433112496475662717985575392155893264493730122956800 

noncomputable def Ns372p112 := nat_lit 2486749783782124127506484006701486776393962217359755275173646223235408883227363259882511434909606312206337085904650545962332386456801 

noncomputable def Ns372p113 := nat_lit 17495173569393132424996568275276370804415142147495989673045540297432900988880512405062264799294080782340251828833101634739974991471228712161 

noncomputable def Ns372p114 := nat_lit 2417166059954793258096141009794361735641561520475892868279987585224753313496036635635603180158937376648195129495138725456264257280554303488000 

noncomputable abbrev qz365 := (BSN.sinEvenQ 68719476736)

noncomputable abbrev qz366 := (BSN.sinOddQ 68719476736)

noncomputable def Ns372p115 := BSN.sin_dyadic_bound_f 107887055607 68719476736 4 3 33554432 11531251 Ns372p110 Ns372p111 Ns372p112 Ns372p113 Ns372p114 Ns372p112 33554420 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107887055607) qz365 0 3 Ns372p110 Ns372p111 Ns372p112 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107887055607) qz366 0 3 Ns372p113 Ns372p114 Ns372p112 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz367 := (@Nat.cast Real Real.instNatCast 33554432)

noncomputable abbrev qz368 := (@Nat.cast Real Real.instNatCast Ns372p98)

noncomputable def Ns372p116 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44590245087) qz367) Bool.false 44590245087 33554432 155 16777216 Bool.true 33554420 33554432 1 5760000 (Ns372p108 rfl) (Enclosure.sfrac_false_div 44590245087 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44590245087) qz367) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns372p109) qz368) 226375608064910080 72057594037927936 Bool.false 33554420 33554432 211 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q1 44590245087 33554432 226375608064910080 72057594037927936 211 Ns372p109 Ns372p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554420 33554432 Ns372p109 Ns372p98 107887055607 68719476736 11531251 11520000 (Ns372p115 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p117 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns372p86 Ns372p87 28318704410667307 3072000000000000000000 356721960697 268435456 2476 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz364 qz12 (Enclosure.sfrac Bool.true Ns372p88 Ns372p89)) Bool.false Ns372p86 Ns372p87 28318704410667307 3072000000000000000000 Ns372p90 (Ns372p107 rfl rfl)) 

noncomputable def Ns372p118 := Ns372p85 48754 BSN.abs_quadSignPos (BSN.cos_quad_nat3 531 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 208310051 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 347 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 225151988 268435456) qz11 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 8388605 8388608 888259 94371840000 268435360 268435456 2527 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 8388605 8388608 888259 94371840000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 33554420 33554432 909577216 96636764160000 8388605 8388608 888259 94371840000 (Ns372p116 rfl rfl) rfl)) rfl) (Ns372p117 rfl) RS373to384.d7 

noncomputable def Ns372p119 := nat_lit 50777900649609536542873991680667173643447661557522992366293240123040000 

noncomputable def Ns372p120 := nat_lit 9783225446575624168688766434777683578849446968051522941942878087235502080 

noncomputable def Ns372p121 := nat_lit 10454133397878018005046969035342947430239811437046645901600100000000 

noncomputable def Ns372p122 := nat_lit 132972814056809364630757045023309185246523487241662142580260657303200000 

noncomputable def Ns372p123 := nat_lit 179359133187219776425960717970924198945573194414277920602286098265984204800 

noncomputable abbrev qz369 := (BSN.sinEvenQ 268435456)

noncomputable abbrev qz370 := (BSN.sinOddQ 268435456)

noncomputable def Ns372p124 := BSN.sin_dyadic_bound_f 238457510 268435456 3 2 268435456 134217728 Ns372p119 Ns372p120 Ns372p121 Ns372p122 Ns372p123 Ns372p121 208310051 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 238457510) qz369 0 2 Ns372p119 Ns372p120 Ns372p121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 238457510) qz370 0 2 Ns372p122 Ns372p123 Ns372p121 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p125 := nat_lit 79932985872668757176874475635804426923454321272778180653338665856545345 

noncomputable def Ns372p126 := nat_lit 25899297876577669892792633851712490512984877849525325792124027286081 

noncomputable def Ns372p127 := nat_lit 209306364136618000188178152877061202672026008769329336897937828818203201 

noncomputable def Ns372p128 := BSN.sin_dyadic_bound_f 267092073 268435456 3 2 268435456 134217728 Ns372p125 Ns372p120 Ns372p126 Ns372p127 Ns372p123 Ns372p126 225151988 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 267092073) qz369 0 2 Ns372p125 Ns372p120 Ns372p126 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 267092073) qz370 0 2 Ns372p127 Ns372p123 Ns372p126 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p129 := nat_lit 9467311145753190037905169514496 

noncomputable def Ns372p130 := nat_lit 623075623024179315423659559506411520 

noncomputable def Ns372p131 := nat_lit 4361529361169255207965616916544880640 

noncomputable def Ns372p132 := BSN.sin_dyadic_bound_f 55469808 268435456 2 1 268435456 134217728 Ns372p129 Ns372p130 Ns372p129 Ns372p129 Ns372p131 Ns372p129 55075884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 55469808) qz369 0 1 Ns372p129 Ns372p130 Ns372p129 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 55469808) qz370 0 1 Ns372p129 Ns372p131 Ns372p129 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p133 := nat_lit 29891431958560166757628829505981256488701774828829621367801498787320250276005535633903833598077193701744644096 

noncomputable def Ns372p134 := nat_lit 871683568514489007341798292243696146469029465094156570908284878217177001794361422139649254553384847460322508800 

noncomputable def Ns372p135 := nat_lit 9714402957883913954294637179977955670371140651934304729182182838570818464952704192630213798840216784896 

noncomputable def Ns372p136 := nat_lit 149331737420599250948986090857428830712225168667635961716349775101983350688340144178391917634524400555067641856 

noncomputable def Ns372p137 := nat_lit 30508924898007115256962940228529365126416031278295479981789970737601195062802649774887723909368469661111287808000 

noncomputable def Ns372p138 := BSN.sin_dyadic_bound_f 382194714 268435456 4 3 268435456 134217728 Ns372p133 Ns372p134 Ns372p135 Ns372p136 Ns372p137 Ns372p135 265539968 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 382194714) qz369 0 3 Ns372p133 Ns372p134 Ns372p135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 382194714) qz370 0 3 Ns372p136 Ns372p137 Ns372p135 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p139 := Ns372p83 82850 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 217 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 55075884 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 115 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 265539968 268435456) qz11 rfl rfl (Ns372p118 RS373to384.d9 RS373to384.d11 RS373to384.d13 RS373to384.d17 (Ns372p124 rfl rfl) (Ns372p128 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns372p117 rfl) RS373to384.d19 RS373to384.d21 RS373to384.d23 RS373to384.d25 RS373to384.d17 (Ns372p132 rfl rfl) (Ns372p138 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns372p140 := nat_lit 50038433105647144186771266355456 

noncomputable def Ns372p141 := BSN.sin_dyadic_bound_f 84105796 268435456 2 1 268435456 134217728 Ns372p140 Ns372p130 Ns372p140 Ns372p140 Ns372p131 Ns372p140 82736444 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 84105796) qz369 0 1 Ns372p140 Ns372p130 Ns372p140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 84105796) qz370 0 1 Ns372p140 Ns372p131 Ns372p140 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p142 := nat_lit 4789319845771960787591733901997657459624045764212497982876613927106296094044085843778702813724459396597560561 

noncomputable def Ns372p143 := nat_lit 67052582193422231333984484018745857420694574238012043916021913709013615522643186318434558042568065189255577600 

noncomputable def Ns372p144 := nat_lit 703007048395517250942816368391345606463208627736727340017906185770988985611514612870096084821727524081 

noncomputable def Ns372p145 := nat_lit 29035478914076574219440779550397489074415330641889836943946450092393690392484935072722500259609925174490051825 

noncomputable def Ns372p146 := nat_lit 6101784979601423051392588045705873025283206255659095996357994147520239012560529954977544781873693932222257561600 

noncomputable abbrev qz371 := (BSN.cosEvenQ 268435456)

noncomputable abbrev qz372 := (BSN.cosOddQ 268435456)

noncomputable def Ns372p147 := BSN.cos_dyadic_bound_f 307076541 268435456 4 3 268435456 134217728 Ns372p142 Ns372p143 Ns372p144 Ns372p145 Ns372p146 Ns372p144 111133037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 307076541) qz371 0 3 Ns372p142 Ns372p143 Ns372p144 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 307076541) qz372 0 3 Ns372p145 Ns372p146 Ns372p144 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p148 := Ns372p81 111707 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 33 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 82736444 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 111133037 268435456) qz11 rfl rfl (Ns372p139 rfl rfl) (Ns372p117 rfl) RS373to384.d27 RS373to384.d29 RS373to384.d31 RS373to384.d33 RS373to384.d17 (Ns372p141 rfl rfl) (Ns372p147 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p149 := nat_lit 4153067861514640110925835004415182095780649122469999766066763636920225 

noncomputable def Ns372p150 := nat_lit 69958553506764298776819012995102892821833094233017729734979342241 

noncomputable def Ns372p151 := nat_lit 10876969228213617910226786352209199131884750448126003072898143368236961 

noncomputable def Ns372p152 := BSN.sin_dyadic_bound_f 127527869 268435456 3 2 268435456 134217728 Ns372p149 Ns372p120 Ns372p150 Ns372p151 Ns372p123 Ns372p150 122784553 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 127527869) qz369 0 2 Ns372p149 Ns372p120 Ns372p150 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 127527869) qz370 0 2 Ns372p151 Ns372p123 Ns372p150 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p153 := nat_lit 4905300301528164601914738068312494891128467773271837061433914068585845604942866535441649722469315345704288256 

noncomputable def Ns372p154 := nat_lit 755271071165920938483283843824098835946560504650436489025593329508398010845521181829259820064231653376 

noncomputable def Ns372p155 := nat_lit 29738127546536499773865621916653077332581162790142893162637068008819081485999580320540845058279599728796631040 

noncomputable def Ns372p156 := BSN.cos_dyadic_bound_f 308917068 268435456 4 3 268435456 134217728 Ns372p153 Ns372p143 Ns372p154 Ns372p155 Ns372p146 Ns372p154 109455051 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 308917068) qz371 0 3 Ns372p153 Ns372p143 Ns372p154 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 308917068) qz372 0 3 Ns372p155 Ns372p146 Ns372p154 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p157 := Ns372p79 136921 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 97 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 122784553 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 150 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 109455051 268435456) qz11 rfl rfl (Ns372p148 rfl) (Ns372p117 rfl) RS373to384.d35 RS373to384.d37 RS373to384.d39 RS373to384.d41 RS373to384.d17 (Ns372p152 rfl rfl) (Ns372p156 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p158 := nat_lit 21365469912887553664807191971406939959452406900078279189827169542636801 

noncomputable def Ns372p159 := nat_lit 1087025049619513796520974048308631508761049663116835882438097565248389120 

noncomputable def Ns372p160 := nat_lit 5995750073910369287577538624365601053732529850041065417535822398721 

noncomputable def Ns372p161 := nat_lit 64084418238514840255846420836972088676249755640534755438646436983112961 

noncomputable def Ns372p162 := nat_lit 48916127232878120843443832173888417894247234840257614709714390436177510400 

noncomputable def Ns372p163 := BSN.cos_dyadic_bound_f 222448991 268435456 3 2 268435456 134217728 Ns372p158 Ns372p159 Ns372p160 Ns372p161 Ns372p162 Ns372p160 181420500 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 222448991) qz371 0 2 Ns372p158 Ns372p159 Ns372p160 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 222448991) qz372 0 2 Ns372p161 Ns372p162 Ns372p160 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz595 := (BSN.cos_quad_nat2 198 rfl)

noncomputable def Ns372p164 := Ns372p77 Bool.false 28400209 136921 Bool.true 222448991 14148475504056880 1 Bool.false 181420500 Bool.true Bool.true 28969991 148530 BSN.abs_quadSignNeg qz595 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 181420500 268435456) qz11 rfl (Ns372p157 rfl) (Ns372p117 rfl) RS373to384.d43 RS373to384.d45 RS373to384.d17 (Ns372p163 rfl rfl) rfl 

noncomputable def Ns372p165 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) 28969991 268435456 148530 268435456 28969991 268435456 148530 268435456 15553145488801792 28969991 134217728 74265 67108864 (Ns372p164 rfl rfl rfl rfl) 

noncomputable def Ns372p166 := @Enclosure.Real.IsNear.mulLit_ff qz587 (Zeta.RiemannSiegel.correction qz10) 2570567 8388608 1 16777216 118985916304675 281474976710656 47197050892001 1583296743997440000 305861269917559500725 2361183241434822606848 

noncomputable abbrev qz596 := (@HPow.hPow Real Real Real qz7 qz8 qz9)

noncomputable def Ns372p167 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz596 1 1 0 1 2570567 8388608 1 16777216 2570567 8388608 1 16777216 

noncomputable abbrev qz21 := (@Enclosure.Real.IsNear.of_eq qz350 (@HMul.hMul Real Real Real qz349 qz348 qz347) Bool.false 951335823773 8388608000 178141 8388608000 (BSN.t_div_two_pi_mk qz348 712564 1000 qz352) (@Enclosure.Real.IsNear.mulLit_ff qz348 qz347 712564 1000 0 1 5340353 33554432 1 33554432 951335823773 8388608000 178141 8388608000 (Enclosure.Real.IsNear.const Bool.false 712564 1000) RS373to384.d48 rfl))

noncomputable def Ns372p168 := @Enclosure.Real.IsNear.sqrt_image qz8 951335823773 8388608000 178141 8388608000 178665965 178665999 16777216 qz21 

noncomputable abbrev qz741 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 712564 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz597 := qz741

noncomputable abbrev qz373 := qz597

noncomputable abbrev qz22 := qz373

noncomputable def Ns372p169 := @Enclosure.Real.IsNear.sqrt_image qz22 89332991 8388608 17 16777216 54749588 54749595 16777216 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 357331964 33554432 34 33554432 89332991 8388608 17 16777216 (Ns372p168 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz598 := (Real.sqrt qz741)

noncomputable abbrev qz374 := qz598

noncomputable abbrev qz23 := qz374

noncomputable def Ns372p170 := @Enclosure.Real.IsNear.inv_image qz23 109499183 33554432 7 33554432 5141133 5141135 16777216 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 109499183 33554432 7 33554432 109499183 33554432 7 33554432 (Ns372p169 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns372p171 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz23) Bool.false 10282268 33554432 2 33554432 2570567 8388608 1 16777216 (Ns372p170 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz375 := (@HMul.hMul Real Real Real qz584 qz582 qz586)

noncomputable abbrev qz24 := (Real.cos qz375)

noncomputable abbrev qz599 := (@HMul.hMul Real Real Real qz733 qz736 qz736)

noncomputable abbrev qz600 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz376 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz599 qz586) qz600)

noncomputable abbrev qz25 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz376))

noncomputable def Ns372p172 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz10) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz24) qz25) Bool.false 118985916304675 

noncomputable def Ns372p173 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz24) qz25 56754145 33554432 633 

noncomputable abbrev qz26 := (@Neg.neg Real Real.instNeg (Real.cos qz375))

noncomputable def Ns372p174 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz24) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz26)) Bool.true 56754145 33554432 633 33554432 (BSN.inv_eq_neg_inv_neg qz24) 

noncomputable def Ns372p175 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz26) Bool.false 56754145 33554432 633 33554432 56754145 33554432 

noncomputable def Ns372p176 := @Enclosure.Real.IsNear.recentre' qz24 Bool.true 19838197 33554432 1271954432 193273528320000 19838197 33554432 1242143 188743680000 

noncomputable abbrev qz27 := qz375

noncomputable abbrev qz377 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable def Ns372p177 := @Enclosure.Real.IsNear.cos_image qz27 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 34223951) qz377) Bool.false 34223951 8388608 215 33554432 Bool.true 19838197 33554432 1 

noncomputable def Ns372p178 := nat_lit 458763282047325991174763063 

noncomputable def Ns372p179 := nat_lit 72057594037927936000000000000000 

noncomputable def Ns372p180 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz10 884279719003555 140737488355328 1 500000000000000 5446911 8388608 17 16777216 4816592928517372768605 1180591620717411303424 Ns372p178 

noncomputable def Ns372p181 := @Enclosure.Real.IsNear.subLit_ff_p qz22 qz1 89332991 8388608 17 16777216 10 1 0 1 5446911 5446911 8388608 17 

noncomputable abbrev qz378 := (Enclosure.Real.IsNear.const Bool.false 10 1)

noncomputable def Ns372p182 := @Ns372p181 16777216 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 357331964 33554432 34 33554432 89332991 8388608 17 16777216 (Ns372p168 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns372p183 := @Enclosure.Real.IsNear.recentre' qz27 Bool.false 4816592928517372768605 1180591620717411303424 Ns372p178 Ns372p179 34223951 8388608 215 33554432 (@Ns372p180 Ns372p179 RS373to384.d47 (Ns372p182 rfl rfl) rfl) 

noncomputable def Ns372p184 := nat_lit 1208925819614629174706176 

noncomputable def Ns372p185 := nat_lit 647690409340203045985273895169098958046307464880375338727549180434765721565365591108877121 

noncomputable def Ns372p186 := nat_lit 20052072892042597411705012245279816272850392000149059967199507548332190919545345701492817920 

noncomputable def Ns372p187 := nat_lit 298591264545327354815700862231947718950600493409129647483864648123461952178052447992641 

noncomputable def Ns372p188 := nat_lit 1942474045491518483246190283782832978701021193654307756887679812008050240791740668430646081 

noncomputable def Ns372p189 := nat_lit 902343280141916883526725551037591732278267640006707698523977839674948591379540556567176806400 

noncomputable abbrev qz379 := (BSN.cosEvenQ 68719476736)

noncomputable abbrev qz380 := (BSN.cosOddQ 68719476736)

noncomputable def Ns372p190 := BSN.cos_dyadic_bound_f 64474003319 68719476736 3 2 33554432 11531251 Ns372p185 Ns372p186 Ns372p187 Ns372p188 Ns372p189 Ns372p187 19838197 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 64474003319) qz379 0 2 Ns372p185 Ns372p186 Ns372p187 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 64474003319) qz380 0 2 Ns372p188 Ns372p189 Ns372p187 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p191 := @Ns372p177 5760000 (Ns372p183 rfl) (Enclosure.sfrac_false_div 34223951 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 34223951) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1134238661427537213652992) (@Nat.cast Real Real.instNatCast Ns372p184)) 226375608064910080 72057594037927936 Bool.false 19838197 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q2 34223951 8388608 226375608064910080 72057594037927936 0 1134238661427537213652992 Ns372p184 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 19838197 33554432 1134238661427537213652992 Ns372p184 64474003319 68719476736 11531251 11520000 (Ns372p190 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p192 := @Enclosure.Real.IsNear.inv_image qz26 19838197 33554432 1242143 188743680000 28376756 28377389 16777216 (@Enclosure.Real.IsNear.neg qz24 Bool.true 19838197 33554432 1242143 188743680000 (Ns372p176 (Ns372p191 rfl rfl) rfl)) 

noncomputable def Ns372p193 := Ns372p174 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz26) Bool.false 56754145 33554432 633 33554432 (@Ns372p175 633 33554432 (Ns372p192 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p194 := @Enclosure.Real.IsNear.recentre' qz25 Bool.true 4193030 16777216 

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz349 qz346 qz376)

noncomputable def Ns372p195 := @Enclosure.Real.IsNear.cos_image qz28 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3823943)) (@Nat.cast Real Real.instNatCast 2097152)) Bool.true 3823943 2097152 

noncomputable def Ns372p196 := nat_lit 18058060301044380476409997405 

noncomputable def Ns372p197 := nat_lit 9903520314283042199192993792 

noncomputable def Ns372p198 := nat_lit 17692149541364308482477124174461131 

noncomputable def Ns372p199 := @Enclosure.Real.IsNear.recentre' qz28 Bool.true Ns372p196 Ns372p197 Ns372p198 

noncomputable def Ns372p200 := nat_lit 1208925819614629174706176000000000000000 

noncomputable abbrev qz29 := qz376

noncomputable def Ns372p201 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz29 884279719003555 140737488355328 1 500000000000000 20421208259071 

noncomputable abbrev qz381 := (@HSub.hSub Real Real Real qz588 qz599 qz586)

noncomputable abbrev qz30 := qz381

noncomputable abbrev qz382 := qz600

noncomputable abbrev qz31 := qz382

noncomputable def Ns372p202 := @Enclosure.Real.IsNear.subLit_tf qz30 qz31 16023161747967 70368744177664 655602909 281474976710656 1 16 

noncomputable abbrev qz383 := qz599

noncomputable abbrev qz32 := qz383

noncomputable def Ns372p203 := @Enclosure.Real.IsNear.subLit_ff_n qz32 qz10 29668839441921 70368744177664 370390237 281474976710656 5446911 8388608 17 16777216 

noncomputable def Ns372p204 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz10 5446911 8388608 17 16777216 5446911 8388608 17 16777216 29668839441921 70368744177664 

noncomputable def Ns372p205 := nat_lit 1607168873315165659365994453188204825577080790079370298870518273646309185333575688481 

noncomputable def Ns372p206 := nat_lit 3466537250751077332112698720796095110148055492926080949987665366995300109908547993600 

noncomputable def Ns372p207 := nat_lit 9775453637075478038750269017694620098315927580656500297584175889473525879284001 

noncomputable def Ns372p208 := nat_lit 9707618351424835128538166938250984029531462686986623312646242241409973788611069485345 

noncomputable def Ns372p209 := nat_lit 315454889818348037222255583592444655023473049856273366448877548396572310001677867417600 

noncomputable def Ns372p210 := BSN.cos_dyadic_bound_t 3823943 2097152 4 3 16777216 5760000 Ns372p205 Ns372p206 Ns372p207 Ns372p208 Ns372p209 Ns372p207 4193030 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3823943) (BSN.cosEvenQ 2097152) 0 3 Ns372p205 Ns372p206 Ns372p207 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3823943) (BSN.cosOddQ 2097152) 0 3 Ns372p208 Ns372p209 Ns372p207 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz384 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns372p211 := @Ns372p194 716868608 48318382080000 2096515 8388608 700067 47185920000 (@Ns372p195 123 8388608 Bool.true 4193030 16777216 1 5760000 (@Ns372p199 Ns372p200 3823943 2097152 123 8388608 (@Ns372p201 70368744177664 655602909 281474976710656 Ns372p196 Ns372p197 Ns372p198 Ns372p200 RS373to384.d47 (@Ns372p202 0 1 326739332145136 20421208259071 70368744177664 655602909 281474976710656 (@Ns372p203 134412022824289959936 16023161747967 70368744177664 655602909 281474976710656 (@Ns372p204 370390237 281474976710656 (Ns372p182 rfl rfl) (Ns372p182 rfl rfl) rfl) (Ns372p182 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 3823943 2097152) (BSN.cos_neg_of_bound 3823943 2097152 Bool.true 4193030 16777216 1 5760000 (Ns372p210 rfl rfl)) rfl rfl) 

noncomputable abbrev qz33 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 10) (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 10 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1))

noncomputable def Ns372p212 := @Ns372p166 24331570601686135801 Ns372p74 (Ns372p167 qz33 (@Enclosure.Real.IsNear.of_eq qz596 (@Inv.inv Real Real.instInv qz23) Bool.false 2570567 8388608 1 16777216 (BSN.rpow_neg_quarter_mk qz8 (BSN.t_div_two_pi_nonneg qz4 712564 1000 qz11)) Ns372p171) rfl) (@Ns372p172 281474976710656 47197050892001 1583296743997440000 (BSN.correction_mk qz10 (BSN.cos_two_pi_p_ne_zero_mk qz4 712564 1000 10 qz11 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 712564 1000 10 qz11 rfl rfl rfl))) (@Ns372p173 33554432 2096515 8388608 700067 47185920000 118985916304675 281474976710656 47197050892001 1583296743997440000 Ns372p193 (Ns372p211 rfl) rfl)) 

noncomputable abbrev qz34 := qz353

noncomputable def Ns372p213 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 815506741294616620981 2361183241434822606848 2963919887925933175801 Ns372p74 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HMul.hMul Real Real Real qz5 qz587 (Zeta.RiemannSiegel.correction qz10))) Bool.true 815506741294616620981 2361183241434822606848 2963919887925933175801 Ns372p74 (BSN.hardyZApproximantRS₀_eq qz4 10 (@BSN.floor_sqrt_eq_dec qz4 712564 1000 10 qz11 rfl rfl rfl)) (@Ns372p76 815506741294616620981 2361183241434822606848 2963919887925933175801 Ns372p74 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10)) Bool.true 28969991 134217728 74265 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (Ns372p165 (Ns372p164 rfl rfl rfl rfl) rfl rfl)) (Ns372p212 rfl) rfl rfl)) 

theorem RS373to384.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 815506741294616620981 2361183241434822606848 2963919887925933175801 Ns372p74 := Ns372p213 

theorem RS373to384.d50 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS373to384.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS373to384.d3 a b h)) 

noncomputable def Ns372p214 := nat_lit 8854437155380584775680000 

noncomputable def Ns372p215 := nat_lit 631419138868534417408370147328 

noncomputable abbrev qz742 := (Enclosure.sfrac Bool.false 713892 1000)

noncomputable abbrev qz601 := qz742

noncomputable abbrev qz385 := qz601

noncomputable abbrev qz35 := qz385

noncomputable abbrev qz743 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 713892 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz602 := qz743

noncomputable abbrev qz386 := qz602

noncomputable abbrev qz36 := qz386

noncomputable abbrev qz744 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 713892 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz603 := qz744

noncomputable abbrev qz387 := qz603

noncomputable abbrev qz37 := qz387

noncomputable abbrev qz604 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz36 qz9))

noncomputable def Ns372p216 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) (@HMul.hMul Real Real Real qz5 qz604 (Zeta.RiemannSiegel.correction qz37)) 151318857 134217728 148811 134217728 619619784164506020573 4722366482869645213696 89528292714393894661 Ns372p214 Ns372p215 

noncomputable def Ns372p217 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos BSN.quadSignNeg 9 10 713892 1000 198 268435456 134217728 4503599627370496 Bool.false 357565384131 2481 618095470 48 84886744 8 

noncomputable def Ns372p218 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 713892 1000 97 150 268435456 134217728 4503599627370496 Bool.false 357565384131 2481 

noncomputable def Ns372p219 := Ns372p218 558195838 48 94906264 8 589812974 48 89478488 8 Bool.false 276436401 111919 Bool.true 25388508 Bool.true 248765263 14148475504056880 1 Bool.false 25350673 Bool.true Bool.false 161184168 Bool.true Bool.false 213745527 

noncomputable def Ns372p220 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 713892 1000 33 36 268435456 134217728 4503599627370496 Bool.false 357565384131 2481 

noncomputable def Ns372p221 := Ns372p220 480971758 48 109588312 8 522351262 48 101459064 8 Bool.false 288349150 83008 Bool.false 288798736 Bool.true 157335583 14148475504056880 1 Bool.false 236222809 Bool.true Bool.false 223631619 Bool.false Bool.false 276436401 

noncomputable def Ns372p222 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 713892 1000 217 116 268435456 134217728 4503599627370496 Bool.false 357565384131 2481 

noncomputable def Ns372p223 := Ns372p222 372130544 47 134217720 8 432030192 47 120047984 16 Bool.false 343762216 48848 Bool.false 404703879 Bool.false 230224624 14148475504056880 1 Bool.false 267900267 Bool.true Bool.false 175614207 Bool.false Bool.false 288349150 

noncomputable def Ns372p224 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 713892 1000 532 348 268435456 134217728 4503599627370496 Bool.false 357565384131 2481 

noncomputable def Ns372p225 := Ns372p224 186065264 47 189812528 16 294906480 47 154981288 8 Bool.false 268435424 2535 Bool.false 413128845 Bool.false 297222274 14148475504056880 1 Bool.false 8527148 Bool.false Bool.false 120026247 Bool.false Bool.false 343762216 

noncomputable def Ns372p226 := nat_lit 37865281122267949034782228878601916233510771390383 

noncomputable def Ns372p227 := nat_lit 28426644344504643212709912972391089523864371200 

noncomputable def Ns372p228 := nat_lit 89002940068588934825725362831360000 

noncomputable def Ns372p229 := nat_lit 381231008619877381495221282171487518720 

noncomputable abbrev qz605 := (@Eq.refl Real qz742)

noncomputable abbrev qz388 := qz605

noncomputable abbrev qz38 := qz388

noncomputable def Ns372p230 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz35 713892 1000 2038568150656 16000000 1427784 4000 2000 Ns372p228 Ns372p229 qz38 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns372p231 := nat_lit 3573416251625691323438622938574799462482281155929802014720 

noncomputable abbrev qz606 := (@HSub.hSub Real Real Real qz737 qz738 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz739 (@Nat.cast Real Real.instNatCast 1427784))))

noncomputable abbrev qz389 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 713892 4000) (Real.log (Enclosure.sfrac Bool.false 2038568150656 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz606))

noncomputable abbrev qz607 := (Enclosure.sfrac Bool.false 713892 2000)

noncomputable abbrev qz39 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz389 qz607) (@HMul.hMul Real Real Real qz349 qz607 (Real.log Real.pi)))

noncomputable def Ns372p232 := @Enclosure.Real.IsNear.addLit_ft_p qz39 (Enclosure.sfrac Bool.true Ns372p228 Ns372p229) 9373363648630248051 7036874417766400 85113699804394813 9216000000000000000000 Ns372p228 Ns372p229 0 1 Ns372p231 

noncomputable def Ns372p233 := nat_lit 786294732898088878426030080000 

noncomputable abbrev qz40 := (@HSub.hSub Real Real Real qz353 qz389 qz607)

noncomputable def Ns372p234 := @Enclosure.Real.IsNear.subLit_ff_p qz40 (@HMul.hMul Real Real Real qz5 qz607 (Real.log Real.pi)) 61243390265738370111 35184372088832000 35248658513737 9000000000000000000 6855283747953 16777216000 178473 33554432000 Ns372p233 9373363648630248051 7036874417766400 

noncomputable abbrev qz41 := qz389

noncomputable def Ns372p235 := @Enclosure.Real.IsNear.subLit_ff_p qz41 qz607 73802311145358597183 35184372088832000 35248658513737 9000000000000000000 713892 2000 0 1 122486780531476740222000 61243390265738370111 35184372088832000 35248658513737 9000000000000000000 

noncomputable def Ns372p236 := nat_lit 1329504243893273528498851318251651072 

noncomputable def Ns372p237 := nat_lit 56844511703132101161254912 

noncomputable def Ns372p238 := nat_lit 2345408894646954419105253540574584132303818817793940393805878194844777296748417602615712417552737143474418289887450772764638272586743661324739782891642040480197669110491492037941194626906538196012349836492800 

noncomputable def Ns372p239 := nat_lit 85755305996568260457078062327710798383228868492031709011222058093434137029889098476195101364597851111784824228799897080720119752495209574311281913175688219965944563605436654044105657625790015537338730414080 

noncomputable def Ns372p240 := nat_lit 1725707253781916230893443999670910755497053689869615607709580980493130180761651666921170482844518550311467792972608134881696519328308247746845906856790382305280533831375125647764319815711618131558400 

noncomputable def Ns372p241 := BSN.log_dyadic_bound 989992150656 3087144150656 9 8 Ns372p238 134217728 46080000 Ns372p239 Ns372p240 89229907 4077136301312 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 989992150656) (BSN.artanhQ 3087144150656) 0 8 Ns372p239 Ns372p238 Ns372p240 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz390 := (Real.log (Enclosure.sfrac Bool.false 2038568150656 16000000))

noncomputable def Ns372p242 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 713892 4000) qz390 713892 4000 0 1 3308786062007543 281474976710656 48828161 2250000000000000 590528974844672221839 281474976710656000 2904836126051 750000000000000000 (Enclosure.Real.IsNear.const Bool.false 713892 4000) (BSN.isNear_log_sfrac 2038568150656 16000000 3308786062007543 281474976710656 48828161 2250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2038568150656) qz356)) Bool.false Ns372p237 Ns372p98 1000000737280000 46080000000000000000000 3308786062007543 281474976710656 48828161 2250000000000000 (BSN.log_rat_reduce_isNear 2038568150656 16000000 16 4077136301312 2097152000000 89229907 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns372p241 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p243 := BSN.arctan_dyadic_bound_f 1000 1427784 1 0 16777216 5760000 0 1 1 0 1 1 11750 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1427784) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1427784) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns372p244 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1427784))) 884279719003555 562949953421312 1 2000000000000000 11750 16777216 1 5760000 14829137188189246586880 883885454427555 562949953421312 3125000009 18000000000000000 qz17 (Ns372p243 rfl) rfl rfl 

noncomputable abbrev qz391 := (@HMul.hMul Real Real Real qz584 qz589 qz606)

noncomputable abbrev qz42 := qz391

noncomputable abbrev qz392 := qz606

noncomputable abbrev qz43 := qz392

noncomputable def Ns372p245 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 713892 4000) qz390) qz42 590528974844672221839 281474976710656000 2904836126051 750000000000000000 883885454427555 2251799813685248 3125000009 72000000000000000 Ns372p236 73802311145358597183 35184372088832000 35248658513737 9000000000000000000 (Ns372p242 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz43 1 4 0 1 883885454427555 562949953421312 3125000009 18000000000000000 883885454427555 2251799813685248 3125000009 72000000000000000 qz363 Ns372p244 rfl) 

noncomputable def Ns372p246 := @Ns372p232 Ns372p226 Ns372p227 85113699804394813 9216000000000000000000 (@Ns372p234 85113699804394813 9216000000000000000000 (Ns372p235 (Ns372p245 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 713892 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz607 (Real.log Real.pi) 713892 2000 0 1 38410761 33554432 1 67108864 6855283747953 16777216000 178473 33554432000 (Enclosure.Real.IsNear.const Bool.false 713892 2000) RS373to384.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns372p228 Ns372p229) 

noncomputable def Ns372p247 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns372p226 Ns372p227 85113699804394813 9216000000000000000000 5586959127 4194304 311 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz364 qz39 (Enclosure.sfrac Bool.true Ns372p228 Ns372p229)) Bool.false Ns372p226 Ns372p227 85113699804394813 9216000000000000000000 Ns372p230 (Ns372p246 rfl rfl)) 

noncomputable def Ns372p248 := nat_lit 3506997881578141128677778222783176330587658173421144108666471212915242726430273815802127587470214535714530700234619378706716284647009816576 

noncomputable def Ns372p249 := nat_lit 2494448727374965476023924135542651981119147220020358264786722251159633718774907485535259003448988131496391975590815394870426653822976 

noncomputable def Ns372p250 := nat_lit 17513223752609356157951331342348912708696220772741148572192955722401291767697402941808199388640467585664258429459769163184918349006149390336 

noncomputable def Ns372p251 := BSN.sin_dyadic_bound_f 107914850926 68719476736 4 3 33554432 11531251 Ns372p248 Ns372p111 Ns372p249 Ns372p250 Ns372p114 Ns372p249 33554428 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107914850926) qz365 0 3 Ns372p248 Ns372p111 Ns372p249 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107914850926) qz366 0 3 Ns372p250 Ns372p114 Ns372p249 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz608 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable def Ns372p252 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz35) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5586959127) qz608) Bool.false 5586959127 4194304 311 33554432 Bool.false 33554428 33554432 1 5760000 (Ns372p247 rfl) (Enclosure.sfrac_false_div 5586959127 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5586959127) qz608) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949229067229869274824704) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 33554428 33554432 211 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 5586959127 4194304 226375608064910080 72057594037927936 211 949229067229869274824704 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554428 33554432 949229067229869274824704 604462909807314587353088 107914850926 68719476736 11531251 11520000 (Ns372p251 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p253 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns372p226 Ns372p227 85113699804394813 9216000000000000000000 357565384131 268435456 2481 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz364 qz39 (Enclosure.sfrac Bool.true Ns372p228 Ns372p229)) Bool.false Ns372p226 Ns372p227 85113699804394813 9216000000000000000000 Ns372p230 (Ns372p246 rfl rfl)) 

noncomputable def Ns372p254 := Ns372p225 48848 BSN.abs_quadSignPos (BSN.cos_quad_nat0 532 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 8527148 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 348 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 120026247 268435456) qz38 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) Bool.false 8388607 8388608 1782143 188743680000 268435424 268435456 2535 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 8388607 8388608 1782143 188743680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz35) qz35) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 33554428 33554432 1824914432 193273528320000 8388607 8388608 1782143 188743680000 (Ns372p252 rfl rfl) rfl)) rfl) (Ns372p253 rfl) RS373to384.d7 

noncomputable def Ns372p255 := nat_lit 15726619959347690745223399736683938198121505747637100996687822974215757484565224327687097604005945520445640625 

noncomputable def Ns372p256 := nat_lit 24718734112959082368673828498152015019782682117665550606732826188756551948296594616238869607461181640625 

noncomputable def Ns372p257 := nat_lit 95196336760613547512521819242506314412920121997149119246664149119634572069678032418837199121491385338583240625 

noncomputable def Ns372p258 := BSN.cos_dyadic_bound_f 413128845 268435456 4 3 268435456 134217728 Ns372p255 Ns372p143 Ns372p256 Ns372p257 Ns372p146 Ns372p256 8527148 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 413128845) qz371 0 3 Ns372p255 Ns372p143 Ns372p256 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 413128845) qz372 0 3 Ns372p257 Ns372p146 Ns372p256 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p259 := nat_lit 4202992175033242889712337854382470256675673700898477905556034542319637585640346166433518348814900945732243456 

noncomputable def Ns372p260 := nat_lit 475309211372154399340994348289578750711045782849469554014948557698244802316420244704502701743255064576 

noncomputable def Ns372p261 := nat_lit 25482955647019564843789843097164758778324062300269414222280328256757251756921329223910269674683641513817149440 

noncomputable def Ns372p262 := BSN.cos_dyadic_bound_f 297222274 268435456 4 3 268435456 134217728 Ns372p259 Ns372p143 Ns372p260 Ns372p261 Ns372p146 Ns372p260 120026247 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 297222274) qz371 0 3 Ns372p259 Ns372p143 Ns372p260 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 297222274) qz372 0 3 Ns372p261 Ns372p146 Ns372p260 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p263 := nat_lit 37593186355593491809835957535975246503339258500722140440769780204766163240389887509578160093926679320281553441 

noncomputable def Ns372p264 := nat_lit 19304048692833307057020222551477375906323977086984161085112980117052268689217967426448115823923406903841 

noncomputable def Ns372p265 := nat_lit 187767673584348332556132888454962951923723068863818208370948170397158624176444240340767045528110565460005165601 

noncomputable def Ns372p266 := BSN.sin_dyadic_bound_f 404703879 268435456 4 3 268435456 134217728 Ns372p263 Ns372p134 Ns372p264 Ns372p265 Ns372p137 Ns372p264 267900267 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 404703879) qz369 0 3 Ns372p263 Ns372p134 Ns372p264 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 404703879) qz370 0 3 Ns372p265 Ns372p137 Ns372p264 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p267 := nat_lit 24514087525190801155204288083508462318385083365577178563943327026118656 

noncomputable def Ns372p268 := nat_lit 7892492518122873424820106848098434299456849631425934575311966437376 

noncomputable def Ns372p269 := nat_lit 73526477590536157718763224036829190086556336397468683822679357145481216 

noncomputable def Ns372p270 := BSN.cos_dyadic_bound_f 230224624 268435456 3 2 268435456 134217728 Ns372p267 Ns372p159 Ns372p268 Ns372p269 Ns372p162 Ns372p268 175614207 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 230224624) qz371 0 2 Ns372p267 Ns372p159 Ns372p268 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 230224624) qz372 0 2 Ns372p269 Ns372p162 Ns372p268 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p271 := Ns372p223 83008 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 217 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267900267 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 116 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 175614207 268435456) qz38 rfl rfl (Ns372p254 RS373to384.d9 RS373to384.d11 RS373to384.d13 RS373to384.d17 (Ns372p258 rfl rfl) (Ns372p262 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns372p253 rfl) RS373to384.d19 RS373to384.d21 RS373to384.d23 RS373to384.d25 RS373to384.d17 (Ns372p266 rfl rfl) (Ns372p270 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns372p272 := nat_lit 109273491401489251913947927554222438888425673661294063933896496009707520 

noncomputable def Ns372p273 := nat_lit 48390744608028778663871801120944009072773675796955960658544669229056 

noncomputable def Ns372p274 := nat_lit 286114130560249327466312589249720097264520845066384619700091274370482176 

noncomputable def Ns372p275 := BSN.sin_dyadic_bound_f 288798736 268435456 3 2 268435456 134217728 Ns372p272 Ns372p120 Ns372p273 Ns372p274 Ns372p123 Ns372p273 236222809 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 288798736) qz369 0 2 Ns372p272 Ns372p120 Ns372p273 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 288798736) qz370 0 2 Ns372p274 Ns372p123 Ns372p273 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p276 := nat_lit 5345731216232479640499698514359620986717377609838503126203762082737921 

noncomputable def Ns372p277 := nat_lit 375504918420352129200026820492668007176870581463893877133406007041 

noncomputable def Ns372p278 := nat_lit 16036442638860598217240695489437877624137779088352581590857019436199681 

noncomputable def Ns372p279 := BSN.cos_dyadic_bound_f 157335583 268435456 3 2 268435456 134217728 Ns372p276 Ns372p159 Ns372p277 Ns372p278 Ns372p162 Ns372p277 223631619 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 157335583) qz371 0 2 Ns372p276 Ns372p159 Ns372p277 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 157335583) qz372 0 2 Ns372p278 Ns372p162 Ns372p277 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p280 := Ns372p221 111919 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 33 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 236222809 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 223631619 268435456) qz38 rfl rfl (Ns372p271 rfl rfl) (Ns372p253 rfl) RS373to384.d27 RS373to384.d29 RS373to384.d31 RS373to384.d33 RS373to384.d17 (Ns372p275 rfl rfl) (Ns372p279 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p281 := nat_lit 415478656110317897004479652096 

noncomputable def Ns372p282 := BSN.sin_dyadic_bound_f 25388508 268435456 2 1 268435456 134217728 Ns372p281 Ns372p130 Ns372p281 Ns372p281 Ns372p131 Ns372p281 25350673 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 25388508) qz369 0 1 Ns372p281 Ns372p130 Ns372p281 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 25388508) qz370 0 1 Ns372p281 Ns372p131 Ns372p281 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p283 := nat_lit 33420917344035014364897468472778534885968037937526127460407926636732801 

noncomputable def Ns372p284 := nat_lit 14666209725856196084013080301908415918032066213199791344785783054721 

noncomputable def Ns372p285 := nat_lit 100233419612653330702524379257731787826068049680151982798534208344088961 

noncomputable def Ns372p286 := BSN.cos_dyadic_bound_f 248765263 268435456 3 2 268435456 134217728 Ns372p283 Ns372p159 Ns372p284 Ns372p285 Ns372p162 Ns372p284 161184168 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 248765263) qz371 0 2 Ns372p283 Ns372p159 Ns372p284 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 248765263) qz372 0 2 Ns372p285 Ns372p162 Ns372p284 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p287 := Ns372p219 137180 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 97 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 25350673 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 150 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 161184168 268435456) qz38 rfl rfl (Ns372p280 rfl) (Ns372p253 rfl) RS373to384.d35 RS373to384.d37 RS373to384.d39 RS373to384.d41 RS373to384.d17 (Ns372p282 rfl rfl) (Ns372p286 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p288 := nat_lit 13919381798892777973366300493536956062726759557455364415453255711061601 

noncomputable def Ns372p289 := nat_lit 2545326248449718472605243802536511332867529791730847696542691751521 

noncomputable def Ns372p290 := nat_lit 41753054744181434483153690993005795165514543612782631550966681749681761 

noncomputable def Ns372p291 := BSN.cos_dyadic_bound_f 199856341 268435456 3 2 268435456 134217728 Ns372p288 Ns372p159 Ns372p289 Ns372p290 Ns372p162 Ns372p289 197410464 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 199856341) qz371 0 2 Ns372p288 Ns372p159 Ns372p289 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 199856341) qz372 0 2 Ns372p290 Ns372p162 Ns372p289 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p292 := Ns372p217 Bool.false 213745527 137180 Bool.true 199856341 14148475504056880 1 Bool.false 197410464 Bool.true Bool.false 151318857 148811 BSN.abs_quadSignNeg qz595 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 197410464 268435456) qz38 rfl (Ns372p287 rfl) (Ns372p253 rfl) RS373to384.d43 RS373to384.d45 RS373to384.d17 (Ns372p291 rfl rfl) rfl 

noncomputable def Ns372p293 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) 151318857 268435456 148811 268435456 151318857 268435456 148811 268435456 81238692760387584 151318857 134217728 148811 134217728 (Ns372p292 rfl rfl rfl rfl) 

noncomputable def Ns372p294 := @Enclosure.Real.IsNear.mulLit_ff qz604 (Zeta.RiemannSiegel.correction qz37) 5138741 16777216 1 16777216 120578130745353 281474976710656 52134671512549 1583296743997440000 619619784164506020573 4722366482869645213696 

noncomputable abbrev qz609 := (@HPow.hPow Real Real Real qz7 qz36 qz9)

noncomputable def Ns372p295 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz609 1 1 0 1 5138741 16777216 1 16777216 5138741 16777216 1 16777216 

noncomputable def Ns372p296 := @Enclosure.Real.IsNear.sqrt_image qz36 953108820969 8388608000 178473 8388608000 178832377 178832411 16777216 (@Enclosure.Real.IsNear.of_eq qz36 (@HMul.hMul Real Real Real qz5 qz35 qz3) Bool.false 953108820969 8388608000 178473 8388608000 (BSN.t_div_two_pi_mk qz35 713892 1000 qz38) (@Enclosure.Real.IsNear.mulLit_ff qz35 qz3 713892 1000 0 1 5340353 33554432 1 33554432 953108820969 8388608000 178473 8388608000 (Enclosure.Real.IsNear.const Bool.false 713892 1000) RS373to384.d48 rfl)) 

noncomputable abbrev qz745 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 713892 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz610 := qz745

noncomputable abbrev qz393 := qz610

noncomputable abbrev qz44 := qz393

noncomputable def Ns372p297 := @Enclosure.Real.IsNear.sqrt_image qz44 89416197 8388608 17 16777216 54775080 54775086 16777216 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 357664788 33554432 34 33554432 89416197 8388608 17 16777216 (Ns372p296 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns372p298 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz44) 54775083 16777216 3 16777216 5138740 5138742 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz44) Bool.false 109550166 33554432 6 33554432 54775083 16777216 3 16777216 (Ns372p297 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns372p299 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 10277482 33554432 2 33554432 5138741 16777216 1 16777216 (Ns372p298 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz394 := (@HMul.hMul Real Real Real qz584 qz582 qz603)

noncomputable abbrev qz45 := (Real.cos qz394)

noncomputable abbrev qz611 := (@HMul.hMul Real Real Real qz733 qz744 qz744)

noncomputable abbrev qz395 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz611 qz603) qz600)

noncomputable abbrev qz46 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz395))

noncomputable def Ns372p300 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz37) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz45) qz46) Bool.false 120578130745353 

noncomputable def Ns372p301 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz45) qz46 31077807 16777216 379 

noncomputable abbrev qz47 := (@Neg.neg Real Real.instNeg (Real.cos qz394))

noncomputable def Ns372p302 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz45) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz47)) Bool.true 31077807 16777216 379 16777216 (BSN.inv_eq_neg_inv_neg qz45) 

noncomputable def Ns372p303 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz47) Bool.false 62155614 33554432 758 33554432 31077807 16777216 

noncomputable def Ns372p304 := @Enclosure.Real.IsNear.recentre' qz45 Bool.true 18114211 33554432 1271954432 193273528320000 18114211 33554432 1242143 188743680000 

noncomputable abbrev qz48 := qz394

noncomputable def Ns372p305 := @Enclosure.Real.IsNear.cos_image qz48 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 138986999) qz367) Bool.false 138986999 33554432 215 33554432 Bool.true 18114211 33554432 1 

noncomputable def Ns372p306 := nat_lit 458763282048755459370086967 

noncomputable def Ns372p307 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz37 884279719003555 140737488355328 1 500000000000000 5530117 8388608 17 16777216 4890170306816782565935 1180591620717411303424 Ns372p306 

noncomputable def Ns372p308 := @Enclosure.Real.IsNear.subLit_ff_p qz44 qz1 89416197 8388608 17 16777216 10 1 0 1 5530117 5530117 8388608 17 

noncomputable def Ns372p309 := @Ns372p308 16777216 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 357664788 33554432 34 33554432 89416197 8388608 17 16777216 (Ns372p296 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns372p310 := @Enclosure.Real.IsNear.recentre' qz48 Bool.false 4890170306816782565935 1180591620717411303424 Ns372p306 Ns372p179 138986999 33554432 215 33554432 (@Ns372p307 Ns372p179 RS373to384.d47 (Ns372p309 rfl rfl) rfl) 

noncomputable def Ns372p311 := nat_lit 4838327606438438274859008 

noncomputable def Ns372p312 := nat_lit 837817704959785329814317384940918818667843180251358619674090197397425184510681280163167041 

noncomputable def Ns372p313 := nat_lit 499486513878181464636758211268065986138873271216084419528652908732486717898326782589761 

noncomputable def Ns372p314 := nat_lit 2512454141851599626513678638400220324031251794211643690183213286374810580096247186924321601 

noncomputable def Ns372p315 := BSN.cos_dyadic_bound_f 68756770679 68719476736 3 2 33554432 11531251 Ns372p312 Ns372p186 Ns372p313 Ns372p314 Ns372p189 Ns372p313 18114211 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 68756770679) qz379 0 2 Ns372p312 Ns372p186 Ns372p313 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 68756770679) qz380 0 2 Ns372p314 Ns372p189 Ns372p313 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p316 := @Ns372p305 5760000 (Ns372p310 rfl) (Enclosure.sfrac_false_div 138986999 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 138986999) qz367) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns372p311) qz368) 226375608064910080 72057594037927936 Bool.false 18114211 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q2 138986999 33554432 226375608064910080 72057594037927936 0 Ns372p311 Ns372p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 18114211 33554432 Ns372p311 Ns372p98 68756770679 68719476736 11531251 11520000 (Ns372p315 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p317 := @Enclosure.Real.IsNear.inv_image qz47 18114211 33554432 1242143 188743680000 31077428 31078186 16777216 (@Enclosure.Real.IsNear.neg qz45 Bool.true 18114211 33554432 1242143 188743680000 (Ns372p304 (Ns372p316 rfl rfl) rfl)) 

noncomputable def Ns372p318 := Ns372p302 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz47) Bool.false 31077807 16777216 379 16777216 (@Ns372p303 379 16777216 (Ns372p317 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p319 := @Enclosure.Real.IsNear.recentre' qz46 Bool.true 3879879 16777216 

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz349 qz346 qz395)

noncomputable def Ns372p320 := @Enclosure.Real.IsNear.cos_image qz49 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 60537821)) qz367) Bool.true 60537821 33554432 

noncomputable def Ns372p321 := nat_lit 17867611143506622168805078805 

noncomputable def Ns372p322 := nat_lit 17844836971909882835882553231915507 

noncomputable def Ns372p323 := @Enclosure.Real.IsNear.recentre' qz49 Bool.true Ns372p321 Ns372p197 Ns372p322 

noncomputable abbrev qz50 := qz395

noncomputable def Ns372p324 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz50 884279719003555 140737488355328 1 500000000000000 20205836184551 

noncomputable abbrev qz396 := (@HSub.hSub Real Real Real qz588 qz611 qz603)

noncomputable abbrev qz51 := qz396

noncomputable def Ns372p325 := @Enclosure.Real.IsNear.subLit_tf qz51 qz31 15807789673447 70368744177664 661260917 281474976710656 1 16 

noncomputable abbrev qz397 := qz611

noncomputable abbrev qz52 := qz397

noncomputable def Ns372p326 := @Enclosure.Real.IsNear.subLit_ff_n qz52 qz37 30582194033689 70368744177664 376048245 281474976710656 5530117 8388608 17 16777216 

noncomputable def Ns372p327 := @Enclosure.Real.IsNear.mulLit_ff qz37 qz37 5530117 8388608 17 16777216 5530117 8388608 17 16777216 30582194033689 70368744177664 

noncomputable def Ns372p328 := nat_lit 433475705455629450556488379020516977149322072993009004157427894526631859431350166314328502891998321 

noncomputable def Ns372p329 := nat_lit 975743491921780970500323514261193594148711042915413329552712293065467609596717903600577236539801600 

noncomputable def Ns372p330 := nat_lit 2422821498969331878442475205809312406795955289373176188911893437916315673068196227596660272241 

noncomputable def Ns372p331 := nat_lit 2618753083572593142294054697303950135048021627677990097341486779033039314624340332232657215898545265 

noncomputable def Ns372p332 := nat_lit 88792657764882068315529439797768617067532704905302612989296818668957552473301329227652528525121945600 

noncomputable def Ns372p333 := BSN.cos_dyadic_bound_t 60537821 33554432 4 3 16777216 5760000 Ns372p328 Ns372p329 Ns372p330 Ns372p331 Ns372p332 Ns372p330 3879879 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 60537821) (BSN.cosEvenQ 33554432) 0 3 Ns372p328 Ns372p329 Ns372p330 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 60537821) (BSN.cosOddQ 33554432) 0 3 Ns372p331 Ns372p332 Ns372p330 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p334 := @Ns372p319 180657152 12079595520000 3879879 16777216 176423 11796480000 (@Ns372p320 31 2097152 Bool.true 3879879 16777216 1 5760000 (@Ns372p323 Ns372p200 60537821 33554432 31 2097152 (@Ns372p324 70368744177664 661260917 281474976710656 Ns372p321 Ns372p197 Ns372p322 Ns372p200 RS373to384.d47 (@Ns372p325 0 1 323293378952816 20205836184551 70368744177664 661260917 281474976710656 (@Ns372p326 132605350916994891776 15807789673447 70368744177664 661260917 281474976710656 (@Ns372p327 376048245 281474976710656 (Ns372p309 rfl rfl) (Ns372p309 rfl rfl) rfl) (Ns372p309 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 60537821 33554432) (BSN.cos_neg_of_bound 60537821 33554432 Bool.true 3879879 16777216 1 5760000 (Ns372p333 rfl rfl)) rfl rfl) 

noncomputable def Ns372p335 := @Ns372p294 89528292714393894661 Ns372p214 (Ns372p295 qz33 (@Enclosure.Real.IsNear.of_eq qz609 (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 5138741 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz36 (BSN.t_div_two_pi_nonneg qz35 713892 1000 qz38)) Ns372p299) rfl) (@Ns372p300 281474976710656 52134671512549 1583296743997440000 (BSN.correction_mk qz37 (BSN.cos_two_pi_p_ne_zero_mk qz35 713892 1000 10 qz38 rfl rfl (@BSN.floor_sqrt_eq_dec qz35 713892 1000 10 qz38 rfl rfl rfl))) (@Ns372p301 16777216 3879879 16777216 176423 11796480000 120578130745353 281474976710656 52134671512549 1583296743997440000 Ns372p318 (Ns372p334 rfl) rfl)) 

noncomputable def Ns372p336 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (hardyZApproximantRS₀ qz35) Bool.false 4704439184580254684451 4722366482869645213696 9906693783172854054661 Ns372p214 (@Eq.refl Real (hardyZApproximantRS₀ qz35)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) (@HMul.hMul Real Real Real qz5 qz604 (Zeta.RiemannSiegel.correction qz37))) Bool.false 4704439184580254684451 4722366482869645213696 9906693783172854054661 Ns372p214 (BSN.hardyZApproximantRS₀_eq qz35 10 (@BSN.floor_sqrt_eq_dec qz35 713892 1000 10 qz38 rfl rfl rfl)) (@Ns372p216 4704439184580254684451 4722366482869645213696 9906693783172854054661 Ns372p214 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 10)) Bool.false 151318857 134217728 148811 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) (Ns372p293 (Ns372p292 rfl rfl rfl rfl) rfl rfl)) (Ns372p335 rfl) rfl rfl)) 

theorem RS373to384.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz35) Bool.false 4704439184580254684451 4722366482869645213696 9906693783172854054661 Ns372p214 := Ns372p336 

noncomputable abbrev qz612 := (@HMul.hMul Real Real Real qz733 (Real.sqrt qz741) qz735)

noncomputable abbrev qz398 := qz612

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv qz398)

noncomputable abbrev qz399 := (@HMul.hMul Real Real Real qz584 (@HMul.hMul Real Real Real qz584 qz612 qz612) qz612)

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz399))

noncomputable abbrev qz400 := (@HMul.hMul Real Real Real qz584 qz598 qz598)

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz349 qz400 qz374))

noncomputable abbrev qz613 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz53)

noncomputable def Ns372p337 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz364 (@HAdd.hAdd Real Real Real qz364 qz613 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55)) Bool.false 

noncomputable def Ns372p338 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz364 qz613 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55) 18133401 1073741824 

noncomputable def Ns372p339 := @Enclosure.Real.IsNear.addLit_ff qz613 qz54 2266675 134217728 25 134217728 

noncomputable def Ns372p340 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz53 25 4 0 1 90667 33554432 1 33554432 2266675 

noncomputable def Ns372p341 := @Enclosure.Real.IsNear.recentre' qz53 Bool.false 90667 33554432 1 33554432 90667 33554432 1 33554432 

noncomputable def Ns372p342 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz8 109499183 33554432 7 33554432 951335823773 8388608000 178141 8388608000 104170495461775477459 281474976710656000 26165645972201 

noncomputable def Ns372p343 := @Enclosure.Real.IsNear.sqrt_image qz8 951335823773 8388608000 178141 8388608000 178665965 178665999 16777216 qz21 

noncomputable def Ns372p344 := @Enclosure.Real.IsNear.sqrt_image qz22 89332991 8388608 17 16777216 54749588 54749595 16777216 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 357331964 33554432 34 33554432 89332991 8388608 17 16777216 (Ns372p343 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz401 := (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 109499183 33554432 7 33554432 109499183 33554432 7 33554432 (Ns372p344 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns372p345 := @Ns372p342 281474976710656000 qz401 

noncomputable def Ns372p346 := Ns372p345 qz21 

noncomputable abbrev qz56 := qz398

noncomputable def Ns372p347 := @Enclosure.Real.IsNear.inv_image qz56 104170495461775477459 281474976710656000 26165645972201 281474976710656000 45333 45334 16777216 (Ns372p346 rfl) rfl rfl 

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv qz399)

noncomputable def Ns372p348 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz57 1 32 0 1 1 

noncomputable def Ns372p349 := @Enclosure.Real.IsNear.recentre' qz57 Bool.false 1 33554432 1 33554432 

noncomputable def Ns372p350 := nat_lit 1130405311134948188547993119611346025431075293964548339213579 

noncomputable def Ns372p351 := nat_lit 22300745198530623141535718272648361505980416000000000 

noncomputable def Ns372p352 := nat_lit 851809117577350842664893307574318808866545660481482421 

noncomputable abbrev qz58 := qz399

noncomputable def Ns372p353 := @Enclosure.Real.IsNear.inv_image qz58 Ns372p350 Ns372p351 Ns372p352 Ns372p351 0 1 

noncomputable def Ns372p354 := nat_lit 10851492124751785344767335992487417096681 

noncomputable def Ns372p355 := nat_lit 79228162514264337593543950336000000 

noncomputable def Ns372p356 := nat_lit 5451377294644205285220968497018919 

noncomputable abbrev qz402 := (@HMul.hMul Real Real Real qz584 qz612 qz612)

noncomputable abbrev qz59 := qz402

noncomputable def Ns372p357 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz56 Ns372p354 Ns372p355 Ns372p356 Ns372p355 104170495461775477459 281474976710656000 26165645972201 

noncomputable def Ns372p358 := @Enclosure.Real.IsNear.mulLit_ff qz56 qz56 104170495461775477459 281474976710656000 26165645972201 281474976710656000 104170495461775477459 281474976710656000 26165645972201 281474976710656000 Ns372p354 

noncomputable def Ns372p359 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz55 13 10 0 1 965533 33554432 1 

noncomputable def Ns372p360 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 965533 33554432 1 33554432 965533 33554432 

noncomputable def Ns372p361 := nat_lit 1312902987116519591161487 

noncomputable abbrev qz60 := qz400

noncomputable def Ns372p362 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz23 11990071077667489 1125899906842624 1532988611 1125899906842624 109499183 33554432 7 33554432 Ns372p361 

noncomputable def Ns372p363 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz23 109499183 33554432 7 33554432 109499183 33554432 7 33554432 11990071077667489 1125899906842624 1532988611 

noncomputable def Ns372p364 := @Ns372p363 1125899906842624 qz401 

noncomputable def Ns372p365 := Ns372p364 qz401 

noncomputable def Ns372p366 := @Ns372p362 37778931862957161709568 251791508727397513 37778931862957161709568 (Ns372p365 rfl) qz401 

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz349 qz400 qz374)

noncomputable def Ns372p367 := @Enclosure.Real.IsNear.inv_image qz61 Ns372p361 37778931862957161709568 251791508727397513 37778931862957161709568 482766 482767 16777216 (Ns372p366 rfl) 

noncomputable def Ns372p368 := @Ns372p338 201 1073741824 12551929 335544320 13 335544320 19562090847010816 291497869 5368709120 1213 5368709120 (@Ns372p339 1 1073741824 1 1073741824 2433823883132928 18133401 1073741824 201 1073741824 (@Ns372p340 134217728 25 134217728 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns372p341 (Ns372p347 rfl rfl rfl rfl) rfl) rfl) (@Ns372p348 33554432 1 33554432 1 1073741824 1 1073741824 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns372p349 1 33554432 1 33554432 (@Ns372p353 16777216 (@Ns372p357 281474976710656000 Ns372p350 Ns372p351 Ns372p352 Ns372p351 (@Ns372p358 Ns372p355 Ns372p356 Ns372p355 (Ns372p346 rfl) (Ns372p346 rfl) rfl) (Ns372p346 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns372p359 33554432 12551929 335544320 13 335544320 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns372p360 1 33554432 (Ns372p367 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS373to384.d52 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 := @Ns372p337 291497869 5368709120 1213 5368709120 (BSN.hardyZErrorBoundRS₀_mk qz4 712564 1000 qz11 rfl rfl) (Ns372p368 rfl rfl) 

noncomputable def Ns372p369 := nat_lit 28691542045757278561327120384 

noncomputable abbrev qz746 := (Enclosure.sfrac Bool.false 715219 1000)

noncomputable abbrev qz614 := qz746

noncomputable abbrev qz403 := qz614

noncomputable abbrev qz62 := qz403

noncomputable abbrev qz747 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 715219 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz615 := qz747

noncomputable abbrev qz404 := qz615

noncomputable abbrev qz63 := qz404

noncomputable abbrev qz748 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 715219 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz616 := qz748

noncomputable abbrev qz405 := qz616

noncomputable abbrev qz64 := qz405

noncomputable abbrev qz617 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz63 qz9))

noncomputable def Ns372p370 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) (@HMul.hMul Real Real Real qz5 qz617 (Zeta.RiemannSiegel.correction qz64)) 23744833 4194304 149077 134217728 157020371108772032073 1180591620717411303424 100346519534908961831 Ns372p214 Ns372p369 

noncomputable def Ns372p371 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos BSN.quadSignNeg 9 10 715219 1000 198 268435456 134217728 4503599627370496 Bool.false 358408503732 2484 618095470 48 84886744 8 

noncomputable def Ns372p372 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 715219 1000 96 150 268435456 134217728 4503599627370496 Bool.false 358408503732 2484 

noncomputable def Ns372p373 := Ns372p372 558195838 48 94906264 8 589812974 48 89478488 8 Bool.true 651240051 112118 Bool.true 344652212 Bool.true 188327479 14148475504056880 1 Bool.false 75953394 Bool.false Bool.false 205038221 Bool.true Bool.true 692732548 

noncomputable def Ns372p374 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 715219 1000 34 36 268435456 134217728 4503599627370496 Bool.false 358408503732 2484 

noncomputable def Ns372p375 := Ns372p374 480971758 48 109588312 8 522351262 48 101459064 8 Bool.true 646992183 83154 Bool.false 72011385 Bool.true 7376106 14148475504056880 1 Bool.false 258834236 Bool.true Bool.false 268334121 Bool.false Bool.true 651240051 

noncomputable def Ns372p376 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 715219 1000 218 117 268435456 134217728 4503599627370496 Bool.false 358408503732 2484 

noncomputable def Ns372p377 := Ns372p376 372130544 47 134217720 8 432030192 47 120047984 16 Bool.true 568599319 48932 Bool.false 332348820 Bool.false 78382732 14148475504056880 1 Bool.false 87670113 Bool.true Bool.false 77273612 Bool.true Bool.true 646992183 

noncomputable def Ns372p378 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 715219 1000 534 349 268435456 134217728 4503599627370496 Bool.false 358408503732 2484 

noncomputable def Ns372p379 := Ns372p378 186065264 47 189812528 16 294906480 47 154981288 8 Bool.true 268435272 2535 Bool.false 166024984 Bool.false 327343547 14148475504056880 1 Bool.false 218708904 Bool.true Bool.false 252036766 Bool.true Bool.true 568599319 

noncomputable def Ns372p380 := nat_lit 1810988175733801936959955256536497848558020336659878068777 

noncomputable def Ns372p381 := nat_lit 1356366915688991891330668360902378801279819627626496000 

noncomputable def Ns372p382 := nat_lit 89833224896932182114560642607520000 

noncomputable def Ns372p383 := nat_lit 385502663587258181033424864637703081280 

noncomputable abbrev qz618 := (@Eq.refl Real qz746)

noncomputable abbrev qz406 := qz618

noncomputable abbrev qz65 := qz406

noncomputable def Ns372p384 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz62 715219 1000 2046153871844 16000000 1430438 4000 2000 Ns372p382 Ns372p383 qz65 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns372p385 := nat_lit 579516216234816619827185682091679311538566507731160982008640 

noncomputable abbrev qz619 := (@HSub.hSub Real Real Real qz737 qz738 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz739 (@Nat.cast Real Real.instNatCast 1430438))))

noncomputable abbrev qz407 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 715219 4000) (Real.log (Enclosure.sfrac Bool.false 2046153871844 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz619))

noncomputable abbrev qz620 := (Enclosure.sfrac Bool.false 715219 2000)

noncomputable abbrev qz66 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz407 qz620) (@HMul.hMul Real Real Real qz349 qz620 (Real.log Real.pi)))

noncomputable def Ns372p386 := @Enclosure.Real.IsNear.addLit_ft_p qz66 (Enclosure.sfrac Bool.true Ns372p382 Ns372p383) 1503274483204350585913 1125899906842624000 113694890282933413 12288000000000000000000 Ns372p382 Ns372p383 0 1 Ns372p385 

noncomputable def Ns372p387 := nat_lit 100883042848031047678355832832000 

noncomputable abbrev qz67 := (@HSub.hSub Real Real Real qz353 qz407 qz620)

noncomputable def Ns372p388 := @Enclosure.Real.IsNear.subLit_ff_p qz67 (@HMul.hMul Real Real Real qz5 qz620 (Real.log Real.pi)) 1964179940743485107257 1125899906842624000 1471393895141 375000000000000000 27472106071659 67108864000 715219 134217728000 Ns372p387 1503274483204350585913 1125899906842624000 

noncomputable abbrev qz68 := qz407

noncomputable def Ns372p389 := @Enclosure.Real.IsNear.subLit_ff_p qz68 qz620 473362488695904490917 225179981368524800 1471393895141 375000000000000000 715219 2000 0 1 785671976297394042902800 1964179940743485107257 1125899906842624000 1471393895141 375000000000000000 

noncomputable def Ns372p390 := nat_lit 1065917563851023045166651959112892416 

noncomputable def Ns372p391 := nat_lit 56862472454762821907906560 

noncomputable def Ns372p392 := nat_lit 2439337980553789656347121155221580257910819798158593202979198384767502516123359274988382439043297504730398985654459897177063590714051182524695844803450265205523960268971066181934205712292929567166544268492800 

noncomputable def Ns372p393 := nat_lit 90181653262111321460629112994273540944138732196753933622225273207578415379885703279582258594601048898087729997456664108198338037816046522038908503004285055603837398915209612619829278371967925257899165614080 

noncomputable def Ns372p394 := nat_lit 1949880601757382706389762809558682383350662803817138295070406388234360079859129594987507408564574586904481791834902818337462448656869743784812619711769479797394032870315681340809866986131846227558400 

noncomputable def Ns372p395 := BSN.log_dyadic_bound 997577871844 3094729871844 9 8 Ns372p392 134217728 46080000 Ns372p393 Ns372p394 89728418 4092307743688 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 997577871844) (BSN.artanhQ 3094729871844) 0 8 Ns372p393 Ns372p392 Ns372p394 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz408 := (Real.log (Enclosure.sfrac Bool.false 2046153871844 16000000))

noncomputable def Ns372p396 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 715219 4000) qz408 715219 4000 0 1 3309831515348215 281474976710656 48828161 2250000000000000 473450877315166996817 225179981368524800 34922828482259 9000000000000000000 (Enclosure.Real.IsNear.const Bool.false 715219 4000) (BSN.isNear_log_sfrac 2046153871844 16000000 3309831515348215 281474976710656 48828161 2250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2046153871844) qz356)) Bool.false Ns372p391 Ns372p98 1000000737280000 46080000000000000000000 3309831515348215 281474976710656 48828161 2250000000000000 (BSN.log_rat_reduce_isNear 2046153871844 16000000 16 4092307743688 2097152000000 89728418 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns372p395 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p397 := BSN.arctan_dyadic_bound_f 1000 1430438 1 0 16777216 5760000 0 1 1 0 1 1 11728 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1430438) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1430438) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns372p398 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1430438))) 884279719003555 562949953421312 1 2000000000000000 11728 16777216 1 5760000 14829149573088221855744 883886192625059 562949953421312 3125000009 18000000000000000 qz17 (Ns372p397 rfl) rfl rfl 

noncomputable abbrev qz409 := (@HMul.hMul Real Real Real qz584 qz589 qz619)

noncomputable abbrev qz69 := qz409

noncomputable abbrev qz410 := qz619

noncomputable abbrev qz70 := qz410

noncomputable def Ns372p399 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 715219 4000) qz408) qz69 473450877315166996817 225179981368524800 34922828482259 9000000000000000000 883886192625059 2251799813685248 3125000009 72000000000000000 Ns372p390 473362488695904490917 225179981368524800 1471393895141 375000000000000000 (Ns372p396 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz70 1 4 0 1 883886192625059 562949953421312 3125000009 18000000000000000 883886192625059 2251799813685248 3125000009 72000000000000000 qz363 Ns372p398 rfl) 

noncomputable def Ns372p400 := @Ns372p386 Ns372p380 Ns372p381 113694890282933413 12288000000000000000000 (@Ns372p388 113694890282933413 12288000000000000000000 (Ns372p389 (Ns372p399 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 715219 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz620 (Real.log Real.pi) 715219 2000 0 1 38410761 33554432 1 67108864 27472106071659 67108864000 715219 134217728000 (Enclosure.Real.IsNear.const Bool.false 715219 2000) RS373to384.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns372p382 Ns372p383) 

noncomputable def Ns372p401 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns372p380 Ns372p381 113694890282933413 12288000000000000000000 22400531483 16777216 311 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz364 qz66 (Enclosure.sfrac Bool.true Ns372p382 Ns372p383)) Bool.false Ns372p380 Ns372p381 113694890282933413 12288000000000000000000 Ns372p384 (Ns372p400 rfl rfl)) 

noncomputable def Ns372p402 := nat_lit 3795157554424323512467456 

noncomputable def Ns372p403 := nat_lit 2417851639229258349412352 

noncomputable def Ns372p404 := nat_lit 3500491675349374985631382928383566486115845790848438164830726964925114581772793315080993457981248707100408181608209731586198222125609455616 

noncomputable def Ns372p405 := nat_lit 2480618986310532424322964524999604369348320291489025065032221129056950787277599060843122722873756317638258877618762918337830243209216 

noncomputable def Ns372p406 := nat_lit 17480773263263541986190860782109248895049241765990889339908039431503776563315676632106438753452957040212046372614577867132467955786852274176 

noncomputable def Ns372p407 := BSN.sin_dyadic_bound_f 107864865254 68719476736 4 3 33554432 11531251 Ns372p404 Ns372p111 Ns372p405 Ns372p406 Ns372p114 Ns372p405 33554409 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107864865254) qz365 0 3 Ns372p404 Ns372p111 Ns372p405 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107864865254) qz366 0 3 Ns372p406 Ns372p114 Ns372p405 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz411 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable abbrev qz412 := (@Nat.cast Real Real.instNatCast Ns372p403)

noncomputable def Ns372p408 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz62) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 22400531483) qz411) Bool.false 22400531483 16777216 311 33554432 Bool.true 33554409 33554432 1 5760000 (Ns372p401 rfl) (Enclosure.sfrac_false_div 22400531483 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 22400531483) qz411) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns372p402) qz412) 226375608064910080 72057594037927936 Bool.false 33554409 33554432 212 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q1 22400531483 16777216 226375608064910080 72057594037927936 212 Ns372p402 Ns372p403 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554409 33554432 Ns372p402 Ns372p403 107864865254 68719476736 11531251 11520000 (Ns372p407 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p409 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns372p380 Ns372p381 113694890282933413 12288000000000000000000 358408503732 268435456 2484 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz364 qz66 (Enclosure.sfrac Bool.true Ns372p382 Ns372p383)) Bool.false Ns372p380 Ns372p381 113694890282933413 12288000000000000000000 Ns372p384 (Ns372p400 rfl rfl)) 

noncomputable def Ns372p410 := Ns372p379 48932 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 534 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 218708904 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 349 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 252036766 268435456) qz65 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) Bool.true 33554409 33554432 1782143 188743680000 268435272 268435456 2535 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 33554409 33554432 1782143 188743680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz62) qz62) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 33554409 33554432 1824914432 193273528320000 33554409 33554432 1782143 188743680000 (Ns372p408 rfl rfl) rfl)) rfl) (Ns372p409 rfl) RS373to384.d7 

noncomputable def Ns372p411 := nat_lit 6628273348438758311323743728165222519743827891858207357740949623013376 

noncomputable def Ns372p412 := nat_lit 577281415550638194804809392899180004255478890213572751711635767296 

noncomputable def Ns372p413 := nat_lit 19883665482485173657581621565709869199222972717794194927719425597505536 

noncomputable def Ns372p414 := BSN.cos_dyadic_bound_f 166024984 268435456 3 2 268435456 134217728 Ns372p411 Ns372p159 Ns372p412 Ns372p413 Ns372p162 Ns372p412 218708904 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 166024984) qz371 0 2 Ns372p411 Ns372p159 Ns372p412 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 166024984) qz372 0 2 Ns372p413 Ns372p162 Ns372p412 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p415 := nat_lit 16074991188546596706545855266280824017009688016196458056235583371344147009007428146902117974597218349676181841 

noncomputable def Ns372p416 := nat_lit 1513719508023620645712175763296789752074538474423007836568910196362779257593231483727528913057570044241 

noncomputable def Ns372p417 := nat_lit 80338642642362700944579096714628024437964164748861360004509971807496977761419700686468519168546663144326642001 

noncomputable def Ns372p418 := BSN.sin_dyadic_bound_f 327343547 268435456 4 3 268435456 134217728 Ns372p415 Ns372p134 Ns372p416 Ns372p417 Ns372p137 Ns372p416 252036766 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 327343547) qz369 0 3 Ns372p415 Ns372p134 Ns372p416 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 327343547) qz370 0 3 Ns372p417 Ns372p137 Ns372p416 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p419 := nat_lit 6573980862842863935537119368860389067089782871488868033802461481114583127343388165005300075387001503744000000 

noncomputable def Ns372p420 := nat_lit 1816057913323609258097993712673680033731026160467434046606044460665737174217968083054104576000000000000 

noncomputable def Ns372p421 := nat_lit 39845005979188119162478775311967169864470825597515709884735046724004035818262784461899435645837456021913600000 

noncomputable def Ns372p422 := BSN.cos_dyadic_bound_f 332348820 268435456 4 3 268435456 134217728 Ns372p419 Ns372p143 Ns372p420 Ns372p421 Ns372p146 Ns372p420 87670113 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 332348820) qz371 0 3 Ns372p419 Ns372p143 Ns372p420 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 332348820) qz372 0 3 Ns372p421 Ns372p146 Ns372p420 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p423 := nat_lit 37746925701736053983872780062976 

noncomputable def Ns372p424 := BSN.sin_dyadic_bound_f 78382732 268435456 2 1 268435456 134217728 Ns372p423 Ns372p130 Ns372p423 Ns372p423 Ns372p131 Ns372p423 77273612 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 78382732) qz369 0 1 Ns372p423 Ns372p130 Ns372p423 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 78382732) qz370 0 1 Ns372p423 Ns372p131 Ns372p423 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p425 := Ns372p377 83154 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 218 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 87670113 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 117 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 77273612 268435456) qz65 rfl rfl (Ns372p410 RS373to384.d9 RS373to384.d11 RS373to384.d13 RS373to384.d17 (Ns372p414 rfl rfl) (Ns372p418 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns372p409 rfl) RS373to384.d19 RS373to384.d21 RS373to384.d23 RS373to384.d25 RS373to384.d17 (Ns372p422 rfl rfl) (Ns372p424 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns372p426 := nat_lit 26890857745990289806472252150625 

noncomputable def Ns372p427 := nat_lit 124615124604835863084731911901282304 

noncomputable def Ns372p428 := nat_lit 1869226869072537946270978678519234560 

noncomputable def Ns372p429 := BSN.cos_dyadic_bound_f 72011385 268435456 2 1 268435456 134217728 Ns372p426 Ns372p427 Ns372p426 Ns372p426 Ns372p428 Ns372p426 258834236 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 72011385) qz371 0 1 Ns372p426 Ns372p427 Ns372p426 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 72011385) qz372 0 1 Ns372p426 Ns372p428 Ns372p426 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p430 := nat_lit 2960115090047835392278311696 

noncomputable def Ns372p431 := BSN.cos_dyadic_bound_f 7376106 268435456 2 1 268435456 134217728 Ns372p430 Ns372p427 Ns372p430 Ns372p430 Ns372p428 Ns372p430 268334121 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 7376106) qz371 0 1 Ns372p430 Ns372p427 Ns372p430 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 7376106) qz372 0 1 Ns372p430 Ns372p428 Ns372p430 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p432 := Ns372p375 112118 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 34 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 258834236 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268334121 268435456) qz65 rfl rfl (Ns372p425 rfl rfl) (Ns372p409 rfl) RS373to384.d27 RS373to384.d29 RS373to384.d31 RS373to384.d33 RS373to384.d17 (Ns372p429 rfl rfl) (Ns372p431 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p433 := nat_lit 7604507877248700062023132132437405874807381175206261644947016017691105128142773057469404424723738517030567936 

noncomputable def Ns372p434 := nat_lit 2809136495584622295882366542804271470697660589384857609057076442075766536177587401728917858613991571456 

noncomputable def Ns372p435 := nat_lit 46084331454027674073008801163724496274267808652446840726311043190722436361600058692064615809928761030423347200 

noncomputable def Ns372p436 := BSN.cos_dyadic_bound_f 344652212 268435456 4 3 268435456 134217728 Ns372p433 Ns372p143 Ns372p434 Ns372p435 Ns372p146 Ns372p434 75953394 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 344652212) qz371 0 3 Ns372p433 Ns372p143 Ns372p434 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 344652212) qz372 0 3 Ns372p435 Ns372p146 Ns372p434 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p437 := nat_lit 10974536602009123304909054851465869312452832718046150734438643615135041 

noncomputable def Ns372p438 := nat_lit 1582375473838746632962387649084597078082915117479282547024356439361 

noncomputable def Ns372p439 := nat_lit 32920445055079692421461239779099438743202332323903493638221882132526401 

noncomputable def Ns372p440 := BSN.cos_dyadic_bound_f 188327479 268435456 3 2 268435456 134217728 Ns372p437 Ns372p159 Ns372p438 Ns372p439 Ns372p162 Ns372p438 205038221 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 188327479) qz371 0 2 Ns372p437 Ns372p159 Ns372p438 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 188327479) qz372 0 2 Ns372p439 Ns372p162 Ns372p438 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p441 := Ns372p373 137425 BSN.abs_quadSignPos (BSN.cos_quad_nat0 96 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 75953394 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 150 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 205038221 268435456) qz65 rfl rfl (Ns372p432 rfl) (Ns372p409 rfl) RS373to384.d35 RS373to384.d37 RS373to384.d39 RS373to384.d41 RS373to384.d17 (Ns372p436 rfl rfl) (Ns372p440 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p442 := nat_lit 8552917165106474389073919854906068102079375318008082106704470993881441 

noncomputable def Ns372p443 := nat_lit 961154767295195006643266876781123813801015212624239718818712209761 

noncomputable def Ns372p444 := nat_lit 25656829185784832777208473030964642058610523923598997840675775557224801 

noncomputable def Ns372p445 := BSN.cos_dyadic_bound_f 176949429 268435456 3 2 268435456 134217728 Ns372p442 Ns372p159 Ns372p443 Ns372p444 Ns372p162 Ns372p443 212195497 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 176949429) qz371 0 2 Ns372p442 Ns372p159 Ns372p443 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 176949429) qz372 0 2 Ns372p444 Ns372p162 Ns372p443 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p446 := Ns372p371 Bool.true 692732548 137425 Bool.true 176949429 14148475504056880 1 Bool.false 212195497 Bool.true Bool.true 759834656 149077 BSN.abs_quadSignNeg qz595 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 212195497 268435456) qz65 rfl (Ns372p441 rfl) (Ns372p409 rfl) RS373to384.d43 RS373to384.d45 RS373to384.d17 (Ns372p445 rfl rfl) rfl 

noncomputable def Ns372p447 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) 759834656 268435456 149077 268435456 759834656 268435456 149077 268435456 407933124735926272 23744833 4194304 149077 134217728 (Ns372p446 rfl rfl rfl rfl) 

noncomputable def Ns372p448 := @Enclosure.Real.IsNear.mulLit_ff qz617 (Zeta.RiemannSiegel.correction qz64) 1284089 4194304 1 16777216 122281532751057 281474976710656 14618908157231 395824185999360000 157020371108772032073 1180591620717411303424 

noncomputable abbrev qz621 := (@HPow.hPow Real Real Real qz7 qz63 qz9)

noncomputable def Ns372p449 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz621 1 1 0 1 1284089 4194304 1 16777216 1284089 4194304 1 16777216 

noncomputable def Ns372p450 := @Enclosure.Real.IsNear.sqrt_image qz63 3819521932307 33554432000 715219 33554432000 178998509 178998543 16777216 (@Enclosure.Real.IsNear.of_eq qz63 (@HMul.hMul Real Real Real qz5 qz62 qz3) Bool.false 3819521932307 33554432000 715219 33554432000 (BSN.t_div_two_pi_mk qz62 715219 1000 qz65) (@Enclosure.Real.IsNear.mulLit_ff qz62 qz3 715219 1000 0 1 5340353 33554432 1 33554432 3819521932307 33554432000 715219 33554432000 (Enclosure.Real.IsNear.const Bool.false 715219 1000) RS373to384.d48 rfl)) 

noncomputable abbrev qz749 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 715219 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz622 := qz749

noncomputable abbrev qz413 := qz622

noncomputable abbrev qz71 := qz413

noncomputable def Ns372p451 := @Enclosure.Real.IsNear.sqrt_image qz71 89499263 8388608 17 16777216 54800516 54800523 16777216 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 357997052 33554432 34 33554432 89499263 8388608 17 16777216 (Ns372p450 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns372p452 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz71) 109601039 33554432 7 33554432 5136355 5136357 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz71) Bool.false 109601039 33554432 7 33554432 109601039 33554432 7 33554432 (Ns372p451 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns372p453 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 10272712 33554432 2 33554432 1284089 4194304 1 16777216 (Ns372p452 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz414 := (@HMul.hMul Real Real Real qz584 qz582 qz616)

noncomputable abbrev qz72 := (Real.cos qz414)

noncomputable abbrev qz623 := (@HMul.hMul Real Real Real qz733 qz748 qz748)

noncomputable abbrev qz415 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz623 qz616) qz600)

noncomputable abbrev qz73 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz415))

noncomputable def Ns372p454 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz64) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz72) qz73) Bool.false 122281532751057 

noncomputable def Ns372p455 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz72) qz73 34488219 16777216 467 

noncomputable abbrev qz74 := (@Neg.neg Real Real.instNeg (Real.cos qz414))

noncomputable def Ns372p456 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz72) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz74)) Bool.true 34488219 16777216 467 16777216 (BSN.inv_eq_neg_inv_neg qz72) 

noncomputable def Ns372p457 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz74) Bool.false 68976438 33554432 934 33554432 34488219 16777216 

noncomputable def Ns372p458 := @Enclosure.Real.IsNear.recentre' qz72 Bool.true 16322964 33554432 1271954432 193273528320000 4080741 8388608 1242143 188743680000 

noncomputable abbrev qz75 := qz414

noncomputable def Ns372p459 := @Enclosure.Real.IsNear.cos_image qz75 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 141074675) qz367) Bool.false 141074675 33554432 215 33554432 Bool.true 16322964 33554432 1 

noncomputable def Ns372p460 := nat_lit 458763282050182522383725111 

noncomputable def Ns372p461 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz64 884279719003555 140737488355328 1 500000000000000 5613183 8388608 17 16777216 4963623885955531865565 1180591620717411303424 Ns372p460 

noncomputable def Ns372p462 := @Enclosure.Real.IsNear.subLit_ff_p qz71 qz1 89499263 8388608 17 16777216 10 1 0 1 5613183 5613183 8388608 17 

noncomputable def Ns372p463 := @Ns372p462 16777216 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 357997052 33554432 34 33554432 89499263 8388608 17 16777216 (Ns372p450 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns372p464 := @Enclosure.Real.IsNear.recentre' qz75 Bool.false 4963623885955531865565 1180591620717411303424 Ns372p460 Ns372p179 141074675 33554432 215 33554432 (@Ns372p461 Ns372p179 RS373to384.d47 (Ns372p463 rfl rfl) rfl) 

noncomputable def Ns372p465 := nat_lit 5139193425819888758292480 

noncomputable def Ns372p466 := nat_lit 1066642683558722269200158550085854999598815805802382232855044769968956615420258667759024961 

noncomputable def Ns372p467 := nat_lit 809321923894180577743543631599534390552277053844399627418195385073049241876836072962881 

noncomputable def Ns372p468 := nat_lit 3198309406828378446444988562994365930015342863299457899310297919136723747777022331131149121 

noncomputable def Ns372p469 := BSN.cos_dyadic_bound_f 73032331127 68719476736 3 2 33554432 11531251 Ns372p466 Ns372p186 Ns372p467 Ns372p468 Ns372p189 Ns372p467 16322964 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 73032331127) qz379 0 2 Ns372p466 Ns372p186 Ns372p467 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 73032331127) qz380 0 2 Ns372p468 Ns372p189 Ns372p467 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p470 := @Ns372p459 5760000 (Ns372p464 rfl) (Enclosure.sfrac_false_div 141074675 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 141074675) qz367) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns372p465) qz368) 226375608064910080 72057594037927936 Bool.false 16322964 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q2 141074675 33554432 226375608064910080 72057594037927936 0 Ns372p465 Ns372p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16322964 33554432 Ns372p465 Ns372p98 73032331127 68719476736 11531251 11520000 (Ns372p469 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p471 := @Enclosure.Real.IsNear.inv_image qz74 4080741 8388608 1242143 188743680000 34487752 34488686 16777216 (@Enclosure.Real.IsNear.neg qz72 Bool.true 4080741 8388608 1242143 188743680000 (Ns372p458 (Ns372p470 rfl rfl) rfl)) 

noncomputable def Ns372p472 := Ns372p456 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz74) Bool.false 34488219 16777216 467 16777216 (@Ns372p457 467 16777216 (Ns372p471 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p473 := @Enclosure.Real.IsNear.recentre' qz73 Bool.true 3545603 16777216 

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz349 qz346 qz415)

noncomputable def Ns372p474 := @Enclosure.Real.IsNear.cos_image qz76 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 59852259)) qz367) Bool.true 59852259 33554432 

noncomputable def Ns372p475 := nat_lit 17665269156681742583108714845 

noncomputable def Ns372p476 := nat_lit 17997267495017100979973199907644107 

noncomputable def Ns372p477 := @Enclosure.Real.IsNear.recentre' qz76 Bool.true Ns372p475 Ns372p197 Ns372p476 

noncomputable abbrev qz77 := qz415

noncomputable def Ns372p478 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz77 884279719003555 140737488355328 1 500000000000000 19977014938879 

noncomputable abbrev qz416 := (@HSub.hSub Real Real Real qz588 qz623 qz616)

noncomputable abbrev qz78 := qz416

noncomputable def Ns372p479 := @Enclosure.Real.IsNear.subLit_tf qz78 qz31 15578968427775 70368744177664 666909405 281474976710656 1 16 

noncomputable abbrev qz417 := qz623

noncomputable abbrev qz79 := qz417

noncomputable def Ns372p480 := @Enclosure.Real.IsNear.subLit_ff_n qz79 qz64 31507823391489 70368744177664 381696733 281474976710656 5613183 8388608 17 16777216 

noncomputable def Ns372p481 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz64 5613183 8388608 17 16777216 5613183 8388608 17 16777216 31507823391489 70368744177664 

noncomputable def Ns372p482 := nat_lit 414055319482467759046485796576650703725781097059092902738110413597614768393926449344317756345877361 

noncomputable def Ns372p483 := nat_lit 2113326306881563008736413538119385543571626239968747645146504357989899850395127341622688154481 

noncomputable def Ns372p484 := nat_lit 2501894474208349252193880286111613704738486131482584164863762786555907072797883227742425443205055345 

noncomputable def Ns372p485 := BSN.cos_dyadic_bound_t 59852259 33554432 4 3 16777216 5760000 Ns372p482 Ns372p329 Ns372p483 Ns372p484 Ns372p332 Ns372p483 3545603 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 59852259) (BSN.cosEvenQ 33554432) 0 3 Ns372p482 Ns372p329 Ns372p483 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 59852259) (BSN.cosOddQ 33554432) 0 3 Ns372p484 Ns372p332 Ns372p483 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p486 := @Ns372p473 2919314432 193273528320000 3545603 16777216 2850893 188743680000 (@Ns372p474 501 33554432 Bool.true 3545603 16777216 1 5760000 (@Ns372p477 Ns372p200 59852259 33554432 501 33554432 (@Ns372p478 70368744177664 666909405 281474976710656 Ns372p475 Ns372p197 Ns372p476 Ns372p200 RS373to384.d47 (@Ns372p479 0 1 319632239022064 19977014938879 70368744177664 666909405 281474976710656 (@Ns372p480 130685859184980787200 15578968427775 70368744177664 666909405 281474976710656 (@Ns372p481 381696733 281474976710656 (Ns372p463 rfl rfl) (Ns372p463 rfl rfl) rfl) (Ns372p463 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 59852259 33554432) (BSN.cos_neg_of_bound 59852259 33554432 Bool.true 3545603 16777216 1 5760000 (Ns372p485 rfl rfl)) rfl rfl) 

noncomputable def Ns372p487 := @Ns372p448 100346519534908961831 Ns372p214 (Ns372p449 qz33 (@Enclosure.Real.IsNear.of_eq qz621 (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 1284089 4194304 1 16777216 (BSN.rpow_neg_quarter_mk qz63 (BSN.t_div_two_pi_nonneg qz62 715219 1000 qz65)) Ns372p453) rfl) (@Ns372p454 281474976710656 14618908157231 395824185999360000 (BSN.correction_mk qz64 (BSN.cos_two_pi_p_ne_zero_mk qz62 715219 1000 10 qz65 rfl rfl (@BSN.floor_sqrt_eq_dec qz62 715219 1000 10 qz65 rfl rfl rfl))) (@Ns372p455 16777216 3545603 16777216 2850893 188743680000 122281532751057 281474976710656 14618908157231 395824185999360000 Ns372p472 (Ns372p486 rfl) rfl)) 

noncomputable def Ns372p488 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (hardyZApproximantRS₀ qz62) Bool.true 6840596686782188072521 1180591620717411303424 9935060215572674081831 Ns372p214 (@Eq.refl Real (hardyZApproximantRS₀ qz62)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) (@HMul.hMul Real Real Real qz5 qz617 (Zeta.RiemannSiegel.correction qz64))) Bool.true 6840596686782188072521 1180591620717411303424 9935060215572674081831 Ns372p214 (BSN.hardyZApproximantRS₀_eq qz62 10 (@BSN.floor_sqrt_eq_dec qz62 715219 1000 10 qz65 rfl rfl rfl)) (@Ns372p370 6840596686782188072521 1180591620717411303424 9935060215572674081831 Ns372p214 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 10)) Bool.true 23744833 4194304 149077 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) (Ns372p447 (Ns372p446 rfl rfl rfl rfl) rfl rfl)) (Ns372p487 rfl) rfl rfl)) 

theorem RS373to384.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz62) Bool.true 6840596686782188072521 1180591620717411303424 9935060215572674081831 Ns372p214 := Ns372p488 

noncomputable def Ns372p489 := nat_lit 2213609288845146193920000 

noncomputable def Ns372p490 := nat_lit 48612704950035054661373788160 

noncomputable abbrev qz750 := (Enclosure.sfrac Bool.false 716546 1000)

noncomputable abbrev qz624 := qz750

noncomputable abbrev qz418 := qz624

noncomputable abbrev qz80 := qz418

noncomputable abbrev qz751 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 716546 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz625 := qz751

noncomputable abbrev qz419 := qz625

noncomputable abbrev qz81 := qz419

noncomputable abbrev qz752 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 716546 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz626 := qz752

noncomputable abbrev qz420 := qz626

noncomputable abbrev qz82 := qz420

noncomputable abbrev qz627 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz81 qz9))

noncomputable def Ns372p491 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) (@HMul.hMul Real Real Real qz5 qz627 (Zeta.RiemannSiegel.correction qz82)) 347520595 134217728 149359 134217728 19910058829419934875 147573952589676412928 29360101724795576047 Ns372p489 Ns372p490 

noncomputable def Ns372p492 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos BSN.quadSignNeg 9 10 716546 1000 198 268435456 134217728 4503599627370496 Bool.false 359251953815 2489 618095470 48 84886744 8 

noncomputable def Ns372p493 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 716546 1000 96 150 268435456 134217728 4503599627370496 Bool.false 359251953815 2489 

noncomputable def Ns372p494 := Ns372p493 558195838 48 94906264 8 589812974 48 89478488 8 Bool.false 439529508 112331 Bool.true 241928006 Bool.true 127559212 14148475504056880 1 Bool.false 166598751 Bool.false Bool.false 238693741 Bool.true Bool.false 418866477 

noncomputable def Ns372p495 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 716546 1000 34 35 268435456 134217728 4503599627370496 Bool.false 359251953815 2489 

noncomputable def Ns372p496 := Ns372p495 480971758 48 109588312 8 522351262 48 101459064 8 Bool.false 408277765 83313 Bool.false 277211946 Bool.true 278743576 14148475504056880 1 Bool.false 137574937 Bool.true Bool.false 231282256 Bool.false Bool.false 439529508 

noncomputable def Ns372p497 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 716546 1000 219 117 268435456 134217728 4503599627370496 Bool.false 359251953815 2489 

noncomputable def Ns372p498 := Ns372p497 372130544 47 134217720 8 432030192 47 120047984 16 Bool.false 413200670 49027 Bool.false 260324243 Bool.false 348528751 14148475504056880 1 Bool.false 221395695 Bool.false Bool.false 258535849 Bool.true Bool.false 408277765 

noncomputable def Ns372p499 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 716546 1000 535 350 268435456 134217728 4503599627370496 Bool.false 359251953815 2489 

noncomputable def Ns372p500 := Ns372p499 186065264 47 189812528 16 294906480 47 154981288 8 Bool.false 268435392 2543 Bool.false 340909034 Bool.false 357795303 14148475504056880 1 Bool.false 256381749 Bool.false Bool.false 63261408 Bool.true Bool.false 413200670 

noncomputable def Ns372p501 := nat_lit 14340248372294350136299524498083336838983420374740329773 

noncomputable def Ns372p502 := nat_lit 10715129229183142923379377334232501004402595725312000 

noncomputable def Ns372p503 := nat_lit 90669694602983881310655143828480000 

noncomputable def Ns372p504 := nat_lit 389814130510172360059346004499548180480 

noncomputable abbrev qz628 := (@Eq.refl Real qz750)

noncomputable abbrev qz421 := qz628

noncomputable abbrev qz83 := qz421

noncomputable def Ns372p505 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz80 716546 1000 2053753680464 16000000 1433092 4000 2000 Ns372p503 Ns372p504 qz83 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns372p506 := nat_lit 293688286664588290791414261720746738462380449274681953751040 

noncomputable abbrev qz629 := (@HSub.hSub Real Real Real qz737 qz738 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz739 (@Nat.cast Real Real.instNatCast 1433092))))

noncomputable abbrev qz422 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 716546 4000) (Real.log (Enclosure.sfrac Bool.false 2053753680464 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz629))

noncomputable abbrev qz630 := (Enclosure.sfrac Bool.false 716546 2000)

noncomputable abbrev qz84 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz422 qz630) (@HMul.hMul Real Real Real qz349 qz630 (Real.log Real.pi)))

noncomputable def Ns372p507 := @Enclosure.Real.IsNear.addLit_ft_p qz84 (Enclosure.sfrac Bool.true Ns372p503 Ns372p504) 753406084388787251273 562949953421312000 170857271240010613 18432000000000000000000 Ns372p503 Ns372p504 0 1 Ns372p506 

noncomputable def Ns372p508 := nat_lit 25280113227009823385306791936000 

noncomputable abbrev qz85 := (@HSub.hSub Real Real Real qz353 qz422 qz630)

noncomputable def Ns372p509 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (@HMul.hMul Real Real Real qz5 qz630 (Real.log Real.pi)) 984286389566527694921 562949953421312000 35378248453031 9000000000000000000 13761538575753 33554432000 358273 67108864000 Ns372p508 753406084388787251273 562949953421312000 

noncomputable def Ns372p510 := nat_lit 1968572779133055389842000 

noncomputable abbrev qz86 := qz422

noncomputable def Ns372p511 := @Enclosure.Real.IsNear.subLit_ff_p qz86 qz630 1185976158228641409097 562949953421312000 35378248453031 9000000000000000000 716546 2000 0 1 Ns372p510 984286389566527694921 562949953421312000 35378248453031 9000000000000000000 

noncomputable def Ns372p512 := nat_lit 2670580892134400926722541167161901056 

noncomputable def Ns372p513 := nat_lit 56880399915785097131851776 

noncomputable def Ns372p514 := nat_lit 2536969182237392819199828117768003889921948463479440518974573153594075246649211368362044803196076123506967757272831469814513422415322137546623690461645998265015595646338191307605557859691601454256343534796800 

noncomputable def Ns372p515 := nat_lit 94826420322173515430540995251411011466970642132655405513887294436265255019340764606034692260749177794492146770857887153404109908952770469990910553124876135383792605096043383110858163928408463082040831508480 

noncomputable def Ns372p516 := nat_lit 2201630800578089207015923674577036779335460429049360998986519190270174339129353569580652840609874106090102767654251592701367127517266621834154302162325696618085839275164199960405112502812347360870400 

noncomputable def Ns372p517 := BSN.log_dyadic_bound 1005177680464 3102329680464 9 8 Ns372p514 134217728 46080000 Ns372p515 Ns372p516 90226005 4107507360928 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1005177680464) (BSN.artanhQ 3102329680464) 0 8 Ns372p515 Ns372p514 Ns372p516 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz423 := (Real.log (Enclosure.sfrac Bool.false 2053753680464 16000000))

noncomputable def Ns372p518 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 716546 4000) qz423 716546 4000 0 1 3310875030920439 281474976710656 48828161 2250000000000000 1186197129952958441847 562949953421312000 17493811725953 4500000000000000000 (Enclosure.Real.IsNear.const Bool.false 716546 4000) (BSN.isNear_log_sfrac 2053753680464 16000000 3310875030920439 281474976710656 48828161 2250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2053753680464) qz356)) Bool.false Ns372p513 Ns372p98 1000000737280000 46080000000000000000000 3310875030920439 281474976710656 48828161 2250000000000000 (BSN.log_rat_reduce_isNear 2053753680464 16000000 16 4107507360928 2097152000000 90226005 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns372p517 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p519 := BSN.arctan_dyadic_bound_f 1000 1433092 1 0 16777216 5760000 0 1 1 0 1 1 11707 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1433092) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1433092) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns372p520 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1433092))) 884279719003555 562949953421312 1 2000000000000000 11707 16777216 1 5760000 14829161395037243703296 883886897268131 562949953421312 3125000009 18000000000000000 qz17 (Ns372p519 rfl) rfl rfl 

noncomputable abbrev qz424 := (@HMul.hMul Real Real Real qz584 qz589 qz629)

noncomputable abbrev qz87 := qz424

noncomputable abbrev qz425 := qz629

noncomputable abbrev qz88 := qz425

noncomputable def Ns372p521 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 716546 4000) qz423) qz87 1186197129952958441847 562949953421312000 17493811725953 4500000000000000000 883886897268131 2251799813685248 3125000009 72000000000000000 Ns372p512 1185976158228641409097 562949953421312000 35378248453031 9000000000000000000 (Ns372p518 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz88 1 4 0 1 883886897268131 562949953421312 3125000009 18000000000000000 883886897268131 2251799813685248 3125000009 72000000000000000 qz363 Ns372p520 rfl) 

noncomputable def Ns372p522 := @Ns372p507 Ns372p501 Ns372p502 170857271240010613 18432000000000000000000 (@Ns372p509 170857271240010613 18432000000000000000000 (Ns372p511 (Ns372p521 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 716546 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz630 (Real.log Real.pi) 716546 2000 0 1 38410761 33554432 1 67108864 13761538575753 33554432000 358273 67108864000 (Enclosure.Real.IsNear.const Bool.false 716546 2000) RS373to384.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns372p503 Ns372p504) 

noncomputable def Ns372p523 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns372p501 Ns372p502 170857271240010613 18432000000000000000000 22453247113 16777216 39 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz364 qz84 (Enclosure.sfrac Bool.true Ns372p503 Ns372p504)) Bool.false Ns372p501 Ns372p502 170857271240010613 18432000000000000000000 Ns372p505 (Ns372p522 rfl rfl)) 

noncomputable def Ns372p524 := nat_lit 3796375539138876728672256 

noncomputable def Ns372p525 := nat_lit 3504996532468956416977629507723150493292898374559062752513264945405210560450044425450766998925440173537090077112637272122975032099108294656 

noncomputable def Ns372p526 := nat_lit 2490189165466030956053002789328114717669881196352513400310242542196077543291399448641651804309098550608824001722077006734329594515456 

noncomputable def Ns372p527 := nat_lit 17503241798058929826835628124083615271544325340711953678996211214383514960980053843141990085717514984068833659255378785638209581791852630016 

noncomputable def Ns372p528 := BSN.sin_dyadic_bound_f 107899482462 68719476736 4 3 33554432 11531251 Ns372p525 Ns372p111 Ns372p526 Ns372p527 Ns372p114 Ns372p526 33554424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107899482462) qz365 0 3 Ns372p525 Ns372p111 Ns372p526 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107899482462) qz366 0 3 Ns372p527 Ns372p114 Ns372p526 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p529 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz80) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 22453247113) qz411) Bool.false 22453247113 16777216 39 4194304 Bool.false 33554424 33554432 1 5760000 (Ns372p523 rfl) (Enclosure.sfrac_false_div 22453247113 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 22453247113) qz411) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns372p524) qz412) 226375608064910080 72057594037927936 Bool.false 33554424 33554432 212 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 22453247113 16777216 226375608064910080 72057594037927936 212 Ns372p524 Ns372p403 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554424 33554432 Ns372p524 Ns372p403 107899482462 68719476736 11531251 11520000 (Ns372p528 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p530 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns372p501 Ns372p502 170857271240010613 18432000000000000000000 359251953815 268435456 2489 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz364 qz84 (Enclosure.sfrac Bool.true Ns372p503 Ns372p504)) Bool.false Ns372p501 Ns372p502 170857271240010613 18432000000000000000000 Ns372p505 (Ns372p522 rfl rfl)) 

noncomputable def Ns372p531 := Ns372p500 49027 BSN.abs_quadSignPos (BSN.cos_quad_nat3 535 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 256381749 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 350 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 63261408 268435456) qz83 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) Bool.false 4194303 4194304 223471 23592960000 268435392 268435456 2543 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 4194303 4194304 223471 23592960000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz80) qz80) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 33554424 33554432 228834304 24159191040000 4194303 4194304 223471 23592960000 (Ns372p529 rfl rfl) rfl)) rfl) (Ns372p530 rfl) RS373to384.d7 

noncomputable def Ns372p532 := nat_lit 18912355678128246003168273810536555220993008260007476222726684719018397191916035773733356501244078950802067456 

noncomputable def Ns372p533 := nat_lit 2464121515896014876918457626791688766288100769478923935003044782623757066326527453148120363729353773056 

noncomputable def Ns372p534 := nat_lit 94511526049292901366993792906711989854831941123268009971908589948857441726108636559055592376962152134655676416 

noncomputable def Ns372p535 := BSN.sin_dyadic_bound_f 340909034 268435456 4 3 268435456 134217728 Ns372p532 Ns372p134 Ns372p533 Ns372p534 Ns372p137 Ns372p533 256381749 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 340909034) qz369 0 3 Ns372p532 Ns372p134 Ns372p533 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 340909034) qz370 0 3 Ns372p534 Ns372p137 Ns372p533 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p536 := nat_lit 8834839703224641702350981431408027973541190933543110871569863242480442190644108469487391048879014304239740321 

noncomputable def Ns372p537 := nat_lit 4401651153517567526550558042942704356624207146434142938075140292077915927108740661502414746406907700641 

noncomputable def Ns372p538 := nat_lit 53530999506390072450318765418001944482758977185738632449947108362172935075407296494171452093292325416343856545 

noncomputable def Ns372p539 := BSN.cos_dyadic_bound_f 357795303 268435456 4 3 268435456 134217728 Ns372p536 Ns372p143 Ns372p537 Ns372p538 Ns372p146 Ns372p537 63261408 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 357795303) qz371 0 3 Ns372p536 Ns372p143 Ns372p537 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 357795303) qz372 0 3 Ns372p538 Ns372p146 Ns372p537 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p540 := nat_lit 72131799677542444201281748253244746122758527434280454136893610692988705 

noncomputable def Ns372p541 := nat_lit 21091958754721888984389481640750649138269989663953959269464729472801 

noncomputable def Ns372p542 := nat_lit 188882469317484470802144138645365500699096087106516692519713656538681121 

noncomputable def Ns372p543 := BSN.sin_dyadic_bound_f 260324243 268435456 3 2 268435456 134217728 Ns372p540 Ns372p120 Ns372p541 Ns372p542 Ns372p123 Ns372p541 221395695 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 260324243) qz369 0 2 Ns372p540 Ns372p120 Ns372p541 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 260324243) qz370 0 2 Ns372p542 Ns372p123 Ns372p541 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p544 := nat_lit 20662389484359842702308143264298937903792216576717866411265979342020708969665703555726026847696109361373764801 

noncomputable def Ns372p545 := nat_lit 3212649297729021405772316425034741506511225577809639566282564291046858669046840642911984412307641720001 

noncomputable def Ns372p546 := nat_lit 103251973151193220790347941566558214132743337183453491987037324873521807256445307297520531446469319357424852161 

noncomputable def Ns372p547 := BSN.sin_dyadic_bound_f 348528751 268435456 4 3 268435456 134217728 Ns372p544 Ns372p134 Ns372p545 Ns372p546 Ns372p137 Ns372p545 258535849 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 348528751) qz369 0 3 Ns372p544 Ns372p134 Ns372p545 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 348528751) qz370 0 3 Ns372p546 Ns372p137 Ns372p545 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p548 := Ns372p498 83313 BSN.abs_quadSignPos (BSN.cos_quad_nat3 219 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 221395695 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 117 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 258535849 268435456) qz83 rfl rfl (Ns372p531 RS373to384.d9 RS373to384.d11 RS373to384.d13 RS373to384.d17 (Ns372p535 rfl rfl) (Ns372p539 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns372p530 rfl) RS373to384.d19 RS373to384.d21 RS373to384.d23 RS373to384.d25 RS373to384.d17 (Ns372p543 rfl rfl) (Ns372p547 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns372p549 := nat_lit 3179702269104437451572786110433399065438216519454656773220384771755854948600010113719087627037242854593335296 

noncomputable def Ns372p550 := nat_lit 205941228319490517448034114497022865446075955059444669428312940212478990077938418076886189136867823616 

noncomputable def Ns372p551 := nat_lit 19281492499919174093912109642957028052502906610845031182780340408068693776786293525827804342293304349963653120 

noncomputable def Ns372p552 := BSN.cos_dyadic_bound_f 277211946 268435456 4 3 268435456 134217728 Ns372p549 Ns372p143 Ns372p550 Ns372p551 Ns372p146 Ns372p550 137574937 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 277211946) qz371 0 3 Ns372p549 Ns372p143 Ns372p550 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 277211946) qz372 0 3 Ns372p551 Ns372p146 Ns372p550 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p553 := nat_lit 94826062500633239658301099742845225743080498504660671499744422899220480 

noncomputable def Ns372p554 := nat_lit 36445082563467186759493461130601813052002879464623846152138943102976 

noncomputable def Ns372p555 := nat_lit 248294966891793823659844652770383188296459967612120939129370025494839296 

noncomputable def Ns372p556 := BSN.sin_dyadic_bound_f 278743576 268435456 3 2 268435456 134217728 Ns372p553 Ns372p120 Ns372p554 Ns372p555 Ns372p123 Ns372p554 231282256 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 278743576) qz369 0 2 Ns372p553 Ns372p120 Ns372p554 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 278743576) qz370 0 2 Ns372p555 Ns372p123 Ns372p554 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p557 := Ns372p496 112331 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 34 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 137574937 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 35 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 231282256 268435456) qz83 rfl rfl (Ns372p548 rfl rfl) (Ns372p530 rfl) RS373to384.d27 RS373to384.d29 RS373to384.d31 RS373to384.d33 RS373to384.d17 (Ns372p552 rfl rfl) (Ns372p556 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p558 := nat_lit 29893991016783482482134464232946521408496860142831711862684294150922496 

noncomputable def Ns372p559 := nat_lit 11735164115476272651995944494397669589381371526887040096854566543616 

noncomputable def Ns372p560 := nat_lit 89658502722119494901099400809850768886311817685441361507859173319680256 

noncomputable def Ns372p561 := BSN.cos_dyadic_bound_f 241928006 268435456 3 2 268435456 134217728 Ns372p558 Ns372p159 Ns372p559 Ns372p560 Ns372p162 Ns372p559 166598751 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 241928006) qz371 0 2 Ns372p558 Ns372p159 Ns372p559 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 241928006) qz372 0 2 Ns372p560 Ns372p162 Ns372p559 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p562 := nat_lit 2309560207061204766576124871849021985721692461033356565078558417944576 

noncomputable def Ns372p563 := nat_lit 70096223685044192787851803847389334377245690878441948736871530496 

noncomputable def Ns372p564 := nat_lit 6928540428736244211342798911939371178496322891718312811338201510772736 

noncomputable def Ns372p565 := BSN.cos_dyadic_bound_f 127559212 268435456 3 2 268435456 134217728 Ns372p562 Ns372p159 Ns372p563 Ns372p564 Ns372p162 Ns372p563 238693741 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 127559212) qz371 0 2 Ns372p562 Ns372p159 Ns372p563 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 127559212) qz372 0 2 Ns372p564 Ns372p162 Ns372p563 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p566 := Ns372p494 137685 BSN.abs_quadSignPos (BSN.cos_quad_nat0 96 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 166598751 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 150 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 238693741 268435456) qz83 rfl rfl (Ns372p557 rfl) (Ns372p530 rfl) RS373to384.d35 RS373to384.d37 RS373to384.d39 RS373to384.d41 RS373to384.d17 (Ns372p561 rfl rfl) (Ns372p565 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p567 := nat_lit 4869989968441379618119927895782200476771778110843082849106082665758976 

noncomputable def Ns372p568 := nat_lit 311647003411260932901181123467283713821004840279095659864182128896 

noncomputable def Ns372p569 := nat_lit 14609346611317316332493981325099666862887692322848690355998519633019136 

noncomputable def Ns372p570 := BSN.cos_dyadic_bound_f 153712034 268435456 3 2 268435456 134217728 Ns372p567 Ns372p159 Ns372p568 Ns372p569 Ns372p162 Ns372p568 225615489 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 153712034) qz371 0 2 Ns372p567 Ns372p159 Ns372p568 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 153712034) qz372 0 2 Ns372p569 Ns372p162 Ns372p568 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p571 := Ns372p492 Bool.false 418866477 137685 Bool.true 153712034 14148475504056880 1 Bool.false 225615489 Bool.true Bool.false 347520595 149359 BSN.abs_quadSignNeg qz595 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 225615489 268435456) qz83 rfl (Ns372p566 rfl) (Ns372p530 rfl) RS373to384.d43 RS373to384.d45 RS373to384.d17 (Ns372p570 rfl rfl) rfl 

noncomputable def Ns372p572 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) 347520595 268435456 149359 268435456 347520595 268435456 149359 268435456 186573698776432640 347520595 134217728 149359 134217728 (Ns372p571 rfl rfl rfl rfl) 

noncomputable def Ns372p573 := @Enclosure.Real.IsNear.mulLit_ff qz627 (Zeta.RiemannSiegel.correction qz82) 641747 2097152 1 16777216 31024778969625 70368744177664 1426863144509 32985348833280000 19910058829419934875 147573952589676412928 

noncomputable abbrev qz631 := (@HPow.hPow Real Real Real qz7 qz81 qz9)

noncomputable def Ns372p574 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz631 1 1 0 1 641747 2097152 1 16777216 641747 2097152 1 16777216 

noncomputable def Ns372p575 := @Enclosure.Real.IsNear.sqrt_image qz81 1913304290369 16777216000 358273 16777216000 179164486 179164521 16777216 (@Enclosure.Real.IsNear.of_eq qz81 (@HMul.hMul Real Real Real qz5 qz80 qz3) Bool.false 1913304290369 16777216000 358273 16777216000 (BSN.t_div_two_pi_mk qz80 716546 1000 qz83) (@Enclosure.Real.IsNear.mulLit_ff qz80 qz3 716546 1000 0 1 5340353 33554432 1 33554432 1913304290369 16777216000 358273 16777216000 (Enclosure.Real.IsNear.const Bool.false 716546 1000) RS373to384.d48 rfl)) 

noncomputable abbrev qz753 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 716546 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz632 := qz753

noncomputable abbrev qz426 := qz632

noncomputable abbrev qz89 := qz426

noncomputable def Ns372p576 := @Enclosure.Real.IsNear.sqrt_image qz89 358329007 33554432 35 33554432 54825917 54825924 16777216 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 358329007 33554432 35 33554432 358329007 33554432 35 33554432 (Ns372p575 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns372p577 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz89) 109651841 33554432 7 33554432 5133975 5133977 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz89) Bool.false 109651841 33554432 7 33554432 109651841 33554432 7 33554432 (Ns372p576 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns372p578 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 10267952 33554432 2 33554432 641747 2097152 1 16777216 (Ns372p577 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz427 := (@HMul.hMul Real Real Real qz584 qz582 qz626)

noncomputable abbrev qz90 := (Real.cos qz427)

noncomputable abbrev qz633 := (@HMul.hMul Real Real Real qz733 qz752 qz752)

noncomputable abbrev qz428 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz633 qz626) qz600)

noncomputable abbrev qz91 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz428))

noncomputable def Ns372p579 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz82) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz90) qz91) Bool.false 31024778969625 

noncomputable def Ns372p580 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz90) qz91 77807625 33554432 1221 

noncomputable abbrev qz92 := (@Neg.neg Real Real.instNeg (Real.cos qz427))

noncomputable def Ns372p581 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz90) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz92)) Bool.true 77807625 33554432 1221 33554432 (BSN.inv_eq_neg_inv_neg qz90) 

noncomputable def Ns372p582 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz92) Bool.false 77807625 33554432 1221 33554432 77807625 33554432 

noncomputable def Ns372p583 := @Enclosure.Real.IsNear.recentre' qz90 Bool.true 14470303 33554432 1306514432 193273528320000 14470303 33554432 1275893 188743680000 

noncomputable abbrev qz93 := qz427

noncomputable def Ns372p584 := @Enclosure.Real.IsNear.cos_image qz93 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 71580205) qz411) Bool.false 71580205 16777216 221 33554432 Bool.true 14470303 33554432 1 

noncomputable def Ns372p585 := nat_lit 944512639512260561960106549 

noncomputable def Ns372p586 := nat_lit 144115188075855872000000000000000 

noncomputable def Ns372p587 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz82 884279719003555 140737488355328 1 500000000000000 22784687 33554432 35 33554432 20148036617943952562285 4722366482869645213696 Ns372p585 

noncomputable def Ns372p588 := @Enclosure.Real.IsNear.subLit_ff_p qz89 qz1 358329007 33554432 35 33554432 10 1 0 1 22784687 22784687 33554432 35 

noncomputable def Ns372p589 := @Ns372p588 33554432 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 358329007 33554432 35 33554432 358329007 33554432 35 33554432 (Ns372p575 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns372p590 := @Enclosure.Real.IsNear.recentre' qz93 Bool.false 20148036617943952562285 4722366482869645213696 Ns372p585 Ns372p586 71580205 16777216 221 33554432 (@Ns372p587 Ns372p586 RS373to384.d47 (Ns372p589 rfl rfl) rfl) 

noncomputable def Ns372p591 := nat_lit 2719889758810642002739200 

noncomputable def Ns372p592 := nat_lit 1339209159170668272787614497715046355280557484106045944228454043031456193324481805864041281 

noncomputable def Ns372p593 := nat_lit 1275298871075486467732995736347434154714275574370383157501153869871553991180457785326401 

noncomputable def Ns372p594 := nat_lit 4015076879769853845427377501672444197532243901169397066370359821354625471991084502021471041 

noncomputable def Ns372p595 := BSN.cos_dyadic_bound_f 77303916407 68719476736 3 2 33554432 11531251 Ns372p592 Ns372p186 Ns372p593 Ns372p594 Ns372p189 Ns372p593 14470303 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 77303916407) qz379 0 2 Ns372p592 Ns372p186 Ns372p593 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 77303916407) qz380 0 2 Ns372p594 Ns372p189 Ns372p593 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p596 := @Ns372p584 5760000 (Ns372p590 rfl) (Enclosure.sfrac_false_div 71580205 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 71580205) qz411) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns372p591) qz412) 226375608064910080 72057594037927936 Bool.false 14470303 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q2 71580205 16777216 226375608064910080 72057594037927936 0 Ns372p591 Ns372p403 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 14470303 33554432 Ns372p591 Ns372p403 77303916407 68719476736 11531251 11520000 (Ns372p595 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p597 := @Enclosure.Real.IsNear.inv_image qz92 14470303 33554432 1275893 188743680000 38903202 38904423 16777216 (@Enclosure.Real.IsNear.neg qz90 Bool.true 14470303 33554432 1275893 188743680000 (Ns372p583 (Ns372p596 rfl rfl) rfl)) 

noncomputable def Ns372p598 := Ns372p581 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz92) Bool.false 77807625 33554432 1221 33554432 (@Ns372p582 1221 33554432 (Ns372p597 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p599 := @Enclosure.Real.IsNear.recentre' qz91 Bool.true 3189896 16777216 

noncomputable abbrev qz94 := (@HMul.hMul Real Real Real qz349 qz346 qz428)

noncomputable def Ns372p600 := @Enclosure.Real.IsNear.cos_image qz94 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1847689)) (@Nat.cast Real Real.instNatCast 1048576)) Bool.true 1847689 1048576 

noncomputable def Ns372p601 := nat_lit 279214869953976562269873662845 

noncomputable def Ns372p602 := nat_lit 158456325028528675187087900672 

noncomputable def Ns372p603 := nat_lit 74733467898484691830158776621772213 

noncomputable def Ns372p604 := @Enclosure.Real.IsNear.recentre' qz94 Bool.true Ns372p601 Ns372p602 Ns372p603 

noncomputable def Ns372p605 := nat_lit 4835703278458516698824704000000000000000 

noncomputable abbrev qz95 := qz428

noncomputable def Ns372p606 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz95 884279719003555 140737488355328 1 500000000000000 315754013072479 

noncomputable abbrev qz429 := (@HSub.hSub Real Real Real qz588 qz633 qz626)

noncomputable abbrev qz96 := qz429

noncomputable def Ns372p607 := @Enclosure.Real.IsNear.subLit_tf qz96 qz31 245385268894815 1125899906842624 2769334435 1125899906842624 1 16 

noncomputable abbrev qz430 := qz633

noncomputable abbrev qz97 := qz430

noncomputable def Ns372p608 := @Enclosure.Real.IsNear.subLit_ff_n qz97 qz82 519141961687969 1125899906842624 1594929315 1125899906842624 22784687 33554432 35 33554432 

noncomputable def Ns372p609 := @Enclosure.Real.IsNear.mulLit_ff qz82 qz82 22784687 33554432 35 33554432 22784687 33554432 35 33554432 519141961687969 1125899906842624 

noncomputable def Ns372p610 := nat_lit 341922479963009239896171336475593086957314631903575777950236126231415461715852001 

noncomputable def Ns372p611 := nat_lit 846322570984149739285326836131859157750990110577656481930582364989086940895641600 

noncomputable def Ns372p612 := nat_lit 1583239000835659385546027495209381089802793896398065966510335396632346180321 

noncomputable def Ns372p613 := nat_lit 2066431164047053834818489414105688106184669266547150583237730185679768670981798625 

noncomputable def Ns372p614 := nat_lit 77015353959557626274964742087999183355340100062566739855682995214006911621503385600 

noncomputable def Ns372p615 := BSN.cos_dyadic_bound_t 1847689 1048576 4 3 16777216 5760000 Ns372p610 Ns372p611 Ns372p612 Ns372p613 Ns372p614 Ns372p612 3189896 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 1847689) (BSN.cosEvenQ 1048576) 0 3 Ns372p610 Ns372p611 Ns372p612 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 1847689) (BSN.cosOddQ 1048576) 0 3 Ns372p613 Ns372p614 Ns372p612 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p616 := @Ns372p599 378594304 24159191040000 398737 2097152 369721 23592960000 (@Ns372p600 65 4194304 Bool.true 3189896 16777216 1 5760000 (@Ns372p604 Ns372p605 1847689 1048576 65 4194304 (@Ns372p606 1125899906842624 2769334435 1125899906842624 Ns372p601 Ns372p602 Ns372p603 Ns372p605 RS373to384.d47 (@Ns372p607 0 1 5052064209159664 315754013072479 1125899906842624 2769334435 1125899906842624 (@Ns372p608 8233763318932785070080 245385268894815 1125899906842624 2769334435 1125899906842624 (@Ns372p609 1594929315 1125899906842624 (Ns372p589 rfl rfl) (Ns372p589 rfl rfl) rfl) (Ns372p589 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 1847689 1048576) (BSN.cos_neg_of_bound 1847689 1048576 Bool.true 3189896 16777216 1 5760000 (Ns372p615 rfl rfl)) rfl rfl) 

noncomputable def Ns372p617 := @Ns372p573 29360101724795576047 Ns372p489 (Ns372p574 qz33 (@Enclosure.Real.IsNear.of_eq qz631 (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 641747 2097152 1 16777216 (BSN.rpow_neg_quarter_mk qz81 (BSN.t_div_two_pi_nonneg qz80 716546 1000 qz83)) Ns372p578) rfl) (@Ns372p579 70368744177664 1426863144509 32985348833280000 (BSN.correction_mk qz82 (BSN.cos_two_pi_p_ne_zero_mk qz80 716546 1000 10 qz83 rfl rfl (@BSN.floor_sqrt_eq_dec qz80 716546 1000 10 qz83 rfl rfl rfl))) (@Ns372p580 33554432 398737 2097152 369721 23592960000 31024778969625 70368744177664 1426863144509 32985348833280000 Ns372p598 (Ns372p616 rfl) rfl)) 

noncomputable def Ns372p618 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (hardyZApproximantRS₀ qz80) Bool.false 362192876264714111845 147573952589676412928 2492689459919729336047 Ns372p489 (@Eq.refl Real (hardyZApproximantRS₀ qz80)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) (@HMul.hMul Real Real Real qz5 qz627 (Zeta.RiemannSiegel.correction qz82))) Bool.false 362192876264714111845 147573952589676412928 2492689459919729336047 Ns372p489 (BSN.hardyZApproximantRS₀_eq qz80 10 (@BSN.floor_sqrt_eq_dec qz80 716546 1000 10 qz83 rfl rfl rfl)) (@Ns372p491 362192876264714111845 147573952589676412928 2492689459919729336047 Ns372p489 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 10)) Bool.false 347520595 134217728 149359 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) (Ns372p572 (Ns372p571 rfl rfl rfl rfl) rfl rfl)) (Ns372p617 rfl) rfl rfl)) 

theorem RS373to384.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz80) Bool.false 362192876264714111845 147573952589676412928 2492689459919729336047 Ns372p489 := Ns372p618 

noncomputable def Ns372p619 := nat_lit 4427218577690292387840000 

noncomputable def Ns372p620 := nat_lit 7123909102464381504718897152 

noncomputable abbrev qz754 := (Enclosure.sfrac Bool.false 717873 1000)

noncomputable abbrev qz634 := qz754

noncomputable abbrev qz431 := qz634

noncomputable abbrev qz98 := qz431

noncomputable abbrev qz755 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 717873 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz635 := qz755

noncomputable abbrev qz432 := qz635

noncomputable abbrev qz99 := qz432

noncomputable abbrev qz756 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 717873 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz636 := qz756

noncomputable abbrev qz433 := qz636

noncomputable abbrev qz100 := qz433

noncomputable abbrev qz637 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz99 qz9))

noncomputable def Ns372p621 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) (@HMul.hMul Real Real Real qz5 qz637 (Zeta.RiemannSiegel.correction qz100)) 174712203 134217728 37407 33554432 5052734254854926577 36893488147419103232 66271744368188855923 Ns372p619 Ns372p620 

noncomputable def Ns372p622 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos BSN.quadSignNeg 9 10 717873 1000 198 268435456 134217728 4503599627370496 Bool.false 360095733971 2493 618095470 48 84886744 8 

noncomputable def Ns372p623 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 717873 1000 96 150 268435456 134217728 4503599627370496 Bool.false 360095733971 2493 

noncomputable def Ns372p624 := Ns372p623 558195838 48 94906264 8 589812974 48 89478488 8 Bool.true 95344538 112532 Bool.true 138873728 Bool.true 66460873 14148475504056880 1 Bool.false 233306746 Bool.false Bool.false 260250005 Bool.true Bool.true 99608153 

noncomputable def Ns372p625 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 717873 1000 35 35 268435456 134217728 4503599627370496 Bool.false 360095733971 2493 

noncomputable def Ns372p626 := Ns372p625 480971758 48 109588312 8 522351262 48 101459064 8 Bool.true 166676067 83461 Bool.false 61085150 Bool.true 128123545 14148475504056880 1 Bool.false 60559312 Bool.false Bool.false 123313959 Bool.false Bool.true 95344538 

noncomputable def Ns372p627 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 717873 1000 220 118 268435456 134217728 4503599627370496 Bool.false 360095733971 2493 

noncomputable def Ns372p628 := Ns372p627 372130544 47 134217720 8 432030192 47 120047984 16 Bool.true 180056480 49112 Bool.false 188629739 Bool.false 197347413 14148475504056880 1 Bool.false 204843007 Bool.false Bool.false 199101919 Bool.true Bool.true 166676067 

noncomputable def Ns372p629 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 717873 1000 537 351 268435456 134217728 4503599627370496 Bool.false 360095733971 2493 

noncomputable def Ns372p630 := Ns372p629 186065264 47 189812528 16 294906480 47 154981288 8 Bool.true 268435296 2543 Bool.false 94465728 Bool.false 388577132 14148475504056880 1 Bool.false 92527957 Bool.true Bool.false 266399730 Bool.false Bool.true 180056480 

noncomputable def Ns372p631 := nat_lit 41342261028908116680889519526740760552946813944261005919 

noncomputable def Ns372p632 := nat_lit 30818828562572040986757523802253844373969826951987200 

noncomputable def Ns372p633 := nat_lit 91512383676424848465420921884640000 

noncomputable def Ns372p634 := nat_lit 394165705675886171208074009399929024320 

noncomputable abbrev qz638 := (@Eq.refl Real qz754)

noncomputable abbrev qz434 := qz638

noncomputable abbrev qz101 := qz434

noncomputable def Ns372p635 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz98 717873 1000 2061367576516 16000000 1435746 4000 2000 Ns372p633 Ns372p634 qz101 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns372p636 := nat_lit 119065711763255376040961816237013390392486824159471697046720 

noncomputable abbrev qz639 := (@HSub.hSub Real Real Real qz737 qz738 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz739 (@Nat.cast Real Real.instNatCast 1435746))))

noncomputable abbrev qz435 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 717873 4000) (Real.log (Enclosure.sfrac Bool.false 2061367576516 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz639))

noncomputable abbrev qz640 := (Enclosure.sfrac Bool.false 717873 2000)

noncomputable abbrev qz102 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz435 qz640) (@HMul.hMul Real Real Real qz349 qz640 (Real.log Real.pi)))

noncomputable def Ns372p637 := @Enclosure.Real.IsNear.addLit_ft_p qz102 (Enclosure.sfrac Bool.true Ns372p633 Ns372p634) 302070247754931201071 225179981368524800 342344414111242213 36864000000000000000000 Ns372p633 Ns372p634 0 1 Ns372p636 

noncomputable def Ns372p638 := nat_lit 101357955875159916510151966720000 

noncomputable abbrev qz103 := (@HSub.hSub Real Real Real qz353 qz435 qz640)

noncomputable def Ns372p639 := @Enclosure.Real.IsNear.subLit_ff_p qz103 (@HMul.hMul Real Real Real qz5 qz640 (Real.log Real.pi)) 1972967001946483258603 1125899906842624000 17721521711339 4500000000000000000 27574048231353 67108864000 717873 134217728000 Ns372p638 302070247754931201071 225179981368524800 

noncomputable def Ns372p640 := nat_lit 3945934003892966517206000 

noncomputable abbrev qz104 := qz435

noncomputable def Ns372p641 := @Enclosure.Real.IsNear.subLit_ff_p qz104 qz640 2377093573858900767979 1125899906842624000 17721521711339 4500000000000000000 717873 2000 0 1 Ns372p640 1972967001946483258603 1125899906842624000 17721521711339 4500000000000000000 

noncomputable def Ns372p642 := nat_lit 5352738866727873055020332621383073792 

noncomputable def Ns372p643 := nat_lit 56898294230314114908946432 

noncomputable def Ns372p644 := nat_lit 2638445829441656871436756180051952150020469080816642778368437612515861667347743315747015060554203527064585849350806981286027896069739483607116576263952314837823492564121123881981078572472525789007467826380800 

noncomputable def Ns372p645 := nat_lit 99699949811061693898229679461739714421464369021355734945683931373779310837427513342785011975085628660346055979496734658280913264871657059245330327951223275158772061322014225312589799308072976045430412410880 

noncomputable def Ns372p646 := nat_lit 2484164750241015934006896339561745818947294196875543520926079205717909010540242944915997094491653367108779548928005703677146096094179648634490703448229943458016634253584057043138590679735669778022400 

noncomputable def Ns372p647 := BSN.log_dyadic_bound 1012791576516 3109943576516 9 8 Ns372p644 134217728 46080000 Ns372p645 Ns372p646 90722672 4122735153032 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1012791576516) (BSN.artanhQ 3109943576516) 0 8 Ns372p645 Ns372p644 Ns372p646 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz436 := (Real.log (Enclosure.sfrac Bool.false 2061367576516 16000000))

noncomputable def Ns372p648 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 717873 4000) qz436 717873 4000 0 1 3311916617112823 281474976710656 48828161 2250000000000000 2377535517676633585479 1125899906842624000 11684139473851 3000000000000000000 (Enclosure.Real.IsNear.const Bool.false 717873 4000) (BSN.isNear_log_sfrac 2061367576516 16000000 3311916617112823 281474976710656 48828161 2250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2061367576516) qz356)) Bool.false Ns372p643 Ns372p98 1000000737280000 46080000000000000000000 3311916617112823 281474976710656 48828161 2250000000000000 (BSN.log_rat_reduce_isNear 2061367576516 16000000 16 4122735153032 2097152000000 90722672 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns372p647 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p649 := BSN.arctan_dyadic_bound_f 1000 1435746 1 0 16777216 5760000 0 1 1 0 1 1 11685 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1435746) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1435746) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns372p650 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1435746))) 884279719003555 562949953421312 1 2000000000000000 11685 16777216 1 5760000 14829173779936218972160 883887635465635 562949953421312 3125000009 18000000000000000 qz17 (Ns372p649 rfl) rfl rfl 

noncomputable abbrev qz437 := (@HMul.hMul Real Real Real qz584 qz589 qz639)

noncomputable abbrev qz105 := qz437

noncomputable abbrev qz438 := qz639

noncomputable abbrev qz106 := qz438

noncomputable def Ns372p651 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 717873 4000) qz436) qz105 2377535517676633585479 1125899906842624000 11684139473851 3000000000000000000 883887635465635 2251799813685248 3125000009 72000000000000000 Ns372p642 2377093573858900767979 1125899906842624000 17721521711339 4500000000000000000 (Ns372p648 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz106 1 4 0 1 883887635465635 562949953421312 3125000009 18000000000000000 883887635465635 2251799813685248 3125000009 72000000000000000 qz363 Ns372p650 rfl) 

noncomputable def Ns372p652 := @Ns372p637 Ns372p631 Ns372p632 342344414111242213 36864000000000000000000 (@Ns372p639 342344414111242213 36864000000000000000000 (Ns372p641 (Ns372p651 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 717873 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz640 (Real.log Real.pi) 717873 2000 0 1 38410761 33554432 1 67108864 27574048231353 67108864000 717873 134217728000 (Enclosure.Real.IsNear.const Bool.false 717873 2000) RS373to384.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns372p633 Ns372p634) 

noncomputable def Ns372p653 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns372p631 Ns372p632 342344414111242213 36864000000000000000000 22505983373 16777216 39 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz364 qz102 (Enclosure.sfrac Bool.true Ns372p633 Ns372p634)) Bool.false Ns372p631 Ns372p632 342344414111242213 36864000000000000000000 Ns372p635 (Ns372p652 rfl rfl)) 

noncomputable def Ns372p654 := BSN.cos_dyadic_bound_f 74298513 68719476736 1 0 33554432 11531251 0 1 1 0 1 1 33554412 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 74298513) qz379 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 74298513) qz380 0 0 rfl) rfl rfl 

noncomputable def Ns372p655 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz98) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 22505983373) qz411) Bool.false 22505983373 16777216 39 4194304 Bool.true 33554412 33554432 1 5760000 (Ns372p653 rfl) (Enclosure.sfrac_false_div 22505983373 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 22505983373) qz411) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2614146547096418779136) qz412) 226375608064910080 72057594037927936 Bool.false 33554412 33554432 213 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q2 22505983373 16777216 226375608064910080 72057594037927936 213 2614146547096418779136 Ns372p403 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554412 33554432 2614146547096418779136 Ns372p403 74298513 68719476736 11531251 11520000 (Ns372p654 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p656 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns372p631 Ns372p632 342344414111242213 36864000000000000000000 360095733971 268435456 2493 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz364 qz102 (Enclosure.sfrac Bool.true Ns372p633 Ns372p634)) Bool.false Ns372p631 Ns372p632 342344414111242213 36864000000000000000000 Ns372p635 (Ns372p652 rfl rfl)) 

noncomputable def Ns372p657 := Ns372p630 49112 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 537 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 92527957 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 351 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266399730 268435456) qz101 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) Bool.true 8388603 8388608 223471 23592960000 268435296 268435456 2543 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 8388603 8388608 223471 23592960000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz98) qz98) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 33554412 33554432 228834304 24159191040000 8388603 8388608 223471 23592960000 (Ns372p655 rfl rfl) rfl)) rfl) (Ns372p656 rfl) RS373to384.d7 

noncomputable def Ns372p658 := nat_lit 79633738236922639288804369760256 

noncomputable def Ns372p659 := BSN.sin_dyadic_bound_f 94465728 268435456 2 1 268435456 134217728 Ns372p658 Ns372p130 Ns372p658 Ns372p658 Ns372p131 Ns372p658 92527957 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 94465728) qz369 0 1 Ns372p658 Ns372p130 Ns372p658 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 94465728) qz370 0 1 Ns372p658 Ns372p131 Ns372p658 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p660 := nat_lit 31941650544676818044892231136755556489370224965549605276513981974856737570480622049006871878899294630236389376 

noncomputable def Ns372p661 := nat_lit 11850232255352358962800789503147723020241651909746310687919876811555988756770168764852308767294227480576 

noncomputable def Ns372p662 := nat_lit 159565058755163166740358703554779208510775734385189318990849130318860038008355123866055586666039188808831860736 

noncomputable def Ns372p663 := BSN.sin_dyadic_bound_f 388577132 268435456 4 3 268435456 134217728 Ns372p660 Ns372p134 Ns372p661 Ns372p662 Ns372p137 Ns372p661 266399730 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 388577132) qz369 0 3 Ns372p660 Ns372p134 Ns372p661 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 388577132) qz370 0 3 Ns372p662 Ns372p137 Ns372p661 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p664 := nat_lit 11045171868810904864119981947562604053010402219815829639104094142091361 

noncomputable def Ns372p665 := nat_lit 1602807295788538918960409445248224517182085891882069419559637110881 

noncomputable def Ns372p666 := nat_lit 33132309991841137514522025023797315709996842487663724778473163152052321 

noncomputable def Ns372p667 := BSN.cos_dyadic_bound_f 188629739 268435456 3 2 268435456 134217728 Ns372p664 Ns372p159 Ns372p665 Ns372p666 Ns372p162 Ns372p665 204843007 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 188629739) qz371 0 2 Ns372p664 Ns372p159 Ns372p665 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 188629739) qz372 0 2 Ns372p666 Ns372p162 Ns372p665 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p668 := nat_lit 13233357848123871724970685332237818699064971204182359565234433866351201 

noncomputable def Ns372p669 := nat_lit 2300655017872833204931782560187570858304045916570615881580245697121 

noncomputable def Ns372p670 := nat_lit 39695472234335869508502192431593080955478305520713937463940141107659361 

noncomputable def Ns372p671 := BSN.cos_dyadic_bound_f 197347413 268435456 3 2 268435456 134217728 Ns372p668 Ns372p159 Ns372p669 Ns372p670 Ns372p162 Ns372p669 199101919 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 197347413) qz371 0 2 Ns372p668 Ns372p159 Ns372p669 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 197347413) qz372 0 2 Ns372p670 Ns372p162 Ns372p669 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p672 := Ns372p628 83461 BSN.abs_quadSignPos (BSN.cos_quad_nat0 220 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 204843007 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 118 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 199101919 268435456) qz101 rfl rfl (Ns372p657 RS373to384.d9 RS373to384.d11 RS373to384.d13 RS373to384.d17 (Ns372p659 rfl rfl) (Ns372p663 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns372p656 rfl) RS373to384.d19 RS373to384.d21 RS373to384.d23 RS373to384.d25 RS373to384.d17 (Ns372p667 rfl rfl) (Ns372p671 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns372p673 := nat_lit 13923312754459110850023006250000 

noncomputable def Ns372p674 := BSN.sin_dyadic_bound_f 61085150 268435456 2 1 268435456 134217728 Ns372p673 Ns372p130 Ns372p673 Ns372p673 Ns372p131 Ns372p673 60559312 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 61085150) qz369 0 1 Ns372p673 Ns372p130 Ns372p673 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 61085150) qz370 0 1 Ns372p673 Ns372p131 Ns372p673 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p675 := nat_lit 4231209611381285874744012183767139333384924721057891656262850303730625 

noncomputable def Ns372p676 := nat_lit 72615874498604287690514719574141334047512541984554043844187890625 

noncomputable def Ns372p677 := nat_lit 11081621889820846217387580600320340120514916391988407916998384015090625 

noncomputable def Ns372p678 := BSN.sin_dyadic_bound_f 128123545 268435456 3 2 268435456 134217728 Ns372p675 Ns372p120 Ns372p676 Ns372p677 Ns372p123 Ns372p676 123313959 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 128123545) qz369 0 2 Ns372p675 Ns372p120 Ns372p676 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 128123545) qz370 0 2 Ns372p677 Ns372p123 Ns372p676 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p679 := Ns372p626 112532 BSN.abs_quadSignPos (BSN.cos_quad_nat3 35 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 60559312 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 35 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 123313959 268435456) qz101 rfl rfl (Ns372p672 rfl rfl) (Ns372p656 rfl) RS373to384.d27 RS373to384.d29 RS373to384.d31 RS373to384.d33 RS373to384.d17 (Ns372p674 rfl rfl) (Ns372p678 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p680 := nat_lit 3244648758048491527933378946771084234246245116901481941593262932361216 

noncomputable def Ns372p681 := nat_lit 138344135145693720177524993036880170650980567740046375683186753536 

noncomputable def Ns372p682 := nat_lit 9733669585875183196359781790327178942397433389568965732028422423576576 

noncomputable def Ns372p683 := BSN.cos_dyadic_bound_f 138873728 268435456 3 2 268435456 134217728 Ns372p680 Ns372p159 Ns372p681 Ns372p682 Ns372p162 Ns372p681 233306746 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 138873728) qz371 0 2 Ns372p680 Ns372p159 Ns372p681 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 138873728) qz372 0 2 Ns372p682 Ns372p162 Ns372p681 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p684 := nat_lit 19510309853341649766457183892641 

noncomputable def Ns372p685 := BSN.cos_dyadic_bound_f 66460873 268435456 2 1 268435456 134217728 Ns372p684 Ns372p427 Ns372p684 Ns372p684 Ns372p428 Ns372p684 260250005 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 66460873) qz371 0 1 Ns372p684 Ns372p427 Ns372p684 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 66460873) qz372 0 1 Ns372p684 Ns372p428 Ns372p684 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p686 := Ns372p624 137933 BSN.abs_quadSignPos (BSN.cos_quad_nat0 96 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 233306746 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 150 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 260250005 268435456) qz101 rfl rfl (Ns372p679 rfl) (Ns372p656 rfl) RS373to384.d35 RS373to384.d37 RS373to384.d39 RS373to384.d41 RS373to384.d17 (Ns372p683 rfl rfl) (Ns372p685 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p687 := nat_lit 2502575854888782292775199694205109039648432825694483452923700526259521 

noncomputable def Ns372p688 := nat_lit 82301612176449533982003642389907218002969329235606957974693944641 

noncomputable def Ns372p689 := nat_lit 7507562961441993979257635075330547304509292538424979144855152190889281 

noncomputable def Ns372p690 := BSN.cos_dyadic_bound_f 130144567 268435456 3 2 268435456 134217728 Ns372p687 Ns372p159 Ns372p688 Ns372p689 Ns372p162 Ns372p688 237499858 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 130144567) qz371 0 2 Ns372p687 Ns372p159 Ns372p688 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 130144567) qz372 0 2 Ns372p689 Ns372p162 Ns372p688 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p691 := Ns372p622 Bool.true 99608153 137933 Bool.true 130144567 14148475504056880 1 Bool.false 237499858 Bool.true Bool.true 174712203 149628 BSN.abs_quadSignNeg qz595 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 237499858 268435456) qz101 rfl (Ns372p686 rfl) (Ns372p656 rfl) RS373to384.d43 RS373to384.d45 RS373to384.d17 (Ns372p690 rfl rfl) rfl 

noncomputable def Ns372p692 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) 174712203 268435456 149628 268435456 174712203 268435456 149628 268435456 93797899762139136 174712203 134217728 37407 33554432 (Ns372p691 rfl rfl rfl rfl) 

noncomputable def Ns372p693 := @Enclosure.Real.IsNear.mulLit_ff qz637 (Zeta.RiemannSiegel.correction qz100) 2565801 8388608 1 16777216 1969261939977 4398046511104 12891408133441 263882790666240000 5052734254854926577 36893488147419103232 

noncomputable abbrev qz641 := (@HPow.hPow Real Real Real qz7 qz99 qz9)

noncomputable def Ns372p694 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz641 1 1 0 1 2565801 8388608 1 16777216 2565801 8388608 1 16777216 

noncomputable def Ns372p695 := @Enclosure.Real.IsNear.sqrt_image qz99 3833695229169 33554432000 717873 33554432000 179330311 179330345 16777216 (@Enclosure.Real.IsNear.of_eq qz99 (@HMul.hMul Real Real Real qz5 qz98 qz3) Bool.false 3833695229169 33554432000 717873 33554432000 (BSN.t_div_two_pi_mk qz98 717873 1000 qz101) (@Enclosure.Real.IsNear.mulLit_ff qz98 qz3 717873 1000 0 1 5340353 33554432 1 33554432 3833695229169 33554432000 717873 33554432000 (Enclosure.Real.IsNear.const Bool.false 717873 1000) RS373to384.d48 rfl)) 

noncomputable abbrev qz757 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 717873 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz642 := qz757

noncomputable abbrev qz439 := qz642

noncomputable abbrev qz107 := qz439

noncomputable def Ns372p696 := @Enclosure.Real.IsNear.sqrt_image qz107 22416291 2097152 17 16777216 54851284 54851290 16777216 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 358660656 33554432 34 33554432 22416291 2097152 17 16777216 (Ns372p695 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns372p697 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz107) 54851287 16777216 3 16777216 5131601 5131603 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz107) Bool.false 109702574 33554432 6 33554432 54851287 16777216 3 16777216 (Ns372p696 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns372p698 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 10263204 33554432 2 33554432 2565801 8388608 1 16777216 (Ns372p697 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz440 := (@HMul.hMul Real Real Real qz584 qz582 qz636)

noncomputable abbrev qz108 := (Real.cos qz440)

noncomputable abbrev qz643 := (@HMul.hMul Real Real Real qz733 qz756 qz756)

noncomputable abbrev qz441 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz643 qz636) qz600)

noncomputable abbrev qz109 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz441))

noncomputable def Ns372p699 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz100) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz108) qz109) Bool.false 1969261939977 

noncomputable def Ns372p700 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz108) qz109 700129 262144 197 

noncomputable abbrev qz110 := (@Neg.neg Real Real.instNeg (Real.cos qz440))

noncomputable def Ns372p701 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz108) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz110)) Bool.true 700129 262144 197 4194304 (BSN.inv_eq_neg_inv_neg qz108) 

noncomputable def Ns372p702 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz110) Bool.false 89616512 33554432 1576 33554432 700129 262144 

noncomputable def Ns372p703 := @Enclosure.Real.IsNear.recentre' qz108 Bool.true 12563532 33554432 1271954432 193273528320000 3140883 8388608 1242143 188743680000 

noncomputable abbrev qz111 := qz440

noncomputable def Ns372p704 := @Enclosure.Real.IsNear.cos_image qz111 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 72622111) qz411) Bool.false 72622111 16777216 215 33554432 Bool.true 12563532 33554432 1 

noncomputable def Ns372p705 := nat_lit 91752656410606535972243979 

noncomputable def Ns372p706 := nat_lit 14411518807585587200000000000000 

noncomputable def Ns372p707 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz100 884279719003555 140737488355328 1 500000000000000 1444771 2097152 17 16777216 1277581693904485160905 295147905179352825856 Ns372p705 

noncomputable def Ns372p708 := @Enclosure.Real.IsNear.subLit_ff_p qz107 qz1 22416291 2097152 17 16777216 10 1 0 1 1444771 1444771 2097152 17 

noncomputable def Ns372p709 := @Ns372p708 16777216 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 358660656 33554432 34 33554432 22416291 2097152 17 16777216 (Ns372p695 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns372p710 := @Enclosure.Real.IsNear.recentre' qz111 Bool.false 1277581693904485160905 295147905179352825856 Ns372p705 Ns372p706 72622111 16777216 215 33554432 (@Ns372p707 Ns372p706 RS373to384.d47 (Ns372p709 rfl rfl) rfl) 

noncomputable def Ns372p711 := nat_lit 2870044237958004690911232 

noncomputable def Ns372p712 := nat_lit 1660721188849799667767739837213050730423808611090396003313531896023527746151833558896704321 

noncomputable def Ns372p713 := nat_lit 1960244697933081306077956057904680493055299652445595593633397240533428677866361266731841 

noncomputable def Ns372p714 := nat_lit 4978243077153532840691063599523342830285315233966296818753328893589516381099767954156649281 

noncomputable def Ns372p715 := BSN.cos_dyadic_bound_f 81571563383 68719476736 3 2 33554432 11531251 Ns372p712 Ns372p186 Ns372p713 Ns372p714 Ns372p189 Ns372p713 12563532 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 81571563383) qz379 0 2 Ns372p712 Ns372p186 Ns372p713 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 81571563383) qz380 0 2 Ns372p714 Ns372p189 Ns372p713 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p716 := @Ns372p704 5760000 (Ns372p710 rfl) (Enclosure.sfrac_false_div 72622111 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 72622111) qz411) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns372p711) qz412) 226375608064910080 72057594037927936 Bool.false 12563532 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q2 72622111 16777216 226375608064910080 72057594037927936 0 Ns372p711 Ns372p403 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 12563532 33554432 Ns372p711 Ns372p403 81571563383 68719476736 11531251 11520000 (Ns372p715 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p717 := @Enclosure.Real.IsNear.inv_image qz110 3140883 8388608 1242143 188743680000 44807468 44809044 16777216 (@Enclosure.Real.IsNear.neg qz108 Bool.true 3140883 8388608 1242143 188743680000 (Ns372p703 (Ns372p716 rfl rfl) rfl)) 

noncomputable def Ns372p718 := Ns372p701 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz110) Bool.false 700129 262144 197 4194304 (@Ns372p702 197 4194304 (Ns372p717 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p719 := @Enclosure.Real.IsNear.recentre' qz109 Bool.true 2812713 16777216 

noncomputable abbrev qz112 := (@HMul.hMul Real Real Real qz349 qz346 qz441)

noncomputable def Ns372p720 := @Enclosure.Real.IsNear.cos_image qz112 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 58359295)) qz367) Bool.true 58359295 33554432 

noncomputable def Ns372p721 := nat_lit 1076538981363827593451550725 

noncomputable def Ns372p722 := nat_lit 618970019642690137449562112 

noncomputable def Ns372p723 := nat_lit 18301704643957614678239753998824951 

noncomputable def Ns372p724 := @Enclosure.Real.IsNear.recentre' qz112 Bool.true Ns372p721 Ns372p722 Ns372p723 

noncomputable abbrev qz113 := qz441

noncomputable def Ns372p725 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz113 884279719003555 140737488355328 1 500000000000000 1217419056695 

noncomputable abbrev qz442 := (@HSub.hSub Real Real Real qz588 qz643 qz636)

noncomputable abbrev qz114 := qz442

noncomputable def Ns372p726 := @Enclosure.Real.IsNear.subLit_tf qz114 qz31 942541149751 4398046511104 678190673 281474976710656 1 16 

noncomputable abbrev qz443 := qz643

noncomputable abbrev qz115 := qz443

noncomputable def Ns372p727 := @Enclosure.Real.IsNear.subLit_ff_n qz115 qz100 2087363242441 4398046511104 392978001 281474976710656 1444771 2097152 17 16777216 

noncomputable def Ns372p728 := @Enclosure.Real.IsNear.mulLit_ff qz100 qz100 1444771 2097152 17 16777216 1444771 2097152 17 16777216 2087363242441 4398046511104 

noncomputable def Ns372p729 := nat_lit 374046724436562026161783751897383078428272288041390296482070301386042017113130489082799810276890625 

noncomputable def Ns372p730 := nat_lit 1560703635241529200449307071800578959799030390331180594458300359052496326300693933418212890625 

noncomputable def Ns372p731 := nat_lit 2261013770017917384335627422780647691666839513781473925720119078024679619269995752422355959934490625 

noncomputable def Ns372p732 := BSN.cos_dyadic_bound_t 58359295 33554432 4 3 16777216 5760000 Ns372p729 Ns372p329 Ns372p730 Ns372p731 Ns372p332 Ns372p730 2812713 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 58359295) (BSN.cosEvenQ 33554432) 0 3 Ns372p729 Ns372p329 Ns372p730 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 58359295) (BSN.cosOddQ 33554432) 0 3 Ns372p731 Ns372p332 Ns372p730 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p733 := @Ns372p719 2965394432 193273528320000 2812713 16777216 2895893 188743680000 (@Ns372p720 509 33554432 Bool.true 2812713 16777216 1 5760000 (@Ns372p724 Ns372p200 58359295 33554432 509 33554432 (@Ns372p725 4398046511104 678190673 281474976710656 Ns372p721 Ns372p722 Ns372p723 Ns372p200 RS373to384.d47 (@Ns372p726 0 1 19478704907120 1217419056695 4398046511104 678190673 281474976710656 (@Ns372p727 1976652057282609152 942541149751 4398046511104 678190673 281474976710656 (@Ns372p728 392978001 281474976710656 (Ns372p709 rfl rfl) (Ns372p709 rfl rfl) rfl) (Ns372p709 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 58359295 33554432) (BSN.cos_neg_of_bound 58359295 33554432 Bool.true 2812713 16777216 1 5760000 (Ns372p732 rfl rfl)) rfl rfl) 

noncomputable def Ns372p734 := @Ns372p693 66271744368188855923 Ns372p619 (Ns372p694 qz33 (@Enclosure.Real.IsNear.of_eq qz641 (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 2565801 8388608 1 16777216 (BSN.rpow_neg_quarter_mk qz99 (BSN.t_div_two_pi_nonneg qz98 717873 1000 qz101)) Ns372p698) rfl) (@Ns372p699 4398046511104 12891408133441 263882790666240000 (BSN.correction_mk qz100 (BSN.cos_two_pi_p_ne_zero_mk qz98 717873 1000 10 qz101 rfl rfl (@BSN.floor_sqrt_eq_dec qz98 717873 1000 10 qz101 rfl rfl rfl))) (@Ns372p700 4194304 2812713 16777216 2895893 188743680000 1969261939977 4398046511104 12891408133441 263882790666240000 Ns372p718 (Ns372p733 rfl) rfl)) 

noncomputable def Ns372p735 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (hardyZApproximantRS₀ qz98) Bool.true 53077258933070164209 36893488147419103232 5001803519594208695923 Ns372p619 (@Eq.refl Real (hardyZApproximantRS₀ qz98)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) (@HMul.hMul Real Real Real qz5 qz637 (Zeta.RiemannSiegel.correction qz100))) Bool.true 53077258933070164209 36893488147419103232 5001803519594208695923 Ns372p619 (BSN.hardyZApproximantRS₀_eq qz98 10 (@BSN.floor_sqrt_eq_dec qz98 717873 1000 10 qz101 rfl rfl rfl)) (@Ns372p621 53077258933070164209 36893488147419103232 5001803519594208695923 Ns372p619 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 10)) Bool.true 174712203 134217728 37407 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) (Ns372p692 (Ns372p691 rfl rfl rfl rfl) rfl rfl)) (Ns372p734 rfl) rfl rfl)) 

theorem RS373to384.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz98) Bool.true 53077258933070164209 36893488147419103232 5001803519594208695923 Ns372p619 := Ns372p735 

noncomputable def Ns372p736 := nat_lit 144831789451836267511039393792 

noncomputable abbrev qz758 := (Enclosure.sfrac Bool.false 719198 1000)

noncomputable abbrev qz644 := qz758

noncomputable abbrev qz444 := qz644

noncomputable abbrev qz116 := qz444

noncomputable abbrev qz759 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 719198 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz645 := qz759

noncomputable abbrev qz445 := qz645

noncomputable abbrev qz117 := qz445

noncomputable abbrev qz760 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 719198 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz646 := qz760

noncomputable abbrev qz446 := qz646

noncomputable abbrev qz118 := qz446

noncomputable abbrev qz647 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz117 qz9))

noncomputable def Ns372p737 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) (@HMul.hMul Real Real Real qz5 qz647 (Zeta.RiemannSiegel.correction qz118)) 70674597 67108864 18739 16777216 328479477461032897151 2361183241434822606848 81368857439367209599 Ns372p619 Ns372p736 

noncomputable def Ns372p738 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos BSN.quadSignNeg 9 10 719198 1000 198 268435456 134217728 4503599627370496 Bool.false 360938570450 2499 618095470 48 84886744 8 

noncomputable def Ns372p739 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 719198 1000 96 150 268435456 134217728 4503599627370496 Bool.false 360938570450 2499 

noncomputable def Ns372p740 := Ns372p739 558195838 48 94906264 8 589812974 48 89478488 8 Bool.false 215060081 112747 Bool.true 35646734 Bool.true 5126584 14148475504056880 1 Bool.false 266072088 Bool.false Bool.false 268386503 Bool.true Bool.false 219668597 

noncomputable def Ns372p741 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 719198 1000 35 34 268435456 134217728 4503599627370496 Bool.false 360938570450 2499 

noncomputable def Ns372p742 := Ns372p741 480971758 48 109588312 8 522351262 48 101459064 8 Bool.false 131775092 83621 Bool.false 266634050 Bool.true 399059916 14148475504056880 1 Bool.false 224902264 Bool.false Bool.false 22570831 Bool.true Bool.false 215060081 

noncomputable def Ns372p743 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 719198 1000 221 119 268435456 134217728 4503599627370496 Bool.false 360938570450 2499 

noncomputable def Ns372p744 := Ns372p743 372130544 47 134217720 8 432030192 47 120047984 16 Bool.false 167811210 49208 Bool.false 116735819 Bool.false 46086460 14148475504056880 1 Bool.false 113091017 Bool.true Bool.false 45860386 Bool.false Bool.false 131775092 

noncomputable def Ns372p745 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 719198 1000 538 352 268435456 134217728 4503599627370496 Bool.false 360938570450 2499 

noncomputable def Ns372p746 := Ns372p745 186065264 47 189812528 16 294906480 47 154981288 8 Bool.false 268435384 2551 Bool.false 269108304 Bool.false 419005097 14148475504056880 1 Bool.false 144469658 Bool.true Bool.false 2652288 Bool.false Bool.false 167811210 

noncomputable def Ns372p747 := nat_lit 14730490016375038653978597883769557644615207686831506999 

noncomputable def Ns372p748 := nat_lit 10955287487597961624569245859431787431154059051008000 

noncomputable def Ns372p749 := nat_lit 92360042519570528525728609264640000 

noncomputable def Ns372p750 := nat_lit 398551037054784014783553934082439352320 

noncomputable abbrev qz648 := (@Eq.refl Real qz758)

noncomputable abbrev qz447 := qz648

noncomputable abbrev qz119 := qz447

noncomputable def Ns372p751 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz116 719198 1000 2068984052816 16000000 1438396 4000 2000 Ns372p749 Ns372p750 qz119 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns372p752 := nat_lit 301680435535360791633481684659600540561719453426309263339520 

noncomputable abbrev qz649 := (@HSub.hSub Real Real Real qz737 qz738 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz739 (@Nat.cast Real Real.instNatCast 1438396))))

noncomputable abbrev qz448 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 719198 4000) (Real.log (Enclosure.sfrac Bool.false 2068984052816 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz649))

noncomputable abbrev qz650 := (Enclosure.sfrac Bool.false 719198 2000)

noncomputable abbrev qz120 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz448 qz650) (@HMul.hMul Real Real Real qz349 qz650 (Real.log Real.pi)))

noncomputable def Ns372p753 := @Enclosure.Real.IsNear.addLit_ft_p qz120 (Enclosure.sfrac Bool.true Ns372p749 Ns372p750) 756943175355416375211 562949953421312000 171486668212881019 18432000000000000000000 Ns372p749 Ns372p750 0 1 Ns372p752 

noncomputable def Ns372p754 := nat_lit 5079759661065478918740797030400 

noncomputable abbrev qz121 := (@HSub.hSub Real Real Real qz353 qz448 qz650)

noncomputable def Ns372p755 := @Enclosure.Real.IsNear.subLit_ff_p qz121 (@HMul.hMul Real Real Real qz5 qz650 (Real.log Real.pi)) 197735597784773832687 112589990684262400 35507740736003 9000000000000000000 13812471244839 33554432000 359599 67108864000 Ns372p754 756943175355416375211 562949953421312000 

noncomputable def Ns372p756 := nat_lit 1977355977847738326870000 

noncomputable abbrev qz122 := qz448

noncomputable def Ns372p757 := @Enclosure.Real.IsNear.subLit_ff_p qz122 qz650 1191114229224219537323 562949953421312000 35507740736003 9000000000000000000 719198 2000 0 1 Ns372p756 197735597784773832687 112589990684262400 35507740736003 9000000000000000000 

noncomputable def Ns372p758 := nat_lit 2682150799444945332562315910110511104 

noncomputable def Ns372p759 := nat_lit 56916128556896096111034368 

noncomputable def Ns372p760 := nat_lit 2743754649196736121291550657005345538474159504184768244556047431432118661360220548497257633235735292790385285691088042970707920301187351932619518503926294717203959311051068618605377182448027696709564681420800 

noncomputable def Ns372p761 := nat_lit 104805163443558995046669116059913227489974272463951032874758112850516834574488568736566055694088710230158522356153216106576985462066987369496724520168573553182656888685761601239485339378933876855887762554880 

noncomputable def Ns372p762 := nat_lit 2800535884321643913062987496669156748441427619498276609535540712395126996237560536347388444339444324035774446809024399856956172760451603209569039493734485275718155003471762874971008605755604887142400 

noncomputable def Ns372p763 := BSN.log_dyadic_bound 1020408052816 3117560052816 9 8 Ns372p760 134217728 46080000 Ns372p761 Ns372p762 91217674 4137968105632 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1020408052816) (BSN.artanhQ 3117560052816) 0 8 Ns372p761 Ns372p760 Ns372p762 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz449 := (Real.log (Enclosure.sfrac Bool.false 2068984052816 16000000))

noncomputable def Ns372p764 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 719198 4000) qz449 719198 4000 0 1 3312954711547127 281474976710656 48828161 2250000000000000 1191335201317635322073 562949953421312000 17558557867439 4500000000000000000 (Enclosure.Real.IsNear.const Bool.false 719198 4000) (BSN.isNear_log_sfrac 2068984052816 16000000 3312954711547127 281474976710656 48828161 2250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2068984052816) qz356)) Bool.false Ns372p759 Ns372p98 1000000737280000 46080000000000000000000 3312954711547127 281474976710656 48828161 2250000000000000 (BSN.log_rat_reduce_isNear 2068984052816 16000000 16 4137968105632 2097152000000 91217674 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns372p763 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p765 := BSN.arctan_dyadic_bound_f 1000 1438396 1 0 16777216 5760000 0 1 1 0 1 1 11663 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1438396) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1438396) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns372p766 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1438396))) 884279719003555 562949953421312 1 2000000000000000 11663 16777216 1 5760000 14829186164835194241024 883888373663139 562949953421312 3125000009 18000000000000000 qz17 (Ns372p765 rfl) rfl rfl 

noncomputable abbrev qz450 := (@HMul.hMul Real Real Real qz584 qz589 qz649)

noncomputable abbrev qz123 := qz450

noncomputable abbrev qz451 := qz649

noncomputable abbrev qz124 := qz451

noncomputable def Ns372p767 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 719198 4000) qz449) qz123 1191335201317635322073 562949953421312000 17558557867439 4500000000000000000 883888373663139 2251799813685248 3125000009 72000000000000000 Ns372p758 1191114229224219537323 562949953421312000 35507740736003 9000000000000000000 (Ns372p764 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz124 1 4 0 1 883888373663139 562949953421312 3125000009 18000000000000000 883888373663139 2251799813685248 3125000009 72000000000000000 qz363 Ns372p766 rfl) 

noncomputable def Ns372p768 := @Ns372p753 Ns372p747 Ns372p748 171486668212881019 18432000000000000000000 (@Ns372p755 171486668212881019 18432000000000000000000 (Ns372p757 (Ns372p767 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 719198 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz650 (Real.log Real.pi) 719198 2000 0 1 38410761 33554432 1 67108864 13812471244839 33554432000 359599 67108864000 (Enclosure.Real.IsNear.const Bool.false 719198 2000) RS373to384.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns372p749 Ns372p750) 

noncomputable def Ns372p769 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns372p747 Ns372p748 171486668212881019 18432000000000000000000 22558660653 16777216 313 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz364 qz120 (Enclosure.sfrac Bool.true Ns372p749 Ns372p750)) Bool.false Ns372p747 Ns372p748 171486668212881019 18432000000000000000000 Ns372p751 (Ns372p768 rfl rfl)) 

noncomputable def Ns372p770 := nat_lit 3796257787435278995030016 

noncomputable def Ns372p771 := nat_lit 3504560823775581510198263123967775463277141373190713428198546622430039837563467484813525275524506759613479255742029103388038615923121434801 

noncomputable def Ns372p772 := nat_lit 2489262468865144189452214247215607532511860599675086406548042645400963865464539102852372917850531467202551852577266035199016027009201 

noncomputable def Ns372p773 := nat_lit 17501068649911639751787247993210849828697544946733136235781605262125207191989561926935407919968713591539756235844414459186307758845822480561 

noncomputable def Ns372p774 := BSN.sin_dyadic_bound_f 107896135757 68719476736 4 3 33554432 11531251 Ns372p771 Ns372p111 Ns372p772 Ns372p773 Ns372p114 Ns372p772 33554423 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107896135757) qz365 0 3 Ns372p771 Ns372p111 Ns372p772 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107896135757) qz366 0 3 Ns372p773 Ns372p114 Ns372p772 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p775 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz116) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 22558660653) qz411) Bool.false 22558660653 16777216 313 33554432 Bool.false 33554423 33554432 1 5760000 (Ns372p769 rfl) (Enclosure.sfrac_false_div 22558660653 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 22558660653) qz411) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns372p770) qz412) 226375608064910080 72057594037927936 Bool.false 33554423 33554432 213 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 22558660653 16777216 226375608064910080 72057594037927936 213 Ns372p770 Ns372p403 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554423 33554432 Ns372p770 Ns372p403 107896135757 68719476736 11531251 11520000 (Ns372p774 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p776 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns372p747 Ns372p748 171486668212881019 18432000000000000000000 360938570450 268435456 2499 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz364 qz120 (Enclosure.sfrac Bool.true Ns372p749 Ns372p750)) Bool.false Ns372p747 Ns372p748 171486668212881019 18432000000000000000000 Ns372p751 (Ns372p768 rfl rfl)) 

noncomputable def Ns372p777 := Ns372p746 49208 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 538 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 144469658 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 352 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 2652288 268435456) qz119 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) Bool.false 33554423 33554432 1793393 188743680000 268435384 268435456 2551 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 33554423 33554432 1793393 188743680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz116) qz116) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 33554423 33554432 1836434432 193273528320000 33554423 33554432 1793393 188743680000 (Ns372p775 rfl rfl) rfl)) rfl) (Ns372p776 rfl) RS373to384.d7 

noncomputable def Ns372p778 := nat_lit 2823671704471743146922019155212717413654945219531964959205811761512330545366308610288211428722560450267447296 

noncomputable def Ns372p779 := nat_lit 144253111773919594553662217375535640158573289377188370021227464435538420765768675788606134223808495616 

noncomputable def Ns372p780 := nat_lit 17123412261882385013050222897452176383278182336758416776650074032425372103098093688194976192917056198404997120 

noncomputable def Ns372p781 := BSN.cos_dyadic_bound_f 269108304 268435456 4 3 268435456 134217728 Ns372p778 Ns372p143 Ns372p779 Ns372p780 Ns372p146 Ns372p779 144469658 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 269108304) qz371 0 3 Ns372p778 Ns372p143 Ns372p779 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 269108304) qz372 0 3 Ns372p780 Ns372p146 Ns372p779 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p782 := nat_lit 16643881903733395361194112013520317743990069443195910430331241046516675726143644348783891246931892011541402721 

noncomputable def Ns372p783 := nat_lit 29284085881478727162189803836000648130877965726970778213574284935989418549076336862400098362940539475041 

noncomputable def Ns372p784 := nat_lit 100735712838939832360460364519457558459692227454323313706238382544052332137043119969008498923194500045689525345 

noncomputable def Ns372p785 := BSN.cos_dyadic_bound_f 419005097 268435456 4 3 268435456 134217728 Ns372p782 Ns372p143 Ns372p783 Ns372p784 Ns372p146 Ns372p783 2652288 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 419005097) qz371 0 3 Ns372p782 Ns372p143 Ns372p783 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 419005097) qz372 0 3 Ns372p784 Ns372p146 Ns372p783 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p786 := nat_lit 185701981743592007370448027779121 

noncomputable def Ns372p787 := BSN.sin_dyadic_bound_f 116735819 268435456 2 1 268435456 134217728 Ns372p786 Ns372p130 Ns372p786 Ns372p786 Ns372p131 Ns372p786 113091017 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 116735819) qz369 0 1 Ns372p786 Ns372p130 Ns372p786 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 116735819) qz370 0 1 Ns372p786 Ns372p131 Ns372p786 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p788 := nat_lit 4511213708028233487553958560000 

noncomputable def Ns372p789 := BSN.sin_dyadic_bound_f 46086460 268435456 2 1 268435456 134217728 Ns372p788 Ns372p130 Ns372p788 Ns372p788 Ns372p131 Ns372p788 45860386 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 46086460) qz369 0 1 Ns372p788 Ns372p130 Ns372p788 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 46086460) qz370 0 1 Ns372p788 Ns372p131 Ns372p788 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p790 := Ns372p744 83621 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 221 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 113091017 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 119 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 45860386 268435456) qz119 rfl rfl (Ns372p777 RS373to384.d9 RS373to384.d11 RS373to384.d13 RS373to384.d17 (Ns372p781 rfl rfl) (Ns372p785 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns372p776 rfl) RS373to384.d19 RS373to384.d21 RS373to384.d23 RS373to384.d25 RS373to384.d17 (Ns372p787 rfl rfl) (Ns372p789 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns372p791 := nat_lit 79385926122521356826345540246342904516253417757375832546283804900000000 

noncomputable def Ns372p792 := nat_lit 25546115714416461161251011973600028392885359267842212539062500000000 

noncomputable def Ns372p793 := nat_lit 207874160419256403131882008530559873687075232116217340705680054500000000 

noncomputable def Ns372p794 := BSN.sin_dyadic_bound_f 266634050 268435456 3 2 268435456 134217728 Ns372p791 Ns372p120 Ns372p792 Ns372p793 Ns372p123 Ns372p792 224902264 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 266634050) qz369 0 2 Ns372p791 Ns372p120 Ns372p792 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 266634050) qz370 0 2 Ns372p793 Ns372p123 Ns372p792 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p795 := nat_lit 13685430716619383600414763860819277724248324193742698659233077665578888003645668148178290260110532187768487936 

noncomputable def Ns372p796 := nat_lit 16310124705140140870891847563237419208206952015635196408554677059606395915414066673357631881170131091456 

noncomputable def Ns372p797 := nat_lit 82864413723491623867366286445704310639180245904228246059381642175372288665736253795338517900181583479124787200 

noncomputable def Ns372p798 := BSN.cos_dyadic_bound_f 399059916 268435456 4 3 268435456 134217728 Ns372p795 Ns372p143 Ns372p796 Ns372p797 Ns372p146 Ns372p796 22570831 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 399059916) qz371 0 3 Ns372p795 Ns372p143 Ns372p796 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 399059916) qz372 0 3 Ns372p797 Ns372p146 Ns372p796 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p799 := Ns372p742 112747 BSN.abs_quadSignPos (BSN.cos_quad_nat3 35 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 224902264 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 34 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 22570831 268435456) qz119 rfl rfl (Ns372p790 rfl rfl) (Ns372p776 rfl) RS373to384.d27 RS373to384.d29 RS373to384.d31 RS373to384.d33 RS373to384.d17 (Ns372p794 rfl rfl) (Ns372p798 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p800 := nat_lit 1614652173571602482900993963536 

noncomputable def Ns372p801 := BSN.cos_dyadic_bound_f 35646734 268435456 2 1 268435456 134217728 Ns372p800 Ns372p427 Ns372p800 Ns372p800 Ns372p428 Ns372p800 266072088 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 35646734) qz371 0 1 Ns372p800 Ns372p427 Ns372p800 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 35646734) qz372 0 1 Ns372p800 Ns372p428 Ns372p800 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p802 := nat_lit 690736349508649361794011136 

noncomputable def Ns372p803 := BSN.cos_dyadic_bound_f 5126584 268435456 2 1 268435456 134217728 Ns372p802 Ns372p427 Ns372p802 Ns372p802 Ns372p428 Ns372p802 268386503 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 5126584) qz371 0 1 Ns372p802 Ns372p427 Ns372p802 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 5126584) qz372 0 1 Ns372p802 Ns372p428 Ns372p802 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p804 := Ns372p740 138195 BSN.abs_quadSignPos (BSN.cos_quad_nat0 96 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266072088 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 150 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268386503 268435456) qz119 rfl rfl (Ns372p799 rfl) (Ns372p776 rfl) RS373to384.d35 RS373to384.d37 RS373to384.d39 RS373to384.d41 RS373to384.d17 (Ns372p801 rfl rfl) (Ns372p803 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p805 := nat_lit 1113156662904868819211160050240292473041858905206709416024208524206336 

noncomputable def Ns372p806 := nat_lit 16284044544761549991924250317360742736215667854385079379531161856 

noncomputable def Ns372p807 := nat_lit 3339437420625516934533496302220242697640104284284419477913866510295296 

noncomputable def Ns372p808 := BSN.cos_dyadic_bound_f 106284586 268435456 3 2 268435456 134217728 Ns372p805 Ns372p159 Ns372p806 Ns372p807 Ns372p162 Ns372p806 247667698 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 106284586) qz371 0 2 Ns372p805 Ns372p159 Ns372p806 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 106284586) qz372 0 2 Ns372p807 Ns372p162 Ns372p806 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p809 := Ns372p738 Bool.false 219668597 138195 Bool.true 106284586 14148475504056880 1 Bool.false 247667698 Bool.true Bool.false 141349194 149912 BSN.abs_quadSignNeg qz595 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 247667698 268435456) qz119 rfl (Ns372p804 rfl) (Ns372p776 rfl) RS373to384.d43 RS373to384.d45 RS373to384.d17 (Ns372p808 rfl rfl) rfl 

noncomputable def Ns372p810 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) 141349194 268435456 149912 268435456 141349194 268435456 149912 268435456 75886270693244928 70674597 67108864 18739 16777216 (Ns372p809 rfl rfl rfl rfl) 

noncomputable def Ns372p811 := @Enclosure.Real.IsNear.mulLit_ff qz647 (Zeta.RiemannSiegel.correction qz118) 5129237 16777216 1 16777216 64040612173123 140737488355328 47520965857819 791648371998720000 328479477461032897151 2361183241434822606848 

noncomputable abbrev qz651 := (@HPow.hPow Real Real Real qz7 qz117 qz9)

noncomputable def Ns372p812 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz651 1 1 0 1 5129237 16777216 1 16777216 5129237 16777216 1 16777216 

noncomputable def Ns372p813 := @Enclosure.Real.IsNear.sqrt_image qz117 1920385598447 16777216000 359599 16777216000 179495732 179495767 16777216 (@Enclosure.Real.IsNear.of_eq qz117 (@HMul.hMul Real Real Real qz5 qz116 qz3) Bool.false 1920385598447 16777216000 359599 16777216000 (BSN.t_div_two_pi_mk qz116 719198 1000 qz119) (@Enclosure.Real.IsNear.mulLit_ff qz116 qz3 719198 1000 0 1 5340353 33554432 1 33554432 1920385598447 16777216000 359599 16777216000 (Enclosure.Real.IsNear.const Bool.false 719198 1000) RS373to384.d48 rfl)) 

noncomputable abbrev qz761 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 719198 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz652 := qz761

noncomputable abbrev qz452 := qz652

noncomputable abbrev qz125 := qz452

noncomputable def Ns372p814 := @Enclosure.Real.IsNear.sqrt_image qz125 358991499 33554432 35 33554432 54876576 54876583 16777216 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 358991499 33554432 35 33554432 358991499 33554432 35 33554432 (Ns372p813 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns372p815 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz125) 109753159 33554432 7 33554432 5129236 5129238 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz125) Bool.false 109753159 33554432 7 33554432 109753159 33554432 7 33554432 (Ns372p814 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns372p816 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 10258474 33554432 2 33554432 5129237 16777216 1 16777216 (Ns372p815 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz453 := (@HMul.hMul Real Real Real qz584 qz582 qz646)

noncomputable abbrev qz126 := (Real.cos qz453)

noncomputable abbrev qz653 := (@HMul.hMul Real Real Real qz733 qz760 qz760)

noncomputable abbrev qz454 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz653 qz646) qz600)

noncomputable abbrev qz127 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz454))

noncomputable def Ns372p817 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz118) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz126) qz127) Bool.false 64040612173123 

noncomputable def Ns372p818 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz126) qz127 26521399 8388608 567 

noncomputable abbrev qz128 := (@Neg.neg Real Real.instNeg (Real.cos qz453))

noncomputable def Ns372p819 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz126) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz128)) Bool.true 26521399 8388608 567 8388608 (BSN.inv_eq_neg_inv_neg qz126) 

noncomputable def Ns372p820 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz128) Bool.false 106085596 33554432 2268 33554432 26521399 8388608 

noncomputable def Ns372p821 := @Enclosure.Real.IsNear.recentre' qz126 Bool.true 10613127 33554432 1306514432 193273528320000 10613127 33554432 1275893 188743680000 

noncomputable abbrev qz129 := qz453

noncomputable def Ns372p822 := @Enclosure.Real.IsNear.cos_image qz129 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 73661485) qz411) Bool.false 73661485 16777216 221 33554432 Bool.true 10613127 33554432 1 

noncomputable def Ns372p823 := nat_lit 944512639517951324907829813 

noncomputable def Ns372p824 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz118 884279719003555 140737488355328 1 500000000000000 23447179 33554432 35 33554432 20733864857546055721345 4722366482869645213696 Ns372p823 

noncomputable def Ns372p825 := @Enclosure.Real.IsNear.subLit_ff_p qz125 qz1 358991499 33554432 35 33554432 10 1 0 1 23447179 23447179 33554432 35 

noncomputable def Ns372p826 := @Ns372p825 33554432 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 358991499 33554432 35 33554432 358991499 33554432 35 33554432 (Ns372p813 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns372p827 := @Enclosure.Real.IsNear.recentre' qz129 Bool.false 20733864857546055721345 4722366482869645213696 Ns372p823 Ns372p586 73661485 16777216 221 33554432 (@Ns372p824 Ns372p586 RS373to384.d47 (Ns372p826 rfl rfl) rfl) 

noncomputable def Ns372p828 := nat_lit 3019833817449159312015360 

noncomputable def Ns372p829 := nat_lit 539418900552171800727773961995289246643393394036611064975216450752070696064163505788268617743951510964763411568057246831630519825300123361 

noncomputable def Ns372p830 := nat_lit 5312452879021523644167342878668926891519915429617346963252719967526930359331948649748578417931730498127901383505799396607174191825394073600 

noncomputable def Ns372p831 := nat_lit 159808130945286225240416951515265669935832909732896013347378396664062577759903563805123061446539030032325364404746645756161962733281 

noncomputable def Ns372p832 := nat_lit 3269318408724185215802201590768717969364824814618999087494080206319984046334271734915695577910198019308048170170220953886935564245230087905 

noncomputable def Ns372p833 := nat_lit 483433211990958651619228201958872347128312304095178573655997517044950662699207327127120636031787475329639025899027745091252851456110860697600 

noncomputable def Ns372p834 := BSN.cos_dyadic_bound_f 85828839287 68719476736 4 3 33554432 11531251 Ns372p829 Ns372p830 Ns372p831 Ns372p832 Ns372p833 Ns372p831 10613127 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 85828839287) qz379 0 3 Ns372p829 Ns372p830 Ns372p831 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 85828839287) qz380 0 3 Ns372p832 Ns372p833 Ns372p831 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p835 := @Ns372p822 5760000 (Ns372p827 rfl) (Enclosure.sfrac_false_div 73661485 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 73661485) qz411) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns372p828) qz412) 226375608064910080 72057594037927936 Bool.false 10613127 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q2 73661485 16777216 226375608064910080 72057594037927936 0 Ns372p828 Ns372p403 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 10613127 33554432 Ns372p828 Ns372p403 85828839287 68719476736 11531251 11520000 (Ns372p834 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p836 := @Enclosure.Real.IsNear.inv_image qz128 10613127 33554432 1275893 188743680000 53041664 53043932 16777216 (@Enclosure.Real.IsNear.neg qz126 Bool.true 10613127 33554432 1275893 188743680000 (Ns372p821 (Ns372p835 rfl rfl) rfl)) 

noncomputable def Ns372p837 := Ns372p819 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz128) Bool.false 26521399 8388608 567 8388608 (@Ns372p820 567 8388608 (Ns372p836 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p838 := @Enclosure.Real.IsNear.recentre' qz127 Bool.true 2414677 16777216 

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz349 qz346 qz454)

noncomputable def Ns372p839 := @Enclosure.Real.IsNear.cos_image qz130 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 28776681)) qz411) Bool.true 28776681 16777216 

noncomputable def Ns372p840 := nat_lit 271788071111084713209699010805 

noncomputable def Ns372p841 := nat_lit 75984932033304736101797375442151117 

noncomputable def Ns372p842 := @Enclosure.Real.IsNear.recentre' qz130 Bool.true Ns372p840 Ns372p602 Ns372p841 

noncomputable abbrev qz131 := qz454

noncomputable def Ns372p843 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz131 884279719003555 140737488355328 1 500000000000000 307355314466951 

noncomputable abbrev qz455 := (@HSub.hSub Real Real Real qz588 qz653 qz646)

noncomputable abbrev qz132 := qz455

noncomputable def Ns372p844 := @Enclosure.Real.IsNear.subLit_tf qz132 qz31 236986570289287 1125899906842624 2815708875 1125899906842624 1 16 

noncomputable abbrev qz456 := qz653

noncomputable abbrev qz133 := qz456

noncomputable def Ns372p845 := @Enclosure.Real.IsNear.subLit_ff_n qz133 qz118 549770203058041 1125899906842624 1641303755 1125899906842624 23447179 33554432 35 33554432 

noncomputable def Ns372p846 := @Enclosure.Real.IsNear.mulLit_ff qz118 qz118 23447179 33554432 35 33554432 23447179 33554432 35 33554432 549770203058041 1125899906842624 

noncomputable def Ns372p847 := nat_lit 86353720376726938402671151231304941910071897600712025533660903558630690029543179500213756159841 

noncomputable def Ns372p848 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600 

noncomputable def Ns372p849 := nat_lit 322469341017541812693595275057068553622945553984054995791436313932710667374700882257438561 

noncomputable def Ns372p850 := nat_lit 522087489809898415200341481246703327494923223810820013210661055329091508319573969747895434798945 

noncomputable def Ns372p851 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600 

noncomputable def Ns372p852 := BSN.cos_dyadic_bound_t 28776681 16777216 4 3 16777216 5760000 Ns372p847 Ns372p848 Ns372p849 Ns372p850 Ns372p851 Ns372p849 2414677 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 28776681) (BSN.cosEvenQ 16777216) 0 3 Ns372p847 Ns372p848 Ns372p849 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 28776681) (BSN.cosOddQ 16777216) 0 3 Ns372p850 Ns372p851 Ns372p849 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p853 := @Ns372p838 192177152 12079595520000 2414677 16777216 187673 11796480000 (@Ns372p839 33 2097152 Bool.true 2414677 16777216 1 5760000 (@Ns372p842 Ns372p605 28776681 16777216 33 2097152 (@Ns372p843 1125899906842624 2815708875 1125899906842624 Ns372p840 Ns372p602 Ns372p841 Ns372p605 RS373to384.d47 (@Ns372p844 0 1 4917685031471216 307355314466951 1125899906842624 2815708875 1125899906842624 (@Ns372p845 7951949757685100969984 236986570289287 1125899906842624 2815708875 1125899906842624 (@Ns372p846 1641303755 1125899906842624 (Ns372p826 rfl rfl) (Ns372p826 rfl rfl) rfl) (Ns372p826 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 28776681 16777216) (BSN.cos_neg_of_bound 28776681 16777216 Bool.true 2414677 16777216 1 5760000 (Ns372p852 rfl rfl)) rfl rfl) 

noncomputable def Ns372p854 := @Ns372p811 81368857439367209599 Ns372p619 (Ns372p812 qz33 (@Enclosure.Real.IsNear.of_eq qz651 (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 5129237 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz117 (BSN.t_div_two_pi_nonneg qz116 719198 1000 qz119)) Ns372p816) rfl) (@Ns372p817 140737488355328 47520965857819 791648371998720000 (BSN.correction_mk qz118 (BSN.cos_two_pi_p_ne_zero_mk qz116 719198 1000 10 qz119 rfl rfl (@BSN.floor_sqrt_eq_dec qz116 719198 1000 10 qz119 rfl rfl rfl))) (@Ns372p818 8388608 2414677 16777216 187673 11796480000 64040612173123 140737488355328 47520965857819 791648371998720000 Ns372p837 (Ns372p853 rfl) rfl)) 

noncomputable def Ns372p855 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (hardyZApproximantRS₀ qz116) Bool.false 2158161840615216903553 2361183241434822606848 5026268471734038569599 Ns372p619 (@Eq.refl Real (hardyZApproximantRS₀ qz116)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) (@HMul.hMul Real Real Real qz5 qz647 (Zeta.RiemannSiegel.correction qz118))) Bool.false 2158161840615216903553 2361183241434822606848 5026268471734038569599 Ns372p619 (BSN.hardyZApproximantRS₀_eq qz116 10 (@BSN.floor_sqrt_eq_dec qz116 719198 1000 10 qz119 rfl rfl rfl)) (@Ns372p737 2158161840615216903553 2361183241434822606848 5026268471734038569599 Ns372p619 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 10)) Bool.false 70674597 67108864 18739 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) (Ns372p810 (Ns372p809 rfl rfl rfl rfl) rfl rfl)) (Ns372p854 rfl) rfl rfl)) 

theorem RS373to384.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz116) Bool.false 2158161840615216903553 2361183241434822606848 5026268471734038569599 Ns372p619 := Ns372p855 

noncomputable def Ns372p856 := nat_lit 26563311466141754327040000 

noncomputable def Ns372p857 := nat_lit 1434646527971677214287685746688 

noncomputable abbrev qz762 := (Enclosure.sfrac Bool.false 720524 1000)

noncomputable abbrev qz654 := qz762

noncomputable abbrev qz457 := qz654

noncomputable abbrev qz134 := qz457

noncomputable abbrev qz763 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 720524 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz655 := qz763

noncomputable abbrev qz458 := qz655

noncomputable abbrev qz135 := qz458

noncomputable abbrev qz764 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 720524 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz656 := qz764

noncomputable abbrev qz459 := qz656

noncomputable abbrev qz136 := qz459

noncomputable abbrev qz657 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz135 qz9))

noncomputable def Ns372p858 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) (@HMul.hMul Real Real Real qz5 qz657 (Zeta.RiemannSiegel.correction qz136)) 284818739 134217728 75095 67108864 667781093901990079473 4722366482869645213696 589748899236324034427 Ns372p856 Ns372p857 

noncomputable def Ns372p859 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos BSN.quadSignNeg 9 10 720524 1000 198 268435456 134217728 4503599627370496 Bool.false 361782371247 2503 618095470 48 84886744 8 

noncomputable def Ns372p860 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 720524 1000 95 149 268435456 134217728 4503599627370496 Bool.false 361782371247 2503 

noncomputable def Ns372p861 := Ns372p860 558195838 48 94906264 8 589812974 48 89478488 8 Bool.true 208249875 112956 Bool.true 353671046 Bool.true 365075219 14148475504056880 1 Bool.false 259871956 Bool.false Bool.false 262494157 Bool.true Bool.true 203869321 

noncomputable def Ns372p862 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 720524 1000 36 34 268435456 134217728 4503599627370496 Bool.false 361782371247 2503 

noncomputable def Ns372p863 := Ns372p862 480971758 48 109588312 8 522351262 48 101459064 8 Bool.true 254681561 83777 Bool.false 51008868 Bool.true 247896893 14148475504056880 1 Bool.false 263603596 Bool.false Bool.false 161877721 Bool.true Bool.true 208249875 

noncomputable def Ns372p864 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 720524 1000 222 119 268435456 134217728 4503599627370496 Bool.false 361782371247 2503 

noncomputable def Ns372p865 := Ns372p864 372130544 47 134217720 8 432030192 47 120047984 16 Bool.true 233423307 49301 Bool.false 45434086 Bool.false 317015222 14148475504056880 1 Bool.false 264599649 Bool.true Bool.false 248296486 Bool.false Bool.true 254681561 

noncomputable def Ns372p866 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 720524 1000 540 354 268435456 134217728 4503599627370496 Bool.false 361782371247 2503 

noncomputable def Ns372p867 := Ns372p866 186065264 47 189812528 16 294906480 47 154981288 8 Bool.true 268435288 2559 Bool.false 22871704 Bool.false 28445045 14148475504056880 1 Bool.false 267461668 Bool.false Bool.false 266929761 Bool.true Bool.true 233423307 

noncomputable def Ns372p868 := nat_lit 7289558549150151242209519477765774773365505475031063 

noncomputable def Ns372p869 := nat_lit 5408710121595354941643550869477580116080984064000 

noncomputable def Ns372p870 := nat_lit 93214617950222544810822177259520000 

noncomputable def Ns372p871 := nat_lit 402980306863438706222441112211166330880 

noncomputable abbrev qz658 := (@Eq.refl Real qz762)

noncomputable abbrev qz460 := qz658

noncomputable abbrev qz137 := qz460

noncomputable def Ns372p872 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz134 720524 1000 2076620338304 16000000 1441048 4000 2000 Ns372p870 Ns372p871 qz137 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns372p873 := nat_lit 76436561452336689889510890959177250487565082689861719162880 

noncomputable abbrev qz659 := (@HSub.hSub Real Real Real qz737 qz738 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz739 (@Nat.cast Real Real.instNatCast 1441048))))

noncomputable abbrev qz461 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 720524 4000) (Real.log (Enclosure.sfrac Bool.false 2076620338304 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz659))

noncomputable abbrev qz660 := (Enclosure.sfrac Bool.false 720524 2000)

noncomputable abbrev qz138 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz461 qz660) (@HMul.hMul Real Real Real qz349 qz660 (Real.log Real.pi)))

noncomputable def Ns372p874 := @Enclosure.Real.IsNear.addLit_ft_p qz138 (Enclosure.sfrac Bool.true Ns372p870 Ns372p871) 189678188410905640151 140737488355328000 85900683349658111 9216000000000000000000 Ns372p870 Ns372p871 0 1 Ns372p873 

noncomputable def Ns372p875 := nat_lit 3182271937458460680431599616000 

noncomputable abbrev qz139 := (@HSub.hSub Real Real Real qz353 qz461 qz660)

noncomputable def Ns372p876 := @Enclosure.Real.IsNear.subLit_ff_p qz139 (@HMul.hMul Real Real Real qz5 qz660 (Real.log Real.pi)) 247718705351857880279 140737488355328000 35572486877489 9000000000000000000 6918968789691 16777216000 180131 33554432000 Ns372p875 189678188410905640151 140737488355328000 

noncomputable abbrev qz140 := qz461

noncomputable def Ns372p877 := @Enclosure.Real.IsNear.subLit_ff_p qz140 qz660 59684214876345011243 28147497671065600 35572486877489 9000000000000000000 720524 2000 0 1 99087482140743152111600 247718705351857880279 140737488355328000 35572486877489 9000000000000000000 

noncomputable def Ns372p878 := nat_lit 268793807877008006632111927646486528 

noncomputable def Ns372p879 := nat_lit 56933943499985281110507520 

noncomputable def Ns372p880 := nat_lit 2853283566122436153886358291877442272077942933790338625506178502439239051816530388677622292352813017376508406950676299013556135262988503277829816796156862155318584012461326954265877653840808498368258821324800 

noncomputable def Ns372p881 := nat_lit 110164625080950249499788505597815268219932078057374788451628400503064308216700961128716773934075731367670959029889864484809382397328066950431050268795070802132048189415653096232974136114613585840002333409280 

noncomputable def Ns372p882 := nat_lit 3155357964138957334890144354534744705016781749700434689165630720917765314986769686117832941285250897356287075698676874263251261401672845481009356327788951005834912700112688440581429808474121201254400 

noncomputable def Ns372p883 := BSN.log_dyadic_bound 1028044338304 3125196338304 9 8 Ns372p880 134217728 46080000 Ns372p881 Ns372p882 91712138 4153240676608 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1028044338304) (BSN.artanhQ 3125196338304) 0 8 Ns372p881 Ns372p880 Ns372p882 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz462 := (Real.log (Enclosure.sfrac Bool.false 2076620338304 16000000))

noncomputable def Ns372p884 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 720524 4000) qz462 720524 4000 0 1 3313991677713655 281474976710656 48828161 2250000000000000 119390526979647677761 56294995342131200 8795465469091 2250000000000000000 (Enclosure.Real.IsNear.const Bool.false 720524 4000) (BSN.isNear_log_sfrac 2076620338304 16000000 3313991677713655 281474976710656 48828161 2250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2076620338304) qz356)) Bool.false Ns372p879 Ns372p98 1000000737280000 46080000000000000000000 3313991677713655 281474976710656 48828161 2250000000000000 (BSN.log_rat_reduce_isNear 2076620338304 16000000 16 4153240676608 2097152000000 91712138 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns372p883 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p885 := BSN.arctan_dyadic_bound_f 1000 1441048 1 0 16777216 5760000 0 1 1 0 1 1 11642 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1441048) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1441048) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns372p886 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1441048))) 884279719003555 562949953421312 1 2000000000000000 11642 16777216 1 5760000 14829197986784216088576 883889078306211 562949953421312 3125000009 18000000000000000 qz17 (Ns372p885 rfl) rfl rfl 

noncomputable abbrev qz463 := (@HMul.hMul Real Real Real qz584 qz589 qz659)

noncomputable abbrev qz141 := qz463

noncomputable abbrev qz464 := qz659

noncomputable abbrev qz142 := qz464

noncomputable def Ns372p887 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 720524 4000) qz462) qz141 119390526979647677761 56294995342131200 8795465469091 2250000000000000000 883889078306211 2251799813685248 3125000009 72000000000000000 Ns372p878 59684214876345011243 28147497671065600 35572486877489 9000000000000000000 (Ns372p884 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz142 1 4 0 1 883889078306211 562949953421312 3125000009 18000000000000000 883889078306211 2251799813685248 3125000009 72000000000000000 qz363 Ns372p886 rfl) 

noncomputable def Ns372p888 := @Ns372p874 Ns372p868 Ns372p869 85900683349658111 9216000000000000000000 (@Ns372p876 85900683349658111 9216000000000000000000 (Ns372p877 (Ns372p887 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 720524 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz660 (Real.log Real.pi) 720524 2000 0 1 38410761 33554432 1 67108864 6918968789691 16777216000 180131 33554432000 (Enclosure.Real.IsNear.const Bool.false 720524 2000) RS373to384.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns372p870 Ns372p871) 

noncomputable def Ns372p889 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns372p868 Ns372p869 85900683349658111 9216000000000000000000 45222796405 33554432 157 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz364 qz138 (Enclosure.sfrac Bool.true Ns372p870 Ns372p871)) Bool.false Ns372p868 Ns372p869 85900683349658111 9216000000000000000000 Ns372p872 (Ns372p888 rfl rfl)) 

noncomputable def Ns372p890 := BSN.cos_dyadic_bound_f 76233600 68719476736 1 0 33554432 11531251 0 1 1 0 1 1 33554411 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 76233600) qz379 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 76233600) qz380 0 0 rfl) rfl rfl 

noncomputable def Ns372p891 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz134) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 45222796405) qz367) Bool.false 45222796405 33554432 157 16777216 Bool.true 33554411 33554432 1 5760000 (Ns372p889 rfl) (Enclosure.sfrac_false_div 45222796405 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 45222796405) qz367) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5364462757045002567680) qz368) 226375608064910080 72057594037927936 Bool.false 33554411 33554432 214 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q2 45222796405 33554432 226375608064910080 72057594037927936 214 5364462757045002567680 Ns372p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554411 33554432 5364462757045002567680 Ns372p98 76233600 68719476736 11531251 11520000 (Ns372p890 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p892 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns372p868 Ns372p869 85900683349658111 9216000000000000000000 361782371247 268435456 2503 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz364 qz138 (Enclosure.sfrac Bool.true Ns372p870 Ns372p871)) Bool.false Ns372p868 Ns372p869 85900683349658111 9216000000000000000000 Ns372p872 (Ns372p888 rfl rfl)) 

noncomputable def Ns372p893 := Ns372p867 49301 BSN.abs_quadSignPos (BSN.cos_quad_nat0 540 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 267461668 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 354 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 266929761 268435456) qz137 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) Bool.true 33554411 33554432 899509 94371840000 268435288 268435456 2559 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 33554411 33554432 899509 94371840000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz134) qz134) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 33554411 33554432 921097216 96636764160000 33554411 33554432 899509 94371840000 (Ns372p891 rfl rfl) rfl)) rfl) (Ns372p892 rfl) RS373to384.d7 

noncomputable def Ns372p894 := nat_lit 273649139870455346250408595456 

noncomputable def Ns372p895 := BSN.cos_dyadic_bound_f 22871704 268435456 2 1 268435456 134217728 Ns372p894 Ns372p427 Ns372p894 Ns372p894 Ns372p428 Ns372p894 267461668 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 22871704) qz371 0 1 Ns372p894 Ns372p427 Ns372p894 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 22871704) qz372 0 1 Ns372p894 Ns372p428 Ns372p894 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p896 := nat_lit 654676121154931221871956600625 

noncomputable def Ns372p897 := BSN.cos_dyadic_bound_f 28445045 268435456 2 1 268435456 134217728 Ns372p896 Ns372p427 Ns372p896 Ns372p896 Ns372p428 Ns372p896 266929761 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 28445045) qz371 0 1 Ns372p896 Ns372p427 Ns372p896 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 28445045) qz372 0 1 Ns372p896 Ns372p428 Ns372p896 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p898 := nat_lit 4261153538088879374016183916816 

noncomputable def Ns372p899 := BSN.cos_dyadic_bound_f 45434086 268435456 2 1 268435456 134217728 Ns372p898 Ns372p427 Ns372p898 Ns372p898 Ns372p428 Ns372p898 264599649 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 45434086) qz371 0 1 Ns372p898 Ns372p427 Ns372p898 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 45434086) qz372 0 1 Ns372p898 Ns372p428 Ns372p898 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p900 := nat_lit 158686885038252011701389538876771247767177673427901541780536920854421760 

noncomputable def Ns372p901 := nat_lit 102009572745024096680462981664871821320406167076240825862423663534336 

noncomputable def Ns372p902 := nat_lit 415443350077644277347108995087895856441422772802571076659533725830144256 

noncomputable def Ns372p903 := BSN.sin_dyadic_bound_f 317015222 268435456 3 2 268435456 134217728 Ns372p900 Ns372p120 Ns372p901 Ns372p902 Ns372p123 Ns372p901 248296486 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 317015222) qz369 0 2 Ns372p900 Ns372p120 Ns372p901 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 317015222) qz370 0 2 Ns372p902 Ns372p123 Ns372p901 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p904 := Ns372p865 83777 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 222 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 264599649 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 119 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 248296486 268435456) qz137 rfl rfl (Ns372p893 RS373to384.d9 RS373to384.d11 RS373to384.d13 RS373to384.d17 (Ns372p895 rfl rfl) (Ns372p897 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns372p892 rfl) RS373to384.d19 RS373to384.d21 RS373to384.d23 RS373to384.d25 RS373to384.d17 (Ns372p899 rfl rfl) (Ns372p903 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns372p905 := nat_lit 6769907623692337126672096747776 

noncomputable def Ns372p906 := BSN.cos_dyadic_bound_f 51008868 268435456 2 1 268435456 134217728 Ns372p905 Ns372p427 Ns372p905 Ns372p905 Ns372p428 Ns372p905 263603596 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 51008868) qz371 0 1 Ns372p905 Ns372p427 Ns372p905 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 51008868) qz372 0 1 Ns372p905 Ns372p428 Ns372p905 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p907 := nat_lit 32956501885321181138163248457825110684490530056256296881477900061080481 

noncomputable def Ns372p908 := nat_lit 14261613704207610901739290430851568875781366095982388384300256951201 

noncomputable def Ns372p909 := nat_lit 98840982428555128192686266792613628915720027436576925867665099669339041 

noncomputable def Ns372p910 := BSN.cos_dyadic_bound_f 247896893 268435456 3 2 268435456 134217728 Ns372p907 Ns372p159 Ns372p908 Ns372p909 Ns372p162 Ns372p908 161877721 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 247896893) qz371 0 2 Ns372p907 Ns372p159 Ns372p908 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 247896893) qz372 0 2 Ns372p909 Ns372p162 Ns372p908 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p911 := Ns372p863 112956 BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 263603596 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 34 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 161877721 268435456) qz137 rfl rfl (Ns372p904 rfl rfl) (Ns372p892 rfl) RS373to384.d27 RS373to384.d29 RS373to384.d31 RS373to384.d33 RS373to384.d17 (Ns372p906 rfl rfl) (Ns372p910 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p912 := nat_lit 21910321032700358936499575427312161857097966930602043130516064407921563859200579315111843190656464596795068416 

noncomputable def Ns372p913 := nat_lit 3829958625924689103849807423335563717554651678137828650929687746093892984546006266214630193302005026816 

noncomputable def Ns372p914 := nat_lit 109484174448476462831565091116692179730658060907989035393265859541590415166413106486033085562316809341439512576 

noncomputable def Ns372p915 := BSN.sin_dyadic_bound_f 353671046 268435456 4 3 268435456 134217728 Ns372p912 Ns372p134 Ns372p913 Ns372p914 Ns372p137 Ns372p913 259871956 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 353671046) qz369 0 3 Ns372p912 Ns372p134 Ns372p913 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 353671046) qz370 0 3 Ns372p914 Ns372p137 Ns372p913 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p916 := nat_lit 24879329153280832535507797806903062580669483821117610998667118373925395067122624660982104234266431095050163761 

noncomputable def Ns372p917 := nat_lit 5605163081481974711135013610473424498159836993974357496577430213997529751393373358407558494210756531761 

noncomputable def Ns372p918 := nat_lit 124309722927842960718236520599371879646650477223924818481838708994040002652888331631990444430773010464572790321 

noncomputable def Ns372p919 := BSN.sin_dyadic_bound_f 365075219 268435456 4 3 268435456 134217728 Ns372p916 Ns372p134 Ns372p917 Ns372p918 Ns372p137 Ns372p917 262494157 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 365075219) qz369 0 3 Ns372p916 Ns372p134 Ns372p917 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 365075219) qz370 0 3 Ns372p918 Ns372p137 Ns372p917 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p920 := Ns372p861 138451 BSN.abs_quadSignPos (BSN.cos_quad_nat3 95 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 259871956 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 149 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 262494157 268435456) qz137 rfl rfl (Ns372p911 rfl) (Ns372p892 rfl) RS373to384.d35 RS373to384.d37 RS373to384.d39 RS373to384.d41 RS373to384.d17 (Ns372p915 rfl rfl) (Ns372p919 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p921 := nat_lit 395900638649060275818430020777945436554498186475029728797447052083456 

noncomputable def Ns372p922 := nat_lit 2059824850401043328231657104428000509606053975738711334576210176 

noncomputable def Ns372p923 := nat_lit 1187697796297480025368633599019627453662475347317137708969672003830016 

noncomputable def Ns372p924 := BSN.cos_dyadic_bound_f 82078382 268435456 3 2 268435456 134217728 Ns372p921 Ns372p159 Ns372p922 Ns372p923 Ns372p162 Ns372p922 255984535 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 82078382) qz371 0 2 Ns372p921 Ns372p159 Ns372p922 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 82078382) qz372 0 2 Ns372p923 Ns372p162 Ns372p922 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p925 := Ns372p859 Bool.true 203869321 138451 Bool.true 82078382 14148475504056880 1 Bool.false 255984535 Bool.true Bool.true 284818739 150190 BSN.abs_quadSignNeg qz595 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 255984535 268435456) qz137 rfl (Ns372p920 rfl) (Ns372p892 rfl) RS373to384.d43 RS373to384.d45 RS373to384.d17 (Ns372p924 rfl rfl) rfl 

noncomputable def Ns372p926 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) 284818739 268435456 150190 268435456 284818739 268435456 150190 268435456 152910896161619968 284818739 134217728 75095 67108864 (Ns372p925 rfl rfl rfl rfl) 

noncomputable def Ns372p927 := @Enclosure.Real.IsNear.mulLit_ff qz657 (Zeta.RiemannSiegel.correction qz136) 10253751 33554432 1 33554432 65125542243223 140737488355328 114959395948177 1583296743997440000 667781093901990079473 4722366482869645213696 

noncomputable abbrev qz661 := (@HPow.hPow Real Real Real qz7 qz135 qz9)

noncomputable def Ns372p928 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz661 1 1 0 1 10253751 33554432 1 33554432 10253751 33554432 1 33554432 

noncomputable def Ns372p929 := @Enclosure.Real.IsNear.sqrt_image qz135 961963126243 8388608000 180131 8388608000 179661126 179661160 16777216 (@Enclosure.Real.IsNear.of_eq qz135 (@HMul.hMul Real Real Real qz5 qz134 qz3) Bool.false 961963126243 8388608000 180131 8388608000 (BSN.t_div_two_pi_mk qz134 720524 1000 qz137) (@Enclosure.Real.IsNear.mulLit_ff qz134 qz3 720524 1000 0 1 5340353 33554432 1 33554432 961963126243 8388608000 180131 8388608000 (Enclosure.Real.IsNear.const Bool.false 720524 1000) RS373to384.d48 rfl)) 

noncomputable abbrev qz765 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 720524 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz662 := qz765

noncomputable abbrev qz465 := qz662

noncomputable abbrev qz143 := qz465

noncomputable def Ns372p930 := @Enclosure.Real.IsNear.sqrt_image qz143 179661143 16777216 17 16777216 54901853 54901859 16777216 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 359322286 33554432 34 33554432 179661143 16777216 17 16777216 (Ns372p929 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns372p931 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz143) 1715683 524288 3 16777216 5126875 5126876 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz143) Bool.false 109803712 33554432 6 33554432 1715683 524288 3 16777216 (Ns372p930 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns372p932 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 10253751 33554432 1 33554432 10253751 33554432 1 33554432 (Ns372p931 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz466 := (@HMul.hMul Real Real Real qz584 qz582 qz656)

noncomputable abbrev qz144 := (Real.cos qz466)

noncomputable abbrev qz663 := (@HMul.hMul Real Real Real qz733 qz764 qz764)

noncomputable abbrev qz467 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz663 qz656) qz600)

noncomputable abbrev qz145 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz467))

noncomputable def Ns372p933 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz136) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz144) qz145) Bool.false 65125542243223 

noncomputable def Ns372p934 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz144) qz145 130579361 33554432 3345 

noncomputable abbrev qz146 := (@Neg.neg Real Real.instNeg (Real.cos qz466))

noncomputable def Ns372p935 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz144) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz146)) Bool.true 130579361 33554432 3345 33554432 (BSN.inv_eq_neg_inv_neg qz144) 

noncomputable def Ns372p936 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz146) Bool.false 130579361 33554432 3345 33554432 130579361 33554432 

noncomputable def Ns372p937 := @Enclosure.Real.IsNear.recentre' qz144 Bool.true 8622342 33554432 1271954432 193273528320000 4311171 16777216 1242143 188743680000 

noncomputable abbrev qz147 := qz466

noncomputable def Ns372p938 := @Enclosure.Real.IsNear.cos_image qz147 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 74700683) qz411) Bool.false 74700683 16777216 215 33554432 Bool.true 8622342 33554432 1 

noncomputable def Ns372p939 := nat_lit 3670106256446994872586179 

noncomputable def Ns372p940 := nat_lit 576460752303423488000000000000 

noncomputable def Ns372p941 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz136 884279719003555 140737488355328 1 500000000000000 11888983 16777216 17 16777216 10513186546478042334565 2361183241434822606848 Ns372p939 

noncomputable def Ns372p942 := @Enclosure.Real.IsNear.subLit_ff_p qz143 qz1 179661143 16777216 17 16777216 10 1 0 1 11888983 11888983 16777216 17 

noncomputable def Ns372p943 := @Ns372p942 16777216 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 359322286 33554432 34 33554432 179661143 16777216 17 16777216 (Ns372p929 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns372p944 := @Enclosure.Real.IsNear.recentre' qz147 Bool.false 10513186546478042334565 2361183241434822606848 Ns372p939 Ns372p940 74700683 16777216 215 33554432 (@Ns372p941 Ns372p940 RS373to384.d47 (Ns372p943 rfl rfl) rfl) 

noncomputable def Ns372p945 := nat_lit 3169598032667212582486016 

noncomputable def Ns372p946 := nat_lit 654854724018221399621898190309793044806881603726174616807450841984886165901785333073507353588916195480216118766277703312622912620484390625 

noncomputable def Ns372p947 := nat_lit 285662087167882962359625381013921987385625360674769625298635878370546069236630057318638114828389335166257396959412750514472900390625 

noncomputable def Ns372p948 := nat_lit 3968136267467823819177071499921613456491645745019457528544184421025989468221555070432710639330670454405581349328720786918256686326109990625 

noncomputable def Ns372p949 := BSN.cos_dyadic_bound_f 90085394295 68719476736 4 3 33554432 11531251 Ns372p946 Ns372p830 Ns372p947 Ns372p948 Ns372p833 Ns372p947 8622342 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 90085394295) qz379 0 3 Ns372p946 Ns372p830 Ns372p947 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 90085394295) qz380 0 3 Ns372p948 Ns372p833 Ns372p947 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p950 := @Ns372p938 5760000 (Ns372p944 rfl) (Enclosure.sfrac_false_div 74700683 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 74700683) qz411) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns372p945) qz412) 226375608064910080 72057594037927936 Bool.false 8622342 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q2 74700683 16777216 226375608064910080 72057594037927936 0 Ns372p945 Ns372p403 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 8622342 33554432 Ns372p945 Ns372p403 90085394295 68719476736 11531251 11520000 (Ns372p949 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p951 := @Enclosure.Real.IsNear.inv_image qz146 4311171 16777216 1242143 188743680000 65288008 65291353 16777216 (@Enclosure.Real.IsNear.neg qz144 Bool.true 4311171 16777216 1242143 188743680000 (Ns372p937 (Ns372p950 rfl rfl) rfl)) 

noncomputable def Ns372p952 := Ns372p935 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz146) Bool.false 130579361 33554432 3345 33554432 (@Ns372p936 3345 33554432 (Ns372p951 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p953 := @Enclosure.Real.IsNear.recentre' qz145 Bool.true 1994972 16777216 

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz349 qz346 qz467)

noncomputable def Ns372p954 := @Enclosure.Real.IsNear.cos_image qz148 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7088323)) qz608) Bool.true 7088323 4194304 

noncomputable def Ns372p955 := nat_lit 66947318743664442535709572525 

noncomputable def Ns372p956 := nat_lit 39614081257132168796771975168 

noncomputable def Ns372p957 := nat_lit 18605236194177719663111071282451721 

noncomputable def Ns372p958 := @Enclosure.Real.IsNear.recentre' qz148 Bool.true Ns372p955 Ns372p956 Ns372p957 

noncomputable abbrev qz149 := qz467

noncomputable def Ns372p959 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz149 884279719003555 140737488355328 1 500000000000000 75708305081455 

noncomputable abbrev qz468 := (@HSub.hSub Real Real Real qz588 qz663 qz656)

noncomputable abbrev qz150 := qz468

noncomputable def Ns372p960 := @Enclosure.Real.IsNear.subLit_tf qz150 qz31 58116119037039 281474976710656 689438383 281474976710656 1 16 

noncomputable abbrev qz469 := qz663

noncomputable abbrev qz151 := qz469

noncomputable def Ns372p961 := @Enclosure.Real.IsNear.subLit_ff_n qz151 qz136 141347916774289 281474976710656 404225711 281474976710656 11888983 16777216 17 16777216 

noncomputable def Ns372p962 := @Enclosure.Real.IsNear.mulLit_ff qz136 qz136 11888983 16777216 17 16777216 11888983 16777216 17 16777216 141347916774289 281474976710656 

noncomputable def Ns372p963 := nat_lit 4849354888404319944967849724256095633346031762611193813271361587813719380964923497295601 

noncomputable def Ns372p964 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600 

noncomputable def Ns372p965 := nat_lit 16088738415706092606955258270686721802329665581748553117094449045232192491623329521 

noncomputable def Ns372p966 := nat_lit 29324569875631060417226453841059074617432149619342311569627261143013721207079106278895345 

noncomputable def Ns372p967 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600 

noncomputable def Ns372p968 := BSN.cos_dyadic_bound_t 7088323 4194304 4 3 16777216 5760000 Ns372p963 Ns372p964 Ns372p965 Ns372p966 Ns372p967 Ns372p965 1994972 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 7088323) (BSN.cosEvenQ 4194304) 0 3 Ns372p963 Ns372p964 Ns372p965 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 7088323) (BSN.cosOddQ 4194304) 0 3 Ns372p966 Ns372p967 Ns372p965 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p969 := @Ns372p953 1508617216 96636764160000 498743 4194304 1473259 94371840000 (@Ns372p954 259 16777216 Bool.true 1994972 16777216 1 5760000 (@Ns372p958 Ns372p200 7088323 4194304 259 16777216 (@Ns372p959 281474976710656 689438383 281474976710656 Ns372p955 Ns372p956 Ns372p957 Ns372p200 RS373to384.d47 (@Ns372p960 0 1 1211332881303280 75708305081455 281474976710656 689438383 281474976710656 (@Ns372p961 975026682166115303424 58116119037039 281474976710656 689438383 281474976710656 (@Ns372p962 404225711 281474976710656 (Ns372p943 rfl rfl) (Ns372p943 rfl rfl) rfl) (Ns372p943 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7088323 4194304) (BSN.cos_neg_of_bound 7088323 4194304 Bool.true 1994972 16777216 1 5760000 (Ns372p968 rfl rfl)) rfl rfl) 

noncomputable def Ns372p970 := @Ns372p927 589748899236324034427 Ns372p856 (Ns372p928 qz33 (@Enclosure.Real.IsNear.of_eq qz661 (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 10253751 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz135 (BSN.t_div_two_pi_nonneg qz134 720524 1000 qz137)) Ns372p932) rfl) (@Ns372p933 140737488355328 114959395948177 1583296743997440000 (BSN.correction_mk qz136 (BSN.cos_two_pi_p_ne_zero_mk qz134 720524 1000 10 qz137 rfl rfl (@BSN.floor_sqrt_eq_dec qz134 720524 1000 10 qz137 rfl rfl rfl))) (@Ns372p934 33554432 498743 4194304 1473259 94371840000 65125542243223 140737488355328 114959395948177 1583296743997440000 Ns372p952 (Ns372p969 rfl) rfl)) 

noncomputable def Ns372p971 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (hardyZApproximantRS₀ qz134) Bool.true 10688949584749916302321 4722366482869645213696 30314166146858263234427 Ns372p856 (@Eq.refl Real (hardyZApproximantRS₀ qz134)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) (@HMul.hMul Real Real Real qz5 qz657 (Zeta.RiemannSiegel.correction qz136))) Bool.true 10688949584749916302321 4722366482869645213696 30314166146858263234427 Ns372p856 (BSN.hardyZApproximantRS₀_eq qz134 10 (@BSN.floor_sqrt_eq_dec qz134 720524 1000 10 qz137 rfl rfl rfl)) (@Ns372p858 10688949584749916302321 4722366482869645213696 30314166146858263234427 Ns372p856 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 10)) Bool.true 284818739 134217728 75095 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) (Ns372p926 (Ns372p925 rfl rfl rfl rfl) rfl rfl)) (Ns372p970 rfl) rfl rfl)) 

theorem RS373to384.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz134) Bool.true 10688949584749916302321 4722366482869645213696 30314166146858263234427 Ns372p856 := Ns372p971 

noncomputable def Ns372p972 := nat_lit 10625324586456701730816000 

noncomputable def Ns372p973 := nat_lit 569834535633916960326318817280 

noncomputable abbrev qz766 := (Enclosure.sfrac Bool.false 721848 1000)

noncomputable abbrev qz664 := qz766

noncomputable abbrev qz470 := qz664

noncomputable abbrev qz152 := qz470

noncomputable abbrev qz767 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 721848 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz665 := qz767

noncomputable abbrev qz471 := qz665

noncomputable abbrev qz153 := qz471

noncomputable abbrev qz768 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 721848 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz666 := qz768

noncomputable abbrev qz472 := qz666

noncomputable abbrev qz154 := qz472

noncomputable abbrev qz667 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz153 qz9))

noncomputable def Ns372p974 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) (@HMul.hMul Real Real Real qz5 qz667 (Zeta.RiemannSiegel.correction qz154)) 69985609 67108864 75235 67108864 1358402562375715605357 9444732965739290427392 319100059157288462479 Ns372p972 Ns372p973 

noncomputable def Ns372p975 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos BSN.quadSignNeg 9 10 721848 1000 198 268435456 134217728 4503599627370496 Bool.false 362625226087 2508 618095470 48 84886744 8 

noncomputable def Ns372p976 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 721848 1000 95 149 268435456 134217728 4503599627370496 Bool.false 362625226087 2508 

noncomputable def Ns372p977 := Ns372p976 558195838 48 94906264 8 589812974 48 89478488 8 Bool.false 227683744 113168 Bool.true 249867496 Bool.true 303132757 14148475504056880 1 Bool.false 215316171 Bool.false Bool.false 242691194 Bool.true Bool.false 222912437 

noncomputable def Ns372p978 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 721848 1000 36 34 268435456 134217728 4503599627370496 Bool.false 362625226087 2508 

noncomputable def Ns372p979 := Ns372p978 480971758 48 109588312 8 522351262 48 101459064 8 Bool.false 259573920 83935 Bool.false 257057100 Bool.true 96635124 14148475504056880 1 Bool.false 154477710 Bool.false Bool.false 251228468 Bool.true Bool.false 227683744 

noncomputable def Ns372p980 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 721848 1000 222 120 268435456 134217728 4503599627370496 Bool.false 362625226087 2508 

noncomputable def Ns372p981 := Ns372p980 372130544 47 134217720 8 432030192 47 120047984 16 Bool.false 174825128 49395 Bool.false 395588086 Bool.false 166204660 14148475504056880 1 Bool.false 26028382 Bool.true Bool.false 218604678 Bool.false Bool.false 259573920 

noncomputable def Ns372p982 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 721848 1000 541 355 268435456 134217728 4503599627370496 Bool.false 362625226087 2508 

noncomputable def Ns372p983 := Ns372p982 186065264 47 189812528 16 294906480 47 154981288 8 Bool.false 268435400 2567 Bool.false 197718707 Bool.false 59186277 14148475504056880 1 Bool.false 180319714 Bool.true Bool.false 58707893 Bool.false Bool.false 174825128 

noncomputable def Ns372p984 := nat_lit 13133278327453651760713399691870457290358741915646887 

noncomputable def Ns372p985 := nat_lit 9721986511082528375161294967012465382107643904000 

noncomputable def Ns372p986 := nat_lit 94074204132406326543912263024640000 

noncomputable def Ns372p987 := nat_lit 407443747854525015579777093153038008320 

noncomputable abbrev qz668 := (@Eq.refl Real qz766)

noncomputable abbrev qz473 := qz668

noncomputable abbrev qz155 := qz473

noncomputable def Ns372p988 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz152 721848 1000 2084259140416 16000000 1443696 4000 2000 Ns372p986 Ns372p987 qz155 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns372p989 := nat_lit 154926455124240453922220405197156012016571091833090189557760 

noncomputable abbrev qz669 := (@HSub.hSub Real Real Real qz737 qz738 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz739 (@Nat.cast Real Real.instNatCast 1443696))))

noncomputable abbrev qz474 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 721848 4000) (Real.log (Enclosure.sfrac Bool.false 2084259140416 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz669))

noncomputable abbrev qz670 := (Enclosure.sfrac Bool.false 721848 2000)

noncomputable abbrev qz156 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz474 qz670) (@HMul.hMul Real Real Real qz349 qz670 (Real.log Real.pi)))

noncomputable def Ns372p990 := @Enclosure.Real.IsNear.addLit_ft_p qz156 (Enclosure.sfrac Bool.true Ns372p986 Ns372p987) 380240174059782860043 281474976710656000 43028897631850211 4608000000000000000000 Ns372p986 Ns372p987 0 1 Ns372p989 

noncomputable def Ns372p991 := nat_lit 637937153207857395603918028800 

noncomputable abbrev qz157 := (@HSub.hSub Real Real Real qz353 qz474 qz670)

noncomputable def Ns372p992 := @Enclosure.Real.IsNear.subLit_ff_p qz157 (@HMul.hMul Real Real Real qz5 qz670 (Real.log Real.pi)) 99306902565309683151 56294995342131200 35637135362653 9000000000000000000 3465841375791 8388608000 90231 16777216000 Ns372p991 380240174059782860043 281474976710656000 

noncomputable abbrev qz158 := qz474

noncomputable def Ns372p993 := @Enclosure.Real.IsNear.subLit_ff_p qz158 qz670 598125587320865221899 281474976710656000 35637135362653 9000000000000000000 721848 2000 0 1 993069025653096831510000 99306902565309683151 56294995342131200 35637135362653 9000000000000000000 

noncomputable def Ns372p994 := nat_lit 673429543044751920065409978231422976 

noncomputable def Ns372p995 := nat_lit 56951698887472993762541568 

noncomputable def Ns372p996 := nat_lit 2966939504440343037855905142239942882738791564695666893678609773291353770116564990520897439367639809230442353417120100850232558697096492420688942958095243390013696077943977028660658980021817077399699639500800 

noncomputable def Ns372p997 := nat_lit 115777682001380179038571800917685677900958087796947507310976908980540201700761095188353229142579968862737986514170096182446818496511727915101359308259448284826632650969013949051188012849984308883957355642880 

noncomputable def Ns372p998 := nat_lit 3552136201734792064223993800728840356504438424860391479284350926087777750196219485942040791053731842247701266536299597447527697851873720304857114200905688292691468967505251747007468640073471649382400 

noncomputable def Ns372p999 := BSN.log_dyadic_bound 1035683140416 3132835140416 9 8 Ns372p996 134217728 46080000 Ns372p997 Ns372p998 92204949 4168518280832 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1035683140416) (BSN.artanhQ 3132835140416) 0 8 Ns372p997 Ns372p996 Ns372p998 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz475 := (Real.log (Enclosure.sfrac Bool.false 2084259140416 16000000))

noncomputable def Ns372p1000 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 721848 4000) qz475 721848 4000 0 1 3315025177287927 281474976710656 48828161 2250000000000000 299118036771866941137 140737488355328000 1468604598397 375000000000000000 (Enclosure.Real.IsNear.const Bool.false 721848 4000) (BSN.isNear_log_sfrac 2084259140416 16000000 3315025177287927 281474976710656 48828161 2250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2084259140416) qz356)) Bool.false Ns372p995 Ns372p98 1000000737280000 46080000000000000000000 3315025177287927 281474976710656 48828161 2250000000000000 (BSN.log_rat_reduce_isNear 2084259140416 16000000 16 4168518280832 2097152000000 92204949 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns372p999 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p1001 := BSN.arctan_dyadic_bound_f 1000 1443696 1 0 16777216 5760000 0 1 1 0 1 1 11621 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1443696) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1443696) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns372p1002 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1443696))) 884279719003555 562949953421312 1 2000000000000000 11621 16777216 1 5760000 14829209808733237936128 883889782949283 562949953421312 3125000009 18000000000000000 qz17 (Ns372p1001 rfl) rfl rfl 

noncomputable abbrev qz476 := (@HMul.hMul Real Real Real qz584 qz589 qz669)

noncomputable abbrev qz159 := qz476

noncomputable abbrev qz477 := qz669

noncomputable abbrev qz160 := qz477

noncomputable def Ns372p1003 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 721848 4000) qz475) qz159 299118036771866941137 140737488355328000 1468604598397 375000000000000000 883889782949283 2251799813685248 3125000009 72000000000000000 Ns372p994 598125587320865221899 281474976710656000 35637135362653 9000000000000000000 (Ns372p1000 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz160 1 4 0 1 883889782949283 562949953421312 3125000009 18000000000000000 883889782949283 2251799813685248 3125000009 72000000000000000 qz363 Ns372p1002 rfl) 

noncomputable def Ns372p1004 := @Ns372p990 Ns372p984 Ns372p985 43028897631850211 4608000000000000000000 (@Ns372p992 43028897631850211 4608000000000000000000 (Ns372p993 (Ns372p1003 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 721848 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz670 (Real.log Real.pi) 721848 2000 0 1 38410761 33554432 1 67108864 3465841375791 8388608000 90231 16777216000 (Enclosure.Real.IsNear.const Bool.false 721848 2000) RS373to384.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns372p986 Ns372p987) 

noncomputable def Ns372p1005 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns372p984 Ns372p985 43028897631850211 4608000000000000000000 11332038315 8388608 315 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz364 qz156 (Enclosure.sfrac Bool.true Ns372p986 Ns372p987)) Bool.false Ns372p984 Ns372p985 43028897631850211 4608000000000000000000 Ns372p988 (Ns372p1004 rfl rfl)) 

noncomputable def Ns372p1006 := nat_lit 1898245622222511061073920 

noncomputable def Ns372p1007 := nat_lit 3505424708606111172309433803138465493522977820130701694314203533731104261936132620094283242235657630868050420369859319634196914340538351616 

noncomputable def Ns372p1008 := nat_lit 2491100064869740693174615725063500947241440205792466355746061583044619049279860351781563396656338814357271978766753908852269269385216 

noncomputable def Ns372p1009 := nat_lit 17505377376049735857509319333418239593029734443512149913420842563340218257416171456267311268276874846339592193192844135860157876462919090176 

noncomputable def Ns372p1010 := BSN.sin_dyadic_bound_f 107902771004 68719476736 4 3 33554432 11531251 Ns372p1007 Ns372p111 Ns372p1008 Ns372p1009 Ns372p114 Ns372p1008 33554425 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107902771004) qz365 0 3 Ns372p1007 Ns372p111 Ns372p1008 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107902771004) qz366 0 3 Ns372p1009 Ns372p114 Ns372p1008 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1011 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz152) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11332038315) qz377) Bool.false 11332038315 8388608 315 33554432 Bool.false 33554425 33554432 1 5760000 (Ns372p1005 rfl) (Enclosure.sfrac_false_div 11332038315 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11332038315) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns372p1006) (@Nat.cast Real Real.instNatCast Ns372p184)) 226375608064910080 72057594037927936 Bool.false 33554425 33554432 214 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 11332038315 8388608 226375608064910080 72057594037927936 214 Ns372p1006 Ns372p184 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554425 33554432 Ns372p1006 Ns372p184 107902771004 68719476736 11531251 11520000 (Ns372p1010 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p1012 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns372p984 Ns372p985 43028897631850211 4608000000000000000000 362625226087 268435456 2508 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz364 qz156 (Enclosure.sfrac Bool.true Ns372p986 Ns372p987)) Bool.false Ns372p984 Ns372p985 43028897631850211 4608000000000000000000 Ns372p988 (Ns372p1004 rfl rfl)) 

noncomputable def Ns372p1013 := Ns372p983 49395 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 541 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 180319714 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 355 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 58707893 268435456) qz155 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) Bool.false 33554425 33554432 1804643 188743680000 268435400 268435456 2567 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 33554425 33554432 1804643 188743680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz152) qz152) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 33554425 33554432 1847954432 193273528320000 33554425 33554432 1804643 188743680000 (Ns372p1011 rfl rfl) rfl)) rfl) (Ns372p1012 rfl) RS373to384.d7 

noncomputable def Ns372p1014 := nat_lit 23997976077509880086634323775907165778945758025705134188198272244163105 

noncomputable def Ns372p1015 := nat_lit 2335511948633341615840857223028976377175987849792805235667359277601 

noncomputable def Ns372p1016 := nat_lit 62848060802704279578569010406157672983104414658423305951090108724453921 

noncomputable def Ns372p1017 := BSN.sin_dyadic_bound_f 197718707 268435456 3 2 268435456 134217728 Ns372p1014 Ns372p120 Ns372p1015 Ns372p1016 Ns372p123 Ns372p1015 180319714 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 197718707) qz369 0 2 Ns372p1014 Ns372p120 Ns372p1015 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 197718707) qz370 0 2 Ns372p1016 Ns372p123 Ns372p1015 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1018 := nat_lit 12271116788392529313845905491441 

noncomputable def Ns372p1019 := BSN.sin_dyadic_bound_f 59186277 268435456 2 1 268435456 134217728 Ns372p1018 Ns372p130 Ns372p1018 Ns372p1018 Ns372p131 Ns372p1018 58707893 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 59186277) qz369 0 1 Ns372p1018 Ns372p130 Ns372p1018 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 59186277) qz370 0 1 Ns372p1018 Ns372p131 Ns372p1018 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1020 := nat_lit 13214038769280557764445997993446526121647620558990816326863396612317310593638949422426705967616084895596875776 

noncomputable def Ns372p1021 := nat_lit 14686504433712961531537618754313072107862690952647197929145455592523101012484694983335549009047029354496 

noncomputable def Ns372p1022 := nat_lit 80015477289440778863964002167496843713459796346057163977285910345254760701417473996061078170363560746186772480 

noncomputable def Ns372p1023 := BSN.cos_dyadic_bound_f 395588086 268435456 4 3 268435456 134217728 Ns372p1020 Ns372p143 Ns372p1021 Ns372p1022 Ns372p146 Ns372p1021 26028382 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 395588086) qz371 0 3 Ns372p1020 Ns372p143 Ns372p1021 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 395588086) qz372 0 3 Ns372p1022 Ns372p146 Ns372p1021 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1024 := nat_lit 6657015544878363804937461672416275773594303118704426240470429900800000 

noncomputable def Ns372p1025 := nat_lit 582298364050843313494572421486310088013130842900111908889600000000 

noncomputable def Ns372p1026 := nat_lit 19969882037906989728185395872405854700606883094427478497593510502400000 

noncomputable def Ns372p1027 := BSN.cos_dyadic_bound_f 166204660 268435456 3 2 268435456 134217728 Ns372p1024 Ns372p159 Ns372p1025 Ns372p1026 Ns372p162 Ns372p1025 218604678 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 166204660) qz371 0 2 Ns372p1024 Ns372p159 Ns372p1025 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 166204660) qz372 0 2 Ns372p1026 Ns372p162 Ns372p1025 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1028 := Ns372p981 83935 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 222 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 26028382 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 120 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 218604678 268435456) qz155 rfl rfl (Ns372p1013 RS373to384.d9 RS373to384.d11 RS373to384.d13 RS373to384.d17 (Ns372p1017 rfl rfl) (Ns372p1019 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns372p1012 rfl) RS373to384.d19 RS373to384.d21 RS373to384.d23 RS373to384.d25 RS373to384.d17 (Ns372p1023 rfl rfl) (Ns372p1027 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns372p1029 := nat_lit 38106981028696026366546168883848951977897561024984056230807168000000000 

noncomputable def Ns372p1030 := nat_lit 19065000885402533090011632884501045597207664907697610000000000000000 

noncomputable def Ns372p1031 := nat_lit 114282813084317274033458483385777853842498267745136773472421504000000000 

noncomputable def Ns372p1032 := BSN.cos_dyadic_bound_f 257057100 268435456 3 2 268435456 134217728 Ns372p1029 Ns372p159 Ns372p1030 Ns372p1031 Ns372p162 Ns372p1030 154477710 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 257057100) qz371 0 2 Ns372p1029 Ns372p159 Ns372p1030 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 257057100) qz372 0 2 Ns372p1031 Ns372p162 Ns372p1030 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1033 := nat_lit 760699570056982647885534207754787899424000283485694363674567109574656 

noncomputable def Ns372p1034 := nat_lit 7604664629196964930098491904787926606631907539500209291751653376 

noncomputable def Ns372p1035 := nat_lit 2282083500841689549726742426280554122418787586642004090605117825417216 

noncomputable def Ns372p1036 := BSN.cos_dyadic_bound_f 96635124 268435456 3 2 268435456 134217728 Ns372p1033 Ns372p159 Ns372p1034 Ns372p1035 Ns372p162 Ns372p1034 251228468 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 96635124) qz371 0 2 Ns372p1033 Ns372p159 Ns372p1034 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 96635124) qz372 0 2 Ns372p1035 Ns372p162 Ns372p1034 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1037 := Ns372p979 113168 BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 154477710 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 34 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 251228468 268435456) qz155 rfl rfl (Ns372p1028 rfl rfl) (Ns372p1012 rfl) RS373to384.d27 RS373to384.d29 RS373to384.d31 RS373to384.d33 RS373to384.d17 (Ns372p1032 rfl rfl) (Ns372p1036 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p1038 := nat_lit 61219272173776527028409952789447510350706665340613859947174398640783360 

noncomputable def Ns372p1039 := nat_lit 15194209737282436341507544676511616675716387422652547692740567105536 

noncomputable def Ns372p1040 := nat_lit 160311588877459113510806483185743413062947249360066290974906606950547456 

noncomputable def Ns372p1041 := BSN.sin_dyadic_bound_f 249867496 268435456 3 2 268435456 134217728 Ns372p1038 Ns372p120 Ns372p1039 Ns372p1040 Ns372p123 Ns372p1039 215316171 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 249867496) qz369 0 2 Ns372p1038 Ns372p120 Ns372p1039 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 249867496) qz370 0 2 Ns372p1040 Ns372p123 Ns372p1039 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1042 := nat_lit 132649697307240212178745481264136662756765022347187248257693860177412705 

noncomputable def Ns372p1043 := nat_lit 71295637316870630350199375269090565317224128671876897633886108680801 

noncomputable def Ns372p1044 := nat_lit 347300442868068479447575937655636541542918600415259754269219532479169121 

noncomputable def Ns372p1045 := BSN.sin_dyadic_bound_f 303132757 268435456 3 2 268435456 134217728 Ns372p1042 Ns372p120 Ns372p1043 Ns372p1044 Ns372p123 Ns372p1043 242691194 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 303132757) qz369 0 2 Ns372p1042 Ns372p120 Ns372p1043 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 303132757) qz370 0 2 Ns372p1044 Ns372p123 Ns372p1043 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1046 := Ns372p977 138710 BSN.abs_quadSignPos (BSN.cos_quad_nat3 95 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 215316171 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 149 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 242691194 268435456) qz155 rfl rfl (Ns372p1037 rfl) (Ns372p1012 rfl) RS373to384.d35 RS373to384.d37 RS373to384.d39 RS373to384.d41 RS373to384.d17 (Ns372p1041 rfl rfl) (Ns372p1045 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p1047 := nat_lit 10993735684824701230517511786496 

noncomputable def Ns372p1048 := BSN.cos_dyadic_bound_f 57581944 268435456 2 1 268435456 134217728 Ns372p1047 Ns372p427 Ns372p1047 Ns372p1047 Ns372p428 Ns372p1047 262283165 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 57581944) qz371 0 1 Ns372p1047 Ns372p427 Ns372p1047 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 57581944) qz372 0 1 Ns372p1047 Ns372p428 Ns372p1047 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1049 := Ns372p975 Bool.false 222912437 138710 Bool.true 57581944 14148475504056880 1 Bool.false 262283165 Bool.true Bool.false 139971218 150470 BSN.abs_quadSignNeg qz595 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 262283165 268435456) qz155 rfl (Ns372p1046 rfl) (Ns372p1012 rfl) RS373to384.d43 RS373to384.d45 RS373to384.d17 (Ns372p1048 rfl rfl) rfl 

noncomputable def Ns372p1050 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) 139971218 268435456 150470 268435456 139971218 268435456 150470 268435456 75146475461410816 69985609 67108864 75235 67108864 (Ns372p1049 rfl rfl rfl rfl) 

noncomputable def Ns372p1051 := @Enclosure.Real.IsNear.mulLit_ff qz667 (Zeta.RiemannSiegel.correction qz154) 5124523 16777216 1 16777216 265078830239559 562949953421312 62211016178921 633318697598976000 1358402562375715605357 9444732965739290427392 

noncomputable abbrev qz671 := (@HPow.hPow Real Real Real qz7 qz153 qz9)

noncomputable def Ns372p1052 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz671 1 1 0 1 5124523 16777216 1 16777216 5124523 16777216 1 16777216 

noncomputable def Ns372p1053 := @Enclosure.Real.IsNear.sqrt_image qz153 481865391543 4194304000 90231 4194304000 179826118 179826153 16777216 (@Enclosure.Real.IsNear.of_eq qz153 (@HMul.hMul Real Real Real qz5 qz152 qz3) Bool.false 481865391543 4194304000 90231 4194304000 (BSN.t_div_two_pi_mk qz152 721848 1000 qz155) (@Enclosure.Real.IsNear.mulLit_ff qz152 qz3 721848 1000 0 1 5340353 33554432 1 33554432 481865391543 4194304000 90231 4194304000 (Enclosure.Real.IsNear.const Bool.false 721848 1000) RS373to384.d48 rfl)) 

noncomputable abbrev qz769 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 721848 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz672 := qz769

noncomputable abbrev qz478 := qz672

noncomputable abbrev qz161 := qz478

noncomputable def Ns372p1054 := @Enclosure.Real.IsNear.sqrt_image qz161 359652271 33554432 35 33554432 54927057 54927063 16777216 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 359652271 33554432 35 33554432 359652271 33554432 35 33554432 (Ns372p1053 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns372p1055 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz161) 13731765 4194304 3 16777216 5124522 5124524 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz161) Bool.false 109854120 33554432 6 33554432 13731765 4194304 3 16777216 (Ns372p1054 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns372p1056 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 10249046 33554432 2 33554432 5124523 16777216 1 16777216 (Ns372p1055 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz479 := (@HMul.hMul Real Real Real qz584 qz582 qz666)

noncomputable abbrev qz162 := (Real.cos qz479)

noncomputable abbrev qz673 := (@HMul.hMul Real Real Real qz733 qz768 qz768)

noncomputable abbrev qz480 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz673 qz666) qz600)

noncomputable abbrev qz163 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz480))

noncomputable def Ns372p1057 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz154) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz162) qz163) Bool.false 265078830239559 

noncomputable def Ns372p1058 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz162) qz163 170502363 33554432 5857 

noncomputable abbrev qz164 := (@Neg.neg Real Real.instNeg (Real.cos qz479))

noncomputable def Ns372p1059 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz162) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz164)) Bool.true 170502363 33554432 5857 33554432 (BSN.inv_eq_neg_inv_neg qz162) 

noncomputable def Ns372p1060 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz164) Bool.false 170502363 33554432 5857 33554432 170502363 33554432 

noncomputable def Ns372p1061 := @Enclosure.Real.IsNear.recentre' qz162 Bool.true 6603427 33554432 1306514432 193273528320000 6603427 33554432 1275893 188743680000 

noncomputable abbrev qz165 := qz479

noncomputable def Ns372p1062 := @Enclosure.Real.IsNear.cos_image qz165 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 151474723) qz367) Bool.false 151474723 33554432 221 33554432 Bool.true 6603427 33554432 1 

noncomputable def Ns372p1063 := nat_lit 944512639523627313168054837 

noncomputable def Ns372p1064 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz154 884279719003555 140737488355328 1 500000000000000 24107951 33554432 35 33554432 21318172136031472765805 4722366482869645213696 Ns372p1063 

noncomputable def Ns372p1065 := @Enclosure.Real.IsNear.subLit_ff_p qz161 qz1 359652271 33554432 35 33554432 10 1 0 1 24107951 24107951 33554432 35 

noncomputable def Ns372p1066 := @Ns372p1065 33554432 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 359652271 33554432 35 33554432 359652271 33554432 35 33554432 (Ns372p1053 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns372p1067 := @Enclosure.Real.IsNear.recentre' qz165 Bool.false 21318172136031472765805 4722366482869645213696 Ns372p1063 Ns372p586 151474723 33554432 221 33554432 (@Ns372p1064 Ns372p586 RS373to384.d47 (Ns372p1066 rfl rfl) rfl) 

noncomputable def Ns372p1068 := nat_lit 6637998299337817468174336 

noncomputable def Ns372p1069 := nat_lit 787609601549779149579901665955391457332599358999661255865676711618642427661133670631563378785910321903725249624943582358757751278277398241 

noncomputable def Ns372p1070 := nat_lit 496464312146179064144933467883952937868338799267348819613344101711857758066992202955164253812150145682318736167698677845498343886561 

noncomputable def Ns372p1071 := nat_lit 4771444193658092599519250535118366791819124234966003270616997179811280268549899859253853564783900360542569954253463389908572859683809431265 

noncomputable def Ns372p1072 := BSN.cos_dyadic_bound_f 94331629431 68719476736 4 3 33554432 11531251 Ns372p1069 Ns372p830 Ns372p1070 Ns372p1071 Ns372p833 Ns372p1070 6603427 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 94331629431) qz379 0 3 Ns372p1069 Ns372p830 Ns372p1070 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 94331629431) qz380 0 3 Ns372p1071 Ns372p833 Ns372p1070 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1073 := @Ns372p1062 5760000 (Ns372p1067 rfl) (Enclosure.sfrac_false_div 151474723 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 151474723) qz367) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns372p1068) qz368) 226375608064910080 72057594037927936 Bool.false 6603427 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q2 151474723 33554432 226375608064910080 72057594037927936 0 Ns372p1068 Ns372p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 6603427 33554432 Ns372p1068 Ns372p98 94331629431 68719476736 11531251 11520000 (Ns372p1072 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p1074 := @Enclosure.Real.IsNear.inv_image qz164 6603427 33554432 1275893 188743680000 85248253 85254110 16777216 (@Enclosure.Real.IsNear.neg qz162 Bool.true 6603427 33554432 1275893 188743680000 (Ns372p1061 (Ns372p1073 rfl rfl) rfl)) 

noncomputable def Ns372p1075 := Ns372p1059 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz164) Bool.false 170502363 33554432 5857 33554432 (@Ns372p1060 5857 33554432 (Ns372p1074 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p1076 := @Enclosure.Real.IsNear.recentre' qz163 Bool.true 1554693 16777216 

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz349 qz346 qz480)

noncomputable def Ns372p1077 := @Enclosure.Real.IsNear.cos_image qz166 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 27910515)) qz411) Bool.true 27910515 16777216 

noncomputable def Ns372p1078 := nat_lit 263607361365808491766161977725 

noncomputable def Ns372p1079 := nat_lit 15446629408927641588911924615092209 

noncomputable def Ns372p1080 := @Enclosure.Real.IsNear.recentre' qz166 Bool.true Ns372p1078 Ns372p602 Ns372p1079 

noncomputable def Ns372p1081 := nat_lit 967140655691703339764940800000000000000 

noncomputable abbrev qz167 := qz480

noncomputable def Ns372p1082 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz167 884279719003555 140737488355328 1 500000000000000 298104045248095 

noncomputable abbrev qz481 := (@HSub.hSub Real Real Real qz588 qz673 qz666)

noncomputable abbrev qz168 := qz481

noncomputable def Ns372p1083 := @Enclosure.Real.IsNear.subLit_tf qz168 qz31 227735301070431 1125899906842624 2861962915 1125899906842624 1 16 

noncomputable abbrev qz482 := qz673

noncomputable abbrev qz169 := qz482

noncomputable def Ns372p1084 := @Enclosure.Real.IsNear.subLit_ff_n qz169 qz154 581193301418401 1125899906842624 1687557795 1125899906842624 24107951 33554432 35 33554432 

noncomputable def Ns372p1085 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz154 24107951 33554432 35 33554432 24107951 33554432 35 33554432 581193301418401 1125899906842624 

noncomputable def Ns372p1086 := nat_lit 76371807398030821443036979331278315391463062325766087057543866636375544143650251383997405640625 

noncomputable def Ns372p1087 := nat_lit 223467412853868856353824657752216487866652166869134097523588906250873471194749961181640625 

noncomputable def Ns372p1088 := nat_lit 461919328396327812168870887728602316373378195945836052105182757354852310576943006977170807240625 

noncomputable def Ns372p1089 := BSN.cos_dyadic_bound_t 27910515 16777216 4 3 16777216 5760000 Ns372p1086 Ns372p848 Ns372p1087 Ns372p1088 Ns372p851 Ns372p1087 1554693 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 27910515) (BSN.cosEvenQ 16777216) 0 3 Ns372p1086 Ns372p848 Ns372p1087 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 27910515) (BSN.cosOddQ 16777216) 0 3 Ns372p1088 Ns372p851 Ns372p1087 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1090 := @Ns372p1076 390114304 24159191040000 1554693 16777216 380971 23592960000 (@Ns372p1077 67 4194304 Bool.true 1554693 16777216 1 5760000 (@Ns372p1080 Ns372p1081 27910515 16777216 67 4194304 (@Ns372p1082 1125899906842624 2861962915 1125899906842624 Ns372p1078 Ns372p602 Ns372p1079 Ns372p1081 RS373to384.d47 (@Ns372p1083 0 1 4769664723969520 298104045248095 1125899906842624 2861962915 1125899906842624 (@Ns372p1084 7641528673767304200192 227735301070431 1125899906842624 2861962915 1125899906842624 (@Ns372p1085 1687557795 1125899906842624 (Ns372p1066 rfl rfl) (Ns372p1066 rfl rfl) rfl) (Ns372p1066 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 27910515 16777216) (BSN.cos_neg_of_bound 27910515 16777216 Bool.true 1554693 16777216 1 5760000 (Ns372p1089 rfl rfl)) rfl rfl) 

noncomputable def Ns372p1091 := @Ns372p1051 319100059157288462479 Ns372p972 (Ns372p1052 qz33 (@Enclosure.Real.IsNear.of_eq qz671 (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 5124523 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz153 (BSN.t_div_two_pi_nonneg qz152 721848 1000 qz155)) Ns372p1056) rfl) (@Ns372p1057 562949953421312 62211016178921 633318697598976000 (BSN.correction_mk qz154 (BSN.cos_two_pi_p_ne_zero_mk qz152 721848 1000 10 qz155 rfl rfl (@BSN.floor_sqrt_eq_dec qz152 721848 1000 10 qz155 rfl rfl rfl))) (@Ns372p1058 33554432 1554693 16777216 380971 23592960000 265078830239559 562949953421312 62211016178921 633318697598976000 Ns372p1075 (Ns372p1090 rfl) rfl)) 

noncomputable def Ns372p1092 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (hardyZApproximantRS₀ qz152) Bool.false 8491196269302322869395 9444732965739290427392 12231033112622028302479 Ns372p972 (@Eq.refl Real (hardyZApproximantRS₀ qz152)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) (@HMul.hMul Real Real Real qz5 qz667 (Zeta.RiemannSiegel.correction qz154))) Bool.false 8491196269302322869395 9444732965739290427392 12231033112622028302479 Ns372p972 (BSN.hardyZApproximantRS₀_eq qz152 10 (@BSN.floor_sqrt_eq_dec qz152 721848 1000 10 qz155 rfl rfl rfl)) (@Ns372p974 8491196269302322869395 9444732965739290427392 12231033112622028302479 Ns372p972 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 10)) Bool.false 69985609 67108864 75235 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) (Ns372p1050 (Ns372p1049 rfl rfl rfl rfl) rfl rfl)) (Ns372p1091 rfl) rfl rfl)) 

theorem RS373to384.d58 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz152) Bool.false 8491196269302322869395 9444732965739290427392 12231033112622028302479 Ns372p972 := Ns372p1092 

noncomputable def Ns372p1093 := nat_lit 643515908791149516218695680 

noncomputable abbrev qz770 := (Enclosure.sfrac Bool.false 723172 1000)

noncomputable abbrev qz674 := qz770

noncomputable abbrev qz483 := qz674

noncomputable abbrev qz170 := qz483

noncomputable abbrev qz771 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 723172 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz675 := qz771

noncomputable abbrev qz484 := qz675

noncomputable abbrev qz171 := qz484

noncomputable abbrev qz772 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 723172 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz676 := qz772

noncomputable abbrev qz485 := qz676

noncomputable abbrev qz172 := qz485

noncomputable abbrev qz677 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz171 qz9))

noncomputable def Ns372p1094 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) (@HMul.hMul Real Real Real qz5 qz677 (Zeta.RiemannSiegel.correction qz172)) 129717093 67108864 150739 134217728 675043533027236547 4611686018427387904 1134672635457859869337 Ns372p856 Ns372p1093 

noncomputable def Ns372p1095 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos BSN.quadSignNeg 9 10 723172 1000 198 268435456 134217728 4503599627370496 Bool.false 363468406893 2512 618095470 48 84886744 8 

noncomputable def Ns372p1096 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 723172 1000 95 149 268435456 134217728 4503599627370496 Bool.false 363468406893 2512 

noncomputable def Ns372p1097 := Ns372p1096 558195838 48 94906264 8 589812974 48 89478488 8 Bool.true 154270802 113369 Bool.true 145737979 Bool.true 240864328 14148475504056880 1 Bool.false 138683183 Bool.false Bool.false 209819671 Bool.true Bool.true 175178786 

noncomputable def Ns372p1098 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 723172 1000 37 33 268435456 134217728 4503599627370496 Bool.false 363468406893 2512 

noncomputable def Ns372p1099 := Ns372p1098 480971758 48 109588312 8 522351262 48 101459064 8 Bool.true 37944937 84083 Bool.false 41773870 Bool.true 366704817 14148475504056880 1 Bool.false 41605464 Bool.true Bool.false 262830276 Bool.true Bool.true 154270802 

noncomputable def Ns372p1100 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 723172 1000 223 121 268435456 134217728 4503599627370496 Bool.false 363468406893 2512 

noncomputable def Ns372p1101 := Ns372p1100 372130544 47 134217720 8 432030192 47 120047984 16 Bool.true 156424891 49480 Bool.false 324410624 Bool.false 15720063 14148475504056880 1 Bool.false 251012340 Bool.false Bool.false 15711079 Bool.true Bool.true 37944937 

noncomputable def Ns372p1102 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 723172 1000 542 356 268435456 134217728 4503599627370496 Bool.false 363468406893 2512 

noncomputable def Ns372p1103 := Ns372p1102 186065264 47 189812528 16 294906480 47 154981288 8 Bool.true 268435288 2567 Bool.false 372891675 Bool.false 90253475 14148475504056880 1 Bool.false 48497961 Bool.true Bool.false 253405319 Bool.false Bool.true 156424891 

noncomputable def Ns372p1104 := nat_lit 374325490683440938776131065704848145323901624867317 

noncomputable def Ns372p1105 := nat_lit 276453831689985305371059382744173125212884172800 

noncomputable def Ns372p1106 := nat_lit 94940120047206345448866153103360000 

noncomputable def Ns372p1107 := nat_lit 411948310866930045740394864595194347520 

noncomputable abbrev qz678 := (@Eq.refl Real qz770)

noncomputable abbrev qz486 := qz678

noncomputable abbrev qz173 := qz486

noncomputable def Ns372p1108 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz170 723172 1000 2091911966336 16000000 1446344 4000 2000 Ns372p1106 Ns372p1107 qz173 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns372p1109 := nat_lit 3925087257188797658181204083525268488311554701968717905920 

noncomputable abbrev qz679 := (@HSub.hSub Real Real Real qz737 qz738 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz739 (@Nat.cast Real Real.instNatCast 1446344))))

noncomputable abbrev qz487 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 723172 4000) (Real.log (Enclosure.sfrac Bool.false 2091911966336 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz679))

noncomputable abbrev qz680 := (Enclosure.sfrac Bool.false 723172 2000)

noncomputable abbrev qz174 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz487 qz680) (@HMul.hMul Real Real Real qz349 qz680 (Real.log Real.pi)))

noncomputable def Ns372p1110 := @Enclosure.Real.IsNear.addLit_ft_p qz174 (Enclosure.sfrac Bool.true Ns372p1106 Ns372p1107) 9528107827436642921 7036874417766400 28738302392580911 3072000000000000000000 Ns372p1106 Ns372p1107 0 1 Ns372p1109 

noncomputable def Ns372p1111 := nat_lit 799275615460976423002439680000 

noncomputable abbrev qz175 := (@HSub.hSub Real Real Real qz353 qz487 qz680)

noncomputable def Ns372p1112 := @Enclosure.Real.IsNear.subLit_ff_p qz175 (@HMul.hMul Real Real Real qz5 qz680 (Real.log Real.pi)) 62203994593636543501 35184372088832000 11900594615939 3000000000000000000 6944396713473 16777216000 180793 33554432000 Ns372p1111 9528107827436642921 7036874417766400 

noncomputable abbrev qz176 := qz487

noncomputable def Ns372p1113 := @Enclosure.Real.IsNear.subLit_ff_p qz176 qz680 74926170959748951053 35184372088832000 11900594615939 3000000000000000000 723172 2000 0 1 124407989187273087002000 62203994593636543501 35184372088832000 11900594615939 3000000000000000000 

noncomputable def Ns372p1114 := nat_lit 1349749902458493818447340818401329152 

noncomputable def Ns372p1115 := nat_lit 56969421740956998290112512 

noncomputable def Ns372p1116 := nat_lit 3085049696210843123061249931642142453700117159723418565452301145104190506538534558741435686132754725870114956671061351666382111396141052792083833868091041004010665740268984536693926791797878066719151148236800 

noncomputable def Ns372p1117 := nat_lit 121664496063319639840085041309920214976824213056055337464246658610947844638049614583009226336660780328025626625031244045426290599202195731607926091747664525351281430071612949968607087084816734640539151892480 

noncomputable def Ns372p1118 := nat_lit 3996188505808931363349896050323851086294421839166672619114051547032411128170644010356239026455062718602645059952368683391390995500152362464772920140602443840387606545215126131105784721223199385190400 

noncomputable def Ns372p1119 := BSN.log_dyadic_bound 1043335966336 3140487966336 9 8 Ns372p1116 134217728 46080000 Ns372p1117 Ns372p1118 92696857 4183823932672 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1043335966336) (BSN.artanhQ 3140487966336) 0 8 Ns372p1117 Ns372p1116 Ns372p1118 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz488 := (Real.log (Enclosure.sfrac Bool.false 2091911966336 16000000))

noncomputable def Ns372p1120 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 723172 4000) qz488 723172 4000 0 1 3316056783133943 281474976710656 48828161 2250000000000000 599519853993134956799 281474976710656000 8827789711673 2250000000000000000 (Enclosure.Real.IsNear.const Bool.false 723172 4000) (BSN.isNear_log_sfrac 2091911966336 16000000 3316056783133943 281474976710656 48828161 2250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2091911966336) qz356)) Bool.false Ns372p1115 Ns372p98 1000000737280000 46080000000000000000000 3316056783133943 281474976710656 48828161 2250000000000000 (BSN.log_rat_reduce_isNear 2091911966336 16000000 16 4183823932672 2097152000000 92696857 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns372p1119 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p1121 := BSN.arctan_dyadic_bound_f 1000 1446344 1 0 16777216 5760000 0 1 1 0 1 1 11599 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1446344) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1446344) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns372p1122 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1446344))) 884279719003555 562949953421312 1 2000000000000000 11599 16777216 1 5760000 14829222193632213204992 883890521146787 562949953421312 3125000009 18000000000000000 qz17 (Ns372p1121 rfl) rfl rfl 

noncomputable abbrev qz489 := (@HMul.hMul Real Real Real qz584 qz589 qz679)

noncomputable abbrev qz177 := qz489

noncomputable abbrev qz490 := qz679

noncomputable abbrev qz178 := qz490

noncomputable def Ns372p1123 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 723172 4000) qz488) qz177 599519853993134956799 281474976710656000 8827789711673 2250000000000000000 883890521146787 2251799813685248 3125000009 72000000000000000 Ns372p1114 74926170959748951053 35184372088832000 11900594615939 3000000000000000000 (Ns372p1120 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz178 1 4 0 1 883890521146787 562949953421312 3125000009 18000000000000000 883890521146787 2251799813685248 3125000009 72000000000000000 qz363 Ns372p1122 rfl) 

noncomputable def Ns372p1124 := @Ns372p1110 Ns372p1104 Ns372p1105 28738302392580911 3072000000000000000000 (@Ns372p1112 28738302392580911 3072000000000000000000 (Ns372p1113 (Ns372p1123 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 723172 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz680 (Real.log Real.pi) 723172 2000 0 1 38410761 33554432 1 67108864 6944396713473 16777216000 180793 33554432000 (Enclosure.Real.IsNear.const Bool.false 723172 2000) RS373to384.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns372p1106 Ns372p1107) 

noncomputable def Ns372p1125 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns372p1104 Ns372p1105 28738302392580911 3072000000000000000000 45433550861 33554432 315 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz364 qz174 (Enclosure.sfrac Bool.true Ns372p1106 Ns372p1107)) Bool.false Ns372p1104 Ns372p1105 28738302392580911 3072000000000000000000 Ns372p1108 (Ns372p1124 rfl rfl)) 

noncomputable def Ns372p1126 := nat_lit 7590567685203705443909632 

noncomputable def Ns372p1127 := nat_lit 3500958564199569043726282376526013581052123621687977210064069412314667274427893336415118298718933436612054614424002019674328278918758400000 

noncomputable def Ns372p1128 := nat_lit 2481609712616456501461416113476915416194359858957948337174318794250366335695224975598765687287206709843161702619662913536000000000000 

noncomputable def Ns372p1129 := nat_lit 17483101932746585698748093380960935373658787590682579404963945143447433978146357260083740548739808143965190166208853873015843505569792000000 

noncomputable def Ns372p1130 := BSN.sin_dyadic_bound_f 107868454580 68719476736 4 3 33554432 11531251 Ns372p1127 Ns372p111 Ns372p1128 Ns372p1129 Ns372p114 Ns372p1128 33554411 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107868454580) qz365 0 3 Ns372p1127 Ns372p111 Ns372p1128 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107868454580) qz366 0 3 Ns372p1129 Ns372p114 Ns372p1128 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1131 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz170) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 45433550861) qz367) Bool.false 45433550861 33554432 315 33554432 Bool.true 33554411 33554432 1 5760000 (Ns372p1125 rfl) (Enclosure.sfrac_false_div 45433550861 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 45433550861) qz367) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns372p1126) qz368) 226375608064910080 72057594037927936 Bool.false 33554411 33554432 215 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q1 45433550861 33554432 226375608064910080 72057594037927936 215 Ns372p1126 Ns372p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554411 33554432 Ns372p1126 Ns372p98 107868454580 68719476736 11531251 11520000 (Ns372p1130 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p1132 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns372p1104 Ns372p1105 28738302392580911 3072000000000000000000 363468406893 268435456 2512 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz364 qz174 (Enclosure.sfrac Bool.true Ns372p1106 Ns372p1107)) Bool.false Ns372p1104 Ns372p1105 28738302392580911 3072000000000000000000 Ns372p1108 (Ns372p1124 rfl rfl)) 

noncomputable def Ns372p1133 := Ns372p1103 49480 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 542 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 48497961 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 356 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 253405319 268435456) qz173 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) Bool.true 33554411 33554432 1804643 188743680000 268435288 268435456 2567 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 33554411 33554432 1804643 188743680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz170) qz170) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 33554411 33554432 1847954432 193273528320000 33554411 33554432 1804643 188743680000 (Ns372p1131 rfl rfl) rfl)) rfl) (Ns372p1132 rfl) RS373to384.d7 

noncomputable def Ns372p1134 := nat_lit 10426470968692460914254260800364884705838843130070626706642570321357448823995149615264420538748064321494140625 

noncomputable def Ns372p1135 := nat_lit 7227569082623454522914872561813013426929325220779790263225717627735561848569306476244986057281494140625 

noncomputable def Ns372p1136 := nat_lit 63160627059692038740068604910646389005593086991126440867215911450528077681741138330103586507995566657494140625 

noncomputable def Ns372p1137 := BSN.cos_dyadic_bound_f 372891675 268435456 4 3 268435456 134217728 Ns372p1134 Ns372p143 Ns372p1135 Ns372p1136 Ns372p146 Ns372p1135 48497961 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 372891675) qz371 0 3 Ns372p1134 Ns372p143 Ns372p1135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 372891675) qz372 0 3 Ns372p1136 Ns372p146 Ns372p1135 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1138 := nat_lit 578799076015152303485691111653094208551325865825403048693040275390625 

noncomputable def Ns372p1139 := nat_lit 4402622605678870586913168411634583690449678722717846832275390625 

noncomputable def Ns372p1140 := nat_lit 1736388422800245552715899508622459356486596698118763710385456275390625 

noncomputable def Ns372p1141 := BSN.cos_dyadic_bound_f 90253475 268435456 3 2 268435456 134217728 Ns372p1138 Ns372p159 Ns372p1139 Ns372p1140 Ns372p162 Ns372p1139 253405319 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 90253475) qz371 0 2 Ns372p1138 Ns372p159 Ns372p1139 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 90253475) qz372 0 2 Ns372p1140 Ns372p162 Ns372p1139 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1142 := nat_lit 15506174113455752324946158245134102530348968121351477958002854692934326595850745508274939422932465882209714176 

noncomputable def Ns372p1143 := nat_lit 1358753950552605624963502307034018040170319230467655523912999357747418029465556905627077995732848869376 

noncomputable def Ns372p1144 := nat_lit 77497080159254367149828020707351945529673216687601798370970450920380699990812452129984657373321425353793601536 

noncomputable def Ns372p1145 := BSN.sin_dyadic_bound_f 324410624 268435456 4 3 268435456 134217728 Ns372p1142 Ns372p134 Ns372p1143 Ns372p1144 Ns372p137 Ns372p1143 251012340 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 324410624) qz369 0 3 Ns372p1142 Ns372p134 Ns372p1143 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 324410624) qz370 0 3 Ns372p1144 Ns372p137 Ns372p1143 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1146 := nat_lit 61068482569159389300571112961 

noncomputable def Ns372p1147 := BSN.sin_dyadic_bound_f 15720063 268435456 2 1 268435456 134217728 Ns372p1146 Ns372p130 Ns372p1146 Ns372p1146 Ns372p131 Ns372p1146 15711079 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 15720063) qz369 0 1 Ns372p1146 Ns372p130 Ns372p1146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 15720063) qz370 0 1 Ns372p1146 Ns372p131 Ns372p1146 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1148 := Ns372p1101 84083 BSN.abs_quadSignPos (BSN.cos_quad_nat3 223 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 251012340 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 121 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 15711079 268435456) qz173 rfl rfl (Ns372p1133 RS373to384.d9 RS373to384.d11 RS373to384.d13 RS373to384.d17 (Ns372p1137 rfl rfl) (Ns372p1141 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns372p1132 rfl) RS373to384.d19 RS373to384.d21 RS373to384.d23 RS373to384.d25 RS373to384.d17 (Ns372p1145 rfl rfl) (Ns372p1147 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns372p1149 := nat_lit 3045221192731482141916773610000 

noncomputable def Ns372p1150 := BSN.sin_dyadic_bound_f 41773870 268435456 2 1 268435456 134217728 Ns372p1149 Ns372p130 Ns372p1149 Ns372p1149 Ns372p131 Ns372p1149 41605464 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 41773870) qz369 0 1 Ns372p1149 Ns372p130 Ns372p1149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 41773870) qz370 0 1 Ns372p1149 Ns372p131 Ns372p1149 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1151 := nat_lit 25327045621878483171581427001549148994588651505967431412774265445481941724850628100013476209794278758863018561 

noncomputable def Ns372p1152 := nat_lit 5912884261102135127276622201755714343098441733315159254534470850326262095585157996003123659840737450561 

noncomputable def Ns372p1153 := nat_lit 126545151921665200733304093043775391590666687226768126825328184493484924538243958855235659616375504588621421121 

noncomputable def Ns372p1154 := BSN.sin_dyadic_bound_f 366704817 268435456 4 3 268435456 134217728 Ns372p1151 Ns372p134 Ns372p1152 Ns372p1153 Ns372p137 Ns372p1152 262830276 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 366704817) qz369 0 3 Ns372p1151 Ns372p134 Ns372p1152 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 366704817) qz370 0 3 Ns372p1153 Ns372p137 Ns372p1152 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1155 := Ns372p1099 113369 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 37 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 41605464 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 33 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 262830276 268435456) qz173 rfl rfl (Ns372p1148 rfl rfl) (Ns372p1132 rfl) RS373to384.d27 RS373to384.d29 RS373to384.d31 RS373to384.d33 RS373to384.d17 (Ns372p1150 rfl rfl) (Ns372p1154 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p1156 := nat_lit 7083448644113123602090368672984526567321913205084616384051386983599585 

noncomputable def Ns372p1157 := nat_lit 203508213443853438829670992892773957641443224608106974797388795361 

noncomputable def Ns372p1158 := nat_lit 18551559816522128909430955628590028899435496057619867880270627279949281 

noncomputable def Ns372p1159 := BSN.sin_dyadic_bound_f 145737979 268435456 3 2 268435456 134217728 Ns372p1156 Ns372p120 Ns372p1157 Ns372p1158 Ns372p123 Ns372p1157 138683183 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 145737979) qz369 0 2 Ns372p1156 Ns372p120 Ns372p1157 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 145737979) qz370 0 2 Ns372p1158 Ns372p123 Ns372p1157 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1160 := nat_lit 52859655777336945184903178319536549408373108446711277489457025159004160 

noncomputable def Ns372p1161 := nat_lit 11328695040338544699823138538447547898675198486074320724017740251136 

noncomputable def Ns372p1162 := nat_lit 138423613910579070221422896231628714325331714658123511191215227646509056 

noncomputable def Ns372p1163 := BSN.sin_dyadic_bound_f 240864328 268435456 3 2 268435456 134217728 Ns372p1160 Ns372p120 Ns372p1161 Ns372p1162 Ns372p123 Ns372p1161 209819671 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 240864328) qz369 0 2 Ns372p1160 Ns372p120 Ns372p1161 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 240864328) qz370 0 2 Ns372p1162 Ns372p123 Ns372p1161 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1164 := Ns372p1097 138957 BSN.abs_quadSignPos (BSN.cos_quad_nat3 95 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 138683183 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 149 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 209819671 268435456) qz173 rfl rfl (Ns372p1155 rfl) (Ns372p1132 rfl) RS373to384.d35 RS373to384.d37 RS373to384.d39 RS373to384.d41 RS373to384.d17 (Ns372p1159 rfl rfl) (Ns372p1163 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p1165 := nat_lit 1151731467101041135252034323761 

noncomputable def Ns372p1166 := BSN.cos_dyadic_bound_f 32759541 268435456 2 1 268435456 134217728 Ns372p1165 Ns372p427 Ns372p1165 Ns372p1165 Ns372p428 Ns372p1165 266438968 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 32759541) qz371 0 1 Ns372p1165 Ns372p427 Ns372p1165 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 32759541) qz372 0 1 Ns372p1165 Ns372p428 Ns372p1165 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1167 := Ns372p1095 Bool.true 175178786 138957 Bool.true 32759541 14148475504056880 1 Bool.false 266438968 Bool.true Bool.true 259434186 150739 BSN.abs_quadSignNeg qz595 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 266438968 268435456) qz173 rfl (Ns372p1164 rfl) (Ns372p1132 rfl) RS373to384.d43 RS373to384.d45 RS373to384.d17 (Ns372p1166 rfl rfl) rfl 

noncomputable def Ns372p1168 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) 259434186 268435456 150739 268435456 259434186 268435456 150739 268435456 139282668041797632 129717093 67108864 150739 134217728 (Ns372p1167 rfl rfl rfl rfl) 

noncomputable def Ns372p1169 := @Enclosure.Real.IsNear.mulLit_ff qz677 (Zeta.RiemannSiegel.correction qz172) 40017 131072 1 16777216 16868919035091 35184372088832 221373360214081 1583296743997440000 675043533027236547 4611686018427387904 

noncomputable abbrev qz681 := (@HPow.hPow Real Real Real qz7 qz171 qz9)

noncomputable def Ns372p1170 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz681 1 1 0 1 40017 131072 1 16777216 40017 131072 1 16777216 

noncomputable def Ns372p1171 := @Enclosure.Real.IsNear.sqrt_image qz171 965498439929 8388608000 180793 8388608000 179990960 179990994 16777216 (@Enclosure.Real.IsNear.of_eq qz171 (@HMul.hMul Real Real Real qz5 qz170 qz3) Bool.false 965498439929 8388608000 180793 8388608000 (BSN.t_div_two_pi_mk qz170 723172 1000 qz173) (@Enclosure.Real.IsNear.mulLit_ff qz170 qz3 723172 1000 0 1 5340353 33554432 1 33554432 965498439929 8388608000 180793 8388608000 (Enclosure.Real.IsNear.const Bool.false 723172 1000) RS373to384.d48 rfl)) 

noncomputable abbrev qz773 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 723172 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz682 := qz773

noncomputable abbrev qz491 := qz682

noncomputable abbrev qz179 := qz491

noncomputable def Ns372p1172 := @Enclosure.Real.IsNear.sqrt_image qz179 179990977 16777216 17 16777216 54952226 54952232 16777216 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 359981954 33554432 34 33554432 179990977 16777216 17 16777216 (Ns372p1171 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns372p1173 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz179) 54952229 16777216 3 16777216 5122175 5122177 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz179) Bool.false 109904458 33554432 6 33554432 54952229 16777216 3 16777216 (Ns372p1172 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns372p1174 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 10244352 33554432 2 33554432 40017 131072 1 16777216 (Ns372p1173 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz492 := (@HMul.hMul Real Real Real qz584 qz582 qz676)

noncomputable abbrev qz180 := (Real.cos qz492)

noncomputable abbrev qz683 := (@HMul.hMul Real Real Real qz733 qz772 qz772)

noncomputable abbrev qz493 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz683 qz676) qz600)

noncomputable abbrev qz181 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz493))

noncomputable def Ns372p1175 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz172) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz180) qz181) Bool.false 16868919035091 

noncomputable def Ns372p1176 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz180) qz181 123421783 16777216 747 

noncomputable abbrev qz182 := (@Neg.neg Real Real.instNeg (Real.cos qz492))

noncomputable def Ns372p1177 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz180) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz182)) Bool.true 123421783 16777216 747 2097152 (BSN.inv_eq_neg_inv_neg qz180) 

noncomputable def Ns372p1178 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz182) Bool.false 246843566 33554432 11952 33554432 123421783 16777216 

noncomputable def Ns372p1179 := @Enclosure.Real.IsNear.recentre' qz180 Bool.true 4561188 33554432 1271954432 193273528320000 1140297 8388608 1242143 188743680000 

noncomputable abbrev qz183 := qz492

noncomputable def Ns372p1180 := @Enclosure.Real.IsNear.cos_image qz183 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 76773091) qz411) Bool.false 76773091 16777216 215 33554432 Bool.true 4561188 33554432 1 

noncomputable def Ns372p1181 := nat_lit 458763282058707611559490103 

noncomputable def Ns372p1182 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz172 884279719003555 140737488355328 1 500000000000000 12218817 16777216 17 16777216 10804852063315860894435 2361183241434822606848 Ns372p1181 

noncomputable def Ns372p1183 := @Enclosure.Real.IsNear.subLit_ff_p qz179 qz1 179990977 16777216 17 16777216 10 1 0 1 12218817 12218817 16777216 17 

noncomputable def Ns372p1184 := @Ns372p1183 16777216 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 359981954 33554432 34 33554432 179990977 16777216 17 16777216 (Ns372p1171 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns372p1185 := @Enclosure.Real.IsNear.recentre' qz183 Bool.false 10804852063315860894435 2361183241434822606848 Ns372p1181 Ns372p179 76773091 16777216 215 33554432 (@Ns372p1182 Ns372p179 RS373to384.d47 (Ns372p1184 rfl rfl) rfl) 

noncomputable def Ns372p1186 := nat_lit 3468263501357120898465792 

noncomputable def Ns372p1187 := nat_lit 939522274599262904981955282002485906852011208946092478052107388891778286068658954393093920886067328136318910790420565797226629347781275361 

noncomputable def Ns372p1188 := nat_lit 841680699342557276251238435283779830235646739019399267234377506958776002846519803176343980222117723152184135622271502106232120045281 

noncomputable def Ns372p1189 := nat_lit 5690212231687880159837608396806198672656255085234326204238257427195345785818739555291948131014468182986438894487666976517230556135657991905 

noncomputable def Ns372p1190 := BSN.cos_dyadic_bound_f 98573977463 68719476736 4 3 33554432 11531251 Ns372p1187 Ns372p830 Ns372p1188 Ns372p1189 Ns372p833 Ns372p1188 4561188 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 98573977463) qz379 0 3 Ns372p1187 Ns372p830 Ns372p1188 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 98573977463) qz380 0 3 Ns372p1189 Ns372p833 Ns372p1188 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1191 := @Ns372p1180 5760000 (Ns372p1185 rfl) (Enclosure.sfrac_false_div 76773091 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 76773091) qz411) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns372p1186) qz412) 226375608064910080 72057594037927936 Bool.false 4561188 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q2 76773091 16777216 226375608064910080 72057594037927936 0 Ns372p1186 Ns372p403 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 4561188 33554432 Ns372p1186 Ns372p403 98573977463 68719476736 11531251 11520000 (Ns372p1190 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p1192 := @Enclosure.Real.IsNear.inv_image qz182 1140297 8388608 1242143 188743680000 123415807 123427759 16777216 (@Enclosure.Real.IsNear.neg qz180 Bool.true 1140297 8388608 1242143 188743680000 (Ns372p1179 (Ns372p1191 rfl rfl) rfl)) 

noncomputable def Ns372p1193 := Ns372p1177 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz182) Bool.false 123421783 16777216 747 2097152 (@Ns372p1178 747 2097152 (Ns372p1192 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p1194 := @Enclosure.Real.IsNear.recentre' qz181 Bool.true 1093416 16777216 

noncomputable abbrev qz184 := (@HMul.hMul Real Real Real qz349 qz346 qz493)

noncomputable def Ns372p1195 := @Enclosure.Real.IsNear.cos_image qz184 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 54895561)) qz367) Bool.true 54895561 33554432 

noncomputable def Ns372p1196 := nat_lit 64809240172581399205823508445 

noncomputable def Ns372p1197 := nat_lit 18907867650836815813182090221148821 

noncomputable def Ns372p1198 := @Enclosure.Real.IsNear.recentre' qz184 Bool.true Ns372p1196 Ns372p956 Ns372p1197 

noncomputable abbrev qz185 := qz493

noncomputable def Ns372p1199 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz185 884279719003555 140737488355328 1 500000000000000 73290429238399 

noncomputable abbrev qz494 := (@HSub.hSub Real Real Real qz588 qz683 qz676)

noncomputable abbrev qz186 := qz494

noncomputable def Ns372p1200 := @Enclosure.Real.IsNear.subLit_tf qz186 qz31 55698243193983 281474976710656 700652739 281474976710656 1 16 

noncomputable abbrev qz495 := qz683

noncomputable abbrev qz187 := qz495

noncomputable def Ns372p1201 := @Enclosure.Real.IsNear.subLit_ff_n qz187 qz172 149299488879489 281474976710656 415440067 281474976710656 12218817 16777216 17 16777216 

noncomputable def Ns372p1202 := @Enclosure.Real.IsNear.mulLit_ff qz172 qz172 12218817 16777216 17 16777216 12218817 16777216 17 16777216 149299488879489 281474976710656 

noncomputable def Ns372p1203 := nat_lit 292497979010054583112458170498786972653160796779144326706564532988482824664795468716485699379052001 

noncomputable def Ns372p1204 := nat_lit 748939492474363673011521629778411306077482174533312227980300038362110716064487140097801764321 

noncomputable def Ns372p1205 := nat_lit 1769460834540828425780640806785226112974678467471061077476721332813590842166940152316307092609875425 

noncomputable def Ns372p1206 := BSN.cos_dyadic_bound_t 54895561 33554432 4 3 16777216 5760000 Ns372p1203 Ns372p329 Ns372p1204 Ns372p1205 Ns372p332 Ns372p1204 1093416 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 54895561) (BSN.cosEvenQ 33554432) 0 3 Ns372p1203 Ns372p329 Ns372p1204 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 54895561) (BSN.cosOddQ 33554432) 0 3 Ns372p1205 Ns372p332 Ns372p1204 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1207 := @Ns372p1194 1531657216 96636764160000 136677 2097152 1495759 94371840000 (@Ns372p1195 263 16777216 Bool.true 1093416 16777216 1 5760000 (@Ns372p1198 Ns372p200 54895561 33554432 263 16777216 (@Ns372p1199 281474976710656 700652739 281474976710656 Ns372p1196 Ns372p956 Ns372p1197 Ns372p200 RS373to384.d47 (@Ns372p1200 0 1 1172646867814384 73290429238399 281474976710656 700652739 281474976710656 (@Ns372p1201 934461456885982691328 55698243193983 281474976710656 700652739 281474976710656 (@Ns372p1202 415440067 281474976710656 (Ns372p1184 rfl rfl) (Ns372p1184 rfl rfl) rfl) (Ns372p1184 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 54895561 33554432) (BSN.cos_neg_of_bound 54895561 33554432 Bool.true 1093416 16777216 1 5760000 (Ns372p1206 rfl rfl)) rfl rfl) 

noncomputable def Ns372p1208 := @Ns372p1169 1134672635457859869337 Ns372p856 (Ns372p1170 qz33 (@Enclosure.Real.IsNear.of_eq qz681 (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 40017 131072 1 16777216 (BSN.rpow_neg_quarter_mk qz171 (BSN.t_div_two_pi_nonneg qz170 723172 1000 qz173)) Ns372p1174) rfl) (@Ns372p1175 35184372088832 221373360214081 1583296743997440000 (BSN.correction_mk qz172 (BSN.cos_two_pi_p_ne_zero_mk qz170 723172 1000 10 qz173 rfl rfl (@BSN.floor_sqrt_eq_dec qz170 723172 1000 10 qz173 rfl rfl rfl))) (@Ns372p1176 2097152 136677 2097152 1495759 94371840000 16868919035091 35184372088832 221373360214081 1583296743997440000 Ns372p1193 (Ns372p1207 rfl) rfl)) 

noncomputable def Ns372p1209 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (hardyZApproximantRS₀ qz170) Bool.true 9589134287702284995 4611686018427387904 30967743622136623389337 Ns372p856 (@Eq.refl Real (hardyZApproximantRS₀ qz170)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) (@HMul.hMul Real Real Real qz5 qz677 (Zeta.RiemannSiegel.correction qz172))) Bool.true 9589134287702284995 4611686018427387904 30967743622136623389337 Ns372p856 (BSN.hardyZApproximantRS₀_eq qz170 10 (@BSN.floor_sqrt_eq_dec qz170 723172 1000 10 qz173 rfl rfl rfl)) (@Ns372p1094 9589134287702284995 4611686018427387904 30967743622136623389337 Ns372p856 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 10)) Bool.true 129717093 67108864 150739 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) (Ns372p1168 (Ns372p1167 rfl rfl rfl rfl) rfl rfl)) (Ns372p1208 rfl) rfl rfl)) 

theorem RS373to384.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz170) Bool.true 9589134287702284995 4611686018427387904 30967743622136623389337 Ns372p856 := Ns372p1209 

noncomputable def Ns372p1210 := nat_lit 175493047559978862963115163648 

noncomputable abbrev qz774 := (Enclosure.sfrac Bool.false 724496 1000)

noncomputable abbrev qz684 := qz774

noncomputable abbrev qz496 := qz684

noncomputable abbrev qz188 := qz496

noncomputable abbrev qz775 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 724496 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz685 := qz775

noncomputable abbrev qz497 := qz685

noncomputable abbrev qz189 := qz497

noncomputable abbrev qz776 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 724496 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz686 := qz776

noncomputable abbrev qz498 := qz686

noncomputable abbrev qz190 := qz498

noncomputable abbrev qz687 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz189 qz9))

noncomputable def Ns372p1211 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) (@HMul.hMul Real Real Real qz5 qz687 (Zeta.RiemannSiegel.correction qz190)) 57168779 134217728 151011 134217728 703922497154795900487 4722366482869645213696 85860342443806967797 1062532458645670173081600 Ns372p1210 

noncomputable def Ns372p1212 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos BSN.quadSignNeg 9 10 724496 1000 198 268435456 134217728 4503599627370496 Bool.false 364311913235 2517 618095470 48 84886744 8 

noncomputable def Ns372p1213 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 724496 1000 95 149 268435456 134217728 4503599627370496 Bool.false 364311913235 2517 

noncomputable def Ns372p1214 := Ns372p1213 558195838 48 94906264 8 589812974 48 89478488 8 Bool.false 182633899 113573 Bool.true 41282927 Bool.true 178270364 14148475504056880 1 Bool.false 41120384 Bool.false Bool.false 165452242 Bool.true Bool.false 142021400 

noncomputable def Ns372p1215 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 724496 1000 37 33 268435456 134217728 4503599627370496 Bool.false 364311913235 2517 

noncomputable def Ns372p1216 := Ns372p1215 480971758 48 109588312 8 522351262 48 101459064 8 Bool.false 342988997 84233 Bool.false 248473605 Bool.true 214791546 14148475504056880 1 Bool.false 214480883 Bool.true Bool.false 192593891 Bool.true Bool.false 182633899 

noncomputable def Ns372p1217 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 724496 1000 224 121 268435456 134217728 4503599627370496 Bool.false 364311913235 2517 

noncomputable def Ns372p1218 := Ns372p1217 372130544 47 134217720 8 432030192 47 120047984 16 Bool.false 369630755 49567 Bool.false 253558697 Bool.false 287218431 14148475504056880 1 Bool.false 157325573 Bool.false Bool.false 235468112 Bool.true Bool.false 342988997 

noncomputable def Ns372p1219 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 724496 1000 544 357 268435456 134217728 4503599627370496 Bool.false 364311913235 2517 

noncomputable def Ns372p1220 := Ns372p1219 186065264 47 189812528 16 294906480 47 154981288 8 Bool.false 268435432 2567 Bool.false 126732751 Bool.false 121646209 14148475504056880 1 Bool.false 239070725 Bool.false Bool.false 117525193 Bool.true Bool.false 369630755 

noncomputable def Ns372p1221 := nat_lit 485548271083522754418522055469653448447642370421778843 

noncomputable def Ns372p1222 := nat_lit 357765878147249594248331190179023091755558895616000 

noncomputable def Ns372p1223 := nat_lit 95812400588126738433372876308480000 

noncomputable def Ns372p1224 := nat_lit 416494298432080068448944005857947156480 

noncomputable abbrev qz688 := (@Eq.refl Real qz774)

noncomputable abbrev qz499 := qz688

noncomputable abbrev qz191 := qz499

noncomputable def Ns372p1225 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz188 724496 1000 2099578816064 16000000 1448992 4000 2000 Ns372p1223 Ns372p1224 qz191 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns372p1226 := nat_lit 636417829874594944671445228545184167949293807759233965096960 

noncomputable abbrev qz689 := (@HSub.hSub Real Real Real qz737 qz738 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz739 (@Nat.cast Real Real.instNatCast 1448992))))

noncomputable abbrev qz500 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 724496 4000) (Real.log (Enclosure.sfrac Bool.false 2099578816064 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz689))

noncomputable abbrev qz690 := (Enclosure.sfrac Bool.false 724496 2000)

noncomputable abbrev qz192 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz500 qz690) (@HMul.hMul Real Real Real qz349 qz690 (Real.log Real.pi)))

noncomputable def Ns372p1227 := @Enclosure.Real.IsNear.addLit_ft_p qz192 (Enclosure.sfrac Bool.true Ns372p1223 Ns372p1224) 1528035173940206736427 1125899906842624000 21593005190255957 2304000000000000000000 Ns372p1223 Ns372p1224 0 1 Ns372p1226 

noncomputable def Ns372p1228 := nat_lit 6409044042198104875422711808000 

noncomputable abbrev qz193 := (@HSub.hSub Real Real Real qz353 qz500 qz690)

noncomputable def Ns372p1229 := @Enclosure.Real.IsNear.subLit_ff_p qz193 (@HMul.hMul Real Real Real qz5 qz690 (Real.log Real.pi)) 1994918968086157562923 1125899906842624000 35766433963097 9000000000000000000 1739277668841 4194304000 45281 8388608000 Ns372p1228 1528035173940206736427 1125899906842624000 

noncomputable abbrev qz194 := qz500

noncomputable def Ns372p1230 := @Enclosure.Real.IsNear.subLit_ff_p qz194 qz690 96110958301603376867 45035996273704960 35766433963097 9000000000000000000 724496 2000 0 1 159593517446892605033840 1994918968086157562923 1125899906842624000 35766433963097 9000000000000000000 

noncomputable def Ns372p1231 := nat_lit 216422637996661123583536236662358016 

noncomputable def Ns372p1232 := nat_lit 56987112195342139077427200 

noncomputable def Ns372p1233 := BSN.log_dyadic_bound 2426816064 4196730816064 1 0 1 134217728 46080000 0 1 155226 4199157632128 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 2426816064) (BSN.artanhQ 4196730816064) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz501 := (Real.log (Enclosure.sfrac Bool.false 2099578816064 16000000))

noncomputable def Ns372p1234 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 724496 4000) qz501 724496 4000 0 1 53073384049667175 4503599627370496 195312653 9000000000000000 96128636126119174047 45035996273704960 8843952240493 2250000000000000000 (Enclosure.Real.IsNear.const Bool.false 724496 4000) (BSN.isNear_log_sfrac 2099578816064 16000000 53073384049667175 4503599627370496 195312653 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2099578816064) qz356)) Bool.false Ns372p1232 Ns372p98 1000000783360000 46080000000000000000000 53073384049667175 4503599627370496 195312653 9000000000000000 (BSN.log_rat_reduce_isNear 2099578816064 16000000 17 4199157632128 4194304000000 155226 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns372p1233 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p1235 := BSN.arctan_dyadic_bound_f 1000 1448992 1 0 16777216 5760000 0 1 1 0 1 1 11578 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1448992) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1448992) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns372p1236 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1448992))) 884279719003555 562949953421312 1 2000000000000000 11578 16777216 1 5760000 14829234015581235052544 883891225789859 562949953421312 3125000009 18000000000000000 qz17 (Ns372p1235 rfl) rfl rfl 

noncomputable abbrev qz502 := (@HMul.hMul Real Real Real qz584 qz589 qz689)

noncomputable abbrev qz195 := qz502

noncomputable abbrev qz503 := qz689

noncomputable abbrev qz196 := qz503

noncomputable def Ns372p1237 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 724496 4000) qz501) qz195 96128636126119174047 45035996273704960 8843952240493 2250000000000000000 883891225789859 2251799813685248 3125000009 72000000000000000 Ns372p1231 96110958301603376867 45035996273704960 35766433963097 9000000000000000000 (Ns372p1234 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz196 1 4 0 1 883891225789859 562949953421312 3125000009 18000000000000000 883891225789859 2251799813685248 3125000009 72000000000000000 qz363 Ns372p1236 rfl) 

noncomputable def Ns372p1238 := @Ns372p1227 Ns372p1221 Ns372p1222 21593005190255957 2304000000000000000000 (@Ns372p1229 21593005190255957 2304000000000000000000 (Ns372p1230 (Ns372p1237 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 724496 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz690 (Real.log Real.pi) 724496 2000 0 1 38410761 33554432 1 67108864 1739277668841 4194304000 45281 8388608000 (Enclosure.Real.IsNear.const Bool.false 724496 2000) RS373to384.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns372p1223 Ns372p1224) 

noncomputable def Ns372p1239 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz188) Bool.false Ns372p1221 Ns372p1222 21593005190255957 2304000000000000000000 22769494577 16777216 315 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz188) (@HAdd.hAdd Real Real Real qz364 qz192 (Enclosure.sfrac Bool.true Ns372p1223 Ns372p1224)) Bool.false Ns372p1221 Ns372p1222 21593005190255957 2304000000000000000000 Ns372p1225 (Ns372p1238 rfl rfl)) 

noncomputable def Ns372p1240 := nat_lit 3797008608375274685333504 

noncomputable def Ns372p1241 := nat_lit 3507339734315707819278487240289123383485127572458975437095864899118502889603330087652678290547280646802857244357443395644002790707982996241 

noncomputable def Ns372p1242 := nat_lit 2495176792417658716169552913516435838546394895410339839359425233463394089619261154344815223249929566753002923278080561086772808749841 

noncomputable def Ns372p1243 := nat_lit 17514928780311262465455646504672065373255040513985790753158069790079160172403309033891475578065540263444056805745556609281136774954313814801 

noncomputable def Ns372p1244 := BSN.sin_dyadic_bound_f 107917475371 68719476736 4 3 33554432 11531251 Ns372p1241 Ns372p111 Ns372p1242 Ns372p1243 Ns372p114 Ns372p1242 33554429 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107917475371) qz365 0 3 Ns372p1241 Ns372p111 Ns372p1242 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107917475371) qz366 0 3 Ns372p1243 Ns372p114 Ns372p1242 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1245 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz188) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 22769494577) qz411) Bool.false 22769494577 16777216 315 33554432 Bool.false 33554429 33554432 1 5760000 (Ns372p1239 rfl) (Enclosure.sfrac_false_div 22769494577 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 22769494577) qz411) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns372p1240) qz412) 226375608064910080 72057594037927936 Bool.false 33554429 33554432 215 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 22769494577 16777216 226375608064910080 72057594037927936 215 Ns372p1240 Ns372p403 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554429 33554432 Ns372p1240 Ns372p403 107917475371 68719476736 11531251 11520000 (Ns372p1244 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p1246 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz188) Bool.false Ns372p1221 Ns372p1222 21593005190255957 2304000000000000000000 364311913235 268435456 2517 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz188) (@HAdd.hAdd Real Real Real qz364 qz192 (Enclosure.sfrac Bool.true Ns372p1223 Ns372p1224)) Bool.false Ns372p1221 Ns372p1222 21593005190255957 2304000000000000000000 Ns372p1225 (Ns372p1238 rfl rfl)) 

noncomputable def Ns372p1247 := Ns372p1220 49567 BSN.abs_quadSignPos (BSN.cos_quad_nat0 544 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 239070725 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 357 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 117525193 268435456) qz191 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 1) Bool.false 33554429 33554432 1804643 188743680000 268435432 268435456 2567 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz188)) Bool.false 33554429 33554432 1804643 188743680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz188) qz188) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz188)) Bool.false 33554429 33554432 1847954432 193273528320000 33554429 33554432 1804643 188743680000 (Ns372p1245 rfl rfl) rfl)) rfl) (Ns372p1246 rfl) RS373to384.d7 

noncomputable def Ns372p1248 := nat_lit 2250282734388272779973786721331179099972420594528680381509463209553281 

noncomputable def Ns372p1249 := nat_lit 66544305670156581907704095489374162426361218178024551709408112001 

noncomputable def Ns372p1250 := nat_lit 6750715114553478026757544755802558551592409061149685095424970812435841 

noncomputable def Ns372p1251 := BSN.cos_dyadic_bound_f 126732751 268435456 3 2 268435456 134217728 Ns372p1248 Ns372p159 Ns372p1249 Ns372p1250 Ns372p162 Ns372p1249 239070725 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 126732751) qz371 0 2 Ns372p1248 Ns372p159 Ns372p1249 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 126732751) qz372 0 2 Ns372p1250 Ns372p162 Ns372p1249 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1252 := nat_lit 3438283428763625748718205185067100687383694322561267778100392887870465 

noncomputable def Ns372p1253 := nat_lit 47950002317287719699035386415176719889964066261081866329608709121 

noncomputable def Ns372p1254 := nat_lit 9004950394377172780811024665502496276077472807743659572003162006512641 

noncomputable def Ns372p1255 := BSN.sin_dyadic_bound_f 121646209 268435456 3 2 268435456 134217728 Ns372p1252 Ns372p120 Ns372p1253 Ns372p1254 Ns372p123 Ns372p1253 117525193 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 121646209) qz369 0 2 Ns372p1252 Ns372p120 Ns372p1253 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 121646209) qz370 0 2 Ns372p1254 Ns372p123 Ns372p1253 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1256 := nat_lit 36073525232402605262444856812111723945552994439194303147495357570047041 

noncomputable def Ns372p1257 := nat_lit 17085515653186269798509513244875976790093493302774432695738137271361 

noncomputable def Ns372p1258 := nat_lit 108186404665901443247737551409845419883078796330977360577094596435598401 

noncomputable def Ns372p1259 := BSN.cos_dyadic_bound_f 253558697 268435456 3 2 268435456 134217728 Ns372p1256 Ns372p159 Ns372p1257 Ns372p1258 Ns372p162 Ns372p1257 157325573 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 253558697) qz371 0 2 Ns372p1256 Ns372p159 Ns372p1257 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 253558697) qz372 0 2 Ns372p1258 Ns372p162 Ns372p1257 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1260 := nat_lit 106900248216780247639769367197302128438590036351118050778816951387367425 

noncomputable def Ns372p1261 := nat_lit 46312523262737787882697383506750961245871176744326394670264927856641 

noncomputable def Ns372p1262 := nat_lit 279901858387237168352347784991066072925718684728675509305530634226575361 

noncomputable def Ns372p1263 := BSN.sin_dyadic_bound_f 287218431 268435456 3 2 268435456 134217728 Ns372p1260 Ns372p120 Ns372p1261 Ns372p1262 Ns372p123 Ns372p1261 235468112 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 287218431) qz369 0 2 Ns372p1260 Ns372p120 Ns372p1261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 287218431) qz370 0 2 Ns372p1262 Ns372p123 Ns372p1261 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1264 := Ns372p1218 84233 BSN.abs_quadSignPos (BSN.cos_quad_nat0 224 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 157325573 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 121 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 235468112 268435456) qz191 rfl rfl (Ns372p1247 RS373to384.d9 RS373to384.d11 RS373to384.d13 RS373to384.d17 (Ns372p1251 rfl rfl) (Ns372p1255 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns372p1246 rfl) RS373to384.d19 RS373to384.d21 RS373to384.d23 RS373to384.d25 RS373to384.d17 (Ns372p1259 rfl rfl) (Ns372p1263 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns372p1265 := nat_lit 59864279856965817030706703192016242146521737718895567033522970225030625 

noncomputable def Ns372p1266 := nat_lit 14529212920411290261262370569715742524194183754268669370016000390625 

noncomputable def Ns372p1267 := nat_lit 156763876137801235848570750236262999181565379632933859623103943731590625 

noncomputable def Ns372p1268 := BSN.sin_dyadic_bound_f 248473605 268435456 3 2 268435456 134217728 Ns372p1265 Ns372p120 Ns372p1266 Ns372p1267 Ns372p123 Ns372p1266 214480883 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 248473605) qz369 0 2 Ns372p1265 Ns372p120 Ns372p1266 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 248473605) qz370 0 2 Ns372p1267 Ns372p123 Ns372p1266 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1269 := nat_lit 33424806773686665560293139160304786664707105203818200562128539554914560 

noncomputable def Ns372p1270 := nat_lit 4530409626367123616387931131494220338104826371620231257390703943936 

noncomputable def Ns372p1271 := nat_lit 87533825648831910648245974483728212527018820100636473478777066266009856 

noncomputable def Ns372p1272 := BSN.sin_dyadic_bound_f 214791546 268435456 3 2 268435456 134217728 Ns372p1269 Ns372p120 Ns372p1270 Ns372p1271 Ns372p123 Ns372p1270 192593891 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 214791546) qz369 0 2 Ns372p1269 Ns372p120 Ns372p1270 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 214791546) qz370 0 2 Ns372p1271 Ns372p123 Ns372p1270 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1273 := Ns372p1216 113573 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 37 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 214480883 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 33 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 192593891 268435456) qz191 rfl rfl (Ns372p1264 rfl rfl) (Ns372p1246 rfl) RS373to384.d27 RS373to384.d29 RS373to384.d31 RS373to384.d33 RS373to384.d17 (Ns372p1268 rfl rfl) (Ns372p1272 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p1274 := nat_lit 2904570528664965941566559154241 

noncomputable def Ns372p1275 := BSN.sin_dyadic_bound_f 41282927 268435456 2 1 268435456 134217728 Ns372p1274 Ns372p130 Ns372p1274 Ns372p1274 Ns372p131 Ns372p1274 41120384 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 41282927) qz369 0 1 Ns372p1274 Ns372p130 Ns372p1274 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 41282927) qz370 0 1 Ns372p1274 Ns372p131 Ns372p1274 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1276 := nat_lit 15859366700226747536612797417892276343160410364358049482691076983685120 

noncomputable def Ns372p1277 := nat_lit 1020077597694649507095480783296291511998092155148545647043642720256 

noncomputable def Ns372p1278 := nat_lit 41534785041626166496688695792259196426781649281257984333143321440485376 

noncomputable def Ns372p1279 := BSN.sin_dyadic_bound_f 178270364 268435456 3 2 268435456 134217728 Ns372p1276 Ns372p120 Ns372p1277 Ns372p1278 Ns372p123 Ns372p1277 165452242 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 178270364) qz369 0 2 Ns372p1276 Ns372p120 Ns372p1277 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 178270364) qz370 0 2 Ns372p1278 Ns372p123 Ns372p1277 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1280 := Ns372p1214 139208 BSN.abs_quadSignPos (BSN.cos_quad_nat3 95 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 41120384 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 149 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 165452242 268435456) qz191 rfl rfl (Ns372p1273 rfl) (Ns372p1246 rfl) RS373to384.d35 RS373to384.d37 RS373to384.d39 RS373to384.d41 RS373to384.d17 (Ns372p1275 rfl rfl) (Ns372p1279 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p1281 := nat_lit 3356634530939762527941806401 

noncomputable def Ns372p1282 := BSN.cos_dyadic_bound_f 7611601 268435456 2 1 268435456 134217728 Ns372p1281 Ns372p427 Ns372p1281 Ns372p1281 Ns372p428 Ns372p1281 268327548 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 7611601) qz371 0 1 Ns372p1281 Ns372p427 Ns372p1281 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 7611601) qz372 0 1 Ns372p1281 Ns372p428 Ns372p1281 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1283 := Ns372p1212 Bool.false 142021400 139208 Bool.true 7611601 14148475504056880 1 Bool.false 268327548 Bool.true Bool.false 57168779 151011 BSN.abs_quadSignNeg qz595 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268327548 268435456) qz191 rfl (Ns372p1280 rfl) (Ns372p1246 rfl) RS373to384.d43 RS373to384.d45 RS373to384.d17 (Ns372p1282 rfl rfl) rfl 

noncomputable def Ns372p1284 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) 57168779 268435456 151011 268435456 57168779 268435456 151011 268435456 30692254519656448 57168779 134217728 151011 134217728 (Ns372p1283 rfl rfl rfl rfl) 

noncomputable def Ns372p1285 := @Enclosure.Real.IsNear.mulLit_ff qz687 (Zeta.RiemannSiegel.correction qz190) 2559917 8388608 1 16777216 274978640774211 562949953421312 167640963716057 633318697598976000 703922497154795900487 4722366482869645213696 

noncomputable abbrev qz691 := (@HPow.hPow Real Real Real qz7 qz189 qz9)

noncomputable def Ns372p1286 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz691 1 1 0 1 2559917 8388608 1 16777216 2559917 8388608 1 16777216 

noncomputable def Ns372p1287 := @Enclosure.Real.IsNear.sqrt_image qz189 241816524193 2097152000 45281 2097152000 180155650 180155685 16777216 (@Enclosure.Real.IsNear.of_eq qz189 (@HMul.hMul Real Real Real qz5 qz188 qz3) Bool.false 241816524193 2097152000 45281 2097152000 (BSN.t_div_two_pi_mk qz188 724496 1000 qz191) (@Enclosure.Real.IsNear.mulLit_ff qz188 qz3 724496 1000 0 1 5340353 33554432 1 33554432 241816524193 2097152000 45281 2097152000 (Enclosure.Real.IsNear.const Bool.false 724496 1000) RS373to384.d48 rfl)) 

noncomputable abbrev qz777 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 724496 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz692 := qz777

noncomputable abbrev qz504 := qz692

noncomputable abbrev qz197 := qz504

noncomputable def Ns372p1288 := @Enclosure.Real.IsNear.sqrt_image qz197 360311335 33554432 35 33554432 54977361 54977367 16777216 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 360311335 33554432 35 33554432 360311335 33554432 35 33554432 (Ns372p1287 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns372p1289 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz197) 13744341 4194304 3 16777216 5119833 5119835 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz197) Bool.false 109954728 33554432 6 33554432 13744341 4194304 3 16777216 (Ns372p1288 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns372p1290 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz197)) Bool.false 10239668 33554432 2 33554432 2559917 8388608 1 16777216 (Ns372p1289 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz505 := (@HMul.hMul Real Real Real qz584 qz582 qz686)

noncomputable abbrev qz198 := (Real.cos qz505)

noncomputable abbrev qz693 := (@HMul.hMul Real Real Real qz733 qz776 qz776)

noncomputable abbrev qz506 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz693 qz686) qz600)

noncomputable abbrev qz199 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz506))

noncomputable def Ns372p1291 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz190) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz198) qz199) Bool.false 274978640774211 

noncomputable def Ns372p1292 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz198) qz199 449736991 33554432 40749 

noncomputable abbrev qz200 := (@Neg.neg Real Real.instNeg (Real.cos qz505))

noncomputable def Ns372p1293 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz198) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz200)) Bool.true 449736991 33554432 40749 33554432 (BSN.inv_eq_neg_inv_neg qz198) 

noncomputable def Ns372p1294 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz200) Bool.false 449736991 33554432 40749 33554432 449736991 33554432 

noncomputable def Ns372p1295 := @Enclosure.Real.IsNear.recentre' qz198 Bool.true 2503463 33554432 1306514432 193273528320000 2503463 33554432 1275893 188743680000 

noncomputable abbrev qz201 := qz505

noncomputable def Ns372p1296 := @Enclosure.Real.IsNear.cos_image qz201 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 303937) (@Nat.cast Real Real.instNatCast 65536)) Bool.false 303937 65536 221 33554432 Bool.true 2503463 33554432 1 

noncomputable def Ns372p1297 := nat_lit 37780505581171545192799869 

noncomputable def Ns372p1298 := nat_lit 5764607523034234880000000000000 

noncomputable def Ns372p1299 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz190 884279719003555 140737488355328 1 500000000000000 24767015 33554432 35 33554432 21900969064756831738325 4722366482869645213696 Ns372p1297 

noncomputable def Ns372p1300 := @Enclosure.Real.IsNear.subLit_ff_p qz197 qz1 360311335 33554432 35 33554432 10 1 0 1 24767015 24767015 33554432 35 

noncomputable def Ns372p1301 := @Ns372p1300 33554432 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 360311335 33554432 35 33554432 360311335 33554432 35 33554432 (Ns372p1287 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns372p1302 := @Enclosure.Real.IsNear.recentre' qz201 Bool.false 21900969064756831738325 4722366482869645213696 Ns372p1297 Ns372p1298 303937 65536 221 33554432 (@Ns372p1299 Ns372p1298 RS373to384.d47 (Ns372p1301 rfl rfl) rfl) 

noncomputable def Ns372p1303 := nat_lit 1112348740192265888271973151530049062552324554014401416083604902651366167163114286383124008125628473414207122771701977717132710839960383201 

noncomputable def Ns372p1304 := nat_lit 1394915873690373076486848664169182864789197159454026551719528328937222278135049239913962282725042442758946927987452389455523196612321 

noncomputable def Ns372p1305 := nat_lit 6734864915980318046102735266546198542181200481894820996106993393020020101050875804406052467287981521741861604838320711605922349175636405985 

noncomputable def Ns372p1306 := BSN.cos_dyadic_bound_f 102812440439 68719476736 4 3 33554432 11531251 Ns372p1303 Ns372p830 Ns372p1304 Ns372p1305 Ns372p833 Ns372p1304 2503463 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 102812440439) qz379 0 3 Ns372p1303 Ns372p830 Ns372p1304 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 102812440439) qz380 0 3 Ns372p1305 Ns372p833 Ns372p1304 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1307 := @Ns372p1296 5760000 (Ns372p1302 rfl) (Enclosure.sfrac_false_div 303937 65536) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 303937) (@Nat.cast Real Real.instNatCast 65536)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 14130434217927512162304) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 2503463 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q2 303937 65536 226375608064910080 72057594037927936 0 14130434217927512162304 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 2503463 33554432 14130434217927512162304 9444732965739290427392 102812440439 68719476736 11531251 11520000 (Ns372p1306 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p1308 := @Enclosure.Real.IsNear.inv_image qz200 2503463 33554432 1275893 188743680000 224848121 224888870 16777216 (@Enclosure.Real.IsNear.neg qz198 Bool.true 2503463 33554432 1275893 188743680000 (Ns372p1295 (Ns372p1307 rfl rfl) rfl)) 

noncomputable def Ns372p1309 := Ns372p1293 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz200) Bool.false 449736991 33554432 40749 33554432 (@Ns372p1294 40749 33554432 (Ns372p1308 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p1310 := @Enclosure.Real.IsNear.recentre' qz199 Bool.true 611421 16777216 

noncomputable abbrev qz202 := (@HMul.hMul Real Real Real qz349 qz346 qz506)

noncomputable def Ns372p1311 := @Enclosure.Real.IsNear.cos_image qz202 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 53930291)) qz367) Bool.true 53930291 33554432 

noncomputable def Ns372p1312 := nat_lit 254678601204176052965464252045 

noncomputable def Ns372p1313 := nat_lit 78478135600788507884479364819015013 

noncomputable def Ns372p1314 := @Enclosure.Real.IsNear.recentre' qz202 Bool.true Ns372p1312 Ns372p602 Ns372p1313 

noncomputable abbrev qz203 := qz506

noncomputable def Ns372p1315 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz203 884279719003555 140737488355328 1 500000000000000 288006832827919 

noncomputable abbrev qz507 := (@HSub.hSub Real Real Real qz588 qz693 qz686)

noncomputable abbrev qz204 := qz507

noncomputable def Ns372p1316 := @Enclosure.Real.IsNear.subLit_tf qz204 qz31 217638088650255 1125899906842624 2908097395 1125899906842624 1 16 

noncomputable abbrev qz508 := qz693

noncomputable abbrev qz205 := qz508

noncomputable def Ns372p1317 := @Enclosure.Real.IsNear.subLit_ff_n qz205 qz190 613405032010225 1125899906842624 1733692275 1125899906842624 24767015 33554432 35 33554432 

noncomputable def Ns372p1318 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz190 24767015 33554432 35 33554432 24767015 33554432 35 33554432 613405032010225 1125899906842624 

noncomputable def Ns372p1319 := nat_lit 272382077010720600569176882892975898206154121871753546791381587725397853298620781264651373103158961 

noncomputable def Ns372p1320 := nat_lit 605331346772798448382906421025678105936313488874799092986313074630687808109657477702464444081 

noncomputable def Ns372p1321 := nat_lit 1648089700784292342959682755035406249779727652061144612998368016418555743809295249277103330710394545 

noncomputable def Ns372p1322 := BSN.cos_dyadic_bound_t 53930291 33554432 4 3 16777216 5760000 Ns372p1319 Ns372p329 Ns372p1320 Ns372p1321 Ns372p332 Ns372p1320 611421 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 53930291) (BSN.cosEvenQ 33554432) 0 3 Ns372p1319 Ns372p329 Ns372p1320 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 53930291) (BSN.cosOddQ 33554432) 0 3 Ns372p1321 Ns372p332 Ns372p1320 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1323 := @Ns372p1310 1589257216 96636764160000 611421 16777216 1552009 94371840000 (@Ns372p1311 273 16777216 Bool.true 611421 16777216 1 5760000 (@Ns372p1314 Ns372p605 53930291 33554432 273 16777216 (@Ns372p1315 1125899906842624 2908097395 1125899906842624 Ns372p1312 Ns372p602 Ns372p1313 Ns372p605 RS373to384.d47 (@Ns372p1316 0 1 4608109325246704 288006832827919 1125899906842624 2908097395 1125899906842624 (@Ns372p1317 7302722446224953180160 217638088650255 1125899906842624 2908097395 1125899906842624 (@Ns372p1318 1733692275 1125899906842624 (Ns372p1301 rfl rfl) (Ns372p1301 rfl rfl) rfl) (Ns372p1301 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 53930291 33554432) (BSN.cos_neg_of_bound 53930291 33554432 Bool.true 611421 16777216 1 5760000 (Ns372p1322 rfl rfl)) rfl rfl) 

noncomputable def Ns372p1324 := @Ns372p1285 85860342443806967797 1062532458645670173081600 (Ns372p1286 qz33 (@Enclosure.Real.IsNear.of_eq qz691 (@Inv.inv Real Real.instInv (Real.sqrt qz197)) Bool.false 2559917 8388608 1 16777216 (BSN.rpow_neg_quarter_mk qz189 (BSN.t_div_two_pi_nonneg qz188 724496 1000 qz191)) Ns372p1290) rfl) (@Ns372p1291 562949953421312 167640963716057 633318697598976000 (BSN.correction_mk qz190 (BSN.cos_two_pi_p_ne_zero_mk qz188 724496 1000 10 qz191 rfl rfl (@BSN.floor_sqrt_eq_dec qz188 724496 1000 10 qz191 rfl rfl rfl))) (@Ns372p1292 33554432 611421 16777216 1552009 94371840000 274978640774211 562949953421312 167640963716057 633318697598976000 Ns372p1309 (Ns372p1323 rfl) rfl)) 

noncomputable def Ns372p1325 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz188) (hardyZApproximantRS₀ qz188) Bool.false 1307525095045409075641 4722366482869645213696 1281336465482794026997 1062532458645670173081600 (@Eq.refl Real (hardyZApproximantRS₀ qz188)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz188) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) (@HMul.hMul Real Real Real qz5 qz687 (Zeta.RiemannSiegel.correction qz190))) Bool.false 1307525095045409075641 4722366482869645213696 1281336465482794026997 1062532458645670173081600 (BSN.hardyZApproximantRS₀_eq qz188 10 (@BSN.floor_sqrt_eq_dec qz188 724496 1000 10 qz191 rfl rfl rfl)) (@Ns372p1211 1307525095045409075641 4722366482869645213696 1281336465482794026997 1062532458645670173081600 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 10)) Bool.false 57168779 134217728 151011 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) (Ns372p1284 (Ns372p1283 rfl rfl rfl rfl) rfl rfl)) (Ns372p1324 rfl) rfl rfl)) 

theorem RS373to384.d60 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz188) Bool.false 1307525095045409075641 4722366482869645213696 1281336465482794026997 1062532458645670173081600 := Ns372p1325 

noncomputable def Ns372p1326 := nat_lit 311732617315924457899815862272 

noncomputable abbrev qz778 := (Enclosure.sfrac Bool.false 725819 1000)

noncomputable abbrev qz694 := qz778

noncomputable abbrev qz509 := qz694

noncomputable abbrev qz206 := qz509

noncomputable abbrev qz779 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 725819 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz695 := qz779

noncomputable abbrev qz510 := qz695

noncomputable abbrev qz207 := qz510

noncomputable abbrev qz780 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 725819 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz696 := qz780

noncomputable abbrev qz511 := qz696

noncomputable abbrev qz208 := qz511

noncomputable abbrev qz697 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz207 qz9))

noncomputable def Ns372p1327 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) (@HMul.hMul Real Real Real qz5 qz697 (Zeta.RiemannSiegel.correction qz208)) 517903101 67108864 151289 134217728 89654127118630387365 590295810358705651712 616513278759514207 1328165573307087716352 Ns372p1326 

noncomputable def Ns372p1328 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin BSN.quadSignNeg 9 10 725819 1000 197 268435456 134217728 4503599627370496 Bool.false 365155106719 2521 618095470 48 84886744 8 

noncomputable def Ns372p1329 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 725819 1000 94 149 268435456 134217728 4503599627370496 Bool.false 365155106719 2521 

noncomputable def Ns372p1330 := Ns372p1329 558195838 48 94906264 8 589812974 48 89478488 8 Bool.true 891600871 113782 Bool.true 358239965 Bool.true 115399445 14148475504056880 1 Bool.false 62829184 Bool.true Bool.false 111877632 Bool.true Bool.true 951106887 

noncomputable def Ns372p1331 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 725819 1000 38 33 268435456 134217728 4503599627370496 Bool.false 365155106719 2521 

noncomputable def Ns372p1332 := Ns372p1331 480971758 48 109588312 8 522351262 48 101459064 8 Bool.true 759402220 84389 Bool.false 33684025 Bool.true 62668781 14148475504056880 1 Bool.false 266324845 Bool.true Bool.false 62101054 Bool.true Bool.true 891600871 

noncomputable def Ns372p1333 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 725819 1000 225 122 268435456 134217728 4503599627370496 Bool.false 365155106719 2521 

noncomputable def Ns372p1334 := Ns372p1333 372130544 47 134217720 8 432030192 47 120047984 16 Bool.true 570206884 49660 Bool.false 182766043 Bool.false 137178543 14148475504056880 1 Bool.false 168969069 Bool.true Bool.false 234140483 Bool.true Bool.true 759402220 

noncomputable def Ns372p1335 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 725819 1000 545 358 268435456 134217728 4503599627370496 Bool.false 365155106719 2521 

noncomputable def Ns372p1336 := Ns372p1335 186065264 47 189812528 16 294906480 47 154981288 8 Bool.true 268435360 2575 Bool.false 302104462 Bool.false 153020992 14148475504056880 1 Bool.false 242249992 Bool.true Bool.false 225989174 Bool.true Bool.true 570206884 

noncomputable def Ns372p1337 := nat_lit 32245594608498951274650644818465894506604217260533228107261 

noncomputable def Ns372p1338 := nat_lit 23704614103534832586452289359387654172565528784142336000 

noncomputable def Ns372p1339 := nat_lit 96690414697150625119537128847520000 

noncomputable def Ns372p1340 := nat_lit 421078533881577367496125840762524713280 

noncomputable abbrev qz781 := (@Eq.refl Real (Enclosure.sfrac Bool.false 725819 1000))

noncomputable abbrev qz698 := qz781

noncomputable abbrev qz512 := qz698

noncomputable abbrev qz209 := qz512

noncomputable def Ns372p1341 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz206 725819 1000 2107253883044 16000000 1451638 4000 2000 Ns372p1339 Ns372p1340 qz209 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns372p1342 := nat_lit 10318590274719664407888206341909086242113349523370632994323520 

noncomputable abbrev qz699 := (@HSub.hSub Real Real Real qz737 qz738 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz739 (@Nat.cast Real Real.instNatCast 1451638))))

noncomputable abbrev qz513 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 725819 4000) (Real.log (Enclosure.sfrac Bool.false 2107253883044 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz699))

noncomputable abbrev qz700 := (Enclosure.sfrac Bool.false 725819 2000)

noncomputable abbrev qz210 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz513 qz700) (@HMul.hMul Real Real Real qz349 qz700 (Real.log Real.pi)))

noncomputable def Ns372p1343 := @Enclosure.Real.IsNear.addLit_ft_p qz210 (Enclosure.sfrac Bool.true Ns372p1339 Ns372p1340) 24505148532319367789309 18014398509481984000 346116056054106743 36864000000000000000000 Ns372p1339 Ns372p1340 0 1 Ns372p1342 

noncomputable def Ns372p1344 := nat_lit 1644512680155220057538718334976000 

noncomputable abbrev qz211 := (@HSub.hSub Real Real Real qz353 qz513 qz700)

noncomputable def Ns372p1345 := @Enclosure.Real.IsNear.subLit_ff_p qz211 (@HMul.hMul Real Real Real qz5 qz700 (Real.log Real.pi)) 31988930440475545500413 18014398509481984000 143324134492307 36000000000000000000 27879260138259 67108864000 725819 134217728000 Ns372p1344 24505148532319367789309 18014398509481984000 

noncomputable def Ns372p1346 := nat_lit 63977860880951091000826000 

noncomputable abbrev qz212 := qz513

noncomputable def Ns372p1347 := @Enclosure.Real.IsNear.subLit_ff_p qz212 qz700 38526526796352397572861 18014398509481984000 143324134492307 36000000000000000000 725819 2000 0 1 Ns372p1346 31988930440475545500413 18014398509481984000 143324134492307 36000000000000000000 

noncomputable def Ns372p1348 := nat_lit 86754025861966043370816941407000854528 

noncomputable def Ns372p1349 := nat_lit 57004757010451800529043456 

noncomputable def Ns372p1350 := nat_lit 53031086488124992220117808 

noncomputable def Ns372p1351 := BSN.log_dyadic_bound 10101883044 4204405883044 2 1 Ns372p1350 134217728 46080000 102048041034654705936 102048041034654705936 644968 4214507766088 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 10101883044) (BSN.artanhQ 4204405883044) 0 1 102048041034654705936 Ns372p1350 102048041034654705936 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz514 := (Real.log (Enclosure.sfrac Bool.false 2107253883044 16000000))

noncomputable def Ns372p1352 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 725819 4000) qz514 725819 4000 0 1 53089817064303719 4503599627370496 195312653 9000000000000000 38533597931795861020861 18014398509481984000 141761634487807 36000000000000000000 (Enclosure.Real.IsNear.const Bool.false 725819 4000) (BSN.isNear_log_sfrac 2107253883044 16000000 53089817064303719 4503599627370496 195312653 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2107253883044) qz356)) Bool.false Ns372p1349 Ns372p98 1000000783360000 46080000000000000000000 53089817064303719 4503599627370496 195312653 9000000000000000 (BSN.log_rat_reduce_isNear 2107253883044 16000000 17 4214507766088 4194304000000 644968 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns372p1351 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p1353 := BSN.arctan_dyadic_bound_f 1000 1451638 1 0 16777216 5760000 0 1 1 0 1 1 11557 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1451638) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1451638) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns372p1354 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1451638))) 884279719003555 562949953421312 1 2000000000000000 11557 16777216 1 5760000 14829245837530256900096 883891930432931 562949953421312 3125000009 18000000000000000 qz17 (Ns372p1353 rfl) rfl rfl 

noncomputable abbrev qz515 := (@HMul.hMul Real Real Real qz584 qz589 qz699)

noncomputable abbrev qz213 := qz515

noncomputable abbrev qz516 := qz699

noncomputable abbrev qz214 := qz516

noncomputable def Ns372p1355 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 725819 4000) qz514) qz213 38533597931795861020861 18014398509481984000 141761634487807 36000000000000000000 883891930432931 2251799813685248 3125000009 72000000000000000 Ns372p1348 38526526796352397572861 18014398509481984000 143324134492307 36000000000000000000 (Ns372p1352 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz214 1 4 0 1 883891930432931 562949953421312 3125000009 18000000000000000 883891930432931 2251799813685248 3125000009 72000000000000000 qz363 Ns372p1354 rfl) 

noncomputable def Ns372p1356 := @Ns372p1343 Ns372p1337 Ns372p1338 346116056054106743 36864000000000000000000 (@Ns372p1345 346116056054106743 36864000000000000000000 (Ns372p1347 (Ns372p1355 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 725819 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz700 (Real.log Real.pi) 725819 2000 0 1 38410761 33554432 1 67108864 27879260138259 67108864000 725819 134217728000 (Enclosure.Real.IsNear.const Bool.false 725819 2000) RS373to384.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns372p1339 Ns372p1340) 

noncomputable def Ns372p1357 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns372p1337 Ns372p1338 346116056054106743 36864000000000000000000 45644388339 33554432 79 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz364 qz210 (Enclosure.sfrac Bool.true Ns372p1339 Ns372p1340)) Bool.false Ns372p1337 Ns372p1338 346116056054106743 36864000000000000000000 Ns372p1341 (Ns372p1356 rfl rfl)) 

noncomputable def Ns372p1358 := nat_lit 7591830691522122725982208 

noncomputable def Ns372p1359 := nat_lit 3503293941622673449515075855817786406230423977647872515959636377048785459414429684760965793716343298721340948582678621585861141589041853041 

noncomputable def Ns372p1360 := nat_lit 2486569276283673461123340559406444269878203064097912521685576702677332984296558867086665021917582163690001224011053273083913452630641 

noncomputable def Ns372p1361 := nat_lit 17494749922980751547490804727073302235386836952942759277907657983683975016249368116685041840411925126034052668227335982715012627560110207601 

noncomputable def Ns372p1362 := BSN.sin_dyadic_bound_f 107886402979 68719476736 4 3 33554432 11531251 Ns372p1359 Ns372p111 Ns372p1360 Ns372p1361 Ns372p114 Ns372p1360 33554420 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107886402979) qz365 0 3 Ns372p1359 Ns372p111 Ns372p1360 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107886402979) qz366 0 3 Ns372p1361 Ns372p114 Ns372p1360 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1363 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz206) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 45644388339) qz367) Bool.false 45644388339 33554432 79 8388608 Bool.true 33554420 33554432 1 5760000 (Ns372p1357 rfl) (Enclosure.sfrac_false_div 45644388339 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 45644388339) qz367) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns372p1358) qz368) 226375608064910080 72057594037927936 Bool.false 33554420 33554432 216 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q1 45644388339 33554432 226375608064910080 72057594037927936 216 Ns372p1358 Ns372p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554420 33554432 Ns372p1358 Ns372p98 107886402979 68719476736 11531251 11520000 (Ns372p1362 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p1364 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns372p1337 Ns372p1338 346116056054106743 36864000000000000000000 365155106719 268435456 2521 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz364 qz210 (Enclosure.sfrac Bool.true Ns372p1339 Ns372p1340)) Bool.false Ns372p1337 Ns372p1338 346116056054106743 36864000000000000000000 Ns372p1341 (Ns372p1356 rfl rfl)) 

noncomputable def Ns372p1365 := Ns372p1336 49660 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 545 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 242249992 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 358 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 225989174 268435456) qz209 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) Bool.true 8388605 8388608 452567 47185920000 268435360 268435456 2575 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.true 8388605 8388608 452567 47185920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz206) qz206) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.true 33554420 33554432 463428608 48318382080000 8388605 8388608 452567 47185920000 (Ns372p1363 rfl rfl) rfl)) rfl) (Ns372p1364 rfl) RS373to384.d7 

noncomputable def Ns372p1366 := nat_lit 130857974350747456584650052091461670364777517447832972703936935723843840 

noncomputable def Ns372p1367 := nat_lit 69383646041428061598180816533531932130416957701085771189537001226496 

noncomputable def Ns372p1368 := nat_lit 342610930729795312288638796060392942112872823003284599166480343179510016 

noncomputable def Ns372p1369 := BSN.sin_dyadic_bound_f 302104462 268435456 3 2 268435456 134217728 Ns372p1366 Ns372p120 Ns372p1367 Ns372p1368 Ns372p123 Ns372p1367 242249992 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 302104462) qz369 0 2 Ns372p1366 Ns372p120 Ns372p1367 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 302104462) qz370 0 2 Ns372p1368 Ns372p123 Ns372p1367 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1370 := nat_lit 4782997400082599680653073579019760012189640025812578926010754291204096 

noncomputable def Ns372p1371 := nat_lit 300613240078378808446753689631996718277605098522122762231759241216 

noncomputable def Ns372p1372 := nat_lit 14348390973767642284342327229680016043132364867240692532507799355129856 

noncomputable def Ns372p1373 := BSN.cos_dyadic_bound_f 153020992 268435456 3 2 268435456 134217728 Ns372p1370 Ns372p159 Ns372p1371 Ns372p1372 Ns372p162 Ns372p1371 225989174 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 153020992) qz371 0 2 Ns372p1370 Ns372p159 Ns372p1371 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 153020992) qz372 0 2 Ns372p1372 Ns372p162 Ns372p1371 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1374 := nat_lit 17520810761523868085011294067459614858683153144921747261501313477051105 

noncomputable def Ns372p1375 := nat_lit 1244984869800071589548478131845347167557984121397684503018087973601 

noncomputable def Ns372p1376 := nat_lit 45885822018963787725789358354942670258279831024312789433784267916509921 

noncomputable def Ns372p1377 := BSN.sin_dyadic_bound_f 182766043 268435456 3 2 268435456 134217728 Ns372p1374 Ns372p120 Ns372p1375 Ns372p1376 Ns372p123 Ns372p1375 168969069 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 182766043) qz369 0 2 Ns372p1374 Ns372p120 Ns372p1375 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 182766043) qz370 0 2 Ns372p1376 Ns372p123 Ns372p1375 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1378 := nat_lit 3089094323031301295619543814089901136801586914205614987939226611338881 

noncomputable def Ns372p1379 := nat_lit 125397675651576139269926640587443284002601062319804256178140073601 

noncomputable def Ns372p1380 := nat_lit 9267032173742600734580091588988528523836755540492205355305323553869441 

noncomputable def Ns372p1381 := BSN.cos_dyadic_bound_f 137178543 268435456 3 2 268435456 134217728 Ns372p1378 Ns372p159 Ns372p1379 Ns372p1380 Ns372p162 Ns372p1379 234140483 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 137178543) qz371 0 2 Ns372p1378 Ns372p159 Ns372p1379 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 137178543) qz372 0 2 Ns372p1380 Ns372p162 Ns372p1379 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1382 := Ns372p1334 84389 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 225 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 168969069 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 122 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 234140483 268435456) qz209 rfl rfl (Ns372p1365 RS373to384.d9 RS373to384.d11 RS373to384.d13 RS373to384.d17 (Ns372p1369 rfl rfl) (Ns372p1373 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns372p1364 rfl) RS373to384.d19 RS373to384.d21 RS373to384.d23 RS373to384.d25 RS373to384.d17 (Ns372p1377 rfl rfl) (Ns372p1381 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns372p1383 := nat_lit 1287347885606595282965250390625 

noncomputable def Ns372p1384 := BSN.cos_dyadic_bound_f 33684025 268435456 2 1 268435456 134217728 Ns372p1383 Ns372p427 Ns372p1383 Ns372p1383 Ns372p428 Ns372p1383 266324845 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 33684025) qz371 0 1 Ns372p1383 Ns372p427 Ns372p1383 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 33684025) qz372 0 1 Ns372p1383 Ns372p428 Ns372p1383 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1385 := nat_lit 15424283125312153766487937973521 

noncomputable def Ns372p1386 := BSN.sin_dyadic_bound_f 62668781 268435456 2 1 268435456 134217728 Ns372p1385 Ns372p130 Ns372p1385 Ns372p1385 Ns372p131 Ns372p1385 62101054 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 62668781) qz369 0 1 Ns372p1385 Ns372p130 Ns372p1385 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 62668781) qz370 0 1 Ns372p1385 Ns372p131 Ns372p1385 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1387 := Ns372p1332 113782 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 266324845 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 33 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 62101054 268435456) qz209 rfl rfl (Ns372p1382 rfl rfl) (Ns372p1364 rfl) RS373to384.d27 RS373to384.d29 RS373to384.d31 RS373to384.d33 RS373to384.d17 (Ns372p1384 rfl rfl) (Ns372p1386 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p1388 := nat_lit 8878923773607187282880850659339209399391406986621941570774240856808855605258131717164275197284822304040640625 

noncomputable def Ns372p1389 := nat_lit 4467745290059092398608546736134711455607806508518982937360921331434959814903304111890231376758056640625 

noncomputable def Ns372p1390 := nat_lit 53797773438146218795811270719734472211222672894267565869411780851889071413924255383546962096149255020226240625 

noncomputable def Ns372p1391 := BSN.cos_dyadic_bound_f 358239965 268435456 4 3 268435456 134217728 Ns372p1388 Ns372p143 Ns372p1389 Ns372p1390 Ns372p146 Ns372p1389 62829184 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 358239965) qz371 0 3 Ns372p1388 Ns372p143 Ns372p1389 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 358239965) qz372 0 3 Ns372p1390 Ns372p146 Ns372p1389 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1392 := nat_lit 177343338793625950341786179400625 

noncomputable def Ns372p1393 := BSN.sin_dyadic_bound_f 115399445 268435456 2 1 268435456 134217728 Ns372p1392 Ns372p130 Ns372p1392 Ns372p1392 Ns372p131 Ns372p1392 111877632 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 115399445) qz369 0 1 Ns372p1392 Ns372p130 Ns372p1392 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 115399445) qz370 0 1 Ns372p1392 Ns372p131 Ns372p1392 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1394 := Ns372p1330 139464 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 94 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 62829184 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 149 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 111877632 268435456) qz209 rfl rfl (Ns372p1387 rfl) (Ns372p1364 rfl) RS373to384.d35 RS373to384.d37 RS373to384.d39 RS373to384.d41 RS373to384.d17 (Ns372p1391 rfl rfl) (Ns372p1393 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p1395 := nat_lit 37263757004475295094333715131678207094114690559879087586114173574394884674863658886136637521117894028239568896 

noncomputable def Ns372p1396 := nat_lit 18801840353197589071743637643610151059890971615905279410201626449228861581028955588036887855686479773696 

noncomputable def Ns372p1397 := nat_lit 186123981127387883532238465742755409784578606513010785780671917667410625372800111481331758054457486897269702656 

noncomputable def Ns372p1398 := BSN.sin_dyadic_bound_f 403815852 268435456 4 3 268435456 134217728 Ns372p1395 Ns372p134 Ns372p1396 Ns372p1397 Ns372p137 Ns372p1396 267842753 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 403815852) qz369 0 3 Ns372p1395 Ns372p134 Ns372p1396 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 403815852) qz370 0 3 Ns372p1397 Ns372p137 Ns372p1396 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1399 := Ns372p1328 Bool.true 951106887 139464 Bool.true 403815852 14148475504056880 1 Bool.false 267842753 Bool.true Bool.true 1035806202 151289 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 197 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267842753 268435456) qz209 rfl (Ns372p1394 rfl) (Ns372p1364 rfl) RS373to384.d43 RS373to384.d45 RS373to384.d17 (Ns372p1398 rfl rfl) rfl 

noncomputable def Ns372p1400 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) 1035806202 268435456 151289 268435456 1035806202 268435456 151289 268435456 556094220322996224 517903101 67108864 151289 134217728 (Ns372p1399 rfl rfl rfl rfl) 

noncomputable def Ns372p1401 := @Enclosure.Real.IsNear.mulLit_ff qz697 (Zeta.RiemannSiegel.correction qz208) 10234999 33554432 1 33554432 8759563837635 17592186044416 1204677224701279 791648371998720000 89654127118630387365 590295810358705651712 

noncomputable abbrev qz701 := (@HPow.hPow Real Real Real qz7 qz207 qz9)

noncomputable def Ns372p1402 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz701 1 1 0 1 10234999 33554432 1 33554432 10234999 33554432 1 33554432 

noncomputable def Ns372p1403 := @Enclosure.Real.IsNear.sqrt_image qz207 3876129674107 33554432000 725819 33554432000 180320066 180320101 16777216 (@Enclosure.Real.IsNear.of_eq qz207 (@HMul.hMul Real Real Real qz5 qz206 qz3) Bool.false 3876129674107 33554432000 725819 33554432000 (BSN.t_div_two_pi_mk qz206 725819 1000 qz209) (@Enclosure.Real.IsNear.mulLit_ff qz206 qz3 725819 1000 0 1 5340353 33554432 1 33554432 3876129674107 33554432000 725819 33554432000 (Enclosure.Real.IsNear.const Bool.false 725819 1000) RS373to384.d48 rfl)) 

noncomputable abbrev qz782 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 725819 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz702 := qz782

noncomputable abbrev qz517 := qz702

noncomputable abbrev qz215 := qz517

noncomputable def Ns372p1404 := @Enclosure.Real.IsNear.sqrt_image qz215 360640167 33554432 35 33554432 55002442 55002448 16777216 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 360640167 33554432 35 33554432 360640167 33554432 35 33554432 (Ns372p1403 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns372p1405 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz215) 55002445 16777216 3 16777216 5117499 5117500 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz215) Bool.false 110004890 33554432 6 33554432 55002445 16777216 3 16777216 (Ns372p1404 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns372p1406 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 10234999 33554432 1 33554432 10234999 33554432 1 33554432 (Ns372p1405 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz216 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz511))

noncomputable abbrev qz703 := (@HMul.hMul Real Real Real qz733 qz780 qz780)

noncomputable abbrev qz518 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz703 qz696) qz600)

noncomputable abbrev qz217 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz518))

noncomputable def Ns372p1407 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz208) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz216) qz217) Bool.false 8759563837635 

noncomputable def Ns372p1408 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz216) qz217 320100999 4194304 330283 

noncomputable abbrev qz704 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz216))

noncomputable def Ns372p1409 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz216) (@Neg.neg Real Real.instNeg qz704) Bool.true 320100999 4194304 330283 8388608 (BSN.inv_eq_neg_inv_neg qz216) 

noncomputable def Ns372p1410 := @Enclosure.Real.IsNear.recentre' qz704 Bool.false 2560807992 33554432 1321132 33554432 320100999 4194304 

noncomputable def Ns372p1411 := @Enclosure.Real.IsNear.recentre' qz216 Bool.true 439666 33554432 1306514432 193273528320000 219833 16777216 1275893 188743680000 

noncomputable abbrev qz218 := (@HMul.hMul Real Real Real qz349 qz346 qz511)

noncomputable def Ns372p1412 := @Enclosure.Real.IsNear.cos_image qz218 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 157681857) qz367) Bool.false 157681857 33554432 221 33554432 Bool.true 439666 33554432 1 

noncomputable def Ns372p1413 := nat_lit 944512639532113275191753269 

noncomputable def Ns372p1414 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz208 884279719003555 140737488355328 1 500000000000000 25095847 33554432 35 33554432 22191748533316208736085 4722366482869645213696 Ns372p1413 

noncomputable def Ns372p1415 := @Enclosure.Real.IsNear.subLit_ff_p qz215 qz1 360640167 33554432 35 33554432 10 1 0 1 25095847 25095847 33554432 35 

noncomputable def Ns372p1416 := @Ns372p1415 33554432 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 360640167 33554432 35 33554432 360640167 33554432 35 33554432 (Ns372p1403 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns372p1417 := @Enclosure.Real.IsNear.recentre' qz218 Bool.false 22191748533316208736085 4722366482869645213696 Ns372p1413 Ns372p586 157681857 33554432 221 33554432 (@Ns372p1414 Ns372p586 RS373to384.d47 (Ns372p1416 rfl rfl) rfl) 

noncomputable def Ns372p1418 := nat_lit 7532540583159857030365184 

noncomputable def Ns372p1419 := nat_lit 1307769607696483593855655907623473725751511273285043145149593164821840535070225758528868733982354341923567206551107286731579505956966452961 

noncomputable def Ns372p1420 := nat_lit 2263289746464104523283748910472051241062936509534270823457374477188744244145355162216743639474940867131047885098999431756137629830881 

noncomputable def Ns372p1421 := nat_lit 7915319916351915239800586416562471967894200632771812392758327672322931111813226385426176270204086908507605807295520314797480228481585467105 

noncomputable def Ns372p1422 := BSN.cos_dyadic_bound_f 107043839863 68719476736 4 3 33554432 11531251 Ns372p1419 Ns372p830 Ns372p1420 Ns372p1421 Ns372p833 Ns372p1420 439666 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 107043839863) qz379 0 3 Ns372p1419 Ns372p830 Ns372p1420 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 107043839863) qz380 0 3 Ns372p1421 Ns372p833 Ns372p1420 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1423 := @Ns372p1412 5760000 (Ns372p1417 rfl) (Enclosure.sfrac_false_div 157681857 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 157681857) qz367) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns372p1418) qz368) 226375608064910080 72057594037927936 Bool.false 439666 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q2 157681857 33554432 226375608064910080 72057594037927936 0 Ns372p1418 Ns372p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 439666 33554432 Ns372p1418 Ns372p98 107043839863 68719476736 11531251 11520000 (Ns372p1422 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p1424 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz216) 219833 16777216 1275893 188743680000 1279743430 1281064562 16777216 (@Enclosure.Real.IsNear.neg qz216 Bool.true 219833 16777216 1275893 188743680000 (Ns372p1411 (Ns372p1423 rfl rfl) rfl)) 

noncomputable def Ns372p1425 := Ns372p1409 (@Enclosure.Real.IsNear.neg qz704 Bool.false 320100999 4194304 330283 8388608 (@Ns372p1410 330283 8388608 (Ns372p1424 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p1426 := @Enclosure.Real.IsNear.recentre' qz217 Bool.true 109460 16777216 

noncomputable abbrev qz219 := (@HMul.hMul Real Real Real qz349 qz346 qz518)

noncomputable def Ns372p1427 := @Enclosure.Real.IsNear.cos_image qz219 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 13231525)) qz377) Bool.true 13231525 8388608 

noncomputable def Ns372p1428 := nat_lit 249936444595738252353885135245 

noncomputable def Ns372p1429 := nat_lit 79099307561165916362017237767107173 

noncomputable def Ns372p1430 := @Enclosure.Real.IsNear.recentre' qz219 Bool.true Ns372p1428 Ns372p602 Ns372p1429 

noncomputable abbrev qz220 := qz518

noncomputable def Ns372p1431 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz220 884279719003555 140737488355328 1 500000000000000 282644099174159 

noncomputable abbrev qz519 := (@HSub.hSub Real Real Real qz588 qz703 qz696)

noncomputable abbrev qz221 := qz519

noncomputable def Ns372p1432 := @Enclosure.Real.IsNear.subLit_tf qz221 qz31 212275354996495 1125899906842624 2931115635 1125899906842624 1 16 

noncomputable abbrev qz520 := qz703

noncomputable abbrev qz222 := qz520

noncomputable def Ns372p1433 := @Enclosure.Real.IsNear.subLit_ff_n qz222 qz208 629801536647409 1125899906842624 1756710515 1125899906842624 25095847 33554432 35 33554432 

noncomputable def Ns372p1434 := @Enclosure.Real.IsNear.mulLit_ff qz208 qz208 25095847 33554432 35 33554432 25095847 33554432 35 33554432 629801536647409 1125899906842624 

noncomputable def Ns372p1435 := nat_lit 15055062076818515564064840786080197610280203357676806873693233691596376242491909183994140625 

noncomputable def Ns372p1436 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600 

noncomputable def Ns372p1437 := nat_lit 28795115205432861078744049605076877527078552005394653400900177789492666721343994140625 

noncomputable def Ns372p1438 := nat_lit 91110378533536691340635652663853117612285246784170214747295464998603242369926194239994140625 

noncomputable def Ns372p1439 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600 

noncomputable def Ns372p1440 := BSN.cos_dyadic_bound_t 13231525 8388608 4 3 16777216 5760000 Ns372p1435 Ns372p1436 Ns372p1437 Ns372p1438 Ns372p1439 Ns372p1437 109460 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 13231525) (BSN.cosEvenQ 8388608) 0 3 Ns372p1435 Ns372p1436 Ns372p1437 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 13231525) (BSN.cosOddQ 8388608) 0 3 Ns372p1438 Ns372p1439 Ns372p1437 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1441 := @Ns372p1426 1600777216 96636764160000 27365 4194304 1563259 94371840000 (@Ns372p1427 275 16777216 Bool.true 109460 16777216 1 5760000 (@Ns372p1430 Ns372p605 13231525 8388608 275 16777216 (@Ns372p1431 1125899906842624 2931115635 1125899906842624 Ns372p1428 Ns372p602 Ns372p1429 Ns372p605 RS373to384.d47 (@Ns372p1432 0 1 4522305586786544 282644099174159 1125899906842624 2931115635 1125899906842624 (@Ns372p1433 7122778964505751715840 212275354996495 1125899906842624 2931115635 1125899906842624 (@Ns372p1434 1756710515 1125899906842624 (Ns372p1416 rfl rfl) (Ns372p1416 rfl rfl) rfl) (Ns372p1416 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 13231525 8388608) (BSN.cos_neg_of_bound 13231525 8388608 Bool.true 109460 16777216 1 5760000 (Ns372p1440 rfl rfl)) rfl rfl) 

noncomputable def Ns372p1442 := @Ns372p1401 616513278759514207 1328165573307087716352 (Ns372p1402 qz33 (@Enclosure.Real.IsNear.of_eq qz701 (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 10234999 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz207 (BSN.t_div_two_pi_nonneg qz206 725819 1000 qz209)) Ns372p1406) rfl) (@Ns372p1407 17592186044416 1204677224701279 791648371998720000 (BSN.correction_mk qz208 (BSN.cos_two_pi_p_ne_zero_mk qz206 725819 1000 10 qz209 rfl rfl (@BSN.floor_sqrt_eq_dec qz206 725819 1000 10 qz209 rfl rfl rfl))) (@Ns372p1408 8388608 27365 4194304 1563259 94371840000 8759563837635 17592186044416 1204677224701279 791648371998720000 Ns372p1425 (Ns372p1441 rfl) rfl)) 

noncomputable def Ns372p1443 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (hardyZApproximantRS₀ qz206) Bool.true 4645177980004615454373 590295810358705651712 2113609410650943583 1328165573307087716352 (@Eq.refl Real (hardyZApproximantRS₀ qz206)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) (@HMul.hMul Real Real Real qz5 qz697 (Zeta.RiemannSiegel.correction qz208))) Bool.true 4645177980004615454373 590295810358705651712 2113609410650943583 1328165573307087716352 (BSN.hardyZApproximantRS₀_eq qz206 10 (@BSN.floor_sqrt_eq_dec qz206 725819 1000 10 qz209 rfl rfl rfl)) (@Ns372p1327 4645177980004615454373 590295810358705651712 2113609410650943583 1328165573307087716352 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 10)) Bool.true 517903101 67108864 151289 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) (Ns372p1400 (Ns372p1399 rfl rfl rfl rfl) rfl rfl)) (Ns372p1442 rfl) rfl rfl)) 

theorem RS373to384.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz206) Bool.true 4645177980004615454373 590295810358705651712 2113609410650943583 1328165573307087716352 := Ns372p1443 

noncomputable def Ns372p1444 := nat_lit 38614028415902946799401304064 

noncomputable abbrev qz783 := (Enclosure.sfrac Bool.false 727142 1000)

noncomputable abbrev qz705 := qz783

noncomputable abbrev qz521 := qz705

noncomputable abbrev qz223 := qz521

noncomputable abbrev qz784 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 727142 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz706 := qz784

noncomputable abbrev qz522 := qz706

noncomputable abbrev qz224 := qz522

noncomputable abbrev qz785 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 727142 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz707 := qz785

noncomputable abbrev qz523 := qz707

noncomputable abbrev qz225 := qz523

noncomputable abbrev qz708 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz224 qz9))

noncomputable def Ns372p1445 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (@HMul.hMul Real Real Real qz5 qz708 (Zeta.RiemannSiegel.correction qz225)) 86196717 134217728 151561 134217728 91400239585877006855 590295810358705651712 56128028404382288189 442721857769029238784000 Ns372p1444 

noncomputable def Ns372p1446 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin BSN.quadSignNeg 9 10 727142 1000 197 268435456 134217728 4503599627370496 Bool.false 365998623826 2526 618095470 48 84886744 8 

noncomputable def Ns372p1447 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 727142 1000 94 149 268435456 134217728 4503599627370496 Bool.false 365998623826 2526 

noncomputable def Ns372p1448 := Ns372p1447 558195838 48 94906264 8 589812974 48 89478488 8 Bool.false 242978554 113986 Bool.true 253215951 Bool.true 52204902 14148475504056880 1 Bool.false 157603155 Bool.true Bool.false 51876442 Bool.true Bool.false 169965277 

noncomputable def Ns372p1449 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 727142 1000 38 32 268435456 134217728 4503599627370496 Bool.false 365998623826 2526 

noncomputable def Ns372p1450 := Ns372p1449 480971758 48 109588312 8 522351262 48 101459064 8 Bool.false 278024921 84539 Bool.false 240875496 Bool.true 331879822 14148475504056880 1 Bool.false 167422746 Bool.true Bool.false 88113259 Bool.false Bool.false 242978554 

noncomputable def Ns372p1451 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 727142 1000 226 122 268435456 134217728 4503599627370496 Bool.false 365998623826 2526 

noncomputable def Ns372p1452 := Ns372p1451 372130544 47 134217720 8 432030192 47 120047984 16 Bool.false 406273375 49746 Bool.false 112297012 Bool.false 409119706 14148475504056880 1 Bool.false 245286919 Bool.true Bool.false 12533164 Bool.true Bool.false 278024921 

noncomputable def Ns372p1453 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 727142 1000 547 359 268435456 134217728 4503599627370496 Bool.false 365998623826 2526 

noncomputable def Ns372p1454 := Ns372p1453 186065264 47 189812528 16 294906480 47 154981288 8 Bool.false 268435448 2575 Bool.false 56142368 Bool.false 184719398 14148475504056880 1 Bool.false 55733962 Bool.false Bool.false 170482405 Bool.false Bool.false 406273375 

noncomputable def Ns372p1455 := nat_lit 255274760744019208014772899975242998168900646327692289809 

noncomputable def Ns372p1456 := nat_lit 187226924760586335294318104038437239909069711474688000 

noncomputable def Ns372p1457 := nat_lit 97574853860403357892594255631360000 

noncomputable def Ns372p1458 := nat_lit 425704740247479856621607959910846238720 

noncomputable abbrev qz786 := (@Eq.refl Real (Enclosure.sfrac Bool.false 727142 1000))

noncomputable abbrev qz709 := qz786

noncomputable abbrev qz524 := qz709

noncomputable abbrev qz226 := qz524

noncomputable def Ns372p1459 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz223 727142 1000 2114942952656 16000000 1454284 4000 2000 Ns372p1457 Ns372p1458 qz226 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns372p1460 := nat_lit 5228027100037513380142548991492976602499085236791138095288320 

noncomputable abbrev qz710 := (@HSub.hSub Real Real Real qz737 qz738 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz739 (@Nat.cast Real Real.instNatCast 1454284))))

noncomputable abbrev qz525 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 727142 4000) (Real.log (Enclosure.sfrac Bool.false 2114942952656 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz710))

noncomputable abbrev qz711 := (Enclosure.sfrac Bool.false 727142 2000)

noncomputable abbrev qz227 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz525 qz711) (@HMul.hMul Real Real Real qz349 qz711 (Real.log Real.pi)))

noncomputable def Ns372p1461 := @Enclosure.Real.IsNear.addLit_ft_p qz227 (Enclosure.sfrac Bool.true Ns372p1457 Ns372p1458) 12280877999794868214181 9007199254740992000 173372014532059087 18432000000000000000000 Ns372p1457 Ns372p1458 0 1 Ns372p1460 

noncomputable def Ns372p1462 := nat_lit 412077885744412919441697800192000 

noncomputable abbrev qz228 := (@HSub.hSub Real Real Real qz353 qz525 qz711)

noncomputable def Ns372p1463 := @Enclosure.Real.IsNear.subLit_ff_p qz228 (@HMul.hMul Real Real Real qz5 qz711 (Real.log Real.pi)) 16029589554783439313317 9007199254740992000 71791266566113 18000000000000000000 13965038787531 33554432000 363571 67108864000 Ns372p1462 12280877999794868214181 9007199254740992000 

noncomputable def Ns372p1464 := nat_lit 32059179109566878626634000 

noncomputable abbrev qz229 := qz525

noncomputable def Ns372p1465 := @Enclosure.Real.IsNear.subLit_ff_p qz229 qz711 19304345995028876515749 9007199254740992000 71791266566113 18000000000000000000 727142 2000 0 1 Ns372p1464 16029589554783439313317 9007199254740992000 71791266566113 18000000000000000000 

noncomputable def Ns372p1466 := nat_lit 43469522714921587552165237329600970752 

noncomputable def Ns372p1467 := nat_lit 57022369687874521064800256 

noncomputable def Ns372p1468 := nat_lit 53225231670570452644363008 

noncomputable def Ns372p1469 := BSN.log_dyadic_bound 17790952656 4212094952656 2 1 Ns372p1468 134217728 46080000 316517996408033454336 316517996408033454336 1133818 4229885905312 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 17790952656) (BSN.artanhQ 4212094952656) 0 1 316517996408033454336 Ns372p1468 316517996408033454336 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz526 := (Real.log (Enclosure.sfrac Bool.false 2114942952656 16000000))

noncomputable def Ns372p1470 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 727142 4000) qz526 727142 4000 0 1 53106220148386919 4503599627370496 195312653 9000000000000000 19307881565569180527749 9007199254740992000 71010016563863 18000000000000000000 (Enclosure.Real.IsNear.const Bool.false 727142 4000) (BSN.isNear_log_sfrac 2114942952656 16000000 53106220148386919 4503599627370496 195312653 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2114942952656) qz356)) Bool.false Ns372p1467 Ns372p98 1000000783360000 46080000000000000000000 53106220148386919 4503599627370496 195312653 9000000000000000 (BSN.log_rat_reduce_isNear 2114942952656 16000000 17 4229885905312 4194304000000 1133818 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns372p1469 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p1471 := BSN.arctan_dyadic_bound_f 1000 1454284 1 0 16777216 5760000 0 1 1 0 1 1 11536 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1454284) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1454284) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns372p1472 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1454284))) 884279719003555 562949953421312 1 2000000000000000 11536 16777216 1 5760000 14829257659479278747648 883892635076003 562949953421312 3125000009 18000000000000000 qz17 (Ns372p1471 rfl) rfl rfl 

noncomputable abbrev qz527 := (@HMul.hMul Real Real Real qz584 qz589 qz710)

noncomputable abbrev qz230 := qz527

noncomputable abbrev qz528 := qz710

noncomputable abbrev qz231 := qz528

noncomputable def Ns372p1473 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 727142 4000) qz526) qz230 19307881565569180527749 9007199254740992000 71010016563863 18000000000000000000 883892635076003 2251799813685248 3125000009 72000000000000000 Ns372p1466 19304345995028876515749 9007199254740992000 71791266566113 18000000000000000000 (Ns372p1470 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz231 1 4 0 1 883892635076003 562949953421312 3125000009 18000000000000000 883892635076003 2251799813685248 3125000009 72000000000000000 qz363 Ns372p1472 rfl) 

noncomputable def Ns372p1474 := @Ns372p1461 Ns372p1455 Ns372p1456 173372014532059087 18432000000000000000000 (@Ns372p1463 173372014532059087 18432000000000000000000 (Ns372p1465 (Ns372p1473 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 727142 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz711 (Real.log Real.pi) 727142 2000 0 1 38410761 33554432 1 67108864 13965038787531 33554432000 363571 67108864000 (Enclosure.Real.IsNear.const Bool.false 727142 2000) RS373to384.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns372p1457 Ns372p1458) 

noncomputable def Ns372p1475 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns372p1455 Ns372p1456 173372014532059087 18432000000000000000000 22874913989 16777216 79 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz364 qz227 (Enclosure.sfrac Bool.true Ns372p1457 Ns372p1458)) Bool.false Ns372p1455 Ns372p1456 173372014532059087 18432000000000000000000 Ns372p1459 (Ns372p1474 rfl rfl)) 

noncomputable def Ns372p1476 := nat_lit 3797737101056058377371648 

noncomputable def Ns372p1477 := nat_lit 3510037589091149173191042865422645291477483147483362686515795530709714925856066987702375909745264285222000903712402194911268354587078892241 

noncomputable def Ns372p1478 := nat_lit 2500927542909034698541209686991278939951083790914386420342324437825870997568937227696396543909465824368279171323652512416110561925841 

noncomputable def Ns372p1479 := nat_lit 17528384609960387368742828392327347590364393312499481796345586947170959986658743482426804492486646572009399537247585245023650554338387630801 

noncomputable def Ns372p1480 := BSN.sin_dyadic_bound_f 107938180379 68719476736 4 3 33554432 11531251 Ns372p1477 Ns372p111 Ns372p1478 Ns372p1479 Ns372p114 Ns372p1478 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107938180379) qz365 0 3 Ns372p1477 Ns372p111 Ns372p1478 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107938180379) qz366 0 3 Ns372p1479 Ns372p114 Ns372p1478 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1481 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz223) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 22874913989) qz411) Bool.false 22874913989 16777216 79 8388608 Bool.false 33554431 33554432 1 5760000 (Ns372p1475 rfl) (Enclosure.sfrac_false_div 22874913989 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 22874913989) qz411) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns372p1476) qz412) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 216 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 22874913989 16777216 226375608064910080 72057594037927936 216 Ns372p1476 Ns372p403 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554431 33554432 Ns372p1476 Ns372p403 107938180379 68719476736 11531251 11520000 (Ns372p1480 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p1482 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns372p1455 Ns372p1456 173372014532059087 18432000000000000000000 365998623826 268435456 2526 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz364 qz227 (Enclosure.sfrac Bool.true Ns372p1457 Ns372p1458)) Bool.false Ns372p1455 Ns372p1456 173372014532059087 18432000000000000000000 Ns372p1459 (Ns372p1474 rfl rfl)) 

noncomputable def Ns372p1483 := Ns372p1454 49746 BSN.abs_quadSignPos (BSN.cos_quad_nat3 547 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 55733962 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 359 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 170482405 268435456) qz226 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) Bool.false 33554431 33554432 452567 47185920000 268435448 268435456 2575 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 33554431 33554432 452567 47185920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz223) qz223) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 33554431 33554432 463428608 48318382080000 33554431 33554432 452567 47185920000 (Ns372p1481 rfl rfl) rfl)) rfl) (Ns372p1482 rfl) RS373to384.d7 

noncomputable def Ns372p1484 := nat_lit 9934886416408670459445589835776 

noncomputable def Ns372p1485 := BSN.sin_dyadic_bound_f 56142368 268435456 2 1 268435456 134217728 Ns372p1484 Ns372p130 Ns372p1484 Ns372p1484 Ns372p131 Ns372p1484 55733962 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 56142368) qz369 0 1 Ns372p1484 Ns372p130 Ns372p1484 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 56142368) qz370 0 1 Ns372p1484 Ns372p131 Ns372p1484 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1486 := nat_lit 18281992268576252511393979759618587808546678469804955795180921449816320 

noncomputable def Ns372p1487 := nat_lit 1355501605706509002669852441629598687891453892628390707642276454656 

noncomputable def Ns372p1488 := nat_lit 47879213700814279372408481514095567767365666971758247783375754397163776 

noncomputable def Ns372p1489 := BSN.sin_dyadic_bound_f 184719398 268435456 3 2 268435456 134217728 Ns372p1486 Ns372p120 Ns372p1487 Ns372p1488 Ns372p123 Ns372p1487 170482405 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 184719398) qz369 0 2 Ns372p1486 Ns372p120 Ns372p1487 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 184719398) qz370 0 2 Ns372p1488 Ns372p123 Ns372p1487 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1490 := nat_lit 1387233335164424228173558950492214140493367733944351290009394337611776 

noncomputable def Ns372p1491 := nat_lit 25289812275955732632973339249417008648161564993034805663141789696 

noncomputable def Ns372p1492 := nat_lit 4161649425868720773055410904798143587462806878703067800416856729255936 

noncomputable def Ns372p1493 := BSN.cos_dyadic_bound_f 112297012 268435456 3 2 268435456 134217728 Ns372p1490 Ns372p159 Ns372p1491 Ns372p1492 Ns372p162 Ns372p1491 245286919 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 112297012) qz371 0 2 Ns372p1490 Ns372p159 Ns372p1491 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 112297012) qz372 0 2 Ns372p1492 Ns372p162 Ns372p1491 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1494 := nat_lit 15123055935114423416581757987133746157097044220308399780951543503826869247373157541280073416698770276443426816 

noncomputable def Ns372p1495 := nat_lit 21988964751367346083374014325544979474633203134462135099627409779091288401625947122207696963205209460736 

noncomputable def Ns372p1496 := nat_lit 91550616508454603773565043635958273683601997739142438784046547817358774413979750903883889772678474876905000960 

noncomputable def Ns372p1497 := BSN.cos_dyadic_bound_f 409119706 268435456 4 3 268435456 134217728 Ns372p1494 Ns372p143 Ns372p1495 Ns372p1496 Ns372p146 Ns372p1495 12533164 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 409119706) qz371 0 3 Ns372p1494 Ns372p143 Ns372p1495 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 409119706) qz372 0 3 Ns372p1496 Ns372p146 Ns372p1495 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1498 := Ns372p1452 84539 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 226 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 245286919 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 122 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 12533164 268435456) qz226 rfl rfl (Ns372p1483 RS373to384.d9 RS373to384.d11 RS373to384.d13 RS373to384.d17 (Ns372p1485 rfl rfl) (Ns372p1489 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns372p1482 rfl) RS373to384.d19 RS373to384.d21 RS373to384.d23 RS373to384.d25 RS373to384.d17 (Ns372p1493 rfl rfl) (Ns372p1497 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns372p1499 := nat_lit 29376960286975741633366381126578971910998329562065310951299402973577216 

noncomputable def Ns372p1500 := nat_lit 11332897884352148183700182890904114513163785845555156722760638529536 

noncomputable def Ns372p1501 := nat_lit 88108215065158520603731743013955107503968661114504822540452687643672576 

noncomputable def Ns372p1502 := BSN.cos_dyadic_bound_f 240875496 268435456 3 2 268435456 134217728 Ns372p1499 Ns372p159 Ns372p1500 Ns372p1501 Ns372p162 Ns372p1500 167422746 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 240875496) qz371 0 2 Ns372p1499 Ns372p159 Ns372p1500 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 240875496) qz372 0 2 Ns372p1501 Ns372p162 Ns372p1500 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1503 := nat_lit 6536900083205137817746322523604873226344609899214761645886084936551934154715238650608219024976062791866781696 

noncomputable def Ns372p1504 := nat_lit 1785542459009775824603317776739151704531759192759832336558902666778116075404306771658067684574754902016 

noncomputable def Ns372p1505 := nat_lit 39620466571571834826456793505512040563949485097296800981207401285680026202446120138059708694584852978836049920 

noncomputable def Ns372p1506 := BSN.cos_dyadic_bound_f 331879822 268435456 4 3 268435456 134217728 Ns372p1503 Ns372p143 Ns372p1504 Ns372p1505 Ns372p146 Ns372p1504 88113259 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 331879822) qz371 0 3 Ns372p1503 Ns372p143 Ns372p1504 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 331879822) qz372 0 3 Ns372p1505 Ns372p146 Ns372p1504 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1507 := Ns372p1450 113986 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 167422746 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 88113259 268435456) qz226 rfl rfl (Ns372p1498 rfl rfl) (Ns372p1482 rfl) RS373to384.d27 RS373to384.d29 RS373to384.d31 RS373to384.d33 RS373to384.d17 (Ns372p1502 rfl rfl) (Ns372p1506 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p1508 := nat_lit 35878780232092360523119556966881072096091666813938658479525593254122881 

noncomputable def Ns372p1509 := nat_lit 16901625714654210159315107436901148913910770152701100819376639497601 

noncomputable def Ns372p1510 := nat_lit 107602537444847773149040040685769413990447178901510573236938026483373441 

noncomputable def Ns372p1511 := BSN.cos_dyadic_bound_f 253215951 268435456 3 2 268435456 134217728 Ns372p1508 Ns372p159 Ns372p1509 Ns372p1510 Ns372p162 Ns372p1509 157603155 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 253215951) qz371 0 2 Ns372p1508 Ns372p159 Ns372p1509 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 253215951) qz372 0 2 Ns372p1510 Ns372p162 Ns372p1509 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1512 := nat_lit 7427542394679536760788978796816 

noncomputable def Ns372p1513 := BSN.sin_dyadic_bound_f 52204902 268435456 2 1 268435456 134217728 Ns372p1512 Ns372p130 Ns372p1512 Ns372p1512 Ns372p131 Ns372p1512 51876442 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 52204902) qz369 0 1 Ns372p1512 Ns372p130 Ns372p1512 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 52204902) qz370 0 1 Ns372p1512 Ns372p131 Ns372p1512 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1514 := Ns372p1448 139715 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 94 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 157603155 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 149 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 51876442 268435456) qz226 rfl rfl (Ns372p1507 rfl) (Ns372p1482 rfl) RS373to384.d35 RS373to384.d37 RS373to384.d39 RS373to384.d41 RS373to384.d17 (Ns372p1511 rfl rfl) (Ns372p1513 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p1515 := nat_lit 28610763440635232332233234626408443108765457376821953696503464746955417298203156741759975826760147437245956096 

noncomputable def Ns372p1516 := nat_lit 8520007657508401837779002481693414495718784486304905627156460992883700115445801281300323674330178256896 

noncomputable def Ns372p1517 := nat_lit 142938899968355696054455748825215585140029045427668158523480607927414033017049760305257602067971708371500793856 

noncomputable def Ns372p1518 := BSN.sin_dyadic_bound_f 378039052 268435456 4 3 268435456 134217728 Ns372p1515 Ns372p134 Ns372p1516 Ns372p1517 Ns372p137 Ns372p1516 264899447 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 378039052) qz369 0 3 Ns372p1515 Ns372p134 Ns372p1516 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 378039052) qz370 0 3 Ns372p1517 Ns372p137 Ns372p1516 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1519 := Ns372p1446 Bool.false 169965277 139715 Bool.true 378039052 14148475504056880 1 Bool.false 264899447 Bool.true Bool.false 86196717 151561 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 197 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 264899447 268435456) qz226 rfl (Ns372p1514 rfl) (Ns372p1482 rfl) RS373to384.d43 RS373to384.d45 RS373to384.d17 (Ns372p1518 rfl rfl) rfl 

noncomputable def Ns372p1520 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) 86196717 268435456 151561 268435456 86196717 268435456 151561 268435456 46276510067195904 86196717 134217728 151561 134217728 (Ns372p1519 rfl rfl rfl rfl) 

noncomputable def Ns372p1521 := @Enclosure.Real.IsNear.mulLit_ff qz708 (Zeta.RiemannSiegel.correction qz225) 2557585 8388608 1 16777216 35736931357463 70368744177664 8227676120963 19791209299968000 91400239585877006855 590295810358705651712 

noncomputable abbrev qz712 := (@HPow.hPow Real Real Real qz7 qz224 qz9)

noncomputable def Ns372p1522 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz712 1 1 0 1 2557585 8388608 1 16777216 2557585 8388608 1 16777216 

noncomputable def Ns372p1523 := @Enclosure.Real.IsNear.sqrt_image qz224 1941597480563 16777216000 363571 16777216000 180484332 180484367 16777216 (@Enclosure.Real.IsNear.of_eq qz224 (@HMul.hMul Real Real Real qz5 qz223 qz3) Bool.false 1941597480563 16777216000 363571 16777216000 (BSN.t_div_two_pi_mk qz223 727142 1000 qz226) (@Enclosure.Real.IsNear.mulLit_ff qz223 qz3 727142 1000 0 1 5340353 33554432 1 33554432 1941597480563 16777216000 363571 16777216000 (Enclosure.Real.IsNear.const Bool.false 727142 1000) RS373to384.d48 rfl)) 

noncomputable abbrev qz787 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 727142 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz713 := qz787

noncomputable abbrev qz529 := qz713

noncomputable abbrev qz232 := qz529

noncomputable def Ns372p1524 := @Enclosure.Real.IsNear.sqrt_image qz232 360968699 33554432 35 33554432 55027489 55027496 16777216 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 360968699 33554432 35 33554432 360968699 33554432 35 33554432 (Ns372p1523 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns372p1525 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz232) 110054985 33554432 7 33554432 5115169 5115171 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz232) Bool.false 110054985 33554432 7 33554432 110054985 33554432 7 33554432 (Ns372p1524 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns372p1526 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 10230340 33554432 2 33554432 2557585 8388608 1 16777216 (Ns372p1525 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz233 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz523))

noncomputable abbrev qz714 := (@HMul.hMul Real Real Real qz733 qz785 qz785)

noncomputable abbrev qz530 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz714 qz707) qz600)

noncomputable abbrev qz234 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz530))

noncomputable def Ns372p1527 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz225) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz233) qz234) Bool.false 35736931357463 

noncomputable def Ns372p1528 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz233) qz234 173331319 8388608 24211 

noncomputable def Ns372p1529 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz233) Bool.false 693325276 33554432 96844 33554432 173331319 8388608 24211 

noncomputable def Ns372p1530 := @Enclosure.Real.IsNear.recentre' qz233 Bool.false 1623913 33554432 1306514432 193273528320000 1623913 33554432 1275893 188743680000 

noncomputable abbrev qz235 := (@HMul.hMul Real Real Real qz349 qz346 qz523)

noncomputable def Ns372p1531 := @Enclosure.Real.IsNear.cos_image qz235 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39936521) qz377) Bool.false 39936521 8388608 221 33554432 Bool.false 1623913 33554432 1 

noncomputable def Ns372p1532 := nat_lit 944512639534935343583132213 

noncomputable def Ns372p1533 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz225 884279719003555 140737488355328 1 500000000000000 25424379 33554432 35 33554432 22482262717959884667345 4722366482869645213696 Ns372p1532 

noncomputable def Ns372p1534 := @Enclosure.Real.IsNear.subLit_ff_p qz232 qz1 360968699 33554432 35 33554432 10 1 0 1 25424379 25424379 33554432 35 

noncomputable def Ns372p1535 := @Ns372p1534 33554432 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 360968699 33554432 35 33554432 360968699 33554432 35 33554432 (Ns372p1523 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns372p1536 := @Enclosure.Real.IsNear.recentre' qz235 Bool.false 22482262717959884667345 4722366482869645213696 Ns372p1532 Ns372p586 39936521 8388608 221 33554432 (@Ns372p1533 Ns372p586 RS373to384.d47 (Ns372p1535 rfl rfl) rfl) 

noncomputable def Ns372p1537 := BSN.sin_dyadic_bound_f 3327075123 68719476736 1 0 33554432 11531251 0 1 1 0 1 1 1623913 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 3327075123) qz365 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 3327075123) qz366 0 0 rfl) rfl rfl 

noncomputable def Ns372p1538 := @Ns372p1531 5760000 (Ns372p1536 rfl) (Enclosure.sfrac_false_div 39936521 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39936521) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 58530524555859975995392) (@Nat.cast Real Real.instNatCast Ns372p184)) 226375608064910080 72057594037927936 Bool.false 1623913 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 39936521 8388608 226375608064910080 72057594037927936 0 58530524555859975995392 Ns372p184 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1623913 33554432 58530524555859975995392 Ns372p184 3327075123 68719476736 11531251 11520000 (Ns372p1537 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p1539 := @Enclosure.Real.IsNear.inv_image qz233 1623913 33554432 1275893 188743680000 346614216 346711060 16777216 (Ns372p1530 (Ns372p1538 rfl rfl) rfl) rfl 

noncomputable def Ns372p1540 := @Enclosure.Real.IsNear.recentre' qz234 Bool.false 412354 16777216 

noncomputable abbrev qz236 := (@HMul.hMul Real Real Real qz349 qz346 qz530)

noncomputable def Ns372p1541 := @Enclosure.Real.IsNear.cos_image qz236 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 25941193)) qz411) Bool.true 25941193 16777216 

noncomputable def Ns372p1542 := nat_lit 245007640784995683101369814805 

noncomputable def Ns372p1543 := nat_lit 79719912813957921814938621201916717 

noncomputable def Ns372p1544 := @Enclosure.Real.IsNear.recentre' qz236 Bool.true Ns372p1542 Ns372p602 Ns372p1543 

noncomputable abbrev qz237 := qz530

noncomputable def Ns372p1545 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz237 884279719003555 140737488355328 1 500000000000000 277070292939751 

noncomputable abbrev qz531 := (@HSub.hSub Real Real Real qz588 qz714 qz707)

noncomputable abbrev qz238 := qz531

noncomputable def Ns372p1546 := @Enclosure.Real.IsNear.subLit_tf qz238 qz31 206701548762087 1125899906842624 2954112875 1125899906842624 1 16 

noncomputable abbrev qz532 := qz714

noncomputable abbrev qz239 := qz532

noncomputable def Ns372p1547 := @Enclosure.Real.IsNear.subLit_ff_n qz239 qz225 646399047535641 1125899906842624 1779707755 1125899906842624 25424379 33554432 35 33554432 

noncomputable def Ns372p1548 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz225 25424379 33554432 35 33554432 25424379 33554432 35 33554432 646399047535641 1125899906842624 

noncomputable def Ns372p1549 := nat_lit 56927283994139714742569545352118518237798031148497728982109375098627541257231528363272888986081 

noncomputable def Ns372p1550 := nat_lit 92870832327425141874199951985983322652445906881057562288084211068190505160784359824108001 

noncomputable def Ns372p1551 := nat_lit 344577703162328568907414309334406456860295007193233282173943109399578841173709517811264021408225 

noncomputable def Ns372p1552 := BSN.cos_dyadic_bound_f 25941193 16777216 4 3 16777216 5760000 Ns372p1549 Ns372p848 Ns372p1550 Ns372p1551 Ns372p851 Ns372p1550 412354 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 25941193) (BSN.cosEvenQ 16777216) 0 3 Ns372p1549 Ns372p848 Ns372p1550 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 25941193) (BSN.cosOddQ 16777216) 0 3 Ns372p1551 Ns372p851 Ns372p1550 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1553 := @Ns372p1540 1612297216 96636764160000 206177 8388608 1574509 94371840000 (@Ns372p1541 277 16777216 Bool.false 412354 16777216 1 5760000 (@Ns372p1544 Ns372p605 25941193 16777216 277 16777216 (@Ns372p1545 1125899906842624 2954112875 1125899906842624 Ns372p1542 Ns372p602 Ns372p1543 Ns372p605 RS373to384.d47 (@Ns372p1546 0 1 4433124687036016 277070292939751 1125899906842624 2954112875 1125899906842624 (@Ns372p1547 6935753062232132419584 206701548762087 1125899906842624 2954112875 1125899906842624 (@Ns372p1548 1779707755 1125899906842624 (Ns372p1535 rfl rfl) (Ns372p1535 rfl rfl) rfl) (Ns372p1535 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 25941193 16777216) (BSN.cos_neg_of_bound 25941193 16777216 Bool.false 412354 16777216 1 5760000 (Ns372p1552 rfl rfl)) rfl rfl) 

noncomputable def Ns372p1554 := @Ns372p1521 56128028404382288189 442721857769029238784000 (Ns372p1522 qz33 (@Enclosure.Real.IsNear.of_eq qz712 (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 2557585 8388608 1 16777216 (BSN.rpow_neg_quarter_mk qz224 (BSN.t_div_two_pi_nonneg qz223 727142 1000 qz226)) Ns372p1526) rfl) (@Ns372p1527 70368744177664 8227676120963 19791209299968000 (BSN.correction_mk qz225 (BSN.cos_two_pi_p_ne_zero_mk qz223 727142 1000 10 qz226 rfl rfl (@BSN.floor_sqrt_eq_dec qz223 727142 1000 10 qz226 rfl rfl rfl))) (@Ns372p1528 8388608 206177 8388608 1574509 94371840000 35736931357463 70368744177664 8227676120963 19791209299968000 (@Ns372p1529 8388608 (Ns372p1539 rfl rfl rfl rfl rfl) rfl) (Ns372p1553 rfl) rfl)) 

noncomputable def Ns372p1555 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (hardyZApproximantRS₀ qz223) Bool.false 287696930884591838713 590295810358705651712 556057273856457296189 442721857769029238784000 (@Eq.refl Real (hardyZApproximantRS₀ qz223)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (@HMul.hMul Real Real Real qz5 qz708 (Zeta.RiemannSiegel.correction qz225))) Bool.false 287696930884591838713 590295810358705651712 556057273856457296189 442721857769029238784000 (BSN.hardyZApproximantRS₀_eq qz223 10 (@BSN.floor_sqrt_eq_dec qz223 727142 1000 10 qz226 rfl rfl rfl)) (@Ns372p1445 287696930884591838713 590295810358705651712 556057273856457296189 442721857769029238784000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10)) Bool.false 86196717 134217728 151561 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (Ns372p1520 (Ns372p1519 rfl rfl rfl rfl) rfl rfl)) (Ns372p1554 rfl) rfl rfl)) 

theorem RS373to384.d62 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz223) Bool.false 287696930884591838713 590295810358705651712 556057273856457296189 442721857769029238784000 := Ns372p1555 

noncomputable def Ns372p1556 := nat_lit 37449505453700033220542726144 

noncomputable abbrev qz788 := (Enclosure.sfrac Bool.false 728464 1000)

noncomputable abbrev qz715 := qz788

noncomputable abbrev qz533 := qz715

noncomputable abbrev qz240 := qz533

noncomputable abbrev qz789 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 728464 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz716 := qz789

noncomputable abbrev qz534 := qz716

noncomputable abbrev qz241 := qz534

noncomputable abbrev qz790 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 728464 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz717 := qz790

noncomputable abbrev qz535 := qz717

noncomputable abbrev qz242 := qz535

noncomputable abbrev qz718 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz241 qz9))

noncomputable def Ns372p1557 := @Enclosure.Real.IsNear.subLit_ff_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (@HMul.hMul Real Real Real qz5 qz718 (Zeta.RiemannSiegel.correction qz242)) 13267321 134217728 151837 134217728 745822917383705209395 4722366482869645213696 485671335478932076759 Ns372p214 Ns372p1556 

noncomputable def Ns372p1558 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin BSN.quadSignNeg 9 10 728464 1000 197 268435456 134217728 4503599627370496 Bool.false 366841826113 2530 618095470 48 84886744 8 

noncomputable def Ns372p1559 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 728464 1000 94 148 268435456 134217728 4503599627370496 Bool.false 366841826113 2530 

noncomputable def Ns372p1560 := Ns372p1559 558195838 48 94906264 8 589812974 48 89478488 8 Bool.false 172407693 114194 Bool.true 147948562 Bool.true 410392795 14148475504056880 1 Bool.false 228686114 Bool.true Bool.false 11261327 Bool.false Bool.false 95308719 

noncomputable def Ns372p1561 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 728464 1000 39 32 268435456 134217728 4503599627370496 Bool.false 366841826113 2530 

noncomputable def Ns372p1562 := Ns372p1561 480971758 48 109588312 8 522351262 48 101459064 8 Bool.false 81903439 84694 Bool.false 26575690 Bool.true 179225904 14148475504056880 1 Bool.false 26532297 Bool.false Bool.false 210793599 Bool.false Bool.false 172407693 

noncomputable def Ns372p1563 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 728464 1000 227 123 268435456 134217728 4503599627370496 Bool.false 366841826113 2530 

noncomputable def Ns372p1564 := Ns372p1563 372130544 47 134217720 8 432030192 47 120047984 16 Bool.true 37761828 49839 Bool.false 41885292 Bool.false 259520651 14148475504056880 1 Bool.false 41715536 Bool.false Bool.false 220940290 Bool.false Bool.false 81903439 

noncomputable def Ns372p1565 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 728464 1000 548 360 268435456 134217728 4503599627370496 Bool.false 366841826113 2530 

noncomputable def Ns372p1566 := Ns372p1565 186065264 47 189812528 16 294906480 47 154981288 8 Bool.true 268435416 2583 Bool.false 231708948 Bool.false 216397890 14148475504056880 1 Bool.false 174488920 Bool.false Bool.false 185833962 Bool.false Bool.true 37761828 

noncomputable def Ns372p1567 := nat_lit 505208317369084324408002006761294568436142220190338787 

noncomputable def Ns372p1568 := nat_lit 369684739836635481151859330675000337843571654656000 

noncomputable def Ns372p1569 := nat_lit 98465077434163214415727366635520000 

noncomputable def Ns372p1570 := nat_lit 430369679625885888412431034579640647680 

noncomputable abbrev qz791 := (@Eq.refl Real (Enclosure.sfrac Bool.false 728464 1000))

noncomputable abbrev qz719 := qz791

noncomputable abbrev qz536 := qz719

noncomputable abbrev qz243 := qz536

noncomputable def Ns372p1571 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz240 728464 1000 2122640197184 16000000 1456928 4000 2000 Ns372p1569 Ns372p1570 qz243 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns372p1572 := nat_lit 662186645742006205688056390302164016740620330847880854896640 

noncomputable abbrev qz720 := (@HSub.hSub Real Real Real qz737 qz738 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz739 (@Nat.cast Real Real.instNatCast 1456928))))

noncomputable abbrev qz537 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 728464 4000) (Real.log (Enclosure.sfrac Bool.false 2122640197184 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz720))

noncomputable abbrev qz721 := (Enclosure.sfrac Bool.false 728464 2000)

noncomputable abbrev qz244 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz537 qz721) (@HMul.hMul Real Real Real qz349 qz721 (Real.log Real.pi)))

noncomputable def Ns372p1573 := @Enclosure.Real.IsNear.addLit_ft_p qz244 (Enclosure.sfrac Bool.true Ns372p1569 Ns372p1570) 1538646396231855937523 1125899906842624000 7236906821161871 768000000000000000000 Ns372p1569 Ns372p1570 0 1 Ns372p1572 

noncomputable def Ns372p1574 := nat_lit 6453550734300858286176468992000 

noncomputable abbrev qz245 := (@HSub.hSub Real Real Real qz353 qz537 qz721)

noncomputable def Ns372p1575 := @Enclosure.Real.IsNear.subLit_ff_p qz245 (@HMul.hMul Real Real Real qz5 qz721 (Real.log Real.pi)) 2008087271293603583987 1125899906842624000 11986728038291 3000000000000000000 1748803537569 4194304000 45529 8388608000 Ns372p1574 1538646396231855937523 1125899906842624000 

noncomputable abbrev qz246 := qz537

noncomputable def Ns372p1576 := @Enclosure.Real.IsNear.subLit_ff_p qz246 qz721 483635209232541241751 225179981368524800 11986728038291 3000000000000000000 728464 2000 0 1 803234908517441433594800 2008087271293603583987 1125899906842624000 11986728038291 3000000000000000000 

noncomputable def Ns372p1577 := nat_lit 1089049674041462301545870013390389248 

noncomputable def Ns372p1578 := nat_lit 57039937077099388762849280 

noncomputable def Ns372p1579 := nat_lit 53419938562244911012589568 

noncomputable def Ns372p1580 := BSN.log_dyadic_bound 25488197184 4219792197184 2 1 Ns372p1579 134217728 46080000 649648195690465529856 649648195690465529856 1621411 4245280394368 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 25488197184) (BSN.artanhQ 4219792197184) 0 1 649648195690465529856 Ns372p1579 649648195690465529856 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz538 := (Real.log (Enclosure.sfrac Bool.false 2122640197184 16000000))

noncomputable def Ns372p1581 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 728464 4000) qz538 728464 4000 0 1 53122581054549095 4503599627370496 195312653 9000000000000000 483723598566513149251 225179981368524800 8892389778437 2250000000000000000 (Enclosure.Real.IsNear.const Bool.false 728464 4000) (BSN.isNear_log_sfrac 2122640197184 16000000 53122581054549095 4503599627370496 195312653 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2122640197184) qz356)) Bool.false Ns372p1578 Ns372p98 1000000783360000 46080000000000000000000 53122581054549095 4503599627370496 195312653 9000000000000000 (BSN.log_rat_reduce_isNear 2122640197184 16000000 17 4245280394368 4194304000000 1621411 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns372p1580 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns372p1582 := BSN.arctan_dyadic_bound_f 1000 1456928 1 0 16777216 5760000 0 1 1 0 1 1 11515 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1456928) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1456928) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns372p1583 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1456928))) 884279719003555 562949953421312 1 2000000000000000 11515 16777216 1 5760000 14829269481428300595200 883893339719075 562949953421312 3125000009 18000000000000000 qz17 (Ns372p1582 rfl) rfl rfl 

noncomputable abbrev qz539 := (@HMul.hMul Real Real Real qz584 qz589 qz720)

noncomputable abbrev qz247 := qz539

noncomputable abbrev qz540 := qz720

noncomputable abbrev qz248 := qz540

noncomputable def Ns372p1584 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 728464 4000) qz538) qz247 483723598566513149251 225179981368524800 8892389778437 2250000000000000000 883893339719075 2251799813685248 3125000009 72000000000000000 Ns372p1577 483635209232541241751 225179981368524800 11986728038291 3000000000000000000 (Ns372p1581 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz248 1 4 0 1 883893339719075 562949953421312 3125000009 18000000000000000 883893339719075 2251799813685248 3125000009 72000000000000000 qz363 Ns372p1583 rfl) 

noncomputable def Ns372p1585 := @Ns372p1573 Ns372p1567 Ns372p1568 7236906821161871 768000000000000000000 (@Ns372p1575 7236906821161871 768000000000000000000 (Ns372p1576 (Ns372p1584 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 728464 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz721 (Real.log Real.pi) 728464 2000 0 1 38410761 33554432 1 67108864 1748803537569 4194304000 45529 8388608000 (Enclosure.Real.IsNear.const Bool.false 728464 2000) RS373to384.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns372p1569 Ns372p1570) 

noncomputable def Ns372p1586 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns372p1567 Ns372p1568 7236906821161871 768000000000000000000 5731903533 4194304 317 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz364 qz244 (Enclosure.sfrac Bool.true Ns372p1569 Ns372p1570)) Bool.false Ns372p1567 Ns372p1568 7236906821161871 768000000000000000000 Ns372p1571 (Ns372p1585 rfl rfl)) 

noncomputable def Ns372p1587 := nat_lit 3506283099367896998711257190418898187448033667130775565720243481542701567129018868349413879329377443216185607001577742674839191402821062656 

noncomputable def Ns372p1588 := nat_lit 2492926867999569531888211686093446347754608210943628570397192976551678404051841809576733608941635820150625514125318281812596261523456 

noncomputable def Ns372p1589 := nat_lit 17509658697282751771302793296707970170558890725980409333437516851258491305731964271692426101228408909909299293841718167636242894281603158016 

noncomputable def Ns372p1590 := BSN.sin_dyadic_bound_f 107909362834 68719476736 4 3 33554432 11531251 Ns372p1587 Ns372p111 Ns372p1588 Ns372p1589 Ns372p114 Ns372p1588 33554427 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107909362834) qz365 0 3 Ns372p1587 Ns372p111 Ns372p1588 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107909362834) qz366 0 3 Ns372p1589 Ns372p114 Ns372p1588 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1591 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz240) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5731903533) qz608) Bool.false 5731903533 4194304 317 33554432 Bool.true 33554427 33554432 1 5760000 (Ns372p1586 rfl) (Enclosure.sfrac_false_div 5731903533 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5731903533) qz608) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949180793463220203421696) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 33554427 33554432 217 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q1 5731903533 4194304 226375608064910080 72057594037927936 217 949180793463220203421696 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554427 33554432 949180793463220203421696 604462909807314587353088 107909362834 68719476736 11531251 11520000 (Ns372p1590 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p1592 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns372p1567 Ns372p1568 7236906821161871 768000000000000000000 366841826113 268435456 2530 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz364 qz244 (Enclosure.sfrac Bool.true Ns372p1569 Ns372p1570)) Bool.false Ns372p1567 Ns372p1568 7236906821161871 768000000000000000000 Ns372p1571 (Ns372p1585 rfl rfl)) 

noncomputable def Ns372p1593 := Ns372p1566 49839 BSN.abs_quadSignPos (BSN.cos_quad_nat0 548 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 174488920 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 360 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 185833962 268435456) qz243 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) Bool.true 33554427 33554432 1815893 188743680000 268435416 268435456 2583 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 33554427 33554432 1815893 188743680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz240) qz240) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 33554427 33554432 1859474432 193273528320000 33554427 33554432 1815893 188743680000 (Ns372p1591 rfl rfl) rfl)) rfl) (Ns372p1592 rfl) RS373to384.d7 

noncomputable def Ns372p1594 := nat_lit 25152635986371428263079856094503135380176555692196187391011037800103936 

noncomputable def Ns372p1595 := nat_lit 8308879173024858759018121830188880488578465376302616035516397715456 

noncomputable def Ns372p1596 := nat_lit 75441290200768235071721532039849028379552510145835956940962080604880896 

noncomputable def Ns372p1597 := BSN.cos_dyadic_bound_f 231708948 268435456 3 2 268435456 134217728 Ns372p1594 Ns372p159 Ns372p1595 Ns372p1596 Ns372p162 Ns372p1595 174488920 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 231708948) qz371 0 2 Ns372p1594 Ns372p159 Ns372p1595 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 231708948) qz372 0 2 Ns372p1596 Ns372p162 Ns372p1595 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1598 := nat_lit 19133307259506713924068165971266863154353258641190585328776410544800000 

noncomputable def Ns372p1599 := nat_lit 4808661148221230901830180612220164266251616140369889863248100000000 

noncomputable def Ns372p1600 := nat_lit 57390304456223699310400837552576149134527272691291016206602735434400000 

noncomputable def Ns372p1601 := BSN.cos_dyadic_bound_f 216397890 268435456 3 2 268435456 134217728 Ns372p1598 Ns372p159 Ns372p1599 Ns372p1600 Ns372p162 Ns372p1599 185833962 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 216397890) qz371 0 2 Ns372p1598 Ns372p159 Ns372p1599 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 216397890) qz372 0 2 Ns372p1600 Ns372p162 Ns372p1599 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1602 := nat_lit 3077841064872484254523793469696 

noncomputable def Ns372p1603 := BSN.sin_dyadic_bound_f 41885292 268435456 2 1 268435456 134217728 Ns372p1602 Ns372p130 Ns372p1602 Ns372p1602 Ns372p131 Ns372p1602 41715536 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 41885292) qz369 0 1 Ns372p1602 Ns372p130 Ns372p1602 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 41885292) qz370 0 1 Ns372p1602 Ns372p131 Ns372p1602 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1604 := nat_lit 71245007776108261249277586969623694014765151639075832639644085641815905 

noncomputable def Ns372p1605 := nat_lit 20576683407401051789896450286174915574105978008714492125297732495201 

noncomputable def Ns372p1606 := nat_lit 186560753354766796807114800191408248746788749376041642973722123209287521 

noncomputable def Ns372p1607 := BSN.sin_dyadic_bound_f 259520651 268435456 3 2 268435456 134217728 Ns372p1604 Ns372p120 Ns372p1605 Ns372p1606 Ns372p123 Ns372p1605 220940290 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 259520651) qz369 0 2 Ns372p1604 Ns372p120 Ns372p1605 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 259520651) qz370 0 2 Ns372p1606 Ns372p123 Ns372p1605 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1608 := Ns372p1564 84694 BSN.abs_quadSignPos (BSN.cos_quad_nat3 227 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 41715536 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 123 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 220940290 268435456) qz243 rfl rfl (Ns372p1593 RS373to384.d9 RS373to384.d11 RS373to384.d13 RS373to384.d17 (Ns372p1597 rfl rfl) (Ns372p1601 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns372p1592 rfl) RS373to384.d19 RS373to384.d21 RS373to384.d23 RS373to384.d25 RS373to384.d17 (Ns372p1603 rfl rfl) (Ns372p1607 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns372p1609 := nat_lit 498813497602995824108371210000 

noncomputable def Ns372p1610 := BSN.sin_dyadic_bound_f 26575690 268435456 2 1 268435456 134217728 Ns372p1609 Ns372p130 Ns372p1609 Ns372p1609 Ns372p131 Ns372p1609 26532297 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 26575690) qz369 0 1 Ns372p1609 Ns372p130 Ns372p1609 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 26575690) qz370 0 1 Ns372p1609 Ns372p131 Ns372p1609 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1611 := nat_lit 9001674038446679450400940278182247994226266180841549553616628289110016 

noncomputable def Ns372p1612 := nat_lit 1064648476252813644149242379410178212618208739034420150774410510336 

noncomputable def Ns372p1613 := nat_lit 27002892818387532723914522349787923626253562125046579820548336046309376 

noncomputable def Ns372p1614 := BSN.cos_dyadic_bound_f 179225904 268435456 3 2 268435456 134217728 Ns372p1611 Ns372p159 Ns372p1612 Ns372p1613 Ns372p162 Ns372p1612 210793599 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 179225904) qz371 0 2 Ns372p1611 Ns372p159 Ns372p1612 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 179225904) qz372 0 2 Ns372p1613 Ns372p162 Ns372p1612 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1615 := Ns372p1562 114194 BSN.abs_quadSignPos (BSN.cos_quad_nat3 39 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 26532297 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 210793599 268435456) qz243 rfl rfl (Ns372p1608 rfl rfl) (Ns372p1592 rfl) RS373to384.d27 RS373to384.d29 RS373to384.d31 RS373to384.d33 RS373to384.d17 (Ns372p1610 rfl rfl) (Ns372p1614 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p1616 := nat_lit 4179608875022653964312173625584222503372168236941815858763613637918976 

noncomputable def Ns372p1617 := nat_lit 229554593063077115611563399567505161706705109852211208111211888896 

noncomputable def Ns372p1618 := nat_lit 12538367515881835738705297749953532499793091300605743153874618489979136 

noncomputable def Ns372p1619 := BSN.cos_dyadic_bound_f 147948562 268435456 3 2 268435456 134217728 Ns372p1616 Ns372p159 Ns372p1617 Ns372p1618 Ns372p162 Ns372p1617 228686114 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 147948562) qz371 0 2 Ns372p1616 Ns372p159 Ns372p1617 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 147948562) qz372 0 2 Ns372p1618 Ns372p162 Ns372p1617 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1620 := nat_lit 15312788235552470408406508034007494499375210514884288019830971626604809509345129045219624765752996827618140625 

noncomputable def Ns372p1621 := nat_lit 22824261294806629051263324648689834210343706653344038505126307281022643535647668680643647947968994140625 

noncomputable def Ns372p1622 := nat_lit 92696726906557827079391014531758037696556125018479217537469087684063422577115975284147467605448813325179740625 

noncomputable def Ns372p1623 := BSN.cos_dyadic_bound_f 410392795 268435456 4 3 268435456 134217728 Ns372p1620 Ns372p143 Ns372p1621 Ns372p1622 Ns372p146 Ns372p1621 11261327 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 410392795) qz371 0 3 Ns372p1620 Ns372p143 Ns372p1621 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 410392795) qz372 0 3 Ns372p1622 Ns372p146 Ns372p1621 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1624 := Ns372p1560 139969 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 94 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 228686114 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 148 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 11261327 268435456) qz243 rfl rfl (Ns372p1615 rfl) (Ns372p1592 rfl) RS373to384.d35 RS373to384.d37 RS373to384.d39 RS373to384.d41 RS373to384.d17 (Ns372p1619 rfl rfl) (Ns372p1623 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns372p1625 := nat_lit 21488721719010245258235925974775123280895833342015558914247218626580201368815116691416035525497476773761253376 

noncomputable def Ns372p1626 := nat_lit 3613304365552928404339781298728399869616278684402422908497550408140051773963545084682022163290915864576 

noncomputable def Ns372p1627 := nat_lit 107378745722665320727099872213794642660803124817134672563801568421442628731197275402418949922938442841887604736 

noncomputable def Ns372p1628 := BSN.sin_dyadic_bound_f 351958976 268435456 4 3 268435456 134217728 Ns372p1625 Ns372p134 Ns372p1626 Ns372p1627 Ns372p137 Ns372p1626 259437680 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 351958976) qz369 0 3 Ns372p1625 Ns372p134 Ns372p1626 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 351958976) qz370 0 3 Ns372p1627 Ns372p137 Ns372p1626 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1629 := Ns372p1558 Bool.false 95308719 139969 Bool.true 351958976 14148475504056880 1 Bool.false 259437680 Bool.true Bool.false 13267321 151837 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 197 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 259437680 268435456) qz243 rfl (Ns372p1624 rfl) (Ns372p1592 rfl) RS373to384.d43 RS373to384.d45 RS373to384.d17 (Ns372p1628 rfl rfl) rfl 

noncomputable def Ns372p1630 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) 13267321 268435456 151837 268435456 13267321 268435456 151837 268435456 7122838725066752 13267321 134217728 151837 134217728 (Ns372p1629 rfl rfl rfl rfl) 

noncomputable def Ns372p1631 := @Enclosure.Real.IsNear.mulLit_ff qz718 (Zeta.RiemannSiegel.correction qz242) 10225695 33554432 1 33554432 72936159095661 140737488355328 11870453125651 65970697666560000 745822917383705209395 4722366482869645213696 

noncomputable abbrev qz722 := (@HPow.hPow Real Real Real qz7 qz241 qz9)

noncomputable def Ns372p1632 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz722 1 1 0 1 10225695 33554432 1 33554432 10225695 33554432 1 33554432 

noncomputable def Ns372p1633 := @Enclosure.Real.IsNear.sqrt_image qz241 243140931737 2097152000 45529 2097152000 180648325 180648359 16777216 (@Enclosure.Real.IsNear.of_eq qz241 (@HMul.hMul Real Real Real qz5 qz240 qz3) Bool.false 243140931737 2097152000 45529 2097152000 (BSN.t_div_two_pi_mk qz240 728464 1000 qz243) (@Enclosure.Real.IsNear.mulLit_ff qz240 qz3 728464 1000 0 1 5340353 33554432 1 33554432 243140931737 2097152000 45529 2097152000 (Enclosure.Real.IsNear.const Bool.false 728464 1000) RS373to384.d48 rfl)) 

noncomputable abbrev qz792 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 728464 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz723 := qz792

noncomputable abbrev qz541 := qz723

noncomputable abbrev qz249 := qz541

noncomputable def Ns372p1634 := @Enclosure.Real.IsNear.sqrt_image qz249 90324171 8388608 17 16777216 55052483 55052489 16777216 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 361296684 33554432 34 33554432 90324171 8388608 17 16777216 (Ns372p1633 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns372p1635 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz249) 27526243 8388608 3 16777216 5112847 5112848 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz249) Bool.false 110104972 33554432 6 33554432 27526243 8388608 3 16777216 (Ns372p1634 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns372p1636 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 10225695 33554432 1 33554432 10225695 33554432 1 33554432 (Ns372p1635 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz535))

noncomputable abbrev qz724 := (@HMul.hMul Real Real Real qz733 qz790 qz790)

noncomputable abbrev qz542 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz724 qz717) qz600)

noncomputable abbrev qz251 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz542))

noncomputable def Ns372p1637 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz242) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz250) qz251) Bool.false 72936159095661 

noncomputable def Ns372p1638 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz250) qz251 76530731 8388608 9149 

noncomputable def Ns372p1639 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz250) Bool.false 306122924 33554432 18298 33554432 76530731 8388608 9149 

noncomputable def Ns372p1640 := @Enclosure.Real.IsNear.recentre' qz250 Bool.false 3677934 33554432 633097216 96636764160000 1838967 16777216 618259 94371840000 

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz349 qz346 qz535)

noncomputable def Ns372p1641 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 161806875) qz367) Bool.false 161806875 33554432 107 16777216 Bool.false 3677934 33554432 1 

noncomputable def Ns372p1642 := nat_lit 458763282064354333912560183 

noncomputable def Ns372p1643 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz242 884279719003555 140737488355328 1 500000000000000 6438091 8388608 17 16777216 5693073300399316413505 1180591620717411303424 Ns372p1642 

noncomputable def Ns372p1644 := @Enclosure.Real.IsNear.subLit_ff_p qz249 qz1 90324171 8388608 17 16777216 10 1 0 1 6438091 6438091 8388608 17 

noncomputable def Ns372p1645 := @Ns372p1644 16777216 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 361296684 33554432 34 33554432 90324171 8388608 17 16777216 (Ns372p1633 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns372p1646 := @Enclosure.Real.IsNear.recentre' qz252 Bool.false 5693073300399316413505 1180591620717411303424 Ns372p1642 Ns372p179 161806875 33554432 107 16777216 (@Ns372p1643 Ns372p179 RS373to384.d47 (Ns372p1645 rfl rfl) rfl) 

noncomputable def Ns372p1647 := nat_lit 3245112595497199873242590767768379874961 

noncomputable def Ns372p1648 := nat_lit 2676089423823674776984286192717803380717649920 

noncomputable def Ns372p1649 := nat_lit 18732625966765723438890003349024623665023549440 

noncomputable def Ns372p1650 := BSN.sin_dyadic_bound_f 7547575091 68719476736 2 1 33554432 11531251 Ns372p1647 Ns372p1648 Ns372p1647 Ns372p1647 Ns372p1649 Ns372p1647 3677934 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 7547575091) qz365 0 1 Ns372p1647 Ns372p1648 Ns372p1647 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 7547575091) qz366 0 1 Ns372p1647 Ns372p1649 Ns372p1647 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1651 := @Ns372p1641 5760000 (Ns372p1646 rfl) (Enclosure.sfrac_false_div 161806875 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 161806875) qz367) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 531113380773471002296320) qz368) 226375608064910080 72057594037927936 Bool.false 3677934 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 161806875 33554432 226375608064910080 72057594037927936 0 531113380773471002296320 Ns372p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 3677934 33554432 531113380773471002296320 Ns372p98 7547575091 68719476736 11531251 11520000 (Ns372p1650 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns372p1652 := @Enclosure.Real.IsNear.inv_image qz250 1838967 16777216 618259 94371840000 153052313 153070611 16777216 (Ns372p1640 (Ns372p1651 rfl rfl) rfl) rfl 

noncomputable def Ns372p1653 := @Enclosure.Real.IsNear.recentre' qz251 Bool.false 953031 16777216 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz349 qz346 qz542)

noncomputable def Ns372p1654 := @Enclosure.Real.IsNear.cos_image qz253 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6350011)) qz608) Bool.true 6350011 4194304 

noncomputable def Ns372p1655 := nat_lit 14993539587678584008043506805 

noncomputable def Ns372p1656 := nat_lit 19511017500472899725969666943642651 

noncomputable def Ns372p1657 := @Enclosure.Real.IsNear.recentre' qz253 Bool.true Ns372p1655 Ns372p197 Ns372p1656 

noncomputable abbrev qz254 := qz542

noncomputable def Ns372p1658 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz254 884279719003555 140737488355328 1 500000000000000 16955652454151 

noncomputable abbrev qz543 := (@HSub.hSub Real Real Real qz588 qz724 qz717)

noncomputable abbrev qz255 := qz543

noncomputable def Ns372p1659 := @Enclosure.Real.IsNear.subLit_tf qz255 qz31 12557605943047 70368744177664 723003149 281474976710656 1 16 

noncomputable abbrev qz544 := qz724

noncomputable abbrev qz256 := qz544

noncomputable def Ns372p1660 := @Enclosure.Real.IsNear.subLit_ff_n qz256 qz242 41449015724281 70368744177664 437790477 281474976710656 6438091 8388608 17 16777216 

noncomputable def Ns372p1661 := @Enclosure.Real.IsNear.mulLit_ff qz242 qz242 6438091 8388608 17 16777216 6438091 8388608 17 16777216 41449015724281 70368744177664 

noncomputable def Ns372p1662 := nat_lit 3117880416718113488335469785528892836368036383087528741116431930522592730634250778686801 

noncomputable def Ns372p1663 := nat_lit 4298270383100058250345414715828127847378471238418785596893236169977524723986576721 

noncomputable def Ns372p1664 := nat_lit 18875808718946331804528526969606776829377567026403773019820237837787422009112356767249745 

noncomputable def Ns372p1665 := BSN.cos_dyadic_bound_f 6350011 4194304 4 3 16777216 5760000 Ns372p1662 Ns372p964 Ns372p1663 Ns372p1664 Ns372p967 Ns372p1663 953031 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 6350011) (BSN.cosEvenQ 4194304) 0 3 Ns372p1662 Ns372p964 Ns372p1663 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 6350011) (BSN.cosOddQ 4194304) 0 3 Ns372p1664 Ns372p967 Ns372p1663 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns372p1666 := @Ns372p1653 1577737216 96636764160000 953031 16777216 1540759 94371840000 (@Ns372p1654 271 16777216 Bool.false 953031 16777216 1 5760000 (@Ns372p1657 Ns372p200 6350011 4194304 271 16777216 (@Ns372p1658 70368744177664 723003149 281474976710656 Ns372p1655 Ns372p197 Ns372p1656 Ns372p200 RS373to384.d47 (@Ns372p1659 0 1 271290439266416 16955652454151 70368744177664 723003149 281474976710656 (@Ns372p1660 105340833674691608576 12557605943047 70368744177664 723003149 281474976710656 (@Ns372p1661 437790477 281474976710656 (Ns372p1645 rfl rfl) (Ns372p1645 rfl rfl) rfl) (Ns372p1645 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6350011 4194304) (BSN.cos_neg_of_bound 6350011 4194304 Bool.false 953031 16777216 1 5760000 (Ns372p1665 rfl rfl)) rfl rfl) 

noncomputable def Ns372p1667 := @Ns372p1631 485671335478932076759 Ns372p214 (Ns372p1632 qz33 (@Enclosure.Real.IsNear.of_eq qz722 (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 10225695 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz241 (BSN.t_div_two_pi_nonneg qz240 728464 1000 qz243)) Ns372p1636) rfl) (@Ns372p1637 140737488355328 11870453125651 65970697666560000 (BSN.correction_mk qz242 (BSN.cos_two_pi_p_ne_zero_mk qz240 728464 1000 10 qz243 rfl rfl (@BSN.floor_sqrt_eq_dec qz240 728464 1000 10 qz243 rfl rfl rfl))) (@Ns372p1638 16777216 953031 16777216 1540759 94371840000 72936159095661 140737488355328 11870453125651 65970697666560000 (@Ns372p1639 16777216 (Ns372p1652 rfl rfl rfl rfl rfl) rfl) (Ns372p1666 rfl) rfl)) 

noncomputable def Ns372p1668 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (hardyZApproximantRS₀ qz240) Bool.true 279020558697730550323 4722366482869645213696 10502464157076402796759 Ns372p214 (@Eq.refl Real (hardyZApproximantRS₀ qz240)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (@HMul.hMul Real Real Real qz5 qz718 (Zeta.RiemannSiegel.correction qz242))) Bool.true 279020558697730550323 4722366482869645213696 10502464157076402796759 Ns372p214 (BSN.hardyZApproximantRS₀_eq qz240 10 (@BSN.floor_sqrt_eq_dec qz240 728464 1000 10 qz243 rfl rfl rfl)) (@Ns372p1557 279020558697730550323 4722366482869645213696 10502464157076402796759 Ns372p214 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10)) Bool.false 13267321 134217728 151837 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (Ns372p1630 (Ns372p1629 rfl rfl rfl rfl) rfl rfl)) (Ns372p1667 rfl) rfl rfl)) 

theorem RS373to384.d63 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz240) Bool.true 279020558697730550323 4722366482869645213696 10502464157076402796759 Ns372p214 := Ns372p1668 

noncomputable def RS373to384.d64 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz545 := (RS373to384.d3 qz583 qz601 (@Enclosure.dec_le_dec qz583 qz601 712564 1000 713892 1000 (@Eq.refl Real qz583) qz605 rfl rfl rfl))

noncomputable abbrev qz257 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz545)

noncomputable def Ns372p1669 := @Enclosure.Real.IsNear.of_eq qz257 (hardyZApproximantRS₀ qz4) Bool.true 815506741294616620981 2361183241434822606848 2963919887925933175801 Ns372p74 

noncomputable abbrev qz546 := (@Enclosure.dec_le_dec qz583 qz601 712564 1000 713892 1000 (@Eq.refl Real qz583) qz605 rfl rfl rfl)

noncomputable abbrev qz258 := qz546

noncomputable def Ns372p1670 := @Enclosure.Real.IsNear.neg_val qz257 815506741294616620981 2361183241434822606848 2963919887925933175801 Ns372p74 (Ns372p1669 (RS373to384.d4 qz4 qz35 qz258) RS373to384.d49) rfl 

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz545)

noncomputable def Ns372p1671 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantRS₀ qz35) Bool.false 4704439184580254684451 4722366482869645213696 9906693783172854054661 Ns372p214 

noncomputable def Ns372p1672 := @Enclosure.Real.IsNear.pos_val qz259 4704439184580254684451 4722366482869645213696 9906693783172854054661 Ns372p214 (Ns372p1671 (RS373to384.d50 qz4 qz35 qz258) RS373to384.d51) rfl 

noncomputable def Ns372p1673 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz257 qz4 qz4 712564 1000 712564 1000 

noncomputable def Ns372p1674 := @Enclosure.norm_gt_of_isNear qz257 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 815506741294616620981 2361183241434822606848 2963919887925933175801 

noncomputable def Ns372p1675 := @Ns372p1674 Ns372p74 291497869 5368709120 1213 5368709120 (Ns372p1669 (RS373to384.d4 qz4 qz35 qz258) RS373to384.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable def Ns372p1676 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz259 qz4 qz35 712564 1000 713892 1000 

noncomputable def Ns372p1677 := @Enclosure.norm_gt_of_isNear qz259 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 4704439184580254684451 4722366482869645213696 9906693783172854054661 

noncomputable def Ns372p1678 := @Ns372p1677 Ns372p214 291497869 5368709120 1213 5368709120 (Ns372p1671 (RS373to384.d50 qz4 qz35 qz258) RS373to384.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable abbrev qz260 := qz545

noncomputable def Ns372p1679 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz260 (@BSN.thirtyTwoPi_le_dec qz4 712564 1000 qz11 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz257 qz259 (Ns372p1670 rfl rfl) (Ns372p1672 rfl rfl)) (Ns372p1673 qz11 qz11 rfl rfl rfl rfl (Ns372p1675 rfl)) (Ns372p1676 qz11 qz38 rfl rfl rfl rfl (Ns372p1678 rfl)) 

noncomputable abbrev qz547 := (RS373to384.d3 qz601 qz614 (@Enclosure.dec_le_dec qz601 qz614 713892 1000 715219 1000 qz605 qz618 rfl rfl rfl))

noncomputable abbrev qz261 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz547)

noncomputable def Ns372p1680 := @Enclosure.Real.IsNear.of_eq qz261 (hardyZApproximantRS₀ qz35) Bool.false 4704439184580254684451 4722366482869645213696 9906693783172854054661 Ns372p214 

noncomputable abbrev qz548 := (@Enclosure.dec_le_dec qz601 qz614 713892 1000 715219 1000 qz605 qz618 rfl rfl rfl)

noncomputable abbrev qz262 := qz548

noncomputable def Ns372p1681 := @Enclosure.Real.IsNear.pos_val qz261 4704439184580254684451 4722366482869645213696 9906693783172854054661 Ns372p214 (Ns372p1680 (RS373to384.d4 qz35 qz62 qz262) RS373to384.d51) rfl 

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz547)

noncomputable def Ns372p1682 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantRS₀ qz62) Bool.true 6840596686782188072521 1180591620717411303424 9935060215572674081831 Ns372p214 

noncomputable def Ns372p1683 := @Enclosure.Real.IsNear.neg_val qz263 6840596686782188072521 1180591620717411303424 9935060215572674081831 Ns372p214 (Ns372p1682 (RS373to384.d50 qz35 qz62 qz262) RS373to384.d53) rfl 

noncomputable def Ns372p1684 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz261 qz4 qz35 712564 1000 713892 1000 

noncomputable def Ns372p1685 := @Enclosure.norm_gt_of_isNear qz261 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 4704439184580254684451 4722366482869645213696 9906693783172854054661 

noncomputable def Ns372p1686 := @Ns372p1685 Ns372p214 291497869 5368709120 1213 5368709120 (Ns372p1680 (RS373to384.d4 qz35 qz62 qz262) RS373to384.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable def Ns372p1687 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz263 qz4 qz62 712564 1000 715219 1000 

noncomputable def Ns372p1688 := @Enclosure.norm_gt_of_isNear qz263 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 6840596686782188072521 1180591620717411303424 9935060215572674081831 

noncomputable def Ns372p1689 := @Ns372p1688 Ns372p214 291497869 5368709120 1213 5368709120 (Ns372p1682 (RS373to384.d50 qz35 qz62 qz262) RS373to384.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable abbrev qz264 := qz547

noncomputable def Ns372p1690 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz264 (@BSN.thirtyTwoPi_le_dec qz35 713892 1000 qz38 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz261 qz263 (Ns372p1681 rfl rfl) (Ns372p1683 rfl rfl)) (Ns372p1684 qz11 qz38 rfl rfl rfl rfl (Ns372p1686 rfl)) (Ns372p1687 qz11 qz65 rfl rfl rfl rfl (Ns372p1689 rfl)) 

noncomputable abbrev qz549 := (RS373to384.d3 qz614 qz624 (@Enclosure.dec_le_dec qz614 qz624 715219 1000 716546 1000 qz618 qz628 rfl rfl rfl))

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz549)

noncomputable def Ns372p1691 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantRS₀ qz62) Bool.true 6840596686782188072521 1180591620717411303424 9935060215572674081831 Ns372p214 

noncomputable abbrev qz550 := (@Enclosure.dec_le_dec qz614 qz624 715219 1000 716546 1000 qz618 qz628 rfl rfl rfl)

noncomputable abbrev qz266 := qz550

noncomputable def Ns372p1692 := @Enclosure.Real.IsNear.neg_val qz265 6840596686782188072521 1180591620717411303424 9935060215572674081831 Ns372p214 (Ns372p1691 (RS373to384.d4 qz62 qz80 qz266) RS373to384.d53) rfl 

noncomputable abbrev qz267 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz549)

noncomputable def Ns372p1693 := @Enclosure.Real.IsNear.of_eq qz267 (hardyZApproximantRS₀ qz80) Bool.false 362192876264714111845 147573952589676412928 2492689459919729336047 Ns372p489 

noncomputable def Ns372p1694 := @Enclosure.Real.IsNear.pos_val qz267 362192876264714111845 147573952589676412928 2492689459919729336047 Ns372p489 (Ns372p1693 (RS373to384.d50 qz62 qz80 qz266) RS373to384.d54) rfl 

noncomputable def Ns372p1695 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz265 qz4 qz62 712564 1000 715219 1000 

noncomputable def Ns372p1696 := @Enclosure.norm_gt_of_isNear qz265 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 6840596686782188072521 1180591620717411303424 9935060215572674081831 

noncomputable def Ns372p1697 := @Ns372p1696 Ns372p214 291497869 5368709120 1213 5368709120 (Ns372p1691 (RS373to384.d4 qz62 qz80 qz266) RS373to384.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable def Ns372p1698 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz267 qz4 qz80 712564 1000 716546 1000 

noncomputable def Ns372p1699 := @Enclosure.norm_gt_of_isNear qz267 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 362192876264714111845 147573952589676412928 2492689459919729336047 

noncomputable def Ns372p1700 := @Ns372p1699 Ns372p489 291497869 5368709120 1213 5368709120 (Ns372p1693 (RS373to384.d50 qz62 qz80 qz266) RS373to384.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable abbrev qz268 := qz549

noncomputable def Ns372p1701 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz62 715219 1000 qz65 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz265 qz267 (Ns372p1692 rfl rfl) (Ns372p1694 rfl rfl)) (Ns372p1695 qz11 qz65 rfl rfl rfl rfl (Ns372p1697 rfl)) (Ns372p1698 qz11 qz83 rfl rfl rfl rfl (Ns372p1700 rfl)) 

noncomputable abbrev qz551 := (RS373to384.d3 qz624 qz634 (@Enclosure.dec_le_dec qz624 qz634 716546 1000 717873 1000 qz628 qz638 rfl rfl rfl))

noncomputable abbrev qz269 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz551)

noncomputable def Ns372p1702 := @Enclosure.Real.IsNear.of_eq qz269 (hardyZApproximantRS₀ qz80) Bool.false 362192876264714111845 147573952589676412928 2492689459919729336047 Ns372p489 

noncomputable abbrev qz552 := (@Enclosure.dec_le_dec qz624 qz634 716546 1000 717873 1000 qz628 qz638 rfl rfl rfl)

noncomputable abbrev qz270 := qz552

noncomputable def Ns372p1703 := @Enclosure.Real.IsNear.pos_val qz269 362192876264714111845 147573952589676412928 2492689459919729336047 Ns372p489 (Ns372p1702 (RS373to384.d4 qz80 qz98 qz270) RS373to384.d54) rfl 

noncomputable abbrev qz271 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz551)

noncomputable def Ns372p1704 := @Enclosure.Real.IsNear.of_eq qz271 (hardyZApproximantRS₀ qz98) Bool.true 53077258933070164209 36893488147419103232 5001803519594208695923 Ns372p619 

noncomputable def Ns372p1705 := @Enclosure.Real.IsNear.neg_val qz271 53077258933070164209 36893488147419103232 5001803519594208695923 Ns372p619 (Ns372p1704 (RS373to384.d50 qz80 qz98 qz270) RS373to384.d55) rfl 

noncomputable def Ns372p1706 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz269 qz4 qz80 712564 1000 716546 1000 

noncomputable def Ns372p1707 := @Enclosure.norm_gt_of_isNear qz269 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 362192876264714111845 147573952589676412928 2492689459919729336047 

noncomputable def Ns372p1708 := @Ns372p1707 Ns372p489 291497869 5368709120 1213 5368709120 (Ns372p1702 (RS373to384.d4 qz80 qz98 qz270) RS373to384.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable def Ns372p1709 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz271 qz4 qz98 712564 1000 717873 1000 

noncomputable def Ns372p1710 := @Enclosure.norm_gt_of_isNear qz271 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 53077258933070164209 36893488147419103232 5001803519594208695923 

noncomputable def Ns372p1711 := @Ns372p1710 Ns372p619 291497869 5368709120 1213 5368709120 (Ns372p1704 (RS373to384.d50 qz80 qz98 qz270) RS373to384.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable abbrev qz272 := qz551

noncomputable def Ns372p1712 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz80 716546 1000 qz83 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz269 qz271 (Ns372p1703 rfl rfl) (Ns372p1705 rfl rfl)) (Ns372p1706 qz11 qz83 rfl rfl rfl rfl (Ns372p1708 rfl)) (Ns372p1709 qz11 qz101 rfl rfl rfl rfl (Ns372p1711 rfl)) 

noncomputable abbrev qz553 := (RS373to384.d3 qz634 qz644 (@Enclosure.dec_le_dec qz634 qz644 717873 1000 719198 1000 qz638 qz648 rfl rfl rfl))

noncomputable abbrev qz273 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz553)

noncomputable def Ns372p1713 := @Enclosure.Real.IsNear.of_eq qz273 (hardyZApproximantRS₀ qz98) Bool.true 53077258933070164209 36893488147419103232 5001803519594208695923 Ns372p619 

noncomputable abbrev qz554 := (@Enclosure.dec_le_dec qz634 qz644 717873 1000 719198 1000 qz638 qz648 rfl rfl rfl)

noncomputable abbrev qz274 := qz554

noncomputable def Ns372p1714 := @Enclosure.Real.IsNear.neg_val qz273 53077258933070164209 36893488147419103232 5001803519594208695923 Ns372p619 (Ns372p1713 (RS373to384.d4 qz98 qz116 qz274) RS373to384.d55) rfl 

noncomputable abbrev qz275 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz553)

noncomputable def Ns372p1715 := @Enclosure.Real.IsNear.of_eq qz275 (hardyZApproximantRS₀ qz116) Bool.false 2158161840615216903553 2361183241434822606848 5026268471734038569599 Ns372p619 

noncomputable def Ns372p1716 := @Enclosure.Real.IsNear.pos_val qz275 2158161840615216903553 2361183241434822606848 5026268471734038569599 Ns372p619 (Ns372p1715 (RS373to384.d50 qz98 qz116 qz274) RS373to384.d56) rfl 

noncomputable def Ns372p1717 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz273 qz4 qz98 712564 1000 717873 1000 

noncomputable def Ns372p1718 := @Enclosure.norm_gt_of_isNear qz273 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 53077258933070164209 36893488147419103232 5001803519594208695923 

noncomputable def Ns372p1719 := @Ns372p1718 Ns372p619 291497869 5368709120 1213 5368709120 (Ns372p1713 (RS373to384.d4 qz98 qz116 qz274) RS373to384.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable def Ns372p1720 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz275 qz4 qz116 712564 1000 719198 1000 

noncomputable def Ns372p1721 := @Enclosure.norm_gt_of_isNear qz275 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2158161840615216903553 2361183241434822606848 5026268471734038569599 

noncomputable def Ns372p1722 := @Ns372p1721 Ns372p619 291497869 5368709120 1213 5368709120 (Ns372p1715 (RS373to384.d50 qz98 qz116 qz274) RS373to384.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable abbrev qz276 := qz553

noncomputable def Ns372p1723 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz98 717873 1000 qz101 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz273 qz275 (Ns372p1714 rfl rfl) (Ns372p1716 rfl rfl)) (Ns372p1717 qz11 qz101 rfl rfl rfl rfl (Ns372p1719 rfl)) (Ns372p1720 qz11 qz119 rfl rfl rfl rfl (Ns372p1722 rfl)) 

noncomputable abbrev qz555 := (RS373to384.d3 qz644 qz654 (@Enclosure.dec_le_dec qz644 qz654 719198 1000 720524 1000 qz648 qz658 rfl rfl rfl))

noncomputable abbrev qz277 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz555)

noncomputable def Ns372p1724 := @Enclosure.Real.IsNear.of_eq qz277 (hardyZApproximantRS₀ qz116) Bool.false 2158161840615216903553 2361183241434822606848 5026268471734038569599 Ns372p619 

noncomputable abbrev qz556 := (@Enclosure.dec_le_dec qz644 qz654 719198 1000 720524 1000 qz648 qz658 rfl rfl rfl)

noncomputable abbrev qz278 := qz556

noncomputable def Ns372p1725 := @Enclosure.Real.IsNear.pos_val qz277 2158161840615216903553 2361183241434822606848 5026268471734038569599 Ns372p619 (Ns372p1724 (RS373to384.d4 qz116 qz134 qz278) RS373to384.d56) rfl 

noncomputable abbrev qz279 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz555)

noncomputable def Ns372p1726 := @Enclosure.Real.IsNear.of_eq qz279 (hardyZApproximantRS₀ qz134) Bool.true 10688949584749916302321 4722366482869645213696 30314166146858263234427 Ns372p856 

noncomputable def Ns372p1727 := @Enclosure.Real.IsNear.neg_val qz279 10688949584749916302321 4722366482869645213696 30314166146858263234427 Ns372p856 (Ns372p1726 (RS373to384.d50 qz116 qz134 qz278) RS373to384.d57) rfl 

noncomputable def Ns372p1728 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz277 qz4 qz116 712564 1000 719198 1000 

noncomputable def Ns372p1729 := @Enclosure.norm_gt_of_isNear qz277 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2158161840615216903553 2361183241434822606848 5026268471734038569599 

noncomputable def Ns372p1730 := @Ns372p1729 Ns372p619 291497869 5368709120 1213 5368709120 (Ns372p1724 (RS373to384.d4 qz116 qz134 qz278) RS373to384.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable def Ns372p1731 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz279 qz4 qz134 712564 1000 720524 1000 

noncomputable def Ns372p1732 := @Enclosure.norm_gt_of_isNear qz279 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 10688949584749916302321 4722366482869645213696 30314166146858263234427 

noncomputable def Ns372p1733 := @Ns372p1732 Ns372p856 291497869 5368709120 1213 5368709120 (Ns372p1726 (RS373to384.d50 qz116 qz134 qz278) RS373to384.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable abbrev qz280 := qz555

noncomputable def Ns372p1734 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz116 719198 1000 qz119 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz277 qz279 (Ns372p1725 rfl rfl) (Ns372p1727 rfl rfl)) (Ns372p1728 qz11 qz119 rfl rfl rfl rfl (Ns372p1730 rfl)) (Ns372p1731 qz11 qz137 rfl rfl rfl rfl (Ns372p1733 rfl)) 

noncomputable abbrev qz557 := (RS373to384.d3 qz654 qz664 (@Enclosure.dec_le_dec qz654 qz664 720524 1000 721848 1000 qz658 qz668 rfl rfl rfl))

noncomputable abbrev qz281 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz557)

noncomputable def Ns372p1735 := @Enclosure.Real.IsNear.of_eq qz281 (hardyZApproximantRS₀ qz134) Bool.true 10688949584749916302321 4722366482869645213696 30314166146858263234427 Ns372p856 

noncomputable abbrev qz558 := (@Enclosure.dec_le_dec qz654 qz664 720524 1000 721848 1000 qz658 qz668 rfl rfl rfl)

noncomputable abbrev qz282 := qz558

noncomputable def Ns372p1736 := @Enclosure.Real.IsNear.neg_val qz281 10688949584749916302321 4722366482869645213696 30314166146858263234427 Ns372p856 (Ns372p1735 (RS373to384.d4 qz134 qz152 qz282) RS373to384.d57) rfl 

noncomputable abbrev qz283 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz557)

noncomputable def Ns372p1737 := @Enclosure.Real.IsNear.of_eq qz283 (hardyZApproximantRS₀ qz152) Bool.false 8491196269302322869395 9444732965739290427392 12231033112622028302479 Ns372p972 

noncomputable def Ns372p1738 := @Enclosure.Real.IsNear.pos_val qz283 8491196269302322869395 9444732965739290427392 12231033112622028302479 Ns372p972 (Ns372p1737 (RS373to384.d50 qz134 qz152 qz282) RS373to384.d58) rfl 

noncomputable def Ns372p1739 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz281 qz4 qz134 712564 1000 720524 1000 

noncomputable def Ns372p1740 := @Enclosure.norm_gt_of_isNear qz281 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 10688949584749916302321 4722366482869645213696 30314166146858263234427 

noncomputable def Ns372p1741 := @Ns372p1740 Ns372p856 291497869 5368709120 1213 5368709120 (Ns372p1735 (RS373to384.d4 qz134 qz152 qz282) RS373to384.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable def Ns372p1742 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz283 qz4 qz152 712564 1000 721848 1000 

noncomputable def Ns372p1743 := @Enclosure.norm_gt_of_isNear qz283 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 8491196269302322869395 9444732965739290427392 12231033112622028302479 

noncomputable def Ns372p1744 := @Ns372p1743 Ns372p972 291497869 5368709120 1213 5368709120 (Ns372p1737 (RS373to384.d50 qz134 qz152 qz282) RS373to384.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable abbrev qz284 := qz557

noncomputable def Ns372p1745 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz134 720524 1000 qz137 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz281 qz283 (Ns372p1736 rfl rfl) (Ns372p1738 rfl rfl)) (Ns372p1739 qz11 qz137 rfl rfl rfl rfl (Ns372p1741 rfl)) (Ns372p1742 qz11 qz155 rfl rfl rfl rfl (Ns372p1744 rfl)) 

noncomputable abbrev qz559 := (RS373to384.d3 qz664 qz674 (@Enclosure.dec_le_dec qz664 qz674 721848 1000 723172 1000 qz668 qz678 rfl rfl rfl))

noncomputable abbrev qz285 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz559)

noncomputable def Ns372p1746 := @Enclosure.Real.IsNear.of_eq qz285 (hardyZApproximantRS₀ qz152) Bool.false 8491196269302322869395 9444732965739290427392 12231033112622028302479 Ns372p972 

noncomputable abbrev qz560 := (@Enclosure.dec_le_dec qz664 qz674 721848 1000 723172 1000 qz668 qz678 rfl rfl rfl)

noncomputable abbrev qz286 := qz560

noncomputable def Ns372p1747 := @Enclosure.Real.IsNear.pos_val qz285 8491196269302322869395 9444732965739290427392 12231033112622028302479 Ns372p972 (Ns372p1746 (RS373to384.d4 qz152 qz170 qz286) RS373to384.d58) rfl 

noncomputable abbrev qz287 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz559)

noncomputable def Ns372p1748 := @Enclosure.Real.IsNear.of_eq qz287 (hardyZApproximantRS₀ qz170) Bool.true 9589134287702284995 4611686018427387904 30967743622136623389337 Ns372p856 

noncomputable def Ns372p1749 := @Enclosure.Real.IsNear.neg_val qz287 9589134287702284995 4611686018427387904 30967743622136623389337 Ns372p856 (Ns372p1748 (RS373to384.d50 qz152 qz170 qz286) RS373to384.d59) rfl 

noncomputable def Ns372p1750 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz285 qz4 qz152 712564 1000 721848 1000 

noncomputable def Ns372p1751 := @Enclosure.norm_gt_of_isNear qz285 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 8491196269302322869395 9444732965739290427392 12231033112622028302479 

noncomputable def Ns372p1752 := @Ns372p1751 Ns372p972 291497869 5368709120 1213 5368709120 (Ns372p1746 (RS373to384.d4 qz152 qz170 qz286) RS373to384.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable def Ns372p1753 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz287 qz4 qz170 712564 1000 723172 1000 

noncomputable def Ns372p1754 := @Enclosure.norm_gt_of_isNear qz287 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 9589134287702284995 4611686018427387904 30967743622136623389337 

noncomputable def Ns372p1755 := @Ns372p1754 Ns372p856 291497869 5368709120 1213 5368709120 (Ns372p1748 (RS373to384.d50 qz152 qz170 qz286) RS373to384.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable abbrev qz288 := qz559

noncomputable def Ns372p1756 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz152 721848 1000 qz155 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz285 qz287 (Ns372p1747 rfl rfl) (Ns372p1749 rfl rfl)) (Ns372p1750 qz11 qz155 rfl rfl rfl rfl (Ns372p1752 rfl)) (Ns372p1753 qz11 qz173 rfl rfl rfl rfl (Ns372p1755 rfl)) 

noncomputable abbrev qz725 := (@Enclosure.dec_le_dec qz770 qz774 723172 1000 724496 1000 (@Eq.refl Real qz770) (@Eq.refl Real qz774) rfl rfl rfl)

noncomputable abbrev qz561 := (RS373to384.d3 qz674 qz684 qz725)

noncomputable abbrev qz289 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz561)

noncomputable def Ns372p1757 := @Enclosure.Real.IsNear.of_eq qz289 (hardyZApproximantRS₀ qz170) Bool.true 9589134287702284995 4611686018427387904 30967743622136623389337 Ns372p856 

noncomputable abbrev qz562 := qz725

noncomputable abbrev qz290 := qz562

noncomputable def Ns372p1758 := @Enclosure.Real.IsNear.neg_val qz289 9589134287702284995 4611686018427387904 30967743622136623389337 Ns372p856 (Ns372p1757 (RS373to384.d4 qz170 qz188 qz290) RS373to384.d59) rfl 

noncomputable abbrev qz291 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz561)

noncomputable def Ns372p1759 := @Enclosure.Real.IsNear.of_eq qz291 (hardyZApproximantRS₀ qz188) Bool.false 1307525095045409075641 4722366482869645213696 1281336465482794026997 1062532458645670173081600 

noncomputable def Ns372p1760 := @Enclosure.Real.IsNear.pos_val qz291 1307525095045409075641 4722366482869645213696 1281336465482794026997 1062532458645670173081600 (Ns372p1759 (RS373to384.d50 qz170 qz188 qz290) RS373to384.d60) rfl 

noncomputable def Ns372p1761 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz289 qz4 qz170 712564 1000 723172 1000 

noncomputable def Ns372p1762 := @Enclosure.norm_gt_of_isNear qz289 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 9589134287702284995 4611686018427387904 30967743622136623389337 

noncomputable def Ns372p1763 := @Ns372p1762 Ns372p856 291497869 5368709120 1213 5368709120 (Ns372p1757 (RS373to384.d4 qz170 qz188 qz290) RS373to384.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable def Ns372p1764 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz291 qz4 qz188 712564 1000 724496 1000 

noncomputable def Ns372p1765 := @Enclosure.norm_gt_of_isNear qz291 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1307525095045409075641 4722366482869645213696 1281336465482794026997 

noncomputable def Ns372p1766 := @Ns372p1765 1062532458645670173081600 291497869 5368709120 1213 5368709120 (Ns372p1759 (RS373to384.d50 qz170 qz188 qz290) RS373to384.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable abbrev qz292 := qz561

noncomputable def Ns372p1767 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz170 723172 1000 qz173 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz289 qz291 (Ns372p1758 rfl rfl) (Ns372p1760 rfl rfl)) (Ns372p1761 qz11 qz173 rfl rfl rfl rfl (Ns372p1763 rfl)) (Ns372p1764 qz11 qz191 rfl rfl rfl rfl (Ns372p1766 rfl)) 

noncomputable abbrev qz726 := (@Enclosure.dec_le_dec qz774 qz778 724496 1000 725819 1000 (@Eq.refl Real qz774) qz781 rfl rfl rfl)

noncomputable abbrev qz563 := (RS373to384.d3 qz684 qz694 qz726)

noncomputable abbrev qz293 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz563)

noncomputable def Ns372p1768 := @Enclosure.Real.IsNear.of_eq qz293 (hardyZApproximantRS₀ qz188) Bool.false 1307525095045409075641 4722366482869645213696 1281336465482794026997 1062532458645670173081600 

noncomputable abbrev qz564 := qz726

noncomputable abbrev qz294 := qz564

noncomputable def Ns372p1769 := @Enclosure.Real.IsNear.pos_val qz293 1307525095045409075641 4722366482869645213696 1281336465482794026997 1062532458645670173081600 (Ns372p1768 (RS373to384.d4 qz188 qz206 qz294) RS373to384.d60) rfl 

noncomputable abbrev qz295 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz563)

noncomputable def Ns372p1770 := @Enclosure.Real.IsNear.of_eq qz295 (hardyZApproximantRS₀ qz206) Bool.true 4645177980004615454373 590295810358705651712 2113609410650943583 1328165573307087716352 

noncomputable def Ns372p1771 := @Enclosure.Real.IsNear.neg_val qz295 4645177980004615454373 590295810358705651712 2113609410650943583 1328165573307087716352 (Ns372p1770 (RS373to384.d50 qz188 qz206 qz294) RS373to384.d61) rfl 

noncomputable def Ns372p1772 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz293 qz4 qz188 712564 1000 724496 1000 

noncomputable def Ns372p1773 := @Enclosure.norm_gt_of_isNear qz293 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1307525095045409075641 4722366482869645213696 1281336465482794026997 

noncomputable def Ns372p1774 := @Ns372p1773 1062532458645670173081600 291497869 5368709120 1213 5368709120 (Ns372p1768 (RS373to384.d4 qz188 qz206 qz294) RS373to384.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable def Ns372p1775 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz295 qz4 qz206 712564 1000 725819 1000 

noncomputable def Ns372p1776 := @Enclosure.norm_gt_of_isNear qz295 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 4645177980004615454373 590295810358705651712 2113609410650943583 

noncomputable def Ns372p1777 := @Ns372p1776 1328165573307087716352 291497869 5368709120 1213 5368709120 (Ns372p1770 (RS373to384.d50 qz188 qz206 qz294) RS373to384.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable abbrev qz296 := qz563

noncomputable def Ns372p1778 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz188 724496 1000 qz191 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz293 qz295 (Ns372p1769 rfl rfl) (Ns372p1771 rfl rfl)) (Ns372p1772 qz11 qz191 rfl rfl rfl rfl (Ns372p1774 rfl)) (Ns372p1775 qz11 qz209 rfl rfl rfl rfl (Ns372p1777 rfl)) 

noncomputable abbrev qz727 := (@Enclosure.dec_le_dec qz778 qz783 725819 1000 727142 1000 qz781 qz786 rfl rfl rfl)

noncomputable abbrev qz565 := (RS373to384.d3 qz694 qz705 qz727)

noncomputable abbrev qz297 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz565)

noncomputable def Ns372p1779 := @Enclosure.Real.IsNear.of_eq qz297 (hardyZApproximantRS₀ qz206) Bool.true 4645177980004615454373 590295810358705651712 2113609410650943583 1328165573307087716352 

noncomputable abbrev qz566 := qz727

noncomputable abbrev qz298 := qz566

noncomputable def Ns372p1780 := @Enclosure.Real.IsNear.neg_val qz297 4645177980004615454373 590295810358705651712 2113609410650943583 1328165573307087716352 (Ns372p1779 (RS373to384.d4 qz206 qz223 qz298) RS373to384.d61) rfl 

noncomputable abbrev qz299 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz565)

noncomputable def Ns372p1781 := @Enclosure.Real.IsNear.of_eq qz299 (hardyZApproximantRS₀ qz223) Bool.false 287696930884591838713 590295810358705651712 556057273856457296189 442721857769029238784000 

noncomputable def Ns372p1782 := @Enclosure.Real.IsNear.pos_val qz299 287696930884591838713 590295810358705651712 556057273856457296189 442721857769029238784000 (Ns372p1781 (RS373to384.d50 qz206 qz223 qz298) RS373to384.d62) rfl 

noncomputable def Ns372p1783 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz297 qz4 qz206 712564 1000 725819 1000 

noncomputable def Ns372p1784 := @Enclosure.norm_gt_of_isNear qz297 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 4645177980004615454373 590295810358705651712 2113609410650943583 

noncomputable def Ns372p1785 := @Ns372p1784 1328165573307087716352 291497869 5368709120 1213 5368709120 (Ns372p1779 (RS373to384.d4 qz206 qz223 qz298) RS373to384.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable def Ns372p1786 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz299 qz4 qz223 712564 1000 727142 1000 

noncomputable def Ns372p1787 := @Enclosure.norm_gt_of_isNear qz299 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 287696930884591838713 590295810358705651712 556057273856457296189 

noncomputable def Ns372p1788 := @Ns372p1787 442721857769029238784000 291497869 5368709120 1213 5368709120 (Ns372p1781 (RS373to384.d50 qz206 qz223 qz298) RS373to384.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable abbrev qz300 := qz565

noncomputable def Ns372p1789 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz206 725819 1000 qz209 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz297 qz299 (Ns372p1780 rfl rfl) (Ns372p1782 rfl rfl)) (Ns372p1783 qz11 qz209 rfl rfl rfl rfl (Ns372p1785 rfl)) (Ns372p1786 qz11 qz226 rfl rfl rfl rfl (Ns372p1788 rfl)) 

noncomputable abbrev qz793 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 727142 1000) (Enclosure.sfrac Bool.false 728464 1000) 727142 1000 728464 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 727142 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 728464 1000)) rfl rfl rfl)

noncomputable abbrev qz728 := qz793

noncomputable abbrev qz567 := (RS373to384.d3 qz705 qz715 qz728)

noncomputable abbrev qz301 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz567)

noncomputable def Ns372p1790 := @Enclosure.Real.IsNear.of_eq qz301 (hardyZApproximantRS₀ qz223) Bool.false 287696930884591838713 590295810358705651712 556057273856457296189 442721857769029238784000 

noncomputable abbrev qz568 := qz728

noncomputable abbrev qz302 := qz568

noncomputable def Ns372p1791 := @Enclosure.Real.IsNear.pos_val qz301 287696930884591838713 590295810358705651712 556057273856457296189 442721857769029238784000 (Ns372p1790 (RS373to384.d4 qz223 qz240 qz302) RS373to384.d62) rfl 

noncomputable abbrev qz303 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz567)

noncomputable def Ns372p1792 := @Enclosure.Real.IsNear.of_eq qz303 (hardyZApproximantRS₀ qz240) Bool.true 279020558697730550323 4722366482869645213696 10502464157076402796759 Ns372p214 

noncomputable def Ns372p1793 := @Enclosure.Real.IsNear.neg_val qz303 279020558697730550323 4722366482869645213696 10502464157076402796759 Ns372p214 (Ns372p1792 (RS373to384.d50 qz223 qz240 qz302) RS373to384.d63) rfl 

noncomputable def Ns372p1794 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz301 qz4 qz223 712564 1000 727142 1000 

noncomputable def Ns372p1795 := @Enclosure.norm_gt_of_isNear qz301 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 287696930884591838713 590295810358705651712 556057273856457296189 

noncomputable def Ns372p1796 := @Ns372p1795 442721857769029238784000 291497869 5368709120 1213 5368709120 (Ns372p1790 (RS373to384.d4 qz223 qz240 qz302) RS373to384.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable def Ns372p1797 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz303 qz4 qz240 712564 1000 728464 1000 

noncomputable def Ns372p1798 := @Enclosure.norm_gt_of_isNear qz303 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 279020558697730550323 4722366482869645213696 10502464157076402796759 

noncomputable def Ns372p1799 := @Ns372p1798 Ns372p214 291497869 5368709120 1213 5368709120 (Ns372p1792 (RS373to384.d50 qz223 qz240 qz302) RS373to384.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 291497869 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS373to384.d52) rfl rfl rfl rfl 

noncomputable abbrev qz304 := qz567

noncomputable def Ns372p1800 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz223 727142 1000 qz226 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz301 qz303 (Ns372p1791 rfl rfl) (Ns372p1793 rfl rfl)) (Ns372p1794 qz11 qz226 rfl rfl rfl rfl (Ns372p1796 rfl)) (Ns372p1797 qz11 qz243 rfl rfl rfl rfl (Ns372p1799 rfl)) 

noncomputable def Ns372p1801 := @List.cons RS373to384.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns372p1789)) (@List.cons RS373to384.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns372p1800)) (@List.nil RS373to384.d0)) 

noncomputable def Ns372p1802 := @List.cons RS373to384.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns372p1767)) (@List.cons RS373to384.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns372p1778)) Ns372p1801) 

noncomputable def Ns372p1803 := @List.cons RS373to384.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns372p1745)) (@List.cons RS373to384.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns372p1756)) Ns372p1802) 

noncomputable def Ns372p1804 := @List.cons RS373to384.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns372p1723)) (@List.cons RS373to384.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns372p1734)) Ns372p1803) 

noncomputable def Ns372p1805 := @List.cons RS373to384.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns372p1701)) (@List.cons RS373to384.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns372p1712)) Ns372p1804) 

noncomputable def Ns372p1806 := @List.cons RS373to384.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz260 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz260) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz260) Ns372p1679)) (@List.cons RS373to384.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz264 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz264) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz264) Ns372p1690)) Ns372p1805) 

noncomputable abbrev qz569 := (RS373to384.d2 qz674 qz684 qz725)

noncomputable abbrev qz729 := (RS373to384.d2 qz778 qz783 (@Enclosure.dec_le_dec qz778 qz783 725819 1000 727142 1000 qz781 qz786 rfl rfl rfl))

noncomputable abbrev qz730 := (@List.cons RS373to384.d1 (RS373to384.d2 qz783 qz788 qz793) (@List.nil RS373to384.d1))

noncomputable abbrev qz570 := (@List.cons RS373to384.d1 (RS373to384.d2 qz684 qz694 qz726) (@List.cons RS373to384.d1 qz729 qz730))

noncomputable abbrev qz305 := (@List.cons RS373to384.d1 (RS373to384.d2 qz470 qz483 qz560) (@List.cons RS373to384.d1 qz569 qz570))

noncomputable def Ns372p1807 := @List.cons RS373to384.d1 (RS373to384.d2 qz116 qz134 qz278) (@List.cons RS373to384.d1 (RS373to384.d2 qz134 qz152 qz282) qz305) 

noncomputable abbrev qz306 := (RS373to384.d2 qz431 qz444 qz554)

noncomputable def Ns372p1808 := @List.IsChain.cons_cons RS373to384.d1 RS373to384.d64 qz306 (RS373to384.d2 qz116 qz134 qz278) (@List.cons RS373to384.d1 (RS373to384.d2 qz134 qz152 qz282) qz305) 

noncomputable def Ns372p1809 := @List.IsChain.cons_cons RS373to384.d1 RS373to384.d64 (RS373to384.d2 qz116 qz134 qz278) (RS373to384.d2 qz134 qz152 qz282) qz305 (@Enclosure.dec_le_dec qz134 qz134 720524 1000 720524 1000 qz137 qz137 rfl rfl rfl) 

noncomputable abbrev qz307 := (RS373to384.d2 qz470 qz483 qz560)

noncomputable abbrev qz308 := qz569

noncomputable abbrev qz309 := qz570

noncomputable abbrev qz571 := (RS373to384.d2 qz684 qz694 qz726)

noncomputable abbrev qz310 := qz571

noncomputable abbrev qz572 := (@List.cons RS373to384.d1 qz729 qz730)

noncomputable abbrev qz311 := qz572

noncomputable abbrev qz573 := qz729

noncomputable abbrev qz312 := qz573

noncomputable abbrev qz574 := qz730

noncomputable abbrev qz313 := qz574

noncomputable abbrev qz731 := (RS373to384.d2 qz783 qz788 qz793)

noncomputable abbrev qz575 := qz731

noncomputable abbrev qz314 := qz575

noncomputable def Ns372p1810 := @List.IsChain.cons_cons RS373to384.d1 RS373to384.d64 qz307 qz308 qz309 (@Enclosure.dec_le_dec qz170 qz170 723172 1000 723172 1000 qz173 qz173 rfl rfl rfl) (@List.IsChain.cons_cons RS373to384.d1 RS373to384.d64 qz308 qz310 qz311 (@Enclosure.dec_le_dec qz188 qz188 724496 1000 724496 1000 qz191 qz191 rfl rfl rfl) (@List.IsChain.cons_cons RS373to384.d1 RS373to384.d64 qz310 qz312 qz313 (@Enclosure.dec_le_dec qz206 qz206 725819 1000 725819 1000 qz209 qz209 rfl rfl rfl) (@List.IsChain.cons_cons RS373to384.d1 RS373to384.d64 qz312 qz314 (@List.nil RS373to384.d1) (@Enclosure.dec_le_dec qz223 qz223 727142 1000 727142 1000 qz226 qz226 rfl rfl rfl) (@List.IsChain.singleton RS373to384.d1 RS373to384.d64 qz314)))) 

noncomputable abbrev qz315 := (@List.cons RS373to384.d1 qz569 qz570)

noncomputable def Ns372p1811 := @List.IsChain.cons_cons RS373to384.d1 RS373to384.d64 (RS373to384.d2 qz134 qz152 qz282) qz307 qz315 (@Enclosure.dec_le_dec qz152 qz152 721848 1000 721848 1000 qz155 qz155 rfl rfl rfl) Ns372p1810 

noncomputable def Ns372p1812 := @List.IsChain.cons_cons RS373to384.d1 RS373to384.d64 (RS373to384.d2 qz4 qz35 qz258) (RS373to384.d2 qz35 qz62 qz262) (@List.cons RS373to384.d1 (RS373to384.d2 qz62 qz80 qz266) (@List.cons RS373to384.d1 (RS373to384.d2 qz80 qz98 qz270) (@List.cons RS373to384.d1 qz306 Ns372p1807))) (@Enclosure.dec_le_dec qz35 qz35 713892 1000 713892 1000 qz38 qz38 rfl rfl rfl) (@List.IsChain.cons_cons RS373to384.d1 RS373to384.d64 (RS373to384.d2 qz35 qz62 qz262) (RS373to384.d2 qz62 qz80 qz266) (@List.cons RS373to384.d1 (RS373to384.d2 qz80 qz98 qz270) (@List.cons RS373to384.d1 qz306 Ns372p1807)) (@Enclosure.dec_le_dec qz62 qz62 715219 1000 715219 1000 qz65 qz65 rfl rfl rfl) (@List.IsChain.cons_cons RS373to384.d1 RS373to384.d64 (RS373to384.d2 qz62 qz80 qz266) (RS373to384.d2 qz80 qz98 qz270) (@List.cons RS373to384.d1 qz306 Ns372p1807) (@Enclosure.dec_le_dec qz80 qz80 716546 1000 716546 1000 qz83 qz83 rfl rfl rfl) (@List.IsChain.cons_cons RS373to384.d1 RS373to384.d64 (RS373to384.d2 qz80 qz98 qz270) qz306 Ns372p1807 (@Enclosure.dec_le_dec qz98 qz98 717873 1000 717873 1000 qz101 qz101 rfl rfl rfl) (Ns372p1808 (@Enclosure.dec_le_dec qz116 qz116 719198 1000 719198 1000 qz119 qz119 rfl rfl rfl) (Ns372p1809 Ns372p1811))))) 

noncomputable abbrev qz576 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz577 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns372p1806 Ns372p1812)

noncomputable abbrev qz578 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns372p1806 Ns372p1812))

theorem RS373to384.d65 : Zeta.Certificates.BatchSpec 12 712564 1000 728464 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz576 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz576 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz576 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz240)))) qz577 (@And.intro (@Eq Nat (@List.length qz576 qz578) 12) (And (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz576 qz578)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz576 qz578)) (@Option.some Real qz240))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz576 qz578)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz576 qz578)) (@Option.some Real qz240)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz240))))

theorem solution : Zeta.Certificates.BatchSpec 12 712564 1000 728464 1000 := RS373to384.d65
#print axioms solution
#check solution
