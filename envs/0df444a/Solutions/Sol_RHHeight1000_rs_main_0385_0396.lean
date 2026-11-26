-- Prove2me | solution 1 for RHHeight1000.rs_main_0385_0396
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T09:04:27.179402+00:00
-- url     : https://prove2.me/submissions/82526b9a-c18a-44c6-8376-c6f70f952aba

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

noncomputable def RS385to396.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS385to396.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS385to396.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS385to396.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS385to396.d2 a b h 

theorem RS385to396.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS385to396.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS385to396.d3 a b h)) 

noncomputable def Ns384p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns384p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns384p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns384p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns384p0 Ns384p1 Ns384p2 Ns384p1 307286088 268435456 1 92160000 307286088 268435456 1 92160000 153643044 134217728 2 134217728 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns384p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns384p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns384p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns384p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns384p8 := nat_lit 167537954069964697925743468333314178468718661948561187618563575975392713740913527107727581163208035826476740967700482432525301063254420572874757592895482956004842597348203117269212172556829666669574421653274845612596416189641484794702002223261246862056663160605878293700340502480877986491439034432953223334258717026053687371824342493299510132312376251152844516906794910572262907940062760396663270105627554083664899640691826599584783763757814813433640133591539937449421955686657622469485188711283992428713614179785896055117030632677201478317872225272595773536303110412989181984739022579128493081560758017763072115692678596043664844667144619713966763611484179303468167142547433165016751768184247559143333542643815355903304572487929375 

noncomputable def Ns384p9 := nat_lit 17907736863639440849562382641391758203535690054199171304015283257442503423240620144819838407313611418261944516207295868563739563278604805791797182761045687776939279949642059267526948014748996956777332184087524644234759874591635243045607722412471722018588244283882362848653445974523544951031470230725674276297342086185092985546835544820091590454230569790847977790484558207349923322458845585052164126500435851662252152223728079705692133047658564669873831757357628115566356048471439549797170528303905720944834637690907185213991407615774042056720704508980680095051114888612186461088301140868302968264130481206655302741383410655080008578156649725227045954510069588220729495895148666460653631514375880874422615237249871322129146554264800 

noncomputable def Ns384p10 := nat_lit 55164646516618494962085419356369025784335016154267579706247610053041231157772817011486486467101704279863254798704146668052276438579475100451766223896220272709675360577301802978530276301158911649961092601279696986330335403118086533522541958716560166657634553390183479955483588238249446822384543398154260439705049143284278540285021213103458182619368483938376641172730818250587232036579805400979202432024046862170503602539341971086573372247299262086029843105216008583038025403798224342134620653974939981235680083776396058604459065501719125356177784467570909658245422960948263734871602033841948787585406240093531041217463298165642337705122589129757920995868559518021463265498464182174549661735402095023640043996665674913376875 

noncomputable def Ns384p11 := BSN.log_dyadic_bound Ns384p6 Ns384p7 15 14 Ns384p8 268435456 92160000 Ns384p9 Ns384p10 307286088 Ns384p4 Ns384p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns384p6) (BSN.artanhQ Ns384p7) 0 14 Ns384p9 Ns384p8 Ns384p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns384p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns384p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns384p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns384p15 := nat_lit 167537954069966963268140139327979112712430526945422964221951926912223381190141639739514890494967825643602350173964944759828460064784215684919760383437959917620844610857567326816719640593037578236900835917107172977527392439886629774248115214831425484905681376157923696414882114961796820014026232307332015059110330001516939277521159573995394989771587717775443426002499543257897301982481613760098955890450106043861450716722534643739571053080256776912576113428445260435254713579381797931690799491102381747484553243404562568585572234105168360737285205910186933811836504830286397217473365026331067977496463917110493303316865058355012304571237619413071097245713770677768486493924969821719264401216877841676972336093778875903304572487929375 

noncomputable def Ns384p16 := nat_lit 17907736863639702486765313263906285882628955290251965205176678923530777959693011244026517850256414903756943142851250712732214241881959351517241344993825585048584379523049477943740273636414656012170312373198803997844271825165684859407921203335666024680974464565759223251918458072775203410604089667122984485578465112081892102496937045858735135721609691262763214794451343726045584198128451069547586972080574568545086657023793200560105564573365716615162566961587407171758966967827997201380802107846920231945878242774600967607639551032178207663699700360114112068650063802902647517702890145150192721997537569966984346993833704449560383184487996362781528900358997452380059737141488304159449328022742959995775545894292303322129146554264800 

noncomputable def Ns384p17 := nat_lit 55164646516619937449385584700664297411818070214438189962773666351465523500358685366424500506990751111492356556545320273548942244833046464529601272738875466881799996765940232256588350019911833156887888425998391295014189841212513610526066550079316346993943774342801096070086869790972589246312728227659319758310961510342377923950694747797317942483020440897997204711883064182772445608288320382376665481938194224815739627075458138172195220395246294556718284728034954178416253903237031389214179719385823921869528509431462690683227358218086518156757026652846493301460983550768858152506145788622699720737745394141184245149692548799188169247529408201840608223422296381897323845616153036586108326210125693898345963996665674913376875 

noncomputable def Ns384p18 := BSN.log_dyadic_bound Ns384p13 Ns384p14 15 14 Ns384p15 268435456 92160000 Ns384p16 Ns384p17 307286088 Ns384p12 Ns384p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns384p13) (BSN.artanhQ Ns384p14) 0 14 Ns384p16 Ns384p15 Ns384p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns384p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 153643044 134217728 2 134217728 38410761 33554432 1 67108864 (Ns384p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns384p0 Ns384p1 307286088 268435456 1 92160000 Bool.false (BSN.logfrac_isNear Ns384p4 Ns384p5 1 Ns384p0 Ns384p1 307286088 268435456 92160000 rfl rfl rfl (Ns384p11 rfl))) (BSN.isNear_log_sfrac Ns384p2 Ns384p1 307286088 268435456 1 92160000 Bool.false (BSN.logfrac_isNear Ns384p12 Ns384p5 1 Ns384p2 Ns384p1 307286088 268435456 92160000 rfl rfl rfl (Ns384p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS385to396.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 67108864 := Ns384p19 

noncomputable def Ns384p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 16777216 5760000 385100712855 135135 11629079 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz316 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz0 := qz316

theorem RS385to396.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 11629079 16777216 1 5760000 := BSN.isNear_log_sfrac 2 1 11629079 16777216 1 5760000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 11629079 16777216 5760000 rfl rfl rfl (Ns384p20 rfl)) 

theorem RS385to396.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 186065264 268435456 47 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 11629079 16777216 1 5760000 186065264 268435456 47 268435456 RS385to396.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz577 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz319 := qz577

noncomputable def Ns384p21 := @Enclosure.Real.IsNear.inv_image qz317 47453133 33554432 1 33554432 11863282 11863284 16777216 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 47453133 33554432 1 33554432 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 47453133 33554432 1 33554432 47453133 33554432 1 33554432 (BSN.sqrt_enclosure 2 1 23726566 23726567 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS385to396.d8 : Enclosure.Real.IsNear qz320 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 23726566 33554432 2 33554432 11863283 16777216 1 16777216 (Ns384p21 rfl rfl) rfl 

theorem RS385to396.d9 : Enclosure.Real.IsNear qz320 Bool.false 189812528 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 189812528 268435456 16 268435456 RS385to396.d8 rfl 

noncomputable def Ns384p22 := BSN.log_dyadic_bound 1 2 13 12 132638213186519040000 16777216 5760000 13079757671720842725 316234143225 18431655 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS385to396.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 18431655 16777216 1 5760000 := BSN.isNear_log_sfrac 3 1 18431655 16777216 1 5760000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 18431655 16777216 5760000 rfl rfl rfl (Ns384p22 rfl)) 

theorem RS385to396.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 294906480 268435456 47 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 18431655 16777216 1 5760000 294906480 268435456 47 268435456 RS385to396.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns384p23 := @Enclosure.Real.IsNear.inv_image qz321 58117981 33554432 1 33554432 9686330 9686331 16777216 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 58117981 33554432 1 33554432 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 58117981 33554432 1 33554432 58117981 33554432 1 33554432 (BSN.sqrt_enclosure 3 1 29058990 29058991 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS385to396.d12 : Enclosure.Real.IsNear qz323 Bool.false 19372661 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 19372661 33554432 1 33554432 19372661 33554432 1 33554432 (Ns384p23 rfl rfl) rfl 

theorem RS385to396.d13 : Enclosure.Real.IsNear qz323 Bool.false 154981288 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 19372661 33554432 1 33554432 154981288 268435456 8 268435456 RS385to396.d12 rfl 

noncomputable def Ns384p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns384p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns384p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns384p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns384p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns384p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns384p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns384p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns384p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns384p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns384p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns384p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns384p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns384p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns384p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns384p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns384p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns384p25 Ns384p26 Ns384p27 Ns384p28 200200021673987500790625 Ns384p29 Ns384p30 Ns384p31 Ns384p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns384p32 Ns384p33 151412625 Ns384p34 Ns384p35 1322214852783825 Ns384p27 Ns384p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns384p32 Ns384p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns384p34 Ns384p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns384p36 Ns384p37 1267389585 Ns384p38 Ns384p39 1927077560082675 Ns384p29 Ns384p30 Ns384p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns384p36 Ns384p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns384p38 Ns384p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS385to396.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns384p24 Ns384p25 1 Ns384p26 := Ns384p40 rfl rfl rfl 

noncomputable def Ns384p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns384p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns384p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns384p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns384p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns384p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns384p25 Ns384p26 Ns384p42 Ns384p43 9945 Ns384p44 Ns384p45 65835 Ns384p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns384p42 Ns384p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns384p44 Ns384p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS385to396.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns384p41 Ns384p25 1 Ns384p26 := Ns384p46 rfl 

noncomputable def Ns384p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns384p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS385to396.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns384p47 Ns384p25 1 Ns384p48 := BSN.pi_combine Ns384p24 Ns384p41 Ns384p25 Ns384p26 Ns384p48 Ns384p47 rfl rfl rfl rfl RS385to396.d14 RS385to396.d15 

theorem RS385to396.d17 : Enclosure.Real.IsNear Real.pi Bool.false 14148475504056880 4503599627370496 1 4503599627370496 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns384p47 Ns384p25 1 Ns384p48 14148475504056880 4503599627370496 1 4503599627370496 RS385to396.d16 rfl 

noncomputable def Ns384p49 := nat_lit 147443727375074537121690809726715087890625 

noncomputable def Ns384p50 := nat_lit 22889945643899497138335355216896171420000 

noncomputable def Ns384p51 := nat_lit 355592320898650075318906513310625 

noncomputable def Ns384p52 := BSN.log_dyadic_bound 3 5 17 16 Ns384p49 16777216 5760000 Ns384p50 Ns384p51 23258159 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 3) (BSN.artanhQ 5) 0 16 Ns384p50 Ns384p49 Ns384p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS385to396.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 23258159 16777216 1 5760000 := BSN.isNear_log_sfrac 4 1 23258159 16777216 1 5760000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 23258159 16777216 5760000 rfl rfl rfl (Ns384p52 rfl)) 

theorem RS385to396.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 372130544 268435456 47 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 23258159 16777216 1 5760000 372130544 268435456 47 268435456 RS385to396.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns384p53 := @Enclosure.Real.IsNear.inv_image qz325 67108865 33554432 1 33554432 8388607 8388608 16777216 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 67108865 33554432 1 33554432 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 67108865 33554432 1 33554432 67108865 33554432 1 33554432 (BSN.sqrt_enclosure 4 1 33554432 33554433 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS385to396.d20 : Enclosure.Real.IsNear qz327 Bool.false 16777215 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 16777215 33554432 1 33554432 16777215 33554432 1 33554432 (Ns384p53 rfl rfl) rfl 

theorem RS385to396.d21 : Enclosure.Real.IsNear qz327 Bool.false 134217720 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 16777215 33554432 1 33554432 134217720 268435456 8 268435456 RS385to396.d20 rfl 

noncomputable def Ns384p54 := nat_lit 61697213297292266380244507781205789317049021875 

noncomputable def Ns384p55 := nat_lit 12776162289178456695994184080609776001208236500 

noncomputable def Ns384p56 := nat_lit 57671893776295590731569354191667200000 

noncomputable def Ns384p57 := nat_lit 885951608314392539099884620 

noncomputable def Ns384p58 := nat_lit 1286943652057122751813246125 

noncomputable def Ns384p59 := BSN.log_dyadic_bound 2 3 22 21 Ns384p54 16777216 5760000 Ns384p55 Ns384p56 27001887 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 21 10 9927050056596826020 47940881637414340575 686533194547200 Ns384p57 Ns384p58 84004523356416638976000 Ns384p55 Ns384p54 Ns384p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 10 21 Ns384p57 Ns384p58 84004523356416638976000 rfl rfl rfl rfl)) rfl rfl 

theorem RS385to396.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 5760000 := BSN.isNear_log_sfrac 5 1 27001887 16777216 1 5760000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 27001887 16777216 5760000 rfl rfl rfl (Ns384p59 rfl rfl)) 

theorem RS385to396.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 432030192 268435456 47 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 5760000 432030192 268435456 47 268435456 RS385to396.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns384p60 := @Enclosure.Real.IsNear.inv_image qz328 75029991 33554432 1 33554432 7502998 7503000 16777216 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 75029991 33554432 1 33554432 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 75029991 33554432 1 33554432 75029991 33554432 1 33554432 (BSN.sqrt_enclosure 5 1 37514995 37514996 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS385to396.d24 : Enclosure.Real.IsNear qz329 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 15005998 33554432 2 33554432 7502999 16777216 1 16777216 (Ns384p60 rfl rfl) rfl 

theorem RS385to396.d25 : Enclosure.Real.IsNear qz329 Bool.false 120047984 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 120047984 268435456 16 268435456 RS385to396.d24 rfl 

noncomputable def Ns384p61 := BSN.log_dyadic_bound 2 10 5 4 94500000000 16777216 5760000 1291130880 26880 6802575 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz577)

theorem RS385to396.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 781250009 4500000000000000 := BSN.isNear_log_sfrac 6 1 4034683545132279 2251799813685248 781250009 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 1083052117253279893684224 604462909807314587353088 1000000011520000 5760000000000000000000 4034683545132279 2251799813685248 781250009 4500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 6802575 16777216 24973259072661432 36028797018963968 5760000 1000000000000000 rfl rfl rfl rfl (Ns384p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS385to396.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 480971758 268435456 48 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 781250009 4500000000000000 480971758 268435456 48 268435456 RS385to396.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns384p62 := @Enclosure.Real.IsNear.inv_image qz331 82191237 33554432 1 33554432 6849269 6849270 16777216 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 82191237 33554432 1 33554432 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 82191237 33554432 1 33554432 82191237 33554432 1 33554432 (BSN.sqrt_enclosure 6 1 41095618 41095619 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS385to396.d28 : Enclosure.Real.IsNear qz332 Bool.false 13698539 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 13698539 33554432 1 33554432 13698539 33554432 1 33554432 (Ns384p62 rfl rfl) rfl 

theorem RS385to396.d29 : Enclosure.Real.IsNear qz332 Bool.false 109588312 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 13698539 33554432 1 33554432 109588312 268435456 8 268435456 RS385to396.d28 rfl 

noncomputable def Ns384p63 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 16777216 5760000 11010900719820672 5524329195 9388794 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz577)

theorem RS385to396.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 781250009 4500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 781250009 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 1176230476650867868041216 604462909807314587353088 1000000011520000 5760000000000000000000 4381799983422711 2251799813685248 781250009 4500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 9388794 16777216 24973259072661432 36028797018963968 5760000 1000000000000000 rfl rfl rfl rfl (Ns384p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS385to396.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 522351262 268435456 48 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 781250009 4500000000000000 522351262 268435456 48 268435456 RS385to396.d30 rfl 

noncomputable abbrev qz334 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns384p64 := @Enclosure.Real.IsNear.inv_image qz334 88776683 33554432 1 33554432 6341191 6341192 16777216 (@Enclosure.Real.IsNear.of_eq qz334 (Real.sqrt qz333) Bool.false 88776683 33554432 1 33554432 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 88776683 33554432 1 33554432 88776683 33554432 1 33554432 (BSN.sqrt_enclosure 7 1 44388341 44388342 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS385to396.d32 : Enclosure.Real.IsNear qz335 Bool.false 12682383 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 12682383 33554432 1 33554432 12682383 33554432 1 33554432 (Ns384p64 rfl rfl) rfl 

theorem RS385to396.d33 : Enclosure.Real.IsNear qz335 Bool.false 101459064 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 12682383 33554432 1 33554432 101459064 268435456 8 268435456 RS385to396.d32 rfl 

noncomputable def Ns384p65 := nat_lit 1256945285058001618599936 

noncomputable def Ns384p66 := BSN.log_dyadic_bound 0 16 1 0 1 16777216 5760000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz577)

theorem RS385to396.d34 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 1562500027 9000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1562500027 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false Ns384p65 604462909807314587353088 1000000017280000 5760000000000000000000 9364972152248037 4503599627370496 1562500027 9000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 16777216 24973259072661432 36028797018963968 5760000 1000000000000000 rfl rfl rfl rfl (Ns384p66 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS385to396.d35 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 558195838 268435456 48 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 1562500027 9000000000000000 558195838 268435456 48 268435456 RS385to396.d34 rfl 

noncomputable abbrev qz337 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns384p67 := @Enclosure.Real.IsNear.inv_image qz337 94906265 33554432 1 33554432 5931641 5931642 16777216 (@Enclosure.Real.IsNear.of_eq qz337 (Real.sqrt qz336) Bool.false 94906265 33554432 1 33554432 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 94906265 33554432 1 33554432 94906265 33554432 1 33554432 (BSN.sqrt_enclosure 8 1 47453132 47453133 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz338 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS385to396.d36 : Enclosure.Real.IsNear qz338 Bool.false 11863283 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 11863283 33554432 1 33554432 11863283 33554432 1 33554432 (Ns384p67 rfl rfl) rfl 

theorem RS385to396.d37 : Enclosure.Real.IsNear qz338 Bool.false 94906264 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 11863283 33554432 1 33554432 94906264 268435456 8 268435456 RS385to396.d36 rfl 

noncomputable def Ns384p68 := nat_lit 1328140746012062765809664 

noncomputable def Ns384p69 := BSN.log_dyadic_bound 1 17 3 2 1252815 16777216 5760000 1448 3 1976071 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz577)

theorem RS385to396.d38 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 1562500027 9000000000000000 := BSN.isNear_log_sfrac 9 1 9895419672221413 4503599627370496 1562500027 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false Ns384p68 604462909807314587353088 1000000017280000 5760000000000000000000 9895419672221413 4503599627370496 1562500027 9000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 1976071 16777216 24973259072661432 36028797018963968 5760000 1000000000000000 rfl rfl rfl rfl (Ns384p69 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS385to396.d39 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 589812974 268435456 48 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 1562500027 9000000000000000 589812974 268435456 48 268435456 RS385to396.d38 rfl 

noncomputable abbrev qz340 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns384p70 := @Enclosure.Real.IsNear.inv_image qz340 100663297 33554432 1 33554432 5592405 5592406 16777216 (@Enclosure.Real.IsNear.of_eq qz340 (Real.sqrt qz339) Bool.false 100663297 33554432 1 33554432 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 100663297 33554432 1 33554432 100663297 33554432 1 33554432 (BSN.sqrt_enclosure 9 1 50331648 50331649 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz341 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS385to396.d40 : Enclosure.Real.IsNear qz341 Bool.false 11184811 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 11184811 33554432 1 33554432 11184811 33554432 1 33554432 (Ns384p70 rfl rfl) rfl 

theorem RS385to396.d41 : Enclosure.Real.IsNear qz341 Bool.false 89478488 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 11184811 33554432 1 33554432 89478488 268435456 8 268435456 RS385to396.d40 rfl 

noncomputable def Ns384p71 := nat_lit 1391827265235416537628672 

noncomputable def Ns384p72 := BSN.log_dyadic_bound 2 18 4 3 3571283520 16777216 5760000 14806464 960 3743727 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 18) 0 3 14806464 3571283520 960 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz706 := (Enclosure.sfrac Bool.false 10 1)

noncomputable abbrev qz578 := qz706

noncomputable abbrev qz342 := qz578

noncomputable abbrev qz1 := qz342

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10) qz577)

theorem RS385to396.d42 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 10369921216632549 4503599627370496 1562500027 9000000000000000 := BSN.isNear_log_sfrac 10 1 10369921216632549 4503599627370496 1562500027 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false Ns384p71 604462909807314587353088 1000000017280000 5760000000000000000000 10369921216632549 4503599627370496 1562500027 9000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 3743727 16777216 24973259072661432 36028797018963968 5760000 1000000000000000 rfl rfl rfl rfl (Ns384p72 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS385to396.d43 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 618095470 268435456 48 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 10369921216632549 4503599627370496 1562500027 9000000000000000 618095470 268435456 48 268435456 RS385to396.d42 rfl 

noncomputable abbrev qz344 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10))

noncomputable def Ns384p73 := @Enclosure.Real.IsNear.inv_image qz344 106108431 33554432 1 33554432 5305421 5305422 16777216 (@Enclosure.Real.IsNear.of_eq qz344 (Real.sqrt qz343) Bool.false 106108431 33554432 1 33554432 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz343) Bool.false 106108431 33554432 1 33554432 106108431 33554432 1 33554432 (BSN.sqrt_enclosure 10 1 53054215 53054216 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz345 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

theorem RS385to396.d44 : Enclosure.Real.IsNear qz345 Bool.false 10610843 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz345 Bool.false 10610843 33554432 1 33554432 10610843 33554432 1 33554432 (Ns384p73 rfl rfl) rfl 

theorem RS385to396.d45 : Enclosure.Real.IsNear qz345 Bool.false 84886744 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz345 Bool.false 10610843 33554432 1 33554432 84886744 268435456 8 268435456 RS385to396.d44 rfl 

theorem RS385to396.d46 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz707 := (@instHMul Real Real.instMul)

noncomputable abbrev qz579 := qz707

noncomputable abbrev qz346 := (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz2 := qz346

theorem RS385to396.d47 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS385to396.d46 rfl 

noncomputable abbrev qz347 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 2 1) Real.pi))

noncomputable abbrev qz3 := qz347

theorem RS385to396.d48 : Enclosure.Real.IsNear qz3 Bool.false 5340353 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 5340353 33554432 1 33554432 5340353 33554432 1 33554432 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 2670176 2670177 16777216 RS385to396.d47 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns384p74 := nat_lit 8854437155380584775680000 

noncomputable def Ns384p75 := nat_lit 37449505453700033220542726144 

noncomputable abbrev qz708 := (Enclosure.sfrac Bool.false 728464 1000)

noncomputable abbrev qz580 := qz708

noncomputable abbrev qz348 := qz580

noncomputable abbrev qz4 := qz348

noncomputable abbrev qz349 := qz579

noncomputable abbrev qz5 := qz349

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 10)

noncomputable abbrev qz350 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz709 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 728464 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz581 := qz709

noncomputable abbrev qz351 := qz581

noncomputable abbrev qz352 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz7 := (@HPow.hPow Real Real Real qz350 qz351 qz352)

noncomputable abbrev qz710 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 728464 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz582 := qz710

noncomputable abbrev qz353 := qz582

noncomputable abbrev qz8 := qz353

noncomputable def Ns384p76 := @Enclosure.Real.IsNear.subLit_ff_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8)) 13267321 134217728 151837 134217728 745822917383705209395 4722366482869645213696 485671335478932076759 Ns384p74 Ns384p75 

noncomputable def Ns384p77 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin BSN.quadSignNeg 9 10 728464 1000 197 268435456 134217728 4503599627370496 Bool.false 366841826113 2530 618095470 48 84886744 8 

noncomputable def Ns384p78 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 728464 1000 94 148 268435456 134217728 4503599627370496 Bool.false 366841826113 2530 

noncomputable def Ns384p79 := Ns384p78 558195838 48 94906264 8 589812974 48 89478488 8 Bool.false 172407693 114194 Bool.true 147948562 Bool.true 410392795 14148475504056880 1 Bool.false 228686114 Bool.true Bool.false 11261327 Bool.false Bool.false 95308719 

noncomputable def Ns384p80 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 728464 1000 39 32 268435456 134217728 4503599627370496 Bool.false 366841826113 2530 

noncomputable def Ns384p81 := Ns384p80 480971758 48 109588312 8 522351262 48 101459064 8 Bool.false 81903439 84694 Bool.false 26575690 Bool.true 179225904 14148475504056880 1 Bool.false 26532297 Bool.false Bool.false 210793599 Bool.false Bool.false 172407693 

noncomputable def Ns384p82 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 728464 1000 227 123 268435456 134217728 4503599627370496 Bool.false 366841826113 2530 

noncomputable def Ns384p83 := Ns384p82 372130544 47 134217720 8 432030192 47 120047984 16 Bool.true 37761828 49839 Bool.false 41885292 Bool.false 259520651 14148475504056880 1 Bool.false 41715536 Bool.false Bool.false 220940290 Bool.false Bool.false 81903439 

noncomputable def Ns384p84 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 728464 1000 548 360 268435456 134217728 4503599627370496 Bool.false 366841826113 2530 

noncomputable def Ns384p85 := Ns384p84 186065264 47 189812528 16 294906480 47 154981288 8 Bool.true 268435416 2583 Bool.false 231708948 Bool.false 216397890 14148475504056880 1 Bool.false 174488920 Bool.false Bool.false 185833962 Bool.false Bool.true 37761828 

noncomputable def Ns384p86 := nat_lit 505208317369084324408002006761294568436142220190338787 

noncomputable def Ns384p87 := nat_lit 369684739836635481151859330675000337843571654656000 

noncomputable def Ns384p88 := nat_lit 98465077434163214415727366635520000 

noncomputable def Ns384p89 := nat_lit 430369679625885888412431034579640647680 

noncomputable abbrev qz354 := (@Eq.refl Real qz580)

noncomputable abbrev qz9 := qz354

noncomputable def Ns384p90 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 728464 1000 2122640197184 16000000 1456928 4000 2000 Ns384p88 Ns384p89 qz9 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns384p91 := nat_lit 662186645742006205688056390302164016740620330847880854896640 

noncomputable abbrev qz711 := (@instHSub Real Real.instSub)

noncomputable abbrev qz583 := qz711

noncomputable abbrev qz355 := qz583

noncomputable abbrev qz584 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz712 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz713 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz585 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1456928))))

noncomputable abbrev qz356 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 728464 4000) (Real.log (Enclosure.sfrac Bool.false 2122640197184 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz585))

noncomputable abbrev qz586 := (Enclosure.sfrac Bool.false 728464 2000)

noncomputable abbrev qz10 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz356 qz586) (@HMul.hMul Real Real Real qz349 qz586 (Real.log Real.pi)))

noncomputable def Ns384p92 := @Enclosure.Real.IsNear.addLit_ft_p qz10 (Enclosure.sfrac Bool.true Ns384p88 Ns384p89) 1538646396231855937523 1125899906842624000 7236906821161871 768000000000000000000 Ns384p88 Ns384p89 0 1 Ns384p91 

noncomputable def Ns384p93 := nat_lit 6453550734300858286176468992000 

noncomputable abbrev qz11 := (@HSub.hSub Real Real Real qz355 qz356 qz586)

noncomputable def Ns384p94 := @Enclosure.Real.IsNear.subLit_ff_p qz11 (@HMul.hMul Real Real Real qz5 qz586 (Real.log Real.pi)) 2008087271293603583987 1125899906842624000 11986728038291 3000000000000000000 1748803537569 4194304000 45529 8388608000 Ns384p93 1538646396231855937523 1125899906842624000 

noncomputable abbrev qz12 := qz356

noncomputable def Ns384p95 := @Enclosure.Real.IsNear.subLit_ff_p qz12 qz586 483635209232541241751 225179981368524800 11986728038291 3000000000000000000 728464 2000 0 1 803234908517441433594800 2008087271293603583987 1125899906842624000 11986728038291 3000000000000000000 

noncomputable def Ns384p96 := nat_lit 1089049674041462301545870013390389248 

noncomputable def Ns384p97 := nat_lit 57039937077099388762849280 

noncomputable def Ns384p98 := nat_lit 4835703278458516698824704 

noncomputable def Ns384p99 := nat_lit 53419938562244911012589568 

noncomputable def Ns384p100 := BSN.log_dyadic_bound 25488197184 4219792197184 2 1 Ns384p99 134217728 46080000 649648195690465529856 649648195690465529856 1621411 4245280394368 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 25488197184) (BSN.artanhQ 4219792197184) 0 1 649648195690465529856 Ns384p99 649648195690465529856 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz357 := (Real.log (Enclosure.sfrac Bool.false 2122640197184 16000000))

noncomputable abbrev qz358 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns384p101 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 728464 4000) qz357 728464 4000 0 1 53122581054549095 4503599627370496 195312653 9000000000000000 483723598566513149251 225179981368524800 8892389778437 2250000000000000000 (Enclosure.Real.IsNear.const Bool.false 728464 4000) (BSN.isNear_log_sfrac 2122640197184 16000000 53122581054549095 4503599627370496 195312653 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2122640197184) qz358)) Bool.false Ns384p97 Ns384p98 1000000783360000 46080000000000000000000 53122581054549095 4503599627370496 195312653 9000000000000000 (BSN.log_rat_reduce_isNear 2122640197184 16000000 17 4245280394368 4194304000000 1621411 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns384p100 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns384p102 := BSN.arctan_dyadic_bound_f 1000 1456928 1 0 16777216 5760000 0 1 1 0 1 1 11515 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1456928) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1456928) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz587 := qz712

noncomputable abbrev qz359 := qz587

noncomputable abbrev qz13 := qz359

noncomputable abbrev qz588 := qz713

noncomputable abbrev qz360 := qz588

noncomputable abbrev qz14 := qz360

noncomputable abbrev qz714 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz589 := qz714

noncomputable abbrev qz361 := qz589

noncomputable abbrev qz15 := (@Enclosure.Real.IsNear.mulLit_ff qz361 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz362 := (@Nat.cast Real Real.instNatCast 1456928)

noncomputable def Ns384p103 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz362)) 884279719003555 562949953421312 1 2000000000000000 11515 16777216 1 5760000 14829269481428300595200 883893339719075 562949953421312 3125000009 18000000000000000 qz15 (Ns384p102 rfl) rfl rfl 

noncomputable abbrev qz363 := (@HMul.hMul Real Real Real qz579 qz584 qz585)

noncomputable abbrev qz16 := qz363

noncomputable abbrev qz364 := qz584

noncomputable abbrev qz17 := qz364

noncomputable abbrev qz365 := qz585

noncomputable abbrev qz18 := qz365

noncomputable abbrev qz366 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns384p104 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 728464 4000) qz357) qz16 483723598566513149251 225179981368524800 8892389778437 2250000000000000000 883893339719075 2251799813685248 3125000009 72000000000000000 Ns384p96 483635209232541241751 225179981368524800 11986728038291 3000000000000000000 (Ns384p101 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz18 1 4 0 1 883893339719075 562949953421312 3125000009 18000000000000000 883893339719075 2251799813685248 3125000009 72000000000000000 qz366 Ns384p103 rfl) 

noncomputable def Ns384p105 := @Ns384p92 Ns384p86 Ns384p87 7236906821161871 768000000000000000000 (@Ns384p94 7236906821161871 768000000000000000000 (Ns384p95 (Ns384p104 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 728464 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz586 (Real.log Real.pi) 728464 2000 0 1 38410761 33554432 1 67108864 1748803537569 4194304000 45529 8388608000 (Enclosure.Real.IsNear.const Bool.false 728464 2000) RS385to396.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns384p88 Ns384p89) 

noncomputable abbrev qz367 := (@instHAdd Real Real.instAdd)

noncomputable def Ns384p106 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns384p86 Ns384p87 7236906821161871 768000000000000000000 5731903533 4194304 317 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz367 qz10 (Enclosure.sfrac Bool.true Ns384p88 Ns384p89)) Bool.false Ns384p86 Ns384p87 7236906821161871 768000000000000000000 Ns384p90 (Ns384p105 rfl rfl)) 

noncomputable def Ns384p107 := nat_lit 3506283099367896998711257190418898187448033667130775565720243481542701567129018868349413879329377443216185607001577742674839191402821062656 

noncomputable def Ns384p108 := nat_lit 69061887427279807374175457422696049589758900585025510522285359577850094671315332446731519433112496475662717985575392155893264493730122956800 

noncomputable def Ns384p109 := nat_lit 2492926867999569531888211686093446347754608210943628570397192976551678404051841809576733608941635820150625514125318281812596261523456 

noncomputable def Ns384p110 := nat_lit 17509658697282751771302793296707970170558890725980409333437516851258491305731964271692426101228408909909299293841718167636242894281603158016 

noncomputable def Ns384p111 := nat_lit 2417166059954793258096141009794361735641561520475892868279987585224753313496036635635603180158937376648195129495138725456264257280554303488000 

noncomputable abbrev qz368 := (BSN.sinEvenQ 68719476736)

noncomputable abbrev qz369 := (BSN.sinOddQ 68719476736)

noncomputable def Ns384p112 := BSN.sin_dyadic_bound_f 107909362834 68719476736 4 3 33554432 11531251 Ns384p107 Ns384p108 Ns384p109 Ns384p110 Ns384p111 Ns384p109 33554427 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107909362834) qz368 0 3 Ns384p107 Ns384p108 Ns384p109 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107909362834) qz369 0 3 Ns384p110 Ns384p111 Ns384p109 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p113 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5731903533) (@Nat.cast Real Real.instNatCast 4194304)) Bool.false 5731903533 4194304 317 33554432 Bool.true 33554427 33554432 1 5760000 (Ns384p106 rfl) (Enclosure.sfrac_false_div 5731903533 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5731903533) (@Nat.cast Real Real.instNatCast 4194304)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949180793463220203421696) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 33554427 33554432 217 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q1 5731903533 4194304 226375608064910080 72057594037927936 217 949180793463220203421696 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554427 33554432 949180793463220203421696 604462909807314587353088 107909362834 68719476736 11531251 11520000 (Ns384p112 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p114 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns384p86 Ns384p87 7236906821161871 768000000000000000000 366841826113 268435456 2530 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz367 qz10 (Enclosure.sfrac Bool.true Ns384p88 Ns384p89)) Bool.false Ns384p86 Ns384p87 7236906821161871 768000000000000000000 Ns384p90 (Ns384p105 rfl rfl)) 

noncomputable def Ns384p115 := Ns384p85 49839 BSN.abs_quadSignPos (BSN.cos_quad_nat0 548 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 174488920 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 360 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 185833962 268435456) qz9 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 33554427 33554432 1815893 188743680000 268435416 268435456 2583 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 33554427 33554432 1815893 188743680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 33554427 33554432 1859474432 193273528320000 33554427 33554432 1815893 188743680000 (Ns384p113 rfl rfl) rfl)) rfl) (Ns384p114 rfl) RS385to396.d7 

noncomputable def Ns384p116 := nat_lit 25152635986371428263079856094503135380176555692196187391011037800103936 

noncomputable def Ns384p117 := nat_lit 1087025049619513796520974048308631508761049663116835882438097565248389120 

noncomputable def Ns384p118 := nat_lit 8308879173024858759018121830188880488578465376302616035516397715456 

noncomputable def Ns384p119 := nat_lit 75441290200768235071721532039849028379552510145835956940962080604880896 

noncomputable def Ns384p120 := nat_lit 48916127232878120843443832173888417894247234840257614709714390436177510400 

noncomputable abbrev qz370 := (BSN.cosEvenQ 268435456)

noncomputable abbrev qz371 := (BSN.cosOddQ 268435456)

noncomputable def Ns384p121 := BSN.cos_dyadic_bound_f 231708948 268435456 3 2 268435456 134217728 Ns384p116 Ns384p117 Ns384p118 Ns384p119 Ns384p120 Ns384p118 174488920 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 231708948) qz370 0 2 Ns384p116 Ns384p117 Ns384p118 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 231708948) qz371 0 2 Ns384p119 Ns384p120 Ns384p118 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p122 := nat_lit 19133307259506713924068165971266863154353258641190585328776410544800000 

noncomputable def Ns384p123 := nat_lit 4808661148221230901830180612220164266251616140369889863248100000000 

noncomputable def Ns384p124 := nat_lit 57390304456223699310400837552576149134527272691291016206602735434400000 

noncomputable def Ns384p125 := BSN.cos_dyadic_bound_f 216397890 268435456 3 2 268435456 134217728 Ns384p122 Ns384p117 Ns384p123 Ns384p124 Ns384p120 Ns384p123 185833962 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 216397890) qz370 0 2 Ns384p122 Ns384p117 Ns384p123 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 216397890) qz371 0 2 Ns384p124 Ns384p120 Ns384p123 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p126 := nat_lit 3077841064872484254523793469696 

noncomputable def Ns384p127 := nat_lit 623075623024179315423659559506411520 

noncomputable def Ns384p128 := nat_lit 4361529361169255207965616916544880640 

noncomputable abbrev qz372 := (BSN.sinEvenQ 268435456)

noncomputable abbrev qz373 := (BSN.sinOddQ 268435456)

noncomputable def Ns384p129 := BSN.sin_dyadic_bound_f 41885292 268435456 2 1 268435456 134217728 Ns384p126 Ns384p127 Ns384p126 Ns384p126 Ns384p128 Ns384p126 41715536 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 41885292) qz372 0 1 Ns384p126 Ns384p127 Ns384p126 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 41885292) qz373 0 1 Ns384p126 Ns384p128 Ns384p126 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p130 := nat_lit 71245007776108261249277586969623694014765151639075832639644085641815905 

noncomputable def Ns384p131 := nat_lit 9783225446575624168688766434777683578849446968051522941942878087235502080 

noncomputable def Ns384p132 := nat_lit 20576683407401051789896450286174915574105978008714492125297732495201 

noncomputable def Ns384p133 := nat_lit 186560753354766796807114800191408248746788749376041642973722123209287521 

noncomputable def Ns384p134 := nat_lit 179359133187219776425960717970924198945573194414277920602286098265984204800 

noncomputable def Ns384p135 := BSN.sin_dyadic_bound_f 259520651 268435456 3 2 268435456 134217728 Ns384p130 Ns384p131 Ns384p132 Ns384p133 Ns384p134 Ns384p132 220940290 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 259520651) qz372 0 2 Ns384p130 Ns384p131 Ns384p132 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 259520651) qz373 0 2 Ns384p133 Ns384p134 Ns384p132 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p136 := Ns384p83 84694 BSN.abs_quadSignPos (BSN.cos_quad_nat3 227 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 41715536 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 123 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 220940290 268435456) qz9 rfl rfl (Ns384p115 RS385to396.d9 RS385to396.d11 RS385to396.d13 RS385to396.d17 (Ns384p121 rfl rfl) (Ns384p125 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns384p114 rfl) RS385to396.d19 RS385to396.d21 RS385to396.d23 RS385to396.d25 RS385to396.d17 (Ns384p129 rfl rfl) (Ns384p135 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns384p137 := nat_lit 498813497602995824108371210000 

noncomputable def Ns384p138 := BSN.sin_dyadic_bound_f 26575690 268435456 2 1 268435456 134217728 Ns384p137 Ns384p127 Ns384p137 Ns384p137 Ns384p128 Ns384p137 26532297 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 26575690) qz372 0 1 Ns384p137 Ns384p127 Ns384p137 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 26575690) qz373 0 1 Ns384p137 Ns384p128 Ns384p137 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p139 := nat_lit 9001674038446679450400940278182247994226266180841549553616628289110016 

noncomputable def Ns384p140 := nat_lit 1064648476252813644149242379410178212618208739034420150774410510336 

noncomputable def Ns384p141 := nat_lit 27002892818387532723914522349787923626253562125046579820548336046309376 

noncomputable def Ns384p142 := BSN.cos_dyadic_bound_f 179225904 268435456 3 2 268435456 134217728 Ns384p139 Ns384p117 Ns384p140 Ns384p141 Ns384p120 Ns384p140 210793599 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 179225904) qz370 0 2 Ns384p139 Ns384p117 Ns384p140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 179225904) qz371 0 2 Ns384p141 Ns384p120 Ns384p140 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p143 := Ns384p81 114194 BSN.abs_quadSignPos (BSN.cos_quad_nat3 39 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 26532297 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 210793599 268435456) qz9 rfl rfl (Ns384p136 rfl rfl) (Ns384p114 rfl) RS385to396.d27 RS385to396.d29 RS385to396.d31 RS385to396.d33 RS385to396.d17 (Ns384p138 rfl rfl) (Ns384p142 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p144 := nat_lit 4179608875022653964312173625584222503372168236941815858763613637918976 

noncomputable def Ns384p145 := nat_lit 229554593063077115611563399567505161706705109852211208111211888896 

noncomputable def Ns384p146 := nat_lit 12538367515881835738705297749953532499793091300605743153874618489979136 

noncomputable def Ns384p147 := BSN.cos_dyadic_bound_f 147948562 268435456 3 2 268435456 134217728 Ns384p144 Ns384p117 Ns384p145 Ns384p146 Ns384p120 Ns384p145 228686114 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 147948562) qz370 0 2 Ns384p144 Ns384p117 Ns384p145 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 147948562) qz371 0 2 Ns384p146 Ns384p120 Ns384p145 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p148 := nat_lit 15312788235552470408406508034007494499375210514884288019830971626604809509345129045219624765752996827618140625 

noncomputable def Ns384p149 := nat_lit 67052582193422231333984484018745857420694574238012043916021913709013615522643186318434558042568065189255577600 

noncomputable def Ns384p150 := nat_lit 22824261294806629051263324648689834210343706653344038505126307281022643535647668680643647947968994140625 

noncomputable def Ns384p151 := nat_lit 92696726906557827079391014531758037696556125018479217537469087684063422577115975284147467605448813325179740625 

noncomputable def Ns384p152 := nat_lit 6101784979601423051392588045705873025283206255659095996357994147520239012560529954977544781873693932222257561600 

noncomputable def Ns384p153 := BSN.cos_dyadic_bound_f 410392795 268435456 4 3 268435456 134217728 Ns384p148 Ns384p149 Ns384p150 Ns384p151 Ns384p152 Ns384p150 11261327 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 410392795) qz370 0 3 Ns384p148 Ns384p149 Ns384p150 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 410392795) qz371 0 3 Ns384p151 Ns384p152 Ns384p150 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz590 := (BSN.cos_quad_nat0 148 rfl)

noncomputable def Ns384p154 := Ns384p79 139969 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 94 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 228686114 268435456) BSN.abs_quadSignPos qz590 (BSN.sfrac_eq_quadSignPos_mul Bool.false 11261327 268435456) qz9 rfl rfl (Ns384p143 rfl) (Ns384p114 rfl) RS385to396.d35 RS385to396.d37 RS385to396.d39 RS385to396.d41 RS385to396.d17 (Ns384p147 rfl rfl) (Ns384p153 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p155 := nat_lit 21488721719010245258235925974775123280895833342015558914247218626580201368815116691416035525497476773761253376 

noncomputable def Ns384p156 := nat_lit 871683568514489007341798292243696146469029465094156570908284878217177001794361422139649254553384847460322508800 

noncomputable def Ns384p157 := nat_lit 3613304365552928404339781298728399869616278684402422908497550408140051773963545084682022163290915864576 

noncomputable def Ns384p158 := nat_lit 107378745722665320727099872213794642660803124817134672563801568421442628731197275402418949922938442841887604736 

noncomputable def Ns384p159 := nat_lit 30508924898007115256962940228529365126416031278295479981789970737601195062802649774887723909368469661111287808000 

noncomputable def Ns384p160 := BSN.sin_dyadic_bound_f 351958976 268435456 4 3 268435456 134217728 Ns384p155 Ns384p156 Ns384p157 Ns384p158 Ns384p159 Ns384p157 259437680 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 351958976) qz372 0 3 Ns384p155 Ns384p156 Ns384p157 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 351958976) qz373 0 3 Ns384p158 Ns384p159 Ns384p157 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz374 := (BSN.cos_quad_nat1 197 rfl)

noncomputable def Ns384p161 := Ns384p77 Bool.false 95308719 139969 Bool.true 351958976 14148475504056880 1 Bool.false 259437680 Bool.true Bool.false 13267321 151837 BSN.abs_quadSignNeg qz374 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 259437680 268435456) qz9 rfl (Ns384p154 rfl) (Ns384p114 rfl) RS385to396.d43 RS385to396.d45 RS385to396.d17 (Ns384p160 rfl rfl) rfl 

noncomputable def Ns384p162 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) 13267321 268435456 151837 268435456 13267321 268435456 151837 268435456 7122838725066752 13267321 134217728 151837 134217728 (Ns384p161 rfl rfl rfl rfl) 

noncomputable def Ns384p163 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8) 10225695 33554432 1 33554432 72936159095661 140737488355328 11870453125651 65970697666560000 745822917383705209395 4722366482869645213696 

noncomputable def Ns384p164 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz7 1 1 0 1 10225695 33554432 1 33554432 10225695 33554432 1 33554432 

noncomputable abbrev qz19 := qz351

noncomputable abbrev qz20 := (@Enclosure.Real.IsNear.of_eq qz351 (@HMul.hMul Real Real Real qz349 qz348 qz347) Bool.false 243140931737 2097152000 45529 2097152000 (BSN.t_div_two_pi_mk qz348 728464 1000 qz354) (@Enclosure.Real.IsNear.mulLit_ff qz348 qz347 728464 1000 0 1 5340353 33554432 1 33554432 243140931737 2097152000 45529 2097152000 (Enclosure.Real.IsNear.const Bool.false 728464 1000) RS385to396.d48 rfl))

noncomputable def Ns384p165 := @Enclosure.Real.IsNear.sqrt_image qz19 243140931737 2097152000 45529 2097152000 180648325 180648359 16777216 qz20 

noncomputable abbrev qz715 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 728464 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz591 := qz715

noncomputable abbrev qz375 := qz591

noncomputable abbrev qz21 := qz375

noncomputable def Ns384p166 := @Enclosure.Real.IsNear.sqrt_image qz21 90324171 8388608 17 16777216 55052483 55052489 16777216 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 361296684 33554432 34 33554432 90324171 8388608 17 16777216 (Ns384p165 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz592 := (Real.sqrt qz715)

noncomputable abbrev qz376 := qz592

noncomputable abbrev qz22 := qz376

noncomputable def Ns384p167 := @Enclosure.Real.IsNear.inv_image qz22 27526243 8388608 3 16777216 5112847 5112848 16777216 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 110104972 33554432 6 33554432 27526243 8388608 3 16777216 (Ns384p166 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns384p168 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz22) Bool.false 10225695 33554432 1 33554432 10225695 33554432 1 33554432 (Ns384p167 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz23 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz353))

noncomputable abbrev qz593 := (@HMul.hMul Real Real Real qz707 qz710 qz710)

noncomputable abbrev qz594 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz377 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz593 qz582) qz594)

noncomputable abbrev qz24 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz377))

noncomputable def Ns384p169 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz8) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz23) qz24) Bool.false 72936159095661 

noncomputable def Ns384p170 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz23) qz24 76530731 8388608 9149 

noncomputable def Ns384p171 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz23) Bool.false 306122924 33554432 18298 33554432 76530731 8388608 9149 

noncomputable def Ns384p172 := @Enclosure.Real.IsNear.recentre' qz23 Bool.false 3677934 33554432 633097216 96636764160000 1838967 16777216 618259 94371840000 

noncomputable abbrev qz25 := (@HMul.hMul Real Real Real qz349 qz346 qz353)

noncomputable abbrev qz378 := (@Nat.cast Real Real.instNatCast 33554432)

noncomputable def Ns384p173 := @Enclosure.Real.IsNear.cos_image qz25 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 161806875) qz378) Bool.false 161806875 33554432 107 16777216 Bool.false 3677934 33554432 1 

noncomputable def Ns384p174 := nat_lit 458763282064354333912560183 

noncomputable def Ns384p175 := nat_lit 72057594037927936000000000000000 

noncomputable def Ns384p176 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz8 884279719003555 140737488355328 1 500000000000000 6438091 8388608 17 16777216 5693073300399316413505 1180591620717411303424 Ns384p174 

noncomputable def Ns384p177 := @Enclosure.Real.IsNear.subLit_ff_p qz21 qz1 90324171 8388608 17 16777216 10 1 0 1 6438091 6438091 8388608 17 

noncomputable abbrev qz379 := (Enclosure.Real.IsNear.const Bool.false 10 1)

noncomputable def Ns384p178 := @Ns384p177 16777216 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 361296684 33554432 34 33554432 90324171 8388608 17 16777216 (Ns384p165 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns384p179 := @Enclosure.Real.IsNear.recentre' qz25 Bool.false 5693073300399316413505 1180591620717411303424 Ns384p174 Ns384p175 161806875 33554432 107 16777216 (@Ns384p176 Ns384p175 RS385to396.d47 (Ns384p178 rfl rfl) rfl) 

noncomputable def Ns384p180 := nat_lit 3245112595497199873242590767768379874961 

noncomputable def Ns384p181 := nat_lit 2676089423823674776984286192717803380717649920 

noncomputable def Ns384p182 := nat_lit 18732625966765723438890003349024623665023549440 

noncomputable def Ns384p183 := BSN.sin_dyadic_bound_f 7547575091 68719476736 2 1 33554432 11531251 Ns384p180 Ns384p181 Ns384p180 Ns384p180 Ns384p182 Ns384p180 3677934 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 7547575091) qz368 0 1 Ns384p180 Ns384p181 Ns384p180 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 7547575091) qz369 0 1 Ns384p180 Ns384p182 Ns384p180 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz380 := (@Nat.cast Real Real.instNatCast Ns384p98)

noncomputable def Ns384p184 := @Ns384p173 5760000 (Ns384p179 rfl) (Enclosure.sfrac_false_div 161806875 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 161806875) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 531113380773471002296320) qz380) 226375608064910080 72057594037927936 Bool.false 3677934 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 161806875 33554432 226375608064910080 72057594037927936 0 531113380773471002296320 Ns384p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 3677934 33554432 531113380773471002296320 Ns384p98 7547575091 68719476736 11531251 11520000 (Ns384p183 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p185 := @Enclosure.Real.IsNear.inv_image qz23 1838967 16777216 618259 94371840000 153052313 153070611 16777216 (Ns384p172 (Ns384p184 rfl rfl) rfl) rfl 

noncomputable def Ns384p186 := @Enclosure.Real.IsNear.recentre' qz24 Bool.false 953031 16777216 

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz349 qz346 qz377)

noncomputable def Ns384p187 := @Enclosure.Real.IsNear.cos_image qz26 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6350011)) (@Nat.cast Real Real.instNatCast 4194304)) Bool.true 6350011 4194304 

noncomputable def Ns384p188 := nat_lit 14993539587678584008043506805 

noncomputable def Ns384p189 := nat_lit 9903520314283042199192993792 

noncomputable def Ns384p190 := nat_lit 19511017500472899725969666943642651 

noncomputable def Ns384p191 := @Enclosure.Real.IsNear.recentre' qz26 Bool.true Ns384p188 Ns384p189 Ns384p190 

noncomputable def Ns384p192 := nat_lit 1208925819614629174706176000000000000000 

noncomputable abbrev qz27 := qz377

noncomputable def Ns384p193 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz27 884279719003555 140737488355328 1 500000000000000 16955652454151 

noncomputable abbrev qz381 := (@HSub.hSub Real Real Real qz583 qz593 qz582)

noncomputable abbrev qz28 := qz381

noncomputable abbrev qz382 := qz594

noncomputable abbrev qz29 := qz382

noncomputable def Ns384p194 := @Enclosure.Real.IsNear.subLit_tf qz28 qz29 12557605943047 70368744177664 723003149 281474976710656 1 16 

noncomputable abbrev qz383 := qz593

noncomputable abbrev qz30 := qz383

noncomputable def Ns384p195 := @Enclosure.Real.IsNear.subLit_ff_n qz30 qz8 41449015724281 70368744177664 437790477 281474976710656 6438091 8388608 17 16777216 

noncomputable def Ns384p196 := @Enclosure.Real.IsNear.mulLit_ff qz8 qz8 6438091 8388608 17 16777216 6438091 8388608 17 16777216 41449015724281 70368744177664 

noncomputable def Ns384p197 := nat_lit 3117880416718113488335469785528892836368036383087528741116431930522592730634250778686801 

noncomputable def Ns384p198 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600 

noncomputable def Ns384p199 := nat_lit 4298270383100058250345414715828127847378471238418785596893236169977524723986576721 

noncomputable def Ns384p200 := nat_lit 18875808718946331804528526969606776829377567026403773019820237837787422009112356767249745 

noncomputable def Ns384p201 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600 

noncomputable def Ns384p202 := BSN.cos_dyadic_bound_f 6350011 4194304 4 3 16777216 5760000 Ns384p197 Ns384p198 Ns384p199 Ns384p200 Ns384p201 Ns384p199 953031 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 6350011) (BSN.cosEvenQ 4194304) 0 3 Ns384p197 Ns384p198 Ns384p199 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 6350011) (BSN.cosOddQ 4194304) 0 3 Ns384p200 Ns384p201 Ns384p199 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz384 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns384p203 := @Ns384p186 1577737216 96636764160000 953031 16777216 1540759 94371840000 (@Ns384p187 271 16777216 Bool.false 953031 16777216 1 5760000 (@Ns384p191 Ns384p192 6350011 4194304 271 16777216 (@Ns384p193 70368744177664 723003149 281474976710656 Ns384p188 Ns384p189 Ns384p190 Ns384p192 RS385to396.d47 (@Ns384p194 0 1 271290439266416 16955652454151 70368744177664 723003149 281474976710656 (@Ns384p195 105340833674691608576 12557605943047 70368744177664 723003149 281474976710656 (@Ns384p196 437790477 281474976710656 (Ns384p178 rfl rfl) (Ns384p178 rfl rfl) rfl) (Ns384p178 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6350011 4194304) (BSN.cos_neg_of_bound 6350011 4194304 Bool.false 953031 16777216 1 5760000 (Ns384p202 rfl rfl)) rfl rfl) 

noncomputable abbrev qz31 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 10) (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 10 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1))

noncomputable def Ns384p204 := @Ns384p163 485671335478932076759 Ns384p74 (Ns384p164 qz31 (@Enclosure.Real.IsNear.of_eq qz7 (@Inv.inv Real Real.instInv qz22) Bool.false 10225695 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz19 (BSN.t_div_two_pi_nonneg qz4 728464 1000 qz9)) Ns384p168) rfl) (@Ns384p169 140737488355328 11870453125651 65970697666560000 (BSN.correction_mk qz8 (BSN.cos_two_pi_p_ne_zero_mk qz4 728464 1000 10 qz9 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 728464 1000 10 qz9 rfl rfl rfl))) (@Ns384p170 16777216 953031 16777216 1540759 94371840000 72936159095661 140737488355328 11870453125651 65970697666560000 (@Ns384p171 16777216 (Ns384p185 rfl rfl rfl rfl rfl) rfl) (Ns384p203 rfl) rfl)) 

noncomputable abbrev qz32 := qz355

noncomputable def Ns384p205 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 279020558697730550323 4722366482869645213696 10502464157076402796759 Ns384p74 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8))) Bool.true 279020558697730550323 4722366482869645213696 10502464157076402796759 Ns384p74 (BSN.hardyZApproximantRS₀_eq qz4 10 (@BSN.floor_sqrt_eq_dec qz4 728464 1000 10 qz9 rfl rfl rfl)) (@Ns384p76 279020558697730550323 4722366482869645213696 10502464157076402796759 Ns384p74 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10)) Bool.false 13267321 134217728 151837 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (Ns384p162 (Ns384p161 rfl rfl rfl rfl) rfl rfl)) (Ns384p204 rfl) rfl rfl)) 

theorem RS385to396.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 279020558697730550323 4722366482869645213696 10502464157076402796759 Ns384p74 := Ns384p205 

theorem RS385to396.d50 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS385to396.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS385to396.d3 a b h)) 

noncomputable def Ns384p206 := nat_lit 5902958103587056517120000 

noncomputable def Ns384p207 := nat_lit 1007638437584442388768561823744 

noncomputable abbrev qz716 := (Enclosure.sfrac Bool.false 729786 1000)

noncomputable abbrev qz595 := qz716

noncomputable abbrev qz385 := qz595

noncomputable abbrev qz33 := qz385

noncomputable abbrev qz717 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 729786 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz596 := qz717

noncomputable abbrev qz386 := qz596

noncomputable abbrev qz34 := (@HPow.hPow Real Real Real qz350 qz386 qz352)

noncomputable abbrev qz718 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 729786 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz597 := qz718

noncomputable abbrev qz387 := qz597

noncomputable abbrev qz35 := qz387

noncomputable def Ns384p208 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz34) (Zeta.RiemannSiegel.correction qz35)) 117504023 67108864 152109 134217728 1522238285104116881123 9444732965739290427392 216469669896573853453 Ns384p206 Ns384p207 

noncomputable def Ns384p209 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.sin BSN.quadSignNeg 9 10 729786 1000 197 268435456 134217728 4503599627370496 Bool.false 367685350432 2535 618095470 48 84886744 8 

noncomputable def Ns384p210 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 729786 1000 94 148 268435456 134217728 4503599627370496 Bool.false 367685350432 2535 

noncomputable def Ns384p211 := Ns384p210 558195838 48 94906264 8 589812974 48 89478488 8 Bool.false 383545932 114398 Bool.true 42359141 Bool.true 346601228 14148475504056880 1 Bool.false 265100247 Bool.true Bool.false 74082038 Bool.false Bool.false 314512855 

noncomputable def Ns384p212 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 729786 1000 39 32 268435456 134217728 4503599627370496 Bool.false 367685350432 2535 

noncomputable def Ns384p213 := Ns384p212 480971758 48 109588312 8 522351262 48 101459064 8 Bool.false 198621753 84844 Bool.false 234255345 Bool.true 26249953 14148475504056880 1 Bool.false 205634272 Bool.false Bool.false 267153004 Bool.false Bool.false 383545932 

noncomputable def Ns384p214 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 729786 1000 227 124 268435456 134217728 4503599627370496 Bool.false 367685350432 2535 

noncomputable def Ns384p215 := Ns384p214 372130544 47 134217720 8 432030192 47 120047984 16 Bool.true 44921276 49925 Bool.false 393453031 Bool.false 110243628 14148475504056880 1 Bool.false 266955106 Bool.false Bool.false 246113908 Bool.false Bool.false 198621753 

noncomputable def Ns384p216 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 729786 1000 549 361 268435456 134217728 4503599627370496 Bool.false 367685350432 2535 

noncomputable def Ns384p217 := Ns384p216 186065264 47 189812528 16 294906480 47 154981288 8 Bool.false 268435440 2583 Bool.false 407597560 Bool.false 248398414 14148475504056880 1 Bool.false 268067332 Bool.true Bool.false 214435660 Bool.true Bool.true 44921276 

noncomputable def Ns384p218 := nat_lit 232975369573000290145765546772356610571818909688850835 

noncomputable def Ns384p219 := nat_lit 170087955624249023700747691968557536450397983473664 

noncomputable def Ns384p220 := nat_lit 99361786744367654701118710164480000 

noncomputable def Ns384p221 := nat_lit 435077140712747113101025100751547207680 

noncomputable abbrev qz598 := (@Eq.refl Real qz716)

noncomputable abbrev qz388 := qz598

noncomputable abbrev qz36 := qz388

noncomputable def Ns384p222 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz33 729786 1000 2130351423184 16000000 1459572 4000 2000 Ns384p220 Ns384p221 qz36 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns384p223 := nat_lit 42942020119695413479667505581080770460597661433848985907200 

noncomputable abbrev qz599 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1459572))))

noncomputable abbrev qz389 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 729786 4000) (Real.log (Enclosure.sfrac Bool.false 2130351423184 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz599))

noncomputable abbrev qz600 := (Enclosure.sfrac Bool.false 729786 2000)

noncomputable abbrev qz37 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz389 qz600) (@HMul.hMul Real Real Real qz349 qz600 (Real.log Real.pi)))

noncomputable def Ns384p224 := @Enclosure.Real.IsNear.addLit_ft_p qz37 (Enclosure.sfrac Bool.true Ns384p220 Ns384p221) 98699801164268725415 72057594037927936 173999512883710721 18432000000000000000000 Ns384p220 Ns384p221 0 1 Ns384p223 

noncomputable def Ns384p225 := nat_lit 413976970822496972083036160000000 

noncomputable abbrev qz38 := (@HSub.hSub Real Real Real qz355 qz389 qz600)

noncomputable def Ns384p226 := @Enclosure.Real.IsNear.subLit_ff_p qz38 (@HMul.hMul Real Real Real qz5 qz600 (Real.log Real.pi)) 16099817591532981921163 9007199254740992000 72049469893379 18000000000000000000 14015817813573 33554432000 364893 67108864000 Ns384p225 98699801164268725415 72057594037927936 

noncomputable def Ns384p227 := nat_lit 32199635183065963842326000 

noncomputable abbrev qz39 := qz389

noncomputable def Ns384p228 := @Enclosure.Real.IsNear.subLit_ff_p qz39 qz600 19386481549193186715019 9007199254740992000 72049469893379 18000000000000000000 729786 2000 0 1 Ns384p227 16099817591532981921163 9007199254740992000 72049469893379 18000000000000000000 

noncomputable def Ns384p229 := nat_lit 43654475540485715854375401301540339712 

noncomputable def Ns384p230 := nat_lit 57057472616867691696750592 

noncomputable def Ns384p231 := nat_lit 53615355579097314566093568 

noncomputable def Ns384p232 := BSN.log_dyadic_bound 33199423184 4227503423184 2 1 Ns384p231 134217728 46080000 1102201699750316697856 1102201699750316697856 2108120 4260702846368 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 33199423184) (BSN.artanhQ 4227503423184) 0 1 1102201699750316697856 Ns384p231 1102201699750316697856 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz390 := (Real.log (Enclosure.sfrac Bool.false 2130351423184 16000000))

noncomputable def Ns384p233 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 729786 4000) qz390 729786 4000 0 1 53138912298593383 4503599627370496 195312653 9000000000000000 19390017125370635303019 9007199254740992000 23756073297043 6000000000000000000 (Enclosure.Real.IsNear.const Bool.false 729786 4000) (BSN.isNear_log_sfrac 2130351423184 16000000 53138912298593383 4503599627370496 195312653 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2130351423184) qz358)) Bool.false Ns384p230 Ns384p98 1000000783360000 46080000000000000000000 53138912298593383 4503599627370496 195312653 9000000000000000 (BSN.log_rat_reduce_isNear 2130351423184 16000000 17 4260702846368 4194304000000 2108120 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns384p232 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns384p234 := BSN.arctan_dyadic_bound_f 1000 1459572 1 0 16777216 5760000 0 1 1 0 1 1 11494 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1459572) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1459572) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz391 := (@Nat.cast Real Real.instNatCast 1459572)

noncomputable def Ns384p235 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz391)) 884279719003555 562949953421312 1 2000000000000000 11494 16777216 1 5760000 14829281303377322442752 883894044362147 562949953421312 3125000009 18000000000000000 qz15 (Ns384p234 rfl) rfl rfl 

noncomputable abbrev qz392 := (@HMul.hMul Real Real Real qz579 qz584 qz599)

noncomputable abbrev qz40 := qz392

noncomputable abbrev qz393 := qz599

noncomputable abbrev qz41 := qz393

noncomputable def Ns384p236 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 729786 4000) qz390) qz40 19390017125370635303019 9007199254740992000 23756073297043 6000000000000000000 883894044362147 2251799813685248 3125000009 72000000000000000 Ns384p229 19386481549193186715019 9007199254740992000 72049469893379 18000000000000000000 (Ns384p233 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz41 1 4 0 1 883894044362147 562949953421312 3125000009 18000000000000000 883894044362147 2251799813685248 3125000009 72000000000000000 qz366 Ns384p235 rfl) 

noncomputable def Ns384p237 := @Ns384p224 Ns384p218 Ns384p219 173999512883710721 18432000000000000000000 (@Ns384p226 173999512883710721 18432000000000000000000 (Ns384p228 (Ns384p236 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 729786 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz600 (Real.log Real.pi) 729786 2000 0 1 38410761 33554432 1 67108864 14015817813573 33554432000 364893 67108864000 (Enclosure.Real.IsNear.const Bool.false 729786 2000) RS385to396.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns384p220 Ns384p221) 

noncomputable def Ns384p238 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz33) Bool.false Ns384p218 Ns384p219 173999512883710721 18432000000000000000000 11490167201 8388608 317 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz33) (@HAdd.hAdd Real Real Real qz367 qz37 (Enclosure.sfrac Bool.true Ns384p220 Ns384p221)) Bool.false Ns384p218 Ns384p219 173999512883710721 18432000000000000000000 Ns384p222 (Ns384p237 rfl rfl)) 

noncomputable def Ns384p239 := nat_lit 1208925819614629174706176 

noncomputable def Ns384p240 := BSN.cos_dyadic_bound_f 18683846 68719476736 1 0 33554432 11531251 0 1 1 0 1 1 33554430 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 18683846) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 18683846) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable abbrev qz394 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable def Ns384p241 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz33) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11490167201) qz394) Bool.false 11490167201 8388608 317 33554432 Bool.false 33554430 33554432 1 5760000 (Ns384p238 rfl) (Enclosure.sfrac_false_div 11490167201 8388608) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11490167201) qz394) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 328689701883784200192) (@Nat.cast Real Real.instNatCast Ns384p239)) 226375608064910080 72057594037927936 Bool.false 33554430 33554432 218 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q0 11490167201 8388608 226375608064910080 72057594037927936 218 328689701883784200192 Ns384p239 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554430 33554432 328689701883784200192 Ns384p239 18683846 68719476736 11531251 11520000 (Ns384p240 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p242 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz33) Bool.false Ns384p218 Ns384p219 173999512883710721 18432000000000000000000 367685350432 268435456 2535 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz33) (@HAdd.hAdd Real Real Real qz367 qz37 (Enclosure.sfrac Bool.true Ns384p220 Ns384p221)) Bool.false Ns384p218 Ns384p219 173999512883710721 18432000000000000000000 Ns384p222 (Ns384p237 rfl rfl)) 

noncomputable def Ns384p243 := Ns384p217 49925 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 549 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268067332 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 361 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 214435660 268435456) qz36 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 1) Bool.false 16777215 16777216 1815893 188743680000 268435440 268435456 2583 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz33)) Bool.false 16777215 16777216 1815893 188743680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz33) qz33) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz33)) Bool.false 33554430 33554432 1859474432 193273528320000 16777215 16777216 1815893 188743680000 (Ns384p241 rfl rfl) rfl)) rfl) (Ns384p242 rfl) RS385to396.d7 

noncomputable def Ns384p244 := nat_lit 38681864313485102572371502572301860217853080406546232084586698543535335271235862159516295312215210616422400000 

noncomputable def Ns384p245 := nat_lit 21027077060472696232142287997263327768368307750795501147199272016557517018727191940312334336000000000000 

noncomputable def Ns384p246 := nat_lit 193199432555717653247339173341225220016776892558762370865834943461771421930335213837697638843681563738112000000 

noncomputable def Ns384p247 := BSN.sin_dyadic_bound_f 407597560 268435456 4 3 268435456 134217728 Ns384p244 Ns384p156 Ns384p245 Ns384p246 Ns384p159 Ns384p245 268067332 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 407597560) qz372 0 3 Ns384p244 Ns384p156 Ns384p245 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 407597560) qz373 0 3 Ns384p246 Ns384p159 Ns384p245 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p248 := nat_lit 59791832678041510409440393335036039614886245489594261389647344102129920 

noncomputable def Ns384p249 := nat_lit 14494076482526808998893414745318920505539613121721960403247608217856 

noncomputable def Ns384p250 := nat_lit 156574190413898912429202821777411492167693102622930753798899690806558976 

noncomputable def Ns384p251 := BSN.sin_dyadic_bound_f 248398414 268435456 3 2 268435456 134217728 Ns384p248 Ns384p131 Ns384p249 Ns384p250 Ns384p134 Ns384p249 214435660 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 248398414) qz372 0 2 Ns384p248 Ns384p131 Ns384p249 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 248398414) qz373 0 2 Ns384p250 Ns384p134 Ns384p249 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p252 := nat_lit 33577797207989092469541529195109968024967211125987961441895532345755989213337782159926552383873155300705977761 

noncomputable def Ns384p253 := nat_lit 13763051767746602679410395576870331113859605371486267892416385972466232860914742725245370637490439865761 

noncomputable def Ns384p254 := nat_lit 167730767515006610941664786679982626991834426471557450554938418030400899052780020001629056952946512911580284321 

noncomputable def Ns384p255 := BSN.sin_dyadic_bound_f 393453031 268435456 4 3 268435456 134217728 Ns384p252 Ns384p156 Ns384p253 Ns384p254 Ns384p159 Ns384p253 266955106 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 393453031) qz372 0 3 Ns384p252 Ns384p156 Ns384p253 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 393453031) qz373 0 3 Ns384p254 Ns384p159 Ns384p253 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p256 := nat_lit 1288516956151504469828336890951455229307905729619748411216788015087616 

noncomputable def Ns384p257 := nat_lit 21818655025911421408084908961144170030755713862242292153345703936 

noncomputable def Ns384p258 := nat_lit 3865507231144461586642194503036443399583655677431520749066057353854976 

noncomputable def Ns384p259 := BSN.cos_dyadic_bound_f 110243628 268435456 3 2 268435456 134217728 Ns384p256 Ns384p117 Ns384p257 Ns384p258 Ns384p120 Ns384p257 246113908 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 110243628) qz370 0 2 Ns384p256 Ns384p117 Ns384p257 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 110243628) qz371 0 2 Ns384p258 Ns384p120 Ns384p257 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p260 := Ns384p215 84844 BSN.abs_quadSignPos (BSN.cos_quad_nat3 227 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266955106 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 124 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 246113908 268435456) qz36 rfl rfl (Ns384p243 RS385to396.d9 RS385to396.d11 RS385to396.d13 RS385to396.d17 (Ns384p247 rfl rfl) (Ns384p251 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns384p242 rfl) RS385to396.d19 RS385to396.d21 RS385to396.d23 RS385to396.d25 RS385to396.d17 (Ns384p255 rfl rfl) (Ns384p259 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns384p261 := nat_lit 47291448969203960312148443736620372239280341522456088156517450637130625 

noncomputable def Ns384p262 := nat_lit 9068095217664371720099366716322167105807019853508026023570562890625 

noncomputable def Ns384p263 := nat_lit 123843875146134153739508620335512643784705778336193598843983732662090625 

noncomputable def Ns384p264 := BSN.sin_dyadic_bound_f 234255345 268435456 3 2 268435456 134217728 Ns384p261 Ns384p131 Ns384p262 Ns384p263 Ns384p134 Ns384p262 205634272 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 234255345) qz372 0 2 Ns384p261 Ns384p131 Ns384p262 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 234255345) qz373 0 2 Ns384p263 Ns384p134 Ns384p262 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p265 := nat_lit 474803728391945323473589879681 

noncomputable def Ns384p266 := nat_lit 124615124604835863084731911901282304 

noncomputable def Ns384p267 := nat_lit 1869226869072537946270978678519234560 

noncomputable def Ns384p268 := BSN.cos_dyadic_bound_f 26249953 268435456 2 1 268435456 134217728 Ns384p265 Ns384p266 Ns384p265 Ns384p265 Ns384p267 Ns384p265 267153004 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 26249953) qz370 0 1 Ns384p265 Ns384p266 Ns384p265 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 26249953) qz371 0 1 Ns384p265 Ns384p267 Ns384p265 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p269 := Ns384p213 114398 BSN.abs_quadSignPos (BSN.cos_quad_nat3 39 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 205634272 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 267153004 268435456) qz36 rfl rfl (Ns384p260 rfl rfl) (Ns384p242 rfl) RS385to396.d27 RS385to396.d29 RS385to396.d31 RS385to396.d33 RS385to396.d17 (Ns384p264 rfl rfl) (Ns384p268 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p270 := nat_lit 3219501100719104395637914610161 

noncomputable def Ns384p271 := BSN.cos_dyadic_bound_f 42359141 268435456 2 1 268435456 134217728 Ns384p270 Ns384p266 Ns384p270 Ns384p270 Ns384p267 Ns384p270 265100247 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 42359141) qz370 0 1 Ns384p270 Ns384p266 Ns384p270 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 42359141) qz371 0 1 Ns384p270 Ns384p267 Ns384p270 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p272 := nat_lit 7778273837815816710071009451157659118053473578394332966538634341882472893807204821708134730118769378271952896 

noncomputable def Ns384p273 := nat_lit 3005807507992684693511283922251424646202472844065092771948095633019116251195815290343082875527643529216 

noncomputable def Ns384p274 := nat_lit 47136218613352881697585786840839851376320941523359017510205925198092240296672797183047104557407774819294904320 

noncomputable def Ns384p275 := BSN.cos_dyadic_bound_f 346601228 268435456 4 3 268435456 134217728 Ns384p272 Ns384p149 Ns384p273 Ns384p274 Ns384p152 Ns384p273 74082038 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 346601228) qz370 0 3 Ns384p272 Ns384p149 Ns384p273 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 346601228) qz371 0 3 Ns384p274 Ns384p152 Ns384p273 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p276 := Ns384p211 140220 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 94 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 265100247 268435456) BSN.abs_quadSignPos qz590 (BSN.sfrac_eq_quadSignPos_mul Bool.false 74082038 268435456) qz36 rfl rfl (Ns384p269 rfl) (Ns384p242 rfl) RS385to396.d35 RS385to396.d37 RS385to396.d39 RS385to396.d41 RS385to396.d17 (Ns384p271 rfl rfl) (Ns384p275 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p277 := nat_lit 15726648516668369375871004070497765337515441389125873386256215410209731209945680770291673222013099144564965376 

noncomputable def Ns384p278 := nat_lit 1417497627605773383574813934610918694063767145758117473892743219846571182010935311275058774091891736576 

noncomputable def Ns384p279 := nat_lit 78598485063787893297889107637389928991069271183249830034061828867799907768386454139901796869377742807274356736 

noncomputable def Ns384p280 := BSN.sin_dyadic_bound_f 325556868 268435456 4 3 268435456 134217728 Ns384p277 Ns384p156 Ns384p278 Ns384p279 Ns384p159 Ns384p278 251416280 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 325556868) qz372 0 3 Ns384p277 Ns384p156 Ns384p278 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 325556868) qz373 0 3 Ns384p279 Ns384p159 Ns384p278 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p281 := Ns384p209 Bool.false 314512855 140220 Bool.true 325556868 14148475504056880 1 Bool.false 251416280 Bool.true Bool.false 235008046 152109 BSN.abs_quadSignNeg qz374 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 251416280 268435456) qz36 rfl (Ns384p276 rfl) (Ns384p242 rfl) RS385to396.d43 RS385to396.d45 RS385to396.d17 (Ns384p280 rfl rfl) rfl 

noncomputable def Ns384p282 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) 235008046 268435456 152109 268435456 235008046 268435456 152109 268435456 126168983983357952 117504023 67108864 152109 134217728 (Ns384p281 rfl rfl rfl rfl) 

noncomputable def Ns384p283 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz34) (Zeta.RiemannSiegel.correction qz35) 10221061 33554432 1 33554432 148931533145543 281474976710656 21169677640969 175921860444160000 1522238285104116881123 9444732965739290427392 

noncomputable def Ns384p284 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz34 1 1 0 1 10221061 33554432 1 33554432 10221061 33554432 1 33554432 

noncomputable abbrev qz42 := qz386

noncomputable def Ns384p285 := @Enclosure.Real.IsNear.sqrt_image qz42 1948657427229 16777216000 364893 16777216000 180812168 180812203 16777216 (@Enclosure.Real.IsNear.of_eq qz42 (@HMul.hMul Real Real Real qz5 qz33 qz3) Bool.false 1948657427229 16777216000 364893 16777216000 (BSN.t_div_two_pi_mk qz33 729786 1000 qz36) (@Enclosure.Real.IsNear.mulLit_ff qz33 qz3 729786 1000 0 1 5340353 33554432 1 33554432 1948657427229 16777216000 364893 16777216000 (Enclosure.Real.IsNear.const Bool.false 729786 1000) RS385to396.d48 rfl)) 

noncomputable abbrev qz719 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 729786 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz601 := qz719

noncomputable abbrev qz395 := qz601

noncomputable abbrev qz43 := qz395

noncomputable def Ns384p286 := @Enclosure.Real.IsNear.sqrt_image qz43 361624371 33554432 35 33554432 55077443 55077449 16777216 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 361624371 33554432 35 33554432 361624371 33554432 35 33554432 (Ns384p285 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns384p287 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz43) 27538723 8388608 3 16777216 5110530 5110531 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz43) Bool.false 110154892 33554432 6 33554432 27538723 8388608 3 16777216 (Ns384p286 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns384p288 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz43)) Bool.false 10221061 33554432 1 33554432 10221061 33554432 1 33554432 (Ns384p287 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz44 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz387))

noncomputable abbrev qz602 := (@HMul.hMul Real Real Real qz707 qz718 qz718)

noncomputable abbrev qz396 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz602 qz597) qz594)

noncomputable abbrev qz45 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz396))

noncomputable def Ns384p289 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz35) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz44) qz45) Bool.false 148931533145543 

noncomputable def Ns384p290 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz44) qz45 98482561 16777216 977 

noncomputable def Ns384p291 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz44) Bool.false 196965122 33554432 7816 33554432 98482561 16777216 977 

noncomputable def Ns384p292 := @Enclosure.Real.IsNear.recentre' qz44 Bool.false 5716240 33554432 1306514432 193273528320000 357265 2097152 1275893 188743680000 

noncomputable abbrev qz46 := (@HMul.hMul Real Real Real qz349 qz346 qz387)

noncomputable def Ns384p293 := @Enclosure.Real.IsNear.cos_image qz46 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 163865793) qz378) Bool.false 163865793 33554432 221 33554432 Bool.false 5716240 33554432 1 

noncomputable def Ns384p294 := nat_lit 944512639540567523176938037 

noncomputable def Ns384p295 := nat_lit 144115188075855872000000000000000 

noncomputable def Ns384p296 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz35 884279719003555 140737488355328 1 500000000000000 26080051 33554432 35 33554432 23062060169878383581305 4722366482869645213696 Ns384p294 

noncomputable def Ns384p297 := @Enclosure.Real.IsNear.subLit_ff_p qz43 qz1 361624371 33554432 35 33554432 10 1 0 1 26080051 26080051 33554432 35 

noncomputable def Ns384p298 := @Ns384p297 33554432 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 361624371 33554432 35 33554432 361624371 33554432 35 33554432 (Ns384p285 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns384p299 := @Enclosure.Real.IsNear.recentre' qz46 Bool.false 23062060169878383581305 4722366482869645213696 Ns384p294 Ns384p295 163865793 33554432 221 33554432 (@Ns384p296 Ns384p295 RS385to396.d47 (Ns384p298 rfl rfl) rfl) 

noncomputable def Ns384p300 := nat_lit 19153818984789405200928207665794751700625 

noncomputable def Ns384p301 := BSN.sin_dyadic_bound_f 11764239155 68719476736 2 1 33554432 11531251 Ns384p300 Ns384p181 Ns384p300 Ns384p300 Ns384p182 Ns384p300 5716240 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 11764239155) qz368 0 1 Ns384p300 Ns384p181 Ns384p300 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 11764239155) qz369 0 1 Ns384p300 Ns384p182 Ns384p300 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p302 := @Ns384p293 5760000 (Ns384p299 rfl) (Enclosure.sfrac_false_div 163865793 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 163865793) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 827834735576236022562816) qz380) 226375608064910080 72057594037927936 Bool.false 5716240 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 163865793 33554432 226375608064910080 72057594037927936 0 827834735576236022562816 Ns384p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 5716240 33554432 827834735576236022562816 Ns384p98 11764239155 68719476736 11531251 11520000 (Ns384p301 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p303 := @Enclosure.Real.IsNear.inv_image qz44 357265 2097152 1275893 188743680000 98478653 98486469 16777216 (Ns384p292 (Ns384p302 rfl rfl) rfl) rfl 

noncomputable def Ns384p304 := @Enclosure.Real.IsNear.recentre' qz45 Bool.false 1512263 16777216 

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz349 qz346 qz396)

noncomputable def Ns384p305 := @Enclosure.Real.IsNear.cos_image qz47 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 49678541)) qz378) Bool.true 49678541 33554432 

noncomputable def Ns384p306 := nat_lit 234600277682653531432785642725 

noncomputable def Ns384p307 := nat_lit 158456325028528675187087900672 

noncomputable def Ns384p308 := nat_lit 16191698759269747023702374826777209 

noncomputable def Ns384p309 := @Enclosure.Real.IsNear.recentre' qz47 Bool.true Ns384p306 Ns384p307 Ns384p308 

noncomputable def Ns384p310 := nat_lit 967140655691703339764940800000000000000 

noncomputable abbrev qz48 := qz396

noncomputable def Ns384p311 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz48 884279719003555 140737488355328 1 500000000000000 265300981851095 

noncomputable abbrev qz397 := (@HSub.hSub Real Real Real qz583 qz602 qz597)

noncomputable abbrev qz49 := qz397

noncomputable def Ns384p312 := @Enclosure.Real.IsNear.subLit_tf qz49 qz29 194932237673431 1125899906842624 3000009915 1125899906842624 1 16 

noncomputable abbrev qz398 := qz602

noncomputable abbrev qz50 := qz398

noncomputable def Ns384p313 := @Enclosure.Real.IsNear.subLit_ff_n qz50 qz35 680169060162601 1125899906842624 1825604795 1125899906842624 26080051 33554432 35 33554432 

noncomputable def Ns384p314 := @Enclosure.Real.IsNear.mulLit_ff qz35 qz35 26080051 33554432 35 33554432 26080051 33554432 35 33554432 680169060162601 1125899906842624 

noncomputable def Ns384p315 := nat_lit 195902959695853366996606489789977828322905484830211952675404095756913734919905421492597537045302961 

noncomputable def Ns384p316 := nat_lit 975743491921780970500323514261193594148711042915413329552712293065467609596717903600577236539801600 

noncomputable def Ns384p317 := nat_lit 225957099713303308296636409339149960203325235391690927788637763606980343178175623550789308081 

noncomputable def Ns384p318 := nat_lit 1186217241979426289481808903515648524879988523581780884039806095191559190303805270655369760704122545 

noncomputable def Ns384p319 := nat_lit 88792657764882068315529439797768617067532704905302612989296818668957552473301329227652528525121945600 

noncomputable def Ns384p320 := BSN.cos_dyadic_bound_f 49678541 33554432 4 3 16777216 5760000 Ns384p315 Ns384p316 Ns384p317 Ns384p318 Ns384p319 Ns384p317 1512263 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 49678541) (BSN.cosEvenQ 33554432) 0 3 Ns384p315 Ns384p316 Ns384p317 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 49678541) (BSN.cosOddQ 33554432) 0 3 Ns384p318 Ns384p319 Ns384p317 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p321 := @Ns384p304 1635337216 96636764160000 1512263 16777216 1597009 94371840000 (@Ns384p305 281 16777216 Bool.false 1512263 16777216 1 5760000 (@Ns384p309 Ns384p310 49678541 33554432 281 16777216 (@Ns384p311 1125899906842624 3000009915 1125899906842624 Ns384p306 Ns384p307 Ns384p308 Ns384p310 RS385to396.d47 (@Ns384p312 0 1 4244815709617520 265300981851095 1125899906842624 3000009915 1125899906842624 (@Ns384p313 6540840513620978696192 194932237673431 1125899906842624 3000009915 1125899906842624 (@Ns384p314 1825604795 1125899906842624 (Ns384p298 rfl rfl) (Ns384p298 rfl rfl) rfl) (Ns384p298 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 49678541 33554432) (BSN.cos_neg_of_bound 49678541 33554432 Bool.false 1512263 16777216 1 5760000 (Ns384p320 rfl rfl)) rfl rfl) 

noncomputable def Ns384p322 := @Ns384p283 216469669896573853453 Ns384p206 (Ns384p284 qz31 (@Enclosure.Real.IsNear.of_eq qz34 (@Inv.inv Real Real.instInv (Real.sqrt qz43)) Bool.false 10221061 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz42 (BSN.t_div_two_pi_nonneg qz33 729786 1000 qz36)) Ns384p288) rfl) (@Ns384p289 281474976710656 21169677640969 175921860444160000 (BSN.correction_mk qz35 (BSN.cos_two_pi_p_ne_zero_mk qz33 729786 1000 10 qz36 rfl rfl (@BSN.floor_sqrt_eq_dec qz33 729786 1000 10 qz36 rfl rfl rfl))) (@Ns384p290 4194304 1512263 16777216 1597009 94371840000 148931533145543 281474976710656 21169677640969 175921860444160000 (@Ns384p291 4194304 (Ns384p303 rfl rfl rfl rfl rfl) rfl) (Ns384p321 rfl) rfl)) 

noncomputable def Ns384p323 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz33) (hardyZApproximantRS₀ qz33) Bool.false 15014982783562576603421 9444732965739290427392 6906294237471757213453 Ns384p206 (@Eq.refl Real (hardyZApproximantRS₀ qz33)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz33) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz34) (Zeta.RiemannSiegel.correction qz35))) Bool.false 15014982783562576603421 9444732965739290427392 6906294237471757213453 Ns384p206 (BSN.hardyZApproximantRS₀_eq qz33 10 (@BSN.floor_sqrt_eq_dec qz33 729786 1000 10 qz36 rfl rfl rfl)) (@Ns384p208 15014982783562576603421 9444732965739290427392 6906294237471757213453 Ns384p206 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 10)) Bool.false 117504023 67108864 152109 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (Ns384p282 (Ns384p281 rfl rfl rfl rfl) rfl rfl)) (Ns384p322 rfl) rfl rfl)) 

theorem RS385to396.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz33) Bool.false 15014982783562576603421 9444732965739290427392 6906294237471757213453 Ns384p206 := Ns384p323 

noncomputable abbrev qz603 := (@HMul.hMul Real Real Real qz707 (Real.sqrt qz715) qz709)

noncomputable abbrev qz399 := qz603

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv qz399)

noncomputable abbrev qz400 := (@HMul.hMul Real Real Real qz579 (@HMul.hMul Real Real Real qz579 qz603 qz603) qz603)

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz400))

noncomputable abbrev qz401 := (@HMul.hMul Real Real Real qz579 qz592 qz592)

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz349 qz401 qz376))

noncomputable abbrev qz604 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz51)

noncomputable def Ns384p324 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz367 (@HAdd.hAdd Real Real Real qz367 qz604 qz52) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz53)) Bool.false 

noncomputable def Ns384p325 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz367 qz604 qz52) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz53) 17639801 1073741824 

noncomputable def Ns384p326 := @Enclosure.Real.IsNear.addLit_ff qz604 qz52 2204975 134217728 25 134217728 

noncomputable def Ns384p327 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz51 25 4 0 1 88199 33554432 1 33554432 2204975 

noncomputable def Ns384p328 := @Enclosure.Real.IsNear.recentre' qz51 Bool.false 88199 33554432 1 33554432 88199 33554432 1 33554432 

noncomputable def Ns384p329 := @Enclosure.Real.IsNear.mulLit_ff qz22 qz19 27526243 8388608 3 16777216 243140931737 2097152000 45529 2097152000 6692756370239074091 17592186044416000 808976891723 

noncomputable def Ns384p330 := @Enclosure.Real.IsNear.sqrt_image qz19 243140931737 2097152000 45529 2097152000 180648325 180648359 16777216 qz20 

noncomputable def Ns384p331 := @Enclosure.Real.IsNear.sqrt_image qz21 90324171 8388608 17 16777216 55052483 55052489 16777216 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 361296684 33554432 34 33554432 90324171 8388608 17 16777216 (Ns384p330 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz402 := (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 110104972 33554432 6 33554432 27526243 8388608 3 16777216 (Ns384p331 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns384p332 := @Ns384p329 8796093022208000 qz402 

noncomputable def Ns384p333 := Ns384p332 qz20 

noncomputable abbrev qz54 := qz399

noncomputable def Ns384p334 := @Enclosure.Real.IsNear.inv_image qz54 6692756370239074091 17592186044416000 808976891723 8796093022208000 44099 44100 16777216 (Ns384p333 rfl) rfl rfl 

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv qz400)

noncomputable def Ns384p335 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz55 1 32 0 1 1 

noncomputable def Ns384p336 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 1 33554432 1 33554432 

noncomputable def Ns384p337 := nat_lit 299788554650481086321632875709268959029052374124264135571 

noncomputable def Ns384p338 := nat_lit 5444517870735015415413993718908291383296000000000 

noncomputable def Ns384p339 := nat_lit 108709502480629454087959957832903706382096085208791 

noncomputable def Ns384p340 := nat_lit 2722258935367507707706996859454145691648000000000 

noncomputable abbrev qz56 := qz400

noncomputable def Ns384p341 := @Enclosure.Real.IsNear.inv_image qz56 Ns384p337 Ns384p338 Ns384p339 Ns384p340 0 1 

noncomputable def Ns384p342 := nat_lit 44792987831375706190941575760987476281 

noncomputable def Ns384p343 := nat_lit 309485009821345068724781056000000 

noncomputable def Ns384p344 := nat_lit 2707142949949462641172573778761 

noncomputable def Ns384p345 := nat_lit 38685626227668133590597632000000 

noncomputable abbrev qz403 := (@HMul.hMul Real Real Real qz579 qz603 qz603)

noncomputable abbrev qz57 := qz403

noncomputable def Ns384p346 := @Enclosure.Real.IsNear.mulLit_ff qz57 qz54 Ns384p342 Ns384p343 Ns384p344 Ns384p345 6692756370239074091 17592186044416000 808976891723 

noncomputable def Ns384p347 := @Enclosure.Real.IsNear.mulLit_ff qz54 qz54 6692756370239074091 17592186044416000 808976891723 8796093022208000 6692756370239074091 17592186044416000 808976891723 8796093022208000 Ns384p342 

noncomputable def Ns384p348 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz53 13 10 0 1 949683 33554432 1 

noncomputable def Ns384p349 := @Enclosure.Real.IsNear.recentre' qz53 Bool.false 949683 33554432 1 33554432 949683 33554432 

noncomputable abbrev qz58 := qz401

noncomputable def Ns384p350 := @Enclosure.Real.IsNear.mulLit_ff qz58 qz22 757694053695049 70368744177664 330314925 281474976710656 27526243 8388608 3 16777216 20856470641664966670907 

noncomputable def Ns384p351 := @Enclosure.Real.IsNear.mulLit_ff qz22 qz22 27526243 8388608 3 16777216 27526243 8388608 3 16777216 757694053695049 70368744177664 330314925 

noncomputable def Ns384p352 := @Ns384p351 281474976710656 qz402 

noncomputable def Ns384p353 := Ns384p352 qz402 

noncomputable def Ns384p354 := @Ns384p350 590295810358705651712 27276987419438913 4722366482869645213696 (Ns384p353 rfl) qz402 

noncomputable abbrev qz59 := (@HMul.hMul Real Real Real qz349 qz401 qz376)

noncomputable def Ns384p355 := @Enclosure.Real.IsNear.inv_image qz59 20856470641664966670907 590295810358705651712 27276987419438913 4722366482869645213696 474841 474842 16777216 (Ns384p354 rfl) 

noncomputable def Ns384p356 := @Ns384p325 201 1073741824 12345879 335544320 13 335544320 19175221667823616 285733069 5368709120 1213 5368709120 (@Ns384p326 1 1073741824 1 1073741824 2367574012592128 17639801 1073741824 201 1073741824 (@Ns384p327 134217728 25 134217728 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns384p328 (Ns384p334 rfl rfl rfl rfl) rfl) rfl) (@Ns384p335 33554432 1 33554432 1 1073741824 1 1073741824 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns384p336 1 33554432 1 33554432 (@Ns384p341 16777216 (@Ns384p346 8796093022208000 Ns384p337 Ns384p338 Ns384p339 Ns384p340 (@Ns384p347 Ns384p343 Ns384p344 Ns384p345 (Ns384p333 rfl) (Ns384p333 rfl) rfl) (Ns384p333 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns384p348 33554432 12345879 335544320 13 335544320 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns384p349 1 33554432 (Ns384p355 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS385to396.d52 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 := @Ns384p324 285733069 5368709120 1213 5368709120 (BSN.hardyZErrorBoundRS₀_mk qz4 728464 1000 qz9 rfl rfl) (Ns384p356 rfl rfl) 

noncomputable def Ns384p357 := nat_lit 17708874310761169551360000 

noncomputable def Ns384p358 := nat_lit 1132948722451388480524476481536 

noncomputable abbrev qz720 := (Enclosure.sfrac Bool.false 731107 1000)

noncomputable abbrev qz605 := qz720

noncomputable abbrev qz404 := qz605

noncomputable abbrev qz60 := qz404

noncomputable abbrev qz721 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 731107 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz606 := qz721

noncomputable abbrev qz405 := qz606

noncomputable abbrev qz61 := (@HPow.hPow Real Real Real qz350 qz405 qz352)

noncomputable abbrev qz722 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 731107 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz607 := qz722

noncomputable abbrev qz406 := qz607

noncomputable abbrev qz62 := qz406

noncomputable def Ns384p359 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz61) (Zeta.RiemannSiegel.correction qz62)) 97869447 134217728 76193 67108864 1554175690053509028429 9444732965739290427392 485399865844940883929 Ns384p357 Ns384p358 

noncomputable def Ns384p360 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.sin BSN.quadSignNeg 9 10 731107 1000 197 268435456 134217728 4503599627370496 Bool.false 368528557756 2539 618095470 48 84886744 8 

noncomputable def Ns384p361 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 731107 1000 93 148 268435456 134217728 4503599627370496 Bool.false 368528557756 2539 

noncomputable def Ns384p362 := Ns384p361 558195838 48 94906264 8 589812974 48 89478488 8 Bool.false 26228581 114606 Bool.true 358185947 Bool.true 282536842 14148475504056880 1 Bool.false 260966445 Bool.true Bool.false 132975771 Bool.false Bool.true 21711731 

noncomputable def Ns384p363 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 731107 1000 40 31 268435456 134217728 4503599627370496 Bool.false 368528557756 2539 

noncomputable def Ns384p364 := Ns384p363 480971758 48 109588312 8 522351262 48 101459064 8 Bool.true 173368213 84999 Bool.false 20441549 Bool.true 294726074 14148475504056880 1 Bool.false 267657512 Bool.false Bool.false 238980340 Bool.false Bool.false 26228581 

noncomputable def Ns384p365 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 731107 1000 228 124 268435456 134217728 4503599627370496 Bool.false 368528557756 2539 

noncomputable def Ns384p366 := Ns384p365 372130544 47 134217720 8 432030192 47 120047984 16 Bool.true 238742459 50018 Bool.false 323418479 Bool.false 382739068 14148475504056880 1 Bool.false 96060681 Bool.false Bool.false 38782160 Bool.false Bool.true 173368213 

noncomputable def Ns384p367 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 731107 1000 551 362 268435456 134217728 4503599627370496 Bool.false 368528557756 2539 

noncomputable def Ns384p368 := Ns384p367 186065264 47 189812528 16 294906480 47 154981288 8 Bool.true 268435448 2591 Bool.false 161697814 Bool.false 280376850 14148475504056880 1 Bool.false 152094992 Bool.false Bool.false 134847788 Bool.true Bool.true 238742459 

noncomputable def Ns384p369 := nat_lit 33992241701278981298140345459996536446025878217972805557349 

noncomputable def Ns384p370 := nat_lit 24759880094789745805379672728146867415748185103007744000 

noncomputable def Ns384p371 := nat_lit 100264331461870440226235714707360000 

noncomputable def Ns384p372 := nat_lit 439823823491098867417642152733259085120 

noncomputable abbrev qz608 := (@Eq.refl Real qz720)

noncomputable abbrev qz407 := qz608

noncomputable abbrev qz63 := qz407

noncomputable def Ns384p373 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz60 731107 1000 2138070781796 16000000 1462214 4000 2000 Ns384p371 Ns384p372 qz63 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns384p374 := nat_lit 10877517344409274015404910547198891662728281029751297778351680 

noncomputable abbrev qz609 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1462214))))

noncomputable abbrev qz408 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 731107 4000) (Real.log (Enclosure.sfrac Bool.false 2138070781796 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz609))

noncomputable abbrev qz610 := (Enclosure.sfrac Bool.false 731107 2000)

noncomputable abbrev qz64 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz408 qz610) (@HMul.hMul Real Real Real qz349 qz610 (Real.log Real.pi)))

noncomputable def Ns384p375 := @Enclosure.Real.IsNear.addLit_ft_p qz64 (Enclosure.sfrac Bool.true Ns384p371 Ns384p372) 24731536969213392202389 18014398509481984000 38736227717857031 4096000000000000000000 Ns384p371 Ns384p372 0 1 Ns384p374 

noncomputable def Ns384p376 := nat_lit 1659705350977913724288783876096000 

noncomputable abbrev qz65 := (@HSub.hSub Real Real Real qz355 qz408 qz610)

noncomputable def Ns384p377 := @Enclosure.Real.IsNear.subLit_ff_p qz65 (@HMul.hMul Real Real Real qz5 qz610 (Real.log Real.pi)) 32269842441412850494101 18014398509481984000 16039660866819 4000000000000000000 28082376242427 67108864000 731107 134217728000 Ns384p376 24731536969213392202389 18014398509481984000 

noncomputable def Ns384p378 := nat_lit 12907936976565140197640400 

noncomputable abbrev qz66 := qz408

noncomputable def Ns384p379 := @Enclosure.Real.IsNear.subLit_ff_p qz66 qz610 7771013773389754586449 3602879701896396800 16039660866819 4000000000000000000 731107 2000 0 1 Ns384p378 32269842441412850494101 18014398509481984000 16039660866819 4000000000000000000 

noncomputable def Ns384p380 := nat_lit 17498767367064545400069533084892004352 

noncomputable def Ns384p381 := nat_lit 57074963192697314963619840 

noncomputable def Ns384p382 := nat_lit 53811336034331545886956848 

noncomputable def Ns384p383 := BSN.log_dyadic_bound 40918781796 4235222781796 2 1 Ns384p382 134217728 46080000 1674346703668660985616 1674346703668660985616 2593581 4276141563592 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 40918781796) (BSN.artanhQ 4235222781796) 0 1 1674346703668660985616 Ns384p382 1674346703668660985616 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz409 := (Real.log (Enclosure.sfrac Bool.false 2138070781796 16000000))

noncomputable def Ns384p384 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 731107 4000) qz409 731107 4000 0 1 53155201666706535 4503599627370496 195312653 9000000000000000 7772428004988162936849 3602879701896396800 142794447796871 36000000000000000000 (Enclosure.Real.IsNear.const Bool.false 731107 4000) (BSN.isNear_log_sfrac 2138070781796 16000000 53155201666706535 4503599627370496 195312653 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2138070781796) qz358)) Bool.false Ns384p381 Ns384p98 1000000783360000 46080000000000000000000 53155201666706535 4503599627370496 195312653 9000000000000000 (BSN.log_rat_reduce_isNear 2138070781796 16000000 17 4276141563592 4194304000000 2593581 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns384p383 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns384p385 := BSN.arctan_dyadic_bound_f 1000 1462214 1 0 16777216 5760000 0 1 1 0 1 1 11473 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1462214) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1462214) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz410 := (@Nat.cast Real Real.instNatCast 1462214)

noncomputable def Ns384p386 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz410)) 884279719003555 562949953421312 1 2000000000000000 11473 16777216 1 5760000 14829293125326344290304 883894749005219 562949953421312 3125000009 18000000000000000 qz15 (Ns384p385 rfl) rfl rfl 

noncomputable abbrev qz411 := (@HMul.hMul Real Real Real qz579 qz584 qz609)

noncomputable abbrev qz67 := qz411

noncomputable abbrev qz412 := qz609

noncomputable abbrev qz68 := qz412

noncomputable def Ns384p387 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 731107 4000) qz409) qz67 7772428004988162936849 3602879701896396800 142794447796871 36000000000000000000 883894749005219 2251799813685248 3125000009 72000000000000000 Ns384p380 7771013773389754586449 3602879701896396800 16039660866819 4000000000000000000 (Ns384p384 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz68 1 4 0 1 883894749005219 562949953421312 3125000009 18000000000000000 883894749005219 2251799813685248 3125000009 72000000000000000 qz366 Ns384p386 rfl) 

noncomputable def Ns384p388 := @Ns384p375 Ns384p369 Ns384p370 38736227717857031 4096000000000000000000 (@Ns384p377 38736227717857031 4096000000000000000000 (Ns384p379 (Ns384p387 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 731107 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz610 (Real.log Real.pi) 731107 2000 0 1 38410761 33554432 1 67108864 28082376242427 67108864000 731107 134217728000 (Enclosure.Real.IsNear.const Bool.false 731107 2000) RS385to396.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns384p371 Ns384p372) 

noncomputable def Ns384p389 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz60) Bool.false Ns384p369 Ns384p370 38736227717857031 4096000000000000000000 46066069719 33554432 159 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz60) (@HAdd.hAdd Real Real Real qz367 qz64 (Enclosure.sfrac Bool.true Ns384p371 Ns384p372)) Bool.false Ns384p369 Ns384p370 38736227717857031 4096000000000000000000 Ns384p373 (Ns384p388 rfl rfl)) 

noncomputable def Ns384p390 := nat_lit 7595282500127156588249088 

noncomputable def Ns384p391 := nat_lit 3509682531282986808211326796684939385924442849607558917897921552770746196577516090527896087694684454468185844523834326922781250679974400000 

noncomputable def Ns384p392 := nat_lit 2500170197882407808322590512402744244901344946470928990537313075058614430418088413979326364261697482770824793798794408881000000000000 

noncomputable def Ns384p393 := nat_lit 17526613723891056224051038479959668207758964359219641845189465894803146605341857521078915990200428130484908649174113737373044406455872000000 

noncomputable def Ns384p394 := BSN.sin_dyadic_bound_f 107935456130 68719476736 4 3 33554432 11531251 Ns384p391 Ns384p108 Ns384p392 Ns384p393 Ns384p111 Ns384p392 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107935456130) qz368 0 3 Ns384p391 Ns384p108 Ns384p392 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107935456130) qz369 0 3 Ns384p393 Ns384p111 Ns384p392 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p395 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz60) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46066069719) qz378) Bool.false 46066069719 33554432 159 16777216 Bool.true 33554431 33554432 1 5760000 (Ns384p389 rfl) (Enclosure.sfrac_false_div 46066069719 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46066069719) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns384p390) qz380) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 218 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q1 46066069719 33554432 226375608064910080 72057594037927936 218 Ns384p390 Ns384p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554431 33554432 Ns384p390 Ns384p98 107935456130 68719476736 11531251 11520000 (Ns384p394 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p396 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz60) Bool.false Ns384p369 Ns384p370 38736227717857031 4096000000000000000000 368528557756 268435456 2539 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz60) (@HAdd.hAdd Real Real Real qz367 qz64 (Enclosure.sfrac Bool.true Ns384p371 Ns384p372)) Bool.false Ns384p369 Ns384p370 38736227717857031 4096000000000000000000 Ns384p373 (Ns384p388 rfl rfl)) 

noncomputable def Ns384p397 := Ns384p368 50018 BSN.abs_quadSignPos (BSN.cos_quad_nat3 551 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 152094992 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 362 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 134847788 268435456) qz63 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 1) Bool.true 33554431 33554432 910759 94371840000 268435448 268435456 2591 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz60)) Bool.true 33554431 33554432 910759 94371840000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz60) qz60) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz60)) Bool.true 33554431 33554432 932617216 96636764160000 33554431 33554432 910759 94371840000 (Ns384p395 rfl rfl) rfl)) rfl) (Ns384p396 rfl) RS385to396.d7 

noncomputable def Ns384p398 := nat_lit 10734376016252441658581255935092389254334959205184077916055212463448320 

noncomputable def Ns384p399 := nat_lit 467340253282517226683785858568329541845889647223595197216539238656 

noncomputable def Ns384p400 := nat_lit 28113085301203461220774372748137623132571428382719937292682443959787776 

noncomputable def Ns384p401 := BSN.sin_dyadic_bound_f 161697814 268435456 3 2 268435456 134217728 Ns384p398 Ns384p131 Ns384p399 Ns384p400 Ns384p134 Ns384p399 152094992 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 161697814) qz372 0 2 Ns384p398 Ns384p131 Ns384p399 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 161697814) qz373 0 2 Ns384p400 Ns384p134 Ns384p399 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p402 := nat_lit 3327522118741689374637914803175823570407618948925496497279813927128994512870727819849547922050203240000000000 

noncomputable def Ns384p403 := nat_lit 235996643544190933193166759692004267491729047156895995480411682658908510117994453369140625000000000000 

noncomputable def Ns384p404 := nat_lit 20177438976255001419117376671173035922619240759013564999420985798384359979319260946162274316845399656000000000 

noncomputable def Ns384p405 := BSN.cos_dyadic_bound_f 280376850 268435456 4 3 268435456 134217728 Ns384p402 Ns384p149 Ns384p403 Ns384p404 Ns384p152 Ns384p403 134847788 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 280376850) qz370 0 3 Ns384p402 Ns384p149 Ns384p403 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 280376850) qz371 0 3 Ns384p404 Ns384p152 Ns384p403 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p406 := nat_lit 5894521411088199947691080927597370795897104542955500134141940867382723217805963237727831910431484116154544321 

noncomputable def Ns384p407 := nat_lit 1309718506365256895628357937346154645304333934607781782113579735442895617347404464014429943841970024641 

noncomputable def Ns384p408 := nat_lit 35730225546826982651040537791877302549681957832395504339345229488422766577090352462967516463198747054440804545 

noncomputable def Ns384p409 := BSN.cos_dyadic_bound_f 323418479 268435456 4 3 268435456 134217728 Ns384p406 Ns384p149 Ns384p407 Ns384p408 Ns384p152 Ns384p407 96060681 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 323418479) qz370 0 3 Ns384p406 Ns384p149 Ns384p407 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 323418479) qz371 0 3 Ns384p408 Ns384p152 Ns384p407 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p410 := nat_lit 11575063232920021447145583779385782488516531297383146484911250329190507192704955565675443999214508180563296256 

noncomputable def Ns384p411 := nat_lit 9881742662448440261146369193801840092116707430447741126123709079548397619141872711333949006625820901376 

noncomputable def Ns384p412 := nat_lit 70107116836279996968619964528271711357849444823898772608332349920483745654144438999669489728913523814212567040 

noncomputable def Ns384p413 := BSN.cos_dyadic_bound_f 382739068 268435456 4 3 268435456 134217728 Ns384p410 Ns384p149 Ns384p411 Ns384p412 Ns384p152 Ns384p411 38782160 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 382739068) qz370 0 3 Ns384p410 Ns384p149 Ns384p411 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 382739068) qz371 0 3 Ns384p412 Ns384p152 Ns384p411 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p414 := Ns384p366 84999 BSN.abs_quadSignPos (BSN.cos_quad_nat0 228 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 96060681 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 124 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 38782160 268435456) qz63 rfl rfl (Ns384p397 RS385to396.d9 RS385to396.d11 RS385to396.d13 RS385to396.d17 (Ns384p401 rfl rfl) (Ns384p405 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns384p396 rfl) RS385to396.d19 RS385to396.d21 RS385to396.d23 RS385to396.d25 RS385to396.d17 (Ns384p409 rfl rfl) (Ns384p413 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns384p415 := nat_lit 174604410204526234673627398801 

noncomputable def Ns384p416 := BSN.cos_dyadic_bound_f 20441549 268435456 2 1 268435456 134217728 Ns384p415 Ns384p266 Ns384p415 Ns384p415 Ns384p267 Ns384p415 267657512 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 20441549) qz370 0 1 Ns384p415 Ns384p266 Ns384p415 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 20441549) qz371 0 1 Ns384p415 Ns384p267 Ns384p415 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p417 := nat_lit 118528881023232756884069752347628875791973426181139067040284152910618880 

noncomputable def Ns384p418 := nat_lit 56930955356977196584281828538352681699618975594280540879531439595776 

noncomputable def Ns384p419 := nat_lit 310340609704555447806665276045204008446702447371068721372653540054180096 

noncomputable def Ns384p420 := BSN.sin_dyadic_bound_f 294726074 268435456 3 2 268435456 134217728 Ns384p417 Ns384p131 Ns384p418 Ns384p419 Ns384p134 Ns384p418 238980340 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 294726074) qz372 0 2 Ns384p417 Ns384p131 Ns384p418 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 294726074) qz373 0 2 Ns384p419 Ns384p134 Ns384p418 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p421 := Ns384p364 114606 BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 267657512 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 31 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 238980340 268435456) qz63 rfl rfl (Ns384p414 rfl rfl) (Ns384p396 rfl) RS385to396.d27 RS385to396.d29 RS385to396.d31 RS385to396.d33 RS385to396.d17 (Ns384p416 rfl rfl) (Ns384p420 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p422 := nat_lit 23051935430898313191020503085661696230328427604426816523664073487094427795129656945504323731494155013934796241 

noncomputable def Ns384p423 := nat_lit 4459667845667308185361202149232071281892689977231158591277917216819319918552953048177388342299833650641 

noncomputable def Ns384p424 := nat_lit 115185043417434816096147891476419152845830728569158037336140635757159424229793000330222053704687791020957224401 

noncomputable def Ns384p425 := BSN.sin_dyadic_bound_f 358185947 268435456 4 3 268435456 134217728 Ns384p422 Ns384p156 Ns384p423 Ns384p424 Ns384p159 Ns384p423 260966445 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 358185947) qz372 0 3 Ns384p422 Ns384p156 Ns384p423 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 358185947) qz373 0 3 Ns384p424 Ns384p159 Ns384p423 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p426 := nat_lit 3431328321600946912813655089573169148435354814197772867250401884290699232027968275209245881174045878664892416 

noncomputable def Ns384p427 := nat_lit 258762321837034291984167259774192938595522754061156504803041223851495464354692096547517973814245134336 

noncomputable def Ns384p428 := nat_lit 20806593231719772574050745832307209521771021529474821750227796599119095341385231976578448349538766780062044160 

noncomputable def Ns384p429 := BSN.cos_dyadic_bound_f 282536842 268435456 4 3 268435456 134217728 Ns384p426 Ns384p149 Ns384p427 Ns384p428 Ns384p152 Ns384p427 132975771 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 282536842) qz370 0 3 Ns384p426 Ns384p149 Ns384p427 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 282536842) qz371 0 3 Ns384p428 Ns384p152 Ns384p427 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p430 := Ns384p362 140475 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 93 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 260966445 268435456) BSN.abs_quadSignPos qz590 (BSN.sfrac_eq_quadSignPos_mul Bool.false 132975771 268435456) qz63 rfl rfl (Ns384p421 rfl) (Ns384p396 rfl) RS385to396.d35 RS385to396.d37 RS385to396.d39 RS385to396.d41 RS385to396.d17 (Ns384p425 rfl rfl) (Ns384p429 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p431 := nat_lit 125313020250779274109129474871886569707566586251377703923771436605440000 

noncomputable def Ns384p432 := nat_lit 63630982836421941486728638631968359452576733344208479760409600000000 

noncomputable def Ns384p433 := nat_lit 328097745732210558571027254487632114747370220709146220356932146995200000 

noncomputable def Ns384p434 := BSN.sin_dyadic_bound_f 298853660 268435456 3 2 268435456 134217728 Ns384p431 Ns384p131 Ns384p432 Ns384p433 Ns384p134 Ns384p432 240831845 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 298853660) qz372 0 2 Ns384p431 Ns384p131 Ns384p432 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 298853660) qz373 0 2 Ns384p433 Ns384p134 Ns384p432 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p435 := Ns384p360 Bool.true 21711731 140475 Bool.true 298853660 14148475504056880 1 Bool.false 240831845 Bool.true Bool.true 97869447 152386 BSN.abs_quadSignNeg qz374 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 240831845 268435456) qz63 rfl (Ns384p430 rfl) (Ns384p396 rfl) RS385to396.d43 RS385to396.d45 RS385to396.d17 (Ns384p434 rfl rfl) rfl 

noncomputable def Ns384p436 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) 97869447 268435456 152386 268435456 97869447 268435456 152386 268435456 52543259267825664 97869447 134217728 76193 67108864 (Ns384p435 rfl rfl rfl rfl) 

noncomputable def Ns384p437 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz61) (Zeta.RiemannSiegel.correction qz62) 10216441 33554432 1 33554432 152124961134069 281474976710656 47483716106137 527765581332480000 1554175690053509028429 9444732965739290427392 

noncomputable def Ns384p438 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz61 1 1 0 1 10216441 33554432 1 33554432 10216441 33554432 1 33554432 

noncomputable abbrev qz69 := qz405

noncomputable def Ns384p439 := @Enclosure.Real.IsNear.sqrt_image qz69 3904369460771 33554432000 731107 33554432000 180975740 180975775 16777216 (@Enclosure.Real.IsNear.of_eq qz69 (@HMul.hMul Real Real Real qz5 qz60 qz3) Bool.false 3904369460771 33554432000 731107 33554432000 (BSN.t_div_two_pi_mk qz60 731107 1000 qz63) (@Enclosure.Real.IsNear.mulLit_ff qz60 qz3 731107 1000 0 1 5340353 33554432 1 33554432 3904369460771 33554432000 731107 33554432000 (Enclosure.Real.IsNear.const Bool.false 731107 1000) RS385to396.d48 rfl)) 

noncomputable abbrev qz723 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 731107 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz611 := qz723

noncomputable abbrev qz413 := qz611

noncomputable abbrev qz70 := qz413

noncomputable def Ns384p440 := @Enclosure.Real.IsNear.sqrt_image qz70 361951515 33554432 35 33554432 55102350 55102357 16777216 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 361951515 33554432 35 33554432 361951515 33554432 35 33554432 (Ns384p439 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns384p441 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz70) 110204707 33554432 7 33554432 5108220 5108221 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz70) Bool.false 110204707 33554432 7 33554432 110204707 33554432 7 33554432 (Ns384p440 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns384p442 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz70)) Bool.false 10216441 33554432 1 33554432 10216441 33554432 1 33554432 (Ns384p441 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz71 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz406))

noncomputable abbrev qz612 := (@HMul.hMul Real Real Real qz707 qz722 qz722)

noncomputable abbrev qz414 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz612 qz607) qz594)

noncomputable abbrev qz72 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz414))

noncomputable def Ns384p443 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz62) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz71) qz72) Bool.false 152124961134069 

noncomputable def Ns384p444 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz71) qz72 145658733 33554432 4275 

noncomputable def Ns384p445 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz71) Bool.false 145658733 33554432 4275 33554432 145658733 33554432 4275 

noncomputable def Ns384p446 := @Enclosure.Real.IsNear.recentre' qz71 Bool.false 7729711 33554432 1306514432 193273528320000 7729711 33554432 1275893 188743680000 

noncomputable abbrev qz73 := (@HMul.hMul Real Real Real qz349 qz346 qz406)

noncomputable def Ns384p447 := @Enclosure.Real.IsNear.cos_image qz73 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 165921299) qz378) Bool.false 165921299 33554432 221 33554432 Bool.false 7729711 33554432 1 

noncomputable def Ns384p448 := nat_lit 188902527908675533747820657 

noncomputable def Ns384p449 := nat_lit 28823037615171174400000000000000 

noncomputable def Ns384p450 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz62 884279719003555 140737488355328 1 500000000000000 26407195 33554432 35 33554432 23351346974272082578225 4722366482869645213696 Ns384p448 

noncomputable def Ns384p451 := @Enclosure.Real.IsNear.subLit_ff_p qz70 qz1 361951515 33554432 35 33554432 10 1 0 1 26407195 26407195 33554432 35 

noncomputable def Ns384p452 := @Ns384p451 33554432 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 361951515 33554432 35 33554432 361951515 33554432 35 33554432 (Ns384p439 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns384p453 := @Enclosure.Real.IsNear.recentre' qz73 Bool.false 23351346974272082578225 4722366482869645213696 Ns384p448 Ns384p449 165921299 33554432 221 33554432 (@Ns384p450 Ns384p449 RS385to396.d47 (Ns384p452 rfl rfl) rfl) 

noncomputable def Ns384p454 := nat_lit 65109674583419325967834704070917711290001 

noncomputable def Ns384p455 := BSN.sin_dyadic_bound_f 15973915443 68719476736 2 1 33554432 11531251 Ns384p454 Ns384p181 Ns384p454 Ns384p454 Ns384p182 Ns384p454 7729711 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 15973915443) qz368 0 1 Ns384p454 Ns384p181 Ns384p454 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 15973915443) qz369 0 1 Ns384p454 Ns384p182 Ns384p454 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p456 := @Ns384p447 5760000 (Ns384p453 rfl) (Enclosure.sfrac_false_div 165921299 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 165921299) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1124064369357286222594048) qz380) 226375608064910080 72057594037927936 Bool.false 7729711 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 165921299 33554432 226375608064910080 72057594037927936 0 1124064369357286222594048 Ns384p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 7729711 33554432 1124064369357286222594048 Ns384p98 15973915443 68719476736 11531251 11520000 (Ns384p455 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p457 := @Enclosure.Real.IsNear.inv_image qz71 7729711 33554432 1275893 188743680000 72827229 72831504 16777216 (Ns384p446 (Ns384p456 rfl rfl) rfl) rfl 

noncomputable def Ns384p458 := @Enclosure.Real.IsNear.recentre' qz72 Bool.false 2088786 16777216 

noncomputable abbrev qz74 := (@HMul.hMul Real Real Real qz349 qz346 qz414)

noncomputable abbrev qz415 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable def Ns384p459 := @Enclosure.Real.IsNear.cos_image qz74 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 24259369)) qz415) Bool.true 24259369 16777216 

noncomputable def Ns384p460 := nat_lit 229123264422413245552112709845 

noncomputable def Ns384p461 := nat_lit 81576477082048672519717479814055533 

noncomputable def Ns384p462 := @Enclosure.Real.IsNear.recentre' qz74 Bool.true Ns384p460 Ns384p307 Ns384p461 

noncomputable def Ns384p463 := nat_lit 4835703278458516698824704000000000000000 

noncomputable abbrev qz75 := qz414

noncomputable def Ns384p464 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz75 884279719003555 140737488355328 1 500000000000000 259107225347879 

noncomputable abbrev qz416 := (@HSub.hSub Real Real Real qz583 qz612 qz607)

noncomputable abbrev qz76 := qz416

noncomputable def Ns384p465 := @Enclosure.Real.IsNear.subLit_tf qz76 qz29 188738481170215 1125899906842624 3022909995 1125899906842624 1 16 

noncomputable abbrev qz417 := qz612

noncomputable abbrev qz77 := qz417

noncomputable def Ns384p466 := @Enclosure.Real.IsNear.subLit_ff_n qz77 qz62 697339947768025 1125899906842624 1848504875 1125899906842624 26407195 33554432 35 33554432 

noncomputable def Ns384p467 := @Enclosure.Real.IsNear.mulLit_ff qz62 qz62 26407195 33554432 35 33554432 26407195 33554432 35 33554432 697339947768025 1125899906842624 

noncomputable def Ns384p468 := nat_lit 43504274412007908235022543391813154741895925284135166250165213834335224226794267391896122182241 

noncomputable def Ns384p469 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600 

noncomputable def Ns384p470 := nat_lit 41548371405111422468041515985607211189553395514983169308420998943622287238885895862372961 

noncomputable def Ns384p471 := nat_lit 263469063097992969509105078648601477903594355027358641623959808613002779481712910549418260187745 

noncomputable def Ns384p472 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600 

noncomputable def Ns384p473 := BSN.cos_dyadic_bound_f 24259369 16777216 4 3 16777216 5760000 Ns384p468 Ns384p469 Ns384p470 Ns384p471 Ns384p472 Ns384p470 2088786 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 24259369) (BSN.cosEvenQ 16777216) 0 3 Ns384p468 Ns384p469 Ns384p470 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 24259369) (BSN.cosOddQ 16777216) 0 3 Ns384p471 Ns384p472 Ns384p470 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p474 := @Ns384p458 3299474432 193273528320000 1044393 8388608 3222143 188743680000 (@Ns384p459 567 33554432 Bool.false 2088786 16777216 1 5760000 (@Ns384p462 Ns384p463 24259369 16777216 567 33554432 (@Ns384p464 1125899906842624 3022909995 1125899906842624 Ns384p460 Ns384p307 Ns384p461 Ns384p463 RS385to396.d47 (@Ns384p465 0 1 4145715605566064 259107225347879 1125899906842624 3022909995 1125899906842624 (@Ns384p466 6333012532209259642880 188738481170215 1125899906842624 3022909995 1125899906842624 (@Ns384p467 1848504875 1125899906842624 (Ns384p452 rfl rfl) (Ns384p452 rfl rfl) rfl) (Ns384p452 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 24259369 16777216) (BSN.cos_neg_of_bound 24259369 16777216 Bool.false 2088786 16777216 1 5760000 (Ns384p473 rfl rfl)) rfl rfl) 

noncomputable def Ns384p475 := @Ns384p437 485399865844940883929 Ns384p357 (Ns384p438 qz31 (@Enclosure.Real.IsNear.of_eq qz61 (@Inv.inv Real Real.instInv (Real.sqrt qz70)) Bool.false 10216441 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz69 (BSN.t_div_two_pi_nonneg qz60 731107 1000 qz63)) Ns384p442) rfl) (@Ns384p443 281474976710656 47483716106137 527765581332480000 (BSN.correction_mk qz62 (BSN.cos_two_pi_p_ne_zero_mk qz60 731107 1000 10 qz63 rfl rfl (@BSN.floor_sqrt_eq_dec qz60 731107 1000 10 qz63 rfl rfl rfl))) (@Ns384p444 33554432 1044393 8388608 3222143 188743680000 152124961134069 281474976710656 47483716106137 527765581332480000 (@Ns384p445 33554432 (Ns384p457 rfl rfl rfl rfl rfl) rfl) (Ns384p474 rfl) rfl)) 

noncomputable def Ns384p476 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz60) (hardyZApproximantRS₀ qz60) Bool.true 8441125768805954460237 9444732965739290427392 20591421335077765203929 Ns384p357 (@Eq.refl Real (hardyZApproximantRS₀ qz60)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz60) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz61) (Zeta.RiemannSiegel.correction qz62))) Bool.true 8441125768805954460237 9444732965739290427392 20591421335077765203929 Ns384p357 (BSN.hardyZApproximantRS₀_eq qz60 10 (@BSN.floor_sqrt_eq_dec qz60 731107 1000 10 qz63 rfl rfl rfl)) (@Ns384p359 8441125768805954460237 9444732965739290427392 20591421335077765203929 Ns384p357 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 10)) Bool.true 97869447 134217728 76193 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (Ns384p436 (Ns384p435 rfl rfl rfl rfl) rfl rfl)) (Ns384p475 rfl) rfl rfl)) 

theorem RS385to396.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz60) Bool.true 8441125768805954460237 9444732965739290427392 20591421335077765203929 Ns384p357 := Ns384p476 

noncomputable def Ns384p477 := nat_lit 83242990093103929433205506048 

noncomputable abbrev qz724 := (Enclosure.sfrac Bool.false 732428 1000)

noncomputable abbrev qz613 := qz724

noncomputable abbrev qz418 := qz613

noncomputable abbrev qz78 := qz418

noncomputable abbrev qz725 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 732428 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz614 := qz725

noncomputable abbrev qz419 := qz614

noncomputable abbrev qz79 := (@HPow.hPow Real Real Real qz350 qz419 qz352)

noncomputable abbrev qz726 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 732428 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz615 := qz726

noncomputable abbrev qz420 := qz615

noncomputable abbrev qz80 := qz420

noncomputable def Ns384p478 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz79) (Zeta.RiemannSiegel.correction qz80)) 152298985 67108864 76333 67108864 99218825612655687873 590295810358705651712 4064649429657275569 184467440737095516160000 Ns384p477 

noncomputable def Ns384p479 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.sin BSN.quadSignNeg 9 10 732428 1000 197 268435456 134217728 4503599627370496 Bool.false 369372085207 2544 618095470 48 84886744 8 

noncomputable def Ns384p480 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 732428 1000 93 148 268435456 134217728 4503599627370496 Bool.false 369372085207 2544 

noncomputable def Ns384p481 := Ns384p480 558195838 48 94906264 8 589812974 48 89478488 8 Bool.false 391661640 114818 Bool.true 252035198 Bool.true 218152330 14148475504056880 1 Bool.false 216603622 Bool.true Bool.false 184563957 Bool.false Bool.false 376602017 

noncomputable def Ns384p482 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 732428 1000 40 31 268435456 134217728 4503599627370496 Bool.false 369372085207 2544 

noncomputable def Ns384p483 := Ns384p482 480971758 48 109588312 8 522351262 48 101459064 8 Bool.false 268519377 85157 Bool.false 228605307 Bool.true 141224640 14148475504056880 1 Bool.false 176835709 Bool.false Bool.false 134799417 Bool.false Bool.false 391661640 

noncomputable def Ns384p484 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 732428 1000 229 125 268435456 134217728 4503599627370496 Bool.false 369372085207 2544 

noncomputable def Ns384p485 := Ns384p484 372130544 47 134217720 8 432030192 47 120047984 16 Bool.false 469171367 50112 Bool.false 253704053 Bool.false 233897207 14148475504056880 1 Bool.false 217585176 Bool.true Bool.false 205403884 Bool.true Bool.false 268519377 

noncomputable def Ns384p486 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 732428 1000 552 363 268435456 134217728 4503599627370496 Bool.false 369372085207 2544 

noncomputable def Ns384p487 := Ns384p486 186065264 47 189812528 16 294906480 47 154981288 8 Bool.false 268435392 2599 Bool.false 337775623 Bool.false 312675412 14148475504056880 1 Bool.false 82523330 Bool.false Bool.false 246614876 Bool.false Bool.false 469171367 

noncomputable def Ns384p488 := nat_lit 52552910828841808848099692435291963721213638710572257 

noncomputable def Ns384p489 := nat_lit 38192015984518327164208271538728035949654468198400 

noncomputable def Ns384p490 := nat_lit 101173422851000704518642695536640000 

noncomputable def Ns384p491 := nat_lit 444613583205713973895277263814676971520 

noncomputable abbrev qz616 := (@Eq.refl Real qz724)

noncomputable abbrev qz421 := qz616

noncomputable abbrev qz81 := qz421

noncomputable def Ns384p492 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz78 732428 1000 2145804100736 16000000 1464856 4000 2000 Ns384p490 Ns384p491 qz81 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns384p493 := nat_lit 551057210252636285547049830950287061509353124245770149560320 

noncomputable abbrev qz617 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1464856))))

noncomputable abbrev qz422 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 732428 4000) (Real.log (Enclosure.sfrac Bool.false 2145804100736 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz617))

noncomputable abbrev qz618 := (Enclosure.sfrac Bool.false 732428 2000)

noncomputable abbrev qz82 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz422 qz618) (@HMul.hMul Real Real Real qz349 qz618 (Real.log Real.pi)))

noncomputable def Ns384p494 := @Enclosure.Real.IsNear.addLit_ft_p qz82 (Enclosure.sfrac Bool.true Ns384p490 Ns384p491) 1239407256540317581441 900719925474099200 87313268288501279 9216000000000000000000 Ns384p490 Ns384p491 0 1 Ns384p493 

noncomputable def Ns384p495 := nat_lit 103969016274721603862166241280000 

noncomputable abbrev qz83 := (@HSub.hSub Real Real Real qz355 qz422 qz618)

noncomputable def Ns384p496 := @Enclosure.Real.IsNear.subLit_ff_p qz83 (@HMul.hMul Real Real Real qz5 qz618 (Real.log Real.pi)) 8085017795801621430917 4503599627370496000 9038434738499 2250000000000000000 7033279214427 16777216000 183107 33554432000 Ns384p495 1239407256540317581441 900719925474099200 

noncomputable def Ns384p497 := nat_lit 16170035591603242861834000 

noncomputable abbrev qz84 := qz422

noncomputable def Ns384p498 := @Enclosure.Real.IsNear.subLit_ff_p qz84 qz618 9734299029739480253061 4503599627370496000 9038434738499 2250000000000000000 732428 2000 0 1 Ns384p497 8085017795801621430917 4503599627370496000 9038434738499 2250000000000000000 

noncomputable def Ns384p499 := nat_lit 21919692741523852014090871842042544128 

noncomputable def Ns384p500 := nat_lit 57092422171271952599089152 

noncomputable def Ns384p501 := nat_lit 54008029418318524139225088 

noncomputable def Ns384p502 := BSN.log_dyadic_bound 48652100736 4242956100736 2 1 Ns384p501 134217728 46080000 2367026906025891741696 2367026906025891741696 3078165 4291608201472 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 48652100736) (BSN.artanhQ 4242956100736) 0 1 2367026906025891741696 Ns384p501 2367026906025891741696 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz423 := (Real.log (Enclosure.sfrac Bool.false 2145804100736 16000000))

noncomputable def Ns384p503 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 732428 4000) qz423 732428 4000 0 1 53171461607582823 4503599627370496 195312653 9000000000000000 9736066820579667971061 4503599627370496000 35763113952871 9000000000000000000 (Enclosure.Real.IsNear.const Bool.false 732428 4000) (BSN.isNear_log_sfrac 2145804100736 16000000 53171461607582823 4503599627370496 195312653 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2145804100736) qz358)) Bool.false Ns384p500 Ns384p98 1000000783360000 46080000000000000000000 53171461607582823 4503599627370496 195312653 9000000000000000 (BSN.log_rat_reduce_isNear 2145804100736 16000000 17 4291608201472 4194304000000 3078165 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns384p502 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns384p504 := BSN.arctan_dyadic_bound_f 1000 1464856 1 0 16777216 5760000 0 1 1 0 1 1 11453 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1464856) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1464856) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz424 := (@Nat.cast Real Real.instNatCast 1464856)

noncomputable def Ns384p505 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz424)) 884279719003555 562949953421312 1 2000000000000000 11453 16777216 1 5760000 14829304384325412716544 883895420093859 562949953421312 3125000009 18000000000000000 qz15 (Ns384p504 rfl) rfl rfl 

noncomputable abbrev qz425 := (@HMul.hMul Real Real Real qz579 qz584 qz617)

noncomputable abbrev qz85 := qz425

noncomputable abbrev qz426 := qz617

noncomputable abbrev qz86 := qz426

noncomputable def Ns384p506 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 732428 4000) qz423) qz85 9736066820579667971061 4503599627370496000 35763113952871 9000000000000000000 883895420093859 2251799813685248 3125000009 72000000000000000 Ns384p499 9734299029739480253061 4503599627370496000 9038434738499 2250000000000000000 (Ns384p503 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz86 1 4 0 1 883895420093859 562949953421312 3125000009 18000000000000000 883895420093859 2251799813685248 3125000009 72000000000000000 qz366 Ns384p505 rfl) 

noncomputable def Ns384p507 := @Ns384p494 Ns384p488 Ns384p489 87313268288501279 9216000000000000000000 (@Ns384p496 87313268288501279 9216000000000000000000 (Ns384p498 (Ns384p506 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 732428 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz618 (Real.log Real.pi) 732428 2000 0 1 38410761 33554432 1 67108864 7033279214427 16777216000 183107 33554432000 (Enclosure.Real.IsNear.const Bool.false 732428 2000) RS385to396.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns384p490 Ns384p491) 

noncomputable def Ns384p508 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz78) Bool.false Ns384p488 Ns384p489 87313268288501279 9216000000000000000000 23085755325 16777216 319 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz78) (@HAdd.hAdd Real Real Real qz367 qz82 (Enclosure.sfrac Bool.true Ns384p490 Ns384p491)) Bool.false Ns384p488 Ns384p489 87313268288501279 9216000000000000000000 Ns384p492 (Ns384p507 rfl rfl)) 

noncomputable def Ns384p509 := nat_lit 2417851639229258349412352 

noncomputable def Ns384p510 := BSN.cos_dyadic_bound_f 45577909 68719476736 1 0 33554432 11531251 0 1 1 0 1 1 33554424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 45577909) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 45577909) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable abbrev qz427 := (@Nat.cast Real Real.instNatCast Ns384p509)

noncomputable def Ns384p511 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz78) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23085755325) qz415) Bool.false 23085755325 16777216 319 33554432 Bool.false 33554424 33554432 1 5760000 (Ns384p508 rfl) (Enclosure.sfrac_false_div 23085755325 16777216) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23085755325) qz415) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1603630133733878661120) qz427) 226375608064910080 72057594037927936 Bool.false 33554424 33554432 219 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q0 23085755325 16777216 226375608064910080 72057594037927936 219 1603630133733878661120 Ns384p509 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554424 33554432 1603630133733878661120 Ns384p509 45577909 68719476736 11531251 11520000 (Ns384p510 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p512 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz78) Bool.false Ns384p488 Ns384p489 87313268288501279 9216000000000000000000 369372085207 268435456 2544 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz78) (@HAdd.hAdd Real Real Real qz367 qz82 (Enclosure.sfrac Bool.true Ns384p490 Ns384p491)) Bool.false Ns384p488 Ns384p489 87313268288501279 9216000000000000000000 Ns384p492 (Ns384p507 rfl rfl)) 

noncomputable def Ns384p513 := Ns384p487 50112 BSN.abs_quadSignPos (BSN.cos_quad_nat0 552 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 82523330 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 363 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 246614876 268435456) qz81 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 1) Bool.false 4194303 4194304 1827143 188743680000 268435392 268435456 2599 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz78)) Bool.false 4194303 4194304 1827143 188743680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz78) qz78) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz78)) Bool.false 33554424 33554432 1870994432 193273528320000 4194303 4194304 1827143 188743680000 (Ns384p511 rfl rfl) rfl)) rfl) (Ns384p512 rfl) RS385to396.d7 

noncomputable def Ns384p514 := nat_lit 7014645040221045220359664506518719522038678778763308763296073528127731365167534700063129373863925751903828001 

noncomputable def Ns384p515 := nat_lit 2205665469046084601677333101629200732487277952633087477596812124083391043861198166353286855298251634721 

noncomputable def Ns384p516 := nat_lit 42513229244912553578499525461781328744292948347624330598100243942182029600206031691373621088225492308494006305 

noncomputable def Ns384p517 := BSN.cos_dyadic_bound_f 337775623 268435456 4 3 268435456 134217728 Ns384p514 Ns384p149 Ns384p515 Ns384p516 Ns384p152 Ns384p515 82523330 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 337775623) qz370 0 3 Ns384p514 Ns384p149 Ns384p515 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 337775623) qz371 0 3 Ns384p516 Ns384p152 Ns384p515 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p518 := nat_lit 150169079049713282537875886660593959761284034188350887018143480968970240 

noncomputable def Ns384p519 := nat_lit 91358686341187842400811200102795619501922022480705073002287999287296 

noncomputable def Ns384p520 := nat_lit 393152054876125245378168865977579654086074120552140705405514936253218816 

noncomputable def Ns384p521 := BSN.sin_dyadic_bound_f 312675412 268435456 3 2 268435456 134217728 Ns384p518 Ns384p131 Ns384p519 Ns384p520 Ns384p134 Ns384p519 246614876 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 312675412) qz372 0 2 Ns384p518 Ns384p131 Ns384p519 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 312675412) qz373 0 2 Ns384p520 Ns384p134 Ns384p519 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p522 := nat_lit 65067706449482811323648817985251985814002992556652551791130246378399585 

noncomputable def Ns384p523 := nat_lit 17164029098023792255181888875799097458128142359284348499922332395361 

noncomputable def Ns384p524 := nat_lit 170387632272962943517333752617480097640789915894079746698246009119549281 

noncomputable def Ns384p525 := BSN.sin_dyadic_bound_f 253704053 268435456 3 2 268435456 134217728 Ns384p522 Ns384p131 Ns384p523 Ns384p524 Ns384p134 Ns384p523 217585176 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 253704053) qz372 0 2 Ns384p522 Ns384p131 Ns384p523 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 253704053) qz373 0 2 Ns384p524 Ns384p134 Ns384p523 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p526 := nat_lit 47002853045637462620931481961120432381410473853685422845134693041975105 

noncomputable def Ns384p527 := nat_lit 8957777830643620107654197580025085386259268827354498348570264481601 

noncomputable def Ns384p528 := nat_lit 123088207288753264812741488816376329908306821276788962073264606110297921 

noncomputable def Ns384p529 := BSN.sin_dyadic_bound_f 233897207 268435456 3 2 268435456 134217728 Ns384p526 Ns384p131 Ns384p527 Ns384p528 Ns384p134 Ns384p527 205403884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 233897207) qz372 0 2 Ns384p526 Ns384p131 Ns384p527 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 233897207) qz373 0 2 Ns384p528 Ns384p134 Ns384p527 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p530 := Ns384p485 85157 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 229 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 217585176 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 125 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 205403884 268435456) qz81 rfl rfl (Ns384p513 RS385to396.d9 RS385to396.d11 RS385to396.d13 RS385to396.d17 (Ns384p517 rfl rfl) (Ns384p521 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns384p512 rfl) RS385to396.d19 RS385to396.d21 RS385to396.d23 RS385to396.d25 RS385to396.d17 (Ns384p525 rfl rfl) (Ns384p529 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns384p531 := nat_lit 23831423426074888221925290098819338638759710474075272784402757683149281 

noncomputable def Ns384p532 := nat_lit 7459169318602558552150966395535162076020981480976386050479557868001 

noncomputable def Ns384p533 := nat_lit 71479351939587459548671568363666945592127089459263865581107313933711841 

noncomputable def Ns384p534 := BSN.cos_dyadic_bound_f 228605307 268435456 3 2 268435456 134217728 Ns384p531 Ns384p117 Ns384p532 Ns384p533 Ns384p120 Ns384p532 176835709 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 228605307) qz370 0 2 Ns384p531 Ns384p117 Ns384p532 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 228605307) qz371 0 2 Ns384p533 Ns384p120 Ns384p532 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p535 := nat_lit 6245888236652164698844401437623182438365634452524288598967205232640000 

noncomputable def Ns384p536 := nat_lit 158228171984611271424185934632795602612361655903034382745600000000 

noncomputable def Ns384p537 := nat_lit 16358022536096265793010174130833215193315289266311198560675377971200000 

noncomputable def Ns384p538 := BSN.sin_dyadic_bound_f 141224640 268435456 3 2 268435456 134217728 Ns384p535 Ns384p131 Ns384p536 Ns384p537 Ns384p134 Ns384p536 134799417 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 141224640) qz372 0 2 Ns384p535 Ns384p131 Ns384p536 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 141224640) qz373 0 2 Ns384p537 Ns384p134 Ns384p536 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p539 := Ns384p483 114818 BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 176835709 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 31 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 134799417 268435456) qz81 rfl rfl (Ns384p530 rfl rfl) (Ns384p512 rfl) RS385to396.d27 RS385to396.d29 RS385to396.d31 RS385to396.d33 RS385to396.d17 (Ns384p534 rfl rfl) (Ns384p538 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p540 := nat_lit 63372038698732772392473629005230672257054931807578230572742472458174720 

noncomputable def Ns384p541 := nat_lit 16281318479758931098649949244751690699092085496727821487567139635456 

noncomputable def Ns384p542 := nat_lit 165948026838190032282318833191112638888297719929043520741440890592952576 

noncomputable def Ns384p543 := BSN.sin_dyadic_bound_f 252035198 268435456 3 2 268435456 134217728 Ns384p540 Ns384p131 Ns384p541 Ns384p542 Ns384p134 Ns384p541 216603622 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 252035198) qz372 0 2 Ns384p540 Ns384p131 Ns384p541 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 252035198) qz373 0 2 Ns384p542 Ns384p134 Ns384p541 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p544 := nat_lit 19761548152402207187102387924937015282350585132930405556093912368800000 

noncomputable def Ns384p545 := nat_lit 5129545034419119393775236209532764436315506128312138470144100000000 

noncomputable def Ns384p546 := nat_lit 59274385367137783322519613302391980318179124386534592391341448906400000 

noncomputable def Ns384p547 := BSN.cos_dyadic_bound_f 218152330 268435456 3 2 268435456 134217728 Ns384p544 Ns384p117 Ns384p545 Ns384p546 Ns384p120 Ns384p545 184563957 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 218152330) qz370 0 2 Ns384p544 Ns384p117 Ns384p545 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 218152330) qz371 0 2 Ns384p546 Ns384p120 Ns384p545 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p548 := Ns384p481 140734 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 93 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 216603622 268435456) BSN.abs_quadSignPos qz590 (BSN.sfrac_eq_quadSignPos_mul Bool.false 184563957 268435456) qz81 rfl rfl (Ns384p539 rfl) (Ns384p512 rfl) RS385to396.d35 RS385to396.d37 RS385to396.d39 RS385to396.d41 RS385to396.d17 (Ns384p543 rfl rfl) (Ns384p547 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p549 := nat_lit 85759830199553731616629071094432197183601428277655155406522261550390625 

noncomputable def Ns384p550 := nat_lit 29811459248022736330419612989318290974745546772243128344879150390625 

noncomputable def Ns384p551 := nat_lit 224560812921953450756160221112006382057377962222894156237857071150390625 

noncomputable def Ns384p552 := BSN.sin_dyadic_bound_f 271830325 268435456 3 2 268435456 134217728 Ns384p549 Ns384p131 Ns384p550 Ns384p551 Ns384p134 Ns384p550 227696790 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 271830325) qz372 0 2 Ns384p549 Ns384p131 Ns384p550 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 271830325) qz373 0 2 Ns384p551 Ns384p134 Ns384p550 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p553 := Ns384p479 Bool.false 376602017 140734 Bool.true 271830325 14148475504056880 1 Bool.false 227696790 Bool.true Bool.false 304597970 152666 BSN.abs_quadSignNeg qz374 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 227696790 268435456) qz81 rfl (Ns384p548 rfl) (Ns384p512 rfl) RS385to396.d43 RS385to396.d45 RS385to396.d17 (Ns384p552 rfl rfl) rfl 

noncomputable def Ns384p554 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) 304597970 268435456 152666 268435456 304597970 268435456 152666 268435456 163529789947248640 152298985 67108864 76333 67108864 (Ns384p553 rfl rfl rfl rfl) 

noncomputable def Ns384p555 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz79) (Zeta.RiemannSiegel.correction qz80) 1276479 4194304 1 16777216 77728521669887 140737488355328 6359017412781 87960930222080000 99218825612655687873 590295810358705651712 

noncomputable def Ns384p556 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz79 1 1 0 1 1276479 4194304 1 16777216 1276479 4194304 1 16777216 

noncomputable abbrev qz87 := qz419

noncomputable def Ns384p557 := @Enclosure.Real.IsNear.sqrt_image qz87 977856016771 8388608000 183107 8388608000 181139164 181139199 16777216 (@Enclosure.Real.IsNear.of_eq qz87 (@HMul.hMul Real Real Real qz5 qz78 qz3) Bool.false 977856016771 8388608000 183107 8388608000 (BSN.t_div_two_pi_mk qz78 732428 1000 qz81) (@Enclosure.Real.IsNear.mulLit_ff qz78 qz3 732428 1000 0 1 5340353 33554432 1 33554432 977856016771 8388608000 183107 8388608000 (Enclosure.Real.IsNear.const Bool.false 732428 1000) RS385to396.d48 rfl)) 

noncomputable abbrev qz727 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 732428 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz619 := qz727

noncomputable abbrev qz428 := qz619

noncomputable abbrev qz88 := qz428

noncomputable def Ns384p558 := @Enclosure.Real.IsNear.sqrt_image qz88 362278363 33554432 35 33554432 55127224 55127230 16777216 (@Enclosure.Real.IsNear.recentre' qz88 Bool.false 362278363 33554432 35 33554432 362278363 33554432 35 33554432 (Ns384p557 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns384p559 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz88) 55127227 16777216 3 16777216 5105915 5105917 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz88) Bool.false 110254454 33554432 6 33554432 55127227 16777216 3 16777216 (Ns384p558 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns384p560 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz88)) Bool.false 10211832 33554432 2 33554432 1276479 4194304 1 16777216 (Ns384p559 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz89 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz420))

noncomputable abbrev qz620 := (@HMul.hMul Real Real Real qz707 qz726 qz726)

noncomputable abbrev qz429 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz620 qz615) qz594)

noncomputable abbrev qz90 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz429))

noncomputable def Ns384p561 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz80) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz89) qz90) Bool.false 77728521669887 

noncomputable def Ns384p562 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz89) qz90 28980979 8388608 677 

noncomputable def Ns384p563 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz89) Bool.false 115923916 33554432 2708 33554432 28980979 8388608 677 

noncomputable def Ns384p564 := @Enclosure.Real.IsNear.recentre' qz89 Bool.false 9712404 33554432 1306514432 193273528320000 2428101 8388608 1275893 188743680000 

noncomputable abbrev qz91 := (@HMul.hMul Real Real Real qz349 qz346 qz420)

noncomputable def Ns384p565 := @Enclosure.Real.IsNear.cos_image qz91 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 83987473) qz415) Bool.false 83987473 16777216 221 33554432 Bool.false 9712404 33554432 1 

noncomputable def Ns384p566 := nat_lit 944512639546185271680629301 

noncomputable def Ns384p567 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz80 884279719003555 140737488355328 1 500000000000000 26734043 33554432 35 33554432 23640372031868956522865 4722366482869645213696 Ns384p566 

noncomputable def Ns384p568 := @Enclosure.Real.IsNear.subLit_ff_p qz88 qz1 362278363 33554432 35 33554432 10 1 0 1 26734043 26734043 33554432 35 

noncomputable def Ns384p569 := @Ns384p568 33554432 (@Enclosure.Real.IsNear.recentre' qz88 Bool.false 362278363 33554432 35 33554432 362278363 33554432 35 33554432 (Ns384p557 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns384p570 := @Enclosure.Real.IsNear.recentre' qz91 Bool.false 23640372031868956522865 4722366482869645213696 Ns384p566 Ns384p295 83987473 16777216 221 33554432 (@Ns384p567 Ns384p295 RS385to396.d47 (Ns384p569 rfl rfl) rfl) 

noncomputable def Ns384p571 := nat_lit 165831143817605108717361318126275922362001 

noncomputable def Ns384p572 := BSN.sin_dyadic_bound_f 20179784499 68719476736 2 1 33554432 11531251 Ns384p571 Ns384p181 Ns384p571 Ns384p571 Ns384p182 Ns384p571 9712404 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 20179784499) qz368 0 1 Ns384p571 Ns384p181 Ns384p571 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 20179784499) qz369 0 1 Ns384p571 Ns384p182 Ns384p571 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p573 := @Ns384p565 5760000 (Ns384p570 rfl) (Enclosure.sfrac_false_div 83987473 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 83987473) qz415) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 710013046501851703279616) qz427) 226375608064910080 72057594037927936 Bool.false 9712404 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 83987473 16777216 226375608064910080 72057594037927936 0 710013046501851703279616 Ns384p509 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 9712404 33554432 710013046501851703279616 Ns384p509 20179784499 68719476736 11531251 11520000 (Ns384p572 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p574 := @Enclosure.Real.IsNear.inv_image qz89 2428101 8388608 1275893 188743680000 57960604 57963312 16777216 (Ns384p564 (Ns384p573 rfl rfl) rfl) rfl 

noncomputable def Ns384p575 := @Enclosure.Real.IsNear.recentre' qz90 Bool.false 2682053 16777216 

noncomputable abbrev qz92 := (@HMul.hMul Real Real Real qz349 qz346 qz429)

noncomputable def Ns384p576 := @Enclosure.Real.IsNear.cos_image qz92 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 23659979)) qz415) Bool.true 23659979 16777216 

noncomputable def Ns384p577 := nat_lit 223462186690124449391994290005 

noncomputable def Ns384p578 := nat_lit 82193901216264346517401955051531757 

noncomputable def Ns384p579 := @Enclosure.Real.IsNear.recentre' qz92 Bool.true Ns384p577 Ns384p307 Ns384p578 

noncomputable abbrev qz93 := qz429

noncomputable def Ns384p580 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz93 884279719003555 140737488355328 1 500000000000000 252705316980391 

noncomputable abbrev qz430 := (@HSub.hSub Real Real Real qz583 qz620 qz615)

noncomputable abbrev qz94 := qz430

noncomputable def Ns384p581 := @Enclosure.Real.IsNear.subLit_tf qz94 qz29 182336572802727 1125899906842624 3045789355 1125899906842624 1 16 

noncomputable abbrev qz431 := qz620

noncomputable abbrev qz95 := qz431

noncomputable def Ns384p582 := @Enclosure.Real.IsNear.subLit_ff_n qz95 qz80 714709055125849 1125899906842624 1871384235 1125899906842624 26734043 33554432 35 33554432 

noncomputable def Ns384p583 := @Enclosure.Real.IsNear.mulLit_ff qz80 qz80 26734043 33554432 35 33554432 26734043 33554432 35 33554432 714709055125849 1125899906842624 

noncomputable def Ns384p584 := nat_lit 39351738394212382771087987511399505533884349200541786971730986772489807927086970654386200581521 

noncomputable def Ns384p585 := nat_lit 30773171549366320116377696351663768744298143527444151312080039687237623673319109725066641 

noncomputable def Ns384p586 := nat_lit 238359897473213530146801890004113626509164170756310300525147132190330403300486484808898495714705 

noncomputable def Ns384p587 := BSN.cos_dyadic_bound_f 23659979 16777216 4 3 16777216 5760000 Ns384p584 Ns384p469 Ns384p585 Ns384p586 Ns384p472 Ns384p585 2682053 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 23659979) (BSN.cosEvenQ 16777216) 0 3 Ns384p584 Ns384p469 Ns384p585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 23659979) (BSN.cosOddQ 16777216) 0 3 Ns384p586 Ns384p472 Ns384p585 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p588 := @Ns384p575 3322514432 193273528320000 2682053 16777216 3244643 188743680000 (@Ns384p576 571 33554432 Bool.false 2682053 16777216 1 5760000 (@Ns384p579 Ns384p463 23659979 16777216 571 33554432 (@Ns384p580 1125899906842624 3045789355 1125899906842624 Ns384p577 Ns384p307 Ns384p578 Ns384p463 RS385to396.d47 (@Ns384p581 0 1 4043285071686256 252705316980391 1125899906842624 3045789355 1125899906842624 (@Ns384p582 6118200133222152536064 182336572802727 1125899906842624 3045789355 1125899906842624 (@Ns384p583 1871384235 1125899906842624 (Ns384p569 rfl rfl) (Ns384p569 rfl rfl) rfl) (Ns384p569 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 23659979 16777216) (BSN.cos_neg_of_bound 23659979 16777216 Bool.false 2682053 16777216 1 5760000 (Ns384p587 rfl rfl)) rfl rfl) 

noncomputable def Ns384p589 := @Ns384p555 4064649429657275569 184467440737095516160000 (Ns384p556 qz31 (@Enclosure.Real.IsNear.of_eq qz79 (@Inv.inv Real Real.instInv (Real.sqrt qz88)) Bool.false 1276479 4194304 1 16777216 (BSN.rpow_neg_quarter_mk qz87 (BSN.t_div_two_pi_nonneg qz78 732428 1000 qz81)) Ns384p560) rfl) (@Ns384p561 140737488355328 6359017412781 87960930222080000 (BSN.correction_mk qz80 (BSN.cos_two_pi_p_ne_zero_mk qz78 732428 1000 10 qz81 rfl rfl (@BSN.floor_sqrt_eq_dec qz78 732428 1000 10 qz81 rfl rfl rfl))) (@Ns384p562 8388608 2682053 16777216 3244643 188743680000 77728521669887 140737488355328 6359017412781 87960930222080000 (@Ns384p563 8388608 (Ns384p574 rfl rfl rfl rfl rfl) rfl) (Ns384p588 rfl) rfl)) 

noncomputable def Ns384p590 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz78) (hardyZApproximantRS₀ qz78) Bool.false 1240417213635205171007 590295810358705651712 213887202137220795569 184467440737095516160000 (@Eq.refl Real (hardyZApproximantRS₀ qz78)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz78) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz79) (Zeta.RiemannSiegel.correction qz80))) Bool.false 1240417213635205171007 590295810358705651712 213887202137220795569 184467440737095516160000 (BSN.hardyZApproximantRS₀_eq qz78 10 (@BSN.floor_sqrt_eq_dec qz78 732428 1000 10 qz81 rfl rfl rfl)) (@Ns384p478 1240417213635205171007 590295810358705651712 213887202137220795569 184467440737095516160000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 10)) Bool.false 152298985 67108864 76333 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (Ns384p554 (Ns384p553 rfl rfl rfl rfl) rfl rfl)) (Ns384p589 rfl) rfl rfl)) 

theorem RS385to396.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz78) Bool.false 1240417213635205171007 590295810358705651712 213887202137220795569 184467440737095516160000 := Ns384p590 

noncomputable def Ns384p591 := nat_lit 6640827866535438581760000 

noncomputable def Ns384p592 := nat_lit 411008490410436698808015388672 

noncomputable abbrev qz728 := (Enclosure.sfrac Bool.false 733748 1000)

noncomputable abbrev qz621 := qz728

noncomputable abbrev qz432 := qz621

noncomputable abbrev qz96 := qz432

noncomputable abbrev qz729 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 733748 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz622 := qz729

noncomputable abbrev qz433 := qz622

noncomputable abbrev qz97 := (@HPow.hPow Real Real Real qz350 qz433 qz352)

noncomputable abbrev qz730 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 733748 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz623 := qz730

noncomputable abbrev qz434 := qz623

noncomputable abbrev qz98 := qz434

noncomputable def Ns384p593 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz97) (Zeta.RiemannSiegel.correction qz98)) 168305627 33554432 76473 67108864 405551925267472872993 2361183241434822606848 123104572740019592839 Ns384p591 Ns384p592 

noncomputable def Ns384p594 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.sin BSN.quadSignNeg 9 10 733748 1000 197 268435456 134217728 4503599627370496 Bool.false 370215293534 2549 618095470 48 84886744 8 

noncomputable def Ns384p595 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 733748 1000 93 148 268435456 134217728 4503599627370496 Bool.false 370215293534 2549 

noncomputable def Ns384p596 := Ns384p595 558195838 48 94906264 8 589812974 48 89478488 8 Bool.true 632399232 115029 Bool.true 145645378 Bool.true 153497129 14148475504056880 1 Bool.false 138603890 Bool.true Bool.false 225731861 Bool.false Bool.true 606159151 

noncomputable def Ns384p597 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 733748 1000 41 30 268435456 134217728 4503599627370496 Bool.false 370215293534 2549 

noncomputable def Ns384p598 := Ns384p597 480971758 48 109588312 8 522351262 48 101459064 8 Bool.true 621451916 85315 Bool.false 15273486 Bool.true 409177407 14148475504056880 1 Bool.false 15265246 Bool.true Bool.false 12475525 Bool.true Bool.true 632399232 

noncomputable def Ns384p599 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 733748 1000 230 126 268435456 134217728 4503599627370496 Bool.false 370215293534 2549 

noncomputable def Ns384p600 := Ns384p599 372130544 47 134217720 8 432030192 47 120047984 16 Bool.true 403506940 50206 Bool.false 184042633 Bool.false 85168252 14148475504056880 1 Bool.false 207777514 Bool.true Bool.false 255037474 Bool.true Bool.true 621451916 

noncomputable def Ns384p601 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 733748 1000 554 364 268435456 134217728 4503599627370496 Bool.false 370215293534 2549 

noncomputable def Ns384p602 := Ns384p601 186065264 47 189812528 16 294906480 47 154981288 8 Bool.true 268435440 2607 Bool.false 92062944 Bool.false 344949758 14148475504056880 1 Bool.false 252802584 Bool.true Bool.false 75667960 Bool.false Bool.true 403506940 

noncomputable def Ns384p603 := nat_lit 53245021828906307547934784032305731010170307744119039 

noncomputable def Ns384p604 := nat_lit 38606864610915195757584914214987558553118991974400 

noncomputable def Ns384p605 := nat_lit 102088400796930585813605743984640000 

noncomputable def Ns384p606 := nat_lit 449443056840859304154116127348825784320 

noncomputable abbrev qz624 := (@Eq.refl Real qz728)

noncomputable abbrev qz435 := qz624

noncomputable abbrev qz99 := qz435

noncomputable def Ns384p607 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz96 733748 1000 2153545510016 16000000 1467496 4000 2000 Ns384p605 Ns384p606 qz99 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns384p608 := nat_lit 558314520092672603433832641014590141997203406130973654384640 

noncomputable abbrev qz625 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1467496))))

noncomputable abbrev qz436 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 733748 4000) (Real.log (Enclosure.sfrac Bool.false 2153545510016 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz625))

noncomputable abbrev qz626 := (Enclosure.sfrac Bool.false 733748 2000)

noncomputable abbrev qz100 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz436 qz626) (@HMul.hMul Real Real Real qz349 qz626 (Real.log Real.pi)))

noncomputable def Ns384p609 := @Enclosure.Real.IsNear.addLit_ft_p qz100 (Enclosure.sfrac Bool.true Ns384p605 Ns384p606) 1242236593819313926927 900719925474099200 87469905547234289 9216000000000000000000 Ns384p605 Ns384p606 0 1 Ns384p608 

noncomputable def Ns384p610 := nat_lit 104206358288054473619312476160000 

noncomputable abbrev qz101 := (@HSub.hSub Real Real Real qz355 qz436 qz626)

noncomputable def Ns384p611 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (@HMul.hMul Real Real Real qz5 qz626 (Real.log Real.pi)) 8102567049544236023627 4503599627370496000 18109096064743 4500000000000000000 7045954765557 16777216000 183437 33554432000 Ns384p610 1242236593819313926927 900719925474099200 

noncomputable def Ns384p612 := nat_lit 16205134099088472047254000 

noncomputable abbrev qz102 := qz436

noncomputable def Ns384p613 := @Enclosure.Real.IsNear.subLit_ff_p qz102 qz626 9754820659236159373131 4503599627370496000 18109096064743 4500000000000000000 733748 2000 0 1 Ns384p612 8102567049544236023627 4503599627370496000 18109096064743 4500000000000000000 

noncomputable def Ns384p614 := nat_lit 21965903343000991746354842762622271488 

noncomputable def Ns384p615 := nat_lit 57109836510167083738202112 

noncomputable def Ns384p616 := nat_lit 54205287964968667260960768 

noncomputable def Ns384p617 := BSN.log_dyadic_bound 56393510016 4250697510016 2 1 Ns384p616 134217728 46080000 3180227971924692320256 3180227971924692320256 3561510 4307091020032 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 56393510016) (BSN.artanhQ 4250697510016) 0 1 3180227971924692320256 Ns384p616 3180227971924692320256 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz437 := (Real.log (Enclosure.sfrac Bool.false 2153545510016 16000000))

noncomputable def Ns384p618 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 733748 4000) qz437 733748 4000 0 1 53187679974517863 4503599627370496 195312653 9000000000000000 9756588451485633235131 4503599627370496000 35827567128361 9000000000000000000 (Enclosure.Real.IsNear.const Bool.false 733748 4000) (BSN.isNear_log_sfrac 2153545510016 16000000 53187679974517863 4503599627370496 195312653 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2153545510016) qz358)) Bool.false Ns384p615 Ns384p98 1000000783360000 46080000000000000000000 53187679974517863 4503599627370496 195312653 9000000000000000 (BSN.log_rat_reduce_isNear 2153545510016 16000000 17 4307091020032 4194304000000 3561510 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns384p617 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns384p619 := BSN.arctan_dyadic_bound_f 1000 1467496 1 0 16777216 5760000 0 1 1 0 1 1 11432 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1467496) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1467496) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz438 := (@Nat.cast Real Real.instNatCast 1467496)

noncomputable def Ns384p620 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz438)) 884279719003555 562949953421312 1 2000000000000000 11432 16777216 1 5760000 14829316206274434564096 883896124736931 562949953421312 3125000009 18000000000000000 qz15 (Ns384p619 rfl) rfl rfl 

noncomputable abbrev qz439 := (@HMul.hMul Real Real Real qz579 qz584 qz625)

noncomputable abbrev qz103 := qz439

noncomputable abbrev qz440 := qz625

noncomputable abbrev qz104 := qz440

noncomputable def Ns384p621 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 733748 4000) qz437) qz103 9756588451485633235131 4503599627370496000 35827567128361 9000000000000000000 883896124736931 2251799813685248 3125000009 72000000000000000 Ns384p614 9754820659236159373131 4503599627370496000 18109096064743 4500000000000000000 (Ns384p618 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz104 1 4 0 1 883896124736931 562949953421312 3125000009 18000000000000000 883896124736931 2251799813685248 3125000009 72000000000000000 qz366 Ns384p620 rfl) 

noncomputable def Ns384p622 := @Ns384p609 Ns384p603 Ns384p604 87469905547234289 9216000000000000000000 (@Ns384p611 87469905547234289 9216000000000000000000 (Ns384p613 (Ns384p621 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 733748 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz626 (Real.log Real.pi) 733748 2000 0 1 38410761 33554432 1 67108864 7045954765557 16777216000 183437 33554432000 (Enclosure.Real.IsNear.const Bool.false 733748 2000) RS385to396.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns384p605 Ns384p606) 

noncomputable def Ns384p623 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz96) Bool.false Ns384p603 Ns384p604 87469905547234289 9216000000000000000000 46276911691 33554432 5 524288 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz96) (@HAdd.hAdd Real Real Real qz367 qz100 (Enclosure.sfrac Bool.true Ns384p605 Ns384p606)) Bool.false Ns384p603 Ns384p604 87469905547234289 9216000000000000000000 Ns384p607 (Ns384p622 rfl rfl)) 

noncomputable def Ns384p624 := BSN.cos_dyadic_bound_f 18306605 68719476736 1 0 33554432 11531251 0 1 1 0 1 1 33554430 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 18306605) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 18306605) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns384p625 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz96) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46276911691) qz378) Bool.false 46276911691 33554432 5 524288 Bool.true 33554430 33554432 1 5760000 (Ns384p623 rfl) (Enclosure.sfrac_false_div 46276911691 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46276911691) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1288212828109901135872) qz380) 226375608064910080 72057594037927936 Bool.false 33554430 33554432 219 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q2 46276911691 33554432 226375608064910080 72057594037927936 219 1288212828109901135872 Ns384p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554430 33554432 1288212828109901135872 Ns384p98 18306605 68719476736 11531251 11520000 (Ns384p624 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p626 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz96) Bool.false Ns384p603 Ns384p604 87469905547234289 9216000000000000000000 370215293534 268435456 2549 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz96) (@HAdd.hAdd Real Real Real qz367 qz100 (Enclosure.sfrac Bool.true Ns384p605 Ns384p606)) Bool.false Ns384p603 Ns384p604 87469905547234289 9216000000000000000000 Ns384p607 (Ns384p622 rfl rfl)) 

noncomputable def Ns384p627 := Ns384p602 50206 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 554 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 252802584 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 364 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 75667960 268435456) qz99 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 1) Bool.true 16777215 16777216 28637 2949120000 268435440 268435456 2607 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz96)) Bool.true 16777215 16777216 28637 2949120000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz96) qz96) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz96)) Bool.true 33554430 33554432 29324288 3019898880000 16777215 16777216 28637 2949120000 (Ns384p625 rfl rfl) rfl)) rfl) (Ns384p626 rfl) RS385to396.d7 

noncomputable def Ns384p628 := nat_lit 626630900933054899600154025516514575218811951084496052890057253584896 

noncomputable def Ns384p629 := nat_lit 5160346566372741847635624040324314132827936711205244782841430016 

noncomputable def Ns384p630 := nat_lit 1879882382106031953316766805301463077028170197380065748180606077894656 

noncomputable def Ns384p631 := BSN.cos_dyadic_bound_f 92062944 268435456 3 2 268435456 134217728 Ns384p628 Ns384p117 Ns384p629 Ns384p630 Ns384p120 Ns384p629 252802584 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 92062944) qz370 0 2 Ns384p628 Ns384p117 Ns384p629 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 92062944) qz371 0 2 Ns384p630 Ns384p120 Ns384p629 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p632 := nat_lit 7630845104284870488103183299975019517492684102700058035956975746665215484182586728284700809597405955327266816 

noncomputable def Ns384p633 := nat_lit 2838377367643959046453128366754588645859066646225012718366971928138093166060840844443306647023664500736 

noncomputable def Ns384p634 := nat_lit 46243766403580350475263805958036282278558645948561903153602461559728503179021352029355752509697274825213480960 

noncomputable def Ns384p635 := BSN.cos_dyadic_bound_f 344949758 268435456 4 3 268435456 134217728 Ns384p632 Ns384p149 Ns384p633 Ns384p634 Ns384p152 Ns384p633 75667960 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 344949758) qz370 0 3 Ns384p632 Ns384p149 Ns384p633 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 344949758) qz371 0 3 Ns384p634 Ns384p152 Ns384p633 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p636 := nat_lit 10009206837193242808991730347961156196126584494272374968671144956582721 

noncomputable def Ns384p637 := nat_lit 1316277636933601214410086897896699465522341317702051417545555499841 

noncomputable def Ns384p638 := nat_lit 30024987956305861224546370870087675189448708800181720803178343758748481 

noncomputable def Ns384p639 := BSN.cos_dyadic_bound_f 184042633 268435456 3 2 268435456 134217728 Ns384p636 Ns384p117 Ns384p637 Ns384p638 Ns384p120 Ns384p637 207777514 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 184042633) qz370 0 2 Ns384p636 Ns384p117 Ns384p637 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 184042633) qz371 0 2 Ns384p638 Ns384p120 Ns384p637 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p640 := nat_lit 458967940957037547425755037224645620987338560780078229938748207988736 

noncomputable def Ns384p641 := nat_lit 2768355571340935693838690079566372191215821374153677758760288256 

noncomputable def Ns384p642 := nat_lit 1376898286159969960405877434293777730217633250697486382460727103389696 

noncomputable def Ns384p643 := BSN.cos_dyadic_bound_f 85168252 268435456 3 2 268435456 134217728 Ns384p640 Ns384p117 Ns384p641 Ns384p642 Ns384p120 Ns384p641 255037474 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 85168252) qz370 0 2 Ns384p640 Ns384p117 Ns384p641 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 85168252) qz371 0 2 Ns384p642 Ns384p120 Ns384p641 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p644 := Ns384p600 85315 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 230 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 207777514 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 126 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 255037474 268435456) qz99 rfl rfl (Ns384p627 RS385to396.d9 RS385to396.d11 RS385to396.d13 RS385to396.d17 (Ns384p631 rfl rfl) (Ns384p635 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns384p626 rfl) RS385to396.d19 RS385to396.d21 RS385to396.d23 RS385to396.d25 RS385to396.d17 (Ns384p639 rfl rfl) (Ns384p643 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns384p645 := nat_lit 54419266610126100681304102416 

noncomputable def Ns384p646 := BSN.sin_dyadic_bound_f 15273486 268435456 2 1 268435456 134217728 Ns384p645 Ns384p127 Ns384p645 Ns384p645 Ns384p128 Ns384p645 15265246 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 15273486) qz372 0 1 Ns384p645 Ns384p127 Ns384p645 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 15273486) qz373 0 1 Ns384p645 Ns384p128 Ns384p645 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p647 := nat_lit 15131616738794794150510096965551383759761109580456237999207543728234843853554145896401138853791100434716852481 

noncomputable def Ns384p648 := nat_lit 22026208713960099081136301333697875740745923151978601486806878702723163953576458779355732892075885625601 

noncomputable def Ns384p649 := nat_lit 91602330819808248938488777150101077017140719519479540664875043841552839913203541639599663276627475615871172865 

noncomputable def Ns384p650 := BSN.cos_dyadic_bound_f 409177407 268435456 4 3 268435456 134217728 Ns384p647 Ns384p149 Ns384p648 Ns384p649 Ns384p152 Ns384p648 12475525 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 409177407) qz370 0 3 Ns384p647 Ns384p149 Ns384p648 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 409177407) qz371 0 3 Ns384p649 Ns384p152 Ns384p648 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p651 := Ns384p598 115029 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 15265246 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 12475525 268435456) qz99 rfl rfl (Ns384p644 rfl rfl) (Ns384p626 rfl) RS385to396.d27 RS385to396.d29 RS385to396.d31 RS385to396.d33 RS385to396.d17 (Ns384p646 rfl rfl) (Ns384p650 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p652 := nat_lit 7065462164225755617088019640492658375662434117752182850846330859618560 

noncomputable def Ns384p653 := nat_lit 202476048277730371405506879435085091629233361710536644239622471936 

noncomputable def Ns384p654 := nat_lit 18504454040322624576533966333009305608015165835336757073840192862617856 

noncomputable def Ns384p655 := BSN.sin_dyadic_bound_f 145645378 268435456 3 2 268435456 134217728 Ns384p652 Ns384p131 Ns384p653 Ns384p654 Ns384p134 Ns384p653 138603890 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 145645378) qz372 0 2 Ns384p652 Ns384p131 Ns384p653 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 145645378) qz373 0 2 Ns384p654 Ns384p134 Ns384p653 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p656 := nat_lit 4842810343659182145121984464111539520973903383433242193074952217931841 

noncomputable def Ns384p657 := nat_lit 308178299895762144481443555899627398004179591044171231550981124161 

noncomputable def Ns384p658 := nat_lit 14527814674377754911076990505222819308125701791117638236761754691547201 

noncomputable def Ns384p659 := BSN.cos_dyadic_bound_f 153497129 268435456 3 2 268435456 134217728 Ns384p656 Ns384p117 Ns384p657 Ns384p658 Ns384p120 Ns384p657 225731861 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 153497129) qz370 0 2 Ns384p656 Ns384p117 Ns384p657 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 153497129) qz371 0 2 Ns384p658 Ns384p120 Ns384p657 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p660 := Ns384p596 140992 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 93 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 138603890 268435456) BSN.abs_quadSignPos qz590 (BSN.sfrac_eq_quadSignPos_mul Bool.false 225731861 268435456) qz99 rfl rfl (Ns384p651 rfl) (Ns384p626 rfl) RS385to396.d35 RS385to396.d37 RS385to396.d39 RS385to396.d41 RS385to396.d17 (Ns384p655 rfl rfl) (Ns384p659 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p661 := nat_lit 56132266292769555413954110134826380207115051024502321822710656002798625 

noncomputable def Ns384p662 := nat_lit 12774527811541084913988663153664090734311641487989713971309010859041 

noncomputable def Ns384p663 := nat_lit 146992395816987292899066687755629825347921962406525526189241027323081761 

noncomputable def Ns384p664 := BSN.sin_dyadic_bound_f 244508019 268435456 3 2 268435456 134217728 Ns384p661 Ns384p131 Ns384p662 Ns384p663 Ns384p134 Ns384p662 212072955 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 244508019) qz372 0 2 Ns384p661 Ns384p131 Ns384p662 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 244508019) qz373 0 2 Ns384p663 Ns384p134 Ns384p662 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p665 := Ns384p594 Bool.true 606159151 140992 Bool.true 244508019 14148475504056880 1 Bool.false 212072955 Bool.true Bool.true 673222508 152946 BSN.abs_quadSignNeg qz374 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 212072955 268435456) qz99 rfl (Ns384p660 rfl) (Ns384p626 rfl) RS385to396.d43 RS385to396.d45 RS385to396.d17 (Ns384p664 rfl rfl) rfl 

noncomputable def Ns384p666 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) 673222508 268435456 152946 268435456 673222508 268435456 152946 268435456 361433581848887296 168305627 33554432 76473 67108864 (Ns384p665 rfl rfl rfl rfl) 

noncomputable def Ns384p667 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz97) (Zeta.RiemannSiegel.correction qz98) 2551809 8388608 1 16777216 158927225849377 281474976710656 96308977083649 1583296743997440000 405551925267472872993 2361183241434822606848 

noncomputable def Ns384p668 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz97 1 1 0 1 2551809 8388608 1 16777216 2551809 8388608 1 16777216 

noncomputable abbrev qz105 := qz433

noncomputable def Ns384p669 := @Enclosure.Real.IsNear.sqrt_image qz105 979618333261 8388608000 183437 8388608000 181302318 181302353 16777216 (@Enclosure.Real.IsNear.of_eq qz105 (@HMul.hMul Real Real Real qz5 qz96 qz3) Bool.false 979618333261 8388608000 183437 8388608000 (BSN.t_div_two_pi_mk qz96 733748 1000 qz99) (@Enclosure.Real.IsNear.mulLit_ff qz96 qz3 733748 1000 0 1 5340353 33554432 1 33554432 979618333261 8388608000 183437 8388608000 (Enclosure.Real.IsNear.const Bool.false 733748 1000) RS385to396.d48 rfl)) 

noncomputable abbrev qz731 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 733748 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz627 := qz731

noncomputable abbrev qz441 := qz627

noncomputable abbrev qz106 := qz441

noncomputable def Ns384p670 := @Enclosure.Real.IsNear.sqrt_image qz106 362604671 33554432 35 33554432 55152045 55152052 16777216 (@Enclosure.Real.IsNear.recentre' qz106 Bool.false 362604671 33554432 35 33554432 362604671 33554432 35 33554432 (Ns384p669 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns384p671 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz106) 110304097 33554432 7 33554432 5103617 5103619 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz106) Bool.false 110304097 33554432 7 33554432 110304097 33554432 7 33554432 (Ns384p670 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns384p672 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz106)) Bool.false 10207236 33554432 2 33554432 2551809 8388608 1 16777216 (Ns384p671 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz107 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz434))

noncomputable abbrev qz628 := (@HMul.hMul Real Real Real qz707 qz730 qz730)

noncomputable abbrev qz442 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz628 qz623) qz594)

noncomputable abbrev qz108 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz442))

noncomputable def Ns384p673 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz98) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz107) qz108) Bool.false 158927225849377 

noncomputable def Ns384p674 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz107) qz108 96597791 33554432 1881 

noncomputable def Ns384p675 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz107) Bool.false 96597791 33554432 1881 33554432 96597791 33554432 1881 

noncomputable def Ns384p676 := @Enclosure.Real.IsNear.recentre' qz107 Bool.false 11655545 33554432 1306514432 193273528320000 11655545 33554432 1275893 188743680000 

noncomputable abbrev qz109 := (@HMul.hMul Real Real Real qz349 qz346 qz434)

noncomputable def Ns384p677 := @Enclosure.Real.IsNear.cos_image qz109 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 170025199) qz378) Bool.false 170025199 33554432 221 33554432 Bool.false 11655545 33554432 1 

noncomputable def Ns384p678 := nat_lit 944512639548988236057475637 

noncomputable def Ns384p679 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz98 884279719003555 140737488355328 1 500000000000000 27060351 33554432 35 33554432 23928919578417568547805 4722366482869645213696 Ns384p678 

noncomputable def Ns384p680 := @Enclosure.Real.IsNear.subLit_ff_p qz106 qz1 362604671 33554432 35 33554432 10 1 0 1 27060351 27060351 33554432 35 

noncomputable def Ns384p681 := @Ns384p680 33554432 (@Enclosure.Real.IsNear.recentre' qz106 Bool.false 362604671 33554432 35 33554432 362604671 33554432 35 33554432 (Ns384p669 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns384p682 := @Enclosure.Real.IsNear.recentre' qz109 Bool.false 23928919578417568547805 4722366482869645213696 Ns384p678 Ns384p295 170025199 33554432 221 33554432 (@Ns384p679 Ns384p295 RS385to396.d47 (Ns384p681 rfl rfl) rfl) 

noncomputable def Ns384p683 := nat_lit 1715498689701791135694848 

noncomputable def Ns384p684 := nat_lit 353217620488849595822913445891706261331601 

noncomputable def Ns384p685 := BSN.sin_dyadic_bound_f 24378702643 68719476736 2 1 33554432 11531251 Ns384p684 Ns384p181 Ns384p684 Ns384p684 Ns384p182 Ns384p684 11655545 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 24378702643) qz368 0 1 Ns384p684 Ns384p181 Ns384p684 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 24378702643) qz369 0 1 Ns384p684 Ns384p182 Ns384p684 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p686 := @Ns384p677 5760000 (Ns384p682 rfl) (Enclosure.sfrac_false_div 170025199 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 170025199) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns384p683) qz380) 226375608064910080 72057594037927936 Bool.false 11655545 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 170025199 33554432 226375608064910080 72057594037927936 0 Ns384p683 Ns384p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 11655545 33554432 Ns384p683 Ns384p98 24378702643 68719476736 11531251 11520000 (Ns384p685 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p687 := @Enclosure.Real.IsNear.inv_image qz107 11655545 33554432 1275893 188743680000 48297955 48299836 16777216 (Ns384p676 (Ns384p686 rfl rfl) rfl) rfl 

noncomputable def Ns384p688 := @Enclosure.Real.IsNear.recentre' qz108 Bool.false 3290494 16777216 

noncomputable abbrev qz110 := (@HMul.hMul Real Real Real qz349 qz346 qz442)

noncomputable def Ns384p689 := @Enclosure.Real.IsNear.cos_image qz110 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 23041625)) qz415) Bool.true 23041625 16777216 

noncomputable def Ns384p690 := nat_lit 217621995312787310854465637725 

noncomputable def Ns384p691 := nat_lit 16562061055365563746366840160184209 

noncomputable def Ns384p692 := @Enclosure.Real.IsNear.recentre' qz110 Bool.true Ns384p690 Ns384p307 Ns384p691 

noncomputable abbrev qz111 := qz442

noncomputable def Ns384p693 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz111 884279719003555 140737488355328 1 500000000000000 246100855460095 

noncomputable abbrev qz443 := (@HSub.hSub Real Real Real qz583 qz628 qz623)

noncomputable abbrev qz112 := qz443

noncomputable def Ns384p694 := @Enclosure.Real.IsNear.subLit_tf qz112 qz29 175732111282431 1125899906842624 3068630915 1125899906842624 1 16 

noncomputable abbrev qz444 := qz628

noncomputable abbrev qz113 := qz444

noncomputable def Ns384p695 := @Enclosure.Real.IsNear.subLit_ff_n qz113 qz98 732262596243201 1125899906842624 1894225795 1125899906842624 27060351 33554432 35 33554432 

noncomputable def Ns384p696 := @Enclosure.Real.IsNear.mulLit_ff qz98 qz98 27060351 33554432 35 33554432 27060351 33554432 35 33554432 732262596243201 1125899906842624 

noncomputable def Ns384p697 := nat_lit 35388023972153391050302681731826912835002564529954576020092868554871169240438171121832275390625 

noncomputable def Ns384p698 := nat_lit 22395318899992196372910137063140697293293090421021248345294183833175338804721832275390625 

noncomputable def Ns384p699 := nat_lit 214384777682805647934347022617607657924952618401041530316102566325575943970274960881832275390625 

noncomputable def Ns384p700 := BSN.cos_dyadic_bound_f 23041625 16777216 4 3 16777216 5760000 Ns384p697 Ns384p469 Ns384p698 Ns384p699 Ns384p472 Ns384p698 3290494 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 23041625) (BSN.cosEvenQ 16777216) 0 3 Ns384p697 Ns384p469 Ns384p698 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 23041625) (BSN.cosOddQ 16777216) 0 3 Ns384p699 Ns384p472 Ns384p698 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p701 := @Ns384p688 3345554432 193273528320000 1645247 8388608 3267143 188743680000 (@Ns384p689 575 33554432 Bool.false 3290494 16777216 1 5760000 (@Ns384p692 Ns384p310 23041625 16777216 575 33554432 (@Ns384p693 1125899906842624 3068630915 1125899906842624 Ns384p690 Ns384p307 Ns384p691 Ns384p310 RS385to396.d47 (@Ns384p694 0 1 3937613687361520 246100855460095 1125899906842624 3068630915 1125899906842624 (@Ns384p695 5896591178242763784192 175732111282431 1125899906842624 3068630915 1125899906842624 (@Ns384p696 1894225795 1125899906842624 (Ns384p681 rfl rfl) (Ns384p681 rfl rfl) rfl) (Ns384p681 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 23041625 16777216) (BSN.cos_neg_of_bound 23041625 16777216 Bool.false 3290494 16777216 1 5760000 (Ns384p700 rfl rfl)) rfl rfl) 

noncomputable def Ns384p702 := @Ns384p667 123104572740019592839 Ns384p591 (Ns384p668 qz31 (@Enclosure.Real.IsNear.of_eq qz97 (@Inv.inv Real Real.instInv (Real.sqrt qz106)) Bool.false 2551809 8388608 1 16777216 (BSN.rpow_neg_quarter_mk qz105 (BSN.t_div_two_pi_nonneg qz96 733748 1000 qz99)) Ns384p672) rfl) (@Ns384p673 281474976710656 96308977083649 1583296743997440000 (BSN.correction_mk qz98 (BSN.cos_two_pi_p_ne_zero_mk qz96 733748 1000 10 qz99 rfl rfl (@BSN.floor_sqrt_eq_dec qz96 733748 1000 10 qz99 rfl rfl rfl))) (@Ns384p674 33554432 1645247 8388608 3267143 188743680000 158927225849377 281474976710656 96308977083649 1583296743997440000 (@Ns384p675 33554432 (Ns384p687 rfl rfl rfl rfl rfl) rfl) (Ns384p701 rfl) rfl)) 

noncomputable def Ns384p703 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz96) (hardyZApproximantRS₀ qz96) Bool.true 12249007535291811788321 2361183241434822606848 7690570316722283912839 Ns384p591 (@Eq.refl Real (hardyZApproximantRS₀ qz96)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz96) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz97) (Zeta.RiemannSiegel.correction qz98))) Bool.true 12249007535291811788321 2361183241434822606848 7690570316722283912839 Ns384p591 (BSN.hardyZApproximantRS₀_eq qz96 10 (@BSN.floor_sqrt_eq_dec qz96 733748 1000 10 qz99 rfl rfl rfl)) (@Ns384p593 12249007535291811788321 2361183241434822606848 7690570316722283912839 Ns384p591 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 10)) Bool.true 168305627 33554432 76473 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (Ns384p666 (Ns384p665 rfl rfl rfl rfl) rfl rfl)) (Ns384p702 rfl) rfl rfl)) 

theorem RS385to396.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz96) Bool.true 12249007535291811788321 2361183241434822606848 7690570316722283912839 Ns384p591 := Ns384p703 

noncomputable def Ns384p704 := nat_lit 2951479051793528258560000 

noncomputable def Ns384p705 := nat_lit 702148437026426067830861463552 

noncomputable abbrev qz732 := (Enclosure.sfrac Bool.false 735068 1000)

noncomputable abbrev qz629 := qz732

noncomputable abbrev qz445 := qz629

noncomputable abbrev qz114 := qz445

noncomputable abbrev qz733 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 735068 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz630 := qz733

noncomputable abbrev qz446 := qz630

noncomputable abbrev qz115 := (@HPow.hPow Real Real Real qz350 qz446 qz352)

noncomputable abbrev qz734 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 735068 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz631 := qz734

noncomputable abbrev qz447 := qz631

noncomputable abbrev qz116 := qz447

noncomputable def Ns384p706 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz115) (Zeta.RiemannSiegel.correction qz116)) 172252137 134217728 153213 134217728 829169760234983359725 4722366482869645213696 47569917243718379091 Ns384p704 Ns384p705 

noncomputable def Ns384p707 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.sin BSN.quadSignNeg 9 10 735068 1000 197 268435456 134217728 4503599627370496 Bool.false 371058820861 2553 618095470 48 84886744 8 

noncomputable def Ns384p708 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 735068 1000 93 148 268435456 134217728 4503599627370496 Bool.false 371058820861 2553 

noncomputable def Ns384p709 := Ns384p708 558195838 48 94906264 8 589812974 48 89478488 8 Bool.false 162671899 115229 Bool.true 38936557 Bool.true 88522927 14148475504056880 1 Bool.false 38800166 Bool.true Bool.false 253970994 Bool.false Bool.false 233610969 

noncomputable def Ns384p710 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 735068 1000 41 30 268435456 134217728 4503599627370496 Bool.false 371058820861 2553 

noncomputable def Ns384p711 := Ns384p710 480971758 48 109588312 8 522351262 48 101459064 8 Bool.false 302821464 85462 Bool.false 223918092 Bool.true 255153746 14148475504056880 1 Bool.false 198838837 Bool.true Bool.false 156030414 Bool.true Bool.false 162671899 

noncomputable def Ns384p712 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 735068 1000 231 126 268435456 134217728 4503599627370496 Bool.false 371058820861 2553 

noncomputable def Ns384p713 := Ns384p712 372130544 47 134217720 8 432030192 47 120047984 16 Bool.false 275222284 50291 Bool.false 114700214 Bool.false 358415726 14148475504056880 1 Bool.false 111241646 Bool.false Bool.false 62658291 Bool.true Bool.false 302821464 

noncomputable def Ns384p714 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 735068 1000 555 365 268435456 134217728 4503599627370496 Bool.false 371058820861 2553 

noncomputable def Ns384p715 := Ns384p714 186065264 47 189812528 16 294906480 47 154981288 8 Bool.false 268435304 2607 Bool.false 268326695 Bool.false 377543103 14148475504056880 1 Bool.false 225821865 Bool.false Bool.false 264818762 Bool.true Bool.false 275222284 

noncomputable def Ns384p716 := nat_lit 269724834009524700209760931732288723801320996260071501 

noncomputable def Ns384p717 := nat_lit 195127307966559886100029927505945166533206474752000 

noncomputable def Ns384p718 := nat_lit 103009986601489258279272480112640000 

noncomputable def Ns384p719 := nat_lit 454316167083009812282468023490964357120 

noncomputable abbrev qz632 := (@Eq.refl Real qz732)

noncomputable abbrev qz448 := qz632

noncomputable abbrev qz117 := qz448

noncomputable def Ns384p720 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz114 735068 1000 2161300858496 16000000 1470136 4000 2000 Ns384p718 Ns384p719 qz117 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns384p721 := nat_lit 2828269875463713720471502787521163808486939649744007342325760 

noncomputable abbrev qz633 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1470136))))

noncomputable abbrev qz449 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 735068 4000) (Real.log (Enclosure.sfrac Bool.false 2161300858496 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz633))

noncomputable abbrev qz634 := (Enclosure.sfrac Bool.false 735068 2000)

noncomputable abbrev qz118 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz449 qz634) (@HMul.hMul Real Real Real qz349 qz634 (Real.log Real.pi)))

noncomputable def Ns384p722 := @Enclosure.Real.IsNear.addLit_ft_p qz118 (Enclosure.sfrac Bool.true Ns384p718 Ns384p719) 6225335007421576313873 4503599627370496000 87626542805967299 9216000000000000000000 Ns384p718 Ns384p719 0 1 Ns384p721 

noncomputable def Ns384p723 := nat_lit 20888758018374677775666223513600 

noncomputable abbrev qz119 := (@HSub.hSub Real Real Real qz355 qz449 qz634)

noncomputable def Ns384p724 := @Enclosure.Real.IsNear.subLit_ff_p qz119 (@HMul.hMul Real Real Real qz5 qz634 (Real.log Real.pi)) 1624024331043375113629 900719925474099200 2267665331561 562500000000000000 7058630316687 16777216000 183767 33554432000 Ns384p723 6225335007421576313873 4503599627370496000 

noncomputable def Ns384p725 := nat_lit 16240243310433751136290000 

noncomputable abbrev qz120 := qz449

noncomputable def Ns384p726 := @Enclosure.Real.IsNear.subLit_ff_p qz120 qz634 9775347640662863445009 4503599627370496000 2267665331561 562500000000000000 735068 2000 0 1 Ns384p725 1624024331043375113629 900719925474099200 2267665331561 562500000000000000 

noncomputable def Ns384p727 := nat_lit 22012125995953164521584747833282527232 

noncomputable def Ns384p728 := nat_lit 57127219576066402416590848 

noncomputable def Ns384p729 := nat_lit 54403262244098260198146048 

noncomputable def Ns384p730 := BSN.log_dyadic_bound 64148858496 4258452858496 2 1 Ns384p729 134217728 46080000 4115076046339831382016 4115076046339831382016 4043987 4322601716992 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 64148858496) (BSN.artanhQ 4258452858496) 0 1 4115076046339831382016 Ns384p729 4115076046339831382016 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz450 := (Real.log (Enclosure.sfrac Bool.false 2161300858496 16000000))

noncomputable def Ns384p731 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 735068 4000) qz450 735068 4000 0 1 53203869216205927 4503599627370496 195312653 9000000000000000 9777115434254514587009 4503599627370496000 35892020303851 9000000000000000000 (Enclosure.Real.IsNear.const Bool.false 735068 4000) (BSN.isNear_log_sfrac 2161300858496 16000000 53203869216205927 4503599627370496 195312653 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2161300858496) qz358)) Bool.false Ns384p728 Ns384p98 1000000783360000 46080000000000000000000 53203869216205927 4503599627370496 195312653 9000000000000000 (BSN.log_rat_reduce_isNear 2161300858496 16000000 17 4322601716992 4194304000000 4043987 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns384p730 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns384p732 := BSN.arctan_dyadic_bound_f 1000 1470136 1 0 16777216 5760000 0 1 1 0 1 1 11412 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1470136) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1470136) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz451 := (@Nat.cast Real Real.instNatCast 1470136)

noncomputable def Ns384p733 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz451)) 884279719003555 562949953421312 1 2000000000000000 11412 16777216 1 5760000 14829327465273502990336 883896795825571 562949953421312 3125000009 18000000000000000 qz15 (Ns384p732 rfl) rfl rfl 

noncomputable abbrev qz452 := (@HMul.hMul Real Real Real qz579 qz584 qz633)

noncomputable abbrev qz121 := qz452

noncomputable abbrev qz453 := qz633

noncomputable abbrev qz122 := qz453

noncomputable def Ns384p734 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 735068 4000) qz450) qz121 9777115434254514587009 4503599627370496000 35892020303851 9000000000000000000 883896795825571 2251799813685248 3125000009 72000000000000000 Ns384p727 9775347640662863445009 4503599627370496000 2267665331561 562500000000000000 (Ns384p731 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz122 1 4 0 1 883896795825571 562949953421312 3125000009 18000000000000000 883896795825571 2251799813685248 3125000009 72000000000000000 qz366 Ns384p733 rfl) 

noncomputable def Ns384p735 := @Ns384p722 Ns384p716 Ns384p717 87626542805967299 9216000000000000000000 (@Ns384p724 87626542805967299 9216000000000000000000 (Ns384p726 (Ns384p734 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 735068 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz634 (Real.log Real.pi) 735068 2000 0 1 38410761 33554432 1 67108864 7058630316687 16777216000 183767 33554432000 (Enclosure.Real.IsNear.const Bool.false 735068 2000) RS385to396.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns384p718 Ns384p719) 

noncomputable def Ns384p736 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz114) Bool.false Ns384p716 Ns384p717 87626542805967299 9216000000000000000000 46382352607 33554432 5 524288 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz114) (@HAdd.hAdd Real Real Real qz367 qz118 (Enclosure.sfrac Bool.true Ns384p718 Ns384p719)) Bool.false Ns384p716 Ns384p717 87626542805967299 9216000000000000000000 Ns384p720 (Ns384p735 rfl rfl)) 

noncomputable def Ns384p737 := BSN.cos_dyadic_bound_f 72699300 68719476736 1 0 33554432 11531251 0 1 1 0 1 1 33554413 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 72699300) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 72699300) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns384p738 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz114) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46382352607) qz378) Bool.false 46382352607 33554432 5 524288 Bool.false 33554413 33554432 1 5760000 (Ns384p736 rfl) (Enclosure.sfrac_false_div 46382352607 33554432) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46382352607) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5115758513276797845504) qz380) 226375608064910080 72057594037927936 Bool.false 33554413 33554432 220 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q0 46382352607 33554432 226375608064910080 72057594037927936 220 5115758513276797845504 Ns384p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554413 33554432 5115758513276797845504 Ns384p98 72699300 68719476736 11531251 11520000 (Ns384p737 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p739 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz114) Bool.false Ns384p716 Ns384p717 87626542805967299 9216000000000000000000 371058820861 268435456 2553 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz114) (@HAdd.hAdd Real Real Real qz367 qz118 (Enclosure.sfrac Bool.true Ns384p718 Ns384p719)) Bool.false Ns384p716 Ns384p717 87626542805967299 9216000000000000000000 Ns384p720 (Ns384p735 rfl rfl)) 

noncomputable def Ns384p740 := Ns384p715 50291 BSN.abs_quadSignPos (BSN.cos_quad_nat3 555 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 225821865 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 365 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 264818762 268435456) qz117 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 1) Bool.false 33554413 33554432 28637 2949120000 268435304 268435456 2607 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz114)) Bool.false 33554413 33554432 28637 2949120000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz114) qz114) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz114)) Bool.false 33554413 33554432 29324288 3019898880000 33554413 33554432 28637 2949120000 (Ns384p738 rfl rfl) rfl)) rfl) (Ns384p739 rfl) RS385to396.d7 

noncomputable def Ns384p741 := nat_lit 81421703910145242818293051447453529919467923296180643661693948154930625 

noncomputable def Ns384p742 := nat_lit 26872684393119914584960317264601897806519253699540676488785187890625 

noncomputable def Ns384p743 := nat_lit 213203811608982013233820437086807032430729244126864334209168973911090625 

noncomputable def Ns384p744 := BSN.sin_dyadic_bound_f 268326695 268435456 3 2 268435456 134217728 Ns384p741 Ns384p131 Ns384p742 Ns384p743 Ns384p134 Ns384p742 225821865 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 268326695) qz372 0 2 Ns384p741 Ns384p131 Ns384p742 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 268326695) qz373 0 2 Ns384p743 Ns384p134 Ns384p742 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p745 := nat_lit 28460727190581355107163149168885788227406822639564120951025930415129221023800261592029775041564141015325469441 

noncomputable def Ns384p746 := nat_lit 8386842575961425896767327917097716171353710281053746362818250695572964812646428852828397875142541699841 

noncomputable def Ns384p747 := nat_lit 142189919449641615434329428836951609486334942022811104625967891418645004947434883927370069007430322984020601601 

noncomputable def Ns384p748 := BSN.sin_dyadic_bound_f 377543103 268435456 4 3 268435456 134217728 Ns384p745 Ns384p156 Ns384p746 Ns384p747 Ns384p159 Ns384p746 264818762 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 377543103) qz372 0 3 Ns384p745 Ns384p156 Ns384p746 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 377543103) qz373 0 3 Ns384p747 Ns384p159 Ns384p746 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p749 := nat_lit 173083995798730670282239924473616 

noncomputable def Ns384p750 := BSN.sin_dyadic_bound_f 114700214 268435456 2 1 268435456 134217728 Ns384p749 Ns384p127 Ns384p749 Ns384p749 Ns384p128 Ns384p749 111241646 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 114700214) qz372 0 1 Ns384p749 Ns384p127 Ns384p749 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 114700214) qz373 0 1 Ns384p749 Ns384p128 Ns384p749 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p751 := nat_lit 8896394385712776396834924339104713427273114159151193485712358971621429229869845392029952517856657819075219456 

noncomputable def Ns384p752 := nat_lit 4494120163310283394139493508022766811370562571634111496506186404945589304792884345050651037940215320576 

noncomputable def Ns384p753 := nat_lit 53903495605116891098441071836823873154325612813113755366735829811963176531336173396516218067346025350394941440 

noncomputable def Ns384p754 := BSN.cos_dyadic_bound_f 358415726 268435456 4 3 268435456 134217728 Ns384p751 Ns384p149 Ns384p752 Ns384p753 Ns384p152 Ns384p752 62658291 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 358415726) qz370 0 3 Ns384p751 Ns384p149 Ns384p752 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 358415726) qz371 0 3 Ns384p753 Ns384p152 Ns384p752 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p755 := Ns384p713 85462 BSN.abs_quadSignPos (BSN.cos_quad_nat3 231 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 111241646 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 126 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 62658291 268435456) qz117 rfl rfl (Ns384p740 RS385to396.d9 RS385to396.d11 RS385to396.d13 RS385to396.d17 (Ns384p744 rfl rfl) (Ns384p748 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns384p739 rfl) RS385to396.d19 RS385to396.d21 RS385to396.d23 RS385to396.d25 RS385to396.d17 (Ns384p750 rfl rfl) (Ns384p754 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns384p756 := nat_lit 39479129628346068335364088574133636653142253617109926307708314073497600 

noncomputable def Ns384p757 := nat_lit 6319947620771212343766257877917919931096777147411386535554402287616 

noncomputable def Ns384p758 := nat_lit 103387488159044168439301753276642895554531745643715902846749924969742336 

noncomputable def Ns384p759 := BSN.sin_dyadic_bound_f 223918092 268435456 3 2 268435456 134217728 Ns384p756 Ns384p131 Ns384p757 Ns384p758 Ns384p134 Ns384p757 198838837 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 223918092) qz372 0 2 Ns384p756 Ns384p131 Ns384p757 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 223918092) qz373 0 2 Ns384p758 Ns384p134 Ns384p757 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p760 := nat_lit 36990274967567312992763435800605415120211226064225846524026212385833216 

noncomputable def Ns384p761 := nat_lit 17964518854129096707660082373421028280246940482771604785535787745536 

noncomputable def Ns384p762 := nat_lit 110934895864993680784874987237069403304073184311711996362507565582008576 

noncomputable def Ns384p763 := BSN.cos_dyadic_bound_f 255153746 268435456 3 2 268435456 134217728 Ns384p760 Ns384p117 Ns384p761 Ns384p762 Ns384p120 Ns384p761 156030414 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 255153746) qz370 0 2 Ns384p760 Ns384p117 Ns384p761 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 255153746) qz371 0 2 Ns384p762 Ns384p120 Ns384p761 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p764 := Ns384p711 115229 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 198838837 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 156030414 268435456) qz117 rfl rfl (Ns384p755 rfl rfl) (Ns384p739 rfl) RS385to396.d27 RS385to396.d29 RS385to396.d31 RS385to396.d33 RS385to396.d17 (Ns384p759 rfl rfl) (Ns384p763 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p765 := nat_lit 2298424191192236389812761034001 

noncomputable def Ns384p766 := BSN.sin_dyadic_bound_f 38936557 268435456 2 1 268435456 134217728 Ns384p765 Ns384p127 Ns384p765 Ns384p765 Ns384p128 Ns384p765 38800166 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 38936557) qz372 0 1 Ns384p765 Ns384p127 Ns384p765 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 38936557) qz373 0 1 Ns384p765 Ns384p128 Ns384p765 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p767 := nat_lit 535667027925108584987491975612284503236478604560063935022272590034561 

noncomputable def Ns384p768 := nat_lit 3770909616597014843765106073975484255904339988479931200570046081 

noncomputable def Ns384p769 := nat_lit 1606993541956092560932788396624705558740924005000214845204416630011521 

noncomputable def Ns384p770 := BSN.cos_dyadic_bound_f 88522927 268435456 3 2 268435456 134217728 Ns384p767 Ns384p117 Ns384p768 Ns384p769 Ns384p120 Ns384p768 253970994 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 88522927) qz370 0 2 Ns384p767 Ns384p117 Ns384p768 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 88522927) qz371 0 2 Ns384p769 Ns384p120 Ns384p768 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p771 := Ns384p709 141238 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 93 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 38800166 268435456) BSN.abs_quadSignPos qz590 (BSN.sfrac_eq_quadSignPos_mul Bool.false 253970994 268435456) qz117 rfl rfl (Ns384p764 rfl) (Ns384p739 rfl) RS385to396.d35 RS385to396.d37 RS385to396.d39 RS385to396.d41 RS385to396.d17 (Ns384p766 rfl rfl) (Ns384p770 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p772 := nat_lit 34735540226064884654073385747208496169718510314662681224607629668515840 

noncomputable def Ns384p773 := nat_lit 4892638856455856462303141727202104750397630956399646817184431210496 

noncomputable def Ns384p774 := nat_lit 90966112510116626516872281394178210370143073707329994255315969576534016 

noncomputable def Ns384p775 := BSN.sin_dyadic_bound_f 216866712 268435456 3 2 268435456 134217728 Ns384p772 Ns384p131 Ns384p773 Ns384p774 Ns384p134 Ns384p773 194033664 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 216866712) qz372 0 2 Ns384p772 Ns384p131 Ns384p773 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 216866712) qz373 0 2 Ns384p774 Ns384p134 Ns384p773 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p776 := Ns384p707 Bool.false 233610969 141238 Bool.true 216866712 14148475504056880 1 Bool.false 194033664 Bool.true Bool.false 172252137 153213 BSN.abs_quadSignNeg qz374 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 194033664 268435456) qz117 rfl (Ns384p771 rfl) (Ns384p739 rfl) RS385to396.d43 RS385to396.d45 RS385to396.d17 (Ns384p775 rfl rfl) rfl 

noncomputable def Ns384p777 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) 172252137 268435456 153213 268435456 172252137 268435456 153213 268435456 92477161885138944 172252137 134217728 153213 134217728 (Ns384p776 rfl rfl rfl rfl) 

noncomputable def Ns384p778 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz115) (Zeta.RiemannSiegel.correction qz116) 5101325 16777216 1 16777216 162540077378913 281474976710656 83745866713519 1583296743997440000 829169760234983359725 4722366482869645213696 

noncomputable def Ns384p779 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz115 1 1 0 1 5101325 16777216 1 16777216 5101325 16777216 1 16777216 

noncomputable abbrev qz123 := qz446

noncomputable def Ns384p780 := @Enclosure.Real.IsNear.sqrt_image qz123 981380649751 8388608000 183767 8388608000 181465324 181465359 16777216 (@Enclosure.Real.IsNear.of_eq qz123 (@HMul.hMul Real Real Real qz5 qz114 qz3) Bool.false 981380649751 8388608000 183767 8388608000 (BSN.t_div_two_pi_mk qz114 735068 1000 qz117) (@Enclosure.Real.IsNear.mulLit_ff qz114 qz3 735068 1000 0 1 5340353 33554432 1 33554432 981380649751 8388608000 183767 8388608000 (Enclosure.Real.IsNear.const Bool.false 735068 1000) RS385to396.d48 rfl)) 

noncomputable abbrev qz735 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 735068 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz635 := qz735

noncomputable abbrev qz454 := qz635

noncomputable abbrev qz124 := qz454

noncomputable def Ns384p781 := @Enclosure.Real.IsNear.sqrt_image qz124 362930683 33554432 35 33554432 55176833 55176839 16777216 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 362930683 33554432 35 33554432 362930683 33554432 35 33554432 (Ns384p780 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns384p782 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz124) 13794209 4194304 3 16777216 5101324 5101326 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz124) Bool.false 110353672 33554432 6 33554432 13794209 4194304 3 16777216 (Ns384p781 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns384p783 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz124)) Bool.false 10202650 33554432 2 33554432 5101325 16777216 1 16777216 (Ns384p782 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz125 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz447))

noncomputable abbrev qz636 := (@HMul.hMul Real Real Real qz707 qz734 qz734)

noncomputable abbrev qz455 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz636 qz631) qz594)

noncomputable abbrev qz126 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz455))

noncomputable def Ns384p784 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz116) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz125) qz126) Bool.false 162540077378913 

noncomputable def Ns384p785 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz125) qz126 83070891 33554432 1391 

noncomputable def Ns384p786 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz125) Bool.false 83070891 33554432 1391 33554432 83070891 33554432 1391 

noncomputable def Ns384p787 := @Enclosure.Real.IsNear.recentre' qz125 Bool.false 13553483 33554432 1306514432 193273528320000 13553483 33554432 1275893 188743680000 

noncomputable abbrev qz127 := (@HMul.hMul Real Real Real qz349 qz346 qz447)

noncomputable def Ns384p788 := @Enclosure.Real.IsNear.cos_image qz127 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 172073593) qz378) Bool.false 172073593 33554432 221 33554432 Bool.false 13553483 33554432 1 

noncomputable def Ns384p789 := nat_lit 944512639551788657813682741 

noncomputable def Ns384p790 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz116 884279719003555 140737488355328 1 500000000000000 27386363 33554432 35 33554432 24217205378169355520465 4722366482869645213696 Ns384p789 

noncomputable def Ns384p791 := @Enclosure.Real.IsNear.subLit_ff_p qz124 qz1 362930683 33554432 35 33554432 10 1 0 1 27386363 27386363 33554432 35 

noncomputable def Ns384p792 := @Ns384p791 33554432 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 362930683 33554432 35 33554432 362930683 33554432 35 33554432 (Ns384p780 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns384p793 := @Enclosure.Real.IsNear.recentre' qz127 Bool.false 24217205378169355520465 4722366482869645213696 Ns384p789 Ns384p295 172073593 33554432 221 33554432 (@Ns384p790 Ns384p295 RS385to396.d47 (Ns384p792 rfl rfl) rfl) 

noncomputable def Ns384p794 := nat_lit 2010703376265245848764416 

noncomputable def Ns384p795 := nat_lit 666611538199219935299150010885215730900625 

noncomputable def Ns384p796 := BSN.sin_dyadic_bound_f 28573813555 68719476736 2 1 33554432 11531251 Ns384p795 Ns384p181 Ns384p795 Ns384p795 Ns384p182 Ns384p795 13553483 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 28573813555) qz368 0 1 Ns384p795 Ns384p181 Ns384p795 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 28573813555) qz369 0 1 Ns384p795 Ns384p182 Ns384p795 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p797 := @Ns384p788 5760000 (Ns384p793 rfl) (Enclosure.sfrac_false_div 172073593 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 172073593) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns384p794) qz380) 226375608064910080 72057594037927936 Bool.false 13553483 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 172073593 33554432 226375608064910080 72057594037927936 0 Ns384p794 Ns384p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 13553483 33554432 Ns384p794 Ns384p98 28573813555 68719476736 11531251 11520000 (Ns384p796 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p798 := @Enclosure.Real.IsNear.inv_image qz125 13553483 33554432 1275893 188743680000 41534750 41536141 16777216 (Ns384p787 (Ns384p797 rfl rfl) rfl) rfl 

noncomputable def Ns384p799 := @Enclosure.Real.IsNear.recentre' qz126 Bool.false 3913286 16777216 

noncomputable abbrev qz128 := (@HMul.hMul Real Real Real qz349 qz346 qz455)

noncomputable def Ns384p800 := @Enclosure.Real.IsNear.cos_image qz128 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 44807841)) qz378) Bool.true 44807841 33554432 

noncomputable def Ns384p801 := nat_lit 211599047087777447417726627605 

noncomputable def Ns384p802 := nat_lit 83426150185907040245069724902621997 

noncomputable def Ns384p803 := @Enclosure.Real.IsNear.recentre' qz128 Bool.true Ns384p801 Ns384p307 Ns384p802 

noncomputable abbrev qz129 := qz455

noncomputable def Ns384p804 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz129 884279719003555 140737488355328 1 500000000000000 239289720820711 

noncomputable abbrev qz456 := (@HSub.hSub Real Real Real qz583 qz636 qz631)

noncomputable abbrev qz130 := qz456

noncomputable def Ns384p805 := @Enclosure.Real.IsNear.subLit_tf qz130 qz29 168920976643047 1125899906842624 3091451755 1125899906842624 1 16 

noncomputable abbrev qz457 := qz636

noncomputable abbrev qz131 := qz457

noncomputable def Ns384p806 := @Enclosure.Real.IsNear.subLit_ff_n qz131 qz116 750012878367769 1125899906842624 1917046635 1125899906842624 27386363 33554432 35 33554432 

noncomputable def Ns384p807 := @Enclosure.Real.IsNear.mulLit_ff qz116 qz116 27386363 33554432 35 33554432 27386363 33554432 35 33554432 750012878367769 1125899906842624 

noncomputable def Ns384p808 := nat_lit 129527627080597979104313144825571524355400885441722996280467268615917109858246625517638405681010561 

noncomputable def Ns384p809 := nat_lit 65501044117553325124974552697532869926191455296492180377582301830212121295503979114093303681 

noncomputable def Ns384p810 := nat_lit 784810897866351064264370741994145973678344876133399099898650255028052290590480000078588238337103745 

noncomputable def Ns384p811 := BSN.cos_dyadic_bound_f 44807841 33554432 4 3 16777216 5760000 Ns384p808 Ns384p316 Ns384p809 Ns384p810 Ns384p319 Ns384p809 3913286 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 44807841) (BSN.cosEvenQ 33554432) 0 3 Ns384p808 Ns384p316 Ns384p809 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 44807841) (BSN.cosOddQ 33554432) 0 3 Ns384p810 Ns384p319 Ns384p809 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p812 := @Ns384p799 843588608 48318382080000 1956643 8388608 823817 47185920000 (@Ns384p800 145 8388608 Bool.false 3913286 16777216 1 5760000 (@Ns384p803 Ns384p463 44807841 33554432 145 8388608 (@Ns384p804 1125899906842624 3091451755 1125899906842624 Ns384p801 Ns384p307 Ns384p802 Ns384p463 RS385to396.d47 (@Ns384p805 0 1 3828635533131376 239289720820711 1125899906842624 3091451755 1125899906842624 (@Ns384p806 5668047424142708834304 168920976643047 1125899906842624 3091451755 1125899906842624 (@Ns384p807 1917046635 1125899906842624 (Ns384p792 rfl rfl) (Ns384p792 rfl rfl) rfl) (Ns384p792 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 44807841 33554432) (BSN.cos_neg_of_bound 44807841 33554432 Bool.false 3913286 16777216 1 5760000 (Ns384p811 rfl rfl)) rfl rfl) 

noncomputable def Ns384p813 := @Ns384p778 47569917243718379091 Ns384p704 (Ns384p779 qz31 (@Enclosure.Real.IsNear.of_eq qz115 (@Inv.inv Real Real.instInv (Real.sqrt qz124)) Bool.false 5101325 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz123 (BSN.t_div_two_pi_nonneg qz114 735068 1000 qz117)) Ns384p783) rfl) (@Ns384p784 281474976710656 83745866713519 1583296743997440000 (BSN.correction_mk qz116 (BSN.cos_two_pi_p_ne_zero_mk qz114 735068 1000 10 qz117 rfl rfl (@BSN.floor_sqrt_eq_dec qz114 735068 1000 10 qz117 rfl rfl rfl))) (@Ns384p785 33554432 1956643 8388608 823817 47185920000 162540077378913 281474976710656 83745866713519 1583296743997440000 (@Ns384p786 33554432 (Ns384p798 rfl rfl rfl rfl rfl) rfl) (Ns384p812 rfl) rfl)) 

noncomputable def Ns384p814 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz114) (hardyZApproximantRS₀ qz114) Bool.false 5231413521069482474259 4722366482869645213696 3416759417772604139091 Ns384p704 (@Eq.refl Real (hardyZApproximantRS₀ qz114)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz114) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz115) (Zeta.RiemannSiegel.correction qz116))) Bool.false 5231413521069482474259 4722366482869645213696 3416759417772604139091 Ns384p704 (BSN.hardyZApproximantRS₀_eq qz114 10 (@BSN.floor_sqrt_eq_dec qz114 735068 1000 10 qz117 rfl rfl rfl)) (@Ns384p706 5231413521069482474259 4722366482869645213696 3416759417772604139091 Ns384p704 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 10)) Bool.false 172252137 134217728 153213 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (Ns384p777 (Ns384p776 rfl rfl rfl rfl) rfl rfl)) (Ns384p813 rfl) rfl rfl)) 

theorem RS385to396.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz114) Bool.false 5231413521069482474259 4722366482869645213696 3416759417772604139091 Ns384p704 := Ns384p814 

noncomputable def Ns384p815 := nat_lit 144154348619394027285762801664 

noncomputable abbrev qz736 := (Enclosure.sfrac Bool.false 736387 1000)

noncomputable abbrev qz637 := qz736

noncomputable abbrev qz458 := qz637

noncomputable abbrev qz132 := qz458

noncomputable abbrev qz737 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 736387 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz638 := qz737

noncomputable abbrev qz459 := qz638

noncomputable abbrev qz133 := (@HPow.hPow Real Real Real qz350 qz459 qz352)

noncomputable abbrev qz738 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 736387 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz639 := qz738

noncomputable abbrev qz460 := qz639

noncomputable abbrev qz134 := qz460

noncomputable def Ns384p816 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz133) (Zeta.RiemannSiegel.correction qz134)) 55026747 33554432 76741 67108864 423971288571361503269 2361183241434822606848 4224267348057112303 295147905179352825856000 Ns384p815 

noncomputable def Ns384p817 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.sin BSN.quadSignNeg 9 10 736387 1000 197 268435456 134217728 4503599627370496 Bool.false 371902026995 2557 618095470 48 84886744 8 

noncomputable def Ns384p818 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 736387 1000 92 148 268435456 134217728 4503599627370496 Bool.false 371902026995 2557 

noncomputable def Ns384p819 := Ns384p818 558195838 48 94906264 8 589812974 48 89478488 8 Bool.true 278104952 115430 Bool.true 353648161 Bool.true 23280106 14148475504056880 1 Bool.false 67284031 Bool.false Bool.false 267426603 Bool.false Bool.true 165174252 

noncomputable def Ns384p820 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 736387 1000 42 30 268435456 134217728 4503599627370496 Bool.false 371902026995 2557 

noncomputable def Ns384p821 := Ns384p820 480971758 48 109588312 8 522351262 48 101459064 8 Bool.true 74238116 85610 Bool.false 11065049 Bool.true 100928927 14148475504056880 1 Bool.false 268207434 Bool.true Bool.false 249683822 Bool.true Bool.true 278104952 

noncomputable def Ns384p822 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 736387 1000 232 127 268435456 134217728 4503599627370496 Bool.false 371902026995 2557 

noncomputable def Ns384p823 := Ns384p822 372130544 47 134217720 8 432030192 47 120047984 16 Bool.true 291201324 50376 Bool.false 45408732 Bool.false 210116608 14148475504056880 1 Bool.false 264603919 Bool.false Bool.false 189308328 Bool.false Bool.true 74238116 

noncomputable def Ns384p824 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 736387 1000 557 366 268435456 134217728 4503599627370496 Bool.false 371902026995 2557 

noncomputable def Ns384p825 := Ns384p824 186065264 47 189812528 16 294906480 47 154981288 8 Bool.true 268435392 2607 Bool.false 22797889 Bool.false 410110161 14148475504056880 1 Bool.false 22770492 Bool.true Bool.false 11543706 Bool.true Bool.true 291201324 

noncomputable def Ns384p826 := nat_lit 35816918657017181858303826187992509928126414080130677816581 

noncomputable def Ns384p827 := nat_lit 25852321832973151991458642031314841196739855650914304000 

noncomputable def Ns384p828 := nat_lit 103937510263373266473007326739360000 

noncomputable def Ns384p829 := nat_lit 459229487023782780700618424974998553920 

noncomputable abbrev qz640 := (@Eq.refl Real qz736)

noncomputable abbrev qz461 := qz640

noncomputable abbrev qz135 := qz461

noncomputable def Ns384p830 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz132 736387 1000 2169064255076 16000000 1472774 4000 2000 Ns384p828 Ns384p829 qz135 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns384p831 := nat_lit 11461413970245498194657224380157603177000452505641816901305920 

noncomputable abbrev qz641 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1472774))))

noncomputable abbrev qz462 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 736387 4000) (Real.log (Enclosure.sfrac Bool.false 2169064255076 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz641))

noncomputable abbrev qz642 := (Enclosure.sfrac Bool.false 736387 2000)

noncomputable abbrev qz136 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz462 qz642) (@HMul.hMul Real Real Real qz349 qz642 (Real.log Real.pi)))

noncomputable def Ns384p832 := @Enclosure.Real.IsNear.addLit_ft_p qz136 (Enclosure.sfrac Bool.true Ns384p828 Ns384p829) 24957926628138448058101 18014398509481984000 117044081866813813 12288000000000000000000 Ns384p828 Ns384p829 0 1 Ns384p831 

noncomputable def Ns384p833 := nat_lit 1674898103809721683902164107264000 

noncomputable abbrev qz137 := (@HSub.hSub Real Real Real qz355 qz462 qz642)

noncomputable def Ns384p834 := @Enclosure.Real.IsNear.subLit_ff_p qz137 (@HMul.hMul Real Real Real qz5 qz642 (Real.log Real.pi)) 32550673177900032194293 18014398509481984000 48462732869737 12000000000000000000 28285185060507 67108864000 736387 134217728000 Ns384p833 24957926628138448058101 18014398509481984000 

noncomputable def Ns384p835 := nat_lit 65101346355800064388586000 

noncomputable abbrev qz138 := qz462

noncomputable def Ns384p836 := @Enclosure.Real.IsNear.subLit_ff_p qz138 qz642 39183457615500987070197 18014398509481984000 48462732869737 12000000000000000000 736387 2000 0 1 Ns384p835 32550673177900032194293 18014398509481984000 48462732869737 12000000000000000000 

noncomputable def Ns384p837 := nat_lit 88233302558128934550091842861039353856 

noncomputable def Ns384p838 := nat_lit 57144558326545387769298944 

noncomputable def Ns384p839 := nat_lit 54601803405224069687297328 

noncomputable def Ns384p840 := BSN.log_dyadic_bound 71912255076 4266216255076 2 1 Ns384p839 134217728 46080000 5171372430115687765776 5171372430115687765776 4525234 4338128510152 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 71912255076) (BSN.artanhQ 4266216255076) 0 1 5171372430115687765776 Ns384p839 5171372430115687765776 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz463 := (Real.log (Enclosure.sfrac Bool.false 2169064255076 16000000))

noncomputable def Ns384p841 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 736387 4000) qz463 736387 4000 0 1 53220017185942631 4503599627370496 195312653 9000000000000000 39190528795504736214197 18014398509481984000 143825698604711 36000000000000000000 (Enclosure.Real.IsNear.const Bool.false 736387 4000) (BSN.isNear_log_sfrac 2169064255076 16000000 53220017185942631 4503599627370496 195312653 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2169064255076) qz358)) Bool.false Ns384p838 Ns384p98 1000000783360000 46080000000000000000000 53220017185942631 4503599627370496 195312653 9000000000000000 (BSN.log_rat_reduce_isNear 2169064255076 16000000 17 4338128510152 4194304000000 4525234 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns384p840 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns384p842 := BSN.arctan_dyadic_bound_f 1000 1472774 1 0 16777216 5760000 0 1 1 0 1 1 11391 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1472774) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1472774) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz464 := (@Nat.cast Real Real.instNatCast 1472774)

noncomputable def Ns384p843 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz464)) 884279719003555 562949953421312 1 2000000000000000 11391 16777216 1 5760000 14829339287222524837888 883897500468643 562949953421312 3125000009 18000000000000000 qz15 (Ns384p842 rfl) rfl rfl 

noncomputable abbrev qz465 := (@HMul.hMul Real Real Real qz579 qz584 qz641)

noncomputable abbrev qz139 := qz465

noncomputable abbrev qz466 := qz641

noncomputable abbrev qz140 := qz466

noncomputable def Ns384p844 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 736387 4000) qz463) qz139 39190528795504736214197 18014398509481984000 143825698604711 36000000000000000000 883897500468643 2251799813685248 3125000009 72000000000000000 Ns384p837 39183457615500987070197 18014398509481984000 48462732869737 12000000000000000000 (Ns384p841 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz140 1 4 0 1 883897500468643 562949953421312 3125000009 18000000000000000 883897500468643 2251799813685248 3125000009 72000000000000000 qz366 Ns384p843 rfl) 

noncomputable def Ns384p845 := @Ns384p832 Ns384p826 Ns384p827 117044081866813813 12288000000000000000000 (@Ns384p834 117044081866813813 12288000000000000000000 (Ns384p836 (Ns384p844 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 736387 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz642 (Real.log Real.pi) 736387 2000 0 1 38410761 33554432 1 67108864 28285185060507 67108864000 736387 134217728000 (Enclosure.Real.IsNear.const Bool.false 736387 2000) RS385to396.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns384p828 Ns384p829) 

noncomputable def Ns384p846 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz132) Bool.false Ns384p826 Ns384p827 117044081866813813 12288000000000000000000 23243876687 16777216 5 524288 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz132) (@HAdd.hAdd Real Real Real qz367 qz136 (Enclosure.sfrac Bool.true Ns384p828 Ns384p829)) Bool.false Ns384p826 Ns384p827 117044081866813813 12288000000000000000000 Ns384p830 (Ns384p845 rfl rfl)) 

noncomputable def Ns384p847 := BSN.cos_dyadic_bound_f 44866844 68719476736 1 0 33554432 11531251 0 1 1 0 1 1 33554424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 44866844) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 44866844) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns384p848 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz132) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23243876687) qz415) Bool.false 23243876687 16777216 5 524288 Bool.true 33554424 33554432 1 5760000 (Ns384p846 rfl) (Enclosure.sfrac_false_div 23243876687 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23243876687) qz415) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1578611756193078575104) qz427) 226375608064910080 72057594037927936 Bool.false 33554424 33554432 220 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q2 23243876687 16777216 226375608064910080 72057594037927936 220 1578611756193078575104 Ns384p509 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554424 33554432 1578611756193078575104 Ns384p509 44866844 68719476736 11531251 11520000 (Ns384p847 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p849 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz132) Bool.false Ns384p826 Ns384p827 117044081866813813 12288000000000000000000 371902026995 268435456 2557 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz132) (@HAdd.hAdd Real Real Real qz367 qz136 (Enclosure.sfrac Bool.true Ns384p828 Ns384p829)) Bool.false Ns384p826 Ns384p827 117044081866813813 12288000000000000000000 Ns384p830 (Ns384p845 rfl rfl)) 

noncomputable def Ns384p850 := Ns384p825 50376 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 557 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 22770492 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 366 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 11543706 268435456) qz135 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 1) Bool.true 4194303 4194304 28637 2949120000 268435392 268435456 2607 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz132)) Bool.true 4194303 4194304 28637 2949120000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz132) qz132) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz132)) Bool.true 33554424 33554432 29324288 3019898880000 4194303 4194304 28637 2949120000 (Ns384p848 rfl rfl) rfl)) rfl) (Ns384p849 rfl) RS385to396.d7 

noncomputable def Ns384p851 := nat_lit 270133558238297526519649655041 

noncomputable def Ns384p852 := BSN.sin_dyadic_bound_f 22797889 268435456 2 1 268435456 134217728 Ns384p851 Ns384p127 Ns384p851 Ns384p851 Ns384p128 Ns384p851 22770492 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 22797889) qz372 0 1 Ns384p851 Ns384p127 Ns384p851 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 22797889) qz373 0 1 Ns384p851 Ns384p128 Ns384p851 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p853 := nat_lit 15270512311966185950564277543348311813280705256068018199620772909927663977866632752415884727074936086254500801 

noncomputable def Ns384p854 := nat_lit 22636347659836491646095948203972810008940167181774971601074045425593816085360032753913655813556033731521 

noncomputable def Ns384p855 := nat_lit 92441357240125461153606791621061581350504490620864537275825201260708638299134147177076384307845329738772691905 

noncomputable def Ns384p856 := BSN.cos_dyadic_bound_f 410110161 268435456 4 3 268435456 134217728 Ns384p853 Ns384p149 Ns384p854 Ns384p855 Ns384p152 Ns384p854 11543706 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 410110161) qz370 0 3 Ns384p853 Ns384p149 Ns384p854 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 410110161) qz371 0 3 Ns384p855 Ns384p152 Ns384p854 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p857 := nat_lit 4251649934394895862219573534976 

noncomputable def Ns384p858 := BSN.cos_dyadic_bound_f 45408732 268435456 2 1 268435456 134217728 Ns384p857 Ns384p266 Ns384p857 Ns384p857 Ns384p267 Ns384p857 264603919 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 45408732) qz370 0 1 Ns384p857 Ns384p266 Ns384p857 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 45408732) qz371 0 1 Ns384p857 Ns384p267 Ns384p857 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p859 := nat_lit 30608125578256298498757926859487374899358624238933506587808597488435200 

noncomputable def Ns384p860 := nat_lit 3799120332552514953836412507457966786933987466974999627731426082816 

noncomputable def Ns384p861 := nat_lit 80157987462513791996345501868883430885427075122260272016291904446529536 

noncomputable def Ns384p862 := BSN.sin_dyadic_bound_f 210116608 268435456 3 2 268435456 134217728 Ns384p859 Ns384p131 Ns384p860 Ns384p861 Ns384p134 Ns384p860 189308328 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 210116608) qz372 0 2 Ns384p859 Ns384p131 Ns384p860 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 210116608) qz373 0 2 Ns384p861 Ns384p134 Ns384p860 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p863 := Ns384p823 85610 BSN.abs_quadSignPos (BSN.cos_quad_nat0 232 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 264603919 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 127 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 189308328 268435456) qz135 rfl rfl (Ns384p850 RS385to396.d9 RS385to396.d11 RS385to396.d13 RS385to396.d17 (Ns384p852 rfl rfl) (Ns384p856 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns384p849 rfl) RS385to396.d19 RS385to396.d21 RS385to396.d23 RS385to396.d25 RS385to396.d17 (Ns384p858 rfl rfl) (Ns384p862 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns384p864 := nat_lit 14990404981115544152500504801 

noncomputable def Ns384p865 := BSN.cos_dyadic_bound_f 11065049 268435456 2 1 268435456 134217728 Ns384p864 Ns384p266 Ns384p864 Ns384p864 Ns384p267 Ns384p864 268207434 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 11065049) qz370 0 1 Ns384p864 Ns384p266 Ns384p864 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 11065049) qz371 0 1 Ns384p864 Ns384p267 Ns384p864 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p866 := nat_lit 905183412896941577527623891133078903521882025016045672054409016738561 

noncomputable def Ns384p867 := nat_lit 10767757084166486467882927377831106778159478938010488652334990081 

noncomputable def Ns384p868 := nat_lit 2715528703176656399609935907544481048352089756090260995185922380235521 

noncomputable def Ns384p869 := BSN.cos_dyadic_bound_f 100928927 268435456 3 2 268435456 134217728 Ns384p866 Ns384p117 Ns384p867 Ns384p868 Ns384p120 Ns384p867 249683822 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 100928927) qz370 0 2 Ns384p866 Ns384p117 Ns384p867 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 100928927) qz371 0 2 Ns384p868 Ns384p120 Ns384p867 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p870 := Ns384p821 115430 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 42 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268207434 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 249683822 268435456) qz135 rfl rfl (Ns384p863 rfl rfl) (Ns384p849 rfl) RS385to396.d27 RS385to396.d29 RS385to396.d31 RS385to396.d33 RS385to396.d17 (Ns384p865 rfl rfl) (Ns384p869 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p871 := nat_lit 8431573351818766082917960898431147476106291804238147850694389689128213312980999524214048455586433464232636801 

noncomputable def Ns384p872 := nat_lit 3826985781489771164303024060978503995244828433197533039864086451468205730642824467741083252749430747521 

noncomputable def Ns384p873 := nat_lit 51090486800472130032282100088288228673219953840767689013033748539597610741554479251644114472204110196393963905 

noncomputable def Ns384p874 := BSN.cos_dyadic_bound_f 353648161 268435456 4 3 268435456 134217728 Ns384p871 Ns384p149 Ns384p872 Ns384p873 Ns384p152 Ns384p872 67284031 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 353648161) qz370 0 3 Ns384p871 Ns384p149 Ns384p872 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 353648161) qz371 0 3 Ns384p873 Ns384p152 Ns384p872 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p875 := nat_lit 293724256886714826401936167696 

noncomputable def Ns384p876 := BSN.cos_dyadic_bound_f 23280106 268435456 2 1 268435456 134217728 Ns384p875 Ns384p266 Ns384p875 Ns384p875 Ns384p267 Ns384p875 267426603 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 23280106) qz370 0 1 Ns384p875 Ns384p266 Ns384p875 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 23280106) qz371 0 1 Ns384p875 Ns384p267 Ns384p875 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p877 := Ns384p819 141485 BSN.abs_quadSignPos (BSN.cos_quad_nat0 92 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 67284031 268435456) BSN.abs_quadSignPos qz590 (BSN.sfrac_eq_quadSignPos_mul Bool.false 267426603 268435456) qz135 rfl rfl (Ns384p870 rfl) (Ns384p849 rfl) RS385to396.d35 RS385to396.d37 RS385to396.d39 RS385to396.d41 RS385to396.d17 (Ns384p874 rfl rfl) (Ns384p876 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p878 := nat_lit 20006286006015483517124952752442041316857403390734055873088118283749185 

noncomputable def Ns384p879 := nat_lit 1623229277032557132374120313625400575625152614945889878800740042561 

noncomputable def Ns384p880 := nat_lit 52394787644544404119017699109221381371789806252450710131617489544988481 

noncomputable def Ns384p881 := BSN.sin_dyadic_bound_f 188928503 268435456 3 2 268435456 134217728 Ns384p878 Ns384p131 Ns384p879 Ns384p880 Ns384p134 Ns384p879 173712565 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 188928503) qz372 0 2 Ns384p878 Ns384p131 Ns384p879 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 188928503) qz373 0 2 Ns384p880 Ns384p134 Ns384p879 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p882 := Ns384p817 Bool.true 165174252 141485 Bool.true 188928503 14148475504056880 1 Bool.false 173712565 Bool.true Bool.true 220106988 153482 BSN.abs_quadSignNeg qz374 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 173712565 268435456) qz135 rfl (Ns384p877 rfl) (Ns384p849 rfl) RS385to396.d43 RS385to396.d45 RS385to396.d17 (Ns384p881 rfl rfl) rfl 

noncomputable def Ns384p883 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) 220106988 268435456 153482 268435456 220106988 268435456 153482 268435456 118169039385133056 55026747 33554432 76741 67108864 (Ns384p882 rfl rfl rfl rfl) 

noncomputable def Ns384p884 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz133) (Zeta.RiemannSiegel.correction qz134) 5099039 16777216 1 16777216 83147292768571 140737488355328 37188240755269 791648371998720000 423971288571361503269 2361183241434822606848 

noncomputable def Ns384p885 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz133 1 1 0 1 5099039 16777216 1 16777216 5099039 16777216 1 16777216 

noncomputable abbrev qz141 := qz459

noncomputable def Ns384p886 := @Enclosure.Real.IsNear.sqrt_image qz141 3932566524611 33554432000 736387 33554432000 181628061 181628096 16777216 (@Enclosure.Real.IsNear.of_eq qz141 (@HMul.hMul Real Real Real qz5 qz132 qz3) Bool.false 3932566524611 33554432000 736387 33554432000 (BSN.t_div_two_pi_mk qz132 736387 1000 qz135) (@Enclosure.Real.IsNear.mulLit_ff qz132 qz3 736387 1000 0 1 5340353 33554432 1 33554432 3932566524611 33554432000 736387 33554432000 (Enclosure.Real.IsNear.const Bool.false 736387 1000) RS385to396.d48 rfl)) 

noncomputable abbrev qz739 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 736387 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz643 := qz739

noncomputable abbrev qz467 := qz643

noncomputable abbrev qz142 := qz467

noncomputable def Ns384p887 := @Enclosure.Real.IsNear.sqrt_image qz142 363256157 33554432 35 33554432 55201568 55201575 16777216 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 363256157 33554432 35 33554432 363256157 33554432 35 33554432 (Ns384p886 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns384p888 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz142) 110403143 33554432 7 33554432 5099038 5099040 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz142) Bool.false 110403143 33554432 7 33554432 110403143 33554432 7 33554432 (Ns384p887 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns384p889 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz142)) Bool.false 10198078 33554432 2 33554432 5099039 16777216 1 16777216 (Ns384p888 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz143 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz460))

noncomputable abbrev qz644 := (@HMul.hMul Real Real Real qz707 qz738 qz738)

noncomputable abbrev qz468 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz644 qz639) qz594)

noncomputable abbrev qz144 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz468))

noncomputable def Ns384p890 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz134) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz143) qz144) Bool.false 83147292768571 

noncomputable def Ns384p891 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz143) qz144 73120241 33554432 1073 

noncomputable def Ns384p892 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz143) Bool.false 73120241 33554432 1073 33554432 73120241 33554432 1073 

noncomputable def Ns384p893 := @Enclosure.Real.IsNear.recentre' qz143 Bool.false 15397924 33554432 325188608 48318382080000 3849481 8388608 317567 47185920000 

noncomputable abbrev qz145 := (@HMul.hMul Real Real Real qz349 qz346 qz460)

noncomputable def Ns384p894 := @Enclosure.Real.IsNear.cos_image qz145 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 174118607) qz378) Bool.false 174118607 33554432 55 8388608 Bool.false 15397924 33554432 1 

noncomputable def Ns384p895 := nat_lit 944512639554584458185079349 

noncomputable def Ns384p896 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz134 884279719003555 140737488355328 1 500000000000000 27711837 33554432 35 33554432 24505015435432318580535 4722366482869645213696 Ns384p895 

noncomputable def Ns384p897 := @Enclosure.Real.IsNear.subLit_ff_p qz142 qz1 363256157 33554432 35 33554432 10 1 0 1 27711837 27711837 33554432 35 

noncomputable def Ns384p898 := @Ns384p897 33554432 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 363256157 33554432 35 33554432 363256157 33554432 35 33554432 (Ns384p886 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns384p899 := @Enclosure.Real.IsNear.recentre' qz145 Bool.false 24505015435432318580535 4722366482869645213696 Ns384p895 Ns384p295 174118607 33554432 55 8388608 (@Ns384p896 Ns384p295 RS385to396.d47 (Ns384p898 rfl rfl) rfl) 

noncomputable def Ns384p900 := nat_lit 2305420953493004168986624 

noncomputable def Ns384p901 := nat_lit 1152077624826920707100833580346281911901841 

noncomputable def Ns384p902 := BSN.sin_dyadic_bound_f 32762002227 68719476736 2 1 33554432 11531251 Ns384p901 Ns384p181 Ns384p901 Ns384p901 Ns384p182 Ns384p901 15397924 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 32762002227) qz368 0 1 Ns384p901 Ns384p181 Ns384p901 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 32762002227) qz369 0 1 Ns384p901 Ns384p182 Ns384p901 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p903 := @Ns384p894 5760000 (Ns384p899 rfl) (Enclosure.sfrac_false_div 174118607 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 174118607) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns384p900) qz380) 226375608064910080 72057594037927936 Bool.false 15397924 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 174118607 33554432 226375608064910080 72057594037927936 0 Ns384p900 Ns384p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 15397924 33554432 Ns384p900 Ns384p98 32762002227 68719476736 11531251 11520000 (Ns384p902 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p904 := @Enclosure.Real.IsNear.inv_image qz143 3849481 8388608 317567 47185920000 36559584 36560657 16777216 (Ns384p893 (Ns384p903 rfl rfl) rfl) rfl 

noncomputable def Ns384p905 := @Enclosure.Real.IsNear.recentre' qz144 Bool.false 4548524 16777216 

noncomputable abbrev qz146 := (@HMul.hMul Real Real Real qz349 qz346 qz468)

noncomputable def Ns384p906 := @Enclosure.Real.IsNear.cos_image qz146 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 43494831)) qz378) Bool.true 43494831 33554432 

noncomputable def Ns384p907 := nat_lit 205398533986037456259008483845 

noncomputable def Ns384p908 := nat_lit 84040978799384632286027339049458113 

noncomputable def Ns384p909 := @Enclosure.Real.IsNear.recentre' qz146 Bool.true Ns384p907 Ns384p307 Ns384p908 

noncomputable abbrev qz147 := qz468

noncomputable def Ns384p910 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz147 884279719003555 140737488355328 1 500000000000000 232277784474679 

noncomputable abbrev qz469 := (@HSub.hSub Real Real Real qz583 qz644 qz639)

noncomputable abbrev qz148 := qz469

noncomputable def Ns384p911 := @Enclosure.Real.IsNear.subLit_tf qz148 qz29 161909040297015 1125899906842624 3114234935 1125899906842624 1 16 

noncomputable abbrev qz470 := qz644

noncomputable abbrev qz149 := qz470

noncomputable def Ns384p912 := @Enclosure.Real.IsNear.subLit_ff_n qz149 qz134 767945909914569 1125899906842624 1939829815 1125899906842624 27711837 33554432 35 33554432 

noncomputable def Ns384p913 := @Enclosure.Real.IsNear.mulLit_ff qz134 qz134 27711837 33554432 35 33554432 27711837 33554432 35 33554432 767945909914569 1125899906842624 

noncomputable def Ns384p914 := nat_lit 114975377440518595518342526168614840794694966818238718836361743642710062438847629705491090910907841 

noncomputable def Ns384p915 := nat_lit 45840756140482910394597427705927343481980917746573040501786025990092693035286242987245735361 

noncomputable def Ns384p916 := nat_lit 696736911228139498511839956347257034777843707502724726277993059920706707897466692410025167762656705 

noncomputable def Ns384p917 := BSN.cos_dyadic_bound_f 43494831 33554432 4 3 16777216 5760000 Ns384p914 Ns384p316 Ns384p915 Ns384p916 Ns384p319 Ns384p915 4548524 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 43494831) (BSN.cosEvenQ 33554432) 0 3 Ns384p914 Ns384p316 Ns384p915 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 43494831) (BSN.cosOddQ 33554432) 0 3 Ns384p916 Ns384p319 Ns384p915 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p918 := @Ns384p905 424674304 24159191040000 1137131 4194304 414721 23592960000 (@Ns384p906 73 4194304 Bool.false 4548524 16777216 1 5760000 (@Ns384p909 Ns384p463 43494831 33554432 73 4194304 (@Ns384p910 1125899906842624 3114234935 1125899906842624 Ns384p907 Ns384p307 Ns384p908 Ns384p463 RS385to396.d47 (@Ns384p911 0 1 3716444551594864 232277784474679 1125899906842624 3114234935 1125899906842624 (@Ns384p912 5432765882831449620480 161909040297015 1125899906842624 3114234935 1125899906842624 (@Ns384p913 1939829815 1125899906842624 (Ns384p898 rfl rfl) (Ns384p898 rfl rfl) rfl) (Ns384p898 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 43494831 33554432) (BSN.cos_neg_of_bound 43494831 33554432 Bool.false 4548524 16777216 1 5760000 (Ns384p917 rfl rfl)) rfl rfl) 

noncomputable def Ns384p919 := @Ns384p884 4224267348057112303 295147905179352825856000 (Ns384p885 qz31 (@Enclosure.Real.IsNear.of_eq qz133 (@Inv.inv Real Real.instInv (Real.sqrt qz142)) Bool.false 5099039 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz141 (BSN.t_div_two_pi_nonneg qz132 736387 1000 qz135)) Ns384p889) rfl) (@Ns384p890 140737488355328 37188240755269 791648371998720000 (BSN.correction_mk qz134 (BSN.cos_two_pi_p_ne_zero_mk qz132 736387 1000 10 qz135 rfl rfl (@BSN.floor_sqrt_eq_dec qz132 736387 1000 10 qz135 rfl rfl rfl))) (@Ns384p891 33554432 1137131 4194304 414721 23592960000 83147292768571 140737488355328 37188240755269 791648371998720000 (@Ns384p892 33554432 (Ns384p904 rfl rfl rfl rfl rfl) rfl) (Ns384p918 rfl) rfl)) 

noncomputable def Ns384p920 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz132) (hardyZApproximantRS₀ qz132) Bool.true 4296134371143401482277 2361183241434822606848 341734754656689176303 295147905179352825856000 (@Eq.refl Real (hardyZApproximantRS₀ qz132)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz132) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz133) (Zeta.RiemannSiegel.correction qz134))) Bool.true 4296134371143401482277 2361183241434822606848 341734754656689176303 295147905179352825856000 (BSN.hardyZApproximantRS₀_eq qz132 10 (@BSN.floor_sqrt_eq_dec qz132 736387 1000 10 qz135 rfl rfl rfl)) (@Ns384p816 4296134371143401482277 2361183241434822606848 341734754656689176303 295147905179352825856000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 10)) Bool.true 55026747 33554432 76741 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (Ns384p883 (Ns384p882 rfl rfl rfl rfl) rfl rfl)) (Ns384p919 rfl) rfl rfl)) 

theorem RS385to396.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz132) Bool.true 4296134371143401482277 2361183241434822606848 341734754656689176303 295147905179352825856000 := Ns384p920 

noncomputable def Ns384p921 := nat_lit 1328165573307087716352000 

noncomputable def Ns384p922 := nat_lit 22939619275996699733042135040 

noncomputable abbrev qz740 := (Enclosure.sfrac Bool.false 737705 1000)

noncomputable abbrev qz645 := qz740

noncomputable abbrev qz471 := qz645

noncomputable abbrev qz150 := qz471

noncomputable abbrev qz741 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 737705 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz646 := qz741

noncomputable abbrev qz472 := qz646

noncomputable abbrev qz151 := (@HPow.hPow Real Real Real qz350 qz472 qz352)

noncomputable abbrev qz742 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 737705 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz647 := qz742

noncomputable abbrev qz473 := qz647

noncomputable abbrev qz152 := qz473

noncomputable def Ns384p923 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz151) (Zeta.RiemannSiegel.correction qz152)) 335543625 134217728 153761 134217728 13553576378244018945 73786976294838206464 17216827161158843521 Ns384p921 Ns384p922 

noncomputable def Ns384p924 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.sin BSN.quadSignNeg 9 10 737705 1000 197 268435456 134217728 4503599627370496 Bool.false 372744910264 2562 618095470 48 84886744 8 

noncomputable def Ns384p925 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 737705 1000 92 147 268435456 134217728 4503599627370496 Bool.false 372744910264 2562 

noncomputable def Ns384p926 := Ns384p925 558195838 48 94906264 8 589812974 48 89478488 8 Bool.false 237370263 115641 Bool.true 246467007 Bool.true 379427765 14148475504056880 1 Bool.false 163016053 Bool.false Bool.false 265120563 Bool.false Bool.false 383378663 

noncomputable def Ns384p927 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 737705 1000 42 29 268435456 134217728 4503599627370496 Bool.false 372744910264 2562 

noncomputable def Ns384p928 := Ns384p927 480971758 48 109588312 8 522351262 48 101459064 8 Bool.false 411611462 85767 Bool.false 220027541 Bool.true 368162049 14148475504056880 1 Bool.false 183197812 Bool.true Bool.false 263122638 Bool.true Bool.false 237370263 

noncomputable def Ns384p929 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 737705 1000 232 128 268435456 134217728 4503599627370496 Bool.false 372744910264 2562 

noncomputable def Ns384p930 := Ns384p929 372130544 47 134217720 8 432030192 47 120047984 16 Bool.false 282842727 50470 Bool.false 397823944 Bool.false 61926656 14148475504056880 1 Bool.false 23802183 Bool.false Bool.false 261324001 Bool.false Bool.false 411611462 

noncomputable def Ns384p931 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 737705 1000 558 368 268435456 134217728 4503599627370496 Bool.false 372744910264 2562 

noncomputable def Ns384p932 := Ns384p931 186065264 47 189812528 16 294906480 47 154981288 8 Bool.false 268435328 2615 Bool.false 198789712 Bool.false 20991833 14148475504056880 1 Bool.false 198131674 Bool.true Bool.false 267615086 Bool.false Bool.false 282842727 

noncomputable def Ns384p933 := nat_lit 92890445262995071294172375660429548366312128380369591 

noncomputable def Ns384p934 := nat_lit 66895853828121615748357680206527183518133219491840 

noncomputable def Ns384p935 := nat_lit 104870992427749313084638551500000000 

noncomputable def Ns384p936 := nat_lit 464183232324622106398632205615845000000 

noncomputable abbrev qz648 := (@Eq.refl Real qz740)

noncomputable abbrev qz474 := qz648

noncomputable abbrev qz153 := qz474

noncomputable def Ns384p937 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz150 737705 1000 2176835668100 16000000 1475410 4000 2000 Ns384p935 Ns384p936 qz153 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns384p938 := nat_lit 464452226314975356470861878302147741831560641901847955000000 

noncomputable abbrev qz649 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1475410))))

noncomputable abbrev qz475 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 737705 4000) (Real.log (Enclosure.sfrac Bool.false 2176835668100 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz649))

noncomputable abbrev qz650 := (Enclosure.sfrac Bool.false 737705 2000)

noncomputable abbrev qz154 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz475 qz650) (@HMul.hMul Real Real Real qz349 qz650 (Real.log Real.pi)))

noncomputable def Ns384p939 := @Enclosure.Real.IsNear.addLit_ft_p qz154 (Enclosure.sfrac Bool.true Ns384p935 Ns384p936) 1000579662381425846039 720575940379279360 70351569063730777 7372800000000000000000 Ns384p935 Ns384p936 0 1 Ns384p938 

noncomputable def Ns384p940 := nat_lit 67147764483921023227916189696000 

noncomputable abbrev qz155 := (@HSub.hSub Real Real Real qz355 qz475 qz650)

noncomputable def Ns384p941 := @Enclosure.Real.IsNear.subLit_ff_p qz155 (@HMul.hMul Real Real Real qz5 qz650 (Real.log Real.pi)) 6524165551413494612851 3602879701896396800 29129124137173 7200000000000000000 5667162088701 13421772800 147541 26843545600 Ns384p940 1000579662381425846039 720575940379279360 

noncomputable def Ns384p942 := nat_lit 13048331102826989225702000 

noncomputable abbrev qz156 := qz475

noncomputable def Ns384p943 := @Enclosure.Real.IsNear.subLit_ff_p qz156 qz650 7853096736657235313523 3602879701896396800 29129124137173 7200000000000000000 737705 2000 0 1 Ns384p942 6524165551413494612851 3602879701896396800 29129124137173 7200000000000000000 

noncomputable def Ns384p944 := nat_lit 17683601768456991556688984955320008704 

noncomputable def Ns384p945 := nat_lit 57161852905719227872182272 

noncomputable def Ns384p946 := nat_lit 54800911761212627272830000 

noncomputable def Ns384p947 := BSN.log_dyadic_bound 79683668100 4273987668100 2 1 Ns384p946 134217728 46080000 6349486961870957610000 6349486961870957610000 5005255 4353671336200 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 79683668100) (BSN.artanhQ 4273987668100) 0 1 6349486961870957610000 Ns384p946 6349486961870957610000 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz476 := (Real.log (Enclosure.sfrac Bool.false 2176835668100 16000000))

noncomputable def Ns384p948 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 737705 4000) qz476 737705 4000 0 1 53236124017945703 4503599627370496 195312653 9000000000000000 7854510973731726966323 3602879701896396800 28816624136273 7200000000000000000 (Enclosure.Real.IsNear.const Bool.false 737705 4000) (BSN.isNear_log_sfrac 2176835668100 16000000 53236124017945703 4503599627370496 195312653 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2176835668100) qz358)) Bool.false Ns384p945 Ns384p98 1000000783360000 46080000000000000000000 53236124017945703 4503599627370496 195312653 9000000000000000 (BSN.log_rat_reduce_isNear 2176835668100 16000000 17 4353671336200 4194304000000 5005255 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns384p947 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns384p949 := BSN.arctan_dyadic_bound_f 1000 1475410 1 0 16777216 5760000 0 1 1 0 1 1 11371 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1475410) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1475410) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns384p950 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1475410))) 884279719003555 562949953421312 1 2000000000000000 11371 16777216 1 5760000 14829350546221593264128 883898171557283 562949953421312 3125000009 18000000000000000 qz15 (Ns384p949 rfl) rfl rfl 

noncomputable abbrev qz477 := (@HMul.hMul Real Real Real qz579 qz584 qz649)

noncomputable abbrev qz157 := qz477

noncomputable abbrev qz478 := qz649

noncomputable abbrev qz158 := qz478

noncomputable def Ns384p951 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 737705 4000) qz476) qz157 7854510973731726966323 3602879701896396800 28816624136273 7200000000000000000 883898171557283 2251799813685248 3125000009 72000000000000000 Ns384p944 7853096736657235313523 3602879701896396800 29129124137173 7200000000000000000 (Ns384p948 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz158 1 4 0 1 883898171557283 562949953421312 3125000009 18000000000000000 883898171557283 2251799813685248 3125000009 72000000000000000 qz366 Ns384p950 rfl) 

noncomputable def Ns384p952 := @Ns384p939 Ns384p933 Ns384p934 70351569063730777 7372800000000000000000 (@Ns384p941 70351569063730777 7372800000000000000000 (Ns384p943 (Ns384p951 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 737705 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz650 (Real.log Real.pi) 737705 2000 0 1 38410761 33554432 1 67108864 5667162088701 13421772800 147541 26843545600 (Enclosure.Real.IsNear.const Bool.false 737705 2000) RS385to396.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns384p935 Ns384p936) 

noncomputable def Ns384p953 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz150) Bool.false Ns384p933 Ns384p934 70351569063730777 7372800000000000000000 46593113783 33554432 321 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz150) (@HAdd.hAdd Real Real Real qz367 qz154 (Enclosure.sfrac Bool.true Ns384p935 Ns384p936)) Bool.false Ns384p933 Ns384p934 70351569063730777 7372800000000000000000 Ns384p937 (Ns384p952 rfl rfl)) 

noncomputable def Ns384p954 := nat_lit 7591287435023806990647296 

noncomputable def Ns384p955 := nat_lit 3502289282867714992293329972392100343584676039587153670174752519903303186033671985907662943964051103081189455898481508933693902055014400000 

noncomputable def Ns384p956 := nat_lit 2484434908299883482406204200088910455884345429393693398210371827334370265404011045177880692629665628491480573245501997056000000000000 

noncomputable def Ns384p957 := nat_lit 17489739062738487055441170187978505774178700105277739636307967783577807604729881238012424001512881444035971125933590285360340582531072000000 

noncomputable def Ns384p958 := BSN.sin_dyadic_bound_f 107878682840 68719476736 4 3 33554432 11531251 Ns384p955 Ns384p108 Ns384p956 Ns384p957 Ns384p111 Ns384p956 33554416 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107878682840) qz368 0 3 Ns384p955 Ns384p108 Ns384p956 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107878682840) qz369 0 3 Ns384p957 Ns384p111 Ns384p956 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p959 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz150) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46593113783) qz378) Bool.false 46593113783 33554432 321 33554432 Bool.false 33554416 33554432 1 5760000 (Ns384p953 rfl) (Enclosure.sfrac_false_div 46593113783 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46593113783) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns384p954) qz380) 226375608064910080 72057594037927936 Bool.false 33554416 33554432 220 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 46593113783 33554432 226375608064910080 72057594037927936 220 Ns384p954 Ns384p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554416 33554432 Ns384p954 Ns384p98 107878682840 68719476736 11531251 11520000 (Ns384p958 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p960 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz150) Bool.false Ns384p933 Ns384p934 70351569063730777 7372800000000000000000 372744910264 268435456 2562 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz150) (@HAdd.hAdd Real Real Real qz367 qz154 (Enclosure.sfrac Bool.true Ns384p935 Ns384p936)) Bool.false Ns384p933 Ns384p934 70351569063730777 7372800000000000000000 Ns384p937 (Ns384p952 rfl rfl)) 

noncomputable def Ns384p961 := Ns384p932 50470 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 558 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 198131674 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 368 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 267615086 268435456) qz153 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 1) Bool.false 2097151 2097152 1838393 188743680000 268435328 268435456 2615 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz150)) Bool.false 2097151 2097152 1838393 188743680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz150) qz150) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz150)) Bool.false 33554416 33554432 1882514432 193273528320000 2097151 2097152 1838393 188743680000 (Ns384p959 rfl rfl) rfl)) rfl) (Ns384p960 rfl) RS385to396.d7 

noncomputable def Ns384p962 := nat_lit 13624549639890186478319292762708753661403216008686490822917737546776576 

noncomputable def Ns384p963 := nat_lit 2438659895204691192349160463867813273911572576099065561957579882496 

noncomputable def Ns384p964 := nat_lit 40868771599880150052573179967198525357661824880907274337629297480564736 

noncomputable def Ns384p965 := BSN.cos_dyadic_bound_f 198789712 268435456 3 2 268435456 134217728 Ns384p962 Ns384p117 Ns384p963 Ns384p964 Ns384p120 Ns384p963 198131674 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 198789712) qz370 0 2 Ns384p962 Ns384p117 Ns384p963 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 198789712) qz371 0 2 Ns384p964 Ns384p120 Ns384p963 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p966 := nat_lit 194178638094152751424300612321 

noncomputable def Ns384p967 := BSN.cos_dyadic_bound_f 20991833 268435456 2 1 268435456 134217728 Ns384p966 Ns384p266 Ns384p966 Ns384p966 Ns384p267 Ns384p966 267615086 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 20991833) qz370 0 1 Ns384p966 Ns384p266 Ns384p966 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 20991833) qz371 0 1 Ns384p966 Ns384p267 Ns384p966 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p968 := nat_lit 13516186641650445457892543454324871866602071227575244185526457002677068154308410372057448556499813102587478016 

noncomputable def Ns384p969 := nat_lit 15714154678941761194062965179977707858300073381626178886759734074188245254506307995290297045590197927936 

noncomputable def Ns384p970 := nat_lit 81841602101918204274213973661957214282783713085084008006144620822154946154801797552210855803964937150513807360 

noncomputable def Ns384p971 := BSN.cos_dyadic_bound_f 397823944 268435456 4 3 268435456 134217728 Ns384p968 Ns384p149 Ns384p969 Ns384p970 Ns384p152 Ns384p969 23802183 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 397823944) qz370 0 3 Ns384p968 Ns384p149 Ns384p969 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 397823944) qz371 0 3 Ns384p970 Ns384p152 Ns384p969 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p972 := nat_lit 14706540256006038723655049936896 

noncomputable def Ns384p973 := BSN.cos_dyadic_bound_f 61926656 268435456 2 1 268435456 134217728 Ns384p972 Ns384p266 Ns384p972 Ns384p972 Ns384p267 Ns384p972 261324001 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 61926656) qz370 0 1 Ns384p972 Ns384p266 Ns384p972 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 61926656) qz371 0 1 Ns384p972 Ns384p267 Ns384p972 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p974 := Ns384p930 85767 BSN.abs_quadSignPos (BSN.cos_quad_nat0 232 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 23802183 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 128 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 261324001 268435456) qz153 rfl rfl (Ns384p961 RS385to396.d9 RS385to396.d11 RS385to396.d13 RS385to396.d17 (Ns384p965 rfl rfl) (Ns384p967 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns384p960 rfl) RS385to396.d19 RS385to396.d21 RS385to396.d23 RS385to396.d25 RS385to396.d17 (Ns384p971 rfl rfl) (Ns384p973 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns384p975 := nat_lit 20450015824777311884605950748638867830927646478737504932766367915183201 

noncomputable def Ns384p976 := nat_lit 5493085531034071319764664341626814188027724705375108208058914049121 

noncomputable def Ns384p977 := nat_lit 61339061303269867511178322917233349864406883986801764581882985917451361 

noncomputable def Ns384p978 := BSN.cos_dyadic_bound_f 220027541 268435456 3 2 268435456 134217728 Ns384p975 Ns384p117 Ns384p976 Ns384p977 Ns384p120 Ns384p976 183197812 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 220027541) qz370 0 2 Ns384p975 Ns384p117 Ns384p976 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 220027541) qz371 0 2 Ns384p977 Ns384p120 Ns384p976 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p979 := nat_lit 25732509311582070119287105252161914172744405868479379175424018516777878916914118637631874330614911514958003201 

noncomputable def Ns384p980 := nat_lit 6201092657582211946705426520028121294791793815961841993373115476686385972293360399026509022465821670401 

noncomputable def Ns384p981 := nat_lit 128569566235209731109045588327593156547347366243318800636437524461993134630442068708844366630139238126558018561 

noncomputable def Ns384p982 := BSN.sin_dyadic_bound_f 368162049 268435456 4 3 268435456 134217728 Ns384p979 Ns384p156 Ns384p980 Ns384p981 Ns384p159 Ns384p980 263122638 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 368162049) qz372 0 3 Ns384p979 Ns384p156 Ns384p980 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 368162049) qz373 0 3 Ns384p981 Ns384p159 Ns384p980 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p983 := Ns384p928 115641 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 42 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 183197812 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 29 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 263122638 268435456) qz153 rfl rfl (Ns384p974 rfl rfl) (Ns384p960 rfl) RS385to396.d27 RS385to396.d29 RS385to396.d31 RS385to396.d33 RS385to396.d17 (Ns384p978 rfl rfl) (Ns384p982 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p984 := nat_lit 32202355465785265185991336972124639843472788405792986334187393417966081 

noncomputable def Ns384p985 := nat_lit 13616651728261804729085469158205763797623663337081057862990694412801 

noncomputable def Ns384p986 := nat_lit 96579833093899271948515839978057508002823117890704796886836198865072641 

noncomputable def Ns384p987 := BSN.cos_dyadic_bound_f 246467007 268435456 3 2 268435456 134217728 Ns384p984 Ns384p117 Ns384p985 Ns384p986 Ns384p120 Ns384p985 163016053 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 246467007) qz370 0 2 Ns384p984 Ns384p117 Ns384p985 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 246467007) qz371 0 2 Ns384p986 Ns384p120 Ns384p985 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p988 := nat_lit 29034045633674715545791664991128121323970131165929701535310328854729067455970067007372710615128424448199540625 

noncomputable def Ns384p989 := nat_lit 8903264828428391698264236048722636574218356848911055428760543154919314112831692921991939545078369140625 

noncomputable def Ns384p990 := nat_lit 145051889519078989139250460873659176118899726434870642194593492885522024181690890016446797947387306023521140625 

noncomputable def Ns384p991 := BSN.sin_dyadic_bound_f 379427765 268435456 4 3 268435456 134217728 Ns384p988 Ns384p156 Ns384p989 Ns384p990 Ns384p159 Ns384p989 265120563 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 379427765) qz372 0 3 Ns384p988 Ns384p156 Ns384p989 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 379427765) qz373 0 3 Ns384p990 Ns384p159 Ns384p989 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p992 := Ns384p926 141743 BSN.abs_quadSignPos (BSN.cos_quad_nat0 92 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 163016053 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 147 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 265120563 268435456) qz153 rfl rfl (Ns384p983 rfl) (Ns384p960 rfl) RS385to396.d35 RS385to396.d37 RS385to396.d39 RS385to396.d41 RS385to396.d17 (Ns384p987 rfl rfl) (Ns384p991 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p993 := nat_lit 10470559321319338928706420379315231892800710862871491367143774347097665 

noncomputable def Ns384p994 := nat_lit 444652024353976979606568216169338284927914110428159178505608787521 

noncomputable def Ns384p995 := nat_lit 27422173547796933612454595121094666504873883256103688941944685637695041 

noncomputable def Ns384p996 := BSN.sin_dyadic_bound_f 160695063 268435456 3 2 268435456 134217728 Ns384p993 Ns384p131 Ns384p994 Ns384p995 Ns384p134 Ns384p994 151267672 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 160695063) qz372 0 2 Ns384p993 Ns384p131 Ns384p994 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 160695063) qz373 0 2 Ns384p995 Ns384p134 Ns384p994 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p997 := Ns384p924 Bool.false 383378663 141743 Bool.true 160695063 14148475504056880 1 Bool.false 151267672 Bool.true Bool.false 335543625 153761 BSN.abs_quadSignNeg qz374 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 151267672 268435456) qz153 rfl (Ns384p992 rfl) (Ns384p960 rfl) RS385to396.d43 RS385to396.d45 RS385to396.d17 (Ns384p996 rfl rfl) rfl 

noncomputable def Ns384p998 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) 335543625 268435456 153761 268435456 335543625 268435456 153761 268435456 180143611969536000 335543625 134217728 153761 134217728 (Ns384p997 rfl rfl rfl rfl) 

noncomputable def Ns384p999 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz151) (Zeta.RiemannSiegel.correction qz152) 637095 2097152 1 16777216 21274027230231 35184372088832 3368602255411 79164837199872000 13553576378244018945 73786976294838206464 

noncomputable def Ns384p1000 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz151 1 1 0 1 637095 2097152 1 16777216 637095 2097152 1 16777216 

noncomputable abbrev qz159 := qz472

noncomputable def Ns384p1001 := @Enclosure.Real.IsNear.sqrt_image qz159 787921021973 6710886400 147541 6710886400 181790529 181790564 16777216 (@Enclosure.Real.IsNear.of_eq qz159 (@HMul.hMul Real Real Real qz5 qz150 qz3) Bool.false 787921021973 6710886400 147541 6710886400 (BSN.t_div_two_pi_mk qz150 737705 1000 qz153) (@Enclosure.Real.IsNear.mulLit_ff qz150 qz3 737705 1000 0 1 5340353 33554432 1 33554432 787921021973 6710886400 147541 6710886400 (Enclosure.Real.IsNear.const Bool.false 737705 1000) RS385to396.d48 rfl)) 

noncomputable abbrev qz743 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 737705 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz651 := qz743

noncomputable abbrev qz479 := qz651

noncomputable abbrev qz160 := qz479

noncomputable def Ns384p1002 := @Enclosure.Real.IsNear.sqrt_image qz160 363581093 33554432 35 33554432 55226252 55226258 16777216 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 363581093 33554432 35 33554432 363581093 33554432 35 33554432 (Ns384p1001 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns384p1003 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz160) 55226255 16777216 3 16777216 5096759 5096761 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz160) Bool.false 110452510 33554432 6 33554432 55226255 16777216 3 16777216 (Ns384p1002 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns384p1004 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz160)) Bool.false 10193520 33554432 2 33554432 637095 2097152 1 16777216 (Ns384p1003 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz161 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz473))

noncomputable abbrev qz652 := (@HMul.hMul Real Real Real qz707 qz742 qz742)

noncomputable abbrev qz480 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz652 qz647) qz594)

noncomputable abbrev qz162 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz480))

noncomputable def Ns384p1005 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz152) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz161) qz162) Bool.false 21274027230231 

noncomputable def Ns384p1006 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz161) qz162 32763397 16777216 433 

noncomputable def Ns384p1007 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz161) Bool.false 65526794 33554432 866 33554432 32763397 16777216 433 

noncomputable def Ns384p1008 := @Enclosure.Real.IsNear.recentre' qz161 Bool.false 17182283 33554432 1306514432 193273528320000 17182283 33554432 1275893 188743680000 

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz349 qz346 qz473)

noncomputable def Ns384p1009 := @Enclosure.Real.IsNear.cos_image qz163 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11010015) (@Nat.cast Real Real.instNatCast 2097152)) Bool.false 11010015 2097152 221 33554432 Bool.false 17182283 33554432 1 

noncomputable def Ns384p1010 := nat_lit 944512639557375637171665461 

noncomputable def Ns384p1011 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz152 884279719003555 140737488355328 1 500000000000000 28036773 33554432 35 33554432 24792349750206457728015 4722366482869645213696 Ns384p1010 

noncomputable def Ns384p1012 := @Enclosure.Real.IsNear.subLit_ff_p qz160 qz1 363581093 33554432 35 33554432 10 1 0 1 28036773 28036773 33554432 35 

noncomputable def Ns384p1013 := @Ns384p1012 33554432 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 363581093 33554432 35 33554432 363581093 33554432 35 33554432 (Ns384p1001 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns384p1014 := @Enclosure.Real.IsNear.recentre' qz163 Bool.false 24792349750206457728015 4722366482869645213696 Ns384p1010 Ns384p295 11010015 2097152 221 33554432 (@Ns384p1011 Ns384p295 RS385to396.d47 (Ns384p1013 rfl rfl) rfl) 

noncomputable def Ns384p1015 := nat_lit 1862692545788921929733790580588427031953041 

noncomputable def Ns384p1016 := BSN.sin_dyadic_bound_f 36943266611 68719476736 2 1 33554432 11531251 Ns384p1015 Ns384p181 Ns384p1015 Ns384p1015 Ns384p182 Ns384p1015 17182283 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 36943266611) qz368 0 1 Ns384p1015 Ns384p181 Ns384p1015 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 36943266611) qz369 0 1 Ns384p1015 Ns384p182 Ns384p1015 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1017 := @Ns384p1009 5760000 (Ns384p1014 rfl) (Enclosure.sfrac_false_div 11010015 2097152) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11010015) (@Nat.cast Real Real.instNatCast 2097152)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 162478204829367376281600) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 17182283 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 11010015 2097152 226375608064910080 72057594037927936 0 162478204829367376281600 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 17182283 33554432 162478204829367376281600 302231454903657293676544 36943266611 68719476736 11531251 11520000 (Ns384p1016 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p1018 := @Enclosure.Real.IsNear.inv_image qz161 17182283 33554432 1275893 188743680000 32762964 32763830 16777216 (Ns384p1008 (Ns384p1017 rfl rfl) rfl) rfl 

noncomputable def Ns384p1019 := @Enclosure.Real.IsNear.recentre' qz162 Bool.false 5194584 16777216 

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz349 qz346 qz480)

noncomputable def Ns384p1020 := @Enclosure.Real.IsNear.cos_image qz164 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 42144417)) qz378) Bool.true 42144417 33554432 

noncomputable def Ns384p1021 := nat_lit 199021385058432182223069112405 

noncomputable def Ns384p1022 := nat_lit 84654791117260603879550642109680017 

noncomputable def Ns384p1023 := @Enclosure.Real.IsNear.recentre' qz164 Bool.true Ns384p1021 Ns384p307 Ns384p1022 

noncomputable abbrev qz165 := qz480

noncomputable def Ns384p1024 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz165 884279719003555 140737488355328 1 500000000000000 225066097052071 

noncomputable abbrev qz481 := (@HSub.hSub Real Real Real qz583 qz652 qz647)

noncomputable abbrev qz166 := qz481

noncomputable def Ns384p1025 := @Enclosure.Real.IsNear.subLit_tf qz166 qz29 154697352874407 1125899906842624 3136980455 1125899906842624 1 16 

noncomputable abbrev qz482 := qz652

noncomputable abbrev qz167 := qz482

noncomputable def Ns384p1026 := @Enclosure.Real.IsNear.subLit_ff_n qz167 qz152 786060640253529 1125899906842624 1962575335 1125899906842624 28036773 33554432 35 33554432 

noncomputable def Ns384p1027 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz152 28036773 33554432 35 33554432 28036773 33554432 35 33554432 786060640253529 1125899906842624 

noncomputable def Ns384p1028 := nat_lit 6728401619220500715677785877496642149025589136602518122730456321 

noncomputable def Ns384p1029 := nat_lit 64791741944522487909851911563195676133695224709322207119351480320 

noncomputable def Ns384p1030 := nat_lit 9952229986862609757625936196335187593570178219038021294327041 

noncomputable def Ns384p1031 := nat_lit 20165300397687776927518105760097256071889627053369478325602714881 

noncomputable def Ns384p1032 := nat_lit 2915628387503511955943336020343805426016285111919499320370816614400 

noncomputable def Ns384p1033 := BSN.cos_dyadic_bound_f 42144417 33554432 3 2 16777216 5760000 Ns384p1028 Ns384p1029 Ns384p1030 Ns384p1031 Ns384p1032 Ns384p1030 5194584 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 42144417) (BSN.cosEvenQ 33554432) 0 2 Ns384p1028 Ns384p1029 Ns384p1030 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 42144417) (BSN.cosOddQ 33554432) 0 2 Ns384p1031 Ns384p1032 Ns384p1030 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1034 := @Ns384p1019 855108608 48318382080000 649323 2097152 835067 47185920000 (@Ns384p1020 147 8388608 Bool.false 5194584 16777216 1 5760000 (@Ns384p1023 Ns384p463 42144417 33554432 147 8388608 (@Ns384p1024 1125899906842624 3136980455 1125899906842624 Ns384p1021 Ns384p307 Ns384p1022 Ns384p463 RS385to396.d47 (@Ns384p1025 0 1 3601057552833136 225066097052071 1125899906842624 3136980455 1125899906842624 (@Ns384p1026 5190781807604294221824 154697352874407 1125899906842624 3136980455 1125899906842624 (@Ns384p1027 1962575335 1125899906842624 (Ns384p1013 rfl rfl) (Ns384p1013 rfl rfl) rfl) (Ns384p1013 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 42144417 33554432) (BSN.cos_neg_of_bound 42144417 33554432 Bool.false 5194584 16777216 1 5760000 (Ns384p1033 rfl rfl)) rfl rfl) 

noncomputable def Ns384p1035 := @Ns384p999 17216827161158843521 Ns384p921 (Ns384p1000 qz31 (@Enclosure.Real.IsNear.of_eq qz151 (@Inv.inv Real Real.instInv (Real.sqrt qz160)) Bool.false 637095 2097152 1 16777216 (BSN.rpow_neg_quarter_mk qz159 (BSN.t_div_two_pi_nonneg qz150 737705 1000 qz153)) Ns384p1004) rfl) (@Ns384p1005 35184372088832 3368602255411 79164837199872000 (BSN.correction_mk qz152 (BSN.cos_two_pi_p_ne_zero_mk qz150 737705 1000 10 qz153 rfl rfl (@BSN.floor_sqrt_eq_dec qz150 737705 1000 10 qz153 rfl rfl rfl))) (@Ns384p1006 16777216 649323 2097152 835067 47185920000 21274027230231 35184372088832 3368602255411 79164837199872000 (@Ns384p1007 16777216 (Ns384p1018 rfl rfl rfl rfl rfl) rfl) (Ns384p1034 rfl) rfl)) 

noncomputable def Ns384p1036 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz150) (hardyZApproximantRS₀ qz150) Bool.false 170913482278560845055 73786976294838206464 1538774893747348667521 Ns384p921 (@Eq.refl Real (hardyZApproximantRS₀ qz150)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz150) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz151) (Zeta.RiemannSiegel.correction qz152))) Bool.false 170913482278560845055 73786976294838206464 1538774893747348667521 Ns384p921 (BSN.hardyZApproximantRS₀_eq qz150 10 (@BSN.floor_sqrt_eq_dec qz150 737705 1000 10 qz153 rfl rfl rfl)) (@Ns384p923 170913482278560845055 73786976294838206464 1538774893747348667521 Ns384p921 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 10)) Bool.false 335543625 134217728 153761 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) (Ns384p998 (Ns384p997 rfl rfl rfl rfl) rfl rfl)) (Ns384p1035 rfl) rfl rfl)) 

theorem RS385to396.d58 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz150) Bool.false 170913482278560845055 73786976294838206464 1538774893747348667521 Ns384p921 := Ns384p1036 

noncomputable def Ns384p1037 := nat_lit 10625324586456701730816000 

noncomputable def Ns384p1038 := nat_lit 1613905692672047770403443048448 

noncomputable abbrev qz744 := (Enclosure.sfrac Bool.false 739024 1000)

noncomputable abbrev qz653 := qz744

noncomputable abbrev qz483 := qz653

noncomputable abbrev qz168 := qz483

noncomputable abbrev qz745 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 739024 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz654 := qz745

noncomputable abbrev qz484 := qz654

noncomputable abbrev qz169 := (@HPow.hPow Real Real Real qz350 qz484 qz352)

noncomputable abbrev qz746 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 739024 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz655 := qz746

noncomputable abbrev qz485 := qz655

noncomputable abbrev qz170 := qz485

noncomputable def Ns384p1039 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz169) (Zeta.RiemannSiegel.correction qz170)) 145649935 134217728 154041 134217728 1775331423578879927901 9444732965739290427392 129955584769403084833 Ns384p1037 Ns384p1038 

noncomputable def Ns384p1040 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.sin BSN.quadSignNeg 9 10 739024 1000 197 268435456 134217728 4503599627370496 Bool.false 373588749686 2567 618095470 48 84886744 8 

noncomputable def Ns384p1041 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 739024 1000 92 147 268435456 134217728 4503599627370496 Bool.false 373588749686 2567 

noncomputable def Ns384p1042 := Ns384p1041 558195838 48 94906264 8 589812974 48 89478488 8 Bool.true 270339244 115852 Bool.true 138887895 Bool.true 313551656 14148475504056880 1 Bool.false 233299739 Bool.false Bool.false 246959615 Bool.false Bool.true 105535458 

noncomputable def Ns384p1043 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 739024 1000 43 29 268435456 134217728 4503599627370496 Bool.false 373588749686 2567 

noncomputable def Ns384p1044 := Ns384p1043 480971758 48 109588312 8 522351262 48 101459064 8 Bool.true 201125444 85924 Bool.false 7807786 Bool.true 213303942 14148475504056880 1 Bool.false 7806685 Bool.false Bool.false 191554687 Bool.true Bool.true 270339244 

noncomputable def Ns384p1045 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 739024 1000 233 128 268435456 134217728 4503599627370496 Bool.false 373588749686 2567 

noncomputable def Ns384p1046 := Ns384p1045 372130544 47 134217720 8 432030192 47 120047984 16 Bool.true 112491486 50564 Bool.false 329165750 Bool.false 335918255 14148475504056880 1 Bool.false 252658088 Bool.true Bool.false 84288761 Bool.false Bool.true 201125444 

noncomputable def Ns384p1047 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 739024 1000 559 369 268435456 134217728 4503599627370496 Bool.false 373588749686 2567 

noncomputable def Ns384p1048 := Ns384p1047 186065264 47 189812528 16 294906480 47 154981288 8 Bool.true 268435320 2623 Bool.false 375551622 Bool.false 54192180 14148475504056880 1 Bool.false 264485671 Bool.false Bool.false 53824818 Bool.true Bool.true 112491486 

noncomputable def Ns384p1049 := nat_lit 560903443859894567453775469547060598265866516294487471 

noncomputable def Ns384p1050 := nat_lit 403027050067085836143066859437435428170257924096000 

noncomputable def Ns384p1051 := nat_lit 105811885486905675233591431659520000 

noncomputable def Ns384p1052 := nat_lit 469185237385199680159644758605206650880 

noncomputable abbrev qz656 := (@Eq.refl Real qz744)

noncomputable abbrev qz486 := qz656

noncomputable abbrev qz171 := qz486

noncomputable def Ns384p1053 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz168 739024 1000 2184626890304 16000000 1478048 4000 2000 Ns384p1051 Ns384p1052 qz171 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns384p1054 := nat_lit 735187361936041007453012583444723267359036560237510617989120 

noncomputable abbrev qz657 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1478048))))

noncomputable abbrev qz487 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 739024 4000) (Real.log (Enclosure.sfrac Bool.false 2184626890304 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz657))

noncomputable abbrev qz658 := (Enclosure.sfrac Bool.false 739024 2000)

noncomputable abbrev qz172 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz487 qz658) (@HMul.hMul Real Real Real qz349 qz658 (Real.log Real.pi)))

noncomputable def Ns384p1055 := @Enclosure.Real.IsNear.addLit_ft_p qz172 (Enclosure.sfrac Bool.true Ns384p1051 Ns384p1052) 1566945041082028527999 1125899906842624000 7341331660317211 768000000000000000000 Ns384p1051 Ns384p1052 0 1 Ns384p1054 

noncomputable def Ns384p1056 := nat_lit 6572243853590516583100317696000 

noncomputable abbrev qz173 := (@HSub.hSub Real Real Real qz355 qz487 qz658)

noncomputable def Ns384p1057 := @Enclosure.Real.IsNear.subLit_ff_p qz173 (@HMul.hMul Real Real Real qz5 qz658 (Real.log Real.pi)) 2043191050839041905023 1125899906842624000 12158603172931 3000000000000000000 1774154639829 4194304000 46189 8388608000 Ns384p1056 1566945041082028527999 1125899906842624000 

noncomputable def Ns384p1058 := nat_lit 4086382101678083810046000 

noncomputable abbrev qz174 := qz487

noncomputable def Ns384p1059 := @Enclosure.Real.IsNear.subLit_ff_p qz174 qz658 2459224577216273584511 1125899906842624000 12158603172931 3000000000000000000 739024 2000 0 1 Ns384p1058 2043191050839041905023 1125899906842624000 12158603172931 3000000000000000000 

noncomputable def Ns384p1060 := nat_lit 5537681444785787641247006537681993728 

noncomputable def Ns384p1061 := nat_lit 57179129722696137625829376 

noncomputable def Ns384p1062 := nat_lit 5041830090656770296851230325558043621546816008355840 

noncomputable def Ns384p1063 := nat_lit 701607193871127974729143280740599032147972456448 

noncomputable def Ns384p1064 := nat_lit 175652720645722856663377280010546006529671168 

noncomputable def Ns384p1065 := BSN.log_dyadic_bound 87474890304 4281778890304 3 2 Ns384p1062 134217728 46080000 Ns384p1063 Ns384p1064 5484783 4369253780608 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 87474890304) (BSN.artanhQ 4281778890304) 0 2 Ns384p1063 Ns384p1062 Ns384p1064 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz488 := (Real.log (Enclosure.sfrac Bool.false 2184626890304 16000000))

noncomputable def Ns384p1066 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 739024 4000) qz488 739024 4000 0 1 53252214307613799 4503599627370496 195312653 9000000000000000 2459666526654373762011 1125899906842624000 9021296129417 2250000000000000000 (Enclosure.Real.IsNear.const Bool.false 739024 4000) (BSN.isNear_log_sfrac 2184626890304 16000000 53252214307613799 4503599627370496 195312653 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2184626890304) qz358)) Bool.false Ns384p1061 Ns384p98 1000000783360000 46080000000000000000000 53252214307613799 4503599627370496 195312653 9000000000000000 (BSN.log_rat_reduce_isNear 2184626890304 16000000 17 4369253780608 4194304000000 5484783 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns384p1065 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns384p1067 := BSN.arctan_dyadic_bound_f 1000 1478048 1 0 16777216 5760000 0 1 1 0 1 1 11350 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1478048) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1478048) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns384p1068 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1478048))) 884279719003555 562949953421312 1 2000000000000000 11350 16777216 1 5760000 14829362368170615111680 883898876200355 562949953421312 3125000009 18000000000000000 qz15 (Ns384p1067 rfl) rfl rfl 

noncomputable abbrev qz489 := (@HMul.hMul Real Real Real qz579 qz584 qz657)

noncomputable abbrev qz175 := qz489

noncomputable abbrev qz490 := qz657

noncomputable abbrev qz176 := qz490

noncomputable def Ns384p1069 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 739024 4000) qz488) qz175 2459666526654373762011 1125899906842624000 9021296129417 2250000000000000000 883898876200355 2251799813685248 3125000009 72000000000000000 Ns384p1060 2459224577216273584511 1125899906842624000 12158603172931 3000000000000000000 (Ns384p1066 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz176 1 4 0 1 883898876200355 562949953421312 3125000009 18000000000000000 883898876200355 2251799813685248 3125000009 72000000000000000 qz366 Ns384p1068 rfl) 

noncomputable def Ns384p1070 := @Ns384p1055 Ns384p1049 Ns384p1050 7341331660317211 768000000000000000000 (@Ns384p1057 7341331660317211 768000000000000000000 (Ns384p1059 (Ns384p1069 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 739024 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz658 (Real.log Real.pi) 739024 2000 0 1 38410761 33554432 1 67108864 1774154639829 4194304000 46189 8388608000 (Enclosure.Real.IsNear.const Bool.false 739024 2000) RS385to396.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns384p1051 Ns384p1052) 

noncomputable def Ns384p1071 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz168) Bool.false Ns384p1049 Ns384p1050 7341331660317211 768000000000000000000 23349296855 16777216 161 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz168) (@HAdd.hAdd Real Real Real qz367 qz172 (Enclosure.sfrac Bool.true Ns384p1051 Ns384p1052)) Bool.false Ns384p1049 Ns384p1050 7341331660317211 768000000000000000000 Ns384p1053 (Ns384p1070 rfl rfl)) 

noncomputable def Ns384p1072 := BSN.cos_dyadic_bound_f 68668427 68719476736 1 0 33554432 11531251 0 1 1 0 1 1 33554415 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 68668427) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 68668427) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns384p1073 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz168) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23349296855) qz415) Bool.false 23349296855 16777216 161 16777216 Bool.true 33554415 33554432 1 5760000 (Ns384p1071 rfl) (Enclosure.sfrac_false_div 23349296855 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23349296855) qz415) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2416055519162117652480) qz427) 226375608064910080 72057594037927936 Bool.false 33554415 33554432 221 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q2 23349296855 16777216 226375608064910080 72057594037927936 221 2416055519162117652480 Ns384p509 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554415 33554432 2416055519162117652480 Ns384p509 68668427 68719476736 11531251 11520000 (Ns384p1072 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p1074 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz168) Bool.false Ns384p1049 Ns384p1050 7341331660317211 768000000000000000000 373588749686 268435456 2567 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz168) (@HAdd.hAdd Real Real Real qz367 qz172 (Enclosure.sfrac Bool.true Ns384p1051 Ns384p1052)) Bool.false Ns384p1049 Ns384p1050 7341331660317211 768000000000000000000 Ns384p1053 (Ns384p1070 rfl rfl)) 

noncomputable def Ns384p1075 := Ns384p1048 50564 BSN.abs_quadSignPos (BSN.cos_quad_nat3 559 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 264485671 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 369 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 53824818 268435456) qz171 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 1) Bool.true 33554415 33554432 922009 94371840000 268435320 268435456 2623 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz168)) Bool.true 33554415 33554432 922009 94371840000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz168) qz168) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz168)) Bool.true 33554415 33554432 944137216 96636764160000 33554415 33554432 922009 94371840000 (Ns384p1073 rfl rfl) rfl)) rfl) (Ns384p1074 rfl) RS385to396.d7 

noncomputable def Ns384p1076 := nat_lit 27864204120234922494197426762898058150749242024190404824150489977332229019190520841449444616243022701821628416 

noncomputable def Ns384p1077 := nat_lit 7871104972104656757292216848816544452667542291815260433014121090443745863217355878886155402890372386816 

noncomputable def Ns384p1078 := nat_lit 139212015800867457571841955181562399375895035387250718069144780469712386410268496723853760420662905680629272576 

noncomputable def Ns384p1079 := BSN.sin_dyadic_bound_f 375551622 268435456 4 3 268435456 134217728 Ns384p1076 Ns384p156 Ns384p1077 Ns384p1078 Ns384p159 Ns384p1077 264485671 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 375551622) qz372 0 3 Ns384p1076 Ns384p156 Ns384p1077 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 375551622) qz373 0 3 Ns384p1078 Ns384p159 Ns384p1077 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1080 := nat_lit 8624749443006105444313625760000 

noncomputable def Ns384p1081 := BSN.sin_dyadic_bound_f 54192180 268435456 2 1 268435456 134217728 Ns384p1080 Ns384p127 Ns384p1080 Ns384p1080 Ns384p128 Ns384p1080 53824818 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 54192180) qz372 0 1 Ns384p1080 Ns384p127 Ns384p1080 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 54192180) qz373 0 1 Ns384p1080 Ns384p128 Ns384p1080 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1082 := nat_lit 16436195393333325837828044372887686503244927953985950117683902291671094984902810462008279446459265000000000000 

noncomputable def Ns384p1083 := nat_lit 1617989436210028550079794982859138219009416941691901793030895911454721098005771636962890625000000000000 

noncomputable def Ns384p1084 := nat_lit 82143014519792219845153352317481928121709245774524249131132269399804205451701202292714849380733825000000000000 

noncomputable def Ns384p1085 := BSN.sin_dyadic_bound_f 329165750 268435456 4 3 268435456 134217728 Ns384p1082 Ns384p156 Ns384p1083 Ns384p1084 Ns384p159 Ns384p1083 252658088 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 329165750) qz372 0 3 Ns384p1082 Ns384p156 Ns384p1083 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 329165750) qz373 0 3 Ns384p1084 Ns384p159 Ns384p1083 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1086 := nat_lit 6861400732190646056005117092633217814672276157604895946588316511446605507474487324385733915321997232371890625 

noncomputable def Ns384p1087 := nat_lit 2064444762798236334648575284282652389880204164657917748394180135481726697326949581222893246777587890625 

noncomputable def Ns384p1088 := nat_lit 41585372032048854157740726780415738330583546784724333303943610102725019720807698098081586652877157966477490625 

noncomputable def Ns384p1089 := BSN.cos_dyadic_bound_f 335918255 268435456 4 3 268435456 134217728 Ns384p1086 Ns384p149 Ns384p1087 Ns384p1088 Ns384p152 Ns384p1087 84288761 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 335918255) qz370 0 3 Ns384p1086 Ns384p149 Ns384p1087 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 335918255) qz371 0 3 Ns384p1088 Ns384p152 Ns384p1087 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1090 := Ns384p1046 85924 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 233 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 252658088 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 128 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 84288761 268435456) qz171 rfl rfl (Ns384p1075 RS385to396.d9 RS385to396.d11 RS385to396.d13 RS385to396.d17 (Ns384p1079 rfl rfl) (Ns384p1081 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns384p1074 rfl) RS385to396.d19 RS385to396.d21 RS385to396.d23 RS385to396.d25 RS385to396.d17 (Ns384p1085 rfl rfl) (Ns384p1089 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns384p1091 := BSN.sin_dyadic_bound_f 7807786 268435456 1 0 268435456 134217728 0 1 1 0 1 1 7806685 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 7807786) qz372 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 7807786) qz373 0 0 rfl) rfl rfl 

noncomputable def Ns384p1092 := nat_lit 32508286757941275988894976324854080439627527135075765195247660755820800 

noncomputable def Ns384p1093 := nat_lit 4285396914839742518881916727853862545774253760389424846371499254016 

noncomputable def Ns384p1094 := nat_lit 85133812771031696578265795842772732992997984181014945013992605266452736 

noncomputable def Ns384p1095 := BSN.sin_dyadic_bound_f 213303942 268435456 3 2 268435456 134217728 Ns384p1092 Ns384p131 Ns384p1093 Ns384p1094 Ns384p134 Ns384p1093 191554687 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 213303942) qz372 0 2 Ns384p1092 Ns384p131 Ns384p1093 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 213303942) qz373 0 2 Ns384p1094 Ns384p134 Ns384p1093 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1096 := Ns384p1044 115852 BSN.abs_quadSignPos (BSN.cos_quad_nat3 43 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 7806685 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 29 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 191554687 268435456) qz171 rfl rfl (Ns384p1090 rfl rfl) (Ns384p1074 rfl) RS385to396.d27 RS385to396.d29 RS385to396.d31 RS385to396.d33 RS385to396.d17 (Ns384p1091 rfl rfl) (Ns384p1095 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p1097 := nat_lit 3245973009510363118541180702755349827557131347795373159747010602690625 

noncomputable def Ns384p1098 := nat_lit 138457079260806952638828318364752641985894583373673921049437890625 

noncomputable def Ns384p1099 := nat_lit 9737642114372567741718264451629319977387422254219372131398932932290625 

noncomputable def Ns384p1100 := BSN.cos_dyadic_bound_f 138887895 268435456 3 2 268435456 134217728 Ns384p1097 Ns384p117 Ns384p1098 Ns384p1099 Ns384p120 Ns384p1098 233299739 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 138887895) qz370 0 2 Ns384p1097 Ns384p117 Ns384p1098 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 138887895) qz371 0 2 Ns384p1099 Ns384p120 Ns384p1098 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1101 := nat_lit 151860548341250553138130187387115027276637822153301564840739719033651200 

noncomputable def Ns384p1102 := nat_lit 93427083229833213117080561899165526738261925563017960382443150114816 

noncomputable def Ns384p1103 := nat_lit 397578744663760290159579979389845470109808538712497307408937213321281536 

noncomputable def Ns384p1104 := BSN.sin_dyadic_bound_f 313551656 268435456 3 2 268435456 134217728 Ns384p1101 Ns384p131 Ns384p1102 Ns384p1103 Ns384p134 Ns384p1102 246959615 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 313551656) qz372 0 2 Ns384p1101 Ns384p131 Ns384p1102 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 313551656) qz373 0 2 Ns384p1103 Ns384p134 Ns384p1102 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1105 := Ns384p1042 142001 BSN.abs_quadSignPos (BSN.cos_quad_nat0 92 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 233299739 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 147 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 246959615 268435456) qz171 rfl rfl (Ns384p1096 rfl) (Ns384p1074 rfl) RS385to396.d35 RS385to396.d37 RS385to396.d39 RS385to396.d41 RS385to396.d17 (Ns384p1100 rfl rfl) (Ns384p1104 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p1106 := nat_lit 4784878085676240013736447655042970436973165851732067843378037312733440 

noncomputable def Ns384p1107 := nat_lit 92862911084153433297565032125830776078759987243678098539393597696 

noncomputable def Ns384p1108 := nat_lit 12531673208248397120893928753155766466054164000271306968116272038953216 

noncomputable def Ns384p1109 := BSN.sin_dyadic_bound_f 132123566 268435456 3 2 268435456 134217728 Ns384p1106 Ns384p131 Ns384p1107 Ns384p1108 Ns384p134 Ns384p1107 126853115 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 132123566) qz372 0 2 Ns384p1106 Ns384p131 Ns384p1107 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 132123566) qz373 0 2 Ns384p1108 Ns384p134 Ns384p1107 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1110 := Ns384p1040 Bool.true 105535458 142001 Bool.true 132123566 14148475504056880 1 Bool.false 126853115 Bool.true Bool.true 145649935 154041 BSN.abs_quadSignNeg qz374 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 126853115 268435456) qz171 rfl (Ns384p1105 rfl) (Ns384p1074 rfl) RS385to396.d43 RS385to396.d45 RS385to396.d17 (Ns384p1109 rfl rfl) rfl 

noncomputable def Ns384p1111 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) 145649935 268435456 154041 268435456 145649935 268435456 154041 268435456 78195213436190720 145649935 134217728 154041 134217728 (Ns384p1110 rfl rfl rfl rfl) 

noncomputable def Ns384p1112 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz169) (Zeta.RiemannSiegel.correction qz170) 10188969 33554432 1 33554432 174240536366229 281474976710656 15919121874683 395824185999360000 1775331423578879927901 9444732965739290427392 

noncomputable def Ns384p1113 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz169 1 1 0 1 10188969 33554432 1 33554432 10188969 33554432 1 33554432 

noncomputable abbrev qz177 := qz484

noncomputable def Ns384p1114 := @Enclosure.Real.IsNear.sqrt_image qz177 246665564717 2097152000 46189 2097152000 181952975 181953011 16777216 (@Enclosure.Real.IsNear.of_eq qz177 (@HMul.hMul Real Real Real qz5 qz168 qz3) Bool.false 246665564717 2097152000 46189 2097152000 (BSN.t_div_two_pi_mk qz168 739024 1000 qz171) (@Enclosure.Real.IsNear.mulLit_ff qz168 qz3 739024 1000 0 1 5340353 33554432 1 33554432 246665564717 2097152000 46189 2097152000 (Enclosure.Real.IsNear.const Bool.false 739024 1000) RS385to396.d48 rfl)) 

noncomputable abbrev qz747 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 739024 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz659 := qz747

noncomputable abbrev qz491 := qz659

noncomputable abbrev qz178 := qz491

noncomputable def Ns384p1115 := @Enclosure.Real.IsNear.sqrt_image qz178 181952993 16777216 9 8388608 55250921 55250928 16777216 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 363905986 33554432 36 33554432 181952993 16777216 9 8388608 (Ns384p1114 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns384p1116 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz178) 110501849 33554432 7 33554432 5094484 5094485 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz178) Bool.false 110501849 33554432 7 33554432 110501849 33554432 7 33554432 (Ns384p1115 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns384p1117 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz178)) Bool.false 10188969 33554432 1 33554432 10188969 33554432 1 33554432 (Ns384p1116 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz179 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz485))

noncomputable abbrev qz660 := (@HMul.hMul Real Real Real qz707 qz746 qz746)

noncomputable abbrev qz492 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz660 qz655) qz594)

noncomputable abbrev qz180 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz492))

noncomputable def Ns384p1118 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz170) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz179) qz180) Bool.false 174240536366229 

noncomputable def Ns384p1119 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz179) qz180 59562511 33554432 735 

noncomputable def Ns384p1120 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz179) Bool.false 59562511 33554432 735 33554432 59562511 33554432 735 

noncomputable def Ns384p1121 := @Enclosure.Real.IsNear.recentre' qz179 Bool.false 18902828 33554432 1341074432 193273528320000 4725707 8388608 1309643 188743680000 

noncomputable abbrev qz181 := (@HMul.hMul Real Real Real qz349 qz346 qz485)

noncomputable def Ns384p1122 := @Enclosure.Real.IsNear.cos_image qz181 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 178201603) qz378) Bool.false 178201603 33554432 227 33554432 Bool.false 18902828 33554432 1 

noncomputable def Ns384p1123 := nat_lit 242874678742302623061558271 

noncomputable def Ns384p1124 := nat_lit 36028797018963968000000000000000 

noncomputable def Ns384p1125 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz170 884279719003555 140737488355328 1 500000000000000 14180833 16777216 9 8388608 12539823020476339861315 2361183241434822606848 Ns384p1123 

noncomputable def Ns384p1126 := @Enclosure.Real.IsNear.subLit_ff_p qz178 qz1 181952993 16777216 9 8388608 10 1 0 1 14180833 14180833 16777216 9 

noncomputable def Ns384p1127 := @Ns384p1126 8388608 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 363905986 33554432 36 33554432 181952993 16777216 9 8388608 (Ns384p1114 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns384p1128 := @Enclosure.Real.IsNear.recentre' qz181 Bool.false 12539823020476339861315 2361183241434822606848 Ns384p1123 Ns384p1124 178201603 33554432 227 33554432 (@Ns384p1125 Ns384p1124 RS385to396.d47 (Ns384p1127 rfl rfl) rfl) 

noncomputable def Ns384p1129 := nat_lit 2893842689945971390939136 

noncomputable def Ns384p1130 := nat_lit 192885710450653803988076472621633047804264987434089193171156437181746747976523067555630625 

noncomputable def Ns384p1131 := nat_lit 180468656028383376705345110207518346455653528001341539704795567934989718275908111313435361280 

noncomputable def Ns384p1132 := nat_lit 8180143985371853688632016016527316875791040548122977357746295894470938011785625390625 

noncomputable def Ns384p1133 := nat_lit 505163616661450313158037738364059795260037972071250925865878127187412339372208000204590625 

noncomputable def Ns384p1134 := nat_lit 3308592027187028572931327020471169685020314680024594894587918745474811501724982040746314956800 

noncomputable def Ns384p1135 := BSN.sin_dyadic_bound_f 41123978035 68719476736 3 2 33554432 11531251 Ns384p1130 Ns384p1131 Ns384p1132 Ns384p1133 Ns384p1134 Ns384p1132 18902828 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 41123978035) qz368 0 2 Ns384p1130 Ns384p1131 Ns384p1132 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 41123978035) qz369 0 2 Ns384p1133 Ns384p1134 Ns384p1132 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1136 := @Ns384p1122 5760000 (Ns384p1128 rfl) (Enclosure.sfrac_false_div 178201603 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 178201603) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns384p1129) qz380) 226375608064910080 72057594037927936 Bool.false 18902828 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 178201603 33554432 226375608064910080 72057594037927936 0 Ns384p1129 Ns384p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 18902828 33554432 Ns384p1129 Ns384p98 41123978035 68719476736 11531251 11520000 (Ns384p1135 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p1137 := @Enclosure.Real.IsNear.inv_image qz179 4725707 8388608 1309643 188743680000 29780888 29781623 16777216 (Ns384p1121 (Ns384p1136 rfl rfl) rfl) rfl 

noncomputable def Ns384p1138 := @Enclosure.Real.IsNear.recentre' qz180 Bool.false 5850678 16777216 

noncomputable abbrev qz182 := (@HMul.hMul Real Real Real qz349 qz346 qz492)

noncomputable def Ns384p1139 := @Enclosure.Real.IsNear.cos_image qz182 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 5094331)) (@Nat.cast Real Real.instNatCast 4194304)) Bool.true 5094331 4194304 

noncomputable def Ns384p1140 := nat_lit 48114596645387862938632522525 

noncomputable def Ns384p1141 := nat_lit 39614081257132168796771975168 

noncomputable def Ns384p1142 := nat_lit 548154791688268904641301940999119 

noncomputable def Ns384p1143 := @Enclosure.Real.IsNear.recentre' qz182 Bool.true Ns384p1140 Ns384p1141 Ns384p1142 

noncomputable def Ns384p1144 := nat_lit 30223145490365729367654400000000000000 

noncomputable abbrev qz183 := qz492

noncomputable def Ns384p1145 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz183 884279719003555 140737488355328 1 500000000000000 54411059771455 

noncomputable abbrev qz493 := (@HSub.hSub Real Real Real qz583 qz660 qz655)

noncomputable abbrev qz184 := qz493

noncomputable def Ns384p1146 := @Enclosure.Real.IsNear.subLit_tf qz184 qz29 36818873727039 281474976710656 101562525 35184372088832 1 16 

noncomputable abbrev qz494 := qz660

noncomputable abbrev qz185 := qz494

noncomputable def Ns384p1147 := @Enclosure.Real.IsNear.subLit_ff_n qz185 qz170 201096024573889 281474976710656 63813789 35184372088832 14180833 16777216 9 8388608 

noncomputable def Ns384p1148 := @Enclosure.Real.IsNear.mulLit_ff qz170 qz170 14180833 16777216 9 8388608 14180833 16777216 9 8388608 201096024573889 281474976710656 

noncomputable def Ns384p1149 := nat_lit 350638624254574495304926897070385441240039779414711447521 

noncomputable def Ns384p1150 := nat_lit 3861888762982039923063034508418779142719222587902677483520 

noncomputable def Ns384p1151 := nat_lit 453625307695054009099250865100158646105379023567695841 

noncomputable def Ns384p1152 := nat_lit 1051008622148333377896582189480956006427908580196998950881 

noncomputable def Ns384p1153 := nat_lit 173784994334191796537836552878845061422365016455620486758400 

noncomputable def Ns384p1154 := BSN.cos_dyadic_bound_f 5094331 4194304 3 2 16777216 5760000 Ns384p1149 Ns384p1150 Ns384p1151 Ns384p1152 Ns384p1153 Ns384p1151 5850678 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 5094331) (BSN.cosEvenQ 4194304) 0 2 Ns384p1149 Ns384p1150 Ns384p1151 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 5094331) (BSN.cosOddQ 4194304) 0 2 Ns384p1152 Ns384p1153 Ns384p1151 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1155 := @Ns384p1138 1773577216 96636764160000 2925339 8388608 1732009 94371840000 (@Ns384p1139 305 16777216 Bool.false 5850678 16777216 1 5760000 (@Ns384p1143 Ns384p1144 5094331 4194304 305 16777216 (@Ns384p1145 281474976710656 101562525 35184372088832 Ns384p1140 Ns384p1141 Ns384p1142 Ns384p1144 RS385to396.d47 (@Ns384p1146 0 1 870576956343280 54411059771455 281474976710656 101562525 35184372088832 (@Ns384p1147 617718197395258343424 36818873727039 281474976710656 101562525 35184372088832 (@Ns384p1148 63813789 35184372088832 (Ns384p1127 rfl rfl) (Ns384p1127 rfl rfl) rfl) (Ns384p1127 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 5094331 4194304) (BSN.cos_neg_of_bound 5094331 4194304 Bool.false 5850678 16777216 1 5760000 (Ns384p1154 rfl rfl)) rfl rfl) 

noncomputable def Ns384p1156 := @Ns384p1112 129955584769403084833 Ns384p1037 (Ns384p1113 qz31 (@Enclosure.Real.IsNear.of_eq qz169 (@Inv.inv Real Real.instInv (Real.sqrt qz178)) Bool.false 10188969 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz177 (BSN.t_div_two_pi_nonneg qz168 739024 1000 qz171)) Ns384p1117) rfl) (@Ns384p1118 281474976710656 15919121874683 395824185999360000 (BSN.correction_mk qz170 (BSN.cos_two_pi_p_ne_zero_mk qz168 739024 1000 10 qz171 rfl rfl (@BSN.floor_sqrt_eq_dec qz168 739024 1000 10 qz171 rfl rfl rfl))) (@Ns384p1119 33554432 2925339 8388608 1732009 94371840000 174240536366229 281474976710656 15919121874683 395824185999360000 (@Ns384p1120 33554432 (Ns384p1137 rfl rfl rfl rfl rfl) rfl) (Ns384p1155 rfl) rfl)) 

noncomputable def Ns384p1157 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz168) (hardyZApproximantRS₀ qz168) Bool.true 12024534439087269979741 9444732965739290427392 12324586271874885836833 Ns384p1037 (@Eq.refl Real (hardyZApproximantRS₀ qz168)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz168) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz169) (Zeta.RiemannSiegel.correction qz170))) Bool.true 12024534439087269979741 9444732965739290427392 12324586271874885836833 Ns384p1037 (BSN.hardyZApproximantRS₀_eq qz168 10 (@BSN.floor_sqrt_eq_dec qz168 739024 1000 10 qz171 rfl rfl rfl)) (@Ns384p1039 12024534439087269979741 9444732965739290427392 12324586271874885836833 Ns384p1037 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 10)) Bool.true 145649935 134217728 154041 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (Ns384p1111 (Ns384p1110 rfl rfl rfl rfl) rfl rfl)) (Ns384p1156 rfl) rfl rfl)) 

theorem RS385to396.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz168) Bool.true 12024534439087269979741 9444732965739290427392 12324586271874885836833 Ns384p1037 := Ns384p1157 

noncomputable def Ns384p1158 := nat_lit 26614092237523886387958382592 

noncomputable abbrev qz748 := (Enclosure.sfrac Bool.false 740341 1000)

noncomputable abbrev qz661 := qz748

noncomputable abbrev qz495 := qz661

noncomputable abbrev qz186 := qz495

noncomputable abbrev qz749 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 740341 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz662 := qz749

noncomputable abbrev qz496 := qz662

noncomputable abbrev qz187 := (@HPow.hPow Real Real Real qz350 qz496 qz352)

noncomputable abbrev qz750 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 740341 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz663 := qz750

noncomputable abbrev qz497 := qz663

noncomputable abbrev qz188 := qz497

noncomputable def Ns384p1159 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz187) (Zeta.RiemannSiegel.correction qz188)) 70910347 134217728 19289 16777216 113576564994887455149 590295810358705651712 1631436493460950021 147573952589676412928000 Ns384p1158 

noncomputable def Ns384p1160 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz186) qz186 Real.sin BSN.quadSignNeg 9 10 740341 1000 197 268435456 134217728 4503599627370496 Bool.false 374431624572 2572 618095470 48 84886744 8 

noncomputable def Ns384p1161 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz186) qz186 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 740341 1000 92 147 268435456 134217728 4503599627370496 Bool.false 374431624572 2572 

noncomputable def Ns384p1162 := Ns384p1161 558195838 48 94906264 8 589812974 48 89478488 8 Bool.true 62787106 116055 Bool.true 31156928 Bool.true 247460456 14148475504056880 1 Bool.false 266629314 Bool.false Bool.false 213870124 Bool.false Bool.false 102770633 

noncomputable def Ns384p1163 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz186) qz186 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 740341 1000 43 29 268435456 134217728 4503599627370496 Bool.false 374431624572 2572 

noncomputable def Ns384p1164 := Ns384p1163 480971758 48 109588312 8 522351262 48 101459064 8 Bool.true 120220312 86074 Bool.false 217242867 Bool.true 58365668 14148475504056880 1 Bool.false 194293406 Bool.false Bool.false 57906877 Bool.true Bool.true 62787106 

noncomputable def Ns384p1165 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz186) qz186 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 740341 1000 234 129 268435456 134217728 4503599627370496 Bool.false 374431624572 2572 

noncomputable def Ns384p1166 := Ns384p1165 372130544 47 134217720 8 432030192 47 120047984 16 Bool.false 33113657 50650 Bool.false 260287282 Bool.false 188151950 14148475504056880 1 Bool.false 151824882 Bool.true Bool.false 173119811 Bool.true Bool.true 120220312 

noncomputable def Ns384p1167 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz186) qz186 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 740341 1000 561 370 268435456 134217728 4503599627370496 Bool.false 374431624572 2572 

noncomputable def Ns384p1168 := Ns384p1167 186065264 47 189812528 16 294906480 47 154981288 8 Bool.false 268435400 2623 Bool.false 130063699 Bool.false 87017803 14148475504056880 1 Bool.false 125034045 Bool.true Bool.false 254454402 Bool.true Bool.false 33113657 

noncomputable def Ns384p1169 := nat_lit 7447599536172924875753871973793962398077138103827738799191 

noncomputable def Ns384p1170 := nat_lit 5339291999916830011608715036890474920145524337357619200 

noncomputable def Ns384p1171 := nat_lit 106758077727981746489901950896480000 

noncomputable def Ns384p1172 := nat_lit 474224393080365126316940930174801398080 

noncomputable abbrev qz664 := (@Eq.refl Real qz748)

noncomputable abbrev qz498 := qz664

noncomputable abbrev qz189 := qz498

noncomputable def Ns384p1173 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz186 740341 1000 2192420185124 16000000 1480682 4000 2000 Ns384p1171 Ns384p1172 qz189 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns384p1174 := nat_lit 2383231851575335960241239031614067967384684193224876415741120 

noncomputable abbrev qz665 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1480682))))

noncomputable abbrev qz499 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 740341 4000) (Real.log (Enclosure.sfrac Bool.false 2192420185124 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz665))

noncomputable abbrev qz666 := (Enclosure.sfrac Bool.false 740341 2000)

noncomputable abbrev qz190 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz499 qz666) (@HMul.hMul Real Real Real qz349 qz666 (Real.log Real.pi)))

noncomputable def Ns384p1175 := @Enclosure.Real.IsNear.addLit_ft_p qz190 (Enclosure.sfrac Bool.true Ns384p1171 Ns384p1172) 5025537005237875445239 3602879701896396800 39223227195008753 4096000000000000000000 Ns384p1171 Ns384p1172 0 1 Ns384p1174 

noncomputable def Ns384p1176 := nat_lit 1686290397057379354517417492480000 

noncomputable abbrev qz191 := (@HSub.hSub Real Real Real qz355 qz499 qz666)

noncomputable def Ns384p1177 := @Enclosure.Real.IsNear.subLit_ff_p qz191 (@HMul.hMul Real Real Real qz5 qz666 (Real.log Real.pi)) 32761200519261689693651 18014398509481984000 16240051648797 4000000000000000000 28437061209501 67108864000 740341 134217728000 Ns384p1176 5025537005237875445239 3602879701896396800 

noncomputable def Ns384p1178 := nat_lit 65522401038523379387302000 

noncomputable abbrev qz192 := qz499

noncomputable def Ns384p1179 := @Enclosure.Real.IsNear.subLit_ff_p qz192 qz666 39429599422715890451923 18014398509481984000 16240051648797 4000000000000000000 740341 2000 0 1 Ns384p1178 32761200519261689693651 18014398509481984000 16240051648797 4000000000000000000 

noncomputable def Ns384p1180 := nat_lit 88787564633755604216985915390798331904 

noncomputable def Ns384p1181 := nat_lit 57196349578144960397443072 

noncomputable def Ns384p1182 := nat_lit 5078637104094455664380262071947346707761186752720640 

noncomputable def Ns384p1183 := nat_lit 835261107903743929530500068518162872726289451008 

noncomputable def Ns384p1184 := nat_lit 247122803586672652544412623954039560998544128 

noncomputable def Ns384p1185 := BSN.log_dyadic_bound 95268185124 4289572185124 3 2 Ns384p1182 134217728 46080000 Ns384p1183 Ns384p1184 5962730 4384840370248 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 95268185124) (BSN.artanhQ 4289572185124) 0 2 Ns384p1183 Ns384p1182 Ns384p1184 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz500 := (Real.log (Enclosure.sfrac Bool.false 2192420185124 16000000))

noncomputable def Ns384p1186 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 740341 4000) qz500 740341 4000 0 1 53268251547724903 4503599627370496 195312653 9000000000000000 39436670619094202411923 18014398509481984000 144597964834673 36000000000000000000 (Enclosure.Real.IsNear.const Bool.false 740341 4000) (BSN.isNear_log_sfrac 2192420185124 16000000 53268251547724903 4503599627370496 195312653 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2192420185124) qz358)) Bool.false Ns384p1181 Ns384p98 1000000783360000 46080000000000000000000 53268251547724903 4503599627370496 195312653 9000000000000000 (BSN.log_rat_reduce_isNear 2192420185124 16000000 17 4384840370248 4194304000000 5962730 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns384p1185 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns384p1187 := BSN.arctan_dyadic_bound_f 1000 1480682 1 0 16777216 5760000 0 1 1 0 1 1 11330 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1480682) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1480682) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns384p1188 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1480682))) 884279719003555 562949953421312 1 2000000000000000 11330 16777216 1 5760000 14829373627169683537920 883899547288995 562949953421312 3125000009 18000000000000000 qz15 (Ns384p1187 rfl) rfl rfl 

noncomputable abbrev qz501 := (@HMul.hMul Real Real Real qz579 qz584 qz665)

noncomputable abbrev qz193 := qz501

noncomputable abbrev qz502 := qz665

noncomputable abbrev qz194 := qz502

noncomputable def Ns384p1189 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 740341 4000) qz500) qz193 39436670619094202411923 18014398509481984000 144597964834673 36000000000000000000 883899547288995 2251799813685248 3125000009 72000000000000000 Ns384p1180 39429599422715890451923 18014398509481984000 16240051648797 4000000000000000000 (Ns384p1186 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz194 1 4 0 1 883899547288995 562949953421312 3125000009 18000000000000000 883899547288995 2251799813685248 3125000009 72000000000000000 qz366 Ns384p1188 rfl) 

noncomputable def Ns384p1190 := @Ns384p1175 Ns384p1169 Ns384p1170 39223227195008753 4096000000000000000000 (@Ns384p1177 39223227195008753 4096000000000000000000 (Ns384p1179 (Ns384p1189 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 740341 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz666 (Real.log Real.pi) 740341 2000 0 1 38410761 33554432 1 67108864 28437061209501 67108864000 740341 134217728000 (Enclosure.Real.IsNear.const Bool.false 740341 2000) RS385to396.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns384p1171 Ns384p1172) 

noncomputable def Ns384p1191 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz186) Bool.false Ns384p1169 Ns384p1170 39223227195008753 4096000000000000000000 46803953071 33554432 161 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz186) (@HAdd.hAdd Real Real Real qz367 qz190 (Enclosure.sfrac Bool.true Ns384p1171 Ns384p1172)) Bool.false Ns384p1169 Ns384p1170 39223227195008753 4096000000000000000000 Ns384p1173 (Ns384p1190 rfl rfl)) 

noncomputable def Ns384p1192 := nat_lit 7592811289832641571848192 

noncomputable def Ns384p1193 := nat_lit 3505107937295701414522978664472105169691228438509132946592197643684547744338753212641425563532577479939722753372705677564920470467272745761 

noncomputable def Ns384p1194 := nat_lit 2490426146108979897622094925605639171834255898483757554128116159840478267852329055519973889716256386226058868310127235602574447452961 

noncomputable def Ns384p1195 := nat_lit 17503797442575222769951080992213500077960032599272173207316675640966361759910204464139655627280075821766415297665172352723159789536787538721 

noncomputable def Ns384p1196 := BSN.sin_dyadic_bound_f 107900338119 68719476736 4 3 33554432 11531251 Ns384p1193 Ns384p108 Ns384p1194 Ns384p1195 Ns384p111 Ns384p1194 33554425 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107900338119) qz368 0 3 Ns384p1193 Ns384p108 Ns384p1194 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107900338119) qz369 0 3 Ns384p1195 Ns384p111 Ns384p1194 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1197 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz186) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46803953071) qz378) Bool.false 46803953071 33554432 161 16777216 Bool.false 33554425 33554432 1 5760000 (Ns384p1191 rfl) (Enclosure.sfrac_false_div 46803953071 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46803953071) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns384p1192) qz380) 226375608064910080 72057594037927936 Bool.false 33554425 33554432 221 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 46803953071 33554432 226375608064910080 72057594037927936 221 Ns384p1192 Ns384p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554425 33554432 Ns384p1192 Ns384p98 107900338119 68719476736 11531251 11520000 (Ns384p1196 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p1198 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz186) Bool.false Ns384p1169 Ns384p1170 39223227195008753 4096000000000000000000 374431624572 268435456 2572 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz186) (@HAdd.hAdd Real Real Real qz367 qz190 (Enclosure.sfrac Bool.true Ns384p1171 Ns384p1172)) Bool.false Ns384p1169 Ns384p1170 39223227195008753 4096000000000000000000 Ns384p1173 (Ns384p1190 rfl rfl)) 

noncomputable def Ns384p1199 := Ns384p1168 50650 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 561 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 125034045 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 370 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 254454402 268435456) qz189 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 1) Bool.false 33554425 33554432 922009 94371840000 268435400 268435456 2623 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz186)) Bool.false 33554425 33554432 922009 94371840000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz186) qz186) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz186)) Bool.false 33554425 33554432 944137216 96636764160000 33554425 33554432 922009 94371840000 (Ns384p1197 rfl rfl) rfl)) rfl) (Ns384p1198 rfl) RS385to396.d7 

noncomputable def Ns384p1200 := nat_lit 4493384894527306529145139945344150653738805192234141069882159353481505 

noncomputable def Ns384p1201 := nat_lit 81893382442717130909147518439536928115620396326145365263806810401 

noncomputable def Ns384p1202 := nat_lit 11768256420190419367644370760871492461908493070447746185766656905234721 

noncomputable def Ns384p1203 := BSN.sin_dyadic_bound_f 130063699 268435456 3 2 268435456 134217728 Ns384p1200 Ns384p131 Ns384p1201 Ns384p1202 Ns384p134 Ns384p1201 125034045 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 130063699) qz372 0 2 Ns384p1200 Ns384p131 Ns384p1201 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 130063699) qz373 0 2 Ns384p1202 Ns384p134 Ns384p1201 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1204 := nat_lit 500154415606583125728070730161939703407121717631460582356753953651041 

noncomputable def Ns384p1205 := nat_lit 3287493578923371231341553239037163221311104102009570213417515361 

noncomputable def Ns384p1206 := nat_lit 1500456671832591530441749507379341035894922530686177727929835025922401 

noncomputable def Ns384p1207 := BSN.cos_dyadic_bound_f 87017803 268435456 3 2 268435456 134217728 Ns384p1204 Ns384p117 Ns384p1205 Ns384p1206 Ns384p120 Ns384p1205 254454402 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 87017803) qz370 0 2 Ns384p1204 Ns384p117 Ns384p1205 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 87017803) qz371 0 2 Ns384p1206 Ns384p120 Ns384p1205 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1208 := nat_lit 40059825316240618680567147693335866437560910332571069953412620330189056 

noncomputable def Ns384p1209 := nat_lit 21068013459725520644651538033181468930326008521025112102884813291776 

noncomputable def Ns384p1210 := nat_lit 120137339921802405000412140003941236374822078980671159636032091363983616 

noncomputable def Ns384p1211 := BSN.cos_dyadic_bound_f 260287282 268435456 3 2 268435456 134217728 Ns384p1208 Ns384p117 Ns384p1209 Ns384p1210 Ns384p120 Ns384p1209 151824882 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 260287282) qz370 0 2 Ns384p1208 Ns384p117 Ns384p1209 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 260287282) qz371 0 2 Ns384p1210 Ns384p120 Ns384p1209 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1212 := nat_lit 19679354927089268860581220734189067402837437442810980735391612900000000 

noncomputable def Ns384p1213 := nat_lit 1570615176159501874370749105698029759453738364292050039062500000000 

noncomputable def Ns384p1214 := nat_lit 51538624765424779250868501662419284483058934869058000511676694500000000 

noncomputable def Ns384p1215 := BSN.sin_dyadic_bound_f 188151950 268435456 3 2 268435456 134217728 Ns384p1212 Ns384p131 Ns384p1213 Ns384p1214 Ns384p134 Ns384p1213 173119811 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 188151950) qz372 0 2 Ns384p1212 Ns384p131 Ns384p1213 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 188151950) qz373 0 2 Ns384p1214 Ns384p134 Ns384p1213 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1216 := Ns384p1166 86074 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 234 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 151824882 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 129 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 173119811 268435456) qz189 rfl rfl (Ns384p1199 RS385to396.d9 RS385to396.d11 RS385to396.d13 RS385to396.d17 (Ns384p1203 rfl rfl) (Ns384p1207 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns384p1198 rfl) RS385to396.d19 RS385to396.d21 RS385to396.d23 RS385to396.d25 RS385to396.d17 (Ns384p1211 rfl rfl) (Ns384p1215 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns384p1217 := nat_lit 34977197208051435252602584752135983449742823591091488545205937847765025 

noncomputable def Ns384p1218 := nat_lit 4960942633846803828055733160289733291287198460911823354587715831841 

noncomputable def Ns384p1219 := nat_lit 91598913066346578455380393640001392323997692036302898475822409489942561 

noncomputable def Ns384p1220 := BSN.sin_dyadic_bound_f 217242867 268435456 3 2 268435456 134217728 Ns384p1217 Ns384p131 Ns384p1218 Ns384p1219 Ns384p134 Ns384p1218 194293406 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 217242867) qz372 0 2 Ns384p1217 Ns384p131 Ns384p1218 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 217242867) qz373 0 2 Ns384p1219 Ns384p134 Ns384p1218 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1221 := nat_lit 11604591085621995342517482578176 

noncomputable def Ns384p1222 := BSN.sin_dyadic_bound_f 58365668 268435456 2 1 268435456 134217728 Ns384p1221 Ns384p127 Ns384p1221 Ns384p1221 Ns384p128 Ns384p1221 57906877 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 58365668) qz372 0 1 Ns384p1221 Ns384p127 Ns384p1221 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 58365668) qz373 0 1 Ns384p1221 Ns384p128 Ns384p1221 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1223 := Ns384p1164 116055 BSN.abs_quadSignPos (BSN.cos_quad_nat3 43 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 194293406 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 29 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 57906877 268435456) qz189 rfl rfl (Ns384p1216 rfl rfl) (Ns384p1198 rfl) RS385to396.d27 RS385to396.d29 RS385to396.d31 RS385to396.d33 RS385to396.d17 (Ns384p1220 rfl rfl) (Ns384p1222 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p1224 := nat_lit 942363643811458286317371129856 

noncomputable def Ns384p1225 := BSN.cos_dyadic_bound_f 31156928 268435456 2 1 268435456 134217728 Ns384p1224 Ns384p266 Ns384p1224 Ns384p1224 Ns384p267 Ns384p1224 266629314 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 31156928) qz370 0 1 Ns384p1224 Ns384p266 Ns384p1224 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 31156928) qz371 0 1 Ns384p1224 Ns384p267 Ns384p1224 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1226 := nat_lit 58893619373794803100058285634708649821576815745744812504118668453478400 

noncomputable def Ns384p1227 := nat_lit 14061979840445958197068718856116131451354201726364212474960429449216 

noncomputable def Ns384p1228 := nat_lit 154222426583054238472595493974660371034160896340822300214398957635239936 

noncomputable def Ns384p1229 := BSN.sin_dyadic_bound_f 247460456 268435456 3 2 268435456 134217728 Ns384p1226 Ns384p131 Ns384p1227 Ns384p1228 Ns384p134 Ns384p1227 213870124 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 247460456) qz372 0 2 Ns384p1226 Ns384p131 Ns384p1227 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 247460456) qz373 0 2 Ns384p1228 Ns384p134 Ns384p1227 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1230 := Ns384p1162 142251 BSN.abs_quadSignPos (BSN.cos_quad_nat0 92 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266629314 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 147 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 213870124 268435456) qz189 rfl rfl (Ns384p1223 rfl) (Ns384p1198 rfl) RS385to396.d35 RS385to396.d37 RS385to396.d39 RS385to396.d41 RS385to396.d17 (Ns384p1225 rfl rfl) (Ns384p1229 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p1231 := nat_lit 113781559128549333762533601868816 

noncomputable def Ns384p1232 := BSN.sin_dyadic_bound_f 103280414 268435456 2 1 268435456 134217728 Ns384p1231 Ns384p127 Ns384p1231 Ns384p1231 Ns384p128 Ns384p1231 100751070 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 103280414) qz372 0 1 Ns384p1231 Ns384p127 Ns384p1231 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 103280414) qz373 0 1 Ns384p1231 Ns384p128 Ns384p1231 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1233 := Ns384p1160 Bool.false 102770633 142251 Bool.true 103280414 14148475504056880 1 Bool.false 100751070 Bool.true Bool.false 70910347 154312 BSN.abs_quadSignNeg qz374 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 100751070 268435456) qz189 rfl (Ns384p1230 rfl) (Ns384p1198 rfl) RS385to396.d43 RS385to396.d45 RS385to396.d17 (Ns384p1232 rfl rfl) rfl 

noncomputable def Ns384p1234 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) 70910347 268435456 154312 268435456 70910347 268435456 154312 268435456 38069702664126464 70910347 134217728 19289 16777216 (Ns384p1233 rfl rfl rfl rfl) 

noncomputable def Ns384p1235 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz187) (Zeta.RiemannSiegel.correction qz188) 5092217 16777216 1 16777216 22303952285397 35184372088832 5747100594871 158329674399744000 113576564994887455149 590295810358705651712 

noncomputable def Ns384p1236 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz187 1 1 0 1 5092217 16777216 1 16777216 5092217 16777216 1 16777216 

noncomputable abbrev qz195 := qz496

noncomputable def Ns384p1237 := @Enclosure.Real.IsNear.sqrt_image qz195 3953682280373 33554432000 740341 33554432000 182115031 182115066 16777216 (@Enclosure.Real.IsNear.of_eq qz195 (@HMul.hMul Real Real Real qz5 qz186 qz3) Bool.false 3953682280373 33554432000 740341 33554432000 (BSN.t_div_two_pi_mk qz186 740341 1000 qz189) (@Enclosure.Real.IsNear.mulLit_ff qz186 qz3 740341 1000 0 1 5340353 33554432 1 33554432 3953682280373 33554432000 740341 33554432000 (Enclosure.Real.IsNear.const Bool.false 740341 1000) RS385to396.d48 rfl)) 

noncomputable abbrev qz751 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 740341 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz667 := qz751

noncomputable abbrev qz503 := qz667

noncomputable abbrev qz196 := qz503

noncomputable def Ns384p1238 := @Enclosure.Real.IsNear.sqrt_image qz196 364230097 33554432 35 33554432 55275520 55275527 16777216 (@Enclosure.Real.IsNear.recentre' qz196 Bool.false 364230097 33554432 35 33554432 364230097 33554432 35 33554432 (Ns384p1237 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns384p1239 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz196) 110551047 33554432 7 33554432 5092216 5092218 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz196) Bool.false 110551047 33554432 7 33554432 110551047 33554432 7 33554432 (Ns384p1238 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns384p1240 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz196)) Bool.false 10184434 33554432 2 33554432 5092217 16777216 1 16777216 (Ns384p1239 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz197 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz497))

noncomputable abbrev qz668 := (@HMul.hMul Real Real Real qz707 qz750 qz750)

noncomputable abbrev qz504 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz668 qz663) qz594)

noncomputable abbrev qz198 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz504))

noncomputable def Ns384p1241 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz188) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz197) qz198) Bool.false 22303952285397 

noncomputable def Ns384p1242 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz197) qz198 13697381 8388608 303 

noncomputable def Ns384p1243 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz197) Bool.false 54789524 33554432 606 33554432 13697381 8388608 303 

noncomputable def Ns384p1244 := @Enclosure.Real.IsNear.recentre' qz197 Bool.false 20549547 33554432 1306514432 193273528320000 20549547 33554432 1275893 188743680000 

noncomputable abbrev qz199 := (@HMul.hMul Real Real Real qz349 qz346 qz497)

noncomputable def Ns384p1245 := @Enclosure.Real.IsNear.cos_image qz199 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 45059513) qz394) Bool.false 45059513 8388608 221 33554432 Bool.false 20549547 33554432 1 

noncomputable def Ns384p1246 := nat_lit 944512639562950539081611829 

noncomputable def Ns384p1247 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz188 884279719003555 140737488355328 1 500000000000000 28685777 33554432 35 33554432 25366250824958640937235 4722366482869645213696 Ns384p1246 

noncomputable def Ns384p1248 := @Enclosure.Real.IsNear.subLit_ff_p qz196 qz1 364230097 33554432 35 33554432 10 1 0 1 28685777 28685777 33554432 35 

noncomputable def Ns384p1249 := @Ns384p1248 33554432 (@Enclosure.Real.IsNear.recentre' qz196 Bool.false 364230097 33554432 35 33554432 364230097 33554432 35 33554432 (Ns384p1237 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns384p1250 := @Enclosure.Real.IsNear.recentre' qz199 Bool.false 25366250824958640937235 4722366482869645213696 Ns384p1246 Ns384p295 45059513 8388608 221 33554432 (@Ns384p1247 Ns384p295 RS385to396.d47 (Ns384p1249 rfl rfl) rfl) 

noncomputable def Ns384p1251 := nat_lit 283867036655902049632169794617226924594425938123497014420382805913323598702704237073894945 

noncomputable def Ns384p1252 := nat_lit 17716314956201904022466560840693829554827300971650449123823472325439764604783260569121 

noncomputable def Ns384p1253 := nat_lit 743432602922195326906313087660899869642312498502823794183373539389225379840579543247851041 

noncomputable def Ns384p1254 := BSN.sin_dyadic_bound_f 45294625587 68719476736 3 2 33554432 11531251 Ns384p1251 Ns384p1131 Ns384p1252 Ns384p1253 Ns384p1134 Ns384p1252 20549547 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 45294625587) qz368 0 2 Ns384p1251 Ns384p1131 Ns384p1252 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 45294625587) qz369 0 2 Ns384p1253 Ns384p1134 Ns384p1252 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1255 := @Ns384p1245 5760000 (Ns384p1250 rfl) (Enclosure.sfrac_false_div 45059513 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 45059513) qz394) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 796831480146965001404416) (@Nat.cast Real Real.instNatCast Ns384p239)) 226375608064910080 72057594037927936 Bool.false 20549547 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 45059513 8388608 226375608064910080 72057594037927936 0 796831480146965001404416 Ns384p239 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 20549547 33554432 796831480146965001404416 Ns384p239 45294625587 68719476736 11531251 11520000 (Ns384p1254 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p1256 := @Enclosure.Real.IsNear.inv_image qz197 20549547 33554432 1275893 188743680000 27394459 27395065 16777216 (Ns384p1244 (Ns384p1255 rfl rfl) rfl) rfl 

noncomputable def Ns384p1257 := @Enclosure.Real.IsNear.recentre' qz198 Bool.false 6513348 16777216 

noncomputable abbrev qz200 := (@HMul.hMul Real Real Real qz349 qz346 qz504)

noncomputable def Ns384p1258 := @Enclosure.Real.IsNear.cos_image qz200 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 9832209)) qz394) Bool.true 9832209 8388608 

noncomputable def Ns384p1259 := nat_lit 185725177238246780874241464445 

noncomputable def Ns384p1260 := nat_lit 85880776079065429411623632900305353 

noncomputable def Ns384p1261 := @Enclosure.Real.IsNear.recentre' qz200 Bool.true Ns384p1259 Ns384p307 Ns384p1260 

noncomputable abbrev qz201 := qz504

noncomputable def Ns384p1262 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz201 884279719003555 140737488355328 1 500000000000000 210029895797599 

noncomputable abbrev qz505 := (@HSub.hSub Real Real Real qz583 qz668 qz663)

noncomputable abbrev qz202 := qz505

noncomputable def Ns384p1263 := @Enclosure.Real.IsNear.subLit_tf qz202 qz29 139661151619935 1125899906842624 3182410735 1125899906842624 1 16 

noncomputable abbrev qz506 := qz668

noncomputable abbrev qz203 := qz506

noncomputable def Ns384p1264 := @Enclosure.Real.IsNear.subLit_ff_n qz203 qz188 822873802093729 1125899906842624 2008005615 1125899906842624 28685777 33554432 35 33554432 

noncomputable def Ns384p1265 := @Enclosure.Real.IsNear.mulLit_ff qz188 qz188 28685777 33554432 35 33554432 28685777 33554432 35 33554432 822873802093729 1125899906842624 

noncomputable def Ns384p1266 := nat_lit 77832486169508127268696245177928125426573922717349657859201 

noncomputable def Ns384p1267 := nat_lit 988643523323402220304136834155207460536120982503085435781120 

noncomputable def Ns384p1268 := nat_lit 87339120249364599241793756445650453328296124779197781121 

noncomputable def Ns384p1269 := nat_lit 233322780268025652607605148020893075373065175902490578015361 

noncomputable def Ns384p1270 := nat_lit 44488958549553099913686157536984335724125444212638844610150400 

noncomputable def Ns384p1271 := BSN.cos_dyadic_bound_f 9832209 8388608 3 2 16777216 5760000 Ns384p1266 Ns384p1267 Ns384p1268 Ns384p1269 Ns384p1270 Ns384p1268 6513348 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 9832209) (BSN.cosEvenQ 8388608) 0 2 Ns384p1266 Ns384p1267 Ns384p1268 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 9832209) (BSN.cosOddQ 8388608) 0 2 Ns384p1269 Ns384p1270 Ns384p1268 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1272 := @Ns384p1257 866628608 48318382080000 1628337 4194304 846317 47185920000 (@Ns384p1258 149 8388608 Bool.false 6513348 16777216 1 5760000 (@Ns384p1261 Ns384p463 9832209 8388608 149 8388608 (@Ns384p1262 1125899906842624 3182410735 1125899906842624 Ns384p1259 Ns384p307 Ns384p1260 Ns384p463 RS385to396.d47 (@Ns384p1263 0 1 3360478332761584 210029895797599 1125899906842624 3182410735 1125899906842624 (@Ns384p1264 4686250615072798801920 139661151619935 1125899906842624 3182410735 1125899906842624 (@Ns384p1265 2008005615 1125899906842624 (Ns384p1249 rfl rfl) (Ns384p1249 rfl rfl) rfl) (Ns384p1249 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 9832209 8388608) (BSN.cos_neg_of_bound 9832209 8388608 Bool.false 6513348 16777216 1 5760000 (Ns384p1271 rfl rfl)) rfl rfl) 

noncomputable def Ns384p1273 := @Ns384p1235 1631436493460950021 147573952589676412928000 (Ns384p1236 qz31 (@Enclosure.Real.IsNear.of_eq qz187 (@Inv.inv Real Real.instInv (Real.sqrt qz196)) Bool.false 5092217 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz195 (BSN.t_div_two_pi_nonneg qz186 740341 1000 qz189)) Ns384p1240) rfl) (@Ns384p1241 35184372088832 5747100594871 158329674399744000 (BSN.correction_mk qz188 (BSN.cos_two_pi_p_ne_zero_mk qz186 740341 1000 10 qz189 rfl rfl (@BSN.floor_sqrt_eq_dec qz186 740341 1000 10 qz189 rfl rfl rfl))) (@Ns384p1242 16777216 1628337 4194304 846317 47185920000 22303952285397 35184372088832 5747100594871 158329674399744000 (@Ns384p1243 16777216 (Ns384p1256 rfl rfl rfl rfl rfl) rfl) (Ns384p1272 rfl) rfl)) 

noncomputable def Ns384p1274 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz186) (hardyZApproximantRS₀ qz186) Bool.false 198290439229636537939 590295810358705651712 171299274798831062021 147573952589676412928000 (@Eq.refl Real (hardyZApproximantRS₀ qz186)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz186) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz187) (Zeta.RiemannSiegel.correction qz188))) Bool.false 198290439229636537939 590295810358705651712 171299274798831062021 147573952589676412928000 (BSN.hardyZApproximantRS₀_eq qz186 10 (@BSN.floor_sqrt_eq_dec qz186 740341 1000 10 qz189 rfl rfl rfl)) (@Ns384p1159 198290439229636537939 590295810358705651712 171299274798831062021 147573952589676412928000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 10)) Bool.false 70910347 134217728 19289 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) (Ns384p1234 (Ns384p1233 rfl rfl rfl rfl) rfl rfl)) (Ns384p1273 rfl) rfl rfl)) 

theorem RS385to396.d60 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz186) Bool.false 198290439229636537939 590295810358705651712 171299274798831062021 147573952589676412928000 := Ns384p1274 

noncomputable def Ns384p1275 := nat_lit 1475739525896764129280000 

noncomputable def Ns384p1276 := nat_lit 40318023683790367014673973248 

noncomputable abbrev qz752 := (Enclosure.sfrac Bool.false 741658 1000)

noncomputable abbrev qz669 := qz752

noncomputable abbrev qz507 := qz669

noncomputable abbrev qz204 := qz507

noncomputable abbrev qz205 := qz350

noncomputable abbrev qz753 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 741658 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz670 := qz753

noncomputable abbrev qz508 := qz670

noncomputable abbrev qz206 := qz508

noncomputable abbrev qz207 := qz352

noncomputable abbrev qz754 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 741658 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz671 := qz754

noncomputable abbrev qz509 := qz671

noncomputable abbrev qz208 := qz509

noncomputable abbrev qz672 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz205 qz206 qz207))

noncomputable def Ns384p1277 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) (@HMul.hMul Real Real Real qz5 qz672 (Zeta.RiemannSiegel.correction qz208)) 10465131 33554432 38647 33554432 465152613734314455755 2361183241434822606848 15327132399734988711 Ns384p1275 Ns384p1276 

noncomputable def Ns384p1278 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.sin BSN.quadSignNeg 9 10 741658 1000 197 268435456 134217728 4503599627370496 Bool.false 375274814081 2576 618095470 48 84886744 8 

noncomputable def Ns384p1279 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 741658 1000 91 147 268435456 134217728 4503599627370496 Bool.false 375274814081 2576 

noncomputable def Ns384p1280 := Ns384p1279 558195838 48 94906264 8 589812974 48 89478488 8 Bool.true 165635810 116263 Bool.true 344768766 Bool.true 181054634 14148475504056880 1 Bool.false 257498827 Bool.false Bool.false 167635822 Bool.false Bool.true 18717620 

noncomputable def Ns384p1281 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 741658 1000 44 28 268435456 134217728 4503599627370496 Bool.false 375274814081 2576 

noncomputable def Ns384p1282 := Ns384p1281 480971758 48 109588312 8 522351262 48 101459064 8 Bool.true 311032474 86229 Bool.false 5335142 Bool.true 324770199 14148475504056880 1 Bool.false 268382439 Bool.false Bool.false 94797262 Bool.false Bool.true 165635810 

noncomputable def Ns384p1283 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 741658 1000 235 130 268435456 134217728 4503599627370496 Bool.false 375274814081 2576 

noncomputable def Ns384p1284 := Ns384p1283 372130544 47 134217720 8 432030192 47 120047984 16 Bool.true 280278674 50743 Bool.false 191723436 Bool.false 40700268 14148475504056880 1 Bool.false 175833912 Bool.false Bool.false 265355868 Bool.true Bool.true 311032474 

noncomputable def Ns384p1285 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 741658 1000 562 371 268435456 134217728 4503599627370496 Bool.false 375274814081 2576 

noncomputable def Ns384p1286 := Ns384p1285 186065264 47 189812528 16 294906480 47 154981288 8 Bool.true 268435288 2631 Bool.false 306547827 Bool.false 120158050 14148475504056880 1 Bool.false 111614097 Bool.true Bool.false 116185442 Bool.false Bool.true 280278674 

noncomputable def Ns384p1287 := nat_lit 294702996471775282286531476590675546771018850329355299311 

noncomputable def Ns384p1288 := nat_lit 210802138257487420542921701938846578810610922815488000 

noncomputable def Ns384p1289 := nat_lit 107711026737323666656234395888640000 

noncomputable def Ns384p1290 := nat_lit 479308569668972769575070064863317790720 

noncomputable abbrev qz755 := (@Eq.refl Real (Enclosure.sfrac Bool.false 741658 1000))

noncomputable abbrev qz673 := qz755

noncomputable abbrev qz510 := qz673

noncomputable abbrev qz209 := qz510

noncomputable def Ns384p1291 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz204 741658 1000 2200227355856 16000000 1483316 4000 2000 Ns384p1289 Ns384p1290 qz209 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns384p1292 := nat_lit 6035517367741957781228164640577035197870466054745196529889280 

noncomputable abbrev qz674 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1483316))))

noncomputable abbrev qz511 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 741658 4000) (Real.log (Enclosure.sfrac Bool.false 2200227355856 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz674))

noncomputable abbrev qz675 := (Enclosure.sfrac Bool.false 741658 2000)

noncomputable abbrev qz210 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz511 qz675) (@HMul.hMul Real Real Real qz349 qz675 (Real.log Real.pi)))

noncomputable def Ns384p1293 := @Enclosure.Real.IsNear.addLit_ft_p qz210 (Enclosure.sfrac Bool.true Ns384p1289 Ns384p1290) 12592135254508337281499 9007199254740992000 58939028302488571 6144000000000000000000 Ns384p1289 Ns384p1290 0 1 Ns384p1292 

noncomputable def Ns384p1294 := nat_lit 422521946132202696745123053568000 

noncomputable abbrev qz211 := (@HSub.hSub Real Real Real qz355 qz511 qz675)

noncomputable def Ns384p1295 := @Enclosure.Real.IsNear.subLit_ff_p qz211 (@HMul.hMul Real Real Real qz5 qz675 (Real.log Real.pi)) 16415682669524542732763 9007199254740992000 24402948600529 6000000000000000000 14243824090869 33554432000 370829 67108864000 Ns384p1294 12592135254508337281499 9007199254740992000 

noncomputable def Ns384p1296 := nat_lit 32831365339049085465526000 

noncomputable abbrev qz212 := qz511

noncomputable def Ns384p1297 := @Enclosure.Real.IsNear.subLit_ff_p qz212 qz675 19755813361960890055131 9007199254740992000 24402948600529 6000000000000000000 741658 2000 0 1 Ns384p1296 16415682669524542732763 9007199254740992000 24402948600529 6000000000000000000 

noncomputable def Ns384p1298 := nat_lit 44486136847664065134114521479001407488 

noncomputable def Ns384p1299 := nat_lit 57213538845145114068647936 

noncomputable def Ns384p1300 := nat_lit 5115711350785395413379200262841348195793142311485440 

noncomputable def Ns384p1301 := nat_lit 981379457615738301922668425886487473291558125568 

noncomputable def Ns384p1302 := nat_lit 338641848449181725090652324769055146094297088 

noncomputable def Ns384p1303 := BSN.log_dyadic_bound 103075355856 4297379355856 3 2 Ns384p1300 134217728 46080000 Ns384p1301 Ns384p1302 6439828 4400454711712 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 103075355856) (BSN.artanhQ 4297379355856) 0 2 Ns384p1301 Ns384p1300 Ns384p1302 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz512 := (Real.log (Enclosure.sfrac Bool.false 2200227355856 16000000))

noncomputable def Ns384p1304 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 741658 4000) qz512 741658 4000 0 1 53284260300123239 4503599627370496 195312653 9000000000000000 19759348962834400595131 9007199254740992000 72427595799337 18000000000000000000 (Enclosure.Real.IsNear.const Bool.false 741658 4000) (BSN.isNear_log_sfrac 2200227355856 16000000 53284260300123239 4503599627370496 195312653 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2200227355856) qz358)) Bool.false Ns384p1299 Ns384p98 1000000783360000 46080000000000000000000 53284260300123239 4503599627370496 195312653 9000000000000000 (BSN.log_rat_reduce_isNear 2200227355856 16000000 17 4400454711712 4194304000000 6439828 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns384p1303 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns384p1305 := BSN.arctan_dyadic_bound_f 1000 1483316 1 0 16777216 5760000 0 1 1 0 1 1 11310 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1483316) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1483316) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns384p1306 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1483316))) 884279719003555 562949953421312 1 2000000000000000 11310 16777216 1 5760000 14829384886168751964160 883900218377635 562949953421312 3125000009 18000000000000000 qz15 (Ns384p1305 rfl) rfl rfl 

noncomputable abbrev qz513 := (@HMul.hMul Real Real Real qz579 qz584 qz674)

noncomputable abbrev qz213 := qz513

noncomputable abbrev qz514 := qz674

noncomputable abbrev qz214 := qz514

noncomputable def Ns384p1307 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 741658 4000) qz512) qz213 19759348962834400595131 9007199254740992000 72427595799337 18000000000000000000 883900218377635 2251799813685248 3125000009 72000000000000000 Ns384p1298 19755813361960890055131 9007199254740992000 24402948600529 6000000000000000000 (Ns384p1304 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz214 1 4 0 1 883900218377635 562949953421312 3125000009 18000000000000000 883900218377635 2251799813685248 3125000009 72000000000000000 qz366 Ns384p1306 rfl) 

noncomputable def Ns384p1308 := @Ns384p1293 Ns384p1287 Ns384p1288 58939028302488571 6144000000000000000000 (@Ns384p1295 58939028302488571 6144000000000000000000 (Ns384p1297 (Ns384p1307 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 741658 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz675 (Real.log Real.pi) 741658 2000 0 1 38410761 33554432 1 67108864 14243824090869 33554432000 370829 67108864000 (Enclosure.Real.IsNear.const Bool.false 741658 2000) RS385to396.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns384p1289 Ns384p1290) 

noncomputable def Ns384p1309 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz204) Bool.false Ns384p1287 Ns384p1288 58939028302488571 6144000000000000000000 2931834485 2097152 323 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz204) (@HAdd.hAdd Real Real Real qz367 qz210 (Enclosure.sfrac Bool.true Ns384p1289 Ns384p1290)) Bool.false Ns384p1287 Ns384p1288 58939028302488571 6144000000000000000000 Ns384p1291 (Ns384p1308 rfl rfl)) 

noncomputable def Ns384p1310 := nat_lit 3500931941245707966881669104930580699011527681035941748554791657347147170685310020230740296182441757232098333822346479068937951367291644161 

noncomputable def Ns384p1311 := nat_lit 2481553212306616708846818830730062049194419951726991228955744024784349809338486363132649890671273222384967665314936522454406370863361 

noncomputable def Ns384p1312 := nat_lit 17482969147286914154454818266987947729339318606417956652120553211976490769020135230394467853803217338194899692874808170632041573308022565121 

noncomputable def Ns384p1313 := BSN.sin_dyadic_bound_f 107868249919 68719476736 4 3 33554432 11531251 Ns384p1310 Ns384p108 Ns384p1311 Ns384p1312 Ns384p111 Ns384p1311 33554411 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107868249919) qz368 0 3 Ns384p1310 Ns384p108 Ns384p1311 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107868249919) qz369 0 3 Ns384p1312 Ns384p111 Ns384p1311 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1314 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz204) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2931834485) (@Nat.cast Real Real.instNatCast 2097152)) Bool.false 2931834485 2097152 323 33554432 Bool.true 33554411 33554432 1 5760000 (Ns384p1309 rfl) (Enclosure.sfrac_false_div 2931834485 2097152) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2931834485) (@Nat.cast Real Real.instNatCast 2097152)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474409580216933081415680) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 33554411 33554432 222 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q1 2931834485 2097152 226375608064910080 72057594037927936 222 474409580216933081415680 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554411 33554432 474409580216933081415680 302231454903657293676544 107868249919 68719476736 11531251 11520000 (Ns384p1313 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p1315 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz204) Bool.false Ns384p1287 Ns384p1288 58939028302488571 6144000000000000000000 375274814081 268435456 2576 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz204) (@HAdd.hAdd Real Real Real qz367 qz210 (Enclosure.sfrac Bool.true Ns384p1289 Ns384p1290)) Bool.false Ns384p1287 Ns384p1288 58939028302488571 6144000000000000000000 Ns384p1291 (Ns384p1308 rfl rfl)) 

noncomputable def Ns384p1316 := Ns384p1286 50743 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 562 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 111614097 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 371 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 116185442 268435456) qz209 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 1) Bool.true 33554411 33554432 1849643 188743680000 268435288 268435456 2631 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz204)) Bool.true 33554411 33554432 1849643 188743680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz204) qz204) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz204)) Bool.true 33554411 33554432 1894034432 193273528320000 33554411 33554432 1849643 188743680000 (Ns384p1314 rfl rfl) rfl)) rfl) (Ns384p1315 rfl) RS385to396.d7 

noncomputable def Ns384p1317 := nat_lit 4756387298784147641671402429403624293947117090156297408405236447262259904016649344124394378861100542366049201 

noncomputable def Ns384p1318 := nat_lit 688618844253789356815191470310912832866037233782425239381524159510094240316253202573363957794215551921 

noncomputable def Ns384p1319 := nat_lit 28835958259327610799851314058101353998412299126187987656278525252499306678884468490674195950794199078393078705 

noncomputable def Ns384p1320 := BSN.cos_dyadic_bound_f 306547827 268435456 4 3 268435456 134217728 Ns384p1317 Ns384p149 Ns384p1318 Ns384p1319 Ns384p152 Ns384p1318 111614097 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 306547827) qz370 0 3 Ns384p1317 Ns384p149 Ns384p1318 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 306547827) qz371 0 3 Ns384p1319 Ns384p152 Ns384p1318 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1321 := nat_lit 3273094570943335709440909214538905740403769814771556241482332900000000 

noncomputable def Ns384p1322 := nat_lit 43453320991012808389905726661448867876553650132737539062500000000 

noncomputable def Ns384p1323 := nat_lit 8572320189950941408750702381187301260033311285158622866914294500000000 

noncomputable def Ns384p1324 := BSN.sin_dyadic_bound_f 120158050 268435456 3 2 268435456 134217728 Ns384p1321 Ns384p131 Ns384p1322 Ns384p1323 Ns384p134 Ns384p1322 116185442 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 120158050) qz372 0 2 Ns384p1321 Ns384p131 Ns384p1322 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 120158050) qz373 0 2 Ns384p1323 Ns384p134 Ns384p1322 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1325 := nat_lit 21216780629261141170463465963226924207369994676641692513414638452408320 

noncomputable def Ns384p1326 := nat_lit 1825583195035905288231996633616811465059538944395673241945762758656 

noncomputable def Ns384p1327 := nat_lit 55564803084796740171223368575806564753120842042437315968932331378507776 

noncomputable def Ns384p1328 := BSN.sin_dyadic_bound_f 191723436 268435456 3 2 268435456 134217728 Ns384p1325 Ns384p131 Ns384p1326 Ns384p1327 Ns384p134 Ns384p1326 175833912 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 191723436) qz372 0 2 Ns384p1325 Ns384p131 Ns384p1326 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 191723436) qz373 0 2 Ns384p1327 Ns384p134 Ns384p1326 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1329 := nat_lit 2744031394135153560275008286976 

noncomputable def Ns384p1330 := BSN.cos_dyadic_bound_f 40700268 268435456 2 1 268435456 134217728 Ns384p1329 Ns384p266 Ns384p1329 Ns384p1329 Ns384p267 Ns384p1329 265355868 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 40700268) qz370 0 1 Ns384p1329 Ns384p266 Ns384p1329 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 40700268) qz371 0 1 Ns384p1329 Ns384p267 Ns384p1329 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1331 := Ns384p1284 86229 BSN.abs_quadSignPos (BSN.cos_quad_nat3 235 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 175833912 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 130 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 265355868 268435456) qz209 rfl rfl (Ns384p1316 RS385to396.d9 RS385to396.d11 RS385to396.d13 RS385to396.d17 (Ns384p1320 rfl rfl) (Ns384p1324 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns384p1315 rfl) RS385to396.d19 RS385to396.d21 RS385to396.d23 RS385to396.d25 RS385to396.d17 (Ns384p1328 rfl rfl) (Ns384p1330 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns384p1332 := nat_lit 810184503905332932372506896 

noncomputable def Ns384p1333 := BSN.cos_dyadic_bound_f 5335142 268435456 2 1 268435456 134217728 Ns384p1332 Ns384p266 Ns384p1332 Ns384p1332 Ns384p267 Ns384p1332 268382439 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 5335142) qz370 0 1 Ns384p1332 Ns384p266 Ns384p1332 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 5335142) qz371 0 1 Ns384p1332 Ns384p267 Ns384p1332 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1334 := nat_lit 5993811344826271390266900024674449755282205287142510069367707469955560764607202840258688310134687754489264481 

noncomputable def Ns384p1335 := nat_lit 1376936958529446171632692215454192965321142331741595297878270142161403210635615721183729618483673397601 

noncomputable def Ns384p1336 := nat_lit 36331570868278469033293171811694723354738133838307551415000475511917991668380399173948552801630345240470976865 

noncomputable def Ns384p1337 := BSN.cos_dyadic_bound_f 324770199 268435456 4 3 268435456 134217728 Ns384p1334 Ns384p149 Ns384p1335 Ns384p1336 Ns384p152 Ns384p1335 94797262 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 324770199) qz370 0 3 Ns384p1334 Ns384p149 Ns384p1335 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 324770199) qz371 0 3 Ns384p1336 Ns384p152 Ns384p1335 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1338 := Ns384p1282 116263 BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268382439 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 94797262 268435456) qz209 rfl rfl (Ns384p1331 rfl rfl) (Ns384p1315 rfl) RS385to396.d27 RS385to396.d29 RS385to396.d31 RS385to396.d33 RS385to396.d17 (Ns384p1333 rfl rfl) (Ns384p1337 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p1339 := nat_lit 19784288805757788779676753022772908593313834128137437423331120825915789855633397349317782639261430104415277056 

noncomputable def Ns384p1340 := nat_lit 2820557600994380245442447262316272167773913299974264070375479806167765455932675997964135313923962310656 

noncomputable def Ns384p1341 := nat_lit 98866455074643279731520815710134577927819275197367949150264780291119058761919162743928390731129626994849878016 

noncomputable def Ns384p1342 := BSN.sin_dyadic_bound_f 344768766 268435456 4 3 268435456 134217728 Ns384p1339 Ns384p156 Ns384p1340 Ns384p1341 Ns384p159 Ns384p1340 257498827 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 344768766) qz372 0 3 Ns384p1339 Ns384p156 Ns384p1340 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 344768766) qz373 0 3 Ns384p1341 Ns384p159 Ns384p1340 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1343 := nat_lit 16873671960569899134615580219360306716097577458517401810865212003344640 

noncomputable def Ns384p1344 := nat_lit 1154721251663887886757622097541999512835842715779674399195704484096 

noncomputable def Ns384p1345 := nat_lit 44191080824227994295986054900642878161996682931720028127048286011023616 

noncomputable def Ns384p1346 := BSN.sin_dyadic_bound_f 181054634 268435456 3 2 268435456 134217728 Ns384p1343 Ns384p131 Ns384p1344 Ns384p1345 Ns384p134 Ns384p1344 167635822 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 181054634) qz372 0 2 Ns384p1343 Ns384p131 Ns384p1344 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 181054634) qz373 0 2 Ns384p1345 Ns384p134 Ns384p1344 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1347 := Ns384p1280 142505 BSN.abs_quadSignPos (BSN.cos_quad_nat3 91 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 257498827 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 147 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 167635822 268435456) qz209 rfl rfl (Ns384p1338 rfl) (Ns384p1315 rfl) RS385to396.d35 RS385to396.d37 RS385to396.d39 RS385to396.d41 RS385to396.d17 (Ns384p1342 rfl rfl) (Ns384p1346 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p1348 := nat_lit 30185855775647081115004088111041 

noncomputable def Ns384p1349 := BSN.sin_dyadic_bound_f 74122639 268435456 2 1 268435456 134217728 Ns384p1348 Ns384p127 Ns384p1348 Ns384p1348 Ns384p128 Ns384p1348 73184286 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 74122639) qz372 0 1 Ns384p1348 Ns384p127 Ns384p1348 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 74122639) qz373 0 1 Ns384p1348 Ns384p128 Ns384p1348 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1350 := Ns384p1278 Bool.true 18717620 142505 Bool.true 74122639 14148475504056880 1 Bool.false 73184286 Bool.true Bool.true 41860524 154588 BSN.abs_quadSignNeg qz374 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 73184286 268435456) qz209 rfl (Ns384p1347 rfl) (Ns384p1315 rfl) RS385to396.d43 RS385to396.d45 RS385to396.d17 (Ns384p1349 rfl rfl) rfl 

noncomputable def Ns384p1351 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) 41860524 268435456 154588 268435456 41860524 268435456 154588 268435456 22473697696677888 10465131 33554432 38647 33554432 (Ns384p1350 rfl rfl rfl rfl) 

noncomputable def Ns384p1352 := @Enclosure.Real.IsNear.mulLit_ff qz672 (Zeta.RiemannSiegel.correction qz208) 5089955 16777216 1 16777216 91386390200761 140737488355328 18000174350261 527765581332480000 465152613734314455755 2361183241434822606848 

noncomputable abbrev qz676 := (@HPow.hPow Real Real Real qz205 qz206 qz207)

noncomputable def Ns384p1353 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz676 1 1 0 1 5089955 16777216 1 16777216 5089955 16777216 1 16777216 

noncomputable def Ns384p1354 := @Enclosure.Real.IsNear.sqrt_image qz206 1980357762637 16777216000 370829 16777216000 182276942 182276977 16777216 (@Enclosure.Real.IsNear.of_eq qz206 (@HMul.hMul Real Real Real qz5 qz204 qz3) Bool.false 1980357762637 16777216000 370829 16777216000 (BSN.t_div_two_pi_mk qz204 741658 1000 qz209) (@Enclosure.Real.IsNear.mulLit_ff qz204 qz3 741658 1000 0 1 5340353 33554432 1 33554432 1980357762637 16777216000 370829 16777216000 (Enclosure.Real.IsNear.const Bool.false 741658 1000) RS385to396.d48 rfl)) 

noncomputable abbrev qz756 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 741658 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz677 := qz756

noncomputable abbrev qz515 := qz677

noncomputable abbrev qz215 := qz515

noncomputable def Ns384p1355 := @Enclosure.Real.IsNear.sqrt_image qz215 364553919 33554432 35 33554432 55300087 55300093 16777216 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 364553919 33554432 35 33554432 364553919 33554432 35 33554432 (Ns384p1354 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns384p1356 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz215) 27650045 8388608 3 16777216 5089954 5089956 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz215) Bool.false 110600180 33554432 6 33554432 27650045 8388608 3 16777216 (Ns384p1355 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns384p1357 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 10179910 33554432 2 33554432 5089955 16777216 1 16777216 (Ns384p1356 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz216 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz509))

noncomputable abbrev qz678 := (@HMul.hMul Real Real Real qz707 qz754 qz754)

noncomputable abbrev qz516 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz678 qz671) qz594)

noncomputable abbrev qz217 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz516))

noncomputable def Ns384p1358 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz208) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz216) qz217) Bool.false 91386390200761 

noncomputable def Ns384p1359 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz216) qz217 50901401 33554432 523 

noncomputable def Ns384p1360 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz216) Bool.false 50901401 33554432 523 33554432 50901401 33554432 523 

noncomputable def Ns384p1361 := @Enclosure.Real.IsNear.recentre' qz216 Bool.false 22119232 33554432 1306514432 193273528320000 345613 524288 1275893 188743680000 

noncomputable abbrev qz218 := (@HMul.hMul Real Real Real qz349 qz346 qz509)

noncomputable def Ns384p1362 := @Enclosure.Real.IsNear.cos_image qz218 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 91136343) qz415) Bool.false 91136343 16777216 221 33554432 Bool.false 22119232 33554432 1 

noncomputable def Ns384p1363 := nat_lit 944512639565732148881062453 

noncomputable def Ns384p1364 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz208 884279719003555 140737488355328 1 500000000000000 29009599 33554432 35 33554432 25652600052125810124445 4722366482869645213696 Ns384p1363 

noncomputable def Ns384p1365 := @Enclosure.Real.IsNear.subLit_ff_p qz215 qz1 364553919 33554432 35 33554432 10 1 0 1 29009599 29009599 33554432 35 

noncomputable def Ns384p1366 := @Ns384p1365 33554432 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 364553919 33554432 35 33554432 364553919 33554432 35 33554432 (Ns384p1354 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns384p1367 := @Enclosure.Real.IsNear.recentre' qz218 Bool.false 25652600052125810124445 4722366482869645213696 Ns384p1363 Ns384p295 91136343 16777216 221 33554432 (@Ns384p1364 Ns384p295 RS385to396.d47 (Ns384p1366 rfl rfl) rfl) 

noncomputable def Ns384p1368 := nat_lit 1740273791081695470944256 

noncomputable def Ns384p1369 := nat_lit 403655434283718488213844342053051669479739678515754454046928656903766519057323743535631905 

noncomputable def Ns384p1370 := nat_lit 35821370550394629330841828756123466797547387573300683685861942898613436027026758635041 

noncomputable def Ns384p1371 := nat_lit 1057134807571704925445913818606673029691169795580428702349321753507076461491804142126960161 

noncomputable def Ns384p1372 := BSN.sin_dyadic_bound_f 49461556019 68719476736 3 2 33554432 11531251 Ns384p1369 Ns384p1131 Ns384p1370 Ns384p1371 Ns384p1134 Ns384p1370 22119232 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 49461556019) qz368 0 2 Ns384p1369 Ns384p1131 Ns384p1370 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 49461556019) qz369 0 2 Ns384p1371 Ns384p1134 Ns384p1370 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1373 := @Ns384p1362 5760000 (Ns384p1367 rfl) (Enclosure.sfrac_false_div 91136343 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 91136343) qz415) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns384p1368) qz427) 226375608064910080 72057594037927936 Bool.false 22119232 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 91136343 16777216 226375608064910080 72057594037927936 0 Ns384p1368 Ns384p509 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 22119232 33554432 Ns384p1368 Ns384p509 49461556019 68719476736 11531251 11520000 (Ns384p1372 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p1374 := @Enclosure.Real.IsNear.inv_image qz216 345613 524288 1275893 188743680000 25450439 25450962 16777216 (Ns384p1361 (Ns384p1373 rfl rfl) rfl) rfl 

noncomputable def Ns384p1375 := @Enclosure.Real.IsNear.recentre' qz217 Bool.false 7181444 16777216 

noncomputable abbrev qz219 := (@HMul.hMul Real Real Real qz349 qz346 qz516)

noncomputable def Ns384p1376 := @Enclosure.Real.IsNear.cos_image qz219 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 18932503)) qz415) Bool.true 18932503 16777216 

noncomputable def Ns384p1377 := nat_lit 178812436580760870887279338205 

noncomputable def Ns384p1378 := nat_lit 86492484022775800987342104921787477 

noncomputable def Ns384p1379 := @Enclosure.Real.IsNear.recentre' qz219 Bool.true Ns384p1377 Ns384p307 Ns384p1378 

noncomputable abbrev qz220 := qz516

noncomputable def Ns384p1380 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz220 884279719003555 140737488355328 1 500000000000000 202212527029631 

noncomputable abbrev qz517 := (@HSub.hSub Real Real Real qz583 qz678 qz671)

noncomputable abbrev qz221 := qz517

noncomputable def Ns384p1381 := @Enclosure.Real.IsNear.subLit_tf qz221 qz29 131843782851967 1125899906842624 3205078275 1125899906842624 1 16 

noncomputable abbrev qz518 := qz678

noncomputable abbrev qz222 := qz518

noncomputable def Ns384p1382 := @Enclosure.Real.IsNear.subLit_ff_n qz222 qz208 841556834140801 1125899906842624 2030673155 1125899906842624 29009599 33554432 35 33554432 

noncomputable def Ns384p1383 := @Enclosure.Real.IsNear.mulLit_ff qz208 qz208 29009599 33554432 35 33554432 29009599 33554432 35 33554432 841556834140801 1125899906842624 

noncomputable def Ns384p1384 := nat_lit 17117486996510416703050380782816499467948786646404720080549441 

noncomputable def Ns384p1385 := nat_lit 253092741970790968397859029543733109897246971520789871559966720 

noncomputable def Ns384p1386 := nat_lit 16506852649209385273940917080435019317954865505053418026561 

noncomputable def Ns384p1387 := nat_lit 51319447284232831338603260514288628365210450208204053405595201 

noncomputable def Ns384p1388 := nat_lit 11389173388685593577903656329467989945376113718435544220198502400 

noncomputable def Ns384p1389 := BSN.cos_dyadic_bound_f 18932503 16777216 3 2 16777216 5760000 Ns384p1384 Ns384p1385 Ns384p1386 Ns384p1387 Ns384p1388 Ns384p1386 7181444 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 18932503) (BSN.cosEvenQ 16777216) 0 2 Ns384p1384 Ns384p1385 Ns384p1386 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 18932503) (BSN.cosOddQ 16777216) 0 2 Ns384p1387 Ns384p1388 Ns384p1386 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1390 := @Ns384p1375 3495314432 193273528320000 1795361 4194304 3413393 188743680000 (@Ns384p1376 601 33554432 Bool.false 7181444 16777216 1 5760000 (@Ns384p1379 Ns384p463 18932503 16777216 601 33554432 (@Ns384p1380 1125899906842624 3205078275 1125899906842624 Ns384p1377 Ns384p307 Ns384p1378 Ns384p463 RS385to396.d47 (@Ns384p1381 0 1 3235400432474096 202212527029631 1125899906842624 3205078275 1125899906842624 (@Ns384p1382 4423943246329092767744 131843782851967 1125899906842624 3205078275 1125899906842624 (@Ns384p1383 2030673155 1125899906842624 (Ns384p1366 rfl rfl) (Ns384p1366 rfl rfl) rfl) (Ns384p1366 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 18932503 16777216) (BSN.cos_neg_of_bound 18932503 16777216 Bool.false 7181444 16777216 1 5760000 (Ns384p1389 rfl rfl)) rfl rfl) 

noncomputable def Ns384p1391 := @Ns384p1352 15327132399734988711 Ns384p1275 (Ns384p1353 qz31 (@Enclosure.Real.IsNear.of_eq qz676 (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 5089955 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz206 (BSN.t_div_two_pi_nonneg qz204 741658 1000 qz209)) Ns384p1357) rfl) (@Ns384p1358 140737488355328 18000174350261 527765581332480000 (BSN.correction_mk qz208 (BSN.cos_two_pi_p_ne_zero_mk qz204 741658 1000 10 qz209 rfl rfl (@BSN.floor_sqrt_eq_dec qz204 741658 1000 10 qz209 rfl rfl rfl))) (@Ns384p1359 33554432 1795361 4194304 3413393 188743680000 91386390200761 140737488355328 18000174350261 527765581332480000 (@Ns384p1360 33554432 (Ns384p1374 rfl rfl rfl rfl rfl) rfl) (Ns384p1390 rfl) rfl)) 

noncomputable def Ns384p1392 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz204) (hardyZApproximantRS₀ qz204) Bool.true 1201570739859055489739 2361183241434822606848 1715040167546097868711 Ns384p1275 (@Eq.refl Real (hardyZApproximantRS₀ qz204)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz204) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) (@HMul.hMul Real Real Real qz5 qz672 (Zeta.RiemannSiegel.correction qz208))) Bool.true 1201570739859055489739 2361183241434822606848 1715040167546097868711 Ns384p1275 (BSN.hardyZApproximantRS₀_eq qz204 10 (@BSN.floor_sqrt_eq_dec qz204 741658 1000 10 qz209 rfl rfl rfl)) (@Ns384p1277 1201570739859055489739 2361183241434822606848 1715040167546097868711 Ns384p1275 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 10)) Bool.true 10465131 33554432 38647 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) (Ns384p1351 (Ns384p1350 rfl rfl rfl rfl) rfl rfl)) (Ns384p1391 rfl) rfl rfl)) 

theorem RS385to396.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz204) Bool.true 1201570739859055489739 2361183241434822606848 1715040167546097868711 Ns384p1275 := Ns384p1392 

noncomputable def Ns384p1393 := nat_lit 4177410411335140909882424688640 

noncomputable abbrev qz757 := (Enclosure.sfrac Bool.false 742975 1000)

noncomputable abbrev qz679 := qz757

noncomputable abbrev qz519 := qz679

noncomputable abbrev qz223 := qz519

noncomputable abbrev qz758 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 742975 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz680 := qz758

noncomputable abbrev qz520 := qz680

noncomputable abbrev qz224 := qz520

noncomputable abbrev qz759 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 742975 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz681 := qz759

noncomputable abbrev qz521 := qz681

noncomputable abbrev qz225 := qz521

noncomputable abbrev qz682 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz205 qz224 qz207))

noncomputable def Ns384p1394 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (@HMul.hMul Real Real Real qz5 qz682 (Zeta.RiemannSiegel.correction qz225)) 911679787 134217728 38715 33554432 952747895593914295029 4722366482869645213696 87135926955371214481 Ns384p74 Ns384p1393 

noncomputable def Ns384p1395 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin BSN.quadSignNeg 9 10 742975 1000 197 268435456 134217728 4503599627370496 Bool.false 376118317648 2581 618095470 48 84886744 8 

noncomputable def Ns384p1396 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 742975 1000 91 147 268435456 134217728 4503599627370496 Bool.false 376118317648 2581 

noncomputable def Ns384p1397 := Ns384p1396 558195838 48 94906264 8 589812974 48 89478488 8 Bool.false 815575133 116467 Bool.true 236409117 Bool.true 114334754 14148475504056880 1 Bool.false 207012049 Bool.false Bool.false 110908941 Bool.false Bool.false 925734591 

noncomputable def Ns384p1398 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 742975 1000 44 28 268435456 134217728 4503599627370496 Bool.false 376118317648 2581 

noncomputable def Ns384p1399 := Ns384p1398 480971758 48 109588312 8 522351262 48 101459064 8 Bool.false 657453049 86379 Bool.false 215398904 Bool.true 169203244 14148475504056880 1 Bool.false 186553566 Bool.false Bool.false 216850841 Bool.false Bool.false 815575133 

noncomputable def Ns384p1400 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 742975 1000 236 130 268435456 134217728 4503599627370496 Bool.false 376118317648 2581 

noncomputable def Ns384p1401 := Ns384p1400 372130544 47 134217720 8 432030192 47 120047984 16 Bool.false 583548162 50829 Bool.false 123473648 Bool.false 315220072 14148475504056880 1 Bool.false 240535218 Bool.false Bool.false 103670181 Bool.true Bool.false 657453049 

noncomputable def Ns384p1402 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 742975 1000 564 372 268435456 134217728 4503599627370496 Bool.false 376118317648 2581 

noncomputable def Ns384p1403 := Ns384p1402 186065264 47 189812528 16 294906480 47 154981288 8 Bool.false 268435432 2631 Bool.false 61688585 Bool.false 153612354 14148475504056880 1 Bool.false 261378334 Bool.false Bool.false 225669484 Bool.false Bool.false 583548162 

noncomputable def Ns384p1404 := nat_lit 1252110364436005038608616293618329136163309978389 

noncomputable def Ns384p1405 := nat_lit 893630543551049682420434128907513045176025088 

noncomputable def Ns384p1406 := nat_lit 108670768638116458776807812500000000 

noncomputable def Ns384p1407 := nat_lit 484438088358725124909334838203125000000 

noncomputable abbrev qz760 := (@Eq.refl Real (Enclosure.sfrac Bool.false 742975 1000))

noncomputable abbrev qz683 := qz760

noncomputable abbrev qz522 := qz683

noncomputable abbrev qz226 := qz522

noncomputable def Ns384p1408 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz223 742975 1000 2208048402500 16000000 1485950 4000 2000 Ns384p1406 Ns384p1407 qz226 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns384p1409 := nat_lit 97821122221562893641298147938931963762758592061640625000000 

noncomputable abbrev qz684 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1485950))))

noncomputable abbrev qz523 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 742975 4000) (Real.log (Enclosure.sfrac Bool.false 2208048402500 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz684))

noncomputable abbrev qz685 := (Enclosure.sfrac Bool.false 742975 2000)

noncomputable abbrev qz227 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz523 qz685) (@HMul.hMul Real Real Real qz349 qz685 (Real.log Real.pi)))

noncomputable def Ns384p1410 := @Enclosure.Real.IsNear.addLit_ft_p qz227 (Enclosure.sfrac Bool.true Ns384p1406 Ns384p1407) 201927016544237661261 144115188075855872 4723457264997121 491520000000000000000 Ns384p1406 Ns384p1407 0 1 Ns384p1409 

noncomputable def Ns384p1411 := nat_lit 2710218538238599038648503500800 

noncomputable abbrev qz228 := (@HSub.hSub Real Real Real qz355 qz523 qz685)

noncomputable def Ns384p1412 := @Enclosure.Real.IsNear.subLit_ff_p qz228 (@HMul.hMul Real Real Real qz5 qz685 (Real.log Real.pi)) 1316062049400888679809 720575940379279360 1955665578229 480000000000000000 1141529406159 2684354560 29719 5368709120 Ns384p1411 201927016544237661261 144115188075855872 

noncomputable def Ns384p1413 := nat_lit 2632124098801777359618000 

noncomputable abbrev qz229 := qz523

noncomputable def Ns384p1414 := @Enclosure.Real.IsNear.subLit_ff_p qz229 qz685 1583747004052536221057 720575940379279360 1955665578229 480000000000000000 742975 2000 0 1 Ns384p1413 1316062049400888679809 720575940379279360 1955665578229 480000000000000000 

noncomputable def Ns384p1415 := nat_lit 3566281208650070771784871602747867136 

noncomputable def Ns384p1416 := nat_lit 57230697631782989696335872 

noncomputable def Ns384p1417 := nat_lit 5153054644620501573137682294169815375585937500000000 

noncomputable def Ns384p1418 := nat_lit 1140156652087159899811970831816200312500000000000 

noncomputable def Ns384p1419 := nat_lit 453723303908609075937763371075117187500000000 

noncomputable def Ns384p1420 := BSN.log_dyadic_bound 110896402500 4305200402500 3 2 Ns384p1417 134217728 46080000 Ns384p1418 Ns384p1419 6916080 4416096805000 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 110896402500) (BSN.artanhQ 4305200402500) 0 2 Ns384p1418 Ns384p1417 Ns384p1419 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz524 := (Real.log (Enclosure.sfrac Bool.false 2208048402500 16000000))

noncomputable def Ns384p1421 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 742975 4000) qz524 742975 4000 0 1 53300240665472103 4503599627370496 195312653 9000000000000000 1584029852337165429057 720575940379279360 5804496734507 1440000000000000000 (Enclosure.Real.IsNear.const Bool.false 742975 4000) (BSN.isNear_log_sfrac 2208048402500 16000000 53300240665472103 4503599627370496 195312653 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2208048402500) qz358)) Bool.false Ns384p1416 Ns384p98 1000000783360000 46080000000000000000000 53300240665472103 4503599627370496 195312653 9000000000000000 (BSN.log_rat_reduce_isNear 2208048402500 16000000 17 4416096805000 4194304000000 6916080 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns384p1420 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns384p1422 := BSN.arctan_dyadic_bound_f 1000 1485950 1 0 16777216 5760000 0 1 1 0 1 1 11290 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1485950) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1485950) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns384p1423 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1485950))) 884279719003555 562949953421312 1 2000000000000000 11290 16777216 1 5760000 14829396145167820390400 883900889466275 562949953421312 3125000009 18000000000000000 qz15 (Ns384p1422 rfl) rfl rfl 

noncomputable abbrev qz525 := (@HMul.hMul Real Real Real qz579 qz584 qz684)

noncomputable abbrev qz230 := qz525

noncomputable abbrev qz526 := qz684

noncomputable abbrev qz231 := qz526

noncomputable def Ns384p1424 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 742975 4000) qz524) qz230 1584029852337165429057 720575940379279360 5804496734507 1440000000000000000 883900889466275 2251799813685248 3125000009 72000000000000000 Ns384p1415 1583747004052536221057 720575940379279360 1955665578229 480000000000000000 (Ns384p1421 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz231 1 4 0 1 883900889466275 562949953421312 3125000009 18000000000000000 883900889466275 2251799813685248 3125000009 72000000000000000 qz366 Ns384p1423 rfl) 

noncomputable def Ns384p1425 := @Ns384p1410 Ns384p1404 Ns384p1405 4723457264997121 491520000000000000000 (@Ns384p1412 4723457264997121 491520000000000000000 (Ns384p1414 (Ns384p1424 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 742975 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz685 (Real.log Real.pi) 742975 2000 0 1 38410761 33554432 1 67108864 1141529406159 2684354560 29719 5368709120 (Enclosure.Real.IsNear.const Bool.false 742975 2000) RS385to396.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns384p1406 Ns384p1407) 

noncomputable def Ns384p1426 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns384p1404 Ns384p1405 4723457264997121 491520000000000000000 23507394853 16777216 323 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz367 qz227 (Enclosure.sfrac Bool.true Ns384p1406 Ns384p1407)) Bool.false Ns384p1404 Ns384p1405 4723457264997121 491520000000000000000 Ns384p1408 (Ns384p1425 rfl rfl)) 

noncomputable def Ns384p1427 := nat_lit 3796976403523755453710336 

noncomputable def Ns384p1428 := nat_lit 3507220505010638093507399825222902429912920211693077344717062608170407992464572986940086443076054731850513988915232706314774601410830790625 

noncomputable def Ns384p1429 := nat_lit 2494922846294955101051646175159091972227605206681350894352116740707129287255104012193876468002899611465915760477874720693535400390625 

noncomputable def Ns384p1430 := nat_lit 17514334111233794604909468209326544369199422118504250573007508058810229566369907551474007062436854324350599341403657434433710810448552390625 

noncomputable def Ns384p1431 := BSN.sin_dyadic_bound_f 107916560055 68719476736 4 3 33554432 11531251 Ns384p1428 Ns384p108 Ns384p1429 Ns384p1430 Ns384p111 Ns384p1429 33554429 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107916560055) qz368 0 3 Ns384p1428 Ns384p108 Ns384p1429 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107916560055) qz369 0 3 Ns384p1430 Ns384p111 Ns384p1429 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1432 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz223) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23507394853) qz415) Bool.false 23507394853 16777216 323 33554432 Bool.false 33554429 33554432 1 5760000 (Ns384p1426 rfl) (Enclosure.sfrac_false_div 23507394853 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23507394853) qz415) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns384p1427) qz427) 226375608064910080 72057594037927936 Bool.false 33554429 33554432 222 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 23507394853 16777216 226375608064910080 72057594037927936 222 Ns384p1427 Ns384p509 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554429 33554432 Ns384p1427 Ns384p509 107916560055 68719476736 11531251 11520000 (Ns384p1431 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p1433 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns384p1404 Ns384p1405 4723457264997121 491520000000000000000 376118317648 268435456 2581 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz367 qz227 (Enclosure.sfrac Bool.true Ns384p1406 Ns384p1407)) Bool.false Ns384p1404 Ns384p1405 4723457264997121 491520000000000000000 Ns384p1408 (Ns384p1425 rfl rfl)) 

noncomputable def Ns384p1434 := Ns384p1403 50829 BSN.abs_quadSignPos (BSN.cos_quad_nat0 564 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 261378334 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 372 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 225669484 268435456) qz226 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) Bool.false 33554429 33554432 1849643 188743680000 268435432 268435456 2631 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 33554429 33554432 1849643 188743680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz223) qz223) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 33554429 33554432 1894034432 193273528320000 33554429 33554432 1849643 188743680000 (Ns384p1432 rfl rfl) rfl)) rfl) (Ns384p1433 rfl) RS385to396.d7 

noncomputable def Ns384p1435 := nat_lit 14481689593750770665250889950625 

noncomputable def Ns384p1436 := BSN.cos_dyadic_bound_f 61688585 268435456 2 1 268435456 134217728 Ns384p1435 Ns384p266 Ns384p1435 Ns384p1435 Ns384p267 Ns384p1435 261378334 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 61688585) qz370 0 1 Ns384p1435 Ns384p266 Ns384p1435 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 61688585) qz371 0 1 Ns384p1435 Ns384p267 Ns384p1435 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1437 := nat_lit 4857368977248363102278319640871750816347860027027562826361340637020416 

noncomputable def Ns384p1438 := nat_lit 310033880184010548933284863614026250611868535282600087960702484736 

noncomputable def Ns384p1439 := nat_lit 14571486863984721285737092352888024396542356344012123278908100506091776 

noncomputable def Ns384p1440 := BSN.cos_dyadic_bound_f 153612354 268435456 3 2 268435456 134217728 Ns384p1437 Ns384p117 Ns384p1438 Ns384p1439 Ns384p120 Ns384p1438 225669484 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 153612354) qz370 0 2 Ns384p1437 Ns384p117 Ns384p1438 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 153612354) qz371 0 2 Ns384p1439 Ns384p120 Ns384p1438 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1441 := nat_lit 2027577605906519856637429198693329600395462516899884087522715695579136 

noncomputable def Ns384p1442 := nat_lit 54024932844309056122736084111837344741346406611842683347880902656 

noncomputable def Ns384p1443 := nat_lit 6082624767853870951800042123911765126496904857886428577201451324932096 

noncomputable def Ns384p1444 := BSN.cos_dyadic_bound_f 123473648 268435456 3 2 268435456 134217728 Ns384p1441 Ns384p117 Ns384p1442 Ns384p1443 Ns384p120 Ns384p1442 240535218 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 123473648) qz370 0 2 Ns384p1441 Ns384p117 Ns384p1442 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 123473648) qz371 0 2 Ns384p1443 Ns384p120 Ns384p1442 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1445 := nat_lit 5318529359790789533701187412733764784216808791058757698269698355524646543247615797798526789623271488221085696 

noncomputable def Ns384p1446 := nat_lit 962423827790251017980116301545386803844928487777727328874359020045032713483299162074992851276336726016 

noncomputable def Ns384p1447 := nat_lit 32241420904900479287566442738255606399264932224510107099716455225782048490353473375711708358006790772668497920 

noncomputable def Ns384p1448 := BSN.cos_dyadic_bound_f 315220072 268435456 4 3 268435456 134217728 Ns384p1445 Ns384p149 Ns384p1446 Ns384p1447 Ns384p152 Ns384p1446 103670181 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 315220072) qz370 0 3 Ns384p1445 Ns384p149 Ns384p1446 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 315220072) qz371 0 3 Ns384p1447 Ns384p152 Ns384p1446 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1449 := Ns384p1401 86379 BSN.abs_quadSignPos (BSN.cos_quad_nat0 236 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 240535218 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 130 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 103670181 268435456) qz226 rfl rfl (Ns384p1434 RS385to396.d9 RS385to396.d11 RS385to396.d13 RS385to396.d17 (Ns384p1436 rfl rfl) (Ns384p1440 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns384p1433 rfl) RS385to396.d19 RS385to396.d21 RS385to396.d23 RS385to396.d25 RS385to396.d17 (Ns384p1444 rfl rfl) (Ns384p1448 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns384p1450 := nat_lit 18782349326483744820618683153345406405085000875613082171797582712406016 

noncomputable def Ns384p1451 := nat_lit 4633913401116990851328562658240503263660594957713319910897233166336 

noncomputable def Ns384p1452 := nat_lit 56337780152649000480153392334719738208727681436923819875570953670885376 

noncomputable def Ns384p1453 := BSN.cos_dyadic_bound_f 215398904 268435456 3 2 268435456 134217728 Ns384p1450 Ns384p117 Ns384p1451 Ns384p1452 Ns384p120 Ns384p1451 186553566 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 215398904) qz370 0 2 Ns384p1450 Ns384p117 Ns384p1451 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 215398904) qz371 0 2 Ns384p1452 Ns384p120 Ns384p1451 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1454 := nat_lit 7150630604052360875866766454535375171038814108166493949139845078122496 

noncomputable def Ns384p1455 := nat_lit 671845606309668720134385419274567018025022689218290626315765743616 

noncomputable def Ns384p1456 := nat_lit 21450548120944463290160030592767576379080392279121045266166903702880256 

noncomputable def Ns384p1457 := BSN.cos_dyadic_bound_f 169203244 268435456 3 2 268435456 134217728 Ns384p1454 Ns384p117 Ns384p1455 Ns384p1456 Ns384p120 Ns384p1455 216850841 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 169203244) qz370 0 2 Ns384p1454 Ns384p117 Ns384p1455 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 169203244) qz371 0 2 Ns384p1456 Ns384p120 Ns384p1455 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1458 := Ns384p1399 116467 BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 186553566 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 216850841 268435456) qz226 rfl rfl (Ns384p1449 rfl rfl) (Ns384p1433 rfl) RS385to396.d27 RS385to396.d29 RS385to396.d31 RS385to396.d33 RS385to396.d17 (Ns384p1453 rfl rfl) (Ns384p1457 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p1459 := nat_lit 49055146086072144901705293611076286533937761340268858594179572787685025 

noncomputable def Ns384p1460 := nat_lit 9756942982273441651549153462892993176431393092054250428342289671841 

noncomputable def Ns384p1461 := nat_lit 128461966603455746313220879875783685599932295540459875150729184070182561 

noncomputable def Ns384p1462 := BSN.sin_dyadic_bound_f 236409117 268435456 3 2 268435456 134217728 Ns384p1459 Ns384p131 Ns384p1460 Ns384p1461 Ns384p134 Ns384p1460 207012049 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 236409117) qz372 0 2 Ns384p1459 Ns384p131 Ns384p1460 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 236409117) qz373 0 2 Ns384p1461 Ns384p134 Ns384p1460 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1463 := nat_lit 170888582248327844804540951946256 

noncomputable def Ns384p1464 := BSN.sin_dyadic_bound_f 114334754 268435456 2 1 268435456 134217728 Ns384p1463 Ns384p127 Ns384p1463 Ns384p1463 Ns384p128 Ns384p1463 110908941 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 114334754) qz372 0 1 Ns384p1463 Ns384p127 Ns384p1463 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 114334754) qz373 0 1 Ns384p1463 Ns384p128 Ns384p1463 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1465 := Ns384p1397 142756 BSN.abs_quadSignPos (BSN.cos_quad_nat3 91 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 207012049 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 147 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 110908941 268435456) qz226 rfl rfl (Ns384p1458 rfl) (Ns384p1433 rfl) RS385to396.d35 RS385to396.d37 RS385to396.d39 RS385to396.d41 RS385to396.d17 (Ns384p1462 rfl rfl) (Ns384p1464 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p1466 := nat_lit 3974817665425788195023644532496 

noncomputable def Ns384p1467 := BSN.sin_dyadic_bound_f 44650806 268435456 2 1 268435456 134217728 Ns384p1466 Ns384p127 Ns384p1466 Ns384p1466 Ns384p128 Ns384p1466 44445190 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 44650806) qz372 0 1 Ns384p1466 Ns384p127 Ns384p1466 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 44650806) qz373 0 1 Ns384p1466 Ns384p128 Ns384p1466 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1468 := Ns384p1395 Bool.false 925734591 142756 Bool.true 44650806 14148475504056880 1 Bool.false 44445190 Bool.true Bool.false 911679787 154860 BSN.abs_quadSignNeg qz374 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 44445190 268435456) qz226 rfl (Ns384p1465 rfl) (Ns384p1433 rfl) RS385to396.d43 RS385to396.d45 RS385to396.d17 (Ns384p1467 rfl rfl) rfl 

noncomputable def Ns384p1469 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) 911679787 268435456 154860 268435456 911679787 268435456 154860 268435456 489454358698655744 911679787 134217728 38715 33554432 (Ns384p1468 rfl rfl rfl rfl) 

noncomputable def Ns384p1470 := @Enclosure.Real.IsNear.mulLit_ff qz682 (Zeta.RiemannSiegel.correction qz225) 2543849 8388608 1 16777216 374530050955821 562949953421312 34115542225513 1055531162664960000 952747895593914295029 4722366482869645213696 

noncomputable abbrev qz686 := (@HPow.hPow Real Real Real qz205 qz224 qz207)

noncomputable def Ns384p1471 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz686 1 1 0 1 2543849 8388608 1 16777216 2543849 8388608 1 16777216 

noncomputable def Ns384p1472 := @Enclosure.Real.IsNear.sqrt_image qz224 158709950807 1342177280 29719 1342177280 182438709 182438744 16777216 (@Enclosure.Real.IsNear.of_eq qz224 (@HMul.hMul Real Real Real qz5 qz223 qz3) Bool.false 158709950807 1342177280 29719 1342177280 (BSN.t_div_two_pi_mk qz223 742975 1000 qz226) (@Enclosure.Real.IsNear.mulLit_ff qz223 qz3 742975 1000 0 1 5340353 33554432 1 33554432 158709950807 1342177280 29719 1342177280 (Enclosure.Real.IsNear.const Bool.false 742975 1000) RS385to396.d48 rfl)) 

noncomputable abbrev qz761 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 742975 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz687 := qz761

noncomputable abbrev qz527 := qz687

noncomputable abbrev qz232 := qz527

noncomputable def Ns384p1473 := @Enclosure.Real.IsNear.sqrt_image qz232 364877453 33554432 35 33554432 55324620 55324626 16777216 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 364877453 33554432 35 33554432 364877453 33554432 35 33554432 (Ns384p1472 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns384p1474 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz232) 55324623 16777216 3 16777216 5087697 5087699 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz232) Bool.false 110649246 33554432 6 33554432 55324623 16777216 3 16777216 (Ns384p1473 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns384p1475 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 10175396 33554432 2 33554432 2543849 8388608 1 16777216 (Ns384p1474 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz233 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz521))

noncomputable abbrev qz688 := (@HMul.hMul Real Real Real qz707 qz759 qz759)

noncomputable abbrev qz528 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz688 qz681) qz594)

noncomputable abbrev qz234 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz528))

noncomputable def Ns384p1476 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz225) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz233) qz234) Bool.false 374530050955821 

noncomputable def Ns384p1477 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz233) qz234 47694837 33554432 459 

noncomputable def Ns384p1478 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz233) Bool.false 47694837 33554432 459 33554432 47694837 33554432 459 

noncomputable def Ns384p1479 := @Enclosure.Real.IsNear.recentre' qz233 Bool.false 23606327 33554432 1306514432 193273528320000 23606327 33554432 1275893 188743680000 

noncomputable abbrev qz235 := (@HMul.hMul Real Real Real qz349 qz346 qz521)

noncomputable def Ns384p1480 := @Enclosure.Real.IsNear.cos_image qz235 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 92152755) qz415) Bool.false 92152755 16777216 221 33554432 Bool.false 23606327 33554432 1 

noncomputable def Ns384p1481 := nat_lit 944512639568511284779350581 

noncomputable def Ns384p1482 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz225 884279719003555 140737488355328 1 500000000000000 29333133 33554432 35 33554432 25938694606733906287815 4722366482869645213696 Ns384p1481 

noncomputable def Ns384p1483 := @Enclosure.Real.IsNear.subLit_ff_p qz232 qz1 364877453 33554432 35 33554432 10 1 0 1 29333133 29333133 33554432 35 

noncomputable def Ns384p1484 := @Ns384p1483 33554432 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 364877453 33554432 35 33554432 364877453 33554432 35 33554432 (Ns384p1472 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns384p1485 := @Enclosure.Real.IsNear.recentre' qz235 Bool.false 25938694606733906287815 4722366482869645213696 Ns384p1481 Ns384p295 92152755 16777216 221 33554432 (@Ns384p1482 Ns384p295 RS385to396.d47 (Ns384p1484 rfl rfl) rfl) 

noncomputable def Ns384p1486 := nat_lit 1886754197624252289515520 

noncomputable def Ns384p1487 := nat_lit 557720351353893839122208526119521688034771244753359350695103337503584769350674536201784865 

noncomputable def Ns384p1488 := nat_lit 68379222747101184100430461929005519716055451249128363804906981115175048764791136521761 

noncomputable def Ns384p1489 := nat_lit 1460585449090036176736288300041338412106765360766299710660062701206630779172814123450306081 

noncomputable def Ns384p1490 := BSN.sin_dyadic_bound_f 53624779571 68719476736 3 2 33554432 11531251 Ns384p1487 Ns384p1131 Ns384p1488 Ns384p1489 Ns384p1134 Ns384p1488 23606327 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 53624779571) qz368 0 2 Ns384p1487 Ns384p1131 Ns384p1488 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 53624779571) qz369 0 2 Ns384p1489 Ns384p1134 Ns384p1488 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1491 := @Ns384p1480 5760000 (Ns384p1485 rfl) (Enclosure.sfrac_false_div 92152755 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 92152755) qz415) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns384p1486) qz427) 226375608064910080 72057594037927936 Bool.false 23606327 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 92152755 16777216 226375608064910080 72057594037927936 0 Ns384p1486 Ns384p509 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 23606327 33554432 Ns384p1486 Ns384p509 53624779571 68719476736 11531251 11520000 (Ns384p1490 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p1492 := @Enclosure.Real.IsNear.inv_image qz233 23606327 33554432 1275893 188743680000 23847189 23847648 16777216 (Ns384p1479 (Ns384p1491 rfl rfl) rfl) rfl 

noncomputable def Ns384p1493 := @Enclosure.Real.IsNear.recentre' qz234 Bool.false 7852633 16777216 

noncomputable abbrev qz236 := (@HMul.hMul Real Real Real qz349 qz346 qz528)

noncomputable def Ns384p1494 := @Enclosure.Real.IsNear.cos_image qz236 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 36363259)) qz378) Bool.true 36363259 33554432 

noncomputable def Ns384p1495 := nat_lit 171720638932769000760814767205 

noncomputable def Ns384p1496 := nat_lit 87103647927204186867115053878341537 

noncomputable def Ns384p1497 := @Enclosure.Real.IsNear.recentre' qz236 Bool.true Ns384p1495 Ns384p307 Ns384p1496 

noncomputable abbrev qz237 := qz528

noncomputable def Ns384p1498 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz237 884279719003555 140737488355328 1 500000000000000 194192669177431 

noncomputable abbrev qz529 := (@HSub.hSub Real Real Real qz583 qz688 qz681)

noncomputable abbrev qz238 := qz529

noncomputable def Ns384p1499 := @Enclosure.Real.IsNear.subLit_tf qz238 qz29 123823924999767 1125899906842624 3227725655 1125899906842624 1 16 

noncomputable abbrev qz530 := qz688

noncomputable abbrev qz239 := qz530

noncomputable def Ns384p1500 := @Enclosure.Real.IsNear.subLit_ff_n qz239 qz225 860432691595689 1125899906842624 2053320535 1125899906842624 29333133 33554432 35 33554432 

noncomputable def Ns384p1501 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz225 29333133 33554432 35 33554432 29333133 33554432 35 33554432 860432691595689 1125899906842624 

noncomputable def Ns384p1502 := nat_lit 3726631528932655922867317418693930278080237345539680482552223201 

noncomputable def Ns384p1503 := nat_lit 3057048958885566725329799529498260083624939243563762531210721 

noncomputable def Ns384p1504 := nat_lit 11173780488880196635151292657022794314073462158131913922594248161 

noncomputable def Ns384p1505 := BSN.cos_dyadic_bound_f 36363259 33554432 3 2 16777216 5760000 Ns384p1502 Ns384p1029 Ns384p1503 Ns384p1504 Ns384p1032 Ns384p1503 7852633 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 36363259) (BSN.cosEvenQ 33554432) 0 2 Ns384p1502 Ns384p1029 Ns384p1503 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 36363259) (BSN.cosOddQ 33554432) 0 2 Ns384p1504 Ns384p1032 Ns384p1503 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1506 := @Ns384p1493 1762057216 96636764160000 7852633 16777216 1720759 94371840000 (@Ns384p1494 303 16777216 Bool.false 7852633 16777216 1 5760000 (@Ns384p1497 Ns384p463 36363259 33554432 303 16777216 (@Ns384p1498 1125899906842624 3227725655 1125899906842624 Ns384p1495 Ns384p307 Ns384p1496 Ns384p463 RS385to396.d47 (@Ns384p1499 0 1 3107082706838896 194192669177431 1125899906842624 3227725655 1125899906842624 (@Ns384p1500 4154841471377781817344 123823924999767 1125899906842624 3227725655 1125899906842624 (@Ns384p1501 2053320535 1125899906842624 (Ns384p1484 rfl rfl) (Ns384p1484 rfl rfl) rfl) (Ns384p1484 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 36363259 33554432) (BSN.cos_neg_of_bound 36363259 33554432 Bool.false 7852633 16777216 1 5760000 (Ns384p1505 rfl rfl)) rfl rfl) 

noncomputable def Ns384p1507 := @Ns384p1470 87135926955371214481 Ns384p74 (Ns384p1471 qz31 (@Enclosure.Real.IsNear.of_eq qz686 (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 2543849 8388608 1 16777216 (BSN.rpow_neg_quarter_mk qz224 (BSN.t_div_two_pi_nonneg qz223 742975 1000 qz226)) Ns384p1475) rfl) (@Ns384p1476 562949953421312 34115542225513 1055531162664960000 (BSN.correction_mk qz225 (BSN.cos_two_pi_p_ne_zero_mk qz223 742975 1000 10 qz226 rfl rfl (@BSN.floor_sqrt_eq_dec qz223 742975 1000 10 qz226 rfl rfl rfl))) (@Ns384p1477 33554432 7852633 16777216 1720759 94371840000 374530050955821 562949953421312 34115542225513 1055531162664960000 (@Ns384p1478 33554432 (Ns384p1492 rfl rfl rfl rfl rfl) rfl) (Ns384p1506 rfl) rfl)) 

noncomputable def Ns384p1508 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (hardyZApproximantRS₀ qz223) Bool.false 31124132956081188543755 4722366482869645213696 10303358167598852814481 Ns384p74 (@Eq.refl Real (hardyZApproximantRS₀ qz223)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (@HMul.hMul Real Real Real qz5 qz682 (Zeta.RiemannSiegel.correction qz225))) Bool.false 31124132956081188543755 4722366482869645213696 10303358167598852814481 Ns384p74 (BSN.hardyZApproximantRS₀_eq qz223 10 (@BSN.floor_sqrt_eq_dec qz223 742975 1000 10 qz226 rfl rfl rfl)) (@Ns384p1394 31124132956081188543755 4722366482869645213696 10303358167598852814481 Ns384p74 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10)) Bool.false 911679787 134217728 38715 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (Ns384p1469 (Ns384p1468 rfl rfl rfl rfl) rfl rfl)) (Ns384p1507 rfl) rfl rfl)) 

theorem RS385to396.d62 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz223) Bool.false 31124132956081188543755 4722366482869645213696 10303358167598852814481 Ns384p74 := Ns384p1508 

noncomputable def Ns384p1509 := nat_lit 53126622932283508654080000 

noncomputable def Ns384p1510 := nat_lit 1632575776067577594505303425024 

noncomputable abbrev qz762 := (Enclosure.sfrac Bool.false 744291 1000)

noncomputable abbrev qz689 := qz762

noncomputable abbrev qz531 := qz689

noncomputable abbrev qz240 := qz531

noncomputable abbrev qz763 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 744291 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz690 := qz763

noncomputable abbrev qz532 := qz690

noncomputable abbrev qz241 := qz532

noncomputable abbrev qz764 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 744291 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz691 := qz764

noncomputable abbrev qz533 := qz691

noncomputable abbrev qz242 := qz533

noncomputable abbrev qz692 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz205 qz241 qz207))

noncomputable def Ns384p1511 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (@HMul.hMul Real Real Real qz5 qz692 (Zeta.RiemannSiegel.correction qz242)) 158986947 67108864 155133 134217728 1951851198292258553325 9444732965739290427392 496772146707607687483 Ns384p1509 Ns384p1510 

noncomputable def Ns384p1512 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin BSN.quadSignNeg 9 10 744291 1000 197 268435456 134217728 4503599627370496 Bool.false 376961493763 2585 618095470 48 84886744 8 

noncomputable def Ns384p1513 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 744291 1000 91 147 268435456 134217728 4503599627370496 Bool.false 376961493763 2585 

noncomputable def Ns384p1514 := Ns384p1513 558195838 48 94906264 8 589812974 48 89478488 8 Bool.true 372472955 116673 Bool.true 127818725 Bool.true 47352513 14148475504056880 1 Bool.false 123043127 Bool.false Bool.false 47107311 Bool.false Bool.true 313268204 

noncomputable def Ns384p1515 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 744291 1000 45 28 268435456 134217728 4503599627370496 Bool.false 376961493763 2585 

noncomputable def Ns384p1516 := Ns384p1515 480971758 48 109588312 8 522351262 48 101459064 8 Bool.true 472188753 86533 Bool.false 3958757 Bool.true 13441390 14148475504056880 1 Bool.false 3958613 Bool.true Bool.false 268099000 Bool.false Bool.true 372472955 

noncomputable def Ns384p1517 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 744291 1000 237 131 268435456 134217728 4503599627370496 Bool.false 376961493763 2585 

noncomputable def Ns384p1518 := Ns384p1517 372130544 47 134217720 8 432030192 47 120047984 16 Bool.true 515139438 50921 Bool.false 55268539 Bool.false 168187026 14148475504056880 1 Bool.false 54878882 Bool.true Bool.false 157397106 Bool.false Bool.true 472188753 

noncomputable def Ns384p1519 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 744291 1000 565 373 268435456 134217728 4503599627370496 Bool.false 376961493763 2585 

noncomputable def Ns384p1520 := Ns384p1519 186065264 47 189812528 16 294906480 47 154981288 8 Bool.true 268435336 2639 Bool.false 238345384 Bool.false 187034113 14148475504056880 1 Bool.false 208239313 Bool.true Bool.false 172264007 Bool.true Bool.true 515139438 

noncomputable def Ns384p1521 := nat_lit 4300649705652712946796773560143242830972890704000615460861 

noncomputable def Ns384p1522 := nat_lit 3062506075376711644454692222989812001968133341446144000 

noncomputable def Ns384p1523 := nat_lit 109636603163366836124180593176480000 

noncomputable def Ns384p1524 := nat_lit 489609325143021663963555845223188854080 

noncomputable abbrev qz765 := (@Eq.refl Real (Enclosure.sfrac Bool.false 744291 1000))

noncomputable abbrev qz693 := qz765

noncomputable abbrev qz534 := qz693

noncomputable abbrev qz243 := qz534

noncomputable def Ns384p1525 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz240 744291 1000 2215877370724 16000000 1488582 4000 2000 Ns384p1523 Ns384p1524 qz243 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns384p1526 := nat_lit 12385871152279813286774707853212539353201925227521772527279680 

noncomputable abbrev qz694 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1488582))))

noncomputable abbrev qz535 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 744291 4000) (Real.log (Enclosure.sfrac Bool.false 2215877370724 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz694))

noncomputable abbrev qz695 := (Enclosure.sfrac Bool.false 744291 2000)

noncomputable abbrev qz244 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz535 qz695) (@HMul.hMul Real Real Real qz349 qz695 (Real.log Real.pi)))

noncomputable def Ns384p1527 := @Enclosure.Real.IsNear.addLit_ft_p qz244 (Enclosure.sfrac Bool.true Ns384p1523 Ns384p1524) 25297461652102293676821 18014398509481984000 354883945276276927 36864000000000000000000 Ns384p1523 Ns384p1524 0 1 Ns384p1526 

noncomputable def Ns384p1528 := nat_lit 1697683913556148140445840441344000 

noncomputable abbrev qz245 := (@HSub.hSub Real Real Real qz355 qz535 qz695)

noncomputable def Ns384p1529 := @Enclosure.Real.IsNear.subLit_ff_p qz245 (@HMul.hMul Real Real Real qz5 qz695 (Real.log Real.pi)) 32971704845244757107477 18014398509481984000 146931949818523 36000000000000000000 28588783715451 67108864000 744291 134217728000 Ns384p1528 25297461652102293676821 18014398509481984000 

noncomputable def Ns384p1530 := nat_lit 65943409690489514214954000 

noncomputable abbrev qz246 := qz535

noncomputable def Ns384p1531 := @Enclosure.Real.IsNear.subLit_ff_p qz246 qz695 39675682185755184784149 18014398509481984000 146931949818523 36000000000000000000 744291 2000 0 1 Ns384p1530 32971704845244757107477 18014398509481984000 146931949818523 36000000000000000000 

noncomputable def Ns384p1532 := nat_lit 89341693753718638227151532427105533952 

noncomputable def Ns384p1533 := nat_lit 57247813039749254491406336 

noncomputable def Ns384p1534 := nat_lit 5190640146904922498612884211406562467286671179984640 

noncomputable def Ns384p1535 := nat_lit 1311654065448919463459719652573662052679583991808 

noncomputable def Ns384p1536 := nat_lit 596067430208732226129243370652544491483996928 

noncomputable def Ns384p1537 := BSN.log_dyadic_bound 118725370724 4313029370724 3 2 Ns384p1534 134217728 46080000 Ns384p1535 Ns384p1536 7391128 4431754741448 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 118725370724) (BSN.artanhQ 4313029370724) 0 2 Ns384p1535 Ns384p1534 Ns384p1536 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz536 := (Real.log (Enclosure.sfrac Bool.false 2215877370724 16000000))

noncomputable def Ns384p1538 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 744291 4000) qz536 744291 4000 0 1 53316180631284839 4503599627370496 195312653 9000000000000000 39682753398239624104149 18014398509481984000 16152161090447 4000000000000000000 (Enclosure.Real.IsNear.const Bool.false 744291 4000) (BSN.isNear_log_sfrac 2215877370724 16000000 53316180631284839 4503599627370496 195312653 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2215877370724) qz358)) Bool.false Ns384p1533 Ns384p98 1000000783360000 46080000000000000000000 53316180631284839 4503599627370496 195312653 9000000000000000 (BSN.log_rat_reduce_isNear 2215877370724 16000000 17 4431754741448 4194304000000 7391128 134217728 24973259072661432 36028797018963968 46080000 1000000000000000 rfl rfl rfl rfl (Ns384p1537 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns384p1539 := BSN.arctan_dyadic_bound_f 1000 1488582 1 0 16777216 5760000 0 1 1 0 1 1 11270 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1488582) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1488582) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns384p1540 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1488582))) 884279719003555 562949953421312 1 2000000000000000 11270 16777216 1 5760000 14829407404166888816640 883901560554915 562949953421312 3125000009 18000000000000000 qz15 (Ns384p1539 rfl) rfl rfl 

noncomputable abbrev qz537 := (@HMul.hMul Real Real Real qz579 qz584 qz694)

noncomputable abbrev qz247 := qz537

noncomputable abbrev qz538 := qz694

noncomputable abbrev qz248 := qz538

noncomputable def Ns384p1541 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 744291 4000) qz536) qz247 39682753398239624104149 18014398509481984000 16152161090447 4000000000000000000 883901560554915 2251799813685248 3125000009 72000000000000000 Ns384p1532 39675682185755184784149 18014398509481984000 146931949818523 36000000000000000000 (Ns384p1538 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz248 1 4 0 1 883901560554915 562949953421312 3125000009 18000000000000000 883901560554915 2251799813685248 3125000009 72000000000000000 qz366 Ns384p1540 rfl) 

noncomputable def Ns384p1542 := @Ns384p1527 Ns384p1521 Ns384p1522 354883945276276927 36864000000000000000000 (@Ns384p1529 354883945276276927 36864000000000000000000 (Ns384p1531 (Ns384p1541 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 744291 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz695 (Real.log Real.pi) 744291 2000 0 1 38410761 33554432 1 67108864 28588783715451 67108864000 744291 134217728000 (Enclosure.Real.IsNear.const Bool.false 744291 2000) RS385to396.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns384p1523 Ns384p1524) 

noncomputable def Ns384p1543 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns384p1521 Ns384p1522 354883945276276927 36864000000000000000000 1472505835 1048576 81 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz367 qz244 (Enclosure.sfrac Bool.true Ns384p1523 Ns384p1524)) Bool.false Ns384p1521 Ns384p1522 354883945276276927 36864000000000000000000 Ns384p1525 (Ns384p1542 rfl rfl)) 

noncomputable def Ns384p1544 := nat_lit 3502596197628825488867409526441760231706891777294476631946201894494645895379258365430115582760616415495940542581058177620807242697124745216 

noncomputable def Ns384p1545 := nat_lit 2485086810324903552692943795209640929735035923571506680799441125029774764932674859795628499877807969345528853229520872187853096226816 

noncomputable def Ns384p1546 := nat_lit 17491269838581202980649012410600558663136661187909478592153325596604636163983677222048926320428327277739089324282968016481884917584666955776 

noncomputable def Ns384p1547 := BSN.sin_dyadic_bound_f 107881041454 68719476736 4 3 33554432 11531251 Ns384p1544 Ns384p108 Ns384p1545 Ns384p1546 Ns384p111 Ns384p1545 33554417 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107881041454) qz368 0 3 Ns384p1544 Ns384p108 Ns384p1545 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107881041454) qz369 0 3 Ns384p1546 Ns384p111 Ns384p1545 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1548 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz240) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1472505835) (@Nat.cast Real Real.instNatCast 1048576)) Bool.false 1472505835 1048576 81 8388608 Bool.true 33554417 33554432 1 5760000 (Ns384p1543 rfl) (Enclosure.sfrac_false_div 1472505835 1048576) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1472505835) (@Nat.cast Real Real.instNatCast 1048576)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 237232918992055361863680) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false 33554417 33554432 223 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q1 1472505835 1048576 226375608064910080 72057594037927936 223 237232918992055361863680 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554417 33554432 237232918992055361863680 151115727451828646838272 107881041454 68719476736 11531251 11520000 (Ns384p1547 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p1549 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns384p1521 Ns384p1522 354883945276276927 36864000000000000000000 376961493763 268435456 2585 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz367 qz244 (Enclosure.sfrac Bool.true Ns384p1523 Ns384p1524)) Bool.false Ns384p1521 Ns384p1522 354883945276276927 36864000000000000000000 Ns384p1525 (Ns384p1542 rfl rfl)) 

noncomputable def Ns384p1550 := Ns384p1520 50921 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 565 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 208239313 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 373 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 172264007 268435456) qz243 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) Bool.true 33554417 33554432 463817 47185920000 268435336 268435456 2639 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 33554417 33554432 463817 47185920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz240) qz240) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 33554417 33554432 474948608 48318382080000 33554417 33554432 463817 47185920000 (Ns384p1548 rfl rfl) rfl)) rfl) (Ns384p1549 rfl) RS385to396.d7 

noncomputable def Ns384p1551 := nat_lit 50682442510507504462212378104531129282425467166320527739053364886896640 

noncomputable def Ns384p1552 := nat_lit 10414872638636075465698077603272172588467276015813482733166810628096 

noncomputable def Ns384p1553 := nat_lit 132722868209914243755040336243366707460256800322051969868333685581807616 

noncomputable def Ns384p1554 := BSN.sin_dyadic_bound_f 238345384 268435456 3 2 268435456 134217728 Ns384p1551 Ns384p131 Ns384p1552 Ns384p1553 Ns384p134 Ns384p1552 208239313 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 238345384) qz372 0 2 Ns384p1551 Ns384p131 Ns384p1552 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 238345384) qz373 0 2 Ns384p1553 Ns384p134 Ns384p1552 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1555 := nat_lit 19215798892426968849536027337027812274426049481479141420079667080024065 

noncomputable def Ns384p1556 := nat_lit 1497499186138798943068040476912018590672563010232618058268463288321 

noncomputable def Ns384p1557 := nat_lit 50324667814816884169543675721919746021969040682809755670971455316643841 

noncomputable def Ns384p1558 := BSN.sin_dyadic_bound_f 187034113 268435456 3 2 268435456 134217728 Ns384p1555 Ns384p131 Ns384p1556 Ns384p1557 Ns384p134 Ns384p1556 172264007 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 187034113) qz372 0 2 Ns384p1555 Ns384p131 Ns384p1556 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 187034113) qz373 0 2 Ns384p1557 Ns384p134 Ns384p1556 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1559 := nat_lit 9330650824526000538483764419441 

noncomputable def Ns384p1560 := BSN.sin_dyadic_bound_f 55268539 268435456 2 1 268435456 134217728 Ns384p1559 Ns384p127 Ns384p1559 Ns384p1559 Ns384p128 Ns384p1559 54878882 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 55268539) qz372 0 1 Ns384p1559 Ns384p127 Ns384p1559 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 55268539) qz373 0 1 Ns384p1559 Ns384p128 Ns384p1559 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1561 := nat_lit 12564158219670296199097644779842482368145606888295006867755518123393280 

noncomputable def Ns384p1562 := nat_lit 640235762028846963488738640791520942485037974907421458323826360576 

noncomputable def Ns384p1563 := nat_lit 32905092098378919531124373608454743739807804169765644066522404128112896 

noncomputable def Ns384p1564 := BSN.sin_dyadic_bound_f 168187026 268435456 3 2 268435456 134217728 Ns384p1561 Ns384p131 Ns384p1562 Ns384p1563 Ns384p134 Ns384p1562 157397106 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 168187026) qz372 0 2 Ns384p1561 Ns384p131 Ns384p1562 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 168187026) qz373 0 2 Ns384p1563 Ns384p134 Ns384p1562 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1565 := Ns384p1518 86533 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 237 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 54878882 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 131 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 157397106 268435456) qz243 rfl rfl (Ns384p1550 RS385to396.d9 RS385to396.d11 RS385to396.d13 RS385to396.d17 (Ns384p1554 rfl rfl) (Ns384p1558 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns384p1549 rfl) RS385to396.d19 RS385to396.d21 RS385to396.d23 RS385to396.d25 RS385to396.d17 (Ns384p1560 rfl rfl) (Ns384p1564 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns384p1566 := BSN.sin_dyadic_bound_f 3958757 268435456 1 0 268435456 134217728 0 1 1 0 1 1 3958613 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 3958757) qz372 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 3958757) qz373 0 0 rfl) rfl rfl 

noncomputable def Ns384p1567 := nat_lit 32641997641764493970450410000 

noncomputable def Ns384p1568 := BSN.cos_dyadic_bound_f 13441390 268435456 2 1 268435456 134217728 Ns384p1567 Ns384p266 Ns384p1567 Ns384p1567 Ns384p267 Ns384p1567 268099000 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 13441390) qz370 0 1 Ns384p1567 Ns384p266 Ns384p1567 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 13441390) qz371 0 1 Ns384p1567 Ns384p267 Ns384p1567 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1569 := Ns384p1516 116673 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 45 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 3958613 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268099000 268435456) qz243 rfl rfl (Ns384p1565 rfl rfl) (Ns384p1549 rfl) RS385to396.d27 RS385to396.d29 RS385to396.d31 RS385to396.d33 RS385to396.d17 (Ns384p1566 rfl rfl) (Ns384p1568 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p1570 := nat_lit 4191086346146318706884259560881124924991490830172961626191936300390625 

noncomputable def Ns384p1571 := nat_lit 71245239205652364051770453421764643920595419650779419097900390625 

noncomputable def Ns384p1572 := nat_lit 10976539366662596985631262650145025279839937876916417282871769900390625 

noncomputable def Ns384p1573 := BSN.sin_dyadic_bound_f 127818725 268435456 3 2 268435456 134217728 Ns384p1570 Ns384p131 Ns384p1571 Ns384p1572 Ns384p134 Ns384p1571 123043127 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 127818725) qz372 0 2 Ns384p1570 Ns384p131 Ns384p1571 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 127818725) qz373 0 2 Ns384p1572 Ns384p134 Ns384p1571 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1574 := nat_lit 5027732093423311257426971298561 

noncomputable def Ns384p1575 := BSN.sin_dyadic_bound_f 47352513 268435456 2 1 268435456 134217728 Ns384p1574 Ns384p127 Ns384p1574 Ns384p1574 Ns384p128 Ns384p1574 47107311 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 47352513) qz372 0 1 Ns384p1574 Ns384p127 Ns384p1574 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 47352513) qz373 0 1 Ns384p1574 Ns384p128 Ns384p1574 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1576 := Ns384p1514 143008 BSN.abs_quadSignPos (BSN.cos_quad_nat3 91 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 123043127 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 147 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 47107311 268435456) qz243 rfl rfl (Ns384p1569 rfl) (Ns384p1549 rfl) RS385to396.d35 RS385to396.d37 RS385to396.d39 RS385to396.d41 RS385to396.d17 (Ns384p1573 rfl rfl) (Ns384p1575 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns384p1577 := nat_lit 49134206357760943421683210000 

noncomputable def Ns384p1578 := BSN.sin_dyadic_bound_f 14888330 268435456 2 1 268435456 134217728 Ns384p1577 Ns384p127 Ns384p1577 Ns384p1577 Ns384p128 Ns384p1577 14880697 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 14888330) qz372 0 1 Ns384p1577 Ns384p127 Ns384p1577 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 14888330) qz373 0 1 Ns384p1577 Ns384p128 Ns384p1577 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1579 := Ns384p1512 Bool.true 313268204 143008 Bool.true 14888330 14148475504056880 1 Bool.false 14880697 Bool.true Bool.true 317973894 155133 BSN.abs_quadSignNeg qz374 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 14880697 268435456) qz243 rfl (Ns384p1576 rfl) (Ns384p1549 rfl) RS385to396.d43 RS385to396.d45 RS385to396.d17 (Ns384p1578 rfl rfl) rfl 

noncomputable def Ns384p1580 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) 317973894 268435456 155133 268435456 317973894 268435456 155133 268435456 170710934463971328 158986947 67108864 155133 134217728 (Ns384p1579 rfl rfl rfl rfl) 

noncomputable def Ns384p1581 := @Enclosure.Real.IsNear.mulLit_ff qz692 (Zeta.RiemannSiegel.correction qz242) 10170895 33554432 1 33554432 191905549933635 281474976710656 48736382516273 1583296743997440000 1951851198292258553325 9444732965739290427392 

noncomputable abbrev qz696 := (@HPow.hPow Real Real Real qz205 qz241 qz207)

noncomputable def Ns384p1582 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz696 1 1 0 1 10170895 33554432 1 33554432 10170895 33554432 1 33554432 

noncomputable def Ns384p1583 := @Enclosure.Real.IsNear.sqrt_image qz241 3974776674723 33554432000 744291 33554432000 182600211 182600246 16777216 (@Enclosure.Real.IsNear.of_eq qz241 (@HMul.hMul Real Real Real qz5 qz240 qz3) Bool.false 3974776674723 33554432000 744291 33554432000 (BSN.t_div_two_pi_mk qz240 744291 1000 qz243) (@Enclosure.Real.IsNear.mulLit_ff qz240 qz3 744291 1000 0 1 5340353 33554432 1 33554432 3974776674723 33554432000 744291 33554432000 (Enclosure.Real.IsNear.const Bool.false 744291 1000) RS385to396.d48 rfl)) 

noncomputable abbrev qz766 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 744291 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz697 := qz766

noncomputable abbrev qz539 := qz697

noncomputable abbrev qz249 := qz539

noncomputable def Ns384p1584 := @Enclosure.Real.IsNear.sqrt_image qz249 365200457 33554432 35 33554432 55349102 55349109 16777216 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 365200457 33554432 35 33554432 365200457 33554432 35 33554432 (Ns384p1583 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns384p1585 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz249) 110698211 33554432 7 33554432 5085447 5085448 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz249) Bool.false 110698211 33554432 7 33554432 110698211 33554432 7 33554432 (Ns384p1584 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns384p1586 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 10170895 33554432 1 33554432 10170895 33554432 1 33554432 (Ns384p1585 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz533))

noncomputable abbrev qz698 := (@HMul.hMul Real Real Real qz707 qz764 qz764)

noncomputable abbrev qz540 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz698 qz691) qz594)

noncomputable abbrev qz251 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz540))

noncomputable def Ns384p1587 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz242) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz250) qz251) Bool.false 191905549933635 

noncomputable def Ns384p1588 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz250) qz251 45027735 33554432 409 

noncomputable def Ns384p1589 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz250) Bool.false 45027735 33554432 409 33554432 45027735 33554432 409 

noncomputable def Ns384p1590 := @Enclosure.Real.IsNear.recentre' qz250 Bool.false 25004587 33554432 1306514432 193273528320000 25004587 33554432 1275893 188743680000 

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz349 qz346 qz533)

noncomputable def Ns384p1591 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46583751) qz394) Bool.false 46583751 8388608 221 33554432 Bool.false 25004587 33554432 1 

noncomputable def Ns384p1592 := nat_lit 944512639571285868012304949 

noncomputable def Ns384p1593 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz242 884279719003555 140737488355328 1 500000000000000 29656137 33554432 35 33554432 26224320493090930567035 4722366482869645213696 Ns384p1592 

noncomputable def Ns384p1594 := @Enclosure.Real.IsNear.subLit_ff_p qz249 qz1 365200457 33554432 35 33554432 10 1 0 1 29656137 29656137 33554432 35 

noncomputable def Ns384p1595 := @Ns384p1594 33554432 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 365200457 33554432 35 33554432 365200457 33554432 35 33554432 (Ns384p1583 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns384p1596 := @Enclosure.Real.IsNear.recentre' qz252 Bool.false 26224320493090930567035 4722366482869645213696 Ns384p1592 Ns384p295 46583751 8388608 221 33554432 (@Ns384p1593 Ns384p295 RS385to396.d47 (Ns384p1595 rfl rfl) rfl) 

noncomputable def Ns384p1597 := nat_lit 751828294851825888064074687331101005891638230838267503202721309707266999377878381169577505 

noncomputable def Ns384p1598 := nat_lit 124248584875757911518914805198373807923150369371999861745599231198240991586571493150241 

noncomputable def Ns384p1599 := nat_lit 1968872941188792765453926890468276695931938837311717365754777221906616417717588930169507361 

noncomputable def Ns384p1600 := BSN.sin_dyadic_bound_f 57781183283 68719476736 3 2 33554432 11531251 Ns384p1597 Ns384p1131 Ns384p1598 Ns384p1599 Ns384p1134 Ns384p1598 25004587 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 57781183283) qz368 0 2 Ns384p1597 Ns384p1131 Ns384p1598 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 57781183283) qz369 0 2 Ns384p1599 Ns384p1134 Ns384p1598 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1601 := @Ns384p1591 5760000 (Ns384p1596 rfl) (Enclosure.sfrac_false_div 46583751 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46583751) qz394) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1016497326189331404029952) (@Nat.cast Real Real.instNatCast Ns384p239)) 226375608064910080 72057594037927936 Bool.false 25004587 33554432 0 1000000000000000 11520000 5760000 (BSN.sin_reduce_arg_pos_rat_q3 46583751 8388608 226375608064910080 72057594037927936 0 1016497326189331404029952 Ns384p239 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 25004587 33554432 1016497326189331404029952 Ns384p239 57781183283 68719476736 11531251 11520000 (Ns384p1600 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns384p1602 := @Enclosure.Real.IsNear.inv_image qz250 25004587 33554432 1275893 188743680000 22513663 22514072 16777216 (Ns384p1590 (Ns384p1601 rfl rfl) rfl) rfl 

noncomputable def Ns384p1603 := @Enclosure.Real.IsNear.recentre' qz251 Bool.false 8523882 16777216 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz349 qz346 qz540)

noncomputable def Ns384p1604 := @Enclosure.Real.IsNear.cos_image qz253 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8706217)) qz394) Bool.true 8706217 8388608 

noncomputable def Ns384p1605 := nat_lit 164455790784671678056787300845 

noncomputable def Ns384p1606 := nat_lit 87713810648233216192141441058049913 

noncomputable def Ns384p1607 := @Enclosure.Real.IsNear.recentre' qz253 Bool.true Ns384p1605 Ns384p307 Ns384p1606 

noncomputable abbrev qz254 := qz540

noncomputable def Ns384p1608 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz254 884279719003555 140737488355328 1 500000000000000 185977114764079 

noncomputable abbrev qz541 := (@HSub.hSub Real Real Real qz583 qz698 qz691)

noncomputable abbrev qz255 := qz541

noncomputable def Ns384p1609 := @Enclosure.Real.IsNear.subLit_tf qz255 qz29 115608370586415 1125899906842624 3250335935 1125899906842624 1 16 

noncomputable abbrev qz542 := qz698

noncomputable abbrev qz256 := qz542

noncomputable def Ns384p1610 := @Enclosure.Real.IsNear.subLit_ff_n qz256 qz242 879486461762769 1125899906842624 2075930815 1125899906842624 29656137 33554432 35 33554432 

noncomputable def Ns384p1611 := @Enclosure.Real.IsNear.mulLit_ff qz242 qz242 29656137 33554432 35 33554432 29656137 33554432 35 33554432 879486461762769 1125899906842624 

noncomputable def Ns384p1612 := nat_lit 47828489908307879198093145074948779326762587788280178861121 

noncomputable def Ns384p1613 := nat_lit 33009268553945767190833339343293116876871877293216818241 

noncomputable def Ns384p1614 := nat_lit 143419451187815746059897768546159751746534019610254102946881 

noncomputable def Ns384p1615 := BSN.cos_dyadic_bound_f 8706217 8388608 3 2 16777216 5760000 Ns384p1612 Ns384p1267 Ns384p1613 Ns384p1614 Ns384p1270 Ns384p1613 8523882 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 8706217) (BSN.cosEvenQ 8388608) 0 2 Ns384p1612 Ns384p1267 Ns384p1613 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 8706217) (BSN.cosOddQ 8388608) 0 2 Ns384p1614 Ns384p1270 Ns384p1613 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns384p1616 := @Ns384p1603 3541394432 193273528320000 4261941 8388608 3458393 188743680000 (@Ns384p1604 609 33554432 Bool.false 8523882 16777216 1 5760000 (@Ns384p1607 Ns384p463 8706217 8388608 609 33554432 (@Ns384p1608 1125899906842624 3250335935 1125899906842624 Ns384p1605 Ns384p307 Ns384p1606 Ns384p463 RS385to396.d47 (@Ns384p1609 0 1 2975633836225264 185977114764079 1125899906842624 3250335935 1125899906842624 (@Ns384p1610 3879173209472662241280 115608370586415 1125899906842624 3250335935 1125899906842624 (@Ns384p1611 2075930815 1125899906842624 (Ns384p1595 rfl rfl) (Ns384p1595 rfl rfl) rfl) (Ns384p1595 rfl rfl) rfl rfl) qz384 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8706217 8388608) (BSN.cos_neg_of_bound 8706217 8388608 Bool.false 8523882 16777216 1 5760000 (Ns384p1615 rfl rfl)) rfl rfl) 

noncomputable def Ns384p1617 := @Ns384p1581 496772146707607687483 Ns384p1509 (Ns384p1582 qz31 (@Enclosure.Real.IsNear.of_eq qz696 (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 10170895 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz241 (BSN.t_div_two_pi_nonneg qz240 744291 1000 qz243)) Ns384p1586) rfl) (@Ns384p1587 281474976710656 48736382516273 1583296743997440000 (BSN.correction_mk qz242 (BSN.cos_two_pi_p_ne_zero_mk qz240 744291 1000 10 qz243 rfl rfl (@BSN.floor_sqrt_eq_dec qz240 744291 1000 10 qz243 rfl rfl rfl))) (@Ns384p1588 33554432 4261941 8388608 3458393 188743680000 191905549933635 281474976710656 48736382516273 1583296743997440000 (@Ns384p1589 33554432 (Ns384p1602 rfl rfl rfl rfl rfl) rfl) (Ns384p1616 rfl) rfl)) 

noncomputable def Ns384p1618 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (hardyZApproximantRS₀ qz240) Bool.true 24327274800353908456941 9444732965739290427392 61902165593346322567483 Ns384p1509 (@Eq.refl Real (hardyZApproximantRS₀ qz240)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (@HMul.hMul Real Real Real qz5 qz692 (Zeta.RiemannSiegel.correction qz242))) Bool.true 24327274800353908456941 9444732965739290427392 61902165593346322567483 Ns384p1509 (BSN.hardyZApproximantRS₀_eq qz240 10 (@BSN.floor_sqrt_eq_dec qz240 744291 1000 10 qz243 rfl rfl rfl)) (@Ns384p1511 24327274800353908456941 9444732965739290427392 61902165593346322567483 Ns384p1509 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10)) Bool.true 158986947 67108864 155133 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (Ns384p1580 (Ns384p1579 rfl rfl rfl rfl) rfl rfl)) (Ns384p1617 rfl) rfl rfl)) 

theorem RS385to396.d63 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz240) Bool.true 24327274800353908456941 9444732965739290427392 61902165593346322567483 Ns384p1509 := Ns384p1618 

noncomputable def RS385to396.d64 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz543 := (RS385to396.d3 qz580 qz595 (@Enclosure.dec_le_dec qz580 qz595 728464 1000 729786 1000 (@Eq.refl Real qz580) qz598 rfl rfl rfl))

noncomputable abbrev qz257 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz543)

noncomputable def Ns384p1619 := @Enclosure.Real.IsNear.of_eq qz257 (hardyZApproximantRS₀ qz4) Bool.true 279020558697730550323 4722366482869645213696 10502464157076402796759 Ns384p74 

noncomputable abbrev qz544 := (@Enclosure.dec_le_dec qz580 qz595 728464 1000 729786 1000 (@Eq.refl Real qz580) qz598 rfl rfl rfl)

noncomputable abbrev qz258 := qz544

noncomputable def Ns384p1620 := @Enclosure.Real.IsNear.neg_val qz257 279020558697730550323 4722366482869645213696 10502464157076402796759 Ns384p74 (Ns384p1619 (RS385to396.d4 qz4 qz33 qz258) RS385to396.d49) rfl 

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz543)

noncomputable def Ns384p1621 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantRS₀ qz33) Bool.false 15014982783562576603421 9444732965739290427392 6906294237471757213453 Ns384p206 

noncomputable def Ns384p1622 := @Enclosure.Real.IsNear.pos_val qz259 15014982783562576603421 9444732965739290427392 6906294237471757213453 Ns384p206 (Ns384p1621 (RS385to396.d50 qz4 qz33 qz258) RS385to396.d51) rfl 

noncomputable def Ns384p1623 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz257 qz4 qz4 728464 1000 728464 1000 

noncomputable def Ns384p1624 := @Enclosure.norm_gt_of_isNear qz257 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 279020558697730550323 4722366482869645213696 10502464157076402796759 

noncomputable def Ns384p1625 := @Ns384p1624 Ns384p74 285733069 5368709120 1213 5368709120 (Ns384p1619 (RS385to396.d4 qz4 qz33 qz258) RS385to396.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable def Ns384p1626 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz259 qz4 qz33 728464 1000 729786 1000 

noncomputable def Ns384p1627 := @Enclosure.norm_gt_of_isNear qz259 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 15014982783562576603421 9444732965739290427392 6906294237471757213453 

noncomputable def Ns384p1628 := @Ns384p1627 Ns384p206 285733069 5368709120 1213 5368709120 (Ns384p1621 (RS385to396.d50 qz4 qz33 qz258) RS385to396.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable abbrev qz260 := qz543

noncomputable def Ns384p1629 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz260 (@BSN.thirtyTwoPi_le_dec qz4 728464 1000 qz9 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz257 qz259 (Ns384p1620 rfl rfl) (Ns384p1622 rfl rfl)) (Ns384p1623 qz9 qz9 rfl rfl rfl rfl (Ns384p1625 rfl)) (Ns384p1626 qz9 qz36 rfl rfl rfl rfl (Ns384p1628 rfl)) 

noncomputable abbrev qz545 := (RS385to396.d3 qz595 qz605 (@Enclosure.dec_le_dec qz595 qz605 729786 1000 731107 1000 qz598 qz608 rfl rfl rfl))

noncomputable abbrev qz261 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz545)

noncomputable def Ns384p1630 := @Enclosure.Real.IsNear.of_eq qz261 (hardyZApproximantRS₀ qz33) Bool.false 15014982783562576603421 9444732965739290427392 6906294237471757213453 Ns384p206 

noncomputable abbrev qz546 := (@Enclosure.dec_le_dec qz595 qz605 729786 1000 731107 1000 qz598 qz608 rfl rfl rfl)

noncomputable abbrev qz262 := qz546

noncomputable def Ns384p1631 := @Enclosure.Real.IsNear.pos_val qz261 15014982783562576603421 9444732965739290427392 6906294237471757213453 Ns384p206 (Ns384p1630 (RS385to396.d4 qz33 qz60 qz262) RS385to396.d51) rfl 

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz545)

noncomputable def Ns384p1632 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantRS₀ qz60) Bool.true 8441125768805954460237 9444732965739290427392 20591421335077765203929 Ns384p357 

noncomputable def Ns384p1633 := @Enclosure.Real.IsNear.neg_val qz263 8441125768805954460237 9444732965739290427392 20591421335077765203929 Ns384p357 (Ns384p1632 (RS385to396.d50 qz33 qz60 qz262) RS385to396.d53) rfl 

noncomputable def Ns384p1634 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz261 qz4 qz33 728464 1000 729786 1000 

noncomputable def Ns384p1635 := @Enclosure.norm_gt_of_isNear qz261 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 15014982783562576603421 9444732965739290427392 6906294237471757213453 

noncomputable def Ns384p1636 := @Ns384p1635 Ns384p206 285733069 5368709120 1213 5368709120 (Ns384p1630 (RS385to396.d4 qz33 qz60 qz262) RS385to396.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable def Ns384p1637 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz263 qz4 qz60 728464 1000 731107 1000 

noncomputable def Ns384p1638 := @Enclosure.norm_gt_of_isNear qz263 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 8441125768805954460237 9444732965739290427392 20591421335077765203929 

noncomputable def Ns384p1639 := @Ns384p1638 Ns384p357 285733069 5368709120 1213 5368709120 (Ns384p1632 (RS385to396.d50 qz33 qz60 qz262) RS385to396.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable abbrev qz264 := qz545

noncomputable def Ns384p1640 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz264 (@BSN.thirtyTwoPi_le_dec qz33 729786 1000 qz36 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz261 qz263 (Ns384p1631 rfl rfl) (Ns384p1633 rfl rfl)) (Ns384p1634 qz9 qz36 rfl rfl rfl rfl (Ns384p1636 rfl)) (Ns384p1637 qz9 qz63 rfl rfl rfl rfl (Ns384p1639 rfl)) 

noncomputable abbrev qz547 := (RS385to396.d3 qz605 qz613 (@Enclosure.dec_le_dec qz605 qz613 731107 1000 732428 1000 qz608 qz616 rfl rfl rfl))

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz547)

noncomputable def Ns384p1641 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantRS₀ qz60) Bool.true 8441125768805954460237 9444732965739290427392 20591421335077765203929 Ns384p357 

noncomputable abbrev qz548 := (@Enclosure.dec_le_dec qz605 qz613 731107 1000 732428 1000 qz608 qz616 rfl rfl rfl)

noncomputable abbrev qz266 := qz548

noncomputable def Ns384p1642 := @Enclosure.Real.IsNear.neg_val qz265 8441125768805954460237 9444732965739290427392 20591421335077765203929 Ns384p357 (Ns384p1641 (RS385to396.d4 qz60 qz78 qz266) RS385to396.d53) rfl 

noncomputable abbrev qz267 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz547)

noncomputable def Ns384p1643 := @Enclosure.Real.IsNear.of_eq qz267 (hardyZApproximantRS₀ qz78) Bool.false 1240417213635205171007 590295810358705651712 213887202137220795569 184467440737095516160000 

noncomputable def Ns384p1644 := @Enclosure.Real.IsNear.pos_val qz267 1240417213635205171007 590295810358705651712 213887202137220795569 184467440737095516160000 (Ns384p1643 (RS385to396.d50 qz60 qz78 qz266) RS385to396.d54) rfl 

noncomputable def Ns384p1645 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz265 qz4 qz60 728464 1000 731107 1000 

noncomputable def Ns384p1646 := @Enclosure.norm_gt_of_isNear qz265 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 8441125768805954460237 9444732965739290427392 20591421335077765203929 

noncomputable def Ns384p1647 := @Ns384p1646 Ns384p357 285733069 5368709120 1213 5368709120 (Ns384p1641 (RS385to396.d4 qz60 qz78 qz266) RS385to396.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable def Ns384p1648 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz267 qz4 qz78 728464 1000 732428 1000 

noncomputable def Ns384p1649 := @Enclosure.norm_gt_of_isNear qz267 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1240417213635205171007 590295810358705651712 213887202137220795569 

noncomputable def Ns384p1650 := @Ns384p1649 184467440737095516160000 285733069 5368709120 1213 5368709120 (Ns384p1643 (RS385to396.d50 qz60 qz78 qz266) RS385to396.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable abbrev qz268 := qz547

noncomputable def Ns384p1651 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz60 731107 1000 qz63 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz265 qz267 (Ns384p1642 rfl rfl) (Ns384p1644 rfl rfl)) (Ns384p1645 qz9 qz63 rfl rfl rfl rfl (Ns384p1647 rfl)) (Ns384p1648 qz9 qz81 rfl rfl rfl rfl (Ns384p1650 rfl)) 

noncomputable abbrev qz549 := (RS385to396.d3 qz613 qz621 (@Enclosure.dec_le_dec qz613 qz621 732428 1000 733748 1000 qz616 qz624 rfl rfl rfl))

noncomputable abbrev qz269 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz549)

noncomputable def Ns384p1652 := @Enclosure.Real.IsNear.of_eq qz269 (hardyZApproximantRS₀ qz78) Bool.false 1240417213635205171007 590295810358705651712 213887202137220795569 184467440737095516160000 

noncomputable abbrev qz550 := (@Enclosure.dec_le_dec qz613 qz621 732428 1000 733748 1000 qz616 qz624 rfl rfl rfl)

noncomputable abbrev qz270 := qz550

noncomputable def Ns384p1653 := @Enclosure.Real.IsNear.pos_val qz269 1240417213635205171007 590295810358705651712 213887202137220795569 184467440737095516160000 (Ns384p1652 (RS385to396.d4 qz78 qz96 qz270) RS385to396.d54) rfl 

noncomputable abbrev qz271 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz549)

noncomputable def Ns384p1654 := @Enclosure.Real.IsNear.of_eq qz271 (hardyZApproximantRS₀ qz96) Bool.true 12249007535291811788321 2361183241434822606848 7690570316722283912839 Ns384p591 

noncomputable def Ns384p1655 := @Enclosure.Real.IsNear.neg_val qz271 12249007535291811788321 2361183241434822606848 7690570316722283912839 Ns384p591 (Ns384p1654 (RS385to396.d50 qz78 qz96 qz270) RS385to396.d55) rfl 

noncomputable def Ns384p1656 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz269 qz4 qz78 728464 1000 732428 1000 

noncomputable def Ns384p1657 := @Enclosure.norm_gt_of_isNear qz269 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1240417213635205171007 590295810358705651712 213887202137220795569 

noncomputable def Ns384p1658 := @Ns384p1657 184467440737095516160000 285733069 5368709120 1213 5368709120 (Ns384p1652 (RS385to396.d4 qz78 qz96 qz270) RS385to396.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable def Ns384p1659 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz271 qz4 qz96 728464 1000 733748 1000 

noncomputable def Ns384p1660 := @Enclosure.norm_gt_of_isNear qz271 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 12249007535291811788321 2361183241434822606848 7690570316722283912839 

noncomputable def Ns384p1661 := @Ns384p1660 Ns384p591 285733069 5368709120 1213 5368709120 (Ns384p1654 (RS385to396.d50 qz78 qz96 qz270) RS385to396.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable abbrev qz272 := qz549

noncomputable def Ns384p1662 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz78 732428 1000 qz81 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz269 qz271 (Ns384p1653 rfl rfl) (Ns384p1655 rfl rfl)) (Ns384p1656 qz9 qz81 rfl rfl rfl rfl (Ns384p1658 rfl)) (Ns384p1659 qz9 qz99 rfl rfl rfl rfl (Ns384p1661 rfl)) 

noncomputable abbrev qz551 := (RS385to396.d3 qz621 qz629 (@Enclosure.dec_le_dec qz621 qz629 733748 1000 735068 1000 qz624 qz632 rfl rfl rfl))

noncomputable abbrev qz273 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz551)

noncomputable def Ns384p1663 := @Enclosure.Real.IsNear.of_eq qz273 (hardyZApproximantRS₀ qz96) Bool.true 12249007535291811788321 2361183241434822606848 7690570316722283912839 Ns384p591 

noncomputable abbrev qz552 := (@Enclosure.dec_le_dec qz621 qz629 733748 1000 735068 1000 qz624 qz632 rfl rfl rfl)

noncomputable abbrev qz274 := qz552

noncomputable def Ns384p1664 := @Enclosure.Real.IsNear.neg_val qz273 12249007535291811788321 2361183241434822606848 7690570316722283912839 Ns384p591 (Ns384p1663 (RS385to396.d4 qz96 qz114 qz274) RS385to396.d55) rfl 

noncomputable abbrev qz275 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz551)

noncomputable def Ns384p1665 := @Enclosure.Real.IsNear.of_eq qz275 (hardyZApproximantRS₀ qz114) Bool.false 5231413521069482474259 4722366482869645213696 3416759417772604139091 Ns384p704 

noncomputable def Ns384p1666 := @Enclosure.Real.IsNear.pos_val qz275 5231413521069482474259 4722366482869645213696 3416759417772604139091 Ns384p704 (Ns384p1665 (RS385to396.d50 qz96 qz114 qz274) RS385to396.d56) rfl 

noncomputable def Ns384p1667 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz273 qz4 qz96 728464 1000 733748 1000 

noncomputable def Ns384p1668 := @Enclosure.norm_gt_of_isNear qz273 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 12249007535291811788321 2361183241434822606848 7690570316722283912839 

noncomputable def Ns384p1669 := @Ns384p1668 Ns384p591 285733069 5368709120 1213 5368709120 (Ns384p1663 (RS385to396.d4 qz96 qz114 qz274) RS385to396.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable def Ns384p1670 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz275 qz4 qz114 728464 1000 735068 1000 

noncomputable def Ns384p1671 := @Enclosure.norm_gt_of_isNear qz275 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 5231413521069482474259 4722366482869645213696 3416759417772604139091 

noncomputable def Ns384p1672 := @Ns384p1671 Ns384p704 285733069 5368709120 1213 5368709120 (Ns384p1665 (RS385to396.d50 qz96 qz114 qz274) RS385to396.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable abbrev qz276 := qz551

noncomputable def Ns384p1673 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz96 733748 1000 qz99 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz273 qz275 (Ns384p1664 rfl rfl) (Ns384p1666 rfl rfl)) (Ns384p1667 qz9 qz99 rfl rfl rfl rfl (Ns384p1669 rfl)) (Ns384p1670 qz9 qz117 rfl rfl rfl rfl (Ns384p1672 rfl)) 

noncomputable abbrev qz553 := (RS385to396.d3 qz629 qz637 (@Enclosure.dec_le_dec qz629 qz637 735068 1000 736387 1000 qz632 qz640 rfl rfl rfl))

noncomputable abbrev qz277 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz553)

noncomputable def Ns384p1674 := @Enclosure.Real.IsNear.of_eq qz277 (hardyZApproximantRS₀ qz114) Bool.false 5231413521069482474259 4722366482869645213696 3416759417772604139091 Ns384p704 

noncomputable abbrev qz554 := (@Enclosure.dec_le_dec qz629 qz637 735068 1000 736387 1000 qz632 qz640 rfl rfl rfl)

noncomputable abbrev qz278 := qz554

noncomputable def Ns384p1675 := @Enclosure.Real.IsNear.pos_val qz277 5231413521069482474259 4722366482869645213696 3416759417772604139091 Ns384p704 (Ns384p1674 (RS385to396.d4 qz114 qz132 qz278) RS385to396.d56) rfl 

noncomputable abbrev qz279 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz553)

noncomputable def Ns384p1676 := @Enclosure.Real.IsNear.of_eq qz279 (hardyZApproximantRS₀ qz132) Bool.true 4296134371143401482277 2361183241434822606848 341734754656689176303 295147905179352825856000 

noncomputable def Ns384p1677 := @Enclosure.Real.IsNear.neg_val qz279 4296134371143401482277 2361183241434822606848 341734754656689176303 295147905179352825856000 (Ns384p1676 (RS385to396.d50 qz114 qz132 qz278) RS385to396.d57) rfl 

noncomputable def Ns384p1678 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz277 qz4 qz114 728464 1000 735068 1000 

noncomputable def Ns384p1679 := @Enclosure.norm_gt_of_isNear qz277 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 5231413521069482474259 4722366482869645213696 3416759417772604139091 

noncomputable def Ns384p1680 := @Ns384p1679 Ns384p704 285733069 5368709120 1213 5368709120 (Ns384p1674 (RS385to396.d4 qz114 qz132 qz278) RS385to396.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable def Ns384p1681 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz279 qz4 qz132 728464 1000 736387 1000 

noncomputable def Ns384p1682 := @Enclosure.norm_gt_of_isNear qz279 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 4296134371143401482277 2361183241434822606848 341734754656689176303 

noncomputable def Ns384p1683 := @Ns384p1682 295147905179352825856000 285733069 5368709120 1213 5368709120 (Ns384p1676 (RS385to396.d50 qz114 qz132 qz278) RS385to396.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable abbrev qz280 := qz553

noncomputable def Ns384p1684 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz114 735068 1000 qz117 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz277 qz279 (Ns384p1675 rfl rfl) (Ns384p1677 rfl rfl)) (Ns384p1678 qz9 qz117 rfl rfl rfl rfl (Ns384p1680 rfl)) (Ns384p1681 qz9 qz135 rfl rfl rfl rfl (Ns384p1683 rfl)) 

noncomputable abbrev qz555 := (RS385to396.d3 qz637 qz645 (@Enclosure.dec_le_dec qz637 qz645 736387 1000 737705 1000 qz640 qz648 rfl rfl rfl))

noncomputable abbrev qz281 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz555)

noncomputable def Ns384p1685 := @Enclosure.Real.IsNear.of_eq qz281 (hardyZApproximantRS₀ qz132) Bool.true 4296134371143401482277 2361183241434822606848 341734754656689176303 295147905179352825856000 

noncomputable abbrev qz556 := (@Enclosure.dec_le_dec qz637 qz645 736387 1000 737705 1000 qz640 qz648 rfl rfl rfl)

noncomputable abbrev qz282 := qz556

noncomputable def Ns384p1686 := @Enclosure.Real.IsNear.neg_val qz281 4296134371143401482277 2361183241434822606848 341734754656689176303 295147905179352825856000 (Ns384p1685 (RS385to396.d4 qz132 qz150 qz282) RS385to396.d57) rfl 

noncomputable abbrev qz283 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz555)

noncomputable def Ns384p1687 := @Enclosure.Real.IsNear.of_eq qz283 (hardyZApproximantRS₀ qz150) Bool.false 170913482278560845055 73786976294838206464 1538774893747348667521 Ns384p921 

noncomputable def Ns384p1688 := @Enclosure.Real.IsNear.pos_val qz283 170913482278560845055 73786976294838206464 1538774893747348667521 Ns384p921 (Ns384p1687 (RS385to396.d50 qz132 qz150 qz282) RS385to396.d58) rfl 

noncomputable def Ns384p1689 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz281 qz4 qz132 728464 1000 736387 1000 

noncomputable def Ns384p1690 := @Enclosure.norm_gt_of_isNear qz281 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 4296134371143401482277 2361183241434822606848 341734754656689176303 

noncomputable def Ns384p1691 := @Ns384p1690 295147905179352825856000 285733069 5368709120 1213 5368709120 (Ns384p1685 (RS385to396.d4 qz132 qz150 qz282) RS385to396.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable def Ns384p1692 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz283 qz4 qz150 728464 1000 737705 1000 

noncomputable def Ns384p1693 := @Enclosure.norm_gt_of_isNear qz283 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 170913482278560845055 73786976294838206464 1538774893747348667521 

noncomputable def Ns384p1694 := @Ns384p1693 Ns384p921 285733069 5368709120 1213 5368709120 (Ns384p1687 (RS385to396.d50 qz132 qz150 qz282) RS385to396.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable abbrev qz284 := qz555

noncomputable def Ns384p1695 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz132 736387 1000 qz135 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz281 qz283 (Ns384p1686 rfl rfl) (Ns384p1688 rfl rfl)) (Ns384p1689 qz9 qz135 rfl rfl rfl rfl (Ns384p1691 rfl)) (Ns384p1692 qz9 qz153 rfl rfl rfl rfl (Ns384p1694 rfl)) 

noncomputable abbrev qz557 := (RS385to396.d3 qz645 qz653 (@Enclosure.dec_le_dec qz645 qz653 737705 1000 739024 1000 qz648 qz656 rfl rfl rfl))

noncomputable abbrev qz285 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz557)

noncomputable def Ns384p1696 := @Enclosure.Real.IsNear.of_eq qz285 (hardyZApproximantRS₀ qz150) Bool.false 170913482278560845055 73786976294838206464 1538774893747348667521 Ns384p921 

noncomputable abbrev qz558 := (@Enclosure.dec_le_dec qz645 qz653 737705 1000 739024 1000 qz648 qz656 rfl rfl rfl)

noncomputable abbrev qz286 := qz558

noncomputable def Ns384p1697 := @Enclosure.Real.IsNear.pos_val qz285 170913482278560845055 73786976294838206464 1538774893747348667521 Ns384p921 (Ns384p1696 (RS385to396.d4 qz150 qz168 qz286) RS385to396.d58) rfl 

noncomputable abbrev qz287 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz557)

noncomputable def Ns384p1698 := @Enclosure.Real.IsNear.of_eq qz287 (hardyZApproximantRS₀ qz168) Bool.true 12024534439087269979741 9444732965739290427392 12324586271874885836833 Ns384p1037 

noncomputable def Ns384p1699 := @Enclosure.Real.IsNear.neg_val qz287 12024534439087269979741 9444732965739290427392 12324586271874885836833 Ns384p1037 (Ns384p1698 (RS385to396.d50 qz150 qz168 qz286) RS385to396.d59) rfl 

noncomputable def Ns384p1700 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz285 qz4 qz150 728464 1000 737705 1000 

noncomputable def Ns384p1701 := @Enclosure.norm_gt_of_isNear qz285 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 170913482278560845055 73786976294838206464 1538774893747348667521 

noncomputable def Ns384p1702 := @Ns384p1701 Ns384p921 285733069 5368709120 1213 5368709120 (Ns384p1696 (RS385to396.d4 qz150 qz168 qz286) RS385to396.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable def Ns384p1703 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz287 qz4 qz168 728464 1000 739024 1000 

noncomputable def Ns384p1704 := @Enclosure.norm_gt_of_isNear qz287 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 12024534439087269979741 9444732965739290427392 12324586271874885836833 

noncomputable def Ns384p1705 := @Ns384p1704 Ns384p1037 285733069 5368709120 1213 5368709120 (Ns384p1698 (RS385to396.d50 qz150 qz168 qz286) RS385to396.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable abbrev qz288 := qz557

noncomputable def Ns384p1706 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz150 737705 1000 qz153 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz285 qz287 (Ns384p1697 rfl rfl) (Ns384p1699 rfl rfl)) (Ns384p1700 qz9 qz153 rfl rfl rfl rfl (Ns384p1702 rfl)) (Ns384p1703 qz9 qz171 rfl rfl rfl rfl (Ns384p1705 rfl)) 

noncomputable abbrev qz699 := (@Enclosure.dec_le_dec qz744 qz748 739024 1000 740341 1000 (@Eq.refl Real qz744) (@Eq.refl Real qz748) rfl rfl rfl)

noncomputable abbrev qz559 := (RS385to396.d3 qz653 qz661 qz699)

noncomputable abbrev qz289 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz559)

noncomputable def Ns384p1707 := @Enclosure.Real.IsNear.of_eq qz289 (hardyZApproximantRS₀ qz168) Bool.true 12024534439087269979741 9444732965739290427392 12324586271874885836833 Ns384p1037 

noncomputable abbrev qz560 := qz699

noncomputable abbrev qz290 := qz560

noncomputable def Ns384p1708 := @Enclosure.Real.IsNear.neg_val qz289 12024534439087269979741 9444732965739290427392 12324586271874885836833 Ns384p1037 (Ns384p1707 (RS385to396.d4 qz168 qz186 qz290) RS385to396.d59) rfl 

noncomputable abbrev qz291 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz559)

noncomputable def Ns384p1709 := @Enclosure.Real.IsNear.of_eq qz291 (hardyZApproximantRS₀ qz186) Bool.false 198290439229636537939 590295810358705651712 171299274798831062021 147573952589676412928000 

noncomputable def Ns384p1710 := @Enclosure.Real.IsNear.pos_val qz291 198290439229636537939 590295810358705651712 171299274798831062021 147573952589676412928000 (Ns384p1709 (RS385to396.d50 qz168 qz186 qz290) RS385to396.d60) rfl 

noncomputable def Ns384p1711 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz289 qz4 qz168 728464 1000 739024 1000 

noncomputable def Ns384p1712 := @Enclosure.norm_gt_of_isNear qz289 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 12024534439087269979741 9444732965739290427392 12324586271874885836833 

noncomputable def Ns384p1713 := @Ns384p1712 Ns384p1037 285733069 5368709120 1213 5368709120 (Ns384p1707 (RS385to396.d4 qz168 qz186 qz290) RS385to396.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable def Ns384p1714 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz291 qz4 qz186 728464 1000 740341 1000 

noncomputable def Ns384p1715 := @Enclosure.norm_gt_of_isNear qz291 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 198290439229636537939 590295810358705651712 171299274798831062021 

noncomputable def Ns384p1716 := @Ns384p1715 147573952589676412928000 285733069 5368709120 1213 5368709120 (Ns384p1709 (RS385to396.d50 qz168 qz186 qz290) RS385to396.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable abbrev qz292 := qz559

noncomputable def Ns384p1717 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz168 739024 1000 qz171 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz289 qz291 (Ns384p1708 rfl rfl) (Ns384p1710 rfl rfl)) (Ns384p1711 qz9 qz171 rfl rfl rfl rfl (Ns384p1713 rfl)) (Ns384p1714 qz9 qz189 rfl rfl rfl rfl (Ns384p1716 rfl)) 

noncomputable abbrev qz700 := (@Enclosure.dec_le_dec qz748 qz752 740341 1000 741658 1000 (@Eq.refl Real qz748) qz755 rfl rfl rfl)

noncomputable abbrev qz561 := (RS385to396.d3 qz661 qz669 qz700)

noncomputable abbrev qz293 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz561)

noncomputable def Ns384p1718 := @Enclosure.Real.IsNear.of_eq qz293 (hardyZApproximantRS₀ qz186) Bool.false 198290439229636537939 590295810358705651712 171299274798831062021 147573952589676412928000 

noncomputable abbrev qz562 := qz700

noncomputable abbrev qz294 := qz562

noncomputable def Ns384p1719 := @Enclosure.Real.IsNear.pos_val qz293 198290439229636537939 590295810358705651712 171299274798831062021 147573952589676412928000 (Ns384p1718 (RS385to396.d4 qz186 qz204 qz294) RS385to396.d60) rfl 

noncomputable abbrev qz295 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz561)

noncomputable def Ns384p1720 := @Enclosure.Real.IsNear.of_eq qz295 (hardyZApproximantRS₀ qz204) Bool.true 1201570739859055489739 2361183241434822606848 1715040167546097868711 Ns384p1275 

noncomputable def Ns384p1721 := @Enclosure.Real.IsNear.neg_val qz295 1201570739859055489739 2361183241434822606848 1715040167546097868711 Ns384p1275 (Ns384p1720 (RS385to396.d50 qz186 qz204 qz294) RS385to396.d61) rfl 

noncomputable def Ns384p1722 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz293 qz4 qz186 728464 1000 740341 1000 

noncomputable def Ns384p1723 := @Enclosure.norm_gt_of_isNear qz293 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 198290439229636537939 590295810358705651712 171299274798831062021 

noncomputable def Ns384p1724 := @Ns384p1723 147573952589676412928000 285733069 5368709120 1213 5368709120 (Ns384p1718 (RS385to396.d4 qz186 qz204 qz294) RS385to396.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable def Ns384p1725 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz295 qz4 qz204 728464 1000 741658 1000 

noncomputable def Ns384p1726 := @Enclosure.norm_gt_of_isNear qz295 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1201570739859055489739 2361183241434822606848 1715040167546097868711 

noncomputable def Ns384p1727 := @Ns384p1726 Ns384p1275 285733069 5368709120 1213 5368709120 (Ns384p1720 (RS385to396.d50 qz186 qz204 qz294) RS385to396.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable abbrev qz296 := qz561

noncomputable def Ns384p1728 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz186 740341 1000 qz189 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz293 qz295 (Ns384p1719 rfl rfl) (Ns384p1721 rfl rfl)) (Ns384p1722 qz9 qz189 rfl rfl rfl rfl (Ns384p1724 rfl)) (Ns384p1725 qz9 qz209 rfl rfl rfl rfl (Ns384p1727 rfl)) 

noncomputable abbrev qz701 := (@Enclosure.dec_le_dec qz752 qz757 741658 1000 742975 1000 qz755 qz760 rfl rfl rfl)

noncomputable abbrev qz563 := (RS385to396.d3 qz669 qz679 qz701)

noncomputable abbrev qz297 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz563)

noncomputable def Ns384p1729 := @Enclosure.Real.IsNear.of_eq qz297 (hardyZApproximantRS₀ qz204) Bool.true 1201570739859055489739 2361183241434822606848 1715040167546097868711 Ns384p1275 

noncomputable abbrev qz564 := qz701

noncomputable abbrev qz298 := qz564

noncomputable def Ns384p1730 := @Enclosure.Real.IsNear.neg_val qz297 1201570739859055489739 2361183241434822606848 1715040167546097868711 Ns384p1275 (Ns384p1729 (RS385to396.d4 qz204 qz223 qz298) RS385to396.d61) rfl 

noncomputable abbrev qz299 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz563)

noncomputable def Ns384p1731 := @Enclosure.Real.IsNear.of_eq qz299 (hardyZApproximantRS₀ qz223) Bool.false 31124132956081188543755 4722366482869645213696 10303358167598852814481 Ns384p74 

noncomputable def Ns384p1732 := @Enclosure.Real.IsNear.pos_val qz299 31124132956081188543755 4722366482869645213696 10303358167598852814481 Ns384p74 (Ns384p1731 (RS385to396.d50 qz204 qz223 qz298) RS385to396.d62) rfl 

noncomputable def Ns384p1733 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz297 qz4 qz204 728464 1000 741658 1000 

noncomputable def Ns384p1734 := @Enclosure.norm_gt_of_isNear qz297 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1201570739859055489739 2361183241434822606848 1715040167546097868711 

noncomputable def Ns384p1735 := @Ns384p1734 Ns384p1275 285733069 5368709120 1213 5368709120 (Ns384p1729 (RS385to396.d4 qz204 qz223 qz298) RS385to396.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable def Ns384p1736 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz299 qz4 qz223 728464 1000 742975 1000 

noncomputable def Ns384p1737 := @Enclosure.norm_gt_of_isNear qz299 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 31124132956081188543755 4722366482869645213696 10303358167598852814481 

noncomputable def Ns384p1738 := @Ns384p1737 Ns384p74 285733069 5368709120 1213 5368709120 (Ns384p1731 (RS385to396.d50 qz204 qz223 qz298) RS385to396.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable abbrev qz300 := qz563

noncomputable def Ns384p1739 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz204 741658 1000 qz209 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz297 qz299 (Ns384p1730 rfl rfl) (Ns384p1732 rfl rfl)) (Ns384p1733 qz9 qz209 rfl rfl rfl rfl (Ns384p1735 rfl)) (Ns384p1736 qz9 qz226 rfl rfl rfl rfl (Ns384p1738 rfl)) 

noncomputable abbrev qz767 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 742975 1000) (Enclosure.sfrac Bool.false 744291 1000) 742975 1000 744291 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 742975 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 744291 1000)) rfl rfl rfl)

noncomputable abbrev qz702 := qz767

noncomputable abbrev qz565 := (RS385to396.d3 qz679 qz689 qz702)

noncomputable abbrev qz301 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz565)

noncomputable def Ns384p1740 := @Enclosure.Real.IsNear.of_eq qz301 (hardyZApproximantRS₀ qz223) Bool.false 31124132956081188543755 4722366482869645213696 10303358167598852814481 Ns384p74 

noncomputable abbrev qz566 := qz702

noncomputable abbrev qz302 := qz566

noncomputable def Ns384p1741 := @Enclosure.Real.IsNear.pos_val qz301 31124132956081188543755 4722366482869645213696 10303358167598852814481 Ns384p74 (Ns384p1740 (RS385to396.d4 qz223 qz240 qz302) RS385to396.d62) rfl 

noncomputable abbrev qz303 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz565)

noncomputable def Ns384p1742 := @Enclosure.Real.IsNear.of_eq qz303 (hardyZApproximantRS₀ qz240) Bool.true 24327274800353908456941 9444732965739290427392 61902165593346322567483 Ns384p1509 

noncomputable def Ns384p1743 := @Enclosure.Real.IsNear.neg_val qz303 24327274800353908456941 9444732965739290427392 61902165593346322567483 Ns384p1509 (Ns384p1742 (RS385to396.d50 qz223 qz240 qz302) RS385to396.d63) rfl 

noncomputable def Ns384p1744 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz301 qz4 qz223 728464 1000 742975 1000 

noncomputable def Ns384p1745 := @Enclosure.norm_gt_of_isNear qz301 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 31124132956081188543755 4722366482869645213696 10303358167598852814481 

noncomputable def Ns384p1746 := @Ns384p1745 Ns384p74 285733069 5368709120 1213 5368709120 (Ns384p1740 (RS385to396.d4 qz223 qz240 qz302) RS385to396.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable def Ns384p1747 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz303 qz4 qz240 728464 1000 744291 1000 

noncomputable def Ns384p1748 := @Enclosure.norm_gt_of_isNear qz303 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 24327274800353908456941 9444732965739290427392 61902165593346322567483 

noncomputable def Ns384p1749 := @Ns384p1748 Ns384p1509 285733069 5368709120 1213 5368709120 (Ns384p1742 (RS385to396.d50 qz223 qz240 qz302) RS385to396.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 285733069 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS385to396.d52) rfl rfl rfl rfl 

noncomputable abbrev qz304 := qz565

noncomputable def Ns384p1750 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz223 742975 1000 qz226 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz301 qz303 (Ns384p1741 rfl rfl) (Ns384p1743 rfl rfl)) (Ns384p1744 qz9 qz226 rfl rfl rfl rfl (Ns384p1746 rfl)) (Ns384p1747 qz9 qz243 rfl rfl rfl rfl (Ns384p1749 rfl)) 

noncomputable def Ns384p1751 := @List.cons RS385to396.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns384p1739)) (@List.cons RS385to396.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns384p1750)) (@List.nil RS385to396.d0)) 

noncomputable def Ns384p1752 := @List.cons RS385to396.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns384p1717)) (@List.cons RS385to396.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns384p1728)) Ns384p1751) 

noncomputable def Ns384p1753 := @List.cons RS385to396.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns384p1695)) (@List.cons RS385to396.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns384p1706)) Ns384p1752) 

noncomputable def Ns384p1754 := @List.cons RS385to396.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns384p1673)) (@List.cons RS385to396.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns384p1684)) Ns384p1753) 

noncomputable def Ns384p1755 := @List.cons RS385to396.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns384p1651)) (@List.cons RS385to396.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns384p1662)) Ns384p1754) 

noncomputable def Ns384p1756 := @List.cons RS385to396.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz260 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz260) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz260) Ns384p1629)) (@List.cons RS385to396.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz264 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz264) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz264) Ns384p1640)) Ns384p1755) 

noncomputable abbrev qz567 := (RS385to396.d2 qz653 qz661 qz699)

noncomputable abbrev qz703 := (RS385to396.d2 qz752 qz757 (@Enclosure.dec_le_dec qz752 qz757 741658 1000 742975 1000 qz755 qz760 rfl rfl rfl))

noncomputable abbrev qz704 := (@List.cons RS385to396.d1 (RS385to396.d2 qz757 qz762 qz767) (@List.nil RS385to396.d1))

noncomputable abbrev qz568 := (@List.cons RS385to396.d1 (RS385to396.d2 qz661 qz669 qz700) (@List.cons RS385to396.d1 qz703 qz704))

noncomputable abbrev qz305 := (@List.cons RS385to396.d1 (RS385to396.d2 qz471 qz483 qz558) (@List.cons RS385to396.d1 qz567 qz568))

noncomputable def Ns384p1757 := @List.cons RS385to396.d1 (RS385to396.d2 qz114 qz132 qz278) (@List.cons RS385to396.d1 (RS385to396.d2 qz132 qz150 qz282) qz305) 

noncomputable abbrev qz306 := (RS385to396.d2 qz432 qz445 qz552)

noncomputable def Ns384p1758 := @List.IsChain.cons_cons RS385to396.d1 RS385to396.d64 qz306 (RS385to396.d2 qz114 qz132 qz278) (@List.cons RS385to396.d1 (RS385to396.d2 qz132 qz150 qz282) qz305) 

noncomputable def Ns384p1759 := @List.IsChain.cons_cons RS385to396.d1 RS385to396.d64 (RS385to396.d2 qz114 qz132 qz278) (RS385to396.d2 qz132 qz150 qz282) qz305 (@Enclosure.dec_le_dec qz132 qz132 736387 1000 736387 1000 qz135 qz135 rfl rfl rfl) 

noncomputable abbrev qz307 := (RS385to396.d2 qz471 qz483 qz558)

noncomputable abbrev qz308 := qz567

noncomputable abbrev qz309 := qz568

noncomputable abbrev qz569 := (RS385to396.d2 qz661 qz669 qz700)

noncomputable abbrev qz310 := qz569

noncomputable abbrev qz570 := (@List.cons RS385to396.d1 qz703 qz704)

noncomputable abbrev qz311 := qz570

noncomputable abbrev qz571 := qz703

noncomputable abbrev qz312 := qz571

noncomputable abbrev qz572 := qz704

noncomputable abbrev qz313 := qz572

noncomputable abbrev qz705 := (RS385to396.d2 qz757 qz762 qz767)

noncomputable abbrev qz573 := qz705

noncomputable abbrev qz314 := qz573

noncomputable def Ns384p1760 := @List.IsChain.cons_cons RS385to396.d1 RS385to396.d64 qz307 qz308 qz309 (@Enclosure.dec_le_dec qz168 qz168 739024 1000 739024 1000 qz171 qz171 rfl rfl rfl) (@List.IsChain.cons_cons RS385to396.d1 RS385to396.d64 qz308 qz310 qz311 (@Enclosure.dec_le_dec qz186 qz186 740341 1000 740341 1000 qz189 qz189 rfl rfl rfl) (@List.IsChain.cons_cons RS385to396.d1 RS385to396.d64 qz310 qz312 qz313 (@Enclosure.dec_le_dec qz204 qz204 741658 1000 741658 1000 qz209 qz209 rfl rfl rfl) (@List.IsChain.cons_cons RS385to396.d1 RS385to396.d64 qz312 qz314 (@List.nil RS385to396.d1) (@Enclosure.dec_le_dec qz223 qz223 742975 1000 742975 1000 qz226 qz226 rfl rfl rfl) (@List.IsChain.singleton RS385to396.d1 RS385to396.d64 qz314)))) 

noncomputable abbrev qz315 := (@List.cons RS385to396.d1 qz567 qz568)

noncomputable def Ns384p1761 := @List.IsChain.cons_cons RS385to396.d1 RS385to396.d64 (RS385to396.d2 qz132 qz150 qz282) qz307 qz315 (@Enclosure.dec_le_dec qz150 qz150 737705 1000 737705 1000 qz153 qz153 rfl rfl rfl) Ns384p1760 

noncomputable def Ns384p1762 := @List.IsChain.cons_cons RS385to396.d1 RS385to396.d64 (RS385to396.d2 qz4 qz33 qz258) (RS385to396.d2 qz33 qz60 qz262) (@List.cons RS385to396.d1 (RS385to396.d2 qz60 qz78 qz266) (@List.cons RS385to396.d1 (RS385to396.d2 qz78 qz96 qz270) (@List.cons RS385to396.d1 qz306 Ns384p1757))) (@Enclosure.dec_le_dec qz33 qz33 729786 1000 729786 1000 qz36 qz36 rfl rfl rfl) (@List.IsChain.cons_cons RS385to396.d1 RS385to396.d64 (RS385to396.d2 qz33 qz60 qz262) (RS385to396.d2 qz60 qz78 qz266) (@List.cons RS385to396.d1 (RS385to396.d2 qz78 qz96 qz270) (@List.cons RS385to396.d1 qz306 Ns384p1757)) (@Enclosure.dec_le_dec qz60 qz60 731107 1000 731107 1000 qz63 qz63 rfl rfl rfl) (@List.IsChain.cons_cons RS385to396.d1 RS385to396.d64 (RS385to396.d2 qz60 qz78 qz266) (RS385to396.d2 qz78 qz96 qz270) (@List.cons RS385to396.d1 qz306 Ns384p1757) (@Enclosure.dec_le_dec qz78 qz78 732428 1000 732428 1000 qz81 qz81 rfl rfl rfl) (@List.IsChain.cons_cons RS385to396.d1 RS385to396.d64 (RS385to396.d2 qz78 qz96 qz270) qz306 Ns384p1757 (@Enclosure.dec_le_dec qz96 qz96 733748 1000 733748 1000 qz99 qz99 rfl rfl rfl) (Ns384p1758 (@Enclosure.dec_le_dec qz114 qz114 735068 1000 735068 1000 qz117 qz117 rfl rfl rfl) (Ns384p1759 Ns384p1761))))) 

noncomputable abbrev qz574 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz575 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns384p1756 Ns384p1762)

noncomputable abbrev qz576 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns384p1756 Ns384p1762))

theorem RS385to396.d65 : Zeta.Certificates.BatchSpec 12 728464 1000 744291 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz574 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz574 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz574 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz240)))) qz575 (@And.intro (@Eq Nat (@List.length qz574 qz576) 12) (And (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz574 qz576)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz574 qz576)) (@Option.some Real qz240))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz574 qz576)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz574 qz576)) (@Option.some Real qz240)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz240))))

theorem solution : Zeta.Certificates.BatchSpec 12 728464 1000 744291 1000 := RS385to396.d65
#print axioms solution
#check solution
