-- Prove2me | solution 1 for RHHeight1000.rs_main_0325_0336
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:18:11.749402+00:00
-- url     : https://prove2.me/submissions/ca8ed436-ee35-4f35-b62a-230311f5f880

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

noncomputable def RS325to336.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS325to336.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS325to336.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS325to336.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS325to336.d2 a b h 

theorem RS325to336.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS325to336.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS325to336.d3 a b h)) 

noncomputable def Ns324p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns324p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns324p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns324p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns324p0 Ns324p1 Ns324p2 Ns324p1 307286088 268435456 1 77440000 307286088 268435456 1 77440000 153643044 134217728 2 134217728 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns324p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns324p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns324p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns324p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns324p8 := nat_lit 167537954069964697925743468333314178468718661948561187618563575975392713740913527107727581163208035826476740967700482432525301063254420572874757592895482956004842597348203117269212172556829666669574421653274845612596416189641484794702002223261246862056663160605878293700340502480877986491439034432953223334258717026053687371824342493299510132312376251152844516906794910572262907940062760396663270105627554083664899640691826599584783763757814813433640133591539937449421955686657622469485188711283992428713614179785896055117030632677201478317872225272595773536303110412989181984739022579128493081560758017763072115692678596043664844667144619713966763611484179303468167142547433165016751768184247559143333542643815355903304572487929375 

noncomputable def Ns324p9 := nat_lit 17907736863639440849562382641391758203535690054199171304015283257442503423240620144819838407313611418261944516207295868563739563278604805791797182761045687776939279949642059267526948014748996956777332184087524644234759874591635243045607722412471722018588244283882362848653445974523544951031470230725674276297342086185092985546835544820091590454230569790847977790484558207349923322458845585052164126500435851662252152223728079705692133047658564669873831757357628115566356048471439549797170528303905720944834637690907185213991407615774042056720704508980680095051114888612186461088301140868302968264130481206655302741383410655080008578156649725227045954510069588220729495895148666460653631514375880874422615237249871322129146554264800 

noncomputable def Ns324p10 := nat_lit 55164646516618494962085419356369025784335016154267579706247610053041231157772817011486486467101704279863254798704146668052276438579475100451766223896220272709675360577301802978530276301158911649961092601279696986330335403118086533522541958716560166657634553390183479955483588238249446822384543398154260439705049143284278540285021213103458182619368483938376641172730818250587232036579805400979202432024046862170503602539341971086573372247299262086029843105216008583038025403798224342134620653974939981235680083776396058604459065501719125356177784467570909658245422960948263734871602033841948787585406240093531041217463298165642337705122589129757920995868559518021463265498464182174549661735402095023640043996665674913376875 

noncomputable def Ns324p11 := BSN.log_dyadic_bound Ns324p6 Ns324p7 15 14 Ns324p8 268435456 77440000 Ns324p9 Ns324p10 307286088 Ns324p4 Ns324p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns324p6) (BSN.artanhQ Ns324p7) 0 14 Ns324p9 Ns324p8 Ns324p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns324p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns324p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns324p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns324p15 := nat_lit 167537954069966963268140139327979112712430526945422964221951926912223381190141639739514890494967825643602350173964944759828460064784215684919760383437959917620844610857567326816719640593037578236900835917107172977527392439886629774248115214831425484905681376157923696414882114961796820014026232307332015059110330001516939277521159573995394989771587717775443426002499543257897301982481613760098955890450106043861450716722534643739571053080256776912576113428445260435254713579381797931690799491102381747484553243404562568585572234105168360737285205910186933811836504830286397217473365026331067977496463917110493303316865058355012304571237619413071097245713770677768486493924969821719264401216877841676972336093778875903304572487929375 

noncomputable def Ns324p16 := nat_lit 17907736863639702486765313263906285882628955290251965205176678923530777959693011244026517850256414903756943142851250712732214241881959351517241344993825585048584379523049477943740273636414656012170312373198803997844271825165684859407921203335666024680974464565759223251918458072775203410604089667122984485578465112081892102496937045858735135721609691262763214794451343726045584198128451069547586972080574568545086657023793200560105564573365716615162566961587407171758966967827997201380802107846920231945878242774600967607639551032178207663699700360114112068650063802902647517702890145150192721997537569966984346993833704449560383184487996362781528900358997452380059737141488304159449328022742959995775545894292303322129146554264800 

noncomputable def Ns324p17 := nat_lit 55164646516619937449385584700664297411818070214438189962773666351465523500358685366424500506990751111492356556545320273548942244833046464529601272738875466881799996765940232256588350019911833156887888425998391295014189841212513610526066550079316346993943774342801096070086869790972589246312728227659319758310961510342377923950694747797317942483020440897997204711883064182772445608288320382376665481938194224815739627075458138172195220395246294556718284728034954178416253903237031389214179719385823921869528509431462690683227358218086518156757026652846493301460983550768858152506145788622699720737745394141184245149692548799188169247529408201840608223422296381897323845616153036586108326210125693898345963996665674913376875 

noncomputable def Ns324p18 := BSN.log_dyadic_bound Ns324p13 Ns324p14 15 14 Ns324p15 268435456 77440000 Ns324p16 Ns324p17 307286088 Ns324p12 Ns324p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns324p13) (BSN.artanhQ Ns324p14) 0 14 Ns324p16 Ns324p15 Ns324p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns324p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 153643044 134217728 2 134217728 38410761 33554432 1 67108864 (Ns324p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns324p0 Ns324p1 307286088 268435456 1 77440000 Bool.false (BSN.logfrac_isNear Ns324p4 Ns324p5 1 Ns324p0 Ns324p1 307286088 268435456 77440000 rfl rfl rfl (Ns324p11 rfl))) (BSN.isNear_log_sfrac Ns324p2 Ns324p1 307286088 268435456 1 77440000 Bool.false (BSN.logfrac_isNear Ns324p12 Ns324p5 1 Ns324p2 Ns324p1 307286088 268435456 77440000 rfl rfl rfl (Ns324p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS325to336.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 67108864 := Ns324p19 

noncomputable def Ns324p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 16777216 4840000 385100712855 135135 11629079 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz577 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz316 := qz577

noncomputable abbrev qz0 := qz316

theorem RS325to336.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 11629079 16777216 1 4840000 := BSN.isNear_log_sfrac 2 1 11629079 16777216 1 4840000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 11629079 16777216 4840000 rfl rfl rfl (Ns324p20 rfl)) 

theorem RS325to336.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 186065264 268435456 56 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 11629079 16777216 1 4840000 186065264 268435456 56 268435456 RS325to336.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz578 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz319 := qz578

noncomputable def Ns324p21 := @Enclosure.Real.IsNear.inv_image qz317 47453133 33554432 1 33554432 11863282 11863284 16777216 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 47453133 33554432 1 33554432 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 47453133 33554432 1 33554432 47453133 33554432 1 33554432 (BSN.sqrt_enclosure 2 1 23726566 23726567 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS325to336.d8 : Enclosure.Real.IsNear qz320 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 23726566 33554432 2 33554432 11863283 16777216 1 16777216 (Ns324p21 rfl rfl) rfl 

theorem RS325to336.d9 : Enclosure.Real.IsNear qz320 Bool.false 189812528 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 189812528 268435456 16 268435456 RS325to336.d8 rfl 

noncomputable def Ns324p22 := BSN.log_dyadic_bound 1 2 13 12 132638213186519040000 16777216 4840000 13079757671720842725 316234143225 18431655 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS325to336.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 18431655 16777216 1 4840000 := BSN.isNear_log_sfrac 3 1 18431655 16777216 1 4840000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 18431655 16777216 4840000 rfl rfl rfl (Ns324p22 rfl)) 

theorem RS325to336.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 294906480 268435456 56 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 18431655 16777216 1 4840000 294906480 268435456 56 268435456 RS325to336.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns324p23 := @Enclosure.Real.IsNear.inv_image qz321 58117981 33554432 1 33554432 9686330 9686331 16777216 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 58117981 33554432 1 33554432 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 58117981 33554432 1 33554432 58117981 33554432 1 33554432 (BSN.sqrt_enclosure 3 1 29058990 29058991 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS325to336.d12 : Enclosure.Real.IsNear qz323 Bool.false 19372661 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 19372661 33554432 1 33554432 19372661 33554432 1 33554432 (Ns324p23 rfl rfl) rfl 

theorem RS325to336.d13 : Enclosure.Real.IsNear qz323 Bool.false 154981288 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 19372661 33554432 1 33554432 154981288 268435456 8 268435456 RS325to336.d12 rfl 

noncomputable def Ns324p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns324p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns324p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns324p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns324p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns324p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns324p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns324p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns324p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns324p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns324p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns324p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns324p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns324p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns324p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns324p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns324p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns324p25 Ns324p26 Ns324p27 Ns324p28 200200021673987500790625 Ns324p29 Ns324p30 Ns324p31 Ns324p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns324p32 Ns324p33 151412625 Ns324p34 Ns324p35 1322214852783825 Ns324p27 Ns324p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns324p32 Ns324p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns324p34 Ns324p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns324p36 Ns324p37 1267389585 Ns324p38 Ns324p39 1927077560082675 Ns324p29 Ns324p30 Ns324p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns324p36 Ns324p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns324p38 Ns324p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS325to336.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns324p24 Ns324p25 1 Ns324p26 := Ns324p40 rfl rfl rfl 

noncomputable def Ns324p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns324p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns324p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns324p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns324p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns324p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns324p25 Ns324p26 Ns324p42 Ns324p43 9945 Ns324p44 Ns324p45 65835 Ns324p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns324p42 Ns324p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns324p44 Ns324p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS325to336.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns324p41 Ns324p25 1 Ns324p26 := Ns324p46 rfl 

noncomputable def Ns324p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns324p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS325to336.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns324p47 Ns324p25 1 Ns324p48 := BSN.pi_combine Ns324p24 Ns324p41 Ns324p25 Ns324p26 Ns324p48 Ns324p47 rfl rfl rfl rfl RS325to336.d14 RS325to336.d15 

theorem RS325to336.d17 : Enclosure.Real.IsNear Real.pi Bool.false 14148475504056880 4503599627370496 1 4503599627370496 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns324p47 Ns324p25 1 Ns324p48 14148475504056880 4503599627370496 1 4503599627370496 RS325to336.d16 rfl 

noncomputable def Ns324p49 := nat_lit 147443727375074537121690809726715087890625 

noncomputable def Ns324p50 := nat_lit 22889945643899497138335355216896171420000 

noncomputable def Ns324p51 := nat_lit 355592320898650075318906513310625 

noncomputable def Ns324p52 := BSN.log_dyadic_bound 3 5 17 16 Ns324p49 16777216 4840000 Ns324p50 Ns324p51 23258159 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 3) (BSN.artanhQ 5) 0 16 Ns324p50 Ns324p49 Ns324p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS325to336.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 23258159 16777216 1 4840000 := BSN.isNear_log_sfrac 4 1 23258159 16777216 1 4840000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 23258159 16777216 4840000 rfl rfl rfl (Ns324p52 rfl)) 

theorem RS325to336.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 372130544 268435456 56 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 23258159 16777216 1 4840000 372130544 268435456 56 268435456 RS325to336.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns324p53 := @Enclosure.Real.IsNear.inv_image qz325 67108865 33554432 1 33554432 8388607 8388608 16777216 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 67108865 33554432 1 33554432 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 67108865 33554432 1 33554432 67108865 33554432 1 33554432 (BSN.sqrt_enclosure 4 1 33554432 33554433 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS325to336.d20 : Enclosure.Real.IsNear qz327 Bool.false 16777215 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 16777215 33554432 1 33554432 16777215 33554432 1 33554432 (Ns324p53 rfl rfl) rfl 

theorem RS325to336.d21 : Enclosure.Real.IsNear qz327 Bool.false 134217720 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 16777215 33554432 1 33554432 134217720 268435456 8 268435456 RS325to336.d20 rfl 

noncomputable def Ns324p54 := nat_lit 61697213297292266380244507781205789317049021875 

noncomputable def Ns324p55 := nat_lit 12776162289178456695994184080609776001208236500 

noncomputable def Ns324p56 := nat_lit 57671893776295590731569354191667200000 

noncomputable def Ns324p57 := nat_lit 885951608314392539099884620 

noncomputable def Ns324p58 := nat_lit 1286943652057122751813246125 

noncomputable def Ns324p59 := BSN.log_dyadic_bound 2 3 22 21 Ns324p54 16777216 4840000 Ns324p55 Ns324p56 27001887 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 21 10 9927050056596826020 47940881637414340575 686533194547200 Ns324p57 Ns324p58 84004523356416638976000 Ns324p55 Ns324p54 Ns324p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 10 21 Ns324p57 Ns324p58 84004523356416638976000 rfl rfl rfl rfl)) rfl rfl 

theorem RS325to336.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 4840000 := BSN.isNear_log_sfrac 5 1 27001887 16777216 1 4840000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 27001887 16777216 4840000 rfl rfl rfl (Ns324p59 rfl rfl)) 

theorem RS325to336.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 432030192 268435456 56 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 4840000 432030192 268435456 56 268435456 RS325to336.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns324p60 := @Enclosure.Real.IsNear.inv_image qz328 75029991 33554432 1 33554432 7502998 7503000 16777216 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 75029991 33554432 1 33554432 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 75029991 33554432 1 33554432 75029991 33554432 1 33554432 (BSN.sqrt_enclosure 5 1 37514995 37514996 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS325to336.d24 : Enclosure.Real.IsNear qz329 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 15005998 33554432 2 33554432 7502999 16777216 1 16777216 (Ns324p60 rfl rfl) rfl 

theorem RS325to336.d25 : Enclosure.Real.IsNear qz329 Bool.false 120047984 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 120047984 268435456 16 268435456 RS325to336.d24 rfl 

noncomputable def Ns324p61 := BSN.log_dyadic_bound 2 10 5 4 94500000000 16777216 4840000 1291130880 26880 6802575 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz578)

theorem RS325to336.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 12500000121 60500000000000000 := BSN.isNear_log_sfrac 6 1 4034683545132279 2251799813685248 12500000121 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 1083052117253279893684224 604462909807314587353088 1000000009680000 4840000000000000000000 4034683545132279 2251799813685248 12500000121 60500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 6802575 16777216 24973259072661432 36028797018963968 4840000 1000000000000000 rfl rfl rfl rfl (Ns324p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS325to336.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 480971758 268435456 57 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 12500000121 60500000000000000 480971758 268435456 57 268435456 RS325to336.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns324p62 := @Enclosure.Real.IsNear.inv_image qz331 82191237 33554432 1 33554432 6849269 6849270 16777216 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 82191237 33554432 1 33554432 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 82191237 33554432 1 33554432 82191237 33554432 1 33554432 (BSN.sqrt_enclosure 6 1 41095618 41095619 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS325to336.d28 : Enclosure.Real.IsNear qz332 Bool.false 13698539 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 13698539 33554432 1 33554432 13698539 33554432 1 33554432 (Ns324p62 rfl rfl) rfl 

theorem RS325to336.d29 : Enclosure.Real.IsNear qz332 Bool.false 109588312 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 13698539 33554432 1 33554432 109588312 268435456 8 268435456 RS325to336.d28 rfl 

noncomputable def Ns324p63 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 16777216 4840000 11010900719820672 5524329195 9388794 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz578)

theorem RS325to336.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 12500000121 60500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 12500000121 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 1176230476650867868041216 604462909807314587353088 1000000009680000 4840000000000000000000 4381799983422711 2251799813685248 12500000121 60500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 9388794 16777216 24973259072661432 36028797018963968 4840000 1000000000000000 rfl rfl rfl rfl (Ns324p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS325to336.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 522351262 268435456 57 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 12500000121 60500000000000000 522351262 268435456 57 268435456 RS325to336.d30 rfl 

noncomputable abbrev qz334 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns324p64 := @Enclosure.Real.IsNear.inv_image qz334 88776683 33554432 1 33554432 6341191 6341192 16777216 (@Enclosure.Real.IsNear.of_eq qz334 (Real.sqrt qz333) Bool.false 88776683 33554432 1 33554432 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 88776683 33554432 1 33554432 88776683 33554432 1 33554432 (BSN.sqrt_enclosure 7 1 44388341 44388342 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS325to336.d32 : Enclosure.Real.IsNear qz335 Bool.false 12682383 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 12682383 33554432 1 33554432 12682383 33554432 1 33554432 (Ns324p64 rfl rfl) rfl 

theorem RS325to336.d33 : Enclosure.Real.IsNear qz335 Bool.false 101459064 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 12682383 33554432 1 33554432 101459064 268435456 8 268435456 RS325to336.d32 rfl 

noncomputable def Ns324p65 := nat_lit 1256945285058001618599936 

noncomputable def Ns324p66 := BSN.log_dyadic_bound 0 16 1 0 1 16777216 4840000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz578)

theorem RS325to336.d34 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 25000000363 121000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 25000000363 121000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false Ns324p65 604462909807314587353088 1000000014520000 4840000000000000000000 9364972152248037 4503599627370496 25000000363 121000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 16777216 24973259072661432 36028797018963968 4840000 1000000000000000 rfl rfl rfl rfl (Ns324p66 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS325to336.d35 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 558195838 268435456 56 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 25000000363 121000000000000000 558195838 268435456 56 268435456 RS325to336.d34 rfl 

noncomputable abbrev qz337 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns324p67 := @Enclosure.Real.IsNear.inv_image qz337 94906265 33554432 1 33554432 5931641 5931642 16777216 (@Enclosure.Real.IsNear.of_eq qz337 (Real.sqrt qz336) Bool.false 94906265 33554432 1 33554432 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 94906265 33554432 1 33554432 94906265 33554432 1 33554432 (BSN.sqrt_enclosure 8 1 47453132 47453133 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz338 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS325to336.d36 : Enclosure.Real.IsNear qz338 Bool.false 11863283 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 11863283 33554432 1 33554432 11863283 33554432 1 33554432 (Ns324p67 rfl rfl) rfl 

theorem RS325to336.d37 : Enclosure.Real.IsNear qz338 Bool.false 94906264 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 11863283 33554432 1 33554432 94906264 268435456 8 268435456 RS325to336.d36 rfl 

noncomputable def Ns324p68 := nat_lit 1328140746012062765809664 

noncomputable def Ns324p69 := BSN.log_dyadic_bound 1 17 3 2 1252815 16777216 4840000 1448 3 1976071 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz578)

theorem RS325to336.d38 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 25000000363 121000000000000000 := BSN.isNear_log_sfrac 9 1 9895419672221413 4503599627370496 25000000363 121000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false Ns324p68 604462909807314587353088 1000000014520000 4840000000000000000000 9895419672221413 4503599627370496 25000000363 121000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 1976071 16777216 24973259072661432 36028797018963968 4840000 1000000000000000 rfl rfl rfl rfl (Ns324p69 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS325to336.d39 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 589812974 268435456 56 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 25000000363 121000000000000000 589812974 268435456 56 268435456 RS325to336.d38 rfl 

noncomputable abbrev qz340 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns324p70 := @Enclosure.Real.IsNear.inv_image qz340 100663297 33554432 1 33554432 5592405 5592406 16777216 (@Enclosure.Real.IsNear.of_eq qz340 (Real.sqrt qz339) Bool.false 100663297 33554432 1 33554432 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 100663297 33554432 1 33554432 100663297 33554432 1 33554432 (BSN.sqrt_enclosure 9 1 50331648 50331649 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz341 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS325to336.d40 : Enclosure.Real.IsNear qz341 Bool.false 11184811 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 11184811 33554432 1 33554432 11184811 33554432 1 33554432 (Ns324p70 rfl rfl) rfl 

theorem RS325to336.d41 : Enclosure.Real.IsNear qz341 Bool.false 89478488 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 11184811 33554432 1 33554432 89478488 268435456 8 268435456 RS325to336.d40 rfl 

noncomputable def Ns324p71 := nat_lit 1391827265235416537628672 

noncomputable def Ns324p72 := BSN.log_dyadic_bound 2 18 4 3 3571283520 16777216 4840000 14806464 960 3743727 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 18) 0 3 14806464 3571283520 960 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz722 := (Enclosure.sfrac Bool.false 10 1)

noncomputable abbrev qz579 := qz722

noncomputable abbrev qz342 := qz579

noncomputable abbrev qz1 := qz342

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10) qz578)

theorem RS325to336.d42 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 10369921216632549 4503599627370496 25000000363 121000000000000000 := BSN.isNear_log_sfrac 10 1 10369921216632549 4503599627370496 25000000363 121000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false Ns324p71 604462909807314587353088 1000000014520000 4840000000000000000000 10369921216632549 4503599627370496 25000000363 121000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 3743727 16777216 24973259072661432 36028797018963968 4840000 1000000000000000 rfl rfl rfl rfl (Ns324p72 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS325to336.d43 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 618095470 268435456 56 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 10369921216632549 4503599627370496 25000000363 121000000000000000 618095470 268435456 56 268435456 RS325to336.d42 rfl 

noncomputable abbrev qz344 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10))

noncomputable def Ns324p73 := @Enclosure.Real.IsNear.inv_image qz344 106108431 33554432 1 33554432 5305421 5305422 16777216 (@Enclosure.Real.IsNear.of_eq qz344 (Real.sqrt qz343) Bool.false 106108431 33554432 1 33554432 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz343) Bool.false 106108431 33554432 1 33554432 106108431 33554432 1 33554432 (BSN.sqrt_enclosure 10 1 53054215 53054216 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz345 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

theorem RS325to336.d44 : Enclosure.Real.IsNear qz345 Bool.false 10610843 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz345 Bool.false 10610843 33554432 1 33554432 10610843 33554432 1 33554432 (Ns324p73 rfl rfl) rfl 

theorem RS325to336.d45 : Enclosure.Real.IsNear qz345 Bool.false 84886744 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz345 Bool.false 10610843 33554432 1 33554432 84886744 268435456 8 268435456 RS325to336.d44 rfl 

theorem RS325to336.d46 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz723 := (@instHMul Real Real.instMul)

noncomputable abbrev qz580 := (@HMul.hMul Real Real Real qz723 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz346 := qz580

noncomputable abbrev qz2 := qz346

theorem RS325to336.d47 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS325to336.d46 rfl 

noncomputable abbrev qz347 := (@Inv.inv Real Real.instInv qz580)

noncomputable abbrev qz3 := qz347

theorem RS325to336.d48 : Enclosure.Real.IsNear qz3 Bool.false 5340353 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 5340353 33554432 1 33554432 5340353 33554432 1 33554432 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 2670176 2670177 16777216 RS325to336.d47 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns324p74 := nat_lit 357128965267016919285760000 

noncomputable def Ns324p75 := nat_lit 32923962438163438401207926784 

noncomputable abbrev qz724 := (Enclosure.sfrac Bool.false 648182 1000)

noncomputable abbrev qz581 := qz724

noncomputable abbrev qz348 := qz581

noncomputable abbrev qz4 := qz348

noncomputable abbrev qz582 := qz723

noncomputable abbrev qz349 := qz582

noncomputable abbrev qz5 := qz349

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 10)

noncomputable abbrev qz725 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 648182 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz583 := qz725

noncomputable abbrev qz350 := qz583

noncomputable abbrev qz351 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz584 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz7 := (@HPow.hPow Real Real Real qz584 qz350 qz351)

noncomputable abbrev qz726 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 648182 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz585 := qz726

noncomputable abbrev qz352 := qz585

noncomputable abbrev qz8 := qz352

noncomputable def Ns324p76 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8)) 42806457 67108864 158855 134217728 114075693708112095975 590295810358705651712 2512409871525971108121 Ns324p74 Ns324p75 

noncomputable def Ns324p77 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos BSN.quadSignPos 9 10 648182 1000 200 268435456 134217728 4503599627370496 Bool.false 316243176965 2434 618095470 56 84886744 8 

noncomputable def Ns324p78 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 648182 1000 108 156 268435456 134217728 4503599627370496 Bool.false 316243176965 2434 

noncomputable def Ns324p79 := Ns324p78 558195838 56 94906264 8 589812974 56 89478488 8 Bool.true 306202484 119972 Bool.true 30315448 Bool.true 284417338 14148475504056880 1 Bool.false 266725454 Bool.false Bool.false 131338972 Bool.false Bool.true 168121139 

noncomputable def Ns324p80 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 648182 1000 10 52 268435456 134217728 4503599627370496 Bool.false 316243176965 2434 

noncomputable def Ns324p81 := Ns324p80 480971758 57 109588312 8 522351262 57 101459064 8 Bool.true 251972445 88991 Bool.false 269366638 Bool.true 409322470 14148475504056880 1 Bool.false 144251862 Bool.true Bool.false 12330617 Bool.false Bool.true 306202484 

noncomputable def Ns324p82 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 648182 1000 177 85 268435456 134217728 4503599627370496 Bool.false 316243176965 2434 

noncomputable def Ns324p83 := Ns324p82 372130544 56 134217720 8 432030192 56 120047984 16 Bool.true 466598 52275 Bool.false 401491890 Bool.false 368101651 14148475504056880 1 Bool.false 267678369 Bool.true Bool.false 263110675 Bool.true Bool.true 251972445 

noncomputable def Ns324p84 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 648182 1000 463 296 268435456 134217728 4503599627370496 Bool.false 316243176965 2434 

noncomputable def Ns324p85 := Ns324p84 186065264 56 189812528 16 294906480 56 154981288 8 Bool.true 268435432 2496 Bool.false 411632727 Bool.false 279506178 14148475504056880 1 Bool.false 268248291 Bool.false Bool.false 135599918 Bool.false Bool.true 466598 

noncomputable def Ns324p86 := nat_lit 6916656102662590232776852690040425850539347533031657523 

noncomputable def Ns324p87 := nat_lit 5871038081300061117205361487463311565426029232128000 

noncomputable def Ns324p88 := nat_lit 54919518963247592564295164687360000 

noncomputable def Ns324p89 := nat_lit 213587121153980155839430571630630277120 

noncomputable abbrev qz353 := (@Eq.refl Real qz581)

noncomputable abbrev qz9 := qz353

noncomputable def Ns324p90 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 648182 1000 1680560620496 16000000 1296364 4000 2000 Ns324p88 Ns324p89 qz9 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns324p91 := nat_lit 141653116982529847967269943092027921419045837476488346071040 

noncomputable abbrev qz727 := (@instHSub Real Real.instSub)

noncomputable abbrev qz586 := qz727

noncomputable abbrev qz354 := qz586

noncomputable abbrev qz587 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz728 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz729 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz588 := (@HSub.hSub Real Real Real qz727 qz728 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz729 (@Nat.cast Real Real.instNatCast 1296364))))

noncomputable abbrev qz355 := (@HSub.hSub Real Real Real qz586 (@HMul.hMul Real Real Real qz582 (Enclosure.sfrac Bool.false 648182 4000) (Real.log (Enclosure.sfrac Bool.false 1680560620496 16000000))) (@HMul.hMul Real Real Real qz582 qz587 qz588))

noncomputable abbrev qz589 := (Enclosure.sfrac Bool.false 648182 2000)

noncomputable abbrev qz10 := (@HSub.hSub Real Real Real qz354 (@HSub.hSub Real Real Real qz354 qz355 qz589) (@HMul.hMul Real Real Real qz349 qz589 (Real.log Real.pi)))

noncomputable def Ns324p92 := @Enclosure.Real.IsNear.addLit_ft_p qz10 (Enclosure.sfrac Bool.true Ns324p88 Ns324p89) 663210155809672096767 562949953421312000 2246639004394950599 247808000000000000000000 Ns324p88 Ns324p89 0 1 Ns324p91 

noncomputable def Ns324p93 := nat_lit 22253640074825047313265721344000 

noncomputable abbrev qz11 := (@HSub.hSub Real Real Real qz354 qz355 qz589)

noncomputable def Ns324p94 := @Enclosure.Real.IsNear.subLit_ff_p qz11 (@HMul.hMul Real Real Real qz5 qz589 (Real.log Real.pi)) 872062703965293865983 562949953421312000 512642501235213 121000000000000000000 12448581943251 33554432000 324091 67108864000 Ns324p93 663210155809672096767 562949953421312000 

noncomputable abbrev qz12 := qz355

noncomputable def Ns324p95 := @Enclosure.Real.IsNear.subLit_ff_p qz12 qz589 8436077738556482347 4503599627370496 512642501235213 121000000000000000000 648182 2000 0 1 13953003263444701855728 872062703965293865983 562949953421312000 512642501235213 121000000000000000000 

noncomputable def Ns324p96 := nat_lit 18996358279915755237102753526317056 

noncomputable def Ns324p97 := nat_lit 55910639555821829095424000 

noncomputable def Ns324p98 := nat_lit 4835703278458516698824704 

noncomputable def Ns324p99 := nat_lit 23071252366023028150077706495659788022231515172676369550511949555762554581237712579157128389914695877584227831553021538263338004702651488208559875985244160 

noncomputable def Ns324p100 := nat_lit 426193070476198540923843427017251370432672788982677427097903382536894818573153952061341633906918842680784801240202349623650823686011762451821486042775552 

noncomputable def Ns324p101 := nat_lit 42199043833735288077343725297738578619755076652184639852018696320360732818797297662731335835866503815118745142452955632232779827053479053303480320 

noncomputable def Ns324p102 := BSN.log_dyadic_bound 631984620496 2729136620496 7 6 Ns324p99 134217728 38720000 Ns324p100 Ns324p101 63309748 3361121240992 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 631984620496) (BSN.artanhQ 2729136620496) 0 6 Ns324p100 Ns324p99 Ns324p101 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz356 := (Real.log (Enclosure.sfrac Bool.false 1680560620496 16000000))

noncomputable abbrev qz357 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns324p103 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 648182 4000) qz356 648182 4000 0 1 3254427548720375 281474976710656 195312621 7562500000000000 8437845429538680433 4503599627370496 63299062652511 15125000000000000000 (Enclosure.Real.IsNear.const Bool.false 648182 4000) (BSN.isNear_log_sfrac 1680560620496 16000000 3254427548720375 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1680560620496) qz357)) Bool.false Ns324p97 Ns324p98 1000000619520000 38720000000000000000000 3254427548720375 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1680560620496 16000000 16 3361121240992 2097152000000 63309748 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns324p102 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns324p104 := BSN.arctan_dyadic_bound_f 1000 1296364 1 0 16777216 4840000 0 1 1 0 1 1 12941 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1296364) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1296364) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz590 := qz728

noncomputable abbrev qz358 := qz590

noncomputable abbrev qz13 := qz358

noncomputable abbrev qz591 := qz729

noncomputable abbrev qz359 := qz591

noncomputable abbrev qz14 := qz359

noncomputable abbrev qz730 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz592 := qz730

noncomputable abbrev qz360 := qz592

noncomputable abbrev qz15 := (@Enclosure.Real.IsNear.mulLit_ff qz360 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz361 := (@Nat.cast Real Real.instNatCast 1296364)

noncomputable def Ns324p105 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz361)) 884279719003555 562949953421312 1 2000000000000000 12941 16777216 1 4840000 14828466714794721804288 883845491099043 562949953421312 50000000121 242000000000000000 qz15 (Ns324p104 rfl) rfl rfl 

noncomputable abbrev qz362 := (@HMul.hMul Real Real Real qz582 qz587 qz588)

noncomputable abbrev qz16 := qz362

noncomputable abbrev qz363 := qz587

noncomputable abbrev qz17 := qz363

noncomputable abbrev qz364 := qz588

noncomputable abbrev qz18 := qz364

noncomputable abbrev qz365 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns324p106 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 648182 4000) qz356) qz16 8437845429538680433 4503599627370496 63299062652511 15125000000000000000 883845491099043 2251799813685248 50000000121 968000000000000000 Ns324p96 8436077738556482347 4503599627370496 512642501235213 121000000000000000000 (Ns324p103 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz18 1 4 0 1 883845491099043 562949953421312 50000000121 242000000000000000 883845491099043 2251799813685248 50000000121 968000000000000000 qz365 Ns324p105 rfl) 

noncomputable def Ns324p107 := @Ns324p92 Ns324p86 Ns324p87 2246639004394950599 247808000000000000000000 (@Ns324p94 2246639004394950599 247808000000000000000000 (Ns324p95 (Ns324p106 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 648182 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz589 (Real.log Real.pi) 648182 2000 0 1 38410761 33554432 1 67108864 12448581943251 33554432000 324091 67108864000 (Enclosure.Real.IsNear.const Bool.false 648182 2000) RS325to336.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns324p88 Ns324p89) 

noncomputable abbrev qz366 := (@instHAdd Real Real.instAdd)

noncomputable def Ns324p108 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns324p86 Ns324p87 2246639004394950599 247808000000000000000000 617662455 524288 305 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz366 qz10 (Enclosure.sfrac Bool.true Ns324p88 Ns324p89)) Bool.false Ns324p86 Ns324p87 2246639004394950599 247808000000000000000000 Ns324p90 (Ns324p107 rfl rfl)) 

noncomputable def Ns324p109 := nat_lit 3514366258950758600328217977074506129388040573259970716052992607994404169597913026617147921543340685969785547097824551925217420552276279296 

noncomputable def Ns324p110 := nat_lit 69061887427279807374175457422696049589758900585025510522285359577850094671315332446731519433112496475662717985575392155893264493730122956800 

noncomputable def Ns324p111 := nat_lit 2510172954607598128906477023992340374491972783784746672191216661469676589389643998104114567787067656988471819068282071440710273335296 

noncomputable def Ns324p112 := nat_lit 17549974245022709694517761789970315877485601815566038963649774107729315517226419724627413141450636567239549638617410463073165633640470675456 

noncomputable def Ns324p113 := nat_lit 2417166059954793258096141009794361735641561520475892868279987585224753313496036635635603180158937376648195129495138725456264257280554303488000 

noncomputable abbrev qz593 := (BSN.sinEvenQ 68719476736)

noncomputable abbrev qz594 := (BSN.sinOddQ 68719476736)

noncomputable def Ns324p114 := BSN.sin_dyadic_bound_f 107971376264 68719476736 4 3 33554432 9689454 Ns324p109 Ns324p110 Ns324p111 Ns324p112 Ns324p113 Ns324p111 33554429 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107971376264) qz593 0 3 Ns324p109 Ns324p110 Ns324p111 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107971376264) qz594 0 3 Ns324p112 Ns324p113 Ns324p111 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p115 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 617662455) (@Nat.cast Real Real.instNatCast 524288)) Bool.false 617662455 524288 305 33554432 Bool.true 33554429 33554432 1 4840000 (Ns324p108 rfl) (Enclosure.sfrac_false_div 617662455 524288) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 617662455) (@Nat.cast Real Real.instNatCast 524288)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 118715783669317684428800) (@Nat.cast Real Real.instNatCast 75557863725914323419136)) 226375608064910080 72057594037927936 Bool.false 33554429 33554432 187 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q1 617662455 524288 226375608064910080 72057594037927936 187 118715783669317684428800 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554429 33554432 118715783669317684428800 75557863725914323419136 107971376264 68719476736 9689454 9680000 (Ns324p114 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns324p116 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns324p86 Ns324p87 2246639004394950599 247808000000000000000000 316243176965 268435456 2434 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz366 qz10 (Enclosure.sfrac Bool.true Ns324p88 Ns324p89)) Bool.false Ns324p86 Ns324p87 2246639004394950599 247808000000000000000000 Ns324p90 (Ns324p107 rfl rfl)) 

noncomputable def Ns324p117 := Ns324p85 52275 BSN.abs_quadSignPos (BSN.cos_quad_nat3 463 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268248291 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 296 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 135599918 268435456) qz9 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 33554429 33554432 23589913 2537553920000 268435432 268435456 2496 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 33554429 33554432 23589913 2537553920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 33554429 33554432 1509754432 162403450880000 33554429 33554432 23589913 2537553920000 (Ns324p115 rfl rfl) rfl)) rfl) (Ns324p116 rfl) RS325to336.d7 

noncomputable def Ns324p118 := nat_lit 40239384361690401974407562195873490075067102865036530712705206772587197046055395334643394955182440974587879521 

noncomputable def Ns324p119 := nat_lit 871683568514489007341798292243696146469029465094156570908284878217177001794361422139649254553384847460322508800 

noncomputable def Ns324p120 := nat_lit 23665667276035477147146221254497261679831580635396565882728181861979685988065743000235565492623893684321 

noncomputable def Ns324p121 := nat_lit 200969818603812372817232539922514106911233574116212464706869902990496703886413012362881284359613943952392413281 

noncomputable def Ns324p122 := nat_lit 30508924898007115256962940228529365126416031278295479981789970737601195062802649774887723909368469661111287808000 

noncomputable abbrev qz367 := (BSN.sinEvenQ 268435456)

noncomputable abbrev qz368 := (BSN.sinOddQ 268435456)

noncomputable def Ns324p123 := BSN.sin_dyadic_bound_f 411632727 268435456 4 3 268435456 134217728 Ns324p118 Ns324p119 Ns324p120 Ns324p121 Ns324p122 Ns324p120 268248291 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 411632727) qz367 0 3 Ns324p118 Ns324p119 Ns324p120 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 411632727) qz368 0 3 Ns324p121 Ns324p122 Ns324p120 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p124 := nat_lit 3286352818274038400511378797870783655173926193035283242546442164257331628791425863468751321414515986635165696 

noncomputable def Ns324p125 := nat_lit 67052582193422231333984484018745857420694574238012043916021913709013615522643186318434558042568065189255577600 

noncomputable def Ns324p126 := nat_lit 227351037214143778548705768311528703668784545366235021184845514082684434426732645056550909726341206016 

noncomputable def Ns324p127 := nat_lit 19927912727670031880223812082357090861669349732692077147579718942879759100369318789246278234622719197733457920 

noncomputable def Ns324p128 := nat_lit 6101784979601423051392588045705873025283206255659095996357994147520239012560529954977544781873693932222257561600 

noncomputable abbrev qz369 := (BSN.cosEvenQ 268435456)

noncomputable abbrev qz370 := (BSN.cosOddQ 268435456)

noncomputable def Ns324p129 := BSN.cos_dyadic_bound_f 279506178 268435456 4 3 268435456 134217728 Ns324p124 Ns324p125 Ns324p126 Ns324p127 Ns324p128 Ns324p126 135599918 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 279506178) qz369 0 3 Ns324p124 Ns324p125 Ns324p126 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 279506178) qz370 0 3 Ns324p127 Ns324p128 Ns324p126 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p130 := nat_lit 36411915549385549765548741320063966257499785467423256553826376762094176029789784399403860825765358869670400000 

noncomputable def Ns324p131 := nat_lit 17543705372452431723377852665673789530763288272106795278337824672722581972754500652632682321000000000000 

noncomputable def Ns324p132 := nat_lit 181873565679724752527355037571691365503276760978080162197507802550350428020542737871193010129148317644352000000 

noncomputable def Ns324p133 := BSN.sin_dyadic_bound_f 401491890 268435456 4 3 268435456 134217728 Ns324p130 Ns324p119 Ns324p131 Ns324p132 Ns324p122 Ns324p131 267678369 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 401491890) qz367 0 3 Ns324p130 Ns324p119 Ns324p131 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 401491890) qz368 0 3 Ns324p132 Ns324p122 Ns324p131 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p134 := nat_lit 25715607784669109202354175127353059851499469930041797560771712595042007121743284054286941425815115250279255601 

noncomputable def Ns324p135 := nat_lit 6188895990095263308191023785195882306796767434188039072953477962954601355010048091175462720495638154801 

noncomputable def Ns324p136 := nat_lit 128485180576280019152303199705448640216975117849011575710053392439033775942670566458244384253719377026082278961 

noncomputable def Ns324p137 := BSN.sin_dyadic_bound_f 368101651 268435456 4 3 268435456 134217728 Ns324p134 Ns324p119 Ns324p135 Ns324p136 Ns324p122 Ns324p135 263110675 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 368101651) qz367 0 3 Ns324p134 Ns324p119 Ns324p135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 368101651) qz368 0 3 Ns324p136 Ns324p122 Ns324p135 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p138 := Ns324p83 88991 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 177 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267678369 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 85 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 263110675 268435456) qz9 rfl rfl (Ns324p117 RS325to336.d9 RS325to336.d11 RS325to336.d13 RS325to336.d17 (Ns324p123 rfl rfl) (Ns324p129 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns324p116 rfl) RS325to336.d19 RS325to336.d21 RS325to336.d23 RS325to336.d25 RS325to336.d17 (Ns324p133 rfl rfl) (Ns324p137 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns324p139 := nat_lit 2834536358337844951416098682570722173342687699105556669807664287782559281480226104377170789988820684019470336 

noncomputable def Ns324p140 := nat_lit 145923645217675238660554000962831534721927508209476793935644101875028811347184835901184953410840825856 

noncomputable def Ns324p141 := nat_lit 17189271611236980557298464093830909553153013010245640039603400331019395846610463597096219260964944406669824000 

noncomputable def Ns324p142 := BSN.cos_dyadic_bound_f 269366638 268435456 4 3 268435456 134217728 Ns324p139 Ns324p125 Ns324p140 Ns324p141 Ns324p128 Ns324p140 144251862 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 269366638) qz369 0 3 Ns324p139 Ns324p125 Ns324p140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 269366638) qz370 0 3 Ns324p141 Ns324p128 Ns324p140 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p143 := nat_lit 15153155137690625914104343857872113777277652074333031883278649545332947904869700074637449727331743193664000000 

noncomputable def Ns324p144 := nat_lit 22120097343938058272354311245704079967092602408930669927952992224206799269923812464115417441000000000000 

noncomputable def Ns324p145 := nat_lit 91732439955473480877779579819495776561234272556720270938086264099053927148660447085400542936203136332761600000 

noncomputable def Ns324p146 := BSN.cos_dyadic_bound_f 409322470 268435456 4 3 268435456 134217728 Ns324p143 Ns324p125 Ns324p144 Ns324p145 Ns324p128 Ns324p144 12330617 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 409322470) qz369 0 3 Ns324p143 Ns324p125 Ns324p144 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 409322470) qz370 0 3 Ns324p145 Ns324p128 Ns324p144 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p147 := Ns324p81 119972 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 10 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 144251862 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 12330617 268435456) qz9 rfl rfl (Ns324p138 rfl rfl) (Ns324p116 rfl) RS325to336.d27 RS325to336.d29 RS325to336.d31 RS325to336.d33 RS325to336.d17 (Ns324p142 rfl rfl) (Ns324p146 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p148 := nat_lit 844609500812310978907116015616 

noncomputable def Ns324p149 := nat_lit 124615124604835863084731911901282304 

noncomputable def Ns324p150 := nat_lit 1869226869072537946270978678519234560 

noncomputable def Ns324p151 := BSN.cos_dyadic_bound_f 30315448 268435456 2 1 268435456 134217728 Ns324p148 Ns324p149 Ns324p148 Ns324p148 Ns324p150 Ns324p148 266725454 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 30315448) qz369 0 1 Ns324p148 Ns324p149 Ns324p148 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 30315448) qz370 0 1 Ns324p148 Ns324p150 Ns324p148 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p152 := nat_lit 3523665906031653967433441858015568621446300388899670202079929322480456344226043468196182762460705388299227136 

noncomputable def Ns324p153 := nat_lit 280203017571303832111935070898712735572521340513197692097281743070387254216551500178476684301653446656 

noncomputable def Ns324p154 := nat_lit 21366222319447937829761112279598164987609795032987113538932986675091945897572248186555804754289797901558681600 

noncomputable def Ns324p155 := BSN.cos_dyadic_bound_f 284417338 268435456 4 3 268435456 134217728 Ns324p152 Ns324p125 Ns324p153 Ns324p154 Ns324p128 Ns324p153 131338972 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 284417338) qz369 0 3 Ns324p152 Ns324p125 Ns324p153 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 284417338) qz370 0 3 Ns324p154 Ns324p128 Ns324p153 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz595 := (BSN.cos_quad_nat0 156 rfl)

noncomputable def Ns324p156 := Ns324p79 146596 BSN.abs_quadSignPos (BSN.cos_quad_nat0 108 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266725454 268435456) BSN.abs_quadSignPos qz595 (BSN.sfrac_eq_quadSignPos_mul Bool.false 131338972 268435456) qz9 rfl rfl (Ns324p147 rfl) (Ns324p116 rfl) RS325to336.d35 RS325to336.d37 RS325to336.d39 RS325to336.d41 RS325to336.d17 (Ns324p151 rfl rfl) (Ns324p155 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p157 := nat_lit 16460006919050191861105660179121 

noncomputable def Ns324p158 := BSN.cos_dyadic_bound_f 63695317 268435456 2 1 268435456 134217728 Ns324p157 Ns324p149 Ns324p157 Ns324p157 Ns324p150 Ns324p157 260913920 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 63695317) qz369 0 1 Ns324p157 Ns324p149 Ns324p157 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 63695317) qz370 0 1 Ns324p157 Ns324p150 Ns324p157 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz596 := (BSN.cos_quad_nat0 200 rfl)

noncomputable def Ns324p159 := Ns324p77 Bool.true 168121139 146596 Bool.true 63695317 14148475504056880 1 Bool.false 260913920 Bool.false Bool.true 85612914 158855 BSN.abs_quadSignPos qz596 (BSN.sfrac_eq_quadSignPos_mul Bool.false 260913920 268435456) qz9 rfl (Ns324p156 rfl) (Ns324p116 rfl) RS325to336.d43 RS325to336.d45 RS325to336.d17 (Ns324p158 rfl rfl) rfl 

noncomputable def Ns324p160 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) 85612914 268435456 158855 268435456 85612914 268435456 158855 268435456 45963083218157568 42806457 67108864 158855 134217728 (Ns324p159 rfl rfl rfl rfl) 

noncomputable def Ns324p161 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8) 1316075 4194304 1 16777216 86678717936373 140737488355328 474763831976571 21286545113743360000 114075693708112095975 590295810358705651712 

noncomputable def Ns324p162 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz7 1 1 0 1 1316075 4194304 1 16777216 1316075 4194304 1 16777216 

noncomputable abbrev qz19 := qz350

noncomputable abbrev qz20 := (@Enclosure.Real.IsNear.of_eq qz350 (@HMul.hMul Real Real Real qz349 qz348 qz347) Bool.false 1730760344123 16777216000 324091 16777216000 (BSN.t_div_two_pi_mk qz348 648182 1000 qz353) (@Enclosure.Real.IsNear.mulLit_ff qz348 qz347 648182 1000 0 1 5340353 33554432 1 33554432 1730760344123 16777216000 324091 16777216000 (Enclosure.Real.IsNear.const Bool.false 648182 1000) RS325to336.d48 rfl))

noncomputable def Ns324p163 := @Enclosure.Real.IsNear.sqrt_image qz19 1730760344123 16777216000 324091 16777216000 170403446 170403479 16777216 qz20 

noncomputable abbrev qz731 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 648182 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz597 := qz731

noncomputable abbrev qz371 := qz597

noncomputable abbrev qz21 := qz371

noncomputable def Ns324p164 := @Enclosure.Real.IsNear.sqrt_image qz21 340806925 33554432 33 33554432 53468639 53468645 16777216 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 340806925 33554432 33 33554432 340806925 33554432 33 33554432 (Ns324p163 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz598 := (Real.sqrt qz731)

noncomputable abbrev qz372 := qz598

noncomputable abbrev qz22 := qz372

noncomputable def Ns324p165 := @Enclosure.Real.IsNear.inv_image qz22 26734321 8388608 3 16777216 5264299 5264301 16777216 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 106937284 33554432 6 33554432 26734321 8388608 3 16777216 (Ns324p164 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns324p166 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz22) Bool.false 10528600 33554432 2 33554432 1316075 4194304 1 16777216 (Ns324p165 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz23 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz352))

noncomputable abbrev qz599 := (@HMul.hMul Real Real Real qz723 qz726 qz726)

noncomputable abbrev qz600 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz373 := (@HSub.hSub Real Real Real qz586 (@HSub.hSub Real Real Real qz586 qz599 qz585) qz600)

noncomputable abbrev qz24 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz373))

noncomputable def Ns324p167 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz8) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz23) qz24) Bool.false 86678717936373 

noncomputable def Ns324p168 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz23) qz24 60732513 33554432 705 

noncomputable def Ns324p169 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz23) Bool.false 60732513 33554432 705 33554432 60732513 33554432 705 

noncomputable def Ns324p170 := @Enclosure.Real.IsNear.recentre' qz23 Bool.false 9269334 16777216 65017152 10150215680000 4634667 8388608 1015893 158597120000 

noncomputable abbrev qz25 := (@HMul.hMul Real Real Real qz349 qz346 qz352)

noncomputable abbrev qz374 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable def Ns324p171 := @Enclosure.Real.IsNear.cos_image qz25 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16532961) qz374) Bool.false 16532961 16777216 13 2097152 Bool.false 9269334 16777216 1 

noncomputable def Ns324p172 := nat_lit 890540488543658932754108071 

noncomputable def Ns324p173 := nat_lit 144115188075855872000000000000000 

noncomputable def Ns324p174 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz8 884279719003555 140737488355328 1 500000000000000 5262605 33554432 33 33554432 4653614870626703560775 4722366482869645213696 Ns324p172 

noncomputable def Ns324p175 := @Enclosure.Real.IsNear.subLit_ff_p qz21 qz1 340806925 33554432 33 33554432 10 1 0 1 5262605 5262605 33554432 33 

noncomputable abbrev qz375 := (Enclosure.Real.IsNear.const Bool.false 10 1)

noncomputable def Ns324p176 := @Ns324p175 33554432 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 340806925 33554432 33 33554432 340806925 33554432 33 33554432 (Ns324p163 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns324p177 := @Enclosure.Real.IsNear.recentre' qz25 Bool.false 4653614870626703560775 4722366482869645213696 Ns324p172 Ns324p173 16532961 16777216 13 2097152 (@Ns324p174 Ns324p173 RS325to336.d47 (Ns324p176 rfl rfl) rfl) 

noncomputable def Ns324p178 := nat_lit 9950276339398338300341476520809377814339738266765834033340161 

noncomputable def Ns324p179 := nat_lit 253092741970790968397859029543733109897246971520789871559966720 

noncomputable def Ns324p180 := nat_lit 5582196630097780475391401840067488501008411849729030004481 

noncomputable def Ns324p181 := nat_lit 29839664624934819340073646758747998466017197976598044040011521 

noncomputable def Ns324p182 := nat_lit 11389173388685593577903656329467989945376113718435544220198502400 

noncomputable abbrev qz601 := (BSN.cosEvenQ 16777216)

noncomputable def Ns324p183 := BSN.cos_dyadic_bound_f 16532961 16777216 3 2 16777216 4840000 Ns324p178 Ns324p179 Ns324p180 Ns324p181 Ns324p182 Ns324p180 9269334 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 16532961) qz601 0 2 Ns324p178 Ns324p179 Ns324p180 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 16532961) (BSN.cosOddQ 16777216) 0 2 Ns324p181 Ns324p182 Ns324p180 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p184 := @Enclosure.Real.IsNear.inv_image qz23 4634667 8388608 1015893 158597120000 30365904 30366609 16777216 (Ns324p170 (@Ns324p171 4840000 (Ns324p177 rfl) (Enclosure.sfrac_false_div 16532961 16777216) (Ns324p183 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns324p185 := @Enclosure.Real.IsNear.recentre' qz24 Bool.false 5708884 16777216 

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz349 qz346 qz373)

noncomputable def Ns324p186 := @Enclosure.Real.IsNear.cos_image qz26 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 5132091)) (@Nat.cast Real Real.instNatCast 4194304)) Bool.true 5132091 4194304 

noncomputable def Ns324p187 := nat_lit 193884920172455847603697881445 

noncomputable def Ns324p188 := nat_lit 158456325028528675187087900672 

noncomputable def Ns324p189 := nat_lit 39254735309236475475684023026718333 

noncomputable def Ns324p190 := @Enclosure.Real.IsNear.recentre' qz26 Bool.true Ns324p187 Ns324p188 Ns324p189 

noncomputable def Ns324p191 := nat_lit 4835703278458516698824704000000000000000 

noncomputable abbrev qz27 := qz373

noncomputable def Ns324p192 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz27 884279719003555 140737488355328 1 500000000000000 219257454406999 

noncomputable abbrev qz376 := (@HSub.hSub Real Real Real qz586 qz599 qz585)

noncomputable abbrev qz28 := qz376

noncomputable abbrev qz377 := qz600

noncomputable abbrev qz29 := qz377

noncomputable def Ns324p193 := @Enclosure.Real.IsNear.subLit_tf qz28 qz29 148888710229335 1125899906842624 1454629275 1125899906842624 1 16 

noncomputable abbrev qz378 := qz599

noncomputable abbrev qz30 := qz378

noncomputable def Ns324p194 := @Enclosure.Real.IsNear.subLit_ff_n qz30 qz8 27695011386025 1125899906842624 347333019 1125899906842624 5262605 33554432 33 33554432 

noncomputable def Ns324p195 := @Enclosure.Real.IsNear.mulLit_ff qz8 qz8 5262605 33554432 33 33554432 5262605 33554432 33 33554432 27695011386025 1125899906842624 

noncomputable def Ns324p196 := nat_lit 361164747928321513384164190045416629176072301523752338401 

noncomputable def Ns324p197 := nat_lit 3861888762982039923063034508418779142719222587902677483520 

noncomputable def Ns324p198 := nat_lit 481232320745807914071428121431949844375050513400087521 

noncomputable def Ns324p199 := nat_lit 1082531779143472924324349713893385987839466803544456840161 

noncomputable def Ns324p200 := nat_lit 173784994334191796537836552878845061422365016455620486758400 

noncomputable def Ns324p201 := BSN.cos_dyadic_bound_f 5132091 4194304 3 2 16777216 4840000 Ns324p196 Ns324p197 Ns324p198 Ns324p199 Ns324p200 Ns324p198 5708884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 5132091) (BSN.cosEvenQ 4194304) 0 2 Ns324p196 Ns324p197 Ns324p198 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 5132091) (BSN.cosOddQ 4194304) 0 2 Ns324p199 Ns324p200 Ns324p198 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz379 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns324p202 := @Ns324p185 679857216 81201725440000 1427221 4194304 10622769 1268776960000 (@Ns324p186 137 16777216 Bool.false 5708884 16777216 1 4840000 (@Ns324p190 Ns324p191 5132091 4194304 137 16777216 (@Ns324p192 1125899906842624 1454629275 1125899906842624 Ns324p187 Ns324p188 Ns324p189 Ns324p191 RS325to336.d47 (@Ns324p193 0 1 3508119270511984 219257454406999 1125899906842624 1454629275 1125899906842624 (@Ns324p194 4995876102957925662720 148888710229335 1125899906842624 1454629275 1125899906842624 (@Ns324p195 347333019 1125899906842624 (Ns324p176 rfl rfl) (Ns324p176 rfl rfl) rfl) (Ns324p176 rfl rfl) rfl rfl) qz379 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 5132091 4194304) (BSN.cos_neg_of_bound 5132091 4194304 Bool.false 5708884 16777216 1 4840000 (Ns324p201 rfl rfl)) rfl rfl) 

noncomputable abbrev qz31 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 10) (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 10 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1))

noncomputable def Ns324p203 := @Ns324p161 2512409871525971108121 Ns324p74 (Ns324p162 qz31 (@Enclosure.Real.IsNear.of_eq qz7 (@Inv.inv Real Real.instInv qz22) Bool.false 1316075 4194304 1 16777216 (BSN.rpow_neg_quarter_mk qz19 (BSN.t_div_two_pi_nonneg qz4 648182 1000 qz9)) Ns324p166) rfl) (@Ns324p167 140737488355328 474763831976571 21286545113743360000 (BSN.correction_mk qz8 (BSN.cos_two_pi_p_ne_zero_mk qz4 648182 1000 10 qz9 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 648182 1000 10 qz9 rfl rfl rfl))) (@Ns324p168 33554432 1427221 4194304 10622769 1268776960000 86678717936373 140737488355328 474763831976571 21286545113743360000 (@Ns324p169 33554432 (Ns324p184 rfl rfl rfl rfl rfl) rfl) (Ns324p202 rfl) rfl)) 

noncomputable abbrev qz32 := qz354

noncomputable def Ns324p204 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 490605271431258893031 590295810358705651712 425196675376988652708121 Ns324p74 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8))) Bool.true 490605271431258893031 590295810358705651712 425196675376988652708121 Ns324p74 (BSN.hardyZApproximantRS₀_eq qz4 10 (@BSN.floor_sqrt_eq_dec qz4 648182 1000 10 qz9 rfl rfl rfl)) (@Ns324p76 490605271431258893031 590295810358705651712 425196675376988652708121 Ns324p74 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HAdd.hAdd Real Real Real qz366 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10)) Bool.true 42806457 67108864 158855 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (Ns324p160 (Ns324p159 rfl rfl rfl rfl) rfl rfl)) (Ns324p203 rfl) rfl rfl)) 

theorem RS325to336.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 490605271431258893031 590295810358705651712 425196675376988652708121 Ns324p74 := Ns324p204 

theorem RS325to336.d50 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS325to336.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS325to336.d3 a b h)) 

noncomputable def Ns324p205 := nat_lit 17382420498285395602491572224 

noncomputable abbrev qz732 := (Enclosure.sfrac Bool.false 649791 1000)

noncomputable abbrev qz602 := qz732

noncomputable abbrev qz380 := qz602

noncomputable abbrev qz33 := qz380

noncomputable abbrev qz733 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 649791 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz603 := qz733

noncomputable abbrev qz381 := qz603

noncomputable abbrev qz34 := (@HPow.hPow Real Real Real qz584 qz381 qz351)

noncomputable abbrev qz734 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 649791 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz604 := qz734

noncomputable abbrev qz382 := qz604

noncomputable abbrev qz35 := qz382

noncomputable def Ns324p206 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz34) (Zeta.RiemannSiegel.correction qz35)) 142932749 134217728 159251 134217728 27647094623392247541 147573952589676412928 2858707497747543302093 Ns324p74 Ns324p205 

noncomputable def Ns324p207 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.cos BSN.quadSignPos 9 10 649791 1000 200 268435456 134217728 4503599627370496 Bool.false 317244681985 2440 618095470 56 84886744 8 

noncomputable def Ns324p208 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 649791 1000 107 156 268435456 134217728 4503599627370496 Bool.false 317244681985 2440 

noncomputable def Ns324p209 := Ns324p208 558195838 56 94906264 8 589812974 56 89478488 8 Bool.true 89589611 120272 Bool.true 348604960 Bool.true 231921393 14148475504056880 1 Bool.false 258556344 Bool.false Bool.false 174327425 Bool.false Bool.false 59933002 

noncomputable def Ns324p210 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 649791 1000 11 52 268435456 134217728 4503599627370496 Bool.false 317244681985 2440 

noncomputable def Ns324p211 := Ns324p210 480971758 57 109588312 8 522351262 57 101459064 8 Bool.true 181009424 89214 Bool.false 75330671 Bool.true 248280631 14148475504056880 1 Bool.false 74345811 Bool.false Bool.false 161571444 Bool.false Bool.true 89589611 

noncomputable def Ns324p212 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 649791 1000 178 86 268435456 134217728 4503599627370496 Bool.false 317244681985 2440 

noncomputable def Ns324p213 := Ns324p212 372130544 56 134217720 8 432030192 56 120047984 16 Bool.true 90912168 52407 Bool.false 382581437 Bool.false 252812664 14148475504056880 1 Bool.false 38938131 Bool.true Bool.false 157929439 Bool.true Bool.true 181009424 

noncomputable def Ns324p214 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 649791 1000 465 297 268435456 134217728 4503599627370496 Bool.false 317244681985 2440 

noncomputable def Ns324p215 := Ns324p214 186065264 56 189812528 16 294906480 56 154981288 8 Bool.false 223098984 2504 Bool.false 270443881 Bool.false 384849244 14148475504056880 1 Bool.false 226959471 Bool.true Bool.false 265915816 Bool.true Bool.true 90912168 

noncomputable def Ns324p216 := nat_lit 4006426399629889836675986925395156971779687059214674533 

noncomputable def Ns324p217 := nat_lit 3390023406492638286176986752766780858942707057295360 

noncomputable def Ns324p218 := nat_lit 55604552232265212206497598376480000 

noncomputable def Ns324p219 := nat_lit 216788085498604804794758257279603894080 

noncomputable abbrev qz605 := (@Eq.refl Real qz732)

noncomputable abbrev qz383 := qz605

noncomputable abbrev qz36 := qz383

noncomputable def Ns324p220 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz33 649791 1000 1688914374724 16000000 1299582 4000 2000 Ns324p218 Ns324p219 qz36 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns324p221 := nat_lit 11538508030934082729626842345138052078725498730538262655040 

noncomputable abbrev qz606 := (@HSub.hSub Real Real Real qz727 qz728 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz729 (@Nat.cast Real Real.instNatCast 1299582))))

noncomputable abbrev qz384 := (@HSub.hSub Real Real Real qz586 (@HMul.hMul Real Real Real qz582 (Enclosure.sfrac Bool.false 649791 4000) (Real.log (Enclosure.sfrac Bool.false 1688914374724 16000000))) (@HMul.hMul Real Real Real qz582 qz587 qz606))

noncomputable abbrev qz607 := (Enclosure.sfrac Bool.false 649791 2000)

noncomputable abbrev qz37 := (@HSub.hSub Real Real Real qz354 (@HSub.hSub Real Real Real qz354 qz384 qz607) (@HMul.hMul Real Real Real qz349 qz607 (Real.log Real.pi)))

noncomputable def Ns324p222 := @Enclosure.Real.IsNear.addLit_ft_p qz37 (Enclosure.sfrac Bool.true Ns324p218 Ns324p219) 53224837096569815413 45035996273704960 4504368248747263899 495616000000000000000000 Ns324p218 Ns324p219 0 1 Ns324p221 

noncomputable def Ns324p223 := nat_lit 89296458853396465226403020800000 

noncomputable abbrev qz38 := (@HSub.hSub Real Real Real qz354 qz384 qz607)

noncomputable def Ns324p224 := @Enclosure.Real.IsNear.subLit_ff_p qz38 (@HMul.hMul Real Real Real qz5 qz607 (Real.log Real.pi)) 1749362904570629317741 1125899906842624000 513899533263969 121000000000000000000 24958966800951 67108864000 649791 134217728000 Ns324p223 53224837096569815413 45035996273704960 

noncomputable def Ns324p225 := nat_lit 3498725809141258635482000 

noncomputable abbrev qz39 := qz384

noncomputable def Ns324p226 := @Enclosure.Real.IsNear.subLit_ff_p qz39 qz607 2115162717754217063533 1125899906842624000 513899533263969 121000000000000000000 649791 2000 0 1 Ns324p225 1749362904570629317741 1125899906842624000 513899533263969 121000000000000000000 

noncomputable def Ns324p227 := nat_lit 4762923013752928785640660253680861184 

noncomputable def Ns324p228 := nat_lit 55934617404785092976443392 

noncomputable def Ns324p229 := nat_lit 23933105538571942717869669094905587671906221449806883972837169514043015432495158104938852268617594158841712831039813600439971245257090048697368986790133760 

noncomputable def Ns324p230 := nat_lit 451422818491282029031883044269936901764518548240349557941908409753734551686336215996976183893771139089713556850156675407796620464389618501592205777436672 

noncomputable def Ns324p231 := nat_lit 49401353282844406358096636926576296733203563129248004952896487124973048850572685644447712983075227191712851002949988168303602818352862614540779520 

noncomputable def Ns324p232 := BSN.log_dyadic_bound 640338374724 2737490374724 7 6 Ns324p229 134217728 38720000 Ns324p230 Ns324p231 63975267 3377828749448 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 640338374724) (BSN.artanhQ 2737490374724) 0 6 Ns324p230 Ns324p229 Ns324p231 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz385 := (Real.log (Enclosure.sfrac Bool.false 1688914374724 16000000))

noncomputable def Ns324p233 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 649791 4000) qz385 649791 4000 0 1 3255823243222263 281474976710656 195312621 7562500000000000 2115604641036637497033 1125899906842624000 126912383312211 30250000000000000000 (Enclosure.Real.IsNear.const Bool.false 649791 4000) (BSN.isNear_log_sfrac 1688914374724 16000000 3255823243222263 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1688914374724) qz357)) Bool.false Ns324p228 Ns324p98 1000000619520000 38720000000000000000000 3255823243222263 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1688914374724 16000000 16 3377828749448 2097152000000 63975267 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns324p232 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns324p234 := BSN.arctan_dyadic_bound_f 1000 1299582 1 0 16777216 4840000 0 1 1 0 1 1 12909 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1299582) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1299582) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz386 := (@Nat.cast Real Real.instNatCast 1299582)

noncomputable def Ns324p235 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz386)) 884279719003555 562949953421312 1 2000000000000000 12909 16777216 1 4840000 14828484729193231286272 883846564840867 562949953421312 50000000121 242000000000000000 qz15 (Ns324p234 rfl) rfl rfl 

noncomputable abbrev qz387 := (@HMul.hMul Real Real Real qz582 qz587 qz606)

noncomputable abbrev qz40 := qz387

noncomputable abbrev qz388 := qz606

noncomputable abbrev qz41 := qz388

noncomputable def Ns324p236 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 649791 4000) qz385) qz40 2115604641036637497033 1125899906842624000 126912383312211 30250000000000000000 883846564840867 2251799813685248 50000000121 968000000000000000 Ns324p227 2115162717754217063533 1125899906842624000 513899533263969 121000000000000000000 (Ns324p233 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz41 1 4 0 1 883846564840867 562949953421312 50000000121 242000000000000000 883846564840867 2251799813685248 50000000121 968000000000000000 qz365 Ns324p235 rfl) 

noncomputable def Ns324p237 := @Ns324p222 Ns324p216 Ns324p217 4504368248747263899 495616000000000000000000 (@Ns324p224 4504368248747263899 495616000000000000000000 (Ns324p226 (Ns324p236 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 649791 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz607 (Real.log Real.pi) 649791 2000 0 1 38410761 33554432 1 67108864 24958966800951 67108864000 649791 134217728000 (Enclosure.Real.IsNear.const Bool.false 649791 2000) RS325to336.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns324p218 Ns324p219) 

noncomputable def Ns324p238 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz33) Bool.false Ns324p216 Ns324p217 4504368248747263899 495616000000000000000000 1239237039 1048576 153 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz33) (@HAdd.hAdd Real Real Real qz366 qz37 (Enclosure.sfrac Bool.true Ns324p218 Ns324p219)) Bool.false Ns324p216 Ns324p217 4504368248747263899 495616000000000000000000 Ns324p220 (Ns324p237 rfl rfl)) 

noncomputable def Ns324p239 := nat_lit 101041258722388691513260125099876307456677405237379019916698431459097166713431487865638881 

noncomputable def Ns324p240 := nat_lit 20052072892042597411705012245279816272850392000149059967199507548332190919545345701492817920 

noncomputable def Ns324p241 := nat_lit 7272398396681801823880132048750180148876157493962030143915060363564013586652384940001 

noncomputable def Ns324p242 := nat_lit 303109231370372710936132615035531422009734463397149135689807464256564372113121158827036641 

noncomputable def Ns324p243 := nat_lit 902343280141916883526725551037591732278267640006707698523977839674948591379540556567176806400 

noncomputable def Ns324p244 := BSN.cos_dyadic_bound_f 40523757499 68719476736 3 2 33554432 9689454 Ns324p239 Ns324p240 Ns324p241 Ns324p242 Ns324p243 Ns324p241 27887373 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 40523757499) (BSN.cosEvenQ 68719476736) 0 2 Ns324p239 Ns324p240 Ns324p241 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 40523757499) (BSN.cosOddQ 68719476736) 0 2 Ns324p242 Ns324p243 Ns324p241 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p245 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz33) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1239237039) (@Nat.cast Real Real.instNatCast 1048576)) Bool.false 1239237039 1048576 153 16777216 Bool.false 27887373 33554432 1 4840000 (Ns324p238 rfl) (Enclosure.sfrac_false_div 1239237039 1048576) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1239237039) (@Nat.cast Real Real.instNatCast 1048576)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 89112685143831869390848) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false 27887373 33554432 188 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q0 1239237039 1048576 226375608064910080 72057594037927936 188 89112685143831869390848 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 27887373 33554432 89112685143831869390848 151115727451828646838272 40523757499 68719476736 9689454 9680000 (Ns324p244 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns324p246 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz33) Bool.false Ns324p216 Ns324p217 4504368248747263899 495616000000000000000000 317244681985 268435456 2440 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz33) (@HAdd.hAdd Real Real Real qz366 qz37 (Enclosure.sfrac Bool.true Ns324p218 Ns324p219)) Bool.false Ns324p216 Ns324p217 4504368248747263899 495616000000000000000000 Ns324p220 (Ns324p237 rfl rfl)) 

noncomputable def Ns324p247 := Ns324p215 52407 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 465 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 226959471 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 297 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 265915816 268435456) qz36 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 1) Bool.false 27887373 33554432 11832769 1268776960000 223098984 268435456 2504 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz33)) Bool.false 27887373 33554432 11832769 1268776960000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz33) qz33) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz33)) Bool.false 27887373 33554432 757297216 81201725440000 27887373 33554432 11832769 1268776960000 (Ns324p245 rfl rfl) rfl)) rfl) (Ns324p246 rfl) RS325to336.d7 

noncomputable def Ns324p248 := nat_lit 84022940665992906983460876119208464073888726685843181530214648701852225 

noncomputable def Ns324p249 := nat_lit 9783225446575624168688766434777683578849446968051522941942878087235502080 

noncomputable def Ns324p250 := nat_lit 28616550193922630730746360804056215025795549792725938057718264306241 

noncomputable def Ns324p251 := nat_lit 220013751139191262602166800489958457750142996144210585822278250362640961 

noncomputable def Ns324p252 := nat_lit 179359133187219776425960717970924198945573194414277920602286098265984204800 

noncomputable def Ns324p253 := BSN.sin_dyadic_bound_f 270443881 268435456 3 2 268435456 134217728 Ns324p248 Ns324p249 Ns324p250 Ns324p251 Ns324p252 Ns324p250 226959471 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 270443881) qz367 0 2 Ns324p248 Ns324p249 Ns324p250 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 270443881) qz368 0 2 Ns324p251 Ns324p252 Ns324p250 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p254 := nat_lit 30731737855906864015706560868664344626359076472885614107830944694895370674371788437275514964194011309550862336 

noncomputable def Ns324p255 := nat_lit 10555714933345070846559129234811078776829315434209806384650539504835188834690700164368807503703715086336 

noncomputable def Ns324p256 := nat_lit 153526125010802474848183475067361788414610878233782328172691422097564643672513732865008638097772833731715792896 

noncomputable def Ns324p257 := BSN.sin_dyadic_bound_f 384849244 268435456 4 3 268435456 134217728 Ns324p254 Ns324p119 Ns324p255 Ns324p256 Ns324p122 Ns324p255 265915816 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 384849244) qz367 0 3 Ns324p254 Ns324p119 Ns324p255 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 384849244) qz368 0 3 Ns324p256 Ns324p122 Ns324p255 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p258 := nat_lit 11555959539693375374268873130566922813329409989969634932479505453361629354484823247694276562881800616622162161 

noncomputable def Ns324p259 := nat_lit 9833015613990188966912309145703108785155447074962790649018702217799047610580080379053241808393964093681 

noncomputable def Ns324p260 := nat_lit 69991599316623867083358977044483336753385953213955563705732384319872561744138525574073491736431855358590583025 

noncomputable def Ns324p261 := BSN.cos_dyadic_bound_f 382581437 268435456 4 3 268435456 134217728 Ns324p258 Ns324p125 Ns324p259 Ns324p260 Ns324p128 Ns324p259 38938131 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 382581437) qz369 0 3 Ns324p258 Ns324p125 Ns324p259 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 382581437) qz370 0 3 Ns324p260 Ns324p128 Ns324p259 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p262 := nat_lit 35650648131737783206025557253594973424846765612893787197715845885198336 

noncomputable def Ns324p263 := nat_lit 1087025049619513796520974048308631508761049663116835882438097565248389120 

noncomputable def Ns324p264 := nat_lit 16687473927208768804046843017462290354107824772015450556159655673856 

noncomputable def Ns324p265 := nat_lit 106918569447358932080468578074749995693832081189137330692035218344247296 

noncomputable def Ns324p266 := nat_lit 48916127232878120843443832173888417894247234840257614709714390436177510400 

noncomputable def Ns324p267 := BSN.cos_dyadic_bound_f 252812664 268435456 3 2 268435456 134217728 Ns324p262 Ns324p263 Ns324p264 Ns324p265 Ns324p266 Ns324p264 157929439 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 252812664) qz369 0 2 Ns324p262 Ns324p263 Ns324p264 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 252812664) qz370 0 2 Ns324p265 Ns324p266 Ns324p264 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p268 := Ns324p213 89214 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 178 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 38938131 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 86 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 157929439 268435456) qz36 rfl rfl (Ns324p247 RS325to336.d9 RS325to336.d11 RS325to336.d13 RS325to336.d17 (Ns324p253 rfl rfl) (Ns324p257 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns324p246 rfl) RS325to336.d19 RS325to336.d21 RS325to336.d23 RS325to336.d25 RS325to336.d17 (Ns324p261 rfl rfl) (Ns324p267 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns324p269 := nat_lit 32202333508175115454972875478081 

noncomputable def Ns324p270 := nat_lit 623075623024179315423659559506411520 

noncomputable def Ns324p271 := nat_lit 4361529361169255207965616916544880640 

noncomputable def Ns324p272 := BSN.sin_dyadic_bound_f 75330671 268435456 2 1 268435456 134217728 Ns324p269 Ns324p270 Ns324p269 Ns324p269 Ns324p271 Ns324p269 74345811 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 75330671) qz367 0 1 Ns324p269 Ns324p270 Ns324p269 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 75330671) qz368 0 1 Ns324p269 Ns324p271 Ns324p269 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p273 := nat_lit 33161128523942314655746874059218926353413649153450329369494978559309121 

noncomputable def Ns324p274 := nat_lit 14439186428030692010483317731606013179313940190782864602178119890241 

noncomputable def Ns324p275 := nat_lit 99454507198970882583219655542193567033882319579969422379280579438146881 

noncomputable def Ns324p276 := BSN.cos_dyadic_bound_f 248280631 268435456 3 2 268435456 134217728 Ns324p273 Ns324p263 Ns324p274 Ns324p275 Ns324p266 Ns324p274 161571444 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 248280631) qz369 0 2 Ns324p273 Ns324p263 Ns324p274 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 248280631) qz370 0 2 Ns324p275 Ns324p266 Ns324p274 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p277 := Ns324p211 120272 BSN.abs_quadSignPos (BSN.cos_quad_nat3 11 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 74345811 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 161571444 268435456) qz36 rfl rfl (Ns324p268 rfl rfl) (Ns324p246 rfl) RS325to336.d27 RS325to336.d29 RS325to336.d31 RS325to336.d33 RS325to336.d17 (Ns324p272 rfl rfl) (Ns324p276 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p278 := nat_lit 20680484488011859399252521849224138080805486194314096844141939867658647286623789587154525307532598470246400000 

noncomputable def Ns324p279 := nat_lit 3221089144821812303095034283667052580183403764506846858878864603648286008232230986465673216000000000000 

noncomputable def Ns324p280 := nat_lit 103342343166482142907174937979763210546784448141650099117870615011160116441045680411765308624116469727232000000 

noncomputable def Ns324p281 := BSN.sin_dyadic_bound_f 348604960 268435456 4 3 268435456 134217728 Ns324p278 Ns324p119 Ns324p279 Ns324p280 Ns324p122 Ns324p279 258556344 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 348604960) qz367 0 3 Ns324p278 Ns324p119 Ns324p279 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 348604960) qz368 0 3 Ns324p280 Ns324p122 Ns324p279 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p282 := nat_lit 25245039483718630317414474835254388611358641224192957014411961412932481 

noncomputable def Ns324p283 := nat_lit 8370019832075383712133771438890738267614147070499858637374042723201 

noncomputable def Ns324p284 := nat_lit 75718378411491740184819156962885384357540695378437871325961136153351041 

noncomputable def Ns324p285 := BSN.cos_dyadic_bound_f 231921393 268435456 3 2 268435456 134217728 Ns324p282 Ns324p263 Ns324p283 Ns324p284 Ns324p266 Ns324p283 174327425 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 231921393) qz369 0 2 Ns324p282 Ns324p263 Ns324p283 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 231921393) qz370 0 2 Ns324p284 Ns324p266 Ns324p283 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p286 := Ns324p209 146962 BSN.abs_quadSignPos (BSN.cos_quad_nat3 107 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 258556344 268435456) BSN.abs_quadSignPos qz595 (BSN.sfrac_eq_quadSignPos_mul Bool.false 174327425 268435456) qz36 rfl rfl (Ns324p277 rfl) (Ns324p246 rfl) RS325to336.d35 RS325to336.d37 RS325to336.d39 RS325to336.d41 RS325to336.d17 (Ns324p281 rfl rfl) (Ns324p285 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p287 := nat_lit 10339826127134060524108768727296 

noncomputable def Ns324p288 := BSN.cos_dyadic_bound_f 56705908 268435456 2 1 268435456 134217728 Ns324p287 Ns324p149 Ns324p287 Ns324p287 Ns324p150 Ns324p287 262468248 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 56705908) qz369 0 1 Ns324p287 Ns324p149 Ns324p287 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 56705908) qz370 0 1 Ns324p287 Ns324p150 Ns324p287 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p289 := Ns324p207 Bool.false 59933002 146962 Bool.true 56705908 14148475504056880 1 Bool.false 262468248 Bool.false Bool.false 142932749 159251 BSN.abs_quadSignPos qz596 (BSN.sfrac_eq_quadSignPos_mul Bool.false 262468248 268435456) qz36 rfl (Ns324p286 rfl) (Ns324p246 rfl) RS325to336.d43 RS325to336.d45 RS325to336.d17 (Ns324p288 rfl rfl) rfl 

noncomputable def Ns324p290 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) 142932749 268435456 159251 268435456 142932749 268435456 159251 268435456 76736435310297088 142932749 134217728 159251 134217728 (Ns324p289 rfl rfl rfl rfl) 

noncomputable def Ns324p291 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz34) (Zeta.RiemannSiegel.correction qz35) 2630519 8388608 1 16777216 10510129226739 17592186044416 540955929310387 21286545113743360000 27647094623392247541 147573952589676412928 

noncomputable def Ns324p292 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz34 1 1 0 1 2630519 8388608 1 16777216 2630519 8388608 1 16777216 

noncomputable abbrev qz42 := qz381

noncomputable def Ns324p293 := @Enclosure.Real.IsNear.sqrt_image qz42 3470113316223 33554432000 649791 33554432000 170614814 170614847 16777216 (@Enclosure.Real.IsNear.of_eq qz42 (@HMul.hMul Real Real Real qz5 qz33 qz3) Bool.false 3470113316223 33554432000 649791 33554432000 (BSN.t_div_two_pi_mk qz33 649791 1000 qz36) (@Enclosure.Real.IsNear.mulLit_ff qz33 qz3 649791 1000 0 1 5340353 33554432 1 33554432 3470113316223 33554432000 649791 33554432000 (Enclosure.Real.IsNear.const Bool.false 649791 1000) RS325to336.d48 rfl)) 

noncomputable abbrev qz735 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 649791 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz608 := qz735

noncomputable abbrev qz389 := qz608

noncomputable abbrev qz43 := qz389

noncomputable def Ns324p294 := @Enclosure.Real.IsNear.sqrt_image qz43 341229661 33554432 33 33554432 53501790 53501796 16777216 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 341229661 33554432 33 33554432 341229661 33554432 33 33554432 (Ns324p293 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns324p295 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz43) 53501793 16777216 3 16777216 5261037 5261039 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz43) Bool.false 107003586 33554432 6 33554432 53501793 16777216 3 16777216 (Ns324p294 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns324p296 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz43)) Bool.false 10522076 33554432 2 33554432 2630519 8388608 1 16777216 (Ns324p295 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz44 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz382))

noncomputable abbrev qz609 := (@HMul.hMul Real Real Real qz723 qz734 qz734)

noncomputable abbrev qz390 := (@HSub.hSub Real Real Real qz586 (@HSub.hSub Real Real Real qz586 qz609 qz604) qz600)

noncomputable abbrev qz45 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz390))

noncomputable def Ns324p297 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz35) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz44) qz45) Bool.false 10510129226739 

noncomputable def Ns324p298 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz44) qz45 69205231 33554432 915 

noncomputable def Ns324p299 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz44) Bool.false 69205231 33554432 915 33554432 69205231 33554432 915 

noncomputable def Ns324p300 := @Enclosure.Real.IsNear.recentre' qz44 Bool.false 8134500 16777216 65017152 10150215680000 2033625 4194304 1015893 158597120000 

noncomputable abbrev qz46 := (@HMul.hMul Real Real Real qz349 qz346 qz382)

noncomputable abbrev qz391 := (@Nat.cast Real Real.instNatCast 33554432)

noncomputable def Ns324p301 := @Enclosure.Real.IsNear.cos_image qz46 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 35722051) qz391) Bool.false 35722051 33554432 13 2097152 Bool.false 8134500 16777216 1 

noncomputable def Ns324p302 := nat_lit 890540488547290207343791783 

noncomputable def Ns324p303 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz35 884279719003555 140737488355328 1 500000000000000 5685341 33554432 33 33554432 5027431741919390387255 4722366482869645213696 Ns324p302 

noncomputable def Ns324p304 := @Enclosure.Real.IsNear.subLit_ff_p qz43 qz1 341229661 33554432 33 33554432 10 1 0 1 5685341 5685341 33554432 33 

noncomputable def Ns324p305 := @Ns324p304 33554432 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 341229661 33554432 33 33554432 341229661 33554432 33 33554432 (Ns324p293 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns324p306 := @Enclosure.Real.IsNear.recentre' qz46 Bool.false 5027431741919390387255 4722366482869645213696 Ns324p302 Ns324p173 35722051 33554432 13 2097152 (@Ns324p303 Ns324p173 RS325to336.d47 (Ns324p305 rfl rfl) rfl) 

noncomputable def Ns324p307 := nat_lit 3470454295855402427383735433623901541422660614894470082738354081 

noncomputable def Ns324p308 := nat_lit 64791741944522487909851911563195676133695224709322207119351480320 

noncomputable def Ns324p309 := nat_lit 2651496690557620697270981537437967916889932252119031043946401 

noncomputable def Ns324p310 := nat_lit 10406059894185092040756664337796828688434201980179172186127169441 

noncomputable def Ns324p311 := nat_lit 2915628387503511955943336020343805426016285111919499320370816614400 

noncomputable abbrev qz392 := (BSN.cosEvenQ 33554432)

noncomputable def Ns324p312 := BSN.cos_dyadic_bound_f 35722051 33554432 3 2 16777216 4840000 Ns324p307 Ns324p308 Ns324p309 Ns324p310 Ns324p311 Ns324p309 8134500 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 35722051) qz392 0 2 Ns324p307 Ns324p308 Ns324p309 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 35722051) (BSN.cosOddQ 33554432) 0 2 Ns324p310 Ns324p311 Ns324p309 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p313 := @Enclosure.Real.IsNear.inv_image qz44 2033625 4194304 1015893 158597120000 34602158 34603073 16777216 (Ns324p300 (@Ns324p301 4840000 (Ns324p306 rfl) (Enclosure.sfrac_false_div 35722051 33554432) (Ns324p312 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns324p314 := @Enclosure.Real.IsNear.recentre' qz45 Bool.false 4859808 16777216 

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz349 qz346 qz390)

noncomputable def Ns324p315 := @Enclosure.Real.IsNear.cos_image qz47 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 42846231)) qz391) Bool.true 42846231 33554432 

noncomputable def Ns324p316 := nat_lit 202335606039897774248902430725 

noncomputable def Ns324p317 := nat_lit 40007662357210330311427259963099357 

noncomputable def Ns324p318 := @Enclosure.Real.IsNear.recentre' qz47 Bool.true Ns324p316 Ns324p188 Ns324p317 

noncomputable abbrev qz48 := qz390

noncomputable def Ns324p319 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz48 884279719003555 140737488355328 1 500000000000000 228814029872695 

noncomputable abbrev qz393 := (@HSub.hSub Real Real Real qz586 qz609 qz604)

noncomputable abbrev qz49 := qz393

noncomputable def Ns324p320 := @Enclosure.Real.IsNear.subLit_tf qz49 qz29 158445285695031 1125899906842624 1482529851 1125899906842624 1 16 

noncomputable abbrev qz394 := qz609

noncomputable abbrev qz50 := qz394

noncomputable def Ns324p321 := @Enclosure.Real.IsNear.subLit_ff_n qz50 qz35 32323102286281 1125899906842624 375233595 1125899906842624 5685341 33554432 33 33554432 

noncomputable def Ns324p322 := @Enclosure.Real.IsNear.mulLit_ff qz35 qz35 5685341 33554432 33 33554432 5685341 33554432 33 33554432 32323102286281 1125899906842624 

noncomputable def Ns324p323 := nat_lit 7188629028395234909730871751898316844875923543436798308805152321 

noncomputable def Ns324p324 := nat_lit 11357977375730225513374353174418850690090665034042638462783041 

noncomputable def Ns324p325 := nat_lit 21543171130434244278165866549346112833247589300242309649489890881 

noncomputable def Ns324p326 := BSN.cos_dyadic_bound_f 42846231 33554432 3 2 16777216 4840000 Ns324p323 Ns324p308 Ns324p324 Ns324p325 Ns324p311 Ns324p324 4859808 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 42846231) qz392 0 2 Ns324p323 Ns324p308 Ns324p324 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 42846231) (BSN.cosOddQ 33554432) 0 2 Ns324p325 Ns324p311 Ns324p324 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p327 := @Ns324p314 689537216 81201725440000 151869 524288 10774019 1268776960000 (@Ns324p315 139 16777216 Bool.false 4859808 16777216 1 4840000 (@Ns324p318 Ns324p191 42846231 33554432 139 16777216 (@Ns324p319 1125899906842624 1482529851 1125899906842624 Ns324p316 Ns324p188 Ns324p317 Ns324p191 RS325to336.d47 (@Ns324p320 0 1 3661024477963120 228814029872695 1125899906842624 1482529851 1125899906842624 (@Ns324p321 5316541564574490427392 158445285695031 1125899906842624 1482529851 1125899906842624 (@Ns324p322 375233595 1125899906842624 (Ns324p305 rfl rfl) (Ns324p305 rfl rfl) rfl) (Ns324p305 rfl rfl) rfl rfl) qz379 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 42846231 33554432) (BSN.cos_neg_of_bound 42846231 33554432 Bool.false 4859808 16777216 1 4840000 (Ns324p326 rfl rfl)) rfl rfl) 

noncomputable def Ns324p328 := @Ns324p291 2858707497747543302093 Ns324p74 (Ns324p292 qz31 (@Enclosure.Real.IsNear.of_eq qz34 (@Inv.inv Real Real.instInv (Real.sqrt qz43)) Bool.false 2630519 8388608 1 16777216 (BSN.rpow_neg_quarter_mk qz42 (BSN.t_div_two_pi_nonneg qz33 649791 1000 qz36)) Ns324p296) rfl) (@Ns324p297 17592186044416 540955929310387 21286545113743360000 (BSN.correction_mk qz35 (BSN.cos_two_pi_p_ne_zero_mk qz33 649791 1000 10 qz36 rfl rfl (@BSN.floor_sqrt_eq_dec qz33 649791 1000 10 qz36 rfl rfl rfl))) (@Ns324p298 33554432 151869 524288 10774019 1268776960000 10510129226739 17592186044416 540955929310387 21286545113743360000 (@Ns324p299 33554432 (Ns324p313 rfl rfl rfl rfl rfl) rfl) (Ns324p327 rfl) rfl)) 

noncomputable def Ns324p329 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz33) (hardyZApproximantRS₀ qz33) Bool.false 129509124892096188683 147573952589676412928 426596656986340521222093 Ns324p74 (@Eq.refl Real (hardyZApproximantRS₀ qz33)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz33) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz34) (Zeta.RiemannSiegel.correction qz35))) Bool.false 129509124892096188683 147573952589676412928 426596656986340521222093 Ns324p74 (BSN.hardyZApproximantRS₀_eq qz33 10 (@BSN.floor_sqrt_eq_dec qz33 649791 1000 10 qz36 rfl rfl rfl)) (@Ns324p206 129509124892096188683 147573952589676412928 426596656986340521222093 Ns324p74 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (@HAdd.hAdd Real Real Real qz366 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 10)) Bool.false 142932749 134217728 159251 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (Ns324p290 (Ns324p289 rfl rfl rfl rfl) rfl rfl)) (Ns324p328 rfl) rfl rfl)) 

theorem RS325to336.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz33) Bool.false 129509124892096188683 147573952589676412928 426596656986340521222093 Ns324p74 := Ns324p329 

noncomputable abbrev qz610 := (@HMul.hMul Real Real Real qz723 (Real.sqrt qz731) qz725)

noncomputable abbrev qz395 := qz610

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv qz395)

noncomputable abbrev qz396 := (@HMul.hMul Real Real Real qz582 (@HMul.hMul Real Real Real qz582 qz610 qz610) qz610)

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz396))

noncomputable abbrev qz397 := (@HMul.hMul Real Real Real qz582 qz598 qz598)

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz349 qz397 qz372))

noncomputable abbrev qz611 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz51)

noncomputable def Ns324p330 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz366 (@HAdd.hAdd Real Real Real qz366 qz611 qz52) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz53)) Bool.false 

noncomputable def Ns324p331 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz366 qz611 qz52) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz53) 20411801 1073741824 

noncomputable def Ns324p332 := @Enclosure.Real.IsNear.addLit_ff qz611 qz52 2551475 134217728 25 134217728 

noncomputable def Ns324p333 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz51 25 4 0 1 102059 33554432 1 33554432 2551475 

noncomputable def Ns324p334 := @Enclosure.Real.IsNear.recentre' qz51 Bool.false 102059 33554432 1 33554432 102059 33554432 1 33554432 

noncomputable def Ns324p335 := @Enclosure.Real.IsNear.mulLit_ff qz22 qz19 26734321 8388608 3 16777216 1730760344123 16777216000 324091 16777216000 46270702613854745483 140737488355328000 2815123457383 

noncomputable def Ns324p336 := @Enclosure.Real.IsNear.sqrt_image qz19 1730760344123 16777216000 324091 16777216000 170403446 170403479 16777216 qz20 

noncomputable def Ns324p337 := @Enclosure.Real.IsNear.sqrt_image qz21 340806925 33554432 33 33554432 53468639 53468645 16777216 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 340806925 33554432 33 33554432 340806925 33554432 33 33554432 (Ns324p336 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz398 := (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 106937284 33554432 6 33554432 26734321 8388608 3 16777216 (Ns324p337 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns324p338 := @Ns324p335 35184372088832000 qz398 

noncomputable def Ns324p339 := Ns324p338 qz20 

noncomputable abbrev qz54 := qz395

noncomputable def Ns324p340 := @Enclosure.Real.IsNear.inv_image qz54 46270702613854745483 140737488355328000 2815123457383 35184372088832000 51029 51030 16777216 (Ns324p339 rfl) rfl rfl 

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv qz396)

noncomputable def Ns324p341 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz55 1 32 0 1 1 

noncomputable def Ns324p342 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 1 33554432 1 33554432 

noncomputable def Ns324p343 := nat_lit 99064552656722186079921694164026033536207361407075156593587 

noncomputable def Ns324p344 := nat_lit 2787593149816327892691964784081045188247552000000000 

noncomputable def Ns324p345 := nat_lit 18081355896500411913949021872076760752567840814133697 

noncomputable def Ns324p346 := nat_lit 696898287454081973172991196020261297061888000000000 

noncomputable abbrev qz56 := qz396

noncomputable def Ns324p347 := @Enclosure.Real.IsNear.inv_image qz56 Ns324p343 Ns324p344 Ns324p345 Ns324p346 0 1 

noncomputable def Ns324p348 := nat_lit 2140977920379784375877126683998708903289 

noncomputable def Ns324p349 := nat_lit 19807040628566084398385987584000000 

noncomputable def Ns324p350 := nat_lit 130257756167695546917095296668367 

noncomputable def Ns324p351 := nat_lit 2475880078570760549798248448000000 

noncomputable abbrev qz399 := (@HMul.hMul Real Real Real qz582 qz610 qz610)

noncomputable abbrev qz57 := qz399

noncomputable def Ns324p352 := @Enclosure.Real.IsNear.mulLit_ff qz57 qz54 Ns324p348 Ns324p349 Ns324p350 Ns324p351 46270702613854745483 140737488355328000 2815123457383 

noncomputable def Ns324p353 := @Enclosure.Real.IsNear.mulLit_ff qz54 qz54 46270702613854745483 140737488355328000 2815123457383 35184372088832000 46270702613854745483 140737488355328000 2815123457383 35184372088832000 Ns324p348 

noncomputable def Ns324p354 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz53 13 10 0 1 1036603 33554432 1 

noncomputable def Ns324p355 := @Enclosure.Real.IsNear.recentre' qz53 Bool.false 1036603 33554432 1 33554432 1036603 33554432 

noncomputable abbrev qz58 := qz397

noncomputable def Ns324p356 := @Enclosure.Real.IsNear.mulLit_ff qz58 qz22 714723919331041 70368744177664 320811861 281474976710656 26734321 8388608 3 16777216 19107658685774155358161 

noncomputable def Ns324p357 := @Enclosure.Real.IsNear.mulLit_ff qz22 qz22 26734321 8388608 3 16777216 26734321 8388608 3 16777216 714723919331041 70368744177664 320811861 

noncomputable def Ns324p358 := @Ns324p357 281474976710656 qz398 

noncomputable def Ns324p359 := Ns324p358 qz398 

noncomputable def Ns324p360 := @Ns324p356 590295810358705651712 25730062539570837 4722366482869645213696 (Ns324p359 rfl) qz398 

noncomputable abbrev qz59 := (@HMul.hMul Real Real Real qz349 qz397 qz372)

noncomputable def Ns324p361 := @Enclosure.Real.IsNear.inv_image qz59 19107658685774155358161 590295810358705651712 25730062539570837 4722366482869645213696 518301 518302 16777216 (Ns324p360 rfl) 

noncomputable def Ns324p362 := @Ns324p331 201 1073741824 13475839 335544320 13 335544320 21318635834310656 317672429 5368709120 1213 5368709120 (@Ns324p332 1 1073741824 1 1073741824 2739625554608128 20411801 1073741824 201 1073741824 (@Ns324p333 134217728 25 134217728 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns324p334 (Ns324p340 rfl rfl rfl rfl) rfl) rfl) (@Ns324p341 33554432 1 33554432 1 1073741824 1 1073741824 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns324p342 1 33554432 1 33554432 (@Ns324p347 16777216 (@Ns324p352 35184372088832000 Ns324p343 Ns324p344 Ns324p345 Ns324p346 (@Ns324p353 Ns324p349 Ns324p350 Ns324p351 (Ns324p339 rfl) (Ns324p339 rfl) rfl) (Ns324p339 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns324p354 33554432 13475839 335544320 13 335544320 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns324p355 1 33554432 (Ns324p361 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS325to336.d52 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 := @Ns324p330 317672429 5368709120 1213 5368709120 (BSN.hardyZErrorBoundRS₀_mk qz4 648182 1000 qz9 rfl rfl) (Ns324p362 rfl rfl) 

noncomputable def Ns324p363 := nat_lit 89282241316754229821440000 

noncomputable def Ns324p364 := nat_lit 37353591878269451803415281664 

noncomputable abbrev qz736 := (Enclosure.sfrac Bool.false 650383 1000)

noncomputable abbrev qz612 := qz736

noncomputable abbrev qz400 := qz612

noncomputable abbrev qz60 := qz400

noncomputable abbrev qz737 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 650383 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz613 := qz737

noncomputable abbrev qz401 := qz613

noncomputable abbrev qz61 := (@HPow.hPow Real Real Real qz584 qz401 qz351)

noncomputable abbrev qz738 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 650383 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz614 := qz738

noncomputable abbrev qz402 := qz614

noncomputable abbrev qz62 := qz402

noncomputable def Ns324p365 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz61) (Zeta.RiemannSiegel.correction qz62)) 6776485 134217728 39849 33554432 218699354450048691533 1180591620717411303424 732826384637336261479 Ns324p363 Ns324p364 

noncomputable def Ns324p366 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.cos BSN.quadSignPos 9 10 650383 1000 200 268435456 134217728 4503599627370496 Bool.false 317613300745 2443 618095470 56 84886744 8 

noncomputable def Ns324p367 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 650383 1000 107 156 268435456 134217728 4503599627370496 Bool.false 317613300745 2443 

noncomputable def Ns324p368 := Ns324p367 558195838 56 94906264 8 589812974 56 89478488 8 Bool.true 239709919 120381 Bool.true 310438136 Bool.true 212471914 14148475504056880 1 Bool.false 245722757 Bool.false Bool.false 188647064 Bool.false Bool.true 89951451 

noncomputable def Ns324p369 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 650383 1000 11 52 268435456 134217728 4503599627370496 Bool.false 317613300745 2443 

noncomputable def Ns324p370 := Ns324p369 480971758 57 109588312 8 522351262 57 101459064 8 Bool.true 378323134 89294 Bool.false 159214150 Bool.true 188893818 14148475504056880 1 Bool.false 150041986 Bool.false Bool.false 204672238 Bool.false Bool.true 239709919 

noncomputable def Ns324p371 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 650383 1000 179 86 268435456 134217728 4503599627370496 Bool.false 317613300745 2443 

noncomputable def Ns324p372 := Ns324p371 372130544 56 134217720 8 432030192 56 120047984 16 Bool.true 406591257 52453 Bool.false 109241486 Bool.false 365669550 14148475504056880 1 Bool.false 106251047 Bool.false Bool.false 55582830 Bool.true Bool.true 378323134 

noncomputable def Ns324p373 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 650383 1000 466 298 268435456 134217728 4503599627370496 Bool.false 317613300745 2443 

noncomputable def Ns324p374 := Ns324p373 186065264 56 189812528 16 294906480 56 154981288 8 Bool.true 102580640 2504 Bool.false 107254576 Bool.false 157225939 14148475504056880 1 Bool.false 247291980 Bool.true Bool.false 223692248 Bool.true Bool.true 406591257 

noncomputable def Ns324p375 := nat_lit 36297519085735703570519316196404690543607350805595025757 

noncomputable def Ns324p376 := nat_lit 30677371081648381712937272934073028828334922043228160 

noncomputable def Ns324p377 := nat_lit 55858310058063065770145522628640000 

noncomputable def Ns324p378 := nat_lit 217975831742822249118328222536952614720 

noncomputable abbrev qz615 := (@Eq.refl Real qz736)

noncomputable abbrev qz403 := qz615

noncomputable abbrev qz63 := qz403

noncomputable def Ns324p379 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz60 650383 1000 1691993186756 16000000 1300766 4000 2000 Ns324p377 Ns324p378 qz63 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns324p380 := nat_lit 11615206107435425142566181182849500973954352257790408242240 

noncomputable abbrev qz616 := (@HSub.hSub Real Real Real qz727 qz728 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz729 (@Nat.cast Real Real.instNatCast 1300766))))

noncomputable abbrev qz404 := (@HSub.hSub Real Real Real qz586 (@HMul.hMul Real Real Real qz582 (Enclosure.sfrac Bool.false 650383 4000) (Real.log (Enclosure.sfrac Bool.false 1691993186756 16000000))) (@HMul.hMul Real Real Real qz582 qz587 qz616))

noncomputable abbrev qz617 := (Enclosure.sfrac Bool.false 650383 2000)

noncomputable abbrev qz64 := (@HSub.hSub Real Real Real qz354 (@HSub.hSub Real Real Real qz354 qz404 qz617) (@HMul.hMul Real Real Real qz349 qz617 (Real.log Real.pi)))

noncomputable def Ns324p381 := @Enclosure.Real.IsNear.addLit_ft_p qz64 (Enclosure.sfrac Bool.true Ns324p377 Ns324p378) 53286681051751726117 45035996273704960 409858971370648417 45056000000000000000000 Ns324p377 Ns324p378 0 1 Ns324p380 

noncomputable def Ns324p382 := nat_lit 89400215792834588743775027200000 

noncomputable abbrev qz65 := (@HSub.hSub Real Real Real qz354 qz404 qz617)

noncomputable def Ns324p383 := @Enclosure.Real.IsNear.subLit_ff_p qz65 (@HMul.hMul Real Real Real qz5 qz617 (Real.log Real.pi)) 1751290503425517739933 1125899906842624000 46760184868227 11000000000000000000 24981705971463 67108864000 650383 134217728000 Ns324p382 53286681051751726117 45035996273704960 

noncomputable def Ns324p384 := nat_lit 3502581006851035479866000 

noncomputable abbrev qz66 := qz404

noncomputable def Ns324p385 := @Enclosure.Real.IsNear.subLit_ff_p qz66 qz617 2117423582981530902429 1125899906842624000 46760184868227 11000000000000000000 650383 2000 0 1 Ns324p384 1751290503425517739933 1125899906842624000 46760184868227 11000000000000000000 

noncomputable def Ns324p386 := nat_lit 4768014029650561543934271533604667392 

noncomputable def Ns324p387 := nat_lit 55943424644216378718420992 

noncomputable def Ns324p388 := nat_lit 24258117301105831844934693982663245523391706288470195428561322978559893133368502933087922271720274999438943232534993170569021095110629597986508739297935360 

noncomputable def Ns324p389 := nat_lit 461043177770849646318789662838265858356710907610423889337620000194291708642483644374624699828443838770524296234676288030744431496545325434788787301384192 

noncomputable def Ns324p390 := nat_lit 52328270744995144180774533029822604428284739450634282294305323549596392454018326464636684236640771680061896152918811703244425583488090220758302720 

noncomputable def Ns324p391 := BSN.log_dyadic_bound 643417186756 2740569186756 7 6 Ns324p388 134217728 38720000 Ns324p389 Ns324p390 64219717 3383986373512 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 643417186756) (BSN.artanhQ 2740569186756) 0 6 Ns324p389 Ns324p388 Ns324p390 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz405 := (Real.log (Enclosure.sfrac Bool.false 1691993186756 16000000))

noncomputable def Ns324p392 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 650383 4000) qz405 650383 4000 0 1 3256335892028663 281474976710656 195312621 7562500000000000 2117865506465277927929 1125899906842624000 127028008383843 30250000000000000000 (Enclosure.Real.IsNear.const Bool.false 650383 4000) (BSN.isNear_log_sfrac 1691993186756 16000000 3256335892028663 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1691993186756) qz357)) Bool.false Ns324p387 Ns324p98 1000000619520000 38720000000000000000000 3256335892028663 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1691993186756 16000000 16 3383986373512 2097152000000 64219717 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns324p391 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns324p393 := BSN.arctan_dyadic_bound_f 1000 1300766 1 0 16777216 4840000 0 1 1 0 1 1 12897 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1300766) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1300766) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz406 := (@Nat.cast Real Real.instNatCast 1300766)

noncomputable def Ns324p394 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz406)) 884279719003555 562949953421312 1 2000000000000000 12897 16777216 1 4840000 14828491484592672342016 883846967494051 562949953421312 50000000121 242000000000000000 qz15 (Ns324p393 rfl) rfl rfl 

noncomputable abbrev qz407 := (@HMul.hMul Real Real Real qz582 qz587 qz616)

noncomputable abbrev qz67 := qz407

noncomputable abbrev qz408 := qz616

noncomputable abbrev qz68 := qz408

noncomputable def Ns324p395 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 650383 4000) qz405) qz67 2117865506465277927929 1125899906842624000 127028008383843 30250000000000000000 883846967494051 2251799813685248 50000000121 968000000000000000 Ns324p386 2117423582981530902429 1125899906842624000 46760184868227 11000000000000000000 (Ns324p392 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz68 1 4 0 1 883846967494051 562949953421312 50000000121 242000000000000000 883846967494051 2251799813685248 50000000121 968000000000000000 qz365 Ns324p394 rfl) 

noncomputable def Ns324p396 := @Ns324p381 Ns324p375 Ns324p376 409858971370648417 45056000000000000000000 (@Ns324p383 409858971370648417 45056000000000000000000 (Ns324p385 (Ns324p395 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 650383 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz617 (Real.log Real.pi) 650383 2000 0 1 38410761 33554432 1 67108864 24981705971463 67108864000 650383 134217728000 (Enclosure.Real.IsNear.const Bool.false 650383 2000) RS325to336.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns324p377 Ns324p378) 

noncomputable def Ns324p397 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz60) Bool.false Ns324p375 Ns324p376 409858971370648417 45056000000000000000000 39701662593 33554432 153 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz60) (@HAdd.hAdd Real Real Real qz366 qz64 (Enclosure.sfrac Bool.true Ns324p377 Ns324p378)) Bool.false Ns324p375 Ns324p376 409858971370648417 45056000000000000000000 Ns324p379 (Ns324p396 rfl rfl)) 

noncomputable def Ns324p398 := nat_lit 1896146218041040139452416 

noncomputable def Ns324p399 := nat_lit 527191129779520744201483209288207082331041 

noncomputable def Ns324p400 := nat_lit 2676089423823674776984286192717803380717649920 

noncomputable def Ns324p401 := nat_lit 18732625966765723438890003349024623665023549440 

noncomputable def Ns324p402 := BSN.sin_dyadic_bound_f 26945858423 68719476736 2 1 33554432 9689454 Ns324p399 Ns324p400 Ns324p399 Ns324p399 Ns324p401 Ns324p399 12822580 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 26945858423) qz593 0 1 Ns324p399 Ns324p400 Ns324p399 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 26945858423) qz594 0 1 Ns324p399 Ns324p401 Ns324p399 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz409 := (@Nat.cast Real Real.instNatCast Ns324p98)

noncomputable def Ns324p403 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz60) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39701662593) qz391) Bool.false 39701662593 33554432 153 16777216 Bool.true 12822580 33554432 1 4840000 (Ns324p397 rfl) (Enclosure.sfrac_false_div 39701662593 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39701662593) qz391) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns324p398) qz409) 226375608064910080 72057594037927936 Bool.false 12822580 33554432 188 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q1 39701662593 33554432 226375608064910080 72057594037927936 188 Ns324p398 Ns324p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 12822580 33554432 Ns324p398 Ns324p98 26945858423 68719476736 9689454 9680000 (Ns324p402 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns324p404 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz60) Bool.false Ns324p375 Ns324p376 409858971370648417 45056000000000000000000 317613300745 268435456 2443 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz60) (@HAdd.hAdd Real Real Real qz366 qz64 (Enclosure.sfrac Bool.true Ns324p377 Ns324p378)) Bool.false Ns324p375 Ns324p376 409858971370648417 45056000000000000000000 Ns324p379 (Ns324p396 rfl rfl)) 

noncomputable def Ns324p405 := Ns324p374 52453 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 466 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 247291980 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 298 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 223692248 268435456) qz63 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 1) Bool.true 3205645 8388608 11832769 1268776960000 102580640 268435456 2504 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz60)) Bool.true 3205645 8388608 11832769 1268776960000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz60) qz60) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz60)) Bool.true 12822580 33554432 757297216 81201725440000 3205645 8388608 11832769 1268776960000 (Ns324p403 rfl rfl) rfl)) rfl) (Ns324p404 rfl) RS325to336.d7 

noncomputable def Ns324p406 := nat_lit 1154353185824181707745066221881193630608333317871280439724847719776256 

noncomputable def Ns324p407 := nat_lit 17511632836496439940514247388486554680512676136169359405771390976 

noncomputable def Ns324p408 := nat_lit 3463024534206872130355317637148803918715638928261568980455731616546816 

noncomputable def Ns324p409 := BSN.cos_dyadic_bound_f 107254576 268435456 3 2 268435456 134217728 Ns324p406 Ns324p263 Ns324p407 Ns324p408 Ns324p266 Ns324p407 247291980 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 107254576) qz369 0 2 Ns324p406 Ns324p263 Ns324p407 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 107254576) qz370 0 2 Ns324p408 Ns324p266 Ns324p407 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p410 := nat_lit 5330844413115366401775175758517729369189228390854146549287014775145761 

noncomputable def Ns324p411 := nat_lit 373416562874095285102252400794500565892499648979473252221619029281 

noncomputable def Ns324p412 := nat_lit 15991786406220351014755322770751599106435900173264480701356601087378721 

noncomputable def Ns324p413 := BSN.cos_dyadic_bound_f 157225939 268435456 3 2 268435456 134217728 Ns324p410 Ns324p263 Ns324p411 Ns324p412 Ns324p266 Ns324p411 223692248 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 157225939) qz369 0 2 Ns324p410 Ns324p263 Ns324p411 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 157225939) qz370 0 2 Ns324p412 Ns324p266 Ns324p411 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p414 := nat_lit 142413249713583292589213431334416 

noncomputable def Ns324p415 := BSN.sin_dyadic_bound_f 109241486 268435456 2 1 268435456 134217728 Ns324p414 Ns324p270 Ns324p414 Ns324p414 Ns324p271 Ns324p414 106251047 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 109241486) qz367 0 1 Ns324p414 Ns324p270 Ns324p414 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 109241486) qz368 0 1 Ns324p414 Ns324p271 Ns324p414 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p416 := nat_lit 9640275652090965836984895713541440144280911830109318274448233567980737142453972340415913610141723240000000000 

noncomputable def Ns324p417 := nat_lit 5715649223952994748018393104946229688972036297076630394250571513416256084739006172119140625000000000000 

noncomputable def Ns324p418 := nat_lit 58404557331092660078954960336492751573337500473121810870070349744370771634217567993154045611267287656000000000 

noncomputable def Ns324p419 := BSN.cos_dyadic_bound_f 365669550 268435456 4 3 268435456 134217728 Ns324p416 Ns324p125 Ns324p417 Ns324p418 Ns324p128 Ns324p417 55582830 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 365669550) qz369 0 3 Ns324p416 Ns324p125 Ns324p417 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 365669550) qz370 0 3 Ns324p418 Ns324p128 Ns324p417 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p420 := Ns324p372 89294 BSN.abs_quadSignPos (BSN.cos_quad_nat3 179 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 106251047 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 86 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 55582830 268435456) qz63 rfl rfl (Ns324p405 RS325to336.d9 RS325to336.d11 RS325to336.d13 RS325to336.d17 (Ns324p409 rfl rfl) (Ns324p413 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns324p404 rfl) RS325to336.d19 RS325to336.d21 RS325to336.d23 RS325to336.d25 RS325to336.d17 (Ns324p415 rfl rfl) (Ns324p419 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns324p421 := nat_lit 10089873575553731836184957118590474458273304656015404128535724900000000 

noncomputable def Ns324p422 := nat_lit 412908003383424984539523556396895053834330730428368789062500000000 

noncomputable def Ns324p423 := nat_lit 26425190846825724501938014177217076227295304230286317263363654500000000 

noncomputable def Ns324p424 := BSN.sin_dyadic_bound_f 159214150 268435456 3 2 268435456 134217728 Ns324p421 Ns324p249 Ns324p422 Ns324p423 Ns324p252 Ns324p422 150041986 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 159214150) qz367 0 2 Ns324p421 Ns324p249 Ns324p422 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 159214150) qz368 0 2 Ns324p423 Ns324p252 Ns324p422 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p425 := nat_lit 11107163269074798546774287705547211452853057500678516464594397686374656 

noncomputable def Ns324p426 := nat_lit 1620846765436711565696385626405239747519138229417361627679256453376 

noncomputable def Ns324p427 := nat_lit 33318248113693522217191470345388823879064134225576714670527834546217216 

noncomputable def Ns324p428 := BSN.cos_dyadic_bound_f 188893818 268435456 3 2 268435456 134217728 Ns324p425 Ns324p263 Ns324p426 Ns324p427 Ns324p266 Ns324p426 204672238 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 188893818) qz369 0 2 Ns324p425 Ns324p263 Ns324p426 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 188893818) qz370 0 2 Ns324p427 Ns324p266 Ns324p426 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p429 := Ns324p370 120381 BSN.abs_quadSignPos (BSN.cos_quad_nat3 11 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 150041986 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 204672238 268435456) qz63 rfl rfl (Ns324p420 rfl rfl) (Ns324p404 rfl) RS325to336.d27 RS325to336.d29 RS325to336.d31 RS325to336.d33 RS325to336.d17 (Ns324p424 rfl rfl) (Ns324p428 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p430 := nat_lit 145914476474822608488085565320085870518997029699072433838022328445829120 

noncomputable def Ns324p431 := nat_lit 86258228891956404365056933356540494558070711987573128706919556448256 

noncomputable def Ns324p432 := nat_lit 382017306015853188052204483660504785796660106154352684510247276171493376 

noncomputable def Ns324p433 := BSN.sin_dyadic_bound_f 310438136 268435456 3 2 268435456 134217728 Ns324p430 Ns324p249 Ns324p431 Ns324p432 Ns324p252 Ns324p431 245722757 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 310438136) qz367 0 2 Ns324p430 Ns324p249 Ns324p431 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 310438136) qz368 0 2 Ns324p432 Ns324p252 Ns324p431 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p434 := nat_lit 17781826607686164445401622438739751868328517694543909465711909692334336 

noncomputable def Ns324p435 := nat_lit 4153481124672604728362831486148411069253172003400407947931202969856 

noncomputable def Ns324p436 := nat_lit 53337172860809148126748141653246958782847046739624927581239866671063296 

noncomputable def Ns324p437 := BSN.cos_dyadic_bound_f 212471914 268435456 3 2 268435456 134217728 Ns324p434 Ns324p263 Ns324p435 Ns324p436 Ns324p266 Ns324p435 188647064 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 212471914) qz369 0 2 Ns324p434 Ns324p263 Ns324p435 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 212471914) qz370 0 2 Ns324p436 Ns324p266 Ns324p435 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p438 := Ns324p368 147096 BSN.abs_quadSignPos (BSN.cos_quad_nat3 107 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 245722757 268435456) BSN.abs_quadSignPos qz595 (BSN.sfrac_eq_quadSignPos_mul Bool.false 188647064 268435456) qz63 rfl rfl (Ns324p429 rfl) (Ns324p404 rfl) RS325to336.d35 RS325to336.d37 RS325to336.d39 RS325to336.d41 RS325to336.d17 (Ns324p433 rfl rfl) (Ns324p437 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p439 := nat_lit 8502845630047775727916380741136 

noncomputable def Ns324p440 := BSN.cos_dyadic_bound_f 53999666 268435456 2 1 268435456 134217728 Ns324p439 Ns324p149 Ns324p439 Ns324p439 Ns324p150 Ns324p439 263022341 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 53999666) qz369 0 1 Ns324p439 Ns324p149 Ns324p439 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 53999666) qz370 0 1 Ns324p439 Ns324p150 Ns324p439 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p441 := Ns324p366 Bool.true 89951451 147096 Bool.true 53999666 14148475504056880 1 Bool.false 263022341 Bool.false Bool.true 6776485 159396 BSN.abs_quadSignPos qz596 (BSN.sfrac_eq_quadSignPos_mul Bool.false 263022341 268435456) qz63 rfl (Ns324p438 rfl) (Ns324p404 rfl) RS325to336.d43 RS325to336.d45 RS325to336.d17 (Ns324p440 rfl rfl) rfl 

noncomputable def Ns324p442 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) 6776485 268435456 159396 268435456 6776485 268435456 159396 268435456 3638097682104320 6776485 134217728 39849 33554432 (Ns324p441 rfl rfl rfl rfl) 

noncomputable def Ns324p443 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz61) (Zeta.RiemannSiegel.correction qz62) 10519681 33554432 1 33554432 20789542425293 35184372088832 69512954430697 2660818139217920000 218699354450048691533 1180591620717411303424 

noncomputable def Ns324p444 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz61 1 1 0 1 10519681 33554432 1 33554432 10519681 33554432 1 33554432 

noncomputable abbrev qz69 := qz401

noncomputable def Ns324p445 := @Enclosure.Real.IsNear.sqrt_image qz69 3473274805199 33554432000 650383 33554432000 170692517 170692549 16777216 (@Enclosure.Real.IsNear.of_eq qz69 (@HMul.hMul Real Real Real qz5 qz60 qz3) Bool.false 3473274805199 33554432000 650383 33554432000 (BSN.t_div_two_pi_mk qz60 650383 1000 qz63) (@Enclosure.Real.IsNear.mulLit_ff qz60 qz3 650383 1000 0 1 5340353 33554432 1 33554432 3473274805199 33554432000 650383 33554432000 (Enclosure.Real.IsNear.const Bool.false 650383 1000) RS325to336.d48 rfl)) 

noncomputable abbrev qz739 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 650383 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz618 := qz739

noncomputable abbrev qz410 := qz618

noncomputable abbrev qz70 := qz410

noncomputable def Ns324p446 := @Enclosure.Real.IsNear.sqrt_image qz70 170692533 16777216 1 1048576 53513972 53513978 16777216 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 341385066 33554432 32 33554432 170692533 16777216 1 1048576 (Ns324p445 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns324p447 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz70) 53513975 16777216 3 16777216 5259840 5259841 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz70) Bool.false 107027950 33554432 6 33554432 53513975 16777216 3 16777216 (Ns324p446 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns324p448 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz70)) Bool.false 10519681 33554432 1 33554432 10519681 33554432 1 33554432 (Ns324p447 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz71 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz402))

noncomputable abbrev qz619 := (@HMul.hMul Real Real Real qz723 qz738 qz738)

noncomputable abbrev qz411 := (@HSub.hSub Real Real Real qz586 (@HSub.hSub Real Real Real qz586 qz619 qz614) qz600)

noncomputable abbrev qz72 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz411))

noncomputable def Ns324p449 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz62) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz71) qz72) Bool.false 20789542425293 

noncomputable def Ns324p450 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz71) qz72 36535633 16777216 31 

noncomputable def Ns324p451 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz71) Bool.false 73071266 33554432 992 33554432 36535633 16777216 31 

noncomputable def Ns324p452 := @Enclosure.Real.IsNear.recentre' qz71 Bool.false 7704122 16777216 505617216 81201725440000 3852061 8388608 7900269 1268776960000 

noncomputable abbrev qz73 := (@HMul.hMul Real Real Real qz349 qz346 qz402)

noncomputable def Ns324p453 := @Enclosure.Real.IsNear.cos_image qz73 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 36698489) qz391) Bool.false 36698489 33554432 101 16777216 Bool.false 7704122 16777216 1 

noncomputable def Ns324p454 := nat_lit 26986075410611908771059143 

noncomputable def Ns324p455 := nat_lit 4503599627370496000000000000000 

noncomputable def Ns324p456 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz62 884279719003555 140737488355328 1 500000000000000 2920373 16777216 1 1048576 2582426615825568926015 2361183241434822606848 Ns324p454 

noncomputable def Ns324p457 := @Enclosure.Real.IsNear.subLit_ff_p qz70 qz1 170692533 16777216 1 1048576 10 1 0 1 2920373 2920373 16777216 1 

noncomputable def Ns324p458 := @Ns324p457 1048576 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 341385066 33554432 32 33554432 170692533 16777216 1 1048576 (Ns324p445 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns324p459 := @Enclosure.Real.IsNear.recentre' qz73 Bool.false 2582426615825568926015 2361183241434822606848 Ns324p454 Ns324p455 36698489 33554432 101 16777216 (@Ns324p456 Ns324p455 RS325to336.d47 (Ns324p458 rfl rfl) rfl) 

noncomputable def Ns324p460 := nat_lit 3866084214528527739149337858968099767855104377007494874179117761 

noncomputable def Ns324p461 := nat_lit 3289920974164603416504499257575408982778592530060692197810881 

noncomputable def Ns324p462 := nat_lit 11591672801637254010615004578389148485599755945962363238141731521 

noncomputable def Ns324p463 := BSN.cos_dyadic_bound_f 36698489 33554432 3 2 16777216 4840000 Ns324p460 Ns324p308 Ns324p461 Ns324p462 Ns324p311 Ns324p461 7704122 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 36698489) qz392 0 2 Ns324p460 Ns324p308 Ns324p461 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 36698489) (BSN.cosOddQ 33554432) 0 2 Ns324p462 Ns324p311 Ns324p461 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p464 := @Enclosure.Real.IsNear.inv_image qz71 3852061 8388608 7900269 1268776960000 36535137 36536129 16777216 (Ns324p452 (@Ns324p453 4840000 (Ns324p459 rfl) (Enclosure.sfrac_false_div 36698489 33554432) (Ns324p463 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns324p465 := @Enclosure.Real.IsNear.recentre' qz72 Bool.false 4552168 16777216 

noncomputable abbrev qz74 := (@HMul.hMul Real Real Real qz349 qz346 qz411)

noncomputable def Ns324p466 := @Enclosure.Real.IsNear.cos_image qz74 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 21743629)) qz374) Bool.true 21743629 16777216 

noncomputable def Ns324p467 := nat_lit 51340693506530666213960369525 

noncomputable def Ns324p468 := nat_lit 39614081257132168796771975168 

noncomputable def Ns324p469 := nat_lit 305185229969634794957750273195243 

noncomputable def Ns324p470 := @Enclosure.Real.IsNear.recentre' qz74 Bool.true Ns324p467 Ns324p468 Ns324p469 

noncomputable def Ns324p471 := nat_lit 37778931862957161709568000000000000000 

noncomputable abbrev qz75 := qz411

noncomputable def Ns324p472 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz75 884279719003555 140737488355328 1 500000000000000 58059336206855 

noncomputable abbrev qz412 := (@HSub.hSub Real Real Real qz586 qz619 qz614)

noncomputable abbrev qz76 := qz412

noncomputable def Ns324p473 := @Enclosure.Real.IsNear.subLit_tf qz76 qz29 40467150162439 281474976710656 11308989 8796093022208 1 16 

noncomputable abbrev qz413 := qz619

noncomputable abbrev qz77 := qz413

noncomputable def Ns324p474 := @Enclosure.Real.IsNear.subLit_ff_n qz77 qz62 8528578459129 281474976710656 2920381 8796093022208 2920373 16777216 1 1048576 

noncomputable def Ns324p475 := @Enclosure.Real.IsNear.mulLit_ff qz62 qz62 2920373 16777216 1 1048576 2920373 16777216 1 1048576 8528578459129 281474976710656 

noncomputable def Ns324p476 := nat_lit 29802019884785327975956698760981371797103833219296736287019041 

noncomputable def Ns324p477 := nat_lit 49963888961687030232405634748957574372270089774483997872161 

noncomputable def Ns324p478 := nat_lit 89306131876432609867405285013446200242566959478341240865312801 

noncomputable def Ns324p479 := BSN.cos_dyadic_bound_f 21743629 16777216 3 2 16777216 4840000 Ns324p476 Ns324p179 Ns324p477 Ns324p478 Ns324p182 Ns324p477 4552168 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 21743629) qz601 0 2 Ns324p476 Ns324p179 Ns324p477 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 21743629) (BSN.cosOddQ 16777216) 0 2 Ns324p478 Ns324p182 Ns324p477 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p480 := @Ns324p465 84377152 10150215680000 569021 2097152 1318393 158597120000 (@Ns324p466 17 2097152 Bool.false 4552168 16777216 1 4840000 (@Ns324p470 Ns324p471 21743629 16777216 17 2097152 (@Ns324p472 281474976710656 11308989 8796093022208 Ns324p467 Ns324p468 Ns324p469 Ns324p471 RS325to336.d47 (@Ns324p473 0 1 928949379309680 58059336206855 281474976710656 11308989 8796093022208 (@Ns324p474 678926119179674189824 40467150162439 281474976710656 11308989 8796093022208 (@Ns324p475 2920381 8796093022208 (Ns324p458 rfl rfl) (Ns324p458 rfl rfl) rfl) (Ns324p458 rfl rfl) rfl rfl) qz379 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 21743629 16777216) (BSN.cos_neg_of_bound 21743629 16777216 Bool.false 4552168 16777216 1 4840000 (Ns324p479 rfl rfl)) rfl rfl) 

noncomputable def Ns324p481 := @Ns324p443 732826384637336261479 Ns324p363 (Ns324p444 qz31 (@Enclosure.Real.IsNear.of_eq qz61 (@Inv.inv Real Real.instInv (Real.sqrt qz70)) Bool.false 10519681 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz69 (BSN.t_div_two_pi_nonneg qz60 650383 1000 qz63)) Ns324p448) rfl) (@Ns324p449 35184372088832 69512954430697 2660818139217920000 (BSN.correction_mk qz62 (BSN.cos_two_pi_p_ne_zero_mk qz60 650383 1000 10 qz63 rfl rfl (@BSN.floor_sqrt_eq_dec qz60 650383 1000 10 qz63 rfl rfl rfl))) (@Ns324p450 1048576 569021 2097152 1318393 158597120000 20789542425293 35184372088832 69512954430697 2660818139217920000 (@Ns324p451 1048576 (Ns324p464 rfl rfl rfl rfl rfl) rfl) (Ns324p480 rfl) rfl)) 

noncomputable def Ns324p482 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz60) (hardyZApproximantRS₀ qz60) Bool.true 278305946873645870413 1180591620717411303424 106763768414332230341479 Ns324p363 (@Eq.refl Real (hardyZApproximantRS₀ qz60)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz60) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz61) (Zeta.RiemannSiegel.correction qz62))) Bool.true 278305946873645870413 1180591620717411303424 106763768414332230341479 Ns324p363 (BSN.hardyZApproximantRS₀_eq qz60 10 (@BSN.floor_sqrt_eq_dec qz60 650383 1000 10 qz63 rfl rfl rfl)) (@Ns324p365 278305946873645870413 1180591620717411303424 106763768414332230341479 Ns324p363 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (@HAdd.hAdd Real Real Real qz366 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 10)) Bool.true 6776485 134217728 39849 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (Ns324p442 (Ns324p441 rfl rfl rfl rfl) rfl rfl)) (Ns324p481 rfl) rfl rfl)) 

theorem RS325to336.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz60) Bool.true 278305946873645870413 1180591620717411303424 106763768414332230341479 Ns324p363 := Ns324p482 

noncomputable def Ns324p483 := nat_lit 71425793053403383857152000 

noncomputable def Ns324p484 := nat_lit 2894697718003438719334149521408 

noncomputable abbrev qz740 := (Enclosure.sfrac Bool.false 652160 1000)

noncomputable abbrev qz620 := qz740

noncomputable abbrev qz414 := qz620

noncomputable abbrev qz78 := qz414

noncomputable abbrev qz741 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 652160 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz621 := qz741

noncomputable abbrev qz415 := qz621

noncomputable abbrev qz79 := (@HPow.hPow Real Real Real qz584 qz415 qz351)

noncomputable abbrev qz742 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 652160 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz622 := qz742

noncomputable abbrev qz416 := qz622

noncomputable abbrev qz80 := qz416

noncomputable def Ns324p485 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz79) (Zeta.RiemannSiegel.correction qz80)) 1250001953 134217728 79917 67108864 423088261343241195637 2361183241434822606848 732337002828051360347 Ns324p483 Ns324p484 

noncomputable def Ns324p486 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.cos BSN.quadSignPos 9 10 652160 1000 200 268435456 134217728 4503599627370496 Bool.false 318720213874 2450 618095470 56 84886744 8 

noncomputable def Ns324p487 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 652160 1000 107 156 268435456 134217728 4503599627370496 Bool.false 318720213874 2450 

noncomputable def Ns324p488 := Ns324p487 558195838 56 94906264 8 589812974 56 89478488 8 Bool.false 1027960140 120712 Bool.true 195439011 Bool.true 153656440 14148475504056880 1 Bool.false 178624470 Bool.false Bool.false 225645607 Bool.false Bool.false 1166328630 

noncomputable def Ns324p489 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 652160 1000 11 52 268435456 134217728 4503599627370496 Bool.false 318720213874 2450 

noncomputable def Ns324p490 := Ns324p489 480971758 57 109588312 8 522351262 57 101459064 8 Bool.false 817065354 89540 Bool.false 411440465 Bool.true 10198882 14148475504056880 1 Bool.false 268241044 Bool.false Bool.false 268241732 Bool.false Bool.false 1027960140 

noncomputable def Ns324p491 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 652160 1000 180 87 268435456 134217728 4503599627370496 Bool.false 318720213874 2450 

noncomputable def Ns324p492 := Ns324p491 372130544 56 134217720 8 432030192 56 120047984 16 Bool.false 594608583 52598 Bool.false 133221211 Bool.false 283207600 14148475504056880 1 Bool.false 236050406 Bool.false Bool.false 233516105 Bool.false Bool.false 817065354 

noncomputable def Ns324p493 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 652160 1000 468 299 268435456 134217728 4503599627370496 Bool.false 318720213874 2450 

noncomputable def Ns324p494 := Ns324p493 186065264 56 189812528 16 294906480 56 154981288 8 Bool.false 263259040 2512 Bool.false 40214875 Bool.false 318432825 14148475504056880 1 Bool.false 265428748 Bool.false Bool.false 248831744 Bool.false Bool.false 594608583 

noncomputable def Ns324p495 := nat_lit 723148960660572731781124773259192791152065378669 

noncomputable def Ns324p496 := nat_lit 609057137138518111933749973293703034516275200 

noncomputable def Ns324p497 := nat_lit 56625581386516153740443648000000000 

noncomputable def Ns324p498 := nat_lit 221573695721787994237729425838080000000 

noncomputable abbrev qz623 := (@Eq.refl Real qz740)

noncomputable abbrev qz417 := qz623

noncomputable abbrev qz81 := qz417

noncomputable def Ns324p499 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz78 652160 1000 1701251662400 16000000 1304320 4000 2000 Ns324p497 Ns324p498 qz81 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns324p500 := nat_lit 14810090714328529546877435356348268362794298955141120000000 

noncomputable abbrev qz624 := (@HSub.hSub Real Real Real qz727 qz728 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz729 (@Nat.cast Real Real.instNatCast 1304320))))

noncomputable abbrev qz418 := (@HSub.hSub Real Real Real qz586 (@HMul.hMul Real Real Real qz582 (Enclosure.sfrac Bool.false 652160 4000) (Real.log (Enclosure.sfrac Bool.false 1701251662400 16000000))) (@HMul.hMul Real Real Real qz582 qz587 qz624))

noncomputable abbrev qz625 := (Enclosure.sfrac Bool.false 652160 2000)

noncomputable abbrev qz82 := (@HSub.hSub Real Real Real qz354 (@HSub.hSub Real Real Real qz354 qz418 qz625) (@HMul.hMul Real Real Real qz349 qz625 (Real.log Real.pi)))

noncomputable def Ns324p501 := @Enclosure.Real.IsNear.addLit_ft_p qz82 (Enclosure.sfrac Bool.true Ns324p497 Ns324p498) 66840487783627511989 56294995342131200 7063588885461991 774400000000000000000 Ns324p497 Ns324p498 0 1 Ns324p500 

noncomputable def Ns324p502 := nat_lit 7008733131820500201137766400 

noncomputable abbrev qz83 := (@HSub.hSub Real Real Real qz354 qz418 qz625)

noncomputable def Ns324p503 := @Enclosure.Real.IsNear.subLit_ff_p qz83 (@HMul.hMul Real Real Real qz5 qz625 (Real.log Real.pi)) 87853918857796540597 56294995342131200 103150063132113 24200000000000000000 39140565459 104857600 1019 209715200 Ns324p502 66840487783627511989 56294995342131200 

noncomputable abbrev qz84 := qz418

noncomputable def Ns324p504 := @Enclosure.Real.IsNear.subLit_ff_p qz84 qz625 106210590938958682293 56294995342131200 103150063132113 24200000000000000000 652160 2000 0 1 175707837715593081194000 87853918857796540597 56294995342131200 103150063132113 24200000000000000000 

noncomputable def Ns324p505 := nat_lit 7473905902742101569432605322903552 

noncomputable def Ns324p506 := nat_lit 55969813179988181478539264 

noncomputable def Ns324p507 := nat_lit 25260012676573860061670959570398758205473973406672330628381857167600915674068247662813355827446558101661763203020264834925865205760000000000000000000000000 

noncomputable def Ns324p508 := nat_lit 491055473661072336001543279378001480646788298615888645321612215896454501854521902816269072564701251413503654441356036766613635072000000000000000000000000 

noncomputable def Ns324p509 := nat_lit 62114574842680087883841877715265946414744909219958529837808863792556352124589200042066439798842838383108831518328902123520000000000000000000000000 

noncomputable def Ns324p510 := BSN.log_dyadic_bound 652675662400 2749827662400 7 6 Ns324p507 134217728 38720000 Ns324p508 Ns324p509 64952146 3402503324800 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 652675662400) (BSN.artanhQ 2749827662400) 0 6 Ns324p508 Ns324p507 Ns324p509 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz419 := (Real.log (Enclosure.sfrac Bool.false 1701251662400 16000000))

noncomputable def Ns324p511 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 652160 4000) qz419 652160 4000 0 1 3257871906970871 281474976710656 195312621 7562500000000000 3319771473203317549 1759218604441600 199023560799 47265625000000000 (Enclosure.Real.IsNear.const Bool.false 652160 4000) (BSN.isNear_log_sfrac 1701251662400 16000000 3257871906970871 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1701251662400) qz357)) Bool.false Ns324p506 Ns324p98 1000000619520000 38720000000000000000000 3257871906970871 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1701251662400 16000000 16 3402503324800 2097152000000 64952146 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns324p510 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns324p512 := BSN.arctan_dyadic_bound_f 1000 1304320 1 0 16777216 4840000 0 1 1 0 1 1 12862 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1304320) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1304320) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz420 := (@Nat.cast Real Real.instNatCast 1304320)

noncomputable def Ns324p513 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz420)) 884279719003555 562949953421312 1 2000000000000000 12862 16777216 1 4840000 14828511187841042087936 883848141899171 562949953421312 50000000121 242000000000000000 qz15 (Ns324p512 rfl) rfl rfl 

noncomputable abbrev qz421 := (@HMul.hMul Real Real Real qz582 qz587 qz624)

noncomputable abbrev qz85 := qz421

noncomputable abbrev qz422 := qz624

noncomputable abbrev qz86 := qz422

noncomputable def Ns324p514 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 652160 4000) qz419) qz85 3319771473203317549 1759218604441600 199023560799 47265625000000000 883848141899171 2251799813685248 50000000121 968000000000000000 Ns324p505 106210590938958682293 56294995342131200 103150063132113 24200000000000000000 (Ns324p511 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz86 1 4 0 1 883848141899171 562949953421312 50000000121 242000000000000000 883848141899171 2251799813685248 50000000121 968000000000000000 qz365 Ns324p513 rfl) 

noncomputable def Ns324p515 := @Ns324p501 Ns324p495 Ns324p496 7063588885461991 774400000000000000000 (@Ns324p503 7063588885461991 774400000000000000000 (Ns324p504 (Ns324p514 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 652160 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz625 (Real.log Real.pi) 652160 2000 0 1 38410761 33554432 1 67108864 39140565459 104857600 1019 209715200 (Enclosure.Real.IsNear.const Bool.false 652160 2000) RS325to336.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns324p497 Ns324p498) 

noncomputable def Ns324p516 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz78) Bool.false Ns324p495 Ns324p496 7063588885461991 774400000000000000000 19920013367 16777216 307 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz78) (@HAdd.hAdd Real Real Real qz366 qz82 (Enclosure.sfrac Bool.true Ns324p497 Ns324p498)) Bool.false Ns324p495 Ns324p496 7063588885461991 774400000000000000000 Ns324p499 (Ns324p515 rfl rfl)) 

noncomputable def Ns324p517 := nat_lit 3322355263332463488794624 

noncomputable def Ns324p518 := nat_lit 2417851639229258349412352 

noncomputable def Ns324p519 := nat_lit 5367819703625301574283612641710433838331760833903347624526677699705773388040278161645618305 

noncomputable def Ns324p520 := nat_lit 180468656028383376705345110207518346455653528001341539704795567934989718275908111313435361280 

noncomputable def Ns324p521 := nat_lit 6320771967246692251005347568678834242682782324380183704916149289467972631779238985843841 

noncomputable def Ns324p522 := nat_lit 14048341783452628526145929213178037178285506250745485385857148781332172632034990703094776961 

noncomputable def Ns324p523 := nat_lit 3308592027187028572931327020471169685020314680024594894587918745474811501724982040746314956800 

noncomputable def Ns324p524 := BSN.sin_dyadic_bound_f 94427015919 68719476736 3 2 33554432 9689454 Ns324p519 Ns324p520 Ns324p521 Ns324p522 Ns324p523 Ns324p521 32907380 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 94427015919) qz593 0 2 Ns324p519 Ns324p520 Ns324p521 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 94427015919) qz594 0 2 Ns324p522 Ns324p523 Ns324p521 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz626 := (@Nat.cast Real Real.instNatCast Ns324p518)

noncomputable def Ns324p525 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz78) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 19920013367) qz374) Bool.false 19920013367 16777216 307 33554432 Bool.false 32907380 33554432 1 4840000 (Ns324p516 rfl) (Enclosure.sfrac_false_div 19920013367 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 19920013367) qz374) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns324p517) qz626) 226375608064910080 72057594037927936 Bool.false 32907380 33554432 188 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q3 19920013367 16777216 226375608064910080 72057594037927936 188 Ns324p517 Ns324p518 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 32907380 33554432 Ns324p517 Ns324p518 94427015919 68719476736 9689454 9680000 (Ns324p524 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns324p526 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz78) Bool.false Ns324p495 Ns324p496 7063588885461991 774400000000000000000 318720213874 268435456 2450 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz78) (@HAdd.hAdd Real Real Real qz366 qz82 (Enclosure.sfrac Bool.true Ns324p497 Ns324p498)) Bool.false Ns324p495 Ns324p496 7063588885461991 774400000000000000000 Ns324p499 (Ns324p515 rfl rfl)) 

noncomputable def Ns324p527 := Ns324p494 52598 BSN.abs_quadSignPos (BSN.cos_quad_nat0 468 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 265428748 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 299 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 248831744 268435456) qz81 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 1) Bool.false 8226845 8388608 23741163 2537553920000 263259040 268435456 2512 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz78)) Bool.false 8226845 8388608 23741163 2537553920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz78) qz78) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz78)) Bool.false 32907380 33554432 1519434432 162403450880000 8226845 8388608 23741163 2537553920000 (Ns324p525 rfl rfl) rfl)) rfl) (Ns324p526 rfl) RS325to336.d7 

noncomputable def Ns324p528 := nat_lit 2615452833649897956914306640625 

noncomputable def Ns324p529 := BSN.cos_dyadic_bound_f 40214875 268435456 2 1 268435456 134217728 Ns324p528 Ns324p149 Ns324p528 Ns324p528 Ns324p150 Ns324p528 265428748 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 40214875) qz369 0 1 Ns324p528 Ns324p149 Ns324p528 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 40214875) qz370 0 1 Ns324p528 Ns324p150 Ns324p528 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p530 := nat_lit 161546263373253068255750859546359191350415595188939974494563817487890625 

noncomputable def Ns324p531 := nat_lit 105716466301073929612124339466129857501468363213119122851715087890625 

noncomputable def Ns324p532 := nat_lit 422926196460699154307594526071805100434181324335354883191621507087890625 

noncomputable def Ns324p533 := BSN.sin_dyadic_bound_f 318432825 268435456 3 2 268435456 134217728 Ns324p530 Ns324p249 Ns324p531 Ns324p532 Ns324p252 Ns324p531 248831744 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 318432825) qz367 0 2 Ns324p530 Ns324p249 Ns324p531 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 318432825) qz368 0 2 Ns324p532 Ns324p252 Ns324p531 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p534 := nat_lit 2747754872345226694233914197546729998029576075142952598823601409844961 

noncomputable def Ns324p535 := nat_lit 99217211518601700081622532650647393010999747757561055120187680481 

noncomputable def Ns324p536 := nat_lit 8243066182612642879301579347574888699302706225933342674360563854173921 

noncomputable def Ns324p537 := BSN.cos_dyadic_bound_f 133221211 268435456 3 2 268435456 134217728 Ns324p534 Ns324p263 Ns324p535 Ns324p536 Ns324p266 Ns324p535 236050406 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 133221211) qz369 0 2 Ns324p534 Ns324p263 Ns324p535 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 133221211) qz370 0 2 Ns324p536 Ns324p266 Ns324p535 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p538 := nat_lit 101050581003165069769708419853922671642068501111858809977333350400000000 

noncomputable def Ns324p539 := nat_lit 41384644533809899345796009011753273822324496165109760000000000000000 

noncomputable def Ns324p540 := nat_lit 264589279869520442893152667983778444238276596584886705567301632000000000 

noncomputable def Ns324p541 := BSN.sin_dyadic_bound_f 283207600 268435456 3 2 268435456 134217728 Ns324p538 Ns324p249 Ns324p539 Ns324p540 Ns324p252 Ns324p539 233516105 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 283207600) qz367 0 2 Ns324p538 Ns324p249 Ns324p539 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 283207600) qz368 0 2 Ns324p540 Ns324p252 Ns324p539 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p542 := Ns324p492 89540 BSN.abs_quadSignPos (BSN.cos_quad_nat0 180 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 236050406 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 87 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 233516105 268435456) qz81 rfl rfl (Ns324p527 RS325to336.d9 RS325to336.d11 RS325to336.d13 RS325to336.d17 (Ns324p529 rfl rfl) (Ns324p533 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns324p526 rfl) RS325to336.d19 RS325to336.d21 RS325to336.d23 RS325to336.d25 RS325to336.d17 (Ns324p537 rfl rfl) (Ns324p541 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns324p543 := nat_lit 40164121354109673707313589758521780807194583694401287168651659523326082883686415552995243989809544695866290625 

noncomputable def Ns324p544 := nat_lit 23533364728305482440351778942099377439117731879607711537701819860194942592486798192596345734277587890625 

noncomputable def Ns324p545 := nat_lit 200594350943897519415207438882944780885991500768538921250984011639508781426090403884858920101016019904979890625 

noncomputable def Ns324p546 := BSN.sin_dyadic_bound_f 411440465 268435456 4 3 268435456 134217728 Ns324p543 Ns324p119 Ns324p544 Ns324p545 Ns324p122 Ns324p544 268241044 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 411440465) qz367 0 3 Ns324p543 Ns324p119 Ns324p544 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 411440465) qz368 0 3 Ns324p545 Ns324p122 Ns324p544 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p547 := nat_lit 10819576658019544789004405776 

noncomputable def Ns324p548 := BSN.cos_dyadic_bound_f 10198882 268435456 2 1 268435456 134217728 Ns324p547 Ns324p149 Ns324p547 Ns324p547 Ns324p150 Ns324p547 268241732 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 10198882) qz369 0 1 Ns324p547 Ns324p149 Ns324p547 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 10198882) qz370 0 1 Ns324p547 Ns324p150 Ns324p547 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p549 := Ns324p490 120712 BSN.abs_quadSignPos (BSN.cos_quad_nat3 11 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268241044 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268241732 268435456) qz81 rfl rfl (Ns324p542 rfl rfl) (Ns324p526 rfl) RS325to336.d27 RS325to336.d29 RS325to336.d31 RS325to336.d33 RS325to336.d17 (Ns324p546 rfl rfl) (Ns324p548 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p550 := nat_lit 22910083840848176431222613363298804648813461292431979196533097681475745 

noncomputable def Ns324p551 := nat_lit 2128580357291354174445258772037271300386531600400299131579386910881 

noncomputable def Ns324p552 := nat_lit 59999154262595323698824409342056428021929868048064059316135555872676001 

noncomputable def Ns324p553 := BSN.sin_dyadic_bound_f 195439011 268435456 3 2 268435456 134217728 Ns324p550 Ns324p249 Ns324p551 Ns324p552 Ns324p252 Ns324p551 178624470 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 195439011) qz367 0 2 Ns324p550 Ns324p249 Ns324p551 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 195439011) qz368 0 2 Ns324p552 Ns324p252 Ns324p551 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p554 := nat_lit 4862947899961098705458301294588592497097128920869411244217519308800000 

noncomputable def Ns324p555 := nat_lit 310746421361698106832119810340667203456625075234236537241600000000 

noncomputable def Ns324p556 := nat_lit 14588222207040572720161239644145096156884473512457765259578074726400000 

noncomputable def Ns324p557 := BSN.cos_dyadic_bound_f 153656440 268435456 3 2 268435456 134217728 Ns324p554 Ns324p263 Ns324p555 Ns324p556 Ns324p266 Ns324p555 225645607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 153656440) qz369 0 2 Ns324p554 Ns324p263 Ns324p555 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 153656440) qz370 0 2 Ns324p556 Ns324p266 Ns324p555 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p558 := Ns324p488 147500 BSN.abs_quadSignPos (BSN.cos_quad_nat3 107 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 178624470 268435456) BSN.abs_quadSignPos qz595 (BSN.sfrac_eq_quadSignPos_mul Bool.false 225645607 268435456) qz81 rfl rfl (Ns324p549 rfl) (Ns324p526 rfl) RS325to336.d35 RS325to336.d37 RS325to336.d39 RS325to336.d41 RS325to336.d17 (Ns324p553 rfl rfl) (Ns324p557 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p559 := nat_lit 4264193444144841609865369734961 

noncomputable def Ns324p560 := BSN.cos_dyadic_bound_f 45442187 268435456 2 1 268435456 134217728 Ns324p559 Ns324p149 Ns324p559 Ns324p559 Ns324p150 Ns324p559 264598284 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 45442187) qz369 0 1 Ns324p559 Ns324p149 Ns324p559 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 45442187) qz370 0 1 Ns324p559 Ns324p150 Ns324p559 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p561 := Ns324p486 Bool.false 1166328630 147500 Bool.true 45442187 14148475504056880 1 Bool.false 264598284 Bool.false Bool.false 1250001953 159834 BSN.abs_quadSignPos qz596 (BSN.sfrac_eq_quadSignPos_mul Bool.false 264598284 268435456) qz81 rfl (Ns324p558 rfl) (Ns324p526 rfl) RS325to336.d43 RS325to336.d45 RS325to336.d17 (Ns324p560 rfl rfl) rfl 

noncomputable def Ns324p562 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) 1250001953 268435456 159834 268435456 1250001953 268435456 159834 268435456 671089688508891136 1250001953 134217728 79917 67108864 (Ns324p561 rfl rfl rfl rfl) 

noncomputable def Ns324p563 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz79) (Zeta.RiemannSiegel.correction qz80) 2628127 8388608 1 16777216 160984709393131 281474976710656 173579408984743 5321636278435840000 423088261343241195637 2361183241434822606848 

noncomputable def Ns324p564 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz79 1 1 0 1 2628127 8388608 1 16777216 2628127 8388608 1 16777216 

noncomputable abbrev qz87 := qz415

noncomputable def Ns324p565 := @Enclosure.Real.IsNear.sqrt_image qz87 5441819707 52428800 1019 52428800 170925544 170925577 16777216 (@Enclosure.Real.IsNear.of_eq qz87 (@HMul.hMul Real Real Real qz5 qz78 qz3) Bool.false 5441819707 52428800 1019 52428800 (BSN.t_div_two_pi_mk qz78 652160 1000 qz81) (@Enclosure.Real.IsNear.mulLit_ff qz78 qz3 652160 1000 0 1 5340353 33554432 1 33554432 5441819707 52428800 1019 52428800 (Enclosure.Real.IsNear.const Bool.false 652160 1000) RS325to336.d48 rfl)) 

noncomputable abbrev qz743 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 652160 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz627 := qz743

noncomputable abbrev qz423 := qz627

noncomputable abbrev qz88 := qz423

noncomputable def Ns324p566 := @Enclosure.Real.IsNear.sqrt_image qz88 341851121 33554432 33 33554432 53550488 53550494 16777216 (@Enclosure.Real.IsNear.recentre' qz88 Bool.false 341851121 33554432 33 33554432 341851121 33554432 33 33554432 (Ns324p565 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns324p567 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz88) 53550491 16777216 3 16777216 5256253 5256255 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz88) Bool.false 107100982 33554432 6 33554432 53550491 16777216 3 16777216 (Ns324p566 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns324p568 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz88)) Bool.false 10512508 33554432 2 33554432 2628127 8388608 1 16777216 (Ns324p567 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz89 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz416))

noncomputable abbrev qz628 := (@HMul.hMul Real Real Real qz723 qz742 qz742)

noncomputable abbrev qz424 := (@HSub.hSub Real Real Real qz586 (@HSub.hSub Real Real Real qz586 qz628 qz622) qz600)

noncomputable abbrev qz90 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz424))

noncomputable def Ns324p569 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz80) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz89) qz90) Bool.false 160984709393131 

noncomputable def Ns324p570 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz89) qz90 88294837 33554432 1489 

noncomputable def Ns324p571 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz89) Bool.false 88294837 33554432 1489 33554432 88294837 33554432 1489 

noncomputable def Ns324p572 := @Enclosure.Real.IsNear.recentre' qz89 Bool.false 6375797 16777216 65017152 10150215680000 6375797 16777216 1015893 158597120000 

noncomputable abbrev qz91 := (@HMul.hMul Real Real Real qz349 qz346 qz416)

noncomputable def Ns324p573 := @Enclosure.Real.IsNear.cos_image qz91 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39626799) qz391) Bool.false 39626799 33554432 13 2097152 Bool.false 6375797 16777216 1 

noncomputable def Ns324p574 := nat_lit 890540488552628508095336103 

noncomputable def Ns324p575 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz80 884279719003555 140737488355328 1 500000000000000 6306801 33554432 33 33554432 5576976216091339677555 4722366482869645213696 Ns324p574 

noncomputable def Ns324p576 := @Enclosure.Real.IsNear.subLit_ff_p qz88 qz1 341851121 33554432 33 33554432 10 1 0 1 6306801 6306801 33554432 33 

noncomputable def Ns324p577 := @Ns324p576 33554432 (@Enclosure.Real.IsNear.recentre' qz88 Bool.false 341851121 33554432 33 33554432 341851121 33554432 33 33554432 (Ns324p565 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns324p578 := @Enclosure.Real.IsNear.recentre' qz91 Bool.false 5576976216091339677555 4722366482869645213696 Ns324p574 Ns324p173 39626799 33554432 13 2097152 (@Ns324p575 Ns324p173 RS325to336.d47 (Ns324p577 rfl rfl) rfl) 

noncomputable def Ns324p579 := nat_lit 5257355771061752279342072533804832180196942645973085909577841281 

noncomputable def Ns324p580 := nat_lit 6080116995377483204228622460823142771685320359537676881705601 

noncomputable def Ns324p581 := nat_lit 15759907079194501871617760356492850255047457297200182374970112641 

noncomputable def Ns324p582 := BSN.cos_dyadic_bound_f 39626799 33554432 3 2 16777216 4840000 Ns324p579 Ns324p308 Ns324p580 Ns324p581 Ns324p311 Ns324p580 6375797 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 39626799) qz392 0 2 Ns324p579 Ns324p308 Ns324p580 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 39626799) (BSN.cosOddQ 33554432) 0 2 Ns324p581 Ns324p311 Ns324p580 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p583 := @Enclosure.Real.IsNear.inv_image qz89 6375797 16777216 1015893 158597120000 44146674 44148163 16777216 (Ns324p572 (@Ns324p573 4840000 (Ns324p578 rfl) (Enclosure.sfrac_false_div 39626799 33554432) (Ns324p582 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns324p584 := @Enclosure.Real.IsNear.recentre' qz90 Bool.false 3646526 16777216 

noncomputable abbrev qz92 := (@HMul.hMul Real Real Real qz349 qz346 qz424)

noncomputable def Ns324p585 := @Enclosure.Real.IsNear.cos_image qz92 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 45355447)) qz391) Bool.true 45355447 33554432 

noncomputable def Ns324p586 := nat_lit 214185043359890854711645217725 

noncomputable def Ns324p587 := nat_lit 41114532941289934124584850750092277 

noncomputable def Ns324p588 := @Enclosure.Real.IsNear.recentre' qz92 Bool.true Ns324p586 Ns324p188 Ns324p587 

noncomputable abbrev qz93 := qz424

noncomputable def Ns324p589 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz93 884279719003555 140737488355328 1 500000000000000 242214130616095 

noncomputable abbrev qz425 := (@HSub.hSub Real Real Real qz586 qz628 qz622)

noncomputable abbrev qz94 := qz425

noncomputable def Ns324p590 := @Enclosure.Real.IsNear.subLit_tf qz94 qz29 171845386438431 1125899906842624 1523546211 1125899906842624 1 16 

noncomputable abbrev qz426 := qz628

noncomputable abbrev qz95 := qz426

noncomputable def Ns324p591 := @Enclosure.Real.IsNear.subLit_ff_n qz95 qz80 39775738853601 1125899906842624 416249955 1125899906842624 6306801 33554432 33 33554432 

noncomputable def Ns324p592 := @Enclosure.Real.IsNear.mulLit_ff qz80 qz80 6306801 33554432 33 33554432 6306801 33554432 33 33554432 39775738853601 1125899906842624 

noncomputable def Ns324p593 := nat_lit 135989385725902403807190715936934667015444974483669380641819310161101959811321421723628858270026721 

noncomputable def Ns324p594 := nat_lit 975743491921780970500323514261193594148711042915413329552712293065467609596717903600577236539801600 

noncomputable def Ns324p595 := nat_lit 75779793555976734596573473593123083595886538485969082492975864317113791824132901628221852641 

noncomputable def Ns324p596 := nat_lit 823911176443596640475217690439117671406147388677190551251356148103055423123453421608952111109508065 

noncomputable def Ns324p597 := nat_lit 88792657764882068315529439797768617067532704905302612989296818668957552473301329227652528525121945600 

noncomputable def Ns324p598 := BSN.cos_dyadic_bound_f 45355447 33554432 4 3 16777216 4840000 Ns324p593 Ns324p594 Ns324p595 Ns324p596 Ns324p597 Ns324p595 3646526 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 45355447) qz392 0 3 Ns324p593 Ns324p594 Ns324p595 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 45355447) (BSN.cosOddQ 33554432) 0 3 Ns324p596 Ns324p597 Ns324p595 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p599 := @Ns324p584 708897216 81201725440000 1823263 8388608 11076519 1268776960000 (@Ns324p585 143 16777216 Bool.false 3646526 16777216 1 4840000 (@Ns324p588 Ns324p191 45355447 33554432 143 16777216 (@Ns324p589 1125899906842624 1523546211 1125899906842624 Ns324p586 Ns324p188 Ns324p587 Ns324p191 RS325to336.d47 (@Ns324p590 0 1 3875426089857520 242214130616095 1125899906842624 1523546211 1125899906842624 (@Ns324p591 5766174333762055176192 171845386438431 1125899906842624 1523546211 1125899906842624 (@Ns324p592 416249955 1125899906842624 (Ns324p577 rfl rfl) (Ns324p577 rfl rfl) rfl) (Ns324p577 rfl rfl) rfl rfl) qz379 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 45355447 33554432) (BSN.cos_neg_of_bound 45355447 33554432 Bool.false 3646526 16777216 1 4840000 (Ns324p598 rfl rfl)) rfl rfl) 

noncomputable def Ns324p600 := @Ns324p563 732337002828051360347 Ns324p483 (Ns324p564 qz31 (@Enclosure.Real.IsNear.of_eq qz79 (@Inv.inv Real Real.instInv (Real.sqrt qz88)) Bool.false 2628127 8388608 1 16777216 (BSN.rpow_neg_quarter_mk qz87 (BSN.t_div_two_pi_nonneg qz78 652160 1000 qz81)) Ns324p568) rfl) (@Ns324p569 281474976710656 173579408984743 5321636278435840000 (BSN.correction_mk qz80 (BSN.cos_two_pi_p_ne_zero_mk qz78 652160 1000 10 qz81 rfl rfl (@BSN.floor_sqrt_eq_dec qz78 652160 1000 10 qz81 rfl rfl rfl))) (@Ns324p570 33554432 1823263 8388608 11076519 1268776960000 160984709393131 281474976710656 173579408984743 5321636278435840000 (@Ns324p571 33554432 (Ns324p583 rfl rfl rfl rfl rfl) rfl) (Ns324p599 rfl) rfl)) 

noncomputable def Ns324p601 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz78) (hardyZApproximantRS₀ qz78) Bool.false 21567178651716103548811 2361183241434822606848 85790178295579456416347 Ns324p483 (@Eq.refl Real (hardyZApproximantRS₀ qz78)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz78) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz79) (Zeta.RiemannSiegel.correction qz80))) Bool.false 21567178651716103548811 2361183241434822606848 85790178295579456416347 Ns324p483 (BSN.hardyZApproximantRS₀_eq qz78 10 (@BSN.floor_sqrt_eq_dec qz78 652160 1000 10 qz81 rfl rfl rfl)) (@Ns324p485 21567178651716103548811 2361183241434822606848 85790178295579456416347 Ns324p483 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (@HAdd.hAdd Real Real Real qz366 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 10)) Bool.false 1250001953 134217728 79917 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (Ns324p562 (Ns324p561 rfl rfl rfl rfl) rfl rfl)) (Ns324p600 rfl) rfl rfl)) 

theorem RS325to336.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz78) Bool.false 21567178651716103548811 2361183241434822606848 85790178295579456416347 Ns324p483 := Ns324p601 

noncomputable def Ns324p602 := nat_lit 714257930534033838571520000 

noncomputable def Ns324p603 := nat_lit 686209419374319870251234230272 

noncomputable abbrev qz744 := (Enclosure.sfrac Bool.false 654021 1000)

noncomputable abbrev qz629 := qz744

noncomputable abbrev qz427 := qz629

noncomputable abbrev qz96 := qz427

noncomputable abbrev qz745 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 654021 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz630 := qz745

noncomputable abbrev qz428 := qz630

noncomputable abbrev qz97 := (@HPow.hPow Real Real Real qz584 qz428 qz351)

noncomputable abbrev qz746 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 654021 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz631 := qz746

noncomputable abbrev qz429 := qz631

noncomputable abbrev qz98 := qz429

noncomputable def Ns324p604 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz97) (Zeta.RiemannSiegel.correction qz98)) 49407021 134217728 160287 134217728 1635948564087200668305 9444732965739290427392 9514230654645903835047 Ns324p602 Ns324p603 

noncomputable def Ns324p605 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.cos BSN.quadSignPos 9 10 654021 1000 200 268435456 134217728 4503599627370496 Bool.false 319880147851 2456 618095470 56 84886744 8 

noncomputable def Ns324p606 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 654021 1000 107 156 268435456 134217728 4503599627370496 Bool.false 319880147851 2456 

noncomputable def Ns324p607 := Ns324p606 558195838 56 94906264 8 589812974 56 89478488 8 Bool.true 243823618 121054 Bool.true 74307489 Bool.true 91364407 14148475504056880 1 Bool.false 73362117 Bool.false Bool.false 253036630 Bool.false Bool.true 133540648 

noncomputable def Ns324p608 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 654021 1000 12 51 268435456 134217728 4503599627370496 Bool.false 319880147851 2456 

noncomputable def Ns324p609 := Ns324p608 480971758 57 109588312 8 522351262 57 101459064 8 Bool.true 387739475 89794 Bool.false 254628572 Bool.true 244018031 14148475504056880 1 Bool.false 156457459 Bool.false Bool.false 211772208 Bool.false Bool.true 243823618 

noncomputable def Ns324p610 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 654021 1000 181 88 268435456 134217728 4503599627370496 Bool.false 319880147851 2456 

noncomputable def Ns324p611 := Ns324p610 372130544 56 134217720 8 432030192 56 120047984 16 Bool.true 387499882 52747 Bool.false 178962817 Bool.false 217475961 14148475504056880 1 Bool.false 165996974 Bool.true Bool.false 185054504 Bool.false Bool.true 387739475 

noncomputable def Ns324p612 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 654021 1000 470 301 268435456 134217728 4503599627370496 Bool.false 319880147851 2456 

noncomputable def Ns324p613 := Ns324p612 186065264 56 189812528 16 294906480 56 154981288 8 Bool.true 148900744 2520 Bool.false 10566539 Bool.false 86230986 14148475504056880 1 Bool.false 268227515 Bool.true Bool.false 84755558 Bool.true Bool.true 387499882 

noncomputable def Ns324p614 := nat_lit 105002131265867928921247445154727484583632596303456527551 

noncomputable def Ns324p615 := nat_lit 88115174313404557321931555928927284239448884117504000 

noncomputable def Ns324p616 := nat_lit 57438137254182915004647481968480000 

noncomputable def Ns324p617 := nat_lit 225394549267048494100829430908659548480 

noncomputable abbrev qz632 := (@Eq.refl Real qz744)

noncomputable abbrev qz430 := qz632

noncomputable abbrev qz99 := qz430

noncomputable def Ns324p618 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz96 654021 1000 1710974873764 16000000 1308042 4000 2000 Ns324p616 Ns324p617 qz99 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns324p619 := nat_lit 302406138045699635293192642045615155600861877353954799346880 

noncomputable abbrev qz633 := (@HSub.hSub Real Real Real qz727 qz728 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz729 (@Nat.cast Real Real.instNatCast 1308042))))

noncomputable abbrev qz431 := (@HSub.hSub Real Real Real qz586 (@HMul.hMul Real Real Real qz582 (Enclosure.sfrac Bool.false 654021 4000) (Real.log (Enclosure.sfrac Bool.false 1710974873764 16000000))) (@HMul.hMul Real Real Real qz582 qz587 qz633))

noncomputable abbrev qz634 := (Enclosure.sfrac Bool.false 654021 2000)

noncomputable abbrev qz100 := (@HSub.hSub Real Real Real qz354 (@HSub.hSub Real Real Real qz354 qz431 qz634) (@HMul.hMul Real Real Real qz349 qz634 (Real.log Real.pi)))

noncomputable def Ns324p620 := @Enclosure.Real.IsNear.addLit_ft_p qz100 (Enclosure.sfrac Bool.true Ns324p616 Ns324p617) 1341674870571074747831 1125899906842624000 4533524069144805369 495616000000000000000000 Ns324p616 Ns324p617 0 1 Ns324p619 

noncomputable def Ns324p621 := nat_lit 90038276421371857586024873984000 

noncomputable abbrev qz101 := (@HSub.hSub Real Real Real qz354 qz431 qz634)

noncomputable def Ns324p622 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (@HMul.hMul Real Real Real qz5 qz634 (Real.log Real.pi)) 1763142768159369100727 1125899906842624000 517204222811289 121000000000000000000 25121444319981 67108864000 654021 134217728000 Ns324p621 1341674870571074747831 1125899906842624000 

noncomputable def Ns324p623 := nat_lit 3526285536318738201454000 

noncomputable abbrev qz102 := qz431

noncomputable def Ns324p624 := @Enclosure.Real.IsNear.subLit_ff_p qz102 qz634 2131323859645928996279 1125899906842624000 517204222811289 121000000000000000000 654021 2000 0 1 Ns324p623 1763142768159369100727 1125899906842624000 517204222811289 121000000000000000000 

noncomputable def Ns324p625 := nat_lit 4799314670053626572206983448669192192 

noncomputable def Ns324p626 := nat_lit 55997372111231145283158016 

noncomputable def Ns324p627 := nat_lit 26352917657389194896043749028288211443022628766816697007614926125321950937761355013307712608339180813538664577543032378280037988150316363537723417386024960 

noncomputable def Ns324p628 := nat_lit 524390818552952611389452144072153765014093574704282272199121717364720869471824989342575389352322775852458870559705871356989078809758667978112221747085312 

noncomputable def Ns324p629 := nat_lit 74175335296884655130430455050456246294285423642547166544274383753142414946212095351030273856744614894758779769138414087094363362878183218002001920 

noncomputable def Ns324p630 := BSN.log_dyadic_bound 662398873764 2759550873764 7 6 Ns324p627 134217728 38720000 Ns324p628 Ns324p629 65717060 3421949747528 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 662398873764) (BSN.artanhQ 2759550873764) 0 6 Ns324p628 Ns324p627 Ns324p629 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz432 := (Real.log (Enclosure.sfrac Bool.false 1710974873764 16000000))

noncomputable def Ns324p631 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 654021 4000) qz432 654021 4000 0 1 3259476047895799 281474976710656 195312621 7562500000000000 2131765784320858357779 1125899906842624000 127738555699041 30250000000000000000 (Enclosure.Real.IsNear.const Bool.false 654021 4000) (BSN.isNear_log_sfrac 1710974873764 16000000 3259476047895799 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1710974873764) qz357)) Bool.false Ns324p626 Ns324p98 1000000619520000 38720000000000000000000 3259476047895799 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1710974873764 16000000 16 3421949747528 2097152000000 65717060 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns324p630 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns324p632 := BSN.arctan_dyadic_bound_f 1000 1308042 1 0 16777216 4840000 0 1 1 0 1 1 12826 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1308042) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1308042) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz433 := (@Nat.cast Real Real.instNatCast 1308042)

noncomputable def Ns324p633 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz433)) 884279719003555 562949953421312 1 2000000000000000 12826 16777216 1 4840000 14828531454039365255168 883849349858723 562949953421312 50000000121 242000000000000000 qz15 (Ns324p632 rfl) rfl rfl 

noncomputable abbrev qz434 := (@HMul.hMul Real Real Real qz582 qz587 qz633)

noncomputable abbrev qz103 := qz434

noncomputable abbrev qz435 := qz633

noncomputable abbrev qz104 := qz435

noncomputable def Ns324p634 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 654021 4000) qz432) qz103 2131765784320858357779 1125899906842624000 127738555699041 30250000000000000000 883849349858723 2251799813685248 50000000121 968000000000000000 Ns324p625 2131323859645928996279 1125899906842624000 517204222811289 121000000000000000000 (Ns324p631 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz104 1 4 0 1 883849349858723 562949953421312 50000000121 242000000000000000 883849349858723 2251799813685248 50000000121 968000000000000000 qz365 Ns324p633 rfl) 

noncomputable def Ns324p635 := @Ns324p620 Ns324p614 Ns324p615 4533524069144805369 495616000000000000000000 (@Ns324p622 4533524069144805369 495616000000000000000000 (Ns324p624 (Ns324p634 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 654021 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz634 (Real.log Real.pi) 654021 2000 0 1 38410761 33554432 1 67108864 25121444319981 67108864000 654021 134217728000 (Enclosure.Real.IsNear.const Bool.false 654021 2000) RS325to336.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns324p616 Ns324p617) 

noncomputable def Ns324p636 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz96) Bool.false Ns324p614 Ns324p615 4533524069144805369 495616000000000000000000 39985018481 33554432 77 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz96) (@HAdd.hAdd Real Real Real qz366 qz100 (Enclosure.sfrac Bool.true Ns324p616 Ns324p617)) Bool.false Ns324p614 Ns324p615 4533524069144805369 495616000000000000000000 Ns324p618 (Ns324p635 rfl rfl)) 

noncomputable def Ns324p637 := nat_lit 4752508573198807782653952 

noncomputable def Ns324p638 := nat_lit 779905883814682318400884403897200037167788011652949030922913150237549388339751144006123776 

noncomputable def Ns324p639 := nat_lit 432857420880854501056267001713264501173210597209482594379337514688933246020722311332096 

noncomputable def Ns324p640 := nat_lit 2338851936602285246200540677688173582501017613764428127579980775683270298527211987395707136 

noncomputable def Ns324p641 := BSN.cos_dyadic_bound_f 67537208866 68719476736 3 2 33554432 9689454 Ns324p638 Ns324p240 Ns324p639 Ns324p640 Ns324p243 Ns324p639 18612593 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 67537208866) (BSN.cosEvenQ 68719476736) 0 2 Ns324p638 Ns324p240 Ns324p639 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 67537208866) (BSN.cosOddQ 68719476736) 0 2 Ns324p640 Ns324p243 Ns324p639 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p642 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz96) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39985018481) qz391) Bool.false 39985018481 33554432 77 8388608 Bool.true 18612593 33554432 1 4840000 (Ns324p636 rfl) (Enclosure.sfrac_false_div 39985018481 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39985018481) qz391) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns324p637) qz409) 226375608064910080 72057594037927936 Bool.false 18612593 33554432 189 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q2 39985018481 33554432 226375608064910080 72057594037927936 189 Ns324p637 Ns324p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 18612593 33554432 Ns324p637 Ns324p98 67537208866 68719476736 9689454 9680000 (Ns324p641 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns324p643 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz96) Bool.false Ns324p614 Ns324p615 4533524069144805369 495616000000000000000000 319880147851 268435456 2456 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz96) (@HAdd.hAdd Real Real Real qz366 qz100 (Enclosure.sfrac Bool.true Ns324p616 Ns324p617)) Bool.false Ns324p614 Ns324p615 4533524069144805369 495616000000000000000000 Ns324p618 (Ns324p635 rfl rfl)) 

noncomputable def Ns324p644 := Ns324p613 52747 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 470 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268227515 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 301 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 84755558 268435456) qz99 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 1) Bool.true 18612593 33554432 5954197 634388480000 148900744 268435456 2520 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz96)) Bool.true 18612593 33554432 5954197 634388480000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz96) qz96) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz96)) Bool.true 18612593 33554432 381068608 40600862720000 18612593 33554432 5954197 634388480000 (Ns324p642 rfl rfl) rfl)) rfl) (Ns324p643 rfl) RS325to336.d7 

noncomputable def Ns324p645 := nat_lit 12466112482771786807632667441 

noncomputable def Ns324p646 := BSN.cos_dyadic_bound_f 10566539 268435456 2 1 268435456 134217728 Ns324p645 Ns324p149 Ns324p645 Ns324p645 Ns324p150 Ns324p645 268227515 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 10566539) qz369 0 1 Ns324p645 Ns324p149 Ns324p645 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 10566539) qz370 0 1 Ns324p645 Ns324p150 Ns324p645 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p647 := nat_lit 55290868027939026797742064582416 

noncomputable def Ns324p648 := BSN.sin_dyadic_bound_f 86230986 268435456 2 1 268435456 134217728 Ns324p647 Ns324p270 Ns324p647 Ns324p647 Ns324p271 Ns324p647 84755558 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 86230986) qz367 0 1 Ns324p647 Ns324p270 Ns324p647 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 86230986) qz368 0 1 Ns324p647 Ns324p271 Ns324p647 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p649 := nat_lit 16107231534164930782804288907175282495895327480390038202977288608615425 

noncomputable def Ns324p650 := nat_lit 1052210079953914462479789900745967493545478256701280384291085552641 

noncomputable def Ns324p651 := nat_lit 42183902820778702855357694144667389256164879293367821791937379836431361 

noncomputable def Ns324p652 := BSN.sin_dyadic_bound_f 178962817 268435456 3 2 268435456 134217728 Ns324p649 Ns324p249 Ns324p650 Ns324p651 Ns324p252 Ns324p650 165996974 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 178962817) qz367 0 2 Ns324p649 Ns324p249 Ns324p650 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 178962817) qz368 0 2 Ns324p651 Ns324p252 Ns324p650 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p653 := nat_lit 19517544773124696056495199658574222070149890388059919076510205903712961 

noncomputable def Ns324p654 := nat_lit 5003686237835434015416256305696502917325836176911067531597239628481 

noncomputable def Ns324p655 := nat_lit 58542626946898417301454766463111273204615019491825935094467423231881921 

noncomputable def Ns324p656 := BSN.cos_dyadic_bound_f 217475961 268435456 3 2 268435456 134217728 Ns324p653 Ns324p263 Ns324p654 Ns324p655 Ns324p266 Ns324p654 185054504 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 217475961) qz369 0 2 Ns324p653 Ns324p263 Ns324p654 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 217475961) qz370 0 2 Ns324p655 Ns324p266 Ns324p654 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p657 := Ns324p611 89794 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 181 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 165996974 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 88 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 185054504 268435456) qz99 rfl rfl (Ns324p644 RS325to336.d9 RS325to336.d11 RS325to336.d13 RS325to336.d17 (Ns324p646 rfl rfl) (Ns324p648 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns324p643 rfl) RS325to336.d19 RS325to336.d21 RS325to336.d23 RS325to336.d25 RS325to336.d17 (Ns324p652 rfl rfl) (Ns324p656 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns324p658 := nat_lit 36686524548258489933876606444637187761353320201694423613362069181628416 

noncomputable def Ns324p659 := nat_lit 17670835159598365623431300372227865017990061559442329386750784372736 

noncomputable def Ns324p660 := nat_lit 110024231974456273070382956733167107554023980481964386181312705976139776 

noncomputable def Ns324p661 := BSN.cos_dyadic_bound_f 254628572 268435456 3 2 268435456 134217728 Ns324p658 Ns324p263 Ns324p659 Ns324p660 Ns324p266 Ns324p659 156457459 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 254628572) qz369 0 2 Ns324p658 Ns324p263 Ns324p659 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 254628572) qz370 0 2 Ns324p660 Ns324p266 Ns324p659 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p662 := nat_lit 55683565073112255412296183132124309077562977122458788531978344501149825 

noncomputable def Ns324p663 := nat_lit 12571159816209987614215319696983459965791028491375964827512027021441 

noncomputable def Ns324p664 := nat_lit 145817555218448709909400321495101883887006040322215551735936835173548161 

noncomputable def Ns324p665 := BSN.sin_dyadic_bound_f 244018031 268435456 3 2 268435456 134217728 Ns324p662 Ns324p249 Ns324p663 Ns324p664 Ns324p252 Ns324p663 211772208 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 244018031) qz367 0 2 Ns324p662 Ns324p249 Ns324p663 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 244018031) qz368 0 2 Ns324p664 Ns324p252 Ns324p663 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p666 := Ns324p609 121054 BSN.abs_quadSignPos (BSN.cos_quad_nat0 12 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 156457459 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 51 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 211772208 268435456) qz99 rfl rfl (Ns324p657 rfl rfl) (Ns324p643 rfl) RS325to336.d27 RS325to336.d29 RS325to336.d31 RS325to336.d33 RS325to336.d17 (Ns324p661 rfl rfl) (Ns324p665 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p667 := nat_lit 30488098822553023302512224384641 

noncomputable def Ns324p668 := BSN.sin_dyadic_bound_f 74307489 268435456 2 1 268435456 134217728 Ns324p667 Ns324p270 Ns324p667 Ns324p667 Ns324p271 Ns324p667 73362117 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 74307489) qz367 0 1 Ns324p667 Ns324p270 Ns324p667 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 74307489) qz368 0 1 Ns324p667 Ns324p271 Ns324p667 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p669 := nat_lit 607827611042930904924643984815590846392510888557636872025311560975681 

noncomputable def Ns324p670 := nat_lit 4855302782907531706398510921744025333595673922249017101896238401 

noncomputable def Ns324p671 := nat_lit 1823473122523226899710519157424929051126865474325066118041730890450241 

noncomputable def Ns324p672 := BSN.cos_dyadic_bound_f 91364407 268435456 3 2 268435456 134217728 Ns324p669 Ns324p263 Ns324p670 Ns324p671 Ns324p266 Ns324p670 253036630 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 91364407) qz369 0 2 Ns324p669 Ns324p263 Ns324p670 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 91364407) qz370 0 2 Ns324p671 Ns324p266 Ns324p670 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p673 := Ns324p607 147918 BSN.abs_quadSignPos (BSN.cos_quad_nat3 107 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 73362117 268435456) BSN.abs_quadSignPos qz595 (BSN.sfrac_eq_quadSignPos_mul Bool.false 253036630 268435456) qz99 rfl rfl (Ns324p666 rfl) (Ns324p643 rfl) RS325to336.d35 RS325to336.d37 RS325to336.d39 RS325to336.d41 RS325to336.d17 (Ns324p668 rfl rfl) (Ns324p672 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p674 := nat_lit 1639644569969223081019599360000 

noncomputable def Ns324p675 := BSN.cos_dyadic_bound_f 35783880 268435456 2 1 268435456 134217728 Ns324p674 Ns324p149 Ns324p674 Ns324p674 Ns324p150 Ns324p674 266053894 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 35783880) qz369 0 1 Ns324p674 Ns324p149 Ns324p674 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 35783880) qz370 0 1 Ns324p674 Ns324p150 Ns324p674 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p676 := Ns324p605 Bool.true 133540648 147918 Bool.true 35783880 14148475504056880 1 Bool.false 266053894 Bool.false Bool.true 49407021 160287 BSN.abs_quadSignPos qz596 (BSN.sfrac_eq_quadSignPos_mul Bool.false 266053894 268435456) qz99 rfl (Ns324p673 rfl) (Ns324p643 rfl) RS325to336.d43 RS325to336.d45 RS325to336.d17 (Ns324p675 rfl rfl) rfl 

noncomputable def Ns324p677 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) 49407021 268435456 160287 268435456 49407021 268435456 160287 268435456 26525192423473152 49407021 134217728 160287 134217728 (Ns324p676 rfl rfl rfl rfl) 

noncomputable def Ns324p678 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz97) (Zeta.RiemannSiegel.correction qz98) 5252511 16777216 1 16777216 311460283298255 562949953421312 903441674261903 21286545113743360000 1635948564087200668305 9444732965739290427392 

noncomputable def Ns324p679 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz97 1 1 0 1 5252511 16777216 1 16777216 5252511 16777216 1 16777216 

noncomputable abbrev qz105 := qz428

noncomputable def Ns324p680 := @Enclosure.Real.IsNear.sqrt_image qz105 3492703009413 33554432000 654021 33554432000 171169246 171169279 16777216 (@Enclosure.Real.IsNear.of_eq qz105 (@HMul.hMul Real Real Real qz5 qz96 qz3) Bool.false 3492703009413 33554432000 654021 33554432000 (BSN.t_div_two_pi_mk qz96 654021 1000 qz99) (@Enclosure.Real.IsNear.mulLit_ff qz96 qz3 654021 1000 0 1 5340353 33554432 1 33554432 3492703009413 33554432000 654021 33554432000 (Enclosure.Real.IsNear.const Bool.false 654021 1000) RS325to336.d48 rfl)) 

noncomputable abbrev qz747 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 654021 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz635 := qz747

noncomputable abbrev qz436 := qz635

noncomputable abbrev qz106 := qz436

noncomputable def Ns324p681 := @Enclosure.Real.IsNear.sqrt_image qz106 342338525 33554432 33 33554432 53588650 53588656 16777216 (@Enclosure.Real.IsNear.recentre' qz106 Bool.false 342338525 33554432 33 33554432 342338525 33554432 33 33554432 (Ns324p680 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns324p682 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz106) 53588653 16777216 3 16777216 5252510 5252512 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz106) Bool.false 107177306 33554432 6 33554432 53588653 16777216 3 16777216 (Ns324p681 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns324p683 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz106)) Bool.false 10505022 33554432 2 33554432 5252511 16777216 1 16777216 (Ns324p682 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz107 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz429))

noncomputable abbrev qz636 := (@HMul.hMul Real Real Real qz723 qz746 qz746)

noncomputable abbrev qz437 := (@HSub.hSub Real Real Real qz586 (@HSub.hSub Real Real Real qz586 qz636 qz631) qz600)

noncomputable abbrev qz108 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz437))

noncomputable def Ns324p684 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz98) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz107) qz108) Bool.false 311460283298255 

noncomputable def Ns324p685 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz107) qz108 114075689 33554432 2485 

noncomputable def Ns324p686 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz107) Bool.false 114075689 33554432 2485 33554432 114075689 33554432 2485 

noncomputable def Ns324p687 := @Enclosure.Real.IsNear.recentre' qz107 Bool.false 4934881 16777216 65017152 10150215680000 4934881 16777216 1015893 158597120000 

noncomputable abbrev qz109 := (@HMul.hMul Real Real Real qz349 qz346 qz429)

noncomputable def Ns324p688 := @Enclosure.Real.IsNear.cos_image qz109 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 42689249) qz391) Bool.false 42689249 33554432 13 2097152 Bool.false 4934881 16777216 1 

noncomputable def Ns324p689 := nat_lit 890540488556815276575215271 

noncomputable def Ns324p690 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz98 884279719003555 140737488355328 1 500000000000000 6794205 33554432 33 33554432 6007977688252548398775 4722366482869645213696 Ns324p689 

noncomputable def Ns324p691 := @Enclosure.Real.IsNear.subLit_ff_p qz106 qz1 342338525 33554432 33 33554432 10 1 0 1 6794205 6794205 33554432 33 

noncomputable def Ns324p692 := @Ns324p691 33554432 (@Enclosure.Real.IsNear.recentre' qz106 Bool.false 342338525 33554432 33 33554432 342338525 33554432 33 33554432 (Ns324p680 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns324p693 := @Enclosure.Real.IsNear.recentre' qz109 Bool.false 6007977688252548398775 4722366482869645213696 Ns324p689 Ns324p173 42689249 33554432 13 2097152 (@Ns324p690 Ns324p173 RS325to336.d47 (Ns324p692 rfl rfl) rfl) 

noncomputable def Ns324p694 := nat_lit 7083691352100576809899374916737360568683556758121376110980007681 

noncomputable def Ns324p695 := nat_lit 11029304251659972171399256757505565315460648719235547056736001 

noncomputable def Ns324p696 := nat_lit 21229015447798410485355326236697070575419748976925657238826551041 

noncomputable def Ns324p697 := BSN.cos_dyadic_bound_f 42689249 33554432 3 2 16777216 4840000 Ns324p694 Ns324p308 Ns324p695 Ns324p696 Ns324p311 Ns324p695 4934881 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 42689249) qz392 0 2 Ns324p694 Ns324p308 Ns324p695 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 42689249) (BSN.cosOddQ 33554432) 0 2 Ns324p696 Ns324p311 Ns324p695 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p698 := @Enclosure.Real.IsNear.inv_image qz107 4934881 16777216 1015893 158597120000 57036602 57039087 16777216 (Ns324p687 (@Ns324p688 4840000 (Ns324p693 rfl) (Enclosure.sfrac_false_div 42689249 33554432) (Ns324p697 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns324p699 := @Enclosure.Real.IsNear.recentre' qz108 Bool.false 2730295 16777216 

noncomputable abbrev qz110 := (@HMul.hMul Real Real Real qz349 qz346 qz437)

noncomputable def Ns324p700 := @Enclosure.Real.IsNear.cos_image qz110 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 2951387)) (@Nat.cast Real Real.instNatCast 2097152)) Bool.true 2951387 2097152 

noncomputable def Ns324p701 := nat_lit 223000500076631197361673117445 

noncomputable def Ns324p702 := nat_lit 41982638933887768343315249364371933 

noncomputable def Ns324p703 := @Enclosure.Real.IsNear.recentre' qz110 Bool.true Ns324p701 Ns324p188 Ns324p702 

noncomputable abbrev qz111 := qz437

noncomputable def Ns324p704 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz111 884279719003555 140737488355328 1 500000000000000 252183212262199 

noncomputable abbrev qz438 := (@HSub.hSub Real Real Real qz586 qz636 qz631)

noncomputable abbrev qz112 := qz438

noncomputable def Ns324p705 := @Enclosure.Real.IsNear.subLit_tf qz112 qz29 181814468084535 1125899906842624 1555714875 1125899906842624 1 16 

noncomputable abbrev qz439 := qz636

noncomputable abbrev qz113 := qz439

noncomputable def Ns324p706 := @Enclosure.Real.IsNear.subLit_ff_n qz113 qz98 46161221582025 1125899906842624 448418619 1125899906842624 6794205 33554432 33 33554432 

noncomputable def Ns324p707 := @Enclosure.Real.IsNear.mulLit_ff qz98 qz98 6794205 33554432 33 33554432 6794205 33554432 33 33554432 46161221582025 1125899906842624 

noncomputable def Ns324p708 := nat_lit 567914343443332192998398080702988674416730255775504454274117454798947886041899114961 

noncomputable def Ns324p709 := nat_lit 3466537250751077332112698720796095110148055492926080949987665366995300109908547993600 

noncomputable def Ns324p710 := nat_lit 436831472034606765033189447818562159329414438270994777134377338139065342140881 

noncomputable def Ns324p711 := nat_lit 3439994182105512911711116376330187383190871614803265229882167385594018429719460618705 

noncomputable def Ns324p712 := nat_lit 315454889818348037222255583592444655023473049856273366448877548396572310001677867417600 

noncomputable def Ns324p713 := BSN.cos_dyadic_bound_f 2951387 2097152 4 3 16777216 4840000 Ns324p708 Ns324p709 Ns324p710 Ns324p711 Ns324p712 Ns324p710 2730295 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 2951387) (BSN.cosEvenQ 2097152) 0 3 Ns324p708 Ns324p709 Ns324p710 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 2951387) (BSN.cosOddQ 2097152) 0 3 Ns324p711 Ns324p712 Ns324p710 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p714 := @Ns324p699 1451674432 162403450880000 2730295 16777216 22682413 2537553920000 (@Ns324p700 293 33554432 Bool.false 2730295 16777216 1 4840000 (@Ns324p703 Ns324p191 2951387 2097152 293 33554432 (@Ns324p704 1125899906842624 1555714875 1125899906842624 Ns324p701 Ns324p188 Ns324p702 Ns324p191 RS325to336.d47 (@Ns324p705 0 1 4034931396195184 252183212262199 1125899906842624 1555714875 1125899906842624 (@Ns324p706 6100681205958699909120 181814468084535 1125899906842624 1555714875 1125899906842624 (@Ns324p707 448418619 1125899906842624 (Ns324p692 rfl rfl) (Ns324p692 rfl rfl) rfl) (Ns324p692 rfl rfl) rfl rfl) qz379 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 2951387 2097152) (BSN.cos_neg_of_bound 2951387 2097152 Bool.false 2730295 16777216 1 4840000 (Ns324p713 rfl rfl)) rfl rfl) 

noncomputable def Ns324p715 := @Ns324p678 9514230654645903835047 Ns324p602 (Ns324p679 qz31 (@Enclosure.Real.IsNear.of_eq qz97 (@Inv.inv Real Real.instInv (Real.sqrt qz106)) Bool.false 5252511 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz105 (BSN.t_div_two_pi_nonneg qz96 654021 1000 qz99)) Ns324p683) rfl) (@Ns324p684 562949953421312 903441674261903 21286545113743360000 (BSN.correction_mk qz98 (BSN.cos_two_pi_p_ne_zero_mk qz96 654021 1000 10 qz99 rfl rfl (@BSN.floor_sqrt_eq_dec qz96 654021 1000 10 qz99 rfl rfl rfl))) (@Ns324p685 33554432 2730295 16777216 22682413 2537553920000 311460283298255 562949953421312 903441674261903 21286545113743360000 (@Ns324p686 33554432 (Ns324p698 rfl rfl rfl rfl rfl) rfl) (Ns324p714 rfl) rfl)) 

noncomputable def Ns324p716 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz96) (hardyZApproximantRS₀ qz96) Bool.true 5112658585416673647249 9444732965739290427392 862503344816291389915047 Ns324p602 (@Eq.refl Real (hardyZApproximantRS₀ qz96)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz96) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz97) (Zeta.RiemannSiegel.correction qz98))) Bool.true 5112658585416673647249 9444732965739290427392 862503344816291389915047 Ns324p602 (BSN.hardyZApproximantRS₀_eq qz96 10 (@BSN.floor_sqrt_eq_dec qz96 654021 1000 10 qz99 rfl rfl rfl)) (@Ns324p604 5112658585416673647249 9444732965739290427392 862503344816291389915047 Ns324p602 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (@HAdd.hAdd Real Real Real qz366 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 10)) Bool.true 49407021 134217728 160287 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (Ns324p677 (Ns324p676 rfl rfl rfl rfl) rfl rfl)) (Ns324p715 rfl) rfl rfl)) 

theorem RS325to336.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz96) Bool.true 5112658585416673647249 9444732965739290427392 862503344816291389915047 Ns324p602 := Ns324p716 

noncomputable def Ns324p717 := nat_lit 285703172213613535428608000 

noncomputable def Ns324p718 := nat_lit 2932363958596186365911705321472 

noncomputable abbrev qz748 := (Enclosure.sfrac Bool.false 654697 1000)

noncomputable abbrev qz637 := qz748

noncomputable abbrev qz440 := qz637

noncomputable abbrev qz114 := qz440

noncomputable abbrev qz749 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 654697 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz638 := qz749

noncomputable abbrev qz441 := qz638

noncomputable abbrev qz115 := (@HPow.hPow Real Real Real qz584 qz441 qz351)

noncomputable abbrev qz750 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 654697 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz639 := qz750

noncomputable abbrev qz442 := qz639

noncomputable abbrev qz116 := qz442

noncomputable def Ns324p719 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz115) (Zeta.RiemannSiegel.correction qz116)) 178207591 134217728 40113 33554432 3232674750158061059699 18889465931478580854784 4261813631488320467009 Ns324p717 Ns324p718 

noncomputable def Ns324p720 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.cos BSN.quadSignPos 9 10 654697 1000 200 268435456 134217728 4503599627370496 Bool.false 320301664860 2459 618095470 56 84886744 8 

noncomputable def Ns324p721 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 654697 1000 107 156 268435456 134217728 4503599627370496 Bool.false 320301664860 2459 

noncomputable def Ns324p722 := Ns324p721 558195838 56 94906264 8 589812974 56 89478488 8 Bool.true 3279277 121178 Bool.true 30130866 Bool.true 68560969 14148475504056880 1 Bool.false 30067634 Bool.false Bool.false 259727387 Bool.false Bool.false 93927035 

noncomputable def Ns324p723 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 654697 1000 12 51 268435456 134217728 4503599627370496 Bool.false 320301664860 2459 

noncomputable def Ns324p724 := Ns324p723 480971758 57 109588312 8 522351262 57 101459064 8 Bool.true 93530026 89885 Bool.false 351008673 Bool.true 175610476 14148475504056880 1 Bool.false 69835965 Bool.false Bool.false 163349581 Bool.false Bool.true 3279277 

noncomputable def Ns324p725 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 654697 1000 181 88 268435456 134217728 4503599627370496 Bool.false 320301664860 2459 

noncomputable def Ns324p726 := Ns324p725 372130544 56 134217720 8 432030192 56 120047984 16 Bool.false 2805726 52800 Bool.false 348919578 Bool.false 346940560 14148475504056880 1 Bool.false 258640734 Bool.true Bool.false 73755826 Bool.false Bool.true 93530026 

noncomputable def Ns324p727 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 654697 1000 470 301 268435456 134217728 4503599627370496 Bool.false 320301664860 2459 

noncomputable def Ns324p728 := Ns324p727 186065264 56 189812528 16 294906480 56 154981288 8 Bool.false 223274176 2520 Bool.false 306303429 Bool.false 308391215 14148475504056880 1 Bool.false 111836320 Bool.true Bool.false 244891590 Bool.true Bool.false 2805726 

noncomputable def Ns324p729 := nat_lit 952148034469574880731836824570443551016585364878913697579 

noncomputable def Ns324p730 := nat_lit 797967415884153862392853940498569876094557265854464000 

noncomputable def Ns324p731 := nat_lit 57735593351070292720971401563360000 

noncomputable def Ns324p732 := nat_lit 226795980291897723871231261369578611520 

noncomputable abbrev qz640 := (@Eq.refl Real qz748)

noncomputable abbrev qz443 := qz640

noncomputable abbrev qz117 := qz443

noncomputable def Ns324p733 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz114 654697 1000 1714513647236 16000000 1309394 4000 2000 Ns324p731 Ns324p732 qz117 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns324p734 := nat_lit 304687371030263961834187783862541936325307316761252383225280 

noncomputable abbrev qz641 := (@HSub.hSub Real Real Real qz727 qz728 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz729 (@Nat.cast Real Real.instNatCast 1309394))))

noncomputable abbrev qz444 := (@HSub.hSub Real Real Real qz586 (@HMul.hMul Real Real Real qz582 (Enclosure.sfrac Bool.false 654697 4000) (Real.log (Enclosure.sfrac Bool.false 1714513647236 16000000))) (@HMul.hMul Real Real Real qz582 qz587 qz641))

noncomputable abbrev qz642 := (Enclosure.sfrac Bool.false 654697 2000)

noncomputable abbrev qz118 := (@HSub.hSub Real Real Real qz354 (@HSub.hSub Real Real Real qz354 qz444 qz642) (@HMul.hMul Real Real Real qz349 qz642 (Real.log Real.pi)))

noncomputable def Ns324p735 := @Enclosure.Real.IsNear.addLit_ft_p qz118 (Enclosure.sfrac Bool.true Ns324p731 Ns324p732) 1343442840753240996339 1125899906842624000 4538183486305263533 495616000000000000000000 Ns324p731 Ns324p732 0 1 Ns324p734 

noncomputable def Ns324p736 := nat_lit 90156922891882907582538448896000 

noncomputable abbrev qz119 := (@HSub.hSub Real Real Real qz354 qz444 qz642)

noncomputable def Ns324p737 := @Enclosure.Real.IsNear.subLit_ff_p qz119 (@HMul.hMul Real Real Real qz5 qz642 (Real.log Real.pi)) 1765346370070133799411 1125899906842624000 517732348138473 121000000000000000000 25147409994417 67108864000 654697 134217728000 Ns324p736 1343442840753240996339 1125899906842624000 

noncomputable abbrev qz120 := qz444

noncomputable def Ns324p738 := @Enclosure.Real.IsNear.subLit_ff_p qz120 qz642 17071264125801652015 9007199254740992 517732348138473 121000000000000000000 654697 2000 0 1 28245541921122140790576 1765346370070133799411 1125899906842624000 517732348138473 121000000000000000000 

noncomputable def Ns324p739 := nat_lit 38441069377851818082145403634974720 

noncomputable def Ns324p740 := nat_lit 56007363365018865238016000 

noncomputable def Ns324p741 := nat_lit 26761321385602429765794912336474547288983146442306777315332324600740323342188457035100827099152381795840002960856531396539246077595313728800957098056744960 

noncomputable def Ns324p742 := nat_lit 537003260547615332206108195736059065533338792206845034122232367674634687856772589526454259236699718283535899350534302410045901146280122011641780803469312 

noncomputable def Ns324p743 := nat_lit 79072833689359634849657722514065231168229096589929350752912905536673652448818675249706558668951596259394304519040332692706540025139317941647441920 

noncomputable def Ns324p744 := BSN.log_dyadic_bound 665937647236 2763089647236 7 6 Ns324p741 134217728 38720000 Ns324p742 Ns324p743 65994373 3429027294472 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 665937647236) (BSN.artanhQ 2763089647236) 0 6 Ns324p742 Ns324p741 Ns324p743 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz445 := (Real.log (Enclosure.sfrac Bool.false 1714513647236 16000000))

noncomputable def Ns324p745 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 654697 4000) qz445 654697 4000 0 1 3260057615408375 281474976710656 195312621 7562500000000000 17074799525080135099 9007199254740992 127870587030837 30250000000000000000 (Enclosure.Real.IsNear.const Bool.false 654697 4000) (BSN.isNear_log_sfrac 1714513647236 16000000 3260057615408375 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1714513647236) qz357)) Bool.false Ns324p740 Ns324p98 1000000619520000 38720000000000000000000 3260057615408375 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1714513647236 16000000 16 3429027294472 2097152000000 65994373 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns324p744 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns324p746 := BSN.arctan_dyadic_bound_f 1000 1309394 1 0 16777216 4840000 0 1 1 0 1 1 12812 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1309394) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1309394) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz446 := (@Nat.cast Real Real.instNatCast 1309394)

noncomputable def Ns324p747 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz446)) 884279719003555 562949953421312 1 2000000000000000 12812 16777216 1 4840000 14828539335338713153536 883849819620771 562949953421312 50000000121 242000000000000000 qz15 (Ns324p746 rfl) rfl rfl 

noncomputable abbrev qz447 := (@HMul.hMul Real Real Real qz582 qz587 qz641)

noncomputable abbrev qz121 := qz447

noncomputable abbrev qz448 := qz641

noncomputable abbrev qz122 := qz448

noncomputable def Ns324p748 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 654697 4000) qz445) qz121 17074799525080135099 9007199254740992 127870587030837 30250000000000000000 883849819620771 2251799813685248 50000000121 968000000000000000 Ns324p739 17071264125801652015 9007199254740992 517732348138473 121000000000000000000 (Ns324p745 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz122 1 4 0 1 883849819620771 562949953421312 50000000121 242000000000000000 883849819620771 2251799813685248 50000000121 968000000000000000 qz365 Ns324p747 rfl) 

noncomputable def Ns324p749 := @Ns324p735 Ns324p729 Ns324p730 4538183486305263533 495616000000000000000000 (@Ns324p737 4538183486305263533 495616000000000000000000 (Ns324p738 (Ns324p748 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 654697 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz642 (Real.log Real.pi) 654697 2000 0 1 38410761 33554432 1 67108864 25147409994417 67108864000 654697 134217728000 (Enclosure.Real.IsNear.const Bool.false 654697 2000) RS325to336.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns324p731 Ns324p732) 

noncomputable def Ns324p750 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz114) Bool.false Ns324p729 Ns324p730 4538183486305263533 495616000000000000000000 40037708107 33554432 77 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz114) (@HAdd.hAdd Real Real Real qz366 qz118 (Enclosure.sfrac Bool.true Ns324p731 Ns324p732)) Bool.false Ns324p729 Ns324p730 4538183486305263533 495616000000000000000000 Ns324p733 (Ns324p749 rfl rfl)) 

noncomputable def Ns324p751 := nat_lit 4749978986562636442763264 

noncomputable def Ns324p752 := nat_lit 1400497677270823125529653581306356338524632462998966513872173630593224160778562049039171840 

noncomputable def Ns324p753 := nat_lit 431017697395292365962136697359449650050531336933473349181893336200121039728733788078336 

noncomputable def Ns324p754 := nat_lit 3667272268961134855413725444006637015750146066642258103290350729009358320355720749921894656 

noncomputable def Ns324p755 := BSN.sin_dyadic_bound_f 67501261278 68719476736 3 2 33554432 9689454 Ns324p752 Ns324p520 Ns324p753 Ns324p754 Ns324p523 Ns324p753 27909272 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 67501261278) qz593 0 2 Ns324p752 Ns324p520 Ns324p753 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 67501261278) qz594 0 2 Ns324p754 Ns324p523 Ns324p753 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p756 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz114) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40037708107) qz391) Bool.false 40037708107 33554432 77 8388608 Bool.false 27909272 33554432 1 4840000 (Ns324p750 rfl) (Enclosure.sfrac_false_div 40037708107 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40037708107) qz391) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns324p751) qz409) 226375608064910080 72057594037927936 Bool.false 27909272 33554432 189 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q3 40037708107 33554432 226375608064910080 72057594037927936 189 Ns324p751 Ns324p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 27909272 33554432 Ns324p751 Ns324p98 67501261278 68719476736 9689454 9680000 (Ns324p755 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns324p757 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz114) Bool.false Ns324p729 Ns324p730 4538183486305263533 495616000000000000000000 320301664860 268435456 2459 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz114) (@HAdd.hAdd Real Real Real qz366 qz118 (Enclosure.sfrac Bool.true Ns324p731 Ns324p732)) Bool.false Ns324p729 Ns324p730 4538183486305263533 495616000000000000000000 Ns324p733 (Ns324p749 rfl rfl)) 

noncomputable def Ns324p758 := Ns324p728 52800 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 470 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 111836320 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 301 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 244891590 268435456) qz117 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 1) Bool.false 3488659 4194304 5954197 634388480000 223274176 268435456 2520 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz114)) Bool.false 3488659 4194304 5954197 634388480000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz114) qz114) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz114)) Bool.false 27909272 33554432 381068608 40600862720000 3488659 4194304 5954197 634388480000 (Ns324p756 rfl rfl) rfl)) rfl) (Ns324p757 rfl) RS325to336.d7 

noncomputable def Ns324p759 := nat_lit 4741221862185621899497302511715880524711097870831018930050856063969209872574179090235200017855523574209923921 

noncomputable def Ns324p760 := nat_lit 682059565421296172440598158553750374177572458120832796693804097440355510986683821508824370116590652241 

noncomputable def Ns324p761 := nat_lit 28744078380566893127512120916986928037039148303056166298343032173723609983701709950562360803097335241097169745 

noncomputable def Ns324p762 := BSN.cos_dyadic_bound_f 306303429 268435456 4 3 268435456 134217728 Ns324p759 Ns324p125 Ns324p760 Ns324p761 Ns324p128 Ns324p760 111836320 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 306303429) qz369 0 3 Ns324p759 Ns324p125 Ns324p760 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 306303429) qz370 0 3 Ns324p761 Ns324p128 Ns324p760 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p763 := nat_lit 142101741468540547560632895704520013195216454360606936381165460540330625 

noncomputable def Ns324p764 := nat_lit 81811806792708481256038195393019174416758479339694814113944062890625 

noncomputable def Ns324p765 := nat_lit 372038770444703715593909712624058955895558819120753898918296487218090625 

noncomputable def Ns324p766 := BSN.sin_dyadic_bound_f 308391215 268435456 3 2 268435456 134217728 Ns324p763 Ns324p249 Ns324p764 Ns324p765 Ns324p252 Ns324p764 244891590 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 308391215) qz367 0 2 Ns324p763 Ns324p249 Ns324p764 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 308391215) qz368 0 2 Ns324p765 Ns324p252 Ns324p764 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p767 := nat_lit 20755313172478630799523932713367092093931563585467942201428193688665532284010317229501420971557038490700681216 

noncomputable def Ns324p768 := nat_lit 3256147446265533747334145150574032645138881689605087239014434989202758753210410787111563884379189743616 

noncomputable def Ns324p769 := nat_lit 103716051394085522591457492636711857190821985502255318396477535094428706798701022754547656471514655275571941376 

noncomputable def Ns324p770 := BSN.sin_dyadic_bound_f 348919578 268435456 4 3 268435456 134217728 Ns324p767 Ns324p119 Ns324p768 Ns324p769 Ns324p122 Ns324p768 258640734 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 348919578) qz367 0 3 Ns324p767 Ns324p119 Ns324p768 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 348919578) qz368 0 3 Ns324p769 Ns324p122 Ns324p768 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p771 := nat_lit 7808829770789024086996462444614375724323613522610492676387470030270998880540039127915742344013020135424000000 

noncomputable def Ns324p772 := nat_lit 3041311483717449450222965479029441875231945384071408963484406675612787892548187374470823936000000000000 

noncomputable def Ns324p773 := nat_lit 47321182728207523190561264335500350440175408357650798685612291544496728389930328660043261429978586782105600000 

noncomputable def Ns324p774 := BSN.cos_dyadic_bound_f 346940560 268435456 4 3 268435456 134217728 Ns324p771 Ns324p125 Ns324p772 Ns324p773 Ns324p128 Ns324p772 73755826 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 346940560) qz369 0 3 Ns324p771 Ns324p125 Ns324p772 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 346940560) qz370 0 3 Ns324p773 Ns324p128 Ns324p772 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p775 := Ns324p726 89885 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 181 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 258640734 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 88 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 73755826 268435456) qz117 rfl rfl (Ns324p758 RS325to336.d9 RS325to336.d11 RS325to336.d13 RS325to336.d17 (Ns324p762 rfl rfl) (Ns324p766 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns324p757 rfl) RS325to336.d19 RS325to336.d21 RS325to336.d23 RS325to336.d25 RS325to336.d17 (Ns324p770 rfl rfl) (Ns324p774 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns324p776 := nat_lit 8182225325686966693175527513912554642949666616405374234351223154633536033248072734009229857055123912498275201 

noncomputable def Ns324p777 := nat_lit 3497954611400306628345897186893528243055468178837771029124077019880245797413396226007562709326569857921 

noncomputable def Ns324p778 := nat_lit 49581327865353974016646801090218149121162342327467162856394537921726774598599028144764040650992882139455480705 

noncomputable def Ns324p779 := BSN.cos_dyadic_bound_f 351008673 268435456 4 3 268435456 134217728 Ns324p776 Ns324p125 Ns324p777 Ns324p778 Ns324p128 Ns324p777 69835965 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 351008673) qz369 0 3 Ns324p776 Ns324p125 Ns324p777 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 351008673) qz370 0 3 Ns324p778 Ns324p128 Ns324p777 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p780 := nat_lit 14933764077043615366958103275595485208934605894456578377482590742446080 

noncomputable def Ns324p781 := nat_lit 904489148001643937159712162077509420915088361155838410241752498176 

noncomputable def Ns324p782 := nat_lit 39110774838398418537563440473535288151004391009087262488361631964266496 

noncomputable def Ns324p783 := BSN.sin_dyadic_bound_f 175610476 268435456 3 2 268435456 134217728 Ns324p780 Ns324p249 Ns324p781 Ns324p782 Ns324p252 Ns324p781 163349581 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 175610476) qz367 0 2 Ns324p780 Ns324p249 Ns324p781 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 175610476) qz368 0 2 Ns324p782 Ns324p252 Ns324p781 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p784 := Ns324p724 121178 BSN.abs_quadSignPos (BSN.cos_quad_nat0 12 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 69835965 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 51 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 163349581 268435456) qz117 rfl rfl (Ns324p775 rfl rfl) (Ns324p757 rfl) RS325to336.d27 RS325to336.d29 RS325to336.d31 RS325to336.d33 RS325to336.d17 (Ns324p779 rfl rfl) (Ns324p783 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p785 := nat_lit 824226277150979068048539921936 

noncomputable def Ns324p786 := BSN.sin_dyadic_bound_f 30130866 268435456 2 1 268435456 134217728 Ns324p785 Ns324p270 Ns324p785 Ns324p785 Ns324p271 Ns324p785 30067634 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 30130866) qz367 0 1 Ns324p785 Ns324p270 Ns324p785 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 30130866) qz368 0 1 Ns324p785 Ns324p271 Ns324p785 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p787 := nat_lit 22095701187864359886603283919521 

noncomputable def Ns324p788 := BSN.cos_dyadic_bound_f 68560969 268435456 2 1 268435456 134217728 Ns324p787 Ns324p149 Ns324p787 Ns324p787 Ns324p150 Ns324p787 259727387 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 68560969) qz369 0 1 Ns324p787 Ns324p149 Ns324p787 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 68560969) qz370 0 1 Ns324p787 Ns324p150 Ns324p787 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p789 := Ns324p722 148070 BSN.abs_quadSignPos (BSN.cos_quad_nat3 107 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 30067634 268435456) BSN.abs_quadSignPos qz595 (BSN.sfrac_eq_quadSignPos_mul Bool.false 259727387 268435456) qz117 rfl rfl (Ns324p784 rfl) (Ns324p757 rfl) RS325to336.d35 RS325to336.d37 RS325to336.d39 RS325to336.d41 RS325to336.d17 (Ns324p786 rfl rfl) (Ns324p788 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p790 := nat_lit 1061666578214785306402880816961 

noncomputable def Ns324p791 := BSN.cos_dyadic_bound_f 32099409 268435456 2 1 268435456 134217728 Ns324p790 Ns324p149 Ns324p790 Ns324p790 Ns324p150 Ns324p790 266518524 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 32099409) qz369 0 1 Ns324p790 Ns324p149 Ns324p790 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 32099409) qz370 0 1 Ns324p790 Ns324p150 Ns324p790 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p792 := Ns324p720 Bool.false 93927035 148070 Bool.true 32099409 14148475504056880 1 Bool.false 266518524 Bool.false Bool.false 178207591 160452 BSN.abs_quadSignPos qz596 (BSN.sfrac_eq_quadSignPos_mul Bool.false 266518524 268435456) qz117 rfl (Ns324p789 rfl) (Ns324p757 rfl) RS325to336.d43 RS325to336.d45 RS325to336.d17 (Ns324p791 rfl rfl) rfl 

noncomputable def Ns324p793 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) 178207591 268435456 160452 268435456 178207591 268435456 160452 268435456 95674471905492992 178207591 134217728 40113 33554432 (Ns324p792 rfl rfl rfl rfl) 

noncomputable def Ns324p794 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz115) (Zeta.RiemannSiegel.correction qz116) 10502309 33554432 1 33554432 307806097702711 562949953421312 2026772235946457 42573090227486720000 3232674750158061059699 18889465931478580854784 

noncomputable def Ns324p795 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz115 1 1 0 1 10502309 33554432 1 33554432 10502309 33554432 1 33554432 

noncomputable abbrev qz123 := qz441

noncomputable def Ns324p796 := @Enclosure.Real.IsNear.sqrt_image qz123 3496313088041 33554432000 654697 33554432000 171257684 171257717 16777216 (@Enclosure.Real.IsNear.of_eq qz123 (@HMul.hMul Real Real Real qz5 qz114 qz3) Bool.false 3496313088041 33554432000 654697 33554432000 (BSN.t_div_two_pi_mk qz114 654697 1000 qz117) (@Enclosure.Real.IsNear.mulLit_ff qz114 qz3 654697 1000 0 1 5340353 33554432 1 33554432 3496313088041 33554432000 654697 33554432000 (Enclosure.Real.IsNear.const Bool.false 654697 1000) RS325to336.d48 rfl)) 

noncomputable abbrev qz751 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 654697 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz643 := qz751

noncomputable abbrev qz449 := qz643

noncomputable abbrev qz124 := qz449

noncomputable def Ns324p797 := @Enclosure.Real.IsNear.sqrt_image qz124 342515401 33554432 33 33554432 53602492 53602498 16777216 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 342515401 33554432 33 33554432 342515401 33554432 33 33554432 (Ns324p796 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns324p798 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz124) 53602495 16777216 3 16777216 5251154 5251155 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz124) Bool.false 107204990 33554432 6 33554432 53602495 16777216 3 16777216 (Ns324p797 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns324p799 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz124)) Bool.false 10502309 33554432 1 33554432 10502309 33554432 1 33554432 (Ns324p798 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz125 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz442))

noncomputable abbrev qz644 := (@HMul.hMul Real Real Real qz723 qz750 qz750)

noncomputable abbrev qz450 := (@HSub.hSub Real Real Real qz586 (@HSub.hSub Real Real Real qz586 qz644 qz639) qz600)

noncomputable abbrev qz126 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz450))

noncomputable def Ns324p800 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz116) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz125) qz126) Bool.false 307806097702711 

noncomputable def Ns324p801 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz125) qz126 127908839 33554432 3139 

noncomputable def Ns324p802 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz125) Bool.false 127908839 33554432 3139 33554432 127908839 33554432 3139 

noncomputable def Ns324p803 := @Enclosure.Real.IsNear.recentre' qz125 Bool.false 4401181 16777216 1045114432 162403450880000 4401181 16777216 16329913 2537553920000 

noncomputable abbrev qz127 := (@HMul.hMul Real Real Real qz349 qz346 qz442)

noncomputable def Ns324p804 := @Enclosure.Real.IsNear.cos_image qz127 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43800593) qz391) Bool.false 43800593 33554432 209 33554432 Bool.false 4401181 16777216 1 

noncomputable def Ns324p805 := nat_lit 890540488558334629846109863 

noncomputable def Ns324p806 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz116 884279719003555 140737488355328 1 500000000000000 6971081 33554432 33 33554432 6164385547831021192955 4722366482869645213696 Ns324p805 

noncomputable def Ns324p807 := @Enclosure.Real.IsNear.subLit_ff_p qz124 qz1 342515401 33554432 33 33554432 10 1 0 1 6971081 6971081 33554432 33 

noncomputable def Ns324p808 := @Ns324p807 33554432 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 342515401 33554432 33 33554432 342515401 33554432 33 33554432 (Ns324p796 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns324p809 := @Enclosure.Real.IsNear.recentre' qz127 Bool.false 6164385547831021192955 4722366482869645213696 Ns324p805 Ns324p173 43800593 33554432 209 33554432 (@Ns324p806 Ns324p173 RS325to336.d47 (Ns324p808 rfl rfl) rfl) 

noncomputable def Ns324p810 := nat_lit 7851971936875043342226495051874141054752220460401472117040766081 

noncomputable def Ns324p811 := nat_lit 13546899919213334823911760582785723839670296382996099335478401 

noncomputable def Ns324p812 := nat_lit 23528822010786703357031661634456851716577320788438424152451341441 

noncomputable def Ns324p813 := BSN.cos_dyadic_bound_f 43800593 33554432 3 2 16777216 4840000 Ns324p810 Ns324p308 Ns324p811 Ns324p812 Ns324p311 Ns324p811 4401181 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 43800593) qz392 0 2 Ns324p810 Ns324p308 Ns324p811 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 43800593) (BSN.cosOddQ 33554432) 0 2 Ns324p812 Ns324p311 Ns324p811 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p814 := @Enclosure.Real.IsNear.inv_image qz125 4401181 16777216 16329913 2537553920000 63952850 63955989 16777216 (Ns324p803 (@Ns324p804 4840000 (Ns324p809 rfl) (Enclosure.sfrac_false_div 43800593 33554432) (Ns324p813 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns324p815 := @Enclosure.Real.IsNear.recentre' qz126 Bool.false 2406449 16777216 

noncomputable abbrev qz128 := (@HMul.hMul Real Real Real qz349 qz346 qz450)

noncomputable def Ns324p816 := @Enclosure.Real.IsNear.cos_image qz128 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 23938811)) qz374) Bool.true 23938811 16777216 

noncomputable def Ns324p817 := nat_lit 226095678045377093942729087725 

noncomputable def Ns324p818 := nat_lit 42297669412805139969557838765738437 

noncomputable def Ns324p819 := @Enclosure.Real.IsNear.recentre' qz128 Bool.true Ns324p817 Ns324p188 Ns324p818 

noncomputable abbrev qz129 := qz450

noncomputable def Ns324p820 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz129 884279719003555 140737488355328 1 500000000000000 255683437250095 

noncomputable abbrev qz451 := (@HSub.hSub Real Real Real qz586 qz644 qz639)

noncomputable abbrev qz130 := qz451

noncomputable def Ns324p821 := @Enclosure.Real.IsNear.subLit_tf qz130 qz29 185314693072431 1125899906842624 1567388691 1125899906842624 1 16 

noncomputable abbrev qz452 := qz644

noncomputable abbrev qz131 := qz452

noncomputable def Ns324p822 := @Enclosure.Real.IsNear.subLit_ff_n qz131 qz116 48595970308561 1125899906842624 460092435 1125899906842624 6971081 33554432 33 33554432 

noncomputable def Ns324p823 := @Enclosure.Real.IsNear.mulLit_ff qz116 qz116 6971081 33554432 33 33554432 6971081 33554432 33 33554432 48595970308561 1125899906842624 

noncomputable def Ns324p824 := nat_lit 41244475044930546816488321245779904235309165580328413664530166910228057866058346207268633822801 

noncomputable def Ns324p825 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600 

noncomputable def Ns324p826 := nat_lit 35418560897526499735848414258969783185265539807690452954982218582714980751718938922698321 

noncomputable def Ns324p827 := nat_lit 249805743552115198196458236188849935164022264255298935053935294086196080772971371472264705590865 

noncomputable def Ns324p828 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600 

noncomputable def Ns324p829 := BSN.cos_dyadic_bound_f 23938811 16777216 4 3 16777216 4840000 Ns324p824 Ns324p825 Ns324p826 Ns324p827 Ns324p828 Ns324p826 2406449 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 23938811) qz601 0 3 Ns324p824 Ns324p825 Ns324p826 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 23938811) (BSN.cosOddQ 16777216) 0 3 Ns324p827 Ns324p828 Ns324p826 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p830 := @Ns324p815 728257216 81201725440000 2406449 16777216 11379019 1268776960000 (@Ns324p816 147 16777216 Bool.false 2406449 16777216 1 4840000 (@Ns324p819 Ns324p191 23938811 16777216 147 16777216 (@Ns324p820 1125899906842624 1567388691 1125899906842624 Ns324p817 Ns324p188 Ns324p818 Ns324p191 RS325to336.d47 (@Ns324p821 0 1 4090934996001520 255683437250095 1125899906842624 1567388691 1125899906842624 (@Ns324p822 6218129267299757064192 185314693072431 1125899906842624 1567388691 1125899906842624 (@Ns324p823 460092435 1125899906842624 (Ns324p808 rfl rfl) (Ns324p808 rfl rfl) rfl) (Ns324p808 rfl rfl) rfl rfl) qz379 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 23938811 16777216) (BSN.cos_neg_of_bound 23938811 16777216 Bool.false 2406449 16777216 1 4840000 (Ns324p829 rfl rfl)) rfl rfl) 

noncomputable def Ns324p831 := @Ns324p794 4261813631488320467009 Ns324p717 (Ns324p795 qz31 (@Enclosure.Real.IsNear.of_eq qz115 (@Inv.inv Real Real.instInv (Real.sqrt qz124)) Bool.false 10502309 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz123 (BSN.t_div_two_pi_nonneg qz114 654697 1000 qz117)) Ns324p799) rfl) (@Ns324p800 562949953421312 2026772235946457 42573090227486720000 (BSN.correction_mk qz116 (BSN.cos_two_pi_p_ne_zero_mk qz114 654697 1000 10 qz117 rfl rfl (@BSN.floor_sqrt_eq_dec qz114 654697 1000 10 qz117 rfl rfl rfl))) (@Ns324p801 33554432 2406449 16777216 11379019 1268776960000 307806097702711 562949953421312 2026772235946457 42573090227486720000 (@Ns324p802 33554432 (Ns324p814 rfl rfl rfl rfl rfl) rfl) (Ns324p830 rfl) rfl)) 

noncomputable def Ns324p832 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz114) (hardyZApproximantRS₀ qz114) Bool.false 21847814013035493835149 18889465931478580854784 345808687290523280339009 Ns324p717 (@Eq.refl Real (hardyZApproximantRS₀ qz114)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz114) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz115) (Zeta.RiemannSiegel.correction qz116))) Bool.false 21847814013035493835149 18889465931478580854784 345808687290523280339009 Ns324p717 (BSN.hardyZApproximantRS₀_eq qz114 10 (@BSN.floor_sqrt_eq_dec qz114 654697 1000 10 qz117 rfl rfl rfl)) (@Ns324p719 21847814013035493835149 18889465931478580854784 345808687290523280339009 Ns324p717 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (@HAdd.hAdd Real Real Real qz366 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 10)) Bool.false 178207591 134217728 40113 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (Ns324p793 (Ns324p792 rfl rfl rfl rfl) rfl rfl)) (Ns324p831 rfl) rfl rfl)) 

theorem RS325to336.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz114) Bool.false 21847814013035493835149 18889465931478580854784 345808687290523280339009 Ns324p717 := Ns324p832 

noncomputable def Ns324p833 := nat_lit 54450160402253192951721099264 

noncomputable abbrev qz752 := (Enclosure.sfrac Bool.false 656302 1000)

noncomputable abbrev qz645 := qz752

noncomputable abbrev qz453 := qz645

noncomputable abbrev qz132 := qz453

noncomputable abbrev qz133 := qz584

noncomputable abbrev qz753 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 656302 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz646 := qz753

noncomputable abbrev qz454 := qz646

noncomputable abbrev qz134 := qz454

noncomputable abbrev qz135 := qz351

noncomputable abbrev qz754 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 656302 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz647 := qz754

noncomputable abbrev qz455 := qz647

noncomputable abbrev qz136 := qz455

noncomputable abbrev qz648 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz133 qz134 qz135))

noncomputable def Ns324p834 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (@HMul.hMul Real Real Real qz5 qz648 (Zeta.RiemannSiegel.correction qz136)) 81075237 67108864 80423 67108864 98225290735275704055 590295810358705651712 7552576277324685781563 Ns324p74 Ns324p833 

noncomputable def Ns324p835 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.cos BSN.quadSignPos 9 10 656302 1000 200 268435456 134217728 4503599627370496 Bool.false 321302831094 2465 618095470 56 84886744 8 

noncomputable def Ns324p836 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 656302 1000 106 156 268435456 134217728 4503599627370496 Bool.false 321302831094 2465 

noncomputable def Ns324p837 := Ns324p836 558195838 56 94906264 8 589812974 56 89478488 8 Bool.true 309865111 121476 Bool.true 346526380 Bool.true 14044558 14148475504056880 1 Bool.false 74153977 Bool.true Bool.false 268068133 Bool.false Bool.true 246726454 

noncomputable def Ns324p838 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 656302 1000 13 51 268435456 134217728 4503599627370496 Bool.false 321302831094 2465 

noncomputable def Ns324p839 := Ns324p838 480971758 57 109588312 8 522351262 57 101459064 8 Bool.true 253676010 90107 Bool.false 158557807 Bool.true 12818017 14148475504056880 1 Bool.false 149497298 Bool.true Bool.false 12813146 Bool.false Bool.true 309865111 

noncomputable def Ns324p840 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 656302 1000 182 89 268435456 134217728 4503599627370496 Bool.false 321302831094 2465 

noncomputable def Ns324p841 := Ns324p840 372130544 56 134217720 8 432030192 56 120047984 16 Bool.true 117666638 52931 Bool.false 331158861 Bool.false 233040908 14148475504056880 1 Bool.false 88793954 Bool.true Bool.false 204851549 Bool.true Bool.true 253676010 

noncomputable def Ns324p842 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 656302 1000 472 302 268435456 134217728 4503599627370496 Bool.false 321302831094 2465 

noncomputable def Ns324p843 := Ns324p842 186065264 56 189812528 16 294906480 56 154981288 8 Bool.true 268435424 2528 Bool.false 165520058 Bool.false 414575120 14148475504056880 1 Bool.false 219001276 Bool.false Bool.false 7081486 Bool.true Bool.true 117666638 

noncomputable def Ns324p844 := nat_lit 7572340235634625246510376848742789508397746502153845407 

noncomputable def Ns324p845 := nat_lit 6326382488484975926108535264556394549628798763008000 

noncomputable def Ns324p846 := nat_lit 58446769893579389722972529935360000 

noncomputable def Ns324p847 := nat_lit 230152454186644751684381308752795832320 

noncomputable abbrev qz649 := (@Eq.refl Real qz752)

noncomputable abbrev qz456 := qz649

noncomputable abbrev qz137 := qz456

noncomputable def Ns324p848 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz132 656302 1000 1722930260816 16000000 1312604 4000 2000 Ns324p846 Ns324p847 qz137 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns324p849 := nat_lit 155081528025797125048532517862252329131985848364110753935360 

noncomputable abbrev qz650 := (@HSub.hSub Real Real Real qz727 qz728 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz729 (@Nat.cast Real Real.instNatCast 1312604))))

noncomputable abbrev qz457 := (@HSub.hSub Real Real Real qz586 (@HMul.hMul Real Real Real qz582 (Enclosure.sfrac Bool.false 656302 4000) (Real.log (Enclosure.sfrac Bool.false 1722930260816 16000000))) (@HMul.hMul Real Real Real qz582 qz587 qz650))

noncomputable abbrev qz651 := (Enclosure.sfrac Bool.false 656302 2000)

noncomputable abbrev qz138 := (@HSub.hSub Real Real Real qz354 (@HSub.hSub Real Real Real qz354 qz457 qz651) (@HMul.hMul Real Real Real qz349 qz651 (Real.log Real.pi)))

noncomputable def Ns324p850 := @Enclosure.Real.IsNear.addLit_ft_p qz138 (Enclosure.sfrac Bool.true Ns324p846 Ns324p847) 673821017796483533123 562949953421312000 2274623077873441939 247808000000000000000000 Ns324p846 Ns324p847 0 1 Ns324p849 

noncomputable def Ns324p851 := nat_lit 22609681521822896551295451136000 

noncomputable abbrev qz139 := (@HSub.hSub Real Real Real qz354 qz457 qz651)

noncomputable def Ns324p852 := @Enclosure.Real.IsNear.subLit_ff_p qz139 (@HMul.hMul Real Real Real qz5 qz651 (Real.log Real.pi)) 885289934026232088899 562949953421312000 518986255165293 121000000000000000000 12604529632911 33554432000 328151 67108864000 Ns324p851 673821017796483533123 562949953421312000 

noncomputable def Ns324p853 := nat_lit 1770579868052464177798000 

noncomputable abbrev qz140 := qz457

noncomputable def Ns324p854 := @Enclosure.Real.IsNear.subLit_ff_p qz140 qz651 1070022524191389043011 562949953421312000 518986255165293 121000000000000000000 656302 2000 0 1 Ns324p853 885289934026232088899 562949953421312000 518986255165293 121000000000000000000 

noncomputable def Ns324p855 := nat_lit 2409476520613188617919519715888201728 

noncomputable def Ns324p856 := nat_lit 56031043940377925647335424 

noncomputable def Ns324p857 := nat_lit 27756085329323959658446212218338374681275576206732174043150124295678319992026835391077157524122729621469561076213417495932046069589724500397103390455234560 

noncomputable def Ns324p858 := nat_lit 568068481723271519437070361911187111304703721858536274187769210754364068556852504796992347145703633616925065378638682184173775300343483040327842956050432 

noncomputable def Ns324p859 := nat_lit 91935187094185680182101743423732277460810117228623123965607587336743946618826704931849221173103634232077247374515156159739717534702684169431941120 

noncomputable def Ns324p860 := BSN.log_dyadic_bound 674354260816 2771506260816 7 6 Ns324p857 134217728 38720000 Ns324p858 Ns324p859 66651641 3445860521632 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 674354260816) (BSN.artanhQ 2771506260816) 0 6 Ns324p858 Ns324p857 Ns324p859 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz458 := (Real.log (Enclosure.sfrac Bool.false 1722930260816 16000000))

noncomputable def Ns324p861 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 656302 4000) qz458 656302 4000 0 1 3261436006309111 281474976710656 195312621 7562500000000000 1070243486906341083761 562949953421312000 64092031893771 15125000000000000000 (Enclosure.Real.IsNear.const Bool.false 656302 4000) (BSN.isNear_log_sfrac 1722930260816 16000000 3261436006309111 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1722930260816) qz357)) Bool.false Ns324p856 Ns324p98 1000000619520000 38720000000000000000000 3261436006309111 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1722930260816 16000000 16 3445860521632 2097152000000 66651641 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns324p860 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns324p862 := BSN.arctan_dyadic_bound_f 1000 1312604 1 0 16777216 4840000 0 1 1 0 1 1 12781 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1312604) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1312604) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz459 := (@Nat.cast Real Real.instNatCast 1312604)

noncomputable def Ns324p863 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz459)) 884279719003555 562949953421312 1 2000000000000000 12781 16777216 1 4840000 14828556786787269214208 883850859808163 562949953421312 50000000121 242000000000000000 qz15 (Ns324p862 rfl) rfl rfl 

noncomputable abbrev qz460 := (@HMul.hMul Real Real Real qz582 qz587 qz650)

noncomputable abbrev qz141 := qz460

noncomputable abbrev qz461 := qz650

noncomputable abbrev qz142 := qz461

noncomputable def Ns324p864 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 656302 4000) qz458) qz141 1070243486906341083761 562949953421312000 64092031893771 15125000000000000000 883850859808163 2251799813685248 50000000121 968000000000000000 Ns324p855 1070022524191389043011 562949953421312000 518986255165293 121000000000000000000 (Ns324p861 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz142 1 4 0 1 883850859808163 562949953421312 50000000121 242000000000000000 883850859808163 2251799813685248 50000000121 968000000000000000 qz365 Ns324p863 rfl) 

noncomputable def Ns324p865 := @Ns324p850 Ns324p844 Ns324p845 2274623077873441939 247808000000000000000000 (@Ns324p852 2274623077873441939 247808000000000000000000 (Ns324p854 (Ns324p864 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 656302 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz651 (Real.log Real.pi) 656302 2000 0 1 38410761 33554432 1 67108864 12604529632911 33554432000 328151 67108864000 (Enclosure.Real.IsNear.const Bool.false 656302 2000) RS325to336.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns324p846 Ns324p847) 

noncomputable def Ns324p866 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz132) Bool.false Ns324p844 Ns324p845 2274623077873441939 247808000000000000000000 20081426943 16777216 309 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz132) (@HAdd.hAdd Real Real Real qz366 qz138 (Enclosure.sfrac Bool.true Ns324p846 Ns324p847)) Bool.false Ns324p844 Ns324p845 2274623077873441939 247808000000000000000000 Ns324p848 (Ns324p865 rfl rfl)) 

noncomputable def Ns324p867 := nat_lit 3796788284750888452489216 

noncomputable def Ns324p868 := nat_lit 3506524108861317652305816512687260358244354766672163252033872223531806195076584012768312666566405641652501620981238270037636530964258260241 

noncomputable def Ns324p869 := nat_lit 2493439937849208880167327053737684703940821113208608852883563210113178520586962143193870431444666265686338804603327062407937095533841 

noncomputable def Ns324p870 := nat_lit 17510860758986836042371705802905281544622490394677274301641812384484966269172480023727519757936117538186633409998124510682185116757054358801 

noncomputable def Ns324p871 := BSN.sin_dyadic_bound_f 107911213397 68719476736 4 3 33554432 9689454 Ns324p868 Ns324p110 Ns324p869 Ns324p870 Ns324p113 Ns324p869 33554428 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107911213397) qz593 0 3 Ns324p868 Ns324p110 Ns324p869 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107911213397) qz594 0 3 Ns324p870 Ns324p113 Ns324p869 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p872 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz132) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20081426943) qz374) Bool.false 20081426943 16777216 309 33554432 Bool.true 33554428 33554432 1 4840000 (Ns324p866 rfl) (Enclosure.sfrac_false_div 20081426943 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20081426943) qz374) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns324p867) qz626) 226375608064910080 72057594037927936 Bool.false 33554428 33554432 190 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q1 20081426943 16777216 226375608064910080 72057594037927936 190 Ns324p867 Ns324p518 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554428 33554432 Ns324p867 Ns324p518 107911213397 68719476736 9689454 9680000 (Ns324p871 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns324p873 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz132) Bool.false Ns324p844 Ns324p845 2274623077873441939 247808000000000000000000 321302831094 268435456 2465 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz132) (@HAdd.hAdd Real Real Real qz366 qz138 (Enclosure.sfrac Bool.true Ns324p846 Ns324p847)) Bool.false Ns324p844 Ns324p845 2274623077873441939 247808000000000000000000 Ns324p848 (Ns324p865 rfl rfl)) 

noncomputable def Ns324p874 := Ns324p843 52931 BSN.abs_quadSignPos (BSN.cos_quad_nat0 472 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 219001276 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 302 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 7081486 268435456) qz137 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 1) Bool.true 8388607 8388608 23892413 2537553920000 268435424 268435456 2528 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz132)) Bool.true 8388607 8388608 23892413 2537553920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz132) qz132) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz132)) Bool.true 33554428 33554432 1529114432 162403450880000 8388607 8388608 23892413 2537553920000 (Ns324p872 rfl rfl) rfl)) rfl) (Ns324p873 rfl) RS325to336.d7 

noncomputable def Ns324p875 := nat_lit 6548000190955280079589712704484701604669434131514684851761034092912896 

noncomputable def Ns324p876 := nat_lit 563384687239184865512956688469289132413506155931976907701538038016 

noncomputable def Ns324p877 := nat_lit 19642873803491361869038112200077166235743475382232190601467699202662656 

noncomputable def Ns324p878 := BSN.cos_dyadic_bound_f 165520058 268435456 3 2 268435456 134217728 Ns324p875 Ns324p263 Ns324p876 Ns324p877 Ns324p266 Ns324p876 219001276 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 165520058) qz369 0 2 Ns324p875 Ns324p263 Ns324p876 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 165520058) qz370 0 2 Ns324p877 Ns324p266 Ns324p876 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p879 := nat_lit 15948749015788280117356506083633293069831954703339344712690048655553243632239715049635173297424626089984000000 

noncomputable def Ns324p880 := nat_lit 25777382826236742276725181856837538846972766319709517179193417331213235706030479243273568256000000000000 

noncomputable def Ns324p881 := nat_lit 96537912280245422865605711655002227448369597447981141114525820138618504074691324864667238527539818895769600000 

noncomputable def Ns324p882 := BSN.cos_dyadic_bound_f 414575120 268435456 4 3 268435456 134217728 Ns324p879 Ns324p125 Ns324p880 Ns324p881 Ns324p128 Ns324p880 7081486 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 414575120) qz369 0 3 Ns324p879 Ns324p125 Ns324p880 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 414575120) qz370 0 3 Ns324p881 Ns324p128 Ns324p880 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p883 := nat_lit 6480205038042625370909996443575194168788104428251845615660128601733105412953383489009497899627418429171457201 

noncomputable def Ns324p884 := nat_lit 1739548582555417850342432820701260670857357108072553953037479292960966358091989236026111401148525599921 

noncomputable def Ns324p885 := nat_lit 39277150153444995175580257919357717228125856632434256861550200655342466003459423441066230219443360012921494705 

noncomputable def Ns324p886 := BSN.cos_dyadic_bound_f 331158861 268435456 4 3 268435456 134217728 Ns324p883 Ns324p125 Ns324p884 Ns324p885 Ns324p128 Ns324p884 88793954 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 331158861) qz369 0 3 Ns324p883 Ns324p125 Ns324p884 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 331158861) qz370 0 3 Ns324p885 Ns324p128 Ns324p884 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p887 := nat_lit 46318184289020430041233449633094711215610084407688135472725477570969600 

noncomputable def Ns324p888 := nat_lit 8698759226712039154243375802250416065855643804553470351807694831616 

noncomputable def Ns324p889 := nat_lit 121295446575353116330314069287758695367253121453975839667044752608526336 

noncomputable def Ns324p890 := BSN.sin_dyadic_bound_f 233040908 268435456 3 2 268435456 134217728 Ns324p887 Ns324p249 Ns324p888 Ns324p889 Ns324p252 Ns324p888 204851549 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 233040908) qz367 0 2 Ns324p887 Ns324p249 Ns324p888 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 233040908) qz368 0 2 Ns324p889 Ns324p252 Ns324p888 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p891 := Ns324p841 90107 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 182 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 88793954 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 89 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 204851549 268435456) qz137 rfl rfl (Ns324p874 RS325to336.d9 RS325to336.d11 RS325to336.d13 RS325to336.d17 (Ns324p878 rfl rfl) (Ns324p882 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns324p873 rfl) RS325to336.d19 RS325to336.d21 RS325to336.d23 RS325to336.d25 RS325to336.d17 (Ns324p886 rfl rfl) (Ns324p890 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns324p892 := nat_lit 9924515284288574026503349083048957827252422397153789352806928242354305 

noncomputable def Ns324p893 := nat_lit 399485521566959867641661466787027263511950715902887043832104528001 

noncomputable def Ns324p894 := nat_lit 25992131339435156896294494432277234360567801215196081725947179132168321 

noncomputable def Ns324p895 := BSN.sin_dyadic_bound_f 158557807 268435456 3 2 268435456 134217728 Ns324p892 Ns324p249 Ns324p893 Ns324p894 Ns324p252 Ns324p893 149497298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 158557807) qz367 0 2 Ns324p892 Ns324p249 Ns324p893 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 158557807) qz368 0 2 Ns324p894 Ns324p252 Ns324p893 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p896 := nat_lit 26995002556751179776915419521 

noncomputable def Ns324p897 := BSN.sin_dyadic_bound_f 12818017 268435456 2 1 268435456 134217728 Ns324p896 Ns324p270 Ns324p896 Ns324p896 Ns324p271 Ns324p896 12813146 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 12818017) qz367 0 1 Ns324p896 Ns324p270 Ns324p896 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 12818017) qz368 0 1 Ns324p896 Ns324p271 Ns324p896 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p898 := Ns324p839 121476 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 13 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 149497298 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 51 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 12813146 268435456) qz137 rfl rfl (Ns324p891 rfl rfl) (Ns324p873 rfl) RS325to336.d27 RS325to336.d29 RS325to336.d31 RS325to336.d33 RS325to336.d17 (Ns324p895 rfl rfl) (Ns324p897 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p899 := nat_lit 7771546099429781168976678605072774339323056015753473851945749620299501250447495907002972134600228470784000000 

noncomputable def Ns324p900 := nat_lit 2998027558809645239063916663750143983329300170230437102583010063728001574150492835522809856000000000000 

noncomputable def Ns324p901 := nat_lit 47095493405534572655833050718742459979741954635873700298318710485711210028084865917797774293021361019289600000 

noncomputable def Ns324p902 := BSN.cos_dyadic_bound_f 346526380 268435456 4 3 268435456 134217728 Ns324p899 Ns324p125 Ns324p900 Ns324p901 Ns324p128 Ns324p900 74153977 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 346526380) qz369 0 3 Ns324p899 Ns324p125 Ns324p900 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 346526380) qz370 0 3 Ns324p901 Ns324p128 Ns324p900 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p903 := nat_lit 38907408414513654357879252496 

noncomputable def Ns324p904 := BSN.cos_dyadic_bound_f 14044558 268435456 2 1 268435456 134217728 Ns324p903 Ns324p149 Ns324p903 Ns324p903 Ns324p150 Ns324p903 268068133 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 14044558) qz369 0 1 Ns324p903 Ns324p149 Ns324p903 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 14044558) qz370 0 1 Ns324p903 Ns324p150 Ns324p903 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p905 := Ns324p837 148434 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 106 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 74153977 268435456) BSN.abs_quadSignPos qz595 (BSN.sfrac_eq_quadSignPos_mul Bool.false 268068133 268435456) qz137 rfl rfl (Ns324p898 rfl) (Ns324p873 rfl) RS325to336.d35 RS325to336.d37 RS325to336.d39 RS325to336.d41 RS325to336.d17 (Ns324p902 rfl rfl) (Ns324p904 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p906 := nat_lit 278694395855492805815254118656 

noncomputable def Ns324p907 := BSN.cos_dyadic_bound_f 22976404 268435456 2 1 268435456 134217728 Ns324p906 Ns324p149 Ns324p906 Ns324p906 Ns324p150 Ns324p906 267452737 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 22976404) qz369 0 1 Ns324p906 Ns324p149 Ns324p906 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 22976404) qz370 0 1 Ns324p906 Ns324p150 Ns324p906 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p908 := Ns324p835 Bool.true 246726454 148434 Bool.true 22976404 14148475504056880 1 Bool.false 267452737 Bool.false Bool.true 162150474 160846 BSN.abs_quadSignPos qz596 (BSN.sfrac_eq_quadSignPos_mul Bool.false 267452737 268435456) qz137 rfl (Ns324p905 rfl) (Ns324p873 rfl) RS325to336.d43 RS325to336.d45 RS325to336.d17 (Ns324p907 rfl rfl) rfl 

noncomputable def Ns324p909 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) 162150474 268435456 160846 268435456 162150474 268435456 160846 268435456 87053872857612288 81075237 67108864 80423 67108864 (Ns324p908 rfl rfl rfl rfl) 

noncomputable def Ns324p910 := @Enclosure.Real.IsNear.mulLit_ff qz648 (Zeta.RiemannSiegel.correction qz136) 5247941 16777216 1 16777216 18716919785355 35184372088832 2873984712809153 42573090227486720000 98225290735275704055 590295810358705651712 

noncomputable abbrev qz652 := (@HPow.hPow Real Real Real qz133 qz134 qz135)

noncomputable def Ns324p911 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz652 1 1 0 1 5247941 16777216 1 16777216 5247941 16777216 1 16777216 

noncomputable def Ns324p912 := @Enclosure.Real.IsNear.sqrt_image qz134 1752442177303 16777216000 328151 16777216000 171467476 171467509 16777216 (@Enclosure.Real.IsNear.of_eq qz134 (@HMul.hMul Real Real Real qz5 qz132 qz3) Bool.false 1752442177303 16777216000 328151 16777216000 (BSN.t_div_two_pi_mk qz132 656302 1000 qz137) (@Enclosure.Real.IsNear.mulLit_ff qz132 qz3 656302 1000 0 1 5340353 33554432 1 33554432 1752442177303 16777216000 328151 16777216000 (Enclosure.Real.IsNear.const Bool.false 656302 1000) RS325to336.d48 rfl)) 

noncomputable abbrev qz755 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 656302 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz653 := qz755

noncomputable abbrev qz462 := qz653

noncomputable abbrev qz143 := qz462

noncomputable def Ns324p913 := @Enclosure.Real.IsNear.sqrt_image qz143 342934985 33554432 33 33554432 53635313 53635319 16777216 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 342934985 33554432 33 33554432 342934985 33554432 33 33554432 (Ns324p912 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns324p914 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz143) 13408829 4194304 3 16777216 5247940 5247942 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz143) Bool.false 107270632 33554432 6 33554432 13408829 4194304 3 16777216 (Ns324p913 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns324p915 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 10495882 33554432 2 33554432 5247941 16777216 1 16777216 (Ns324p914 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz144 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz455))

noncomputable abbrev qz654 := (@HMul.hMul Real Real Real qz723 qz754 qz754)

noncomputable abbrev qz463 := (@HSub.hSub Real Real Real qz586 (@HSub.hSub Real Real Real qz586 qz654 qz647) qz600)

noncomputable abbrev qz145 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz463))

noncomputable def Ns324p916 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz136) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz144) qz145) Bool.false 18716919785355 

noncomputable def Ns324p917 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz144) qz145 180611205 33554432 6257 

noncomputable def Ns324p918 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz144) Bool.false 180611205 33554432 6257 33554432 180611205 33554432 6257 

noncomputable def Ns324p919 := @Enclosure.Real.IsNear.recentre' qz144 Bool.false 3116916 16777216 1045114432 162403450880000 779229 4194304 16329913 2537553920000 

noncomputable abbrev qz146 := (@HMul.hMul Real Real Real qz349 qz346 qz455)

noncomputable def Ns324p920 := @Enclosure.Real.IsNear.cos_image qz146 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46436917) qz391) Bool.false 46436917 33554432 209 33554432 Bool.false 3116916 16777216 1 

noncomputable def Ns324p921 := nat_lit 890540488561938828961959591 

noncomputable def Ns324p922 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz136 884279719003555 140737488355328 1 500000000000000 7390665 33554432 33 33554432 6535415169449408814075 4722366482869645213696 Ns324p921 

noncomputable def Ns324p923 := @Enclosure.Real.IsNear.subLit_ff_p qz143 qz1 342934985 33554432 33 33554432 10 1 0 1 7390665 7390665 33554432 33 

noncomputable def Ns324p924 := @Ns324p923 33554432 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 342934985 33554432 33 33554432 342934985 33554432 33 33554432 (Ns324p912 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns324p925 := @Enclosure.Real.IsNear.recentre' qz146 Bool.false 6535415169449408814075 4722366482869645213696 Ns324p921 Ns324p173 46436917 33554432 209 33554432 (@Ns324p922 Ns324p173 RS325to336.d47 (Ns324p924 rfl rfl) rfl) 

noncomputable def Ns324p926 := nat_lit 149460314516525779773866864370212828680787381828117366162739107286977639577130992183734716182410641 

noncomputable def Ns324p927 := nat_lit 100545015314432430108625801849010785775874132446084006953899968916831714215624210209702262161 

noncomputable def Ns324p928 := nat_lit 905408410356319251508745574955648654856117427877479900937707703646826346052010114037626993607292305 

noncomputable def Ns324p929 := BSN.cos_dyadic_bound_f 46436917 33554432 4 3 16777216 4840000 Ns324p926 Ns324p594 Ns324p927 Ns324p928 Ns324p597 Ns324p927 3116916 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 46436917) qz392 0 3 Ns324p926 Ns324p594 Ns324p927 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 46436917) (BSN.cosOddQ 33554432) 0 3 Ns324p928 Ns324p597 Ns324p927 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p930 := @Enclosure.Real.IsNear.inv_image qz144 779229 4194304 16329913 2537553920000 90302474 90308731 16777216 (Ns324p919 (@Ns324p920 4840000 (Ns324p925 rfl) (Enclosure.sfrac_false_div 46436917 33554432) (Ns324p929 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns324p931 := @Enclosure.Real.IsNear.recentre' qz145 Bool.false 1658096 16777216 

noncomputable abbrev qz147 := (@HMul.hMul Real Real Real qz349 qz346 qz463)

noncomputable def Ns324p932 := @Enclosure.Real.IsNear.cos_image qz147 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 12346391)) (@Nat.cast Real Real.instNatCast 8388608)) Bool.true 12346391 8388608 

noncomputable def Ns324p933 := nat_lit 233216733069797619381172216045 

noncomputable def Ns324p934 := nat_lit 43044982493526584458175086864509893 

noncomputable def Ns324p935 := @Enclosure.Real.IsNear.recentre' qz147 Bool.true Ns324p933 Ns324p188 Ns324p934 

noncomputable abbrev qz148 := qz463

noncomputable def Ns324p936 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz148 884279719003555 140737488355328 1 500000000000000 263736381212719 

noncomputable abbrev qz464 := (@HSub.hSub Real Real Real qz586 qz654 qz647)

noncomputable abbrev qz149 := qz464

noncomputable def Ns324p937 := @Enclosure.Real.IsNear.subLit_tf qz149 qz29 193367637035055 1125899906842624 1595081235 1125899906842624 1 16 

noncomputable abbrev qz465 := qz654

noncomputable abbrev qz150 := qz465

noncomputable def Ns324p938 := @Enclosure.Real.IsNear.subLit_ff_n qz150 qz136 54621929142225 1125899906842624 487784979 1125899906842624 7390665 33554432 33 33554432 

noncomputable def Ns324p939 := @Enclosure.Real.IsNear.mulLit_ff qz136 qz136 7390665 33554432 33 33554432 7390665 33554432 33 33554432 54621929142225 1125899906842624 

noncomputable def Ns324p940 := nat_lit 11402940519427061378461490706406399261731255988493744872312864772712248385637061014045649761 

noncomputable def Ns324p941 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600 

noncomputable def Ns324p942 := nat_lit 12545278853541665715391289094074217811151115620024605908462686501865301341388150205281 

noncomputable def Ns324p943 := nat_lit 69049319371238568826410368816207712052500128229763375799207450681776273513211209256900291425 

noncomputable def Ns324p944 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600 

noncomputable def Ns324p945 := BSN.cos_dyadic_bound_f 12346391 8388608 4 3 16777216 4840000 Ns324p940 Ns324p941 Ns324p942 Ns324p943 Ns324p944 Ns324p942 1658096 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 12346391) (BSN.cosEvenQ 8388608) 0 3 Ns324p940 Ns324p941 Ns324p942 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 12346391) (BSN.cosOddQ 8388608) 0 3 Ns324p943 Ns324p944 Ns324p942 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p946 := @Ns324p931 1480714432 162403450880000 103631 1048576 23136163 2537553920000 (@Ns324p932 299 33554432 Bool.false 1658096 16777216 1 4840000 (@Ns324p935 Ns324p191 12346391 8388608 299 33554432 (@Ns324p936 1125899906842624 1595081235 1125899906842624 Ns324p933 Ns324p188 Ns324p934 Ns324p191 RS325to336.d47 (@Ns324p937 0 1 4219782099403504 263736381212719 1125899906842624 1595081235 1125899906842624 (@Ns324p938 6488341227893434613760 193367637035055 1125899906842624 1595081235 1125899906842624 (@Ns324p939 487784979 1125899906842624 (Ns324p924 rfl rfl) (Ns324p924 rfl rfl) rfl) (Ns324p924 rfl rfl) rfl rfl) qz379 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 12346391 8388608) (BSN.cos_neg_of_bound 12346391 8388608 Bool.false 1658096 16777216 1 4840000 (Ns324p945 rfl rfl)) rfl rfl) 

noncomputable def Ns324p947 := @Ns324p910 7552576277324685781563 Ns324p74 (Ns324p911 qz31 (@Enclosure.Real.IsNear.of_eq qz652 (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 5247941 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz134 (BSN.t_div_two_pi_nonneg qz132 656302 1000 qz137)) Ns324p915) rfl) (@Ns324p916 35184372088832 2873984712809153 42573090227486720000 (BSN.correction_mk qz136 (BSN.cos_two_pi_p_ne_zero_mk qz132 656302 1000 10 qz137 rfl rfl (@BSN.floor_sqrt_eq_dec qz132 656302 1000 10 qz137 rfl rfl rfl))) (@Ns324p917 33554432 103631 1048576 23136163 2537553920000 18716919785355 35184372088832 2873984712809153 42573090227486720000 (@Ns324p918 33554432 (Ns324p930 rfl rfl rfl rfl rfl) rfl) (Ns324p946 rfl) rfl)) 

noncomputable def Ns324p948 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz132) (hardyZApproximantRS₀ qz132) Bool.true 811370617184835567351 590295810358705651712 435534530697970246101563 Ns324p74 (@Eq.refl Real (hardyZApproximantRS₀ qz132)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz132) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (@HMul.hMul Real Real Real qz5 qz648 (Zeta.RiemannSiegel.correction qz136))) Bool.true 811370617184835567351 590295810358705651712 435534530697970246101563 Ns324p74 (BSN.hardyZApproximantRS₀_eq qz132 10 (@BSN.floor_sqrt_eq_dec qz132 656302 1000 10 qz137 rfl rfl rfl)) (@Ns324p834 811370617184835567351 590295810358705651712 435534530697970246101563 Ns324p74 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (@HAdd.hAdd Real Real Real qz366 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 10)) Bool.true 81075237 67108864 80423 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (Ns324p909 (Ns324p908 rfl rfl rfl rfl) rfl rfl)) (Ns324p947 rfl) rfl rfl)) 

theorem RS325to336.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz132) Bool.true 811370617184835567351 590295810358705651712 435534530697970246101563 Ns324p74 := Ns324p948 

noncomputable def Ns324p949 := nat_lit 7142579305340338385715200 

noncomputable def Ns324p950 := nat_lit 426690698536715084482106884096 

noncomputable abbrev qz756 := (Enclosure.sfrac Bool.false 657653 1000)

noncomputable abbrev qz655 := qz756

noncomputable abbrev qz466 := qz655

noncomputable abbrev qz151 := qz466

noncomputable abbrev qz757 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 657653 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz656 := qz757

noncomputable abbrev qz467 := qz656

noncomputable abbrev qz152 := qz467

noncomputable abbrev qz758 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 657653 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz657 := qz758

noncomputable abbrev qz468 := qz657

noncomputable abbrev qz153 := qz468

noncomputable abbrev qz658 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz133 qz152 qz135))

noncomputable def Ns324p951 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz151) qz151 10) (@HMul.hMul Real Real Real qz5 qz658 (Zeta.RiemannSiegel.correction qz153)) 202537085 134217728 40295 33554432 383976640808173297353 2361183241434822606848 233963573054183714949 Ns324p949 Ns324p950 

noncomputable def Ns324p952 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.cos BSN.quadSignPos 9 10 657653 1000 200 268435456 134217728 4503599627370496 Bool.false 322145965711 2470 618095470 56 84886744 8 

noncomputable def Ns324p953 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 657653 1000 106 155 268435456 134217728 4503599627370496 Bool.false 322145965711 2470 

noncomputable def Ns324p954 := Ns324p953 558195838 56 94906264 8 589812974 56 89478488 8 Bool.false 83431310 121729 Bool.true 257514340 Bool.true 389404697 14148475504056880 1 Bool.false 154103546 Bool.true Bool.false 266500190 Bool.false Bool.false 117780879 

noncomputable def Ns324p955 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 657653 1000 13 50 268435456 134217728 4503599627370496 Bool.false 322145965711 2470 

noncomputable def Ns324p956 := Ns324p955 480971758 57 109588312 8 522351262 57 101459064 8 Bool.false 234768221 90295 Bool.false 351899579 Bool.true 297037383 14148475504056880 1 Bool.false 259422424 Bool.true Bool.false 120191598 Bool.true Bool.false 83431310 

noncomputable def Ns324p957 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 657653 1000 183 90 268435456 134217728 4503599627370496 Bool.false 322145965711 2470 

noncomputable def Ns324p958 := Ns324p957 372130544 56 134217720 8 432030192 56 120047984 16 Bool.false 242995434 53043 Bool.false 249887685 Bool.false 70845307 14148475504056880 1 Bool.false 215328227 Bool.false Bool.false 259140871 Bool.true Bool.false 234768221 

noncomputable def Ns324p959 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 657653 1000 473 304 268435456 134217728 4503599627370496 Bool.false 322145965711 2470 

noncomputable def Ns324p960 := Ns324p959 186065264 56 189812528 16 294906480 56 154981288 8 Bool.false 268435272 2536 Bool.false 335623075 Bool.false 15976226 14148475504056880 1 Bool.false 254765941 Bool.true Bool.false 267960175 Bool.false Bool.false 242995434 

noncomputable def Ns324p961 := nat_lit 983867687387109539344128946442020608225388828266117050471 

noncomputable def Ns324p962 := nat_lit 819830137322970159917771930939604692944915229835264000 

noncomputable def Ns324p963 := nat_lit 59050815703586803422654571276640000 

noncomputable def Ns324p964 := nat_lit 233009739452816734205319997653192755520 

noncomputable abbrev qz659 := (@Eq.refl Real qz756)

noncomputable abbrev qz469 := qz659

noncomputable abbrev qz154 := qz469

noncomputable def Ns324p965 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz151 657653 1000 1730030873636 16000000 1315306 4000 2000 Ns324p963 Ns324p964 qz154 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns324p966 := nat_lit 314837659963875052590121262861446594632124425045157456150720 

noncomputable abbrev qz660 := (@HSub.hSub Real Real Real qz727 qz728 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz729 (@Nat.cast Real Real.instNatCast 1315306))))

noncomputable abbrev qz470 := (@HSub.hSub Real Real Real qz586 (@HMul.hMul Real Real Real qz582 (Enclosure.sfrac Bool.false 657653 4000) (Real.log (Enclosure.sfrac Bool.false 1730030873636 16000000))) (@HMul.hMul Real Real Real qz582 qz587 qz660))

noncomputable abbrev qz661 := (Enclosure.sfrac Bool.false 657653 2000)

noncomputable abbrev qz155 := (@HSub.hSub Real Real Real qz354 (@HSub.hSub Real Real Real qz354 qz470 qz661) (@HMul.hMul Real Real Real qz349 qz661 (Real.log Real.pi)))

noncomputable def Ns324p967 := @Enclosure.Real.IsNear.addLit_ft_p qz155 (Enclosure.sfrac Bool.true Ns324p963 Ns324p964) 1351178397900985429511 1125899906842624000 4558558097438864617 495616000000000000000000 Ns324p963 Ns324p964 0 1 Ns324p966 

noncomputable def Ns324p968 := nat_lit 90676047344475116655035285504000 

noncomputable abbrev qz156 := (@HSub.hSub Real Real Real qz354 qz470 qz661)

noncomputable def Ns324p969 := @Enclosure.Real.IsNear.subLit_ff_p qz156 (@HMul.hMul Real Real Real qz5 qz661 (Real.log Real.pi)) 1774986849392045420039 1125899906842624000 520041724569177 121000000000000000000 25260952203933 67108864000 657653 134217728000 Ns324p968 1351178397900985429511 1125899906842624000 

noncomputable abbrev qz157 := qz470

noncomputable def Ns324p970 := @Enclosure.Real.IsNear.subLit_ff_p qz157 qz661 85808503004377260831 45035996273704960 520041724569177 121000000000000000000 657653 2000 0 1 141998947951363633603120 1774986849392045420039 1125899906842624000 520041724569177 121000000000000000000 

noncomputable def Ns324p971 := nat_lit 193223571077866759187441533832921088 

noncomputable def Ns324p972 := nat_lit 56050932088533972890419200 

noncomputable def Ns324p973 := nat_lit 28621547718557560802684491969721769405544326848638862289359168870496395853167339130271964193710767138398841582011297284980272687500111488184777977060392960 

noncomputable def Ns324p974 := nat_lit 595484054732087272247375566205849343025601609045630082195477091336409083188912266185325621550829268835642489080267711368005698916963867178258760479014912 

noncomputable def Ns324p975 := nat_lit 104248476328641357418127084938303202303623578794659453063367927259560946821910061369784462087409348892280493049015648287112454017650676648032337920 

noncomputable def Ns324p976 := BSN.log_dyadic_bound 681454873636 2778606873636 7 6 Ns324p973 134217728 38720000 Ns324p974 Ns324p975 67203648 3460061747272 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 681454873636) (BSN.artanhQ 2778606873636) 0 6 Ns324p974 Ns324p973 Ns324p975 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz471 := (Real.log (Enclosure.sfrac Bool.false 1730030873636 16000000))

noncomputable def Ns324p977 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 657653 4000) qz471 657653 4000 0 1 3262593648893175 281474976710656 195312621 7562500000000000 85826180039021728731 45035996273704960 128447931138513 30250000000000000000 (Enclosure.Real.IsNear.const Bool.false 657653 4000) (BSN.isNear_log_sfrac 1730030873636 16000000 3262593648893175 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1730030873636) qz357)) Bool.false Ns324p972 Ns324p98 1000000619520000 38720000000000000000000 3262593648893175 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1730030873636 16000000 16 3460061747272 2097152000000 67203648 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns324p976 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns324p978 := BSN.arctan_dyadic_bound_f 1000 1315306 1 0 16777216 4840000 0 1 1 0 1 1 12755 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1315306) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1315306) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz472 := (@Nat.cast Real Real.instNatCast 1315306)

noncomputable def Ns324p979 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz472)) 884279719003555 562949953421312 1 2000000000000000 12755 16777216 1 4840000 14828571423486058168320 883851732223395 562949953421312 50000000121 242000000000000000 qz15 (Ns324p978 rfl) rfl rfl 

noncomputable abbrev qz473 := (@HMul.hMul Real Real Real qz582 qz587 qz660)

noncomputable abbrev qz158 := qz473

noncomputable abbrev qz474 := qz660

noncomputable abbrev qz159 := qz474

noncomputable def Ns324p980 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 657653 4000) qz471) qz158 85826180039021728731 45035996273704960 128447931138513 30250000000000000000 883851732223395 2251799813685248 50000000121 968000000000000000 Ns324p971 85808503004377260831 45035996273704960 520041724569177 121000000000000000000 (Ns324p977 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz159 1 4 0 1 883851732223395 562949953421312 50000000121 242000000000000000 883851732223395 2251799813685248 50000000121 968000000000000000 qz365 Ns324p979 rfl) 

noncomputable def Ns324p981 := @Ns324p967 Ns324p961 Ns324p962 4558558097438864617 495616000000000000000000 (@Ns324p969 4558558097438864617 495616000000000000000000 (Ns324p970 (Ns324p980 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 657653 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz661 (Real.log Real.pi) 657653 2000 0 1 38410761 33554432 1 67108864 25260952203933 67108864000 657653 134217728000 (Enclosure.Real.IsNear.const Bool.false 657653 2000) RS325to336.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns324p963 Ns324p964) 

noncomputable def Ns324p982 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz151) Bool.false Ns324p961 Ns324p962 4558558097438864617 495616000000000000000000 40268245713 33554432 155 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz151) (@HAdd.hAdd Real Real Real qz366 qz155 (Enclosure.sfrac Bool.true Ns324p963 Ns324p964)) Bool.false Ns324p961 Ns324p962 4558558097438864617 495616000000000000000000 Ns324p965 (Ns324p981 rfl rfl)) 

noncomputable def Ns324p983 := nat_lit 7590329644719488112787456 

noncomputable def Ns324p984 := nat_lit 3500518543699630619054016685806334990330477702119069736824960422950279664143566506450914180871666612700136618581663161014923346291048574641 

noncomputable def Ns324p985 := nat_lit 2480675993131219564988464680279482945687721507707641805928594594471424569054848340787686257782517412665753053055248442142463842840241 

noncomputable def Ns324p986 := nat_lit 17480907272711344141723576334008511020129983500605243906244464336976850041827652528471100973816159775585336439753349092339335800777258561201 

noncomputable def Ns324p987 := BSN.sin_dyadic_bound_f 107865071821 68719476736 4 3 33554432 9689454 Ns324p984 Ns324p110 Ns324p985 Ns324p986 Ns324p113 Ns324p985 33554409 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107865071821) qz593 0 3 Ns324p984 Ns324p110 Ns324p985 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107865071821) qz594 0 3 Ns324p986 Ns324p113 Ns324p985 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p988 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz151) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40268245713) qz391) Bool.false 40268245713 33554432 155 16777216 Bool.false 33554409 33554432 1 4840000 (Ns324p982 rfl) (Enclosure.sfrac_false_div 40268245713 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40268245713) qz391) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns324p983) qz409) 226375608064910080 72057594037927936 Bool.false 33554409 33554432 190 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q3 40268245713 33554432 226375608064910080 72057594037927936 190 Ns324p983 Ns324p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554409 33554432 Ns324p983 Ns324p98 107865071821 68719476736 9689454 9680000 (Ns324p987 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns324p989 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz151) Bool.false Ns324p961 Ns324p962 4558558097438864617 495616000000000000000000 322145965711 268435456 2470 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz151) (@HAdd.hAdd Real Real Real qz366 qz155 (Enclosure.sfrac Bool.true Ns324p963 Ns324p964)) Bool.false Ns324p961 Ns324p962 4558558097438864617 495616000000000000000000 Ns324p965 (Ns324p981 rfl rfl)) 

noncomputable def Ns324p990 := Ns324p960 53043 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 473 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 254765941 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 304 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 267960175 268435456) qz154 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 1) Bool.false 33554409 33554432 11984019 1268776960000 268435272 268435456 2536 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz151)) Bool.false 33554409 33554432 11984019 1268776960000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz151) qz151) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz151)) Bool.false 33554409 33554432 766977216 81201725440000 33554409 33554432 11984019 1268776960000 (Ns324p988 rfl rfl) rfl)) rfl) (Ns324p989 rfl) RS325to336.d7 

noncomputable def Ns324p991 := nat_lit 17765449881634179391779450516424562508587712812939939054282208796470816939402367572233395593983828967056640625 

noncomputable def Ns324p992 := nat_lit 2042780696717571498255676021904910999251535941036093908525114010911917830399524173016607761383056640625 

noncomputable def Ns324p993 := nat_lit 88782903091301285519074803263836003366614663333492978669285713876558802184140252468885445097088099303056640625 

noncomputable def Ns324p994 := BSN.sin_dyadic_bound_f 335623075 268435456 4 3 268435456 134217728 Ns324p991 Ns324p119 Ns324p992 Ns324p993 Ns324p122 Ns324p992 254765941 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 335623075) qz367 0 3 Ns324p991 Ns324p119 Ns324p992 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 335623075) qz368 0 3 Ns324p993 Ns324p122 Ns324p992 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p995 := nat_lit 65147354076267363072383861776 

noncomputable def Ns324p996 := BSN.cos_dyadic_bound_f 15976226 268435456 2 1 268435456 134217728 Ns324p995 Ns324p149 Ns324p995 Ns324p995 Ns324p150 Ns324p995 267960175 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 15976226) qz369 0 1 Ns324p995 Ns324p149 Ns324p995 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 15976226) qz370 0 1 Ns324p995 Ns324p150 Ns324p995 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p997 := nat_lit 61239065265742463479945724668736076408407418270932980361359979772230625 

noncomputable def Ns324p998 := nat_lit 15204033909489697302187727326337552101983509862200966941607000390625 

noncomputable def Ns324p999 := nat_lit 160363412022043468651844784478637558366235265026952337476132583307590625 

noncomputable def Ns324p1000 := BSN.sin_dyadic_bound_f 249887685 268435456 3 2 268435456 134217728 Ns324p997 Ns324p249 Ns324p998 Ns324p999 Ns324p252 Ns324p998 215328227 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 249887685) qz367 0 2 Ns324p997 Ns324p249 Ns324p998 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 249887685) qz368 0 2 Ns324p999 Ns324p252 Ns324p998 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1001 := nat_lit 25190938428460613323004690214001 

noncomputable def Ns324p1002 := BSN.cos_dyadic_bound_f 70845307 268435456 2 1 268435456 134217728 Ns324p1001 Ns324p149 Ns324p1001 Ns324p1001 Ns324p150 Ns324p1001 259140871 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 70845307) qz369 0 1 Ns324p1001 Ns324p149 Ns324p1001 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 70845307) qz370 0 1 Ns324p1001 Ns324p150 Ns324p1001 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1003 := Ns324p958 90295 BSN.abs_quadSignPos (BSN.cos_quad_nat3 183 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 215328227 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 90 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 259140871 268435456) qz154 rfl rfl (Ns324p990 RS325to336.d9 RS325to336.d11 RS325to336.d13 RS325to336.d17 (Ns324p994 rfl rfl) (Ns324p996 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns324p989 rfl) RS325to336.d19 RS325to336.d21 RS325to336.d23 RS325to336.d25 RS325to336.d17 (Ns324p1000 rfl rfl) (Ns324p1002 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns324p1004 := nat_lit 21474205391033651099374794201525817483683364910038463083323369604783507860034113671546264985935850267688649041 

noncomputable def Ns324p1005 := nat_lit 3605993729056615055206406430688309833342073832461806306010024179080605257844180495715367279817237807441 

noncomputable def Ns324p1006 := nat_lit 107306251611477117077976992695399990765765764178969644074124834012642469129596459742809485128139475880889893201 

noncomputable def Ns324p1007 := BSN.sin_dyadic_bound_f 351899579 268435456 4 3 268435456 134217728 Ns324p1004 Ns324p119 Ns324p1005 Ns324p1006 Ns324p122 Ns324p1005 259422424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 351899579) qz367 0 3 Ns324p1004 Ns324p119 Ns324p1005 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 351899579) qz368 0 3 Ns324p1006 Ns324p122 Ns324p1005 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1008 := nat_lit 4192534506067380348257377336093258485249746754867735950501469324548748387790960912236652173696848719907505441 

noncomputable def Ns324p1009 := nat_lit 471773257724387339164307289609484771983281472413757903111378285687785977195072252112361346144453379361 

noncomputable def Ns324p1010 := nat_lit 25419587924147629732154512265322629375129449823534927120677342456923463879622480021845169318032891893222327585 

noncomputable def Ns324p1011 := BSN.cos_dyadic_bound_f 297037383 268435456 4 3 268435456 134217728 Ns324p1008 Ns324p125 Ns324p1009 Ns324p1010 Ns324p128 Ns324p1009 120191598 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 297037383) qz369 0 3 Ns324p1008 Ns324p125 Ns324p1009 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 297037383) qz370 0 3 Ns324p1010 Ns324p128 Ns324p1009 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1012 := Ns324p956 121729 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 13 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 259422424 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 50 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 120191598 268435456) qz154 rfl rfl (Ns324p1003 rfl rfl) (Ns324p989 rfl) RS325to336.d27 RS325to336.d29 RS325to336.d31 RS325to336.d33 RS325to336.d17 (Ns324p1007 rfl rfl) (Ns324p1011 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p1013 := nat_lit 38378973260076161150419229480756075525246519269523990455658787020800000 

noncomputable def Ns324p1014 := nat_lit 19337990660415692694713555681978403579024635314628966559769600000000 

noncomputable def Ns324p1015 := nat_lit 115098243798907652065868261330904269768581508537942713433856821862400000 

noncomputable def Ns324p1016 := BSN.cos_dyadic_bound_f 257514340 268435456 3 2 268435456 134217728 Ns324p1013 Ns324p263 Ns324p1014 Ns324p1015 Ns324p266 Ns324p1014 154103546 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 257514340) qz369 0 2 Ns324p1013 Ns324p263 Ns324p1014 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 257514340) qz370 0 2 Ns324p1015 Ns324p266 Ns324p1014 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1017 := nat_lit 32215029007337479834017945378906271890326656081061657347132992202782847715426781519461410947190754000708046241 

noncomputable def Ns324p1018 := nat_lit 12156658815566715782288562992497424546231966595254775048967301383979332228194759522971773540777166900641 

noncomputable def Ns324p1019 := nat_lit 160929492675182469772465466842111544782478657985268105223452460678613502557107921625328129812893751937970474401 

noncomputable def Ns324p1020 := BSN.sin_dyadic_bound_f 389404697 268435456 4 3 268435456 134217728 Ns324p1017 Ns324p119 Ns324p1018 Ns324p1019 Ns324p122 Ns324p1018 266500190 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 389404697) qz367 0 3 Ns324p1017 Ns324p119 Ns324p1018 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 389404697) qz368 0 3 Ns324p1019 Ns324p122 Ns324p1018 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1021 := Ns324p954 148742 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 106 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 154103546 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 155 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266500190 268435456) qz154 rfl rfl (Ns324p1012 rfl) (Ns324p989 rfl) RS325to336.d35 RS325to336.d37 RS325to336.d39 RS325to336.d41 RS325to336.d17 (Ns324p1016 rfl rfl) (Ns324p1020 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p1022 := nat_lit 49139975330787648899646923521 

noncomputable def Ns324p1023 := BSN.cos_dyadic_bound_f 14888767 268435456 2 1 268435456 134217728 Ns324p1022 Ns324p149 Ns324p1022 Ns324p1022 Ns324p150 Ns324p1022 268022659 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 14888767) qz369 0 1 Ns324p1022 Ns324p149 Ns324p1022 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 14888767) qz370 0 1 Ns324p1022 Ns324p150 Ns324p1022 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1024 := Ns324p952 Bool.false 117780879 148742 Bool.true 14888767 14148475504056880 1 Bool.false 268022659 Bool.false Bool.false 202537085 161180 BSN.abs_quadSignPos qz596 (BSN.sfrac_eq_quadSignPos_mul Bool.false 268022659 268435456) qz154 rfl (Ns324p1021 rfl) (Ns324p989 rfl) RS325to336.d43 RS325to336.d45 RS325to336.d17 (Ns324p1023 rfl rfl) rfl 

noncomputable def Ns324p1025 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 10) 202537085 268435456 161180 268435456 202537085 268435456 161180 268435456 108736269537771520 202537085 134217728 40295 33554432 (Ns324p1024 rfl rfl rfl rfl) 

noncomputable def Ns324p1026 := @Enclosure.Real.IsNear.mulLit_ff qz658 (Zeta.RiemannSiegel.correction qz153) 1311311 4194304 1 16777216 292818897125223 562949953421312 891253425772229 8514618045497344000 383976640808173297353 2361183241434822606848 

noncomputable abbrev qz662 := (@HPow.hPow Real Real Real qz133 qz152 qz135)

noncomputable def Ns324p1027 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz662 1 1 0 1 1311311 4194304 1 16777216 1311311 4194304 1 16777216 

noncomputable def Ns324p1028 := @Enclosure.Real.IsNear.sqrt_image qz152 3512099171509 33554432000 657653 33554432000 171643868 171643901 16777216 (@Enclosure.Real.IsNear.of_eq qz152 (@HMul.hMul Real Real Real qz5 qz151 qz3) Bool.false 3512099171509 33554432000 657653 33554432000 (BSN.t_div_two_pi_mk qz151 657653 1000 qz154) (@Enclosure.Real.IsNear.mulLit_ff qz151 qz3 657653 1000 0 1 5340353 33554432 1 33554432 3512099171509 33554432000 657653 33554432000 (Enclosure.Real.IsNear.const Bool.false 657653 1000) RS325to336.d48 rfl)) 

noncomputable abbrev qz759 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 657653 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz663 := qz759

noncomputable abbrev qz475 := qz663

noncomputable abbrev qz160 := qz475

noncomputable def Ns324p1029 := @Enclosure.Real.IsNear.sqrt_image qz160 343287769 33554432 33 33554432 53662894 53662900 16777216 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 343287769 33554432 33 33554432 343287769 33554432 33 33554432 (Ns324p1028 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns324p1030 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz160) 53662897 16777216 3 16777216 5245243 5245245 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz160) Bool.false 107325794 33554432 6 33554432 53662897 16777216 3 16777216 (Ns324p1029 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns324p1031 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz160)) Bool.false 10490488 33554432 2 33554432 1311311 4194304 1 16777216 (Ns324p1030 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz161 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz468))

noncomputable abbrev qz664 := (@HMul.hMul Real Real Real qz723 qz758 qz758)

noncomputable abbrev qz476 := (@HSub.hSub Real Real Real qz586 (@HSub.hSub Real Real Real qz586 qz664 qz657) qz600)

noncomputable abbrev qz162 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz476))

noncomputable def Ns324p1032 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz153) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz161) qz162) Bool.false 292818897125223 

noncomputable def Ns324p1033 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz161) qz162 278426211 33554432 14869 

noncomputable def Ns324p1034 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz161) Bool.false 278426211 33554432 14869 33554432 278426211 33554432 14869 

noncomputable def Ns324p1035 := @Enclosure.Real.IsNear.recentre' qz161 Bool.false 2021900 16777216 1045114432 162403450880000 505475 4194304 16329913 2537553920000 

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz349 qz346 qz468)

noncomputable def Ns324p1036 := @Enclosure.Real.IsNear.cos_image qz163 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12163381) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false 12163381 8388608 209 33554432 Bool.false 2021900 16777216 1 

noncomputable def Ns324p1037 := nat_lit 890540488564969220447063719 

noncomputable def Ns324p1038 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz153 884279719003555 140737488355328 1 500000000000000 7743449 33554432 33 33554432 6847374905838358961195 4722366482869645213696 Ns324p1037 

noncomputable def Ns324p1039 := @Enclosure.Real.IsNear.subLit_ff_p qz160 qz1 343287769 33554432 33 33554432 10 1 0 1 7743449 7743449 33554432 33 

noncomputable def Ns324p1040 := @Ns324p1039 33554432 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 343287769 33554432 33 33554432 343287769 33554432 33 33554432 (Ns324p1028 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns324p1041 := @Enclosure.Real.IsNear.recentre' qz163 Bool.false 6847374905838358961195 4722366482869645213696 Ns324p1037 Ns324p173 12163381 8388608 209 33554432 (@Ns324p1038 Ns324p173 RS325to336.d47 (Ns324p1040 rfl rfl) rfl) 

noncomputable def Ns324p1042 := nat_lit 10739987884569284924340077014186274951081009693223110228148583563511811307499394121308273041 

noncomputable def Ns324p1043 := nat_lit 10487011085526451465397401430256003365660981368048572551370385889962811912593494210961 

noncomputable def Ns324p1044 := nat_lit 65041882670764535814716296179230541048097440137626138025543778418762994683542656630253123985 

noncomputable def Ns324p1045 := BSN.cos_dyadic_bound_f 12163381 8388608 4 3 16777216 4840000 Ns324p1042 Ns324p941 Ns324p1043 Ns324p1044 Ns324p944 Ns324p1043 2021900 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 12163381) (BSN.cosEvenQ 8388608) 0 3 Ns324p1042 Ns324p941 Ns324p1043 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 12163381) (BSN.cosOddQ 8388608) 0 3 Ns324p1044 Ns324p944 Ns324p1043 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1046 := @Enclosure.Real.IsNear.inv_image qz161 505475 4194304 16329913 2537553920000 139205671 139220540 16777216 (Ns324p1035 (@Ns324p1036 4840000 (Ns324p1041 rfl) (Enclosure.sfrac_false_div 12163381 8388608) (Ns324p1045 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns324p1047 := @Enclosure.Real.IsNear.recentre' qz162 Bool.false 1051693 16777216 

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz349 qz346 qz476)

noncomputable def Ns324p1048 := @Enclosure.Real.IsNear.cos_image qz164 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 50602411)) qz391) Bool.true 50602411 33554432 

noncomputable def Ns324p1049 := nat_lit 238963130617278252777269400205 

noncomputable def Ns324p1050 := nat_lit 8734663872994256414419542973951009 

noncomputable def Ns324p1051 := @Enclosure.Real.IsNear.recentre' qz164 Bool.true Ns324p1049 Ns324p188 Ns324p1050 

noncomputable def Ns324p1052 := nat_lit 967140655691703339764940800000000000000 

noncomputable abbrev qz165 := qz476

noncomputable def Ns324p1053 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz165 884279719003555 140737488355328 1 500000000000000 270234774678031 

noncomputable abbrev qz477 := (@HSub.hSub Real Real Real qz586 qz664 qz657)

noncomputable abbrev qz166 := qz477

noncomputable def Ns324p1054 := @Enclosure.Real.IsNear.subLit_tf qz166 qz29 199866030500367 1125899906842624 1618364979 1125899906842624 1 16 

noncomputable abbrev qz478 := qz664

noncomputable abbrev qz167 := qz478

noncomputable def Ns324p1055 := @Enclosure.Real.IsNear.subLit_ff_n qz167 qz153 59961002415601 1125899906842624 511068723 1125899906842624 7743449 33554432 33 33554432 

noncomputable def Ns324p1056 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz153 7743449 33554432 33 33554432 7743449 33554432 33 33554432 59961002415601 1125899906842624 

noncomputable def Ns324p1057 := nat_lit 210933378726747923070980148606842115005167980981193611166020648016640858522113975360412098991485201 

noncomputable def Ns324p1058 := nat_lit 281873674177478818249608060823596453536616097504697581858151967931366655426124315800417333521 

noncomputable def Ns324p1059 := nat_lit 1277042617799660094603096375432473316297566267208419983932499569094875743066684104888468935853207825 

noncomputable def Ns324p1060 := BSN.cos_dyadic_bound_f 50602411 33554432 4 3 16777216 4840000 Ns324p1057 Ns324p594 Ns324p1058 Ns324p1059 Ns324p597 Ns324p1058 1051693 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 50602411) qz392 0 3 Ns324p1057 Ns324p594 Ns324p1058 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 50602411) (BSN.cosOddQ 33554432) 0 3 Ns324p1059 Ns324p597 Ns324p1058 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1061 := @Ns324p1047 94057152 10150215680000 1051693 16777216 1469643 158597120000 (@Ns324p1048 19 2097152 Bool.false 1051693 16777216 1 4840000 (@Ns324p1051 Ns324p1052 50602411 33554432 19 2097152 (@Ns324p1053 1125899906842624 1618364979 1125899906842624 Ns324p1049 Ns324p188 Ns324p1050 Ns324p1052 RS325to336.d47 (@Ns324p1054 0 1 4323756394848496 270234774678031 1125899906842624 1618364979 1125899906842624 (@Ns324p1055 6706391129534490476544 199866030500367 1125899906842624 1618364979 1125899906842624 (@Ns324p1056 511068723 1125899906842624 (Ns324p1040 rfl rfl) (Ns324p1040 rfl rfl) rfl) (Ns324p1040 rfl rfl) rfl rfl) qz379 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 50602411 33554432) (BSN.cos_neg_of_bound 50602411 33554432 Bool.false 1051693 16777216 1 4840000 (Ns324p1060 rfl rfl)) rfl rfl) 

noncomputable def Ns324p1062 := @Ns324p1026 233963573054183714949 Ns324p949 (Ns324p1027 qz31 (@Enclosure.Real.IsNear.of_eq qz662 (@Inv.inv Real Real.instInv (Real.sqrt qz160)) Bool.false 1311311 4194304 1 16777216 (BSN.rpow_neg_quarter_mk qz152 (BSN.t_div_two_pi_nonneg qz151 657653 1000 qz154)) Ns324p1031) rfl) (@Ns324p1032 562949953421312 891253425772229 8514618045497344000 (BSN.correction_mk qz153 (BSN.cos_two_pi_p_ne_zero_mk qz151 657653 1000 10 qz154 rfl rfl (@BSN.floor_sqrt_eq_dec qz151 657653 1000 10 qz154 rfl rfl rfl))) (@Ns324p1033 33554432 1051693 16777216 1469643 158597120000 292818897125223 562949953421312 891253425772229 8514618045497344000 (@Ns324p1034 33554432 (Ns324p1046 rfl rfl rfl rfl rfl) rfl) (Ns324p1061 rfl) rfl)) 

noncomputable def Ns324p1063 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz151) (hardyZApproximantRS₀ qz151) Bool.false 3179093439405523870007 2361183241434822606848 8811376926637070626949 Ns324p949 (@Eq.refl Real (hardyZApproximantRS₀ qz151)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz151) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz151) qz151 10) (@HMul.hMul Real Real Real qz5 qz658 (Zeta.RiemannSiegel.correction qz153))) Bool.false 3179093439405523870007 2361183241434822606848 8811376926637070626949 Ns324p949 (BSN.hardyZApproximantRS₀_eq qz151 10 (@BSN.floor_sqrt_eq_dec qz151 657653 1000 10 qz154 rfl rfl rfl)) (@Ns324p951 3179093439405523870007 2361183241434822606848 8811376926637070626949 Ns324p949 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz151) qz151 10) (@HAdd.hAdd Real Real Real qz366 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 10)) Bool.false 202537085 134217728 40295 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz151) qz151 10) (Ns324p1025 (Ns324p1024 rfl rfl rfl rfl) rfl rfl)) (Ns324p1062 rfl) rfl rfl)) 

theorem RS325to336.d58 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz151) Bool.false 3179093439405523870007 2361183241434822606848 8811376926637070626949 Ns324p949 := Ns324p1063 

noncomputable def Ns324p1064 := nat_lit 178564482633508459642880000 

noncomputable def Ns324p1065 := nat_lit 5050201405755461307066220544 

noncomputable abbrev qz760 := (Enclosure.sfrac Bool.false 659004 1000)

noncomputable abbrev qz665 := qz760

noncomputable abbrev qz479 := qz665

noncomputable abbrev qz168 := qz479

noncomputable abbrev qz761 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 659004 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz666 := qz761

noncomputable abbrev qz480 := qz666

noncomputable abbrev qz169 := qz480

noncomputable abbrev qz762 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 659004 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz667 := qz762

noncomputable abbrev qz481 := qz667

noncomputable abbrev qz170 := qz481

noncomputable abbrev qz668 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz133 qz169 qz135))

noncomputable def Ns324p1066 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (@HMul.hMul Real Real Real qz5 qz668 (Zeta.RiemannSiegel.correction qz170)) 1972093 1048576 161505 134217728 375488723377740562305 2361183241434822606848 12912877204007624780313 Ns324p1064 Ns324p1065 

noncomputable def Ns324p1067 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos BSN.quadSignPos 9 10 659004 1000 200 268435456 134217728 4503599627370496 Bool.false 322989472763 2475 618095470 56 84886744 8 

noncomputable def Ns324p1068 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 659004 1000 106 155 268435456 134217728 4503599627370496 Bool.false 322989472763 2475 

noncomputable def Ns324p1069 := Ns324p1068 558195838 56 94906264 8 589812974 56 89478488 8 Bool.true 346037837 121973 Bool.true 168129866 Bool.true 342734973 14148475504056880 1 Bool.false 217481768 Bool.true Bool.false 256916831 Bool.false Bool.true 337290306 

noncomputable def Ns324p1070 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 659004 1000 14 50 268435456 134217728 4503599627370496 Bool.false 322989472763 2475 

noncomputable def Ns324p1071 := Ns324p1070 480971758 57 109588312 8 522351262 57 101459064 8 Bool.true 163800084 90475 Bool.false 123956358 Bool.true 159226886 14148475504056880 1 Bool.false 240320541 Bool.true Bool.false 222579934 Bool.true Bool.true 346037837 

noncomputable def Ns324p1072 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 659004 1000 184 90 268435456 134217728 4503599627370496 Bool.false 322989472763 2475 

noncomputable def Ns324p1073 := Ns324p1072 372130544 56 134217720 8 432030192 56 120047984 16 Bool.true 232376540 53146 Bool.false 168988943 Bool.false 330679570 14148475504056880 1 Bool.false 216977084 Bool.false Bool.false 89246123 Bool.true Bool.true 163800084 

noncomputable def Ns324p1074 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 659004 1000 475 305 268435456 134217728 4503599627370496 Bool.false 322989472763 2475 

noncomputable def Ns324p1075 := Ns324p1074 186065264 56 189812528 16 294906480 56 154981288 8 Bool.true 268435424 2536 Bool.false 84441099 Bool.false 39407195 14148475504056880 1 Bool.false 83055359 Bool.false Bool.false 39265802 Bool.true Bool.true 232376540 

noncomputable def Ns324p1076 := nat_lit 84657882183775510418370698363423093667658643912537 

noncomputable def Ns324p1077 := nat_lit 70358878924323104642603833063965572352652083200 

noncomputable def Ns324p1078 := nat_lit 59659845461048782190875546091520000 

noncomputable def Ns324p1079 := nat_lit 235896524160693564185289478888992276480 

noncomputable abbrev qz669 := (@Eq.refl Real qz760)

noncomputable abbrev qz482 := qz669

noncomputable abbrev qz171 := qz482

noncomputable def Ns324p1080 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz168 659004 1000 1737146088064 16000000 1318008 4000 2000 Ns324p1078 Ns324p1079 qz171 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns324p1081 := nat_lit 7989320112186113065120812606641226047909294717930915758080 

noncomputable abbrev qz670 := (@HSub.hSub Real Real Real qz727 qz728 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz729 (@Nat.cast Real Real.instNatCast 1318008))))

noncomputable abbrev qz483 := (@HSub.hSub Real Real Real qz586 (@HMul.hMul Real Real Real qz582 (Enclosure.sfrac Bool.false 659004 4000) (Real.log (Enclosure.sfrac Bool.false 1737146088064 16000000))) (@HMul.hMul Real Real Real qz582 qz587 qz670))

noncomputable abbrev qz671 := (Enclosure.sfrac Bool.false 659004 2000)

noncomputable abbrev qz172 := (@HSub.hSub Real Real Real qz354 (@HSub.hSub Real Real Real qz354 qz483 qz671) (@HMul.hMul Real Real Real qz349 qz671 (Real.log Real.pi)))

noncomputable def Ns324p1082 := @Enclosure.Real.IsNear.addLit_ft_p qz172 (Enclosure.sfrac Bool.true Ns324p1078 Ns324p1079) 33867908057937807421 28147497671065600 1141967509782711339 123904000000000000000000 Ns324p1078 Ns324p1079 0 1 Ns324p1081 

noncomputable def Ns324p1083 := nat_lit 2841046044780815548342599680000 

noncomputable abbrev qz173 := (@HSub.hSub Real Real Real qz354 qz483 qz671)

noncomputable def Ns324p1084 := @Enclosure.Real.IsNear.subLit_ff_p qz173 (@HMul.hMul Real Real Real qz5 qz671 (Real.log Real.pi)) 222424424105016895793 140737488355328000 521097193973061 121000000000000000000 6328211285511 16777216000 164751 33554432000 Ns324p1083 33867908057937807421 28147497671065600 

noncomputable abbrev qz174 := qz483

noncomputable def Ns324p1085 := @Enclosure.Real.IsNear.subLit_ff_p qz174 qz671 268797707993074182449 140737488355328000 521097193973061 121000000000000000000 659004 2000 0 1 444848848210033791586000 222424424105016895793 140737488355328000 521097193973061 121000000000000000000 

noncomputable def Ns324p1086 := nat_lit 1210557257555652282281248358823624704 

noncomputable def Ns324p1087 := nat_lit 56070779416062997647327232 

noncomputable def Ns324p1088 := nat_lit 29513539644614182414951327422996683012407156579650934015800668001851010493923999802091749416455170236078231087072084677971933933994093751900131103300648960 

noncomputable def Ns324p1089 := nat_lit 624107725397732284812396628168864591494387481071571398570605209591615337672313088186657957064775359043727080283011330772093839227945733504301434365018112 

noncomputable def Ns324p1090 := nat_lit 118087064461064567712460748211103239431176448780203529153665606559998623985490047612224527881543957790279195399157564702452930855220117751380049920 

noncomputable def Ns324p1091 := BSN.log_dyadic_bound 688570088064 2785722088064 7 6 Ns324p1088 134217728 38720000 Ns324p1089 Ns324p1090 67754522 3474292176128 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 688570088064) (BSN.artanhQ 2785722088064) 0 6 Ns324p1089 Ns324p1088 Ns324p1090 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz484 := (Real.log (Enclosure.sfrac Bool.false 1737146088064 16000000))

noncomputable def Ns324p1092 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 659004 4000) qz484 659004 4000 0 1 3263748915404023 281474976710656 195312621 7562500000000000 537705897561728193273 281474976710656000 32177949622371 7562500000000000000 (Enclosure.Real.IsNear.const Bool.false 659004 4000) (BSN.isNear_log_sfrac 1737146088064 16000000 3263748915404023 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1737146088064) qz357)) Bool.false Ns324p1087 Ns324p98 1000000619520000 38720000000000000000000 3263748915404023 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1737146088064 16000000 16 3474292176128 2097152000000 67754522 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns324p1091 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns324p1093 := BSN.arctan_dyadic_bound_f 1000 1318008 1 0 16777216 4840000 0 1 1 0 1 1 12729 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1318008) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1318008) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns324p1094 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1318008))) 884279719003555 562949953421312 1 2000000000000000 12729 16777216 1 4840000 14828586060184847122432 883852604638627 562949953421312 50000000121 242000000000000000 qz15 (Ns324p1093 rfl) rfl rfl 

noncomputable abbrev qz485 := (@HMul.hMul Real Real Real qz582 qz587 qz670)

noncomputable abbrev qz175 := qz485

noncomputable abbrev qz486 := qz670

noncomputable abbrev qz176 := qz486

noncomputable def Ns324p1095 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 659004 4000) qz484) qz175 537705897561728193273 281474976710656000 32177949622371 7562500000000000000 883852604638627 2251799813685248 50000000121 968000000000000000 Ns324p1086 268797707993074182449 140737488355328000 521097193973061 121000000000000000000 (Ns324p1092 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz176 1 4 0 1 883852604638627 562949953421312 50000000121 242000000000000000 883852604638627 2251799813685248 50000000121 968000000000000000 qz365 Ns324p1094 rfl) 

noncomputable def Ns324p1096 := @Ns324p1082 Ns324p1076 Ns324p1077 1141967509782711339 123904000000000000000000 (@Ns324p1084 1141967509782711339 123904000000000000000000 (Ns324p1085 (Ns324p1095 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 659004 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz671 (Real.log Real.pi) 659004 2000 0 1 38410761 33554432 1 67108864 6328211285511 16777216000 164751 33554432000 (Enclosure.Real.IsNear.const Bool.false 659004 2000) RS325to336.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns324p1078 Ns324p1079) 

noncomputable def Ns324p1097 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz168) Bool.false Ns324p1076 Ns324p1077 1141967509782711339 123904000000000000000000 40373684095 33554432 155 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz168) (@HAdd.hAdd Real Real Real qz366 qz172 (Enclosure.sfrac Bool.true Ns324p1078 Ns324p1079)) Bool.false Ns324p1076 Ns324p1077 1141967509782711339 123904000000000000000000 Ns324p1080 (Ns324p1096 rfl rfl)) 

noncomputable def Ns324p1098 := nat_lit 7593792002518070790717440 

noncomputable def Ns324p1099 := nat_lit 3506922851472393089883735739676448746712893935314370629764096638115810825371506302904118674425488051479911936043551014151747704528854540625 

noncomputable def Ns324p1100 := nat_lit 2494288950008756328273948471085145460117375740467423999130184463101874680261511809917307254158690503491297893436794976318437744140625 

noncomputable def Ns324p1101 := nat_lit 17512849531743152694979825138056516381936373779489369050910376142920125214524834245981199081987739708563508974981840313090457608829296140625 

noncomputable def Ns324p1102 := BSN.sin_dyadic_bound_f 107914274885 68719476736 4 3 33554432 9689454 Ns324p1099 Ns324p110 Ns324p1100 Ns324p1101 Ns324p113 Ns324p1100 33554428 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107914274885) qz593 0 3 Ns324p1099 Ns324p110 Ns324p1100 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107914274885) qz594 0 3 Ns324p1101 Ns324p113 Ns324p1100 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1103 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz168) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40373684095) qz391) Bool.false 40373684095 33554432 155 16777216 Bool.true 33554428 33554432 1 4840000 (Ns324p1097 rfl) (Enclosure.sfrac_false_div 40373684095 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40373684095) qz391) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns324p1098) qz409) 226375608064910080 72057594037927936 Bool.false 33554428 33554432 191 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q1 40373684095 33554432 226375608064910080 72057594037927936 191 Ns324p1098 Ns324p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554428 33554432 Ns324p1098 Ns324p98 107914274885 68719476736 9689454 9680000 (Ns324p1102 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns324p1104 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz168) Bool.false Ns324p1076 Ns324p1077 1141967509782711339 123904000000000000000000 322989472763 268435456 2475 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz168) (@HAdd.hAdd Real Real Real qz366 qz172 (Enclosure.sfrac Bool.true Ns324p1078 Ns324p1079)) Bool.false Ns324p1076 Ns324p1077 1141967509782711339 123904000000000000000000 Ns324p1080 (Ns324p1096 rfl rfl)) 

noncomputable def Ns324p1105 := Ns324p1075 53146 BSN.abs_quadSignPos (BSN.cos_quad_nat3 475 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 83055359 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 305 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 39265802 268435456) qz171 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 1) Bool.true 8388607 8388608 11984019 1268776960000 268435424 268435456 2536 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz168)) Bool.true 8388607 8388608 11984019 1268776960000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz168) qz168) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz168)) Bool.true 33554428 33554432 766977216 81201725440000 8388607 8388608 11984019 1268776960000 (Ns324p1103 rfl rfl) rfl)) rfl) (Ns324p1104 rfl) RS325to336.d7 

noncomputable def Ns324p1106 := nat_lit 50841166686195278416225853495601 

noncomputable def Ns324p1107 := BSN.sin_dyadic_bound_f 84441099 268435456 2 1 268435456 134217728 Ns324p1106 Ns324p270 Ns324p1106 Ns324p1106 Ns324p271 Ns324p1106 83055359 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 84441099) qz367 0 1 Ns324p1106 Ns324p270 Ns324p1106 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 84441099) qz368 0 1 Ns324p1106 Ns324p271 Ns324p1106 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1108 := nat_lit 2411582322513891834052712400625 

noncomputable def Ns324p1109 := BSN.sin_dyadic_bound_f 39407195 268435456 2 1 268435456 134217728 Ns324p1108 Ns324p270 Ns324p1108 Ns324p1108 Ns324p271 Ns324p1108 39265802 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 39407195) qz367 0 1 Ns324p1108 Ns324p270 Ns324p1108 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 39407195) qz368 0 1 Ns324p1108 Ns324p271 Ns324p1108 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1110 := nat_lit 7114470032527342093217251183067980859771021247688474825883244065297281 

noncomputable def Ns324p1111 := nat_lit 665068404361245525530387274692621880444241708140090383547234096001 

noncomputable def Ns324p1112 := nat_lit 21342079960773303788600692774654557335552175259649144296882637727699841 

noncomputable def Ns324p1113 := BSN.cos_dyadic_bound_f 168988943 268435456 3 2 268435456 134217728 Ns324p1110 Ns324p263 Ns324p1111 Ns324p1112 Ns324p266 Ns324p1111 216977084 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 168988943) qz369 0 2 Ns324p1110 Ns324p263 Ns324p1111 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 168988943) qz370 0 2 Ns324p1112 Ns324p266 Ns324p1111 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1114 := nat_lit 6442719565063245949776924168856538793167491337406562515532369691032227915066092792895254638753350305344000000 

noncomputable def Ns324p1115 := nat_lit 1709575835914837740133578652745840178061559331924396778396682950212406177720573406377664401000000000000 

noncomputable def Ns324p1116 := nat_lit 39050154135480048786159945786834329551828345814154275974295322217497097850966125978567836458255557844953600000 

noncomputable def Ns324p1117 := BSN.cos_dyadic_bound_f 330679570 268435456 4 3 268435456 134217728 Ns324p1114 Ns324p125 Ns324p1115 Ns324p1116 Ns324p128 Ns324p1115 89246123 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 330679570) qz369 0 3 Ns324p1114 Ns324p125 Ns324p1115 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 330679570) qz370 0 3 Ns324p1116 Ns324p128 Ns324p1115 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1118 := Ns324p1073 90475 BSN.abs_quadSignPos (BSN.cos_quad_nat0 184 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 216977084 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 90 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 89246123 268435456) qz171 rfl rfl (Ns324p1105 RS325to336.d9 RS325to336.d11 RS325to336.d13 RS325to336.d17 (Ns324p1107 rfl rfl) (Ns324p1109 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns324p1104 rfl) RS325to336.d19 RS325to336.d21 RS325to336.d23 RS325to336.d25 RS325to336.d17 (Ns324p1113 rfl rfl) (Ns324p1117 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns324p1119 := nat_lit 2059471472394606421815810100820124179663949288704043882892259823165696 

noncomputable def Ns324p1120 := nat_lit 55737881885493603514946220687769948121402812002406701965703618816 

noncomputable def Ns324p1121 := nat_lit 6178302941420048278240400410018996999095605060488126835272848062259456 

noncomputable def Ns324p1122 := BSN.cos_dyadic_bound_f 123956358 268435456 3 2 268435456 134217728 Ns324p1119 Ns324p263 Ns324p1120 Ns324p1121 Ns324p266 Ns324p1120 240320541 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 123956358) qz369 0 2 Ns324p1119 Ns324p263 Ns324p1120 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 123956358) qz370 0 2 Ns324p1121 Ns324p266 Ns324p1120 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1123 := nat_lit 5607462836431669005548389431994950714022051151501948214515758002708736 

noncomputable def Ns324p1124 := nat_lit 413172315011444281697551615368565486294128143903748440739038208256 

noncomputable def Ns324p1125 := nat_lit 16821562164664984128081773192754115011093565198218037146665795931709696 

noncomputable def Ns324p1126 := BSN.cos_dyadic_bound_f 159226886 268435456 3 2 268435456 134217728 Ns324p1123 Ns324p263 Ns324p1124 Ns324p1125 Ns324p266 Ns324p1124 222579934 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 159226886) qz369 0 2 Ns324p1123 Ns324p263 Ns324p1124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 159226886) qz370 0 2 Ns324p1125 Ns324p266 Ns324p1124 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1127 := Ns324p1071 121973 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 14 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 240320541 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 50 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 222579934 268435456) qz171 rfl rfl (Ns324p1118 rfl rfl) (Ns324p1104 rfl) RS325to336.d27 RS325to336.d29 RS325to336.d31 RS325to336.d33 RS325to336.d17 (Ns324p1122 rfl rfl) (Ns324p1126 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p1128 := nat_lit 6970887026364756577103133777346131086378363546554072400338536088658176 

noncomputable def Ns324p1129 := nat_lit 638497108318147732771108139550037663721302233670407753869720740096 

noncomputable def Ns324p1130 := nat_lit 20911384084877633435843859115759293183807648035194876385507868824494336 

noncomputable def Ns324p1131 := BSN.cos_dyadic_bound_f 168129866 268435456 3 2 268435456 134217728 Ns324p1128 Ns324p263 Ns324p1129 Ns324p1130 Ns324p266 Ns324p1129 217481768 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 168129866) qz369 0 2 Ns324p1128 Ns324p263 Ns324p1129 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 168129866) qz370 0 2 Ns324p1130 Ns324p266 Ns324p1129 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1132 := nat_lit 19321166391302034638107406102794497553871118105727067728246788306123055190224647104883574508203882994579790321 

noncomputable def Ns324p1133 := nat_lit 2627248000089865592838347680099867562491105449725879499150868477073597651801039362168925798306842139121 

noncomputable def Ns324p1134 := nat_lit 96553385344280928752160852555180245739612290217127253421670772402407539818052813865937592164650603454259780081 

noncomputable def Ns324p1135 := BSN.sin_dyadic_bound_f 342734973 268435456 4 3 268435456 134217728 Ns324p1132 Ns324p119 Ns324p1133 Ns324p1134 Ns324p122 Ns324p1133 256916831 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 342734973) qz367 0 3 Ns324p1132 Ns324p119 Ns324p1133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 342734973) qz368 0 3 Ns324p1134 Ns324p122 Ns324p1133 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1136 := Ns324p1069 149042 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 106 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 217481768 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 155 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 256916831 268435456) qz171 rfl rfl (Ns324p1127 rfl) (Ns324p1104 rfl) RS325to336.d35 RS325to336.d37 RS325to336.d39 RS325to336.d41 RS325to336.d17 (Ns324p1131 rfl rfl) (Ns324p1135 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p1137 := nat_lit 1708013453390691482379150625 

noncomputable def Ns324p1138 := BSN.cos_dyadic_bound_f 6428695 268435456 2 1 268435456 134217728 Ns324p1137 Ns324p149 Ns324p1137 Ns324p1137 Ns324p150 Ns324p1137 268358480 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 6428695) qz369 0 1 Ns324p1137 Ns324p149 Ns324p1137 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 6428695) qz370 0 1 Ns324p1137 Ns324p150 Ns324p1137 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1139 := Ns324p1067 Bool.true 337290306 149042 Bool.true 6428695 14148475504056880 1 Bool.false 268358480 Bool.false Bool.true 252427904 161505 BSN.abs_quadSignPos qz596 (BSN.sfrac_eq_quadSignPos_mul Bool.false 268358480 268435456) qz171 rfl (Ns324p1136 rfl) (Ns324p1104 rfl) RS325to336.d43 RS325to336.d45 RS325to336.d17 (Ns324p1138 rfl rfl) rfl 

noncomputable def Ns324p1140 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) 252427904 268435456 161505 268435456 252427904 268435456 161505 268435456 135521199034728448 1972093 1048576 161505 134217728 (Ns324p1139 rfl rfl rfl rfl) 

noncomputable def Ns324p1141 := @Enclosure.Real.IsNear.mulLit_ff qz668 (Zeta.RiemannSiegel.correction qz170) 10485107 33554432 1 33554432 35811625325115 70368744177664 2462572431269647 10643272556871680000 375488723377740562305 2361183241434822606848 

noncomputable abbrev qz672 := (@HPow.hPow Real Real Real qz133 qz169 qz135)

noncomputable def Ns324p1142 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz672 1 1 0 1 10485107 33554432 1 33554432 10485107 33554432 1 33554432 

noncomputable def Ns324p1143 := @Enclosure.Real.IsNear.sqrt_image qz169 879828497103 8388608000 164751 8388608000 171820080 171820113 16777216 (@Enclosure.Real.IsNear.of_eq qz169 (@HMul.hMul Real Real Real qz5 qz168 qz3) Bool.false 879828497103 8388608000 164751 8388608000 (BSN.t_div_two_pi_mk qz168 659004 1000 qz171) (@Enclosure.Real.IsNear.mulLit_ff qz168 qz3 659004 1000 0 1 5340353 33554432 1 33554432 879828497103 8388608000 164751 8388608000 (Enclosure.Real.IsNear.const Bool.false 659004 1000) RS325to336.d48 rfl)) 

noncomputable abbrev qz763 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 659004 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz673 := qz763

noncomputable abbrev qz487 := qz673

noncomputable abbrev qz177 := qz487

noncomputable def Ns324p1144 := @Enclosure.Real.IsNear.sqrt_image qz177 343640193 33554432 33 33554432 53690432 53690439 16777216 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 343640193 33554432 33 33554432 343640193 33554432 33 33554432 (Ns324p1143 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns324p1145 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz177) 107380871 33554432 7 33554432 5242553 5242554 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz177) Bool.false 107380871 33554432 7 33554432 107380871 33554432 7 33554432 (Ns324p1144 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns324p1146 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz177)) Bool.false 10485107 33554432 1 33554432 10485107 33554432 1 33554432 (Ns324p1145 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz178 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz481))

noncomputable abbrev qz674 := (@HMul.hMul Real Real Real qz723 qz762 qz762)

noncomputable abbrev qz488 := (@HSub.hSub Real Real Real qz586 (@HSub.hSub Real Real Real qz586 qz674 qz667) qz600)

noncomputable abbrev qz179 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz488))

noncomputable def Ns324p1147 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz170) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz178) qz179) Bool.false 35811625325115 

noncomputable def Ns324p1148 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz178) qz179 153109837 8388608 17901 

noncomputable def Ns324p1149 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz178) Bool.false 612439348 33554432 71604 33554432 153109837 8388608 17901 

noncomputable def Ns324p1150 := @Enclosure.Real.IsNear.recentre' qz178 Bool.false 919193 16777216 65017152 10150215680000 919193 16777216 1015893 158597120000 

noncomputable abbrev qz180 := (@HMul.hMul Real Real Real qz349 qz346 qz481)

noncomputable def Ns324p1151 := @Enclosure.Real.IsNear.cos_image qz180 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 25433935) qz374) Bool.false 25433935 16777216 13 2097152 Bool.false 919193 16777216 1 

noncomputable def Ns324p1152 := nat_lit 890540488567996519555714727 

noncomputable def Ns324p1153 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz170 884279719003555 140737488355328 1 500000000000000 8095873 33554432 33 33554432 7159016301528467828515 4722366482869645213696 Ns324p1152 

noncomputable def Ns324p1154 := @Enclosure.Real.IsNear.subLit_ff_p qz177 qz1 343640193 33554432 33 33554432 10 1 0 1 8095873 8095873 33554432 33 

noncomputable def Ns324p1155 := @Ns324p1154 33554432 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 343640193 33554432 33 33554432 343640193 33554432 33 33554432 (Ns324p1143 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns324p1156 := @Enclosure.Real.IsNear.recentre' qz180 Bool.false 7159016301528467828515 4722366482869645213696 Ns324p1152 Ns324p173 25433935 16777216 13 2097152 (@Ns324p1153 Ns324p173 RS325to336.d47 (Ns324p1155 rfl rfl) rfl) 

noncomputable def Ns324p1157 := nat_lit 52589973171379420446077083365600288802453210916721214219885558518320149399666980762174181890625 

noncomputable def Ns324p1158 := nat_lit 73276157023256606728458593443930723206185050094266865046098069466679321914146308837890625 

noncomputable def Ns324p1159 := nat_lit 318378868973504089838772363446684851627801122260843798644835993740820899003018045281393791490625 

noncomputable def Ns324p1160 := BSN.cos_dyadic_bound_f 25433935 16777216 4 3 16777216 4840000 Ns324p1157 Ns324p825 Ns324p1158 Ns324p1159 Ns324p828 Ns324p1158 919193 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 25433935) qz601 0 3 Ns324p1157 Ns324p825 Ns324p1158 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 25433935) (BSN.cosOddQ 16777216) 0 3 Ns324p1159 Ns324p828 Ns324p1158 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1161 := @Enclosure.Real.IsNear.inv_image qz178 919193 16777216 1015893 158597120000 306183872 306255476 16777216 (Ns324p1150 (@Ns324p1151 4840000 (Ns324p1156 rfl) (Enclosure.sfrac_false_div 25433935 16777216) (Ns324p1160 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns324p1162 := @Enclosure.Real.IsNear.recentre' qz179 Bool.false 467790 16777216 

noncomputable abbrev qz181 := (@HMul.hMul Real Real Real qz349 qz346 qz488)

noncomputable def Ns324p1163 := @Enclosure.Real.IsNear.cos_image qz181 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 51771477)) qz391) Bool.true 51771477 33554432 

noncomputable def Ns324p1164 := nat_lit 244483892222482057273818605405 

noncomputable def Ns324p1165 := nat_lit 44301015047262068961392872317802453 

noncomputable def Ns324p1166 := @Enclosure.Real.IsNear.recentre' qz181 Bool.true Ns324p1164 Ns324p188 Ns324p1165 

noncomputable abbrev qz182 := qz488

noncomputable def Ns324p1167 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz182 884279719003555 140737488355328 1 500000000000000 276478004604671 

noncomputable abbrev qz489 := (@HSub.hSub Real Real Real qz586 qz674 qz667)

noncomputable abbrev qz183 := qz489

noncomputable def Ns324p1168 := @Enclosure.Real.IsNear.subLit_tf qz183 qz29 206109260427007 1125899906842624 1641624963 1125899906842624 1 16 

noncomputable abbrev qz490 := qz674

noncomputable abbrev qz184 := qz490

noncomputable def Ns324p1169 := @Enclosure.Real.IsNear.subLit_ff_n qz184 qz170 65543159632129 1125899906842624 534328707 1125899906842624 8095873 33554432 33 33554432 

noncomputable def Ns324p1170 := @Enclosure.Real.IsNear.mulLit_ff qz170 qz170 8095873 33554432 33 33554432 8095873 33554432 33 33554432 65543159632129 1125899906842624 

noncomputable def Ns324p1171 := nat_lit 231180025577965107182422447431307647244483541197343595145289979476954142198663010221305298778442001 

noncomputable def Ns324p1172 := nat_lit 370754698029759196596619040839954642457766964481524775772914506946179115453110398437988354321 

noncomputable def Ns324p1173 := nat_lit 1399346879039464971257782555436311385744127113274352085627987195969997342391242476564981890381105425 

noncomputable def Ns324p1174 := BSN.cos_dyadic_bound_f 51771477 33554432 4 3 16777216 4840000 Ns324p1171 Ns324p594 Ns324p1172 Ns324p1173 Ns324p597 Ns324p1172 467790 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 51771477) qz392 0 3 Ns324p1171 Ns324p594 Ns324p1172 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 51771477) (BSN.cosOddQ 33554432) 0 3 Ns324p1173 Ns324p597 Ns324p1172 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1175 := @Ns324p1162 1529114432 162403450880000 233895 8388608 23892413 2537553920000 (@Ns324p1163 309 33554432 Bool.false 467790 16777216 1 4840000 (@Ns324p1166 Ns324p191 51771477 33554432 309 33554432 (@Ns324p1167 1125899906842624 1641624963 1125899906842624 Ns324p1164 Ns324p188 Ns324p1165 Ns324p191 RS325to336.d47 (@Ns324p1168 0 1 4423648073674736 276478004604671 1125899906842624 1641624963 1125899906842624 (@Ns324p1169 6915879163568297345024 206109260427007 1125899906842624 1641624963 1125899906842624 (@Ns324p1170 534328707 1125899906842624 (Ns324p1155 rfl rfl) (Ns324p1155 rfl rfl) rfl) (Ns324p1155 rfl rfl) rfl rfl) qz379 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 51771477 33554432) (BSN.cos_neg_of_bound 51771477 33554432 Bool.false 467790 16777216 1 4840000 (Ns324p1174 rfl rfl)) rfl rfl) 

noncomputable def Ns324p1176 := @Ns324p1141 12912877204007624780313 Ns324p1064 (Ns324p1142 qz31 (@Enclosure.Real.IsNear.of_eq qz672 (@Inv.inv Real Real.instInv (Real.sqrt qz177)) Bool.false 10485107 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz169 (BSN.t_div_two_pi_nonneg qz168 659004 1000 qz171)) Ns324p1146) rfl) (@Ns324p1147 70368744177664 2462572431269647 10643272556871680000 (BSN.correction_mk qz170 (BSN.cos_two_pi_p_ne_zero_mk qz168 659004 1000 10 qz171 rfl rfl (@BSN.floor_sqrt_eq_dec qz168 659004 1000 10 qz171 rfl rfl rfl))) (@Ns324p1148 8388608 233895 8388608 23892413 2537553920000 35811625325115 70368744177664 2462572431269647 10643272556871680000 (@Ns324p1149 8388608 (Ns324p1161 rfl rfl rfl rfl rfl) rfl) (Ns324p1175 rfl) rfl)) 

noncomputable def Ns324p1177 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz168) (hardyZApproximantRS₀ qz168) Bool.true 4816247373347722346369 2361183241434822606848 227780593991202709580313 Ns324p1064 (@Eq.refl Real (hardyZApproximantRS₀ qz168)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz168) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (@HMul.hMul Real Real Real qz5 qz668 (Zeta.RiemannSiegel.correction qz170))) Bool.true 4816247373347722346369 2361183241434822606848 227780593991202709580313 Ns324p1064 (BSN.hardyZApproximantRS₀_eq qz168 10 (@BSN.floor_sqrt_eq_dec qz168 659004 1000 10 qz171 rfl rfl rfl)) (@Ns324p1066 4816247373347722346369 2361183241434822606848 227780593991202709580313 Ns324p1064 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (@HAdd.hAdd Real Real Real qz366 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 10)) Bool.true 1972093 1048576 161505 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (Ns324p1140 (Ns324p1139 rfl rfl rfl rfl) rfl rfl)) (Ns324p1176 rfl) rfl rfl)) 

theorem RS325to336.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz168) Bool.true 4816247373347722346369 2361183241434822606848 227780593991202709580313 Ns324p1064 := Ns324p1177 

noncomputable def Ns324p1178 := nat_lit 12251792428102524807619280896 

noncomputable abbrev qz764 := (Enclosure.sfrac Bool.false 660354 1000)

noncomputable abbrev qz675 := qz764

noncomputable abbrev qz491 := qz675

noncomputable abbrev qz185 := qz491

noncomputable abbrev qz765 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 660354 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz676 := qz765

noncomputable abbrev qz492 := qz676

noncomputable abbrev qz186 := qz492

noncomputable abbrev qz766 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 660354 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz677 := qz766

noncomputable abbrev qz493 := qz677

noncomputable abbrev qz187 := qz493

noncomputable abbrev qz678 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz133 qz186 qz135))

noncomputable def Ns324p1179 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz185) qz185 10) (@HMul.hMul Real Real Real qz5 qz678 (Zeta.RiemannSiegel.correction qz187)) 186928825 134217728 161831 134217728 11482241384643574743 73786976294838206464 26402899105613694821301 Ns324p483 Ns324p1178 

noncomputable def Ns324p1180 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz185) qz185 Real.sin BSN.quadSignPos 9 10 660354 1000 199 268435456 134217728 4503599627370496 Bool.false 323832727000 2480 618095470 56 84886744 8 

noncomputable def Ns324p1181 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz185) qz185 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 660354 1000 106 155 268435456 134217728 4503599627370496 Bool.false 323832727000 2480 

noncomputable def Ns324p1182 := Ns324p1181 558195838 56 94906264 8 589812974 56 89478488 8 Bool.false 113116862 122218 Bool.true 78440010 Bool.true 295728251 14148475504056880 1 Bool.false 257056224 Bool.true Bool.false 239435096 Bool.false Bool.false 102045465 

noncomputable def Ns324p1183 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz185) qz185 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 660354 1000 14 50 268435456 134217728 4503599627370496 Bool.false 323832727000 2480 

noncomputable def Ns324p1184 := Ns324p1183 480971758 57 109588312 8 522351262 57 101459064 8 Bool.false 255573634 90655 Bool.false 317898721 Bool.true 21146853 14148475504056880 1 Bool.false 101194236 Bool.true Bool.false 267602931 Bool.true Bool.false 113116862 

noncomputable def Ns324p1185 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz185) qz185 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 660354 1000 185 91 268435456 134217728 4503599627370496 Bool.false 323832727000 2480 

noncomputable def Ns324p1186 := Ns324p1185 372130544 56 134217720 8 432030192 56 120047984 16 Bool.false 228191721 53250 Bool.false 88209518 Bool.false 169035619 14148475504056880 1 Bool.false 86630561 Bool.true Bool.false 158083728 Bool.false Bool.false 255573634 

noncomputable def Ns324p1187 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz185) qz185 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 660354 1000 476 306 268435456 134217728 4503599627370496 Bool.false 323832727000 2480 

noncomputable def Ns324p1188 := Ns324p1187 186065264 56 189812528 16 294906480 56 154981288 8 Bool.false 268435392 2536 Bool.false 254849801 Bool.false 62880256 14148475504056880 1 Bool.false 156277640 Bool.false Bool.false 261104308 Bool.true Bool.false 228191721 

noncomputable def Ns324p1189 := nat_lit 175979586054930544167666091646284335602765931434387009 

noncomputable def Ns324p1190 := nat_lit 145875189536434300529843590322427144626832513433600 

noncomputable def Ns324p1191 := nat_lit 60273433570990291083659207531520000 

noncomputable def Ns324p1192 := nat_lit 238810881606315652746814942093232148480 

noncomputable abbrev qz679 := (@Eq.refl Real qz764)

noncomputable abbrev qz494 := qz679

noncomputable abbrev qz188 := qz494

noncomputable def Ns324p1193 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz185 660354 1000 1744270621264 16000000 1320708 4000 2000 Ns324p1191 Ns324p1192 qz188 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns324p1194 := nat_lit 32436557301644797900984214012243128738301816481986213498880 

noncomputable abbrev qz680 := (@HSub.hSub Real Real Real qz727 qz728 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz729 (@Nat.cast Real Real.instNatCast 1320708))))

noncomputable abbrev qz495 := (@HSub.hSub Real Real Real qz586 (@HMul.hMul Real Real Real qz582 (Enclosure.sfrac Bool.false 660354 4000) (Real.log (Enclosure.sfrac Bool.false 1744270621264 16000000))) (@HMul.hMul Real Real Real qz582 qz587 qz680))

noncomputable abbrev qz681 := (Enclosure.sfrac Bool.false 660354 2000)

noncomputable abbrev qz189 := (@HSub.hSub Real Real Real qz354 (@HSub.hSub Real Real Real qz354 qz495 qz681) (@HMul.hMul Real Real Real qz349 qz681 (Real.log Real.pi)))

noncomputable def Ns324p1195 := @Enclosure.Real.IsNear.addLit_ft_p qz189 (Enclosure.sfrac Bool.true Ns324p1191 Ns324p1192) 135825318635615708981 112589990684262400 2288587544096945253 247808000000000000000000 Ns324p1191 Ns324p1192 0 1 Ns324p1194 

noncomputable def Ns324p1196 := nat_lit 22787707090185500425673768960000 

noncomputable abbrev qz190 := (@HSub.hSub Real Real Real qz354 qz495 qz681)

noncomputable def Ns324p1197 := @Enclosure.Real.IsNear.subLit_ff_p qz190 (@HMul.hMul Real Real Real qz5 qz681 (Real.log Real.pi)) 891901115742354408457 562949953421312000 522151882126461 121000000000000000000 12682349834697 33554432000 330177 67108864000 Ns324p1196 135825318635615708981 112589990684262400 

noncomputable def Ns324p1198 := nat_lit 1783802231484708816914000 

noncomputable abbrev qz191 := qz495

noncomputable def Ns324p1199 := @Enclosure.Real.IsNear.subLit_ff_p qz191 qz681 1077774242513142940681 562949953421312000 522151882126461 121000000000000000000 660354 2000 0 1 Ns324p1198 891901115742354408457 562949953421312000 522151882126461 121000000000000000000 

noncomputable def Ns324p1200 := nat_lit 2426931838485854568001392066468773888 

noncomputable def Ns324p1201 := nat_lit 56090571475417395313508352 

noncomputable def Ns324p1202 := nat_lit 30432166615765815868612458505866105304918951360902946014291837477309936561041877465429989023268521772064099874038990499696927927079410144774800060406824960 

noncomputable def Ns324p1203 := nat_lit 653966167133637999428125916900006265484006203682729700040711422036093751527957007167466322450910458006426750732545529663586273433890274749298764584845312 

noncomputable def Ns324p1204 := nat_lit 133612854191882865717485137107378425506211000871264749985607794736953780474290256587263130832318463775618608247672250281948028777707296929003601920 

noncomputable def Ns324p1205 := BSN.log_dyadic_bound 695694621264 2792846621264 7 6 Ns324p1202 134217728 38720000 Ns324p1203 Ns324p1204 68303862 3488541242528 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 695694621264) (BSN.artanhQ 2792846621264) 0 6 Ns324p1203 Ns324p1202 Ns324p1204 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz496 := (Real.log (Enclosure.sfrac Bool.false 1744270621264 16000000))

noncomputable def Ns324p1206 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 660354 4000) qz496 660354 4000 0 1 3264900964883703 281474976710656 195312621 7562500000000000 1077995205882406405431 562949953421312000 64487735263917 15125000000000000000 (Enclosure.Real.IsNear.const Bool.false 660354 4000) (BSN.isNear_log_sfrac 1744270621264 16000000 3264900964883703 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1744270621264) qz357)) Bool.false Ns324p1201 Ns324p98 1000000619520000 38720000000000000000000 3264900964883703 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1744270621264 16000000 16 3488541242528 2097152000000 68303862 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns324p1205 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns324p1207 := BSN.arctan_dyadic_bound_f 1000 1320708 1 0 16777216 4840000 0 1 1 0 1 1 12703 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1320708) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1320708) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns324p1208 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1320708))) 884279719003555 562949953421312 1 2000000000000000 12703 16777216 1 4840000 14828600696883636076544 883853477053859 562949953421312 50000000121 242000000000000000 qz15 (Ns324p1207 rfl) rfl rfl 

noncomputable abbrev qz497 := (@HMul.hMul Real Real Real qz582 qz587 qz680)

noncomputable abbrev qz192 := qz497

noncomputable abbrev qz498 := qz680

noncomputable abbrev qz193 := qz498

noncomputable def Ns324p1209 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 660354 4000) qz496) qz192 1077995205882406405431 562949953421312000 64487735263917 15125000000000000000 883853477053859 2251799813685248 50000000121 968000000000000000 Ns324p1200 1077774242513142940681 562949953421312000 522151882126461 121000000000000000000 (Ns324p1206 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz193 1 4 0 1 883853477053859 562949953421312 50000000121 242000000000000000 883853477053859 2251799813685248 50000000121 968000000000000000 qz365 Ns324p1208 rfl) 

noncomputable def Ns324p1210 := @Ns324p1195 Ns324p1189 Ns324p1190 2288587544096945253 247808000000000000000000 (@Ns324p1197 2288587544096945253 247808000000000000000000 (Ns324p1199 (Ns324p1209 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 660354 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz681 (Real.log Real.pi) 660354 2000 0 1 38410761 33554432 1 67108864 12682349834697 33554432000 330177 67108864000 (Enclosure.Real.IsNear.const Bool.false 660354 2000) RS325to336.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns324p1191 Ns324p1192) 

noncomputable def Ns324p1211 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz185) Bool.false Ns324p1189 Ns324p1190 2288587544096945253 247808000000000000000000 40479090875 33554432 155 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz185) (@HAdd.hAdd Real Real Real qz366 qz189 (Enclosure.sfrac Bool.true Ns324p1191 Ns324p1192)) Bool.false Ns324p1189 Ns324p1190 2288587544096945253 247808000000000000000000 Ns324p1193 (Ns324p1210 rfl rfl)) 

noncomputable def Ns324p1212 := nat_lit 7592700032143080271380480 

noncomputable def Ns324p1213 := nat_lit 3504902087627596339494233435566485618450337395352283404814430595881702354887575559081766960863898232334473403852511657781730785831363280896 

noncomputable def Ns324p1214 := nat_lit 2489988273900512287140828728108026310399028990838083983901616443446260768364734969703770397134473615238926065414712435256214627024896 

noncomputable def Ns324p1215 := nat_lit 17502770743405976467424854800461633250713780992551765894013599118314158937538005102151513827159275923883232297323834429929903344282612269056 

noncomputable def Ns324p1216 := BSN.sin_dyadic_bound_f 107898757052 68719476736 4 3 33554432 9689454 Ns324p1213 Ns324p110 Ns324p1214 Ns324p1215 Ns324p113 Ns324p1214 33554424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107898757052) qz593 0 3 Ns324p1213 Ns324p110 Ns324p1214 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107898757052) qz594 0 3 Ns324p1215 Ns324p113 Ns324p1214 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1217 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz185) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40479090875) qz391) Bool.false 40479090875 33554432 155 16777216 Bool.false 33554424 33554432 1 4840000 (Ns324p1211 rfl) (Enclosure.sfrac_false_div 40479090875 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40479090875) qz391) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns324p1212) qz409) 226375608064910080 72057594037927936 Bool.false 33554424 33554432 191 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q3 40479090875 33554432 226375608064910080 72057594037927936 191 Ns324p1212 Ns324p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554424 33554432 Ns324p1212 Ns324p98 107898757052 68719476736 9689454 9680000 (Ns324p1216 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns324p1218 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz185) Bool.false Ns324p1189 Ns324p1190 2288587544096945253 247808000000000000000000 323832727000 268435456 2480 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz185) (@HAdd.hAdd Real Real Real qz366 qz189 (Enclosure.sfrac Bool.true Ns324p1191 Ns324p1192)) Bool.false Ns324p1189 Ns324p1190 2288587544096945253 247808000000000000000000 Ns324p1193 (Ns324p1210 rfl rfl)) 

noncomputable def Ns324p1219 := Ns324p1188 53250 BSN.abs_quadSignPos (BSN.cos_quad_nat0 476 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 156277640 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 306 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 261104308 268435456) qz188 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz185) qz185 1) Bool.false 4194303 4194304 11984019 1268776960000 268435392 268435456 2536 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz185) qz185 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz185)) Bool.false 4194303 4194304 11984019 1268776960000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz185) qz185) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz185)) Bool.false 33554424 33554432 766977216 81201725440000 4194303 4194304 11984019 1268776960000 (Ns324p1217 rfl rfl) rfl)) rfl) (Ns324p1218 rfl) RS325to336.d7 

noncomputable def Ns324p1220 := nat_lit 36814249956659549826011729627590746978617718262838704783527141931855681 

noncomputable def Ns324p1221 := nat_lit 17794032950225150655255104342587225087132161730711864222561271918401 

noncomputable def Ns324p1222 := nat_lit 110407161804078199176724678674087066485678890465054690622136303251730241 

noncomputable def Ns324p1223 := BSN.cos_dyadic_bound_f 254849801 268435456 3 2 268435456 134217728 Ns324p1220 Ns324p263 Ns324p1221 Ns324p1222 Ns324p266 Ns324p1221 156277640 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 254849801) qz369 0 2 Ns324p1220 Ns324p263 Ns324p1221 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 254849801) qz370 0 2 Ns324p1222 Ns324p266 Ns324p1221 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1224 := nat_lit 15633535515687087688200063287296 

noncomputable def Ns324p1225 := BSN.cos_dyadic_bound_f 62880256 268435456 2 1 268435456 134217728 Ns324p1224 Ns324p149 Ns324p1224 Ns324p1224 Ns324p150 Ns324p1224 261104308 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 62880256) qz369 0 1 Ns324p1224 Ns324p149 Ns324p1224 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 62880256) qz370 0 1 Ns324p1224 Ns324p150 Ns324p1224 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1226 := nat_lit 60542701508410492060141897320976 

noncomputable def Ns324p1227 := BSN.sin_dyadic_bound_f 88209518 268435456 2 1 268435456 134217728 Ns324p1226 Ns324p270 Ns324p1226 Ns324p1226 Ns324p271 Ns324p1226 86630561 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 88209518) qz367 0 1 Ns324p1226 Ns324p270 Ns324p1226 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 88209518) qz368 0 1 Ns324p1226 Ns324p271 Ns324p1226 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1228 := nat_lit 12819668514399691114890739109063540520820876751585975642094933297304225 

noncomputable def Ns324p1229 := nat_lit 666539400448444224062812377691257269193990209863076801798723310241 

noncomputable def Ns324p1230 := nat_lit 33574243140588941153112976922745391709428363127147300747807627369484961 

noncomputable def Ns324p1231 := BSN.sin_dyadic_bound_f 169035619 268435456 3 2 268435456 134217728 Ns324p1228 Ns324p249 Ns324p1229 Ns324p1230 Ns324p252 Ns324p1229 158083728 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 169035619) qz367 0 2 Ns324p1228 Ns324p249 Ns324p1229 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 169035619) qz368 0 2 Ns324p1230 Ns324p252 Ns324p1229 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1232 := Ns324p1186 90655 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 185 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 86630561 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 91 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 158083728 268435456) qz188 rfl rfl (Ns324p1219 RS325to336.d9 RS325to336.d11 RS325to336.d13 RS325to336.d17 (Ns324p1223 rfl rfl) (Ns324p1225 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns324p1218 rfl) RS325to336.d19 RS325to336.d21 RS325to336.d23 RS325to336.d25 RS325to336.d17 (Ns324p1227 rfl rfl) (Ns324p1231 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns324p1233 := nat_lit 5501842280620572494260783794261627736721284104338331531953983596747796399950840017663521555447626258199086721 

noncomputable def Ns324p1234 := nat_lit 1065283909952239707625086027174071413841569886736756828192734159640343740389963141924706434181583079041 

noncomputable def Ns324p1235 := nat_lit 33351815507919050403398708767167302721835635731261427305145576826914232834272328641943713862909131513749833345 

noncomputable def Ns324p1236 := BSN.cos_dyadic_bound_f 317898721 268435456 4 3 268435456 134217728 Ns324p1233 Ns324p125 Ns324p1234 Ns324p1235 Ns324p128 Ns324p1234 101194236 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 317898721) qz369 0 3 Ns324p1233 Ns324p125 Ns324p1234 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 317898721) qz370 0 3 Ns324p1235 Ns324p128 Ns324p1234 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1237 := nat_lit 199978352141681720270025424881 

noncomputable def Ns324p1238 := BSN.cos_dyadic_bound_f 21146853 268435456 2 1 268435456 134217728 Ns324p1237 Ns324p149 Ns324p1237 Ns324p1237 Ns324p150 Ns324p1237 267602931 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 21146853) qz369 0 1 Ns324p1237 Ns324p149 Ns324p1237 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 21146853) qz370 0 1 Ns324p1237 Ns324p150 Ns324p1237 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1239 := Ns324p1184 122218 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 14 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 101194236 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 50 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267602931 268435456) qz188 rfl rfl (Ns324p1232 rfl rfl) (Ns324p1218 rfl) RS325to336.d27 RS325to336.d29 RS325to336.d31 RS325to336.d33 RS325to336.d17 (Ns324p1236 rfl rfl) (Ns324p1238 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p1240 := nat_lit 37857380614423355060473760010000 

noncomputable def Ns324p1241 := BSN.cos_dyadic_bound_f 78440010 268435456 2 1 268435456 134217728 Ns324p1240 Ns324p149 Ns324p1240 Ns324p1240 Ns324p150 Ns324p1240 257056224 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 78440010) qz369 0 1 Ns324p1240 Ns324p149 Ns324p1240 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 78440010) qz370 0 1 Ns324p1240 Ns324p150 Ns324p1240 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1242 := nat_lit 120150078642504889075844878674050609155193014353264839750679842117198305 

noncomputable def Ns324p1243 := nat_lit 58498202054251977557635354274010681649960975371622975288937924076001 

noncomputable def Ns324p1244 := nat_lit 314584066022282111044500415477498435255215100774615762148931782239396321 

noncomputable def Ns324p1245 := BSN.sin_dyadic_bound_f 295728251 268435456 3 2 268435456 134217728 Ns324p1242 Ns324p249 Ns324p1243 Ns324p1244 Ns324p252 Ns324p1243 239435096 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 295728251) qz367 0 2 Ns324p1242 Ns324p249 Ns324p1243 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 295728251) qz368 0 2 Ns324p1244 Ns324p252 Ns324p1243 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1246 := Ns324p1182 149342 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 106 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 257056224 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 155 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 239435096 268435456) qz188 rfl rfl (Ns324p1239 rfl) (Ns324p1218 rfl) RS325to336.d35 RS325to336.d37 RS325to336.d39 RS325to336.d41 RS325to336.d17 (Ns324p1241 rfl rfl) (Ns324p1245 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p1247 := nat_lit 43312086240213557772509309769378173738175592337657967461579074356237129687324241110767106304086409493844816241 

noncomputable def Ns324p1248 := nat_lit 29499234328397248465196908575581659938579326847668126001289461996724161540643171874935055159121017270641 

noncomputable def Ns324p1249 := nat_lit 216297385191409694958647040477276644611307682769348482008964376471673888918120510873124290186241840640041644401 

noncomputable def Ns324p1250 := BSN.sin_dyadic_bound_f 419260771 268435456 4 3 268435456 134217728 Ns324p1247 Ns324p119 Ns324p1248 Ns324p1249 Ns324p122 Ns324p1248 268424757 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 419260771) qz367 0 3 Ns324p1247 Ns324p119 Ns324p1248 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 419260771) qz368 0 3 Ns324p1249 Ns324p122 Ns324p1248 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1251 := Ns324p1180 Bool.false 102045465 149342 Bool.true 419260771 14148475504056880 1 Bool.false 268424757 Bool.false Bool.false 186928825 161831 BSN.abs_quadSignPos (BSN.cos_quad_nat3 199 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268424757 268435456) qz188 rfl (Ns324p1246 rfl) (Ns324p1218 rfl) RS325to336.d43 RS325to336.d45 RS325to336.d17 (Ns324p1250 rfl rfl) rfl 

noncomputable def Ns324p1252 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz185) qz185 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz185) qz185 10) 186928825 268435456 161831 268435456 186928825 268435456 161831 268435456 100356648756838400 186928825 134217728 161831 134217728 (Ns324p1251 rfl rfl rfl rfl) 

noncomputable def Ns324p1253 := @Enclosure.Real.IsNear.mulLit_ff qz678 (Zeta.RiemannSiegel.correction qz187) 81873 262144 1 16777216 140244541969191 281474976710656 2519219254638081 2128654511374336000 11482241384643574743 73786976294838206464 

noncomputable abbrev qz682 := (@HPow.hPow Real Real Real qz133 qz186 qz135)

noncomputable def Ns324p1254 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz682 1 1 0 1 81873 262144 1 16777216 81873 262144 1 16777216 

noncomputable def Ns324p1255 := @Enclosure.Real.IsNear.sqrt_image qz186 1763261732481 16777216000 330177 16777216000 171995980 171996014 16777216 (@Enclosure.Real.IsNear.of_eq qz186 (@HMul.hMul Real Real Real qz5 qz185 qz3) Bool.false 1763261732481 16777216000 330177 16777216000 (BSN.t_div_two_pi_mk qz185 660354 1000 qz188) (@Enclosure.Real.IsNear.mulLit_ff qz185 qz3 660354 1000 0 1 5340353 33554432 1 33554432 1763261732481 16777216000 330177 16777216000 (Enclosure.Real.IsNear.const Bool.false 660354 1000) RS325to336.d48 rfl)) 

noncomputable abbrev qz767 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 660354 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz683 := qz767

noncomputable abbrev qz499 := qz683

noncomputable abbrev qz194 := qz499

noncomputable def Ns324p1256 := @Enclosure.Real.IsNear.sqrt_image qz194 171995997 16777216 17 16777216 53717908 53717914 16777216 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 343991994 33554432 34 33554432 171995997 16777216 17 16777216 (Ns324p1255 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns324p1257 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz194) 53717911 16777216 3 16777216 5239871 5239873 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz194) Bool.false 107435822 33554432 6 33554432 53717911 16777216 3 16777216 (Ns324p1256 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns324p1258 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz194)) Bool.false 10479744 33554432 2 33554432 81873 262144 1 16777216 (Ns324p1257 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz500 := (@HMul.hMul Real Real Real qz582 qz580 qz677)

noncomputable abbrev qz195 := (Real.cos qz500)

noncomputable abbrev qz684 := (@HMul.hMul Real Real Real qz723 qz766 qz766)

noncomputable abbrev qz501 := (@HSub.hSub Real Real Real qz586 (@HSub.hSub Real Real Real qz586 qz684 qz677) qz600)

noncomputable abbrev qz196 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz501))

noncomputable def Ns324p1259 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz187) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz195) qz196) Bool.false 140244541969191 

noncomputable def Ns324p1260 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz195) qz196 3033823133 33554432 1806097 

noncomputable abbrev qz197 := (@Neg.neg Real Real.instNeg (Real.cos qz500))

noncomputable def Ns324p1261 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz195) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz197)) Bool.true 3033823133 33554432 1806097 33554432 (BSN.inv_eq_neg_inv_neg qz195) 

noncomputable def Ns324p1262 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz197) Bool.false 3033823133 33554432 1806097 33554432 3033823133 33554432 

noncomputable def Ns324p1263 := @Enclosure.Real.IsNear.recentre' qz195 Bool.true 185558 16777216 534657216 81201725440000 92779 8388608 8354019 1268776960000 

noncomputable abbrev qz198 := qz500

noncomputable def Ns324p1264 := @Enclosure.Real.IsNear.cos_image qz198 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 53078301) qz391) Bool.false 53078301 33554432 107 16777216 Bool.true 185558 16777216 1 

noncomputable def Ns324p1265 := nat_lit 458763281990031256295141943 

noncomputable def Ns324p1266 := nat_lit 72057594037927936000000000000000 

noncomputable def Ns324p1267 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz187 884279719003555 140737488355328 1 500000000000000 4223837 16777216 17 16777216 3735053395476818740535 2361183241434822606848 Ns324p1265 

noncomputable def Ns324p1268 := @Enclosure.Real.IsNear.subLit_ff_p qz194 qz1 171995997 16777216 17 16777216 10 1 0 1 4223837 4223837 16777216 17 

noncomputable def Ns324p1269 := @Ns324p1268 16777216 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 343991994 33554432 34 33554432 171995997 16777216 17 16777216 (Ns324p1255 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns324p1270 := @Enclosure.Real.IsNear.recentre' qz198 Bool.false 3735053395476818740535 2361183241434822606848 Ns324p1265 Ns324p1266 53078301 33554432 107 16777216 (@Ns324p1267 Ns324p1266 RS325to336.d47 (Ns324p1269 rfl rfl) rfl) 

noncomputable def Ns324p1271 := nat_lit 255510859513372004083209051818000899643853743037238744960306498619489762622018984747746002508416881 

noncomputable def Ns324p1272 := nat_lit 500039319362560230931051467378228320681883368563356276791707223828783616167672668752715679601 

noncomputable def Ns324p1273 := nat_lit 1546259511339453599343965181866355087440099754474840946834650308187897730590836588622558222920419185 

noncomputable def Ns324p1274 := BSN.cos_dyadic_bound_t 53078301 33554432 4 3 16777216 4840000 Ns324p1271 Ns324p594 Ns324p1272 Ns324p1273 Ns324p597 Ns324p1272 185558 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 53078301) qz392 0 3 Ns324p1271 Ns324p594 Ns324p1272 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 53078301) (BSN.cosOddQ 33554432) 0 3 Ns324p1273 Ns324p597 Ns324p1272 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1275 := @Enclosure.Real.IsNear.inv_image qz197 92779 8388608 8354019 1268776960000 1516008518 1517814615 16777216 (@Enclosure.Real.IsNear.neg qz195 Bool.true 92779 8388608 8354019 1268776960000 (Ns324p1263 (@Ns324p1264 4840000 (Ns324p1270 rfl) (Enclosure.sfrac_false_div 53078301 33554432) (Ns324p1274 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns324p1276 := Ns324p1261 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz197) Bool.false 3033823133 33554432 1806097 33554432 (@Ns324p1262 1806097 33554432 (Ns324p1275 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns324p1277 := @Enclosure.Real.IsNear.recentre' qz196 Bool.true 92454 16777216 

noncomputable abbrev qz199 := (@HMul.hMul Real Real Real qz349 qz346 qz501)

noncomputable def Ns324p1278 := @Enclosure.Real.IsNear.cos_image qz199 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 26446043)) qz374) Bool.true 26446043 16777216 

noncomputable def Ns324p1279 := nat_lit 62443954190671833584730416645 

noncomputable def Ns324p1280 := nat_lit 11572261122904674588284468587330461 

noncomputable def Ns324p1281 := @Enclosure.Real.IsNear.recentre' qz199 Bool.true Ns324p1279 Ns324p468 Ns324p1280 

noncomputable def Ns324p1282 := nat_lit 1208925819614629174706176000000000000000 

noncomputable abbrev qz200 := qz501

noncomputable def Ns324p1283 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz200 884279719003555 140737488355328 1 500000000000000 70615612739639 

noncomputable abbrev qz502 := (@HSub.hSub Real Real Real qz586 qz684 qz677)

noncomputable abbrev qz201 := qz502

noncomputable def Ns324p1284 := @Enclosure.Real.IsNear.subLit_tf qz201 qz29 53023426695223 281474976710656 428823419 281474976710656 1 16 

noncomputable abbrev qz503 := qz684

noncomputable abbrev qz202 := qz503

noncomputable def Ns324p1285 := @Enclosure.Real.IsNear.subLit_ff_n qz202 qz187 17840799002569 281474976710656 143610747 281474976710656 4223837 16777216 17 16777216 

noncomputable def Ns324p1286 := @Enclosure.Real.IsNear.mulLit_ff qz187 qz187 4223837 16777216 17 16777216 4223837 16777216 17 16777216 17840799002569 281474976710656 

noncomputable def Ns324p1287 := nat_lit 61506584270187887921557153074005260538222740487018763847573941940982387410124498664848765526481 

noncomputable def Ns324p1288 := nat_lit 117038405625789673384463817048734173797619505937657769089420718293740544336836643318440401 

noncomputable def Ns324p1289 := nat_lit 372228514929521823180887343908826178222097834446934528791137139283523727751882683518975089091025 

noncomputable def Ns324p1290 := BSN.cos_dyadic_bound_t 26446043 16777216 4 3 16777216 4840000 Ns324p1287 Ns324p825 Ns324p1288 Ns324p1289 Ns324p828 Ns324p1288 92454 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 26446043) qz601 0 3 Ns324p1287 Ns324p825 Ns324p1288 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 26446043) (BSN.cosOddQ 16777216) 0 3 Ns324p1289 Ns324p828 Ns324p1288 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1291 := @Ns324p1277 796017216 81201725440000 46227 8388608 12437769 1268776960000 (@Ns324p1278 161 16777216 Bool.true 92454 16777216 1 4840000 (@Ns324p1281 Ns324p1282 26446043 16777216 161 16777216 (@Ns324p1283 281474976710656 428823419 281474976710656 Ns324p1279 Ns324p468 Ns324p1280 Ns324p1282 RS325to336.d47 (@Ns324p1284 0 1 1129849803834224 70615612739639 281474976710656 428823419 281474976710656 (@Ns324p1285 889585482725922439168 53023426695223 281474976710656 428823419 281474976710656 (@Ns324p1286 143610747 281474976710656 (Ns324p1269 rfl rfl) (Ns324p1269 rfl rfl) rfl) (Ns324p1269 rfl rfl) rfl rfl) qz379 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 26446043 16777216) (BSN.cos_neg_of_bound 26446043 16777216 Bool.true 92454 16777216 1 4840000 (Ns324p1290 rfl rfl)) rfl rfl) 

noncomputable def Ns324p1292 := @Ns324p1253 26402899105613694821301 Ns324p483 (Ns324p1254 qz31 (@Enclosure.Real.IsNear.of_eq qz682 (@Inv.inv Real Real.instInv (Real.sqrt qz194)) Bool.false 81873 262144 1 16777216 (BSN.rpow_neg_quarter_mk qz186 (BSN.t_div_two_pi_nonneg qz185 660354 1000 qz188)) Ns324p1258) rfl) (@Ns324p1259 281474976710656 2519219254638081 2128654511374336000 (BSN.correction_mk qz187 (BSN.cos_two_pi_p_ne_zero_mk qz185 660354 1000 10 qz188 rfl rfl (@BSN.floor_sqrt_eq_dec qz185 660354 1000 10 qz188 rfl rfl rfl))) (@Ns324p1260 33554432 46227 8388608 12437769 1268776960000 140244541969191 281474976710656 2519219254638081 2128654511374336000 Ns324p1276 (Ns324p1291 rfl) rfl)) 

noncomputable def Ns324p1293 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz185) (hardyZApproximantRS₀ qz185) Bool.false 91282966942358946857 73786976294838206464 112523471163168737125301 Ns324p483 (@Eq.refl Real (hardyZApproximantRS₀ qz185)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz185) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz185) qz185 10) (@HMul.hMul Real Real Real qz5 qz678 (Zeta.RiemannSiegel.correction qz187))) Bool.false 91282966942358946857 73786976294838206464 112523471163168737125301 Ns324p483 (BSN.hardyZApproximantRS₀_eq qz185 10 (@BSN.floor_sqrt_eq_dec qz185 660354 1000 10 qz188 rfl rfl rfl)) (@Ns324p1179 91282966942358946857 73786976294838206464 112523471163168737125301 Ns324p483 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz185) qz185 10) (@HAdd.hAdd Real Real Real qz366 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz185) qz185 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz185) qz185 10)) Bool.false 186928825 134217728 161831 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz185) qz185 10) (Ns324p1252 (Ns324p1251 rfl rfl rfl rfl) rfl rfl)) (Ns324p1292 rfl) rfl rfl)) 

theorem RS325to336.d60 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz185) Bool.false 91282966942358946857 73786976294838206464 112523471163168737125301 Ns324p483 := Ns324p1293 

noncomputable def Ns324p1294 := nat_lit 2067606662725917996122487390208 

noncomputable abbrev qz768 := (Enclosure.sfrac Bool.false 661704 1000)

noncomputable abbrev qz685 := qz768

noncomputable abbrev qz504 := qz685

noncomputable abbrev qz203 := qz504

noncomputable abbrev qz769 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 661704 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz686 := qz769

noncomputable abbrev qz505 := qz686

noncomputable abbrev qz204 := qz505

noncomputable abbrev qz770 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 661704 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz687 := qz770

noncomputable abbrev qz506 := qz687

noncomputable abbrev qz205 := qz506

noncomputable abbrev qz688 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz133 qz204 qz135))

noncomputable def Ns324p1295 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz203) qz203 10) (@HMul.hMul Real Real Real qz5 qz688 (Zeta.RiemannSiegel.correction qz205)) 417381193 134217728 162171 134217728 719574885983552138085 4722366482869645213696 4640107701631743307253 Ns324p363 Ns324p1294 

noncomputable def Ns324p1296 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz203) qz203 Real.sin BSN.quadSignPos 9 10 661704 1000 199 268435456 134217728 4503599627370496 Bool.false 324676351630 2485 618095470 56 84886744 8 

noncomputable def Ns324p1297 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz203) qz203 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 661704 1000 105 155 268435456 134217728 4503599627370496 Bool.false 324676351630 2485 

noncomputable def Ns324p1298 := Ns324p1297 558195838 56 94906264 8 589812974 56 89478488 8 Bool.true 478840513 122478 Bool.true 410037189 Bool.true 248351136 14148475504056880 1 Bool.false 268183982 Bool.true Bool.false 214407217 Bool.false Bool.true 502188794 

noncomputable def Ns324p1299 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz203) qz203 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 661704 1000 15 49 268435456 134217728 4503599627370496 Bool.false 324676351630 2485 

noncomputable def Ns324p1300 := Ns324p1299 480971758 57 109588312 8 522351262 57 101459064 8 Bool.true 423186941 90851 Bool.false 90554050 Bool.true 304353855 14148475504056880 1 Bool.false 88846312 Bool.false Bool.false 243210494 Bool.true Bool.true 478840513 

noncomputable def Ns324p1301 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz203) qz203 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 661704 1000 186 92 268435456 134217728 4503599627370496 Bool.false 324676351630 2485 

noncomputable def Ns324p1302 := Ns324p1301 372130544 56 134217720 8 432030192 56 120047984 16 Bool.true 409023685 53369 Bool.false 7800485 Bool.false 7762062 14148475504056880 1 Bool.false 268322126 Bool.true Bool.false 268323240 Bool.false Bool.true 423186941 

noncomputable def Ns324p1303 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz203) qz203 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 661704 1000 478 307 268435456 134217728 4503599627370496 Bool.false 324676351630 2485 

noncomputable def Ns324p1304 := Ns324p1303 186065264 56 189812528 16 294906480 56 154981288 8 Bool.true 268435416 2552 Bool.false 3971468 Bool.false 86723710 14148475504056880 1 Bool.false 268406077 Bool.true Bool.false 85222934 Bool.false Bool.true 409023685 

noncomputable def Ns324p1305 := nat_lit 6977083590399588663294369039711320729050357175755251 

noncomputable def Ns324p1306 := nat_lit 5768503328722446912265483037187355063883923456000 

noncomputable def Ns324p1307 := nat_lit 60892059821788705113275412971520000 

noncomputable def Ns324p1308 := nat_lit 241755181730268626522223219902656020480 

noncomputable abbrev qz771 := (@Eq.refl Real (Enclosure.sfrac Bool.false 661704 1000))

noncomputable abbrev qz689 := qz771

noncomputable abbrev qz507 := qz689

noncomputable abbrev qz206 := qz507

noncomputable def Ns324p1309 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz203 661704 1000 1751409734464 16000000 1323408 4000 2000 Ns324p1307 Ns324p1308 qz206 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns324p1310 := nat_lit 82305027032476939674778758489573800753827957416653303316480 

noncomputable abbrev qz690 := (@HSub.hSub Real Real Real qz727 qz728 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz729 (@Nat.cast Real Real.instNatCast 1323408))))

noncomputable abbrev qz508 := (@HSub.hSub Real Real Real qz586 (@HMul.hMul Real Real Real qz582 (Enclosure.sfrac Bool.false 661704 4000) (Real.log (Enclosure.sfrac Bool.false 1751409734464 16000000))) (@HMul.hMul Real Real Real qz582 qz587 qz690))

noncomputable abbrev qz691 := (Enclosure.sfrac Bool.false 661704 2000)

noncomputable abbrev qz207 := (@HSub.hSub Real Real Real qz354 (@HSub.hSub Real Real Real qz354 qz508 qz691) (@HMul.hMul Real Real Real qz349 qz691 (Real.log Real.pi)))

noncomputable def Ns324p1311 := @Enclosure.Real.IsNear.addLit_ft_p qz207 (Enclosure.sfrac Bool.true Ns324p1307 Ns324p1308) 340447900983969558951 281474976710656000 573310017157116957 61952000000000000000000 Ns324p1307 Ns324p1308 0 1 Ns324p1310 

noncomputable def Ns324p1312 := nat_lit 2855883985777334913972830208000 

noncomputable abbrev qz208 := (@HSub.hSub Real Real Real qz354 qz508 qz691)

noncomputable def Ns324p1313 := @Enclosure.Real.IsNear.subLit_ff_p qz208 (@HMul.hMul Real Real Real qz5 qz691 (Real.log Real.pi)) 447052655917589705127 281474976710656000 523206570279861 121000000000000000000 3177069274593 8388608000 82713 16777216000 Ns324p1312 340447900983969558951 281474976710656000 

noncomputable abbrev qz209 := qz508

noncomputable def Ns324p1314 := @Enclosure.Real.IsNear.subLit_ff_p qz209 qz691 540179214912263664039 281474976710656000 523206570279861 121000000000000000000 661704 2000 0 1 894105311835179410254000 447052655917589705127 281474976710656000 523206570279861 121000000000000000000 

noncomputable def Ns324p1315 := nat_lit 608187727748039428374956937981198336 

noncomputable def Ns324p1316 := nat_lit 56110323110461537702117376 

noncomputable def Ns324p1317 := nat_lit 31378896745949358327483306214205404823301311736635185401796575786902435248917457120212102281041653161639393648914974551915676154712936370385156276444200960 

noncomputable def Ns324p1318 := nat_lit 685131148947226282644765067336057811760064577818484382139013379851129620551528301879928383789293052363314741041644913377160254372876038711832972741312512 

noncomputable def Ns324p1319 := nat_lit 151027375567346622405275585775754056645988348172518431955054508944421117227363727070942219776708048205527778546563914913755249698330689341929553920 

noncomputable def Ns324p1320 := BSN.log_dyadic_bound 702833734464 2799985734464 7 6 Ns324p1317 134217728 38720000 Ns324p1318 Ns324p1319 68852080 3502819468928 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 702833734464) (BSN.artanhQ 2799985734464) 0 6 Ns324p1318 Ns324p1317 Ns324p1319 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz509 := (Real.log (Enclosure.sfrac Bool.false 1751409734464 16000000))

noncomputable def Ns324p1321 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 661704 4000) qz509 661704 4000 0 1 3266050661358839 281474976710656 195312621 7562500000000000 270144848352973650207 140737488355328000 16154892820773 3781250000000000000 (Enclosure.Real.IsNear.const Bool.false 661704 4000) (BSN.isNear_log_sfrac 1751409734464 16000000 3266050661358839 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1751409734464) qz357)) Bool.false Ns324p1316 Ns324p98 1000000619520000 38720000000000000000000 3266050661358839 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1751409734464 16000000 16 3502819468928 2097152000000 68852080 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns324p1320 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns324p1322 := BSN.arctan_dyadic_bound_f 1000 1323408 1 0 16777216 4840000 0 1 1 0 1 1 12677 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1323408) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1323408) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns324p1323 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1323408))) 884279719003555 562949953421312 1 2000000000000000 12677 16777216 1 4840000 14828615333582425030656 883854349469091 562949953421312 50000000121 242000000000000000 qz15 (Ns324p1322 rfl) rfl rfl 

noncomputable abbrev qz510 := (@HMul.hMul Real Real Real qz582 qz587 qz690)

noncomputable abbrev qz210 := qz510

noncomputable abbrev qz511 := qz690

noncomputable abbrev qz211 := qz511

noncomputable def Ns324p1324 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 661704 4000) qz509) qz210 270144848352973650207 140737488355328000 16154892820773 3781250000000000000 883854349469091 2251799813685248 50000000121 968000000000000000 Ns324p1315 540179214912263664039 281474976710656000 523206570279861 121000000000000000000 (Ns324p1321 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz211 1 4 0 1 883854349469091 562949953421312 50000000121 242000000000000000 883854349469091 2251799813685248 50000000121 968000000000000000 qz365 Ns324p1323 rfl) 

noncomputable def Ns324p1325 := @Ns324p1311 Ns324p1305 Ns324p1306 573310017157116957 61952000000000000000000 (@Ns324p1313 573310017157116957 61952000000000000000000 (Ns324p1314 (Ns324p1324 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 661704 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz691 (Real.log Real.pi) 661704 2000 0 1 38410761 33554432 1 67108864 3177069274593 8388608000 82713 16777216000 (Enclosure.Real.IsNear.const Bool.false 661704 2000) RS325to336.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns324p1307 Ns324p1308) 

noncomputable def Ns324p1326 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz203) Bool.false Ns324p1305 Ns324p1306 573310017157116957 61952000000000000000000 40584543953 33554432 39 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz203) (@HAdd.hAdd Real Real Real qz366 qz207 (Enclosure.sfrac Bool.true Ns324p1307 Ns324p1308)) Bool.false Ns324p1305 Ns324p1306 573310017157116957 61952000000000000000000 Ns324p1309 (Ns324p1325 rfl rfl)) 

noncomputable def Ns324p1327 := nat_lit 7598280306745625727205376 

noncomputable def Ns324p1328 := nat_lit 3515237965836153645579383557058904630747471134535386790130213146301698305666845981022944572100647233715209713611523794439605062512647602176 

noncomputable def Ns324p1329 := nat_lit 2512037540699310470201635243182420834362806912303159483880112636830263667719885179977395278301174069569322497043883933694246126616576 

noncomputable def Ns324p1330 := nat_lit 17554321954519543489152062295798452533782288487959982307195689626151393540905581150488200564121747432183079612415643352697242028035786407936 

noncomputable def Ns324p1331 := BSN.sin_dyadic_bound_f 107978057524 68719476736 4 3 33554432 9689454 Ns324p1328 Ns324p110 Ns324p1329 Ns324p1330 Ns324p113 Ns324p1329 33554427 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107978057524) qz593 0 3 Ns324p1328 Ns324p110 Ns324p1329 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107978057524) qz594 0 3 Ns324p1330 Ns324p113 Ns324p1329 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1332 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz203) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40584543953) qz391) Bool.false 40584543953 33554432 39 4194304 Bool.true 33554427 33554432 1 4840000 (Ns324p1326 rfl) (Enclosure.sfrac_false_div 40584543953 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40584543953) qz391) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns324p1327) qz409) 226375608064910080 72057594037927936 Bool.false 33554427 33554432 192 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q1 40584543953 33554432 226375608064910080 72057594037927936 192 Ns324p1327 Ns324p98 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554427 33554432 Ns324p1327 Ns324p98 107978057524 68719476736 9689454 9680000 (Ns324p1331 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns324p1333 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz203) Bool.false Ns324p1305 Ns324p1306 573310017157116957 61952000000000000000000 324676351630 268435456 2485 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz203) (@HAdd.hAdd Real Real Real qz366 qz207 (Enclosure.sfrac Bool.true Ns324p1307 Ns324p1308)) Bool.false Ns324p1305 Ns324p1306 573310017157116957 61952000000000000000000 Ns324p1309 (Ns324p1325 rfl rfl)) 

noncomputable def Ns324p1334 := Ns324p1304 53369 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 478 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268406077 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 307 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 85222934 268435456) qz206 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz203) qz203 1) Bool.true 33554427 33554432 3014911 317194240000 268435416 268435456 2552 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz203) qz203 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz203)) Bool.true 33554427 33554432 3014911 317194240000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz203) qz203) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz203)) Bool.true 33554427 33554432 192954304 20300431360000 33554427 33554432 3014911 317194240000 (Ns324p1332 rfl rfl) rfl)) rfl) (Ns324p1333 rfl) RS325to336.d7 

noncomputable def Ns324p1335 := nat_lit 248773588230004788412600576 

noncomputable def Ns324p1336 := BSN.cos_dyadic_bound_f 3971468 268435456 2 1 268435456 134217728 Ns324p1335 Ns324p149 Ns324p1335 Ns324p1335 Ns324p150 Ns324p1335 268406077 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 3971468) qz369 0 1 Ns324p1335 Ns324p149 Ns324p1335 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 3971468) qz370 0 1 Ns324p1335 Ns324p150 Ns324p1335 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1337 := nat_lit 56565469221263912191730128810000 

noncomputable def Ns324p1338 := BSN.sin_dyadic_bound_f 86723710 268435456 2 1 268435456 134217728 Ns324p1337 Ns324p270 Ns324p1337 Ns324p1337 Ns324p271 Ns324p1337 85222934 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 86723710) qz367 0 1 Ns324p1337 Ns324p270 Ns324p1337 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 86723710) qz368 0 1 Ns324p1337 Ns324p271 Ns324p1337 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1339 := nat_lit 3702426316750093480030800625 

noncomputable def Ns324p1340 := BSN.cos_dyadic_bound_f 7800485 268435456 2 1 268435456 134217728 Ns324p1339 Ns324p149 Ns324p1339 Ns324p1339 Ns324p150 Ns324p1339 268322126 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 7800485) qz369 0 1 Ns324p1339 Ns324p149 Ns324p1339 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 7800485) qz370 0 1 Ns324p1339 Ns324p150 Ns324p1339 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1341 := nat_lit 3630015082422050668838520336 

noncomputable def Ns324p1342 := BSN.cos_dyadic_bound_f 7762062 268435456 2 1 268435456 134217728 Ns324p1341 Ns324p149 Ns324p1341 Ns324p1341 Ns324p150 Ns324p1341 268323240 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 7762062) qz369 0 1 Ns324p1341 Ns324p149 Ns324p1341 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 7762062) qz370 0 1 Ns324p1341 Ns324p150 Ns324p1341 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1343 := Ns324p1302 90851 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 186 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268322126 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 92 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268323240 268435456) qz206 rfl rfl (Ns324p1334 RS325to336.d9 RS325to336.d11 RS325to336.d13 RS325to336.d17 (Ns324p1336 rfl rfl) (Ns324p1338 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns324p1333 rfl) RS325to336.d19 RS325to336.d21 RS325to336.d23 RS325to336.d25 RS325to336.d17 (Ns324p1340 rfl rfl) (Ns324p1342 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns324p1344 := nat_lit 67240589932294941797817006250000 

noncomputable def Ns324p1345 := BSN.sin_dyadic_bound_f 90554050 268435456 2 1 268435456 134217728 Ns324p1344 Ns324p270 Ns324p1344 Ns324p1344 Ns324p271 Ns324p1344 88846312 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 90554050) qz367 0 1 Ns324p1344 Ns324p270 Ns324p1344 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 90554050) qz368 0 1 Ns324p1344 Ns324p271 Ns324p1344 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1346 := nat_lit 134801212112735027761478508313372599178203645869710329601044265965530625 

noncomputable def Ns324p1347 := nat_lit 73625872735155609868611993476791067989546545915334993081138812890625 

noncomputable def Ns324p1348 := nat_lit 352931589834639582673608816640822955166169330489187939918698852784090625 

noncomputable def Ns324p1349 := BSN.sin_dyadic_bound_f 304353855 268435456 3 2 268435456 134217728 Ns324p1346 Ns324p249 Ns324p1347 Ns324p1348 Ns324p252 Ns324p1347 243210494 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 304353855) qz367 0 2 Ns324p1346 Ns324p249 Ns324p1347 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 304353855) qz368 0 2 Ns324p1348 Ns324p252 Ns324p1347 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1350 := Ns324p1300 122478 BSN.abs_quadSignPos (BSN.cos_quad_nat3 15 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 88846312 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 243210494 268435456) qz206 rfl rfl (Ns324p1343 rfl rfl) (Ns324p1333 rfl) RS325to336.d27 RS325to336.d29 RS325to336.d31 RS325to336.d33 RS325to336.d17 (Ns324p1345 rfl rfl) (Ns324p1349 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p1351 := nat_lit 39617996252090892499232253422288897222403103072298210330715346312525591321304771807286282428078251291254301521 

noncomputable def Ns324p1352 := nat_lit 22588061979831353109578907877876887741701140165390023033717836166431704846826531338575794783215545066321 

noncomputable def Ns324p1353 := nat_lit 197869826904359978987449918097760418587558331406725167825638045407982697510686250062775811560613381210457875281 

noncomputable def Ns324p1354 := BSN.sin_dyadic_bound_f 410037189 268435456 4 3 268435456 134217728 Ns324p1351 Ns324p119 Ns324p1352 Ns324p1353 Ns324p122 Ns324p1352 268183982 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 410037189) qz367 0 3 Ns324p1351 Ns324p119 Ns324p1352 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 410037189) qz368 0 3 Ns324p1353 Ns324p122 Ns324p1352 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1355 := nat_lit 59746313613690869443165692903325741567056403187139433320471390710661120 

noncomputable def Ns324p1356 := nat_lit 14472021764089298722887072607996719766212713371510978500820526432256 

noncomputable def Ns324p1357 := nat_lit 156455009524429465867501664248297328462669092525620831397947551961317376 

noncomputable def Ns324p1358 := BSN.sin_dyadic_bound_f 248351136 268435456 3 2 268435456 134217728 Ns324p1355 Ns324p249 Ns324p1356 Ns324p1357 Ns324p252 Ns324p1356 214407217 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 248351136) qz367 0 2 Ns324p1355 Ns324p249 Ns324p1356 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 248351136) qz368 0 2 Ns324p1357 Ns324p252 Ns324p1356 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1359 := Ns324p1298 149657 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 105 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268183982 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 155 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 214407217 268435456) qz206 rfl rfl (Ns324p1350 rfl) (Ns324p1333 rfl) RS325to336.d35 RS325to336.d37 RS325to336.d39 RS325to336.d41 RS325to336.d17 (Ns324p1354 rfl rfl) (Ns324p1358 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p1360 := nat_lit 39628774812863883935064414307083141852980413364128907781631300639182269493247589142239246258016244517212890625 

noncomputable def Ns324p1361 := nat_lit 22606469952403129969201069680172416354737303453182061370613911548105247968752851664495527744293212890625 

noncomputable def Ns324p1362 := nat_lit 197923600091147579602321960797878502321699428905484423131397855819573385609540626406374143573570245413212890625 

noncomputable def Ns324p1363 := BSN.sin_dyadic_bound_f 410065025 268435456 4 3 268435456 134217728 Ns324p1360 Ns324p119 Ns324p1361 Ns324p1362 Ns324p122 Ns324p1361 268185185 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 410065025) qz367 0 3 Ns324p1360 Ns324p119 Ns324p1361 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 410065025) qz368 0 3 Ns324p1362 Ns324p122 Ns324p1361 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1364 := Ns324p1296 Bool.true 502188794 149657 Bool.true 410065025 14148475504056880 1 Bool.false 268185185 Bool.false Bool.true 417381193 162171 BSN.abs_quadSignPos (BSN.cos_quad_nat3 199 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268185185 268435456) qz206 rfl (Ns324p1359 rfl) (Ns324p1333 rfl) RS325to336.d43 RS325to336.d45 RS325to336.d17 (Ns324p1363 rfl rfl) rfl 

noncomputable def Ns324p1365 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz203) qz203 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz203) qz203 10) 417381193 268435456 162171 268435456 417381193 268435456 162171 268435456 224079821737558016 417381193 134217728 162171 134217728 (Ns324p1364 rfl rfl rfl rfl) 

noncomputable def Ns324p1366 := @Enclosure.Real.IsNear.mulLit_ff qz688 (Zeta.RiemannSiegel.correction qz205) 10474395 33554432 1 33554432 68698467642623 140737488355328 7085940033167163 42573090227486720000 719574885983552138085 4722366482869645213696 

noncomputable abbrev qz692 := (@HPow.hPow Real Real Real qz133 qz204 qz135)

noncomputable def Ns324p1367 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz692 1 1 0 1 10474395 33554432 1 33554432 10474395 33554432 1 33554432 

noncomputable def Ns324p1368 := @Enclosure.Real.IsNear.sqrt_image qz204 441716617689 4194304000 82713 4194304000 172171701 172171734 16777216 (@Enclosure.Real.IsNear.of_eq qz204 (@HMul.hMul Real Real Real qz5 qz203 qz3) Bool.false 441716617689 4194304000 82713 4194304000 (BSN.t_div_two_pi_mk qz203 661704 1000 qz206) (@Enclosure.Real.IsNear.mulLit_ff qz203 qz3 661704 1000 0 1 5340353 33554432 1 33554432 441716617689 4194304000 82713 4194304000 (Enclosure.Real.IsNear.const Bool.false 661704 1000) RS325to336.d48 rfl)) 

noncomputable abbrev qz772 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 661704 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz693 := qz772

noncomputable abbrev qz512 := qz693

noncomputable abbrev qz212 := qz512

noncomputable def Ns324p1369 := @Enclosure.Real.IsNear.sqrt_image qz212 344343435 33554432 33 33554432 53745342 53745348 16777216 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 344343435 33554432 33 33554432 344343435 33554432 33 33554432 (Ns324p1368 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns324p1370 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz212) 53745345 16777216 3 16777216 5237197 5237198 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz212) Bool.false 107490690 33554432 6 33554432 53745345 16777216 3 16777216 (Ns324p1369 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns324p1371 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz212)) Bool.false 10474395 33554432 1 33554432 10474395 33554432 1 33554432 (Ns324p1370 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz513 := (@HMul.hMul Real Real Real qz582 qz580 qz687)

noncomputable abbrev qz213 := (Real.cos qz513)

noncomputable abbrev qz694 := (@HMul.hMul Real Real Real qz723 qz770 qz770)

noncomputable abbrev qz514 := (@HSub.hSub Real Real Real qz586 (@HSub.hSub Real Real Real qz586 qz694 qz687) qz600)

noncomputable abbrev qz214 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz514))

noncomputable def Ns324p1372 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz205) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz213) qz214) Bool.false 68698467642623 

noncomputable def Ns324p1373 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz213) qz214 218472527 16777216 1139 

noncomputable abbrev qz215 := (@Neg.neg Real Real.instNeg (Real.cos qz513))

noncomputable def Ns324p1374 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz213) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz215)) Bool.true 218472527 16777216 1139 1048576 (BSN.inv_eq_neg_inv_neg qz213) 

noncomputable def Ns324p1375 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz215) Bool.false 436945054 33554432 36448 33554432 218472527 16777216 

noncomputable def Ns324p1376 := @Enclosure.Real.IsNear.recentre' qz213 Bool.true 1288377 16777216 65017152 10150215680000 1288377 16777216 1015893 158597120000 

noncomputable abbrev qz216 := qz513

noncomputable def Ns324p1377 := @Enclosure.Real.IsNear.cos_image qz216 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 27643235) qz374) Bool.false 27643235 16777216 13 2097152 Bool.true 1288377 16777216 1 

noncomputable def Ns324p1378 := nat_lit 890540488574037322338061991 

noncomputable def Ns324p1379 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz205 884279719003555 140737488355328 1 500000000000000 8799115 33554432 33 33554432 7780878939679965853825 4722366482869645213696 Ns324p1378 

noncomputable def Ns324p1380 := @Enclosure.Real.IsNear.subLit_ff_p qz212 qz1 344343435 33554432 33 33554432 10 1 0 1 8799115 8799115 33554432 33 

noncomputable def Ns324p1381 := @Ns324p1380 33554432 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 344343435 33554432 33 33554432 344343435 33554432 33 33554432 (Ns324p1368 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns324p1382 := @Enclosure.Real.IsNear.recentre' qz216 Bool.false 7780878939679965853825 4722366482869645213696 Ns324p1378 Ns324p173 27643235 16777216 13 2097152 (@Ns324p1379 Ns324p173 RS325to336.d47 (Ns324p1381 rfl rfl) rfl) 

noncomputable def Ns324p1383 := nat_lit 73475509820988900115383532076886685009529233146221695522014322660360001431678562348912780640625 

noncomputable def Ns324p1384 := nat_lit 199097767082151963105072504927377136025457942425488820880760385231162448704005820556640625 

noncomputable def Ns324p1385 := nat_lit 444452443988206042475643925368126147436560361634264199146832803559295333004459858296236582240625 

noncomputable def Ns324p1386 := BSN.cos_dyadic_bound_t 27643235 16777216 4 3 16777216 4840000 Ns324p1383 Ns324p825 Ns324p1384 Ns324p1385 Ns324p828 Ns324p1384 1288377 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 27643235) qz601 0 3 Ns324p1383 Ns324p825 Ns324p1384 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 27643235) (BSN.cosOddQ 16777216) 0 3 Ns324p1385 Ns324p828 Ns324p1384 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1387 := @Enclosure.Real.IsNear.inv_image qz215 1288377 16777216 1015893 158597120000 218454303 218490751 16777216 (@Enclosure.Real.IsNear.neg qz213 Bool.true 1288377 16777216 1015893 158597120000 (Ns324p1376 (@Ns324p1377 4840000 (Ns324p1382 rfl) (Enclosure.sfrac_false_div 27643235 16777216) (Ns324p1386 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns324p1388 := Ns324p1374 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz215) Bool.false 218472527 16777216 1139 1048576 (@Ns324p1375 1139 1048576 (Ns324p1387 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns324p1389 := @Enclosure.Real.IsNear.recentre' qz214 Bool.true 628898 16777216 

noncomputable abbrev qz217 := (@HMul.hMul Real Real Real qz349 qz346 qz514)

noncomputable def Ns324p1390 := @Enclosure.Real.IsNear.cos_image qz217 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 53965269)) qz391) Bool.true 53965269 33554432 

noncomputable def Ns324p1391 := nat_lit 254843778018459202142581133045 

noncomputable def Ns324p1392 := nat_lit 45553545995787964249583370440570593 

noncomputable def Ns324p1393 := @Enclosure.Real.IsNear.recentre' qz217 Bool.true Ns324p1391 Ns324p188 Ns324p1392 

noncomputable abbrev qz218 := qz514

noncomputable def Ns324p1394 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz218 884279719003555 140737488355328 1 500000000000000 288193625322119 

noncomputable abbrev qz515 := (@HSub.hSub Real Real Real qz586 qz694 qz687)

noncomputable abbrev qz219 := qz515

noncomputable def Ns324p1395 := @Enclosure.Real.IsNear.subLit_tf qz219 qz29 217824881144455 1125899906842624 1688038935 1125899906842624 1 16 

noncomputable abbrev qz516 := qz694

noncomputable abbrev qz220 := qz516

noncomputable def Ns324p1396 := @Enclosure.Real.IsNear.subLit_ff_n qz220 qz205 77424424783225 1125899906842624 580742679 1125899906842624 8799115 33554432 33 33554432 

noncomputable def Ns324p1397 := @Enclosure.Real.IsNear.mulLit_ff qz205 qz205 8799115 33554432 33 33554432 8799115 33554432 33 33554432 77424424783225 1125899906842624 

noncomputable def Ns324p1398 := nat_lit 273092217771331444167822726731257935592822737476426057265978050711881106256254024422158710440186641 

noncomputable def Ns324p1399 := nat_lit 610059444142601511830387220660597674175695311407787257976774764964904313726881345934054118161 

noncomputable def Ns324p1400 := nat_lit 1652375198092877006085373723637545141435760587777633943693896171686204440786480068928325382001644305 

noncomputable def Ns324p1401 := BSN.cos_dyadic_bound_t 53965269 33554432 4 3 16777216 4840000 Ns324p1398 Ns324p594 Ns324p1399 Ns324p1400 Ns324p597 Ns324p1399 628898 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 53965269) qz392 0 3 Ns324p1398 Ns324p594 Ns324p1399 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 53965269) (BSN.cosOddQ 33554432) 0 3 Ns324p1400 Ns324p597 Ns324p1399 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1402 := @Ns324p1389 1567834432 162403450880000 314449 8388608 24497413 2537553920000 (@Ns324p1390 317 33554432 Bool.true 628898 16777216 1 4840000 (@Ns324p1393 Ns324p191 53965269 33554432 317 33554432 (@Ns324p1394 1125899906842624 1688038935 1125899906842624 Ns324p1391 Ns324p188 Ns324p1392 Ns324p191 RS325to336.d47 (@Ns324p1395 0 1 4611098005153904 288193625322119 1125899906842624 1688038935 1125899906842624 (@Ns324p1396 7308990162269697474560 217824881144455 1125899906842624 1688038935 1125899906842624 (@Ns324p1397 580742679 1125899906842624 (Ns324p1381 rfl rfl) (Ns324p1381 rfl rfl) rfl) (Ns324p1381 rfl rfl) rfl rfl) qz379 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 53965269 33554432) (BSN.cos_neg_of_bound 53965269 33554432 Bool.true 628898 16777216 1 4840000 (Ns324p1401 rfl rfl)) rfl rfl) 

noncomputable def Ns324p1403 := @Ns324p1366 4640107701631743307253 Ns324p363 (Ns324p1367 qz31 (@Enclosure.Real.IsNear.of_eq qz692 (@Inv.inv Real Real.instInv (Real.sqrt qz212)) Bool.false 10474395 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz204 (BSN.t_div_two_pi_nonneg qz203 661704 1000 qz206)) Ns324p1371) rfl) (@Ns324p1372 140737488355328 7085940033167163 42573090227486720000 (BSN.correction_mk qz205 (BSN.cos_two_pi_p_ne_zero_mk qz203 661704 1000 10 qz206 rfl rfl (@BSN.floor_sqrt_eq_dec qz203 661704 1000 10 qz206 rfl rfl rfl))) (@Ns324p1373 1048576 314449 8388608 24497413 2537553920000 68698467642623 140737488355328 7085940033167163 42573090227486720000 Ns324p1388 (Ns324p1402 rfl) rfl)) 

noncomputable def Ns324p1404 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz203) (hardyZApproximantRS₀ qz203) Bool.true 15404870083376154274661 4722366482869645213696 112516992315409069387253 Ns324p363 (@Eq.refl Real (hardyZApproximantRS₀ qz203)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz203) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz203) qz203 10) (@HMul.hMul Real Real Real qz5 qz688 (Zeta.RiemannSiegel.correction qz205))) Bool.true 15404870083376154274661 4722366482869645213696 112516992315409069387253 Ns324p363 (BSN.hardyZApproximantRS₀_eq qz203 10 (@BSN.floor_sqrt_eq_dec qz203 661704 1000 10 qz206 rfl rfl rfl)) (@Ns324p1295 15404870083376154274661 4722366482869645213696 112516992315409069387253 Ns324p363 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz203) qz203 10) (@HAdd.hAdd Real Real Real qz366 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz203) qz203 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz203) qz203 10)) Bool.true 417381193 134217728 162171 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz203) qz203 10) (Ns324p1365 (Ns324p1364 rfl rfl rfl rfl) rfl rfl)) (Ns324p1403 rfl) rfl rfl)) 

theorem RS325to336.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz203) Bool.true 15404870083376154274661 4722366482869645213696 112516992315409069387253 Ns324p363 := Ns324p1404 

noncomputable def Ns324p1405 := nat_lit 742352858229417091099476885504 

noncomputable abbrev qz773 := (Enclosure.sfrac Bool.false 663053 1000)

noncomputable abbrev qz695 := qz773

noncomputable abbrev qz517 := qz695

noncomputable abbrev qz221 := qz517

noncomputable abbrev qz774 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 663053 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz696 := qz774

noncomputable abbrev qz518 := qz696

noncomputable abbrev qz222 := qz518

noncomputable abbrev qz775 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 663053 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz697 := qz775

noncomputable abbrev qz519 := qz697

noncomputable abbrev qz223 := qz519

noncomputable abbrev qz698 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz133 qz222 qz135))

noncomputable def Ns324p1406 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz221) qz221 10) (@HMul.hMul Real Real Real qz5 qz698 (Zeta.RiemannSiegel.correction qz223)) 648837699 134217728 81249 67108864 176276955124354274949 1180591620717411303424 2524389491339871082467 Ns324p363 Ns324p1405 

noncomputable def Ns324p1407 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz221) qz221 Real.sin BSN.quadSignPos 9 10 663053 1000 199 268435456 134217728 4503599627370496 Bool.false 325519720338 2490 618095470 56 84886744 8 

noncomputable def Ns324p1408 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz221) qz221 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 663053 1000 105 155 268435456 134217728 4503599627370496 Bool.false 325519720338 2490 

noncomputable def Ns324p1409 := Ns324p1408 558195838 56 94906264 8 589812974 56 89478488 8 Bool.false 591528997 122723 Bool.true 319674667 Bool.true 200640130 14148475504056880 1 Bool.false 249294937 Bool.true Bool.false 182473137 Bool.false Bool.false 564214309 

noncomputable def Ns324p1410 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz221) qz221 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 663053 1000 15 49 268435456 134217728 4503599627370496 Bool.false 325519720338 2490 

noncomputable def Ns324p1411 := Ns324p1410 480971758 57 109588312 8 522351262 57 101459064 8 Bool.false 554526501 91031 Bool.false 285091856 Bool.true 165636999 14148475504056880 1 Bool.false 234439662 Bool.false Bool.false 155324366 Bool.true Bool.false 591528997 

noncomputable def Ns324p1412 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz221) qz221 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 663053 1000 186 92 268435456 134217728 4503599627370496 Bool.false 325519720338 2490 

noncomputable def Ns324p1413 := Ns324p1412 372130544 56 134217720 8 432030192 56 120047984 16 Bool.false 525428825 53473 Bool.false 349165089 Bool.false 268322041 14148475504056880 1 Bool.false 71614405 Bool.true Bool.false 145131718 Bool.false Bool.false 554526501 

noncomputable def Ns324p1414 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz221) qz221 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 663053 1000 479 308 268435456 134217728 4503599627370496 Bool.false 325519720338 2490 

noncomputable def Ns324p1415 := Ns324p1414 186065264 56 189812528 16 294906480 56 154981288 8 Bool.false 268435384 2552 Bool.false 174680707 Bool.false 110606148 14148475504056880 1 Bool.false 162610799 Bool.false Bool.false 245968951 Bool.false Bool.false 525428825 

noncomputable def Ns324p1416 := nat_lit 1044166906997541079225388487918487519043043494702336863103 

noncomputable def Ns324p1417 := nat_lit 861058185747581992213561760278078983777023598526464000 

noncomputable def Ns324p1418 := nat_lit 61515291295621669887159109036640000 

noncomputable def Ns324p1419 := nat_lit 244727455579886166166705197690043571520 

noncomputable abbrev qz776 := (@Eq.refl Real (Enclosure.sfrac Bool.false 663053 1000))

noncomputable abbrev qz699 := qz776

noncomputable abbrev qz520 := qz699

noncomputable abbrev qz224 := qz520

noncomputable def Ns324p1420 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz221 663053 1000 1758558123236 16000000 1326106 4000 2000 Ns324p1418 Ns324p1419 qz224 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns324p1421 := nat_lit 334133410239213145352124316133916006093773918304747796192960 

noncomputable abbrev qz700 := (@HSub.hSub Real Real Real qz727 qz728 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz729 (@Nat.cast Real Real.instNatCast 1326106))))

noncomputable abbrev qz521 := (@HSub.hSub Real Real Real qz586 (@HMul.hMul Real Real Real qz582 (Enclosure.sfrac Bool.false 663053 4000) (Real.log (Enclosure.sfrac Bool.false 1758558123236 16000000))) (@HMul.hMul Real Real Real qz582 qz587 qz700))

noncomputable abbrev qz701 := (Enclosure.sfrac Bool.false 663053 2000)

noncomputable abbrev qz225 := (@HSub.hSub Real Real Real qz354 (@HSub.hSub Real Real Real qz354 qz521 qz701) (@HMul.hMul Real Real Real qz349 qz701 (Real.log Real.pi)))

noncomputable def Ns324p1422 := @Enclosure.Real.IsNear.addLit_ft_p qz225 (Enclosure.sfrac Bool.true Ns324p1418 Ns324p1419) 1365328948104896997423 1125899906842624000 4595778293691045217 495616000000000000000000 Ns324p1418 Ns324p1419 0 1 Ns324p1421 

noncomputable def Ns324p1423 := nat_lit 91625674693634590334068457472000 

noncomputable abbrev qz226 := (@HSub.hSub Real Real Real qz354 qz521 qz701)

noncomputable def Ns324p1424 := @Enclosure.Real.IsNear.subLit_ff_p qz226 (@HMul.hMul Real Real Real qz5 qz701 (Real.log Real.pi)) 1792617298019672418351 1125899906842624000 524260477182777 121000000000000000000 25468370313333 67108864000 663053 134217728000 Ns324p1423 1365328948104896997423 1125899906842624000 

noncomputable def Ns324p1425 := nat_lit 3585234596039344836702000 

noncomputable abbrev qz227 := qz521

noncomputable def Ns324p1426 := @Enclosure.Real.IsNear.subLit_ff_p qz227 qz701 2165882953485533603887 1125899906842624000 524260477182777 121000000000000000000 663053 2000 0 1 Ns324p1425 1792617298019672418351 1125899906842624000 524260477182777 121000000000000000000 

noncomputable def Ns324p1427 := nat_lit 4877134831122779229548017604127358976 

noncomputable def Ns324p1428 := nat_lit 56130019873647820208603136 

noncomputable def Ns324p1429 := nat_lit 32353838074332739363593821540913128746605813755558680794838409881940210046837988814418801272840583563956643079494238839478334070056308836555492722433064960 

noncomputable def Ns324p1430 := nat_lit 717631038899837938881310516505525163271452321012466308022629701223054411609512246569807060126921115838207293365529674266712556077048356676109046028173312 

noncomputable def Ns324p1431 := nat_lit 170527120166885842464244960417043464530522881028114567260492644195041336308684775479117444099855972467959087754229822401253420299217579401984081920 

noncomputable def Ns324p1432 := BSN.log_dyadic_bound 709982123236 2807134123236 7 6 Ns324p1429 134217728 38720000 Ns324p1430 Ns324p1431 69398775 3517116246472 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 709982123236) (BSN.artanhQ 2807134123236) 0 6 Ns324p1430 Ns324p1429 Ns324p1431 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz522 := (Real.log (Enclosure.sfrac Bool.false 1758558123236 16000000))

noncomputable def Ns324p1433 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 663053 4000) qz522 663053 4000 0 1 3267197163871479 281474976710656 195312621 7562500000000000 2166324881096475765387 1125899906842624000 129502619291913 30250000000000000000 (Enclosure.Real.IsNear.const Bool.false 663053 4000) (BSN.isNear_log_sfrac 1758558123236 16000000 3267197163871479 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1758558123236) qz357)) Bool.false Ns324p1428 Ns324p98 1000000619520000 38720000000000000000000 3267197163871479 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1758558123236 16000000 16 3517116246472 2097152000000 69398775 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns324p1432 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns324p1434 := BSN.arctan_dyadic_bound_f 1000 1326106 1 0 16777216 4840000 0 1 1 0 1 1 12651 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1326106) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1326106) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns324p1435 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1326106))) 884279719003555 562949953421312 1 2000000000000000 12651 16777216 1 4840000 14828629970281213984768 883855221884323 562949953421312 50000000121 242000000000000000 qz15 (Ns324p1434 rfl) rfl rfl 

noncomputable abbrev qz523 := (@HMul.hMul Real Real Real qz582 qz587 qz700)

noncomputable abbrev qz228 := qz523

noncomputable abbrev qz524 := qz700

noncomputable abbrev qz229 := qz524

noncomputable def Ns324p1436 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 663053 4000) qz522) qz228 2166324881096475765387 1125899906842624000 129502619291913 30250000000000000000 883855221884323 2251799813685248 50000000121 968000000000000000 Ns324p1427 2165882953485533603887 1125899906842624000 524260477182777 121000000000000000000 (Ns324p1433 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz229 1 4 0 1 883855221884323 562949953421312 50000000121 242000000000000000 883855221884323 2251799813685248 50000000121 968000000000000000 qz365 Ns324p1435 rfl) 

noncomputable def Ns324p1437 := @Ns324p1422 Ns324p1416 Ns324p1417 4595778293691045217 495616000000000000000000 (@Ns324p1424 4595778293691045217 495616000000000000000000 (Ns324p1426 (Ns324p1436 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 663053 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz701 (Real.log Real.pi) 663053 2000 0 1 38410761 33554432 1 67108864 25468370313333 67108864000 663053 134217728000 (Enclosure.Real.IsNear.const Bool.false 663053 2000) RS325to336.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns324p1418 Ns324p1419) 

noncomputable def Ns324p1438 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz221) Bool.false Ns324p1416 Ns324p1417 4595778293691045217 495616000000000000000000 20344982521 16777216 39 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz221) (@HAdd.hAdd Real Real Real qz366 qz225 (Enclosure.sfrac Bool.true Ns324p1418 Ns324p1419)) Bool.false Ns324p1416 Ns324p1417 4595778293691045217 495616000000000000000000 Ns324p1420 (Ns324p1437 rfl rfl)) 

noncomputable def Ns324p1439 := BSN.cos_dyadic_bound_f 47542888 68719476736 1 0 33554432 9689454 0 1 1 0 1 1 33554423 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 47542888) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 47542888) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns324p1440 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz221) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20344982521) qz374) Bool.false 20344982521 16777216 39 4194304 Bool.false 33554423 33554432 1 4840000 (Ns324p1438 rfl) (Enclosure.sfrac_false_div 20344982521 16777216) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20344982521) qz374) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1672766662067882033152) qz626) 226375608064910080 72057594037927936 Bool.false 33554423 33554432 193 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q0 20344982521 16777216 226375608064910080 72057594037927936 193 1672766662067882033152 Ns324p518 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554423 33554432 1672766662067882033152 Ns324p518 47542888 68719476736 9689454 9680000 (Ns324p1439 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns324p1441 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz221) Bool.false Ns324p1416 Ns324p1417 4595778293691045217 495616000000000000000000 325519720338 268435456 2490 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz221) (@HAdd.hAdd Real Real Real qz366 qz225 (Enclosure.sfrac Bool.true Ns324p1418 Ns324p1419)) Bool.false Ns324p1416 Ns324p1417 4595778293691045217 495616000000000000000000 Ns324p1420 (Ns324p1437 rfl rfl)) 

noncomputable def Ns324p1442 := Ns324p1415 53473 BSN.abs_quadSignPos (BSN.cos_quad_nat3 479 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 162610799 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 308 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 245968951 268435456) qz224 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 1) Bool.false 33554423 33554432 3014911 317194240000 268435384 268435456 2552 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz221)) Bool.false 33554423 33554432 3014911 317194240000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz221) qz221) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz221)) Bool.false 33554423 33554432 192954304 20300431360000 33554423 33554432 3014911 317194240000 (Ns324p1440 rfl rfl) rfl)) rfl) (Ns324p1441 rfl) RS325to336.d7 

noncomputable def Ns324p1443 := nat_lit 14619981301411545607224479904847019342607144743059482839858762236147105 

noncomputable def Ns324p1444 := nat_lit 866881087305410199703374312567305529809944381969408865193491805601 

noncomputable def Ns324p1445 := nat_lit 38289023696222220211931260954283751212160924893299266490038825917461921 

noncomputable def Ns324p1446 := BSN.sin_dyadic_bound_f 174680707 268435456 3 2 268435456 134217728 Ns324p1443 Ns324p249 Ns324p1444 Ns324p1445 Ns324p252 Ns324p1444 162610799 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 174680707) qz367 0 2 Ns324p1443 Ns324p249 Ns324p1444 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 174680707) qz368 0 2 Ns324p1445 Ns324p252 Ns324p1444 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1447 := nat_lit 1305549426297900941225067216190608379032994507523510768919263156699136 

noncomputable def Ns324p1448 := nat_lit 22399284291162746053858357729534089520640012677483199964769222656 

noncomputable def Ns324p1449 := nat_lit 3916603480325120498183093931856366068919942242545177340357859931652096 

noncomputable def Ns324p1450 := BSN.cos_dyadic_bound_f 110606148 268435456 3 2 268435456 134217728 Ns324p1447 Ns324p263 Ns324p1448 Ns324p1449 Ns324p266 Ns324p1448 245968951 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 110606148) qz369 0 2 Ns324p1447 Ns324p263 Ns324p1448 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 110606148) qz370 0 2 Ns324p1449 Ns324p266 Ns324p1448 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1451 := nat_lit 8011384388554940729766256033327005369268862441152188656939009892606867951153096978549914304718872274476732801 

noncomputable def Ns324p1452 := nat_lit 3283747652289226930341385238168322095608457685969700503227017561530413071157841841655856097281090523521 

noncomputable def Ns324p1453 := nat_lit 48547265522438152210113243598729182053117540434039618937634135850629736783374720116037512530776334775090155905 

noncomputable def Ns324p1454 := BSN.cos_dyadic_bound_f 349165089 268435456 4 3 268435456 134217728 Ns324p1451 Ns324p125 Ns324p1452 Ns324p1453 Ns324p128 Ns324p1452 71614405 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 349165089) qz369 0 3 Ns324p1451 Ns324p125 Ns324p1452 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 349165089) qz370 0 3 Ns324p1453 Ns324p128 Ns324p1452 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1455 := nat_lit 2790796458168981397866626163044841772681174247630235018383862682916331045825981158132484900593990838505366561 

noncomputable def Ns324p1456 := nat_lit 139275967807967207592866438010880692179286949509496981417122537051953386363048809970338658891342210081 

noncomputable def Ns324p1457 := nat_lit 16924127887436909136613120344749589993851284047569283902626116721054019112342086818008797815707290499496993825 

noncomputable def Ns324p1458 := BSN.cos_dyadic_bound_f 268322041 268435456 4 3 268435456 134217728 Ns324p1455 Ns324p125 Ns324p1456 Ns324p1457 Ns324p128 Ns324p1456 145131718 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 268322041) qz369 0 3 Ns324p1455 Ns324p125 Ns324p1456 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 268322041) qz370 0 3 Ns324p1457 Ns324p128 Ns324p1456 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1459 := Ns324p1413 91031 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 186 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 71614405 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 92 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 145131718 268435456) qz224 rfl rfl (Ns324p1442 RS325to336.d9 RS325to336.d11 RS325to336.d13 RS325to336.d17 (Ns324p1446 rfl rfl) (Ns324p1450 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns324p1441 rfl) RS325to336.d19 RS325to336.d21 RS325to336.d23 RS325to336.d25 RS325to336.d17 (Ns324p1454 rfl rfl) (Ns324p1458 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns324p1460 := nat_lit 103767947470550596230248183321643651834275012557977637748218255114240000 

noncomputable def Ns324p1461 := nat_lit 43639371846091781149867343728656010915477245151764480591674963132416 

noncomputable def Ns324p1462 := nat_lit 271702541535119793909740694904934597453047593540648099229137480120795136 

noncomputable def Ns324p1463 := BSN.sin_dyadic_bound_f 285091856 268435456 3 2 268435456 134217728 Ns324p1460 Ns324p249 Ns324p1461 Ns324p1462 Ns324p252 Ns324p1461 234439662 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 285091856) qz367 0 2 Ns324p1460 Ns324p249 Ns324p1461 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 285091856) qz368 0 2 Ns324p1462 Ns324p252 Ns324p1461 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1464 := nat_lit 11819293949779896055374475733254305931723232930482107551646984649882305 

noncomputable def Ns324p1465 := nat_lit 566576852009052213597136704883581181765535686072480195472206904001 

noncomputable def Ns324p1466 := nat_lit 30954376363091713108111136318143846880218942045866164333997052414704321 

noncomputable def Ns324p1467 := BSN.sin_dyadic_bound_f 165636999 268435456 3 2 268435456 134217728 Ns324p1464 Ns324p249 Ns324p1465 Ns324p1466 Ns324p252 Ns324p1465 155324366 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 165636999) qz367 0 2 Ns324p1464 Ns324p249 Ns324p1465 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 165636999) qz368 0 2 Ns324p1466 Ns324p252 Ns324p1465 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1468 := Ns324p1411 122723 BSN.abs_quadSignPos (BSN.cos_quad_nat3 15 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 234439662 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 155324366 268435456) qz224 rfl rfl (Ns324p1459 rfl rfl) (Ns324p1441 rfl) RS325to336.d27 RS325to336.d29 RS325to336.d31 RS325to336.d33 RS325to336.d17 (Ns324p1463 rfl rfl) (Ns324p1467 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p1469 := nat_lit 164082756499448218581842546922109481032541310651589390515050795672790625 

noncomputable def Ns324p1470 := nat_lit 109060069876847803682236076166541865478903991430851549305588029843041 

noncomputable def Ns324p1471 := nat_lit 429563979290182818889340193053636144445880445244227025031019227094705761 

noncomputable def Ns324p1472 := BSN.sin_dyadic_bound_f 319674667 268435456 3 2 268435456 134217728 Ns324p1469 Ns324p249 Ns324p1470 Ns324p1471 Ns324p252 Ns324p1470 249294937 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 319674667) qz367 0 2 Ns324p1469 Ns324p249 Ns324p1470 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 319674667) qz368 0 2 Ns324p1471 Ns324p252 Ns324p1470 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1473 := nat_lit 25448215009094846209462836024917648875919369566353961202111919905440000 

noncomputable def Ns324p1474 := nat_lit 2626288332756742265445877115155034175775140552083336843472100000000 

noncomputable def Ns324p1475 := nat_lit 66645834842709657727782420073740734143504236731937953936356073495200000 

noncomputable def Ns324p1476 := BSN.sin_dyadic_bound_f 200640130 268435456 3 2 268435456 134217728 Ns324p1473 Ns324p249 Ns324p1474 Ns324p1475 Ns324p252 Ns324p1474 182473137 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 200640130) qz367 0 2 Ns324p1473 Ns324p249 Ns324p1474 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 200640130) qz368 0 2 Ns324p1475 Ns324p252 Ns324p1474 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1477 := Ns324p1409 149958 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 105 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 249294937 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 155 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 182473137 268435456) qz224 rfl rfl (Ns324p1468 rfl) (Ns324p1441 rfl) RS325to336.d35 RS325to336.d37 RS325to336.d39 RS325to336.d41 RS325to336.d17 (Ns324p1472 rfl rfl) (Ns324p1476 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p1478 := nat_lit 36055398856825809711990173717929120013145954966001160116233410546719728395829404594201496982564424886225473536 

noncomputable def Ns324p1479 := nat_lit 17034238026765579399359971331205967691898541247739635517571932145201405316732263178363781902257064513536 

noncomputable def Ns324p1480 := nat_lit 180094601728533389350439047546369177083244164081588847387984299012291537685743768411824696373548497031430148096 

noncomputable def Ns324p1481 := BSN.sin_dyadic_bound_f 400507106 268435456 4 3 268435456 134217728 Ns324p1478 Ns324p119 Ns324p1479 Ns324p1480 Ns324p122 Ns324p1479 267602658 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 400507106) qz367 0 3 Ns324p1478 Ns324p119 Ns324p1479 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 400507106) qz368 0 3 Ns324p1480 Ns324p122 Ns324p1479 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1482 := Ns324p1407 Bool.false 564214309 149958 Bool.true 400507106 14148475504056880 1 Bool.false 267602658 Bool.false Bool.false 648837699 162498 BSN.abs_quadSignPos (BSN.cos_quad_nat3 199 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 267602658 268435456) qz224 rfl (Ns324p1477 rfl) (Ns324p1441 rfl) RS325to336.d43 RS325to336.d45 RS325to336.d17 (Ns324p1481 rfl rfl) rfl 

noncomputable def Ns324p1483 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 10) 648837699 268435456 162498 268435456 648837699 268435456 162498 268435456 348342087202111488 648837699 134217728 81249 67108864 (Ns324p1482 rfl rfl rfl rfl) 

noncomputable def Ns324p1484 := @Enclosure.Real.IsNear.mulLit_ff qz698 (Zeta.RiemannSiegel.correction qz223) 10469063 33554432 1 33554432 16837892285523 35184372088832 241006848915603 2660818139217920000 176276955124354274949 1180591620717411303424 

noncomputable abbrev qz702 := (@HPow.hPow Real Real Real qz133 qz222 qz135)

noncomputable def Ns324p1485 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz702 1 1 0 1 10469063 33554432 1 33554432 10469063 33554432 1 33554432 

noncomputable def Ns324p1486 := @Enclosure.Real.IsNear.sqrt_image qz222 3540937077709 33554432000 663053 33554432000 172347113 172347146 16777216 (@Enclosure.Real.IsNear.of_eq qz222 (@HMul.hMul Real Real Real qz5 qz221 qz3) Bool.false 3540937077709 33554432000 663053 33554432000 (BSN.t_div_two_pi_mk qz221 663053 1000 qz224) (@Enclosure.Real.IsNear.mulLit_ff qz221 qz3 663053 1000 0 1 5340353 33554432 1 33554432 3540937077709 33554432000 663053 33554432000 (Enclosure.Real.IsNear.const Bool.false 663053 1000) RS325to336.d48 rfl)) 

noncomputable abbrev qz777 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 663053 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz703 := qz777

noncomputable abbrev qz525 := qz703

noncomputable abbrev qz230 := qz525

noncomputable def Ns324p1487 := @Enclosure.Real.IsNear.sqrt_image qz230 344694259 33554432 33 33554432 53772713 53772719 16777216 (@Enclosure.Real.IsNear.recentre' qz230 Bool.false 344694259 33554432 33 33554432 344694259 33554432 33 33554432 (Ns324p1486 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns324p1488 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz230) 13443179 4194304 3 16777216 5234531 5234532 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz230) Bool.false 107545432 33554432 6 33554432 13443179 4194304 3 16777216 (Ns324p1487 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns324p1489 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz230)) Bool.false 10469063 33554432 1 33554432 10469063 33554432 1 33554432 (Ns324p1488 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz526 := (@HMul.hMul Real Real Real qz582 qz580 qz697)

noncomputable abbrev qz231 := (Real.cos qz526)

noncomputable abbrev qz704 := (@HMul.hMul Real Real Real qz723 qz775 qz775)

noncomputable abbrev qz527 := (@HSub.hSub Real Real Real qz586 (@HSub.hSub Real Real Real qz586 qz704 qz697) qz600)

noncomputable abbrev qz232 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz527))

noncomputable def Ns324p1490 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz223) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz231) qz232) Bool.false 16837892285523 

noncomputable def Ns324p1491 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz231) qz232 14760409 2097152 1331 

noncomputable abbrev qz233 := (@Neg.neg Real Real.instNeg (Real.cos qz526))

noncomputable def Ns324p1492 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz231) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz233)) Bool.true 14760409 2097152 1331 4194304 (BSN.inv_eq_neg_inv_neg qz231) 

noncomputable def Ns324p1493 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz233) Bool.false 236166544 33554432 10648 33554432 14760409 2097152 

noncomputable def Ns324p1494 := @Enclosure.Real.IsNear.recentre' qz231 Bool.true 2383699 16777216 65017152 10150215680000 2383699 16777216 1015893 158597120000 

noncomputable abbrev qz234 := qz526

noncomputable def Ns324p1495 := @Enclosure.Real.IsNear.cos_image qz234 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 28745381) qz374) Bool.false 28745381 16777216 13 2097152 Bool.true 2383699 16777216 1 

noncomputable def Ns324p1496 := nat_lit 890540488577050877551365799 

noncomputable def Ns324p1497 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz223 884279719003555 140737488355328 1 500000000000000 9149939 33554432 33 33554432 8091105487819669033145 4722366482869645213696 Ns324p1496 

noncomputable def Ns324p1498 := @Enclosure.Real.IsNear.subLit_ff_p qz230 qz1 344694259 33554432 33 33554432 10 1 0 1 9149939 9149939 33554432 33 

noncomputable def Ns324p1499 := @Ns324p1498 33554432 (@Enclosure.Real.IsNear.recentre' qz230 Bool.false 344694259 33554432 33 33554432 344694259 33554432 33 33554432 (Ns324p1486 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns324p1500 := @Enclosure.Real.IsNear.recentre' qz234 Bool.false 8091105487819669033145 4722366482869645213696 Ns324p1496 Ns324p173 28745381 16777216 13 2097152 (@Ns324p1497 Ns324p173 RS325to336.d47 (Ns324p1499 rfl rfl) rfl) 

noncomputable def Ns324p1501 := nat_lit 85976712910775854407100756013440499325285722730363543960417164669218434022872970599064589964241 

noncomputable def Ns324p1502 := nat_lit 318285483431547526439311682574787207430208521891304954022686015381169521327947298790314961 

noncomputable def Ns324p1503 := nat_lit 519815849864209766491679794164738393840491318079981605454578975230109164875534527554601753121745 

noncomputable def Ns324p1504 := BSN.cos_dyadic_bound_t 28745381 16777216 4 3 16777216 4840000 Ns324p1501 Ns324p825 Ns324p1502 Ns324p1503 Ns324p828 Ns324p1502 2383699 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 28745381) qz601 0 3 Ns324p1501 Ns324p825 Ns324p1502 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 28745381) (BSN.cosOddQ 16777216) 0 3 Ns324p1503 Ns324p828 Ns324p1502 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1505 := @Enclosure.Real.IsNear.inv_image qz233 2383699 16777216 1015893 158597120000 118077948 118088596 16777216 (@Enclosure.Real.IsNear.neg qz231 Bool.true 2383699 16777216 1015893 158597120000 (Ns324p1494 (@Ns324p1495 4840000 (Ns324p1500 rfl) (Enclosure.sfrac_false_div 28745381 16777216) (Ns324p1504 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns324p1506 := Ns324p1492 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz233) Bool.false 14760409 2097152 1331 4194304 (@Ns324p1493 1331 4194304 (Ns324p1505 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns324p1507 := @Enclosure.Real.IsNear.recentre' qz232 Bool.true 1140747 16777216 

noncomputable abbrev qz235 := (@HMul.hMul Real Real Real qz349 qz346 qz527)

noncomputable def Ns324p1508 := @Enclosure.Real.IsNear.cos_image qz235 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 54990433)) qz391) Bool.true 54990433 33554432 

noncomputable def Ns324p1509 := nat_lit 259684980567814467063671516005 

noncomputable def Ns324p1510 := nat_lit 9235678389701790963838656808010269 

noncomputable def Ns324p1511 := @Enclosure.Real.IsNear.recentre' qz235 Bool.true Ns324p1509 Ns324p188 Ns324p1510 

noncomputable abbrev qz236 := qz527

noncomputable def Ns324p1512 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz236 884279719003555 140737488355328 1 500000000000000 293668366453591 

noncomputable abbrev qz528 := (@HSub.hSub Real Real Real qz586 qz704 qz697)

noncomputable abbrev qz237 := qz528

noncomputable def Ns324p1513 := @Enclosure.Real.IsNear.subLit_tf qz237 qz29 223299622275927 1125899906842624 1711193319 1125899906842624 1 16 

noncomputable abbrev qz529 := qz704

noncomputable abbrev qz238 := qz529

noncomputable def Ns324p1514 := @Enclosure.Real.IsNear.subLit_ff_n qz238 qz223 83721383703721 1125899906842624 603897063 1125899906842624 9149939 33554432 33 33554432 

noncomputable def Ns324p1515 := @Enclosure.Real.IsNear.mulLit_ff qz223 qz223 9149939 33554432 33 33554432 9149939 33554432 33 33554432 83721383703721 1125899906842624 

noncomputable def Ns324p1516 := nat_lit 294533916724796532023363420787059729963650814059376684783577174203304964395638672776047914225063041 

noncomputable def Ns324p1517 := nat_lit 764620033254037426139812458056336669977046185931784657139977391152045457264517180697993106561 

noncomputable def Ns324p1518 := nat_lit 1781742240423058630782013921944891989108933525040307079287765034872059059018256225017350819006207105 

noncomputable def Ns324p1519 := BSN.cos_dyadic_bound_t 54990433 33554432 4 3 16777216 4840000 Ns324p1516 Ns324p594 Ns324p1517 Ns324p1518 Ns324p597 Ns324p1517 1140747 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 54990433) qz392 0 3 Ns324p1516 Ns324p594 Ns324p1517 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 54990433) (BSN.cosOddQ 33554432) 0 3 Ns324p1518 Ns324p597 Ns324p1517 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1520 := @Ns324p1507 796017216 81201725440000 1140747 16777216 12437769 1268776960000 (@Ns324p1508 161 16777216 Bool.true 1140747 16777216 1 4840000 (@Ns324p1511 Ns324p1052 54990433 33554432 161 16777216 (@Ns324p1512 1125899906842624 1711193319 1125899906842624 Ns324p1509 Ns324p188 Ns324p1510 Ns324p1052 RS325to336.d47 (@Ns324p1513 0 1 4698693863257456 293668366453591 1125899906842624 1711193319 1125899906842624 (@Ns324p1514 7492691991283277758464 223299622275927 1125899906842624 1711193319 1125899906842624 (@Ns324p1515 603897063 1125899906842624 (Ns324p1499 rfl rfl) (Ns324p1499 rfl rfl) rfl) (Ns324p1499 rfl rfl) rfl rfl) qz379 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 54990433 33554432) (BSN.cos_neg_of_bound 54990433 33554432 Bool.true 1140747 16777216 1 4840000 (Ns324p1519 rfl rfl)) rfl rfl) 

noncomputable def Ns324p1521 := @Ns324p1484 2524389491339871082467 Ns324p363 (Ns324p1485 qz31 (@Enclosure.Real.IsNear.of_eq qz702 (@Inv.inv Real Real.instInv (Real.sqrt qz230)) Bool.false 10469063 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz222 (BSN.t_div_two_pi_nonneg qz221 663053 1000 qz224)) Ns324p1489) rfl) (@Ns324p1490 35184372088832 241006848915603 2660818139217920000 (BSN.correction_mk qz223 (BSN.cos_two_pi_p_ne_zero_mk qz221 663053 1000 10 qz224 rfl rfl (@BSN.floor_sqrt_eq_dec qz221 663053 1000 10 qz224 rfl rfl rfl))) (@Ns324p1491 4194304 1140747 16777216 12437769 1268776960000 16837892285523 35184372088832 241006848915603 2660818139217920000 Ns324p1506 (Ns324p1520 rfl) rfl)) 

noncomputable def Ns324p1522 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz221) (hardyZApproximantRS₀ qz221) Bool.false 5530959801595040344443 1180591620717411303424 110618795987998262122467 Ns324p363 (@Eq.refl Real (hardyZApproximantRS₀ qz221)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz221) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz221) qz221 10) (@HMul.hMul Real Real Real qz5 qz698 (Zeta.RiemannSiegel.correction qz223))) Bool.false 5530959801595040344443 1180591620717411303424 110618795987998262122467 Ns324p363 (BSN.hardyZApproximantRS₀_eq qz221 10 (@BSN.floor_sqrt_eq_dec qz221 663053 1000 10 qz224 rfl rfl rfl)) (@Ns324p1406 5530959801595040344443 1180591620717411303424 110618795987998262122467 Ns324p363 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz221) qz221 10) (@HAdd.hAdd Real Real Real qz366 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 10)) Bool.false 648837699 134217728 81249 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz221) qz221 10) (Ns324p1483 (Ns324p1482 rfl rfl rfl rfl) rfl rfl)) (Ns324p1521 rfl) rfl rfl)) 

theorem RS325to336.d62 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz221) Bool.false 5530959801595040344443 1180591620717411303424 110618795987998262122467 Ns324p363 := Ns324p1522 

noncomputable def Ns324p1523 := nat_lit 12544489469398178058448404480 

noncomputable abbrev qz778 := (Enclosure.sfrac Bool.false 664401 1000)

noncomputable abbrev qz705 := qz778

noncomputable abbrev qz530 := qz705

noncomputable abbrev qz239 := qz530

noncomputable abbrev qz779 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 664401 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz706 := qz779

noncomputable abbrev qz531 := qz706

noncomputable abbrev qz240 := qz531

noncomputable abbrev qz780 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 664401 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz707 := qz780

noncomputable abbrev qz532 := qz707

noncomputable abbrev qz241 := qz532

noncomputable abbrev qz708 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz133 qz240 qz135))

noncomputable def Ns324p1524 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz239) qz239 10) (@HMul.hMul Real Real Real qz5 qz708 (Zeta.RiemannSiegel.correction qz241)) 8169115 16777216 162829 134217728 172859475119189180045 1180591620717411303424 2024151548530609257 103892062623132194701312 Ns324p1523 

noncomputable def Ns324p1525 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz239) qz239 Real.sin BSN.quadSignPos 9 10 664401 1000 199 268435456 134217728 4503599627370496 Bool.false 326362832213 2495 618095470 56 84886744 8 

noncomputable def Ns324p1526 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz239) qz239 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 664401 1000 105 155 268435456 134217728 4503599627370496 Bool.false 326362832213 2495 

noncomputable def Ns324p1527 := Ns324p1526 558195838 56 94906264 8 589812974 56 89478488 8 Bool.true 126344449 122974 Bool.true 229010782 Bool.true 152596144 14148475504056880 1 Bool.false 202224119 Bool.true Bool.false 144509285 Bool.false Bool.true 149671708 

noncomputable def Ns324p1528 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz239) qz239 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 664401 1000 16 49 268435456 134217728 4503599627370496 Bool.false 326362832213 2495 

noncomputable def Ns324p1529 := Ns324p1528 480971758 57 109588312 8 522351262 57 101459064 8 Bool.true 223309468 91218 Bool.false 58196373 Bool.true 26654626 14148475504056880 1 Bool.false 262151686 Bool.false Bool.false 26610846 Bool.true Bool.true 126344449 

noncomputable def Ns324p1530 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz239) qz239 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 664401 1000 187 93 268435456 134217728 4503599627370496 Bool.false 326362832213 2495 

noncomputable def Ns324p1531 := Ns324p1530 372130544 56 134217720 8 432030192 56 120047984 16 Bool.true 289639264 53584 Bool.false 268987563 Bool.false 107399789 14148475504056880 1 Bool.false 226178474 Bool.false Bool.false 104557274 Bool.true Bool.true 223309468 

noncomputable def Ns324p1532 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz239) qz239 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 664401 1000 480 309 268435456 134217728 4503599627370496 Bool.false 326362832213 2495 

noncomputable def Ns324p1533 := Ns324p1532 186065264 56 189812528 16 294906480 56 154981288 8 Bool.true 268435448 2560 Bool.false 345319178 Bool.false 134526660 14148475504056880 1 Bool.false 75313449 Bool.false Bool.false 128965841 Bool.true Bool.true 289639264 

noncomputable def Ns324p1534 := nat_lit 117745142728525929033554588106344072136958136398709598203 

noncomputable def Ns324p1535 := nat_lit 96846111016311612112350906979562206830039320756224000 

noncomputable def Ns324p1536 := nat_lit 62143147721611037259669226560480000 

noncomputable def Ns324p1537 := nat_lit 247727882409323146081066557489992834880 

noncomputable abbrev qz781 := (@Eq.refl Real (Enclosure.sfrac Bool.false 664401 1000))

noncomputable abbrev qz709 := qz781

noncomputable abbrev qz533 := qz709

noncomputable abbrev qz242 := qz533

noncomputable def Ns324p1538 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz239 664401 1000 1765715755204 16000000 1328802 4000 2000 Ns324p1536 Ns324p1537 qz242 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns324p1539 := nat_lit 339106011058154675616637213746270927754439432828283642824640 

noncomputable abbrev qz710 := (@HSub.hSub Real Real Real qz727 qz728 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz729 (@Nat.cast Real Real.instNatCast 1328802))))

noncomputable abbrev qz534 := (@HSub.hSub Real Real Real qz586 (@HMul.hMul Real Real Real qz582 (Enclosure.sfrac Bool.false 664401 4000) (Real.log (Enclosure.sfrac Bool.false 1765715755204 16000000))) (@HMul.hMul Real Real Real qz582 qz587 qz710))

noncomputable abbrev qz711 := (Enclosure.sfrac Bool.false 664401 2000)

noncomputable abbrev qz243 := (@HSub.hSub Real Real Real qz354 (@HSub.hSub Real Real Real qz354 qz534 qz711) (@HMul.hMul Real Real Real qz349 qz711 (Real.log Real.pi)))

noncomputable def Ns324p1540 := @Enclosure.Real.IsNear.addLit_ft_p qz243 (Enclosure.sfrac Bool.true Ns324p1536 Ns324p1537) 1368865215037888589003 1125899906842624000 4605069557496219189 495616000000000000000000 Ns324p1536 Ns324p1537 0 1 Ns324p1539 

noncomputable def Ns324p1541 := nat_lit 91862989550308420166554222592000 

noncomputable abbrev qz244 := (@HSub.hSub Real Real Real qz354 qz534 qz711)

noncomputable def Ns324p1542 := @Enclosure.Real.IsNear.subLit_ff_p qz244 (@HMul.hMul Real Real Real qz5 qz711 (Real.log Real.pi)) 1797022250707324824779 1125899906842624000 525313602835209 121000000000000000000 25520148019161 67108864000 664401 134217728000 Ns324p1541 1368865215037888589003 1125899906842624000 

noncomputable def Ns324p1543 := nat_lit 3594044501414649649558000 

noncomputable abbrev qz245 := qz534

noncomputable def Ns324p1544 := @Enclosure.Real.IsNear.subLit_ff_p qz245 qz711 2171046762710397938891 1125899906842624000 525313602835209 121000000000000000000 664401 2000 0 1 Ns324p1543 1797022250707324824779 1125899906842624000 525313602835209 121000000000000000000 

noncomputable def Ns324p1545 := nat_lit 4888762695773234904004113994212179968 

noncomputable def Ns324p1546 := nat_lit 56149662089235416003641344 

noncomputable def Ns324p1547 := nat_lit 33357789699102171863473463587799244612257915408902585617019511715215934416229812772415183950811531618109838863825678446354569652080834627326965981548380160 

noncomputable def Ns324p1548 := nat_lit 751517622169416262423198802753966495429631987847295210583514987733528920274341158628345205393792562842137364941457800182560796536079986091346117370314752 

noncomputable def Ns324p1549 := nat_lit 192340206135202318604308592035650237915951752351649548591810454616892849659320570765565166875490398548965227297447130925585310307493229424352952320 

noncomputable def Ns324p1550 := BSN.log_dyadic_bound 717139755204 2814291755204 7 6 Ns324p1547 134217728 38720000 Ns324p1548 Ns324p1549 69943956 3531431510408 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 717139755204) (BSN.artanhQ 2814291755204) 0 6 Ns324p1548 Ns324p1547 Ns324p1549 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz535 := (Real.log (Enclosure.sfrac Bool.false 1765715755204 16000000))

noncomputable def Ns324p1551 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 664401 4000) qz535 664401 4000 0 1 3268340491295991 281474976710656 195312621 7562500000000000 2171488690757547716391 1125899906842624000 129765900705021 30250000000000000000 (Enclosure.Real.IsNear.const Bool.false 664401 4000) (BSN.isNear_log_sfrac 1765715755204 16000000 3268340491295991 281474976710656 195312621 7562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1765715755204) qz357)) Bool.false Ns324p1546 Ns324p98 1000000619520000 38720000000000000000000 3268340491295991 281474976710656 195312621 7562500000000000 (BSN.log_rat_reduce_isNear 1765715755204 16000000 16 3531431510408 2097152000000 69943956 134217728 24973259072661432 36028797018963968 38720000 1000000000000000 rfl rfl rfl rfl (Ns324p1550 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns324p1552 := BSN.arctan_dyadic_bound_f 1000 1328802 1 0 16777216 4840000 0 1 1 0 1 1 12625 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1328802) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1328802) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns324p1553 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1328802))) 884279719003555 562949953421312 1 2000000000000000 12625 16777216 1 4840000 14828644606980002938880 883856094299555 562949953421312 50000000121 242000000000000000 qz15 (Ns324p1552 rfl) rfl rfl 

noncomputable abbrev qz536 := (@HMul.hMul Real Real Real qz582 qz587 qz710)

noncomputable abbrev qz246 := qz536

noncomputable abbrev qz537 := qz710

noncomputable abbrev qz247 := qz537

noncomputable def Ns324p1554 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 664401 4000) qz535) qz246 2171488690757547716391 1125899906842624000 129765900705021 30250000000000000000 883856094299555 2251799813685248 50000000121 968000000000000000 Ns324p1545 2171046762710397938891 1125899906842624000 525313602835209 121000000000000000000 (Ns324p1551 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz247 1 4 0 1 883856094299555 562949953421312 50000000121 242000000000000000 883856094299555 2251799813685248 50000000121 968000000000000000 qz365 Ns324p1553 rfl) 

noncomputable def Ns324p1555 := @Ns324p1540 Ns324p1534 Ns324p1535 4605069557496219189 495616000000000000000000 (@Ns324p1542 4605069557496219189 495616000000000000000000 (Ns324p1544 (Ns324p1554 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 664401 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz711 (Real.log Real.pi) 664401 2000 0 1 38410761 33554432 1 67108864 25520148019161 67108864000 664401 134217728000 (Enclosure.Real.IsNear.const Bool.false 664401 2000) RS325to336.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns324p1536 Ns324p1537) 

noncomputable def Ns324p1556 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz239) Bool.false Ns324p1534 Ns324p1535 4605069557496219189 495616000000000000000000 20397677013 16777216 313 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz239) (@HAdd.hAdd Real Real Real qz366 qz243 (Enclosure.sfrac Bool.true Ns324p1536 Ns324p1537)) Bool.false Ns324p1534 Ns324p1535 4605069557496219189 495616000000000000000000 Ns324p1538 (Ns324p1555 rfl rfl)) 

noncomputable def Ns324p1557 := nat_lit 3797796918167412089552896 

noncomputable def Ns324p1558 := nat_lit 3510259181358934501326879663441652121628398601434524276326153984818831770575446496107484793062206827510872539609780190283687163820731880561 

noncomputable def Ns324p1559 := nat_lit 2501400280758349895030446992478155093984878898058620666875766168224743623793122445938028290492531996764647205765507383863016071451761 

noncomputable def Ns324p1560 := nat_lit 17529489823171729649794242996506117596238377646614729075665876186533138110985995836651045243217113725189903321829755108429939285263043089521 

noncomputable def Ns324p1561 := BSN.sin_dyadic_bound_f 107939880483 68719476736 4 3 33554432 9689454 Ns324p1558 Ns324p110 Ns324p1559 Ns324p1560 Ns324p113 Ns324p1559 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107939880483) qz593 0 3 Ns324p1558 Ns324p110 Ns324p1559 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107939880483) qz594 0 3 Ns324p1560 Ns324p113 Ns324p1559 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1562 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz239) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20397677013) qz374) Bool.false 20397677013 16777216 313 33554432 Bool.true 33554431 33554432 1 4840000 (Ns324p1556 rfl) (Enclosure.sfrac_false_div 20397677013 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20397677013) qz374) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns324p1557) qz626) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 193 1000000000000000 9680000 4840000 (BSN.sin_reduce_arg_pos_rat_q1 20397677013 16777216 226375608064910080 72057594037927936 193 Ns324p1557 Ns324p518 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554431 33554432 Ns324p1557 Ns324p518 107939880483 68719476736 9689454 9680000 (Ns324p1561 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns324p1563 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz239) Bool.false Ns324p1534 Ns324p1535 4605069557496219189 495616000000000000000000 326362832213 268435456 2495 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz239) (@HAdd.hAdd Real Real Real qz366 qz243 (Enclosure.sfrac Bool.true Ns324p1536 Ns324p1537)) Bool.false Ns324p1534 Ns324p1535 4605069557496219189 495616000000000000000000 Ns324p1538 (Ns324p1555 rfl rfl)) 

noncomputable def Ns324p1564 := Ns324p1533 53584 BSN.abs_quadSignPos (BSN.cos_quad_nat0 480 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 75313449 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 309 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 128965841 268435456) qz242 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz239) qz239 1) Bool.true 33554431 33554432 24194913 2537553920000 268435448 268435456 2560 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz239) qz239 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz239)) Bool.true 33554431 33554432 24194913 2537553920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz239) qz239) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz239)) Bool.true 33554431 33554432 1548474432 162403450880000 33554431 33554432 24194913 2537553920000 (Ns324p1562 rfl rfl) rfl)) rfl) (Ns324p1563 rfl) RS325to336.d7 

noncomputable def Ns324p1565 := nat_lit 7663639627868915386623966267027818170350698450669288876019104170936552510765227745568972879795059403700637696 

noncomputable def Ns324p1566 := nat_lit 2875069723889920685007365905054092451237212039976554869053789042774173155025780175642784331869182038016 

noncomputable def Ns324p1567 := nat_lit 46442289565716083693946061985969663361332613328830402584516415033536898976853813460906949411137346383741521920 

noncomputable def Ns324p1568 := BSN.cos_dyadic_bound_f 345319178 268435456 4 3 268435456 134217728 Ns324p1565 Ns324p125 Ns324p1566 Ns324p1567 Ns324p128 Ns324p1566 75313449 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 345319178) qz369 0 3 Ns324p1565 Ns324p125 Ns324p1566 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 345319178) qz370 0 3 Ns324p1567 Ns324p128 Ns324p1566 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1569 := nat_lit 5142612475453161353378803527471753085588338365484763395845647933440000 

noncomputable def Ns324p1570 := nat_lit 107267183618631187654567856446206771441863954426041831449600000000 

noncomputable def Ns324p1571 := nat_lit 13468573288841944808354949462087011841768075558438642921392445235200000 

noncomputable def Ns324p1572 := BSN.sin_dyadic_bound_f 134526660 268435456 3 2 268435456 134217728 Ns324p1569 Ns324p249 Ns324p1570 Ns324p1571 Ns324p252 Ns324p1570 128965841 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 134526660) qz367 0 2 Ns324p1569 Ns324p249 Ns324p1570 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 134526660) qz368 0 2 Ns324p1571 Ns324p252 Ns324p1570 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1573 := nat_lit 82227082109737794114769008958930744676653243189048260922085491393837665 

noncomputable def Ns324p1574 := nat_lit 27406754038263066233817884636394271738548516640677616718793622567521 

noncomputable def Ns324p1575 := nat_lit 215312270780870368193349794507788264379848463134851014845060144928275041 

noncomputable def Ns324p1576 := BSN.sin_dyadic_bound_f 268987563 268435456 3 2 268435456 134217728 Ns324p1573 Ns324p249 Ns324p1574 Ns324p1575 Ns324p252 Ns324p1574 226178474 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 268987563) qz367 0 2 Ns324p1573 Ns324p249 Ns324p1574 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 268987563) qz368 0 2 Ns324p1575 Ns324p252 Ns324p1574 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1577 := nat_lit 133049642685440174264129224519441 

noncomputable def Ns324p1578 := BSN.sin_dyadic_bound_f 107399789 268435456 2 1 268435456 134217728 Ns324p1577 Ns324p270 Ns324p1577 Ns324p1577 Ns324p271 Ns324p1577 104557274 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 107399789) qz367 0 1 Ns324p1577 Ns324p270 Ns324p1577 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 107399789) qz368 0 1 Ns324p1577 Ns324p271 Ns324p1577 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1579 := Ns324p1531 91218 BSN.abs_quadSignPos (BSN.cos_quad_nat3 187 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 226178474 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 93 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 104557274 268435456) qz242 rfl rfl (Ns324p1564 RS325to336.d9 RS325to336.d11 RS325to336.d13 RS325to336.d17 (Ns324p1568 rfl rfl) (Ns324p1572 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns324p1563 rfl) RS325to336.d19 RS325to336.d21 RS325to336.d23 RS325to336.d25 RS325to336.d17 (Ns324p1576 rfl rfl) (Ns324p1578 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns324p1580 := nat_lit 11470535016011423358426256606641 

noncomputable def Ns324p1581 := BSN.cos_dyadic_bound_f 58196373 268435456 2 1 268435456 134217728 Ns324p1580 Ns324p149 Ns324p1580 Ns324p1580 Ns324p150 Ns324p1580 262151686 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 58196373) qz369 0 1 Ns324p1580 Ns324p149 Ns324p1580 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 58196373) qz370 0 1 Ns324p1580 Ns324p150 Ns324p1580 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1582 := nat_lit 504766323866625007506374415376 

noncomputable def Ns324p1583 := BSN.sin_dyadic_bound_f 26654626 268435456 2 1 268435456 134217728 Ns324p1582 Ns324p270 Ns324p1582 Ns324p1582 Ns324p271 Ns324p1582 26610846 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 26654626) qz367 0 1 Ns324p1582 Ns324p270 Ns324p1582 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 26654626) qz368 0 1 Ns324p1582 Ns324p271 Ns324p1582 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1584 := Ns324p1529 122974 BSN.abs_quadSignPos (BSN.cos_quad_nat0 16 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 262151686 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 26610846 268435456) qz242 rfl rfl (Ns324p1579 rfl rfl) (Ns324p1563 rfl) RS325to336.d27 RS325to336.d29 RS325to336.d31 RS325to336.d33 RS325to336.d17 (Ns324p1581 rfl rfl) (Ns324p1583 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p1585 := nat_lit 43195757342014574199770065303692117342102635564604040384147719077658880 

noncomputable def Ns324p1586 := nat_lit 7565670759197016997828470644162775727023690015681480093784695275776 

noncomputable def Ns324p1587 := nat_lit 113119496238332803924258448747674519973377435742509002419282660458660096 

noncomputable def Ns324p1588 := BSN.sin_dyadic_bound_f 229010782 268435456 3 2 268435456 134217728 Ns324p1585 Ns324p249 Ns324p1586 Ns324p1587 Ns324p252 Ns324p1586 202224119 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 229010782) qz367 0 2 Ns324p1585 Ns324p249 Ns324p1586 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 229010782) qz368 0 2 Ns324p1587 Ns324p252 Ns324p1586 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1589 := nat_lit 8513939036480834100456516532788512667875917980619638496595141459968000 

noncomputable def Ns324p1590 := nat_lit 294000775158245611130417299471831476539750983186139637634790588416 

noncomputable def Ns324p1591 := nat_lit 22297935760956690246396665481675531164903482733364370884050152258011136 

noncomputable def Ns324p1592 := BSN.sin_dyadic_bound_f 152596144 268435456 3 2 268435456 134217728 Ns324p1589 Ns324p249 Ns324p1590 Ns324p1591 Ns324p252 Ns324p1590 144509285 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 152596144) qz367 0 2 Ns324p1589 Ns324p249 Ns324p1590 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 152596144) qz368 0 2 Ns324p1591 Ns324p252 Ns324p1590 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1593 := Ns324p1527 150264 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 105 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 202224119 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 155 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 144509285 268435456) qz242 rfl rfl (Ns324p1584 rfl) (Ns324p1563 rfl) RS325to336.d35 RS325to336.d37 RS325to336.d39 RS325to336.d41 RS325to336.d17 (Ns324p1588 rfl rfl) (Ns324p1592 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns324p1594 := nat_lit 32608948414917122124706709634157414929281536076207793921439789874633986496334696499339226412973224338619140625 

noncomputable def Ns324p1595 := nat_lit 12607406491083219947348093001670464858272781830462091837720113767147721327445749273047506809234619140625 

noncomputable def Ns324p1596 := nat_lit 162895510638248451640291365436702718911844402134319207867001082223519877279251339830874960924438884754619140625 

noncomputable def Ns324p1597 := BSN.sin_dyadic_bound_f 390587925 268435456 4 3 268435456 134217728 Ns324p1594 Ns324p119 Ns324p1595 Ns324p1596 Ns324p122 Ns324p1595 266639424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 390587925) qz367 0 3 Ns324p1594 Ns324p119 Ns324p1595 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 390587925) qz368 0 3 Ns324p1596 Ns324p122 Ns324p1595 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1598 := Ns324p1525 Bool.true 149671708 150264 Bool.true 390587925 14148475504056880 1 Bool.false 266639424 Bool.false Bool.true 65352920 162829 BSN.abs_quadSignPos (BSN.cos_quad_nat3 199 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266639424 268435456) qz242 rfl (Ns324p1593 rfl) (Ns324p1563 rfl) RS325to336.d43 RS325to336.d45 RS325to336.d17 (Ns324p1597 rfl rfl) rfl 

noncomputable def Ns324p1599 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz239) qz239 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz239) qz239 10) 65352920 268435456 162829 268435456 65352920 268435456 162829 268435456 35086081762263040 8169115 16777216 162829 134217728 (Ns324p1598 rfl rfl rfl rfl) 

noncomputable def Ns324p1600 := @Enclosure.Real.IsNear.mulLit_ff qz708 (Zeta.RiemannSiegel.correction qz241) 10463749 33554432 1 33554432 16519841513705 35184372088832 2657947178025497 42573090227486720000 172859475119189180045 1180591620717411303424 

noncomputable abbrev qz712 := (@HPow.hPow Real Real Real qz133 qz240 qz135)

noncomputable def Ns324p1601 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz712 1 1 0 1 10463749 33554432 1 33554432 10463749 33554432 1 33554432 

noncomputable def Ns324p1602 := @Enclosure.Real.IsNear.sqrt_image qz240 3548135873553 33554432000 664401 33554432000 172522217 172522250 16777216 (@Enclosure.Real.IsNear.of_eq qz240 (@HMul.hMul Real Real Real qz5 qz239 qz3) Bool.false 3548135873553 33554432000 664401 33554432000 (BSN.t_div_two_pi_mk qz239 664401 1000 qz242) (@Enclosure.Real.IsNear.mulLit_ff qz239 qz3 664401 1000 0 1 5340353 33554432 1 33554432 3548135873553 33554432000 664401 33554432000 (Enclosure.Real.IsNear.const Bool.false 664401 1000) RS325to336.d48 rfl)) 

noncomputable abbrev qz782 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 664401 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz713 := qz782

noncomputable abbrev qz538 := qz713

noncomputable abbrev qz248 := qz538

noncomputable def Ns324p1603 := @Enclosure.Real.IsNear.sqrt_image qz248 345044467 33554432 33 33554432 53800023 53800029 16777216 (@Enclosure.Real.IsNear.recentre' qz248 Bool.false 345044467 33554432 33 33554432 345044467 33554432 33 33554432 (Ns324p1602 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns324p1604 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz248) 26900013 8388608 3 16777216 5231874 5231875 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz248) Bool.false 107600052 33554432 6 33554432 26900013 8388608 3 16777216 (Ns324p1603 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns324p1605 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz248)) Bool.false 10463749 33554432 1 33554432 10463749 33554432 1 33554432 (Ns324p1604 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz539 := (@HMul.hMul Real Real Real qz582 qz580 qz707)

noncomputable abbrev qz249 := (Real.cos qz539)

noncomputable abbrev qz714 := (@HMul.hMul Real Real Real qz723 qz780 qz780)

noncomputable abbrev qz540 := (@HSub.hSub Real Real Real qz586 (@HSub.hSub Real Real Real qz586 qz714 qz707) qz600)

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz540))

noncomputable def Ns324p1606 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz241) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz249) qz250) Bool.false 16519841513705 

noncomputable def Ns324p1607 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz249) qz250 162381103 33554432 5035 

noncomputable abbrev qz251 := (@Neg.neg Real Real.instNeg (Real.cos qz539))

noncomputable def Ns324p1608 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz249) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz251)) Bool.true 162381103 33554432 5035 33554432 (BSN.inv_eq_neg_inv_neg qz249) 

noncomputable def Ns324p1609 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz251) Bool.false 162381103 33554432 5035 33554432 162381103 33554432 

noncomputable def Ns324p1610 := @Enclosure.Real.IsNear.recentre' qz249 Bool.true 3466844 16777216 65017152 10150215680000 866711 4194304 1015893 158597120000 

noncomputable abbrev qz252 := qz539

noncomputable def Ns324p1611 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3730699) (@Nat.cast Real Real.instNatCast 2097152)) Bool.false 3730699 2097152 13 2097152 Bool.true 3466844 16777216 1 

noncomputable def Ns324p1612 := nat_lit 178108097716011828272992187 

noncomputable def Ns324p1613 := nat_lit 28823037615171174400000000000000 

noncomputable def Ns324p1614 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz241 884279719003555 140737488355328 1 500000000000000 9500147 33554432 33 33554432 8400787319652466022585 4722366482869645213696 Ns324p1612 

noncomputable def Ns324p1615 := @Enclosure.Real.IsNear.subLit_ff_p qz248 qz1 345044467 33554432 33 33554432 10 1 0 1 9500147 9500147 33554432 33 

noncomputable def Ns324p1616 := @Ns324p1615 33554432 (@Enclosure.Real.IsNear.recentre' qz248 Bool.false 345044467 33554432 33 33554432 345044467 33554432 33 33554432 (Ns324p1602 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns324p1617 := @Enclosure.Real.IsNear.recentre' qz252 Bool.false 8400787319652466022585 4722366482869645213696 Ns324p1612 Ns324p1613 3730699 2097152 13 2097152 (@Ns324p1614 Ns324p1613 RS325to336.d47 (Ns324p1616 rfl rfl) rfl) 

noncomputable def Ns324p1618 := nat_lit 1455154900336850856541160771158107870326392534614104973638104067728035088182506728081 

noncomputable def Ns324p1619 := nat_lit 7269131557606467561616739673612447350597346543519255666266107179178048079571601 

noncomputable def Ns324p1620 := nat_lit 8793027704091273653636181576219302402148727009287758600078335068499276000463033510545 

noncomputable def Ns324p1621 := BSN.cos_dyadic_bound_t 3730699 2097152 4 3 16777216 4840000 Ns324p1618 Ns324p709 Ns324p1619 Ns324p1620 Ns324p712 Ns324p1619 3466844 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3730699) (BSN.cosEvenQ 2097152) 0 3 Ns324p1618 Ns324p709 Ns324p1619 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3730699) (BSN.cosOddQ 2097152) 0 3 Ns324p1620 Ns324p712 Ns324p1619 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1622 := @Enclosure.Real.IsNear.inv_image qz251 866711 4194304 1015893 158597120000 81188034 81193069 16777216 (@Enclosure.Real.IsNear.neg qz249 Bool.true 866711 4194304 1015893 158597120000 (Ns324p1610 (@Ns324p1611 4840000 (Ns324p1617 rfl) (Enclosure.sfrac_false_div 3730699 2097152) (Ns324p1621 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns324p1623 := Ns324p1608 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz251) Bool.false 162381103 33554432 5035 33554432 (@Ns324p1609 5035 33554432 (Ns324p1622 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns324p1624 := @Enclosure.Real.IsNear.recentre' qz250 Bool.true 1627760 16777216 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz349 qz346 qz540)

noncomputable def Ns324p1625 := @Enclosure.Real.IsNear.cos_image qz253 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 27983913)) qz374) Bool.true 27983913 16777216 

noncomputable def Ns324p1626 := nat_lit 264300585739364287542043622245 

noncomputable def Ns324p1627 := nat_lit 46802140755345923830600797148191377 

noncomputable def Ns324p1628 := @Enclosure.Real.IsNear.recentre' qz253 Bool.true Ns324p1626 Ns324p188 Ns324p1627 

noncomputable abbrev qz254 := qz540

noncomputable def Ns324p1629 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz254 884279719003555 140737488355328 1 500000000000000 298887987657559 

noncomputable abbrev qz541 := (@HSub.hSub Real Real Real qz586 qz714 qz707)

noncomputable abbrev qz255 := qz541

noncomputable def Ns324p1630 := @Enclosure.Real.IsNear.subLit_tf qz255 qz29 228519243479895 1125899906842624 1734307047 1125899906842624 1 16 

noncomputable abbrev qz542 := qz714

noncomputable abbrev qz256 := qz542

noncomputable def Ns324p1631 := @Enclosure.Real.IsNear.subLit_ff_n qz256 qz241 90252793021609 1125899906842624 627010791 1125899906842624 9500147 33554432 33 33554432 

noncomputable def Ns324p1632 := @Enclosure.Real.IsNear.mulLit_ff qz241 qz241 9500147 33554432 33 33554432 9500147 33554432 33 33554432 90252793021609 1125899906842624 

noncomputable def Ns324p1633 := nat_lit 77182044344947354627746444972643088442549896212001385175569453495327600778785298210425433777761 

noncomputable def Ns324p1634 := nat_lit 230622302284198595832148022605080731272141139537273374569564190726399233196042126462314081 

noncomputable def Ns324p1635 := nat_lit 466804964752366480013648685311692520404324698252219304420163382205412904487695115804397850879585 

noncomputable def Ns324p1636 := BSN.cos_dyadic_bound_t 27983913 16777216 4 3 16777216 4840000 Ns324p1633 Ns324p825 Ns324p1634 Ns324p1635 Ns324p828 Ns324p1634 1627760 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 27983913) qz601 0 3 Ns324p1633 Ns324p825 Ns324p1634 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 27983913) (BSN.cosOddQ 16777216) 0 3 Ns324p1635 Ns324p828 Ns324p1634 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns324p1637 := @Ns324p1624 1606554432 162403450880000 101735 1048576 25102413 2537553920000 (@Ns324p1625 325 33554432 Bool.true 1627760 16777216 1 4840000 (@Ns324p1628 Ns324p191 27983913 16777216 325 33554432 (@Ns324p1629 1125899906842624 1734307047 1125899906842624 Ns324p1626 Ns324p188 Ns324p1627 Ns324p191 RS325to336.d47 (@Ns324p1630 0 1 4782207802520944 298887987657559 1125899906842624 1734307047 1125899906842624 (@Ns324p1631 7667833416037580144640 228519243479895 1125899906842624 1734307047 1125899906842624 (@Ns324p1632 627010791 1125899906842624 (Ns324p1616 rfl rfl) (Ns324p1616 rfl rfl) rfl) (Ns324p1616 rfl rfl) rfl rfl) qz379 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 27983913 16777216) (BSN.cos_neg_of_bound 27983913 16777216 Bool.true 1627760 16777216 1 4840000 (Ns324p1636 rfl rfl)) rfl rfl) 

noncomputable def Ns324p1638 := @Ns324p1600 2024151548530609257 103892062623132194701312 (Ns324p1601 qz31 (@Enclosure.Real.IsNear.of_eq qz712 (@Inv.inv Real Real.instInv (Real.sqrt qz248)) Bool.false 10463749 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz240 (BSN.t_div_two_pi_nonneg qz239 664401 1000 qz242)) Ns324p1605) rfl) (@Ns324p1606 35184372088832 2657947178025497 42573090227486720000 (BSN.correction_mk qz241 (BSN.cos_two_pi_p_ne_zero_mk qz239 664401 1000 10 qz242 rfl rfl (@BSN.floor_sqrt_eq_dec qz239 664401 1000 10 qz242 rfl rfl rfl))) (@Ns324p1607 33554432 101735 1048576 25102413 2537553920000 16519841513705 35184372088832 2657947178025497 42573090227486720000 Ns324p1623 (Ns324p1637 rfl) rfl)) 

noncomputable def Ns324p1639 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz239) (hardyZApproximantRS₀ qz239) Bool.true 747709838712106827405 1180591620717411303424 128062946251283975273 103892062623132194701312 (@Eq.refl Real (hardyZApproximantRS₀ qz239)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz239) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz239) qz239 10) (@HMul.hMul Real Real Real qz5 qz708 (Zeta.RiemannSiegel.correction qz241))) Bool.true 747709838712106827405 1180591620717411303424 128062946251283975273 103892062623132194701312 (BSN.hardyZApproximantRS₀_eq qz239 10 (@BSN.floor_sqrt_eq_dec qz239 664401 1000 10 qz242 rfl rfl rfl)) (@Ns324p1524 747709838712106827405 1180591620717411303424 128062946251283975273 103892062623132194701312 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz239) qz239 10) (@HAdd.hAdd Real Real Real qz366 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz239) qz239 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz239) qz239 10)) Bool.true 8169115 16777216 162829 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz239) qz239 10) (Ns324p1599 (Ns324p1598 rfl rfl rfl rfl) rfl rfl)) (Ns324p1638 rfl) rfl rfl)) 

theorem RS325to336.d63 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz239) Bool.true 747709838712106827405 1180591620717411303424 128062946251283975273 103892062623132194701312 := Ns324p1639 

noncomputable def RS325to336.d64 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz543 := (RS325to336.d3 qz581 qz602 (@Enclosure.dec_le_dec qz581 qz602 648182 1000 649791 1000 (@Eq.refl Real qz581) qz605 rfl rfl rfl))

noncomputable abbrev qz257 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz543)

noncomputable def Ns324p1640 := @Enclosure.Real.IsNear.of_eq qz257 (hardyZApproximantRS₀ qz4) Bool.true 490605271431258893031 590295810358705651712 425196675376988652708121 Ns324p74 

noncomputable abbrev qz544 := (@Enclosure.dec_le_dec qz581 qz602 648182 1000 649791 1000 (@Eq.refl Real qz581) qz605 rfl rfl rfl)

noncomputable abbrev qz258 := qz544

noncomputable def Ns324p1641 := @Enclosure.Real.IsNear.neg_val qz257 490605271431258893031 590295810358705651712 425196675376988652708121 Ns324p74 (Ns324p1640 (RS325to336.d4 qz4 qz33 qz258) RS325to336.d49) rfl 

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz543)

noncomputable def Ns324p1642 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantRS₀ qz33) Bool.false 129509124892096188683 147573952589676412928 426596656986340521222093 Ns324p74 

noncomputable def Ns324p1643 := @Enclosure.Real.IsNear.pos_val qz259 129509124892096188683 147573952589676412928 426596656986340521222093 Ns324p74 (Ns324p1642 (RS325to336.d50 qz4 qz33 qz258) RS325to336.d51) rfl 

noncomputable def Ns324p1644 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz257 qz4 qz4 648182 1000 648182 1000 

noncomputable def Ns324p1645 := @Enclosure.norm_gt_of_isNear qz257 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 490605271431258893031 590295810358705651712 425196675376988652708121 

noncomputable def Ns324p1646 := @Ns324p1645 Ns324p74 317672429 5368709120 1213 5368709120 (Ns324p1640 (RS325to336.d4 qz4 qz33 qz258) RS325to336.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable def Ns324p1647 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz259 qz4 qz33 648182 1000 649791 1000 

noncomputable def Ns324p1648 := @Enclosure.norm_gt_of_isNear qz259 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 129509124892096188683 147573952589676412928 426596656986340521222093 

noncomputable def Ns324p1649 := @Ns324p1648 Ns324p74 317672429 5368709120 1213 5368709120 (Ns324p1642 (RS325to336.d50 qz4 qz33 qz258) RS325to336.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable abbrev qz260 := qz543

noncomputable def Ns324p1650 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz260 (@BSN.thirtyTwoPi_le_dec qz4 648182 1000 qz9 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz257 qz259 (Ns324p1641 rfl rfl) (Ns324p1643 rfl rfl)) (Ns324p1644 qz9 qz9 rfl rfl rfl rfl (Ns324p1646 rfl)) (Ns324p1647 qz9 qz36 rfl rfl rfl rfl (Ns324p1649 rfl)) 

noncomputable abbrev qz545 := (RS325to336.d3 qz602 qz612 (@Enclosure.dec_le_dec qz602 qz612 649791 1000 650383 1000 qz605 qz615 rfl rfl rfl))

noncomputable abbrev qz261 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz545)

noncomputable def Ns324p1651 := @Enclosure.Real.IsNear.of_eq qz261 (hardyZApproximantRS₀ qz33) Bool.false 129509124892096188683 147573952589676412928 426596656986340521222093 Ns324p74 

noncomputable abbrev qz546 := (@Enclosure.dec_le_dec qz602 qz612 649791 1000 650383 1000 qz605 qz615 rfl rfl rfl)

noncomputable abbrev qz262 := qz546

noncomputable def Ns324p1652 := @Enclosure.Real.IsNear.pos_val qz261 129509124892096188683 147573952589676412928 426596656986340521222093 Ns324p74 (Ns324p1651 (RS325to336.d4 qz33 qz60 qz262) RS325to336.d51) rfl 

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz545)

noncomputable def Ns324p1653 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantRS₀ qz60) Bool.true 278305946873645870413 1180591620717411303424 106763768414332230341479 Ns324p363 

noncomputable def Ns324p1654 := @Enclosure.Real.IsNear.neg_val qz263 278305946873645870413 1180591620717411303424 106763768414332230341479 Ns324p363 (Ns324p1653 (RS325to336.d50 qz33 qz60 qz262) RS325to336.d53) rfl 

noncomputable def Ns324p1655 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz261 qz4 qz33 648182 1000 649791 1000 

noncomputable def Ns324p1656 := @Enclosure.norm_gt_of_isNear qz261 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 129509124892096188683 147573952589676412928 426596656986340521222093 

noncomputable def Ns324p1657 := @Ns324p1656 Ns324p74 317672429 5368709120 1213 5368709120 (Ns324p1651 (RS325to336.d4 qz33 qz60 qz262) RS325to336.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable def Ns324p1658 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz263 qz4 qz60 648182 1000 650383 1000 

noncomputable def Ns324p1659 := @Enclosure.norm_gt_of_isNear qz263 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 278305946873645870413 1180591620717411303424 106763768414332230341479 

noncomputable def Ns324p1660 := @Ns324p1659 Ns324p363 317672429 5368709120 1213 5368709120 (Ns324p1653 (RS325to336.d50 qz33 qz60 qz262) RS325to336.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable abbrev qz264 := qz545

noncomputable def Ns324p1661 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz264 (@BSN.thirtyTwoPi_le_dec qz33 649791 1000 qz36 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz261 qz263 (Ns324p1652 rfl rfl) (Ns324p1654 rfl rfl)) (Ns324p1655 qz9 qz36 rfl rfl rfl rfl (Ns324p1657 rfl)) (Ns324p1658 qz9 qz63 rfl rfl rfl rfl (Ns324p1660 rfl)) 

noncomputable abbrev qz547 := (RS325to336.d3 qz612 qz620 (@Enclosure.dec_le_dec qz612 qz620 650383 1000 652160 1000 qz615 qz623 rfl rfl rfl))

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz547)

noncomputable def Ns324p1662 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantRS₀ qz60) Bool.true 278305946873645870413 1180591620717411303424 106763768414332230341479 Ns324p363 

noncomputable abbrev qz548 := (@Enclosure.dec_le_dec qz612 qz620 650383 1000 652160 1000 qz615 qz623 rfl rfl rfl)

noncomputable abbrev qz266 := qz548

noncomputable def Ns324p1663 := @Enclosure.Real.IsNear.neg_val qz265 278305946873645870413 1180591620717411303424 106763768414332230341479 Ns324p363 (Ns324p1662 (RS325to336.d4 qz60 qz78 qz266) RS325to336.d53) rfl 

noncomputable abbrev qz267 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz547)

noncomputable def Ns324p1664 := @Enclosure.Real.IsNear.of_eq qz267 (hardyZApproximantRS₀ qz78) Bool.false 21567178651716103548811 2361183241434822606848 85790178295579456416347 Ns324p483 

noncomputable def Ns324p1665 := @Enclosure.Real.IsNear.pos_val qz267 21567178651716103548811 2361183241434822606848 85790178295579456416347 Ns324p483 (Ns324p1664 (RS325to336.d50 qz60 qz78 qz266) RS325to336.d54) rfl 

noncomputable def Ns324p1666 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz265 qz4 qz60 648182 1000 650383 1000 

noncomputable def Ns324p1667 := @Enclosure.norm_gt_of_isNear qz265 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 278305946873645870413 1180591620717411303424 106763768414332230341479 

noncomputable def Ns324p1668 := @Ns324p1667 Ns324p363 317672429 5368709120 1213 5368709120 (Ns324p1662 (RS325to336.d4 qz60 qz78 qz266) RS325to336.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable def Ns324p1669 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz267 qz4 qz78 648182 1000 652160 1000 

noncomputable def Ns324p1670 := @Enclosure.norm_gt_of_isNear qz267 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 21567178651716103548811 2361183241434822606848 85790178295579456416347 

noncomputable def Ns324p1671 := @Ns324p1670 Ns324p483 317672429 5368709120 1213 5368709120 (Ns324p1664 (RS325to336.d50 qz60 qz78 qz266) RS325to336.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable abbrev qz268 := qz547

noncomputable def Ns324p1672 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz60 650383 1000 qz63 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz265 qz267 (Ns324p1663 rfl rfl) (Ns324p1665 rfl rfl)) (Ns324p1666 qz9 qz63 rfl rfl rfl rfl (Ns324p1668 rfl)) (Ns324p1669 qz9 qz81 rfl rfl rfl rfl (Ns324p1671 rfl)) 

noncomputable abbrev qz549 := (RS325to336.d3 qz620 qz629 (@Enclosure.dec_le_dec qz620 qz629 652160 1000 654021 1000 qz623 qz632 rfl rfl rfl))

noncomputable abbrev qz269 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz549)

noncomputable def Ns324p1673 := @Enclosure.Real.IsNear.of_eq qz269 (hardyZApproximantRS₀ qz78) Bool.false 21567178651716103548811 2361183241434822606848 85790178295579456416347 Ns324p483 

noncomputable abbrev qz550 := (@Enclosure.dec_le_dec qz620 qz629 652160 1000 654021 1000 qz623 qz632 rfl rfl rfl)

noncomputable abbrev qz270 := qz550

noncomputable def Ns324p1674 := @Enclosure.Real.IsNear.pos_val qz269 21567178651716103548811 2361183241434822606848 85790178295579456416347 Ns324p483 (Ns324p1673 (RS325to336.d4 qz78 qz96 qz270) RS325to336.d54) rfl 

noncomputable abbrev qz271 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz549)

noncomputable def Ns324p1675 := @Enclosure.Real.IsNear.of_eq qz271 (hardyZApproximantRS₀ qz96) Bool.true 5112658585416673647249 9444732965739290427392 862503344816291389915047 Ns324p602 

noncomputable def Ns324p1676 := @Enclosure.Real.IsNear.neg_val qz271 5112658585416673647249 9444732965739290427392 862503344816291389915047 Ns324p602 (Ns324p1675 (RS325to336.d50 qz78 qz96 qz270) RS325to336.d55) rfl 

noncomputable def Ns324p1677 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz269 qz4 qz78 648182 1000 652160 1000 

noncomputable def Ns324p1678 := @Enclosure.norm_gt_of_isNear qz269 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 21567178651716103548811 2361183241434822606848 85790178295579456416347 

noncomputable def Ns324p1679 := @Ns324p1678 Ns324p483 317672429 5368709120 1213 5368709120 (Ns324p1673 (RS325to336.d4 qz78 qz96 qz270) RS325to336.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable def Ns324p1680 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz271 qz4 qz96 648182 1000 654021 1000 

noncomputable def Ns324p1681 := @Enclosure.norm_gt_of_isNear qz271 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 5112658585416673647249 9444732965739290427392 862503344816291389915047 

noncomputable def Ns324p1682 := @Ns324p1681 Ns324p602 317672429 5368709120 1213 5368709120 (Ns324p1675 (RS325to336.d50 qz78 qz96 qz270) RS325to336.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable abbrev qz272 := qz549

noncomputable def Ns324p1683 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz78 652160 1000 qz81 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz269 qz271 (Ns324p1674 rfl rfl) (Ns324p1676 rfl rfl)) (Ns324p1677 qz9 qz81 rfl rfl rfl rfl (Ns324p1679 rfl)) (Ns324p1680 qz9 qz99 rfl rfl rfl rfl (Ns324p1682 rfl)) 

noncomputable abbrev qz551 := (RS325to336.d3 qz629 qz637 (@Enclosure.dec_le_dec qz629 qz637 654021 1000 654697 1000 qz632 qz640 rfl rfl rfl))

noncomputable abbrev qz273 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz551)

noncomputable def Ns324p1684 := @Enclosure.Real.IsNear.of_eq qz273 (hardyZApproximantRS₀ qz96) Bool.true 5112658585416673647249 9444732965739290427392 862503344816291389915047 Ns324p602 

noncomputable abbrev qz552 := (@Enclosure.dec_le_dec qz629 qz637 654021 1000 654697 1000 qz632 qz640 rfl rfl rfl)

noncomputable abbrev qz274 := qz552

noncomputable def Ns324p1685 := @Enclosure.Real.IsNear.neg_val qz273 5112658585416673647249 9444732965739290427392 862503344816291389915047 Ns324p602 (Ns324p1684 (RS325to336.d4 qz96 qz114 qz274) RS325to336.d55) rfl 

noncomputable abbrev qz275 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz551)

noncomputable def Ns324p1686 := @Enclosure.Real.IsNear.of_eq qz275 (hardyZApproximantRS₀ qz114) Bool.false 21847814013035493835149 18889465931478580854784 345808687290523280339009 Ns324p717 

noncomputable def Ns324p1687 := @Enclosure.Real.IsNear.pos_val qz275 21847814013035493835149 18889465931478580854784 345808687290523280339009 Ns324p717 (Ns324p1686 (RS325to336.d50 qz96 qz114 qz274) RS325to336.d56) rfl 

noncomputable def Ns324p1688 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz273 qz4 qz96 648182 1000 654021 1000 

noncomputable def Ns324p1689 := @Enclosure.norm_gt_of_isNear qz273 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 5112658585416673647249 9444732965739290427392 862503344816291389915047 

noncomputable def Ns324p1690 := @Ns324p1689 Ns324p602 317672429 5368709120 1213 5368709120 (Ns324p1684 (RS325to336.d4 qz96 qz114 qz274) RS325to336.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable def Ns324p1691 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz275 qz4 qz114 648182 1000 654697 1000 

noncomputable def Ns324p1692 := @Enclosure.norm_gt_of_isNear qz275 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 21847814013035493835149 18889465931478580854784 345808687290523280339009 

noncomputable def Ns324p1693 := @Ns324p1692 Ns324p717 317672429 5368709120 1213 5368709120 (Ns324p1686 (RS325to336.d50 qz96 qz114 qz274) RS325to336.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable abbrev qz276 := qz551

noncomputable def Ns324p1694 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz96 654021 1000 qz99 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz273 qz275 (Ns324p1685 rfl rfl) (Ns324p1687 rfl rfl)) (Ns324p1688 qz9 qz99 rfl rfl rfl rfl (Ns324p1690 rfl)) (Ns324p1691 qz9 qz117 rfl rfl rfl rfl (Ns324p1693 rfl)) 

noncomputable abbrev qz553 := (RS325to336.d3 qz637 qz645 (@Enclosure.dec_le_dec qz637 qz645 654697 1000 656302 1000 qz640 qz649 rfl rfl rfl))

noncomputable abbrev qz277 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz553)

noncomputable def Ns324p1695 := @Enclosure.Real.IsNear.of_eq qz277 (hardyZApproximantRS₀ qz114) Bool.false 21847814013035493835149 18889465931478580854784 345808687290523280339009 Ns324p717 

noncomputable abbrev qz554 := (@Enclosure.dec_le_dec qz637 qz645 654697 1000 656302 1000 qz640 qz649 rfl rfl rfl)

noncomputable abbrev qz278 := qz554

noncomputable def Ns324p1696 := @Enclosure.Real.IsNear.pos_val qz277 21847814013035493835149 18889465931478580854784 345808687290523280339009 Ns324p717 (Ns324p1695 (RS325to336.d4 qz114 qz132 qz278) RS325to336.d56) rfl 

noncomputable abbrev qz279 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz553)

noncomputable def Ns324p1697 := @Enclosure.Real.IsNear.of_eq qz279 (hardyZApproximantRS₀ qz132) Bool.true 811370617184835567351 590295810358705651712 435534530697970246101563 Ns324p74 

noncomputable def Ns324p1698 := @Enclosure.Real.IsNear.neg_val qz279 811370617184835567351 590295810358705651712 435534530697970246101563 Ns324p74 (Ns324p1697 (RS325to336.d50 qz114 qz132 qz278) RS325to336.d57) rfl 

noncomputable def Ns324p1699 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz277 qz4 qz114 648182 1000 654697 1000 

noncomputable def Ns324p1700 := @Enclosure.norm_gt_of_isNear qz277 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 21847814013035493835149 18889465931478580854784 345808687290523280339009 

noncomputable def Ns324p1701 := @Ns324p1700 Ns324p717 317672429 5368709120 1213 5368709120 (Ns324p1695 (RS325to336.d4 qz114 qz132 qz278) RS325to336.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable def Ns324p1702 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz279 qz4 qz132 648182 1000 656302 1000 

noncomputable def Ns324p1703 := @Enclosure.norm_gt_of_isNear qz279 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 811370617184835567351 590295810358705651712 435534530697970246101563 

noncomputable def Ns324p1704 := @Ns324p1703 Ns324p74 317672429 5368709120 1213 5368709120 (Ns324p1697 (RS325to336.d50 qz114 qz132 qz278) RS325to336.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable abbrev qz280 := qz553

noncomputable def Ns324p1705 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz114 654697 1000 qz117 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz277 qz279 (Ns324p1696 rfl rfl) (Ns324p1698 rfl rfl)) (Ns324p1699 qz9 qz117 rfl rfl rfl rfl (Ns324p1701 rfl)) (Ns324p1702 qz9 qz137 rfl rfl rfl rfl (Ns324p1704 rfl)) 

noncomputable abbrev qz555 := (RS325to336.d3 qz645 qz655 (@Enclosure.dec_le_dec qz645 qz655 656302 1000 657653 1000 qz649 qz659 rfl rfl rfl))

noncomputable abbrev qz281 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz555)

noncomputable def Ns324p1706 := @Enclosure.Real.IsNear.of_eq qz281 (hardyZApproximantRS₀ qz132) Bool.true 811370617184835567351 590295810358705651712 435534530697970246101563 Ns324p74 

noncomputable abbrev qz556 := (@Enclosure.dec_le_dec qz645 qz655 656302 1000 657653 1000 qz649 qz659 rfl rfl rfl)

noncomputable abbrev qz282 := qz556

noncomputable def Ns324p1707 := @Enclosure.Real.IsNear.neg_val qz281 811370617184835567351 590295810358705651712 435534530697970246101563 Ns324p74 (Ns324p1706 (RS325to336.d4 qz132 qz151 qz282) RS325to336.d57) rfl 

noncomputable abbrev qz283 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz555)

noncomputable def Ns324p1708 := @Enclosure.Real.IsNear.of_eq qz283 (hardyZApproximantRS₀ qz151) Bool.false 3179093439405523870007 2361183241434822606848 8811376926637070626949 Ns324p949 

noncomputable def Ns324p1709 := @Enclosure.Real.IsNear.pos_val qz283 3179093439405523870007 2361183241434822606848 8811376926637070626949 Ns324p949 (Ns324p1708 (RS325to336.d50 qz132 qz151 qz282) RS325to336.d58) rfl 

noncomputable def Ns324p1710 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz281 qz4 qz132 648182 1000 656302 1000 

noncomputable def Ns324p1711 := @Enclosure.norm_gt_of_isNear qz281 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 811370617184835567351 590295810358705651712 435534530697970246101563 

noncomputable def Ns324p1712 := @Ns324p1711 Ns324p74 317672429 5368709120 1213 5368709120 (Ns324p1706 (RS325to336.d4 qz132 qz151 qz282) RS325to336.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable def Ns324p1713 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz283 qz4 qz151 648182 1000 657653 1000 

noncomputable def Ns324p1714 := @Enclosure.norm_gt_of_isNear qz283 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 3179093439405523870007 2361183241434822606848 8811376926637070626949 

noncomputable def Ns324p1715 := @Ns324p1714 Ns324p949 317672429 5368709120 1213 5368709120 (Ns324p1708 (RS325to336.d50 qz132 qz151 qz282) RS325to336.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable abbrev qz284 := qz555

noncomputable def Ns324p1716 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz132 656302 1000 qz137 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz281 qz283 (Ns324p1707 rfl rfl) (Ns324p1709 rfl rfl)) (Ns324p1710 qz9 qz137 rfl rfl rfl rfl (Ns324p1712 rfl)) (Ns324p1713 qz9 qz154 rfl rfl rfl rfl (Ns324p1715 rfl)) 

noncomputable abbrev qz557 := (RS325to336.d3 qz655 qz665 (@Enclosure.dec_le_dec qz655 qz665 657653 1000 659004 1000 qz659 qz669 rfl rfl rfl))

noncomputable abbrev qz285 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz557)

noncomputable def Ns324p1717 := @Enclosure.Real.IsNear.of_eq qz285 (hardyZApproximantRS₀ qz151) Bool.false 3179093439405523870007 2361183241434822606848 8811376926637070626949 Ns324p949 

noncomputable abbrev qz558 := (@Enclosure.dec_le_dec qz655 qz665 657653 1000 659004 1000 qz659 qz669 rfl rfl rfl)

noncomputable abbrev qz286 := qz558

noncomputable def Ns324p1718 := @Enclosure.Real.IsNear.pos_val qz285 3179093439405523870007 2361183241434822606848 8811376926637070626949 Ns324p949 (Ns324p1717 (RS325to336.d4 qz151 qz168 qz286) RS325to336.d58) rfl 

noncomputable abbrev qz287 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz557)

noncomputable def Ns324p1719 := @Enclosure.Real.IsNear.of_eq qz287 (hardyZApproximantRS₀ qz168) Bool.true 4816247373347722346369 2361183241434822606848 227780593991202709580313 Ns324p1064 

noncomputable def Ns324p1720 := @Enclosure.Real.IsNear.neg_val qz287 4816247373347722346369 2361183241434822606848 227780593991202709580313 Ns324p1064 (Ns324p1719 (RS325to336.d50 qz151 qz168 qz286) RS325to336.d59) rfl 

noncomputable def Ns324p1721 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz285 qz4 qz151 648182 1000 657653 1000 

noncomputable def Ns324p1722 := @Enclosure.norm_gt_of_isNear qz285 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 3179093439405523870007 2361183241434822606848 8811376926637070626949 

noncomputable def Ns324p1723 := @Ns324p1722 Ns324p949 317672429 5368709120 1213 5368709120 (Ns324p1717 (RS325to336.d4 qz151 qz168 qz286) RS325to336.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable def Ns324p1724 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz287 qz4 qz168 648182 1000 659004 1000 

noncomputable def Ns324p1725 := @Enclosure.norm_gt_of_isNear qz287 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 4816247373347722346369 2361183241434822606848 227780593991202709580313 

noncomputable def Ns324p1726 := @Ns324p1725 Ns324p1064 317672429 5368709120 1213 5368709120 (Ns324p1719 (RS325to336.d50 qz151 qz168 qz286) RS325to336.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable abbrev qz288 := qz557

noncomputable def Ns324p1727 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz151 657653 1000 qz154 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz285 qz287 (Ns324p1718 rfl rfl) (Ns324p1720 rfl rfl)) (Ns324p1721 qz9 qz154 rfl rfl rfl rfl (Ns324p1723 rfl)) (Ns324p1724 qz9 qz171 rfl rfl rfl rfl (Ns324p1726 rfl)) 

noncomputable abbrev qz715 := (@Enclosure.dec_le_dec qz760 qz764 659004 1000 660354 1000 (@Eq.refl Real qz760) (@Eq.refl Real qz764) rfl rfl rfl)

noncomputable abbrev qz559 := (RS325to336.d3 qz665 qz675 qz715)

noncomputable abbrev qz289 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz559)

noncomputable def Ns324p1728 := @Enclosure.Real.IsNear.of_eq qz289 (hardyZApproximantRS₀ qz168) Bool.true 4816247373347722346369 2361183241434822606848 227780593991202709580313 Ns324p1064 

noncomputable abbrev qz560 := qz715

noncomputable abbrev qz290 := qz560

noncomputable def Ns324p1729 := @Enclosure.Real.IsNear.neg_val qz289 4816247373347722346369 2361183241434822606848 227780593991202709580313 Ns324p1064 (Ns324p1728 (RS325to336.d4 qz168 qz185 qz290) RS325to336.d59) rfl 

noncomputable abbrev qz291 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz559)

noncomputable def Ns324p1730 := @Enclosure.Real.IsNear.of_eq qz291 (hardyZApproximantRS₀ qz185) Bool.false 91282966942358946857 73786976294838206464 112523471163168737125301 Ns324p483 

noncomputable def Ns324p1731 := @Enclosure.Real.IsNear.pos_val qz291 91282966942358946857 73786976294838206464 112523471163168737125301 Ns324p483 (Ns324p1730 (RS325to336.d50 qz168 qz185 qz290) RS325to336.d60) rfl 

noncomputable def Ns324p1732 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz289 qz4 qz168 648182 1000 659004 1000 

noncomputable def Ns324p1733 := @Enclosure.norm_gt_of_isNear qz289 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 4816247373347722346369 2361183241434822606848 227780593991202709580313 

noncomputable def Ns324p1734 := @Ns324p1733 Ns324p1064 317672429 5368709120 1213 5368709120 (Ns324p1728 (RS325to336.d4 qz168 qz185 qz290) RS325to336.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable def Ns324p1735 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz291 qz4 qz185 648182 1000 660354 1000 

noncomputable def Ns324p1736 := @Enclosure.norm_gt_of_isNear qz291 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 91282966942358946857 73786976294838206464 112523471163168737125301 

noncomputable def Ns324p1737 := @Ns324p1736 Ns324p483 317672429 5368709120 1213 5368709120 (Ns324p1730 (RS325to336.d50 qz168 qz185 qz290) RS325to336.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable abbrev qz292 := qz559

noncomputable def Ns324p1738 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz168 659004 1000 qz171 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz289 qz291 (Ns324p1729 rfl rfl) (Ns324p1731 rfl rfl)) (Ns324p1732 qz9 qz171 rfl rfl rfl rfl (Ns324p1734 rfl)) (Ns324p1735 qz9 qz188 rfl rfl rfl rfl (Ns324p1737 rfl)) 

noncomputable abbrev qz716 := (@Enclosure.dec_le_dec qz764 qz768 660354 1000 661704 1000 (@Eq.refl Real qz764) qz771 rfl rfl rfl)

noncomputable abbrev qz561 := (RS325to336.d3 qz675 qz685 qz716)

noncomputable abbrev qz293 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz561)

noncomputable def Ns324p1739 := @Enclosure.Real.IsNear.of_eq qz293 (hardyZApproximantRS₀ qz185) Bool.false 91282966942358946857 73786976294838206464 112523471163168737125301 Ns324p483 

noncomputable abbrev qz562 := qz716

noncomputable abbrev qz294 := qz562

noncomputable def Ns324p1740 := @Enclosure.Real.IsNear.pos_val qz293 91282966942358946857 73786976294838206464 112523471163168737125301 Ns324p483 (Ns324p1739 (RS325to336.d4 qz185 qz203 qz294) RS325to336.d60) rfl 

noncomputable abbrev qz295 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz561)

noncomputable def Ns324p1741 := @Enclosure.Real.IsNear.of_eq qz295 (hardyZApproximantRS₀ qz203) Bool.true 15404870083376154274661 4722366482869645213696 112516992315409069387253 Ns324p363 

noncomputable def Ns324p1742 := @Enclosure.Real.IsNear.neg_val qz295 15404870083376154274661 4722366482869645213696 112516992315409069387253 Ns324p363 (Ns324p1741 (RS325to336.d50 qz185 qz203 qz294) RS325to336.d61) rfl 

noncomputable def Ns324p1743 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz293 qz4 qz185 648182 1000 660354 1000 

noncomputable def Ns324p1744 := @Enclosure.norm_gt_of_isNear qz293 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 91282966942358946857 73786976294838206464 112523471163168737125301 

noncomputable def Ns324p1745 := @Ns324p1744 Ns324p483 317672429 5368709120 1213 5368709120 (Ns324p1739 (RS325to336.d4 qz185 qz203 qz294) RS325to336.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable def Ns324p1746 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz295 qz4 qz203 648182 1000 661704 1000 

noncomputable def Ns324p1747 := @Enclosure.norm_gt_of_isNear qz295 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 15404870083376154274661 4722366482869645213696 112516992315409069387253 

noncomputable def Ns324p1748 := @Ns324p1747 Ns324p363 317672429 5368709120 1213 5368709120 (Ns324p1741 (RS325to336.d50 qz185 qz203 qz294) RS325to336.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable abbrev qz296 := qz561

noncomputable def Ns324p1749 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz185 660354 1000 qz188 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz293 qz295 (Ns324p1740 rfl rfl) (Ns324p1742 rfl rfl)) (Ns324p1743 qz9 qz188 rfl rfl rfl rfl (Ns324p1745 rfl)) (Ns324p1746 qz9 qz206 rfl rfl rfl rfl (Ns324p1748 rfl)) 

noncomputable abbrev qz717 := (@Enclosure.dec_le_dec qz768 qz773 661704 1000 663053 1000 qz771 qz776 rfl rfl rfl)

noncomputable abbrev qz563 := (RS325to336.d3 qz685 qz695 qz717)

noncomputable abbrev qz297 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz563)

noncomputable def Ns324p1750 := @Enclosure.Real.IsNear.of_eq qz297 (hardyZApproximantRS₀ qz203) Bool.true 15404870083376154274661 4722366482869645213696 112516992315409069387253 Ns324p363 

noncomputable abbrev qz564 := qz717

noncomputable abbrev qz298 := qz564

noncomputable def Ns324p1751 := @Enclosure.Real.IsNear.neg_val qz297 15404870083376154274661 4722366482869645213696 112516992315409069387253 Ns324p363 (Ns324p1750 (RS325to336.d4 qz203 qz221 qz298) RS325to336.d61) rfl 

noncomputable abbrev qz299 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz563)

noncomputable def Ns324p1752 := @Enclosure.Real.IsNear.of_eq qz299 (hardyZApproximantRS₀ qz221) Bool.false 5530959801595040344443 1180591620717411303424 110618795987998262122467 Ns324p363 

noncomputable def Ns324p1753 := @Enclosure.Real.IsNear.pos_val qz299 5530959801595040344443 1180591620717411303424 110618795987998262122467 Ns324p363 (Ns324p1752 (RS325to336.d50 qz203 qz221 qz298) RS325to336.d62) rfl 

noncomputable def Ns324p1754 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz297 qz4 qz203 648182 1000 661704 1000 

noncomputable def Ns324p1755 := @Enclosure.norm_gt_of_isNear qz297 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 15404870083376154274661 4722366482869645213696 112516992315409069387253 

noncomputable def Ns324p1756 := @Ns324p1755 Ns324p363 317672429 5368709120 1213 5368709120 (Ns324p1750 (RS325to336.d4 qz203 qz221 qz298) RS325to336.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable def Ns324p1757 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz299 qz4 qz221 648182 1000 663053 1000 

noncomputable def Ns324p1758 := @Enclosure.norm_gt_of_isNear qz299 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 5530959801595040344443 1180591620717411303424 110618795987998262122467 

noncomputable def Ns324p1759 := @Ns324p1758 Ns324p363 317672429 5368709120 1213 5368709120 (Ns324p1752 (RS325to336.d50 qz203 qz221 qz298) RS325to336.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable abbrev qz300 := qz563

noncomputable def Ns324p1760 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz203 661704 1000 qz206 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz297 qz299 (Ns324p1751 rfl rfl) (Ns324p1753 rfl rfl)) (Ns324p1754 qz9 qz206 rfl rfl rfl rfl (Ns324p1756 rfl)) (Ns324p1757 qz9 qz224 rfl rfl rfl rfl (Ns324p1759 rfl)) 

noncomputable abbrev qz783 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 663053 1000) (Enclosure.sfrac Bool.false 664401 1000) 663053 1000 664401 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 663053 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 664401 1000)) rfl rfl rfl)

noncomputable abbrev qz718 := qz783

noncomputable abbrev qz565 := (RS325to336.d3 qz695 qz705 qz718)

noncomputable abbrev qz301 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz565)

noncomputable def Ns324p1761 := @Enclosure.Real.IsNear.of_eq qz301 (hardyZApproximantRS₀ qz221) Bool.false 5530959801595040344443 1180591620717411303424 110618795987998262122467 Ns324p363 

noncomputable abbrev qz566 := qz718

noncomputable abbrev qz302 := qz566

noncomputable def Ns324p1762 := @Enclosure.Real.IsNear.pos_val qz301 5530959801595040344443 1180591620717411303424 110618795987998262122467 Ns324p363 (Ns324p1761 (RS325to336.d4 qz221 qz239 qz302) RS325to336.d62) rfl 

noncomputable abbrev qz303 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz565)

noncomputable def Ns324p1763 := @Enclosure.Real.IsNear.of_eq qz303 (hardyZApproximantRS₀ qz239) Bool.true 747709838712106827405 1180591620717411303424 128062946251283975273 103892062623132194701312 

noncomputable def Ns324p1764 := @Enclosure.Real.IsNear.neg_val qz303 747709838712106827405 1180591620717411303424 128062946251283975273 103892062623132194701312 (Ns324p1763 (RS325to336.d50 qz221 qz239 qz302) RS325to336.d63) rfl 

noncomputable def Ns324p1765 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz301 qz4 qz221 648182 1000 663053 1000 

noncomputable def Ns324p1766 := @Enclosure.norm_gt_of_isNear qz301 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 5530959801595040344443 1180591620717411303424 110618795987998262122467 

noncomputable def Ns324p1767 := @Ns324p1766 Ns324p363 317672429 5368709120 1213 5368709120 (Ns324p1761 (RS325to336.d4 qz221 qz239 qz302) RS325to336.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable def Ns324p1768 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz303 qz4 qz239 648182 1000 664401 1000 

noncomputable def Ns324p1769 := @Enclosure.norm_gt_of_isNear qz303 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 747709838712106827405 1180591620717411303424 128062946251283975273 

noncomputable def Ns324p1770 := @Ns324p1769 103892062623132194701312 317672429 5368709120 1213 5368709120 (Ns324p1763 (RS325to336.d50 qz221 qz239 qz302) RS325to336.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 317672429 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS325to336.d52) rfl rfl rfl rfl 

noncomputable abbrev qz304 := qz565

noncomputable def Ns324p1771 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz221 663053 1000 qz224 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz301 qz303 (Ns324p1762 rfl rfl) (Ns324p1764 rfl rfl)) (Ns324p1765 qz9 qz224 rfl rfl rfl rfl (Ns324p1767 rfl)) (Ns324p1768 qz9 qz242 rfl rfl rfl rfl (Ns324p1770 rfl)) 

noncomputable def Ns324p1772 := @List.cons RS325to336.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns324p1760)) (@List.cons RS325to336.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns324p1771)) (@List.nil RS325to336.d0)) 

noncomputable def Ns324p1773 := @List.cons RS325to336.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns324p1738)) (@List.cons RS325to336.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns324p1749)) Ns324p1772) 

noncomputable def Ns324p1774 := @List.cons RS325to336.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns324p1716)) (@List.cons RS325to336.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns324p1727)) Ns324p1773) 

noncomputable def Ns324p1775 := @List.cons RS325to336.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns324p1694)) (@List.cons RS325to336.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns324p1705)) Ns324p1774) 

noncomputable def Ns324p1776 := @List.cons RS325to336.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns324p1672)) (@List.cons RS325to336.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns324p1683)) Ns324p1775) 

noncomputable def Ns324p1777 := @List.cons RS325to336.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz260 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz260) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz260) Ns324p1650)) (@List.cons RS325to336.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz264 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz264) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz264) Ns324p1661)) Ns324p1776) 

noncomputable abbrev qz567 := (RS325to336.d2 qz665 qz675 qz715)

noncomputable abbrev qz719 := (RS325to336.d2 qz768 qz773 (@Enclosure.dec_le_dec qz768 qz773 661704 1000 663053 1000 qz771 qz776 rfl rfl rfl))

noncomputable abbrev qz720 := (@List.cons RS325to336.d1 (RS325to336.d2 qz773 qz778 qz783) (@List.nil RS325to336.d1))

noncomputable abbrev qz568 := (@List.cons RS325to336.d1 (RS325to336.d2 qz675 qz685 qz716) (@List.cons RS325to336.d1 qz719 qz720))

noncomputable abbrev qz305 := (@List.cons RS325to336.d1 (RS325to336.d2 qz466 qz479 qz558) (@List.cons RS325to336.d1 qz567 qz568))

noncomputable def Ns324p1778 := @List.cons RS325to336.d1 (RS325to336.d2 qz114 qz132 qz278) (@List.cons RS325to336.d1 (RS325to336.d2 qz132 qz151 qz282) qz305) 

noncomputable abbrev qz306 := (RS325to336.d2 qz427 qz440 qz552)

noncomputable def Ns324p1779 := @List.IsChain.cons_cons RS325to336.d1 RS325to336.d64 qz306 (RS325to336.d2 qz114 qz132 qz278) (@List.cons RS325to336.d1 (RS325to336.d2 qz132 qz151 qz282) qz305) 

noncomputable def Ns324p1780 := @List.IsChain.cons_cons RS325to336.d1 RS325to336.d64 (RS325to336.d2 qz114 qz132 qz278) (RS325to336.d2 qz132 qz151 qz282) qz305 (@Enclosure.dec_le_dec qz132 qz132 656302 1000 656302 1000 qz137 qz137 rfl rfl rfl) 

noncomputable abbrev qz307 := (RS325to336.d2 qz466 qz479 qz558)

noncomputable abbrev qz308 := qz567

noncomputable abbrev qz309 := qz568

noncomputable abbrev qz569 := (RS325to336.d2 qz675 qz685 qz716)

noncomputable abbrev qz310 := qz569

noncomputable abbrev qz570 := (@List.cons RS325to336.d1 qz719 qz720)

noncomputable abbrev qz311 := qz570

noncomputable abbrev qz571 := qz719

noncomputable abbrev qz312 := qz571

noncomputable abbrev qz572 := qz720

noncomputable abbrev qz313 := qz572

noncomputable abbrev qz721 := (RS325to336.d2 qz773 qz778 qz783)

noncomputable abbrev qz573 := qz721

noncomputable abbrev qz314 := qz573

noncomputable def Ns324p1781 := @List.IsChain.cons_cons RS325to336.d1 RS325to336.d64 qz307 qz308 qz309 (@Enclosure.dec_le_dec qz168 qz168 659004 1000 659004 1000 qz171 qz171 rfl rfl rfl) (@List.IsChain.cons_cons RS325to336.d1 RS325to336.d64 qz308 qz310 qz311 (@Enclosure.dec_le_dec qz185 qz185 660354 1000 660354 1000 qz188 qz188 rfl rfl rfl) (@List.IsChain.cons_cons RS325to336.d1 RS325to336.d64 qz310 qz312 qz313 (@Enclosure.dec_le_dec qz203 qz203 661704 1000 661704 1000 qz206 qz206 rfl rfl rfl) (@List.IsChain.cons_cons RS325to336.d1 RS325to336.d64 qz312 qz314 (@List.nil RS325to336.d1) (@Enclosure.dec_le_dec qz221 qz221 663053 1000 663053 1000 qz224 qz224 rfl rfl rfl) (@List.IsChain.singleton RS325to336.d1 RS325to336.d64 qz314)))) 

noncomputable abbrev qz315 := (@List.cons RS325to336.d1 qz567 qz568)

noncomputable def Ns324p1782 := @List.IsChain.cons_cons RS325to336.d1 RS325to336.d64 (RS325to336.d2 qz132 qz151 qz282) qz307 qz315 (@Enclosure.dec_le_dec qz151 qz151 657653 1000 657653 1000 qz154 qz154 rfl rfl rfl) Ns324p1781 

noncomputable def Ns324p1783 := @List.IsChain.cons_cons RS325to336.d1 RS325to336.d64 (RS325to336.d2 qz4 qz33 qz258) (RS325to336.d2 qz33 qz60 qz262) (@List.cons RS325to336.d1 (RS325to336.d2 qz60 qz78 qz266) (@List.cons RS325to336.d1 (RS325to336.d2 qz78 qz96 qz270) (@List.cons RS325to336.d1 qz306 Ns324p1778))) (@Enclosure.dec_le_dec qz33 qz33 649791 1000 649791 1000 qz36 qz36 rfl rfl rfl) (@List.IsChain.cons_cons RS325to336.d1 RS325to336.d64 (RS325to336.d2 qz33 qz60 qz262) (RS325to336.d2 qz60 qz78 qz266) (@List.cons RS325to336.d1 (RS325to336.d2 qz78 qz96 qz270) (@List.cons RS325to336.d1 qz306 Ns324p1778)) (@Enclosure.dec_le_dec qz60 qz60 650383 1000 650383 1000 qz63 qz63 rfl rfl rfl) (@List.IsChain.cons_cons RS325to336.d1 RS325to336.d64 (RS325to336.d2 qz60 qz78 qz266) (RS325to336.d2 qz78 qz96 qz270) (@List.cons RS325to336.d1 qz306 Ns324p1778) (@Enclosure.dec_le_dec qz78 qz78 652160 1000 652160 1000 qz81 qz81 rfl rfl rfl) (@List.IsChain.cons_cons RS325to336.d1 RS325to336.d64 (RS325to336.d2 qz78 qz96 qz270) qz306 Ns324p1778 (@Enclosure.dec_le_dec qz96 qz96 654021 1000 654021 1000 qz99 qz99 rfl rfl rfl) (Ns324p1779 (@Enclosure.dec_le_dec qz114 qz114 654697 1000 654697 1000 qz117 qz117 rfl rfl rfl) (Ns324p1780 Ns324p1782))))) 

noncomputable abbrev qz574 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz575 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns324p1777 Ns324p1783)

noncomputable abbrev qz576 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns324p1777 Ns324p1783))

theorem RS325to336.d65 : Zeta.Certificates.BatchSpec 12 648182 1000 664401 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz574 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz574 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz574 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz239)))) qz575 (@And.intro (@Eq Nat (@List.length qz574 qz576) 12) (And (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz574 qz576)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz574 qz576)) (@Option.some Real qz239))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz574 qz576)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz574 qz576)) (@Option.some Real qz239)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz239))))

theorem solution : Zeta.Certificates.BatchSpec 12 648182 1000 664401 1000 := RS325to336.d65
#print axioms solution
#check solution
